#!/usr/bin/env python3
"""Plan and export the certified continuation of all 65 roots around the meridian gamma_1.

The loop is the paper's (certificate/tools/monodromy.py): from t = 0 straight to
the entry point E = z - eps z/|z| (z = zeta_3), counter-clockwise around the inscribed
24-gon about z starting at E, and back to 0. Vertices are rounded to 2^-J; the polygon
closes exactly at the rounded E.

  plan   choose Rouche steps (parameter discs) and waypoints; every step, inclusion and
         junction is checked here in exact integer arithmetic (the same checks the Lean
         kernel replays), and the plan is written to certs/meridian1.json;
  emit   write the Lean files from the plan (--check compares instead of writing).

Base labels: the discs of step 0 are ordered exactly as the paper's tracker orders the
roots at t = 0 (acb_poly.roots at 1200 bits), so the closed monodromy is directly
comparable to data/monodromy.json. Every other step's discs are ordered by matching to
its predecessor, so every junction map is the identity except where the circle closes.
"""
import argparse
import cmath
from hashlib import sha256
import json
import math
import multiprocessing as mp
import os
from pathlib import Path
import sys
import time

import flint

import export_continuation as ec

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PLAN = HERE / "certs/meridian1.json"
OUTDIR = HERE / "Sz8/Monodromy/Meridian"
K, J = ec.K, ec.J
RHO = 0.97                    # waypoints within RHO * S of the step centre
STEPS_PER_FILE = 6
LEGS_PER_CHUNK = 24


def log(*a):
    print(f"[{time.strftime('%H:%M:%S')}]", *a, flush=True)


# ---- exact checks (replicas of the Lean Bool checks) ----

_W = {}


def _init():
    _W["cols"] = ec.load_columns()[1]
    _W["rows"] = {}


def _disc_ok(args):
    tau, g, W, S = args
    rows = _W["rows"]
    if tau not in rows:
        if len(rows) > 4:
            rows.clear()
        rows[tau] = ec.step_rows(tau, _W["cols"])
    return ec.disc_ok(rows[tau], g, W, S)


def in_step(tau, S, w):
    d = (w[0] - tau[0], w[1] - tau[1])
    return d[0] * d[0] + d[1] * d[1] <= S * S


def separated(q, r):
    s = q[1] + r[1]
    d = (q[0][0] - r[0][0], q[0][1] - r[0][1])
    return s * s <= d[0] * d[0] + d[1] * d[1]


def pairwise_separated(discs):
    return all(separated(discs[i], discs[j]) for i in range(len(discs)) for j in range(i + 1, len(discs)))


def junction_ok(d1, d2, pi):
    for i in range(65):
        k = pi[i] if i < len(pi) else i
        if not k < 65:
            return False
        for j in range(65):
            if j != k and not separated(d1[i], d2[j]):
                return False
    return True


def gaps_of(discs):
    """Gap per disc: min over j of floor|c_i - c_j| - r_i - r_j (Chain.lean, StepDatum.gaps)."""
    out = []
    for i, (g, W) in enumerate(discs):
        m = min(math.isqrt((g[0] - h[0]) ** 2 + (g[1] - h[1]) ** 2) - W - V
                for j, (h, V) in enumerate(discs) if j != i)
        assert m >= 0, i
        out.append(m)
    return out


def gaps_ok(discs, gaps):
    """Exact replica of gapsOK: every pair separated with margin max(g_i, g_j)."""
    for i in range(len(discs)):
        for j in range(i + 1, len(discs)):
            s = discs[i][1] + discs[j][1] + max(gaps[i], gaps[j])
            d = (discs[i][0][0] - discs[j][0][0], discs[i][0][1] - discs[j][0][1])
            if s * s > d[0] * d[0] + d[1] * d[1]:
                return False
    return len(discs) == len(gaps)


def incl_ok(q, r, g):
    """Exact replica of inclB: |c_q - c_r| + R_q <= r_r + g."""
    D = r[1] + g - q[1]
    d = (q[0][0] - r[0][0], q[0][1] - r[0][1])
    return D >= 0 and d[0] * d[0] + d[1] * d[1] <= D * D


def junction_g(d1, d2, g2, pi):
    """Exact replica of junctionG (65 inclusions into gap-enlarged target discs)."""
    for i in range(65):
        k = pi[i] if i < len(pi) else i
        if not (k < 65 and incl_ok(d1[i], d2[k], g2[k])):
            return False
    return True


# ---- numerics (proposals only) ----

def roots_float(cols, t):
    return [complex(float(r.real.mid()), float(r.imag.mid())) for r in ec.roots_at(cols, t)]


def discs_from(cent):
    return ec.make_discs_from_centres(cent) if hasattr(ec, "make_discs_from_centres") else _discs(cent)


def _discs(cent):
    discs = []
    for i, c in enumerate(cent):
        hsum = sum(1 / math.hypot(c[0] - e[0], c[1] - e[1]) for j, e in enumerate(cent) if j != i)
        discs.append((c, int(0.3 / hsum)))
    return discs


def centres(roots):
    return [(round(r.real * 2 ** K), round(r.imag * 2 ** K)) for r in roots]


def locate(discs, x):
    """Index of the disc containing the root x (float), or None."""
    X = (x.real * 2 ** K, x.imag * 2 ** K)
    hits = [i for i, (g, W) in enumerate(discs) if math.hypot(X[0] - g[0], X[1] - g[1]) < 0.9 * W]
    return hits[0] if len(hits) == 1 else None


def dy(z):
    return (round(z.real * 2 ** J), round(z.imag * 2 ** J))


def fl(w):
    return complex(w[0] / 2 ** J, w[1] / 2 ** J)


class Planner:
    def __init__(self, pool, cols):
        self.pool, self.cols = pool, cols

    def max_S(self, tau, discs, guess):
        """Largest S (up to a factor 1.06) passing all 65 exact Rouché checks."""
        def ok(S):
            return all(self.pool.map(_disc_ok, [(tau, g, W, S) for g, W in discs]))
        lo, hi = 0, None
        S = max(guess, 1)
        if ok(S):
            lo = S
            while hi is None:
                S = lo * 3 // 2
                if ok(S):
                    lo = S
                else:
                    hi = S
        else:
            hi = S
            while lo == 0:
                S = hi * 2 // 3
                if S == 0:
                    raise RuntimeError(f"no admissible step at {tau}")
                if ok(S):
                    lo = S
                else:
                    hi = S
        while hi > lo * 1.06:
            S = (lo + hi) // 2
            if ok(S):
                lo = S
            else:
                hi = S
        return lo

    def make_step(self, tau, guess, order_ref=None, at=None):
        """A step at tau; discs ordered to match order_ref via the roots at parameter `at`."""
        rts = roots_float(self.cols, fl(tau))
        discs = _discs(centres(rts))
        if order_ref is not None:
            perm = [None] * 65
            for x in roots_float(self.cols, fl(at)):
                a, b = locate(order_ref, x), locate(discs, x)
                if a is None or b is None or perm[a] is not None:
                    raise RuntimeError(f"matching failed at {at}")
                perm[a] = b
            discs = [discs[perm[a]] for a in range(65)]
        assert pairwise_separated(discs)
        S = self.max_S(tau, discs, guess)
        return {"tau": tau, "S": S, "discs": discs}


def farthest_on_segment(p, q, c, r):
    """Largest s in [0, 1] with |p + s(q - p) - c| <= r (floats; p inside)."""
    d = q - p
    f = p - c
    a, b, cc = abs(d) ** 2, 2 * (f.real * d.real + f.imag * d.imag), abs(f) ** 2 - r * r
    disc = b * b - 4 * a * cc
    s = (-b + math.sqrt(max(disc, 0))) / (2 * a)
    return min(1.0, max(0.0, s))


def walk(planner, verts, steps, legs, first):
    """Cover the polyline verts[0] -> ... -> verts[-1] (dyadic GI) with legs, starting in step
    `first` (which contains verts[0]). Appends to steps/legs; returns the last step index."""
    k = first
    cur = verts[0]
    seg = 0
    while True:
        st = steps[k]
        # legs inside step k
        while True:
            tgt = verts[seg + 1]
            if in_step(st["tau"], st["S"] * RHO, tgt) or tgt == cur and in_step(st["tau"], st["S"], tgt):
                legs.append((cur, tgt, k))
                cur = tgt
                seg += 1
                if seg + 1 == len(verts):
                    return k
                continue
            s = farthest_on_segment(fl(cur), fl(tgt), fl(st["tau"]), RHO * st["S"] / 2 ** J)
            x = dy(fl(cur) + s * (fl(tgt) - fl(cur)))
            while not in_step(st["tau"], st["S"], x):
                s *= 0.999
                x = dy(fl(cur) + s * (fl(tgt) - fl(cur)))
            legs.append((cur, x, k))
            cur = x
            break
        # next step: centre ahead of cur along the current segment
        tgt = verts[seg + 1]
        dirn = (fl(tgt) - fl(cur)) / abs(fl(tgt) - fl(cur))
        h = st["S"] / 2 ** J
        ahead = 0.9 * h
        for attempt in range(8):
            c = dy(fl(cur) + min(ahead, abs(fl(tgt) - fl(cur))) * dirn)
            new = planner.make_step(c, st["S"], order_ref=st["discs"], at=cur)
            if in_step(new["tau"], new["S"] * RHO, cur) and junction_ok(st["discs"], new["discs"], []):
                break
            ahead *= 0.6
        else:
            raise RuntimeError(f"cannot place a step after {cur}")
        steps.append(new)
        k = len(steps) - 1
        if len(steps) % 20 == 0:
            log(f"{len(steps)} steps, {len(legs)} legs, |t - z| = {abs(fl(cur) - Z):.3e}, h = {new['S'] / 2 ** J:.3e}")


Z = cmath.exp(2j * math.pi / 3)


def paper_base_roots():
    """The paper tracker's roots at t = 0, in its order (its own code, 1200 bits)."""
    tools = ROOT / "certificate/tools"
    sys.path.insert(0, str(tools))
    cwd = os.getcwd()
    os.chdir(ROOT / "certificate")
    try:
        import monodromy as M
        ct = M.load_f()
        T = M.Tracker(ct, 1200)
        rts = T.roots(flint.acb(0, 0))
    finally:
        os.chdir(cwd)
    return [complex(float(r.real.mid()), float(r.imag.mid())) for r in rts]


def paper_loop():
    """The paper's gamma_1 vertices, as floats (same formulas)."""
    eps = 0.0015118388258389386       # recorded in certificate/results/monodromy.json
    z = complex(-0.5, math.sqrt(3) / 2)
    entry = z - eps * (z / abs(z))
    npts = 24
    ang0 = math.atan2((entry - z).imag, (entry - z).real)
    circ = [z + eps * complex(math.cos(ang0 + 2 * math.pi * k / npts), math.sin(ang0 + 2 * math.pi * k / npts))
            for k in range(npts + 1)]
    return eps, circ


def plan():
    raw, cols = ec.load_columns()
    recorded = json.loads((ROOT / "certificate/results/monodromy.json").read_text())
    eps, circ = paper_loop()
    assert recorded["gamma_1"]["eps"] == eps
    E = dy(circ[0])
    ring = [dy(c) for c in circ[1:-1]]
    out_verts = [(0, 0), E]
    circle_verts = [E] + ring + [E]
    with mp.Pool(os.cpu_count(), initializer=_init) as pool:
        planner = Planner(pool, cols)
        base = _discs(centres(paper_base_roots()))
        assert pairwise_separated(base)
        S0 = planner.max_S((0, 0), base, 2 ** J // 400)
        steps = [{"tau": (0, 0), "S": S0, "discs": base}]
        legs = []
        log("step 0: h =", S0 / 2 ** J)
        tail_last = walk(planner, out_verts, steps, legs, 0)
        n_tail = len(legs)
        log("tail:", len(steps), "steps,", n_tail, "legs")
        # circle: start a fresh step ahead of E along the first side
        circ_last = walk(planner, circle_verts, steps, legs, tail_last)
        log("circle:", len(steps), "steps,", len(legs), "legs")
    # closing junction at E: circle's last step -> the tail's last step
    st_c, st_t = steps[circ_last], steps[tail_last]
    pi = [None] * 65
    for x in roots_float(cols, fl(E)):
        a, b = locate(st_c["discs"], x), locate(st_t["discs"], x)
        assert a is not None and b is not None and pi[a] is None
        pi[a] = b
    # return tail: the outgoing tail legs reversed
    back = [(b, a, k) for (a, b, k) in reversed(legs[:n_tail])]
    pis = [[] for _ in legs]
    pis[-1] = pi
    legs += back
    pis += [[] for _ in back]
    plan = {"source_f_sha256": sha256(raw).hexdigest(), "K": K, "J": J,
            "steps": steps, "legs": legs, "pis": pis}
    verify_plan(plan)
    PLAN.parent.mkdir(exist_ok=True)
    PLAN.write_text(json.dumps(plan, separators=(",", ":")))
    log("wrote", PLAN)


def lab_closure(plan):
    legs, pis = plan["legs"], plan["pis"]
    res = []
    for i in range(65):
        x = i
        for pi in pis:
            x = pi[x] if x < len(pi) else x
        res.append(x)
    return res


def verify_plan(plan, rouche=False):
    """Exact checks of the chain (everything but the Rouché inequalities, unless rouche)."""
    steps, legs, pis = plan["steps"], plan["legs"], plan["pis"]
    n = len(legs)
    for s in steps:
        s["tau"] = tuple(s["tau"])
        s["discs"] = [(tuple(g), W) for g, W in s["discs"]]
    assert legs[0][0] == (0, 0) or tuple(legs[0][0]) == (0, 0)
    assert tuple(legs[-1][1]) == (0, 0) and legs[0][2] == 0
    for k, (a, b, i) in enumerate(legs):
        a, b = tuple(a), tuple(b)
        nxt = legs[(k + 1) % n]
        assert k + 1 == n or tuple(nxt[0]) == b
        st, st2 = steps[i], steps[nxt[2]]
        assert in_step(st["tau"], st["S"], a) and in_step(st["tau"], st["S"], b), k
        assert in_step(st2["tau"], st2["S"], b), k
        assert junction_g(st["discs"], st2["discs"], gaps_of(st2["discs"]), pis[k]), k
    for s in steps:
        assert len(s["discs"]) == 65 and pairwise_separated(s["discs"])
        assert gaps_ok(s["discs"], gaps_of(s["discs"]))
    sigma = json.loads((ROOT / "data/monodromy.json").read_text())["permutations"]["gamma_1"]
    closure = lab_closure(plan)
    log("closure == recorded sigma_1:", closure == sigma)
    if rouche:
        with mp.Pool(os.cpu_count(), initializer=_init) as pool:
            for idx, s in enumerate(steps):
                assert all(pool.map(_disc_ok, [(s["tau"], g, W, s["S"]) for g, W in s["discs"]])), idx
    return closure == sigma


# ---- Lean emission ----

NS = "Sz8.Monodromy.Meridian1"
HEADER = "-- Generated by export_meridian.py from certs/meridian1.json; do not edit.\n"


def gi(a):
    return f"({a[0]}, {a[1]})"


def tup(names):
    """Proof of a conjunction of the given facts (a single fact is not wrapped)."""
    return names[0] if len(names) == 1 else "⟨" + ", ".join(names) + "⟩"


BCONV = 4096       # digit width of the product check (Sz8/Monodromy/ConvCheck.lean)
_F = [math.factorial(k) for k in range(66)]


def conv_bound_ok(tau, gam, cols):
    """Exact replica of convPre's digit bound: rowBound J K tau * vmajN gam < 2^(BCONV-1)."""
    def lin_maj(c):   # maj 1 (linR K c) for a real column
        return sum(_F[i] * abs(a) << (K * (65 - i)) for i, a in enumerate(c))
    t = 1 + ec.n1(tau)
    row_bound = sum(t ** j * (lin_maj(c) << (J * (7 - j))) for j, c in enumerate(cols))
    vmaj = sum(_F[65] // _F[65 - u] * gam ** (65 - u) for u in range(66))
    return row_bound * vmaj < 2 ** (BCONV - 1)


def disc_list(ds):
    return "[" + ", ".join(f"({gi(g)}, {W})" for g, W in ds) + "]"


def emit_files(plan):
    steps, legs, pis = plan["steps"], plan["legs"], plan["pis"]
    cols = ec.load_columns()[1]
    files = {}
    nfiles = (len(steps) + STEPS_PER_FILE - 1) // STEPS_PER_FILE
    for f in range(nfiles):
        idx = list(range(f * STEPS_PER_FILE, min(len(steps), (f + 1) * STEPS_PER_FILE)))
        data = HEADER + f"import Sz8.Monodromy.StepDatum\n\nnamespace {NS}\nopen GaussPoly\n\n"
        cert = HEADER + (f"import Sz8.Monodromy.Meridian.Data{f:03}\nimport Sz8.Monodromy.ConvCheck\n\n/-! Rouché certificates for steps "
                         f"{idx[0]}–{idx[-1]} of the meridian `γ₁`. -/\n\nnamespace {NS}\nopen GaussPoly\n\n"
                         "set_option maxRecDepth 100000\n\n")
        for k in idx:
            st = steps[k]
            tau, S, discs = tuple(st["tau"]), st["S"], st["discs"]
            gam = max(ec.n1(g) for g, _ in discs)
            assert conv_bound_ok(tau, gam, cols), k
            sl = [discs[i:i + ec_SLICE] for i in range(0, 65, ec_SLICE)]
            for j, part in enumerate(sl):
                data += f"def s{k}d{j} : List (GI × ℕ) :=\n  {disc_list(part)}\n\n"
            gaps = gaps_of(discs)
            assert gaps_ok(discs, gaps), k
            data += (f"def s{k}sl : List (List (GI × ℕ)) := [" + ", ".join(f"s{k}d{j}" for j in range(len(sl))) + "]\n\n"
                     f"def s{k}g : List ℕ :=\n  [" + ", ".join(map(str, gaps)) + "]\n\n"
                     f"/-- Step {k}: `|t - τ/2^{J}| ≤ {S}/2^{J}` (about {S / 2 ** J:.3e}). -/\n"
                     f"def s{k} : StepDatum := ⟨{gi(tau)}, {S}, s{k}sl.flatten, s{k}g⟩\n\n")
            cert += f"theorem s{k}_pre : convPre {J} {K} {BCONV} {gi(tau)} {gam} s{k}sl.flatten = true := by\n  decide +kernel\n\n"
            for j in range(len(sl)):
                cert += f"theorem s{k}_sl{j} : convSlice {J} {K} {BCONV} {gi(tau)} {S} s{k}d{j} = true := by\n  decide +kernel\n\n"
            cert += f"theorem s{k}_gap : gapsOK s{k}sl.flatten s{k}g = true := by\n  decide +kernel\n\n"
            cert += (f"theorem s{k}_cert : s{k}.Cert {J} {K} :=\n  StepDatum.cert_of_conv s{k}_pre s{k}_gap (by\n"
                     f"    simp only [s{k}sl, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,\n"
                     f"      implies_true, and_true]\n    exact ⟨" + ", ".join(f"s{k}_sl{j}" for j in range(len(sl))) + "⟩)\n\n")
        data += f"def file{f:03} : List StepDatum := [" + ", ".join(f"s{k}" for k in idx) + f"]\n\nend {NS}\n"
        cert += (f"theorem file{f:03}_cert : ∀ s ∈ file{f:03}, s.Cert {J} {K} := by\n"
                 f"  simp only [file{f:03}, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,\n"
                 f"    implies_true, and_true]\n  exact " + tup([f"s{k}_cert" for k in idx]) + f"\n\nend {NS}\n")
        files[f"Data{f:03}.lean"] = data
        files[f"Cert{f:03}.lean"] = cert
    # the chain
    wps = [tuple(legs[0][0])] + [tuple(l[1]) for l in legs]
    n = len(legs)
    chain = HEADER + "import Sz8.Monodromy.Chain\n" + "".join(f"import Sz8.Monodromy.Meridian.Data{f:03}\n" for f in range(nfiles)) + f"""
/-! The meridian `γ₁` as a closed chain of certified steps: {n} legs through exact dyadic
waypoints (scale `2^{J}`), {len(steps)} distinct steps. -/

namespace {NS}
open GaussPoly

def steps : List StepDatum :=
  [""" + ", ".join(f"file{f:03}" for f in range(nfiles)) + """].flatten

""" + chunked("wps", "GI", [gi(w) for w in wps]) + chunked("legIdx", "ℕ", [str(l[2]) for l in legs]) + \
        chunked("pis", "List ℕ", ["[]" if not p else "[" + ", ".join(map(str, p)) + "]" for p in pis]) + f"""def chain : Chain := ⟨wps, steps, legIdx, pis⟩

end {NS}
"""
    files["Chain.lean"] = chain
    chunks, legnames = legs_files(files, "Legs", "chain", "Sz8.Monodromy.Meridian.Chain", n)
    sigma = json.loads((ROOT / "data/monodromy.json").read_text())["permutations"]["gamma_1"]
    gamma = HEADER + "import Sz8.Monodromy.MonodromyData\n" + "".join(f"import Sz8.Monodromy.Meridian.Cert{f:03}\n" for f in range(nfiles)) + \
        "".join(f"import Sz8.Monodromy.Meridian.{m}\n" for m in legnames) + f"""
/-! The certified meridian `γ₁`: Mathlib's monodromy of the closed polyline equals the recorded
`σ₁` in the paper's labelling of the roots over `t = 0`. -/

namespace {NS}
open GaussPoly Polynomial

set_option maxRecDepth 100000

theorem chain_steps_cert : ∀ s ∈ steps, s.Cert {J} {K} := by
  rw [steps, List.forall_mem_flatten]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨""" + ", ".join(f"file{f:03}_cert" for f in range(nfiles)) + f"""⟩

""" + legs_all_proof("chain", n, chunks) + f"""theorem closed : chain.wp chain.n = chain.wp 0 := by decide +kernel

theorem wp_zero : chain.wp 0 = (0, 0) := by decide +kernel

theorem lab_eq : ∀ i : Fin 65, chain.lab chain.n i = (σ₁ i : ℕ) := by decide +kernel

/-- The parameter `t = 0` is regular. -/
theorem zero_regular : (0 : ℂ) ∈ paperMonicFamily.regular := by
  have hl := Chain.legOK (k := 0) chain_steps_cert chain_legs_all (by rw [chain_n_eq]; norm_num)
  have h := hl.start
  rw [wp_zero] at h
  simp only [ptC, gc_zero, zero_div] at h
  exact regular_of_cert hl.cert (by simpa using h)

/-- **The meridian `γ₁`.** Over the base point `t = 0`, with fibre points labelled by the
65 certified discs of step 0 (the paper's root order), Mathlib's monodromy of the closed
certified polyline is the recorded `σ₁`. -/
theorem monodromy_γ₁ : ∃ (e : paperMonicFamily.Fiber ⟨0, zero_regular⟩ ≃ Fin 65)
    (γ : Path (⟨0, zero_regular⟩ : paperMonicFamily.Base) ⟨0, zero_regular⟩),
    (∀ u, (γ u).1 = chain.poly {J} (chain.n - 1) u) ∧
    ∀ i, e (paperMonicFamily.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) (e.symm i)) = σ₁ i := by
  have hb0 : ((⟨0, zero_regular⟩ : paperMonicFamily.Base) : ℂ) = ptC {J} (chain.wp 0) := by
    rw [wp_zero]; simp [ptC]
  obtain ⟨hc, ht, γ, hγ, hmono⟩ := Chain.loop_monodromy chain_steps_cert chain_legs_all
    (by rw [chain_n_eq]; norm_num) closed _ hb0 s0 rfl
  exact ⟨labelEquiv hc ht, γ, hγ, fun i => Fin.ext ((hmono i).trans (lab_eq i))⟩

end {NS}
"""
    files["Gamma1.lean"] = gamma
    emit_gamma2(files, plan)
    return files


def legs_files(files, prefix, cname, cmodule, n):
    chunks = [(lo, min(LEGS_PER_CHUNK, n - lo)) for lo in range(0, n, LEGS_PER_CHUNK)]
    per = 8
    names = []
    for g in range((len(chunks) + per - 1) // per):
        src = HEADER + f"import {cmodule}\n\nnamespace {NS}\n\nset_option maxRecDepth 100000\n\n"
        for lo, ln in chunks[g * per:(g + 1) * per]:
            src += f"theorem {cname}_legs{lo} : {cname}.chunkB {lo} {ln} = true := by\n  decide +kernel\n\n"
        names.append(f"{prefix}{g:03}")
        files[f"{prefix}{g:03}.lean"] = src + f"end {NS}\n"
    return chunks, names


def legs_all_proof(cname, n, chunks):
    return (f"theorem {cname}_n_eq : {cname}.n = {n} := by decide +kernel\n\n"
            f"theorem {cname}_legs_all : ∀ k < {cname}.n, {cname}.legB k = true := by\n"
            f"  apply Chain.legs_of_chunkB\n"
            f"  have h := Chain.chunkB_of_chunks (C := {cname}) 0 [" + ", ".join(str(ln) for _, ln in chunks) + "] (by\n"
            "    simp only [Chain.chunkStarts, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,\n"
            "      implies_true, and_true, Nat.reduceAdd]\n"
            "    exact ⟨" + ", ".join(f"{cname}_legs{lo}" for lo, _ in chunks) + "⟩)\n"
            f"  rw [{cname}_n_eq]\n  simpa using h\n\n")


def conj_gi(w):
    return (w[0], -w[1])


def chain2_data(plan):
    """gamma_2 = conj(gamma_1)^-1: the mirror chain traversed backwards, based at step 0 itself.

    Leg 0 is the constant path at t = 0 in step 0; its junction into the mirror of step 0 is
    the conjugation permutation c of the base roots, and so is the final junction back."""
    steps, legs, pis = plan["steps"], plan["legs"], plan["pis"]
    n = len(legs)
    base = [(tuple(g), W) for g, W in steps[0]["discs"]]
    mirror = [((g[0], -g[1]), W) for g, W in base]
    c = [None] * 65                      # disc i of step 0 meets only the mirror of disc c[i]
    for i, (g, W) in enumerate(base):
        hits = [j for j, (h, V) in enumerate(mirror) if not separated((g, W), (h, V))]
        assert len(hits) == 1
        c[i] = hits[0]
    assert sorted(c) == list(range(65)) and all(c[c[i]] == i for i in range(65))
    legs2 = [((0, 0), (0, 0), 0)]
    for k in range(n - 1, -1, -1):
        a, b, idx = legs[k]
        legs2.append((conj_gi(b), conj_gi(a), 1 + idx))
    pis2 = [c]
    for k in range(n - 1, 0, -1):
        p = pis[k - 1]
        if p:
            inv = [0] * 65
            for i, j in enumerate(p):
                inv[j] = i
            p = inv
        pis2.append(p)
    pis2.append(c)
    return legs2, pis2, c


def verify_chain2(plan):
    """Exact chain checks for gamma_2 (its Rouché certificates are the mirrors of gamma_1's)."""
    steps = plan["steps"]
    legs2, pis2, c = chain2_data(plan)
    st2 = [steps[0]] + [{"tau": conj_gi(s["tau"]), "S": s["S"],
                         "discs": [((g[0], -g[1]), W) for g, W in s["discs"]]} for s in steps]
    n = len(legs2)
    for k, (a, b, i) in enumerate(legs2):
        nxt = legs2[(k + 1) % n]
        assert k + 1 == n or tuple(nxt[0]) == tuple(b)
        s, s2 = st2[i], st2[nxt[2]]
        assert in_step(tuple(s["tau"]), s["S"], a) and in_step(tuple(s["tau"]), s["S"], b), k
        assert in_step(tuple(s2["tau"]), s2["S"], b), k
        assert junction_g(s["discs"], s2["discs"], gaps_of(s2["discs"]), pis2[k]), k
    x = list(range(65))
    for p in pis2:
        x = [p[v] if v < len(p) else v for v in x]
    sigma2 = json.loads((ROOT / "data/monodromy.json").read_text())["permutations"]["gamma_2"]
    return x == sigma2


def emit_gamma2(files, plan):
    legs2, pis2, c = chain2_data(plan)
    n2 = len(legs2)
    wps2 = [legs2[0][0]] + [l[1] for l in legs2]
    files["Chain2.lean"] = HEADER + "import Sz8.Monodromy.Conj\nimport Sz8.Monodromy.Meridian.Chain\n" + f"""
/-! The meridian `γ₂` around `ζ₃²`: the mirror image of `γ₁` traversed backwards, based at
step 0 of `γ₁` itself ({n2} legs). Its steps are the mirror images of the steps of `γ₁`. -/

namespace {NS}
open GaussPoly

def steps2 : List StepDatum := s0 :: steps.map StepDatum.conj

""" + chunked("wpsB", "GI", [gi(w) for w in wps2]) + chunked("legIdxB", "ℕ", [str(l[2]) for l in legs2]) + \
        chunked("pisB", "List ℕ", ["[]" if not p else "[" + ", ".join(map(str, p)) + "]" for p in pis2]) + f"""def chain2 : Chain := ⟨wpsB, steps2, legIdxB, pisB⟩

end {NS}
"""
    chunks2, legnames2 = legs_files(files, "LegsB", "chain2", "Sz8.Monodromy.Meridian.Chain2", n2)
    files["Gamma2.lean"] = HEADER + "import Sz8.Monodromy.Meridian.Gamma1\n" + "".join(f"import Sz8.Monodromy.Meridian.{m}\n" for m in legnames2) + f"""
/-! The certified meridian `γ₂` by conjugation, and both meridians in one labelling. -/

namespace {NS}
open GaussPoly Polynomial

set_option maxRecDepth 100000

theorem steps2_cert : ∀ s ∈ steps2, s.Cert {J} {K} := by
  simp only [steps2, List.forall_mem_cons, List.forall_mem_map]
  exact ⟨s0_cert, fun s hs => (chain_steps_cert s hs).conj⟩

""" + legs_all_proof("chain2", n2, chunks2) + f"""theorem closed2 : chain2.wp chain2.n = chain2.wp 0 := by decide +kernel

theorem wp2_zero : chain2.wp 0 = (0, 0) := by decide +kernel

theorem lab2_eq : ∀ i : Fin 65, chain2.lab chain2.n i = (σ₂ i : ℕ) := by decide +kernel

/-- **Both meridians.** Over `t = 0`, with fibre points labelled by the 65 certified discs of
step 0 (the paper's root order), Mathlib's monodromy of the certified polylines `γ₁` (around
`ζ₃`) and `γ₂` (around `ζ₃²`) is the recorded pair `σ₁`, `σ₂`. -/
theorem meridian_monodromy : ∃ (e : paperMonicFamily.Fiber ⟨0, zero_regular⟩ ≃ Fin 65)
    (γ₁ γ₂ : Path (⟨0, zero_regular⟩ : paperMonicFamily.Base) ⟨0, zero_regular⟩),
    (∀ u, (γ₁ u).1 = chain.poly {J} (chain.n - 1) u) ∧
    (∀ u, (γ₂ u).1 = chain2.poly {J} (chain2.n - 1) u) ∧
    (∀ i, e (paperMonicFamily.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ₁) (e.symm i)) = σ₁ i) ∧
    (∀ i, e (paperMonicFamily.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ₂) (e.symm i)) = σ₂ i) := by
  have hb0 : ((⟨0, zero_regular⟩ : paperMonicFamily.Base) : ℂ) = ptC {J} (chain.wp 0) := by
    rw [wp_zero]; simp [ptC]
  have hb0' : ((⟨0, zero_regular⟩ : paperMonicFamily.Base) : ℂ) = ptC {J} (chain2.wp 0) := by
    rw [wp2_zero]; simp [ptC]
  obtain ⟨hc, ht, γ₁, hγ₁, hmono₁⟩ := Chain.loop_monodromy chain_steps_cert chain_legs_all
    (by rw [chain_n_eq]; norm_num) closed _ hb0 s0 rfl
  obtain ⟨hc', ht', γ₂, hγ₂, hmono₂⟩ := Chain.loop_monodromy steps2_cert chain2_legs_all
    (by rw [chain2_n_eq]; norm_num) closed2 _ hb0' s0 rfl
  exact ⟨labelEquiv hc ht, γ₁, γ₂, hγ₁, hγ₂, fun i => Fin.ext ((hmono₁ i).trans (lab_eq i)),
    fun i => Fin.ext ((hmono₂ i).trans (lab2_eq i))⟩

end {NS}
"""


ec_SLICE = 5


def chunked(name, ty, items, size=64):
    """A long list literal as concatenated chunk definitions (elaboration stays linear)."""
    parts = [items[i:i + size] for i in range(0, len(items), size)]
    out = "".join(f"def {name}{c} : List ({ty}) :=\n  [" + ", ".join(p) + "]\n\n" for c, p in enumerate(parts))
    return out + f"def {name} : List ({ty}) :=\n  " + " ++ ".join(f"{name}{c}" for c in range(len(parts))) + "\n\n"


def emit(check):
    plan = json.loads(PLAN.read_text())
    files = emit_files(plan)
    OUTDIR.mkdir(exist_ok=True)
    stale = []
    for name, content in files.items():
        path = OUTDIR / name
        if check:
            if not path.exists() or path.read_text() != content:
                stale.append(name)
        elif not path.exists() or path.read_text() != content:
            path.write_text(content)        # unchanged files keep their build traces
            stale.append(name)
    existing = {p.name for p in OUTDIR.glob("*.lean")}
    extra = existing - set(files)
    if check:
        assert not stale and not extra, f"stale: {stale[:5]}, extra: {sorted(extra)[:5]}"
    else:
        for name in extra:
            (OUTDIR / name).unlink()
    print(f"{'Checked' if check else 'Exported'} {len(files)} files ({len(stale)} {'stale' if check else 'written'}): "
          f"{len(plan['steps'])} steps, {len(plan['legs'])} legs")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["plan", "verify", "emit"])
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    if a.cmd == "plan":
        plan()
    elif a.cmd == "verify":
        p = json.loads(PLAN.read_text())
        print("gamma_2 chain closes to recorded sigma_2:", verify_chain2(json.loads(PLAN.read_text())))
        print(verify_plan(p, rouche=True))
    else:
        emit(a.check)


if __name__ == "__main__":
    main()
