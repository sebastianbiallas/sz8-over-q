#!/usr/bin/env python3
"""Export the certificates behind `Sz8.Monodromy.normalizer_eq`.

Emits `Sz8/Monodromy/NormalizerCerts.lean`. A permutation normalising `G` and fixing the two base
points of the chain conjugates the two-point stabiliser `H` (order 21) to itself. Two short
tables reduce the induced automorphism of `H` to one of two representatives, and a pruned
search then determines the permutation itself: it is equivariant, hence fixed by the images of
the five base points of the `H`-orbits, and every wrong image breaks either injectivity or the
`G₀`-orbit invariant on ordered pairs of points.

Run from any directory; --check compares the generated file without modifying it.
"""
import argparse
from hashlib import sha256
import itertools
import json
from pathlib import Path

from export_provenance import export_outputs
from export_groups import F_SOURCE, SOURCE, ID, build_chain, inv, mul, pack

HERE = Path(__file__).resolve().parent
NPT = 65


def order_of(x):
    k, y = 1, x
    while y != ID:
        y = mul(y, x)
        k += 1
    return k


def evalword(w, gens):
    """`wordProd gens w`, matching `Sz8.Monodromy.wordProd`."""
    x = ID
    for i in reversed(w):
        x = mul(gens[i] if i < len(gens) else ID, x)
    return x


def compute():
    data = json.loads(SOURCE.read_bytes())
    assert data["indexing"] == "zero-based image lists"
    assert data["source_f_sha256"] == sha256(F_SOURCE.read_bytes()).hexdigest()
    s1 = tuple(data["permutations"]["gamma_1"])
    s2 = tuple(data["permutations"]["gamma_2"])
    levels = build_chain([s1, s2], [0, 1, 3])
    a, b = levels[2]["S"]
    tv1, orb1 = levels[1]["tv"], levels[1]["orbit"]
    tv2 = levels[2]["tv"]
    assert len(tv2) == 21 and len(orb1) == 64
    assert sorted(orb1) == list(range(1, NPT))

    # --- H, its orbits, and a word for every point ---
    H, idx, wordOf = [ID], {ID: 0}, [()]
    for h in H:
        w = wordOf[idx[h]]
        for gi, g in enumerate((a, b)):
            k = mul(g, h)
            if k not in idx:
                idx[k] = len(H)
                H.append(k)
                wordOf.append((gi,) + w)
    assert len(H) == 21 and sorted(H) == sorted(tv2)
    assert all(h[0] == 0 and h[1] == 1 for h in H)

    unseen, orbits = set(range(2, NPT)), []
    while unseen:
        r = min(unseen)
        o = sorted({h[r] for h in H})
        orbits.append(o)
        unseen -= set(o)
    assert [len(o) for o in orbits] == [7, 21, 7, 21, 7]
    Xp = [o[0] for o in orbits] + [1, 0]
    lab = [0] * NPT
    for i, o in enumerate(orbits):
        for z in o:
            lab[z] = i
    lab[1], lab[0] = 5, 6
    wtab = [None] * NPT
    wtab[1], wtab[0] = (5, ()), (6, ())
    for i, o in enumerate(orbits):
        for h, w in zip(H, wordOf):
            z = h[o[0]]
            if wtab[z] is None:
                wtab[z] = (i, w)
    assert all(z == evalword(wtab[z][1], [a, b])[Xp[wtab[z][0]]] for z in range(NPT))
    for g in (a, b):
        assert all(lab[g[z]] == lab[z] for z in range(NPT))

    # --- the colour of an ordered pair: the H-orbit label of `(t p)⁻¹ q` ---
    tpos = {o: j for j, o in enumerate(orb1)}
    T = [ID] * NPT   # `getAt` returns the identity off the orbit, as in Lean
    for o, j in tpos.items():
        T[o] = tv1[j]
        assert tv1[j][1] == o
    col = lambda p, q: lab[inv(T[p])[q]]
    for g in levels[1]["S"]:
        for p in range(1, NPT):
            for q in range(1, NPT):
                assert col(g[p], g[q]) == col(p, q)

    # --- the two automorphism representatives ---
    autos = []
    for aa, bb in itertools.product(H, repeat=2):
        ph = [evalword(w, [aa, bb]) for w in wordOf]
        if len(set(ph)) != 21:
            continue
        if all(ph[idx[mul(g, h)]] == mul(gg, ph[j])
               for g, gg in ((a, aa), (b, bb)) for j, h in enumerate(H)):
            autos.append((aa, bb))
    assert len(autos) == 42
    inner = {(mul(mul(h, a), inv(h)), mul(mul(h, b), inv(h))) for h in H}
    assert len(inner) == 21
    outer = next(p for p in autos if p not in inner and p[0] == a)
    reps = [(a, b), outer]

    # --- step 1: conjugate an order-3 element to `a` or `a⁻¹` ---
    ai = inv(a)
    red1 = []
    for p in tv2:
        if order_of(p) != 3:
            red1.append((p, 0, 0))
            continue
        hit = next((h, t) for h in tv2 for t in [mul(mul(inv(h), p), h)] if t in (a, ai))
        red1.append((p, tv2.index(hit[0]), 1 if hit[1] == ai else 0))

    # --- step 2: conjugate the pair by a power of `a`, or reject it by a word ---
    cent = [ID, a, mul(a, a)]
    pool = [w for L in range(1, 11) for w in itertools.product((0, 1), repeat=L)]
    red2 = []
    for aa in (a, ai):
        for bb in tv2:
            hit = None
            for ci, c in enumerate(cent):
                t = (mul(mul(inv(c), aa), c), mul(mul(inv(c), bb), c))
                if t in reps:
                    hit = (0, ci, reps.index(t), (), 0)
                    break
            if hit is None:
                for w in pool:
                    x, y = evalword(w, [a, b]), evalword(w, [aa, bb])
                    for n in (3, 7):
                        xi, yi = n % order_of(x) == 0, n % order_of(y) == 0
                        if xi != yi:
                            hit = (1 if xi else 2, 0, 0, w, n)
                            break
                    if hit:
                        break
            assert hit is not None, (aa, bb)
            red2.append((aa, bb) + hit)
    assert sum(1 for r in red2 if r[2] == 0) == 6

    # --- the pruned search, level by level ---
    def search(ab):
        levels_out, ys = [], [0, 0, 0, 0, 0, 1, 0]

        def uat(z):
            i, w = wtab[z]
            return evalword(w, list(ab))[ys[i]]

        def assigned(k, i):
            return i < k or i in (5, 6)

        def witness(k, det):
            for p in det:
                for q in det:
                    if q == p:
                        continue
                    z = inv(T[p])[q]
                    if not assigned(k, wtab[z][0]):
                        continue
                    P, Q = uat(p), uat(q)
                    if (P == Q and p != q) or col(P, Q) != lab[ys[wtab[z][0]]]:
                        return (p, q)
            return None

        for k in range(5):
            det = [1] + [z for i in range(k) for z in orbits[i]] + orbits[k]
            rows, alive = [], []
            for y in range(NPT):
                ys[k] = y
                w = witness(k + 1, det)
                if w is None:
                    alive.append(y)
                    rows.append((y, 0, 0))
                else:
                    rows.append((y, w[0], w[1]))
            assert len(alive) <= 1, (k, alive)
            levels_out.append((rows, alive[0] if alive else None))
            if not alive:
                break
            ys[k] = alive[0]
        return levels_out

    search0 = search(reps[0])
    assert len(search0) == 5 and [L[1] for L in search0] == Xp[:5], [L[1] for L in search0]
    search1 = search(reps[1])
    assert search1[-1][1] is None and len(search1) <= 5
    wA1 = wordOf[idx[reps[1][0]]]
    wB1 = wordOf[idx[reps[1][1]]]
    return dict(a=a, b=b, reps=reps, tv2=tv2, lab=lab, wtab=wtab, Xp=Xp, orbits=orbits,
                red1=red1, red2=red2, search0=search0, search1=search1, cent=cent,
                wA1=wA1, wB1=wB1)



SEARCH_TAIL = """/-! ## Putting the search together -/

theorem search0_eq {u : Equiv.Perm (Fin 65)}
    (hu : u ∈ normalizer (lclosure Ggens0 : Set (Equiv.Perm (Fin 65))))
    (h0 : u (0 : Fin 65) = 0) (h1 : u (1 : Fin 65) = 1)
    (hc : ∀ i, u * Ggens2.getD i 1 = AB0.getD i 1 * u) : u = 1 := by
  have e0 := lvl0_0 hu h0 h1 hc
  have e1 := lvl0_1 hu h0 h1 hc e0
  have e2 := lvl0_2 hu h0 h1 hc e0 e1
  have e3 := lvl0_3 hu h0 h1 hc e0 e1 e2
  have e4 := lvl0_4 hu h0 h1 hc e0 e1 e2 e3
  have hfix : ∀ i, u (Xp.getD i 0) = Xp.getD i 0 := by
    intro i
    match i with
    | 0 => exact e0
    | 1 => exact e1
    | 2 => exact e2
    | 3 => exact e3
    | 4 => exact e4
    | 5 => exact h1
    | 6 => exact h0
    | (n + 7) => rw [List.getD_eq_default _ _ (Nat.le_add_left 7 n)]; exact h0
  refine Equiv.ext fun z => ?_
  show u z = z
  conv_lhs => rw [hword z]
  rw [word_conj hc, hfix]
  exact (hword z).symm

theorem search1_absurd {u : Equiv.Perm (Fin 65)}
    (hu : u ∈ normalizer (lclosure Ggens0 : Set (Equiv.Perm (Fin 65))))
    (h0 : u (0 : Fin 65) = 0) (h1 : u (1 : Fin 65) = 1)
    (hc : ∀ i, u * Ggens2.getD i 1 = AB1.getD i 1 * u) : False :=
  lvl1_1 hu h0 h1 hc (lvl1_0 hu h0 h1 hc)

/-- **A permutation normalising `G` and fixing both base points lies in the two-point
stabiliser.** -/
theorem mem_of_fixes01 {u : Equiv.Perm (Fin 65)}
    (hu : u ∈ normalizer (lclosure Ggens0 : Set (Equiv.Perm (Fin 65))))
    (h0 : u (0 : Fin 65) = 0) (h1 : u (1 : Fin 65) = 1) : u ∈ lclosure Ggens2 := by
  have hga : Gg2a ∈ lclosure Ggens2 := mem_lclosure (by simp [Ggens2])
  have hgb : Gg2b ∈ lclosure Ggens2 := mem_lclosure (by simp [Ggens2])
  have hmemA : u * Gg2a * u⁻¹ ∈ Red1.map Prod.fst := by
    rw [Red1_cov]; exact Hmem _ (norm_stab2 hu h0 h1 _ hga)
  obtain ⟨r1, hr1, hr1e⟩ := List.mem_map.mp hmemA
  rcases of_decide_eq_true (List.all_eq_true.mp Red1_ok r1 hr1) with hbad | hbad | ⟨hlt, hconj⟩
  · refine absurd ?_ hbad
    rw [hr1e, conj_pow, (show Gg2a ^ 3 = 1 by decide +kernel), mul_one, mul_inv_cancel]
  · refine absurd ?_ (show Gg2a ≠ 1 by decide +kernel)
    have hq : u * Gg2a * u⁻¹ = 1 := hr1e.symm.trans hbad
    have hcg := congrArg (fun x : Equiv.Perm (Fin 65) => u⁻¹ * x * u) hq
    simpa [mul_assoc] using hcg
  set hh : Equiv.Perm (Fin 65) := Gtv2.getD r1.2.1 1 with hhdef
  have hhm : hh ∈ lclosure Ggens2 := Gtv2_mem _
  set u₁ : Equiv.Perm (Fin 65) := hh⁻¹ * u with hu1def
  have hu1n : u₁ ∈ normalizer (lclosure Ggens0 : Set (Equiv.Perm (Fin 65))) :=
    mul_mem (inv_mem (Subgroup.le_normalizer (Hle0 hhm))) hu
  have hu10 : u₁ (0 : Fin 65) = 0 := by
    rw [hu1def, Equiv.Perm.mul_apply, h0]; exact inv_apply_eq (Hfix0 hh hhm)
  have hu11 : u₁ (1 : Fin 65) = 1 := by
    rw [hu1def, Equiv.Perm.mul_apply, h1]; exact inv_apply_eq (Hfix1 hh hhm)
  have haa : u₁ * Gg2a * u₁⁻¹ = Aopt.getD r1.2.2 1 := by
    have e : u₁ * Gg2a * u₁⁻¹ = hh⁻¹ * (u * Gg2a * u⁻¹) * hh := by rw [hu1def]; group
    rw [e, ← hr1e]; exact hconj
  have hmemB : u₁ * Gg2b * u₁⁻¹ ∈ Gtv2 := Hmem _ (norm_stab2 hu1n hu10 hu11 _ hgb)
  have hpair : (Aopt.getD r1.2.2 1, u₁ * Gg2b * u₁⁻¹) ∈ Red2.map (fun r => (r.1, r.2.1)) := by
    rw [Red2_cov]; exact mem_listPairs (getD_mem_self hlt) hmemB
  obtain ⟨r2, hr2, hr2e⟩ := List.mem_map.mp hpair
  obtain ⟨hr2a, hr2b⟩ := Prod.mk.inj hr2e
  set c : Equiv.Perm (Fin 65) := Copt.getD r2.2.2.2.1 1 with hcdef
  have hcm : c ∈ lclosure Ggens2 := Copt_mem _
  have hcn : (c⁻¹ * u₁) ∈ normalizer (lclosure Ggens0 : Set (Equiv.Perm (Fin 65))) :=
    mul_mem (inv_mem (Subgroup.le_normalizer (Hle0 hcm))) hu1n
  have hc0 : (c⁻¹ * u₁) (0 : Fin 65) = 0 := by
    rw [Equiv.Perm.mul_apply, hu10]; exact inv_apply_eq (Hfix0 c hcm)
  have hc1 : (c⁻¹ * u₁) (1 : Fin 65) = 1 := by
    rw [Equiv.Perm.mul_apply, hu11]; exact inv_apply_eq (Hfix1 c hcm)
  have hcja : u₁ * Gg2a * u₁⁻¹ = r2.1 := haa.trans hr2a.symm
  rcases of_decide_eq_true (List.all_eq_true.mp Red2_ok r2 hr2) with
    ⟨_, hA, hB⟩ | ⟨_, hA, hB⟩ | ⟨_, hw1, hw2⟩ | ⟨_, hw1, hw2⟩
  · have e1 : (c⁻¹ * u₁) * Gg2a * (c⁻¹ * u₁)⁻¹ = Gg2a := by
      have e : (c⁻¹ * u₁) * Gg2a * (c⁻¹ * u₁)⁻¹ = c⁻¹ * (u₁ * Gg2a * u₁⁻¹) * c := by group
      rw [e, hcja]; exact hA
    have e2 : (c⁻¹ * u₁) * Gg2b * (c⁻¹ * u₁)⁻¹ = Gg2b := by
      have e : (c⁻¹ * u₁) * Gg2b * (c⁻¹ * u₁)⁻¹ = c⁻¹ * (u₁ * Gg2b * u₁⁻¹) * c := by group
      rw [e, ← hr2b]; exact hB
    have hone := search0_eq hcn hc0 hc1 (conj_getD₂
      (by conv_rhs => rw [← e1]
          group)
      (by conv_rhs => rw [← e2]
          group))
    rw [hu1def] at hone
    have hfin : u = hh * c := by
      have hcg := congrArg (fun x : Equiv.Perm (Fin 65) => hh * c * x) hone
      simpa [mul_assoc] using hcg
    rw [hfin]; exact mul_mem hhm hcm
  · have e1 : (c⁻¹ * u₁) * Gg2a * (c⁻¹ * u₁)⁻¹ = A1 := by
      have e : (c⁻¹ * u₁) * Gg2a * (c⁻¹ * u₁)⁻¹ = c⁻¹ * (u₁ * Gg2a * u₁⁻¹) * c := by group
      rw [e, hcja]; exact hA
    have e2 : (c⁻¹ * u₁) * Gg2b * (c⁻¹ * u₁)⁻¹ = B1 := by
      have e : (c⁻¹ * u₁) * Gg2b * (c⁻¹ * u₁)⁻¹ = c⁻¹ * (u₁ * Gg2b * u₁⁻¹) * c := by group
      rw [e, ← hr2b]; exact hB
    exact absurd (search1_absurd hcn hc0 hc1 (conj_getD₂
      (by conv_rhs => rw [← e1]
          group)
      (by conv_rhs => rw [← e2]
          group))) not_false
  · refine absurd ?_ hw2
    have hcj : ∀ i, u₁ * Ggens2.getD i 1 * u₁⁻¹ =
        ([r2.1, r2.2.1] : List (Equiv.Perm (Fin 65))).getD i 1 := conj_getD₂' hcja hr2b.symm
    rw [← wordProd_conj hcj r2.2.2.2.2.1, conj_pow, hw1, mul_one, mul_inv_cancel]
  · refine absurd ?_ hw1
    have hcj : ∀ i, u₁ * Ggens2.getD i 1 * u₁⁻¹ =
        ([r2.1, r2.2.1] : List (Equiv.Perm (Fin 65))).getD i 1 := conj_getD₂' hcja hr2b.symm
    rw [← wordProd_conj hcj r2.2.2.2.2.1, conj_pow] at hw2
    have hcg := congrArg (fun x : Equiv.Perm (Fin 65) => u₁⁻¹ * x * u₁) hw2
    simpa [mul_assoc] using hcg

/-! ## The normalizer -/

theorem Gto0 : ∀ o ∈ Gorb0, getAt Gtv0 Gorb0 o 0 = o := by
  have h : (Gorb0.all fun o => decide (getAt Gtv0 Gorb0 o 0 = o)) = true := by decide +kernel
  exact fun o ho => of_decide_eq_true (List.all_eq_true.mp h o ho)

theorem Gorb0_all : ∀ z : Fin 65, z ∈ Gorb0 := by
  have h : ((List.finRange 65).all fun z => decide (z ∈ Gorb0)) = true := by decide +kernel
  exact fun z => of_decide_eq_true (List.all_eq_true.mp h z (List.mem_finRange z))

/-- **The normalizer of the recorded monodromy group in the symmetric group is the group
itself.** -/
theorem normalizer_eq :
    normalizer (lclosure Ggens0 : Set (Equiv.Perm (Fin 65))) = lclosure Ggens0 := by
  refine le_antisymm (fun k hk => ?_) Subgroup.le_normalizer
  set g1 : Equiv.Perm (Fin 65) := getAt Gtv0 Gorb0 (k 0) with hg1def
  have hg1 : g1 ∈ lclosure Ggens0 := Gtv0_mem _
  set v : Equiv.Perm (Fin 65) := g1⁻¹ * k with hvdef
  have hv0 : v (0 : Fin 65) = 0 := by
    rw [hvdef, Equiv.Perm.mul_apply]
    exact inv_apply_eq (Gto0 _ (Gorb0_all _))
  have hvn : v ∈ normalizer (lclosure Ggens0 : Set (Equiv.Perm (Fin 65))) :=
    mul_mem (inv_mem (Subgroup.le_normalizer hg1)) hk
  have hv1 : v 1 ∈ Gorb1 := by
    rw [Gorb1_iff]
    exact fun hcon => absurd (v.injective (hcon.trans hv0.symm)) (by decide)
  set g2 : Equiv.Perm (Fin 65) := tv1 (v 1) with hg2def
  have hg2 : g2 ∈ lclosure Ggens1 := Gtv1_mem _
  set w : Equiv.Perm (Fin 65) := g2⁻¹ * v with hwdef
  have hw1 : w (1 : Fin 65) = 1 := by
    rw [hwdef, Equiv.Perm.mul_apply]; exact inv_apply_eq (G1to _ hv1)
  have hw0 : w (0 : Fin 65) = 0 := by
    rw [hwdef, Equiv.Perm.mul_apply, hv0]; exact inv_apply_eq (G1fix0 _ hg2)
  have hwn : w ∈ normalizer (lclosure Ggens0 : Set (Equiv.Perm (Fin 65))) :=
    mul_mem (inv_mem (Subgroup.le_normalizer (lclosure_le Ggens1_mem hg2))) hvn
  have hfin : k = g1 * (g2 * w) := by rw [hwdef, hvdef]; group
  rw [hfin]
  exact mul_mem hg1 (mul_mem (lclosure_le Ggens1_mem hg2) (Hle0 (mem_of_fixes01 hwn hw0 hw1)))

"""

def perm_def(name, p, doc):
    return (f"/-- {doc} -/\ndef {name} : Equiv.Perm (Fin 65) :="
            f" ofPacked {pack(p)} {pack(inv(p))}\n\n")



def fin(x):
    return f"({x} : Fin 65)"


def rows_lit(rows):
    return "[" + ", ".join(f"({y}, {p}, {q})" for y, p, q in rows) + "]"


def ys_lit(vals, k):
    xs = [str(v) for v in vals[:k]] + ["r.1"] + ["0"] * (4 - k) + ["1", "0"]
    return "[" + ", ".join(xs) + "]"


def level_block(Xp, e, k, rows, surv, vals, xb, last):
    """Data and proof for one level of the search."""
    name = f"Lv{e}_{k}"
    out = [f"/-- Level {k} of the search for the {'identity' if e == 0 else 'outer'} "
           "automorphism: a witness for every wrong image of the base point. -/\n"
           f"def {name} : List (Fin 65 × Fin 65 × Fin 65) :=\n  {rows_lit(rows)}\n\n",
           f"theorem {name}_cov : {name}.map Prod.fst = List.finRange 65 := by decide +kernel\n\n"]
    body = (f"rowOK wi ww orbAt tv1 AB{e} {ys_lit(vals, k)} 0 Gorb1 {k + 1} r.2.1 r.2.2")
    if last:
        out.append(f"theorem {name}_ok : ({name}.all fun r => {body}) = true := by\n"
                   "  decide +kernel\n\n")
    else:
        out.append(f"theorem {name}_ok : ({name}.all fun r =>\n"
                   f"    decide (r.1 = ({surv} : Fin 65)) || {body}) = true := by decide +kernel\n\n")
    args = "".join(f" (e{j} : u ({Xp[j]} : Fin 65) = {vals[j]})" for j in range(k))
    concl = "False" if last else f"u ({xb} : Fin 65) = {surv}"
    proof = [f"theorem lvl{e}_{k} {{u : Equiv.Perm (Fin 65)}}\n",
             "    (hu : u ∈ normalizer (lclosure Ggens0 : Set (Equiv.Perm (Fin 65))))\n",
             "    (h0 : u (0 : Fin 65) = 0) (h1 : u (1 : Fin 65) = 1)\n",
             f"    (hc : ∀ i, u * Ggens2.getD i 1 = AB{e}.getD i 1 * u)"
             + (args + " :\n    " if args else " :\n    ") + concl + " := by\n",
             f"  have hm : u ({xb} : Fin 65) ∈ {name}.map Prod.fst := by\n",
             f"    rw [{name}_cov]; exact List.mem_finRange _\n",
             "  obtain ⟨r, hr, hre⟩ := List.mem_map.mp hm\n",
             f"  have h := List.all_eq_true.mp {name}_ok r hr\n"]
    if not last:
        proof += ["  rw [Bool.or_eq_true, decide_eq_true_eq] at h\n",
                  "  rcases h with heq | hrow\n",
                  "  · rw [← hre]; exact heq\n",
                  "  refine absurd (hrow.symm.trans (rowOK_false (A := Ggens2) (Xp := Xp)\n"]
    else:
        proof += ["  refine absurd (h.symm.trans (rowOK_false (A := Ggens2) (Xp := Xp)\n"]
    proof += [f"    hword labAB{e} hc ?_ (hcol_cert hu h0 h1) r.2.1 r.2.2)) (by simp)\n",
              "  intro i hi\n",
              "  rcases hi with hlt | h5 | h6\n",
              "  · interval_cases i\n"]
    for j in range(k):
        proof.append(f"    · exact e{j}.symm\n")
    proof.append("    · exact hre\n")
    proof.append("  · subst h5; exact h1.symm\n")
    proof.append("  · subst h6; exact h0.symm\n\n")
    return "".join(out) + "".join(proof)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = SOURCE.read_bytes()
    D = compute()
    a, b = D["a"], D["b"]
    tv2, Xp, lab, wtab = D["tv2"], D["Xp"], D["lab"], D["wtab"]
    orbP = sum(v << (3 * i) for i, v in enumerate(lab))

    out = [
        "-- Generated by export_normalizer.py; do not edit.\n",
        f"-- data/monodromy.json SHA-256: {sha256(raw).hexdigest()}\n",
        "import Sz8.Monodromy.GroupCerts\nimport Sz8.Monodromy.Normalizer\nimport Mathlib.Tactic.IntervalCases\n\n",
        "/-!\n# Certificates for the normalizer of the monodromy group\n\n",
        "`G = ⟨σ₁, σ₂⟩` is 2-transitive on the 65 points, and the last level `H` of the chain\n",
        "in `Sz8.Monodromy.GroupCerts` is the stabiliser of the two base points `0` and `1`; it has\n",
        "order 21. A permutation `u` normalising `G` and fixing both points conjugates `H` to\n",
        "itself. Two tables reduce the induced automorphism of `H` to one of two\n",
        "representatives, and for each of those a search determines `u`: it is equivariant, so\n",
        "it is fixed by the images of the base points of the five `H`-orbits, and every wrong\n",
        "image is rejected by `Sz8.Monodromy.rowOK` — the partial map is not injective, or it breaks\n",
        "the invariant of `Sz8.Monodromy.colour_transport`. Only the identity survives.\n-/\n\n",
        "namespace Sz8.Monodromy\n\nopen Equiv Subgroup\n\n",
        "set_option maxRecDepth 40000\n\n",
        "/-! ## The two-point stabiliser -/\n\n",
        "theorem Hclosed : ∀ s ∈ Ggens2, ∀ o ∈ Gorb2, s o ∈ Gorb2 := by\n"
        "  have h : (Ggens2.all fun s => Gorb2.all fun o => decide (s o ∈ Gorb2)) = true := by\n"
        "    decide +kernel\n"
        "  intro s hs o ho\n"
        "  simpa using (List.all_eq_true.mp ((List.all_eq_true.mp h) s hs)) o ho\n\n",
        "theorem Hto : ∀ o ∈ Gorb2, getAt Gtv2 Gorb2 o 3 = o := by\n"
        "  have h : (Gorb2.all fun o => decide (getAt Gtv2 Gorb2 o 3 = o)) = true := by\n"
        "    decide +kernel\n"
        "  exact fun o ho => of_decide_eq_true (List.all_eq_true.mp h o ho)\n\n",
        "/-- **The two-point stabiliser is exactly the level-2 transversal**: the next level of\n"
        "the chain is trivial, so every element is its own sift. -/\n"
        "theorem Hmem : ∀ x ∈ lclosure Ggens2, x ∈ Gtv2 := fun x hx =>\n"
        "  mem_tv_of_trivial Hclosed (by decide) Hto Gtv2_mem\n"
        "    (fun k hk h3 => eq_one_of_mem_nil (Gfix2 k hk h3)) (by decide) hx\n\n",
        "theorem G1fix0 : ∀ g ∈ lclosure Ggens1, g (0 : Fin 65) = 0 := by\n"
        "  refine fix_of_gens ?_\n"
        "  have h : (Ggens1.all fun g => decide (g (0 : Fin 65) = 0)) = true := by decide +kernel\n"
        "  exact fun g hg => of_decide_eq_true (List.all_eq_true.mp h g hg)\n\n",
        "theorem Hfix0 : ∀ g ∈ lclosure Ggens2, g (0 : Fin 65) = 0 := by\n"
        "  refine fix_of_gens ?_\n"
        "  have h : (Ggens2.all fun g => decide (g (0 : Fin 65) = 0)) = true := by decide +kernel\n"
        "  exact fun g hg => of_decide_eq_true (List.all_eq_true.mp h g hg)\n\n",
        "theorem Hfix1 : ∀ g ∈ lclosure Ggens2, g (1 : Fin 65) = 1 := by\n"
        "  refine fix_of_gens ?_\n"
        "  have h : (Ggens2.all fun g => decide (g (1 : Fin 65) = 1)) = true := by decide +kernel\n"
        "  exact fun g hg => of_decide_eq_true (List.all_eq_true.mp h g hg)\n\n",
        "theorem Hle0 : lclosure Ggens2 ≤ lclosure Ggens0 :=\n"
        "  le_trans (lclosure_le Ggens2_mem) (lclosure_le Ggens1_mem)\n\n",
        "/-! ## Conjugation preserves the chain -/\n\n",
        "theorem norm_stab1 {u : Equiv.Perm (Fin 65)}\n"
        "    (hu : u ∈ normalizer (lclosure Ggens0 : Set (Equiv.Perm (Fin 65))))\n"
        "    (h0 : u (0 : Fin 65) = 0) :\n"
        "    ∀ g ∈ lclosure Ggens1, u * g * u⁻¹ ∈ lclosure Ggens1 := by\n"
        "  intro g hg\n"
        "  refine Gfix0 _ ((Subgroup.mem_normalizer_iff.mp hu g).mp (lclosure_le Ggens1_mem hg)) ?_\n"
        "  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, inv_apply_eq h0, G1fix0 g hg, h0]\n\n",
        "theorem norm_stab2 {u : Equiv.Perm (Fin 65)}\n"
        "    (hu : u ∈ normalizer (lclosure Ggens0 : Set (Equiv.Perm (Fin 65))))\n"
        "    (h0 : u (0 : Fin 65) = 0) (h1 : u (1 : Fin 65) = 1) :\n"
        "    ∀ g ∈ lclosure Ggens2, u * g * u⁻¹ ∈ lclosure Ggens2 := by\n"
        "  intro g hg\n"
        "  refine Gfix1 _ (norm_stab1 hu h0 _ (lclosure_le Ggens2_mem hg)) ?_\n"
        "  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, inv_apply_eq h1, Hfix1 g hg, h1]\n\n",
        "/-! ## The orbit labelling and the pair invariant -/\n\n",
        "/-- The `H`-orbit of each point, three bits per point; `5` and `6` mark the two fixed\n"
        "points `1` and `0`. -/\n"
        f"def orbP : ℕ := {orbP}\n\n",
        "def orbAt (z : Fin 65) : ℕ := (orbP >>> (3 * z.val)) % 8\n\n",
        "theorem orbAt_H : ∀ h ∈ lclosure Ggens2, ∀ z, orbAt (h z) = orbAt z := by\n"
        "  refine label_of_gens ?_\n"
        "  have h : (Ggens2.all fun g => (List.finRange 65).all fun z =>\n"
        "      decide (orbAt (g z) = orbAt z)) = true := by decide +kernel\n"
        "  exact fun g hg z => of_decide_eq_true\n"
        "    (List.all_eq_true.mp ((List.all_eq_true.mp h) g hg) z (List.mem_finRange z))\n\n",
        "/-- The level-1 transversal as a function: `tv1 p` takes `1` to `p`. -/\n"
        "def tv1 (p : Fin 65) : Equiv.Perm (Fin 65) := getAt Gtv1 Gorb1 p\n\n",
        "theorem G1to : ∀ o ∈ Gorb1, tv1 o 1 = o := by\n"
        "  have h : (Gorb1.all fun o => decide (getAt Gtv1 Gorb1 o 1 = o)) = true := by\n"
        "    decide +kernel\n"
        "  exact fun o ho => of_decide_eq_true (List.all_eq_true.mp h o ho)\n\n",
        "theorem Gorb1_iff : ∀ z : Fin 65, z ∈ Gorb1 ↔ z ≠ 0 := by\n"
        "  have h : ((List.finRange 65).all fun z => decide ((z ∈ Gorb1) ↔ z ≠ 0)) = true := by\n"
        "    decide +kernel\n"
        "  exact fun z => of_decide_eq_true (List.all_eq_true.mp h z (List.mem_finRange z))\n\n",
        "/-- **The pair invariant**, for the recorded chain. -/\n"
        "theorem hcol_cert {u : Equiv.Perm (Fin 65)}\n"
        "    (hu : u ∈ normalizer (lclosure Ggens0 : Set (Equiv.Perm (Fin 65))))\n"
        "    (h0 : u (0 : Fin 65) = 0) (h1 : u (1 : Fin 65) = 1) :\n"
        "    ∀ p q : Fin 65, p ∈ Gorb1 → orbAt ((tv1 (u p))⁻¹ (u q)) = orbAt (u ((tv1 p)⁻¹ q)) := by\n"
        "  intro p q hp\n"
        "  refine colour_transport (G₀ := lclosure Ggens1) (H := lclosure Ggens2) orbAt_H\n"
        "    (fun p => Gtv1_mem _) G1to (fun g hg hb => Gfix1 g hg hb) (norm_stab1 hu h0) h1 ?_ p q hp\n"
        "  intro z hz\n"
        "  rw [Gorb1_iff] at hz ⊢\n"
        "  exact fun hcon => hz (u.injective (hcon.trans h0.symm))\n\n",
        "/-! ## The word table -/\n\n",
        "/-- For every point: which `H`-orbit base it belongs to, and a word in `Ggens2`\n"
        "carrying that base to it. -/\n"
        "def Wtab : List (ℕ × List ℕ) :=\n  ["
        + ", ".join("(%d, [%s])" % (i, ", ".join(map(str, w))) for i, w in wtab) + "]\n\n",
        "def wi (z : Fin 65) : ℕ := (Wtab.getD z.val (0, [])).1\n\n",
        "def ww (z : Fin 65) : List ℕ := (Wtab.getD z.val (0, [])).2\n\n",
        "/-- The five orbit base points, then the two fixed points. -/\n"
        f"def Xp : List (Fin 65) := [{', '.join(map(str, Xp))}]\n\n",
        "theorem Wtab_ok : ((List.finRange 65).all fun z =>\n"
        "    decide (z = wordProd Ggens2 (ww z) (Xp.getD (wi z) 0))) = true := by decide +kernel\n\n",
        "theorem hword : ∀ z : Fin 65, z = wordProd Ggens2 (ww z) (Xp.getD (wi z) 0) :=\n"
        "  fun z => of_decide_eq_true (List.all_eq_true.mp Wtab_ok z (List.mem_finRange z))\n\n",
    ]
    out.append(perm_def("A1", D["reps"][1][0], "Image of the first generator of `H` under the "
                        "outer automorphism representative."))
    out.append(perm_def("B1", D["reps"][1][1], "Image of the second generator."))
    out.append("def AB0 : List (Equiv.Perm (Fin 65)) := Ggens2\n\n"
               "def AB1 : List (Equiv.Perm (Fin 65)) := [A1, B1]\n\n")
    out.append("theorem labAB0 : ∀ g ∈ AB0, ∀ z, orbAt (g z) = orbAt z :=\n"
               "  fun g hg => orbAt_H g (mem_lclosure hg)\n\n")
    wa = "[" + ", ".join(map(str, D["wA1"])) + "]"
    wb = "[" + ", ".join(map(str, D["wB1"])) + "]"
    out.append("theorem A1_mem : A1 ∈ lclosure Ggens2 := by\n"
               f"  have h : A1 = wordProd Ggens2 {wa} := by decide +kernel\n"
               "  rw [h]; exact wordProd_mem _ _\n\n")
    out.append("theorem B1_mem : B1 ∈ lclosure Ggens2 := by\n"
               f"  have h : B1 = wordProd Ggens2 {wb} := by decide +kernel\n"
               "  rw [h]; exact wordProd_mem _ _\n\n")
    out.append("theorem labAB1 : ∀ g ∈ AB1, ∀ z, orbAt (g z) = orbAt z := by\n"
               "  intro g hg\n"
               "  simp only [AB1, List.mem_cons, List.not_mem_nil, or_false] at hg\n"
               "  rcases hg with rfl | rfl\n"
               "  · exact orbAt_H _ A1_mem\n"
               "  · exact orbAt_H _ B1_mem\n\n")
    out.append("/-! ## The search -/\n\n")
    for e, (levels, ab) in enumerate([(D["search0"], 0), (D["search1"], 1)]):
        vals = [L[1] for L in levels]
        for k, (rows, surv) in enumerate(levels):
            last = surv is None
            out.append(level_block(Xp, e, k, rows, surv, vals, Xp[k], last))
    out.append("/-! ## Reducing the induced automorphism -/\n\n")
    out.append("/-- The two possible images of the first generator, after conjugating. -/\n"
               "def Aopt : List (Equiv.Perm (Fin 65)) := [Gg2a, Gg2a⁻¹]\n\n"
               "/-- The remaining freedom: the centraliser of `Gg2a` in `H`. -/\n"
               "def Copt : List (Equiv.Perm (Fin 65)) := [1, Gg2a, Gg2a * Gg2a]\n\n"
               "theorem Copt_mem : ∀ i, Copt.getD i 1 ∈ lclosure Ggens2 := by\n"
               "  have hga : Gg2a ∈ lclosure Ggens2 := mem_lclosure (by simp [Ggens2])\n"
               "  intro i\n"
               "  match i with\n"
               "  | 0 => exact one_mem _\n"
               "  | 1 => exact hga\n"
               "  | 2 => exact mul_mem hga hga\n"
               "  | (n + 3) => rw [List.getD_eq_default _ _ (Nat.le_add_left 3 n)]; exact one_mem _\n\n")
    rows = ", ".join(f"(Gt2_{i}, {h}, {w})" for i, (_, h, w) in enumerate(D["red1"]))
    out.append("/-- For every element of `H`: when it has order 3, the index of a transversal\n"
               "element conjugating it to `Gg2a` or to its inverse. -/\n"
               f"def Red1 : List (Equiv.Perm (Fin 65) × ℕ × ℕ) :=\n  [{rows}]\n\n")
    out.append("theorem Red1_cov : Red1.map Prod.fst = Gtv2 := by decide +kernel\n\n")
    out.append("theorem Red1_ok : (Red1.all fun r => decide (r.1 ^ 3 ≠ 1 ∨ r.1 = 1 ∨\n"
               "    (r.2.2 < 2 ∧ (Gtv2.getD r.2.1 1)⁻¹ * r.1 * (Gtv2.getD r.2.1 1) =\n"
               "      Aopt.getD r.2.2 1))) = true := by decide +kernel\n\n")
    r2rows = []
    for aa, bb, ctag, ci, eps, w, n in D["red2"]:
        an = "Gg2a" if aa == D["a"] else "Gg2a⁻¹"
        bn = f"Gt2_{tv2.index(bb)}"
        tag = eps if ctag == 0 else (2 if ctag == 1 else 3)
        r2rows.append(f"({an}, {bn}, {tag}, {ci}, [{', '.join(map(str, w))}], {n})")
    out.append("/-- For every pair (image of the first generator, image of the second): either a\n"
               "power of `Gg2a` conjugating the pair to one of the two representatives, or a word\n"
               "and an exponent on which the pair and the generators disagree. -/\n"
               "def Red2 : List (Equiv.Perm (Fin 65) × Equiv.Perm (Fin 65) × ℕ × ℕ × List ℕ × ℕ) :=\n"
               "  [" + ",\n   ".join(r2rows) + "]\n\n")
    out.append("theorem Red2_cov : Red2.map (fun r => (r.1, r.2.1)) = listPairs Aopt Gtv2 := by\n"
               "  decide +kernel\n\n")
    out.append("theorem Red2_ok : (Red2.all fun r =>\n"
               "    decide ((r.2.2.1 = 0 ∧\n"
               "        (Copt.getD r.2.2.2.1 1)⁻¹ * r.1 * (Copt.getD r.2.2.2.1 1) = Gg2a ∧\n"
               "        (Copt.getD r.2.2.2.1 1)⁻¹ * r.2.1 * (Copt.getD r.2.2.2.1 1) = Gg2b) ∨\n"
               "      (r.2.2.1 = 1 ∧\n"
               "        (Copt.getD r.2.2.2.1 1)⁻¹ * r.1 * (Copt.getD r.2.2.2.1 1) = A1 ∧\n"
               "        (Copt.getD r.2.2.2.1 1)⁻¹ * r.2.1 * (Copt.getD r.2.2.2.1 1) = B1) ∨\n"
               "      (r.2.2.1 = 2 ∧ wordProd Ggens2 r.2.2.2.2.1 ^ r.2.2.2.2.2 = 1 ∧\n"
               "        wordProd [r.1, r.2.1] r.2.2.2.2.1 ^ r.2.2.2.2.2 ≠ 1) ∨\n"
               "      (r.2.2.1 = 3 ∧ wordProd Ggens2 r.2.2.2.2.1 ^ r.2.2.2.2.2 ≠ 1 ∧\n"
               "        wordProd [r.1, r.2.1] r.2.2.2.2.1 ^ r.2.2.2.2.2 = 1))) = true := by\n"
               "  decide +kernel\n\n")
    out.append(SEARCH_TAIL)
    out.append("end Sz8.Monodromy\n")
    path = HERE / "Sz8/Monodromy/NormalizerCerts.lean"
    export_outputs({path: "".join(out)}, check=args.check, root=HERE,
                   exporter="export_normalizer", sources=[F_SOURCE, SOURCE])
    print(f"{'Checked' if args.check else 'Exported'} normalizer certificates: "
          f"{len(D['search0'])} + {len(D['search1'])} search levels, "
          f"{len(D['red1'])} + {len(D['red2'])} reduction rows")


if __name__ == "__main__":
    main()
