#!/usr/bin/env python3
"""Export verified stabilizer-chain certificates for the recorded monodromy group.

Emits `Sz8/Monodromy/GroupCerts.lean`: a base and strong generating set for `G = ⟨σ₁, σ₂⟩` and
for its derived subgroup, with breadth-first transversals, Schreier-generator sift
certificates, and the conjugation certificates identifying the derived subgroup.
Run from any directory; --check compares the generated file without modifying it.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from export_provenance import export_outputs
from sympy.combinatorics import Permutation, PermutationGroup

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "data/monodromy.json"
F_SOURCE = HERE.parent / "data/f.json"

N = 65
ID = tuple(range(N))


def mul(x, y):
    """`(x * y) i = x (y i)`, matching Lean's composition order."""
    return tuple(x[y[i]] for i in range(N))


def inv(x):
    r = [0] * N
    for i, j in enumerate(x):
        r[j] = i
    return tuple(r)


def comm(a, b):
    return mul(mul(a, b), mul(inv(a), inv(b)))


def order(gens):
    if not gens:
        return 1
    return PermutationGroup([Permutation(list(g)) for g in gens]).order()


def pack(xs):
    v = 0
    for i, x in enumerate(xs):
        v |= x << (7 * i)
    return v


def bfs(gens, b):
    """Orbit of `b` in breadth-first order with its tree: `(generator, parent position)`."""
    orbit, tree, idx = [b], [], {b: 0}
    i = 0
    while i < len(orbit):
        for gi, g in enumerate(gens):
            x = g[orbit[i]]
            if x not in idx:
                idx[x] = len(orbit)
                orbit.append(x)
                tree.append((gi, i))
        i += 1
    return orbit, tree, idx


def schreier(gens, b):
    orbit, tree, idx = bfs(gens, b)
    tv = [ID]
    for gi, p in tree:
        tv.append(mul(gens[gi], tv[p]))
    gs = []
    for si, s in enumerate(gens):
        for oi, o in enumerate(orbit):
            g = mul(inv(tv[idx[s[o]]]), mul(s, tv[oi]))
            assert g[b] == b, "a Schreier generator must fix the base point"
            gs.append((si, oi, g))
    return orbit, tree, idx, tv, gs


def build_chain(gens, bases):
    """A stabilizer chain whose deeper generators are Schreier generators of the level above."""
    levels, cur = [], list(gens)
    for b in bases:
        orbit, tree, idx, tv, gs = schreier(cur, b)
        target = order([g for _, _, g in gs])
        seen, cand = set(), []
        for si, oi, g in gs:
            if g == ID or g in seen:
                continue
            seen.add(g)
            cand.append((si, oi, g))
        chosen = []
        for c in cand:
            if order([g for _, _, g in chosen]) == target:
                break
            chosen.append(c)
        again = True
        while again:
            again = False
            for c in list(chosen):
                rest = [x for x in chosen if x is not c]
                if order([g for _, _, g in rest]) == target:
                    chosen, again = rest, True
                    break
        levels.append(dict(base=b, S=cur, orbit=orbit, tree=tree, idx=idx, tv=tv, sch=gs,
                           wit=[(si, oi) for si, oi, _ in chosen]))
        cur = [g for _, _, g in chosen]
    levels.append(dict(base=None, S=cur, orbit=None))
    return levels


def sift(levels, g, start=0):
    """Indices `(p, q, r)` with `g = tv_start[p] * (tv_{start+1}[q] * tv_{start+2}[r])`."""
    cur, out = g, []
    for j in (start, start + 1, start + 2):
        if j >= len(levels) - 1:
            out.append(0)
            continue
        L = levels[j]
        p = L["idx"][cur[L["base"]]]
        out.append(p)
        cur = mul(inv(L["tv"][p]), cur)
    assert cur == ID, "sift did not reach the identity"
    return tuple(out)


def perm_def(name, p, doc):
    return (f"/-- {doc} -/\ndef {name} : Equiv.Perm (Fin 65) :="
            f" ofPacked {pack(p)} {pack(inv(p))}\n\n")


def pairs_lit(ps):
    return "[" + ", ".join(f"({a}, {b})" for a, b in ps) + "]"


def chain_section(tag, levels, gen_names, doc):
    """Definitions, transversal certificates and chain steps for one group."""
    out, depth = [], len(levels) - 1
    for i, L in enumerate(levels[1:-1], start=1):
        for j, g in enumerate(L["S"]):
            out.append(perm_def(f"{tag}g{i}{'ab'[j]}", g,
                                f"Generator {j + 1} of the {i}-point stabiliser."))
    for i, L in enumerate(levels):
        names = gen_names if i == 0 else [f"{tag}g{i}{'ab'[j]}" for j in range(len(L["S"]))]
        out.append(f"/-- Generators of the {i}-point stabiliser. -/\n"
                   f"def {tag}gens{i} : List (Equiv.Perm (Fin 65)) := [{', '.join(names)}]\n\n")
    for i, L in enumerate(levels[:-1]):
        out.append(f"/-- The orbit of `{L['base']}`, breadth first. -/\n"
                   f"def {tag}orb{i} : List (Fin 65) := [{', '.join(map(str, L['orbit']))}]\n\n")
        entries = ", ".join(f"({si}, {L['orbit'][oi]}, {p[0]}, {p[1]})"
                            for (si, oi, _), p in zip(L["sch"], L["pairs"]))
        out.append(f"/-- Schreier generators of level {i}: for each generator index and orbit\n"
                   f"point, the two deeper transversal indices whose product is the generator. -/\n"
                   f"def {tag}cert{i} : List (ℕ × Fin 65 × ℕ × ℕ) := [{entries}]\n\n")
        for k, t in enumerate(L["tv"]):
            out.append(perm_def(f"{tag}t{i}_{k}", t, f"Transversal element {k} of level {i}."))
        words = [[]]
        for gi, par in L["tree"]:
            words.append([gi] + words[par])
        out.append(f"/-- The level-{i} transversal with a word for each entry. -/\n"
                   f"def {tag}tvw{i} : List (Equiv.Perm (Fin 65) × List ℕ) := ["
                   + ", ".join(f"({tag}t{i}_{k}, [{', '.join(map(str, w))}])"
                               for k, w in enumerate(words)) + "]\n\n")
        out.append(f"/-- The level-{i} transversal, in orbit order. -/\n"
                   f"def {tag}tv{i} : List (Equiv.Perm (Fin 65)) := {tag}tvw{i}.map Prod.fst\n\n")
        out.append(f"theorem {tag}tv{i}_mem : ∀ k, {tag}tv{i}.getD k 1 ∈ lclosure {tag}gens{i} :=\n"
                   f"  tvWords_mem rfl (by decide +kernel)\n\n")
    for i, L in enumerate(levels[1:], start=1):
        prev = levels[i - 1]
        if not L["S"]:
            out.append(f"theorem {tag}gens{i}_mem : ∀ x ∈ {tag}gens{i}, "
                       f"x ∈ lclosure {tag}gens{i-1} := by simp [{tag}gens{i}]\n\n")
            continue
        cases = []
        for j, (si, oi) in enumerate(prev["wit"]):
            gname, pv = f"{tag}g{i}{'ab'[j]}", f"{tag}gens{i-1}.getD {si} 1"
            at, pt = (f"getAt {tag}tv{i-1} {tag}orb{i-1}",
                      f"({tag}orb{i-1}.getD {oi} {prev['base']})")
            cases.append(f"  · have h : {gname} = ({at} ({pv} {pt}))⁻¹ * {pv} * {at} {pt} := by\n"
                         f"      decide +kernel\n    rw [h]\n"
                         f"    exact schreier_mem _ {tag}tv{i-1}_mem (getD_mem_self (by decide)) _")
        out.append(f"/-- The level-{i} generators are Schreier generators of level {i-1}. -/\n"
                   f"theorem {tag}gens{i}_mem : ∀ x ∈ {tag}gens{i}, "
                   f"x ∈ lclosure {tag}gens{i-1} := by\n  intro x hx\n"
                   f"  simp only [{tag}gens{i}, List.mem_cons, List.not_mem_nil, or_false] at hx\n"
                   f"  rcases hx with " + " | ".join(["rfl"] * len(L["S"])) + "\n"
                   + "\n".join(cases) + "\n\n")
    nil = "(fun i => getD_mem_of (by simp) i)"
    for i, L in enumerate(levels[:-1]):
        w1 = f"{tag}tv{i+1}" if i + 1 < depth else "[]"
        w2 = f"{tag}tv{i+2}" if i + 2 < depth else "[]"
        hw1 = f"{tag}tv{i+1}_mem" if i + 1 < depth else nil
        hw2 = (f"(fun i => lclosure_le {tag}gens{i+2}_mem ({tag}tv{i+2}_mem i))"
               if i + 2 < depth else nil)
        b, n = L["base"], len(L["orbit"])
        card_ty = (f"Nat.card (lclosure {tag}gens{i}) = "
                   f"{n} * Nat.card (lclosure {tag}gens{i+1})")
        fix_ty = (f"∀ k ∈ lclosure {tag}gens{i}, k ({b} : Fin 65) = {b} → "
                  f"k ∈ lclosure {tag}gens{i+1}")
        out.append(f"/-- Chain step {i}: the orbit of `{b}` under the {i}-point stabiliser has\n"
                   f"{n} points, and its stabiliser of `{b}` is the next level. -/\n"
                   f"theorem {tag}full{i} : {card_ty} ∧\n    {fix_ty} := by\n"
                   f"  have h := chain_step (S := {tag}gens{i}) (b := {b}) "
                   f"(O := {tag}orb{i})\n"
                   f"    (TV := {tag}tv{i}) (S' := {tag}gens{i+1}) (W₁ := {w1}) (W₂ := {w2})\n"
                   f"    (cert := {tag}cert{i}) {tag}tv{i}_mem {hw1} {hw2}\n"
                   + "    (by decide +kernel) (by decide +kernel) (by decide +kernel)\n"
                   + "    (by decide +kernel) (by decide +kernel) (by decide +kernel)\n"
                   + "    (by decide +kernel) (by decide +kernel) (by decide +kernel)\n"
                   f"    {tag}gens{i+1}_mem\n  exact h\n\n"
                   f"theorem {tag}step{i} : {card_ty} := {tag}full{i}.1\n\n"
                   f"/-- Anything in the {i}-point stabiliser fixing `{b}` lies in the next level. -/\n"
                   f"theorem {tag}fix{i} : {fix_ty} := {tag}full{i}.2\n\n")
    total = 1
    for L in levels[:-1]:
        total *= len(L["orbit"])
    out.append(f"/-- {doc} -/\ntheorem {tag}card : Nat.card (lclosure {tag}gens0) = {total} := by\n"
               f"  rw [" + ", ".join(f"{tag}step{i}" for i in range(depth))
               + f", show {tag}gens{depth} = ([] : List (Equiv.Perm (Fin 65))) from rfl,"
               + " card_lclosure_nil]\n\n")
    return "".join(out), total


def commutator_section(g_levels, n_levels, words):
    """Identify `⟨Nc1, Nc2⟩` with the derived subgroup of `G`."""
    out = ["theorem Nle1 : lclosure Ngens1 ≤ lclosure Ngens0 := lclosure_le Ngens1_mem\n\n",
           "theorem Nle2 : lclosure Ngens2 ≤ lclosure Ngens0 :="
           " (lclosure_le Ngens2_mem).trans Nle1\n\n"]
    for j, (name, expr) in enumerate(words, start=1):
        out.append(f"/-- The {'first' if j == 1 else 'second'} generator of `N` is a commutator"
                   f" of the meridians. -/\ntheorem Nc{j}_eq : Nc{j} = {expr} := by"
                   f" decide +kernel\n\n")
    # conjugation certificates
    s1, s2 = g_levels[0]["S"]
    ngens = n_levels[0]["S"]
    names = {0: "Gs1", 1: "Gs2"}
    certs = []
    for si, s in enumerate([s1, s2]):
        for xi, x in enumerate(ngens):
            for direction, conj in (("", s), ("i", inv(s))):
                y = mul(mul(conj, x), inv(conj))
                p, q, r = sift(n_levels, y, 0)
                lhs = (f"{names[si]} * Nc{xi+1} * {names[si]}⁻¹" if direction == ""
                       else f"{names[si]}⁻¹ * Nc{xi+1} * {names[si]}⁻¹⁻¹")
                nm = f"Nconj_{si+1}_{xi+1}{direction}"
                certs.append(nm)
                out.append(f"theorem {nm} : {lhs} ∈ lclosure Ngens0 :=\n"
                           f"  mem_of_sift₃ (Ntv0_mem {p}) (Nle1 (Ntv1_mem {q}))"
                           f" (Nle2 (Ntv2_mem {r}))\n    (by decide +kernel)\n\n")
    out.append("""/-- `G` normalises `N`: both directions of conjugation are certified on generators. -/
theorem G_normalizes_N : ∀ s ∈ Ggens0,
    s ∈ Subgroup.normalizer (lclosure Ngens0 : Set (Equiv.Perm (Fin 65))) := by
  intro s hs
  simp only [Ggens0, List.mem_cons, List.not_mem_nil, or_false] at hs
  have hN : ∀ x ∈ Ngens0, x = Nc1 ∨ x = Nc2 := by
    intro x hx
    simpa only [Ngens0, List.mem_cons, List.not_mem_nil, or_false] using hx
  rcases hs with rfl | rfl
  · refine mem_normalizer_of (fun x hx => ?_) (fun x hx => ?_)
    · rcases hN x hx with rfl | rfl
      exacts [Nconj_1_1, Nconj_1_2]
    · rcases hN x hx with rfl | rfl
      exacts [Nconj_1_1i, Nconj_1_2i]
  · refine mem_normalizer_of (fun x hx => ?_) (fun x hx => ?_)
    · rcases hN x hx with rfl | rfl
      exacts [Nconj_2_1, Nconj_2_2]
    · rcases hN x hx with rfl | rfl
      exacts [Nconj_2_1i, Nconj_2_2i]

/-- The commutators of the generators of `G` lie in `N`. -/
theorem Nbase : ∀ a ∈ Ggens0, ∀ b ∈ Ggens0, ⁅a, b⁆ ∈ lclosure Ngens0 := by
  intro a ha b hb
  simp only [Ggens0, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  have h1 : Nc1 ∈ lclosure Ngens0 := mem_lclosure (by simp [Ngens0])
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · have h : ⁅Gs1, Gs1⁆ = 1 := by decide +kernel
    rw [h]; exact one_mem _
  · rw [← Nc1_eq]; exact h1
  · have h : ⁅Gs2, Gs1⁆ = Nc1⁻¹ := by decide +kernel
    rw [h]; exact inv_mem h1
  · have h : ⁅Gs2, Gs2⁆ = 1 := by decide +kernel
    rw [h]; exact one_mem _

/-- `N` is contained in the derived subgroup, its generators being commutators. -/
theorem Nsub : lclosure Ngens0 ≤ ⁅lclosure Ggens0, lclosure Ggens0⁆ := by
  refine lclosure_le (fun x hx => ?_)
  have hs1 : Gs1 ∈ lclosure Ggens0 := mem_lclosure (by simp [Ggens0])
  have hs2 : Gs2 ∈ lclosure Ggens0 := mem_lclosure (by simp [Ggens0])
  simp only [Ngens0, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · rw [Nc1_eq]; exact Subgroup.commutator_mem_commutator hs1 hs2
  · rw [Nc2_eq]; exact Subgroup.commutator_mem_commutator hs1 (mul_mem hs2 hs2)

/-- **The derived subgroup of `G` is `N`.** -/
theorem commutator_eq : ⁅lclosure Ggens0, lclosure Ggens0⁆ = lclosure Ngens0 :=
  le_antisymm (commutator_lclosure_le G_normalizes_N Nbase) Nsub

theorem Ncomm_card :
    Nat.card (⁅lclosure Ggens0, lclosure Ggens0⁆ : Subgroup (Equiv.Perm (Fin 65))) = 29120 := by
  rw [commutator_eq]; exact Ncard

/-- The certified generators are the recorded meridian permutations. -/
theorem closure_sigma_eq :
    Subgroup.closure ({σ₁, σ₂} : Set (Equiv.Perm (Fin 65))) = lclosure Ggens0 := by
  have e₁ : Gs1 = σ₁ := by decide +kernel
  have e₂ : Gs2 = σ₂ := by decide +kernel
  have h : ({σ₁, σ₂} : Set (Equiv.Perm (Fin 65))) = {x | x ∈ Ggens0} := by
    ext x; simp [Ggens0, e₁, e₂]
  rw [h, lclosure]

/-- **The group generated by the recorded meridians has order 87360.** -/
theorem card_closure_sigma :
    Nat.card (Subgroup.closure ({σ₁, σ₂} : Set (Equiv.Perm (Fin 65)))) = 87360 := by
  rw [closure_sigma_eq]; exact Gcard

/-- **Its derived subgroup has order 29120.** -/
theorem card_commutator_sigma :
    Nat.card (⁅Subgroup.closure ({σ₁, σ₂} : Set (Equiv.Perm (Fin 65))),
      Subgroup.closure ({σ₁, σ₂} : Set (Equiv.Perm (Fin 65)))⁆ :
        Subgroup (Equiv.Perm (Fin 65))) = 29120 := by
  rw [closure_sigma_eq]; exact Ncomm_card

""")
    return "".join(out)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = SOURCE.read_bytes()
    data = json.loads(raw)
    assert data["indexing"] == "zero-based image lists"
    assert data["source_f_sha256"] == sha256(F_SOURCE.read_bytes()).hexdigest()
    s1 = tuple(data["permutations"]["gamma_1"])
    s2 = tuple(data["permutations"]["gamma_2"])

    g_levels = build_chain([s1, s2], [0, 1, 3])
    nc1, nc2 = comm(s1, s2), comm(s1, mul(s2, s2))
    n_levels = build_chain([nc1, nc2], [0, 1, 2])
    for levels in (g_levels, n_levels):
        for i, L in enumerate(levels[:-1]):
            L["pairs"] = [sift(levels, g, i + 1) for _, _, g in L["sch"]]

    out = ("-- Generated by export_groups.py; do not edit.\n"
           f"-- data/monodromy.json SHA-256: {sha256(raw).hexdigest()}\n"
           "import Sz8.Monodromy.PermChain\nimport Sz8.Monodromy.PackedPerm\n"
           "import Sz8.Monodromy.MonodromyData\n\n"
           "/-!\n# Order certificates for the recorded monodromy group\n\n"
           "A base and strong generating set for `G = ⟨σ₁, σ₂⟩` and for its derived subgroup,\n"
           "in the form `Sz8.Monodromy.card_step` consumes: breadth-first transversals with a word\n"
           "for each entry, and, for every Schreier generator, the two deeper transversal\n"
           "indices whose product it is. The kernel replays every check.\n\n"
           "`G` has order `65 · 64 · 21 = 87360` and its derived subgroup order\n"
           "`65 · 64 · 7 = 29120`. That the derived subgroup is the one generated by the two\n"
           "recorded commutators is certified by conjugating generators in both directions.\n\n"
           "Permutations are packed into single natural numbers (`Sz8.Monodromy.ofPacked`), which\n"
           "the kernel reads with two GMP operations instead of walking a 65-entry vector.\n-/\n\n"
           "namespace Sz8.Monodromy\n\nopen Equiv Subgroup\nopen scoped commutatorElement\n\n"
           "set_option maxRecDepth 10000\n\n")
    out += perm_def("Gs1", s1, "Packed copy of the recorded permutation `σ₁`.")
    out += perm_def("Gs2", s2, "Packed copy of the recorded permutation `σ₂`.")
    body, gtot = chain_section("G", g_levels, ["Gs1", "Gs2"],
                               "The recorded meridians generate a group of order 87360.")
    out += body
    out += perm_def("Nc1", nc1, "The commutator `⁅σ₁, σ₂⁆`.")
    out += perm_def("Nc2", nc2, "The commutator `⁅σ₁, σ₂²⁆`.")
    body, ntot = chain_section("N", n_levels, ["Nc1", "Nc2"],
                               "The two recorded commutators generate a group of order 29120.")
    out += body
    out += commutator_section(g_levels, n_levels,
                              [("Nc1", "⁅Gs1, Gs2⁆"), ("Nc2", "⁅Gs1, Gs2 * Gs2⁆")])
    out += "end Sz8.Monodromy\n"
    assert gtot == 87360 and ntot == 29120, (gtot, ntot)

    path = HERE / "Sz8/Monodromy/GroupCerts.lean"
    export_outputs({path: out}, check=args.check, root=HERE, exporter="export_groups",
                   sources=[F_SOURCE, SOURCE])
    print(f"{'Checked' if args.check else 'Exported'} stabilizer chains: "
          f"|G| = {gtot} = 65·64·21, |[G,G]| = {ntot} = 65·64·7")


if __name__ == "__main__":
    main()
