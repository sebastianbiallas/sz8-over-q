#!/usr/bin/env python3
"""Export the certificates behind `Sz8.Monodromy.eq_of_ninetyOne_dvd`.

Emits `Sz8/Monodromy/NinetyOneCerts.lean`: an element `Pc` of order 13 in the derived subgroup
`N = ⟨⁅σ₁, σ₂⁆, ⁅σ₁, σ₂²⁆⟩`, the 52 elements of `N` normalising `⟨Pc⟩`, a table sending every
ordered pair of distinct points to one of them together with an orbit representative, and, for
each of the 80 representatives, a generator of the two-point stabiliser it fixes plus words
expressing the two generators of `N` in that generator and `Pc`.

Run from any directory; --check compares the generated file without modifying it.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from export_provenance import export_outputs
from export_groups import (F_SOURCE, SOURCE, ID, build_chain, comm, inv, mul, pack, sift)

HERE = Path(__file__).resolve().parent


def order_of(x):
    k, y = 1, x
    while y != ID:
        y = mul(y, x)
        k += 1
    return k


def elements(gens):
    seen, frontier = {ID}, [ID]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mul(g, x)
                if y not in seen:
                    seen.add(y)
                    nxt.append(y)
        frontier = nxt
    return sorted(seen)


def words(c, q, targets):
    """Shortest words in `[c, c⁻¹, q, q⁻¹]`, as index lists, for each target."""
    gens = [c, inv(c), q, inv(q)]
    found, seen, frontier = {}, {ID: []}, [ID]
    while frontier and len(found) < len(targets):
        nxt = []
        for x in frontier:
            wx = seen[x]
            for i, g in enumerate(gens):
                y = mul(x, g)
                if y not in seen:
                    seen[y] = wx + [i]
                    nxt.append(y)
                    if y in targets:
                        found[y] = seen[y]
        frontier = nxt
    return [found[t] for t in targets]


def compute():
    data = json.loads(SOURCE.read_bytes())
    assert data["indexing"] == "zero-based image lists"
    assert data["source_f_sha256"] == sha256(F_SOURCE.read_bytes()).hexdigest()
    s1 = tuple(data["permutations"]["gamma_1"])
    s2 = tuple(data["permutations"]["gamma_2"])
    nc1, nc2 = comm(s1, s2), comm(s1, mul(s2, s2))
    levels = build_chain([nc1, nc2], [0, 1, 2])
    q0 = levels[2]["S"][0]
    assert order_of(q0) == 7 and q0[0] == 0 and q0[1] == 1

    elts = elements([nc1, nc2])
    assert len(elts) == 29120
    c = next(x for x in elts if order_of(x) == 13)
    powers = [ID]
    for _ in range(12):
        powers.append(mul(powers[-1], c))
    power_index = {p: i for i, p in enumerate(powers)}

    # the normaliser of ⟨c⟩ in N, and the power each element conjugates c to
    norm = [x for x in elts if mul(mul(inv(x), c), x) in power_index]
    assert len(norm) == 52
    pw = [power_index[mul(mul(inv(x), c), x)] for x in norm]

    # orbits of that normaliser on unordered pairs of distinct points; the certificate only
    # ever asks that a representative's stabiliser generator fix both points, so the two
    # orderings of a pair share a representative
    unord = [(a, b) for a in range(65) for b in range(a + 1, 65)]
    rep_of, reps, wit = {}, [], {}
    inv_index = {x: i for i, x in enumerate(norm)}
    for p in unord:
        if p in rep_of:
            continue
        r = len(reps)
        reps.append(p)
        for x in norm:
            u, v = x[p[0]], x[p[1]]
            img = (u, v) if u < v else (v, u)
            if img not in rep_of:
                rep_of[img] = r
                wit[img] = inv_index[inv(x)]
    assert len(reps) == 48
    table = {}
    for a in range(65):
        for b in range(65):
            if a == b:
                continue
            key = (a, b) if a < b else (b, a)
            i, r = wit[key], rep_of[key]
            w = norm[i]
            assert {w[a], w[b]} == set(reps[r])
            table[(a, b)] = (i, r)

    # the two-point stabiliser attached to each representative, and words for N's generators
    tv0, idx0 = levels[0]["tv"], levels[0]["idx"]
    tv1, idx1 = levels[1]["tv"], levels[1]["idx"]

    def mapper(a, b):
        t0 = tv0[idx0[a]]
        u = mul(t0, tv1[idx1[inv(t0)[b]]])
        assert u[0] == a and u[1] == b
        return u

    qs, ws = [], []
    for a, b in reps:
        u = mapper(a, b)
        q = mul(mul(u, q0), inv(u))
        assert order_of(q) == 7 and q[a] == a and q[b] == b
        qs.append(q)
        ws.append(words(c, q, (nc1, nc2)))
    return dict(levels=levels, c=c, norm=norm, pw=pw, reps=reps, qs=qs, ws=ws, table=table,
                nc1=nc1, nc2=nc2)


def perm_def(name, p, doc):
    return (f"/-- {doc} -/\ndef {name} : Equiv.Perm (Fin 65) :="
            f" ofPacked {pack(p)} {pack(inv(p))}\n\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = SOURCE.read_bytes()
    D = compute()
    levels = D["levels"]
    sift_of = {}

    def sift3(x):
        return sift(levels, x)

    out = [
        "-- Generated by export_sylow.py; do not edit.\n",
        f"-- data/monodromy.json SHA-256: {sha256(raw).hexdigest()}\n",
        "import Sz8.Monodromy.GroupCerts\nimport Sz8.Monodromy.NinetyOne\n\n",
        "/-!\n# Certificates for the order-91 step\n\n",
        "`Sz8.Monodromy.eq_of_card_dvd` reduces `H ≤ N` with `91 ∣ |H|` to `H = N` given: the\n",
        "two-point stabiliser of `(0, 1)` in `N` (the last level of the chain in\n",
        "`Sz8.Monodromy.GroupCerts`), an element `Pc` of order 13, and, for every ordered pair of\n",
        "distinct points, an element of `N` normalising `⟨Pc⟩` that moves the pair to one of 80\n",
        "orbit representatives, together with a generator of the stabiliser of that\n",
        "representative and words showing that it and `Pc` generate `N`.\n-/\n\n",
        "namespace Sz8.Monodromy\n\nopen Equiv Subgroup\n\n",
        "set_option maxRecDepth 20000\n\n",
        "/-- **The two-point stabiliser of `(0, 1)` in `N` is the last level of the chain.** -/\n",
        "theorem Nstab01 : ∀ k ∈ lclosure Ngens0, k 0 = 0 → k 1 = 1 → k ∈ lclosure Ngens2 :=\n",
        "  fun k hk h0 h1 => Nfix1 k (Nfix0 k hk h0) h1\n\n",
        "/-- It has order 7. -/\n",
        "theorem NQcard : Nat.card (lclosure Ngens2) = 7 := by\n",
        "  rw [Nstep2, show Ngens3 = ([] : List (Equiv.Perm (Fin 65))) from rfl, card_lclosure_nil]\n\n",
    ]
    c = D["c"]
    out.append(perm_def("Pc", c, "An element of order 13 in `N`."))
    p, q, r = sift3(c)
    out.append("theorem Pc_mem : Pc ∈ lclosure Ngens0 :=\n"
               f"  mem_of_sift₃ (Ntv0_mem {p}) (Nle1 (Ntv1_mem {q})) (Nle2 (Ntv2_mem {r}))"
               " (by decide +kernel)\n\n")
    out.append("theorem Pc_card : Nat.card (zpowers Pc) = 13 := by\n"
               "  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩\n"
               "  rw [Nat.card_zpowers, orderOf_eq_prime (by decide +kernel : Pc ^ 13 = 1)"
               " (by decide +kernel : Pc ≠ 1)]\n\n")

    norm, pw = D["norm"], D["pw"]
    for i, w in enumerate(norm):
        out.append(perm_def(f"Wp{i}", w, f"Normalising element {i}."))
    rows = []
    for i, w in enumerate(norm):
        a, b, cc = sift3(w)
        rows.append(f"(Wp{i}, {a}, {b}, {cc}, {pw[i]})")
    out.append("/-- The 52 elements of `N` normalising `⟨Pc⟩`: each with its sift through the\n"
               "chain and the power of `Pc` it conjugates `Pc` to. -/\n"
               "def Wdata : List (Equiv.Perm (Fin 65) × ℕ × ℕ × ℕ × ℕ) :=\n  ["
               + ", ".join(rows) + "]\n\n")
    out.append("def wdflt : Equiv.Perm (Fin 65) × ℕ × ℕ × ℕ × ℕ := (1, 0, 0, 0, 0)\n\n")
    out.append("theorem Wdata_sift : Wdata.all (fun z => decide (z.1 =\n"
               "    Ntv0.getD z.2.1 1 * (Ntv1.getD z.2.2.1 1 * Ntv2.getD z.2.2.2.1 1))) = true := by\n"
               "  decide +kernel\n\n")
    out.append("theorem Wdata_pow : Wdata.all (fun z =>\n"
               "    decide (z.1⁻¹ * Pc * z.1 = Pc ^ z.2.2.2.2)) = true := by decide +kernel\n\n")
    out.append("theorem Wdata_mem : ∀ z ∈ Wdata, z.1 ∈ lclosure Ngens0 := by\n"
               "  intro z hz\n"
               "  have h : z.1 = Ntv0.getD z.2.1 1 * (Ntv1.getD z.2.2.1 1 * Ntv2.getD z.2.2.2.1 1) :=\n"
               "    of_decide_eq_true (List.all_eq_true.mp Wdata_sift z hz)\n"
               "  exact mem_of_sift₃ (Ntv0_mem _) (Nle1 (Ntv1_mem _)) (Nle2 (Ntv2_mem _)) h\n\n")
    out.append("theorem Wdata_zpow : ∀ z ∈ Wdata, z.1⁻¹ * Pc * z.1 ∈ zpowers Pc := by\n"
               "  intro z hz\n"
               "  have h : z.1⁻¹ * Pc * z.1 = Pc ^ z.2.2.2.2 :=\n"
               "    of_decide_eq_true (List.all_eq_true.mp Wdata_pow z hz)\n"
               "  rw [h]\n"
               "  exact ⟨(z.2.2.2.2 : ℤ), by simp⟩\n\n")

    reps, qs, ws = D["reps"], D["qs"], D["ws"]
    for i, qq in enumerate(qs):
        a, b = reps[i]
        out.append(perm_def(f"Rq{i}", qq,
                            f"Generator of the stabiliser of the pair `({a}, {b})`."))
    rows = []
    for i, qq in enumerate(qs):
        a, b, cc = sift3(qq)
        w1 = "[" + ", ".join(map(str, ws[i][0])) + "]"
        w2 = "[" + ", ".join(map(str, ws[i][1])) + "]"
        rows.append(f"(Rq{i}, {a}, {b}, {cc}, {w1}, {w2})")
    out.append("/-- The 80 orbit representatives: a generator of the two-point stabiliser it\n"
               "fixes, its sift through the chain, and words for the two generators of `N`. -/\n"
               "def RepData : List (Equiv.Perm (Fin 65) × ℕ × ℕ × ℕ × List ℕ × List ℕ) :=\n  ["
               + ",\n   ".join(rows) + "]\n\n")
    out.append("def rdflt : Equiv.Perm (Fin 65) × ℕ × ℕ × ℕ × List ℕ × List ℕ :="
               " (1, 0, 0, 0, [], [])\n\n")
    out.append("theorem RepData_sift : RepData.all (fun z => decide (z.1 =\n"
               "    Ntv0.getD z.2.1 1 * (Ntv1.getD z.2.2.1 1 * Ntv2.getD z.2.2.2.1 1))) = true := by\n"
               "  decide +kernel\n\n")
    out.append("theorem RepData_word : RepData.all (fun z =>\n"
               "    decide (Nc1 = wordProd [Pc, Pc⁻¹, z.1, z.1⁻¹] z.2.2.2.2.1 ∧\n"
               "      Nc2 = wordProd [Pc, Pc⁻¹, z.1, z.1⁻¹] z.2.2.2.2.2)) = true := by decide +kernel\n\n")
    out.append("theorem RepData_mem : ∀ z ∈ RepData, z.1 ∈ lclosure Ngens0 := by\n"
               "  intro z hz\n"
               "  have h : z.1 = Ntv0.getD z.2.1 1 * (Ntv1.getD z.2.2.1 1 * Ntv2.getD z.2.2.2.1 1) :=\n"
               "    of_decide_eq_true (List.all_eq_true.mp RepData_sift z hz)\n"
               "  exact mem_of_sift₃ (Ntv0_mem _) (Nle1 (Ntv1_mem _)) (Nle2 (Ntv2_mem _)) h\n\n")
    out.append("theorem RepData_gens : ∀ z ∈ RepData, ∀ y ∈ Ngens0,\n"
               "    y ∈ lclosure [Pc, Pc⁻¹, z.1, z.1⁻¹] := by\n"
               "  intro z hz y hy\n"
               "  have h : Nc1 = wordProd [Pc, Pc⁻¹, z.1, z.1⁻¹] z.2.2.2.2.1 ∧\n"
               "      Nc2 = wordProd [Pc, Pc⁻¹, z.1, z.1⁻¹] z.2.2.2.2.2 :=\n"
               "    of_decide_eq_true (List.all_eq_true.mp RepData_word z hz)\n"
               "  simp only [Ngens0, List.mem_cons, List.not_mem_nil, or_false] at hy\n"
               "  rcases hy with rfl | rfl\n"
               "  · rw [h.1]; exact wordProd_mem _ _\n"
               "  · rw [h.2]; exact wordProd_mem _ _\n\n")

    table = D["table"]
    rows = []
    for a in range(65):
        for b in range(65):
            i, r = table.get((a, b), (0, 0))
            rows.append(f"({a}, {b}, {i}, {r})")
    out.append("/-- For every ordered pair of points, in the order of `ptPairs 65`: an index\n"
               "into `Wdata` and one into `RepData`. Diagonal entries are unused. -/\n"
               "def Tab : List (Fin 65 × Fin 65 × ℕ × ℕ) :=\n  ["
               + ",\n   ".join(rows) + "]\n\n")
    out.append("def tabW (z : Fin 65 × Fin 65 × ℕ × ℕ) : Equiv.Perm (Fin 65) :="
               " (Wdata.getD z.2.2.1 wdflt).1\n\n"
               "def tabQ (z : Fin 65 × Fin 65 × ℕ × ℕ) : Equiv.Perm (Fin 65) :="
               " (RepData.getD z.2.2.2 rdflt).1\n\n")
    out.append("theorem Tab_cov : Tab.map (fun z => (z.1, z.2.1)) = ptPairs 65 := by decide +kernel\n\n")
    out.append("theorem Tab_ok : Tab.all (fun z => decide (z.1 = z.2.1 ∨\n"
               "    (z.2.2.1 < Wdata.length ∧ z.2.2.2 < RepData.length ∧\n"
               "      tabQ z (tabW z z.1) = tabW z z.1 ∧\n"
               "      tabQ z (tabW z z.2.1) = tabW z z.2.1))) = true := by decide +kernel\n\n")
    out.append("/-- **The table hypothesis of `eq_of_card_dvd`.** -/\n"
               "theorem htab_cert : ∀ a b : Fin 65, a ≠ b →\n"
               "    ∃ W ∈ lclosure Ngens0, ∃ q ∈ lclosure Ngens0,\n"
               "      W⁻¹ * Pc * W ∈ zpowers Pc ∧ q (W a) = W a ∧ q (W b) = W b ∧\n"
               "      ∀ y ∈ Ngens0, y ∈ lclosure [Pc, Pc⁻¹, q, q⁻¹] := by\n"
               "  intro a b hab\n"
               "  have hmem : (a, b) ∈ Tab.map (fun z => (z.1, z.2.1)) := by\n"
               "    rw [Tab_cov]; exact mem_ptPairs a b\n"
               "  obtain ⟨z, hz, hzeq⟩ := List.mem_map.mp hmem\n"
               "  obtain ⟨h1, h2⟩ := Prod.mk.inj hzeq\n"
               "  have h := of_decide_eq_true (List.all_eq_true.mp Tab_ok z hz)\n"
               "  rcases h with heq | ⟨hw, hr, hq1, hq2⟩\n"
               "  · exact absurd (h1 ▸ h2 ▸ heq) hab\n"
               "  have hwz : Wdata.getD z.2.2.1 wdflt ∈ Wdata := getD_mem hw\n"
               "  have hrz : RepData.getD z.2.2.2 rdflt ∈ RepData := getD_mem hr\n"
               "  rw [h1] at hq1; rw [h2] at hq2\n"
               "  exact ⟨tabW z, Wdata_mem _ hwz, tabQ z, RepData_mem _ hrz,\n"
               "    Wdata_zpow _ hwz, hq1, hq2, RepData_gens _ hrz⟩\n\n")
    out.append("/-- **A subgroup of `N` whose order is divisible by 91 is `N`.** -/\n"
               "theorem eq_of_ninetyOne_dvd {H : Subgroup (Equiv.Perm (Fin 65))}\n"
               "    (hH : H ≤ lclosure Ngens0) (h91 : 91 ∣ Nat.card H) : H = lclosure Ngens0 :=\n"
               "  eq_of_card_dvd rfl Ncard (b₀ := 0) (b₁ := 1) (by decide) Nle2 NQcard Nstab01\n"
               "    Pc_mem Pc_card htab_cert hH h91\n\n")
    out.append("end Sz8.Monodromy\n")

    path = HERE / "Sz8/Monodromy/NinetyOneCerts.lean"
    export_outputs({path: "".join(out)}, check=args.check, root=HERE, exporter="export_sylow",
                   sources=[F_SOURCE, SOURCE])
    print(f"{'Checked' if args.check else 'Exported'} order-91 certificates: "
          f"{len(norm)} normalising elements, {len(reps)} representatives, "
          f"longest word {max(len(w) for p in ws for w in p)}")


if __name__ == "__main__":
    main()
