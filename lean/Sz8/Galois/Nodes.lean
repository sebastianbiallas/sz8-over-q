import Sz8.Galois.ResDegree
import Sz8.Galois.NodeSep
import Sz8.Galois.NodeLocal

/-!
# The bad set and the nodes, from the resultant identity

`Identity` is the resultant identity for the actual family (proved in `Sz8.Galois.Identity` from
the 813 kernel evaluations). From it, with separability and coprimality of `S̃`:

* `regular_compl`: the non-regular parameters are exactly `{t² + t + 1 = 0} ∪ roots(S̃)`;
* `nodesS_card`: `S̃` has exactly 342 complex roots;
* `nodesS_q`: none of them is a root of `t² + t + 1`;
* `mem_nodesS_of_bad`: **uniqueness** — any finite set disjoint from the roots of `t² + t + 1`
  whose union with them is the bad locus consists of roots of `S̃`;
* `node_local`: at every root of `S̃`, loops of regular parameters in a small disc have trivial
  monodromy (`NodeLocal.local_monodromy_trivial` with `node_M2`, the double root supplied by the
  vanishing resultant, and `V(t) = c̃ q(t)^40 S₁(t)²` where `S̃ = (t - a) S₁`).
-/

open Polynomial Metric

set_option maxRecDepth 100000

namespace Sz8.Galois.Nodes

open Sz8.Monodromy ResEval NodeM2 NodeSep

/-- The resultant identity for the actual family. -/
def Identity : Prop :=
  ∀ z : ℂ, resultant (paperMonicFamily.P z) (derivative (paperMonicFamily.P z))
    = (ctil : ℂ) * (z ^ 2 + z + 1) ^ 40 * ((Stil.map (Int.castRingHom ℂ)).eval z) ^ 2

/-- `S̃` over `ℂ`. -/
noncomputable def SC : ℂ[X] := Stil.map (Int.castRingHom ℂ)

/-- The roots of `S̃`. -/
noncomputable def nodesS : Finset ℂ := SC.roots.toFinset

theorem SC_natDegree : SC.natDegree = 342 := by
  rw [SC, natDegree_map_eq_of_injective (RingHom.injective_int _), Stil_natDegree]

theorem SC_ne_zero : SC ≠ 0 := by
  intro h; have := SC_natDegree; rw [h, natDegree_zero] at this; norm_num at this

theorem mem_nodesS {a : ℂ} : a ∈ nodesS ↔ SC.eval a = 0 := by
  rw [nodesS, Multiset.mem_toFinset, mem_roots SC_ne_zero, IsRoot.def]

theorem ctil_ne : (ctil : ℂ) ≠ 0 := by
  have : ctil ≠ 0 := by decide +kernel
  exact_mod_cast this

theorem not_regular_iff (t : ℂ) :
    t ∉ paperMonicFamily.regular ↔
      resultant (paperMonicFamily.P t) (derivative (paperMonicFamily.P t)) = 0 := by
  have hP0 : paperMonicFamily.P t ≠ 0 := (paperMonicFamily.monic t).ne_zero
  rw [resultant_eq_zero_iff, isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := ℂ) ℂ]
  simp only [MonicFamily.regular, Set.mem_ofPred_eq, aeval_def, eval₂_eq_eval_map,
    Algebra.algebraMap_self, Polynomial.map_id]
  constructor
  · intro h
    push_neg at h
    obtain ⟨x, hx, hd⟩ := h
    exact ⟨Or.inl hP0, fun hc => by rcases hc x with h1 | h1 <;> contradiction⟩
  · rintro ⟨-, h⟩ hreg
    exact h fun x => by
      by_cases hx : (paperMonicFamily.P t).eval x = 0
      · exact Or.inr (hreg x hx)
      · exact Or.inl hx

theorem regular_compl (hId : Identity) :
    paperMonicFamily.regularᶜ = {t : ℂ | t ^ 2 + t + 1 = 0} ∪ ↑nodesS := by
  ext t
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe, mem_nodesS]
  rw [not_regular_iff, hId]
  simp only [mul_eq_zero, pow_eq_zero_iff (by norm_num : (40 : ℕ) ≠ 0),
    pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0), ctil_ne, false_or, SC]

theorem nodesS_q {a : ℂ} (ha : a ∈ nodesS) : a ^ 2 + a + 1 ≠ 0 :=
  q_ne_of_root a (mem_nodesS.1 ha)

theorem SC_derivative_ne {a : ℂ} (ha : a ∈ nodesS) : (derivative SC).eval a ≠ 0 := by
  rw [SC, derivative_map]; exact derivative_ne_of_root a (mem_nodesS.1 ha)

theorem nodesS_card : nodesS.card = 342 := by
  have hsep : SC.Separable := by
    refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := ℂ) ℂ SC (derivative SC)).2 fun z => ?_
    simp only [aeval_def, eval₂_eq_eval_map, Algebra.algebraMap_self, Polynomial.map_id]
    by_cases hz : SC.eval z = 0
    · exact Or.inr (SC_derivative_ne (mem_nodesS.2 hz))
    · exact Or.inl hz
  rw [nodesS, Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
    SC_natDegree]

/-- **Uniqueness of the node set.** -/
theorem mem_nodesS_of_bad (hId : Identity) {nodes : Finset ℂ}
    (hq : ∀ a ∈ nodes, a ^ 2 + a + 1 ≠ 0)
    (hbad : paperMonicFamily.regularᶜ = {t : ℂ | t ^ 2 + t + 1 = 0} ∪ ↑nodes) {a : ℂ}
    (ha : a ∈ nodes) : a ∈ nodesS := by
  have h1 : a ∈ paperMonicFamily.regularᶜ := by rw [hbad]; exact Or.inr ha
  rw [regular_compl hId] at h1
  rcases h1 with h | h
  · exact absurd h (hq a ha)
  · exact h

theorem nodes_eq_nodesS (hId : Identity) {nodes : Finset ℂ}
    (hq : ∀ a ∈ nodes, a ^ 2 + a + 1 ≠ 0)
    (hbad : paperMonicFamily.regularᶜ = {t : ℂ | t ^ 2 + t + 1 = 0} ∪ ↑nodes) : nodes = nodesS := by
  ext a
  refine ⟨mem_nodesS_of_bad hId hq hbad, fun ha => ?_⟩
  have h1 : a ∈ paperMonicFamily.regularᶜ := by rw [regular_compl hId]; exact Or.inr ha
  rw [hbad] at h1
  rcases h1 with h | h
  · exact absurd h (nodesS_q ha)
  · exact h

/-- **Local triviality at a node.** -/
theorem node_local (hId : Identity) {a : ℂ} (ha : a ∈ nodesS) :
    ∃ r > 0, ∀ (b : paperMonicFamily.Base) (δ : Path b b),
      (∀ u, ((δ u : paperMonicFamily.Base) : ℂ) ∈ ball a r) →
        ∀ e : paperMonicFamily.Fiber b,
          paperMonicFamily.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk δ) e = e := by
  have hSa : SC.eval a = 0 := mem_nodesS.1 ha
  obtain ⟨hmult, huniq⟩ := node_M2 a hSa
  have hP0 : paperMonicFamily.P a ≠ 0 := (paperMonicFamily.monic a).ne_zero
  -- the double root
  have hres0 : resultant (paperMonicFamily.P a) (derivative (paperMonicFamily.P a)) = 0 := by
    rw [hId]; simp [show (Stil.map (Int.castRingHom ℂ)).eval a = 0 from hSa]
  rw [← not_regular_iff] at hres0
  simp only [MonicFamily.regular, Set.mem_ofPred_eq, not_forall, not_not] at hres0
  obtain ⟨r₀, hr₀root, hr₀d⟩ := hres0
  have hr₀ : (paperMonicFamily.P a).rootMultiplicity r₀ = 2 := by
    have h1 := (one_lt_rootMultiplicity_iff_isRoot hP0).2 ⟨hr₀root, hr₀d⟩
    have h2 := hmult r₀
    omega
  -- the factor `V`
  set S₁ := SC /ₘ (X - C a) with hS₁
  have hfac : (X - C a) * S₁ = SC := mul_divByMonic_eq_iff_isRoot.2 hSa
  set V : ℂ → ℂ := fun t => (ctil : ℂ) * (t ^ 2 + t + 1) ^ 40 * (S₁.eval t) ^ 2 with hV
  have hVc : ContinuousOn V (ball a 1) := by
    refine (Continuous.continuousOn ?_)
    simp only [hV]
    fun_prop
  have hS₁a : S₁.eval a ≠ 0 := by
    have hd := SC_derivative_ne ha
    rw [← hfac, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul] at hd
    simpa using hd
  have hVa : V a ≠ 0 := by
    simp only [hV]
    exact mul_ne_zero (mul_ne_zero ctil_ne (pow_ne_zero _ (nodesS_q ha))) (pow_ne_zero _ hS₁a)
  have hD : ∀ t ∈ ball a 1, resultant (paperMonicFamily.P t) (derivative (paperMonicFamily.P t))
      = (t - a) ^ 2 * V t := by
    intro t _
    rw [hId, show Stil.map (Int.castRingHom ℂ) = SC from rfl, ← hfac]
    simp only [hV, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hr₀u : ∀ r, 2 ≤ (paperMonicFamily.P a).rootMultiplicity r → r = r₀ := fun r hr =>
    huniq r r₀ hr (by rw [hr₀])
  exact NodeLocal.local_monodromy_trivial paperMonicFamily (by show 4 ≤ 65; norm_num) a hmult r₀
    hr₀ hr₀u one_pos V hVc hVa hD

end Sz8.Galois.Nodes
