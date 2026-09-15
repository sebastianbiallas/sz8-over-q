import Sz8.Galois.Continuation

/-!
# (R): monodromy preserves relations among root germs, with coefficients in `ℂ(t)`

`relations_monodromy`: if a polynomial relation with coefficients in `ℂ(t)` holds among the root
germs at `b`, it holds after permuting them by any monodromy. Denominators are cleared first
(`exists_clear`: `d Q = Q'` with `d ≠ 0` in `ℂ[t]`, not `d(b) ≠ 0`); the cleared relation is a
germ of a holomorphic function (`eval₂_eq_zero_iff`) and continues around the loop
(`Continuation.continue_monodromy`); the nonzero germ of `d` cancels in the field `Mer b`.
-/

open Polynomial Topology Filter

namespace Sz8.Galois.Relations

open Sz8.Monodromy Sz8.Monodromy.MonicFamily Germs Continuation
open scoped nonZeroDivisors

theorem subtype_eval₂ {b : ℂ} {ι : Type*} (Q : MvPolynomial ι ℂ[X]) (r : ι → ℂ → ℂ)
    (hr : ∀ i, AnalyticAt ℂ (r i) b) :
    ((MvPolynomial.eval₂ (polyGerm b) (fun i => anMk (hr i)) Q : anGerm b) : Germ (𝓝 b) ℂ) =
      ((fun t => qv Q t fun i => r i t : ℂ → ℂ) : Germ (𝓝 b) ℂ) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [qv, polyGerm, anMk]
  | add p q hp hq =>
    rw [MvPolynomial.eval₂_add, Subring.coe_add, hp, hq]
    simp [qv]; rfl
  | mul_X p i hp =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Subring.coe_mul, hp]
    simp [qv, anMk]; rfl

theorem eval₂_eq_zero_iff {b : ℂ} {ι : Type*} (Q : MvPolynomial ι ℂ[X]) (r : ι → ℂ → ℂ)
    (hr : ∀ i, AnalyticAt ℂ (r i) b) :
    MvPolynomial.eval₂ (polyGerm b) (fun i => anMk (hr i)) Q = 0 ↔
      (fun t => qv Q t fun i => r i t) =ᶠ[𝓝 b] 0 := by
  rw [← Subtype.val_inj, subtype_eval₂]
  exact Germ.coe_eq

theorem exists_clear {ι : Type*} (Q : MvPolynomial ι (RatFunc ℂ)) :
    ∃ d : ℂ[X], d ≠ 0 ∧ ∃ Q' : MvPolynomial ι ℂ[X],
      Q'.map (algebraMap ℂ[X] (RatFunc ℂ)) = MvPolynomial.C (algebraMap ℂ[X] (RatFunc ℂ) d) * Q := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (ℂ[X]⁰)
    (Q.support.image Q.coeff)
  have hc : ∀ m, ∃ c : ℂ[X], algebraMap ℂ[X] (RatFunc ℂ) c = (d : ℂ[X]) • Q.coeff m := by
    intro m
    by_cases hm : m ∈ Q.support
    · exact hd _ (Finset.mem_image_of_mem _ hm)
    · exact ⟨0, by simp [MvPolynomial.notMem_support_iff.1 hm]⟩
  choose c hc using hc
  refine ⟨d, nonZeroDivisors.ne_zero d.2, ∑ m ∈ Q.support, MvPolynomial.monomial m (c m), ?_⟩
  ext m
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', ← Algebra.smul_def]
  split_ifs with hm
  · exact hc m
  · simp [MvPolynomial.notMem_support_iff.1 hm]

/-- **(R)** -/
theorem relations_monodromy (M : MonicFamily) (b : M.Base) (γ : FundamentalGroup M.Base b)
    (Q : MvPolynomial (M.Fiber b) (RatFunc ℂ)) (hQ : MvPolynomial.aeval (rootGerm M b) Q = 0) :
    MvPolynomial.aeval (rootGerm M b ∘ M.isCoveringMap.monodromyPerm b γ) Q = 0 := by
  obtain ⟨d, hd, Q', hQ'⟩ := exists_clear Q
  have hdM : algebraMap (RatFunc ℂ) (Mer b.1) (algebraMap ℂ[X] (RatFunc ℂ) d) ≠ 0 := by
    rw [algebraMap_poly, Ne, IsFractionRing.to_map_eq_zero_iff, map_eq_zero_iff _ polyGerm_injective]
    exact hd
  have hcomp : (algebraMap (RatFunc ℂ) (Mer b.1)).comp (algebraMap ℂ[X] (RatFunc ℂ)) =
      (algebraMap (anGerm b.1) (Mer b.1)).comp (polyGerm b.1) := RingHom.ext algebraMap_poly
  have transfer : ∀ π : M.Fiber b → M.Fiber b,
      MvPolynomial.aeval (rootGerm M b ∘ π) Q = 0 ↔
        (fun t => qv Q' t fun x => rootFun M b (π x) t) =ᶠ[𝓝 b.1] 0 := by
    intro π
    have e1 : MvPolynomial.aeval (rootGerm M b ∘ π) Q = 0 ↔
        MvPolynomial.aeval (rootGerm M b ∘ π) (Q'.map (algebraMap ℂ[X] (RatFunc ℂ))) = 0 := by
      rw [hQ', map_mul, MvPolynomial.aeval_C, mul_eq_zero, or_iff_right hdM]
    have e2 : MvPolynomial.aeval (rootGerm M b ∘ π) (Q'.map (algebraMap ℂ[X] (RatFunc ℂ))) =
        algebraMap (anGerm b.1) (Mer b.1) (MvPolynomial.eval₂ (polyGerm b.1)
          (fun x => anMk (rootFun_analyticAt M b (π x))) Q') := by
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, hcomp, MvPolynomial.eval₂_comp_left]
      rfl
    rw [e1, e2, IsFractionRing.to_map_eq_zero_iff, eval₂_eq_zero_iff]
  have h0 := (transfer id).1 hQ
  rw [transfer]
  obtain ⟨p⟩ := γ
  exact continue_monodromy M b p Q' h0

end Sz8.Galois.Relations
