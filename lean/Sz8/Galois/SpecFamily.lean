import Sz8.Monodromy.PaperCovering
import Sz8.Monodromy.Specialization
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The paper's family over `ℚ[t]`

`fQ = Σ c_{ij} t^j X^i ∈ ℚ[t][X]` from the exact input terms: monic of degree 65 (`fQ_monic`), equal
to the family over `ℚ(t)` after mapping (`fQ_map`), and equal to `f(X, -7/5)` after evaluating
`t = -7/5` (`fQ_spec`).
-/

open Polynomial

namespace Sz8.Galois.SpecFamily

open Sz8.Monodromy

/-- `f(X, t) ∈ ℚ[t][X]`. -/
noncomputable def fQ : ℚ[X][X] :=
  famTerms.foldr (fun a acc => C (C a.2.2 * X ^ a.2.1) * X ^ a.1 + acc) 0

theorem foldr_coeff (ts : List (ℕ × ℕ × ℚ)) (m : ℕ) :
    (ts.foldr (fun a acc => C (C a.2.2 * X ^ a.2.1) * X ^ a.1 + acc) (0 : ℚ[X][X])).coeff m =
      ((ts.filter fun a => a.1 == m).map fun a => C a.2.2 * X ^ a.2.1).sum := by
  induction ts with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons] at ih ⊢
    rw [coeff_add, ih, coeff_C_mul_X_pow]
    by_cases h : a.1 = m
    · simp [h]
    · simp [h, Ne.symm h]

/-- **`fQ` is monic** (of degree 65). -/
theorem fQ_monic : fQ.Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one 65 ?_ ?_
  · refine natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    rw [fQ, foldr_coeff]
    have hnil : famTerms.filter (fun a => a.1 == m) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      have := List.all_eq_true.1 famTerms_degree_le a ha
      simp only [decide_eq_true_eq] at this
      have hm' : 65 < m := by exact_mod_cast hm
      simp only [beq_iff_eq]; omega
    simp [hnil]
  · rw [fQ, foldr_coeff, famTerms_top]
    simp

/-- Over `ℚ(t)`: the same foldr as `Sz8.Galois.fRat`. -/
theorem fQ_map : fQ.map (algebraMap ℚ[X] (RatFunc ℚ)) =
    famTerms.foldr (fun a acc =>
      C (algebraMap ℚ (RatFunc ℚ) a.2.2 * RatFunc.X ^ a.2.1) * X ^ a.1 + acc) 0 := by
  unfold fQ
  induction famTerms with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, Polynomial.map_add, ih, Polynomial.map_mul,
      Polynomial.map_pow, map_C, map_X, map_mul, map_pow, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X,
      show RatFunc.C a.2.2 = algebraMap ℚ (RatFunc ℚ) a.2.2 from
        congrArg (· a.2.2) (RingHom.ext_rat RatFunc.C (algebraMap ℚ (RatFunc ℚ)))]

/-- At `t = -7/5`: the specialization `h`. -/
theorem fQ_spec : fQ.map (evalRingHom (-7 / 5 : ℚ)) = paperSpecialization := by
  rw [paperSpecialization, fQ, famTerms, List.foldr_map]
  induction inputTerms with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, Polynomial.map_add, ih]
    simp

end Sz8.Galois.SpecFamily
