import Sz8.Monodromy.Link
import Sz8.Monodromy.RootTransport

/-!
The paper's family `f(X, t)` is a `MonicFamily`: monic of degree 65 in `X` for every
complex `t`, with polynomial dependence on `t`. So `RootCovering` applies: over the
parameters where all 65 roots are simple, the roots form a covering space, and Mathlib's
monodromy is defined for every loop of such parameters.
-/

open Polynomial

namespace Sz8.Monodromy

/-- The input terms `(X-degree, t-degree, coefficient)`. -/
def famTerms : List (ℕ × ℕ × ℚ) :=
  inputTerms.map fun a => (a.1, a.2.1, (a.2.2.1 : ℚ) / a.2.2.2)

theorem paperFamily_eq_famTerms (t : ℂ) : paperFamily t = sparseFamily famTerms t :=
  paperFamily_eq_sparse t

section Sparse

variable (ts : List (ℕ × ℕ × ℚ))

theorem sparseFamily_cons (a : ℕ × ℕ × ℚ) (t : ℂ) :
    sparseFamily (a :: ts) t = C ((a.2.2 : ℂ) * t ^ a.2.1) * X ^ a.1 + sparseFamily ts t := by
  simp [sparseFamily]

theorem sparseFamily_eval (t x : ℂ) :
    (sparseFamily ts t).eval x = (ts.map fun a => (a.2.2 : ℂ) * t ^ a.2.1 * x ^ a.1).sum := by
  induction ts with
  | nil => simp [sparseFamily]
  | cons a ts ih => simp [sparseFamily_cons, ih]

theorem sparseFamily_coeff (t : ℂ) (m : ℕ) :
    (sparseFamily ts t).coeff m =
      (ts.map fun a => if a.1 = m then (a.2.2 : ℂ) * t ^ a.2.1 else 0).sum := by
  induction ts with
  | nil => simp [sparseFamily]
  | cons a ts ih =>
    rw [sparseFamily_cons, coeff_add, coeff_C_mul_X_pow, ih, List.map_cons, List.sum_cons]
    congr 1
    split_ifs <;> first | rfl | omega

theorem continuous_sparseFamily_coeff (m : ℕ) :
    Continuous fun t => (sparseFamily ts t).coeff m := by
  simp_rw [sparseFamily_coeff]
  induction ts with
  | nil => exact continuous_const
  | cons a ts ih =>
    simp only [List.map_cons, List.sum_cons]
    refine Continuous.add ?_ ih
    split_ifs <;> fun_prop

theorem contDiff_sparseFamily_eval :
    ContDiff ℂ 1 fun p : ℂ × ℂ => (sparseFamily ts p.1).eval p.2 := by
  simp_rw [sparseFamily_eval]
  induction ts with
  | nil => simpa using contDiff_const
  | cons a ts ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ContDiff.add (by fun_prop) ih

/-- Only the listed terms of X-degree `m` contribute to the coefficient of `X^m`. -/
theorem sparseFamily_coeff_filter (t : ℂ) (m : ℕ) :
    (sparseFamily ts t).coeff m =
      ((ts.filter fun a => a.1 == m).map fun a => (a.2.2 : ℂ) * t ^ a.2.1).sum := by
  rw [sparseFamily_coeff]
  induction ts with
  | nil => simp
  | cons a ts ih =>
    by_cases h : a.1 = m
    · simp [h, ih]
    · simp [h, ih]

end Sparse

theorem famTerms_degree_le : famTerms.all (fun a => a.1 ≤ 65) = true := by decide +kernel

theorem famTerms_top : famTerms.filter (fun a => a.1 == 65) = [(65, 0, 1)] := by decide +kernel

theorem paperFamily_coeff_65 (t : ℂ) : (paperFamily t).coeff 65 = 1 := by
  rw [paperFamily_eq_famTerms, sparseFamily_coeff_filter, famTerms_top]
  simp

theorem paperFamily_coeff_eq_zero (t : ℂ) {m : ℕ} (hm : 65 < m) : (paperFamily t).coeff m = 0 := by
  rw [paperFamily_eq_famTerms, sparseFamily_coeff]
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  have := List.all_eq_true.mp famTerms_degree_le a ha
  simp only [decide_eq_true_eq] at this
  simp [show a.1 ≠ m by omega]

theorem paperFamily_natDegree_le (t : ℂ) : (paperFamily t).natDegree ≤ 65 :=
  natDegree_le_iff_coeff_eq_zero.mpr fun m hm => paperFamily_coeff_eq_zero t (by exact_mod_cast hm)

/-- For every complex `t`, `f(X, t)` is monic of degree 65. -/
theorem paperFamily_monic (t : ℂ) : (paperFamily t).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 65 (paperFamily_natDegree_le t) (paperFamily_coeff_65 t)

theorem paperFamily_natDegree (t : ℂ) : (paperFamily t).natDegree = 65 :=
  natDegree_eq_of_le_of_coeff_ne_zero (paperFamily_natDegree_le t)
    (by rw [paperFamily_coeff_65]; exact one_ne_zero)

/-- The paper's family as a `MonicFamily`; its regular roots form a covering space. -/
noncomputable def paperMonicFamily : MonicFamily where
  P := paperFamily
  n := 65
  monic := paperFamily_monic
  natDegree_eq := paperFamily_natDegree
  continuous_coeff i := by
    simp_rw [paperFamily_eq_famTerms]
    exact continuous_sparseFamily_coeff famTerms i
  contDiff := by
    simp_rw [paperFamily_eq_famTerms]
    exact contDiff_sparseFamily_eval famTerms

/-- The roots of `f(X, t)` form a covering space over the parameters where they are simple. -/
theorem paper_isCoveringMap :
    IsCoveringMap (paperMonicFamily.regular.restrictPreimage paperMonicFamily.proj) :=
  paperMonicFamily.isCoveringMap

end Sz8.Monodromy
