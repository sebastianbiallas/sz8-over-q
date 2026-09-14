import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Node lemma, algebraic core: the discriminant of a product

For monic `A`, `B` of positive degree over a field of characteristic zero,

    Res(AB, (AB)') = Res(A, A') · Res(A, B) · Res(B, A) · Res(B, B'),

and for a monic quadratic `Res(Q, Q') = -(b² - 4c)`. With `A` the product of the simple-root
branches and `B` the residual quadratic this is `D = E · Δ` of the node route.
-/

open Polynomial

namespace Sz8.Galois.NodeAlgebra

variable {K : Type*} [Field K] [CharZero K]

theorem natDegree_derivative_of_pos {p : K[X]} (hp : 0 < p.natDegree) :
    (derivative p).natDegree = p.natDegree - 1 := natDegree_derivative p

theorem resultant_mul_derivative {A B : K[X]} (hA : A.Monic) (hB : B.Monic)
    (ha : 0 < A.natDegree) (hb : 0 < B.natDegree) :
    resultant (A * B) (derivative (A * B))
      = resultant A (derivative A) * resultant A B * (resultant B A * resultant B (derivative B)) := by
  set a := A.natDegree
  set b := B.natDegree
  have hAB : (A * B).natDegree = a + b := hA.natDegree_mul hB
  have hd : (derivative (A * B)).natDegree = a + b - 1 := by
    rw [natDegree_derivative_of_pos (by omega), hAB]
  have hdA := natDegree_derivative_of_pos ha
  have hdB := natDegree_derivative_of_pos hb
  rw [show resultant (A * B) (derivative (A * B))
      = resultant (A * B) (derivative (A * B)) (a + b) (a + b - 1) by rw [hAB, hd],
    resultant_mul_left _ _ _ _ hd.le, derivative_mul]
  congr 1
  · -- `Res(A, A'B + AB') = Res(A, A'B) = Res(A, A') Res(A, B)`
    rw [resultant_add_mul_right _ _ _ _ _ (by rw [hdB]; omega) le_rfl,
      show a + b - 1 = (derivative A).natDegree + B.natDegree by rw [hdA]; omega,
      resultant_mul_right _ _ _ _ le_rfl]
  · -- `Res(B, A'B + AB') = Res(B, AB') = Res(B, A) Res(B, B')`
    rw [add_comm, show derivative A * B = B * derivative A by ring,
      resultant_add_mul_right _ _ _ _ _ (by rw [hdA]; omega) le_rfl,
      show a + b - 1 = A.natDegree + (derivative B).natDegree by rw [hdB]; omega,
      resultant_mul_right _ _ _ _ le_rfl]

theorem resultant_quadratic_derivative (b c : K) :
    resultant (X ^ 2 + C b * X + C c) (derivative (X ^ 2 + C b * X + C c)) = -(b ^ 2 - 4 * c) := by
  have hdeg : (X ^ 2 + C b * X + C c : K[X]).natDegree = 2 := by compute_degree!
  have hdeg' : (X ^ 2 + C b * X + C c : K[X]).degree = 2 := by compute_degree!
  have hmon : (X ^ 2 + C b * X + C c : K[X]).leadingCoeff = 1 := by
    rw [leadingCoeff, hdeg]; simp [coeff_X, coeff_C]
  have h := resultant_deriv (f := (X ^ 2 + C b * X + C c : K[X])) (by rw [hdeg']; norm_num)
  rw [hdeg] at h
  rw [show resultant (X ^ 2 + C b * X + C c) (derivative (X ^ 2 + C b * X + C c))
      = resultant (X ^ 2 + C b * X + C c) (derivative (X ^ 2 + C b * X + C c)) 2 (2 - 1) by
    rw [hdeg, natDegree_derivative_of_pos (by rw [hdeg]; norm_num), hdeg], h, hmon,
    discr_of_degree_eq_two hdeg']
  simp [coeff_X, coeff_C]

end Sz8.Galois.NodeAlgebra
