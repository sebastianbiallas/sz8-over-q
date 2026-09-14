import Sz8.Galois.Resolvent
import Mathlib.Algebra.Order.Field.Power

/-!
# Seven pinning points

The dyadic points `r k = (k - 3) / 2048`, `k = 0, …, 6`, lie in the certified parameter ball
(`|r k| ≤ 3/2048 < 0.0023958`). `W` is the exact inverse of their Vandermonde matrix (`W_inv`, a kernel
check), and every row of `|W|` sums to less than `2^65` (`W_bound`). Hence integer polynomials of degree
`≤ 6` whose values at the points are all smaller than `2^-65` vanish (`pins`), via the general
`pins_of_inverse`.
-/

open Polynomial

namespace Sz8.Galois.Pinning

/-- **Consumer-independent pinning lemma.** -/
theorem pins_of_inverse {n : ℕ} (r : Fin (n + 1) → ℚ) (W : Fin (n + 1) → Fin (n + 1) → ℚ)
    (hW : ∀ j i : Fin (n + 1), ∑ k, W j k * r k ^ (i : ℕ) = if j = i then 1 else 0) {d : ℚ}
    (hb : ∀ j, ∑ k, |W j k| * d < 1) :
    Resolvent.Pins n (fun k => (r k : ℂ)) (fun _ => (d : ℝ)) := by
  intro Δ hdeg hsmall
  set D := Δ.map (Int.castRingHom ℚ) with hD
  have hval : ∀ k, |D.eval (r k)| < d := by
    intro k
    have h := hsmall k
    have e : aeval (r k : ℂ) Δ = ((D.eval (r k) : ℚ) : ℂ) := by
      have h1 := Polynomial.hom_eval₂ Δ (Int.castRingHom ℚ) (Rat.castHom ℂ) (r k)
      rw [hD, eval_map, aeval_def]
      rw [show ((Rat.castHom ℂ) (eval₂ (Int.castRingHom ℚ) (r k) Δ)) =
        ((eval₂ (Int.castRingHom ℚ) (r k) Δ : ℚ) : ℂ) from rfl] at h1
      rw [RingHom.ext_int ((Rat.castHom ℂ).comp (Int.castRingHom ℚ)) (algebraMap ℤ ℂ)] at h1
      exact h1.symm
    rw [e, Complex.norm_ratCast] at h
    have h' : |((D.eval (r k) : ℚ) : ℝ)| < (d : ℝ) := h
    exact_mod_cast h'
  have hdegD : D.natDegree ≤ n := (natDegree_map_le).trans hdeg
  have hsum : ∀ k, D.eval (r k) = ∑ i : Fin (n + 1), D.coeff i * r k ^ (i : ℕ) := by
    intro k
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hdegD), ← Fin.sum_univ_eq_sum_range
      (fun i => D.coeff i * r k ^ i)]
  refine Polynomial.ext fun j => ?_
  rw [coeff_zero]
  by_cases hj : j ≤ n
  · let jj : Fin (n + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    have hc : (D.coeff (jj : ℕ) : ℚ) = ∑ k, W jj k * D.eval (r k) := by
      simp only [hsum, Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ i : Fin (n + 1), ∑ k, W jj k * (D.coeff i * r k ^ (i : ℕ)) =
          D.coeff i * (if jj = i then 1 else 0) := fun i => by
        rw [← hW jj i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hlt : |(D.coeff (jj : ℕ) : ℚ)| < 1 := by
      rw [hc]
      calc |∑ k, W jj k * D.eval (r k)| ≤ ∑ k, |W jj k * D.eval (r k)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k, |W jj k| * d := Finset.sum_le_sum fun k _ => by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hval k).le (abs_nonneg _)
        _ < 1 := hb jj
    have hcoef : (D.coeff (jj : ℕ) : ℚ) = ((Δ.coeff j : ℤ) : ℚ) := by simp [hD, jj]
    rw [hcoef] at hlt
    have : |Δ.coeff j| < 1 := by exact_mod_cast hlt
    exact Int.abs_lt_one_iff.1 this
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- The points. -/
def r (k : Fin 7) : ℚ := ((k : ℤ) - 3) / 2048

/-- The inverse Vandermonde matrix. -/
def W : Fin 7 → Fin 7 → ℚ := ![
    ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)],
    ![(-512/15 : ℚ), (1536/5 : ℚ), (-1536 : ℚ), (0 : ℚ), (1536 : ℚ), (-1536/5 : ℚ), (512/15 : ℚ)],
    ![(1048576/45 : ℚ), (-1572864/5 : ℚ), (3145728 : ℚ), (-51380224/9 : ℚ), (3145728 : ℚ), (-1572864/5 : ℚ), (1048576/45 : ℚ)],
    ![(536870912/3 : ℚ), (-4294967296/3 : ℚ), (6979321856/3 : ℚ), (0 : ℚ), (-6979321856/3 : ℚ), (4294967296/3 : ℚ), (-536870912/3 : ℚ)],
    ![(-1099511627776/9 : ℚ), (4398046511104/3 : ℚ), (-14293651161088/3 : ℚ), (61572651155456/9 : ℚ), (-14293651161088/3 : ℚ), (4398046511104/3 : ℚ), (-1099511627776/9 : ℚ)],
    ![(-2251799813685248/15 : ℚ), (9007199254740992/15 : ℚ), (-2251799813685248/3 : ℚ), (0 : ℚ), (2251799813685248/3 : ℚ), (-9007199254740992/15 : ℚ), (2251799813685248/15 : ℚ)],
    ![(4611686018427387904/45 : ℚ), (-9223372036854775808/15 : ℚ), (4611686018427387904/3 : ℚ), (-18446744073709551616/9 : ℚ), (4611686018427387904/3 : ℚ), (-9223372036854775808/15 : ℚ), (4611686018427387904/45 : ℚ)]]

theorem W_inv : ∀ j i : Fin 7, ∑ k, W j k * r k ^ (i : ℕ) = if j = i then 1 else 0 := by
  decide +kernel

theorem W_bound : ∀ j : Fin 7, ∑ k, |W j k| * (1 / 2 ^ 65) < 1 := by
  decide +kernel

/-- **The pinning property** for the seven points and `δ = 2^-65`. -/
theorem pins : Resolvent.Pins 6 (fun k => (r k : ℂ)) (fun _ => ((1 / 2 ^ 65 : ℚ) : ℝ)) :=
  pins_of_inverse r W W_inv W_bound

theorem r_small (k : Fin 7) : ‖(r k : ℂ)‖ < (2634246607 : ℝ) / 2 ^ 40 := by
  rw [Complex.norm_ratCast]
  fin_cases k <;> norm_num [r]

end Sz8.Galois.Pinning
