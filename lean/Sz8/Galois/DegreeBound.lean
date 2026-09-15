import Sz8.Galois.FirstEdge
import Sz8.Galois.Resolvent
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Degree bounds at infinity from the first Newton edge

In a field `E` over `ℚ` with `τ¹³ t = 1` and `t` transcendental, write `ev τ : ℚ[X] → E` for
`X ↦ τ`.

* `isIntegralElem_root`: a root `x` of the paper's family at `t` has `τ⁷ x` integral over `ℚ[τ]`
  (`FirstEdge.Fτ_monic`, `FirstEdge.Fτ_eval`).
* `isIntegralElem_Θ`: hence `τ²⁸ Θ(13³ x)` is integral over `ℚ[τ]`.
* `natDegree_le_of_isIntegralElem`: if `τ^k Q(t)` is integral over `ℚ[τ]` then `13 deg Q ≤ k`.
-/

open Polynomial

namespace Sz8.Galois.DegreeBound

open Sz8.Monodromy FirstEdge

variable {E : Type*} [Field E] [Algebra ℚ E]

/-- `X ↦ τ`. -/
noncomputable abbrev ev (τ : E) : ℚ[X] →+* E := eval₂RingHom (algebraMap ℚ E) τ

theorem isIntegralElem_add {τ a b : E} (ha : (ev τ).IsIntegralElem a)
    (hb : (ev τ).IsIntegralElem b) : (ev τ).IsIntegralElem (a + b) := by
  let := (ev τ).toAlgebra
  exact IsIntegral.add ha hb

theorem isIntegralElem_mul {τ a b : E} (ha : (ev τ).IsIntegralElem a)
    (hb : (ev τ).IsIntegralElem b) : (ev τ).IsIntegralElem (a * b) := by
  let := (ev τ).toAlgebra
  exact IsIntegral.mul ha hb

theorem isIntegralElem_pow {τ a : E} (ha : (ev τ).IsIntegralElem a) (n : ℕ) :
    (ev τ).IsIntegralElem (a ^ n) := by
  let := (ev τ).toAlgebra
  exact IsIntegral.pow ha n

/-- **The scaled roots are integral over `ℚ[τ]`.** -/
theorem isIntegralElem_root {τ t x : E} (hτ : τ ^ 13 * t = 1)
    (hx : famTerms.foldr (fun a acc => algebraMap ℚ E a.2.2 * t ^ a.2.1 * x ^ a.1 + acc) 0 = 0) :
    (ev τ).IsIntegralElem (τ ^ 7 * x) :=
  ⟨Fτ famTerms, Fτ_monic, by rw [Fτ_eval famTerms (by simpa using edge_terms.1) hτ, hx, mul_zero]⟩

theorem Θ_const_mul {L : Type*} [CommRing L] (c : L) (x : Fin 65 → L)
    (N : Subgroup (Equiv.Perm (Fin 65))) (π : Equiv.Perm (Fin 65)) :
    Resolvent.Θ (fun i => c * x i) N π = c ^ 4 * Resolvent.Θ x N π := by
  classical
  unfold Resolvent.Θ Resolvent.mono
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **The invariant values scaled by `τ²⁸` are integral over `ℚ[τ]`.** -/
theorem isIntegralElem_Θ {τ t : E} (hτ : τ ^ 13 * t = 1) {x : Fin 65 → E}
    (hx : ∀ i, famTerms.foldr (fun a acc => algebraMap ℚ E a.2.2 * t ^ a.2.1 * x i ^ a.1 + acc)
      0 = 0) (N : Subgroup (Equiv.Perm (Fin 65))) (π : Equiv.Perm (Fin 65)) :
    (ev τ).IsIntegralElem (τ ^ 28 * Resolvent.Θ (fun i => 13 ^ 3 * x i) N π) := by
  classical
  have h : τ ^ 28 * Resolvent.Θ (fun i => 13 ^ 3 * x i) N π =
      Resolvent.Θ (fun i => 13 ^ 3 * (τ ^ 7 * x i)) N π := by
    rw [show (fun i => 13 ^ 3 * (τ ^ 7 * x i)) = fun i => τ ^ 7 * (13 ^ 3 * x i) from
      funext fun i => by ring, Θ_const_mul (τ ^ 7) (fun i => 13 ^ 3 * x i)]
    ring
  rw [h]
  let := (ev τ).toAlgebra
  have hy : ∀ i, IsIntegral ℚ[X] (13 ^ 3 * (τ ^ 7 * x i)) := fun i => by
    have h13 : IsIntegral ℚ[X] ((13 : E) ^ 3) := by
      have : ((13 : E) ^ 3) = algebraMap ℚ[X] E (13 ^ 3) := by
        simp [RingHom.algebraMap_toAlgebra]
      rw [this]; exact isIntegral_algebraMap
    exact h13.mul (isIntegralElem_root hτ (hx i))
  have hmem : ∀ i, (13 ^ 3 * (τ ^ 7 * x i)) ∈ integralClosure ℚ[X] E := hy
  change IsIntegral ℚ[X] (Resolvent.Θ _ N π)
  unfold Resolvent.Θ Resolvent.mono
  exact (integralClosure ℚ[X] E).sum_mem fun n _ => (integralClosure ℚ[X] E).mul_mem
    ((integralClosure ℚ[X] E).mul_mem ((integralClosure ℚ[X] E).pow_mem (hmem _) 2) (hmem _))
    (hmem _)

/-- **Degree bound.** -/
theorem natDegree_le_of_isIntegralElem {τ t : E} (hτ : τ ^ 13 * t = 1)
    (ht : ∀ Q : ℚ[X], Q ≠ 0 → Q.eval₂ (algebraMap ℚ E) t ≠ 0) {k : ℕ} {Q : ℚ[X]}
    (h : (ev τ).IsIntegralElem (τ ^ k * Q.eval₂ (algebraMap ℚ E) t)) : 13 * Q.natDegree ≤ k := by
  -- `τ` is transcendental
  have hτ0 : τ ≠ 0 := fun h0 => by simp [h0] at hτ
  have htr : ∀ V : ℚ[X], V ≠ 0 → V.eval₂ (algebraMap ℚ E) τ ≠ 0 := by
    intro V hV0 hV
    have halg : IsAlgebraic ℚ τ := ⟨V, hV0, by rwa [aeval_def]⟩
    have hint := (isAlgebraic_iff_isIntegral.1 halg).pow 13
    have hinv : IsAlgebraic ℚ (τ ^ 13)⁻¹ := hint.isAlgebraic.inv
    rw [← eq_inv_of_mul_eq_one_right hτ] at hinv
    obtain ⟨R, hR0, hR⟩ := hinv
    exact ht R hR0 (by rwa [aeval_def] at hR)
  by_contra hlt
  push Not at hlt
  set d := Q.natDegree with hd
  set w := τ ^ k * Q.eval₂ (algebraMap ℚ E) t with hw
  obtain ⟨e, he⟩ : ∃ e, 13 * d = k + e := ⟨13 * d - k, by omega⟩
  have he0 : 0 < e := by omega
  have hQ0 : Q ≠ 0 := fun h0 => by simp [h0, hd] at hlt
  -- `τ^e w = U(τ)` with `U(0)` the leading coefficient
  let U : ℚ[X] := ∑ j ∈ Finset.range (d + 1), C (Q.coeff j) * X ^ (13 * (d - j))
  have hU : τ ^ e * w = U.eval₂ (algebraMap ℚ E) τ := by
    rw [hw, ← mul_assoc, ← pow_add, add_comm, ← he, eval₂_eq_sum_range, Finset.mul_sum,
      eval₂_finsetSum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [eval₂_mul, eval₂_C, eval₂_X_pow]
    have : 13 * d = 13 * (d - j) + 13 * j := by omega
    rw [this, pow_add, pow_mul τ 13 j]
    calc τ ^ (13 * (d - j)) * (τ ^ 13) ^ j * (algebraMap ℚ E (Q.coeff j) * t ^ j)
        = algebraMap ℚ E (Q.coeff j) * τ ^ (13 * (d - j)) * (τ ^ 13 * t) ^ j := by ring
      _ = _ := by rw [hτ, one_pow, mul_one]
  have hU0 : U.eval 0 = Q.leadingCoeff := by
    simp only [U, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [Finset.sum_eq_single d]
    · rw [Nat.sub_self, mul_zero, pow_zero, mul_one]; rfl
    · intro j hj hjd
      have : 0 < 13 * (d - j) := by
        have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj); omega
      simp [zero_pow this.ne']
    · intro hd'; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self d)) hd'
  have hUne : U.eval 0 ≠ 0 := by rw [hU0]; exact leadingCoeff_ne_zero.2 hQ0
  -- clear denominators in the integral equation of `w`
  obtain ⟨p, hpm, hp⟩ := h
  set n := p.natDegree with hn
  let P : ℚ[X] := ∑ i ∈ Finset.range (n + 1), p.coeff i * U ^ i * X ^ (e * (n - i))
  have hP : P.eval₂ (algebraMap ℚ E) τ = 0 := by
    have hsum := hp
    rw [eval₂_eq_sum_range] at hsum
    have : P.eval₂ (algebraMap ℚ E) τ = τ ^ (e * n) *
        ∑ i ∈ Finset.range (n + 1), ev τ (p.coeff i) * w ^ i := by
      simp only [P, eval₂_finsetSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [eval₂_mul, eval₂_mul, eval₂_pow, eval₂_X_pow, ← hU]
      have : e * n = e * (n - i) + e * i := by rw [← mul_add]; congr 1; omega
      rw [this, pow_add, pow_mul, coe_eval₂RingHom]
      ring
    rw [this, hsum, mul_zero]
  have hP0 : P.eval 0 = U.eval 0 ^ n := by
    simp only [P, eval_finsetSum, eval_mul, eval_pow, eval_X]
    rw [Finset.sum_eq_single n]
    · rw [Nat.sub_self, mul_zero, pow_zero, mul_one, show p.coeff n = 1 from hpm.coeff_natDegree,
        eval_one, one_mul]
    · intro i hi hin
      have : 0 < e * (n - i) := by
        have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        exact Nat.mul_pos he0 (by omega)
      simp [zero_pow this.ne']
    · intro hn'; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) hn'
  have hPne : P ≠ 0 := fun h0 => by
    have := hP0; rw [h0, eval_zero] at this; exact pow_ne_zero n hUne this.symm
  exact htr P hPne hP

end Sz8.Galois.DegreeBound
