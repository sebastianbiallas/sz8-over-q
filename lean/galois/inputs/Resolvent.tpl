import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.ComputeDegree
import Mathlib.Analysis.Complex.Basic

/-!
# The cubic resolvent of the relative invariant of `N` in `G`

**Invariant.** For roots `x : Fin 65 → L` and a subgroup `N` of `S₆₅`,
`Θ x N π = Σ_{n ∈ N} x(πn 0)² x(πn 1) x(πn 3)`. It is right `N`-invariant (`Θ_mul_mem`), and a ring
hom permuting the roots by `p` sends `Θ π` to `Θ (p π)` (`map_Θ`).

**Cosets.** `exists_pow_mul`: if `N ≤ G`, `|G| = 3|N|`, `s ∈ G` and `s, s² ∉ N`, every element of
`G` is `s^j n` with `j < 3`, `n ∈ N`. No normality is used.

**Data.** `E1, E2, E3 ∈ ℚ[t]`: the coefficients of the resolvent `Rs = Y³ - E1 Y² + E2 Y - E3` of
`13¹² θ`, reconstructed from power-series roots at `t = 0` (`galois/upstream/invariant`). Here they are only
data: `Rs_fibre` (split reduction with distinct roots at `t = -7/5`) and `disc_eval_zero_ne` are
kernel facts about these polynomials; that they are the resolvent is
`Sz8.Galois.resolvent_identity`.
-/

open Polynomial

namespace Sz8.Galois.Resolvent

section Invariant

variable {L : Type*} [CommRing L]

/-- The monomial `x(σ 0)² x(σ 1) x(σ 3)`. -/
def mono (x : Fin 65 → L) (σ : Equiv.Perm (Fin 65)) : L := x (σ 0) ^ 2 * x (σ 1) * x (σ 3)

open scoped Classical in
/-- The relative invariant, evaluated after relabelling by `π`. -/
noncomputable def Θ (x : Fin 65 → L) (N : Subgroup (Equiv.Perm (Fin 65))) (π : Equiv.Perm (Fin 65)) :
    L :=
  ∑ n : N, mono x (π * n)

theorem Θ_mul_mem (x : Fin 65 → L) (N : Subgroup (Equiv.Perm (Fin 65))) (π : Equiv.Perm (Fin 65))
    {m : Equiv.Perm (Fin 65)} (hm : m ∈ N) : Θ x N (π * m) = Θ x N π := by
  classical
  unfold Θ
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨m, hm⟩ : N)) _ _ fun n => ?_
  simp [mul_assoc]

theorem map_Θ {L' : Type*} [CommRing L'] (φ : L →+* L') (x : Fin 65 → L) (x' : Fin 65 → L')
    (p : Equiv.Perm (Fin 65)) (hφ : ∀ i, φ (x i) = x' (p i)) (N : Subgroup (Equiv.Perm (Fin 65)))
    (π : Equiv.Perm (Fin 65)) : φ (Θ x N π) = Θ x' N (p * π) := by
  classical
  unfold Θ mono
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [hφ, mul_assoc]

end Invariant

/-- **Three cosets.** -/
theorem exists_pow_mul {Γ : Type*} [Group Γ] {G N : Subgroup Γ} [Finite G] (hNG : N ≤ G)
    (hcard : Nat.card G = 3 * Nat.card N) {s : Γ} (hs : s ∈ G) (hs1 : s ∉ N) (hs2 : s ^ 2 ∉ N)
    {π : Γ} (hπ : π ∈ G) : ∃ j < 3, ∃ n ∈ N, π = s ^ j * n := by
  classical
  let H := N.subgroupOf G
  have hH : Nat.card H = Nat.card N := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNG).toEquiv
  have hindex : H.index = 3 := by
    have h := H.card_mul_index
    rw [hH, hcard] at h
    have : Finite N := Finite.of_injective _ (Subgroup.inclusion_injective hNG)
    have hpos : 0 < Nat.card N := Nat.card_pos
    nlinarith
  let _ := Fintype.ofFinite (G ⧸ H)
  let q : ℕ → G ⧸ H := fun j => ((⟨s ^ j, pow_mem hs j⟩ : G) : G ⧸ H)
  have hq : ∀ i j : ℕ, q i = q j → (s ^ i)⁻¹ * s ^ j ∈ N := by
    intro i j h
    have h' := QuotientGroup.eq.1 h
    rwa [Subgroup.mem_subgroupOf] at h'
  have h01 : q 0 ≠ q 1 := fun h => hs1 (by simpa using hq 0 1 h)
  have h02 : q 0 ≠ q 2 := fun h => hs2 (by simpa using hq 0 2 h)
  have h12 : q 1 ≠ q 2 := fun h => hs1 (by
    have e : (s ^ 1)⁻¹ * s ^ 2 = s := by group
    have h' := hq 1 2 h
    rwa [e] at h')
  have huniv : ({q 0, q 1, q 2} : Finset (G ⧸ H)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [h01, h02]), Finset.card_pair h12,
      Fintype.card_eq_nat_card]
    exact hindex.symm
  have hmem : ((⟨π, hπ⟩ : G) : G ⧸ H) ∈ ({q 0, q 1, q 2} : Finset (G ⧸ H)) := by
    rw [huniv]; exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have key : ∀ j : ℕ, ((⟨π, hπ⟩ : G) : G ⧸ H) = q j → ∃ n ∈ N, π = s ^ j * n := by
    intro j hj
    have h' := QuotientGroup.eq.1 hj.symm
    rw [Subgroup.mem_subgroupOf] at h'
    exact ⟨_, h', by simp⟩
  rcases hmem with h | h | h
  · exact ⟨0, by norm_num, key 0 h⟩
  · exact ⟨1, by norm_num, key 1 h⟩
  · exact ⟨2, by norm_num, key 2 h⟩

/-- **Left multiplication permutes the three cosets.** -/
theorem exists_perm_pow_mul {Γ : Type*} [Group Γ] {G N : Subgroup Γ} [Finite G] (hNG : N ≤ G)
    (hcard : Nat.card G = 3 * Nat.card N) {s : Γ} (hs : s ∈ G) (hs1 : s ∉ N) (hs2 : s ^ 2 ∉ N)
    {ρ : Γ} (hρ : ρ ∈ G) :
    ∃ k : Equiv.Perm (Fin 3), ∀ j : Fin 3, ∃ n ∈ N, ρ * s ^ (j : ℕ) = s ^ (k j : ℕ) * n := by
  have hex : ∀ j : Fin 3, ∃ i : Fin 3, ∃ n ∈ N, ρ * s ^ (j : ℕ) = s ^ (i : ℕ) * n := by
    intro j
    obtain ⟨i, hi, n, hn, h⟩ := exists_pow_mul hNG hcard hs hs1 hs2 (G.mul_mem hρ (pow_mem hs _))
    exact ⟨⟨i, hi⟩, n, hn, h⟩
  choose kf n hn hkn using hex
  have hinj : Function.Injective kf := by
    intro i j hij
    have hmem : (s ^ (i : ℕ))⁻¹ * s ^ (j : ℕ) ∈ N := by
      have e : (s ^ (i : ℕ))⁻¹ * s ^ (j : ℕ) = (n i)⁻¹ * n j := by
        have h1 := hkn i; have h2 := hkn j
        rw [hij] at h1
        calc (s ^ (i : ℕ))⁻¹ * s ^ (j : ℕ) = (ρ * s ^ (i : ℕ))⁻¹ * (ρ * s ^ (j : ℕ)) := by group
          _ = (s ^ (kf j : ℕ) * n i)⁻¹ * (s ^ (kf j : ℕ) * n j) := by rw [h1, h2]
          _ = (n i)⁻¹ * n j := by group
      rw [e]; exact N.mul_mem (N.inv_mem (hn i)) (hn j)
    have hs1' : s⁻¹ ∉ N := fun h => hs1 (by simpa using N.inv_mem h)
    have hs2' : (s ^ 2)⁻¹ ∉ N := fun h => hs2 (by simpa using N.inv_mem h)
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd (by simpa using hmem) hs1
    · exact absurd (by simpa using hmem) hs2
    · exact absurd (by simpa using hmem) hs1'
    · rfl
    · exact absurd (by simpa [pow_two] using hmem) hs1
    · exact absurd (by simpa using hmem) hs2'
    · exact absurd (by simpa [pow_two, mul_assoc] using hmem) hs1'
    · rfl
  refine ⟨Equiv.ofBijective kf (Finite.injective_iff_bijective.1 hinj), fun j => ?_⟩
  exact ⟨n j, hn j, hkn j⟩

/-! ## Cubic algebra -/

theorem vieta_root {R : Type*} [CommRing R] (a b c : R) :
    a ^ 3 - (a + b + c) * a ^ 2 + (a * b + a * c + b * c) * a - a * b * c = 0 := by ring

theorem disc_eq {R : Type*} [CommRing R] (a b c : R) :
    (a + b + c) ^ 2 * (a * b + a * c + b * c) ^ 2 - 4 * (a * b + a * c + b * c) ^ 3 -
      4 * (a + b + c) ^ 3 * (a * b * c) + 18 * (a + b + c) * (a * b + a * c + b * c) * (a * b * c) -
      27 * (a * b * c) ^ 2 = ((a - b) * (a - c) * (b - c)) ^ 2 := by
  ring

/-! ## Pinning a polynomial by approximate values -/

/-- Integer polynomials of degree `≤ d` that are small at the points `p` vanish. -/
def Pins {n : ℕ} (d : ℕ) (p : Fin n → ℂ) (δ : Fin n → ℝ) : Prop :=
  ∀ Δ : ℤ[X], Δ.natDegree ≤ d → (∀ k, ‖aeval (p k) Δ‖ < δ k) → Δ = 0

/-- **Consumer of `Pins`.** An integer polynomial of degree `≤ d` close to `Z` at pinning points
equals `Z`. -/
theorem eq_of_pins {n d : ℕ} {p : Fin n → ℂ} {δ : Fin n → ℝ} (hp : Pins d p δ) {Q Z : ℤ[X]}
    (hQ : Q.natDegree ≤ d) (hZ : Z.natDegree ≤ d) (hnear : ∀ k, ‖aeval (p k) Q - aeval (p k) Z‖ < δ k) :
    Q = Z := by
  have h := hp (Q - Z) ((natDegree_sub_le _ _).trans (max_le hQ hZ)) (fun k => by
    rw [map_sub]; exact hnear k)
  exact sub_eq_zero.1 h

/-! ## Data -/

/-- `e₁` of `13¹² θ`, over `ℤ`. -/
noncomputable def Z1 : ℤ[X] :=
    @Z1@

/-- `e₂` of `13¹² θ`, over `ℤ`. -/
noncomputable def Z2 : ℤ[X] :=
    @Z2@

/-- `e₃` of `13¹² θ`, over `ℤ`. -/
noncomputable def Z3 : ℤ[X] :=
    @Z3@

/-- `e_1` over `ℚ`. -/
noncomputable def E1 : ℚ[X] := Z1.map (Int.castRingHom ℚ)

/-- `e_2` over `ℚ`. -/
noncomputable def E2 : ℚ[X] := Z2.map (Int.castRingHom ℚ)

/-- `e_3` over `ℚ`. -/
noncomputable def E3 : ℚ[X] := Z3.map (Int.castRingHom ℚ)


theorem Z1_natDegree : Z1.natDegree ≤ 2 := by unfold Z1; compute_degree
theorem Z2_natDegree : Z2.natDegree ≤ 4 := by unfold Z2; compute_degree
theorem Z3_natDegree : Z3.natDegree ≤ 6 := by unfold Z3; compute_degree

/-- The resolvent `Y³ - E1 Y² + E2 Y - E3 ∈ ℚ[t][Y]`. -/
noncomputable def Rs : ℚ[X][X] := X ^ 3 - C E1 * X ^ 2 + C E2 * X - C E3

/-- Its discriminant. -/
noncomputable def D : ℚ[X] :=
  E1 ^ 2 * E2 ^ 2 - 4 * E2 ^ 3 - 4 * E1 ^ 3 * E3 + 18 * E1 * E2 * E3 - 27 * E3 ^ 2

theorem Rs_monic : Rs.Monic := by
  unfold Rs; monicity!

/-- The three rational residues at `t = -7/5`. -/
noncomputable def a : Fin 3 → ℚ :=
  ![26960166619488512863648 / 25, -13745237327308063003232 / 25, -20930439694559250518624 / 25]

theorem a_injective : Function.Injective a := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [a] at h <;> rfl

theorem Rs_fibre : Rs.map (evalRingHom (-7 / 5 : ℚ)) = ∏ i, (X - C (a i)) := by
  have ha0 : a 0 = 26960166619488512863648 / 25 := rfl
  have ha1 : a 1 = -13745237327308063003232 / 25 := rfl
  have ha2 : a 2 = -20930439694559250518624 / 25 := rfl
  have h1 : E1.eval (-7 / 5) = a 0 + a 1 + a 2 := by
    rw [ha0, ha1, ha2]
    simp only [E1, Z1, eval_map, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eq_intCast]; norm_num
  have h2 : E2.eval (-7 / 5) = a 0 * a 1 + a 0 * a 2 + a 1 * a 2 := by
    rw [ha0, ha1, ha2]
    simp only [E2, Z2, eval_map, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eq_intCast]; norm_num
  have h3 : E3.eval (-7 / 5) = a 0 * a 1 * a 2 := by
    rw [ha0, ha1, ha2]
    simp only [E3, Z3, eval_map, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eq_intCast]; norm_num
  simp only [Rs, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    map_X, map_C, coe_evalRingHom, Fin.prod_univ_three]
  rw [h1, h2, h3]
  simp only [C_add, C_mul]
  ring

theorem disc_eval_zero_ne : D.eval 0 ≠ 0 := by
  simp only [D, E1, E2, E3, Z1, Z2, Z3, eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat, eval_map,
    eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eq_intCast]
  norm_num

end Sz8.Galois.Resolvent
