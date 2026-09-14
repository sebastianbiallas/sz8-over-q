import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Small group-theoretic tools

Conjugation of a subgroup as a subgroup, Sylow conjugacy specialised to subgroups of prime
order inside a fixed subgroup, and the version of Cauchy's theorem used by the order-91
argument. Nothing here is specific to the recorded permutations.
-/

namespace Sz8.Monodromy

open Subgroup
open scoped Pointwise

variable {Γ : Type*} [Group Γ]

/-- `k H k⁻¹`, as a subgroup. -/
def conjSub (k : Γ) (H : Subgroup Γ) : Subgroup Γ := H.map (MulAut.conj k).toMonoidHom

@[simp] theorem mem_conjSub {k : Γ} {H : Subgroup Γ} {x : Γ} :
    x ∈ conjSub k H ↔ k⁻¹ * x * k ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : k⁻¹ * (k * y * k⁻¹) * k = y := by group
    simpa [MulAut.conj, this] using hy
  · intro h
    refine ⟨k⁻¹ * x * k, h, ?_⟩
    show k * (k⁻¹ * x * k) * k⁻¹ = x
    group

theorem conjSub_le {k : Γ} {H K : Subgroup Γ} (hH : H ≤ K) (hk : k ∈ K) :
    conjSub k H ≤ K := by
  intro x hx
  rw [mem_conjSub] at hx
  have := hH hx
  have : k * (k⁻¹ * x * k) * k⁻¹ ∈ K := mul_mem (mul_mem hk this) (inv_mem hk)
  simpa [mul_assoc] using this

theorem card_conjSub (k : Γ) (H : Subgroup Γ) : Nat.card (conjSub k H) = Nat.card H :=
  (Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj k).toEquiv (fun x => by
    simp [conjSub, MulAut.conj, mul_assoc])).symm)

theorem mem_conjSub_of {k : Γ} {H : Subgroup Γ} {x : Γ} (h : k⁻¹ * x * k ∈ H) :
    x ∈ conjSub k H := mem_conjSub.mpr h

/-- **Sylow's second theorem** for subgroups of prime order, in the group `Γ`. -/
theorem exists_conj_of_card_eq_prime [Finite Γ] {p : ℕ} [Fact p.Prime] {A B : Subgroup Γ}
    (hA : Nat.card A = p) (hB : Nat.card B = p) (hfac : (Nat.card Γ).factorization p = 1) :
    ∃ g : Γ, ∀ x : Γ, (x ∈ B ↔ g⁻¹ * x * g ∈ A) := by
  have hA' : Nat.card A = p ^ (Nat.card Γ).factorization p := by rw [hA, hfac, pow_one]
  have hB' : Nat.card B = p ^ (Nat.card Γ).factorization p := by rw [hB, hfac, pow_one]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (Sylow.ofCard A hA') (Sylow.ofCard B hB')
  have h : (MulAut.conj g • A : Subgroup Γ) = B := by
    have := congrArg (fun P : Sylow p Γ => (P : Subgroup Γ)) hg
    simpa [Sylow.coe_subgroup_smul] using this
  refine ⟨g, fun x => ?_⟩
  rw [← h, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.conj, mul_assoc]

/-- The same, for subgroups of a fixed finite subgroup `K`: the conjugating element lies in `K`. -/
theorem exists_conj_mem_of_card_eq_prime [Finite Γ] {p : ℕ} [Fact p.Prime]
    {K A B : Subgroup Γ} (hAK : A ≤ K) (hBK : B ≤ K)
    (hA : Nat.card A = p) (hB : Nat.card B = p) (hfac : (Nat.card K).factorization p = 1) :
    ∃ g ∈ K, ∀ x ∈ K, (x ∈ B ↔ g⁻¹ * x * g ∈ A) := by
  have e : ∀ (C : Subgroup Γ) (h : C ≤ K), Nat.card (C.subgroupOf K) = Nat.card C :=
    fun C h => Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  obtain ⟨g, hg⟩ := exists_conj_of_card_eq_prime (Γ := K) (A := A.subgroupOf K)
    (B := B.subgroupOf K) (by rw [e _ hAK, hA]) (by rw [e _ hBK, hB]) hfac
  refine ⟨(g : Γ), g.2, fun x hx => ?_⟩
  have h := hg ⟨x, hx⟩
  simpa [Subgroup.mem_subgroupOf] using h

/-- Cauchy's theorem, for a subgroup and stated with `Nat.card`. -/
theorem exists_zpowers_card_eq [Finite Γ] {p : ℕ} [Fact p.Prime] {H : Subgroup Γ}
    (hp : p ∣ Nat.card H) :
    ∃ x ∈ H, Nat.card (Subgroup.zpowers x) = p ∧ Subgroup.zpowers x ≤ H := by
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H) p hp
  refine ⟨(y : Γ), y.2, ?_, ?_⟩
  · rw [Nat.card_zpowers, ← hy]
    exact orderOf_injective H.subtype Subtype.coe_injective y
  · rw [Subgroup.zpowers_le]
    exact y.2

end Sz8.Monodromy
