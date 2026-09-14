import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm

/-!
# Bounding a setwise stabilizer through a two-point stabilizer

`card_stabilizer_set_le`: if `G ≤ Sym(Fin n)` has two-point stabilizers of order at most `k`,
`a ≠ b` lie in a finite set `O`, and an explicit list of `k` distinct elements of `G` fixing `a`
and `b` contains no nontrivial element preserving `O`, then `|Stab_G(O)| ≤ |O| (|O| - 1)`.
Orbit–stabilizer is applied twice (the orbit of `a` lies in `O`, that of `b` in `O ∖ {a}`), and
the explicit list exhausts `G_(a,b)` by counting.
-/

open Pointwise MulAction

namespace Sz8.Galois.Stab13

variable {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))

theorem card_eq_orbit_mul_stabilizer {H : Type*} [Group H] [Finite H] {X : Type*} [MulAction H X]
    (x : X) : Nat.card H = Nat.card (orbit H x) * Nat.card (stabilizer H x) := by
  have h := index_stabilizer H x
  rw [← Nat.card_coe_set_eq] at h
  rw [← h, mul_comm, Subgroup.card_mul_index]

/-- Two-point stabilizers are small when all ordered pairs of distinct points are reachable. -/
theorem card_stabilizer_pair_le {x₀ y₀ : Fin n}
    (hreach : ∀ x y : Fin n, x ≠ y → ∃ g ∈ G, g x₀ = x ∧ g y₀ = y) {a b : Fin n} (hab : a ≠ b)
    {m : ℕ} (hm : Nat.card G ≤ (n * n - n) * m) :
    Nat.card (stabilizer G (a, b)) ≤ m := by
  have hsub : {p : Fin n × Fin n | p.1 ≠ p.2} ⊆ orbit G (a, b) := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨g₁, hg₁, h₁, h₂⟩ := hreach x y hxy
    obtain ⟨g₂, hg₂, h₃, h₄⟩ := hreach a b hab
    have e₃ : (⟨g₂, hg₂⟩ : G) • x₀ = a := h₃
    have e₄ : (⟨g₂, hg₂⟩ : G) • y₀ = b := h₄
    refine ⟨⟨g₁, hg₁⟩ * (⟨g₂, hg₂⟩ : G)⁻¹, ?_⟩
    simp only [mul_smul, Prod.smul_mk]
    refine Prod.ext ?_ ?_
    · show (⟨g₁, hg₁⟩ : G) • ((⟨g₂, hg₂⟩ : G)⁻¹ • a) = x
      rw [← e₃, inv_smul_smul]; exact h₁
    · show (⟨g₁, hg₁⟩ : G) • ((⟨g₂, hg₂⟩ : G)⁻¹ • b) = y
      rw [← e₄, inv_smul_smul]; exact h₂
  have hcard : Nat.card {p : Fin n × Fin n | p.1 ≠ p.2} = n * n - n := by
    have h : {p : Fin n × Fin n | p.1 ≠ p.2} =
        ((Finset.univ : Finset (Fin n)).offDiag : Set (Fin n × Fin n)) := by
      ext p; simp
    rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.offDiag_card]
    simp
  have horb := Nat.card_mono (Set.toFinite _) hsub
  have hGeq := card_eq_orbit_mul_stabilizer (H := G) (a, b)
  rw [hcard] at horb
  by_contra hlt
  push Not at hlt
  have hpos : 0 < n * n - n := by
    rcases Nat.eq_zero_or_pos (n * n - n) with h | h
    · have := Nat.card_pos (α := G); rw [h, zero_mul] at hm; omega
    · exact h
  have h1 : (n * n - n) * m < (n * n - n) * Nat.card (stabilizer G (a, b)) :=
    Nat.mul_lt_mul_of_pos_left hlt hpos
  have h2 := Nat.mul_le_mul_right (Nat.card (stabilizer G (a, b))) horb
  omega

/-- **Setwise stabilizer bound.** -/
theorem card_stabilizer_set_le (O : Finset (Fin n)) {a b : Fin n} (ha : a ∈ O) (hb : b ∈ O)
    (hab : a ≠ b) {k : ℕ} (hk : Nat.card (stabilizer G (a, b)) ≤ k)
    (E : List (Equiv.Perm (Fin n))) (hE : ∀ e ∈ E, e ∈ G ∧ e a = a ∧ e b = b) (hnd : E.Nodup)
    (hlen : k ≤ E.length) (hO : ∀ e ∈ E, (∀ x ∈ O, e x ∈ O) → e = 1) :
    Nat.card (stabilizer G (O : Set (Fin n))) ≤ O.card * (O.card - 1) := by
  classical
  set S := stabilizer G (O : Set (Fin n))
  have hSO : ∀ g : S, ∀ x ∈ O, ((g : G) : Equiv.Perm (Fin n)) x ∈ O := by
    intro g x hx
    have h1 : (g : G) • (O : Set (Fin n)) = O := g.2
    have h2 : (g : G) • x ∈ (g : G) • (O : Set (Fin n)) := Set.smul_mem_smul_set hx
    rw [h1] at h2
    exact h2
  -- the explicit list exhausts `G_(a,b)`
  set T : Set (Equiv.Perm (Fin n)) := Subtype.val '' (stabilizer G (a, b) : Set G)
  have hTcard : Nat.card T = Nat.card (stabilizer G (a, b)) := by
    rw [Nat.card_image_of_injective Subtype.val_injective]; rfl
  have hET : {e | e ∈ E} ⊆ T := by
    intro e he
    obtain ⟨hG, h1, h2⟩ := hE e he
    refine ⟨⟨e, hG⟩, ?_, rfl⟩
    show (⟨e, hG⟩ : G) • (a, b) = (a, b)
    exact Prod.ext h1 h2
  have hEcard : Nat.card {e | e ∈ E} = E.length := by
    have : {e | e ∈ E} = (E.toFinset : Set (Equiv.Perm (Fin n))) := by ext; simp
    rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  have hEq : {e | e ∈ E} = T :=
    (Set.toFinite T).eq_of_subset_of_card_le hET (by rw [hTcard, hEcard]; omega)
  -- orbit–stabilizer, twice
  have hS := card_eq_orbit_mul_stabilizer (H := S) a
  set U := stabilizer S a
  have hU := card_eq_orbit_mul_stabilizer (H := U) b
  have horbS : Nat.card (orbit S a) ≤ O.card := by
    have : orbit S a ⊆ (O : Set (Fin n)) := by
      rintro _ ⟨g, rfl⟩; exact hSO g a ha
    simpa [Nat.card_coe_set_eq, Set.ncard_coe_finset] using Nat.card_mono (Set.toFinite _) this
  have horbU : Nat.card (orbit U b) ≤ O.card - 1 := by
    have : orbit U b ⊆ ((O.erase a : Finset (Fin n)) : Set (Fin n)) := by
      rintro _ ⟨g, rfl⟩
      have hga : ((((g : S) : G)) : Equiv.Perm (Fin n)) a = a := g.2
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
      refine ⟨hSO g b hb, fun h => hab ?_⟩
      have h' : ((((g : S) : G)) : Equiv.Perm (Fin n)) b = ((((g : S) : G)) : Equiv.Perm (Fin n)) a := by
        rw [hga]; exact h
      exact (Equiv.injective _ h').symm
    have h := Nat.card_mono (Set.toFinite _) this
    rwa [Nat.card_coe_set_eq (s := ((O.erase a : Finset (Fin n)) : Set (Fin n))),
      Set.ncard_coe_finset, Finset.card_erase_of_mem ha] at h
  have hstabU : Nat.card (stabilizer U b) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun g h => ?_⟩, ⟨1⟩⟩
    suffices ∀ g : stabilizer U b, g = 1 by rw [this g, this h]
    intro g
    set p : Equiv.Perm (Fin n) := ((((g : U) : S) : G) : Equiv.Perm (Fin n))
    have hpa : p a = a := (g : U).2
    have hpb : p b = b := g.2
    have hpT : p ∈ T := ⟨((g : U) : S), Prod.ext hpa hpb, rfl⟩
    rw [← hEq] at hpT
    have hp1 : p = 1 := hO p hpT (hSO ((g : U) : S))
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    exact hp1
  rw [hS, hU, hstabU, mul_one]
  exact Nat.mul_le_mul horbS horbU

end Sz8.Galois.Stab13
