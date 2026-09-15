import Sz8.Monodromy.GroupCerts
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Summing over `N` through its stabiliser chain

`N = ⟨Ngens0⟩` has the certified chain with base points `0, 1, 2`, orbit lists of lengths `65, 64, 7`
and transversals `Ntv0, Ntv1, Ntv2`; the last stabiliser is trivial. Every element of `N` is
`Ntv0[a] · Ntv1[b] · Ntv2[c]` (sifting, `Nfix0`–`Nfix2`), and there are exactly `29120 = |N|` such
triples, so the factorisation is a bijection (`sum_lclosure`). No orbit list of the invariant is needed.
-/

namespace Sz8.Galois.NSum

open Sz8.Monodromy

theorem orb0_closed : ∀ k ∈ lclosure Ngens0, ∀ o ∈ Norb0, k o ∈ Norb0 :=
  mem_of_lclosure_apply fun s hs o ho => by
    have h : (Ngens0.all fun s => Norb0.all fun o => decide (s o ∈ Norb0)) = true := by decide +kernel
    simpa using (List.all_eq_true.mp ((List.all_eq_true.mp h) s hs)) o ho

theorem orb1_closed : ∀ k ∈ lclosure Ngens1, ∀ o ∈ Norb1, k o ∈ Norb1 :=
  mem_of_lclosure_apply fun s hs o ho => by
    have h : (Ngens1.all fun s => Norb1.all fun o => decide (s o ∈ Norb1)) = true := by decide +kernel
    simpa using (List.all_eq_true.mp ((List.all_eq_true.mp h) s hs)) o ho

theorem orb2_closed : ∀ k ∈ lclosure Ngens2, ∀ o ∈ Norb2, k o ∈ Norb2 :=
  mem_of_lclosure_apply fun s hs o ho => by
    have h : (Ngens2.all fun s => Norb2.all fun o => decide (s o ∈ Norb2)) = true := by decide +kernel
    simpa using (List.all_eq_true.mp ((List.all_eq_true.mp h) s hs)) o ho

theorem to0 : ∀ o ∈ Norb0, getAt Ntv0 Norb0 o 0 = o := by decide +kernel
theorem to1 : ∀ o ∈ Norb1, getAt Ntv1 Norb1 o 1 = o := by decide +kernel
theorem to2 : ∀ o ∈ Norb2, getAt Ntv2 Norb2 o 2 = o := by decide +kernel

theorem len0 : Norb0.length = 65 := by decide +kernel
theorem len1 : Norb1.length = 64 := by decide +kernel
theorem len2 : Norb2.length = 7 := by decide +kernel
theorem nd0 : Norb0.Nodup := by decide +kernel
theorem nd1 : Norb1.Nodup := by decide +kernel
theorem nd2 : Norb2.Nodup := by decide +kernel
theorem b0 : (0 : Fin 65) ∈ Norb0 := by decide +kernel
theorem b1 : (1 : Fin 65) ∈ Norb1 := by decide +kernel
theorem b2 : (2 : Fin 65) ∈ Norb2 := by decide +kernel

/-- The chain product. -/
def tprod (a : Fin 65) (b : Fin 64) (c : Fin 7) : Equiv.Perm (Fin 65) :=
  Ntv0.getD a 1 * Ntv1.getD b 1 * Ntv2.getD c 1

theorem tprod_mem (a : Fin 65) (b : Fin 64) (c : Fin 7) : tprod a b c ∈ lclosure Ngens0 :=
  (lclosure Ngens0).mul_mem ((lclosure Ngens0).mul_mem (Ntv0_mem a) (Nle1 (Ntv1_mem b)))
    (Nle2 (Ntv2_mem c))

/-- One sifting step: an element of `⟨S⟩` is the transversal element at its image of the base point
times an element fixing the base point. -/
theorem sift_step {S : List (Equiv.Perm (Fin 65))} {O : List (Fin 65)} {TV : List (Equiv.Perm (Fin 65))}
    {bp : Fin 65} (hclosed : ∀ k ∈ lclosure S, ∀ o ∈ O, k o ∈ O) (hb : bp ∈ O)
    (hto : ∀ o ∈ O, getAt TV O o bp = o) (hTV : ∀ i, TV.getD i 1 ∈ lclosure S)
    {k : Equiv.Perm (Fin 65)} (hk : k ∈ lclosure S) :
    ∃ i < O.length, TV.getD i 1 * ((TV.getD i 1)⁻¹ * k) = k ∧
      (TV.getD i 1)⁻¹ * k ∈ lclosure S ∧ ((TV.getD i 1)⁻¹ * k) bp = bp := by
  have ho := hclosed k hk bp hb
  refine ⟨O.idxOf (k bp), List.idxOf_lt_length_of_mem ho, by group, ?_, ?_⟩
  · exact (lclosure S).mul_mem ((lclosure S).inv_mem (hTV _)) hk
  · have h := hto (k bp) ho
    simp only [getAt] at h
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, h]

theorem tprod_surjective (k : Equiv.Perm (Fin 65)) (hk : k ∈ lclosure Ngens0) :
    ∃ a b c, tprod a b c = k := by
  obtain ⟨i, hi, hk1, hmem1, hfix1⟩ := sift_step orb0_closed b0 to0 Ntv0_mem hk
  have h1 := Nfix0 _ hmem1 hfix1
  obtain ⟨j, hj, hk2, hmem2, hfix2⟩ := sift_step orb1_closed b1 to1 Ntv1_mem h1
  have h2 := Nfix1 _ hmem2 hfix2
  obtain ⟨l, hl, hk3, hmem3, hfix3⟩ := sift_step orb2_closed b2 to2 Ntv2_mem h2
  have h3 := Nfix2 _ hmem3 hfix3
  have htriv : (Ntv2.getD l 1)⁻¹ * ((Ntv1.getD j 1)⁻¹ * ((Ntv0.getD i 1)⁻¹ * k)) = 1 := by
    have : lclosure Ngens3 = ⊥ := by simp [Ngens3, lclosure]
    rw [this, Subgroup.mem_bot] at h3
    exact h3
  refine ⟨⟨i, len0 ▸ hi⟩, ⟨j, len1 ▸ hj⟩, ⟨l, len2 ▸ hl⟩, ?_⟩
  rw [← hk1, ← hk2, ← hk3, htriv]
  simp [tprod, mul_assoc]

/-- **Summing over `N` through the chain.** -/
theorem sum_lclosure {M : Type*} [AddCommMonoid M] [Fintype (lclosure Ngens0)]
    (F : Equiv.Perm (Fin 65) → M) :
    ∑ n : lclosure Ngens0, F n = ∑ a : Fin 65, ∑ b : Fin 64, ∑ c : Fin 7, F (tprod a b c) := by
  classical
  let φ : Fin 65 × Fin 64 × Fin 7 → lclosure Ngens0 := fun x =>
    ⟨tprod x.1 x.2.1 x.2.2, tprod_mem _ _ _⟩
  have hsurj : Function.Surjective φ := fun k => by
    obtain ⟨a, b, c, h⟩ := tprod_surjective k k.2
    exact ⟨(a, b, c), Subtype.ext h⟩
  have hbij : Function.Bijective φ := by
    refine (Function.Surjective.bijective_of_nat_card_le hsurj ?_)
    rw [Ncard]; simp
  rw [← Fintype.sum_bijective φ hbij (fun x => F (tprod x.1 x.2.1 x.2.2)) (fun n => F n)
    (fun _ => rfl), Fintype.sum_prod_type, Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _]

theorem tv1_fix : ∀ b : Fin 64, Ntv1.getD b 1 0 = 0 := by decide +kernel
theorem tv2_fix : ∀ c : Fin 7, Ntv2.getD c 1 0 = 0 ∧ Ntv2.getD c 1 1 = 1 := by decide +kernel

/-- **Grouped form** of a sum of monomials over `N`: the outer factor depends on the first transversal
only, the middle on the first two. -/
theorem sum_mono_grouped {L : Type*} [CommRing L] [Fintype (lclosure Ngens0)] (x : Fin 65 → L)
    (π : Equiv.Perm (Fin 65)) :
    ∑ n : lclosure Ngens0, x ((π * n) 0) ^ 2 * x ((π * n) 1) * x ((π * n) 3) =
      ∑ a : Fin 65, x (π (Ntv0.getD a 1 0)) ^ 2 *
        ∑ b : Fin 64, x (π (Ntv0.getD a 1 (Ntv1.getD b 1 1))) *
          ∑ c : Fin 7, x (π (Ntv0.getD a 1 (Ntv1.getD b 1 (Ntv2.getD c 1 3)))) := by
  rw [sum_lclosure (fun n => x ((π * n) 0) ^ 2 * x ((π * n) 1) * x ((π * n) 3))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [tprod, Equiv.Perm.mul_apply, (tv2_fix c).1, (tv2_fix c).2, tv1_fix b]
  ring

end Sz8.Galois.NSum
