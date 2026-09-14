import Sz8.Monodromy.Specialization

/-!
Irreducibility of `h = f(X, -7/5)` over `ℚ`, from the factor-degree patterns of its
monic integral model modulo `11` and `31`.

Suppose the monic integral model `H` factors as `f * g` with `f`, `g` monic in `ℤ[X]`.
Modulo `p`, unique factorization makes `deg f` a sum of some of the certified factor
degrees. The kernel checks that the possible sums for `[1,1,7,…,7]` (at `11`) and
`[13,…,13]` (at `31`) meet only in `0` and `65`. Gauss's lemma transfers irreducibility
from `ℤ` to `ℚ`, and `H = h.scaleRoots c` transfers it to `h`.

Irreducibility gives `65 ∣ |Gal(h/ℚ)|`, and with the earlier result `455 ∣ |Gal(h/ℚ)|`.
-/

open Polynomial

namespace Sz8.Monodromy
open ListPoly

set_option maxRecDepth 100000

/-- The factor-degree subset sums modulo 11 and modulo 31 meet only in `0` and `65`. -/
theorem sums_meet_trivially :
    (sums (hbarCerts11.map fun c => c.low.length)).all (fun d =>
      !((sums (hbarCerts31.map fun c => c.low.length)).contains d) || d == 0 || d == 65) =
      true := by
  decide +kernel

/-- A monic integer factor of the model has degree equal to a sum of certified factor
degrees modulo `p`. -/
theorem natDegree_mem_sums_of_factor (p : ℕ) [Fact p.Prime] (primes : List ℕ)
    (hprimes : ∀ d ∈ primes, d.Prime) (certs : List RabinCert)
    (hcheck : checkCerts p primes certs = true)
    (hprod : eqL p (prodL p (certs.map fun c => c.low ++ [1])) (hbarL p) = true)
    {f g : ℤ[X]} (hf : f.Monic) (hfg : f * g = specInt.integralNormalization) :
    f.natDegree ∈ sums (certs.map fun c => c.low.length) := by
  have hdvd : f.map (Int.castRingHom (ZMod p)) ∣
      ((certs.map fun c => c.low ++ [1]).map (toPoly p)).prod := by
    rw [← integralNormalization_mod_eq_prod p certs hprod, ← hfg, Polynomial.map_mul]
    exact dvd_mul_right _ _
  have := natDegree_mem_sums_of_dvd primes hprimes certs hcheck (hf.map _) hdvd
  rwa [hf.natDegree_map] at this

/-- The monic integral model is irreducible over `ℤ`. -/
theorem specModel_irreducible : Irreducible specInt.integralNormalization := by
  have hH : specInt.integralNormalization.Monic := monic_integralNormalization specInt_ne_zero
  have hdeg : specInt.integralNormalization.natDegree = 65 := by
    rw [natDegree_integralNormalization, specInt_natDegree]
  rw [hH.irreducible_iff_natDegree]
  refine ⟨fun h1 => by rw [h1, natDegree_one] at hdeg; omega, ?_⟩
  intro f g hf hg hfg
  have h11 := natDegree_mem_sums_of_factor 11 [7] (by decide) hbarCerts11 hbarCerts11_check
    hbarCerts11_prod hf hfg
  have h31 := natDegree_mem_sums_of_factor 31 [13] (by decide) hbarCerts31 hbarCerts31_check
    hbarCerts31_prod hf hfg
  have hsum : f.natDegree + g.natDegree = 65 := by rw [← hf.natDegree_mul hg, hfg, hdeg]
  have hmeet := List.all_eq_true.mp sums_meet_trivially _ h11
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hmeet
  rcases hmeet with (h | h) | h
  · rw [List.contains_iff_mem.mpr h31] at h
    exact absurd h Bool.noConfusion
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- Over `ℚ`, the monic model is `h` with its roots scaled by `specScale`. -/
theorem specModel_map_eq_scaleRoots :
    specInt.integralNormalization.map (Int.castRingHom ℚ) =
      paperSpecialization.scaleRoots (specScale : ℚ) := by
  have hc : (specScale : ℚ) ≠ 0 := by exact_mod_cast specScale_ne_zero
  have key := congrArg (Polynomial.map (Int.castRingHom ℚ))
    (integralNormalization_mul_C_leadingCoeff specInt)
  rw [Polynomial.map_mul, map_C, map_scaleRoots _ _ _ (by simpa [specInt_leadingCoeff] using hc),
    specInt_map, mul_scaleRoots_of_noZeroDivisors, scaleRoots_C, specInt_leadingCoeff,
    eq_intCast, mul_comm] at key
  exact mul_left_cancel₀ (C_ne_zero.mpr hc) key

/-- `f(X, -7/5)` is irreducible over `ℚ`. -/
theorem paperSpecialization_irreducible : Irreducible paperSpecialization := by
  have hc : (specScale : ℚ) ≠ 0 := by exact_mod_cast specScale_ne_zero
  obtain ⟨hmonic, hdeg⟩ := paperSpecialization_monic_natDegree
  have hQ : Irreducible (paperSpecialization.scaleRoots (specScale : ℚ)) := by
    rw [← specModel_map_eq_scaleRoots, ← algebraMap_int_eq]
    exact ((monic_integralNormalization specInt_ne_zero)
      |>.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp specModel_irreducible
  -- Over a field, a nonzero polynomial is a unit exactly when it has degree `0`.
  have unit_of : ∀ a : ℚ[X], a ≠ 0 → IsUnit (a.scaleRoots (specScale : ℚ)) → IsUnit a := by
    intro a ha hu
    have h0 := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_scaleRoots] at h0
    rw [isUnit_iff_degree_eq_zero, degree_eq_natDegree ha, h0, Nat.cast_zero]
  refine irreducible_iff.mpr ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu
    omega
  · have hab0 : a * b ≠ 0 := hab ▸ hmonic.ne_zero
    have hsplit := congrArg (fun q => q.scaleRoots (specScale : ℚ)) hab
    simp only [mul_scaleRoots_of_noZeroDivisors] at hsplit
    rcases hQ.isUnit_or_isUnit hsplit with h | h
    · exact Or.inl (unit_of a (left_ne_zero_of_mul hab0) h)
    · exact Or.inr (unit_of b (right_ne_zero_of_mul hab0) h)

/-- In characteristic zero, irreducibility implies separability. -/
theorem paperSpecialization_separable : paperSpecialization.Separable :=
  paperSpecialization_irreducible.separable

/-- Transitivity on the 65 roots: `65` divides the order of the Galois group. -/
theorem sixtyFive_dvd_card_gal : 65 ∣ Nat.card paperSpecialization.Gal := by
  rw [Gal.card_of_separable paperSpecialization_separable]
  have := paperSpecialization_irreducible.natDegree_dvd_finrank
    (SplittingField.splits paperSpecialization)
  rwa [paperSpecialization_monic_natDegree.2] at this

/-- Together with `ninetyOne_dvd_card_gal`: `455 = 5 · 7 · 13` divides `|Gal(h/ℚ)|`. -/
theorem fourHundredFiftyFive_dvd_card_gal : 455 ∣ Nat.card paperSpecialization.Gal :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 5 91)
    ((by norm_num : 5 ∣ 65).trans sixtyFive_dvd_card_gal) ninetyOne_dvd_card_gal

end Sz8.Monodromy
