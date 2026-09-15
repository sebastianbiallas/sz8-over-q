import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.Polynomial.IntegralNormalization
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.GoingUp

/-!
From modular factor degrees to the order of the Galois group over `ℚ`.

The argument needs no Frobenius elements and no hypothesis on ramification or
separability at `p`. A monic integral model `H` of `h` splits over the ring of
integers of the splitting field `K`. So its reduction splits over the residue field
`k` of any prime `𝔓 ∣ p`. An irreducible factor of degree `d` of `H mod p` therefore
splits in `k`, giving `d ∣ [k : 𝔽_p] = f(𝔓 | p)`. For Galois `K/ℚ`, the residue degree
`f` divides `[K : ℚ] = |Gal(h)|`.
-/

open Polynomial NumberField

namespace Sz8.Monodromy

/-- If an integral model of `h` has an irreducible factor of degree `d` modulo a
prime `p`, then `d` divides the order of the Galois group of `h` over `ℚ`.

`G = c • h` with integer coefficients and leading coefficient `c`; its
`integralNormalization` is the monic integer polynomial whose roots are `c` times
the roots of `h`. No hypothesis on ramification or separability at `p` is needed:
the residue field of a prime of the splitting field above `p` contains a root of
the factor, and residue degrees divide the Galois degree. -/
theorem natDegree_dvd_card_gal (h : ℚ[X]) (G : ℤ[X]) (c : ℤ) (hc : c ≠ 0)
    (hG : G.map (Int.castRingHom ℚ) = C (c : ℚ) * h) (hlc : G.leadingCoeff = c)
    (p : ℕ) [Fact p.Prime] (g : (ZMod p)[X]) (hg : Irreducible g)
    (hdvd : g ∣ G.integralNormalization.map (Int.castRingHom (ZMod p))) :
    g.natDegree ∣ Nat.card h.Gal := by
  classical
  let K := h.SplittingField
  have : NumberField K := ⟨⟩
  -- Stated explicitly: synthesis misses it through the `ℚ`-algebra instance path.
  have : Normal ℚ K := SplittingField.instNormal h
  have : IsGalois ℚ K := ⟨⟩
  have hG0 : G ≠ 0 := by rintro rfl; exact hc (by simpa using hlc.symm)
  set H := G.integralNormalization with hHdef
  have hH : H.Monic := monic_integralNormalization hG0
  -- `G` and hence its scaled monic model `H` split over `K`.
  have hGK : (G.map (algebraMap ℤ K)).Splits := by
    have : G.map (algebraMap ℤ K) = C (c : K) * h.map (algebraMap ℚ K) := by
      rw [show algebraMap ℤ K = (algebraMap ℚ K).comp (Int.castRingHom ℚ) from
        RingHom.ext_int _ _, ← Polynomial.map_map, hG, Polynomial.map_mul, map_C, map_intCast]
    rw [this]
    exact (SplittingField.splits h).C_mul _
  have hcK : (algebraMap ℤ K) G.leadingCoeff ≠ 0 := by simpa [hlc] using hc
  have hHK : (H.map (algebraMap ℤ K)).Splits := by
    have h1 := hGK.scaleRoots ((algebraMap ℤ K) G.leadingCoeff)
    rw [← map_scaleRoots _ _ _ hcK, ← integralNormalization_mul_C_leadingCoeff,
      Polynomial.map_mul, map_C] at h1
    exact (splits_mul_iff_left (C_ne_zero.mpr hcK) (Splits.C _)).mp h1
  -- Its roots are algebraic integers, so it splits over `𝓞 K`.
  have hHO : (H.map (algebraMap ℤ (𝓞 K))).Splits := by
    apply Splits.of_splits_map_of_injective (i := algebraMap (𝓞 K) K)
      (RingOfIntegers.coe_injective)
    · rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    · intro a ha
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at ha
      have hroot : aeval a H = 0 := by
        rw [aeval_def, eval₂_eq_eval_map]
        exact (mem_roots (hH.map _).ne_zero).mp ha
      exact ⟨⟨a, ⟨H, hH, by rwa [aeval_def] at hroot⟩⟩, rfl⟩
  -- A maximal ideal of `𝓞 K` above `p`, and its residue field.
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ |>.isMaximal
      (by simpa using hpZ.ne_zero)
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  let := Ideal.Quotient.field P
  have : CharP (𝓞 K ⧸ P) p := by
    rw [CharP.charP_iff_prime_eq_zero Fact.out]
    have hmem : (p : 𝓞 K) ∈ P := by
      have : ((p : ℤ) : 𝓞 K) ∈ P := by
        rw [← algebraMap_int_eq, eq_intCast] at *
        exact (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).mp
          (Ideal.mem_span_singleton_self _)
      simpa using this
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  let : Algebra (ZMod p) (𝓞 K ⧸ P) := ZMod.algebra _ p
  -- The factor splits in the residue field.
  have hres : ((H.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p) (𝓞 K ⧸ P))).Splits := by
    have : (H.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p) (𝓞 K ⧸ P)) =
        (H.map (algebraMap ℤ (𝓞 K))).map (Ideal.Quotient.mk P) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      exact RingHom.ext_int _ _
    rw [this]
    exact hHO.map _
  have hgsplit : (g.map (algebraMap (ZMod p) (𝓞 K ⧸ P))).Splits :=
    hres.of_dvd ((hH.map _).map _).ne_zero (Polynomial.map_dvd _ hdvd)
  have hdeg := hg.natDegree_dvd_finrank hgsplit
  -- The residue degree over `𝔽_p` is the inertia degree, which divides `[K : ℚ]`.
  have : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P
    (Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)})
      (by simpa using hpZ.ne_zero) P)
  have hf : Module.finrank (ZMod p) (𝓞 K ⧸ P) = P.inertiaDeg ℤ := by
    have h1 := Ideal.natAbs_pow_inertiaDeg (p : ℤ) P
    have h2 : Nat.card (𝓞 K ⧸ P) = p ^ Module.finrank (ZMod p) (𝓞 K ⧸ P) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
    simp only [Int.natAbs_natCast] at h1
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (h2.symm.trans h1.symm)
  have hcard := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ)] at hcard
  refine hdeg.trans ?_
  change _ ∣ Nat.card Gal(K/ℚ)
  rw [hf, ← hcard]
  exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

end Sz8.Monodromy
