import Sz8.Monodromy.PaperCovering
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.PolynomialAlgebra
import Sz8.Galois.Resolvent
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# A monic integer model of the family

Every input term `c X^i t^j` has `13^(195 - 3i) c ∈ ℤ` (`terms_ok`, a kernel check), so
`fZ = Σ 13^(195-3i) c t^j X^i ∈ ℤ[t][X]` is monic of degree 65 (`fZ_monic`) and
`fZ(13³ x, t) = 13¹⁹⁵ f(x, t)` (`fZ_eval`): the roots scaled by `13³` are integral over `ℤ[t]`.

`int_of_isIntegral`: a polynomial over `ℚ` integral over `ℤ[X]` has integer coefficients.
-/

open Polynomial

namespace Sz8.Galois.IntModel

open Sz8.Monodromy

/-- The term check: `i ≤ 65` and `13^(195 - 3i) c` is an integer. -/
def termOK (a : ℕ × ℕ × ℚ) : Bool := decide (a.1 ≤ 65) && (a.2.2 * 13 ^ (195 - 3 * a.1)).den == 1

theorem terms_ok : famTerms.all termOK = true := by decide +kernel

/-- The integer coefficient of a term. -/
def zc (a : ℕ × ℕ × ℚ) : ℤ := (a.2.2 * 13 ^ (195 - 3 * a.1)).num

/-- `fZ ∈ ℤ[t][X]`. -/
noncomputable def fZ : ℤ[X][X] :=
  famTerms.foldr (fun a acc => C (C (zc a) * X ^ a.2.1) * X ^ a.1 + acc) 0

theorem foldr_coeff (ts : List (ℕ × ℕ × ℚ)) (m : ℕ) :
    (ts.foldr (fun a acc => C (C (zc a) * X ^ a.2.1) * X ^ a.1 + acc) (0 : ℤ[X][X])).coeff m =
      ((ts.filter fun a => a.1 == m).map fun a => C (zc a) * X ^ a.2.1).sum := by
  induction ts with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons] at ih ⊢
    rw [coeff_add, ih, coeff_C_mul_X_pow]
    by_cases h : a.1 = m
    · simp [h]
    · simp [h, Ne.symm h]

/-- **`fZ` is monic.** -/
theorem fZ_monic : fZ.Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one 65 ?_ ?_
  · refine natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    rw [fZ, foldr_coeff]
    have hnil : famTerms.filter (fun a => a.1 == m) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      have := List.all_eq_true.1 famTerms_degree_le a ha
      simp only [decide_eq_true_eq] at this
      have hm' : 65 < m := by exact_mod_cast hm
      simp only [beq_iff_eq]; omega
    simp [hnil]
  · rw [fZ, foldr_coeff, famTerms_top]
    simp [zc]

theorem foldr_eval {L : Type*} [Field L] [Algebra ℚ L] (κ : ℤ[X] →+* L) {t : L} (ht : κ X = t)
    (x : L) (ts : List (ℕ × ℕ × ℚ)) (h : ∀ a ∈ ts, termOK a = true) :
    (ts.foldr (fun a acc => C (C (zc a) * X ^ a.2.1) * X ^ a.1 + acc) (0 : ℤ[X][X])).eval₂ κ
        (13 ^ 3 * x) =
      13 ^ 195 * ts.foldr (fun a acc => algebraMap ℚ L a.2.2 * t ^ a.2.1 * x ^ a.1 + acc) 0 := by
  induction ts with
  | nil => simp
  | cons a l ih =>
    have ha := h a (List.mem_cons_self ..)
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [termOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ha
    rw [List.foldr_cons, List.foldr_cons, eval₂_add, ih', eval₂_mul, eval₂_C, eval₂_X_pow, map_mul,
      map_pow, ht, mul_add]
    congr 1
    have hz : (κ (C (zc a)) : L) = algebraMap ℚ L a.2.2 * 13 ^ (195 - 3 * a.1) := by
      have h1 : κ (C (zc a)) = ((zc a : ℤ) : L) :=
        congrArg (· (zc a)) (RingHom.ext_int (κ.comp C) (Int.castRingHom L))
      rw [h1, zc, ← map_intCast (algebraMap ℚ L), Rat.coe_int_num_of_den_eq_one ha.2, map_mul,
        map_pow, map_ofNat]
    rw [hz]
    have e : 195 = (195 - 3 * a.1) + 3 * a.1 := by omega
    conv_rhs => rw [e, pow_add]
    rw [mul_pow, ← pow_mul]
    ring

/-- **Evaluation.** -/
theorem fZ_eval {L : Type*} [Field L] [Algebra ℚ L] (κ : ℤ[X] →+* L) {t : L} (ht : κ X = t)
    (x : L) : fZ.eval₂ κ (13 ^ 3 * x) =
      13 ^ 195 * famTerms.foldr (fun a acc => algebraMap ℚ L a.2.2 * t ^ a.2.1 * x ^ a.1 + acc) 0 :=
  foldr_eval κ ht x famTerms fun a ha => List.all_eq_true.1 terms_ok a ha

/-- **Integer coefficients.** A polynomial over `ℚ` integral over `ℤ[X]` (through `map`) comes from
`ℤ[X]`. -/
theorem int_of_isIntegral {Q : ℚ[X]} (h : (mapRingHom (Int.castRingHom ℚ)).IsIntegralElem Q) :
    ∃ Z : ℤ[X], Z.map (Int.castRingHom ℚ) = Q := by
  let := Polynomial.algebra (R := ℤ) (A := ℚ)
  have h' : IsIntegral ℤ[X] Q := h
  rw [Polynomial.isIntegral_iff_isIntegral_coeff] at h'
  have hc : ∀ n, Q.coeff n ∈ Set.range (Int.castRingHom ℚ) := fun n => by
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (h' n)
    exact ⟨z, hz⟩
  have hl : Q ∈ lifts (Int.castRingHom ℚ) := (lifts_iff_coeff_lifts Q).2 hc
  obtain ⟨Z, hZ⟩ := hl
  exact ⟨Z, hZ⟩

section Closure

variable {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A)

theorem isIntegralElem_add {a b : A} (ha : f.IsIntegralElem a) (hb : f.IsIntegralElem b) :
    f.IsIntegralElem (a + b) := by
  let := f.toAlgebra; exact IsIntegral.add ha hb

theorem isIntegralElem_mul {a b : A} (ha : f.IsIntegralElem a) (hb : f.IsIntegralElem b) :
    f.IsIntegralElem (a * b) := by
  let := f.toAlgebra; exact IsIntegral.mul ha hb

/-- The relative invariant of integral elements is integral. -/
theorem isIntegralElem_Θ {x : Fin 65 → A} (hx : ∀ i, f.IsIntegralElem (x i))
    (N : Subgroup (Equiv.Perm (Fin 65))) (π : Equiv.Perm (Fin 65)) :
    f.IsIntegralElem (Resolvent.Θ x N π) := by
  classical
  let := f.toAlgebra
  have hmem : ∀ i, x i ∈ integralClosure R A := hx
  change IsIntegral R (Resolvent.Θ x N π)
  unfold Resolvent.Θ Resolvent.mono
  exact (integralClosure R A).sum_mem fun n _ => (integralClosure R A).mul_mem
    ((integralClosure R A).mul_mem ((integralClosure R A).pow_mem (hmem _) 2) (hmem _)) (hmem _)

/-- Integrality descends along an injective ring hom. -/
theorem isIntegralElem_of_comp {B : Type*} [CommRing B] (g : A →+* B) (hg : Function.Injective g)
    {a : A} (h : (g.comp f).IsIntegralElem (g a)) : f.IsIntegralElem a := by
  obtain ⟨p, hpm, hp⟩ := h
  refine ⟨p, hpm, hg ?_⟩
  rw [Polynomial.hom_eval₂, map_zero]; exact hp

end Closure

end Sz8.Galois.IntModel
