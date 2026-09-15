import Sz8.Monodromy.Inputs
import Sz8.Monodromy.SpecCerts
import Sz8.Monodromy.GaloisDegree

/-!
The specialization `h = f(X, -7/5)` over `ℚ`, and the arithmetic input used by
the paper's specialization section: `91` divides the order of `Gal(h/ℚ)`.

`h` is defined term by term from the exact input. Its integral model is
`G = 5^7 13^182 h ∈ ℤ[X]`. All relations between `h`, `G`, the monic model
`integralNormalization G`, and its reductions modulo `11` and `31` are proved
from kernel-checked Boolean facts about the input terms. No large integer
coefficient of the monic model is ever written down.
-/

open Polynomial

namespace Sz8.Monodromy
open ListPoly

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- The specialization `f(X, -7/5) ∈ ℚ[X]` of the exact input. -/
noncomputable def paperSpecialization : ℚ[X] :=
  inputTerms.foldr (fun a acc =>
    C ((a.2.2.1 : ℚ) / a.2.2.2 * (-7 / 5 : ℚ) ^ a.2.1) * X ^ a.1 + acc) 0

/-- A common denominator of all input coefficients. -/
def specDen : ℕ := 13 ^ 182

/-- The leading coefficient of the integral model. -/
def specScale : ℤ := 5 ^ 7 * specDen

/-- `specScale * (n/d) * (-7/5)^j`, an integer whenever `d ∣ specDen` and `j ≤ 7`. -/
def termInt (a : ℕ × ℕ × ℤ × ℕ) : ℤ :=
  a.2.2.1 * ((specDen / a.2.2.2 : ℕ) : ℤ) * (-7) ^ a.2.1 * 5 ^ (7 - a.2.1)

/-- The integral model `specScale * f(X, -7/5)`. -/
noncomputable def specInt : ℤ[X] :=
  inputTerms.foldr (fun a acc => C (termInt a) * X ^ a.1 + acc) 0

def termOK (a : ℕ × ℕ × ℤ × ℕ) : Bool :=
  a.2.2.2 != 0 && a.2.2.2 * (specDen / a.2.2.2) == specDen && decide (a.2.1 ≤ 7) &&
    decide (a.1 ≤ 65)

theorem terms_ok : inputTerms.all termOK = true := by decide +kernel

theorem termInt_cast (a : ℕ × ℕ × ℤ × ℕ) (h : termOK a = true) :
    (termInt a : ℚ) = specScale * ((a.2.2.1 : ℚ) / a.2.2.2 * (-7 / 5 : ℚ) ^ a.2.1) := by
  obtain ⟨i, j, n, d⟩ := a
  simp only [termOK, specScale, termInt, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨hd, hD⟩, hj⟩, -⟩ := h
  generalize specDen = D at hD ⊢
  generalize D / d = e at hD ⊢
  subst hD
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have h5 : (5 : ℚ) ^ (7 - j) = 5 ^ 7 / 5 ^ j := pow_sub₀ _ (by norm_num) hj
  push_cast
  rw [h5, div_pow]
  field_simp
  ring

section Foldr

variable (ts : List (ℕ × ℕ × ℤ × ℕ))

private noncomputable def foldQ : ℚ[X] :=
  ts.foldr (fun a acc => C ((a.2.2.1 : ℚ) / a.2.2.2 * (-7 / 5 : ℚ) ^ a.2.1) * X ^ a.1 + acc) 0

private noncomputable def foldZ : ℤ[X] :=
  ts.foldr (fun a acc => C (termInt a) * X ^ a.1 + acc) 0

/-- The coefficient of `X^n` in the integral model, as a finite sum. -/
def coeffSum (n : ℕ) : ℤ := ts.foldr (fun a s => (if a.1 = n then termInt a else 0) + s) 0

theorem foldZ_map (h : ts.all termOK = true) :
    (foldZ ts).map (Int.castRingHom ℚ) = C (specScale : ℚ) * foldQ ts := by
  induction ts with
  | nil => simp [foldZ, foldQ]
  | cons a ts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [foldZ, foldQ, List.foldr_cons] at ih ⊢
    rw [Polynomial.map_add, ih h.2, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
      eq_intCast, termInt_cast a h.1]
    simp only [C_mul]
    ring

theorem natDegree_foldZ_le (h : ts.all termOK = true) : (foldZ ts).natDegree ≤ 65 := by
  induction ts with
  | nil => simp [foldZ]
  | cons a ts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ha : a.1 ≤ 65 := by
      have := h.1
      simp only [termOK, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
    simp only [foldZ, List.foldr_cons] at ih ⊢
    exact natDegree_add_le_of_degree_le ((natDegree_C_mul_X_pow_le _ _).trans ha) (ih h.2)

theorem coeff_foldZ (n : ℕ) : (foldZ ts).coeff n = coeffSum ts n := by
  induction ts with
  | nil => simp [foldZ, coeffSum]
  | cons a ts ih =>
    simp only [foldZ, coeffSum, List.foldr_cons] at ih ⊢
    rw [coeff_add, coeff_C_mul_X_pow, ih]
    congr 1
    split_ifs <;> first | rfl | omega

/-- Coefficients of the integral model modulo `p`, as a list. -/
def modL (p : ℕ) : List ℕ :=
  ts.foldr (fun a acc => addL p (monoL a.1 (termInt a % (p : ℤ)).toNat) acc) []

theorem foldZ_mod (p : ℕ) [NeZero p] :
    (foldZ ts).map (Int.castRingHom (ZMod p)) = toPoly p (modL ts p) := by
  induction ts with
  | nil => simp [foldZ, modL]
  | cons a ts ih =>
    simp only [foldZ, modL, List.foldr_cons] at ih ⊢
    rw [Polynomial.map_add, ih, toPoly_addL, toPoly_monoL, Polynomial.map_mul, map_C,
      Polynomial.map_pow, map_X, eq_intCast]
    congr 2
    have hp : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_neZero p
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hp.ne'), ZMod.intCast_mod]

end Foldr

theorem paperSpecialization_eq : paperSpecialization = foldQ inputTerms := rfl
theorem specInt_eq : specInt = foldZ inputTerms := rfl

/-- `specInt` is `specScale` times `f(X, -7/5)`. -/
theorem specInt_map : specInt.map (Int.castRingHom ℚ) = C (specScale : ℚ) * paperSpecialization :=
  foldZ_map inputTerms terms_ok

theorem coeffSum_65 : coeffSum inputTerms 65 = specScale := by decide +kernel

theorem specScale_ne_zero : specScale ≠ 0 := by decide +kernel

theorem specInt_natDegree : specInt.natDegree = 65 :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_foldZ_le inputTerms terms_ok)
    (by rw [specInt_eq, coeff_foldZ, coeffSum_65]; exact specScale_ne_zero)

theorem specInt_leadingCoeff : specInt.leadingCoeff = specScale := by
  rw [leadingCoeff, specInt_natDegree, specInt_eq, coeff_foldZ, coeffSum_65]

/-- `f(X, -7/5)` is monic of degree `65`. -/
theorem paperSpecialization_monic_natDegree :
    paperSpecialization.Monic ∧ paperSpecialization.natDegree = 65 := by
  have hc : (specScale : ℚ) ≠ 0 := by exact_mod_cast specScale_ne_zero
  have hdeg := congrArg natDegree specInt_map
  have hlc := congrArg leadingCoeff specInt_map
  rw [natDegree_map_eq_of_injective (RingHom.injective_int _), natDegree_C_mul hc,
    specInt_natDegree] at hdeg
  rw [leadingCoeff_map_of_injective (RingHom.injective_int _), leadingCoeff_C_mul_of_isUnit
    (isUnit_iff_ne_zero.mpr hc), specInt_leadingCoeff, eq_intCast] at hlc
  exact ⟨by rw [Monic, ← mul_right_inj' hc, ← hlc, mul_one], hdeg.symm⟩

/-- Coefficients of the monic model `integralNormalization specInt` modulo `p`. -/
def hbarL (p : ℕ) : List ℕ :=
  (List.range 65).map (fun i =>
    (modL inputTerms p).getD i 0 * (specScale % (p : ℤ)).toNat ^ (64 - i) % p) ++ [1]

theorem integralNormalization_mod (p : ℕ) [NeZero p] :
    specInt.integralNormalization.map (Int.castRingHom (ZMod p)) = toPoly p (hbarL p) := by
  have hdeg : specInt.degree = (65 : ℕ) := by
    have h0 : specInt ≠ 0 :=
      ne_zero_of_natDegree_gt (n := 0) (by rw [specInt_natDegree]; norm_num)
    rw [degree_eq_natDegree h0, specInt_natDegree]
  have hmod := foldZ_mod inputTerms p
  have hp : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_neZero p
  have hc : (((specScale % (p : ℤ)).toNat : ℕ) : ZMod p) = (specScale : ZMod p) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hp.ne'), ZMod.intCast_mod]
  ext i
  rw [coeff_map, integralNormalization_coeff, hdeg, specInt_natDegree, specInt_leadingCoeff,
    coeff_toPoly]
  rcases lt_trichotomy i 65 with hi | rfl | hi
  · have hne : ((65 : ℕ) : WithBot ℕ) ≠ i := by exact_mod_cast hi.ne'
    have hci := congrArg (fun q => q.coeff i) hmod
    simp only [coeff_map, coeff_toPoly, ← specInt_eq] at hci
    simp only [hne, ↓reduceIte, hbarL, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < ((List.range 65).map _).length by simpa using hi),
      List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some, eq_intCast,
      Int.cast_mul, Int.cast_pow, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_mod, hc]
    -- `congr` closes the remaining coefficient equation with `hci`.
    congr 2
  · simp [hbarL]
  · have hne : ((65 : ℕ) : WithBot ℕ) ≠ i := by exact_mod_cast hi.ne
    simp only [hne, ↓reduceIte]
    rw [coeff_eq_zero_of_natDegree_lt (specInt_natDegree ▸ hi)]
    have hlen : (hbarL p).length ≤ i := by simp [hbarL]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]

theorem specInt_ne_zero : specInt ≠ 0 :=
  ne_zero_of_natDegree_gt (n := 0) (by rw [specInt_natDegree]; norm_num)

/-- A kernel-checked product identity identifies the monic model modulo `p` with the
product of the certified factors. -/
theorem integralNormalization_mod_eq_prod (p : ℕ) [NeZero p] (certs : List RabinCert)
    (hprod : eqL p (prodL p (certs.map fun c => c.low ++ [1])) (hbarL p) = true) :
    specInt.integralNormalization.map (Int.castRingHom (ZMod p)) =
      ((certs.map fun c => c.low ++ [1]).map (toPoly p)).prod := by
  rw [integralNormalization_mod, ← toPoly_eq_of_eqL p _ _ hprod, toPoly_prodL]

/-- Every certified irreducible factor degree of the monic model modulo `p` divides
the order of `Gal(f(X, -7/5) / ℚ)`. -/
theorem dvd_card_gal_of_certs (p : ℕ) [Fact p.Prime] (primes : List ℕ)
    (hprimes : ∀ d ∈ primes, d.Prime) (certs : List RabinCert)
    (hcheck : checkCerts p primes certs = true)
    (hprod : eqL p (prodL p (certs.map fun c => c.low ++ [1])) (hbarL p) = true) :
    ∀ c ∈ certs, c.low.length ∣ Nat.card paperSpecialization.Gal := by
  intro c hc
  have hdvd : toPoly p (c.low ++ [1]) ∣
      specInt.integralNormalization.map (Int.castRingHom (ZMod p)) := by
    rw [integralNormalization_mod_eq_prod p certs hprod]
    exact List.dvd_prod (List.mem_map_of_mem (List.mem_map_of_mem hc))
  have := natDegree_dvd_card_gal paperSpecialization specInt specScale specScale_ne_zero
    specInt_map specInt_leadingCoeff p _
    (irreducible_of_mem_checkCerts primes hprimes certs hcheck c hc) hdvd
  rwa [natDegree_toPoly] at this

/-- Kernel replay: all factors of the monic model modulo 11 are irreducible, and their
product is the model. -/
theorem hbarCerts11_check : checkCerts 11 [7] hbarCerts11 = true := by decide +kernel
theorem hbarCerts11_prod :
    eqL 11 (prodL 11 (hbarCerts11.map fun c => c.low ++ [1])) (hbarL 11) = true := by
  decide +kernel
theorem hbarCerts31_check : checkCerts 31 [13] hbarCerts31 = true := by decide +kernel
theorem hbarCerts31_prod :
    eqL 31 (prodL 31 (hbarCerts31.map fun c => c.low ++ [1])) (hbarL 31) = true := by
  decide +kernel

theorem seven_dvd_card_gal : 7 ∣ Nat.card paperSpecialization.Gal := by
  obtain ⟨c, hc, h7⟩ := List.any_eq_true.mp
    (show hbarCerts11.any (fun c => c.low.length == 7) = true by decide +kernel)
  have := dvd_card_gal_of_certs 11 [7] (by decide) hbarCerts11 hbarCerts11_check
    hbarCerts11_prod c hc
  rwa [beq_iff_eq.mp h7] at this

theorem thirteen_dvd_card_gal : 13 ∣ Nat.card paperSpecialization.Gal := by
  obtain ⟨c, hc, h13⟩ := List.any_eq_true.mp
    (show hbarCerts31.any (fun c => c.low.length == 13) = true by decide +kernel)
  have := dvd_card_gal_of_certs 31 [13] (by decide) hbarCerts31 hbarCerts31_check
    hbarCerts31_prod c hc
  rwa [beq_iff_eq.mp h13] at this

/-- The Galois group of `f(X, -7/5)` over `ℚ` has order divisible by `7 · 13 = 91`.
This is the arithmetic input of the paper's specialization argument: combined with
the embedding into `Sz(8)`, whose maximal subgroups have orders 448, 52, 20 and 14,
it forces the group to be all of `Sz(8)`. That group-theoretic step, and the
embedding, are not formalized here. -/
theorem ninetyOne_dvd_card_gal : 91 ∣ Nat.card paperSpecialization.Gal :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) seven_dvd_card_gal thirteen_dvd_card_gal

/-- The divisibility is not vacuous: the Galois group is finite, so `Nat.card` is its order. -/
theorem card_gal_pos : 0 < Nat.card paperSpecialization.Gal := Nat.card_pos

theorem card_gal_ge_ninetyOne : 91 ≤ Nat.card paperSpecialization.Gal :=
  Nat.le_of_dvd card_gal_pos ninetyOne_dvd_card_gal

end Sz8.Monodromy
