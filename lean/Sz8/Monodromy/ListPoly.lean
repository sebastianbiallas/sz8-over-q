import HexBerlekampMathlib
import Mathlib.FieldTheory.Finite.Extension

/-!
Kernel-friendly polynomial arithmetic over `ZMod p`, and a Rabin certificate for
prime degree.

Polynomials are lists of natural-number coefficients in ascending order. Every
operation is structurally recursive and uses only `Nat` addition, multiplication,
remainder and comparison, which the Lean kernel evaluates with GMP. The
certificates supply all quotients, so the kernel never runs polynomial division.

For a monic `P` of prime degree `n` over `𝔽_p`, `checkRabin` verifies
`P ∣ X^(p^n) - X` and that `P` has no root in `𝔽_p`. Mathlib's
`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X` then forces every
irreducible factor to have degree `1` or `n`, hence `P` is irreducible.
-/

open Polynomial

namespace Sz8.Monodromy.ListPoly

section Arithmetic

variable (p : ℕ)

/-- Ascending natural-number coefficients, read in `ZMod p` by Horner's rule. -/
noncomputable def toPoly : List ℕ → (ZMod p)[X]
  | [] => 0
  | a :: as => C (a : ZMod p) + X * toPoly as

def addL : List ℕ → List ℕ → List ℕ
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) % p :: addL as bs

def smulL (c : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: as => c * a % p :: smulL c as

def mulL : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: as, bs => addL p (smulL p a bs) (0 :: mulL as bs)

def isZeroL : List ℕ → Bool
  | [] => true
  | a :: as => a % p == 0 && isZeroL as

/-- Equality of the represented polynomials, allowing trailing zeros. -/
def eqL : List ℕ → List ℕ → Bool
  | [], bs => isZeroL p bs
  | a :: as, [] => isZeroL p (a :: as)
  | a :: as, b :: bs => a % p == b % p && eqL as bs

/-- Horner evaluation at a natural number, reduced modulo `p`. -/
def evalL (x : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: as => (a + x * evalL x as) % p

/-- The coefficient list of `X ^ k`. -/
def xPowL : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => 0 :: xPowL k

@[simp] theorem toPoly_nil : toPoly p [] = 0 := rfl

@[simp] theorem toPoly_cons (a : ℕ) (as : List ℕ) :
    toPoly p (a :: as) = C (a : ZMod p) + X * toPoly p as := rfl

theorem toPoly_addL : ∀ as bs, toPoly p (addL p as bs) = toPoly p as + toPoly p bs
  | [], bs => by simp [addL]
  | a :: as, [] => by simp [addL]
  | a :: as, b :: bs => by
    simp only [addL, toPoly_cons, toPoly_addL as bs, ZMod.natCast_mod, Nat.cast_add, C_add]
    ring

theorem toPoly_smulL (c : ℕ) :
    ∀ as, toPoly p (smulL p c as) = C (c : ZMod p) * toPoly p as
  | [] => by simp [smulL]
  | a :: as => by
    simp only [smulL, toPoly_cons, toPoly_smulL c as, ZMod.natCast_mod, Nat.cast_mul, C_mul]
    ring

theorem toPoly_mulL : ∀ as bs, toPoly p (mulL p as bs) = toPoly p as * toPoly p bs
  | [], bs => by simp [mulL]
  | a :: as, bs => by
    simp only [mulL, toPoly_addL, toPoly_smulL, toPoly_cons, toPoly_mulL as bs,
      Nat.cast_zero, C_0]
    ring

theorem toPoly_of_isZeroL : ∀ as, isZeroL p as = true → toPoly p as = 0
  | [], _ => rfl
  | a :: as, h => by
    simp only [isZeroL, Bool.and_eq_true, beq_iff_eq] at h
    have ha : (a : ZMod p) = 0 := by rw [← ZMod.natCast_mod, h.1, Nat.cast_zero]
    simp [ha, toPoly_of_isZeroL as h.2]

theorem toPoly_eq_of_eqL : ∀ as bs, eqL p as bs = true → toPoly p as = toPoly p bs
  | [], bs, h => (toPoly_of_isZeroL p bs h).symm
  | a :: as, [], h => toPoly_of_isZeroL p (a :: as) h
  | a :: as, b :: bs, h => by
    simp only [eqL, Bool.and_eq_true, beq_iff_eq] at h
    have hab : (a : ZMod p) = b := by rw [← ZMod.natCast_mod, h.1, ZMod.natCast_mod]
    simp [hab, toPoly_eq_of_eqL as bs h.2]

theorem eval_toPoly (x : ℕ) :
    ∀ as, (toPoly p as).eval (x : ZMod p) = (evalL p x as : ZMod p)
  | [] => by simp [evalL]
  | a :: as => by simp [evalL, eval_toPoly x as]

theorem evalL_lt (hp : 0 < p) (x : ℕ) : ∀ as, evalL p x as < p
  | [] => hp
  | _ :: _ => Nat.mod_lt _ hp

theorem toPoly_xPowL : ∀ k, toPoly p (xPowL k) = X ^ k
  | 0 => by simp [xPowL]
  | k + 1 => by simp [xPowL, toPoly_xPowL k, pow_succ']

/-- The coefficient list of `v * X ^ i`. -/
def monoL : ℕ → ℕ → List ℕ
  | 0, v => [v]
  | i + 1, v => 0 :: monoL i v

theorem toPoly_monoL : ∀ i v, toPoly p (monoL i v) = C (v : ZMod p) * X ^ i
  | 0, v => by simp [monoL]
  | i + 1, v => by simp [monoL, toPoly_monoL i v, pow_succ]; ring

theorem toPoly_append :
    ∀ as bs, toPoly p (as ++ bs) = toPoly p as + X ^ as.length * toPoly p bs
  | [], bs => by simp
  | a :: as, bs => by
    simp only [List.cons_append, toPoly_cons, toPoly_append as bs, List.length_cons]
    ring

theorem coeff_toPoly : ∀ (as : List ℕ) (m : ℕ), (toPoly p as).coeff m = (as.getD m 0 : ℕ)
  | [], m => by simp
  | a :: as, 0 => by simp
  | a :: as, m + 1 => by
    simp [coeff_X_mul, coeff_toPoly as m]

theorem degree_toPoly_lt (as : List ℕ) : (toPoly p as).degree < as.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_toPoly, List.getD_eq_getElem?_getD, List.getElem?_eq_none hm]
  simp

/-- `toPoly` of a Hex finite-field polynomial's canonical coefficient list is its
Mathlib image. -/
theorem toMathlibPolynomial_eq_toPoly [Hex.ZMod64.Bounds p] (q : Hex.FpPoly p) :
    HexPolyFpMathlib.toMathlibPolynomial q =
      toPoly p (q.coeffs.toList.map Hex.ZMod64.toNat) := by
  ext m
  rw [HexPolyFpMathlib.coeff_toMathlibPolynomial, coeff_toPoly]
  simp only [HexModArithMathlib.ZMod64.toZMod, Hex.DensePoly.coeff]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getD_eq_getD_getElem?,
    Array.getElem?_toList]
  cases q.coeffs[m]? <;> simp

end Arithmetic

section Rabin

variable {p : ℕ}

/-- The monic polynomial with lower coefficients `low`. -/
theorem toPoly_monic_eq (low : List ℕ) :
    toPoly p (low ++ [1]) = X ^ low.length + toPoly p low := by
  rw [toPoly_append]
  simp [add_comm]

theorem monic_toPoly (low : List ℕ) : (toPoly p (low ++ [1])).Monic := by
  rw [toPoly_monic_eq]
  exact monic_X_pow_add (degree_toPoly_lt p low)

theorem natDegree_toPoly [Nontrivial (ZMod p)] (low : List ℕ) : (toPoly p (low ++ [1])).natDegree = low.length := by
  rw [toPoly_monic_eq, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_toPoly_lt p low

variable [Fact p.Prime] (P : (ZMod p)[X])

/-- `Ms` lists representatives of `y ^ j, y ^ (j+1), …` in `AdjoinRoot P`. -/
def PowChain (y : AdjoinRoot P) : ℕ → List (List ℕ) → Prop
  | _, [] => True
  | j, m :: Ms => AdjoinRoot.mk P (toPoly p m) = y ^ j ∧ PowChain y (j + 1) Ms

variable (p) in
/-- Linear combination `∑ rᵢ • Msᵢ` of reduced representatives. -/
def lincomb : List ℕ → List (List ℕ) → List ℕ
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, m :: Ms => addL p (smulL p a m) (lincomb as Ms)

theorem lincomb_spec (y : AdjoinRoot P) :
    ∀ (rs : List ℕ) (Ms : List (List ℕ)) (j : ℕ), rs.length ≤ Ms.length →
      PowChain P y j Ms →
      AdjoinRoot.mk P (toPoly p (lincomb p rs Ms)) = y ^ j * aeval y (toPoly p rs)
  | [], Ms, j, _, _ => by simp [lincomb]
  | a :: as, [], j, h, _ => by simp at h
  | a :: as, m :: Ms, j, h, hc => by
    obtain ⟨hm, hc⟩ := hc
    have ih := lincomb_spec y as Ms (j + 1) (by simpa using h) hc
    simp only [lincomb, toPoly_addL, toPoly_smulL, map_add, map_mul, ih, hm, toPoly_cons,
      aeval_C, aeval_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
    ring

/-- Frobenius on `AdjoinRoot P`: raising a represented element to the `p`th power
substitutes `X ^ p`. -/
theorem mk_pow_card (rs : List ℕ) :
    AdjoinRoot.mk P (toPoly p rs) ^ p = aeval (AdjoinRoot.mk P (X ^ p)) (toPoly p rs) := by
  rw [← map_pow, ← ZMod.expand_card]
  induction rs with
  | nil => simp
  | cons a as ih =>
    simp only [toPoly_cons, map_add, map_mul, expand_C, expand_X, aeval_C, aeval_X, ih,
      AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

variable (p) in
/-- Check `m' ≡ m * B (mod P)` for consecutive entries, with supplied quotients. -/
def chainOK (PL B : List ℕ) : List ℕ → List (List ℕ) → List (List ℕ) → Bool
  | _, [], [] => true
  | m, m' :: Ms, q :: qs =>
      eqL p (mulL p m B) (addL p (mulL p q PL) m') && chainOK PL B m' Ms qs
  | _, _, _ => false

theorem powChain_of_chainOK (PL B : List ℕ) (y : AdjoinRoot (toPoly p PL))
    (hy : AdjoinRoot.mk (toPoly p PL) (toPoly p B) = y) :
    ∀ (m : List ℕ) (Ms qs : List (List ℕ)) (j : ℕ),
      AdjoinRoot.mk (toPoly p PL) (toPoly p m) = y ^ j →
      chainOK p PL B m Ms qs = true → PowChain (toPoly p PL) y (j + 1) Ms
  | _, [], [], _, _, _ => trivial
  | m, m' :: Ms, q :: qs, j, hm, h => by
    simp only [chainOK, Bool.and_eq_true] at h
    have heq := congrArg (AdjoinRoot.mk (toPoly p PL)) (toPoly_eq_of_eqL p _ _ h.1)
    simp only [toPoly_mulL, toPoly_addL, map_mul, map_add, AdjoinRoot.mk_self, mul_zero,
      zero_add, hm, hy] at heq
    have hm' : AdjoinRoot.mk (toPoly p PL) (toPoly p m') = y ^ (j + 1) := by
      rw [pow_succ]; exact heq.symm
    exact ⟨hm', powChain_of_chainOK PL B y hy m' Ms qs (j + 1) hm' h.2⟩
  | _, [], _ :: _, _, _, h => by simp [chainOK] at h
  | _, _ :: _, [], _, _, h => by simp [chainOK] at h

variable (p) in
/-- Iterate `r ↦ r ^ p (mod P)` `k` times from `r` and compare with `X`. -/
def frobCheck (Ms : List (List ℕ)) : ℕ → List ℕ → Bool
  | 0, rs => eqL p rs [0, 1]
  | k + 1, rs => decide (rs.length ≤ Ms.length) && frobCheck Ms k (lincomb p rs Ms)

theorem frobCheck_spec (Ms : List (List ℕ))
    (hc : PowChain P (AdjoinRoot.mk P (X ^ p)) 0 Ms) :
    ∀ (k : ℕ) (rs : List ℕ), frobCheck p Ms k rs = true →
      AdjoinRoot.mk P (toPoly p rs) ^ (p ^ k) = AdjoinRoot.mk P X
  | 0, rs, h => by
    have := toPoly_eq_of_eqL p _ _ h
    simp [this]
  | k + 1, rs, h => by
    simp only [frobCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [pow_succ', pow_mul, mk_pow_card, ← frobCheck_spec Ms hc k _ h.2,
      lincomb_spec P _ rs Ms 0 h.1 hc, pow_zero, one_mul]

/-- A Rabin certificate for a monic polynomial `low ++ [1]` of prime degree
`low.length`: `B = X^p mod P` with quotient `qB`, and `Ms = [B^1, …, B^(n-1)] mod P`
with quotients `qs`. -/
structure RabinCert where
  low : List ℕ
  qB : List ℕ
  B : List ℕ
  Ms : List (List ℕ)
  qs : List (List ℕ)

variable (p) in
def checkRabin (c : RabinCert) : Bool :=
  let PL := c.low ++ [1]
  eqL p (xPowL p) (addL p (mulL p c.qB PL) c.B) &&
    chainOK p PL c.B [1] c.Ms c.qs &&
    frobCheck p ([1] :: c.Ms) c.low.length [0, 1] &&
    (List.range p).all (fun a => evalL p a PL != 0)

theorem dvd_of_checkRabin (c : RabinCert) (h : checkRabin p c = true) :
    toPoly p (c.low ++ [1]) ∣ X ^ (p ^ c.low.length) - X := by
  simp only [checkRabin, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hB, hchain⟩, hfrob⟩, -⟩ := h
  set P := toPoly p (c.low ++ [1])
  have hy : AdjoinRoot.mk P (toPoly p c.B) = AdjoinRoot.mk P (X ^ p) := by
    have heq := congrArg (AdjoinRoot.mk P) (toPoly_eq_of_eqL p _ _ hB)
    simpa [toPoly_xPowL, toPoly_addL, toPoly_mulL, P, AdjoinRoot.mk_self] using heq.symm
  have hc : PowChain P (AdjoinRoot.mk P (X ^ p)) 0 ([1] :: c.Ms) :=
    ⟨by simp, powChain_of_chainOK _ c.B _ hy [1] c.Ms c.qs 0 (by simp) hchain⟩
  have hx := frobCheck_spec P _ hc _ [0, 1] hfrob
  rw [← AdjoinRoot.mk_eq_mk, map_pow]
  simpa using hx

theorem no_root_of_checkRabin (c : RabinCert) (h : checkRabin p c = true) (x : ZMod p) :
    (toPoly p (c.low ++ [1])).eval x ≠ 0 := by
  simp only [checkRabin, Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne,
    ne_eq] at h
  have hx := h.2 x.val (ZMod.val_lt x)
  rw [← ZMod.natCast_zmod_val x, eval_toPoly, ne_eq, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact hx (Nat.eq_zero_of_dvd_of_lt hdvd (evalL_lt p (Fact.out : p.Prime).pos _ _))

/-- Soundness: a passing Rabin certificate of prime degree proves irreducibility. -/
theorem irreducible_of_checkRabin (c : RabinCert) (hn : c.low.length.Prime)
    (h : checkRabin p c = true) : Irreducible (toPoly p (c.low ++ [1])) := by
  set P := toPoly p (c.low ++ [1]) with hP
  have hmonic : P.Monic := monic_toPoly c.low
  have hdeg : P.natDegree = c.low.length := natDegree_toPoly c.low
  have hP0 : P ≠ 0 := hmonic.ne_zero
  have hunit : ¬ IsUnit P := by
    intro hu
    have := natDegree_eq_zero_of_isUnit hu
    rw [hdeg] at this
    exact hn.ne_zero this
  obtain ⟨g, hg, hgP⟩ := WfDvdMonoid.exists_irreducible_factor hunit hP0
  have hgdvd : g ∣ X ^ (Nat.card (ZMod p)) ^ c.low.length - X := by
    rw [Nat.card_zmod]
    exact hgP.trans (dvd_of_checkRabin c h)
  have hd := hg.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hgdvd
  rcases hn.eq_one_or_self_of_dvd _ hd with h1 | hnd
  · obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one
      ((degree_eq_iff_natDegree_eq_of_pos (n := 1) one_pos).mpr h1)
    exact absurd (hx.dvd hgP) (no_root_of_checkRabin c h x)
  · exact (associated_of_dvd_of_natDegree_le hgP hP0 (by omega)).irreducible hg

/-- Linear factors need no certificate. -/
theorem irreducible_toPoly_linear (a : ℕ) : Irreducible (toPoly p ([a] ++ [1])) :=
  irreducible_of_degree_eq_one (by
    rw [degree_eq_natDegree (monic_toPoly [a]).ne_zero, natDegree_toPoly]; simp)

/-- Canonical coefficient representatives of a Hex finite-field polynomial. -/
def natCoeffs [Hex.ZMod64.Bounds p] (q : Hex.FpPoly p) : List ℕ :=
  q.coeffs.toList.map Hex.ZMod64.toNat

variable (p) in
/-- Every certificate is linear, or has an allowed prime degree and passes Rabin. -/
def checkCerts (primes : List ℕ) (certs : List RabinCert) : Bool :=
  certs.all fun c => c.low.length == 1 || (primes.contains c.low.length && checkRabin p c)

/-- Every certified polynomial in a passing certificate list is irreducible. -/
theorem irreducible_of_mem_checkCerts (primes : List ℕ) (hprimes : ∀ d ∈ primes, d.Prime)
    (certs : List RabinCert) (hcheck : checkCerts p primes certs = true) :
    ∀ c ∈ certs, Irreducible (toPoly p (c.low ++ [1])) := by
  intro c hc
  have hc' := List.all_eq_true.mp hcheck c hc
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.contains_iff_mem] at hc'
  rcases hc' with h1 | ⟨hd, hr⟩
  · obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
    rw [ha]
    exact irreducible_toPoly_linear a
  · exact irreducible_of_checkRabin c (hprimes _ hd) hr

/-- Kernel-checkable irreducibility of a whole list of Hex factors. -/
theorem irreducible_of_checkCerts [Hex.ZMod64.Bounds p] (primes : List ℕ)
    (hprimes : ∀ d ∈ primes, d.Prime) (qs : List (Hex.FpPoly p)) (certs : List RabinCert)
    (hmatch : qs.map natCoeffs = certs.map (fun c => c.low ++ [1]))
    (hcheck : checkCerts p primes certs = true) :
    ∀ q ∈ qs, Irreducible (HexPolyFpMathlib.toMathlibPolynomial q) := by
  intro q hq
  have hmem : natCoeffs q ∈ certs.map (fun c => c.low ++ [1]) :=
    hmatch ▸ List.mem_map_of_mem hq
  obtain ⟨c, hc, hcq⟩ := List.mem_map.mp hmem
  rw [toMathlibPolynomial_eq_toPoly, ← natCoeffs, ← hcq]
  exact irreducible_of_mem_checkCerts primes hprimes certs hcheck c hc

variable (p) in
/-- Product of the certified monic polynomials. -/
def prodL : List (List ℕ) → List ℕ
  | [] => [1]
  | l :: ls => mulL p l (prodL ls)

omit [Fact p.Prime] in
theorem toPoly_prodL : ∀ ls : List (List ℕ), toPoly p (prodL p ls) = (ls.map (toPoly p)).prod
  | [] => by simp [prodL]
  | l :: ls => by simp [prodL, toPoly_mulL, toPoly_prodL ls]

/-- All sums of sub-multisets (with repetition) of a list of degrees. -/
def sums : List ℕ → List ℕ
  | [] => [0]
  | a :: l => sums l ++ (sums l).map (a + ·)

theorem sum_mem_sums_of_sublist {l₁ l₂ : List ℕ} (h : l₁.Sublist l₂) : l₁.sum ∈ sums l₂ := by
  induction h with
  | slnil => simp [sums]
  | cons a _ ih => exact List.mem_append_left _ ih
  | cons_cons a _ ih => exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, by simp⟩)

theorem sum_mem_sums_of_le {s : Multiset ℕ} {l : List ℕ} (h : s ≤ l) : s.sum ∈ sums l := by
  obtain ⟨l₁, rfl⟩ := Quot.exists_rep s
  obtain ⟨l₂, hperm, hsub⟩ := Multiset.coe_le.mp h
  rw [show Multiset.sum (Quot.mk _ l₁) = l₁.sum from Multiset.sum_coe l₁, ← hperm.sum_eq]
  exact sum_mem_sums_of_sublist hsub

/-- Unique factorization: a monic divisor of a certified factorization has degree equal
to the sum of the degrees of some of its factors. -/
theorem natDegree_mem_sums_of_dvd (primes : List ℕ) (hprimes : ∀ d ∈ primes, d.Prime)
    (certs : List RabinCert) (hcheck : checkCerts p primes certs = true)
    {f : (ZMod p)[X]} (hf : f.Monic)
    (hdvd : f ∣ ((certs.map fun c => c.low ++ [1]).map (toPoly p)).prod) :
    f.natDegree ∈ sums (certs.map fun c => c.low.length) := by
  classical
  let m : Multiset (ZMod p)[X] := ((certs.map fun c => c.low ++ [1]).map (toPoly p) : List _)
  have hirr : ∀ q ∈ m, Irreducible q := by
    intro q hq
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hq)
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
    exact irreducible_of_mem_checkCerts primes hprimes certs hcheck c hc
  have hmonic : ∀ q ∈ m, q.Monic := by
    intro q hq
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hq)
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
    exact monic_toPoly c.low
  have hprod : m.prod = ((certs.map fun c => c.low ++ [1]).map (toPoly p)).prod := by
    simp [m]
  have hm0 : m.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => (hirr 0 h0).ne_zero rfl
  have hnf : UniqueFactorizationMonoid.normalizedFactors m.prod = m := by
    rw [UniqueFactorizationMonoid.normalizedFactors_prod_eq m hirr]
    conv_rhs => rw [← Multiset.map_id m]
    exact Multiset.map_congr rfl fun q hq => (hmonic q hq).normalize_eq_self
  have hle := (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
    hf.ne_zero hm0).mp (hprod ▸ hdvd)
  rw [hnf] at hle
  -- The degree of `f` is the sum of the degrees of its normalized factors.
  have hdeg : f.natDegree =
      ((UniqueFactorizationMonoid.normalizedFactors f).map natDegree).sum := by
    have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hf.ne_zero
    rw [← natDegree_multiset_prod _ (UniqueFactorizationMonoid.zero_notMem_normalizedFactors _),
      natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)]
  have hmapdeg : m.map natDegree = ((certs.map fun c => c.low.length : List ℕ) : Multiset ℕ) := by
    simp only [m, Multiset.map_coe, List.map_map]
    congr 1
    exact List.map_congr_left fun c _ => natDegree_toPoly c.low
  rw [hdeg]
  exact sum_mem_sums_of_le (hmapdeg ▸ Multiset.map_le_map hle)

end Rabin

end Sz8.Monodromy.ListPoly
