import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Polynomial.Content

/-!
# M2: a fixed Sylvester minor detects a gcd of degree exactly one

For `deg f = n + 1`, `deg g ≤ n`, the square matrix `mat f g n` represents

    (u, v) ↦ (coefficients of X^1, …, X^(2n) in u f + v g),   deg u, deg v < n,

i.e. the Sylvester matrix of `f`, `g` with the constant-coefficient row and the highest multiplier
of `g` removed. Its determinant `B f g n` is the fixed minor.

* `B_eq_zero`: a common divisor of degree `≥ 2` forces `B = 0` (no hypothesis on the exact
  degrees beyond the bounds).
* `B_ne_zero`: a common divisor `d` of degree one with coprime cofactors forces `B ≠ 0`, when
  `deg f = n + 1` exactly.
* `B_ne_zero_iff`: over a field, when `f`, `g` have a nonconstant common divisor,
  `B ≠ 0 ↔ deg gcd(f, g) = 1`.
* `rootMultiplicity_of_B_ne_zero`: in characteristic zero, `B f f' ≠ 0` means every root of `f`
  has multiplicity at most two and at most one root has multiplicity two. This is the form
  consumed at the nodes: the common root itself comes from the resultant identity.

For `f` of degree 65 this is `n = 64` and a `128 × 128` determinant.
-/

open Polynomial Finset Matrix

namespace Sz8.Galois.FixedMinor

variable {R : Type*} [CommRing R]

/-- Column `j`: `X^j f` for `j < n`, and `X^(j-n) g` otherwise. -/
noncomputable def col (f g : R[X]) (n j : ℕ) : R[X] :=
  if j < n then X ^ j * f else X ^ (j - n) * g

/-- Row `i` is the coefficient of `X^(i+1)`. -/
noncomputable def mat (f g : R[X]) (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) R :=
  Matrix.of fun i j => (col f g n j).coeff (i + 1)

/-- The fixed minor. -/
noncomputable def B (f g : R[X]) (n : ℕ) : R := (mat f g n).det

/-- A vector, read as a function on `ℕ`. -/
def ext {n : ℕ} (x : Fin (2 * n) → R) (i : ℕ) : R := if h : i < 2 * n then x ⟨i, h⟩ else 0

/-- The polynomial with coefficients `a 0, …, a (n-1)`. -/
noncomputable def poly (a : ℕ → R) (n : ℕ) : R[X] := ∑ i ∈ range n, C (a i) * X ^ i

theorem coeff_poly (a : ℕ → R) (n k : ℕ) : (poly a n).coeff k = if k < n then a k else 0 := by
  simp only [poly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

theorem natDegree_poly_lt (a : ℕ → R) {n : ℕ} (hn : 0 < n) : (poly a n).natDegree < n := by
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := n - 1) fun i hi => ?_) (by omega)
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := mem_range.1 hi
  omega

theorem poly_coeff_eq {p : R[X]} {n : ℕ} (hp : p.natDegree < n) : poly p.coeff n = p := by
  conv_rhs => rw [as_sum_range' p n hp]
  simp [poly, C_mul_X_pow_eq_monomial]

/-- The combination `∑ x_j col_j` is `u f + v g`. -/
theorem sum_col (f g : R[X]) {n : ℕ} (x : Fin (2 * n) → R) :
    ∑ j, C (x j) * col f g n j = poly (ext x) n * f + poly (fun i => ext x (n + i)) n * g := by
  have hx : ∑ j : Fin (2 * n), C (x j) * col f g n j
      = ∑ j : Fin (2 * n), C (ext x j) * col f g n j :=
    sum_congr rfl fun j _ => by simp [ext]
  rw [hx, Fin.sum_univ_eq_sum_range (fun j => C (ext x j) * col f g n j) (2 * n), two_mul,
    sum_range_add, poly, poly, sum_mul, sum_mul]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    rw [col, if_pos (mem_range.1 hi), mul_assoc]
  · refine sum_congr rfl fun i _ => ?_
    rw [col, if_neg (by omega), Nat.add_sub_cancel_left, mul_assoc]

theorem mulVec_apply (f g : R[X]) {n : ℕ} (x : Fin (2 * n) → R) (i : Fin (2 * n)) :
    (mat f g n *ᵥ x) i
      = (poly (ext x) n * f + poly (fun i => ext x (n + i)) n * g).coeff (i + 1) := by
  rw [← sum_col, finsetSum_coeff]
  simp only [Matrix.mulVec, dotProduct, mat, Matrix.of_apply, coeff_C_mul]
  exact sum_congr rfl fun _ _ => mul_comm _ _

variable {K : Type*} [Field K]

/-- **A common divisor of degree at least two kills the minor.** -/
theorem B_eq_zero {f g d : K[X]} {n : ℕ} (hf : f.natDegree ≤ n + 1) (hg : g.natDegree ≤ n)
    (hf0 : f ≠ 0) (hd : 2 ≤ d.natDegree) (hdf : d ∣ f) (hdg : d ∣ g) : B f g n = 0 := by
  obtain ⟨P, rfl⟩ := hdf
  obtain ⟨Q, rfl⟩ := hdg
  have hd0 : d ≠ 0 := by rintro rfl; simp at hf0
  have hP0 : P ≠ 0 := by rintro rfl; simp at hf0
  have hPn : P.natDegree < n := by
    rw [natDegree_mul hd0 hP0] at hf; omega
  have hQn : Q.natDegree < n := by
    by_cases hQ0 : Q = 0
    · subst hQ0; simp; omega
    · rw [natDegree_mul hd0 hQ0] at hg; omega
  have hn : 0 < n := by omega
  let x : Fin (2 * n) → K := fun j => if (j : ℕ) < n then Q.coeff j else -P.coeff (j - n)
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, fun h => hP0 ?_, ?_⟩
  · ext k
    by_cases hk : k < n
    · have := congrFun h ⟨n + k, by omega⟩
      simpa [x] using this
    · simp [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hPn (not_lt.1 hk))]
  · funext i
    rw [mulVec_apply]
    have hu : poly (ext x) n = Q := by
      rw [← poly_coeff_eq hQn]
      unfold poly
      refine sum_congr rfl fun k hk => ?_
      have hk := mem_range.1 hk
      simp [ext, x, show k < 2 * n by omega, hk]
    have hv : poly (fun k => ext x (n + k)) n = -P := by
      rw [← poly_coeff_eq (p := -P) (by rwa [natDegree_neg])]
      unfold poly
      refine sum_congr rfl fun k hk => ?_
      have hk := mem_range.1 hk
      simp [ext, x, show n + k < 2 * n by omega]
    rw [hu, hv]
    simp only [Pi.zero_apply]
    rw [show Q * (d * P) + -P * (d * Q) = 0 by ring, coeff_zero]

/-- **A common divisor of degree one with coprime cofactors keeps the minor nonzero.** -/
theorem B_ne_zero {f g d P Q : K[X]} {n : ℕ} (hf : f.natDegree = n + 1) (hg : g.natDegree ≤ n)
    (hd : d.natDegree = 1) (hfP : f = d * P) (hgQ : g = d * Q) (hPQ : IsCoprime P Q) :
    B f g n ≠ 0 := by
  intro h0
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hP0 : P ≠ 0 := by rintro rfl; simp [hfP] at hf0
  have hPn : P.natDegree = n := by
    rw [hfP, natDegree_mul hd0 hP0, hd] at hf; omega
  set u := poly (ext x) n with hu
  set v := poly (fun i => ext x (n + i)) n with hv
  have hn : 0 < n := by
    by_contra hn
    have : n = 0 := by omega
    subst this
    exact hx0 (funext fun i => i.elim0)
  have hun : u.natDegree < n := natDegree_poly_lt _ hn
  have hvn : v.natDegree < n := natDegree_poly_lt _ hn
  have hgn : g.natDegree ≤ n := hg
  -- `u f + v g` is constant
  set h := u * f + v * g with hh
  have hcoeff : ∀ k, 1 ≤ k → h.coeff k = 0 := by
    intro k hk
    by_cases hk2 : k ≤ 2 * n
    · have := congrFun hx ⟨k - 1, by omega⟩
      rw [mulVec_apply, Pi.zero_apply] at this
      rwa [show k - 1 + 1 = k by omega] at this
    · refine coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_add_le _ _) ?_)
      refine max_lt (lt_of_le_of_lt natDegree_mul_le ?_) (lt_of_le_of_lt natDegree_mul_le ?_) <;>
        omega
  have hC : h = C (h.coeff 0) := by
    ext k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [hcoeff k hk, coeff_C, if_neg (by omega)]
  -- the constant is divisible by `d`, hence zero
  have hdh : d ∣ h := by
    rw [hh, hfP, hgQ]; exact ⟨u * P + v * Q, by ring⟩
  have hh0 : h = 0 := by
    by_contra hne
    rw [hC] at hdh hne
    have hunit : IsUnit (C (h.coeff 0)) := isUnit_C.2 (by simpa using hne)
    have := natDegree_eq_zero_of_isUnit (isUnit_of_dvd_unit hdh hunit)
    omega
  -- cancel `d`, then `P ∣ v` and degree forces `v = 0`
  have hlin : u * P + v * Q = 0 := by
    have : d * (u * P + v * Q) = 0 := by rw [← hh0, hh, hfP, hgQ]; ring
    exact (mul_eq_zero.1 this).resolve_left hd0
  have hPv : P ∣ v * Q := ⟨-u, by linear_combination hlin⟩
  have hv0 : v = 0 := eq_zero_of_dvd_of_natDegree_lt (hPQ.dvd_of_dvd_mul_right hPv) (by omega)
  have hu0 : u = 0 := by
    rw [hv0, zero_mul, add_zero] at hh
    exact (mul_eq_zero.1 (hh ▸ hh0)).resolve_right hf0
  apply hx0
  funext j
  by_cases hj : (j : ℕ) < n
  · have := congrArg (fun p => p.coeff j) hu0
    simpa [hu, coeff_poly, hj, ext] using this
  · have := congrArg (fun p => p.coeff (j - n)) hv0
    simpa [hv, coeff_poly, show (j : ℕ) - n < n by omega, ext,
      show n + ((j : ℕ) - n) = j by omega] using this

/-- **The criterion.** Over a field, if `f` (of degree `n + 1`) and `g` (of degree `≤ n`) have a
nonconstant common divisor, the fixed minor is nonzero exactly when their gcd has degree one. -/
theorem B_ne_zero_iff [DecidableEq K] {f g : K[X]} {n : ℕ} (hf : f.natDegree = n + 1)
    (hg : g.natDegree ≤ n) (hcommon : ¬ IsUnit (GCDMonoid.gcd f g)) :
    B f g n ≠ 0 ↔ (GCDMonoid.gcd f g).natDegree = 1 := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hgcd0 : GCDMonoid.gcd f g ≠ 0 := by
    intro h; rw [_root_.gcd_eq_zero_iff] at h; exact hf0 h.1
  have hpos : 1 ≤ (GCDMonoid.gcd f g).natDegree := by
    by_contra h
    exact hcommon (isUnit_iff_degree_eq_zero.2
      (by rw [degree_eq_natDegree hgcd0]; simp; omega))
  constructor
  · intro hB
    by_contra h1
    exact hB (B_eq_zero hf.le hg hf0 (by omega) (GCDMonoid.gcd_dvd_left f g)
      (GCDMonoid.gcd_dvd_right f g))
  · intro h1
    exact B_ne_zero hf hg h1
      (EuclideanDomain.mul_div_cancel' hgcd0 (GCDMonoid.gcd_dvd_left f g)).symm
      (EuclideanDomain.mul_div_cancel' hgcd0 (GCDMonoid.gcd_dvd_right f g)).symm
      (isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hgcd0)

/-- **Characteristic zero, at a node.** If the minor of `f` and `f'` is nonzero, every root of `f`
has multiplicity at most two, and at most one root has multiplicity two. -/
theorem rootMultiplicity_of_B_ne_zero [CharZero K] {f : K[X]} {n : ℕ} (hf : f.natDegree = n + 1)
    (hB : B f (derivative f) n ≠ 0) :
    (∀ r, f.rootMultiplicity r ≤ 2) ∧
      ∀ r s, 2 ≤ f.rootMultiplicity r → 2 ≤ f.rootMultiplicity s → r = s := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hg : (derivative f).natDegree ≤ n := (natDegree_derivative_le f).trans (by omega)
  have hder : ∀ r, 1 ≤ f.rootMultiplicity r →
      f.rootMultiplicity r - 1 ≤ (derivative f).rootMultiplicity r := fun r _ =>
    rootMultiplicity_sub_one_le_derivative_rootMultiplicity f r
  have hd0 : derivative f ≠ 0 := by
    intro h
    have := natDegree_eq_zero_of_derivative_eq_zero h
    omega
  refine ⟨fun r => ?_, fun r s hr hs => ?_⟩
  · by_contra h3
    refine hB (B_eq_zero hf.le hg hf0 (d := (X - C r) ^ 2) (by simp) ?_ ?_)
    · exact (le_rootMultiplicity_iff hf0).1 (by omega)
    · exact (le_rootMultiplicity_iff hd0).1 ((show 2 ≤ f.rootMultiplicity r - 1 by omega).trans
        (hder r (by omega)))
  · by_contra hrs
    have hcop : IsCoprime (X - C r) (X - C s) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hrs).isUnit
    have dvd1 : ∀ p : K[X], p ≠ 0 → ∀ a, 1 ≤ p.rootMultiplicity a → X - C a ∣ p := fun p hp a ha =>
      by simpa using (le_rootMultiplicity_iff hp).1 ha
    refine hB (B_eq_zero hf.le hg hf0 (d := (X - C r) * (X - C s))
      (by rw [natDegree_mul (X_sub_C_ne_zero r) (X_sub_C_ne_zero s)]; simp) ?_ ?_)
    · exact hcop.mul_dvd (dvd1 f hf0 r (by omega)) (dvd1 f hf0 s (by omega))
    · exact hcop.mul_dvd (dvd1 _ hd0 r ((by omega : 1 ≤ f.rootMultiplicity r - 1).trans (hder r (by omega))))
        (dvd1 _ hd0 s ((by omega : 1 ≤ f.rootMultiplicity s - 1).trans (hder s (by omega))))

end Sz8.Galois.FixedMinor
