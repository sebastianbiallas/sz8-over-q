import Sz8.Monodromy.Continuation
import HexPolyMathlib.PolynomialEquivalence

open Complex Metric Polynomial Set

namespace Sz8.Monodromy

/-- Rational coefficient lists, in ascending order, interpreted by Horner's rule. -/
noncomputable def complexPoly : List ℚ → Polynomial ℂ
  | [] => 0
  | a :: cs => C (a : ℂ) + X * complexPoly cs

noncomputable def denseHorner : List ℚ → Hex.DensePoly ℚ
  | [] => 0
  | a :: cs => Hex.DensePoly.C a + Hex.DensePoly.monomial 1 1 * denseHorner cs

theorem denseHorner_to_complexPoly (cs : List ℚ) :
    (HexPolyMathlib.toPolynomial (denseHorner cs)).map (algebraMap ℚ ℂ) = complexPoly cs := by
  induction cs with
  | nil => simp [denseHorner, complexPoly]
  | cons a cs ih =>
    simp [denseHorner, complexPoly, HexPolyMathlib.toPolynomial_add,
      HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_monomial,
      Polynomial.monomial_one_one_eq_X, ih]

/-- Transfer an exact rational polynomial-composition certificate to ℂ. -/
theorem shifted_column (cs es : List ℚ) (s : ℚ) (linear : Bool)
    (h : (denseHorner cs).compose (Hex.DensePoly.C 20 + Hex.DensePoly.monomial 1 1) =
      Hex.DensePoly.C s * (denseHorner es + if linear then Hex.DensePoly.monomial 1 1 else 0)) :
    (complexPoly cs).comp (X + C 20) =
      C (s : ℂ) * (complexPoly es + if linear then X else 0) := by
  have h' := congrArg (fun p : Hex.DensePoly ℚ =>
    (HexPolyMathlib.toPolynomial p).map (algebraMap ℚ ℂ)) h
  cases linear <;>
    simpa [HexPolyMathlib.toPolynomial_compose, HexPolyMathlib.toPolynomial_add,
      HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_monomial,
      Polynomial.map_comp, denseHorner_to_complexPoly, Polynomial.monomial_one_one_eq_X,
      add_comm] using h'

/-- Exact rational majorant on |z| ≤ R. -/
def polyBound : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: cs, R => |a| + R * polyBound cs R

theorem polyBound_nonneg (cs : List ℚ) {R : ℚ} (hR : 0 ≤ R) :
    0 ≤ polyBound cs R := by
  induction cs with
  | nil => rfl
  | cons a cs ih => exact add_nonneg (abs_nonneg _) (mul_nonneg hR ih)

theorem norm_complexPoly_eval_le (cs : List ℚ) {R : ℚ} (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ (R : ℝ)) :
    ‖(complexPoly cs).eval z‖ ≤ (polyBound cs R : ℝ) := by
  induction cs with
  | nil => simp [complexPoly, polyBound]
  | cons a cs ih =>
    simp only [complexPoly, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, polyBound, Rat.cast_add, Rat.cast_mul,
      Rat.cast_abs]
    calc
      ‖(a : ℂ) + z * (complexPoly cs).eval z‖
          ≤ ‖(a : ℂ)‖ + ‖z * (complexPoly cs).eval z‖ := norm_add_le _ _
      _ ≤ |(a : ℝ)| + (R : ℝ) * (polyBound cs R : ℝ) := by
        rw [Complex.norm_ratCast, norm_mul]
        exact add_le_add le_rfl (mul_le_mul hz ih (norm_nonneg _) (by exact_mod_cast hR))

/-- Columns in ascending parameter degree; each column is in ascending X degree. -/
noncomputable def complexFamily : List (List ℚ) → ℂ → Polynomial ℂ
  | [], _ => 0
  | cs :: rest, t => complexPoly cs + C t * complexFamily rest t

def familyBound : List (List ℚ) → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | cs :: rest, R, H => polyBound cs R + H * familyBound rest R H

theorem norm_complexFamily_eval_le (cols : List (List ℚ))
    {R H : ℚ} (hR : 0 ≤ R) (hH : 0 ≤ H)
    {z t : ℂ} (hz : ‖z‖ ≤ (R : ℝ)) (ht : ‖t‖ ≤ (H : ℝ)) :
    ‖(complexFamily cols t).eval z‖ ≤ (familyBound cols R H : ℝ) := by
  induction cols with
  | nil => simp [complexFamily, familyBound]
  | cons cs rest ih =>
    simp only [complexFamily, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, familyBound, Rat.cast_add, Rat.cast_mul]
    calc
      ‖(complexPoly cs).eval z + t * (complexFamily rest t).eval z‖
          ≤ ‖(complexPoly cs).eval z‖ + ‖t * (complexFamily rest t).eval z‖ := norm_add_le _ _
      _ ≤ (polyBound cs R : ℝ) + (H : ℝ) * (familyBound rest R H : ℝ) := by
        rw [norm_mul]
        exact add_le_add (norm_complexPoly_eval_le cs hR hz)
          (mul_le_mul ht ih (norm_nonneg _) (by exact_mod_cast hH))

/-- A finite rational inequality certifies a single simple root for every
parameter in a complex disc. Rouché compares X + error with X. -/
theorem one_root_of_familyBound (cols : List (List ℚ))
    {R H : ℚ} (hR : 0 < R) (hH : 0 ≤ H)
    (hbound : familyBound cols R H < R) {t : ℂ} (ht : ‖t‖ ≤ (H : ℝ)) :
    HexRootsMathlib.rootsInDisc (X + complexFamily cols t) 0 (R : ℝ) = 1 := by
  classical
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have heq : HexRootsMathlib.rootsInDisc (X + complexFamily cols t) 0 (R : ℝ) =
      HexRootsMathlib.rootsInDisc X 0 (R : ℝ) := by
    apply HexRootsMathlib.rouche hRreal.le
    intro z hz
    have hz' : ‖z‖ = (R : ℝ) := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    simp only [Polynomial.eval_add, Polynomial.eval_X, add_sub_cancel_left]
    calc
      ‖(complexFamily cols t).eval z‖ ≤ (familyBound cols R H : ℝ) :=
        norm_complexFamily_eval_le cols hR.le hH hz'.le ht
      _ < (R : ℝ) := by exact_mod_cast hbound
      _ = ‖z‖ := hz'.symm
  rw [heq]
  simp only [HexRootsMathlib.rootsInDisc, Polynomial.roots_X]
  change Multiset.countP (fun x : ℂ => x ∈ ball 0 (R : ℝ)) (0 ::ₘ 0) = 1
  rw [Multiset.countP_cons]
  simp [Metric.mem_ball, hRreal]

end Sz8.Monodromy
