import Sz8.Monodromy.Shift0
import Sz8.Monodromy.Shift1
import Sz8.Monodromy.Shift2
import Sz8.Monodromy.Shift3
import Sz8.Monodromy.Shift4
import Sz8.Monodromy.Shift5
import Sz8.Monodromy.Shift6
import Sz8.Monodromy.Shift7

open Complex Metric Polynomial Set

namespace Sz8.Monodromy

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- The paper's original polynomial, organized as eight columns in t. -/
noncomputable def paperFamily (t : ℂ) : Polynomial ℂ := complexFamily originalColumns t

theorem shifted_family (t : ℂ) :
    (paperFamily t).comp (X + C 20) =
      C (stepScale : ℂ) * (X + complexFamily errorColumns t) := by
  have h0 := shifted_column originalColumn0 errorColumn0 stepScale true shift_certificate_0
  have h1 := shifted_column originalColumn1 errorColumn1 stepScale false shift_certificate_1
  have h2 := shifted_column originalColumn2 errorColumn2 stepScale false shift_certificate_2
  have h3 := shifted_column originalColumn3 errorColumn3 stepScale false shift_certificate_3
  have h4 := shifted_column originalColumn4 errorColumn4 stepScale false shift_certificate_4
  have h5 := shifted_column originalColumn5 errorColumn5 stepScale false shift_certificate_5
  have h6 := shifted_column originalColumn6 errorColumn6 stepScale false shift_certificate_6
  have h7 := shifted_column originalColumn7 errorColumn7 stepScale false shift_certificate_7
  simp only [paperFamily, originalColumns, errorColumns, complexFamily,
    Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.zero_comp]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  ring

theorem step_bound : familyBound errorColumns (1/10) (1/1000000) < 1/10 := by
  decide +kernel

theorem stepScale_ne_zero : stepScale ≠ 0 := by decide +kernel

theorem rootsInDisc_translate (p : Polynomial ℂ) (c : ℂ) (R : ℝ) :
    HexRootsMathlib.rootsInDisc (p.comp (X + C c)) 0 R =
      HexRootsMathlib.rootsInDisc p c R := by
  classical
  have h := Polynomial.map_roots_comp_C_mul_X_add_C p 1 c isUnit_one
  simp only [Polynomial.C_1, one_mul] at h
  unfold HexRootsMathlib.rootsInDisc
  rw [← h, Multiset.countP_map]
  simp [Metric.mem_ball, dist_eq_norm, Multiset.countP_eq_card_filter]

/-- Concrete continuation certificate for the actual degree-65 input:
the disc |X-20| < 1/10 contains exactly one root (with multiplicity)
for EVERY complex parameter |t| ≤ 10^-6. -/
theorem paper_one_root_during_step (t : ℂ) (ht : ‖t‖ ≤ (1/1000000 : ℝ)) :
    HexRootsMathlib.rootsInDisc (paperFamily t) 20 (1/10) = 1 := by
  rw [← rootsInDisc_translate, shifted_family]
  have hs : (stepScale : ℂ) ≠ 0 := by exact_mod_cast stepScale_ne_zero
  have h := one_root_of_familyBound errorColumns
    (R := 1/10) (H := 1/1000000) (by norm_num) (by norm_num) step_bound
    (t := t) (by simpa using ht)
  have hr : ((1/10 : ℚ) : ℝ) = (1/10 : ℝ) := by norm_num
  rw [hr] at h
  simpa only [HexRootsMathlib.rootsInDisc, Polynomial.roots_C_mul _ hs] using h

/-- Both endpoints, and the whole straight segment between them, lie in the
certified parameter disc. This is a nonzero actual parameter step. -/
theorem paper_real_segment (u : ℝ) (hu : u ∈ Set.Icc 0 1) :
    HexRootsMathlib.rootsInDisc (paperFamily ((u / 1000000 : ℝ) : ℂ)) 20 (1/10) = 1 := by
  apply paper_one_root_during_step
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hu.1 (by norm_num))]
  exact div_le_div_of_nonneg_right hu.2 (by norm_num)

end Sz8.Monodromy
