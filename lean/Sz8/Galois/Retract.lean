import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic

/-!
# A punctured half-plane has the fundamental group of the plane

If `U ⊆ ℂ` is convex and contains the closed unit disc about `a`, then the inclusion followed by
translation, `U ∖ {a} → ℂ ∖ {0}`, `z ↦ z - a`, is injective on fundamental groups at any base point at distance `1` from
`a`. The radial map `r z = a + (z - a) / max 1 ‖z - a‖` retracts `ℂ ∖ {a}` into the punctured
disc, fixes the base point, and the straight homotopy from a loop to its retraction stays in
`U ∖ {a}`: in `U` by convexity, away from `a` because the radial multiplier stays positive.

Only injectivity is needed, so only this one homotopy is built: generation of the image then
pulls back (`zpowers_eq_top_of_map_incl`). No chart and no second index computation are involved.
-/

open unitInterval

namespace Sz8.Galois.Retract

variable {a : ℂ} {U : Set ℂ}

/-- The radial factor `1 / max 1 ‖z - a‖`. -/
noncomputable def rad (a z : ℂ) : ℝ := 1 / max 1 ‖z - a‖

theorem rad_pos (a z : ℂ) : 0 < rad a z := by unfold rad; positivity

theorem continuous_rad (a : ℂ) : Continuous (rad a) := by
  unfold rad
  exact continuous_const.div (continuous_const.max (by fun_prop))
    fun z => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'

theorem rad_mul_norm_le (a z : ℂ) : rad a z * ‖z - a‖ ≤ 1 := by
  unfold rad
  rw [div_mul_eq_mul_div, one_mul, div_le_one (lt_of_lt_of_le one_pos (le_max_left _ _))]
  exact le_max_right _ _

theorem rad_eq_one {z : ℂ} (h : ‖z - a‖ = 1) : rad a z = 1 := by simp [rad, h]

/-- The radial retraction onto the closed unit disc about `a`. -/
noncomputable def retr (a z : ℂ) : ℂ := a + (rad a z : ℂ) * (z - a)

theorem retr_mem_ball (a z : ℂ) : retr a z ∈ Metric.closedBall a 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, retr, add_sub_cancel_left, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (rad_pos a z).le]
  exact rad_mul_norm_le a z

theorem retr_ne {z : ℂ} (hz : z ≠ a) : retr a z ≠ a := by
  intro h
  have : (rad a z : ℂ) * (z - a) = 0 := by rw [retr] at h; linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact (rad_pos a z).ne' (by exact_mod_cast h1)
  · exact hz (sub_eq_zero.mp h1)

@[fun_prop] theorem continuous_retr (a : ℂ) : Continuous (retr a) := by
  unfold retr
  exact continuous_const.add
    ((Complex.continuous_ofReal.comp (continuous_rad a)).mul (continuous_id.sub continuous_const))

/-- `U ∖ {a}` and `ℂ ∖ {a}`. -/
abbrev Y (a : ℂ) (U : Set ℂ) := {z : ℂ // z ∈ U ∧ z ≠ a}
abbrev Z (a : ℂ) := {z : ℂ // z ≠ a}

/-- The inclusion followed by translation of the puncture to `0`. -/
def incl (a : ℂ) (U : Set ℂ) : C(Y a U, Z 0) :=
  ⟨fun z => ⟨z.1 - a, sub_ne_zero.2 z.2.2⟩, by fun_prop⟩

theorem retr0_mem (hball : Metric.closedBall a 1 ⊆ U) (w : ℂ) :
    a + ((1 / max 1 ‖w‖ : ℝ) : ℂ) * w ∈ U := by
  have := retr_mem_ball a (w + a)
  simpa [retr, rad] using hball this

theorem retr0_ne {w : ℂ} (hw : w ≠ 0) : a + ((1 / max 1 ‖w‖ : ℝ) : ℂ) * w ≠ a := by
  have := retr_ne (a := a) (z := w + a) (by simpa using hw)
  simpa [retr, rad] using this

/-- The retraction from the punctured plane into `U ∖ {a}`. -/
noncomputable def retrMap (hball : Metric.closedBall a 1 ⊆ U) : C(Z 0, Y a U) :=
  ⟨fun w => ⟨a + ((1 / max 1 ‖(w : ℂ)‖ : ℝ) : ℂ) * w, retr0_mem hball w, retr0_ne w.2⟩, by
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.add ((Complex.continuous_ofReal.comp (continuous_const.div
      (continuous_const.max (continuous_norm.comp continuous_subtype_val))
      fun _ => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne')).mul continuous_subtype_val)⟩

theorem rad_le_one (a z : ℂ) : rad a z ≤ 1 := by
  unfold rad; rw [div_le_one (lt_of_lt_of_le one_pos (le_max_left _ _))]; exact le_max_left _ _

theorem retr_eq_self {z : ℂ} (h : ‖z - a‖ = 1) : retr a z = z := by
  simp [retr, rad_eq_one h]

/-- The straight homotopy from `z` to its retraction. -/
noncomputable def hval (a : ℂ) (s : ℝ) (z : ℂ) : ℂ := ((1 - s : ℝ) : ℂ) * z + (s : ℂ) * retr a z

theorem hval_mem (hU : Convex ℝ U) (hball : Metric.closedBall a 1 ⊆ U) {z : ℂ} (hz : z ∈ U)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : hval a s z ∈ U := by
  have := hU hz (hball (retr_mem_ball a z)) (sub_nonneg.2 h1) h0 (by ring)
  simpa [hval, Complex.real_smul] using this

theorem hval_ne {z : ℂ} (hz : z ≠ a) {s : ℝ} (_h0 : 0 ≤ s) (h1 : s ≤ 1) : hval a s z ≠ a := by
  have hfac : 0 < (1 - s) + s * rad a z := by
    nlinarith [rad_pos a z, rad_le_one a z, mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (rad_le_one a z))]
  intro h
  have : (((1 - s) + s * rad a z : ℝ) : ℂ) * (z - a) = 0 := by
    rw [hval, retr] at h; push_cast at h ⊢; linear_combination h
  rcases mul_eq_zero.mp this with h2 | h2
  · exact hfac.ne' (by exact_mod_cast h2)
  · exact hz (sub_eq_zero.mp h2)

@[fun_prop] theorem continuous_hval (a : ℂ) : Continuous fun p : ℝ × ℂ => hval a p.1 p.2 := by
  unfold hval; fun_prop

theorem retrMap_incl (hball : Metric.closedBall a 1 ⊆ U) {x : Y a U} (hx : ‖(x : ℂ) - a‖ = 1) :
    (retrMap hball).comp (incl a U) x = x := Subtype.ext (retr_eq_self hx)

/-- A loop in `U ∖ {a}` based at distance `1` from `a` is homotopic to its retraction. -/
noncomputable def retrHomotopy (hU : Convex ℝ U) (hball : Metric.closedBall a 1 ⊆ U)
    {x : Y a U} (hx : ‖(x : ℂ) - a‖ = 1) (δ : Path x x) :
    Path.Homotopy δ ((δ.map ((retrMap hball).comp (incl a U)).continuous).cast
      (retrMap_incl hball hx).symm (retrMap_incl hball hx).symm) where
  toFun p := ⟨hval a p.1 (δ p.2), hval_mem hU hball (δ p.2).2.1 p.1.2.1 p.1.2.2,
    hval_ne (δ p.2).2.2 p.1.2.1 p.1.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_hval a).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (δ.continuous.comp continuous_snd)))
  map_zero_left t := Subtype.ext (by simp [hval])
  map_one_left t := Subtype.ext (by simp [hval]; rfl)
  prop' s t ht := by
    rcases ht with rfl | rfl
    · apply Subtype.ext; simp [hval, retr_eq_self hx]; ring
    · apply Subtype.ext; simp [hval, retr_eq_self hx]; ring

/-- **The inclusion `U ∖ {a} → ℂ ∖ {a}` is injective on fundamental groups.** -/
theorem map_incl_injective (hU : Convex ℝ U) (hball : Metric.closedBall a 1 ⊆ U)
    {x : Y a U} (hx : ‖(x : ℂ) - a‖ = 1) :
    Function.Injective (FundamentalGroup.map (incl a U) x) := by
  have key : ∀ P : Path x x,
      (Path.Homotopic.Quotient.map
        (FundamentalGroup.map (incl a U) x (Path.Homotopic.Quotient.mk P) :
          Path.Homotopic.Quotient (incl a U x) (incl a U x)) (retrMap hball)).cast
        (retrMap_incl hball hx).symm (retrMap_incl hball hx).symm = Path.Homotopic.Quotient.mk P :=
    by
      intro P
      have hh : Path.Homotopic.Quotient.mk P = Path.Homotopic.Quotient.mk
          ((P.map ((retrMap hball).comp (incl a U)).continuous).cast
            (retrMap_incl hball hx).symm (retrMap_incl hball hx).symm) :=
        Quotient.sound ⟨retrHomotopy hU hball hx P⟩
      exact hh.symm
  intro p q hpq
  induction p using Path.Homotopic.Quotient.ind with | _ δ =>
  induction q using Path.Homotopic.Quotient.ind with | _ δ' =>
  have h := congrArg (fun P : FundamentalGroup (Z 0) (incl a U x) =>
    (Path.Homotopic.Quotient.map (P : Path.Homotopic.Quotient (incl a U x) (incl a U x))
      (retrMap hball)).cast (retrMap_incl hball hx).symm (retrMap_incl hball hx).symm) hpq
  exact (key δ).symm.trans (h.trans (key δ'))

/-- **Generation pulls back along the inclusion.** If the image of a loop generates `π₁(ℂ ∖ {a})`,
the loop generates `π₁(U ∖ {a})`. -/
theorem zpowers_eq_top_of_map_incl (hU : Convex ℝ U) (hball : Metric.closedBall a 1 ⊆ U)
    {x : Y a U} (hx : ‖(x : ℂ) - a‖ = 1) {γ : FundamentalGroup (Y a U) x}
    (h : Subgroup.zpowers (FundamentalGroup.map (incl a U) x γ) = ⊤) :
    Subgroup.zpowers γ = ⊤ := by
  rw [Subgroup.eq_top_iff'] at h ⊢
  intro δ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h (FundamentalGroup.map (incl a U) x δ))
  exact Subgroup.mem_zpowers_iff.mpr
    ⟨k, map_incl_injective hU hball hx (by rw [map_zpow, hk])⟩

end Sz8.Galois.Retract
