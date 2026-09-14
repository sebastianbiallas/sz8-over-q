import Sz8.Galois.LiftIndex
import Sz8.Monodromy.RootTransport

/-!
# Index of a left-nested polyline from sign data

The segment-wise form of `liftIndex_three_arcs`. A polyline `w 0 → w 1 → ⋯ → w (n+1) = w 0` is
lifted along `exp` one segment at a time, with *the same nesting* as the polyline itself: segment
`k` gets `log` for `k < q`, `log (-z) + πi` for `q ≤ k < r`, and `log z + 2πi` for `r ≤ k`. The
branches agree at the junctions `q` (upper half-plane) and `r` (lower half-plane), so the pieces
glue, and `exp` of the lift equals the polyline pointwise. No associativity is ever needed, which
is what lets this apply directly to the recorded `Chain.poly`.
-/

open Complex Sz8.Monodromy

namespace Sz8.Galois.PolyIndex

variable (w : ℕ → ℂ)

/-- Segment `k`. -/
noncomputable abbrev seg (k : ℕ) : Path (w k) (w (k + 1)) := MonicFamily.segment (w k) (w (k + 1))

/-- The left-nested polyline, in the shape of `Sz8.Monodromy.Chain.poly`. -/
noncomputable def polyC : (m : ℕ) → Path (w 0) (w (m + 1))
  | 0 => seg w 0
  | m + 1 => (polyC m).trans (seg w (m + 1))

theorem polyC_mem {S : Set ℂ} : ∀ m, (∀ k ≤ m, ∀ u, seg w k u ∈ S) → ∀ u, polyC w m u ∈ S
  | 0, h, u => h 0 le_rfl u
  | m + 1, h, u => by
    have hu : polyC w (m + 1) u ∈ Set.range ((polyC w m).trans (seg w (m + 1))) := ⟨u, rfl⟩
    rw [Path.trans_range] at hu
    rcases hu with ⟨v, hv⟩ | ⟨v, hv⟩
    · rw [← hv]; exact polyC_mem m (fun k hk => h k (by omega)) v
    · rw [← hv]; exact h (m + 1) le_rfl v

variable (q r : ℕ)

/-- The branch used on segment `k`. -/
noncomputable def br (k : ℕ) (z : ℂ) : ℂ :=
  if k < q then log z else if k < r then log (-z) + Real.pi * I else log z + per

theorem exp_br {k : ℕ} {z : ℂ} (hz : z ≠ 0) : cexp (br q r k z) = z := by
  unfold br
  split_ifs
  · exact exp_log hz
  · rw [exp_add, exp_log (neg_ne_zero.mpr hz), exp_pi_mul_I]; ring
  · rw [exp_add, exp_log hz, exp_two_pi_mul_I, mul_one]

variable {q r} (n : ℕ)
variable (hs : ∀ k ≤ n, (k < q ∨ r ≤ k) → ∀ u, seg w k u ∈ slitPlane)
variable (hns : ∀ k ≤ n, q ≤ k → k < r → ∀ u, -(seg w k u) ∈ slitPlane)

include hs hns in
theorem seg_ne_zero {k : ℕ} (hk : k ≤ n) (hqr : q < r) (u : unitInterval) : seg w k u ≠ 0 := by
  by_cases h : q ≤ k ∧ k < r
  · exact fun h0 => slitPlane_ne_zero (hns k hk h.1 h.2 u) (by simp [h0])
  · exact slitPlane_ne_zero (hs k hk (by omega) u)

include hs hns in
theorem continuous_br_seg {k : ℕ} (hk : k ≤ n) (hqr : q < r) :
    Continuous fun u => br q r k (seg w k u) := by
  have hseg : Continuous fun u => seg w k u := (seg w k).continuous
  rw [continuous_iff_continuousAt]
  intro u
  by_cases h1 : k < q
  · simp only [br, h1, if_true]
    exact (continuousAt_clog (hs k hk (Or.inl h1) u)).comp (f := fun u => seg w k u) hseg.continuousAt
  by_cases h2 : k < r
  · simp only [br, h1, h2, if_true, if_false]
    exact ((continuousAt_clog (hns k hk (by omega) h2 u)).comp (f := fun u => -seg w k u)
      hseg.neg.continuousAt).add continuousAt_const
  · simp only [br, h1, h2, if_false]
    exact ((continuousAt_clog (hs k hk (Or.inr (by omega)) u)).comp (f := fun u => seg w k u)
      hseg.continuousAt).add continuousAt_const

theorem br_junction (hqr : q < r) (hup : 0 < (w q).im) (hlo : (w r).im < 0) (k : ℕ) :
    br q r k (w (k + 1)) = br q r (k + 1) (w (k + 1)) := by
  unfold br
  by_cases h1 : k + 1 < q
  · simp [h1, show k < q by omega]
  by_cases h2 : k + 1 = q
  · subst h2; simp [show k + 1 < r by omega, negBranch_of_im_pos hup]
  by_cases h3 : k + 1 < r
  · simp [h1, h3, show ¬ k < q by omega, show k < r by omega]
  by_cases h4 : k + 1 = r
  · subst h4; simp [show ¬ k < q by omega, show ¬ k + 1 < q by omega, negBranch_of_im_neg hlo]
  · simp [show ¬ k < q by omega, show ¬ k < r by omega, h1, h3]

variable (hqr : q < r)

/-- The lift of segment `k` by its branch. -/
noncomputable def useg {k : ℕ} (hk : k ≤ n) :
    Path (br q r k (w k)) (br q r k (w (k + 1))) where
  toFun u := br q r k (seg w k u)
  continuous_toFun := continuous_br_seg w n hs hns hk hqr
  source' := by simp
  target' := by simp

variable (hup : 0 < (w q).im) (hlo : (w r).im < 0)

/-- The lift of the polyline, nested exactly as the polyline is. -/
noncomputable def upC : (m : ℕ) → m ≤ n → Path (br q r 0 (w 0)) (br q r m (w (m + 1)))
  | 0, h => useg w n hs hns hqr h
  | m + 1, h => (upC m (by omega)).trans
      ((useg w n hs hns hqr h).cast (br_junction w hqr hup hlo m) rfl)

theorem exp_upC : ∀ (m : ℕ) (h : m ≤ n) (u : unitInterval),
    cexp (upC w n hs hns hqr hup hlo m h u) = polyC w m u
  | 0, h, u => exp_br q r (seg_ne_zero w n hs hns h hqr u)
  | m + 1, h, u => by
    simp only [upC, polyC, Path.trans_apply]
    split_ifs
    · exact exp_upC m (by omega) _
    · simp only [Path.cast_coe]
      exact exp_br q r (seg_ne_zero w n hs hns h hqr _)

include hs hns hqr in
theorem polyC_ne_zero (u : unitInterval) : polyC w n u ≠ 0 :=
  polyC_mem (S := {z | z ≠ 0}) w n (fun k hk u => seg_ne_zero w n hs hns hk hqr u) u

variable (hclose : w (n + 1) = w 0)

/-- The base point `w 0`, in the punctured plane. -/
noncomputable def baseC : CStar := ⟨w 0, (polyC w n).source ▸ polyC_ne_zero w n hs hns hqr 0⟩

/-- The polyline as a loop in the punctured plane. -/
noncomputable def loopC : Path (baseC w n hs hns hqr) (baseC w n hs hns hqr) where
  toFun u := ⟨polyC w n u, polyC_ne_zero w n hs hns hqr u⟩
  continuous_toFun := (polyC w n).continuous.subtype_mk _
  source' := Subtype.ext (polyC w n).source
  target' := Subtype.ext ((polyC w n).target.trans hclose)

include hup hlo in
/-- **Index of a polyline from sign data.** -/
theorem liftIndex_loopC (hq0 : 0 < q) (hrn : r ≤ n) :
    liftIndex (⟨log (w 0), expMap_log (baseC w n hs hns hqr)⟩ :
        expMap ⁻¹' {baseC w n hs hns hqr})
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (loopC w n hs hns hqr hclose))) = 1 := by
  have h1 : log (w 0) = br q r 0 (w 0) := by simp [br, hq0]
  have h2 : log (w 0) + per = br q r n (w (n + 1)) := by
    simp [br, show ¬ n < q by omega, show ¬ n < r by omega, hclose]
  set Γ := (upC w n hs hns hqr hup hlo n le_rfl).cast h1 h2 with hΓ
  have hend : expMap (log (w 0) + per) = baseC w n hs hns hqr := by
    rw [expMap_add_per]; exact expMap_log (baseC w n hs hns hqr)
  have hpath : Γ.map continuous_expMap = (loopC w n hs hns hqr hclose).cast (expMap_log (baseC w n hs hns hqr)) hend := by
    ext u
    simp only [hΓ, Path.map_coe, Path.cast_coe, Function.comp_apply]
    exact exp_upC w n hs hns hqr hup hlo n le_rfl u
  have hmono : isAddQuotientCoveringMap_exp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (loopC w n hs hns hqr hclose))
      (⟨log (w 0), expMap_log (baseC w n hs hns hqr)⟩ : expMap ⁻¹' {baseC w n hs hns hqr}) = (⟨log (w 0) + per, hend⟩ : expMap ⁻¹' {baseC w n hs hns hqr}) :=
    isAddQuotientCoveringMap_exp.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk Γ) (congrArg Path.Homotopic.Quotient.mk hpath)
  refine (liftIndex_unique _ ?_).symm
  have h := liftDisp_add_base (⟨log (w 0), expMap_log (baseC w n hs hns hqr)⟩ : expMap ⁻¹' {baseC w n hs hns hqr})
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopC w n hs hns hqr hclose)))
  rw [hmono] at h
  simp only [one_zsmul]
  have h' : liftDisp (⟨log (w 0), expMap_log (baseC w n hs hns hqr)⟩ : expMap ⁻¹' {baseC w n hs hns hqr})
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopC w n hs hns hqr hclose)))
      + log (w 0) = log (w 0) + per := h
  linear_combination -h'

end Sz8.Galois.PolyIndex
