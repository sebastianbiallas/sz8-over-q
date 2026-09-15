import Sz8.Monodromy.RootCovering
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# B0: continuous simple root branches are holomorphic

`differentiableAt_of_root`: if `r` is continuous at `t₀`, `r t` is a root of `P t` for `t` near
`t₀`, and `r t₀` is a simple root, then `r` is complex differentiable at `t₀` — it agrees near `t₀`
with the implicit function of `(t, x) ↦ P t x`, which is `C¹` over `ℂ`.
`analyticOnNhd_of_root` is the open-set form.
-/

open Polynomial Topology Filter Metric Set

namespace Sz8.Galois.RootAnalytic

open Sz8.Monodromy

theorem differentiableAt_of_root (M : MonicFamily) {r : ℂ → ℂ} {t₀ : ℂ} (hr : ContinuousAt r t₀)
    (hroot : ∀ᶠ t in 𝓝 t₀, (M.P t).eval (r t) = 0)
    (hs : (M.P t₀).derivative.eval (r t₀) ≠ 0) : DifferentiableAt ℂ r t₀ := by
  set x₀ := r t₀
  set f := fun p : ℂ × ℂ => (M.P p.1).eval p.2 with hf
  have cdf : ContDiffAt ℂ 1 f (t₀, x₀) := M.contDiff.contDiffAt
  have if₂ : ((fderiv ℂ f (t₀, x₀)).comp (ContinuousLinearMap.inr ℂ ℂ ℂ)).IsInvertible := by
    rw [M.fderiv_comp_inr]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hs), ?_⟩
    ext
    simp [ContinuousLinearEquiv.unitsEquivAut_apply]
  set ψ := cdf.implicitFunction one_ne_zero if₂
  have hiff := cdf.eventually_apply_eq_iff_implicitFunction one_ne_zero if₂
  have hz₀ : f (t₀, x₀) = 0 := hroot.self_of_nhds
  rw [hz₀] at hiff
  have hψd : DifferentiableAt ℂ ψ t₀ :=
    (cdf.contDiffAt_implicitFunction one_ne_zero if₂).differentiableAt one_ne_zero
  have htend : Tendsto (fun t => (t, r t)) (𝓝 t₀) (𝓝 (t₀, x₀)) :=
    (continuousAt_id.prodMk hr).tendsto
  refine hψd.congr_of_eventuallyEq ?_
  filter_upwards [htend.eventually hiff, hroot] with t h1 h2
  exact ((h1.1 h2)).symm

theorem analyticOnNhd_of_root (M : MonicFamily) {r : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hr : ContinuousOn r U) (hroot : ∀ t ∈ U, (M.P t).eval (r t) = 0)
    (hs : ∀ t ∈ U, (M.P t).derivative.eval (r t) ≠ 0) : AnalyticOnNhd ℂ r U := by
  refine DifferentiableOn.analyticOnNhd (fun t ht => ?_) hU
  exact (differentiableAt_of_root M (hr.continuousAt (hU.mem_nhds ht))
    (eventually_of_mem (hU.mem_nhds ht) hroot) (hs t ht)).differentiableWithinAt

end Sz8.Galois.RootAnalytic
