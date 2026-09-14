import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Lemma L: holomorphic functions of polynomial growth off a finite set are polynomials

`eq_polynomial_of_growth`: `f` complex differentiable off a finite set `S`, bounded near each point
of `S`, with `‖f z‖ ≤ C ‖z‖^N` for large `‖z‖`, agrees off `S` with a polynomial of degree `≤ N`.

This is the analytic core of the converse in the Galois–monodromy bridge. Route: fill the
removable singularities (`differentiableOn_update_limUnder_of_bddAbove`), write the entire
extension as `P(z) + z^(N+1) F(z)` (`AnalyticAt.exists_eq_sum_add_pow_mul`), and apply Liouville
to `F`, which tends to `0` at infinity (`Differentiable.eq_const_of_tendsto_cocompact`).
-/

open Metric Filter Topology Polynomial Function

namespace Sz8.Galois.PolyGrowth

/-- Removing finitely many bounded singularities. -/
theorem exists_fill {f : ℂ → ℂ} {S : Finset ℂ} (hd : DifferentiableOn ℂ f (↑S)ᶜ)
    (hb : ∀ s ∈ S, ∃ ε > 0, ∃ B : ℝ, ∀ z ∈ ball s ε, z ∉ S → ‖f z‖ ≤ B) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z ∉ S, g z = f z := by
  classical
  have hopen : ∀ T : Finset ℂ, IsOpen ((↑T : Set ℂ)ᶜ) := fun T => T.finite_toSet.isClosed.isOpen_compl
  set g : ℂ → ℂ := fun z => if z ∈ S then limUnder (𝓝[≠] z) f else f z with hg
  refine ⟨g, fun z => ?_, fun z hz => by simp [hg, hz]⟩
  by_cases hz : z ∈ S
  · obtain ⟨ε, hε, B, hB⟩ := hb z hz
    obtain ⟨δ₀, hδ₀, hsub⟩ := Metric.isOpen_iff.1 (hopen (S.erase z)) z (by simp)
    set δ := min ε δ₀
    have hδ : 0 < δ := lt_min hε hδ₀
    have hnot : ∀ w ∈ ball z δ, w ≠ z → w ∉ S := fun w hw hne hwS => by
      have := hsub (ball_subset_ball (min_le_right _ _) hw)
      simp [hne, hwS] at this
    have hdiff : DifferentiableOn ℂ f (ball z δ \ {z}) := hd.mono fun w hw => hnot w hw.1 hw.2
    have hbdd : BddAbove (norm ∘ f '' (ball z δ \ {z})) := ⟨B, by
      rintro _ ⟨w, hw, rfl⟩
      exact hB w (ball_subset_ball (min_le_left _ _) hw.1) (hnot w hw.1 hw.2)⟩
    have h := Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds z hδ) hdiff hbdd
    refine (h.differentiableAt (ball_mem_nhds z hδ)).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds z hδ] with w hw
    by_cases hwz : w = z
    · subst hwz; simp [hg, hz]
    · simp [hg, hnot w hw hwz, hwz]
  · have hn := (hopen S).mem_nhds hz
    refine (hd.differentiableAt hn).congr_of_eventuallyEq ?_
    filter_upwards [hn] with w hw
    simp [hg, show w ∉ S from hw]

/-- **Lemma L.** -/
theorem eq_polynomial_of_growth {f : ℂ → ℂ} {S : Finset ℂ} {N : ℕ} {K R : ℝ}
    (hd : DifferentiableOn ℂ f (↑S)ᶜ)
    (hb : ∀ s ∈ S, ∃ ε > 0, ∃ B : ℝ, ∀ z ∈ ball s ε, z ∉ S → ‖f z‖ ≤ B)
    (hg : ∀ z : ℂ, R ≤ ‖z‖ → z ∉ S → ‖f z‖ ≤ K * ‖z‖ ^ N) :
    ∃ p : ℂ[X], p.natDegree ≤ N ∧ ∀ z ∉ S, f z = p.eval z := by
  classical
  obtain ⟨g, hgd, hgf⟩ := exists_fill hd hb
  obtain ⟨F, hF0, hF⟩ := (hgd.analyticAt 0).exists_eq_sum_add_pow_mul (N + 1)
  set d : ℕ → ℂ := fun i => iteratedDeriv i g 0 / i.factorial with hdd
  set p : ℂ[X] := ∑ i ∈ Finset.range (N + 1), C (d i) * X ^ i with hp
  have hpeval : ∀ z, p.eval z = ∑ i ∈ Finset.range (N + 1), (z ^ i / i.factorial) •
      iteratedDeriv i g 0 := fun z => by
    simp only [hp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul, hdd]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hgp : ∀ z, g z = p.eval z + z ^ (N + 1) * F z := fun z => by
    rw [hF z, hpeval, smul_eq_mul]
  have hpdeg : p.natDegree ≤ N := by
    rw [hp]
    refine (natDegree_sum_le_of_forall_le _ _ fun i hi => ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]; exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  -- `F` is entire
  have hFd : Differentiable ℂ F := fun z => by
    by_cases hz : z = 0
    · subst hz; exact hF0.differentiableAt
    · have hq : DifferentiableAt ℂ (fun w => (g w - p.eval w) / w ^ (N + 1)) z :=
        ((hgd z).sub p.differentiable.differentiableAt).div (by fun_prop) (pow_ne_zero _ hz)
      refine hq.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      rw [hgp w]; field_simp [pow_ne_zero (N + 1) (show w ≠ 0 from hw)]; ring
  -- `F → 0` at infinity
  set A : ℝ := ∑ i ∈ Finset.range (N + 1), ‖d i‖
  set R' : ℝ := max (max R 1) (∑ s ∈ S, ‖s‖ + 1) with hR'
  have hFbound : ∀ z : ℂ, R' ≤ ‖z‖ → ‖F z‖ ≤ (K + A) * ‖z‖⁻¹ := by
    intro z hz
    have hz1 : 1 ≤ ‖z‖ := (le_max_right _ _).trans ((le_max_left _ _).trans hz)
    have hzR : R ≤ ‖z‖ := (le_max_left _ _).trans ((le_max_left _ _).trans hz)
    have hzS : z ∉ S := fun h => by
      have h1 : ‖z‖ ≤ ∑ s ∈ S, ‖s‖ :=
        Finset.single_le_sum (f := fun s => ‖s‖) (fun _ _ => norm_nonneg _) h
      linarith [le_max_right (max R 1) (∑ s ∈ S, ‖s‖ + 1)]
    have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
    have hpz : ‖p.eval z‖ ≤ A * ‖z‖ ^ N := by
      rw [show p.eval z = ∑ i ∈ Finset.range (N + 1), d i * z ^ i by
        simp [hp, eval_finsetSum], Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz1
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) (norm_nonneg _)
    have hgz : ‖g z‖ ≤ K * ‖z‖ ^ N := by rw [hgf z hzS]; exact hg z hzR hzS
    have hFz : F z = (g z - p.eval z) / z ^ (N + 1) := by
      rw [hgp z]; field_simp [pow_ne_zero (N + 1) hz0]; ring
    have hpos : 0 < ‖z‖ ^ (N + 1) := by positivity
    rw [hFz, norm_div, norm_pow, div_le_iff₀ hpos]
    calc ‖g z - p.eval z‖ ≤ ‖g z‖ + ‖p.eval z‖ := norm_sub_le _ _
      _ ≤ K * ‖z‖ ^ N + A * ‖z‖ ^ N := add_le_add hgz hpz
      _ = (K + A) * ‖z‖⁻¹ * ‖z‖ ^ (N + 1) := by
        field_simp [norm_ne_zero_iff.2 hz0]; ring
  have hlim : Tendsto F (cocompact ℂ) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_inv_atTop_zero.comp tendsto_norm_cocompact_atTop).const_mul
      (K + A) |>.congr' (Eventually.of_forall fun _ => rfl) |> fun h => by simpa using h)
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop R'] with z hz
    exact hFbound z hz
  have hF0' := hFd.eq_const_of_tendsto_cocompact hlim
  refine ⟨p, hpdeg, fun z hz => ?_⟩
  rw [← hgf z hz, hgp z, hF0']
  simp
