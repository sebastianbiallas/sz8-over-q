import Sz8.Galois.Germs

/-!
# (R): analytic continuation preserves relations among root branches

* `exists_box`: at a simple root, an analytic branch and a box in which it is the only root.
* `eventuallyEq_of_root`: two continuous root branches through the same simple root agree near it.
* `continue_along`: along a continuous parameter path with continuous root values, vanishing of a
  polynomial relation (coefficients in `ℂ[t]`) near the start implies vanishing near the end —
  the set of good times is clopen by the identity theorem on a common ball.
-/

open Polynomial Topology Filter Metric Set

namespace Sz8.Galois.Continuation

open Sz8.Monodromy Sz8.Monodromy.MonicFamily Germs

variable (M : MonicFamily)

theorem exists_box {t₀ r₀ : ℂ} (ht₀ : t₀ ∈ M.regular) (hr₀ : (M.P t₀).eval r₀ = 0) :
    ∃ δ > 0, ∃ ε > 0, ∃ ψ : ℂ → ℂ, ψ t₀ = r₀ ∧ ball t₀ δ ⊆ M.regular ∧
      AnalyticOnNhd ℂ ψ (ball t₀ δ) ∧
      (∀ t ∈ ball t₀ δ, (M.P t).eval (ψ t) = 0 ∧ ψ t ∈ ball r₀ ε) ∧
      ∀ t ∈ ball t₀ δ, ∀ y ∈ ball r₀ ε, (M.P t).eval y = 0 → y = ψ t := by
  set f := fun p : ℂ × ℂ => (M.P p.1).eval p.2 with hf
  have hc : (M.P t₀).derivative.eval r₀ ≠ 0 := ht₀ r₀ hr₀
  have cdf : ContDiffAt ℂ 1 f (t₀, r₀) := M.contDiff.contDiffAt
  have if₂ : ((fderiv ℂ f (t₀, r₀)).comp (ContinuousLinearMap.inr ℂ ℂ ℂ)).IsInvertible := by
    rw [M.fderiv_comp_inr]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hc), ?_⟩
    ext
    simp [ContinuousLinearEquiv.unitsEquivAut_apply]
  set ψ := cdf.implicitFunction one_ne_zero if₂
  have hψ₀ : ψ t₀ = r₀ := cdf.implicitFunction_apply_self one_ne_zero if₂
  have hiff := cdf.eventually_apply_eq_iff_implicitFunction one_ne_zero if₂
  have hz₀' : f (t₀, r₀) = 0 := hr₀
  rw [hz₀'] at hiff
  have hcont : ∀ᶠ t in 𝓝 t₀, ContinuousAt ψ t :=
    ((cdf.contDiffAt_implicitFunction one_ne_zero if₂).eventually (by simp)).mono
      fun t ht => ht.continuousAt
  obtain ⟨ε, hε, hbox⟩ : ∃ ε > 0, ∀ v : ℂ × ℂ, v.1 ∈ ball t₀ ε → v.2 ∈ ball r₀ ε →
      (f v = 0 ↔ ψ v.1 = v.2) := by
    obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp hiff
    refine ⟨ε, hε, fun v h₁ h₂ => h ?_⟩
    rw [← ball_prod_same]
    exact ⟨h₁, h₂⟩
  have hψtend : ∀ᶠ t in 𝓝 t₀, ψ t ∈ ball r₀ ε := by
    have hca : ContinuousAt ψ t₀ := (cdf.contDiffAt_implicitFunction one_ne_zero if₂).continuousAt
    exact hca.preimage_mem_nhds (hψ₀ ▸ ball_mem_nhds r₀ hε)
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp
    (((hcont.and hψtend).and (ball_mem_nhds t₀ hε)).and (M.isOpen_regular.mem_nhds ht₀))
  have hroot : ∀ t ∈ ball t₀ δ, (M.P t).eval (ψ t) = 0 := fun t ht =>
    (hbox (t, ψ t) (hδball ht).1.2 (hδball ht).1.1.2).mpr rfl
  refine ⟨δ, hδ, ε, hε, ψ, hψ₀, fun t ht => (hδball ht).2, ?_,
    fun t ht => ⟨hroot t ht, (hδball ht).1.1.2⟩, fun t ht y hy hyr => ?_⟩
  · exact RootAnalytic.analyticOnNhd_of_root M isOpen_ball
      (fun t ht => ((hδball ht).1.1.1).continuousWithinAt) hroot
      (fun t ht => (hδball ht).2 _ (hroot t ht))
  · exact ((hbox (t, y) (hδball ht).1.2 hy).mp hyr).symm

theorem eventuallyEq_of_root {t₀ : ℂ} (ht₀ : t₀ ∈ M.regular) {r₁ r₂ : ℂ → ℂ}
    (h₁ : ContinuousAt r₁ t₀) (h₂ : ContinuousAt r₂ t₀)
    (hr₁ : ∀ᶠ t in 𝓝 t₀, (M.P t).eval (r₁ t) = 0) (hr₂ : ∀ᶠ t in 𝓝 t₀, (M.P t).eval (r₂ t) = 0)
    (h : r₁ t₀ = r₂ t₀) : r₁ =ᶠ[𝓝 t₀] r₂ := by
  obtain ⟨δ, hδ, ε, hε, ψ, hψ0, -, -, -, huniq⟩ := exists_box M ht₀ (hr₁.self_of_nhds)
  have hb₁ : ∀ᶠ t in 𝓝 t₀, r₁ t ∈ ball (r₁ t₀) ε := h₁.preimage_mem_nhds (ball_mem_nhds _ hε)
  have hb₂ : ∀ᶠ t in 𝓝 t₀, r₂ t ∈ ball (r₁ t₀) ε :=
    h₂.preimage_mem_nhds (h ▸ ball_mem_nhds _ hε)
  filter_upwards [hb₁, hb₂, hr₁, hr₂, ball_mem_nhds t₀ hδ] with t a₁ a₂ a₃ a₄ ht
  rw [huniq t ht _ a₁ a₃, huniq t ht _ a₂ a₄]

/-- A polynomial relation with coefficients in `ℂ[t]`, evaluated at `t` and root values `y`. -/
noncomputable def qv {ι : Type*} (Q : MvPolynomial ι ℂ[X]) (t : ℂ) (y : ι → ℂ) : ℂ :=
  MvPolynomial.eval₂ (evalRingHom t) y Q

omit M in
theorem analyticOnNhd_qv {ι : Type*} (Q : MvPolynomial ι ℂ[X]) {U : Set ℂ} {r : ι → ℂ → ℂ}
    (hr : ∀ i, AnalyticOnNhd ℂ (r i) U) : AnalyticOnNhd ℂ (fun t => qv Q t fun i => r i t) U := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    have h := (a.differentiable.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ U)
    simpa [qv] using h
  | add p q hp hq => simpa [qv] using hp.fun_add hq
  | mul_X p i hp =>
    exact fun x hx => ((hp x hx).mul (hr i x hx)).congr (Eventually.of_forall fun t => by simp [qv])

omit M in
theorem exists_delta {ι : Type*} [Finite ι] (δs : ι → ℝ) (h : ∀ i, 0 < δs i) :
    ∃ δ > 0, ∀ i, δ ≤ δs i := by
  classical
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty δs, ?_, fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
    exact (Finset.lt_inf'_iff _).2 fun i _ => h i

/-- **Continuation along a path.** -/
theorem continue_along {ι : Type*} [Finite ι] (Q : MvPolynomial ι ℂ[X]) (p : unitInterval → ℂ)
    (hp : Continuous p) (hreg : ∀ u, p u ∈ M.regular) (ρ : ι → unitInterval → ℂ)
    (hρ : ∀ i, Continuous (ρ i)) (hroot : ∀ i u, (M.P (p u)).eval (ρ i u) = 0) :
    let V : unitInterval → Prop := fun u => ∀ r : ι → ℂ → ℂ,
      (∀ i, ContinuousAt (r i) (p u) ∧ r i (p u) = ρ i u ∧
        ∀ᶠ t in 𝓝 (p u), (M.P t).eval (r i t) = 0) →
      (fun t => qv Q t fun i => r i t) =ᶠ[𝓝 (p u)] 0
    V 0 → V 1 := by
  intro V h0
  -- local constancy of `V`
  have hloc : ∀ u₀, ∃ N ∈ 𝓝 u₀, ∀ u ∈ N, (V u ↔ V u₀) := by
    intro u₀
    have hb := fun i => exists_box M (hreg u₀) (hroot i u₀)
    choose δs hδs εs hεs ψ hψ0 hsub han hψr huniq using hb
    obtain ⟨δ, hδ, hδle⟩ := exists_delta δs hδs
    set B := ball (p u₀) δ
    have hBi : ∀ i, B ⊆ ball (p u₀) (δs i) := fun i => ball_subset_ball (hδle i)
    set g : ℂ → ℂ := fun t => qv Q t fun i => ψ i t
    have hg : AnalyticOnNhd ℂ g B := analyticOnNhd_qv Q fun i => (han i).mono (hBi i)
    -- `V u` at a point of `B` whose root values lie in the boxes
    have hV : ∀ u, p u ∈ B → (∀ i, ρ i u ∈ ball (ρ i u₀) (εs i)) → (V u ↔ g =ᶠ[𝓝 (p u)] 0) := by
      intro u hpu hρu
      have hρψ : ∀ i, ρ i u = ψ i (p u) := fun i =>
        huniq i (p u) (hBi i hpu) _ (hρu i) (hroot i u)
      constructor
      · intro hVu
        refine hVu ψ fun i => ⟨((han i).mono (hBi i) _ hpu).continuousAt, (hρψ i).symm, ?_⟩
        filter_upwards [isOpen_ball.mem_nhds (hBi i hpu)] with t ht using (hψr i t ht).1
      · intro hgu r hr
        have heq : ∀ i, r i =ᶠ[𝓝 (p u)] ψ i := by
          intro i
          obtain ⟨hc, hv, hrr⟩ := hr i
          have hin : ∀ᶠ t in 𝓝 (p u), r i t ∈ ball (ρ i u₀) (εs i) :=
            hc.preimage_mem_nhds (hv ▸ isOpen_ball.mem_nhds (hρu i))
          filter_upwards [hin, hrr, isOpen_ball.mem_nhds (hBi i hpu)] with t h1 h2 h3
          exact huniq i t h3 _ h1 h2
        have hall : ∀ᶠ t in 𝓝 (p u), ∀ i, r i t = ψ i t := eventually_all.2 heq
        filter_upwards [hgu, hall] with t h1 h2
        simp only [g] at h1
        simpa [funext h2] using h1
    -- identity theorem on `B`
    have hid : ∀ z ∈ B, (g =ᶠ[𝓝 z] 0 ↔ g =ᶠ[𝓝 (p u₀)] 0) := by
      have key : ∀ z ∈ B, g =ᶠ[𝓝 z] 0 → ∀ w ∈ B, g =ᶠ[𝓝 w] 0 := by
        intro z hz hgz w hw
        have hon := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (convex_ball _ _).isPreconnected hz hgz
        filter_upwards [isOpen_ball.mem_nhds hw] with t ht using hon ht
      exact fun z hz => ⟨fun h => key z hz h _ (mem_ball_self hδ),
        fun h => key _ (mem_ball_self hδ) h z hz⟩
    have hN : ∀ᶠ u in 𝓝 u₀, p u ∈ B ∧ ∀ i, ρ i u ∈ ball (ρ i u₀) (εs i) := by
      have h1 : ∀ᶠ u in 𝓝 u₀, p u ∈ B := hp.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hδ)
      refine h1.and ?_
      exact eventually_all.2 fun i =>
        (hρ i).continuousAt.preimage_mem_nhds (ball_mem_nhds _ (hεs i))
    refine ⟨_, hN, fun u hu => ?_⟩
    rw [hV u hu.1 hu.2, hV u₀ (mem_ball_self hδ) (fun i => mem_ball_self (hεs i)),
      hid _ hu.1]
  -- clopen
  set S := {u | V u}
  have hopen : IsOpen S := isOpen_iff_mem_nhds.2 fun u₀ hu₀ => by
    obtain ⟨N, hN, h⟩ := hloc u₀
    exact mem_of_superset hN fun u hu => (h u hu).2 hu₀
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff]
    refine isOpen_iff_mem_nhds.2 fun u₀ hu₀ => ?_
    obtain ⟨N, hN, h⟩ := hloc u₀
    exact mem_of_superset hN fun u hu hVu => hu₀ ((h u hu).1 hVu)
  have huniv : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, h0⟩
  exact (huniv ▸ mem_univ (1 : unitInterval) : (1 : unitInterval) ∈ S)

/-- **Continuation around a loop**, for relations with coefficients in `ℂ[t]`. -/
theorem continue_monodromy (b : M.Base) (γ : Path b b) (Q : MvPolynomial (M.Fiber b) ℂ[X])
    (h : (fun t => qv Q t fun x => rootFun M b x t) =ᶠ[𝓝 b.1] 0) :
    (fun t => qv Q t fun x =>
      rootFun M b (M.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) x) t) =ᶠ[𝓝 b.1] 0 := by
  have hγ0 : ∀ x : M.Fiber b, γ.toContinuousMap 0 = M.regular.restrictPreimage M.proj x.1 :=
    fun x => by simpa using x.2.symm
  set Γ := fun x : M.Fiber b => M.isCoveringMap.liftPath γ.toContinuousMap x.1 (hγ0 x) with hΓ
  set ρ : M.Fiber b → unitInterval → ℂ := fun x u => (Γ x u).1.1.2 with hρdef
  have hρ : ∀ x, Continuous (ρ x) := fun x =>
    continuous_snd.comp (continuous_subtype_val.comp (continuous_subtype_val.comp (Γ x).continuous))
  have hparam : ∀ x u, (Γ x u).1.1.1 = (γ u).1 := fun x u =>
    congrArg Subtype.val (congrFun (M.isCoveringMap.liftPath_lifts γ.toContinuousMap x.1 (hγ0 x)) u)
  have hroot : ∀ x u, (M.P (γ u).1).eval (ρ x u) = 0 := fun x u => by
    have h := (Γ x u).1.2
    rw [← hparam x u]
    exact h
  have hρ0 : ∀ x, ρ x 0 = x.root := fun x => by
    show (Γ x 0).1.1.2 = _
    rw [M.isCoveringMap.liftPath_zero γ.toContinuousMap x.1 (hγ0 x)]
    rfl
  have hρ1 : ∀ x, ρ x 1 =
      Fiber.root (t := b) (M.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) x) :=
    fun x => rfl
  have hp : Continuous fun u => (γ u).1 := continuous_subtype_val.comp γ.continuous
  have key := continue_along M Q (fun u => (γ u).1) hp (fun u => (γ u).2) ρ hρ hroot
  have hp0 : (γ 0).1 = b.1 := by simp
  have hp1 : (γ 1).1 = b.1 := by simp
  simp only at key
  have hV0 : ∀ r : M.Fiber b → ℂ → ℂ, (∀ i, ContinuousAt (r i) (γ 0).1 ∧ r i (γ 0).1 = ρ i 0 ∧
      ∀ᶠ t in 𝓝 (γ 0).1, (M.P t).eval (r i t) = 0) →
      (fun t => qv Q t fun i => r i t) =ᶠ[𝓝 (γ 0).1] 0 := by
    intro r hr
    rw [hp0] at hr ⊢
    have heq : ∀ i, r i =ᶠ[𝓝 b.1] rootFun M b i := fun i =>
      eventuallyEq_of_root M b.2 (hr i).1 (rootFun_analyticAt M b i).continuousAt (hr i).2.2
        (rootFun_root M b i) (by rw [(hr i).2.1, hρ0, rootFun_base])
    filter_upwards [h, eventually_all.2 heq] with t h1 h2
    simpa [funext h2] using h1
  have h1 := key hV0 (fun x => rootFun M b (M.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) x))
    (fun i => by
      rw [hp1]
      exact ⟨(rootFun_analyticAt M b _).continuousAt, by rw [rootFun_base, hρ1],
        rootFun_root M b _⟩)
  rwa [hp1] at h1

end Sz8.Galois.Continuation
