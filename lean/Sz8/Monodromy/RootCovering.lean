import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Complex.Basic

/-!
The zero set of a monic family of complex polynomials is a covering space over the
parameters at which all roots are simple.

For `P : ℂ → ℂ[X]` monic of fixed degree with `C¹` dependence on `t`, the projection
`{(t, x) | P t x = 0} → ℂ` is proper (Cauchy's root bound), has finite fibres, and is a
local homeomorphism over simple roots (implicit function theorem). Mathlib's
`IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` then makes it a covering map over
the regular parameters, so Mathlib's path lifting and monodromy apply to it.
-/

open Polynomial Topology Set Metric Filter

namespace Sz8.Monodromy

/-- A family of monic complex polynomials of fixed degree, depending continuously
differentiably on a complex parameter `t`. -/
structure MonicFamily where
  P : ℂ → ℂ[X]
  n : ℕ
  monic : ∀ t, (P t).Monic
  natDegree_eq : ∀ t, (P t).natDegree = n
  continuous_coeff : ∀ i, Continuous fun t => (P t).coeff i
  contDiff : ContDiff ℂ 1 fun p : ℂ × ℂ => (P p.1).eval p.2

namespace MonicFamily

variable (M : MonicFamily)

/-- The zero set `{(t, x) | P t x = 0}`. -/
def zeroSet : Set (ℂ × ℂ) := {p | (M.P p.1).eval p.2 = 0}

/-- The points `(t, x)` with `x` a root of `P t`. -/
abbrev RootSpace : Type := M.zeroSet

/-- Projection to the parameter. -/
def proj : M.RootSpace → ℂ := fun z => z.1.1

/-- Parameters at which every root is simple. -/
def regular : Set ℂ := {t | ∀ x, (M.P t).eval x = 0 → (M.P t).derivative.eval x ≠ 0}

theorem continuous_eval : Continuous fun p : ℂ × ℂ => (M.P p.1).eval p.2 :=
  M.contDiff.continuous

theorem continuous_proj : Continuous M.proj := continuous_fst.comp continuous_subtype_val

theorem isClosed_zeroSet : IsClosed M.zeroSet :=
  isClosed_eq M.continuous_eval continuous_const

/-- Roots over a compact set of parameters are uniformly bounded (Cauchy's bound). -/
theorem exists_root_bound {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ t ∈ K, ∀ x, (M.P t).eval x = 0 → ‖x‖ ≤ C := by
  have hcont : Continuous fun t => ∑ i ∈ Finset.range M.n, ‖(M.P t).coeff i‖ :=
    continuous_finsetSum _ fun i _ => (M.continuous_coeff i).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C + 1, fun t ht x hx => ?_⟩
  have hroot := IsRoot.norm_lt_cauchyBound (M.monic t).ne_zero hx
  have hbound : (cauchyBound (M.P t) : ℝ) ≤ ∑ i ∈ Finset.range M.n, ‖(M.P t).coeff i‖ + 1 := by
    rw [cauchyBound, (M.monic t).leadingCoeff, nnnorm_one, div_one, M.natDegree_eq]
    have hsup : ((Finset.range M.n).sup fun i => ‖(M.P t).coeff i‖₊) ≤
        ∑ i ∈ Finset.range M.n, ‖(M.P t).coeff i‖₊ :=
      Finset.sup_le fun i hi => Finset.single_le_sum (f := fun i => ‖(M.P t).coeff i‖₊)
        (fun _ _ => zero_le) hi
    have : (((Finset.range M.n).sup fun i => ‖(M.P t).coeff i‖₊ : NNReal) : ℝ) ≤
        ∑ i ∈ Finset.range M.n, ‖(M.P t).coeff i‖ := by
      have := NNReal.coe_le_coe.mpr hsup
      simpa [NNReal.coe_sum] using this
    push_cast
    linarith
  have hCt := hC t ht
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at hCt
  have : ‖x‖ < (cauchyBound (M.P t) : ℝ) := by exact_mod_cast hroot
  linarith

theorem isProperMap_proj : IsProperMap M.proj := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨M.continuous_proj, fun K hK => ?_⟩
  obtain ⟨C, hC⟩ := M.exists_root_bound hK
  rw [Topology.IsInducing.subtypeVal.isCompact_iff]
  refine (hK.prod (isCompact_closedBall (0 : ℂ) C)).of_isClosed_subset ?_ ?_
  · have : Subtype.val '' (M.proj ⁻¹' K) = M.zeroSet ∩ Prod.fst ⁻¹' K := by
      ext p
      simp only [mem_image, mem_preimage, proj, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right, mem_inter_iff]
      tauto
    rw [this]
    exact M.isClosed_zeroSet.inter (hK.isClosed.preimage continuous_fst)
  · rintro _ ⟨⟨⟨t, x⟩, hz⟩, ht, rfl⟩
    exact ⟨ht, mem_closedBall_zero_iff.mpr (hC t ht x hz)⟩

theorem finite_fiber (t : ℂ) : (M.proj ⁻¹' {t}).Finite := by
  have hinj : InjOn (fun z : M.RootSpace => z.1.2) (M.proj ⁻¹' {t}) := by
    rintro ⟨⟨t₁, x₁⟩, h₁⟩ ht₁ ⟨⟨t₂, x₂⟩, h₂⟩ ht₂ hx
    simp only [mem_preimage, mem_singleton_iff, proj] at ht₁ ht₂ hx
    subst ht₁ ht₂ hx
    rfl
  refine Finite.of_finite_image ?_ hinj
  refine ((M.P t).roots.toFinset.finite_toSet).subset ?_
  rintro _ ⟨⟨⟨t', x⟩, hz⟩, ht', rfl⟩
  simp only [mem_preimage, mem_singleton_iff, proj] at ht'
  subst ht'
  simpa [Multiset.mem_toFinset, mem_roots (M.monic _).ne_zero, zeroSet] using hz

/-- The partial derivative in the root variable is the derivative of `P t`. -/
theorem fderiv_comp_inr (t x : ℂ) :
    (fderiv ℂ (fun p : ℂ × ℂ => (M.P p.1).eval p.2) (t, x)).comp
        (ContinuousLinearMap.inr ℂ ℂ ℂ) =
      (1 : ℂ →L[ℂ] ℂ).smulRight ((M.P t).derivative.eval x) := by
  have hf : DifferentiableAt ℂ (fun p : ℂ × ℂ => (M.P p.1).eval p.2) (t, x) :=
    M.contDiff.differentiable one_ne_zero _
  have hg : HasFDerivAt (fun y : ℂ => (t, y)) (ContinuousLinearMap.inr ℂ ℂ ℂ) x :=
    hasFDerivAt_prodMk_right t x
  have h1 := hf.hasFDerivAt.comp x hg
  have h2 := ((M.P t).hasDerivAt x).hasFDerivAt
  exact h1.unique h2

/-- The partial derivative in the root variable is continuous. -/
theorem continuous_derivative : Continuous fun p : ℂ × ℂ => (M.P p.1).derivative.eval p.2 := by
  have hd : ∀ p : ℂ × ℂ, (M.P p.1).derivative.eval p.2 =
      fderiv ℂ (fun p : ℂ × ℂ => (M.P p.1).eval p.2) p (0, 1) := by
    intro p
    have := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) (M.fderiv_comp_inr p.1 p.2)
    simpa using this.symm
  simp_rw [hd]
  exact (M.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const

theorem isLocalHomeomorphOn_proj : IsLocalHomeomorphOn M.proj (M.proj ⁻¹' M.regular) := by
  classical
  rintro ⟨⟨t₀, x₀⟩, hz₀⟩ hreg
  set f := fun p : ℂ × ℂ => (M.P p.1).eval p.2 with hf
  have hc : (M.P t₀).derivative.eval x₀ ≠ 0 := hreg x₀ hz₀
  have cdf : ContDiffAt ℂ 1 f (t₀, x₀) := M.contDiff.contDiffAt
  have if₂ : ((fderiv ℂ f (t₀, x₀)).comp (ContinuousLinearMap.inr ℂ ℂ ℂ)).IsInvertible := by
    rw [M.fderiv_comp_inr]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hc), ?_⟩
    ext
    simp [ContinuousLinearEquiv.unitsEquivAut_apply]
  set ψ := cdf.implicitFunction one_ne_zero if₂
  have hψ₀ : ψ t₀ = x₀ := cdf.implicitFunction_apply_self one_ne_zero if₂
  have hiff := cdf.eventually_apply_eq_iff_implicitFunction one_ne_zero if₂
  have hz₀' : f (t₀, x₀) = 0 := hz₀
  rw [hz₀'] at hiff
  have hcont : ∀ᶠ t in 𝓝 t₀, ContinuousAt ψ t :=
    ((cdf.contDiffAt_implicitFunction one_ne_zero if₂).eventually (by simp)).mono
      fun t ht => ht.continuousAt
  -- A box on which the zero set is the graph of `ψ`.
  obtain ⟨ε, hε, hbox⟩ : ∃ ε > 0, ∀ v : ℂ × ℂ, v.1 ∈ ball t₀ ε → v.2 ∈ ball x₀ ε →
      (f v = 0 ↔ ψ v.1 = v.2) := by
    obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp hiff
    refine ⟨ε, hε, fun v h₁ h₂ => h ?_⟩
    rw [← ball_prod_same]
    exact ⟨h₁, h₂⟩
  have hψtend : ∀ᶠ t in 𝓝 t₀, ψ t ∈ ball x₀ ε := by
    have hca : ContinuousAt ψ t₀ := (cdf.contDiffAt_implicitFunction one_ne_zero if₂).continuousAt
    have hb : ball x₀ ε ∈ 𝓝 (ψ t₀) := hψ₀ ▸ ball_mem_nhds x₀ hε
    exact hca.preimage_mem_nhds hb
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp
    ((hcont.and hψtend).and (ball_mem_nhds t₀ hε))
  have hsub : ∀ t ∈ ball t₀ δ, ContinuousAt ψ t ∧ ψ t ∈ ball x₀ ε ∧ t ∈ ball t₀ ε :=
    fun t ht => ⟨(hδball ht).1.1, (hδball ht).1.2, (hδball ht).2⟩
  have hroot : ∀ t ∈ ball t₀ δ, (M.P t).eval (ψ t) = 0 := fun t ht =>
    (hbox (t, ψ t) (hsub t ht).2.2 (hsub t ht).2.1).mpr rfl
  let inv : ℂ → M.RootSpace := fun t =>
    if h : t ∈ ball t₀ δ then ⟨(t, ψ t), hroot t h⟩ else ⟨(t₀, x₀), hz₀⟩
  let e : OpenPartialHomeomorph M.RootSpace ℂ :=
    { toFun := M.proj
      invFun := inv
      source := {w | w.1.1 ∈ ball t₀ δ ∧ w.1.2 ∈ ball x₀ ε}
      target := ball t₀ δ
      map_source' := fun w hw => hw.1
      map_target' := fun t ht => by
        simp only [inv, ht, ↓reduceDIte]
        exact ⟨ht, (hsub t ht).2.1⟩
      left_inv' := by
        rintro ⟨⟨t, x⟩, hw⟩ ⟨ht, hx⟩
        have : ψ t = x := (hbox (t, x) (hsub t ht).2.2 hx).mp hw
        simp only [inv, proj, ht, ↓reduceDIte, this]
      right_inv' := fun t ht => by simp only [inv, proj, ht, ↓reduceDIte]
      open_source := (isOpen_ball.preimage (continuous_fst.comp continuous_subtype_val)).inter
        (isOpen_ball.preimage (continuous_snd.comp continuous_subtype_val))
      open_target := isOpen_ball
      continuousOn_toFun := M.continuous_proj.continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_domRestrict]
        have : (ball t₀ δ).domRestrict inv =
            fun t : ball t₀ δ => (⟨(t.1, ψ t.1), hroot t.1 t.2⟩ : M.RootSpace) := by
          funext t
          simp only [Set.domRestrict, inv, t.2, ↓reduceDIte]
        rw [this]
        refine Continuous.subtype_mk (continuous_subtype_val.prodMk ?_) _
        exact continuous_iff_continuousAt.mpr fun t =>
          (hsub t.1 t.2).1.comp continuous_subtype_val.continuousAt }
  refine ⟨e, ⟨?_, ?_⟩, rfl⟩
  · simpa using hδ
  · simpa using hε

theorem isOpen_regular : IsOpen M.regular := by
  have hcl : IsClosed (M.proj '' {z | (M.P z.1.1).derivative.eval z.1.2 = 0}) := by
    refine M.isProperMap_proj.isClosedMap _ (isClosed_eq ?_ continuous_const)
    exact M.continuous_derivative.comp continuous_subtype_val
  convert hcl.isOpen_compl using 1
  ext t
  simp only [regular, mem_ofPred_eq, mem_compl_iff, mem_image, not_exists, not_and, proj]
  constructor
  · rintro h ⟨⟨t', x⟩, hz⟩ hd rfl
    exact h x hz hd
  · intro h x hx hd
    exact h ⟨(t, x), hx⟩ hd rfl

/-- The root space is a covering of the regular parameters. -/
theorem isCoveringMapOn_proj : IsCoveringMapOn M.proj M.regular :=
  M.isProperMap_proj.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun t _ => M.finite_fiber t) M.isLocalHomeomorphOn_proj

end MonicFamily

end Sz8.Monodromy

