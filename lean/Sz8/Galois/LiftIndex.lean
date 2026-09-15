import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The lift index

The index of a loop in `ℂ ∖ {0}` about the puncture, defined as the endpoint displacement of its
lift along `exp` rather than as an independently developed winding number. Defining it this way
makes compatibility with `Complex.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv` hold by
construction instead of being a theorem to prove afterwards.
-/

open Complex

namespace Sz8.Galois

/-- The punctured plane. -/
abbrev CStar := {z : ℂ // z ≠ 0}

/-- `exp`, as the covering map `ℂ → ℂ ∖ {0}`. -/
noncomputable abbrev expMap : ℂ → CStar := fun z => ⟨_, z.exp_ne_zero⟩

/-- The period of `exp`. -/
noncomputable abbrev per : ℂ := 2 * Real.pi * I

theorem per_ne_zero : per ≠ 0 := by simp [Real.pi_ne_zero]

/-- The endpoint displacement of the `exp`-lift of a loop at `x` starting from `e`: the lift ends
at `e + liftDisp e γ`. -/
noncomputable def liftDisp {x : CStar} (e : expMap ⁻¹' {x}) (γ : FundamentalGroup CStar x) : ℂ :=
  (Multiplicative.toAdd (isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite e γ).unop).1

/-- Defining property: the lift of `γ` from `e` ends at `e + liftDisp e γ`. -/
theorem liftDisp_add_base {x : CStar} (e : expMap ⁻¹' {x}) (γ : FundamentalGroup CStar x) :
    liftDisp e γ + (e : ℂ) = (isAddQuotientCoveringMap_exp.isCoveringMap.monodromy γ e : ℂ) :=
  isAddQuotientCoveringMap_exp.unop_fundamentalGroupToMulOpposite_smul

theorem liftDisp_mem {x : CStar} (e : expMap ⁻¹' {x}) (γ : FundamentalGroup CStar x) :
    liftDisp e γ ∈ AddSubgroup.zmultiples per :=
  (Multiplicative.toAdd (isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite e γ).unop).2

@[simp] theorem liftDisp_one {x : CStar} (e : expMap ⁻¹' {x}) : liftDisp e 1 = 0 := by
  simp only [liftDisp, map_one, MulOpposite.unop_one]
  rfl

/-- The composition law. -/
theorem liftDisp_mul {x : CStar} (e : expMap ⁻¹' {x}) (γ δ : FundamentalGroup CStar x) :
    liftDisp e (γ * δ) = liftDisp e γ + liftDisp e δ := by
  simp only [liftDisp, map_mul, MulOpposite.unop_mul]
  exact add_comm _ _

/-- The reversal law. -/
theorem liftDisp_inv {x : CStar} (e : expMap ⁻¹' {x}) (γ : FundamentalGroup CStar x) :
    liftDisp e γ⁻¹ = -liftDisp e γ := by
  simp [liftDisp]

/-! ## The integer index -/

/-- The integer index of a loop about the puncture: the multiple of the period by which the
`exp`-lift is displaced. -/
noncomputable def liftIndex {x : CStar} (e : expMap ⁻¹' {x}) (γ : FundamentalGroup CStar x) : ℤ :=
  (AddSubgroup.mem_zmultiples_iff.mp (liftDisp_mem e γ)).choose

theorem liftIndex_smul {x : CStar} (e : expMap ⁻¹' {x}) (γ : FundamentalGroup CStar x) :
    (liftIndex e γ) • per = liftDisp e γ :=
  (AddSubgroup.mem_zmultiples_iff.mp (liftDisp_mem e γ)).choose_spec

theorem liftIndex_unique {x : CStar} (e : expMap ⁻¹' {x}) {γ : FundamentalGroup CStar x} {n : ℤ}
    (h : n • per = liftDisp e γ) : n = liftIndex e γ := by
  rw [← liftIndex_smul e γ, zsmul_eq_mul, zsmul_eq_mul] at h
  exact_mod_cast mul_right_cancel₀ per_ne_zero h

@[simp] theorem liftIndex_one {x : CStar} (e : expMap ⁻¹' {x}) :
    liftIndex e (1 : FundamentalGroup CStar x) = 0 :=
  (liftIndex_unique e (by rw [zero_zsmul]; exact (liftDisp_one e).symm)).symm

/-- The composition law for the index. -/
theorem liftIndex_mul {x : CStar} (e : expMap ⁻¹' {x}) (γ δ : FundamentalGroup CStar x) :
    liftIndex e (γ * δ) = liftIndex e γ + liftIndex e δ :=
  (liftIndex_unique e (by rw [add_zsmul, liftIndex_smul, liftIndex_smul, liftDisp_mul])).symm

/-- The reversal law for the index. -/
theorem liftIndex_inv {x : CStar} (e : expMap ⁻¹' {x}) (γ : FundamentalGroup CStar x) :
    liftIndex e γ⁻¹ = -liftIndex e γ :=
  (liftIndex_unique e (by rw [neg_zsmul, liftIndex_smul, liftDisp_inv])).symm

/-- The index is compatible with `fundamentalGroupEquiv` by construction, not by a theorem proved
afterwards: that equivalence *is* `fundamentalGroupToMulOpposite`, which is what `liftDisp` reads
off. This is the reason for defining the index through the lift rather than developing an
independent winding number and then matching the two. -/
theorem liftDisp_eq_fundamentalGroupEquiv {x : CStar} (e : expMap ⁻¹' {x})
    (γ : FundamentalGroup CStar x) :
    liftDisp e γ
      = (Multiplicative.toAdd (isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e γ).unop).1 :=
  rfl

/-! ## The circle test -/

theorem continuous_expMap : Continuous expMap :=
  Complex.continuous_exp.subtype_mk _

/-- The lift of the positively oriented circle through `exp w`: the straight segment from `w` to
`w + 2πi`. -/
noncomputable def segLift (w : ℂ) : Path w (w + per) where
  toFun := fun t => w + per * (t : ℝ)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem expMap_add_per (w : ℂ) : expMap (w + per) = expMap w :=
  Subtype.ext (by simp [Complex.exp_add, Complex.exp_two_pi_mul_I])

/-- The positively oriented circle through `exp w`, as a loop. -/
noncomputable def circleLoop (w : ℂ) : Path (expMap w) (expMap w) :=
  ((segLift w).map continuous_expMap).cast rfl (expMap_add_per w).symm

/-- The positively oriented circle has index `1`. -/
theorem liftIndex_circleLoop (w : ℂ) :
    liftIndex (⟨w, rfl⟩ : expMap ⁻¹' {expMap w})
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleLoop w))) = 1 := by
  have hmono : isAddQuotientCoveringMap_exp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (circleLoop w)) ⟨w, rfl⟩
      = (⟨w + per, expMap_add_per w⟩ : expMap ⁻¹' {expMap w}) := by
    refine isAddQuotientCoveringMap_exp.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk (segLift w)) ?_
    rfl
  refine (liftIndex_unique _ ?_).symm
  have h := liftDisp_add_base (⟨w, rfl⟩ : expMap ⁻¹' {expMap w})
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleLoop w)))
  rw [hmono] at h
  simp only [one_zsmul]
  have : liftDisp (⟨w, rfl⟩ : expMap ⁻¹' {expMap w})
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleLoop w))) + w = w + per := h
  linear_combination -this

/-! ## The index as an isomorphism, and the generator criterion -/

theorem liftDisp_injective {x : CStar} (e : expMap ⁻¹' {x}) : Function.Injective (liftDisp e) := by
  intro γ δ h
  apply isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite_injective e
  apply MulOpposite.unop_injective
  apply Multiplicative.toAdd.injective
  exact Subtype.ext h

theorem liftIndex_injective {x : CStar} (e : expMap ⁻¹' {x}) :
    Function.Injective (liftIndex e) := by
  intro γ δ h
  apply liftDisp_injective e
  rw [← liftIndex_smul, ← liftIndex_smul, h]

theorem liftIndex_surjective {x : CStar} (e : expMap ⁻¹' {x}) :
    Function.Surjective (liftIndex e) := by
  intro n
  obtain ⟨γ, hγ⟩ := isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite_surjective e
    (MulOpposite.op (Multiplicative.ofAdd
      (⟨n • per, AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩⟩ : AddSubgroup.zmultiples per)))
  refine ⟨γ, (liftIndex_unique e ?_).symm⟩
  simp only [liftDisp, hγ]
  rfl

/-- The index as a homomorphism to `Multiplicative ℤ`. -/
noncomputable def liftIndexHom {x : CStar} (e : expMap ⁻¹' {x}) :
    FundamentalGroup CStar x →* Multiplicative ℤ where
  toFun γ := Multiplicative.ofAdd (liftIndex e γ)
  map_one' := by
    show Multiplicative.ofAdd (liftIndex e (1 : FundamentalGroup CStar x)) = 1
    rw [liftIndex_one]; rfl
  map_mul' γ δ := by
    show Multiplicative.ofAdd (liftIndex e (γ * δ)) = _
    rw [liftIndex_mul]; rfl

/-- **`π₁(ℂ ∖ {0}, x) ≃* ℤ`**, with underlying value the lift index. -/
noncomputable def liftIndexEquiv {x : CStar} (e : expMap ⁻¹' {x}) :
    FundamentalGroup CStar x ≃* Multiplicative ℤ :=
  MulEquiv.ofBijective (liftIndexHom e) ⟨liftIndex_injective e, liftIndex_surjective e⟩

@[simp] theorem liftIndexEquiv_apply {x : CStar} (e : expMap ⁻¹' {x})
    (γ : FundamentalGroup CStar x) :
    liftIndexEquiv e γ = Multiplicative.ofAdd (liftIndex e γ) := rfl

theorem liftIndex_zpow {x : CStar} (e : expMap ⁻¹' {x}) (γ : FundamentalGroup CStar x) (k : ℤ) :
    liftIndex e (γ ^ k) = k * liftIndex e γ := by
  have h := map_zpow (liftIndexHom e) γ k
  change Multiplicative.ofAdd (liftIndex e (γ ^ k))
    = Multiplicative.ofAdd (liftIndex e γ) ^ k at h
  rw [← ofAdd_zsmul] at h
  simpa [smul_eq_mul] using Multiplicative.ofAdd.injective h

/-- **The generator criterion.** A loop of index `±1` generates the fundamental group of the
punctured plane, stated as subgroup equality so that the generation assembly consumes it
directly. Only the absolute value matters. -/
theorem zpowers_eq_top_of_abs_liftIndex {x : CStar} (e : expMap ⁻¹' {x})
    {γ : FundamentalGroup CStar x} (h : |liftIndex e γ| = 1) : Subgroup.zpowers γ = ⊤ := by
  have hs : liftIndex e γ * liftIndex e γ = 1 := by
    rcases (abs_eq zero_le_one).mp h with h1 | h1 <;> rw [h1] <;> norm_num
  rw [Subgroup.eq_top_iff']
  intro δ
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨liftIndex e δ * liftIndex e γ, liftIndex_injective e ?_⟩
  rw [liftIndex_zpow, mul_assoc, hs, mul_one]

/-! ## Index of a loop from sign data: three arcs, two branches of `log` -/

theorem negBranch_of_im_pos {z : ℂ} (h : 0 < z.im) : log (-z) + Real.pi * I = log z := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, arg_neg_eq_arg_sub_pi_of_im_pos h]

theorem negBranch_of_im_neg {z : ℂ} (h : z.im < 0) : log (-z) + Real.pi * I = log z + per := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, arg_neg_eq_arg_add_pi_of_im_neg h]; ring

/-- The lift of an arc avoiding the closed negative real axis, by the principal logarithm. -/
noncomputable def logLift {p q : CStar} (α : Path p q) (hα : ∀ t, (α t : ℂ) ∈ slitPlane) :
    Path (log (p : ℂ)) (log (q : ℂ)) where
  toFun t := log (α t : ℂ)
  continuous_toFun := continuous_iff_continuousAt.2 fun t =>
    (continuousAt_clog (hα t)).comp (f := fun s => (α s : ℂ))
      (continuous_subtype_val.comp α.continuous).continuousAt
  source' := by simp
  target' := by simp

/-- The lift of an arc avoiding the closed positive real axis, by `log (-z) + πi`. -/
noncomputable def negLift {p q : CStar} (β : Path p q) (hβ : ∀ t, -(β t : ℂ) ∈ slitPlane) :
    Path (log (-(p : ℂ)) + Real.pi * I) (log (-(q : ℂ)) + Real.pi * I) where
  toFun t := log (-(β t : ℂ)) + Real.pi * I
  continuous_toFun := continuous_iff_continuousAt.2 fun t =>
    ((continuousAt_clog (hβ t)).comp (f := fun s => -(β s : ℂ))
      (continuous_neg.comp (continuous_subtype_val.comp β.continuous)).continuousAt).add
      continuousAt_const
  source' := by simp
  target' := by simp

@[simp] theorem exp_logLift {p q : CStar} (α : Path p q) (hα : ∀ t, (α t : ℂ) ∈ slitPlane)
    (t : unitInterval) : cexp (logLift α hα t) = (α t : ℂ) := exp_log (α t).2

@[simp] theorem exp_negLift {p q : CStar} (β : Path p q) (hβ : ∀ t, -(β t : ℂ) ∈ slitPlane)
    (t : unitInterval) : cexp (negLift β hβ t) = (β t : ℂ) := by
  show cexp (log (-(β t : ℂ)) + Real.pi * I) = _
  rw [exp_add, exp_log (neg_ne_zero.mpr (β t).2), exp_pi_mul_I]; ring

theorem expMap_log (p : CStar) : expMap (log (p : ℂ)) = p := Subtype.ext (exp_log p.2)

/-- **Three-arc index.** A loop split into an arc off the negative real axis, an arc off the
positive real axis, and a final arc off the negative real axis, whose two interior junctions lie in
the upper and lower half-planes respectively, has index `1`. Only signs enter: the branch
`log (-z) + πi` agrees with `log` above the real axis and exceeds it by `2πi` below. -/
theorem liftIndex_three_arcs {p q r : CStar} (α : Path p q) (β : Path q r) (δ : Path r p)
    (hα : ∀ t, (α t : ℂ) ∈ slitPlane) (hβ : ∀ t, -(β t : ℂ) ∈ slitPlane)
    (hδ : ∀ t, (δ t : ℂ) ∈ slitPlane) (hq : 0 < (q : ℂ).im) (hr : (r : ℂ).im < 0) :
    liftIndex (⟨log (p : ℂ), expMap_log p⟩ : expMap ⁻¹' {p})
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((α.trans β).trans δ))) = 1 := by
  set Γ : Path (log (p : ℂ)) (log (p : ℂ) + per) :=
    ((logLift α hα).trans ((negLift β hβ).cast (negBranch_of_im_pos hq).symm
      (negBranch_of_im_neg hr).symm)).trans
      ((logLift δ hδ).map (continuous_add_const per)) with hΓ
  have hend : expMap (log (p : ℂ) + per) = p := by rw [expMap_add_per, expMap_log]
  have hpath : Γ.map continuous_expMap
      = ((α.trans β).trans δ).cast (expMap_log p) hend := by
    ext t
    simp only [hΓ, Path.map_coe, Path.cast_coe, Function.comp_apply, Path.trans_apply]
    split_ifs <;> simp [exp_add, exp_two_pi_mul_I]
  have hmono : isAddQuotientCoveringMap_exp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk ((α.trans β).trans δ))
      (⟨log (p : ℂ), expMap_log p⟩ : expMap ⁻¹' {p})
      = (⟨log (p : ℂ) + per, hend⟩ : expMap ⁻¹' {p}) := by
    refine isAddQuotientCoveringMap_exp.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk Γ) ?_
    exact congrArg Path.Homotopic.Quotient.mk hpath
  refine (liftIndex_unique _ ?_).symm
  have h := liftDisp_add_base (⟨log (p : ℂ), expMap_log p⟩ : expMap ⁻¹' {p})
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((α.trans β).trans δ)))
  rw [hmono] at h
  simp only [one_zsmul]
  have h' : liftDisp (⟨log (p : ℂ), expMap_log p⟩ : expMap ⁻¹' {p})
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((α.trans β).trans δ)))
      + log (p : ℂ) = log (p : ℂ) + per := h
  linear_combination -h'

end Sz8.Galois
