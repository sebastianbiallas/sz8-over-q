import Sz8.Monodromy.RootTransport
import Sz8.Galois.NodeAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The local node theorem: continuous root branches give trivial local monodromy

Paper-independent. For a `MonicFamily` of degree `n ≥ 4` and a parameter `a` at which `P a` has
exactly one double root and otherwise simple roots, and whose resultant `Res(P_t, P_t')` has the
form `(t - a)^2 V(t)` with `V` continuous and `V(a) ≠ 0`, every loop of regular parameters in a
small disc about `a` has trivial monodromy.

Route: continue the simple roots by the implicit function theorem; `P_t = R_t Q_t` with
`R_t = ∏ (X - ψᵢ(t))` and `Q_t = X² + b X + c`, `b`, `c` read off two coefficients, proved by
`deg (P - R Q) ≤ n - 3` and `n - 2` distinct roots; `D = -E Δ` (`NodeAlgebra`), so
`Δ = (t - a)^2 u` with `u` continuous and nonzero; a continuous `√u`; the roots
`(-b ± (t - a) √u)/2`; every root is the value of a continuous section, so every lift is a
section and monodromy is trivial.
-/

open Polynomial Topology Set Metric Filter

namespace Sz8.Galois.NodeLocal

open Sz8.Monodromy Sz8.Monodromy.MonicFamily

variable (M : MonicFamily)

/-! ### A. A simple root continues -/

theorem exists_branch {t₀ x₀ : ℂ} (hz : (M.P t₀).eval x₀ = 0)
    (hc : (M.P t₀).derivative.eval x₀ ≠ 0) :
    ∃ δ > 0, ∃ ψ : ℂ → ℂ, ψ t₀ = x₀ ∧ ContinuousOn ψ (ball t₀ δ) ∧
      ∀ t ∈ ball t₀ δ, (M.P t).eval (ψ t) = 0 := by
  classical
  set f := fun p : ℂ × ℂ => (M.P p.1).eval p.2 with hf
  have cdf : ContDiffAt ℂ 1 f (t₀, x₀) := M.contDiff.contDiffAt
  have if₂ : ((fderiv ℂ f (t₀, x₀)).comp (ContinuousLinearMap.inr ℂ ℂ ℂ)).IsInvertible := by
    rw [M.fderiv_comp_inr]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hc), ?_⟩
    ext
    simp [ContinuousLinearEquiv.unitsEquivAut_apply]
  set ψ := cdf.implicitFunction one_ne_zero if₂
  have hψ₀ : ψ t₀ = x₀ := cdf.implicitFunction_apply_self one_ne_zero if₂
  have hiff := cdf.eventually_apply_eq_iff_implicitFunction one_ne_zero if₂
  have hz₀' : f (t₀, x₀) = 0 := hz
  rw [hz₀'] at hiff
  have hcont : ∀ᶠ t in 𝓝 t₀, ContinuousAt ψ t :=
    ((cdf.contDiffAt_implicitFunction one_ne_zero if₂).eventually (by simp)).mono
      fun t ht => ht.continuousAt
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
  refine ⟨δ, hδ, ψ, hψ₀, fun t ht => (hδball ht).1.1.continuousWithinAt, fun t ht => ?_⟩
  exact (hbox (t, ψ t) (hδball ht).2 (hδball ht).1.2).mpr rfl

/-! ### B. Continuity of coefficients -/

/-- Every coefficient of `p t` is continuous on `U`. -/
def CoeffCont (p : ℂ → ℂ[X]) (U : Set ℂ) : Prop := ∀ k, ContinuousOn (fun t => (p t).coeff k) U

theorem CoeffCont.mul {p q : ℂ → ℂ[X]} {U : Set ℂ} (hp : CoeffCont p U) (hq : CoeffCont q U) :
    CoeffCont (fun t => p t * q t) U := fun k => by
  simp only [coeff_mul]
  exact continuousOn_finset_sum _ fun x _ => (hp x.1).mul (hq x.2)

theorem CoeffCont.add {p q : ℂ → ℂ[X]} {U : Set ℂ} (hp : CoeffCont p U) (hq : CoeffCont q U) :
    CoeffCont (fun t => p t + q t) U := fun k => by
  simp only [coeff_add]; exact (hp k).add (hq k)

theorem CoeffCont.sub {p q : ℂ → ℂ[X]} {U : Set ℂ} (hp : CoeffCont p U) (hq : CoeffCont q U) :
    CoeffCont (fun t => p t - q t) U := fun k => by
  simp only [coeff_sub]; exact (hp k).sub (hq k)

theorem coeffCont_C {g : ℂ → ℂ} {U : Set ℂ} (hg : ContinuousOn g U) : CoeffCont (fun t => C (g t)) U :=
  fun k => by
    simp only [coeff_C]; split_ifs
    · exact hg
    · exact continuousOn_const

theorem coeffCont_X {U : Set ℂ} : CoeffCont (fun _ => (X : ℂ[X])) U := fun _ => continuousOn_const

theorem coeffCont_prod {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ[X]} {U : Set ℂ}
    (hf : ∀ i ∈ s, CoeffCont (f i) U) : CoeffCont (fun t => ∏ i ∈ s, f i t) U := by
  classical
  induction s using Finset.induction_on with
  | empty => intro k; simp only [Finset.prod_empty]; exact continuousOn_const
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-! ### C. `P = R Q` -/

section factor

variable {n : ℕ} (P : ℂ → ℂ[X]) (Z : Finset ℂ) (ψ : ℂ → ℂ → ℂ)

/-- The product of the simple-root branches. -/
noncomputable def Rt (t : ℂ) : ℂ[X] := ∏ x ∈ Z, (X - C (ψ x t))

/-- The linear coefficient of the residual quadratic. -/
noncomputable def bt (n : ℕ) (t : ℂ) : ℂ := (P t).coeff (n - 1) - (Rt Z ψ t).coeff (n - 3)

/-- The constant coefficient of the residual quadratic. -/
noncomputable def ct (n : ℕ) (t : ℂ) : ℂ :=
  (P t).coeff (n - 2) - (Rt Z ψ t).coeff (n - 4) - bt P Z ψ n t * (Rt Z ψ t).coeff (n - 3)

/-- The residual quadratic. -/
noncomputable def Qt (n : ℕ) (t : ℂ) : ℂ[X] := X ^ 2 + C (bt P Z ψ n t) * X + C (ct P Z ψ n t)

theorem Rt_monic (t : ℂ) : (Rt Z ψ t).Monic :=
  monic_prod_of_monic _ _ fun x _ => monic_X_sub_C _

theorem Rt_natDegree (t : ℂ) : (Rt Z ψ t).natDegree = Z.card := by
  rw [Rt, natDegree_prod_of_monic _ _ fun x _ => monic_X_sub_C _]
  simp

theorem Qt_monic (t : ℂ) : (Qt P Z ψ n t).Monic := by
  unfold Qt; monicity!

theorem Qt_natDegree (t : ℂ) : (Qt P Z ψ n t).natDegree = 2 := by
  unfold Qt; compute_degree!

theorem coeff_mul_Qt (R : ℂ[X]) (b c : ℂ) (k : ℕ) :
    (R * (X ^ 2 + C b * X + C c)).coeff (k + 2)
      = R.coeff k + b * R.coeff (k + 1) + c * R.coeff (k + 2) := by
  rw [mul_add, mul_add, coeff_add, coeff_add, coeff_mul_X_pow, mul_comm (C b) X, ← mul_assoc,
    coeff_mul_C, coeff_mul_X, coeff_mul_C]
  ring

/-- **Factorization.** If the branches are distinct roots of `P t`, `P t` is monic of degree
`n = |Z| + 2`, then `P t = R_t Q_t`. -/
theorem P_eq_Rt_mul_Qt (hn : 4 ≤ n) (hZ : Z.card + 2 = n) {t : ℂ} (hmon : (P t).Monic)
    (hdeg : (P t).natDegree = n) (hroot : ∀ x ∈ Z, (P t).eval (ψ x t) = 0)
    (hinj : ∀ x ∈ Z, ∀ y ∈ Z, ψ x t = ψ y t → x = y) :
    P t = Rt Z ψ t * Qt P Z ψ n t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  set R := Rt Z ψ t
  set H := P t - R * Qt P Z ψ (m + 4) t with hH
  have hRdeg : R.natDegree = m + 2 := by rw [Rt_natDegree]; omega
  have hRtop : R.coeff (m + 2) = 1 := by rw [← hRdeg]; exact Rt_monic Z ψ t
  have hRz : ∀ k, m + 2 < k → R.coeff k = 0 := fun k hk =>
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hPtop : (P t).coeff (m + 4) = 1 := by rw [← hdeg]; exact hmon
  have hPz : ∀ k, m + 4 < k → (P t).coeff k = 0 := fun k hk =>
    coeff_eq_zero_of_natDegree_lt (by omega)
  have i1 : m + 4 - 1 = m + 3 := by omega
  have i2 : m + 4 - 2 = m + 2 := by omega
  have i3 : m + 4 - 3 = m + 1 := by omega
  have i4 : m + 4 - 4 = m := by omega
  have hcoeff : ∀ k, m + 2 ≤ k → H.coeff k = 0 := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [hH, coeff_sub, Qt, coeff_mul_Qt]
    rcases (show j = m ∨ j = m + 1 ∨ j = m + 2 ∨ m + 2 < j by omega) with rfl | rfl | rfl | hj
    · simp only [ct, bt, i1, i2, i3, i4, hRtop]
      ring
    · simp only [bt, i1, i3, hRtop, show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega,
        hRz (m + 3) (by omega)]
      ring
    · simp only [show m + 2 + 1 = m + 3 by omega, show m + 2 + 2 = m + 4 by omega, hRtop,
        hRz (m + 3) (by omega), hRz (m + 4) (by omega), hPtop]
      ring
    · rw [hPz (j + 2) (by omega), hRz j hj, hRz (j + 1) (by omega), hRz (j + 2) (by omega)]
      ring
  have hHdeg : H.natDegree < Z.card := by
    have := (natDegree_le_iff_coeff_eq_zero (p := H) (n := m + 1)).2 fun N hN =>
      hcoeff N (by exact_mod_cast hN)
    omega
  have hR0 : ∀ x ∈ Z, R.eval (ψ x t) = 0 := by
    intro x hx
    simp only [R, Rt, eval_prod]
    exact Finset.prod_eq_zero hx (by simp)
  have hH0 : H = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero H (ι := Z) (f := fun x => ψ x.1 t)
      (fun x y hxy => Subtype.ext (hinj x.1 x.2 y.1 y.2 hxy)) (fun x => ?_) (by simpa using hHdeg)
    simp [hH, hroot x.1 x.2, hR0 x.1 x.2]
  exact sub_eq_zero.1 hH0

end factor

/-! ### D. Square root, quadratic roots, continuity of resultants -/

/-- A continuous square root of a continuous function that does not vanish at `a`. -/
theorem exists_sqrt {u : ℂ → ℂ} {a : ℂ} {ε : ℝ} (hε : 0 < ε) (hu : ContinuousOn u (ball a ε))
    (hua : u a ≠ 0) :
    ∃ r > 0, r ≤ ε ∧ ∃ s : ℂ → ℂ, ContinuousOn s (ball a r) ∧ ∀ t ∈ ball a r, s t ^ 2 = u t := by
  set w := fun t => u t / u a
  have hwa : w a ∈ Complex.slitPlane := by simp [w, hua, Complex.one_mem_slitPlane]
  have hwc : ContinuousAt w a :=
    ((hu a (mem_ball_self hε)).continuousAt (ball_mem_nhds a hε)).div_const _
  have hev : ∀ᶠ t in 𝓝 a, w t ∈ Complex.slitPlane ∧ t ∈ ball a ε :=
    Filter.Eventually.and (show ∀ᶠ t in 𝓝 a, w t ∈ Complex.slitPlane from
      hwc.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hwa)) (ball_mem_nhds a hε)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨min r ε, lt_min hr hε, min_le_right _ _, fun t => u a ^ ((2 : ℕ)⁻¹ : ℂ) * w t ^ ((2 : ℕ)⁻¹ : ℂ),
    ?_, fun t ht => ?_⟩
  · refine continuousOn_const.mul (ContinuousOn.cpow_const ?_ fun t ht => ?_)
    · exact (hu.mono (ball_subset_ball (min_le_right _ _))).div_const _
    · exact (hball t (ball_subset_ball (min_le_left _ _) ht)).1
  · rw [mul_pow, Complex.cpow_nat_inv_pow _ two_ne_zero, Complex.cpow_nat_inv_pow _ two_ne_zero]
    simp only [w]
    field_simp

/-- The roots of a monic quadratic with discriminant `(d s)^2`. -/
theorem quadratic_factor (b c d s : ℂ) (h : b ^ 2 - 4 * c = (d * s) ^ 2) :
    (X ^ 2 + C b * X + C c : ℂ[X])
      = (X - C ((-b + d * s) / 2)) * (X - C ((-b - d * s) / 2)) := by
  have hc : c = (b ^ 2 - (d * s) ^ 2) / 4 := by rw [← h]; ring
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub, hc]
  ring

theorem coeffCont_derivative {p : ℂ → ℂ[X]} {U : Set ℂ} (hp : CoeffCont p U) :
    CoeffCont (fun t => derivative (p t)) U := fun k => by
  simp only [coeff_derivative]
  exact (hp (k + 1)).mul continuousOn_const

/-- A resultant with fixed formal degrees depends continuously on coefficients. -/
theorem continuousOn_resultant {f g : ℂ → ℂ[X]} {U : Set ℂ} (hf : CoeffCont f U)
    (hg : CoeffCont g U) (m k : ℕ) : ContinuousOn (fun t => resultant (f t) (g t) m k) U := by
  classical
  rw [continuousOn_iff_continuous_restrict]
  refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
  show Continuous fun t : U => sylvester (f t) (g t) m k i j
  simp only [sylvester, Matrix.of_apply]
  induction j using Fin.addCases with
  | left j =>
    simp only [Fin.addCases_left]
    split_ifs
    · exact (continuousOn_iff_continuous_restrict.1 (hg _))
    · exact continuous_const
  | right j =>
    simp only [Fin.addCases_right]
    split_ifs
    · exact (continuousOn_iff_continuous_restrict.1 (hf _))
    · exact continuous_const

/-! ### E. A continuous root section is a lift -/

/-- If the root of `e` continues as a continuous root section along a loop, the loop fixes `e`. -/
theorem monodromy_eq_self_of_section {U : Set ℂ} {σ : ℂ → ℂ} (hσ : ContinuousOn σ U)
    (hroot : ∀ t ∈ U, (M.P t).eval (σ t) = 0) {b : M.Base} (δ : Path b b)
    (hδ : ∀ u, ((δ u : M.Base) : ℂ) ∈ U) (e : M.Fiber b) (he : e.root = σ b.1) :
    M.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk δ) e = e := by
  have hc : Continuous fun u => σ ((δ u : M.Base) : ℂ) :=
    hσ.comp_continuous (continuous_subtype_val.comp δ.continuous) hδ
  have h0 : ∀ u, (⟨(((δ u : M.Base) : ℂ), σ (δ u : M.Base)), hroot _ (hδ u)⟩ : M.RootSpace)
      ∈ M.proj ⁻¹' M.regular := fun u => (δ u).2
  have hend : ∀ {u}, δ u = b → (⟨⟨(((δ u : M.Base) : ℂ), σ (δ u : M.Base)), hroot _ (hδ u)⟩, h0 u⟩ :
      M.proj ⁻¹' M.regular) = e.1 := by
    intro u hu
    apply Subtype.ext; apply Subtype.ext
    simp only [hu]
    ext
    · exact e.param.symm
    · exact he.symm
  let Γ : Path e.1 e.1 :=
    { toFun := fun u => ⟨⟨(((δ u : M.Base) : ℂ), σ (δ u : M.Base)), hroot _ (hδ u)⟩, h0 u⟩
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        exact (continuous_subtype_val.comp δ.continuous).prodMk hc
      source' := hend δ.source
      target' := hend δ.target }
  refine M.isCoveringMap.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk Γ) ?_
  refine congrArg Path.Homotopic.Quotient.mk (Path.ext (funext fun u => ?_))
  rfl

/-! ### F. The local node theorem -/

/-- **Local node theorem.** Let `P a` have one double root `r₀` and otherwise simple roots, and let
`Res(P_t, P_t') = (t - a)^2 V(t)` near `a` with `V` continuous and `V(a) ≠ 0`. Then every loop of
regular parameters in a small enough disc about `a` has trivial monodromy. -/
theorem local_monodromy_trivial (hn : 4 ≤ M.n) (a : ℂ)
    (hmult : ∀ r, (M.P a).rootMultiplicity r ≤ 2) (r₀ : ℂ) (hr₀ : (M.P a).rootMultiplicity r₀ = 2)
    (huniq : ∀ r, 2 ≤ (M.P a).rootMultiplicity r → r = r₀)
    {ε : ℝ} (hε : 0 < ε) (V : ℂ → ℂ) (hV : ContinuousOn V (ball a ε)) (hVa : V a ≠ 0)
    (hD : ∀ t ∈ ball a ε, resultant (M.P t) (derivative (M.P t)) = (t - a) ^ 2 * V t) :
    ∃ r > 0, ∀ (b : M.Base) (δ : Path b b), (∀ u, ((δ u : M.Base) : ℂ) ∈ ball a r) →
      ∀ e : M.Fiber b, M.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk δ) e = e := by
  classical
  have hPa0 : M.P a ≠ 0 := (M.monic a).ne_zero
  -- the simple roots at `a`
  set Z := (M.P a).roots.toFinset.erase r₀ with hZ
  have hroot_of_mem : ∀ x ∈ (M.P a).roots.toFinset, (M.P a).IsRoot x := fun x hx =>
    (mem_roots hPa0).1 (Multiset.mem_toFinset.1 hx)
  have hr₀mem : r₀ ∈ (M.P a).roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hPa0, ← rootMultiplicity_pos hPa0, hr₀]; norm_num
  have hZmult : ∀ x ∈ Z, (M.P a).rootMultiplicity x = 1 := by
    intro x hx
    obtain ⟨hne, hx'⟩ := Finset.mem_erase.1 hx
    have hpos := (rootMultiplicity_pos hPa0).2 (hroot_of_mem x hx')
    by_contra h
    exact hne (huniq x (by omega))
  have hcard : Z.card + 2 = M.n := by
    have hsum := Multiset.toFinset_sum_count_eq (M.P a).roots
    rw [IsAlgClosed.card_roots_eq_natDegree, M.natDegree_eq, ← Finset.add_sum_erase _ _ hr₀mem,
      count_roots, hr₀] at hsum
    rw [Finset.sum_congr rfl fun x hx => by rw [count_roots, hZmult x hx]] at hsum
    simp at hsum
    have hZc : Z.card = ((M.P a).roots.toFinset.erase r₀).card := rfl
    omega
  have hderiv : ∀ x ∈ Z, (M.P a).derivative.eval x ≠ 0 := by
    intro x hx h
    have := (one_lt_rootMultiplicity_iff_isRoot hPa0).2
      ⟨hroot_of_mem x (Finset.mem_of_mem_erase hx), h⟩
    rw [hZmult x hx] at this
    exact lt_irrefl _ this
  -- branches
  have hbr : ∀ x ∈ Z, ∃ δ > 0, ∃ ψ : ℂ → ℂ, ψ a = x ∧ ContinuousOn ψ (ball a δ) ∧
      ∀ t ∈ ball a δ, (M.P t).eval (ψ t) = 0 := fun x hx =>
    exists_branch M (hroot_of_mem x (Finset.mem_of_mem_erase hx)) (hderiv x hx)
  choose! δf hδf ψ hψa hψc hψr using hbr
  -- a first radius: all branches defined, inside the resultant disc
  have hev0 : ∀ᶠ t in 𝓝 a, (∀ x ∈ Z, t ∈ ball a (δf x)) ∧ t ∈ ball a ε :=
    ((Filter.eventually_all_finset Z).2 fun x hx => ball_mem_nhds a (hδf x hx)).and
      (ball_mem_nhds a hε)
  obtain ⟨ρ₀, hρ₀, hball₀⟩ := Metric.eventually_nhds_iff_ball.1 hev0
  set U₀ := ball a ρ₀
  have hψc₀ : ∀ x ∈ Z, ContinuousOn (ψ x) U₀ := fun x hx =>
    (hψc x hx).mono fun t ht => (hball₀ t ht).1 x hx
  have hψr₀ : ∀ x ∈ Z, ∀ t ∈ U₀, (M.P t).eval (ψ x t) = 0 := fun x hx t ht =>
    hψr x hx t ((hball₀ t ht).1 x hx)
  have hU₀ε : U₀ ⊆ ball a ε := fun t ht => (hball₀ t ht).2
  have ha₀ : a ∈ U₀ := mem_ball_self hρ₀
  -- coefficient continuity on `U₀`
  have hPc : CoeffCont M.P U₀ := fun k => (M.continuous_coeff k).continuousOn
  have hRc : CoeffCont (Rt Z ψ) U₀ := by
    refine coeffCont_prod Z fun x hx => ?_
    exact coeffCont_X.sub (coeffCont_C (hψc₀ x hx))
  have hbc : ContinuousOn (bt M.P Z ψ M.n) U₀ := (hPc _).sub (hRc _)
  have hcc : ContinuousOn (ct M.P Z ψ M.n) U₀ := ((hPc _).sub (hRc _)).sub (hbc.mul (hRc _))
  have hQc : CoeffCont (Qt M.P Z ψ M.n) U₀ := by
    have h2 : CoeffCont (fun _ => (X : ℂ[X]) ^ 2) U₀ := fun _ => continuousOn_const
    exact (h2.add ((coeffCont_C hbc).mul coeffCont_X)).add (coeffCont_C hcc)
  -- the factor `E`
  set E := fun t => resultant (Rt Z ψ t) (derivative (Rt Z ψ t)) * resultant (Rt Z ψ t) (Qt M.P Z ψ M.n t)
    * resultant (Qt M.P Z ψ M.n t) (Rt Z ψ t) with hE
  have hRdeg : ∀ t, (Rt Z ψ t).natDegree = M.n - 2 := fun t => by rw [Rt_natDegree]; omega
  have hRdeg' : ∀ t, (derivative (Rt Z ψ t)).natDegree = M.n - 3 := fun t => by
    rw [natDegree_derivative, hRdeg]; omega
  have hEc : ContinuousOn E U₀ := by
    have e1 : ∀ t, resultant (Rt Z ψ t) (derivative (Rt Z ψ t))
        = resultant (Rt Z ψ t) (derivative (Rt Z ψ t)) (M.n - 2) (M.n - 3) := fun t => by
      rw [hRdeg, hRdeg']
    have e2 : ∀ t, resultant (Rt Z ψ t) (Qt M.P Z ψ M.n t)
        = resultant (Rt Z ψ t) (Qt M.P Z ψ M.n t) (M.n - 2) 2 := fun t => by
      rw [hRdeg, Qt_natDegree]
    have e3 : ∀ t, resultant (Qt M.P Z ψ M.n t) (Rt Z ψ t)
        = resultant (Qt M.P Z ψ M.n t) (Rt Z ψ t) 2 (M.n - 2) := fun t => by
      rw [hRdeg, Qt_natDegree]
    simp only [hE, e1, e2, e3]
    exact ((continuousOn_resultant hRc (coeffCont_derivative hRc) _ _).mul
      (continuousOn_resultant hRc hQc _ _)).mul (continuousOn_resultant hQc hRc _ _)
  -- factorization wherever the branches are distinct
  have hfac : ∀ t ∈ U₀, (∀ x ∈ Z, ∀ y ∈ Z, ψ x t = ψ y t → x = y) →
      M.P t = Rt Z ψ t * Qt M.P Z ψ M.n t := fun t ht hinj =>
    P_eq_Rt_mul_Qt M.P Z ψ hn hcard (M.monic t) (M.natDegree_eq t) (fun x hx => hψr₀ x hx t ht) hinj
  have hinja : ∀ x ∈ Z, ∀ y ∈ Z, ψ x a = ψ y a → x = y := fun x hx y hy h => by
    rwa [hψa x hx, hψa y hy] at h
  have hfaca := hfac a ha₀ hinja
  -- `E a ≠ 0`
  have hRa : Rt Z ψ a = ∏ x ∈ Z, (X - C x) := Finset.prod_congr rfl fun x hx => by rw [hψa x hx]
  have hQa_ne : ∀ x ∈ Z, (Qt M.P Z ψ M.n a).eval x ≠ 0 := by
    intro x hx hQ
    have h1 : X - C x ∣ Rt Z ψ a := by
      rw [hRa]; exact Finset.dvd_prod_of_mem _ hx
    have h2 : X - C x ∣ Qt M.P Z ψ M.n a := dvd_iff_isRoot.2 hQ
    have h3 : (X - C x) ^ 2 ∣ M.P a := by
      rw [hfaca, pow_two]; exact mul_dvd_mul h1 h2
    have := (le_rootMultiplicity_iff hPa0).2 h3
    rw [hZmult x hx] at this
    omega
  have hcopRQ : IsCoprime (Rt Z ψ a) (Qt M.P Z ψ M.n a) := by
    refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := ℂ) ℂ _ _).2 fun z => ?_
    simp only [aeval_def, eval₂_eq_eval_map, Algebra.algebraMap_self, Polynomial.map_id]
    by_cases hz : (Rt Z ψ a).eval z = 0
    · right
      rw [hRa, eval_prod, Finset.prod_eq_zero_iff] at hz
      obtain ⟨x, hx, hxz⟩ := hz
      have : z = x := by simpa [sub_eq_zero] using hxz
      rw [this]; exact hQa_ne x hx
    · exact Or.inl hz
  have hsepR : IsCoprime (Rt Z ψ a) (derivative (Rt Z ψ a)) := by
    have : (Rt Z ψ a).Separable := by
      rw [hRa]; exact separable_prod_X_sub_C_iff'.2 fun x _ y _ h => h
    exact this
  have hEa : E a ≠ 0 := by
    simp only [hE]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · intro h; rw [resultant_eq_zero_iff] at h; exact h.2 hsepR
    · intro h; rw [resultant_eq_zero_iff] at h; exact h.2 hcopRQ
    · intro h; rw [resultant_eq_zero_iff] at h; exact h.2 hcopRQ.symm
  -- a second radius: distinct branches, `E ≠ 0`
  have hEca : ContinuousAt E a := (hEc a ha₀).continuousAt (ball_mem_nhds a hρ₀)
  have hev1 : ∀ᶠ t in 𝓝 a, (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → ψ x t ≠ ψ y t) ∧ E t ≠ 0 ∧ t ∈ U₀ := by
    refine ((Filter.eventually_all_finset Z).2 fun x hx => (Filter.eventually_all_finset Z).2
      fun y hy => ?_).and (hEca.eventually_ne hEa |>.and (ball_mem_nhds a hρ₀))
    by_cases hxy : x = y
    · exact Filter.Eventually.of_forall fun _ h => absurd hxy h
    · have hc : ContinuousAt (fun t => ψ x t - ψ y t) a :=
        (((hψc₀ x hx).sub (hψc₀ y hy)) a ha₀).continuousAt (ball_mem_nhds a hρ₀)
      have hne : ψ x a - ψ y a ≠ 0 := by rw [hψa x hx, hψa y hy]; exact sub_ne_zero.2 hxy
      exact (hc.eventually_ne hne).mono fun t ht _ h => ht (sub_eq_zero.2 h)
  obtain ⟨ρ₁, hρ₁, hball₁⟩ := Metric.eventually_nhds_iff_ball.1 hev1
  set U₁ := ball a ρ₁
  have hU₁₀ : U₁ ⊆ U₀ := fun t ht => (hball₁ t ht).2.2
  have hinj₁ : ∀ t ∈ U₁, ∀ x ∈ Z, ∀ y ∈ Z, ψ x t = ψ y t → x = y := fun t ht x hx y hy h => by
    by_contra hxy; exact (hball₁ t ht).1 x hx y hy hxy h
  -- `Δ = (t - a)^2 u`
  set u := fun t => -V t / E t with hu
  have hΔ : ∀ t ∈ U₁, bt M.P Z ψ M.n t ^ 2 - 4 * ct M.P Z ψ M.n t = (t - a) ^ 2 * u t := by
    intro t ht
    have hEt := (hball₁ t ht).2.1
    have hDt := hD t (hU₀ε (hU₁₀ ht))
    rw [hfac t (hU₁₀ ht) (hinj₁ t ht), NodeAlgebra.resultant_mul_derivative (Rt_monic Z ψ t)
      (Qt_monic M.P Z ψ t) (by rw [Rt_natDegree]; omega) (by rw [Qt_natDegree]; norm_num)] at hDt
    have hQQ : resultant (Qt M.P Z ψ M.n t) (derivative (Qt M.P Z ψ M.n t))
        = -(bt M.P Z ψ M.n t ^ 2 - 4 * ct M.P Z ψ M.n t) :=
      NodeAlgebra.resultant_quadratic_derivative _ _
    rw [hQQ] at hDt
    have hprod : (bt M.P Z ψ M.n t ^ 2 - 4 * ct M.P Z ψ M.n t) * E t = (t - a) ^ 2 * -V t := by
      simp only [hE]; linear_combination -hDt
    simp only [hu]
    rw [← mul_div_assoc, eq_div_iff hEt]
    exact hprod
  have huc : ContinuousOn u U₁ := by
    refine ((hV.mono fun t ht => hU₀ε (hU₁₀ ht)).neg).div (hEc.mono hU₁₀) fun t ht => (hball₁ t ht).2.1
  have hua : u a ≠ 0 := by
    simp only [hu]; exact div_ne_zero (neg_ne_zero.2 hVa) hEa
  -- a square root, and the final radius
  obtain ⟨r, hr, hrρ, sq, hsqc, hsq⟩ := exists_sqrt hρ₁ huc hua
  set U := ball a r
  have hUU₁ : U ⊆ U₁ := ball_subset_ball hrρ
  set qp := fun t => (-bt M.P Z ψ M.n t + (t - a) * sq t) / 2
  set qm := fun t => (-bt M.P Z ψ M.n t - (t - a) * sq t) / 2
  have hqpc : ContinuousOn qp U :=
    (((hbc.mono fun t ht => hU₁₀ (hUU₁ ht)).neg.add
      ((continuousOn_id.sub continuousOn_const).mul hsqc))).div_const _
  have hqmc : ContinuousOn qm U :=
    (((hbc.mono fun t ht => hU₁₀ (hUU₁ ht)).neg.sub
      ((continuousOn_id.sub continuousOn_const).mul hsqc))).div_const _
  have hQfac : ∀ t ∈ U, Qt M.P Z ψ M.n t = (X - C (qp t)) * (X - C (qm t)) := by
    intro t ht
    refine quadratic_factor _ _ _ _ ?_
    rw [hΔ t (hUU₁ ht), mul_pow, hsq t ht]
  -- every root is on a continuous section
  have hcover : ∀ t ∈ U, ∀ x, (M.P t).eval x = 0 →
      (∃ y ∈ Z, ψ y t = x) ∨ qp t = x ∨ qm t = x := by
    intro t ht x hx
    rw [hfac t (hU₁₀ (hUU₁ ht)) (hinj₁ t (hUU₁ ht)), eval_mul, mul_eq_zero] at hx
    rcases hx with hx | hx
    · left
      rw [Rt, eval_prod, Finset.prod_eq_zero_iff] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      exact ⟨y, hy, by simpa [sub_eq_zero, eq_comm] using hxy⟩
    · right
      rw [hQfac t ht, eval_mul, mul_eq_zero] at hx
      simp only [eval_sub, eval_X, eval_C] at hx
      rcases hx with hx | hx
      · exact Or.inl (sub_eq_zero.1 hx).symm
      · exact Or.inr (sub_eq_zero.1 hx).symm
  have hqroot : ∀ t ∈ U, (M.P t).eval (qp t) = 0 ∧ (M.P t).eval (qm t) = 0 := by
    intro t ht
    rw [hfac t (hU₁₀ (hUU₁ ht)) (hinj₁ t (hUU₁ ht)), hQfac t ht]
    simp
  refine ⟨r, hr, fun b δ hδ e => ?_⟩
  have hb : (b : ℂ) ∈ U := by have := hδ 0; rwa [δ.source] at this
  rcases hcover b hb e.root e.isRoot with ⟨y, hy, hyr⟩ | hq | hq
  · exact monodromy_eq_self_of_section M ((hψc₀ y hy).mono fun t ht => hU₁₀ (hUU₁ ht))
      (fun t ht => hψr₀ y hy t (hU₁₀ (hUU₁ ht))) δ hδ e hyr.symm
  · exact monodromy_eq_self_of_section M hqpc (fun t ht => (hqroot t ht).1) δ hδ e hq.symm
  · exact monodromy_eq_self_of_section M hqmc (fun t ht => (hqroot t ht).2) δ hδ e hq.symm

end Sz8.Galois.NodeLocal
