import Sz8.Galois.Bridge
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# (O), first checkpoint: the orbit polynomial on the regular locus

For a homotopy class `q` of paths `b → t`, the transported labelling is `monodromy q`, and
`orbitPolyOf c q = ∏_{h ∈ M} (Z - Σₓ cₓ root(monodromy q (h x)))`, a product over the monodromy
subgroup `M` (kept symbolic).

* `monodromy_eq_comp` — transport composition: `monodromy q' = monodromy q ∘ monodromy (q' q⁻¹)`,
  so changing the path multiplies `h` on the **left** by an element of `M`;
* `orbitPolyOf_indep` — hence `orbitPolyOf` does not depend on the path;
* `orbitPoly_local` — near each point reachable from `b`, `orbitPoly` is the product over `M` of
  expressions in a fixed family of analytic root sections (no continuity of chosen paths needed);
* `orbitCoeff_analyticAt` — its coefficients are analytic there;
* `exists_separating` — weights `c` whose weighted root sums separate **all** permutations at `b`.
-/

open Polynomial Topology Filter Metric Set

namespace Sz8.Galois.Orbit

open Sz8.Monodromy Sz8.Monodromy.MonicFamily Germs Continuation

variable (M : MonicFamily) (b : M.Base)

/-- The monodromy subgroup. -/
noncomputable abbrev Mon : Subgroup (Equiv.Perm (M.Fiber b)) := (M.isCoveringMap.monodromyPerm b).range

noncomputable instance : Fintype (Mon M b) := Fintype.ofFinite _

variable {M b}

/-- **Transport composition.** -/
theorem monodromy_eq_comp {t : M.Base} (q q' : Path.Homotopic.Quotient b t) (x : M.Fiber b) :
    M.isCoveringMap.monodromy q' x =
      M.isCoveringMap.monodromy q (M.isCoveringMap.monodromyPerm b (q'.trans q.symm) x) := by
  rw [IsCoveringMap.coe_monodromyPerm, ← IsCoveringMap.monodromy_trans_apply,
    Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

variable (M b)

/-- The orbit polynomial along a class of paths. -/
noncomputable def orbitPolyOf (c : M.Fiber b → ℂ) {t : M.Base} (q : Path.Homotopic.Quotient b t) :
    ℂ[X] :=
  ∏ h : Mon M b, (X - C (∑ x, c x * Fiber.root (t := t) (M.isCoveringMap.monodromy q (h.1 x))))

variable {M b}

/-- **Path independence.** -/
theorem orbitPolyOf_indep (c : M.Fiber b → ℂ) {t : M.Base} (q q' : Path.Homotopic.Quotient b t) :
    orbitPolyOf M b c q' = orbitPolyOf M b c q := by
  set g : Mon M b := ⟨M.isCoveringMap.monodromyPerm b (q'.trans q.symm), _, rfl⟩
  unfold orbitPolyOf
  refine Fintype.prod_equiv (Equiv.mulLeft g) _ _ fun h => ?_
  congr 2
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [monodromy_eq_comp q q' (h.1 x)]
  rfl

variable (M b)

open scoped Classical in
/-- The orbit polynomial at a regular parameter (via any path, if there is one). -/
noncomputable def orbitPoly (c : M.Fiber b → ℂ) (t : M.Base) : ℂ[X] :=
  if h : Nonempty (Path b t) then orbitPolyOf M b c (Path.Homotopic.Quotient.mk h.some) else 1

variable {M b}

theorem orbitPoly_eq (c : M.Fiber b → ℂ) {t : M.Base} (q : Path.Homotopic.Quotient b t) :
    orbitPoly M b c t = orbitPolyOf M b c q := by
  obtain ⟨p⟩ := q
  have h : Nonempty (Path b t) := ⟨p⟩
  rw [orbitPoly, dif_pos h]
  exact orbitPolyOf_indep c _ _

open scoped Classical in
/-- The coefficient functions on `ℂ` (zero off the regular locus). -/
noncomputable def orbitCoeff (M : MonicFamily) (b : M.Base) (c : M.Fiber b → ℂ) (k : ℕ) (t : ℂ) : ℂ :=
  if ht : t ∈ M.regular then (orbitPoly M b c ⟨t, ht⟩).coeff k else 0

/-! ## Local agreement with analytic root sections -/

/-- Transport along a path inside a region carrying a continuous root section follows the section. -/
theorem root_monodromy_of_section {U : Set ℂ} {ψ : ℂ → ℂ} (hψ : ContinuousOn ψ U)
    (hroot : ∀ t ∈ U, (M.P t).eval (ψ t) = 0) {T₀ T : M.Base} (σ : Path T₀ T)
    (hσ : ∀ u, ((σ u : M.Base) : ℂ) ∈ U) (e : M.Fiber T₀) (he : e.root = ψ T₀.1) :
    Fiber.root (t := T) (M.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk σ) e) = ψ T.1 := by
  have hT : T.1 ∈ U := by simpa using hσ 1
  set e' := M.mkFiber T (ψ T.1) (hroot _ hT)
  have hc : Continuous fun u => ψ ((σ u : M.Base) : ℂ) :=
    hψ.comp_continuous (continuous_subtype_val.comp σ.continuous) hσ
  have h0 : ∀ u, (⟨(((σ u : M.Base) : ℂ), ψ (σ u : M.Base)), hroot _ (hσ u)⟩ : M.RootSpace)
      ∈ M.proj ⁻¹' M.regular := fun u => (σ u).2
  let Γ : Path e.1 e'.1 :=
    { toFun := fun u => ⟨⟨(((σ u : M.Base) : ℂ), ψ (σ u : M.Base)), hroot _ (hσ u)⟩, h0 u⟩
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        exact (continuous_subtype_val.comp σ.continuous).prodMk hc
      source' := by
        apply Subtype.ext; apply Subtype.ext
        simp only [σ.source]
        ext
        · exact e.param.symm
        · exact he.symm
      target' := by
        apply Subtype.ext; apply Subtype.ext
        simp only [σ.target]
        rfl }
  have hm : M.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk σ) e = e' := by
    refine M.isCoveringMap.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk Γ) ?_
    exact congrArg Path.Homotopic.Quotient.mk (Path.ext (funext fun u => rfl))
  rw [hm]
  rfl

/-- **Local agreement.** Near a point reachable from `b`, the orbit polynomial is the product over
`M` of expressions in a fixed family of analytic root sections. -/
theorem orbitPoly_local (c : M.Fiber b → ℂ) {T₀ : M.Base} (q₀ : Path.Homotopic.Quotient b T₀) :
    ∃ δ > 0, ball T₀.1 δ ⊆ M.regular ∧ ∃ ψ : M.Fiber T₀ → ℂ → ℂ,
      (∀ e, AnalyticOnNhd ℂ (ψ e) (ball T₀.1 δ)) ∧ (∀ e, ψ e T₀.1 = e.root) ∧
      (∀ e, ∀ t ∈ ball T₀.1 δ, (M.P t).eval (ψ e t) = 0) ∧
      ∀ t (ht : t ∈ M.regular), t ∈ ball T₀.1 δ →
        orbitPoly M b c ⟨t, ht⟩ =
          ∏ h : Mon M b, (X - C (∑ x, c x * ψ (M.isCoveringMap.monodromy q₀ (h.1 x)) t)) := by
  have hb := fun e : M.Fiber T₀ => exists_box M T₀.2 e.isRoot
  choose δs hδs εs hεs ψ hψ0 hsub han hψr huniq using hb
  obtain ⟨δ, hδ, hδle⟩ := exists_delta δs hδs
  obtain ⟨δ', hδ', hsub'⟩ := Metric.isOpen_iff.1 M.isOpen_regular T₀.1 T₀.2
  set δ₁ := min δ δ'
  have hδ₁ : 0 < δ₁ := lt_min hδ hδ'
  have hball : ∀ e, ball T₀.1 δ₁ ⊆ ball T₀.1 (δs e) := fun e =>
    ball_subset_ball ((min_le_left _ _).trans (hδle e))
  refine ⟨δ₁, hδ₁, (ball_subset_ball (min_le_right _ _)).trans hsub', ψ,
    fun e => (han e).mono (hball e), hψ0, fun e t ht => (hψr e t (hball e ht)).1,
    fun t ht htb => ?_⟩
  -- the segment from `T₀` to `t` stays in the ball
  have hseg : ∀ u : unitInterval, segment T₀.1 t u ∈ ball T₀.1 δ₁ := by
    intro u
    rw [segment_apply, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul]
    rw [mem_ball, dist_eq_norm] at htb
    have hu : ‖((u : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [u.2.1], u.2.2⟩
    calc ‖((u : ℝ) : ℂ)‖ * ‖t - T₀.1‖ ≤ 1 * ‖t - T₀.1‖ := by gcongr
      _ < δ₁ := by rw [one_mul]; exact htb
  set σ : Path T₀ ⟨t, ht⟩ :=
    basePath (a := T₀) (b := ⟨t, ht⟩) (segment T₀.1 t) fun u =>
      (ball_subset_ball (min_le_right _ _)).trans hsub' (hseg u)
  rw [orbitPoly_eq c (q₀.trans (Path.Homotopic.Quotient.mk σ))]
  unfold orbitPolyOf
  refine Finset.prod_congr rfl fun h _ => ?_
  congr 2
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [IsCoveringMap.monodromy_trans_apply]
  set e := M.isCoveringMap.monodromy q₀ (h.1 x)
  rw [root_monodromy_of_section ((han e).continuousOn) (fun t ht => (hψr e t ht).1) σ
    (fun u => hball e (hseg u)) e (hψ0 e).symm]

omit M b in
/-- Coefficients of `∏ (X - aᵢ(t))` are analytic where the `aᵢ` are. -/
theorem analyticOnNhd_coeff_prod {ι : Type*} (s : Finset ι) {U : Set ℂ} (a : ι → ℂ → ℂ)
    (ha : ∀ i, AnalyticOnNhd ℂ (a i) U) :
    ∀ k, AnalyticOnNhd ℂ (fun t => (∏ i ∈ s, (X - C (a i t))).coeff k) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro k
    simp only [Finset.prod_empty, coeff_one]
    exact analyticOnNhd_const
  | insert j s hj ih =>
    intro k
    simp_rw [Finset.prod_insert hj, mul_comm (X - C _)]
    cases k with
    | zero =>
      simp_rw [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, mul_neg]
      exact ((ih 0).mul (ha j)).neg
    | succ k =>
      simp_rw [coeff_mul_X_sub_C]
      exact (ih k).sub ((ih (k + 1)).mul (ha j))

/-- **Holomorphicity.** The orbit-polynomial coefficients are analytic at every point reachable
from `b`. -/
theorem orbitCoeff_analyticAt (c : M.Fiber b → ℂ) {T₀ : M.Base}
    (q₀ : Path.Homotopic.Quotient b T₀) (k : ℕ) : AnalyticAt ℂ (orbitCoeff M b c k) T₀.1 := by
  obtain ⟨δ, hδ, hsub, ψ, han, -, -, hloc⟩ := orbitPoly_local c q₀
  set a : Mon M b → ℂ → ℂ := fun h t => ∑ x, c x * ψ (M.isCoveringMap.monodromy q₀ (h.1 x)) t
  have ha : ∀ h, AnalyticOnNhd ℂ (a h) (ball T₀.1 δ) := fun h =>
    Finset.analyticOnNhd_fun_sum _ fun x _ => analyticOnNhd_const.mul (han _)
  have hg := analyticOnNhd_coeff_prod Finset.univ a ha k T₀.1 (mem_ball_self hδ)
  refine hg.congr ?_
  filter_upwards [ball_mem_nhds T₀.1 hδ] with t ht
  have htr := hsub ht
  simp only [orbitCoeff, htr, dite_true, hloc t htr ht, a]

/-! ## Separating weights -/

omit M b in
/-- Finite avoidance: weights separating all permutations of a finite set of distinct numbers. -/
theorem exists_separating_gen {F : Type*} [Fintype F] [DecidableEq F] (root : F → ℂ)
    (hr : Function.Injective root) : ∃ c : F → ℂ,
    Function.Injective fun π : Equiv.Perm F => ∑ x, c x * root (π x) := by
  classical
  set e := Fintype.equivFin F
  let D : Equiv.Perm F → Equiv.Perm F → ℂ[X] := fun π σ =>
    ∑ x, C (root (π x) - root (σ x)) * X ^ (e x : ℕ)
  have hcoeff : ∀ π σ x, (D π σ).coeff (e x : ℕ) = root (π x) - root (σ x) := by
    intro π σ x
    simp only [D, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      rw [if_neg]
      intro h
      exact hy (e.injective (Fin.ext h.symm))
    · simp
  have hD : ∀ π σ, π ≠ σ → D π σ ≠ 0 := by
    intro π σ hne h0
    obtain ⟨x, hx⟩ : ∃ x, π x ≠ σ x := by
      by_contra h; push Not at h; exact hne (Equiv.ext h)
    have hc := hcoeff π σ x
    rw [h0, coeff_zero, eq_comm, sub_eq_zero] at hc
    exact hx (hr hc)
  have heval : ∀ π σ s, (D π σ).eval s =
      ∑ x, s ^ (e x : ℕ) * root (π x) - ∑ x, s ^ (e x : ℕ) * root (σ x) := by
    intro π σ s
    simp only [D, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => by ring
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset
    ((Finset.univ : Finset (Equiv.Perm F × Equiv.Perm F)).biUnion fun p =>
      if p.1 = p.2 then ∅ else (D p.1 p.2).roots.toFinset)
  refine ⟨fun x => s ^ (e x : ℕ), fun π σ h => ?_⟩
  by_contra hne
  apply hs
  rw [Finset.mem_biUnion]
  refine ⟨(π, σ), Finset.mem_univ _, ?_⟩
  rw [if_neg hne, Multiset.mem_toFinset, mem_roots (hD π σ hne), IsRoot.def, heval, sub_eq_zero]
  exact h

/-- Weights whose weighted root sums at `b` separate all permutations of the fibre. -/
theorem exists_separating : ∃ c : M.Fiber b → ℂ,
    Function.Injective fun π : Equiv.Perm (M.Fiber b) => ∑ x, c x * (π x).root := by
  classical
  exact exists_separating_gen (fun x : M.Fiber b => x.root) (root_injective M b)

/-! ## The regular locus: finite complement, path connected -/

variable (M b)

omit b in
theorem not_regular_iff (t : ℂ) :
    t ∉ M.regular ↔ resultant (M.P t) (derivative (M.P t)) = 0 := by
  have hP0 : M.P t ≠ 0 := (M.monic t).ne_zero
  rw [resultant_eq_zero_iff, isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := ℂ) ℂ]
  simp only [MonicFamily.regular, Set.mem_ofPred_eq, aeval_def, eval₂_eq_eval_map,
    Algebra.algebraMap_self, Polynomial.map_id]
  constructor
  · intro h
    push Not at h
    obtain ⟨x, hx, hd⟩ := h
    exact ⟨Or.inl hP0, fun hc => by rcases hc x with h1 | h1 <;> contradiction⟩
  · rintro ⟨-, h⟩ hreg
    exact h fun x => by
      by_cases hx : (M.P t).eval x = 0
      · exact Or.inr (hreg x hx)
      · exact Or.inl hx

omit b in
/-- For polynomial coefficients, the non-regular parameters are finitely many. -/
theorem regular_compl_finite (b : M.Base) (Fpol : ℂ[X][X]) (hF : ∀ t, M.P t = Fpol.map (evalRingHom t)) :
    (M.regular)ᶜ.Finite := by
  set D : ℂ[X] := resultant Fpol (derivative Fpol) M.n (M.n - 1)
  have hD : ∀ t, D.eval t = resultant (M.P t) (derivative (M.P t)) := by
    intro t
    rw [← coe_evalRingHom, ← resultant_map_map, ← derivative_map, ← hF, natDegree_derivative,
      M.natDegree_eq]
  have hD0 : D ≠ 0 := fun h => (not_regular_iff M b.1).2 (by rw [← hD, h, eval_zero]) b.2
  refine (D.roots.toFinset.finite_toSet).subset fun t ht => ?_
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hD0, IsRoot.def, hD]
  exact (not_regular_iff M t).1 ht

omit b in
theorem regular_isPathConnected (b : M.Base) (Fpol : ℂ[X][X]) (hF : ∀ t, M.P t = Fpol.map (evalRingHom t)) :
    IsPathConnected M.regular := by
  rw [← compl_compl M.regular]
  exact Set.Countable.isPathConnected_compl_of_one_lt_rank (s := (M.regular)ᶜ)
    (by rw [Complex.rank_real_complex]; norm_num) (regular_compl_finite M b Fpol hF).countable

theorem exists_path (Fpol : ℂ[X][X]) (hF : ∀ t, M.P t = Fpol.map (evalRingHom t)) (t : M.Base) :
    Nonempty (Path b t) :=
  ((regular_isPathConnected M b Fpol hF).joinedIn b.1 b.2 t.1 t.2).joined_subtype

/-- **Checkpoint.** For polynomial coefficients, every orbit-polynomial coefficient is analytic on
the whole regular locus. -/
theorem orbitCoeff_analyticOnNhd (Fpol : ℂ[X][X]) (hF : ∀ t, M.P t = Fpol.map (evalRingHom t))
    (c : M.Fiber b → ℂ) (k : ℕ) : AnalyticOnNhd ℂ (orbitCoeff M b c k) M.regular := fun t ht =>
  orbitCoeff_analyticAt (M := M) (b := b) c (Path.Homotopic.Quotient.mk (exists_path M b Fpol hF ⟨t, ht⟩).some) k

end Sz8.Galois.Orbit
