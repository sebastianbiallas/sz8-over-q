import Sz8.Galois.OrbitPoly

/-!
# (O): the converse of the analytic bridge

`converse`: for a family with polynomial coefficients, a permutation of the fibre over `b` that
preserves every polynomial relation over `ℂ(t)` among the root germs is a monodromy.

With separating weights `c` and the orbit polynomial `Φ ∈ ℂ[t][Z]` (`OrbitPoly.orbitPhi`):
1. near `b`, `Φ` specializes to `∏_{h ∈ M} (Z - θ_h(t))` with `θ_σ = Σₓ cₓ r_{σ x}` in the analytic
   root branches, hence `Φ = ∏_h (Z - θ_h)` over the analytic germs (`orbitPhi_germ`);
2. `Q(Y) = Φ(Σ cₓ Yₓ)` is a relation among the root germs, since `θ_id` is a root;
3. relation preservation gives `Φ(θ_π) = 0`, so `θ_π = θ_h` for some `h ∈ M` in the germ field;
4. injectivity into the germ field and evaluation at `b` give `Σ cₓ root(π x) = Σ cₓ root(h x)`,
   hence `π = h` by separation.
-/

open Polynomial Topology Filter Metric Set

namespace Sz8.Galois.Converse

open Sz8.Monodromy Sz8.Monodromy.MonicFamily Germs Continuation Orbit OrbitPoly

/-- Pointwise product identities near `b` lift to analytic germs. -/
theorem map_polyGerm_eq_prod {b : ℂ} {ι : Type*} [Fintype ι] (A : ℂ[X][X]) (r : ι → ℂ → ℂ)
    (hr : ∀ i, AnalyticAt ℂ (r i) b)
    (h : ∀ᶠ t in 𝓝 b, A.map (evalRingHom t) = ∏ i, (X - C (r i t))) :
    A.map (polyGerm b) = ∏ i, (X - C (anMk (hr i))) := by
  classical
  set E : ℂ[X] →+* (ℂ → ℂ) := RingHom.pi fun t => evalRingHom t
  set Af : (ℂ → ℂ)[X] := A.map E
  set Bf : (ℂ → ℂ)[X] := ∏ i, (X - C (r i))
  have hAB : Af.map (Germ.coeRingHom (𝓝 b)) = Bf.map (Germ.coeRingHom (𝓝 b)) := by
    ext k
    rw [Polynomial.coeff_map (p := Af), Polynomial.coeff_map (p := Bf)]
    show ((Af.coeff k : ℂ → ℂ) : Germ (𝓝 b) ℂ) = ((Bf.coeff k : ℂ → ℂ) : Germ (𝓝 b) ℂ)
    refine Germ.coe_eq.2 ?_
    filter_upwards [h] with t ht
    have hA : Af.map (Pi.evalRingHom (fun _ => ℂ) t) = A.map (evalRingHom t) := by
      rw [Polynomial.map_map]; rfl
    have hB : Bf.map (Pi.evalRingHom (fun _ => ℂ) t) = ∏ i, (X - C (r i t)) := by
      simp [Bf, Polynomial.map_prod]
    have := congrArg (fun p : ℂ[X] => p.coeff k) (hA.trans (ht.trans hB.symm))
    simpa [coeff_map] using this
  have hsub : (anGerm b).subtype.comp (polyGerm b) = (Germ.coeRingHom (𝓝 b)).comp E := by
    ext p <;> rfl
  apply Polynomial.map_injective (anGerm b).subtype Subtype.val_injective
  rw [Polynomial.map_map, hsub, ← Polynomial.map_map]
  refine hAB.trans ?_
  simp [Bf, Polynomial.map_prod, anMk]

variable {M : MonicFamily} {b : M.Base}

/-- The weighted root branch sum along a permutation. -/
noncomputable def θfun (c : M.Fiber b → ℂ) (σ : M.Fiber b → M.Fiber b) (t : ℂ) : ℂ :=
  ∑ x, c x * rootFun M b (σ x) t

theorem θfun_analyticAt (c : M.Fiber b → ℂ) (σ : M.Fiber b → M.Fiber b) :
    AnalyticAt ℂ (θfun c σ) b.1 := by
  have h : AnalyticAt ℂ (fun t => ∑ x, c x * rootFun M b (σ x) t) b.1 :=
    Finset.analyticAt_fun_sum _ fun x _ => analyticAt_const.mul (rootFun_analyticAt M b _)
  exact h

/-- The weighted germ sum. -/
noncomputable def θA (c : M.Fiber b → ℂ) (σ : M.Fiber b → M.Fiber b) : anGerm b.1 :=
  anMk (θfun_analyticAt c σ)

theorem θA_eq (c : M.Fiber b → ℂ) (σ : M.Fiber b → M.Fiber b) :
    θA c σ = ∑ x, polyGerm b.1 (C (c x)) * rootAn M b (σ x) := by
  apply Subtype.ext
  have hf : θfun c σ = ∑ x, (fun t => (C (c x)).eval t) * rootFun M b (σ x) := by
    funext t; simp [θfun, Finset.sum_apply]
  show Germ.coeRingHom (𝓝 b.1) (θfun c σ) = (anGerm b.1).subtype _
  rw [hf, map_sum, map_sum]
  simp only [map_mul]
  rfl

theorem evalGerm_θA (c : M.Fiber b → ℂ) (σ : M.Fiber b → M.Fiber b) :
    evalGerm b.1 (θA c σ) = ∑ x, c x * (σ x).root := by
  simp [θA, θfun]

variable (Fpol : ℂ[X][X]) (hF : ∀ t, M.P t = Fpol.map (evalRingHom t))

include hF in
/-- **Step 1.** Over the analytic germs at `b`, `Φ = ∏_{h ∈ M} (Z - θ_h)`. -/
theorem orbitPhi_germ (c : M.Fiber b → ℂ) :
    (orbitPhi M b Fpol hF c).map (polyGerm b.1) = ∏ h : Mon M b, (X - C (θA c h.1)) := by
  obtain ⟨δ, hδ, hsub, ψ, han, hψ0, hψr, hloc⟩ :=
    orbitPoly_local (M := M) (b := b) c (Path.Homotopic.Quotient.refl b)
  have heq : ∀ e, ψ e =ᶠ[𝓝 b.1] rootFun M b e := fun e =>
    eventuallyEq_of_root M b.2 ((han e) b.1 (mem_ball_self hδ)).continuousAt
      (rootFun_analyticAt M b e).continuousAt
      (eventually_of_mem (ball_mem_nhds _ hδ) (hψr e)) (rootFun_root M b e)
      (by rw [hψ0, rootFun_base])
  have key := map_polyGerm_eq_prod (b := b.1) (ι := Mon M b) (orbitPhi M b Fpol hF c)
    (fun h => θfun c h.1) (fun h => θfun_analyticAt c h.1)
  refine (key ?_).trans rfl
  filter_upwards [ball_mem_nhds b.1 hδ, eventually_all.2 heq] with t ht hall
  rw [orbitPhi_spec Fpol hF c t (hsub ht), hloc t (hsub ht) ht]
  refine Finset.prod_congr rfl fun h _ => ?_
  congr 2
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [IsCoveringMap.monodromy_refl]
  exact congrArg (c x * ·) (hall (h.1 x))

include hF in
/-- **(O)** -/
theorem converse : Bridge.Converse M b := by
  classical
  intro π hπ
  obtain ⟨c, hc⟩ := exists_separating (M := M) (b := b)
  set Φ := orbitPhi M b Fpol hF c
  set ι : ℂ[X] →+* Mer b.1 := (algebraMap (RatFunc ℂ) (Mer b.1)).comp (algebraMap ℂ[X] (RatFunc ℂ))
  have hι : ι = (algebraMap (anGerm b.1) (Mer b.1)).comp (polyGerm b.1) :=
    RingHom.ext algebraMap_poly
  have hΦ : Φ.map ι = ∏ h : Mon M b, (X - C (algebraMap (anGerm b.1) (Mer b.1) (θA c h.1))) := by
    rw [hι, ← Polynomial.map_map, orbitPhi_germ Fpol hF c, Polynomial.map_prod]
    simp
  set L : MvPolynomial (M.Fiber b) (RatFunc ℂ) :=
    ∑ x, MvPolynomial.C (algebraMap ℂ[X] (RatFunc ℂ) (C (c x))) * MvPolynomial.X x
  set Q : MvPolynomial (M.Fiber b) (RatFunc ℂ) :=
    Φ.eval₂ ((MvPolynomial.C).comp (algebraMap ℂ[X] (RatFunc ℂ))) L
  have hQ : ∀ σ : M.Fiber b → M.Fiber b, MvPolynomial.aeval (rootGerm M b ∘ σ) Q =
      ∏ h : Mon M b, (algebraMap (anGerm b.1) (Mer b.1) (θA c σ) -
        algebraMap (anGerm b.1) (Mer b.1) (θA c h.1)) := by
    intro σ
    set g : MvPolynomial (M.Fiber b) (RatFunc ℂ) →+* Mer b.1 :=
      (MvPolynomial.aeval (rootGerm M b ∘ σ)).toRingHom
    have hg : g.comp ((MvPolynomial.C).comp (algebraMap ℂ[X] (RatFunc ℂ))) = ι :=
      RingHom.ext fun p => by simp [g, ι]
    have hL : g L = algebraMap (anGerm b.1) (Mer b.1) (θA c σ) := by
      rw [θA_eq, map_sum, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [g, L, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, MvPolynomial.aeval_C,
        MvPolynomial.aeval_X, Function.comp_apply, rootGerm]
      rw [algebraMap_poly]
    show g Q = _
    rw [Polynomial.hom_eval₂, hg, hL, eval₂_eq_eval_map, hΦ, eval_prod]
    simp
  have h1 : MvPolynomial.aeval (rootGerm M b) Q = 0 := by
    have := hQ id
    simp only [Function.comp_id] at this
    rw [this]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (sub_self _)
  have h2 := hπ Q h1
  rw [hQ, Finset.prod_eq_zero_iff] at h2
  obtain ⟨h, -, hh⟩ := h2
  rw [sub_eq_zero] at hh
  have hA := IsFractionRing.injective (anGerm b.1) (Mer b.1) hh
  have hroot := congrArg (evalGerm b.1) hA
  rw [evalGerm_θA, evalGerm_θA] at hroot
  have : π = h.1 := hc hroot
  rw [this]
  exact h.2

end Sz8.Galois.Converse
