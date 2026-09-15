import Sz8.Galois.RootAnalytic
import Sz8.Galois.NodeLocal
import Mathlib.Topology.Germ
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The germ field and the root germs

* `anGerm b`: analytic germs at `b`, a domain (isolated zeros); `evalGerm` evaluates at `b`.
* `Mer b`: its fraction field, a `ℂ(t)`-algebra (a nonzero polynomial has a nonzero germ).
* `rootGerm x`: the germ of the analytic root branch through a fibre point `x` over a regular `b`.
* `splits_rootGerm` **(S)**: for a family with polynomial coefficients, `f` factors over `Mer b`
  as `∏ₓ (X - rootGerm x)`, and `rootGerm` is injective.
-/

open Polynomial Topology Filter Metric Set
open scoped nonZeroDivisors

namespace Sz8.Galois.Germs

open Sz8.Monodromy Sz8.Monodromy.MonicFamily

/-! ## Analytic germs -/

/-- Analytic germs at `b`. -/
def anGerm (b : ℂ) : Subring (Germ (𝓝 b) ℂ) where
  carrier := {g | ∃ f : ℂ → ℂ, AnalyticAt ℂ f b ∧ (f : Germ (𝓝 b) ℂ) = g}
  mul_mem' := by rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩; exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩; exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  neg_mem' := by rintro _ ⟨f, hf, rfl⟩; exact ⟨-f, hf.neg, rfl⟩

variable {b : ℂ}

/-- An analytic function as an analytic germ. -/
noncomputable def anMk {f : ℂ → ℂ} (hf : AnalyticAt ℂ f b) : anGerm b := ⟨(f : Germ (𝓝 b) ℂ), f, hf, rfl⟩

theorem anMk_eq_iff {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f b) (hg : AnalyticAt ℂ g b) :
    anMk hf = anMk hg ↔ f =ᶠ[𝓝 b] g := by
  rw [anMk, anMk, ← Subtype.val_inj]
  exact Germ.coe_eq

variable (b) in
/-- Evaluation at the base point. -/
noncomputable def evalGerm : anGerm b →+* ℂ := Germ.valueRingHom.comp (anGerm b).subtype

@[simp] theorem evalGerm_anMk {f : ℂ → ℂ} (hf : AnalyticAt ℂ f b) : evalGerm b (anMk hf) = f b :=
  rfl

theorem exists_anMk (g : anGerm b) : ∃ (f : ℂ → ℂ) (hf : AnalyticAt ℂ f b), g = anMk hf := by
  obtain ⟨g, f, hf, rfl⟩ := g
  exact ⟨f, hf, rfl⟩

instance : NoZeroDivisors (anGerm b) := by
  refine ⟨fun {x y} h => ?_⟩
  obtain ⟨f, hf, rfl⟩ := exists_anMk x
  obtain ⟨g, hg, rfl⟩ := exists_anMk y
  have h0 : anMk (hf.mul hg) = anMk (analyticAt_const (v := (0 : ℂ))) := h
  rw [anMk_eq_iff] at h0
  have z0 : ∀ {u : ℂ → ℂ} (hu : AnalyticAt ℂ u b), u =ᶠ[𝓝 b] (fun _ => 0) →
      anMk hu = 0 := fun hu h => (anMk_eq_iff hu analyticAt_const).2 h
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with hf0 | hfne
  · exact Or.inl (z0 hf hf0)
  · right
    rcases hg.eventually_eq_zero_or_eventually_ne_zero with hg0 | hgne
    · exact z0 hg hg0
    · exfalso
      have : ∀ᶠ z in 𝓝[≠] b, False := by
        filter_upwards [hfne, hgne, nhdsWithin_le_nhds h0] with z h1 h2 h3
        exact mul_ne_zero h1 h2 h3
      exact this.exists.elim fun _ h => h

instance : IsDomain (anGerm b) := NoZeroDivisors.to_isDomain _

/-- Meromorphic germs at `b`. -/
abbrev Mer (b : ℂ) := FractionRing (anGerm b)

variable (b) in
/-- Polynomials as analytic germs. -/
noncomputable def polyGerm : ℂ[X] →+* anGerm b where
  toFun p := anMk (p.differentiable.analyticAt b)
  map_one' := by ext; simp [anMk]; rfl
  map_mul' p q := by ext; simp [anMk]; rfl
  map_zero' := by ext; simp [anMk]; rfl
  map_add' p q := by ext; simp [anMk]; rfl

theorem polyGerm_injective : Function.Injective (polyGerm b) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have h : (fun t => p.eval t) =ᶠ[𝓝 b] 0 :=
    (anMk_eq_iff (p.differentiable.analyticAt b) analyticAt_const).1 hp
  have hon : Set.EqOn (fun t => p.eval t) 0 Set.univ :=
    (p.differentiable.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ b) h
  exact Polynomial.funext fun z => by simpa using hon (Set.mem_univ z)

variable (b) in
theorem polyGerm_le :
    ℂ[X]⁰ ≤ (Mer b)⁰.comap ((algebraMap (anGerm b) (Mer b)).comp (polyGerm b)) := by
  intro p hp
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [RingHom.comp_apply, Ne, IsFractionRing.to_map_eq_zero_iff, map_eq_zero_iff _ polyGerm_injective]
  exact nonZeroDivisors.ne_zero hp

noncomputable instance (b : ℂ) : Algebra (RatFunc ℂ) (Mer b) :=
  (RatFunc.liftRingHom _ (polyGerm_le b)).toAlgebra

theorem algebraMap_poly (p : ℂ[X]) :
    algebraMap (RatFunc ℂ) (Mer b) (algebraMap ℂ[X] (RatFunc ℂ) p) =
      algebraMap (anGerm b) (Mer b) (polyGerm b p) :=
  RatFunc.liftRingHom_algebraMap _ _ p

/-! ## Root germs -/

section Roots

variable (M : MonicFamily) (b : M.Base)

theorem root_injective : Function.Injective fun x : M.Fiber b => x.root := by
  intro x y h
  refine Subtype.ext (Subtype.ext (Subtype.ext (Prod.ext ?_ h)))
  exact x.param.trans y.param.symm

instance : Finite (M.Fiber b) := by
  have : Finite ((M.P b.1).rootSet ℂ) := (M.P b.1).rootSet_finite ℂ |>.to_subtype
  refine Finite.of_injective (fun x : M.Fiber b => (⟨x.root, ?_⟩ : (M.P b.1).rootSet ℂ)) ?_
  · rw [mem_rootSet]; exact ⟨(M.monic _).ne_zero, by simpa using x.isRoot⟩
  · intro x y h; exact root_injective M b (congrArg Subtype.val h)

noncomputable instance : Fintype (M.Fiber b) := Fintype.ofFinite _

/-- A regular fibre has `n` points. -/
theorem card_fiber : Fintype.card (M.Fiber b) = M.n := by
  classical
  have hp0 : M.P b.1 ≠ 0 := (M.monic _).ne_zero
  have hnodup : (M.P b.1).roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro r
    rw [count_roots]
    by_contra h
    have h1 := (one_lt_rootMultiplicity_iff_isRoot hp0).1 (lt_of_not_ge h)
    exact b.2 r h1.1 h1.2
  have himg : (Finset.univ.image fun x : M.Fiber b => x.root) = (M.P b.1).roots.toFinset := by
    ext r
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      mem_roots hp0, IsRoot.def]
    exact ⟨fun ⟨x, hx⟩ => hx ▸ x.isRoot, fun hr => ⟨M.mkFiber b r hr, rfl⟩⟩
  rw [← Finset.card_univ, ← Finset.card_image_of_injective _ (root_injective M b), himg,
    Multiset.toFinset_card_of_nodup hnodup, IsAlgClosed.card_roots_eq_natDegree, M.natDegree_eq]

theorem exists_root_branch (x : M.Fiber b) : ∃ r : ℂ → ℂ, AnalyticAt ℂ r b.1 ∧ r b.1 = x.root ∧
    ∀ᶠ t in 𝓝 b.1, (M.P t).eval (r t) = 0 := by
  obtain ⟨δ, hδ, ψ, hψ0, hψc, hψr⟩ := NodeLocal.exists_branch M x.isRoot (b.2 _ x.isRoot)
  have hU : IsOpen (ball b.1 δ ∩ M.regular) := isOpen_ball.inter M.isOpen_regular
  have han := RootAnalytic.analyticOnNhd_of_root M hU (hψc.mono inter_subset_left)
    (fun t ht => hψr t ht.1) (fun t ht => ht.2 _ (hψr t ht.1))
  exact ⟨ψ, han b.1 ⟨mem_ball_self hδ, b.2⟩, hψ0, eventually_of_mem (ball_mem_nhds _ hδ) hψr⟩

/-- The analytic root branch through `x`. -/
noncomputable def rootFun (x : M.Fiber b) : ℂ → ℂ := (exists_root_branch M b x).choose

theorem rootFun_analyticAt (x : M.Fiber b) : AnalyticAt ℂ (rootFun M b x) b.1 :=
  (exists_root_branch M b x).choose_spec.1

@[simp] theorem rootFun_base (x : M.Fiber b) : rootFun M b x b.1 = x.root :=
  (exists_root_branch M b x).choose_spec.2.1

theorem rootFun_root (x : M.Fiber b) : ∀ᶠ t in 𝓝 b.1, (M.P t).eval (rootFun M b x t) = 0 :=
  (exists_root_branch M b x).choose_spec.2.2

/-- The root branch as an analytic germ. -/
noncomputable def rootAn (x : M.Fiber b) : anGerm b.1 := anMk (rootFun_analyticAt M b x)

/-- The root branch as a meromorphic germ. -/
noncomputable def rootGerm (x : M.Fiber b) : Mer b.1 := algebraMap (anGerm b.1) (Mer b.1) (rootAn M b x)

@[simp] theorem evalGerm_rootAn (x : M.Fiber b) : evalGerm b.1 (rootAn M b x) = x.root := by
  simp [rootAn]

theorem rootGerm_injective : Function.Injective (rootGerm M b) := by
  intro x y h
  have h1 := IsFractionRing.injective (anGerm b.1) (Mer b.1) h
  apply root_injective M b
  simpa using congrArg (evalGerm b.1) h1

/-- Near `b` the branches are pairwise distinct. -/
theorem eventually_rootFun_injective :
    ∀ᶠ t in 𝓝 b.1, Function.Injective fun x => rootFun M b x t := by
  have h : ∀ x y : M.Fiber b, ∀ᶠ t in 𝓝 b.1, x ≠ y → rootFun M b x t ≠ rootFun M b y t := by
    intro x y
    by_cases hxy : x = y
    · exact Eventually.of_forall fun _ h => absurd hxy h
    · have hne : rootFun M b x b.1 - rootFun M b y b.1 ≠ 0 := by
        rw [rootFun_base, rootFun_base, sub_ne_zero]
        exact fun h => hxy (root_injective M b h)
      have hc := ((rootFun_analyticAt M b x).sub (rootFun_analyticAt M b y)).continuousAt
      filter_upwards [hc.eventually_ne hne] with t ht _
      exact sub_ne_zero.1 ht
  have h2 : ∀ᶠ t in 𝓝 b.1, ∀ x y : M.Fiber b, x ≠ y → rootFun M b x t ≠ rootFun M b y t := by
    simpa only [eventually_all] using h
  filter_upwards [h2] with t ht x y hxy
  by_contra hne
  exact ht x y hne hxy

/-- A monic polynomial with as many distinct roots as its degree is their product. -/
theorem eq_prod_of_roots {ι : Type*} [Fintype ι] {p : ℂ[X]} (hm : p.Monic)
    (hdeg : p.natDegree = Fintype.card ι) (r : ι → ℂ) (hr : ∀ i, p.eval (r i) = 0)
    (hinj : Function.Injective r) : p = ∏ i, (X - C (r i)) := by
  classical
  set s : Multiset ℂ := Finset.univ.val.map r
  have hnd : s.Nodup := Finset.univ.nodup.map hinj
  have hle : s ≤ p.roots := (Multiset.le_iff_subset hnd).2 fun z hz => by
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact (mem_roots hm.ne_zero).2 (hr i)
  have hprod : (s.map fun a => X - C a).prod = ∏ i, (X - C (r i)) := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]; rfl
  have hdvd := (Multiset.prod_X_sub_C_dvd_iff_le_roots hm.ne_zero s).2 hle
  rw [hprod] at hdvd
  have hmon : (∏ i, (X - C (r i))).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  refine eq_of_monic_of_dvd_of_natDegree_le hmon hm hdvd ?_
  rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
  simp [hdeg]

/-- **(S)** -/
theorem splits_rootGerm (Fpol : ℂ[X][X]) (hF : ∀ t, M.P t = Fpol.map (evalRingHom t)) :
    (Fpol.map (algebraMap ℂ[X] (RatFunc ℂ))).map (algebraMap (RatFunc ℂ) (Mer b.1)) =
      ∏ x, (X - C (rootGerm M b x)) := by
  classical
  -- pointwise factorization near `b`
  have hkey : ∀ᶠ t in 𝓝 b.1, M.P t = ∏ x, (X - C (rootFun M b x t)) := by
    have hroots : ∀ᶠ t in 𝓝 b.1, ∀ x, (M.P t).eval (rootFun M b x t) = 0 :=
      eventually_all.2 fun x => rootFun_root M b x
    filter_upwards [hroots, eventually_rootFun_injective M b] with t h1 h2
    exact eq_prod_of_roots (M.monic t) (by rw [M.natDegree_eq, card_fiber]) _ h1 h2
  -- the polynomial of functions
  set E : ℂ[X] →+* (ℂ → ℂ) := RingHom.pi fun t => evalRingHom t
  set A : (ℂ → ℂ)[X] := Fpol.map E
  set B : (ℂ → ℂ)[X] := ∏ x, (X - C (rootFun M b x))
  have hAB : A.map (Germ.coeRingHom (𝓝 b.1)) = B.map (Germ.coeRingHom (𝓝 b.1)) := by
    ext k
    rw [Polynomial.coeff_map (p := A), Polynomial.coeff_map (p := B)]
    show ((A.coeff k : ℂ → ℂ) : Germ (𝓝 b.1) ℂ) = ((B.coeff k : ℂ → ℂ) : Germ (𝓝 b.1) ℂ)
    refine Germ.coe_eq.2 ?_
    filter_upwards [hkey] with t ht
    have hA : A.map (Pi.evalRingHom (fun _ => ℂ) t) = M.P t := by
      rw [hF, Polynomial.map_map]; rfl
    have hB : B.map (Pi.evalRingHom (fun _ => ℂ) t) = ∏ x, (X - C (rootFun M b x t)) := by
      simp [B, Polynomial.map_prod]
    have := congrArg (fun p : ℂ[X] => p.coeff k) (hA.trans (ht.trans hB.symm))
    simpa [coeff_map] using this
  -- back to analytic germs
  have hsub : (anGerm b.1).subtype.comp (polyGerm b.1) = (Germ.coeRingHom (𝓝 b.1)).comp E := by
    ext p <;> rfl
  have hA' : Fpol.map (polyGerm b.1) = ∏ x, (X - C (rootAn M b x)) := by
    apply Polynomial.map_injective (anGerm b.1).subtype Subtype.val_injective
    rw [Polynomial.map_map, hsub, ← Polynomial.map_map]
    refine hAB.trans ?_
    simp [B, Polynomial.map_prod, rootAn, anMk]
  have hcomp : (algebraMap (RatFunc ℂ) (Mer b.1)).comp (algebraMap ℂ[X] (RatFunc ℂ)) =
      (algebraMap (anGerm b.1) (Mer b.1)).comp (polyGerm b.1) := RingHom.ext algebraMap_poly
  rw [Polynomial.map_map, hcomp, ← Polynomial.map_map, hA', Polynomial.map_prod]
  simp [rootGerm]

end Roots

end Sz8.Galois.Germs
