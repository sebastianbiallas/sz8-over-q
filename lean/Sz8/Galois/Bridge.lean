import Sz8.Galois.Relations
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Sz8.Monodromy.PaperCovering
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The Galois–monodromy bridge, up to the converse (O)

* `mem_image_iff`: the Galois image is the set of permutations preserving every polynomial
  relation among the roots.
* `bridge`: for a family with polynomial coefficients and any fibre labelling `e`, a root
  labelling `βC` in the splitting field over `ℂ(t)` for which the monodromy image lies in the
  Galois image (from (S) and (R)), with equality under `Converse` — the statement (O).
-/

open Polynomial Topology Filter

namespace Sz8.Galois.Bridge

open Sz8.Monodromy Sz8.Monodromy.MonicFamily Germs

section Alg

variable {K : Type*} [Field K] (f : K[X]) {ι : Type*} (ρ : ι ≃ f.rootSet f.SplittingField)

instance splitsSelf : Fact ((f.map (algebraMap K f.SplittingField)).Splits) :=
  ⟨SplittingField.splits f⟩

theorem mem_image_iff (π : Equiv.Perm ι) :
    π ∈ (Gal.galActionHom f f.SplittingField).range.map (Equiv.permCongrHom ρ.symm).toMonoidHom ↔
      ∀ Q : MvPolynomial ι K, MvPolynomial.aeval (fun i => (ρ i : f.SplittingField)) Q = 0 →
        MvPolynomial.aeval (fun i => (ρ (π i) : f.SplittingField)) Q = 0 := by
  have hrestr : ∀ (σ : Gal(f.SplittingField/K)) i,
      (Equiv.permCongrHom ρ.symm).toMonoidHom
        (Gal.galActionHom f f.SplittingField (Gal.restrict f f.SplittingField σ)) i =
        ρ.symm ⟨σ (ρ i), by
          rw [← Gal.galActionHom_restrict f f.SplittingField σ (ρ i)]; exact Subtype.property _⟩ := by
    intro σ i
    simp only [MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe, Equiv.permCongr_apply,
      Equiv.symm_symm]
    congr 1
    exact Subtype.ext (Gal.galActionHom_restrict f f.SplittingField σ (ρ i))
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩ Q hQ
    obtain ⟨σ, rfl⟩ := Gal.restrict_surjective f f.SplittingField g
    have h : (fun i => (ρ ((Equiv.permCongrHom ρ.symm).toMonoidHom
        (Gal.galActionHom f f.SplittingField (Gal.restrict f f.SplittingField σ)) i) :
          f.SplittingField)) = fun i => σ.toAlgHom (ρ i : f.SplittingField) := by
      funext i; rw [hrestr]; simp
    rw [h, ← MvPolynomial.comp_aeval_apply, hQ, map_zero]
  · intro hπ
    set φ := MvPolynomial.aeval (R := K) (fun i => (ρ i : f.SplittingField))
    set φπ := MvPolynomial.aeval (R := K) (fun i => (ρ (π i) : f.SplittingField))
    have hsurj : Function.Surjective φ := by
      rw [← AlgHom.range_eq_top, MvPolynomial.aeval_range, ← SplittingField.adjoin_rootSet f]
      congr 1
      ext x
      exact ⟨fun ⟨i, hi⟩ => hi ▸ (ρ i).2, fun hx => ⟨ρ.symm ⟨x, hx⟩, by simp⟩⟩
    let τ : f.SplittingField →ₐ[K] f.SplittingField :=
      (Ideal.Quotient.liftₐ (RingHom.ker φ) φπ fun a ha => hπ a ha).comp
        (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
    have hτ : ∀ i, τ (ρ i) = ρ (π i) := by
      intro i
      have : (ρ i : f.SplittingField) = φ (MvPolynomial.X i) := by simp [φ]
      have hX : (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (φ (MvPolynomial.X i)) =
          Ideal.Quotient.mk _ (MvPolynomial.X i) :=
        (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm_apply_eq.2 rfl
      rw [this]
      show Ideal.Quotient.liftₐ (RingHom.ker φ) φπ (fun a ha => hπ a ha)
        ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (φ (MvPolynomial.X i))) = _
      rw [hX, Ideal.Quotient.liftₐ_apply]
      exact (Ideal.Quotient.lift_mk _ _ _).trans (by simp [φπ])
    let σ := AlgEquiv.ofBijective τ (Algebra.IsAlgebraic.algHom_bijective τ)
    refine ⟨_, ⟨Gal.restrict f f.SplittingField σ, rfl⟩, Equiv.ext fun i => ?_⟩
    rw [hrestr]
    simp only [Equiv.symm_apply_eq]
    exact Subtype.ext (hτ i)

end Alg

/-- **(O)**, the converse: a permutation of the fibre preserving every relation among the root
germs is a monodromy. -/
def Converse (M : MonicFamily) (b : M.Base) : Prop :=
  ∀ π : Equiv.Perm (M.Fiber b), (∀ Q : MvPolynomial (M.Fiber b) (RatFunc ℂ),
      MvPolynomial.aeval (rootGerm M b) Q = 0 → MvPolynomial.aeval (rootGerm M b ∘ π) Q = 0) →
    π ∈ (M.isCoveringMap.monodromyPerm b).range

variable (M : MonicFamily) (b : M.Base) (Fpol : ℂ[X][X]) (hF : ∀ t, M.P t = Fpol.map (evalRingHom t))

local notation "fC" => Fpol.map (algebraMap ℂ[X] (RatFunc ℂ))

include hF in
/-- **The bridge.** -/
theorem bridge {ι : Type*} (e : M.Fiber b ≃ ι) :
    ∃ βC : (fC).rootSet (fC).SplittingField ≃ ι,
      (M.isCoveringMap.monodromyPerm b).range.map (Equiv.permCongrHom e).toMonoidHom ≤
        (Gal.galActionHom (fC) (fC).SplittingField).range.map (Equiv.permCongrHom βC).toMonoidHom ∧
      (Converse M b →
        (Gal.galActionHom (fC) (fC).SplittingField).range.map (Equiv.permCongrHom βC).toMonoidHom =
          (M.isCoveringMap.monodromyPerm b).range.map (Equiv.permCongrHom e).toMonoidHom) ∧
      ∃ ιM : (fC).SplittingField →ₐ[RatFunc ℂ] Mer b.1,
        ∀ i, ιM (βC.symm i : (fC).SplittingField) = rootGerm M b (e.symm i) := by
  classical
  have hprod := splits_rootGerm M b Fpol hF
  have hinj := rootGerm_injective M b
  have hmon : (∏ x, (X - C (rootGerm M b x))).Monic :=
    monic_prod_of_monic _ _ fun x _ => monic_X_sub_C _
  have hsplit : ((fC).map (algebraMap (RatFunc ℂ) (Mer b.1))).Splits := by
    rw [hprod]; exact Splits.prod fun x _ => Splits.X_sub_C _
  set ιE := SplittingField.lift (fC) hsplit with hιE
  have hιinj : Function.Injective ιE := ιE.toRingHom.injective
  have hne : (fC).map (algebraMap (RatFunc ℂ) (Mer b.1)) ≠ 0 := by rw [hprod]; exact hmon.ne_zero
  have hne' : (fC).map (algebraMap (RatFunc ℂ) (fC).SplittingField) ≠ 0 := by
    intro h
    apply hne
    rw [← ιE.comp_algebraMap, ← Polynomial.map_map, h, Polynomial.map_zero]
  have hroots : ((fC).map (algebraMap (RatFunc ℂ) (Mer b.1))).roots =
      ((fC).map (algebraMap (RatFunc ℂ) (fC).SplittingField)).roots.map ιE := by
    have key := (SplittingField.splits (fC)).roots_map (ιE : (fC).SplittingField →+* Mer b.1)
    rwa [Polynomial.map_map, AlgHom.comp_algebraMap] at key
  have hmemMer : ∀ y : Mer b.1, y ∈ ((fC).map (algebraMap (RatFunc ℂ) (Mer b.1))).roots ↔
      ∃ x, y = rootGerm M b x := by
    intro y
    rw [mem_roots hne, IsRoot.def, hprod, eval_prod, Finset.prod_eq_zero_iff]
    simp [sub_eq_zero]
  have hmemSF : ∀ r : (fC).SplittingField, r ∈ (fC).rootSet (fC).SplittingField ↔
      r ∈ ((fC).map (algebraMap (RatFunc ℂ) (fC).SplittingField)).roots := by
    intro r
    rw [mem_rootSet', mem_roots hne', IsRoot.def, eval_map_algebraMap]
    simp [hne']
  -- the root labelling
  have hex : ∀ x : M.Fiber b, ∃ r : (fC).rootSet (fC).SplittingField, ιE r = rootGerm M b x := by
    intro x
    have h := (hmemMer _).2 ⟨x, rfl⟩
    rw [hroots, Multiset.mem_map] at h
    obtain ⟨r, hr, hr'⟩ := h
    exact ⟨⟨r, (hmemSF r).2 hr⟩, hr'⟩
  choose g hg using hex
  have hgbij : Function.Bijective g := by
    refine ⟨fun x y h => hinj (by rw [← hg, ← hg, h]), fun r => ?_⟩
    have h := Multiset.mem_map_of_mem ιE ((hmemSF r).1 r.2)
    rw [← hroots, hmemMer] at h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, Subtype.ext (hιinj (by rw [hg, hx]))⟩
  set ρ := Equiv.ofBijective g hgbij with hρ
  have htr : ∀ (π : M.Fiber b → M.Fiber b) (Q : MvPolynomial (M.Fiber b) (RatFunc ℂ)),
      MvPolynomial.aeval (fun x => (ρ (π x) : (fC).SplittingField)) Q = 0 ↔
        MvPolynomial.aeval (rootGerm M b ∘ π) Q = 0 := by
    intro π Q
    rw [← map_eq_zero_iff ιE hιinj, MvPolynomial.comp_aeval_apply]
    have hfun : (fun x => ιE (ρ (π x) : (fC).SplittingField)) = rootGerm M b ∘ π := by
      funext x; simp [hρ, hg]
    rw [hfun]
  have hle : (M.isCoveringMap.monodromyPerm b).range ≤
      (Gal.galActionHom (fC) (fC).SplittingField).range.map (Equiv.permCongrHom ρ.symm).toMonoidHom := by
    rintro _ ⟨γ, rfl⟩
    rw [mem_image_iff (fC) ρ]
    intro Q hQ
    exact (htr _ Q).2 (Relations.relations_monodromy M b γ Q ((htr id Q).1 hQ))
  have hcomp : (Equiv.permCongrHom (ρ.symm.trans e)).toMonoidHom =
      (Equiv.permCongrHom e).toMonoidHom.comp (Equiv.permCongrHom ρ.symm).toMonoidHom := by
    ext σ i; simp [Equiv.permCongr_apply]
  refine ⟨ρ.symm.trans e, ?_, fun hO => ?_, ιE, fun i => ?_⟩
  · rw [hcomp, ← Subgroup.map_map]
    exact Subgroup.map_mono hle
  · have hsub : (Gal.galActionHom (fC) (fC).SplittingField).range.map
        (Equiv.permCongrHom ρ.symm).toMonoidHom = (M.isCoveringMap.monodromyPerm b).range := by
      refine le_antisymm (fun π hπ => ?_) hle
      rw [mem_image_iff (fC) ρ π] at hπ
      exact hO π fun Q hQ => (htr π Q).1 (hπ Q ((htr id Q).2 hQ))
    rw [hcomp, ← Subgroup.map_map, hsub]
  · simp [hρ, hg]

/-! ## Polynomial coefficients for sparse term lists -/

/-- Polynomial coefficients from a term list `(X-degree, t-degree, coefficient)`. -/
noncomputable def Fterms (ts : List (ℕ × ℕ × ℚ)) : ℂ[X][X] :=
  ts.foldr (fun a acc => C (C (a.2.2 : ℂ) * X ^ a.2.1) * X ^ a.1 + acc) 0

theorem sparse_eq_Fterms (ts : List (ℕ × ℕ × ℚ)) (t : ℂ) :
    sparseFamily ts t = (Fterms ts).map (evalRingHom t) := by
  induction ts with
  | nil => simp [sparseFamily, Fterms]
  | cons a l ih =>
    rw [sparseFamily_cons, ih]
    simp [Fterms]

set_option maxRecDepth 100000 in
theorem paper_hF : ∀ t, paperMonicFamily.P t = (Fterms famTerms).map (evalRingHom t) := by
  intro t
  have h : paperMonicFamily.P t = paperFamily t := rfl
  rw [h, paperFamily_eq_famTerms, sparse_eq_Fterms]

theorem foldr_eq_Fterms (ts : List (ℕ × ℕ × ℚ)) :
    ts.foldr (fun a acc => C (algebraMap ℚ (RatFunc ℂ) a.2.2 * RatFunc.X ^ a.2.1) * X ^ a.1 + acc) 0
      = (Fterms ts).map (algebraMap ℂ[X] (RatFunc ℂ)) := by
  have hc : ∀ c : ℚ, algebraMap ℚ (RatFunc ℂ) c = algebraMap ℂ (RatFunc ℂ) (c : ℂ) := fun c =>
    congrArg (· c) (RingHom.ext_rat (algebraMap ℚ (RatFunc ℂ))
      ((algebraMap ℂ (RatFunc ℂ)).comp (algebraMap ℚ ℂ)))
  induction ts with
  | nil => simp [Fterms]
  | cons a l ih =>
    rw [List.foldr_cons, ih]
    simp [Fterms, hc, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

end Sz8.Galois.Bridge
