import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Geometric Galois group inside the arithmetic one

`F → F' → E`, `p ∈ F[X]`, `E` a Galois extension of `F'` in which `p` splits. The only
non-formal hypothesis is **relative normality** `hrel`: every element of `F'` algebraic over `F`
has its `F`-minimal polynomial split over `F'`. Under it, restriction identifies `Gal(E/F')`
with a normal subgroup of `Gal(p/F)`, compatibly with the action on the roots of `p` in `E`.
No linear disjointness and no intermediate field of constants is used.
-/

open Polynomial IntermediateField

namespace Sz8.Galois.GaloisDescent

variable {F F' E : Type*} [Field F] [Field F'] [Field E] [Algebra F F'] [Algebra F' E]
  [Algebra F E] [IsScalarTower F F' E] (p : F[X]) [Fact ((p.map (algebraMap F E)).Splits)]

/-- Restriction `Gal(E/F') → Gal(p/F)`. -/
noncomputable def res : Gal(E/F') →* Gal(p.SplittingField/F) :=
  (AlgEquiv.restrictNormalHom p.SplittingField).comp
    { toFun := fun σ => σ.restrictScalars F
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem galActionHom_res (σ : Gal(E/F')) (x : p.rootSet E) :
    (Gal.galActionHom p E (res p σ) x : E) = σ x :=
  Gal.galActionHom_restrict p E _ x

/-- Membership in the fixed field of the image of restriction. -/
theorem mem_fixedField_res_iff [FiniteDimensional F' E] [IsGalois F' E] (x : p.SplittingField) :
    x ∈ fixedField (res (F' := F') (E := E) p).range ↔
      algebraMap p.SplittingField E x ∈ Set.range (algebraMap F' E) := by
  have hc : ∀ σ : Gal(E/F'), algebraMap p.SplittingField E (res p σ x) =
      σ (algebraMap p.SplittingField E x) := fun σ =>
    AlgEquiv.restrictNormal_commutes (σ.restrictScalars F) p.SplittingField x
  rw [mem_fixedField_iff]
  constructor
  · intro h
    rw [← IntermediateField.mem_bot, IsGalois.mem_bot_iff_fixed]
    intro σ
    rw [← hc, h _ ⟨σ, rfl⟩]
  · rintro ⟨z, hz⟩ _ ⟨σ, rfl⟩
    apply (algebraMap p.SplittingField E).injective
    rw [hc, ← hz, AlgEquiv.commutes]

/-- **Relative normality gives stability of the fixed field.** -/
theorem fixedField_res_stable [FiniteDimensional F' E] [IsGalois F' E]
    (hrel : ∀ z : F', IsAlgebraic F z → ((minpoly F z).map (algebraMap F F')).Splits)
    (τ : Gal(p.SplittingField/F)) {x : p.SplittingField} (hx : x ∈ fixedField (res (F' := F') (E := E) p).range) :
    τ x ∈ fixedField (res (F' := F') (E := E) p).range := by
  rw [mem_fixedField_res_iff] at hx ⊢
  obtain ⟨z, hz⟩ := hx
  have hxalg : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hmin : minpoly F z = minpoly F x := by
    rw [← minpoly.algebraMap_eq (algebraMap F' E).injective z, hz,
      minpoly.algebraMap_eq (algebraMap p.SplittingField E).injective x]
  have hzalg : IsAlgebraic F z := by
    refine ⟨minpoly F z, ?_, minpoly.aeval F z⟩
    rw [hmin]; exact minpoly.ne_zero hxalg
  have hs := hrel z hzalg
  -- `τ x` is a root of the minimal polynomial of `x`
  have hroot : aeval (algebraMap p.SplittingField E (τ x)) (minpoly F z) = 0 := by
    rw [hmin, aeval_algebraMap_apply, aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero,
      map_zero]
  have hne : (minpoly F z).map (algebraMap F E) ≠ 0 :=
    Polynomial.map_ne_zero (hmin ▸ minpoly.ne_zero hxalg)
  have hmem : algebraMap p.SplittingField E (τ x) ∈ ((minpoly F z).map (algebraMap F E)).roots := by
    rw [mem_roots hne, IsRoot, eval_map_algebraMap]; exact hroot
  rw [IsScalarTower.algebraMap_eq F F' E, ← Polynomial.map_map, hs.roots_map] at hmem
  obtain ⟨w, -, hw⟩ := Multiset.mem_map.1 hmem
  exact ⟨w, hw⟩

/-- The image of restriction is normal. -/
theorem res_range_normal [FiniteDimensional F' E] [IsGalois F' E]
    (hrel : ∀ z : F', IsAlgebraic F z → ((minpoly F z).map (algebraMap F F')).Splits) :
    (res (F' := F') (E := E) p).range.Normal := by
  have hfin : FiniteDimensional F p.SplittingField := inferInstance
  constructor
  intro h hh τ
  rw [← IntermediateField.fixingSubgroup_fixedField (res (F' := F') (E := E) p).range] at hh ⊢
  rw [IntermediateField.mem_fixingSubgroup_iff] at hh ⊢
  intro x hx
  have h1 := hh _ (fixedField_res_stable p hrel τ⁻¹ hx)
  simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv] at h1 ⊢
  show τ (h (τ⁻¹ x)) = x
  rw [show h (τ⁻¹ x) = τ⁻¹ x from h1]
  exact AlgEquiv.apply_symm_apply τ x

omit [Algebra F' E] [IsScalarTower F F' E] in
/-- Changing the field in which the roots are read conjugates the permutation action. -/
theorem galActionHom_conj (E₁ E₂ : Type*) [Field E₁] [Algebra F E₁] [Field E₂] [Algebra F E₂]
    [Fact ((p.map (algebraMap F E₁)).Splits)] [Fact ((p.map (algebraMap F E₂)).Splits)]
    (ψ : p.Gal) :
    Gal.galActionHom p E₂ ψ = Equiv.permCongr
      ((Gal.rootsEquivRoots p E₁).symm.trans (Gal.rootsEquivRoots p E₂)) (Gal.galActionHom p E₁ ψ) := by
  ext x
  simp [Gal.galActionHom, MulAction.toPermHom, Gal.smul_def, Equiv.permCongr_apply]

end Sz8.Galois.GaloisDescent

namespace Sz8.Galois.GaloisDescent

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F'] (p : F[X]) (q : F'[X])

/-- **Geometric inside arithmetic, with labels.** For `q = p` read over `F'`, and any labelling
`βC` of the roots of `q` in its splitting field `E`, some labelling `β` of the roots of `p` in its
own splitting field makes the geometric image a normal subgroup of the arithmetic image. -/
theorem geometric_normal_in_arithmetic_of_rel {ι : Type*} [CharZero F']
    (hq : p.map (algebraMap F F') = q)
    [Fact ((q.map (algebraMap F' q.SplittingField)).Splits)]
    [Fact ((p.map (algebraMap F p.SplittingField)).Splits)]
    [Fact ((p.map (algebraMap F q.SplittingField)).Splits)]
    (hrel : ∀ z : F', IsAlgebraic F z → ((minpoly F z).map (algebraMap F F')).Splits)
    (βC : q.rootSet q.SplittingField ≃ ι) :
    ∃ β : p.rootSet p.SplittingField ≃ ι,
      (((Gal.galActionHom q q.SplittingField).range.map (Equiv.permCongrHom βC).toMonoidHom ≤
        (Gal.galActionHom p p.SplittingField).range.map (Equiv.permCongrHom β).toMonoidHom) ∧
      ∀ a ∈ (Gal.galActionHom p p.SplittingField).range.map (Equiv.permCongrHom β).toMonoidHom,
        ∀ g ∈ (Gal.galActionHom q q.SplittingField).range.map (Equiv.permCongrHom βC).toMonoidHom,
          a * g * a⁻¹ ∈
            (Gal.galActionHom q q.SplittingField).range.map (Equiv.permCongrHom βC).toMonoidHom) ∧
      ∃ j : p.SplittingField →ₐ[F] q.SplittingField,
        ∀ i, j (β.symm i : p.SplittingField) = (βC.symm i : q.SplittingField) := by
  have hR : q.rootSet q.SplittingField = p.rootSet q.SplittingField := by
    classical
    subst hq
    simp only [rootSet_def, aroots_map]
  set s : p.rootSet q.SplittingField ≃ q.rootSet q.SplittingField := Equiv.setCongr hR.symm with hs
  set γ : p.rootSet q.SplittingField ≃ ι := s.trans βC with hγ
  set r : p.rootSet p.SplittingField ≃ p.rootSet q.SplittingField :=
    (Gal.rootsEquivRoots p p.SplittingField).symm.trans (Gal.rootsEquivRoots p q.SplittingField)
    with hr
  -- arithmetic elements, read in `E`
  have harith : ∀ ψ : p.Gal, (Equiv.permCongrHom (r.trans γ)).toMonoidHom
      (Gal.galActionHom p p.SplittingField ψ) =
        (Equiv.permCongrHom γ).toMonoidHom (Gal.galActionHom p q.SplittingField ψ) := by
    intro ψ
    rw [galActionHom_conj p p.SplittingField q.SplittingField ψ]
    ext i
    simp [Equiv.permCongr_apply, hr]
  -- geometric elements, as restrictions
  have hgeo : ∀ ϕ : Gal(q.SplittingField/F'), (Equiv.permCongrHom βC).toMonoidHom
      (Gal.galActionHom q q.SplittingField (Gal.restrict q q.SplittingField ϕ)) =
        (Equiv.permCongrHom γ).toMonoidHom
          (Gal.galActionHom p q.SplittingField (res (F' := F') p ϕ)) := by
    intro ϕ
    ext i
    simp only [MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe, Equiv.permCongr_apply, hγ,
      Equiv.trans_apply, Equiv.symm_trans_apply]
    congr 1
    apply Subtype.ext
    rw [Gal.galActionHom_restrict, hs, Equiv.setCongr_apply, galActionHom_res]
    rfl
  have hsurj := Gal.restrict_surjective q q.SplittingField
  have : IsGalois F' q.SplittingField := { }
  have hnorm := res_range_normal (F' := F') (E := q.SplittingField) p hrel
  refine ⟨r.trans γ, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨_, ⟨ψ, rfl⟩, rfl⟩
    obtain ⟨ϕ, rfl⟩ := hsurj ψ
    exact ⟨_, ⟨res (F' := F') p ϕ, rfl⟩, (harith _).trans (hgeo ϕ).symm⟩
  · rintro _ ⟨_, ⟨τ, rfl⟩, rfl⟩ _ ⟨_, ⟨ψ, rfl⟩, rfl⟩
    obtain ⟨ϕ, rfl⟩ := hsurj ψ
    obtain ⟨ϕ', hϕ'⟩ := hnorm.conj_mem _ ⟨ϕ, rfl⟩ τ
    refine ⟨_, ⟨Gal.restrict q q.SplittingField ϕ', rfl⟩, ?_⟩
    refine (hgeo ϕ').trans ?_
    rw [harith, hgeo, ← map_inv, ← map_mul, ← map_mul, hϕ']
    congr 1
    have key : ∀ a b : p.Gal, Gal.galActionHom p q.SplittingField (a * b * a⁻¹) =
        Gal.galActionHom p q.SplittingField a * Gal.galActionHom p q.SplittingField b *
          Gal.galActionHom p q.SplittingField a⁻¹ := fun a b => by simp only [map_mul]
    exact key τ (res (F' := F') p ϕ)
  · -- the root map `r` is the canonical map composed with the inverse of the self-lift
    let a : p.SplittingField →ₐ[F] p.SplittingField :=
      IsSplittingField.lift p.SplittingField p
        (Fact.out : (p.map (algebraMap F p.SplittingField)).Splits)
    let aE := AlgEquiv.ofBijective a (Algebra.IsAlgebraic.algHom_bijective a)
    let b : p.SplittingField →ₐ[F] q.SplittingField :=
      IsSplittingField.lift p.SplittingField p
        (Fact.out : (p.map (algebraMap F q.SplittingField)).Splits)
    refine ⟨b.comp aE.symm.toAlgHom, fun i => ?_⟩
    have hr : ∀ x, (r x : q.SplittingField) = b (aE.symm (x : p.SplittingField)) := by
      intro x
      obtain ⟨y, rfl⟩ := (Gal.rootsEquivRoots p p.SplittingField).surjective x
      have hy : ((Gal.rootsEquivRoots p p.SplittingField y : p.rootSet p.SplittingField) :
          p.SplittingField) = aE y := rfl
      rw [hy, AlgEquiv.symm_apply_apply]
      simp only [hr, Equiv.trans_apply, Equiv.symm_apply_apply]
      rfl
    have h := hr ((r.trans γ).symm i)
    change b (aE.symm ((r.trans γ).symm i : p.SplittingField)) = _
    rw [← h]
    simp [hγ, hs]
end Sz8.Galois.GaloisDescent
