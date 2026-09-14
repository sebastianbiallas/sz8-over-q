import Mathlib.RingTheory.Invariant.Galois
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.RingTheory.Ideal.GoingUp
import Sz8.Galois.GaloisDescent

/-!
# Specialization into the decomposition group

`A` integrally closed with fraction field `K`, `L/K` finite Galois, `B` the integral closure of `A`
in `L`, `f ∈ A[X]` monic and split in `L`, and `A → F` a surjection onto a field such that the
reduction `f₀` is separable.

* `exists_decomposition`: some maximal ideal `P` of `B` over the kernel, and a labelling of the
  roots of `f₀` (in any field where `f₀` splits) matching a given labelling of the roots of `f` in
  `L`, such that every element of `Gal(f₀/F)` acts on the labels as an element of the decomposition
  group `Stab(P)`. Proof: the roots of `f` lie in `B` and reduce bijectively onto the roots of `f₀`
  in `B/P` (separability); `B/P` is normal over `F` (`Ideal.Quotient.normal`), so each `σ` extends
  to `B/P`, and `Stab(P) → Aut((B/P)/(A/p))` is onto (`Ideal.Quotient.stabilizerHom_surjective`).
* `image_le_decomposition`: the same, as a containment of labelled permutation groups.
* `smul_eq_self_of_split`: an element of `Stab(P)` fixes every `s ∈ B` that is a root of some
  `c ∈ A[X]` whose reduction splits into distinct linear factors (the split-witness consumer).
* `smul_eq_self_of_residue`: an element of `Stab(P)` fixes every `s ∈ B` that is congruent to an
  element of `A` modulo `P` and is a root of some `c ∈ A[X]` with separable reduction.
-/

open Polynomial
open scoped Pointwise

namespace Sz8.Galois.Specialize

variable {A K L : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- `Gal(L/K)` acting on the integral closure of `A` in `L`. -/
noncomputable instance act : MulSemiringAction Gal(L/K) (integralClosure A L) :=
  IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)

omit [IsDomain A] [IsIntegrallyClosed A] [FiniteDimensional K L] in
theorem coe_smul (g : Gal(L/K)) (b : integralClosure A L) :
    ((g • b : integralClosure A L) : L) = g (b : L) :=
  algebraMap_galRestrict_apply A g b

instance : SMulCommClass Gal(L/K) A (integralClosure A L) :=
  ⟨fun g a b => (map_smul (galRestrict A K L (integralClosure A L) g) a b)⟩

instance isInvariant : Algebra.IsInvariant A (integralClosure A L) Gal(L/K) := by
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)
  exact Algebra.isInvariant_of_isGalois A K L _


variable {F : Type*} [Field F] [Algebra A F]

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- The roots of a monic `f` over `A`, split in `L`, lie in the integral closure, and `f` is their
product there. -/
theorem exists_prod (f : A[X]) (hmon : f.Monic) (hs : (f.map (algebraMap A L)).Splits) :
    ∃ s : Multiset (integralClosure A L),
      s.map (↑) = (f.map (algebraMap A L)).roots ∧
      f.map (algebraMap A (integralClosure A L)) = (s.map fun b => X - C b).prod := by
  have hint : ∀ y ∈ (f.map (algebraMap A L)).roots,
      y ∈ integralClosure A L := by
    intro y hy
    have hy' := (mem_roots (hmon.map _).ne_zero).1 hy
    rw [mem_integralClosure_iff]
    exact ⟨f, hmon, by rwa [IsRoot, eval_map_algebraMap] at hy'⟩
  obtain ⟨s, hs'⟩ : ∃ s : Multiset (integralClosure A L),
      s.map (↑) = (f.map (algebraMap A L)).roots := CanLift.prf _ hint
  refine ⟨s, hs', ?_⟩
  apply map_injective _ (FaithfulSMul.algebraMap_injective (integralClosure A L) L)
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.map_multiset_prod,
    Multiset.map_map]
  conv_lhs => rw [hs.eq_prod_roots_of_monic (hmon.map _), ← hs', Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  simp

theorem mem_rootSet_iff_mem_roots {T S : Type*} [CommRing T] [Field S] [Algebra T S] (q : T[X])
    (x : S) : x ∈ q.rootSet S ↔ x ∈ (q.map (algebraMap T S)).roots := by
  classical
  rw [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, aroots_def]

/-- **Specialization into the decomposition group.** Let `A` be integrally closed with fraction
field `K`, `L/K` finite Galois, `f ∈ A[X]` monic and split in `L`, and `A → F` a surjection onto a
field for which the reduction `f₀` of `f` is separable. Then there is a maximal ideal `P` of the
integral closure of `A` in `L` over the kernel, and a labelling `β₀` of the roots of `f₀` (in any
field `Ω` where it splits) matching a given labelling `β` of the roots of `f` in `L`, such that
every element of `Gal(f₀/F)` acts on the labels as some element of the decomposition group of
`P`. -/
theorem exists_decomposition {Ω ι : Type*} [Field Ω] [Algebra F Ω]
    (hχ : Function.Surjective (algebraMap A F)) (f : A[X]) (hmon : f.Monic)
    [Fact (((f.map (algebraMap A K)).map (algebraMap K L)).Splits)]
    [Fact (((f.map (algebraMap A F)).map (algebraMap F Ω)).Splits)]
    (hsep : (f.map (algebraMap A F)).Separable)
    (β : (f.map (algebraMap A K)).rootSet L ≃ ι) :
    ∃ P : Ideal (integralClosure A L), P.IsMaximal ∧
      P.comap (algebraMap A (integralClosure A L)) = RingHom.ker (algebraMap A F) ∧
      ∃ β₀ : (f.map (algebraMap A F)).rootSet Ω ≃ ι,
        ∀ σ : (f.map (algebraMap A F)).Gal, ∃ g ∈ MulAction.stabilizer Gal(L/K) P,
          Equiv.permCongr β₀ (Gal.galActionHom _ Ω σ) =
            Equiv.permCongr β (Gal.galActionHom _ L (Gal.restrict _ L g)) := by
  classical
  set B := integralClosure A L
  set p := RingHom.ker (algebraMap A F) with hp
  have : p.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hχ
  have : FaithfulSMul A B := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have h : (algebraMap B L).comp (algebraMap A B) = (algebraMap K L).comp (algebraMap A K) := by
      rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    intro x y hxy
    have h2 := congrArg (algebraMap B L) hxy
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, h] at h2
    exact IsFractionRing.injective A K ((algebraMap K L).injective h2)
  obtain ⟨P, hPmax, hPover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) p
  have := hPmax
  let : Field (B ⧸ P) := Ideal.Quotient.field P
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  -- `F` is the residue field of `p`, placed between `A ⧸ p` and `B ⧸ P`
  let e : (A ⧸ p) ≃ₐ[A] F := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A F) hχ
  let : Algebra (A ⧸ p) F := e.toRingEquiv.toRingHom.toAlgebra
  let : Algebra F (B ⧸ P) :=
    ((algebraMap (A ⧸ p) (B ⧸ P)).comp e.symm.toRingEquiv.toRingHom).toAlgebra
  have : IsScalarTower (A ⧸ p) F (B ⧸ P) := IsScalarTower.of_algebraMap_eq' <| RingHom.ext fun x => by
    simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower A F (B ⧸ P) := IsScalarTower.of_algebraMap_eq' <| RingHom.ext fun a => by
    have : e.symm (algebraMap A F a) = Ideal.Quotient.mk p a := by
      rw [AlgEquiv.symm_apply_eq]; exact (e.commutes a).symm
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    change _ = algebraMap (A ⧸ p) (B ⧸ P) (e.symm (algebraMap A F a))
    rw [this]
    rfl
  have : Normal (A ⧸ p) (B ⧸ P) := Ideal.Quotient.normal Gal(L/K) p P
  have : Normal F (B ⧸ P) := Normal.tower_top_of_normal (A ⧸ p) F (B ⧸ P)
  -- the roots of `f` lie in `B`, and reduce onto the roots of `(f.map (algebraMap A F))`
  have hsL : (f.map (algebraMap A L)).Splits := by
    have h := (inferInstance : Fact (((f.map (algebraMap A K)).map (algebraMap K L)).Splits)).out
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at h
  obtain ⟨s, hs1, hs2⟩ := exists_prod f hmon hsL
  have hκ : (f.map (algebraMap A F)).map (algebraMap F (B ⧸ P)) =
      ((s.map (Ideal.Quotient.mk P)).map fun z => X - C z).prod := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq A B (B ⧸ P), ← Polynomial.map_map, hs2,
      Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [Ideal.Quotient.algebraMap_eq]
  have hrootsκ : ((f.map (algebraMap A F)).map (algebraMap F (B ⧸ P))).roots = s.map (Ideal.Quotient.mk P) := by
    rw [hκ, roots_multiset_prod_X_sub_C]
  have hspl : ((f.map (algebraMap A F)).map (algebraMap F (B ⧸ P))).Splits := by
    rw [hκ]
    refine Splits.multisetProd fun q hq => ?_
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hq
    exact Splits.X_sub_C z
  have : Fact (((f.map (algebraMap A F)).map (algebraMap F (B ⧸ P))).Splits) := ⟨hspl⟩
  have hnodup : (s.map (Ideal.Quotient.mk P)).Nodup :=
    hrootsκ ▸ nodup_roots (hsep.map)
  have hmemL : ∀ x : L, x ∈ (f.map (algebraMap A K)).rootSet L ↔ ∃ b ∈ s, (b : L) = x := by
    intro x
    rw [mem_rootSet_iff_mem_roots, Polynomial.map_map, ← IsScalarTower.algebraMap_eq, ← hs1,
      Multiset.mem_map]
  have hmemκ : ∀ z : B ⧸ P, z ∈ (f.map (algebraMap A F)).rootSet (B ⧸ P) ↔ ∃ b ∈ s, Ideal.Quotient.mk P b = z := by
    intro z
    rw [mem_rootSet_iff_mem_roots, hrootsκ, Multiset.mem_map]
  have hB : ∀ x : (f.map (algebraMap A K)).rootSet L, ∃ b ∈ s, (b : L) = x := fun x => (hmemL x).1 x.2
  choose b hbs hb using hB
  let r : (f.map (algebraMap A K)).rootSet L → (f.map (algebraMap A F)).rootSet (B ⧸ P) := fun x =>
    ⟨Ideal.Quotient.mk P (b x), (hmemκ _).2 ⟨b x, hbs x, rfl⟩⟩
  have hr_inj : Function.Injective r := by
    intro x y hxy
    have h := Multiset.inj_on_of_nodup_map hnodup _ (hbs x) _ (hbs y) (congrArg Subtype.val hxy)
    exact Subtype.ext ((hb x).symm.trans ((congrArg Subtype.val h).trans (hb y)))
  have hr_surj : Function.Surjective r := by
    rintro ⟨z, hz⟩
    obtain ⟨c, hc, rfl⟩ := (hmemκ z).1 hz
    let x : (f.map (algebraMap A K)).rootSet L := ⟨c, (hmemL c).2 ⟨c, hc, rfl⟩⟩
    refine ⟨x, Subtype.ext ?_⟩
    show Ideal.Quotient.mk P (b x) = Ideal.Quotient.mk P c
    congr 1
    exact Subtype.ext (hb x)
  let R := Equiv.ofBijective r ⟨hr_inj, hr_surj⟩
  let e₀ : (f.map (algebraMap A F)).rootSet (B ⧸ P) ≃ (f.map (algebraMap A F)).rootSet Ω :=
    (Gal.rootsEquivRoots (f.map (algebraMap A F)) (B ⧸ P)).symm.trans (Gal.rootsEquivRoots (f.map (algebraMap A F)) Ω)
  refine ⟨P, hPmax, hPover.over.symm, e₀.symm.trans (R.symm.trans β), fun σ => ?_⟩
  obtain ⟨τ, rfl⟩ := Gal.restrict_surjective (f.map (algebraMap A F)) (B ⧸ P) σ
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective Gal(L/K) p P
    (τ.restrictScalars (A ⧸ p))
  refine ⟨g, g.2, ?_⟩
  -- reduction intertwines `g` with `τ`
  have hkey : ∀ x : (f.map (algebraMap A K)).rootSet L,
      R (Gal.galActionHom (f.map (algebraMap A K)) L (Gal.restrict (f.map (algebraMap A K)) L g) x) =
        Gal.galActionHom (f.map (algebraMap A F)) (B ⧸ P) (Gal.restrict (f.map (algebraMap A F)) (B ⧸ P) τ) (R x) := by
    intro x
    apply Subtype.ext
    rw [Gal.galActionHom_restrict]
    set y := Gal.galActionHom (f.map (algebraMap A K)) L (Gal.restrict (f.map (algebraMap A K)) L g) x with hy
    have hy' : (y : L) = (g : Gal(L/K)) x := by rw [hy, Gal.galActionHom_restrict]
    have hby : b y = (g : Gal(L/K)) • b x := Subtype.ext (by rw [hb, coe_smul, hb, hy'])
    show Ideal.Quotient.mk P (b y) = τ (Ideal.Quotient.mk P (b x))
    have h2 := congrArg (fun φ => φ (Ideal.Quotient.mk P (b x))) hg
    simp only [Ideal.Quotient.stabilizerHom_apply, AlgEquiv.coe_restrictScalars] at h2
    rw [hby]
    exact h2
  ext i
  simp only [Equiv.permCongr_apply, Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm,
    GaloisDescent.galActionHom_conj (f.map (algebraMap A F)) (B ⧸ P) Ω, e₀]
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  rw [← hkey, Equiv.symm_apply_apply]

/-- Two distinct roots of `c` in a domain with the same image under `φ` make `c.map φ` inseparable. -/
theorem not_separable_of_residue_eq {B κ : Type*} [CommRing B] [IsDomain B] [CommRing κ]
    [IsDomain κ]
    (φ : B →+* κ) {c : B[X]} {x y : B} (hx : c.IsRoot x) (hy : c.IsRoot y) (hxy : x ≠ y)
    (hφ : φ x = φ y) : ¬ (c.map φ).Separable := by
  intro hsep
  have h1 := (mul_divByMonic_eq_iff_isRoot (p := c)).2 hx
  have hy1 : (c /ₘ (X - C x)).IsRoot y := by
    have h := hy
    rw [← h1, IsRoot, eval_mul, eval_sub, eval_X, eval_C] at h
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hxy.symm)
  have h2 := (mul_divByMonic_eq_iff_isRoot (p := c /ₘ (X - C x))).2 hy1
  have hdvd : (X - C (φ x)) * (X - C (φ x)) ∣ c.map φ := by
    refine ⟨(c /ₘ (X - C x) /ₘ (X - C y)).map φ, ?_⟩
    conv_lhs => rw [← h1, ← h2]
    simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, hφ]
    ring
  exact not_isUnit_X_sub_C (φ x) (hsep.squarefree _ hdvd)

omit [IsDomain A] [IsIntegrallyClosed A] [FiniteDimensional K L] in
/-- The residue field of `P` receives `F`. -/
noncomputable def resEmb (hχ : Function.Surjective (algebraMap A F))
    (P : Ideal (integralClosure A L))
    (hP : P.comap (algebraMap A (integralClosure A L)) = RingHom.ker (algebraMap A F)) :
    F →+* integralClosure A L ⧸ P :=
  (Ideal.quotientMap P (algebraMap A (integralClosure A L)) hP.symm.le).comp
    (RingHom.quotientKerEquivOfSurjective hχ).symm.toRingHom

omit [IsDomain A] [IsIntegrallyClosed A] [FiniteDimensional K L] in
theorem resEmb_algebraMap (hχ : Function.Surjective (algebraMap A F))
    (P : Ideal (integralClosure A L))
    (hP : P.comap (algebraMap A (integralClosure A L)) = RingHom.ker (algebraMap A F)) (a : A) :
    resEmb hχ P hP (algebraMap A F a) = Ideal.Quotient.mk P (algebraMap A _ a) := by
  have : (RingHom.quotientKerEquivOfSurjective hχ).symm (algebraMap A F a) = Ideal.Quotient.mk _ a := by
    exact RingHom.quotientKerEquivOfSurjective_symm_apply hχ a
  simp [resEmb, this, Ideal.quotientMap_mk]

omit [IsDomain A] [IsIntegrallyClosed A] [FiniteDimensional K L] in
/-- **Decomposition elements fix integral elements with rational residue.** If `s` in the integral
closure is a root of `c ∈ A[X]` whose reduction is separable, and `s` is congruent modulo `P` to an
element of `A`, then every element of the decomposition group of `P` fixes `s`. -/
theorem smul_eq_self_of_residue (hχ : Function.Surjective (algebraMap A F))
    {P : Ideal (integralClosure A L)}
    (hP : P.comap (algebraMap A (integralClosure A L)) = RingHom.ker (algebraMap A F))
    [P.IsPrime] {c : A[X]} (hsep : (c.map (algebraMap A F)).Separable)
    {s : integralClosure A L} (hc : aeval s c = 0) {a : A}
    (hs : s - algebraMap A _ a ∈ P) {g : Gal(L/K)} (hg : g ∈ MulAction.stabilizer Gal(L/K) P) :
    g • s = s := by
  by_contra hne
  have hgP : g • P = P := hg
  have hroot : ∀ y : integralClosure A L, aeval y c = 0 → (c.map (algebraMap A _)).IsRoot y :=
    fun y hy => by rwa [IsRoot, eval_map_algebraMap]
  have hgs : aeval (g • s) c = 0 := by
    have h := Polynomial.aeval_algHom_apply (MulSemiringAction.toAlgHom A (integralClosure A L) g)
      s c
    rw [hc, map_zero] at h
    exact h
  have hres : Ideal.Quotient.mk P (g • s) = Ideal.Quotient.mk P s := by
    rw [Ideal.Quotient.eq]
    have h1 : g • (s - algebraMap A _ a) ∈ P := by
      rw [← hgP]; exact Ideal.smul_mem_pointwise_smul g _ P hs
    have h2 : g • s - s = g • (s - algebraMap A _ a) - (s - algebraMap A _ a) := by
      rw [smul_sub, smul_algebraMap]; ring
    rw [h2]
    exact P.sub_mem h1 hs
  apply not_separable_of_residue_eq (Ideal.Quotient.mk P) (hroot _ hgs) (hroot _ hc) hne hres
  have := hsep.map (f := resEmb hχ P hP)
  rw [Polynomial.map_map] at this ⊢
  rwa [show (resEmb hχ P hP).comp (algebraMap A F) = (Ideal.Quotient.mk P).comp (algebraMap A _)
    from RingHom.ext (resEmb_algebraMap hχ P hP)] at this

omit [IsDomain A] [IsIntegrallyClosed A] [FiniteDimensional K L] in
/-- **Split witness.** If `s` in the integral closure is a root of `c ∈ A[X]` whose reduction splits
into distinct linear factors over `F`, every element of the decomposition group of `P` fixes `s`:
the residue of `s` is one of the roots, which come from `A`. -/
theorem smul_eq_self_of_split (hχ : Function.Surjective (algebraMap A F))
    {P : Ideal (integralClosure A L)}
    (hP : P.comap (algebraMap A (integralClosure A L)) = RingHom.ker (algebraMap A F))
    [P.IsPrime] {c : A[X]} {s : integralClosure A L} (hc : aeval s c = 0)
    {ι : Type*} [Fintype ι] {a : ι → F} (ha : Function.Injective a)
    (hsplit : c.map (algebraMap A F) = ∏ i, (X - C (a i)))
    {g : Gal(L/K)} (hg : g ∈ MulAction.stabilizer Gal(L/K) P) : g • s = s := by
  have hsep : (c.map (algebraMap A F)).Separable := by
    rw [hsplit]; exact separable_prod_X_sub_C_iff.2 ha
  -- the residue of `s` is a root of the split reduction
  have hcomp : (resEmb hχ P hP).comp (algebraMap A F) = (Ideal.Quotient.mk P).comp (algebraMap A _) :=
    RingHom.ext (resEmb_algebraMap hχ P hP)
  have h0 : ((c.map (algebraMap A F)).map (resEmb hχ P hP)).eval (Ideal.Quotient.mk P s) = 0 := by
    rw [Polynomial.map_map, hcomp, eval_map, ← Polynomial.hom_eval₂]
    change Ideal.Quotient.mk P (aeval s c) = 0
    rw [hc, map_zero]
  rw [hsplit, Polynomial.map_prod, eval_prod, Finset.prod_eq_zero_iff] at h0
  obtain ⟨i, -, hi⟩ := h0
  simp only [Polynomial.map_sub, map_X, map_C, eval_sub, eval_X, eval_C, sub_eq_zero] at hi
  obtain ⟨a', ha'⟩ := hχ (a i)
  rw [← ha', resEmb_algebraMap, Ideal.Quotient.eq] at hi
  exact smul_eq_self_of_residue hχ hP hsep hc hi hg

/-- **Consumer form.** The labelled image of the fibre's Galois group lies in the labelled image of
the decomposition group of `P`. -/
theorem image_le_decomposition {Ω ι : Type*} [Field Ω] [Algebra F Ω]
    (hχ : Function.Surjective (algebraMap A F)) (f : A[X]) (hmon : f.Monic)
    [Fact (((f.map (algebraMap A K)).map (algebraMap K L)).Splits)]
    [Fact (((f.map (algebraMap A F)).map (algebraMap F Ω)).Splits)]
    (hsep : (f.map (algebraMap A F)).Separable)
    (β : (f.map (algebraMap A K)).rootSet L ≃ ι) :
    ∃ P : Ideal (integralClosure A L), P.IsMaximal ∧
      P.comap (algebraMap A (integralClosure A L)) = RingHom.ker (algebraMap A F) ∧
      ∃ β₀ : (f.map (algebraMap A F)).rootSet Ω ≃ ι,
        (Gal.galActionHom _ Ω).range.map (Equiv.permCongrHom β₀).toMonoidHom ≤
          (MulAction.stabilizer Gal(L/K) P).map ((Equiv.permCongrHom β).toMonoidHom.comp
            ((Gal.galActionHom _ L).comp (Gal.restrict (f.map (algebraMap A K)) L))) := by
  obtain ⟨P, hPmax, hP, β₀, h⟩ := exists_decomposition hχ f hmon hsep β (Ω := Ω)
  refine ⟨P, hPmax, hP, β₀, ?_⟩
  rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
  obtain ⟨g, hg, hσ⟩ := h σ
  exact ⟨g, hg, hσ.symm⟩

end Sz8.Galois.Specialize

