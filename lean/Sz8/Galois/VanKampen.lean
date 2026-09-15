import Mathlib.Topology.Subpath
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# The generation half of Seifert–van Kampen

> if `X = U ∪ V` with `U`, `V` open and path connected, the base point in `U ∩ V`, and `U ∩ V` path
> connected, then the images of `π₁(U)` and `π₁(V)` generate `π₁(X)`.

This is the part of van Kampen's theorem that meridian generation (`Sz8.Galois.MainTheorem`) uses;
there is no injectivity claim and no free product with amalgamation. The path-connectedness of `U`
and `V` lets the connecting path at a junction between two consecutive pieces in the same set be
found inside that set.

Ingredients from Mathlib:

* `exists_monotone_Icc_subset_open_cover_unitInterval` (`Mathlib/Topology/UnitInterval.lean`)
  refines an open cover of `[0,1]` to a monotone finite partition with each `Icc (t n) (t (n+1))`
  inside a member (the Lebesgue-number step);
* `Path.concat`, `Path.subpath` and `Path.Homotopic.concat_subpath` (`Mathlib/Topology/Subpath.lean`):
  concatenating the subpaths of `γ` along a partition is homotopic to `γ` (the subdivision step).

Proved here: `mem_range_inclHom` (a loop whose range lies in `Y` has its class in the image of
`π₁(Y)`); `concat_mem`, by induction on the number of pieces, for a concatenation whose pieces lie
in `Good` sets, conjugated back to the base point by connecting paths in those sets
(`Path.concat_succ` peels off the last piece, `PathQ.regroup` inserts the cancelling pair); and
`vanKampen_generation`, which chooses for each piece a member `Y k ∈ {U, V}` and connecting paths
inside `Y (k-1) ∩ Y k` (`IsPathConnected.joinedIn`).

It is applied with a cover adapted to the certified polylines (`Sz8.Galois.TwoPunctures`): with
`a = ζ₃`, `b = ζ₃²` and `0 < ε < √3/2`, `U = {Im z > -ε} ∖ {a}` and `V = {Im z < ε} ∖ {b}` cover
`ℂ ∖ {a, b}`, meet in the convex strip `|Im z| < ε`, and each is a half-plane minus a point, so no
conjugating paths appear. The further punctures at the nodes are handled by
`Sz8.Galois.Descent.kernel_descent` and `Sz8.Galois.Filling.Setup.range_eq_closure`.
-/

open CategoryTheory

namespace Sz8.Galois

variable {X : Type*} [TopologicalSpace X]

/-- The homomorphism `π₁(U, x) → π₁(X, x)` induced by the inclusion of a subset. -/
noncomputable def inclHom (U : Set X) {x : X} (hx : x ∈ U) :
    FundamentalGroup U ⟨x, hx⟩ →* FundamentalGroup X x :=
  FundamentalGroup.mapOfEq (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) rfl

/-- A loop at `x` whose range lies in `Y` has its class in the image of `π₁(Y, x)`. This is the
step that lifts a path to the subtype, and it is what the induction applies to each piece. -/
theorem mem_range_inclHom {Y : Set X} {x : X} (hx : x ∈ Y) (γ : Path x x) (hγ : ∀ u, γ u ∈ Y) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) ∈ (inclHom Y hx).range := by
  refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
    { toFun := fun u => (⟨γ u, hγ u⟩ : Y)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }), ?_⟩
  rw [inclHom, FundamentalGroup.mapOfEq_apply]
  rfl

namespace PathQ
open Path.Homotopic

theorem trans_assoc {y z w v : X} (P : Path.Homotopic.Quotient y z)
    (Q : Path.Homotopic.Quotient z w) (R : Path.Homotopic.Quotient w v) :
    (P.trans Q).trans R = P.trans (Q.trans R) := by
  induction P using Path.Homotopic.Quotient.ind with | _ f =>
  induction Q using Path.Homotopic.Quotient.ind with | _ g =>
  induction R using Path.Homotopic.Quotient.ind with | _ h =>
  exact Quotient.sound ⟨Path.Homotopy.transAssoc f g h⟩

theorem refl_trans {y z : X} (P : Path.Homotopic.Quotient y z) :
    (Path.Homotopic.Quotient.refl y).trans P = P := by
  induction P using Path.Homotopic.Quotient.ind with | _ f =>
  exact Quotient.sound ⟨Path.Homotopy.reflTrans f⟩

theorem trans_refl {y z : X} (P : Path.Homotopic.Quotient y z) :
    P.trans (Path.Homotopic.Quotient.refl z) = P := by
  induction P using Path.Homotopic.Quotient.ind with | _ f =>
  exact Quotient.sound ⟨Path.Homotopy.transRefl f⟩

theorem trans_symm {y z : X} (P : Path.Homotopic.Quotient y z) :
    P.trans P.symm = Path.Homotopic.Quotient.refl y := by
  induction P using Path.Homotopic.Quotient.ind with | _ f =>
  exact Quotient.sound ⟨(Path.Homotopy.reflTransSymm f).symm⟩

theorem symm_trans {y z : X} (P : Path.Homotopic.Quotient y z) :
    P.symm.trans P = Path.Homotopic.Quotient.refl z := by
  induction P using Path.Homotopic.Quotient.ind with | _ f =>
  exact Quotient.sound ⟨(Path.Homotopy.reflSymmTrans f).symm⟩

theorem symm_trans_cancel {a b c : X} (P : Path.Homotopic.Quotient a b)
    (Z : Path.Homotopic.Quotient b c) : P.symm.trans (P.trans Z) = Z := by
  rw [← trans_assoc, symm_trans, refl_trans]

theorem regroup {a b c e : X} (D0 : Path.Homotopic.Quotient a b)
    (C' : Path.Homotopic.Quotient b c) (Dm : Path.Homotopic.Quotient a c)
    (Φ : Path.Homotopic.Quotient c e) (Dn : Path.Homotopic.Quotient a e) :
    D0.trans ((C'.trans Φ).trans Dn.symm)
      = (D0.trans (C'.trans Dm.symm)).trans (Dm.trans (Φ.trans Dn.symm)) := by
  simp only [trans_assoc, symm_trans_cancel]
end PathQ

/-! The three definitional identifications the induction below leans on: concatenation of loop
classes is multiplication in the fundamental group with the factors reversed, the constant class
is the unit, and the two ways of shifting a `Fin` index agree on the nose. -/

example {x : X} (A B : Path.Homotopic.Quotient x x) (H : Subgroup (FundamentalGroup X x))
    (hA : FundamentalGroup.fromPath A ∈ H) (hB : FundamentalGroup.fromPath B ∈ H) :
    FundamentalGroup.fromPath (A.trans B) ∈ H := mul_mem hB hA

example {x : X} : ((1 : FundamentalGroup X x) : Path.Homotopic.Quotient x x)
    = Path.Homotopic.Quotient.refl x := rfl

example {n : ℕ} (k : Fin n) : k.castSucc.succ = k.succ.castSucc := rfl

namespace PathQ
theorem mem_of_trans {a b c : X} {S : Set X} (α : Path a b) (β : Path b c)
    (hα : ∀ u, α u ∈ S) (hβ : ∀ u, β u ∈ S) : ∀ u, (α.trans β) u ∈ S := by
  intro u
  have h : (α.trans β) u ∈ Set.range (α.trans β) := ⟨u, rfl⟩
  rw [Path.trans_range] at h
  rcases h with ⟨v, hv⟩ | ⟨v, hv⟩
  exacts [hv ▸ hα v, hv ▸ hβ v]

theorem mem_of_symm {a b : X} {S : Set X} (α : Path a b) (hα : ∀ u, α u ∈ S) :
    ∀ u, α.symm u ∈ S := fun _u => hα _
end PathQ

/-- The core induction: a concatenation whose pieces each lie in a `Good` set, conjugated back to
the base point by connecting paths that also lie in those sets, has its class in `H`. -/
theorem concat_mem {x : X} (H : Subgroup (FundamentalGroup X x)) (Good : Set X → Prop)
    (hH : ∀ Y : Set X, x ∈ Y → Good Y → ∀ loop : Path x x, (∀ u, loop u ∈ Y) →
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop) ∈ H) :
    ∀ (n : ℕ) (p : Fin (n + 1) → X) (F : (k : Fin n) → Path (p k.castSucc) (p k.succ))
      (Y : Fin n → Set X), (∀ k, Good (Y k)) → (∀ k, x ∈ Y k) → (∀ k u, F k u ∈ Y k) →
      ∀ d : (k : Fin (n + 1)) → Path x (p k),
      (∀ (k : Fin n) u, d k.castSucc u ∈ Y k) → (∀ (k : Fin n) u, d k.succ u ∈ Y k) →
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((d 0).trans ((Path.concat p F).trans (d (Fin.last n)).symm))) ∈ H := by
  intro n
  induction n with
  | zero =>
    intro p F Y _ _ _ d _ _
    rw [Path.concat_zero]
    have key : Path.Homotopic.Quotient.mk
        ((d 0).trans ((Path.refl (p 0)).trans (d (Fin.last 0)).symm))
      = Path.Homotopic.Quotient.refl x := by
      show (Path.Homotopic.Quotient.mk (d 0)).trans
        ((Path.Homotopic.Quotient.refl (p 0)).trans
          (Path.Homotopic.Quotient.mk (d 0)).symm) = _
      rw [PathQ.refl_trans, PathQ.trans_symm]
    rw [key]
    exact one_mem H
  | succ n ih =>
    intro p F Y hgood hxY hF d hd1 hd2
    have hb := hH (Y (Fin.last n)) (hxY _) (hgood _)
      ((d (Fin.last n).castSucc).trans ((F (Fin.last n)).trans (d (Fin.last (n + 1))).symm))
      (PathQ.mem_of_trans _ _ (hd1 (Fin.last n))
        (PathQ.mem_of_trans _ _ (hF (Fin.last n)) (PathQ.mem_of_symm _ (hd2 (Fin.last n)))))
    have ha := ih (p ∘ Fin.castSucc) (fun k => F k.castSucc) (fun k => Y k.castSucc)
      (fun k => hgood _) (fun k => hxY _) (fun k u => hF _ u) (fun k => d k.castSucc)
      (fun k u => hd1 k.castSucc u) (fun k u => hd2 k.castSucc u)
    have key : Path.Homotopic.Quotient.mk
        ((d 0).trans ((Path.concat p F).trans (d (Fin.last (n + 1))).symm))
      = (Path.Homotopic.Quotient.mk ((d 0).trans
          ((Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)).trans
            (d (Fin.last n).castSucc).symm))).trans
        (Path.Homotopic.Quotient.mk ((d (Fin.last n).castSucc).trans
          ((F (Fin.last n)).trans (d (Fin.last (n + 1))).symm))) := by
      rw [Path.concat_succ]
      exact PathQ.regroup (Path.Homotopic.Quotient.mk (d 0))
        (Path.Homotopic.Quotient.mk
          (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)))
        (Path.Homotopic.Quotient.mk (d (Fin.last n).castSucc))
        (Path.Homotopic.Quotient.mk (F (Fin.last n)))
        (Path.Homotopic.Quotient.mk (d (Fin.last (n + 1))))
    rw [key]
    exact mul_mem hb ha

/-- The statement of the generation half of Seifert–van Kampen for `X`; proved as
`vanKampen_generation`. -/
def VanKampenGeneration (X : Type) [TopologicalSpace X] : Prop :=
  ∀ (U V : Set X) (x : X) (hxU : x ∈ U) (hxV : x ∈ V),
    IsOpen U → IsOpen V → U ∪ V = Set.univ →
    IsPathConnected U → IsPathConnected V → IsPathConnected (U ∩ V) →
    (inclHom U hxU).range ⊔ (inclHom V hxV).range = ⊤

open Set unitInterval

/-- Two paths that agree pointwise and have the same endpoints have the same class, across a
`cast` of the endpoints. This is what carries the two end connecting paths, whose endpoints are
only propositionally the base point, through the final assembly. -/
theorem mk_cast_eq {x a b : X} (γ : Path a b) (δ : Path x x) (ha : a = x) (hb : b = x)
    (h : ∀ u, γ u = δ u) :
    (Path.Homotopic.Quotient.mk γ).cast ha.symm hb.symm = Path.Homotopic.Quotient.mk δ := by
  subst ha; subst hb
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]
  exact congrArg _ (Path.ext (funext h))

/-- **The generation half of Seifert–van Kampen: if `X = U ∪ V` with `U`,
`V` open and path connected, the base point in `U ∩ V`, and `U ∩ V` path connected, then the images
of `π₁(U)` and `π₁(V)` generate `π₁(X)`.

The loop is subdivided by `exists_monotone_Icc_subset_open_cover_unitInterval`; each piece is a
`Path.subpath` lying in one member `W k` of the cover; the connecting path at junction `j` is taken
inside `W (j-1) ∩ W j`, which is `U`, `V` or `U ∩ V` and so path connected in every case, with
natural-number subtraction making `j = 0` fall out uniformly; `concat_mem` then assembles the
pieces, and the two end connecting paths are returned to the base point by `mk_cast_eq`. -/
theorem vanKampen_generation (X : Type) [TopologicalSpace X] : VanKampenGeneration X := by
  intro U V x hxU hxV hU hV huv hUc hVc hUVc
  rw [Subgroup.eq_top_iff']
  intro g
  set H := (inclHom U hxU).range ⊔ (inclHom V hxV).range with hHdef
  have hH : ∀ Y : Set X, x ∈ Y → (Y = U ∨ Y = V) → ∀ loop : Path x x, (∀ u, loop u ∈ Y) →
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop) ∈ H := by
    rintro Y hxY (rfl | rfl) loop hloop
    · exact Subgroup.mem_sup_left (mem_range_inclHom hxY loop hloop)
    · exact Subgroup.mem_sup_right (mem_range_inclHom hxY loop hloop)
  induction g using Path.Homotopic.Quotient.ind with | _ γ =>
  -- the cover of the unit interval induced by `γ`
  set c : Bool → Set I := fun b => (fun s => γ s) ⁻¹' (cond b U V) with hc
  have hcopen : ∀ b, IsOpen (c b) := by
    intro b; cases b
    exacts [IsOpen.preimage (map_continuous γ) hV, IsOpen.preimage (map_continuous γ) hU]
  have hccov : (Set.univ : Set I) ⊆ ⋃ b, c b := by
    intro s _
    have h : γ s ∈ U ∪ V := huv ▸ Set.mem_univ _
    rcases h with h | h
    exacts [Set.mem_iUnion.2 ⟨true, h⟩, Set.mem_iUnion.2 ⟨false, h⟩]
  obtain ⟨t, ht0, htmono, ⟨N, htN⟩, htcov⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcopen hccov
  choose sel hsel using htcov
  set W : ℕ → Set X := fun k => cond (sel k) U V with hW
  have hWmem : ∀ k, W k = U ∨ W k = V := by
    intro k; cases h : sel k
    exacts [Or.inr (by simp [hW, h]), Or.inl (by simp [hW, h])]
  have hxW : ∀ k, x ∈ W k := by intro k; cases h : sel k <;> simp [hW, h, hxU, hxV]
  have hpiece : ∀ (k : ℕ) (s : I), s ∈ Icc (t k) (t (k + 1)) → γ s ∈ W k := by
    intro k s hs
    have hm := hsel k hs
    cases h : sel k
    · simpa [hW, h] using (by simpa [hc, h] using hm : γ s ∈ cond false U V)
    · simpa [hW, h] using (by simpa [hc, h] using hm : γ s ∈ cond true U V)
  have hWWconn : ∀ a b : ℕ, IsPathConnected (W a ∩ W b) := by
    intro a b
    rcases hWmem a with ha | ha <;> rcases hWmem b with hb | hb <;> rw [ha, hb]
    · simpa using hUc
    · exact hUVc
    · rw [Set.inter_comm]; exact hUVc
    · simpa using hVc
  have hpS : ∀ j : Fin (N + 1), γ (t j.val) ∈ W (j.val - 1) ∩ W j.val := by
    intro j
    refine ⟨?_, hpiece j.val _ ⟨le_refl _, htmono (Nat.le_succ _)⟩⟩
    rcases Nat.eq_zero_or_pos j.val with h | h
    · rw [h]; exact hpiece 0 _ ⟨le_refl _, htmono (Nat.le_succ _)⟩
    · obtain ⟨m, hm⟩ : ∃ m, j.val = m + 1 := ⟨j.val - 1, by omega⟩
      rw [hm, Nat.succ_sub_one]
      exact hpiece m _ ⟨htmono (Nat.le_succ _), le_refl _⟩
  set d : (j : Fin (N + 1)) → Path x (γ (t j.val)) :=
    fun j => ((hWWconn (j.val - 1) j.val).joinedIn x ⟨hxW _, hxW _⟩ _ (hpS j)).somePath with hd
  have hdmem : ∀ (j : Fin (N + 1)) u, d j u ∈ W (j.val - 1) ∩ W j.val :=
    fun j u => ((hWWconn (j.val - 1) j.val).joinedIn x ⟨hxW _, hxW _⟩ _ (hpS j)).somePath_mem u
  -- the pieces land in their cover member
  have hFmem : ∀ (k : Fin N) u,
      (γ.subpath (t k.castSucc.val) (t k.succ.val)) u ∈ W k.val := by
    intro k u
    have hle : t k.castSucc.val ≤ t k.succ.val := by
      simp only [Fin.val_castSucc, Fin.val_succ]; exact htmono (Nat.le_succ _)
    refine hpiece k.val _ ?_
    have hr : Set.Icc.convexComb (t k.castSucc.val) (t k.succ.val) u
        ∈ Set.uIcc (t k.castSucc.val) (t k.succ.val) := by
      rw [← Path.range_subpathAux]; exact ⟨u, rfl⟩
    rw [Set.uIcc_of_le hle] at hr
    simpa only [Fin.val_castSucc, Fin.val_succ] using hr
  have main := concat_mem H (fun Y => Y = U ∨ Y = V) hH N (fun j : Fin (N + 1) => γ (t j.val))
    (fun k : Fin N => γ.subpath (t k.castSucc.val) (t k.succ.val)) (fun k : Fin N => W k.val)
    (fun k => hWmem _) (fun k => hxW _) hFmem d
    (fun k u => (hdmem k.castSucc u).2) (fun k u => by simpa using (hdmem k.succ u).1)
  -- the two ends
  set D0 := d 0 with hD0
  set DN := d (Fin.last N) with hDN
  set CC := Path.concat (fun j : Fin (N + 1) => γ (t j.val))
    (fun k : Fin N => γ.subpath (t k.castSucc.val) (t k.succ.val)) with hCC
  have htN' : t N = 1 := htN N (le_refl N)
  have hq0 : γ (t (0 : Fin (N + 1)).val) = x := by show γ (t 0) = x; rw [ht0]; exact γ.source
  have hqN : γ (t (Fin.last N).val) = x := by show γ (t N) = x; rw [htN']; exact γ.target
  have hL0 : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (D0.cast rfl hq0.symm)) ∈ H :=
    hH _ (hxW _) (hWmem _) _ (fun u => (hdmem 0 u).2)
  have hLN : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (DN.cast rfl hqN.symm)) ∈ H :=
    hH _ (hxW _) (hWmem _) _ (fun u => (hdmem (Fin.last N) u).2)
  have hZ' : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((D0.cast rfl hq0.symm).symm.trans
        ((D0.trans (CC.trans DN.symm)).trans (DN.cast rfl hqN.symm)))) ∈ H :=
    mul_mem (mul_mem hLN main) (inv_mem hL0)
  have step1 := mk_cast_eq (D0.symm.trans ((D0.trans (CC.trans DN.symm)).trans DN))
    ((D0.cast rfl hq0.symm).symm.trans
      ((D0.trans (CC.trans DN.symm)).trans (DN.cast rfl hqN.symm))) hq0 hqN (fun u => rfl)
  have step2 : Path.Homotopic.Quotient.mk
      (D0.symm.trans ((D0.trans (CC.trans DN.symm)).trans DN))
      = Path.Homotopic.Quotient.mk CC := by
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      PathQ.trans_assoc, PathQ.symm_trans_cancel, PathQ.symm_trans, PathQ.trans_refl]
  have hcs : Path.Homotopic.Quotient.mk (Path.concat (fun j : Fin (N + 1) => γ (t j.val))
      (fun k : Fin N => γ.subpath (t k.castSucc.val) (t k.succ.val)))
      = Path.Homotopic.Quotient.mk
        (γ.subpath (t (0 : Fin (N + 1)).val) (t (Fin.last N).val)) :=
    Quotient.sound (Path.Homotopic.concat_subpath γ (fun j : Fin (N + 1) => t j.val))
  have step3 : (Path.Homotopic.Quotient.mk CC).cast hq0.symm hqN.symm
      = Path.Homotopic.Quotient.mk γ := by
    rw [hCC, hcs]
    refine mk_cast_eq _ _ hq0 hqN (fun u => ?_)
    show γ (Set.Icc.convexComb (t (0 : Fin (N + 1)).val) (t (Fin.last N).val) u) = γ u
    congr 1
    rw [show t (0 : Fin (N + 1)).val = 0 from ht0, show t (Fin.last N).val = 1 from htN']
    ext; simp [Set.Icc.convexComb]
  rw [← step3, ← step2, step1]
  exact hZ'

end Sz8.Galois
