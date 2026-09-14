import Sz8.Galois.VanKampen
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Representations that kill small loops descend

Abstract kernel form of puncture filling. `X = U ∪ D` with `U`, `D` open; `ρ` a representation
of `π₁(U, x)`; `c y` a chosen connecting path from the base point to each `y ∈ U`. If `ρ` kills
`c y · β · (c z)⁻¹` for every path `β` in `U` lying inside `D`, then `ρ` takes equal values on
loops in `U` that become homotopic in `X`.

For puncture filling take `U = X ∖ A` and `D` a union of small discs about the points of `A`;
the connecting paths into each punctured disc run through one fixed point of that disc, so the
hypothesis says that `ρ` kills based conjugates of loops in the punctured discs.

The proof is the grid argument: subdivide the homotopy square so that each small square maps
into `U` or into `D`, value every grid edge by `Φ`, and show each small square commutes —
`Path.Homotopic.map_trans_evalAt` for `U`-squares, all four values trivial for `D`-squares.
-/

open Set unitInterval

namespace Sz8.Galois.Descent

variable {X : Type*} [TopologicalSpace X]

/-- A map from the unit interval landing in `U`, as a path in `U`. -/
def liftU {U : Set X} (p : C(I, X)) (h : ∀ u, p u ∈ U) :
    Path (⟨p 0, h 0⟩ : U) ⟨p 1, h 1⟩ where
  toFun u := ⟨p u, h u⟩
  continuous_toFun := (map_continuous p).subtype_mk _
  source' := rfl
  target' := rfl

theorem conj_congr {Y : Type*} [TopologicalSpace Y] {x : Y} (c : ∀ y, Path x y)
    {a b a' b' : Y} (p : Path a b) (q : Path a' b') (h : ∀ u, p u = q u) :
    Path.Homotopic.Quotient.mk ((c a).trans (p.trans (c b).symm))
      = Path.Homotopic.Quotient.mk ((c a').trans (q.trans (c b').symm)) := by
  have ha : a = a' := by simpa using h 0
  have hb : b = b' := by simpa using h 1
  subst ha; subst hb
  rw [Path.ext (funext h)]

theorem conj_trans {Y : Type*} [TopologicalSpace Y] {x : Y} (c : ∀ y, Path x y) {a b d : Y}
    (p : Path a b) (q : Path b d) :
    FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((c a).trans ((p.trans q).trans (c d).symm)))
      = FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk ((c b).trans (q.trans (c d).symm)))
        * FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk ((c a).trans (p.trans (c b).symm))) := by
  show FundamentalGroup.fromPath _ = FundamentalGroup.fromPath
    ((Path.Homotopic.Quotient.mk ((c a).trans (p.trans (c b).symm))).trans
      (Path.Homotopic.Quotient.mk ((c b).trans (q.trans (c d).symm))))
  congr 1
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    PathQ.trans_assoc, PathQ.symm_trans_cancel]

theorem conj_refl {Y : Type*} [TopologicalSpace Y] {x : Y} (c : ∀ y, Path x y) (a : Y) :
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk ((c a).trans ((Path.refl a).trans (c a).symm))) = 1 := by
  show FundamentalGroup.fromPath _ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.refl x)
  congr 1
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.mk_refl, PathQ.refl_trans, PathQ.trans_symm]

variable {U : Set X} {x : X} {hx : x ∈ U} {H : Type*} [Group H]

open Classical in
/-- The value of a grid edge: the class of the edge conjugated back to the base point by the
connecting paths if the edge lies in `U`, and `1` otherwise. The inverse makes it multiplicative
in the order of concatenation. -/
noncomputable def Φ (ρ : FundamentalGroup U ⟨x, hx⟩ →* H) (c : ∀ y : U, Path ⟨x, hx⟩ y)
    (p : C(I, X)) : H :=
  if h : ∀ u, p u ∈ U then
    (ρ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((c _).trans ((liftU p h).trans (c _).symm)))))⁻¹
  else 1

section
variable (ρ : FundamentalGroup U ⟨x, hx⟩ →* H) (c : ∀ y : U, Path ⟨x, hx⟩ y)

theorem Φ_of_path {a b : U} (α : Path a b) :
    Φ ρ c (α.map continuous_subtype_val).toContinuousMap
      = (ρ (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk ((c a).trans (α.trans (c b).symm)))))⁻¹ := by
  have h : ∀ u, (α.map continuous_subtype_val).toContinuousMap u ∈ U := fun u => (α u).2
  rw [Φ, dite_eq_left_of_eq_true (eq_true h), conj_congr c (liftU _ h) α (fun u => rfl)]

theorem Φ_trans {a b d : U} (α : Path a b) (β : Path b d) :
    Φ ρ c ((α.trans β).map continuous_subtype_val).toContinuousMap
      = Φ ρ c (α.map continuous_subtype_val).toContinuousMap
        * Φ ρ c (β.map continuous_subtype_val).toContinuousMap := by
  rw [Φ_of_path, Φ_of_path, Φ_of_path, conj_trans, map_mul, mul_inv_rev]

theorem Φ_homotopic {a b : U} {α β : Path a b} (h : α.Homotopic β) :
    Φ ρ c (α.map continuous_subtype_val).toContinuousMap
      = Φ ρ c (β.map continuous_subtype_val).toContinuousMap := by
  have e : Path.Homotopic.Quotient.mk α = Path.Homotopic.Quotient.mk β := Quotient.sound h
  rw [Φ_of_path, Φ_of_path]
  simp only [Path.Homotopic.Quotient.mk_trans, e]

theorem Φ_refl (a : U) :
    Φ ρ c ((Path.refl a).map continuous_subtype_val).toContinuousMap = 1 := by
  rw [Φ_of_path, conj_refl, map_one, inv_one]

theorem Φ_eq_one {D : Set X}
    (hc : ∀ (y z : U) (β : Path y z), (∀ u, (β u : X) ∈ D) →
      ρ (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((c y).trans (β.trans (c z).symm)))) = 1)
    (p : C(I, X)) (hp : ∀ u, p u ∈ D) : Φ ρ c p = 1 := by
  unfold Φ
  split_ifs with h
  · rw [hc _ _ _ (fun u => hp u), inv_one]
  · rfl

end

/-- **Descent, kernel form.** A representation of `π₁(U)` that kills every loop conjugated from
a path inside `D` takes equal values on loops in `U` that are homotopic in `X = U ∪ D`. -/
theorem kernel_descent (U D : Set X) (hU : IsOpen U) (hD : IsOpen D)
    (hUD : ∀ y, y ∈ U ∨ y ∈ D) {x : X} (hx : x ∈ U) {H : Type*} [Group H]
    (ρ : FundamentalGroup U ⟨x, hx⟩ →* H) (c : ∀ y : U, Path ⟨x, hx⟩ y)
    (hc : ∀ (y z : U) (β : Path y z), (∀ u, (β u : X) ∈ D) →
      ρ (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((c y).trans (β.trans (c z).symm)))) = 1)
    (γ₀ γ₁ : Path (⟨x, hx⟩ : U) ⟨x, hx⟩)
    (h : (γ₀.map continuous_subtype_val).Homotopic (γ₁.map continuous_subtype_val)) :
    ρ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₀))
      = ρ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₁)) := by
  obtain ⟨F⟩ := h
  set cov : Bool → Set (I × I) := fun b => F ⁻¹' (cond b U D) with hcov_def
  have hopen : ∀ b, IsOpen (cov b) := by
    intro b; cases b
    exacts [hD.preimage F.continuous, hU.preimage F.continuous]
  have hcov : (univ : Set (I × I)) ⊆ ⋃ b, cov b := by
    intro s _
    rcases hUD (F s) with h | h
    exacts [mem_iUnion.2 ⟨true, h⟩, mem_iUnion.2 ⟨false, h⟩]
  obtain ⟨t, ht0, htm, ⟨N, htN⟩, hsq⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hopen hcov
  choose sel hsel using hsq
  have htN' : t N = 1 := htN N le_rfl
  have hcc : ∀ n (u : I), Icc.convexComb (t n) (t (n + 1)) u ∈ Icc (t n) (t (n + 1)) := by
    intro n u
    have hr : Icc.convexComb (t n) (t (n + 1)) u ∈ uIcc (t n) (t (n + 1)) := by
      rw [← Path.range_subpathAux]; exact ⟨u, rfl⟩
    rwa [uIcc_of_le (htm (Nat.le_succ n))] at hr
  have hlo : ∀ n, t n ∈ Icc (t n) (t (n + 1)) := fun n => ⟨le_rfl, htm (Nat.le_succ n)⟩
  have hhi : ∀ n, t (n + 1) ∈ Icc (t n) (t (n + 1)) := fun n => ⟨htm (Nat.le_succ n), le_rfl⟩
  -- the grid edges: `r i j` runs along row `t i`, `k i j` along column `t j`
  let r : ℕ → ℕ → C(I, X) := fun i j =>
    ⟨fun u => F (t i, Icc.convexComb (t j) (t (j + 1)) u),
      F.continuous.comp (continuous_const.prodMk (Icc.continuous_convexComb _ _))⟩
  let k : ℕ → ℕ → C(I, X) := fun i j =>
    ⟨fun u => F (Icc.convexComb (t i) (t (i + 1)) u, t j),
      F.continuous.comp ((Icc.continuous_convexComb _ _).prodMk continuous_const)⟩
  have hsqr : ∀ i j, Φ ρ c (r i j) * Φ ρ c (k i (j + 1))
      = Φ ρ c (k i j) * Φ ρ c (r (i + 1) j) := by
    intro i j
    cases hs : sel i j
    · have hmem : ∀ a ∈ Icc (t i) (t (i + 1)), ∀ b ∈ Icc (t j) (t (j + 1)), F (a, b) ∈ D := by
        intro a ha b hb
        have := hsel i j (Set.mk_mem_prod ha hb)
        simpa [hcov_def, hs] using this
      rw [Φ_eq_one ρ c hc (r i j) (fun u => hmem _ (hlo i) _ (hcc j u)),
        Φ_eq_one ρ c hc (k i (j + 1)) (fun u => hmem _ (hcc i u) _ (hhi j)),
        Φ_eq_one ρ c hc (k i j) (fun u => hmem _ (hcc i u) _ (hlo j)),
        Φ_eq_one ρ c hc (r (i + 1) j) (fun u => hmem _ (hhi i) _ (hcc j u))]
    · have hmem : ∀ a ∈ Icc (t i) (t (i + 1)), ∀ b ∈ Icc (t j) (t (j + 1)), F (a, b) ∈ U := by
        intro a ha b hb
        have := hsel i j (Set.mk_mem_prod ha hb)
        simpa [hcov_def, hs] using this
      let G : C(I × I, U) :=
        ⟨fun q => ⟨F (Icc.convexComb (t i) (t (i + 1)) q.1, Icc.convexComb (t j) (t (j + 1)) q.2),
          hmem _ (hcc i q.1) _ (hcc j q.2)⟩,
          (F.continuous.comp (((Icc.continuous_convexComb _ _).comp continuous_fst).prodMk
            ((Icc.continuous_convexComb _ _).comp continuous_snd))).subtype_mk _⟩
      let f0 : C(I, U) := ⟨fun b => G (0, b), G.continuous.comp (continuous_const.prodMk continuous_id)⟩
      let f1 : C(I, U) := ⟨fun b => G (1, b), G.continuous.comp (continuous_const.prodMk continuous_id)⟩
      let K : f0.Homotopy f1 :=
        { toFun := G
          continuous_toFun := G.continuous
          map_zero_left := fun _ => rfl
          map_one_left := fun _ => rfl }
      have e := Φ_homotopic ρ c (Path.Homotopic.map_trans_evalAt K Path.id)
      rw [Φ_trans, Φ_trans] at e
      have e1 : ((Path.id.map (map_continuous f0)).map continuous_subtype_val).toContinuousMap
          = r i j := by
        ext u; simp [r, G, f0]
      have e2 : ((K.evalAt 1).map continuous_subtype_val).toContinuousMap = k i (j + 1) := by
        ext u; show F (_, _) = F (_, _); rw [Icc.convexComb_one]
      have e3 : ((K.evalAt 0).map continuous_subtype_val).toContinuousMap = k i j := by
        ext u; show F (_, _) = F (_, _); rw [Icc.convexComb_zero]
      have e4 : ((Path.id.map (map_continuous f1)).map continuous_subtype_val).toContinuousMap
          = r (i + 1) j := by
        ext u; simp [r, G, f1]
      rwa [e1, e2, e3, e4] at e
  -- the two sides of the square are constant at the base point
  have hconst : ∀ j, t j = 0 ∨ t j = 1 → ∀ i, Φ ρ c (k i j) = 1 := by
    intro j hj i
    have : k i j = ((Path.refl (⟨x, hx⟩ : U)).map continuous_subtype_val).toContinuousMap := by
      ext u
      rcases hj with hj | hj
      · simp [k, hj]
      · simp [k, hj]
    rw [this, Φ_refl]
  have hside0 : ∀ i, Φ ρ c (k i 0) = 1 := hconst 0 (Or.inl ht0)
  have hsideN : ∀ i, Φ ρ c (k i N) = 1 := hconst N (Or.inr htN')
  -- row products
  let R : ℕ → ℕ → H := fun i n => ((List.range n).map fun j => Φ ρ c (r i j)).prod
  have htel : ∀ i n, R i n * Φ ρ c (k i n) = Φ ρ c (k i 0) * R (i + 1) n := by
    intro i n
    induction n with
    | zero => simp [R]
    | succ n ih =>
      show ((List.range (n + 1)).map fun j => Φ ρ c (r i j)).prod * Φ ρ c (k i (n + 1))
        = Φ ρ c (k i 0) * ((List.range (n + 1)).map fun j => Φ ρ c (r (i + 1) j)).prod
      rw [List.prod_range_succ, List.prod_range_succ, mul_assoc, hsqr, ← mul_assoc]
      erw [ih]
      rw [mul_assoc]
  have hrows : ∀ i, R i N = R 0 N := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      have := htel i N
      rw [hsideN, hside0, mul_one, one_mul] at this
      rw [← this, ih]
  -- a row that is a loop in `U`
  have hrow : ∀ i (γ : Path (⟨x, hx⟩ : U) ⟨x, hx⟩), (∀ s, F (t i, s) = γ s) →
      R i N = Φ ρ c (γ.map continuous_subtype_val).toContinuousMap := by
    intro i γ hγ
    have hn : ∀ n, R i n
        = Φ ρ c ((γ.subpath (t 0) (t n)).map continuous_subtype_val).toContinuousMap := by
      intro n
      induction n with
      | zero =>
        show 1 = _
        rw [Path.subpath_self, Φ_refl]
      | succ n ih =>
        show ((List.range (n + 1)).map fun j => Φ ρ c (r i j)).prod = _
        rw [List.prod_range_succ,
          show ((List.range n).map fun j => Φ ρ c (r i j)).prod = _ from ih]
        have er : r i n
            = ((γ.subpath (t n) (t (n + 1))).map continuous_subtype_val).toContinuousMap := by
          ext u; simp [r, hγ, Path.subpath]
        rw [er, ← Φ_trans]
        exact Φ_homotopic ρ c ⟨Path.Homotopy.subpathTransSubpath γ _ _ _⟩
    rw [hn N]
    congr 1
    ext u
    simp [Path.subpath, ht0, htN']
  have h0 := hrow 0 γ₀ (fun s => by rw [ht0]; simp)
  have h1 := hrow N γ₁ (fun s => by rw [htN']; simp)
  have hA := h0.symm.trans ((hrows N).symm.trans h1)
  rw [Φ_of_path, Φ_of_path, inv_inj] at hA
  have e : ∀ γ : Path (⟨x, hx⟩ : U) ⟨x, hx⟩,
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((c ⟨x, hx⟩).trans (γ.trans (c ⟨x, hx⟩).symm)))
      = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (c ⟨x, hx⟩).symm)
        * FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)
        * FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (c ⟨x, hx⟩)) := fun γ => rfl
  rw [e, e, map_mul, map_mul, map_mul, map_mul] at hA
  exact mul_left_cancel (mul_right_cancel hA)
end Sz8.Galois.Descent
