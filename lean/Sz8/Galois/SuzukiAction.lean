import Sz8.Galois.Suzuki
import Mathlib.Tactic.LinearCombination

/-!
# The action of `Sz(8)` on the ovoid

* Normalization: `normalize (a • v) = normalize v` (`a ≠ 0`), and `normalize v = c • v` with `c ≠ 0`.
* `ov i`: the ovoid point with label `i`; nonzero, normalized, injective.
* `PresSub`: elements of `SL₄(𝔽₈)` mapping every ovoid point (after normalization) to an ovoid point;
  `ψ : PresSub →* Perm (Fin 65)`.
* `ψ_injective`: only the identity fixes the frame `ov 0, ov 29, ov 30, ov 50, ov 49`
  (`(0,0,0,1), (1,0,0,0), (1,0,1,1), (1,1,0,1)` and their sum `(1,1,1,1)`): a matrix fixing their projective
  points is a scalar `μ`, and `μ⁴ = det = 1` means `θ8 μ = θ8 1`.
-/

namespace Sz8.Galois.Suzuki

open Matrix

/-! ## Normalization -/

theorem normalize_smul {a : F8} (ha : a ≠ 0) (v : Fin 4 → F8) : normalize (a • v) = normalize v := by
  unfold normalize
  simp only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, ha, false_or]
  split_ifs <;> (ext k; simp only [Pi.smul_apply, smul_eq_mul]; field_simp)

theorem normalize_eq_smul {v : Fin 4 → F8} (hv : v ≠ 0) : ∃ c : F8, c ≠ 0 ∧ normalize v = c • v := by
  unfold normalize
  split_ifs with h0 h1 h2
  · exact ⟨_, inv_ne_zero h0, rfl⟩
  · exact ⟨_, inv_ne_zero h1, rfl⟩
  · exact ⟨_, inv_ne_zero h2, rfl⟩
  · refine ⟨_, inv_ne_zero fun h3 => hv ?_, rfl⟩
    push Not at h0 h1 h2
    funext k; fin_cases k <;> simp [h0, h1, h2, h3]

/-! ## The labelled ovoid -/

/-- The ovoid point with label `i`. -/
def ov (i : Fin 65) : Fin 4 → F8 := ovoid.getD i 0

theorem ov_checks : ∀ i : Fin 65, veq (ov i) 0 = false ∧ veq (normalize (ov i)) (ov i) = true := by
  decide +kernel

theorem ov_ne_zero (i : Fin 65) : ov i ≠ 0 := fun h => by
  have := (ov_checks i).1; rw [h] at this; simp [veq] at this

theorem normalize_ov (i : Fin 65) : normalize (ov i) = ov i := (veq_iff _ _).1 (ov_checks i).2

theorem ov_injective : Function.Injective ov := by
  intro i j h
  have hlen : ovoid.length = 65 := ovoid_card.2
  have hi : i.val < ovoid.length := by rw [hlen]; exact i.isLt
  have hj : j.val < ovoid.length := by rw [hlen]; exact j.isLt
  simp only [ov, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.getD_some] at h
  exact Fin.ext ((List.Nodup.getElem_inj_iff ovoid_card.1).1 h)

/-! ## Frame: a matrix fixing five projective points is a scalar -/

theorem eq_scalar_of_frame (A : Matrix (Fin 4) (Fin 4) F8) (l0 l1 l2 l9 l10 : F8)
    (h0 : A *ᵥ ![0, 0, 0, 1] = l0 • ![0, 0, 0, 1]) (h1 : A *ᵥ ![1, 0, 0, 0] = l1 • ![1, 0, 0, 0])
    (h2 : A *ᵥ ![1, 0, 1, 1] = l2 • ![1, 0, 1, 1]) (h9 : A *ᵥ ![1, 1, 0, 1] = l9 • ![1, 1, 0, 1])
    (h10 : A *ᵥ ![1, 1, 1, 1] = l10 • ![1, 1, 1, 1]) : A = l10 • 1 := by
  have key : ∀ (a b c d l : F8), A *ᵥ ![a, b, c, d] = l • ![a, b, c, d] →
      (A 0 0 * a + A 0 1 * b + A 0 2 * c + A 0 3 * d = l * a) ∧
      (A 1 0 * a + A 1 1 * b + A 1 2 * c + A 1 3 * d = l * b) ∧
      (A 2 0 * a + A 2 1 * b + A 2 2 * c + A 2 3 * d = l * c) ∧
      (A 3 0 * a + A 3 1 * b + A 3 2 * c + A 3 3 * d = l * d) := fun a b c d l h => by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> [have := congrFun h 0; have := congrFun h 1; have := congrFun h 2;
      have := congrFun h 3] <;> simpa [mulVec, dotProduct, Fin.sum_univ_four] using this
  obtain ⟨h0_0, h0_1, h0_2, h0_3⟩ := key _ _ _ _ _ h0
  obtain ⟨h1_0, h1_1, h1_2, h1_3⟩ := key _ _ _ _ _ h1
  obtain ⟨h2_0, h2_1, h2_2, h2_3⟩ := key _ _ _ _ _ h2
  obtain ⟨h9_0, h9_1, h9_2, h9_3⟩ := key _ _ _ _ _ h9
  obtain ⟨h10_0, h10_1, h10_2, h10_3⟩ := key _ _ _ _ _ h10
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Fin.reduceEq, ↓reduceIte, mul_one, mul_zero]
  · linear_combination -h0_0 + h0_1 + h0_2 + h1_1 + h1_2 + h2_0 - h2_1 - h2_2 + h9_0 - h9_1 - h9_2 - h10_0 + h10_1 + h10_2
  · linear_combination -h0_2 - h1_2 - h2_0 + h2_2 + h9_2 + h10_0 - h10_2
  · linear_combination -h0_1 - h1_1 + h2_1 - h9_0 + h9_1 + h10_0 - h10_1
  · linear_combination h0_0
  · linear_combination h1_1
  · linear_combination -h2_1 + h10_1
  · linear_combination -h0_1 - h1_1 + h2_1
  · linear_combination h0_1
  · linear_combination h1_2
  · linear_combination -h0_2 - h1_2 + h9_2
  · linear_combination -h9_2 + h10_2
  · linear_combination h0_2
  · linear_combination h1_3
  · linear_combination -h0_2 - h1_2 + h2_2 - h2_3 + h9_2 - h10_2 + h10_3
  · linear_combination -h0_1 - h1_1 + h2_1 + h9_1 - h9_3 - h10_1 + h10_3
  · linear_combination h0_1 + h0_2 + h1_1 + h1_2 - h1_3 - h2_1 - h2_2 + h2_3 - h9_1 - h9_2 + h9_3 + h10_1 + h10_2 - h10_3

/-! ## Normalization along a matrix -/

theorem eq_smul_normalize {v : Fin 4 → F8} (hv : v ≠ 0) : ∃ c : F8, c ≠ 0 ∧ v = c • normalize v := by
  obtain ⟨c, hc, h⟩ := normalize_eq_smul hv
  exact ⟨c⁻¹, inv_ne_zero hc, by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem normalize_eq_normalize {v w : Fin 4 → F8} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : normalize v = normalize w) : ∃ c : F8, c ≠ 0 ∧ v = c • w := by
  obtain ⟨a, ha, hva⟩ := normalize_eq_smul hv
  obtain ⟨b, hb, hwb⟩ := normalize_eq_smul hw
  refine ⟨a⁻¹ * b, mul_ne_zero (inv_ne_zero ha) hb, ?_⟩
  rw [h, hwb] at hva
  rw [mul_smul, hva, smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- `SL₄(𝔽₈)` acting on column vectors. -/
local notation "SL" => Matrix.SpecialLinearGroup (Fin 4) F8

theorem sl_mulVec_inv (g : SL) (v : Fin 4 → F8) : (↑g⁻¹ : Matrix (Fin 4) (Fin 4) F8) *ᵥ (↑g *ᵥ v) = v := by
  rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mulVec]

theorem sl_mulVec_inv' (g : SL) (v : Fin 4 → F8) : (↑g : Matrix (Fin 4) (Fin 4) F8) *ᵥ (↑g⁻¹ *ᵥ v) = v := by
  simpa using sl_mulVec_inv g⁻¹ v

theorem sl_mulVec_ne_zero (g : SL) {v : Fin 4 → F8} (hv : v ≠ 0) : (↑g : Matrix (Fin 4) (Fin 4) F8) *ᵥ v ≠ 0 :=
  fun h => hv (by rw [← sl_mulVec_inv g v, h, mulVec_zero])

theorem normalize_mulVec_normalize (g : SL) {v : Fin 4 → F8} (hv : v ≠ 0) :
    normalize ((↑g : Matrix (Fin 4) (Fin 4) F8) *ᵥ normalize v) = normalize (↑g *ᵥ v) := by
  obtain ⟨c, hc, h⟩ := normalize_eq_smul hv
  rw [h, mulVec_smul, normalize_smul hc]

/-! ## Elements preserving the ovoid -/

/-- `g` maps every labelled ovoid point to a labelled ovoid point. -/
def Pres (g : SL) : Prop := ∀ i, ∃ j, normalize ((↑g : Matrix (Fin 4) (Fin 4) F8) *ᵥ ov i) = ov j

theorem Pres.one : Pres 1 := fun i => ⟨i, by simp [normalize_ov]⟩

theorem Pres.mul {g h : SL} (hg : Pres g) (hh : Pres h) : Pres (g * h) := fun i => by
  obtain ⟨j, hj⟩ := hh i
  obtain ⟨k, hk⟩ := hg j
  refine ⟨k, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ← normalize_mulVec_normalize g
    (sl_mulVec_ne_zero h (ov_ne_zero i)), hj, hk]

theorem Pres.inv {g : SL} (hg : Pres g) : Pres g⁻¹ := by
  classical
  let f : Fin 65 → Fin 65 := fun i => (hg i).choose
  have hf : ∀ i, normalize ((↑g : Matrix (Fin 4) (Fin 4) F8) *ᵥ ov i) = ov (f i) := fun i => (hg i).choose_spec
  have hinj : Function.Injective f := by
    intro i i' hii
    have e : normalize ((↑g : Matrix (Fin 4) (Fin 4) F8) *ᵥ ov i) = normalize (↑g *ᵥ ov i') := by
      rw [hf, hf, hii]
    obtain ⟨c, _, hc⟩ := normalize_eq_normalize (sl_mulVec_ne_zero g (ov_ne_zero i))
      (sl_mulVec_ne_zero g (ov_ne_zero i')) e
    have hc' : ov i = c • ov i' := by
      rw [← sl_mulVec_inv g (ov i), hc, mulVec_smul, sl_mulVec_inv]
    apply ov_injective
    rw [← normalize_ov i, ← normalize_ov i', hc']
    exact normalize_smul (fun h0 => ov_ne_zero i (by rw [hc', h0, zero_smul])) _
  have hsurj := Finite.injective_iff_surjective.1 hinj
  intro i
  obtain ⟨j, hj⟩ := hsurj i
  refine ⟨j, ?_⟩
  have e := hf j
  rw [hj] at e
  obtain ⟨c, hc, hcv⟩ := eq_smul_normalize (sl_mulVec_ne_zero g (ov_ne_zero j))
  rw [e] at hcv
  have : ov j = c • ((↑g⁻¹ : Matrix (Fin 4) (Fin 4) F8) *ᵥ ov i) := by
    rw [← sl_mulVec_inv g (ov j), hcv, mulVec_smul]
  rw [← normalize_ov j, this, normalize_smul hc]

/-- The stabilizer of the ovoid in `SL₄(𝔽₈)`. -/
def PresSub : Subgroup SL where
  carrier := {g | Pres g}
  one_mem' := Pres.one
  mul_mem' := Pres.mul
  inv_mem' := Pres.inv

/-- The label of the image of `ov i`. -/
noncomputable def σ (g : PresSub) (i : Fin 65) : Fin 65 := (g.2 i).choose

theorem σ_spec (g : PresSub) (i : Fin 65) :
    normalize ((↑(g : SL) : Matrix (Fin 4) (Fin 4) F8) *ᵥ ov i) = ov (σ g i) := (g.2 i).choose_spec

theorem σ_eq {g : PresSub} {i j : Fin 65}
    (h : normalize ((↑(g : SL) : Matrix (Fin 4) (Fin 4) F8) *ᵥ ov i) = ov j) : σ g i = j :=
  ov_injective (by rw [← σ_spec, h])

theorem σ_mul (g h : PresSub) (i : Fin 65) : σ (g * h) i = σ g (σ h i) := by
  apply σ_eq
  rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec,
    ← normalize_mulVec_normalize _ (sl_mulVec_ne_zero _ (ov_ne_zero i)), σ_spec, σ_spec]

theorem σ_one (i : Fin 65) : σ 1 i = i := σ_eq (by simp [normalize_ov])

/-- **The action homomorphism** of the ovoid stabilizer on the 65 labels. -/
noncomputable def ψ : PresSub →* Equiv.Perm (Fin 65) where
  toFun g := ⟨σ g, σ g⁻¹, fun i => by rw [← σ_mul, inv_mul_cancel, σ_one],
    fun i => by rw [← σ_mul, mul_inv_cancel, σ_one]⟩
  map_one' := Equiv.ext σ_one
  map_mul' g h := Equiv.ext (σ_mul g h)

theorem ψ_apply (g : PresSub) (i : Fin 65) : ψ g i = σ g i := rfl

/-- Generator image equations reduce to this. -/
theorem ψ_eq_of {g : PresSub} {p : Equiv.Perm (Fin 65)}
    (h : ∀ i, normalize ((↑(g : SL) : Matrix (Fin 4) (Fin 4) F8) *ᵥ ov i) = ov (p i)) : ψ g = p :=
  Equiv.ext fun i => σ_eq (h i)

/-! ## Injectivity -/

theorem frame_ov : ov 0 = ![0, 0, 0, 1] ∧ ov 29 = ![1, 0, 0, 0] ∧ ov 30 = ![1, 0, 1, 1] ∧
    ov 50 = ![1, 1, 0, 1] ∧ ov 49 = ![1, 1, 1, 1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact (veq_iff _ _).1 (by decide +kernel)

theorem θ8_injective : Function.Injective θ8 := θ8.injective

theorem ψ_injective : Function.Injective ψ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have fix : ∀ i, ∃ c : F8, (↑(g : SL) : Matrix (Fin 4) (Fin 4) F8) *ᵥ ov i = c • ov i := fun i => by
    have e := σ_spec g i
    rw [← ψ_apply, hg, Equiv.Perm.coe_one, id] at e
    obtain ⟨c, -, hc⟩ := eq_smul_normalize (sl_mulVec_ne_zero (g : SL) (ov_ne_zero i))
    exact ⟨c, by rw [hc, e]⟩
  obtain ⟨h0, h1, h2, h9, h10⟩ := frame_ov
  obtain ⟨l0, e0⟩ := fix 0
  obtain ⟨l1, e1⟩ := fix 29
  obtain ⟨l2, e2⟩ := fix 30
  obtain ⟨l9, e9⟩ := fix 50
  obtain ⟨l10, e10⟩ := fix 49
  rw [h0] at e0; rw [h1] at e1; rw [h2] at e2; rw [h9] at e9; rw [h10] at e10
  have hA := eq_scalar_of_frame _ l0 l1 l2 l9 l10 e0 e1 e2 e9 e10
  have hdet := (g : SL).2
  rw [hA, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at hdet
  have hl : l10 = 1 := θ8_injective (by rw [map_one]; exact hdet)
  apply Subtype.ext
  apply Subtype.ext
  rw [hA, hl, one_smul]
  rfl

end Sz8.Galois.Suzuki
