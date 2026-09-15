import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Data.Matrix.Mul

/-!
# Suzuki's group `Sz(q)` and the computable field of order 8

* `F8`: the field `𝔽₂[z]/(z³ + z + 1)` on 8 explicit elements (bit patterns `c₀ + c₁ z + c₂ z²`), with
  operation tables; every ring and field axiom is a kernel check over all elements.
* `θ8 : F8 →+* F8`, `x ↦ x⁴`, with `θ8 (θ8 x) = x²`.
-/

namespace Sz8.Galois.Suzuki

/-- The field with 8 elements, as bit patterns in the basis `1, z, z²` with `z³ = z + 1`. -/
structure F8 where
  v : Fin 8
deriving DecidableEq

namespace F8

def equivFin : F8 ≃ Fin 8 := ⟨F8.v, F8.mk, fun _ => rfl, fun _ => rfl⟩

instance : Fintype F8 := Fintype.ofEquiv (Fin 8) equivFin.symm

/-- Packed tables: entry `(a, b)` of the multiplication table is digit `8a + b` in base 8. -/
def mulP : ℕ := 2821848294356612419217921029917578219971947684264937521152
def invP : ℕ := 9272648

def addT (a b : Fin 8) : Fin 8 := ⟨(a.val ^^^ b.val) % 8, Nat.mod_lt _ (by norm_num)⟩
def mulT (a b : Fin 8) : Fin 8 := ⟨(mulP >>> (3 * (8 * a.val + b.val))) % 8, Nat.mod_lt _ (by norm_num)⟩
def invT (a : Fin 8) : Fin 8 := ⟨(invP >>> (3 * a.val)) % 8, Nat.mod_lt _ (by norm_num)⟩

instance : Zero F8 := ⟨⟨0⟩⟩
instance : One F8 := ⟨⟨1⟩⟩
instance : Add F8 := ⟨fun a b => ⟨addT a.v b.v⟩⟩
instance : Neg F8 := ⟨fun a => a⟩
instance : Sub F8 := ⟨fun a b => ⟨addT a.v b.v⟩⟩
instance : Mul F8 := ⟨fun a b => ⟨mulT a.v b.v⟩⟩
instance : Inv F8 := ⟨fun a => ⟨invT a.v⟩⟩

theorem add_assoc' : ∀ a b c : F8, a + b + c = a + (b + c) := by decide +kernel
theorem zero_add' : ∀ a : F8, 0 + a = a := by decide +kernel
theorem add_zero' : ∀ a : F8, a + 0 = a := by decide +kernel
theorem add_comm' : ∀ a b : F8, a + b = b + a := by decide +kernel
theorem neg_add_cancel' : ∀ a : F8, -a + a = 0 := by decide +kernel
theorem sub_eq_add_neg' : ∀ a b : F8, a - b = a + -b := by decide +kernel
theorem mul_assoc' : ∀ a b c : F8, a * b * c = a * (b * c) := by decide +kernel
theorem one_mul' : ∀ a : F8, 1 * a = a := by decide +kernel
theorem mul_one' : ∀ a : F8, a * 1 = a := by decide +kernel
theorem mul_comm' : ∀ a b : F8, a * b = b * a := by decide +kernel
theorem zero_mul' : ∀ a : F8, 0 * a = 0 := by decide +kernel
theorem mul_zero' : ∀ a : F8, a * 0 = 0 := by decide +kernel
theorem left_distrib' : ∀ a b c : F8, a * (b + c) = a * b + a * c := by decide +kernel
theorem right_distrib' : ∀ a b c : F8, (a + b) * c = a * c + b * c := by decide +kernel
theorem mul_inv_cancel' : ∀ a : F8, a ≠ 0 → a * a⁻¹ = 1 := by decide +kernel
theorem inv_zero' : (0 : F8)⁻¹ = 0 := by decide +kernel

instance : CommRing F8 where
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero := add_zero'
  add_comm := add_comm'
  neg_add_cancel := neg_add_cancel'
  sub_eq_add_neg := sub_eq_add_neg'
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  mul_comm := mul_comm'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Nontrivial F8 := ⟨⟨0, 1, by decide +kernel⟩⟩

instance : Field F8 where
  __ := (inferInstance : CommRing F8)
  inv := fun a => ⟨invT a.v⟩
  exists_pair_ne := ⟨0, 1, by decide +kernel⟩
  mul_inv_cancel := mul_inv_cancel'
  inv_zero := inv_zero'
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end F8

/-- `x ↦ x⁴`, the square root of the Frobenius: `θ8 (θ8 x) = x²`. -/
def θ8 : F8 →+* F8 where
  toFun x := x ^ 4
  map_one' := by decide +kernel
  map_mul' := by decide +kernel
  map_zero' := by decide +kernel
  map_add' := by decide +kernel

theorem θ8_sq : ∀ x : F8, θ8 (θ8 x) = x ^ 2 := by decide +kernel

/-! ## Suzuki's group over a field with a square root of the Frobenius -/

section Generic

open Matrix

variable {F : Type*} [Field F] (θ : F →+* F)

/-- Suzuki's lower unitriangular matrices `T(a, b)`. -/
def Tmat (a b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; a, 1, 0, 0; b, θ a, 1, 0; a ^ 2 * θ a + a * b + θ b, a * θ a + b, a, 1]

/-- Suzuki's diagonal matrices `M(κ)`. -/
def Mmat (κ : F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.diagonal ![κ * θ κ, κ, κ⁻¹, (κ * θ κ)⁻¹]

/-- The antidiagonal involution `W`. -/
def Wmat : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

theorem det_Tmat (a b : F) : (Tmat θ a b).det = 1 := by
  simp [Tmat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

theorem det_Mmat {κ : F} (hκ : κ ≠ 0) : (Mmat θ κ).det = 1 := by
  have hθ : θ κ ≠ 0 := (map_ne_zero θ).2 hκ
  simp [Mmat, Matrix.det_diagonal, Fin.prod_univ_succ]
  field_simp

theorem det_Wmat : (Wmat : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [Wmat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num

def T (a b : F) : Matrix.SpecialLinearGroup (Fin 4) F := ⟨Tmat θ a b, det_Tmat θ a b⟩
def M (κ : Fˣ) : Matrix.SpecialLinearGroup (Fin 4) F := ⟨Mmat θ κ, det_Mmat θ κ.ne_zero⟩
def W : Matrix.SpecialLinearGroup (Fin 4) F := ⟨Wmat, det_Wmat⟩

/-- **Suzuki's group** `⟨T(a, b), M(κ), W⟩ ≤ SL₄(F)`. For `F = 𝔽_q`, `q = 2^(2n+1)`, and `θ` the
automorphism with `θ² = Frobenius`, this is `Sz(q)` (Suzuki 1962; Wilson, *The Finite Simple Groups*,
§4.2). -/
def Suzuki : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F) :=
  Subgroup.closure (Set.range (fun p : F × F => T θ p.1 p.2) ∪ Set.range (M θ) ∪ {W})

end Generic

/-! ## The ovoid for `q = 8` -/

open Matrix

/-- Scale a nonzero vector so that its first nonzero coordinate is `1`. -/
def normalize (v : Fin 4 → F8) : Fin 4 → F8 :=
  if v 0 ≠ 0 then (v 0)⁻¹ • v else if v 1 ≠ 0 then (v 1)⁻¹ • v else
    if v 2 ≠ 0 then (v 2)⁻¹ • v else (v 3)⁻¹ • v

/-- The Suzuki–Tits ovoid: the orbit of `⟨e₄⟩`, 65 normalized points, listed so that position `i` is
the point with label `i` in the permutation group `N` (`galois/suzuki.py`). -/
def ovoid : List (Fin 4 → F8) :=
  [![⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩],
    ![⟨1⟩, ⟨7⟩, ⟨7⟩, ⟨2⟩],
    ![⟨1⟩, ⟨7⟩, ⟨6⟩, ⟨4⟩],
    ![⟨1⟩, ⟨2⟩, ⟨1⟩, ⟨6⟩],
    ![⟨1⟩, ⟨2⟩, ⟨0⟩, ⟨5⟩],
    ![⟨1⟩, ⟨1⟩, ⟨7⟩, ⟨3⟩],
    ![⟨1⟩, ⟨1⟩, ⟨6⟩, ⟨3⟩],
    ![⟨1⟩, ⟨7⟩, ⟨5⟩, ⟨1⟩],
    ![⟨1⟩, ⟨7⟩, ⟨4⟩, ⟨7⟩],
    ![⟨1⟩, ⟨6⟩, ⟨2⟩, ⟨2⟩],
    ![⟨1⟩, ⟨6⟩, ⟨3⟩, ⟨5⟩],
    ![⟨1⟩, ⟨3⟩, ⟨0⟩, ⟨6⟩],
    ![⟨1⟩, ⟨3⟩, ⟨1⟩, ⟨4⟩],
    ![⟨1⟩, ⟨5⟩, ⟨6⟩, ⟨5⟩],
    ![⟨1⟩, ⟨5⟩, ⟨7⟩, ⟨1⟩],
    ![⟨1⟩, ⟨6⟩, ⟨7⟩, ⟨2⟩],
    ![⟨1⟩, ⟨6⟩, ⟨6⟩, ⟨5⟩],
    ![⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨2⟩],
    ![⟨1⟩, ⟨0⟩, ⟨5⟩, ⟨3⟩],
    ![⟨1⟩, ⟨5⟩, ⟨4⟩, ⟨2⟩],
    ![⟨1⟩, ⟨5⟩, ⟨5⟩, ⟨6⟩],
    ![⟨1⟩, ⟨7⟩, ⟨1⟩, ⟨2⟩],
    ![⟨1⟩, ⟨7⟩, ⟨0⟩, ⟨4⟩],
    ![⟨1⟩, ⟨5⟩, ⟨2⟩, ⟨5⟩],
    ![⟨1⟩, ⟨5⟩, ⟨3⟩, ⟨1⟩],
    ![⟨1⟩, ⟨1⟩, ⟨2⟩, ⟨5⟩],
    ![⟨1⟩, ⟨1⟩, ⟨3⟩, ⟨5⟩],
    ![⟨1⟩, ⟨1⟩, ⟨4⟩, ⟨7⟩],
    ![⟨1⟩, ⟨1⟩, ⟨5⟩, ⟨7⟩],
    ![⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩],
    ![⟨1⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩],
    ![⟨1⟩, ⟨3⟩, ⟨5⟩, ⟨1⟩],
    ![⟨1⟩, ⟨3⟩, ⟨4⟩, ⟨3⟩],
    ![⟨1⟩, ⟨4⟩, ⟨2⟩, ⟨2⟩],
    ![⟨1⟩, ⟨4⟩, ⟨3⟩, ⟨7⟩],
    ![⟨1⟩, ⟨0⟩, ⟨6⟩, ⟨4⟩],
    ![⟨1⟩, ⟨0⟩, ⟨7⟩, ⟨5⟩],
    ![⟨1⟩, ⟨2⟩, ⟨2⟩, ⟨7⟩],
    ![⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩],
    ![⟨1⟩, ⟨2⟩, ⟨7⟩, ⟨5⟩],
    ![⟨1⟩, ⟨2⟩, ⟨6⟩, ⟨6⟩],
    ![⟨1⟩, ⟨3⟩, ⟨2⟩, ⟨6⟩],
    ![⟨1⟩, ⟨3⟩, ⟨3⟩, ⟨4⟩],
    ![⟨1⟩, ⟨0⟩, ⟨2⟩, ⟨6⟩],
    ![⟨1⟩, ⟨0⟩, ⟨3⟩, ⟨7⟩],
    ![⟨1⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩],
    ![⟨1⟩, ⟨4⟩, ⟨4⟩, ⟨3⟩],
    ![⟨1⟩, ⟨2⟩, ⟨5⟩, ⟨7⟩],
    ![⟨1⟩, ⟨2⟩, ⟨4⟩, ⟨4⟩],
    ![⟨1⟩, ⟨1⟩, ⟨1⟩, ⟨1⟩],
    ![⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨1⟩],
    ![⟨1⟩, ⟨5⟩, ⟨0⟩, ⟨2⟩],
    ![⟨1⟩, ⟨5⟩, ⟨1⟩, ⟨6⟩],
    ![⟨1⟩, ⟨6⟩, ⟨1⟩, ⟨4⟩],
    ![⟨1⟩, ⟨6⟩, ⟨0⟩, ⟨3⟩],
    ![⟨1⟩, ⟨4⟩, ⟨1⟩, ⟨2⟩],
    ![⟨1⟩, ⟨4⟩, ⟨0⟩, ⟨7⟩],
    ![⟨1⟩, ⟨4⟩, ⟨7⟩, ⟨3⟩],
    ![⟨1⟩, ⟨4⟩, ⟨6⟩, ⟨6⟩],
    ![⟨1⟩, ⟨7⟩, ⟨3⟩, ⟨1⟩],
    ![⟨1⟩, ⟨7⟩, ⟨2⟩, ⟨7⟩],
    ![⟨1⟩, ⟨6⟩, ⟨5⟩, ⟨3⟩],
    ![⟨1⟩, ⟨6⟩, ⟨4⟩, ⟨4⟩],
    ![⟨1⟩, ⟨3⟩, ⟨6⟩, ⟨3⟩],
    ![⟨1⟩, ⟨3⟩, ⟨7⟩, ⟨1⟩]]

/-- Matrix–vector product with the four coordinates written out. -/
def mv (A : Matrix (Fin 4) (Fin 4) F8) (v : Fin 4 → F8) : Fin 4 → F8 :=
  fun i => A i 0 * v 0 + A i 1 * v 1 + A i 2 * v 2 + A i 3 * v 3

theorem mv_eq (A : Matrix (Fin 4) (Fin 4) F8) (v : Fin 4 → F8) : mv A v = A *ᵥ v := by
  funext i; simp [mv, mulVec, dotProduct, Fin.sum_univ_four]

/-- Coordinatewise equality test. -/
def veq (v w : Fin 4 → F8) : Bool := v 0 == w 0 && v 1 == w 1 && v 2 == w 2 && v 3 == w 3

theorem veq_iff (v w : Fin 4 → F8) : veq v w = true ↔ v = w := by
  constructor
  · intro h
    simp only [veq, Bool.and_eq_true, beq_iff_eq] at h
    funext i; fin_cases i <;> simp [h]
  · rintro rfl; simp [veq]

def memB (v : Fin 4 → F8) (l : List (Fin 4 → F8)) : Bool := l.any (veq v)

theorem memB_iff (v : Fin 4 → F8) (l : List (Fin 4 → F8)) : memB v l = true ↔ v ∈ l := by
  simp only [memB, List.any_eq_true, veq_iff]
  exact ⟨fun ⟨w, hw, h⟩ => h ▸ hw, fun h => ⟨v, h, rfl⟩⟩

def allF8 : List F8 := [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩]

theorem mem_allF8 (x : F8) : x ∈ allF8 := by
  rcases x with ⟨x⟩; fin_cases x <;> simp [allF8]

/-- The stability check for one point. -/
def stableAt (p : Fin 4 → F8) : Bool :=
    (allF8.all fun a => allF8.all fun b => memB (normalize (mv (Tmat θ8 a b) p)) ovoid) &&
    (allF8.all fun κ => κ == 0 || memB (normalize (mv (Mmat θ8 κ) p)) ovoid) &&
    memB (normalize (mv Wmat p)) ovoid

theorem stable0 : ∀ i : Fin 65, 0 ≤ i.val → i.val < 13 →
    stableAt (ovoid.getD i 0) = true := by decide +kernel
theorem stable1 : ∀ i : Fin 65, 13 ≤ i.val → i.val < 26 →
    stableAt (ovoid.getD i 0) = true := by decide +kernel
theorem stable2 : ∀ i : Fin 65, 26 ≤ i.val → i.val < 39 →
    stableAt (ovoid.getD i 0) = true := by decide +kernel
theorem stable3 : ∀ i : Fin 65, 39 ≤ i.val → i.val < 52 →
    stableAt (ovoid.getD i 0) = true := by decide +kernel
theorem stable4 : ∀ i : Fin 65, 52 ≤ i.val → i.val < 65 →
    stableAt (ovoid.getD i 0) = true := by decide +kernel

theorem stable_all (i : Fin 65) : stableAt (ovoid.getD i 0) = true := by
  have h := i.isLt
  rcases Nat.lt_or_ge i.val 13 with h0 | h0
  · exact stable0 i (Nat.zero_le _) h0
  rcases Nat.lt_or_ge i.val 26 with h1 | h1
  · exact stable1 i h0 h1
  rcases Nat.lt_or_ge i.val 39 with h2 | h2
  · exact stable2 i h1 h2
  rcases Nat.lt_or_ge i.val 52 with h3 | h3
  · exact stable3 i h2 h3
  · exact stable4 i h3 h

/-- Pairwise distinctness as one Boolean computation. -/
def distinctB : List (Fin 4 → F8) → Bool
  | [] => true
  | v :: vs => !memB v vs && distinctB vs

theorem distinctB_true : distinctB ovoid = true := by decide +kernel

theorem nodup_of_distinctB : ∀ l : List (Fin 4 → F8), distinctB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | v :: vs, h => by
    simp only [distinctB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨fun hv => ?_, nodup_of_distinctB vs h.2⟩
    have := (memB_iff v vs).2 hv
    rw [h.1] at this; exact Bool.false_ne_true this

/-- The ovoid has 65 distinct points. -/
theorem ovoid_card : ovoid.Nodup ∧ ovoid.length = 65 :=
  ⟨nodup_of_distinctB _ distinctB_true, by decide +kernel⟩

/-- Every generator of `Sz(8)` maps the ovoid into itself. -/
theorem ovoid_stable : ∀ p ∈ ovoid,
    (∀ a b : F8, normalize (Tmat θ8 a b *ᵥ p) ∈ ovoid) ∧
    (∀ κ : F8, κ ≠ 0 → normalize (Mmat θ8 κ *ᵥ p) ∈ ovoid) ∧
    normalize (Wmat *ᵥ p) ∈ ovoid := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hlen : ovoid.length = 65 := by decide +kernel
  have h := stable_all ⟨i, hlen ▸ hi⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h
  simp only [stableAt] at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hT, hM⟩, hW⟩ := h
  refine ⟨fun a b => ?_, fun κ hκ => ?_, ?_⟩
  · rw [← mv_eq]; exact (memB_iff _ _).1 (hT a (mem_allF8 a) b (mem_allF8 b))
  · rw [← mv_eq]; exact (memB_iff _ _).1 ((hM κ (mem_allF8 κ)).resolve_left hκ)
  · rw [← mv_eq]; exact (memB_iff _ _).1 hW

end Sz8.Galois.Suzuki
