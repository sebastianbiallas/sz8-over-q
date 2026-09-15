import Sz8.Monodromy.StepCheck
import Sz8.Galois.PackedWitness
import Mathlib.Data.List.GetD

/-!
# The integer model `F̃ = 13^182 f` and its reductions

Anchor: `Sz8.Monodromy.paperFamily_eq_famPoly`, `paperFamily t = 13^(-182) · famPoly intCols t`, whose
certificate `intCols_match` also checks that the Gaussian-integer columns are real.

* `Ftil ∈ ℤ[t][X]` is built from the real parts of `intCols`; `P_eq_Ftil`:
  `paperMonicFamily.P t = C (L⁻¹) · F̃(t, ·)` with `L = 13^182`.
* `Ftil_natDegree`, `Ftil_leadingCoeff`: degree 65 in `X`, leading coefficient the constant `L`.
* `Fpack p`, `Gpack p`: the reductions of `F̃` and `F̃_X` modulo `p`, packed in the layout of
  `Sz8.Galois.PackedWitness`, **computed in the kernel from `intCols`**; `hF`, `hG` are then
  theorems (`Ftil_reduce`, `Ftil_derivative_reduce`), not hypotheses.
* Scaling, once: `Res(F̃_t, F̃_t') = L^129 · Res(f_t, f_t')` and `B(F̃_t, F̃_t') = L^128 · B(f_t, f_t')`.
-/

open Polynomial

set_option maxRecDepth 100000

namespace Sz8.Galois.FLink

open Sz8.Monodromy Sz8.Monodromy.GaussPoly Packed FixedMinor

/-! ### `F̃` -/

/-- Real parts of a column, as a polynomial in `X` over `ℤ[t]` (constant in `t`). -/
noncomputable def zPoly : List GI → ℤ[X][X]
  | [] => 0
  | a :: as => C (C a.1) + X * zPoly as

/-- `∑_j t^j · column_j`. -/
noncomputable def zFam : List (List GI) → ℤ[X][X]
  | [] => 0
  | P :: Ps => zPoly P + C X * zFam Ps

/-- The integer model `F̃ = 13^182 f`. -/
noncomputable def Ftil : ℤ[X][X] := zFam intCols

/-- The scale `L = 13^182`. -/
def L : ℤ := 13 ^ 182

def imZeroRow : List GI → Bool
  | [] => true
  | a :: as => (a.2 == 0) && imZeroRow as

theorem intCols_real : intCols.all imZeroRow = true := by decide +kernel

theorem map_zPoly (t : ℂ) :
    ∀ l : List GI, imZeroRow l = true →
      (zPoly l).map (eval₂RingHom (Int.castRingHom ℂ) t) = toPolyC l
  | [], _ => by simp [zPoly, toPolyC]
  | a :: as, h => by
    simp only [imZeroRow, Bool.and_eq_true, beq_iff_eq] at h
    simp [zPoly, toPolyC, map_zPoly t as h.2, gc, h.1]

theorem map_zFam (t : ℂ) :
    ∀ cs : List (List GI), cs.all imZeroRow = true →
      (zFam cs).map (eval₂RingHom (Int.castRingHom ℂ) t) = famPoly cs t
  | [], _ => by simp [zFam, famPoly]
  | P :: Ps, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [zFam, famPoly, map_zPoly t P h.1, map_zFam t Ps h.2]

/-- **The link.** `f(·, t) = L⁻¹ · F̃(t, ·)`. -/
theorem P_eq_Ftil (t : ℂ) :
    paperMonicFamily.P t = C (((13 ^ 182 : ℚ) : ℂ)⁻¹) * Ftil.map (eval₂RingHom (Int.castRingHom ℂ) t) := by
  show paperFamily t = _
  rw [paperFamily_eq_famPoly, Ftil, map_zFam t _ intCols_real]

theorem Ftil_map_eq (t : ℂ) :
    Ftil.map (eval₂RingHom (Int.castRingHom ℂ) t) = C ((L : ℂ)) * paperMonicFamily.P t := by
  rw [P_eq_Ftil, ← mul_assoc, ← C_mul]
  have : (L : ℂ) * ((13 ^ 182 : ℚ) : ℂ)⁻¹ = 1 := by
    rw [L]; push_cast; field_simp; norm_num
  rw [this, C_1, one_mul]

/-! ### Coefficients of `F̃` -/

theorem coeff_zPoly : ∀ (l : List GI) (k j : ℕ),
    ((zPoly l).coeff k).coeff j = if j = 0 then (l.getD k (0, 0)).1 else 0
  | [], k, j => by simp [zPoly]
  | a :: as, k, j => by
    rcases k with _ | k
    · rw [zPoly, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero, coeff_C]; rfl
    · rw [zPoly, coeff_add, coeff_C, if_neg (Nat.succ_ne_zero k), coeff_X_mul, zero_add,
        coeff_zPoly as k j]; rfl

theorem coeff_zFam : ∀ (cs : List (List GI)) (k j : ℕ),
    ((zFam cs).coeff k).coeff j = ((cs.getD j []).getD k (0, 0)).1
  | [], k, j => by simp [zFam]
  | P :: Ps, k, j => by
    rcases j with _ | j
    · simp [zFam, coeff_zPoly, coeff_C_mul]
    · simp [zFam, coeff_zPoly, coeff_C_mul, coeff_zFam Ps k j]

theorem intCols_short : intCols.all (fun c => decide (c.length ≤ 66)) = true := by decide +kernel

theorem intCols_top : intCols.map (fun c => (c.getD 65 (0, 0)).1) = [13 ^ 182, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem getD_eq_of_length_le {k : ℕ} {c : List GI} (hc : c.length ≤ 66) (hk : 66 ≤ k) :
    c.getD k (0, 0) = (0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : c.length ≤ k)]

theorem Ftil_coeff_eq_zero {k : ℕ} (hk : 66 ≤ k) : Ftil.coeff k = 0 := by
  ext j
  rw [Ftil, coeff_zFam]
  rcases lt_or_ge j intCols.length with hj | hj
  · have hshort := List.all_eq_true.1 intCols_short _ (List.getElem_mem hj)
    rw [List.getD_eq_getElem (hn := hj), getD_eq_of_length_le (by simpa using hshort) hk]; simp
  · rw [List.getD_eq_default (hn := hj)]; simp

theorem Ftil_coeff_65 : Ftil.coeff 65 = C L := by
  ext j
  rw [Ftil, coeff_zFam, coeff_C]
  have h := congrArg (fun l => l.getD j 0) intCols_top
  rcases lt_or_ge j intCols.length with hj | hj
  · rw [List.getD_eq_getElem (hn := hj)]
    rw [List.getD_eq_getElem (hn := (by simpa using hj))] at h
    simp only [List.getElem_map] at h
    rw [h]
    have hj8 : j < 8 := intCols_length ▸ hj
    interval_cases j <;> simp [L]
  · rw [List.getD_eq_default (hn := hj)]
    have hl : intCols.length = 8 := intCols_length
    simp [show j ≠ 0 by omega]

theorem Ftil_natDegree : Ftil.natDegree = 65 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [Ftil_coeff_65]; simp [L])
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  exact Ftil_coeff_eq_zero (by exact_mod_cast hk)

theorem Ftil_leadingCoeff : Ftil.leadingCoeff = C L := by
  rw [leadingCoeff, Ftil_natDegree, Ftil_coeff_65]

/-! ### Packing a list -/

/-- Pack a list in `s`-bit slots, least significant first. -/
def packL (s : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: as => a + (packL s as <<< s)

theorem dig_packL (s : ℕ) :
    ∀ (l : List ℕ), (∀ a ∈ l, a < 2 ^ s) → ∀ i, dig s (packL s l) i = l.getD i 0
  | [], _, i => by simp [packL, dig]
  | a :: as, h, i => by
    have ha := h a (List.mem_cons_self ..)
    have hs : 0 < 2 ^ s := by positivity
    rcases i with _ | i
    · simp [dig, packL, Nat.shiftLeft_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
    · have := dig_packL s as (fun b hb => h b (List.mem_cons_of_mem _ hb)) i
      simp only [List.getD_cons_succ]
      rw [← this, dig, dig, packL, Nat.shiftLeft_eq, pow_succ', ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt ha, zero_add]

theorem packL_lt (s : ℕ) :
    ∀ (l : List ℕ), (∀ a ∈ l, a < 2 ^ s) → packL s l < 2 ^ (s * l.length)
  | [], _ => by simp [packL]
  | a :: as, h => by
    have ha := h a (List.mem_cons_self ..)
    have ih := packL_lt s as fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [packL, List.length_cons, Nat.shiftLeft_eq]
    calc a + packL s as * 2 ^ s < 2 ^ s + packL s as * 2 ^ s := by omega
      _ = (packL s as + 1) * 2 ^ s := by ring
      _ ≤ 2 ^ (s * as.length) * 2 ^ s := Nat.mul_le_mul_right _ ih
      _ = 2 ^ (s * (as.length + 1)) := by rw [← pow_add]; ring_nf

/-! ### The reductions, computed from `intCols` -/

/-- Row `k` of `F̃ mod p`: the `t`-coefficients. -/
def rowF (p k : ℕ) : List ℕ := intCols.map fun c => ((c.getD k (0, 0)).1 % (p : ℤ)).toNat

/-- Row `k` of `F̃_X mod p`. -/
def rowG (p k : ℕ) : List ℕ :=
  intCols.map fun c => (((k + 1 : ℕ) * (c.getD (k + 1) (0, 0)).1) % (p : ℤ)).toNat

def Fpack (p : ℕ) : ℕ := packL (64 * 313) ((List.range 66).map fun k => packL 64 (rowF p k))

def Gpack (p : ℕ) : ℕ := packL (64 * 313) ((List.range 65).map fun k => packL 64 (rowG p k))

variable {p : ℕ} [Fact p.Prime]

theorem toNat_emod_cast (x : ℤ) (hp : 0 < p) : (((x % (p : ℤ)).toNat : ℕ) : ZMod p) = (x : ZMod p) := by
  rw [← ZMod.intCast_mod x p, ← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]

theorem row_lt (hp : p < 2 ^ 64) (f : List GI → ℤ) :
    ∀ a ∈ intCols.map (fun c => (f c % (p : ℤ)).toNat), a < 2 ^ 64 := by
  intro a ha
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have : (f c % (p : ℤ)).toNat < p := by
    have h1 := Int.emod_lt_of_pos (f c) (by omega : (0 : ℤ) < p)
    have h2 := Int.emod_nonneg (f c) (by omega : (p : ℤ) ≠ 0)
    omega
  omega

theorem packRow_lt (hp : p < 2 ^ 64) (f : List GI → ℤ) :
    packL 64 (intCols.map fun c => (f c % (p : ℤ)).toNat) < 2 ^ (64 * 313) := by
  refine lt_of_lt_of_le (packL_lt 64 _ (row_lt hp f)) (Nat.pow_le_pow_right (by norm_num) ?_)
  simp [intCols_length]

/-- Decoded coefficient `(k, j)` of a packed reduction. -/
theorem decB_coeff (hp : p < 2 ^ 64) (nx : ℕ) (f : ℕ → List GI → ℤ) (k j : ℕ) :
    ((decB (packL (64 * 313) ((List.range nx).map fun k =>
      packL 64 (intCols.map fun c => (f k c % (p : ℤ)).toNat))) nx 313).coeff k).coeff j
      = if k < nx then ((intCols.map fun c => (f k c % (p : ℤ)).toNat).getD j 0) else 0 := by
  rw [coeff_decB]
  split_ifs with hk
  · rw [dig_packL _ _ (fun a ha => by
        obtain ⟨k', hk', rfl⟩ := List.mem_map.1 ha
        exact packRow_lt hp (f k')), coeff_decU,
      List.getD_eq_getElem (hn := (by simpa using hk)), List.getElem_map, List.getElem_range]
    split_ifs with hj
    · rw [dig_packL _ _ (row_lt hp (f k))]
    · rw [List.getD_eq_default (hn := (by simp [intCols_length]; omega))]
  · simp

theorem Ftil_reduce (hp : p < 2 ^ 64) :
    Ftil.map (mapRingHom (Int.castRingHom (ZMod p)))
      = (decB (Fpack p) 66 313).map (mapRingHom (Nat.castRingHom (ZMod p))) := by
  ext k j
  simp only [coeff_map, coe_mapRingHom, eq_intCast, eq_natCast]
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  rw [show Fpack p = packL (64 * 313) ((List.range 66).map fun k =>
      packL 64 (intCols.map fun c => ((fun k c => (c.getD k (0, 0)).1) k c % (p : ℤ)).toNat)) from rfl,
    decB_coeff hp 66 (fun k c => (c.getD k (0, 0)).1), Ftil, coeff_zFam]
  split_ifs with hk
  · rcases lt_or_ge j intCols.length with hj | hj
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
        Option.map_some, Option.getD_some, toNat_emod_cast _ hp0]
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]
  · rcases lt_or_ge j intCols.length with hj | hj
    · have hshort := List.all_eq_true.1 intCols_short _ (List.getElem_mem hj)
      rw [List.getD_eq_getElem (hn := hj), getD_eq_of_length_le (by simpa using hshort) (by omega)]
      simp
    · rw [List.getD_eq_default (hn := hj)]; simp

theorem Ftil_derivative_reduce (hp : p < 2 ^ 64) :
    (derivative Ftil).map (mapRingHom (Int.castRingHom (ZMod p)))
      = (decB (Gpack p) 65 313).map (mapRingHom (Nat.castRingHom (ZMod p))) := by
  ext k j
  simp only [coeff_map, coe_mapRingHom, eq_intCast, eq_natCast]
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  rw [show Gpack p = packL (64 * 313) ((List.range 65).map fun k =>
      packL 64 (intCols.map fun c =>
        ((fun k c => ((k + 1 : ℕ) : ℤ) * (c.getD (k + 1) (0, 0)).1) k c % (p : ℤ)).toNat)) from rfl,
    decB_coeff hp 65 (fun k c => ((k + 1 : ℕ) : ℤ) * (c.getD (k + 1) (0, 0)).1), coeff_derivative]
  rw [show (Ftil.coeff (k + 1) * ((k : ℤ[X]) + 1)) = Ftil.coeff (k + 1) * C ((k + 1 : ℕ) : ℤ) by
    simp, coeff_mul_C, Ftil, coeff_zFam]
  split_ifs with hk
  · rcases lt_or_ge j intCols.length with hj | hj
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
        Option.map_some, Option.getD_some, toNat_emod_cast _ hp0]
      push_cast; ring
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]
  · rcases lt_or_ge j intCols.length with hj | hj
    · have hshort := List.all_eq_true.1 intCols_short _ (List.getElem_mem hj)
      rw [List.getD_eq_getElem (hn := hj), getD_eq_of_length_le (by simpa using hshort) (by omega)]
      simp
    · rw [List.getD_eq_default (hn := hj)]; simp

/-! ### Scaling identities -/

theorem natDegree_P (t : ℂ) : (paperMonicFamily.P t).natDegree = 65 := paperMonicFamily.natDegree_eq t

theorem resultant_Ftil (t : ℂ) :
    resultant (Ftil.map (eval₂RingHom (Int.castRingHom ℂ) t))
        (derivative (Ftil.map (eval₂RingHom (Int.castRingHom ℂ) t)))
      = (L : ℂ) ^ 129 * resultant (paperMonicFamily.P t) (derivative (paperMonicFamily.P t)) := by
  have hL : (L : ℂ) ≠ 0 := by simp [L]
  have hd : (derivative (paperMonicFamily.P t)).natDegree = 64 := by
    rw [natDegree_derivative, natDegree_P]
  rw [Ftil_map_eq, derivative_C_mul, natDegree_C_mul hL, natDegree_C_mul hL, natDegree_P, hd,
    resultant_C_mul_left, resultant_C_mul_right, ← mul_assoc, ← pow_add]

theorem B_Ftil (t : ℂ) :
    B (Ftil.map (eval₂RingHom (Int.castRingHom ℂ) t))
        (derivative (Ftil.map (eval₂RingHom (Int.castRingHom ℂ) t))) 64
      = (L : ℂ) ^ 128 * B (paperMonicFamily.P t) (derivative (paperMonicFamily.P t)) 64 := by
  rw [Ftil_map_eq, derivative_C_mul, B]
  have : mat (C (L : ℂ) * paperMonicFamily.P t) (C (L : ℂ) * derivative (paperMonicFamily.P t)) 64
      = (L : ℂ) • mat (paperMonicFamily.P t) (derivative (paperMonicFamily.P t)) 64 := by
    ext i j
    simp only [mat, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, col]
    split_ifs <;> simp [mul_left_comm, coeff_C_mul]
  rw [this, Matrix.det_smul, Fintype.card_fin, B]

end Sz8.Galois.FLink
