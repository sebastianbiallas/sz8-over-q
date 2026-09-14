import Sz8.Galois.NodeM2
import Sz8.Galois.SepData

/-!
# `S̃` is separable and coprime to `t² + t + 1`

Two Bézout identities modulo `p = 1000003`, `A₁ S̄ + B₁ S̄' = 1` and `A₂ S̄ + B₂ (t² + t + 1) = 1`,
checked in the kernel as packed exact identities (64-bit slots, one row of 700 slots). Through
`FixedMinor.no_common_root_of_modp` (the integer resultant specialises to `F_p`):

* `derivative_ne_of_root`: at every complex root of `S̃`, `S̃' ≠ 0`;
* `q_ne_of_root`: at every complex root of `S̃`, `t² + t + 1 ≠ 0`.
-/

open Polynomial

set_option maxRecDepth 100000

namespace Sz8.Galois.NodeSep

open Packed NodeData NodeM2 FixedMinor FLink

/-- One row of 700 slots: slots `< 2^b`, degree `≤ dt`. -/
def fitsW (b dt x : ℕ) : Bool := fits 64 b 700 x && fits (64 * 700) (64 * (dt + 1)) 1 x

/-- The reduction of `S̃'`, packed. -/
def Dpack : ℕ :=
  packL 64 ((List.range 342).map fun i => ((((i + 1 : ℕ) : ℤ) * Slist.getD (i + 1) 0) % 1000003).toNat)

def qpack : ℕ := packL 64 [1, 1, 1]

def sepChecks : Bool :=
  fitsW 20 340 A1 && fitsW 20 341 B1 && fitsW 20 342 Spack && fitsW 20 341 Dpack &&
  fitsW 34 682 Gm1 && fitsW 34 682 Gp1 &&
  fitsW 20 1 A2 && fitsW 20 341 B2 && fitsW 20 2 qpack && fitsW 34 343 Gm2 && fitsW 34 343 Gp2 &&
  fitsW 20 0 1 &&
  (A1 * Spack + B1 * Dpack + 1000003 * Gm1 == 1 + 1000003 * Gp1) &&
  (A2 * Spack + B2 * qpack + 1000003 * Gm2 == 1 + 1000003 * Gp2)

theorem sep_ok : sepChecks = true := by decide +kernel

/-- Reduction modulo `p` of a one-row literal. -/
noncomputable def redW (x : ℕ) : (ZMod 1000003)[X] := (decU x 700).map (Nat.castRingHom _)

theorem fitsW_spec {b dt x : ℕ} (hb : b ≤ 64) (hdt : dt + 1 ≤ 700) (h : fitsW b dt x = true) :
    Bd (decB x 1 700) (2 ^ b - 1) 0 dt ∧ κ 700 (decB x 1 700) = x ∧ decB x 1 700 = C (decU x 700) := by
  simp only [fitsW, Bool.and_eq_true] at h
  obtain ⟨hB, hk⟩ := decB_spec (W := 700) (nx := 1) hb hdt (by simpa using h.1) h.2
  refine ⟨hB, hk, ?_⟩
  have hx := (fits_spec (by norm_num) hb h.1).1
  rw [decB, Finset.sum_range_one, pow_zero, mul_one, dig, pow_zero, Nat.div_one,
    Nat.mod_eq_of_lt (by simpa using hx)]

theorem κ_CC700 (c : ℕ) : κ 700 (C (C c)) = c := by simp [κ_apply]

theorem hz0 : (Polynomial.map (mapRingHom (Nat.castRingHom (ZMod 1000003))) (C (C 1000003)) :
    (ZMod 1000003)[X][X]) = 0 := by
  rw [map_C, coe_mapRingHom, map_C]
  have : (Nat.castRingHom (ZMod 1000003)) 1000003 = 0 := by
    simp only [eq_natCast]; exact ZMod.natCast_self 1000003
  rw [this, map_zero, map_zero]

/-- A packed Bézout identity gives one over `ZMod p`. -/
theorem redW_bezout {x y z w gm gp dx dy dz dw dg : ℕ} (hxy : dx + dy ≤ 699) (hzw : dz + dw ≤ 699)
    (hdg : dg ≤ 699)
    (hx : fitsW 20 dx x = true) (hy : fitsW 20 dy y = true) (hz : fitsW 20 dz z = true)
    (hw : fitsW 20 dw w = true) (hgm : fitsW 34 dg gm = true) (hgp : fitsW 34 dg gp = true)
    (hone : fitsW 20 0 1 = true)
    (h : x * y + z * w + 1000003 * gm = 1 + 1000003 * gp) : redW x * redW y + redW z * redW w = 1 := by
  obtain ⟨bx, kx, ex⟩ := fitsW_spec (by norm_num) (by omega) hx
  obtain ⟨by', ky, ey⟩ := fitsW_spec (by norm_num) (by omega) hy
  obtain ⟨bz, kz, ez⟩ := fitsW_spec (by norm_num) (by omega) hz
  obtain ⟨bw, kw, ew⟩ := fitsW_spec (by norm_num) (by omega) hw
  obtain ⟨bgm, kgm, egm⟩ := fitsW_spec (by norm_num) (by omega) hgm
  obtain ⟨bgp, kgp, egp⟩ := fitsW_spec (by norm_num) (by omega) hgp
  obtain ⟨b1, k1, e1⟩ := fitsW_spec (by norm_num) (by norm_num) hone
  have bp : Bd (C (C 1000003) : ℕ[X][X]) (2 ^ 20 - 1) 0 0 := (Bd_C _).mono (by norm_num) le_rfl le_rfl
  have e : decB x 1 700 * decB y 1 700 + decB z 1 700 * decB w 1 700 + C (C 1000003) * decB gm 1 700
      = decB 1 1 700 + C (C 1000003) * decB gp 1 700 := by
    refine eq_of_κ_eq_Bd (W := 700) (((bx.mul by').add (bz.mul bw)).add (bp.mul bgm))
      (b1.add (bp.mul bgp)) ?_ ?_ (by simp; omega) (by simp; omega) ?_
    · have h1 : (dx + 1) * ((2 ^ 20 - 1) * (2 ^ 20 - 1)) ≤ 700 * ((2 ^ 20 - 1) * (2 ^ 20 - 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : (dz + 1) * ((2 ^ 20 - 1) * (2 ^ 20 - 1)) ≤ 700 * ((2 ^ 20 - 1) * (2 ^ 20 - 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [zero_add, one_mul] at h1 h2 ⊢
      norm_num at h1 h2 ⊢
      omega
    · norm_num
    · simp only [map_add, map_mul, kx, ky, kz, kw, kgm, kgp, k1, κ_CC700]; exact h
  rw [ex, ey, ez, ew, egm, egp, e1] at e
  have e2 := congrArg (Polynomial.map (mapRingHom (Nat.castRingHom (ZMod 1000003)))) e
  rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, hz0, zero_mul, zero_mul, add_zero,
    add_zero, map_C, map_C, map_C, map_C, map_C, ← C_mul, ← C_mul, ← C_add] at e2
  have e3 := C_injective e2
  have hdec1 : decU 1 700 = 1 := by
    ext j
    rw [coeff_decU, coeff_one]
    rcases j with _ | j
    · simp [dig]
    · simp only [if_neg (Nat.succ_ne_zero j)]
      split_ifs
      · rw [dig, Nat.div_eq_of_lt, Nat.zero_mod]
        calc (1 : ℕ) < 2 ^ 64 := by norm_num
          _ ≤ (2 ^ 64) ^ (j + 1) := Nat.le_self_pow (Nat.succ_ne_zero j) _
      · rfl
  rw [hdec1, map_one] at e3
  exact e3

theorem decU_ext {x n m : ℕ} (hnm : n ≤ m) (hx : x < 2 ^ (64 * n)) : decU x m = decU x n := by
  ext j
  rw [coeff_decU, coeff_decU]
  split_ifs with h1 h2 <;> try rfl
  · rw [dig, Nat.div_eq_of_lt, Nat.zero_mod]
    calc x < 2 ^ (64 * n) := hx
      _ ≤ (2 ^ 64) ^ j := by rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · omega

theorem redW_Spack (hlt : Spack < 2 ^ (64 * 343)) :
    redW Spack = Stil.map (Int.castRingHom (ZMod 1000003)) := by
  rw [redW, decU_ext (by norm_num) hlt, Stil_reduce]

theorem redW_Dpack (hlt : Dpack < 2 ^ (64 * 343)) :
    redW Dpack = (derivative Stil).map (Int.castRingHom (ZMod 1000003)) := by
  rw [redW, decU_ext (by norm_num) hlt]
  ext i
  simp only [coeff_map, eq_intCast, eq_natCast, coeff_decU, coeff_derivative, coeff_Stil]
  have hdig : ∀ i < 342, dig 64 Dpack i
      = ((((i + 1 : ℕ) : ℤ) * Slist.getD (i + 1) 0) % 1000003).toNat := by
    intro i hi
    rw [Dpack, dig_packL _ _ (fun a ha => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
        have h1 := Int.emod_lt_of_pos (((b + 1 : ℕ) : ℤ) * Slist.getD (b + 1) 0) (by norm_num : (0 : ℤ) < 1000003)
        have h2 := Int.emod_nonneg (((b + 1 : ℕ) : ℤ) * Slist.getD (b + 1) 0) (by norm_num : (1000003 : ℤ) ≠ 0)
        omega),
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  rcases lt_or_ge i 342 with hi | hi
  · rw [if_pos (by omega), hdig i hi]
    have h := toNat_emod_cast (p := 1000003) (((i + 1 : ℕ) : ℤ) * Slist.getD (i + 1) 0) (by norm_num)
    simp only [Nat.cast_ofNat] at h
    rw [h]; push_cast; ring
  · rw [List.getD_eq_default (hn := by rw [Slist_length]; omega)]
    split_ifs with h343
    · have : dig 64 Dpack i = 0 := by
        rw [Dpack, dig_packL _ _ (fun a ha => by
            obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
            have h1 := Int.emod_lt_of_pos (((b + 1 : ℕ) : ℤ) * Slist.getD (b + 1) 0) (by norm_num : (0 : ℤ) < 1000003)
            have h2 := Int.emod_nonneg (((b + 1 : ℕ) : ℤ) * Slist.getD (b + 1) 0) (by norm_num : (1000003 : ℤ) ≠ 0)
            omega),
          List.getD_eq_default (hn := by simp; omega)]
      rw [this]; simp
    · simp

/-- `t² + t + 1 ∈ ℤ[t]`. -/
noncomputable def qZ : ℤ[X] := X ^ 2 + X + 1

theorem redW_qpack : redW qpack = qZ.map (Int.castRingHom (ZMod 1000003)) := by
  have hq : decU qpack 700 = X ^ 2 + X + 1 := by
    ext j
    rw [coeff_decU]
    have hd : ∀ j, dig 64 qpack j = [1, 1, 1].getD j 0 :=
      dig_packL 64 [1, 1, 1] (by intro a ha; simp at ha; rcases ha with rfl | rfl | rfl <;> norm_num)
    rw [hd]
    rcases j with _ | _ | _ | j <;> simp [coeff_X, coeff_one]
  rw [redW, hq, qZ]
  simp

theorem natDegree_Stil_pos : Stil.natDegree ≠ 0 := by rw [Stil_natDegree]; norm_num

/-- The closure hypothesis of the transfer lemma, from a Bézout identity over `ZMod p`. -/
theorem hmod_of_bezout {S T : ℤ[X]} {A B : (ZMod 1000003)[X]}
    (h : A * S.map (Int.castRingHom _) + B * T.map (Int.castRingHom _) = 1)
    (a : AlgebraicClosure (ZMod 1000003)) (ha : (S.map (Int.castRingHom _)).eval a = 0) :
    (T.map (Int.castRingHom _)).eval a ≠ 0 := by
  have hK : ∀ U : ℤ[X], U.map (Int.castRingHom (AlgebraicClosure (ZMod 1000003)))
      = (U.map (Int.castRingHom (ZMod 1000003))).map (algebraMap (ZMod 1000003) _) := by
    intro U; rw [Polynomial.map_map]; congr 1
  intro hT
  have := congrArg (fun P => (P.map (algebraMap (ZMod 1000003) (AlgebraicClosure (ZMod 1000003)))).eval a) h
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, eval_add, eval_mul,
    eval_one] at this
  rw [← hK, ← hK, ha, hT, mul_zero, mul_zero, add_zero] at this
  exact zero_ne_one this

theorem lt_of_fitsW {b dt x : ℕ} (hb : b ≤ 64) (hdt : dt + 1 ≤ 700) (h : fitsW b dt x = true) :
    x < 2 ^ (64 * (dt + 1)) := by
  simp only [fitsW, Bool.and_eq_true] at h
  have h1 := (fits_spec (by norm_num) hb h.1).1
  have h2 := (fits_spec (s := 64 * 700) (by norm_num) (by omega) h.2).2 0
  rwa [dig, pow_zero, Nat.div_one, Nat.mod_eq_of_lt (by simpa using h1)] at h2

theorem transfer {T : ℤ[X]} {A B : ℕ} (hb : redW A * Stil.map (Int.castRingHom _) + redW B * T.map (Int.castRingHom _) = 1)
    (z : ℂ) (hz : (Stil.map (Int.castRingHom ℂ)).eval z = 0) :
    (T.map (Int.castRingHom ℂ)).eval z ≠ 0 :=
  no_common_root_of_modp (p := 1000003) Stil T Stil_map_natDegree natDegree_Stil_pos
    (hmod_of_bezout hb) z hz

theorem derivative_ne_of_root (z : ℂ) (hz : (Stil.map (Int.castRingHom ℂ)).eval z = 0) :
    ((derivative Stil).map (Int.castRingHom ℂ)).eval z ≠ 0 := by
  have hc := sep_ok
  simp only [sepChecks, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨fA1, fB1⟩, fS⟩, fD⟩, fGm1⟩, fGp1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, fone⟩, e1⟩, -⟩ := hc
  have hb := redW_bezout (by norm_num) (by norm_num) (by norm_num) fA1 fS fB1 fD fGm1 fGp1 fone e1
  rw [redW_Spack (lt_of_fitsW (by norm_num) (by norm_num) fS),
    redW_Dpack (lt_of_fitsW (by norm_num) (by norm_num) fD)] at hb
  exact transfer hb z hz

theorem q_ne_of_root (z : ℂ) (hz : (Stil.map (Int.castRingHom ℂ)).eval z = 0) :
    z ^ 2 + z + 1 ≠ 0 := by
  have hc := sep_ok
  simp only [sepChecks, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, fS⟩, -⟩, -⟩, -⟩, fA2⟩, fB2⟩, fq⟩, fGm2⟩, fGp2⟩, fone⟩, -⟩, e2⟩ := hc
  have hb := redW_bezout (by norm_num) (by norm_num) (by norm_num) fA2 fS fB2 fq fGm2 fGp2 fone e2
  rw [redW_Spack (lt_of_fitsW (by norm_num) (by norm_num) fS), redW_qpack] at hb
  have := transfer hb z hz
  simpa [qZ] using this

end Sz8.Galois.NodeSep
