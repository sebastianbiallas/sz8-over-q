import Sz8.Galois.FLink
import Sz8.Galois.NodeData
import Mathlib.Tactic.NormNum.Prime

/-!
# M2 at every root of `S̃`, with no remaining hypotheses

* Seven kernel checks `packedChecks 1000003 (Fpack p) (Gpack p) …` for the factors of `S̄` of
  degrees 1, 3, 5, 14, 78, 84, 157 (data in `Sz8.Galois.NodeData`); the reductions of `F̃`, `F̃_X`
  are computed from `intCols`, so `witness_of_packed` needs no further hypotheses.
* `chainChecks`: the factor product `628079 · ∏ Pᵢ ≡ S̃ (mod p)`, as seven packed identities.
* `node_M2`: at every complex root `z` of `S̃`, every root of `f(·, z)` has multiplicity at most two
  and at most one root has multiplicity two.
-/

open Polynomial

namespace Sz8.Galois.NodeM2

open Packed PackedWitness FixedMinor FLink NodeData

instance fact_prime : Fact (Nat.Prime 1000003) := ⟨by norm_num⟩

/-! ### The seven residue witnesses -/

theorem chk0 : packedChecks 1000003 (Fpack 1000003) (Gpack 1000003) P0 rho0 Pq0 Qq0 a0 b0 Hf0 Hg0
    Hab0 Gfp0 Gfm0 Ggp0 Ggm0 Gap0 Gam0 = true := by decide +kernel
theorem chk1 : packedChecks 1000003 (Fpack 1000003) (Gpack 1000003) P1 rho1 Pq1 Qq1 a1 b1 Hf1 Hg1
    Hab1 Gfp1 Gfm1 Ggp1 Ggm1 Gap1 Gam1 = true := by decide +kernel
theorem chk2 : packedChecks 1000003 (Fpack 1000003) (Gpack 1000003) P2 rho2 Pq2 Qq2 a2 b2 Hf2 Hg2
    Hab2 Gfp2 Gfm2 Ggp2 Ggm2 Gap2 Gam2 = true := by decide +kernel
theorem chk3 : packedChecks 1000003 (Fpack 1000003) (Gpack 1000003) P3 rho3 Pq3 Qq3 a3 b3 Hf3 Hg3
    Hab3 Gfp3 Gfm3 Ggp3 Ggm3 Gap3 Gam3 = true := by decide +kernel
theorem chk4 : packedChecks 1000003 (Fpack 1000003) (Gpack 1000003) P4 rho4 Pq4 Qq4 a4 b4 Hf4 Hg4
    Hab4 Gfp4 Gfm4 Ggp4 Ggm4 Gap4 Gam4 = true := by decide +kernel
theorem chk5 : packedChecks 1000003 (Fpack 1000003) (Gpack 1000003) P5 rho5 Pq5 Qq5 a5 b5 Hf5 Hg5
    Hab5 Gfp5 Gfm5 Ggp5 Ggm5 Gap5 Gam5 = true := by decide +kernel
theorem chk6 : packedChecks 1000003 (Fpack 1000003) (Gpack 1000003) P6 rho6 Pq6 Qq6 a6 b6 Hf6 Hg6
    Hab6 Gfp6 Gfm6 Ggp6 Ggm6 Gap6 Gam6 = true := by decide +kernel

theorem hp20 : (1000003 : ℕ) < 2 ^ 20 := by norm_num

theorem wit {Pn ρn Pqn Qqn an bn Hfn Hgn Habn Gfp Gfm Ggp Ggm Gap Gam : ℕ}
    (h : packedChecks 1000003 (Fpack 1000003) (Gpack 1000003) Pn ρn Pqn Qqn an bn Hfn Hgn Habn
      Gfp Gfm Ggp Ggm Gap Gam = true) :
    ∃ w : ResidueWitness Ftil 1000003, w.P = (decU Pn 313).map (Nat.castRingHom _) :=
  witness_of_packed Ftil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp20 h (Ftil_reduce (by norm_num))
    (Ftil_derivative_reduce (by norm_num))

noncomputable def ws : List (ResidueWitness Ftil 1000003) :=
  [(wit chk0).choose, (wit chk1).choose, (wit chk2).choose, (wit chk3).choose, (wit chk4).choose,
    (wit chk5).choose, (wit chk6).choose]

/-! ### `S̃` and its reduction -/

/-- `S̃ ∈ ℤ[t]`. -/
noncomputable def Stil : ℤ[X] := ∑ i ∈ Finset.range Slist.length, C (Slist.getD i 0) * X ^ i

theorem coeff_Stil (i : ℕ) : Stil.coeff i = Slist.getD i 0 := by
  simp only [Stil, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default (hn := by simpa using h)]

theorem Slist_length : Slist.length = 343 := by decide +kernel

theorem lcS_ne : (lcS : ZMod 1000003) ≠ 0 := by decide +kernel

theorem Stil_natDegree : Stil.natDegree = 342 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_Stil, List.getD_eq_default (hn := by rw [Slist_length]; exact_mod_cast hi)]
  · rw [coeff_Stil]; decide +kernel

theorem Stil_map_natDegree :
    (Stil.map (Int.castRingHom (ZMod 1000003))).natDegree = Stil.natDegree := by
  refine natDegree_map_of_leadingCoeff_ne_zero _ ?_
  rw [leadingCoeff, Stil_natDegree, coeff_Stil, eq_intCast]
  decide +kernel

/-- The reduction of `S̃`, packed in 64-bit slots. -/
def Spack : ℕ := packL 64 (Slist.map fun a => (a % (1000003 : ℤ)).toNat)

theorem Stil_reduce :
    Stil.map (Int.castRingHom (ZMod 1000003)) = (decU Spack 343).map (Nat.castRingHom _) := by
  ext i
  simp only [coeff_map, eq_intCast, eq_natCast, coeff_Stil, coeff_decU]
  split_ifs with hi
  · rw [Spack, dig_packL _ _ (fun a ha => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
        have h1 := Int.emod_lt_of_pos b (by norm_num : (0 : ℤ) < 1000003)
        have h2 := Int.emod_nonneg b (by norm_num : (1000003 : ℤ) ≠ 0)
        omega),
      ]
    rcases h : Slist[i]? with _ | b
    · simp [List.getD_eq_getElem?_getD, h]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, h, Option.map_some,
        Option.getD_some]
      exact (toNat_emod_cast b (by norm_num)).symm
  · rw [List.getD_eq_default (hn := by rw [Slist_length]; omega)]; simp

/-! ### The factor product -/

def fits1 (b dt x : ℕ) : Bool := fits 64 b 343 x && fits (64 * 343) (64 * (dt + 1)) 1 x

def chainChecks : Bool :=
  fits1 20 1 P0 && fits1 20 3 P1 && fits1 20 5 P2 && fits1 20 14 P3 && fits1 20 78 P4 &&
  fits1 20 84 P5 && fits1 20 157 P6 &&
  fits1 20 4 T1 && fits1 20 9 T2 && fits1 20 23 T3 && fits1 20 101 T4 && fits1 20 185 T5 &&
  fits1 20 342 T6 && fits1 20 0 lcS && fits1 20 342 Spack &&
  fits1 34 342 Cm1 && fits1 34 342 Cp1 && fits1 34 342 Cm2 && fits1 34 342 Cp2 &&
  fits1 34 342 Cm3 && fits1 34 342 Cp3 && fits1 34 342 Cm4 && fits1 34 342 Cp4 &&
  fits1 34 342 Cm5 && fits1 34 342 Cp5 && fits1 34 342 Cm6 && fits1 34 342 Cp6 &&
  fits1 34 342 Um && fits1 34 342 Up &&
  (P0 * P1 + 1000003 * Cm1 == T1 + 1000003 * Cp1) &&
  (T1 * P2 + 1000003 * Cm2 == T2 + 1000003 * Cp2) &&
  (T2 * P3 + 1000003 * Cm3 == T3 + 1000003 * Cp3) &&
  (T3 * P4 + 1000003 * Cm4 == T4 + 1000003 * Cp4) &&
  (T4 * P5 + 1000003 * Cm5 == T5 + 1000003 * Cp5) &&
  (T5 * P6 + 1000003 * Cm6 == T6 + 1000003 * Cp6) &&
  (lcS * T6 + 1000003 * Um == Spack + 1000003 * Up)

theorem chain_ok : chainChecks = true := by decide +kernel

/-- `t`-polynomial of a single-row literal, reduced modulo `p`. -/
noncomputable def red (x : ℕ) : (ZMod 1000003)[X] := (decU x 343).map (Nat.castRingHom _)

theorem fits1_spec {b dt x : ℕ} (hb : b ≤ 64) (hdt : dt + 1 ≤ 343) (h : fits1 b dt x = true) :
    Bd (decB x 1 343) (2 ^ b - 1) 0 dt ∧ κ 343 (decB x 1 343) = x ∧ decB x 1 343 = C (decU x 343) := by
  simp only [fits1, Bool.and_eq_true] at h
  obtain ⟨hB, hk⟩ := decB_spec (W := 343) (nx := 1) hb hdt (by simpa using h.1) h.2
  refine ⟨hB, hk, ?_⟩
  have hx := (fits_spec (by norm_num) hb h.1).1
  rw [decB, Finset.sum_range_one, pow_zero, mul_one, dig, pow_zero, Nat.div_one,
    Nat.mod_eq_of_lt (by simpa using hx)]

theorem κ_CC' (c : ℕ) : κ 343 (C (C c)) = c := by simp [κ_apply]

/-- One packed product identity gives an identity of reductions. -/
theorem red_mul {x y z gm gp dx dy dz : ℕ} (hdxy : dx + dy ≤ 342) (hdz : dz ≤ 342)
    (hx : fits1 20 dx x = true) (hy : fits1 20 dy y = true) (hz : fits1 20 dz z = true)
    (hgm : fits1 34 342 gm = true) (hgp : fits1 34 342 gp = true)
    (h : x * y + 1000003 * gm = z + 1000003 * gp) : red x * red y = red z := by
  obtain ⟨bx, kx, ex⟩ := fits1_spec (by norm_num) (by omega) hx
  obtain ⟨by', ky, ey⟩ := fits1_spec (by norm_num) (by omega) hy
  obtain ⟨bz, kz, ez⟩ := fits1_spec (by norm_num) (by omega) hz
  obtain ⟨bgm, kgm, egm⟩ := fits1_spec (by norm_num) (by norm_num) hgm
  obtain ⟨bgp, kgp, egp⟩ := fits1_spec (by norm_num) (by norm_num) hgp
  have bp : Bd (C (C 1000003) : ℕ[X][X]) (2 ^ 20 - 1) 0 0 := (Bd_C _).mono (by norm_num) le_rfl le_rfl
  have hdx : dx ≤ 342 := by omega
  have e : decB x 1 343 * decB y 1 343 + C (C 1000003) * decB gm 1 343
      = decB z 1 343 + C (C 1000003) * decB gp 1 343 := by
    refine eq_of_κ_eq_Bd (W := 343) ((bx.mul by').add (bp.mul bgm)) (bz.add (bp.mul bgp)) ?_ ?_
      (by simp; omega) (by simp; omega) ?_
    · have : (dx + 1) * ((2 ^ 20 - 1) * (2 ^ 20 - 1)) ≤ 343 * ((2 ^ 20 - 1) * (2 ^ 20 - 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [zero_add, one_mul] at this ⊢
      norm_num at this ⊢
      omega
    · norm_num
    · simp only [map_add, map_mul, kx, ky, kz, kgm, kgp, κ_CC']; exact h
  rw [ex, ey, ez, egm, egp] at e
  have e2 := congrArg (Polynomial.map (mapRingHom (Nat.castRingHom (ZMod 1000003)))) e
  have hz0 : (Polynomial.map (mapRingHom (Nat.castRingHom (ZMod 1000003))) (C (C 1000003)) :
      (ZMod 1000003)[X][X]) = 0 := by
    rw [map_C, coe_mapRingHom, map_C]
    have : (Nat.castRingHom (ZMod 1000003)) 1000003 = 0 := by
      simp only [eq_natCast]; exact ZMod.natCast_self 1000003
    rw [this, map_zero, map_zero]
  rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_mul, hz0, zero_mul, zero_mul, add_zero, add_zero, map_C, map_C, map_C,
    ← C_mul] at e2
  exact C_injective e2

theorem red_lcS : red lcS = C (lcS : ZMod 1000003) := by
  have h := (fits1_spec (b := 20) (dt := 0) (x := lcS) (by norm_num) (by norm_num)
    (by decide +kernel)).1.tdeg 0
  have hc : decU lcS 343 = C lcS := by
    ext j
    rw [coeff_decU, coeff_C]
    rcases j with _ | j
    · simp [dig, lcS]
    · simp only [if_neg (Nat.succ_ne_zero j)]
      split_ifs
      · rw [dig, Nat.div_eq_of_lt, Nat.zero_mod]
        calc lcS < 2 ^ 64 := by simp [lcS]
          _ ≤ (2 ^ 64) ^ (j + 1) := by
            calc (2 : ℕ) ^ 64 = (2 ^ 64) ^ 1 := (pow_one _).symm
              _ ≤ (2 ^ 64) ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      · rfl
  rw [red, hc, map_C]; rfl

theorem decU_extend {x : ℕ} (hx : x < 2 ^ (64 * 313)) : decU x 343 = decU x 313 := by
  ext j
  rw [coeff_decU, coeff_decU]
  split_ifs with h1 h2 <;> try rfl
  · rw [dig, Nat.div_eq_of_lt, Nat.zero_mod]
    calc x < 2 ^ (64 * 313) := hx
      _ ≤ (2 ^ 64) ^ j := by rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · omega

theorem ws_P :
    C (lcS : ZMod 1000003) * (ws.map ResidueWitness.P).prod
      = Stil.map (Int.castRingHom (ZMod 1000003)) := by
  have hc := chain_ok
  simp only [chainChecks, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨f0, f1⟩, f2⟩, f3⟩, f4⟩, f5⟩, f6⟩, t1⟩, t2⟩, t3⟩, t4⟩, t5⟩, t6⟩, fl⟩, fs⟩, m1⟩, p1⟩, m2⟩, p2⟩, m3⟩, p3⟩, m4⟩, p4⟩, m5⟩, p5⟩, m6⟩, p6⟩, mu⟩, pu⟩, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, eu⟩ := hc
  have r1 := red_mul (by norm_num) (by norm_num) f0 f1 t1 m1 p1 e1
  have r2 := red_mul (by norm_num) (by norm_num) t1 f2 t2 m2 p2 e2
  have r3 := red_mul (by norm_num) (by norm_num) t2 f3 t3 m3 p3 e3
  have r4 := red_mul (by norm_num) (by norm_num) t3 f4 t4 m4 p4 e4
  have r5 := red_mul (by norm_num) (by norm_num) t4 f5 t5 m5 p5 e5
  have r6 := red_mul (by norm_num) (by norm_num) t5 f6 t6 m6 p6 e6
  have ru := red_mul (by norm_num) (by norm_num) fl t6 fs mu pu eu
  have hP : ∀ {Pn ρn Pqn Qqn an bn Hfn Hgn Habn Gfp Gfm Ggp Ggm Gap Gam dt : ℕ}
      (h : packedChecks 1000003 (Fpack 1000003) (Gpack 1000003) Pn ρn Pqn Qqn an bn Hfn Hgn Habn
        Gfp Gfm Ggp Ggm Gap Gam = true) (hf : fits1 20 dt Pn = true) (hdt : dt ≤ 312),
      (wit h).choose.P = red Pn := by
    intro Pn ρn Pqn Qqn an bn Hfn Hgn Habn Gfp Gfm Ggp Ggm Gap Gam dt h hf hdt
    rw [(wit h).choose_spec, red, decU_extend]
    simp only [fits1, Bool.and_eq_true] at hf
    have h1 := (fits_spec (by norm_num) (by norm_num) hf.1).1
    have h2 := (fits_spec (s := 64 * 343) (by norm_num) (by omega) hf.2).2 0
    rw [dig, pow_zero, Nat.div_one, Nat.mod_eq_of_lt (by simpa using h1)] at h2
    exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  simp only [ws, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    hP chk0 f0 (by norm_num), hP chk1 f1 (by norm_num), hP chk2 f2 (by norm_num),
    hP chk3 f3 (by norm_num), hP chk4 f4 (by norm_num), hP chk5 f5 (by norm_num),
    hP chk6 f6 (by norm_num)]
  rw [Stil_reduce, ← red, ← ru, red_lcS, ← r6, ← r5, ← r4, ← r3, ← r2, ← r1]
  ring

/-! ### M2 at the nodes -/

theorem L_ne : ((L : ℤ) : ZMod 1000003) ≠ 0 := by decide +kernel

/-- **M2.** At every complex root `z` of `S̃`, every root of `f(·, z)` has multiplicity at most
two and at most one root has multiplicity two. -/
theorem node_M2 (z : ℂ) (hz : (Stil.map (Int.castRingHom ℂ)).eval z = 0) :
    (∀ r, (Sz8.Monodromy.paperMonicFamily.P z).rootMultiplicity r ≤ 2) ∧
      ∀ r s, 2 ≤ (Sz8.Monodromy.paperMonicFamily.P z).rootMultiplicity r →
        2 ≤ (Sz8.Monodromy.paperMonicFamily.P z).rootMultiplicity s → r = s := by
  have h := node_multiplicity Ftil Stil L 64 Ftil_natDegree Ftil_leadingCoeff L_ne
    Stil_map_natDegree (by rw [Stil_natDegree]; norm_num) ws _ lcS_ne ws_P z hz
  have hL : (L : ℂ) ≠ 0 := by simp [L]
  have hmul : ∀ r, (Ftil.map (eval₂RingHom (Int.castRingHom ℂ) z)).rootMultiplicity r
      = (Sz8.Monodromy.paperMonicFamily.P z).rootMultiplicity r := by
    intro r
    rw [Ftil_map_eq, rootMultiplicity_mul (mul_ne_zero (by simpa using hL)
      (Sz8.Monodromy.paperMonicFamily.monic z).ne_zero), rootMultiplicity_C, zero_add]
  simp only [hmul] at h
  exact h

end Sz8.Galois.NodeM2
