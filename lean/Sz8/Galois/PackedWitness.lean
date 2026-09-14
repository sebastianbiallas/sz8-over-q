import Sz8.Galois.Packed
import Sz8.Galois.ModTransfer

/-!
# From kernel-checked packed data to a `ResidueWitness`

`packedChecks` is the Boolean the kernel evaluates: seventeen slot/degree bounds (two masks per
literal) and the three packed identities

    F̄ + p G⁺ = X·Pq + ρ'·Pq + P·H_f + p G⁻
    F̄' + p G⁺ = X·Qq + ρ'·Qq + P·H_g + p G⁻
    a·Pq + b·Qq + p G⁺ = 1 + P·H_ab + p G⁻

in 64-bit slots with 313 `t`-slots per `X`-row. `witness_of_packed` turns `packedChecks = true`,
together with the reduction of `F` and `F_X` modulo `p` (hypotheses `hF`, `hG`), into a
`ResidueWitness F p` over `P = (decode Pn) mod p`, with `ρ ≡ -ρ'`.

The bounds are uniform over the factors of `S̄` of degree at most 157: `P` has `t`-degree `≤ 157`,
residue elements `≤ 156`, the `P`-quotients `H` `≤ 155`, everything else `≤ 312 < 313`.
-/

open Polynomial

namespace Sz8.Galois.PackedWitness

open Packed FixedMinor

/-- The two masks for a literal with `nx` rows: slots `< 2^b`, `t`-degree `≤ dt`. -/
def fits2 (b nx dt x : ℕ) : Bool := fits 64 b (313 * nx) x && fits (64 * 313) (64 * (dt + 1)) nx x

/-- Everything the kernel checks for one residue witness. -/
def packedChecks (p Fn Gn Pn ρn Pqn Qqn an bn Hfn Hgn Habn Gfp Gfm Ggp Ggm Gap Gam : ℕ) : Bool :=
  fits2 20 66 312 Fn && fits2 20 65 312 Gn && fits2 20 1 157 Pn && fits2 20 1 156 ρn &&
  fits2 20 65 156 Pqn && fits2 20 64 156 Qqn && fits2 20 64 156 an && fits2 20 65 156 bn &&
  fits2 20 66 155 Hfn && fits2 20 65 155 Hgn && fits2 20 129 155 Habn &&
  fits2 34 66 312 Gfp && fits2 34 66 312 Gfm && fits2 34 65 312 Ggp && fits2 34 65 312 Ggm &&
  fits2 34 129 312 Gap && fits2 34 129 312 Gam &&
  (Fn + p * Gfp == (Pqn <<< (64 * 313)) + ρn * Pqn + Pn * Hfn + p * Gfm) &&
  (Gn + p * Ggp == (Qqn <<< (64 * 313)) + ρn * Qqn + Pn * Hgn + p * Ggm) &&
  (an * Pqn + bn * Qqn + p * Gap == 1 + Pn * Habn + p * Gam)

theorem fits2_spec {b nx dt x : ℕ} (hb : b ≤ 64) (hdt : dt + 1 ≤ 313) (h : fits2 b nx dt x = true) :
    Bd (decB x nx 313) (2 ^ b - 1) (nx - 1) dt ∧ κ 313 (decB x nx 313) = x := by
  simp only [fits2, Bool.and_eq_true] at h
  exact decB_spec hb hdt h.1 h.2

theorem κ_X : κ 313 (X : ℕ[X][X]) = 2 ^ (64 * 313) := by simp [κ_apply]

theorem κ_CC (c : ℕ) : κ 313 (C (C c)) = c := by simp [κ_apply]

variable {p : ℕ} [Fact p.Prime]

/-- `ℕ[t][X] → (AdjoinRoot P)[X]`: reduce modulo `p`, then `t ↦ root P`. -/
noncomputable def ψ (P : (ZMod p)[X]) : ℕ[X][X] →+* (AdjoinRoot P)[X] :=
  mapRingHom ((AdjoinRoot.mk P).comp (mapRingHom (Nat.castRingHom (ZMod p))))

theorem ψ_p (P : (ZMod p)[X]) : ψ P (C (C p)) = 0 := by
  have e : (C (C p) : ℕ[X][X]) = (p : ℕ[X][X]) := by simp
  rw [e, map_natCast, ← map_natCast (algebraMap (ZMod p) (AdjoinRoot P)[X]) p, ZMod.natCast_self,
    map_zero]

theorem ψ_X (P : (ZMod p)[X]) : ψ P X = X := by simp [ψ]

theorem toAdj_eq (P : (ZMod p)[X]) :
    toAdj P = (AdjoinRoot.mk P).comp (mapRingHom (Int.castRingHom (ZMod p))) := by
  apply Polynomial.ringHom_ext
  · intro c; simp [toAdj]
  · simp [toAdj, AdjoinRoot.mk_X]

theorem decB_one {x : ℕ} (hx : x < 2 ^ (64 * (313 * 1))) :
    decB x 1 313 = C (decU x 313) := by
  rw [decB, Finset.sum_range_one, pow_zero, mul_one, dig, pow_zero, Nat.div_one,
    Nat.mod_eq_of_lt (by simpa using hx)]

/-- **Packed data gives a residue witness.** -/
theorem witness_of_packed (F : ℤ[X][X])
    (Fn Gn Pn ρn Pqn Qqn an bn Hfn Hgn Habn Gfp Gfm Ggp Ggm Gap Gam : ℕ)
    (hp : p < 2 ^ 20)
    (hchk : packedChecks p Fn Gn Pn ρn Pqn Qqn an bn Hfn Hgn Habn Gfp Gfm Ggp Ggm Gap Gam = true)
    (hF : F.map (mapRingHom (Int.castRingHom (ZMod p)))
      = (decB Fn 66 313).map (mapRingHom (Nat.castRingHom (ZMod p))))
    (hG : (derivative F).map (mapRingHom (Int.castRingHom (ZMod p)))
      = (decB Gn 65 313).map (mapRingHom (Nat.castRingHom (ZMod p)))) :
    ∃ w : ResidueWitness F p, w.P = (decU Pn 313).map (Nat.castRingHom (ZMod p)) := by
  simp only [packedChecks, Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cF, cG⟩, cP⟩, cρ⟩, cPq⟩, cQq⟩, ca⟩, cb⟩, cHf⟩, cHg⟩, cHab⟩, cGfp⟩,
    cGfm⟩, cGgp⟩, cGgm⟩, cGap⟩, cGam⟩, ef⟩, eg⟩, eab⟩ := hchk
  obtain ⟨bF, kF⟩ := fits2_spec (by norm_num) (by norm_num) cF
  obtain ⟨bG, kG⟩ := fits2_spec (by norm_num) (by norm_num) cG
  obtain ⟨bP, kP⟩ := fits2_spec (by norm_num) (by norm_num) cP
  obtain ⟨bρ, kρ⟩ := fits2_spec (by norm_num) (by norm_num) cρ
  obtain ⟨bPq, kPq⟩ := fits2_spec (by norm_num) (by norm_num) cPq
  obtain ⟨bQq, kQq⟩ := fits2_spec (by norm_num) (by norm_num) cQq
  obtain ⟨ba, ka⟩ := fits2_spec (by norm_num) (by norm_num) ca
  obtain ⟨bb, kb⟩ := fits2_spec (by norm_num) (by norm_num) cb
  obtain ⟨bHf, kHf⟩ := fits2_spec (by norm_num) (by norm_num) cHf
  obtain ⟨bHg, kHg⟩ := fits2_spec (by norm_num) (by norm_num) cHg
  obtain ⟨bHab, kHab⟩ := fits2_spec (by norm_num) (by norm_num) cHab
  obtain ⟨bGfp, kGfp⟩ := fits2_spec (by norm_num) (by norm_num) cGfp
  obtain ⟨bGfm, kGfm⟩ := fits2_spec (by norm_num) (by norm_num) cGfm
  obtain ⟨bGgp, kGgp⟩ := fits2_spec (by norm_num) (by norm_num) cGgp
  obtain ⟨bGgm, kGgm⟩ := fits2_spec (by norm_num) (by norm_num) cGgm
  obtain ⟨bGap, kGap⟩ := fits2_spec (by norm_num) (by norm_num) cGap
  obtain ⟨bGam, kGam⟩ := fits2_spec (by norm_num) (by norm_num) cGam
  have bp : Bd (C (C p) : ℕ[X][X]) (2 ^ 20 - 1) 0 0 := (Bd_C p).mono (by omega) le_rfl le_rfl
  set P := (decU Pn 313).map (Nat.castRingHom (ZMod p)) with hPdef
  set F' := decB Fn 66 313
  set G' := decB Gn 65 313
  set P' := decB Pn 1 313
  set ρ' := decB ρn 1 313
  set Pq' := decB Pqn 65 313
  set Qq' := decB Qqn 64 313
  set a' := decB an 64 313
  set b' := decB bn 65 313
  -- the three identities over `ℕ[t][X]`
  have pf : F' + C (C p) * decB Gfp 66 313
      = X * Pq' + ρ' * Pq' + P' * decB Hfn 66 313 + C (C p) * decB Gfm 66 313 := by
    refine eq_of_κ_eq_Bd (W := 313) (bF.add (bp.mul bGfp))
      ((((Bd_X.mul bPq).add (bρ.mul bPq)).add (bP.mul bHf)).add (bp.mul bGfm))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    simp only [map_add, map_mul, kF, kGfp, kPq, kρ, kP, kHf, kGfm, κ_X, κ_CC]
    rw [ef, Nat.shiftLeft_eq, mul_comm]
  have pg : G' + C (C p) * decB Ggp 65 313
      = X * Qq' + ρ' * Qq' + P' * decB Hgn 65 313 + C (C p) * decB Ggm 65 313 := by
    refine eq_of_κ_eq_Bd (W := 313) (bG.add (bp.mul bGgp))
      ((((Bd_X.mul bQq).add (bρ.mul bQq)).add (bP.mul bHg)).add (bp.mul bGgm))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    simp only [map_add, map_mul, kG, kGgp, kQq, kρ, kP, kHg, kGgm, κ_X, κ_CC]
    rw [eg, Nat.shiftLeft_eq, mul_comm]
  have pab : a' * Pq' + b' * Qq' + C (C p) * decB Gap 129 313
      = C (C 1) + P' * decB Habn 129 313 + C (C p) * decB Gam 129 313 := by
    refine eq_of_κ_eq_Bd (W := 313) (((ba.mul bPq).add (bb.mul bQq)).add (bp.mul bGap))
      (((Bd_C 1).add (bP.mul bHab)).add (bp.mul bGam))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    simp only [map_add, map_mul, ka, kPq, kb, kQq, kGap, kP, kHab, kGam, κ_CC]
    exact eab
  -- reduce to the residue ring
  have hlt1 : ∀ {b dt x : ℕ}, b ≤ 64 → fits2 b 1 dt x = true → x < 2 ^ (64 * (313 * 1)) := by
    intro b dt x hb h
    simp only [fits2, Bool.and_eq_true] at h
    exact (fits_spec (by norm_num) hb h.1).1
  have hP0 : ψ P P' = 0 := by
    rw [show P' = C (decU Pn 313) from decB_one (hlt1 (by norm_num) cP)]
    simp [ψ, hPdef]
  have hρC : ψ P ρ' = C (AdjoinRoot.mk P ((decU ρn 313).map (Nat.castRingHom (ZMod p)))) := by
    rw [show ρ' = C (decU ρn 313) from decB_one (hlt1 (by norm_num) cρ)]
    simp [ψ]
  set ρ := -AdjoinRoot.mk P ((decU ρn 313).map (Nat.castRingHom (ZMod p)))
  have hlinF : F.map (toAdj P) = ψ P F' := by
    rw [toAdj_eq, ← Polynomial.map_map, hF, Polynomial.map_map, ψ]
    rfl
  have hlinG : (derivative F).map (toAdj P) = ψ P G' := by
    rw [toAdj_eq, ← Polynomial.map_map, hG, Polynomial.map_map, ψ]
    rfl
  refine ⟨⟨P, ρ, ψ P Pq', ψ P Qq', ψ P a', ψ P b', ?_, ?_, ?_⟩, rfl⟩
  · have := congrArg (ψ P) pf
    simp only [map_add, map_mul, ψ_p, hP0, zero_mul, add_zero, ψ_X, hρC] at this
    rw [hlinF, this]
    simp only [ρ, map_neg, sub_neg_eq_add]
    ring
  · have := congrArg (ψ P) pg
    simp only [map_add, map_mul, ψ_p, hP0, zero_mul, add_zero, ψ_X, hρC] at this
    rw [hlinG, this]
    simp only [ρ, map_neg, sub_neg_eq_add]
    ring
  · have := congrArg (ψ P) pab
    simp only [map_add, map_mul, ψ_p, hP0, zero_mul, add_zero, map_one, map_natCast] at this
    simpa using this

end Sz8.Galois.PackedWitness
