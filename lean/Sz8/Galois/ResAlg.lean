import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# A resultant algorithm, and its correctness

Coefficient lists are **descending** (`[a_m, …, a_0]`). Euclid over `ℚ` with monic normalisation:

    Res(G, H) = a^m · (-1)^(m n) · Res(H/a, G mod (H/a)),   a = lc H, m = deg G, n = deg H.

`res_eq`: for inputs without leading zeros and enough fuel, `res fuel g h` is Mathlib's
`resultant (ofDesc g) (ofDesc h)` with its default formal degrees. Every case is covered: `H = 0`,
`H` constant, `deg G < deg H` (the remainder is `G` itself), zero remainder, and degree drops of
the remainder (handled by `resultant_add_right_deg`).
-/

open Polynomial

namespace Sz8.Galois.ResAlg

/-! ### The algorithm -/

def stripD : List ℚ → List ℚ
  | [] => []
  | a :: as => if a == 0 then stripD as else a :: as

def subScaled : List ℚ → ℚ → List ℚ → List ℚ
  | g :: gs, c, h :: hs => (g - c * h) :: subScaled gs c hs
  | gs, _, [] => gs
  | [], _, _ => []

def remIter : ℕ → List ℚ → List ℚ → List ℚ
  | 0, g, _ => g
  | k + 1, g, h =>
    if g.length < h.length then g else
    match g with
    | [] => []
    | c :: gs => remIter k (subScaled gs c h.tail) h

/-- Remainder of `g` by the monic `h`, both descending. -/
def rem (g h : List ℚ) : List ℚ := stripD (remIter g.length g h)

/-- Euclidean resultant over `ℚ`, descending coefficient lists. -/
def res : ℕ → List ℚ → List ℚ → ℚ
  | 0, _, _ => 0
  | fuel + 1, g, h =>
    match h with
    | [] => if g.length ≤ 1 then 1 else 0
    | [a] => a ^ (g.length - 1)
    | a :: _ =>
      let m := g.length - 1
      let n := h.length - 1
      let hm := h.map (· / a)
      let s : ℚ := if (m * n) % 2 == 0 then 1 else -1
      a ^ m * s * res fuel hm (rem g hm)

/-! ### Semantics -/

/-- The polynomial of a descending coefficient list. -/
noncomputable def ofDesc : List ℚ → ℚ[X]
  | [] => 0
  | a :: as => C a * X ^ as.length + ofDesc as

/-- No leading zero. -/
def Stripped : List ℚ → Prop
  | [] => True
  | a :: _ => a ≠ 0

theorem natDegree_ofDesc_le : ∀ l : List ℚ, (ofDesc l).natDegree ≤ l.length - 1
  | [] => by simp [ofDesc]
  | a :: as => by
    have ih := natDegree_ofDesc_le as
    simp only [ofDesc, List.length_cons, Nat.add_sub_cancel]
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_X_pow_le _ _)) ?_)
    omega

theorem coeff_ofDesc_length (as : List ℚ) : (ofDesc as).coeff as.length = 0 := by
  rcases as with _ | ⟨b, bs⟩
  · simp [ofDesc]
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_ofDesc_le _) (by simp))

theorem coeff_ofDesc_top (a : ℚ) (as : List ℚ) : (ofDesc (a :: as)).coeff as.length = a := by
  simp [ofDesc, coeff_ofDesc_length]

theorem natDegree_ofDesc {l : List ℚ} (hl : Stripped l) : (ofDesc l).natDegree = l.length - 1 := by
  rcases l with _ | ⟨a, as⟩
  · simp [ofDesc]
  · refine le_antisymm (natDegree_ofDesc_le _) ?_
    simp only [List.length_cons, Nat.add_sub_cancel]
    exact le_natDegree_of_ne_zero (by rw [coeff_ofDesc_top]; exact hl)

theorem leadingCoeff_ofDesc {a : ℚ} {as : List ℚ} (ha : a ≠ 0) :
    (ofDesc (a :: as)).leadingCoeff = a := by
  rw [leadingCoeff, natDegree_ofDesc (show Stripped (a :: as) from ha)]
  simpa using coeff_ofDesc_top a as

theorem ofDesc_stripD : ∀ l : List ℚ, ofDesc (stripD l) = ofDesc l
  | [] => rfl
  | a :: as => by
    by_cases ha : a = 0
    · simp [stripD, ha, ofDesc, ofDesc_stripD as]
    · simp [stripD, ha]

theorem stripped_stripD : ∀ l : List ℚ, Stripped (stripD l)
  | [] => trivial
  | a :: as => by
    by_cases ha : a = 0
    · simp only [stripD, ha, beq_self_eq_true, if_true]; exact stripped_stripD as
    · simp only [stripD, beq_iff_eq, ha, if_false]; exact ha

theorem length_stripD_le : ∀ l : List ℚ, (stripD l).length ≤ l.length
  | [] => le_rfl
  | a :: as => by
    by_cases ha : a = 0
    · simp only [stripD, ha, beq_self_eq_true, if_true, List.length_cons]
      exact (length_stripD_le as).trans (Nat.le_succ _)
    · simp [stripD, ha]

theorem ofDesc_subScaled (c : ℚ) :
    ∀ (gs hs : List ℚ), hs.length ≤ gs.length →
      ofDesc (subScaled gs c hs) = ofDesc gs - C c * X ^ (gs.length - hs.length) * ofDesc hs ∧
        (subScaled gs c hs).length = gs.length
  | gs, [], _ => by
    cases gs <;> simp [subScaled, ofDesc]
  | [], _ :: _, h => by simp at h
  | g :: gs, h :: hs, hl => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at hl
    obtain ⟨ih1, ih2⟩ := ofDesc_subScaled c gs hs hl
    refine ⟨?_, by simp [subScaled, ih2]⟩
    simp only [subScaled, ofDesc, ih1, ih2, List.length_cons, Nat.add_sub_add_right]
    have : X ^ gs.length = (X : ℚ[X]) ^ (gs.length - hs.length) * X ^ hs.length := by
      rw [← pow_add, Nat.sub_add_cancel hl]
    rw [this, C_sub, C_mul]
    ring

theorem ofDesc_map_div (a : ℚ) : ∀ l : List ℚ, ofDesc (l.map fun x => x / a) = C a⁻¹ * ofDesc l
  | [] => by simp [ofDesc]
  | b :: bs => by
    rw [List.map_cons, ofDesc, ofDesc, List.length_map, ofDesc_map_div a bs, div_eq_mul_inv, C_mul]
    ring

/-- The remainder loop, for a monic divisor `1 :: ht`. -/
theorem remIter_spec (ht : List ℚ) :
    ∀ (k : ℕ) (g : List ℚ), ∃ q : ℚ[X],
      ofDesc g = ofDesc (remIter k g (1 :: ht)) + ofDesc (1 :: ht) * q ∧
        q.natDegree ≤ g.length - (ht.length + 1) ∧ (q = 0 ∨ ht.length + 1 ≤ g.length) ∧
        (g.length < k + ht.length + 1 → (remIter k g (1 :: ht)).length < ht.length + 1)
  | 0, g => ⟨0, by simp [remIter], by simp, Or.inl rfl, fun h => by simp [remIter]; omega⟩
  | k + 1, g => by
    by_cases hlt : g.length < (1 :: ht).length
    · have hr : remIter (k + 1) g (1 :: ht) = g := by simp only [remIter]; rw [if_pos hlt]
      exact ⟨0, by simp [hr], by simp, Or.inl rfl, fun _ => by rw [hr]; simpa using hlt⟩
    · rcases g with _ | ⟨c, gs⟩
      · simp at hlt
      · simp only [List.length_cons, not_lt, Nat.add_le_add_iff_right] at hlt
        obtain ⟨h1, h2⟩ := ofDesc_subScaled c gs ht hlt
        obtain ⟨q, hq1, hq2, -, hq3⟩ := remIter_spec ht k (subScaled gs c ht)
        have hrem : remIter (k + 1) (c :: gs) (1 :: ht) = remIter k (subScaled gs c ht) (1 :: ht) := by
          simp only [remIter]; rw [if_neg (by simp; omega)]; rfl
        refine ⟨q + C c * X ^ (gs.length - ht.length), ?_, ?_, Or.inr (by simp; omega), ?_⟩
        · rw [hrem]
          rw [h1] at hq1
          have hX : X ^ gs.length = (X : ℚ[X]) ^ (gs.length - ht.length) * X ^ ht.length := by
            rw [← pow_add, Nat.sub_add_cancel hlt]
          simp only [ofDesc, List.length_cons, map_one, one_mul] at hq1 ⊢
          rw [hX]
          linear_combination hq1
        · rw [h2] at hq2
          refine (natDegree_add_le _ _).trans (max_le (hq2.trans (by simp only [List.length_cons]; omega)) ?_)
          exact (natDegree_C_mul_X_pow_le _ _).trans (by simp only [List.length_cons]; omega)
        · intro hk
          rw [hrem]
          exact hq3 (by rw [h2]; simp only [List.length_cons] at hk; omega)

theorem rem_spec (ht : List ℚ) (g : List ℚ) : ∃ q : ℚ[X],
    ofDesc g = ofDesc (rem g (1 :: ht)) + ofDesc (1 :: ht) * q ∧
      q.natDegree ≤ g.length - (ht.length + 1) ∧ (q = 0 ∨ ht.length + 1 ≤ g.length) ∧
      (rem g (1 :: ht)).length < ht.length + 1 ∧ Stripped (rem g (1 :: ht)) := by
  obtain ⟨q, h1, h2, h0, h3⟩ := remIter_spec ht g.length g
  refine ⟨q, by rw [rem, ofDesc_stripD]; exact h1, h2, h0, ?_, stripped_stripD _⟩
  exact lt_of_le_of_lt (length_stripD_le _) (h3 (by omega))

/-! ### Correctness -/

theorem sign_eq (m n : ℕ) : (if (m * n) % 2 == 0 then (1 : ℚ) else -1) = (-1) ^ (m * n) := by
  rcases Nat.even_or_odd (m * n) with h | h
  · rw [h.neg_one_pow, if_pos (by simpa [beq_iff_eq, Nat.even_iff] using h)]
  · rw [h.neg_one_pow, if_neg (by simpa [beq_iff_eq, Nat.odd_iff] using h)]

/-- **Correctness.** -/
theorem res_eq : ∀ (fuel : ℕ) (g h : List ℚ), Stripped g → Stripped h → h.length < fuel →
    res fuel g h = resultant (ofDesc g) (ofDesc h)
  | 0, _, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | fuel + 1, g, [], hg, _, _ => by
    simp only [res, ofDesc, resultant_zero_right, natDegree_zero, pow_zero, mul_one,
      natDegree_ofDesc hg]
    split_ifs with h1
    · rw [show g.length - 1 = 0 by omega, pow_zero]
    · rw [zero_pow (by omega)]
  | fuel + 1, g, [a], hg, ha, _ => by
    have e : ofDesc [a] = C a := by simp [ofDesc]
    show a ^ (g.length - 1) = resultant (ofDesc g) (ofDesc [a])
    rw [e]
    simp only [natDegree_C]
    rw [resultant_C_zero_right, natDegree_ofDesc hg]
  | fuel + 1, g, a :: b :: t, hg, ha, hf => by
    have ha' : a ≠ 0 := ha
    have hm_cons : (a :: b :: t).map (fun x => x / a) = 1 :: (b :: t).map (fun x => x / a) := by
      simp [div_self ha']
    have hmStr : Stripped ((a :: b :: t).map fun x => x / a) := by
      rw [hm_cons]; exact one_ne_zero
    have hHm : ofDesc (a :: b :: t) = C a * ofDesc ((a :: b :: t).map fun x => x / a) := by
      rw [ofDesc_map_div, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha', C_1, one_mul]
    have hHdeg : (ofDesc (a :: b :: t)).natDegree = t.length + 1 := by
      rw [natDegree_ofDesc (show Stripped (a :: b :: t) from ha)]; simp
    have hHmdeg : (ofDesc ((a :: b :: t).map fun x => x / a)).natDegree = t.length + 1 := by
      rw [natDegree_ofDesc hmStr, List.length_map]; simp
    have hGdeg : (ofDesc g).natDegree = g.length - 1 := natDegree_ofDesc hg
    have hHmmon : (ofDesc ((a :: b :: t).map fun x => x / a)).Monic := by
      rw [Monic, leadingCoeff, hHmdeg]
      have := coeff_ofDesc_top 1 ((b :: t).map fun x => x / a)
      rw [← hm_cons] at this
      simpa using this
    obtain ⟨q, hq1, hq2, hq0, hq3, hq4⟩ := rem_spec ((b :: t).map fun x => x / a) g
    rw [← hm_cons] at hq1 hq3 hq4
    simp only [List.length_map, List.length_cons] at hq2 hq0 hq3
    have hlenf : t.length + 1 < fuel := by simpa using hf
    set Hm := ofDesc ((a :: b :: t).map fun x => x / a) with hHmdef
    set R := ofDesc (rem g ((a :: b :: t).map fun x => x / a)) with hRdef
    set G := ofDesc g with hGdef
    -- one step of the algorithm, with the recursive call evaluated
    have hstep : res (fuel + 1) g (a :: b :: t)
        = a ^ (g.length - 1) * (-1) ^ ((g.length - 1) * (t.length + 1)) * resultant Hm R := by
      rw [← res_eq fuel _ _ hmStr hq4 (by omega), ← sign_eq]
      simp only [res, List.length_cons, Nat.add_sub_cancel]
    -- the resultant side
    have hRes : resultant G (ofDesc (a :: b :: t))
        = a ^ (g.length - 1) * (-1) ^ ((g.length - 1) * (t.length + 1)) *
          resultant Hm G (t.length + 1) (g.length - 1) := by
      rw [show resultant G (ofDesc (a :: b :: t))
          = resultant G (ofDesc (a :: b :: t)) G.natDegree (ofDesc (a :: b :: t)).natDegree from rfl,
        hHdeg, hHm, resultant_C_mul_right, resultant_comm G Hm, hGdeg]
      ring
    rw [hstep, hRes]
    congr 1
    by_cases hqz : q = 0
    · rw [hqz, mul_zero, add_zero] at hq1
      rw [show resultant Hm R = resultant Hm R Hm.natDegree R.natDegree from rfl, hHmdeg, ← hq1,
        hGdeg]
    · have hlen : t.length + 2 ≤ g.length := by
        rcases hq0 with h | h
        · exact absurd h hqz
        · omega
      have hRdeg : R.natDegree ≤ t.length := by
        have h1 : R.natDegree ≤ (rem g ((a :: b :: t).map fun x => x / a)).length - 1 :=
          natDegree_ofDesc_le _
        omega
      have hk : g.length - 1 = R.natDegree + (g.length - 1 - R.natDegree) := by omega
      rw [hq1, resultant_add_mul_right Hm R q (t.length + 1) (g.length - 1) (by omega) hHmdeg.le,
        hk, resultant_add_right_deg Hm R (t.length + 1) R.natDegree _ le_rfl, ← hHmdeg,
        hHmmon.coeff_natDegree, one_pow, one_mul]
