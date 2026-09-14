import Sz8.Monodromy.DiscRouche

/-!
Fast replay of `discCheck` by Kronecker packing.

All eight shifted rows of one disc are packed into a single pair of integers: the
coefficient `E_{l,m}` sits at digit `66 l + m` of base `B = 2^b`. The kernel evaluates the
Taylor shift as 66 Horner steps on these huge integers (GMP-accelerated shifts, additions
and small multiplications), then reads the digits back by shift-and-mask. An a-priori bound
`|E_{l,m}| < B/2` (checked cheaply) makes the digits exactly the coefficients, so the packed
check implies `discCheck`.
-/

open Polynomial

namespace Sz8.Monodromy.GaussPoly

/-! ### Integer shifts -/

/-! ### Packed Horner evaluation -/

/-- `A + (2^b + γ) R`. -/
def hstep (b : ℕ) (γ A R : GI) : GI := gadd A (gadd (gshl R b) (gmul γ R))

def hornerP (b : ℕ) (γ : GI) : List GI → GI
  | [] => (0, 0)
  | A :: As => hstep b γ A (hornerP b γ As)

theorem gc_hornerP (b : ℕ) (γ : GI) :
    ∀ As : List GI, gc (hornerP b γ As) = peval As (2 ^ b + gc γ)
  | [] => by simp [hornerP]
  | A :: As => by
    simp only [hornerP, hstep, gc_add, gc_gshl, gc_mul, gc_hornerP b γ As, peval_cons]; ring

/-- Pack rows: entry `i` is `∑_l (Cs_l)_i 2^(66 b l)`. -/
def packCols (b : ℕ) : List (List GI) → List GI
  | [] => []
  | C :: Cs => padd C (pshl (66 * b) (packCols b Cs))

theorem peval_packCols (b : ℕ) :
    ∀ (Cs : List (List GI)) (y : ℂ), peval (packCols b Cs) y = oeval Cs y (2 ^ (66 * b))
  | [], y => by simp [packCols]
  | C :: Cs, y => by
    simp only [packCols, peval_padd, peval_pshl, peval_packCols b Cs y, oeval_cons]

theorem oeval_map_pshift (γ : GI) : ∀ (Cs : List (List GI)) (y σ : ℂ),
    oeval (Cs.map (pshift γ)) y σ = oeval Cs (gc γ + y) σ
  | [], y, σ => by simp
  | C :: Cs, y, σ => by
    simp only [List.map_cons, oeval_cons, peval_pshift, oeval_map_pshift γ Cs y σ]

/-! ### Flattening and exact integer values -/

/-- Pad a row with zeros to length `66`. -/
def pad66 (P : List GI) : List GI := P ++ List.replicate (66 - P.length) (0, 0)

theorem peval_append (l₁ l₂ : List GI) (y : ℂ) :
    peval (l₁ ++ l₂) y = peval l₁ y + y ^ l₁.length * peval l₂ y := by
  induction l₁ with
  | nil => simp
  | cons a as ih => simp only [List.cons_append, peval_cons, ih, List.length_cons]; ring

theorem peval_replicate_zero (n : ℕ) (y : ℂ) : peval (List.replicate n ((0, 0) : GI)) y = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem peval_pad66 (P : List GI) (y : ℂ) : peval (pad66 P) y = peval P y := by
  simp [pad66, peval_append, peval_replicate_zero]

theorem length_pad66 {P : List GI} (h : P.length ≤ 66) : (pad66 P).length = 66 := by
  simp [pad66]; omega

def flat66 : List (List GI) → List GI
  | [] => []
  | P :: Ps => pad66 P ++ flat66 Ps

theorem peval_flat66 (B : ℂ) : ∀ Ps : List (List GI), (∀ P ∈ Ps, P.length ≤ 66) →
    peval (flat66 Ps) B = oeval Ps B (B ^ 66)
  | [], _ => by simp [flat66]
  | P :: Ps, h => by
    simp only [flat66, peval_append, length_pad66 (h P (List.mem_cons_self ..)), peval_pad66,
      peval_flat66 B Ps (fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)), oeval_cons]

/-- Horner value of an integer list at an integer base. -/
def ival (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: as => a + B * ival B as

theorem gc_ival (B : ℤ) : ∀ l : List GI,
    gc (ival B (l.map Prod.fst), ival B (l.map Prod.snd)) = peval l (B : ℂ)
  | [] => by simp [ival]
  | a :: as => by
    have ih := gc_ival B as
    simp only [gc, List.map_cons, ival, peval_cons] at ih ⊢
    rw [← ih]; push_cast; ring

theorem gc_injective : Function.Injective gc := by
  intro a b h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [gc] at hre him
  exact Prod.ext hre him

/-! ### Digits -/

/-- `k` base-`2^b` digits of `n`. -/
def digits (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, n => (n &&& (2 ^ b - 1)) :: digits b k (n >>> b)

theorem length_digits (b : ℕ) : ∀ n m, (digits b n m).length = n
  | 0, _ => rfl
  | n + 1, m => by simp [digits, length_digits b n]

/-- `∑_{i<k} 2^(b-1) 2^(b i)`, the offset making balanced digits nonnegative. -/
def offset (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 ^ (b - 1) + 2 ^ b * offset b k

theorem ival_offset_nonneg (b : ℕ) : ∀ (e : List ℤ), (∀ x ∈ e, |x| < 2 ^ (b - 1)) →
    0 ≤ ival (2 ^ b) e + offset b e.length
  | [], _ => by simp [ival, offset]
  | x :: e, h => by
    have hx := abs_lt.mp (h x (List.mem_cons_self ..))
    have ih := ival_offset_nonneg b e (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have : ival (2 ^ b) (x :: e) + offset b (x :: e).length =
        (x + 2 ^ (b - 1)) + 2 ^ b * (ival (2 ^ b) e + offset b e.length) := by
      simp only [ival, List.length_cons, offset]; push_cast; ring
    rw [this]
    have : (0 : ℤ) ≤ 2 ^ b * (ival (2 ^ b) e + offset b e.length) := by positivity
    linarith

/-- Balanced digits are recovered exactly. -/
theorem digits_ival (b : ℕ) (hb : 0 < b) : ∀ (e : List ℤ), (∀ x ∈ e, |x| < 2 ^ (b - 1)) →
    digits b e.length (ival (2 ^ b) e + offset b e.length).toNat =
      e.map fun x => (x + 2 ^ (b - 1)).toNat
  | [], _ => by simp [digits]
  | x :: e, h => by
    have hx := h x (List.mem_cons_self ..)
    have hsub : ∀ y ∈ e, |y| < 2 ^ (b - 1) := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have ih := digits_ival b hb e hsub
    have hrest := ival_offset_nonneg b e hsub
    have hpos : (2 : ℤ) ^ (b - 1) ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) (by omega)
    have hdig : 0 ≤ x + 2 ^ (b - 1) ∧ x + 2 ^ (b - 1) < 2 ^ b := by
      have := abs_lt.mp hx
      constructor
      · linarith
      · have hb2 : (2 : ℤ) ^ b = 2 ^ (b - 1) + 2 ^ (b - 1) := by
          rw [← two_mul, ← pow_succ']; congr 1; omega
        linarith
    have hval : ival (2 ^ b) (x :: e) + offset b (x :: e).length =
        (x + 2 ^ (b - 1)) + 2 ^ b * (ival (2 ^ b) e + offset b e.length) := by
      simp only [ival, List.length_cons, offset]; push_cast; ring
    rw [hval]
    set r := ival (2 ^ b) e + offset b e.length
    set d := x + 2 ^ (b - 1)
    have hn : (d + 2 ^ b * r).toNat = d.toNat + 2 ^ b * r.toNat := by
      have : d + 2 ^ b * r = ((d.toNat + 2 ^ b * r.toNat : ℕ) : ℤ) := by
        push_cast; rw [Int.toNat_of_nonneg hdig.1, Int.toNat_of_nonneg hrest]
      rw [this, Int.toNat_natCast]
    have hdlt : d.toNat < 2 ^ b := by
      have : (d.toNat : ℤ) < 2 ^ b := by rw [Int.toNat_of_nonneg hdig.1]; exact hdig.2
      exact_mod_cast this
    simp only [List.length_cons, digits, List.map_cons, hn]
    congr 1
    · rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdlt]
    · rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt hdlt, zero_add]
      exact ih

/-! ### A-priori coefficient bound for the Taylor shift -/

theorem n1_gadd_le (a b : GI) : n1 (gadd a b) ≤ n1 a + n1 b := by
  simp only [n1, gadd]; have := Int.natAbs_add_le a.1 b.1; have := Int.natAbs_add_le a.2 b.2
  omega

theorem n1_gmul_le (a b : GI) : n1 (gmul a b) ≤ n1 a * n1 b := by
  simp only [n1, gmul]
  have h1 := Int.natAbs_sub_le (a.1 * b.1) (a.2 * b.2)
  have h2 := Int.natAbs_add_le (a.1 * b.2) (a.2 * b.1)
  simp only [Int.natAbs_mul] at h1 h2
  nlinarith

theorem n1_padd_le {P Q : List GI} {bP bQ : ℕ} (hP : ∀ x ∈ P, n1 x ≤ bP)
    (hQ : ∀ x ∈ Q, n1 x ≤ bQ) : ∀ x ∈ padd P Q, n1 x ≤ bP + bQ := by
  induction P generalizing Q with
  | nil => intro x hx; exact (hQ x hx).trans (Nat.le_add_left _ _)
  | cons a as ih =>
    cases Q with
    | nil => intro x hx; exact (hP x hx).trans (Nat.le_add_right _ _)
    | cons c cs =>
      intro x hx
      simp only [padd, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact (n1_gadd_le _ _).trans (Nat.add_le_add (hP a (by simp)) (hQ c (by simp)))
      · exact ih (fun y hy => hP y (by simp [hy])) (fun y hy => hQ y (by simp [hy])) x hx

theorem n1_pmulC_le (c : GI) {S : List GI} {bS : ℕ} (hS : ∀ x ∈ S, n1 x ≤ bS) :
    ∀ x ∈ pmulC c S, n1 x ≤ n1 c * bS := by
  induction S with
  | nil => simp [pmulC]
  | cons a as ih =>
    intro x hx
    simp only [pmulC, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact (n1_gmul_le _ _).trans (Nat.mul_le_mul_left _ (hS a (by simp)))
    · exact ih (fun y hy => hS y (by simp [hy])) x hx

/-- Every coefficient of `p(γ + w)` is bounded by `∑ n1(a_i) (1 + n1 γ)^i`. -/
theorem n1_pshift_le (γ : GI) : ∀ (p : List GI), ∀ x ∈ pshift γ p, n1 x ≤ maj (1 + n1 γ) p
  | [] => by simp [pshift]
  | a :: as => by
    have ih := n1_pshift_le γ as
    intro x hx
    simp only [pshift, shiftStep] at hx
    have h1 : ∀ y ∈ padd [a] (pmulC γ (pshift γ as)), n1 y ≤ n1 a + n1 γ * maj (1 + n1 γ) as :=
      n1_padd_le (by simp) (n1_pmulC_le γ ih)
    have h2 : ∀ y ∈ ((0, 0) :: pshift γ as), n1 y ≤ maj (1 + n1 γ) as := by
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · simp [n1]
      · exact ih y hy
    have := n1_padd_le h1 h2 x hx
    simp only [maj]
    nlinarith

/-! ### Lengths -/

theorem length_padd : ∀ P Q : List GI, (padd P Q).length = max P.length Q.length
  | [], Q => by simp [padd]
  | a :: as, [] => by simp [padd]
  | a :: as, b :: bs => by simp [padd, length_padd as bs, Nat.succ_max_succ]

theorem length_pmulC (c : GI) : ∀ P : List GI, (pmulC c P).length = P.length
  | [] => rfl
  | a :: as => by simp [pmulC, length_pmulC c as]

theorem length_pshift (γ : GI) : ∀ P : List GI, (pshift γ P).length = P.length
  | [] => rfl
  | a :: as => by
    simp only [pshift, shiftStep, length_padd, length_pmulC, length_pshift γ as, List.length_cons,
      List.length_nil]
    simp only [Nat.max_def]
    split_ifs <;> omega

theorem length_scaleUp (K : ℕ) : ∀ (n : ℕ) (P : List GI), (scaleUp K n P).length = P.length
  | _, [] => rfl
  | n, a :: as => by simp [scaleUp, length_scaleUp K (n - 1) as]

theorem length_flat66 : ∀ Ps : List (List GI), (∀ P ∈ Ps, P.length ≤ 66) →
    (flat66 Ps).length = 66 * Ps.length
  | [], _ => rfl
  | P :: Ps, h => by
    simp only [flat66, List.length_append, length_pad66 (h P (List.mem_cons_self ..)),
      length_flat66 Ps (fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)), List.length_cons]
    ring

theorem mem_flat66 {x : GI} : ∀ {Ps : List (List GI)}, x ∈ flat66 Ps → ∃ P ∈ Ps, x ∈ pad66 P
  | [], h => by simp [flat66] at h
  | P :: Ps, h => by
    simp only [flat66, List.mem_append] at h
    rcases h with h | h
    · exact ⟨P, List.mem_cons_self .., h⟩
    · obtain ⟨Q, hQ, hx⟩ := mem_flat66 h
      exact ⟨Q, List.mem_cons_of_mem _ hQ, hx⟩

/-! ### Majorants of flattened rows -/

theorem maj_replicate_zero (W n : ℕ) : maj W (List.replicate n ((0, 0) : GI)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, maj, n1, ih]

theorem maj_append_zeros (W : ℕ) : ∀ (P : List GI) (n : ℕ),
    maj W (P ++ List.replicate n (0, 0)) = maj W P
  | [], n => by simp [maj_replicate_zero, maj]
  | a :: as, n => by simp [maj, maj_append_zeros W as n]

/-- `∑_l S^l maj W (row l)`, reading rows of 66 from a flat list. -/
def majFlat (S W : ℕ) : ℕ → List GI → ℕ
  | 0, _ => 0
  | k + 1, l => maj W (l.take 66) + S * majFlat S W k (l.drop 66)

theorem majFlat_flat66 (S W : ℕ) : ∀ Ps : List (List GI), (∀ P ∈ Ps, P.length ≤ 66) →
    majFlat S W Ps.length (flat66 Ps) = omaj S W Ps
  | [], _ => rfl
  | P :: Ps, h => by
    have hP := length_pad66 (h P (List.mem_cons_self ..))
    simp only [List.length_cons, majFlat, flat66]
    rw [List.take_left' hP, List.drop_left' hP,
      majFlat_flat66 S W Ps (fun Q hQ => h Q (List.mem_cons_of_mem _ hQ))]
    simp only [omaj, pad66, maj_append_zeros]

/-- Kill the linear coefficient of one row. -/
def killRow : List GI → List GI
  | [] => []
  | a :: [] => [a]
  | a :: _ :: rest => a :: (0, 0) :: rest

theorem kill01_cons (P : List GI) (Ps : List (List GI)) : kill01 (P :: Ps) = killRow P :: Ps := by
  rcases P with _ | ⟨a, _ | ⟨c, rest⟩⟩ <;> rfl

theorem length_killRow (P : List GI) : (killRow P).length = P.length := by
  rcases P with _ | ⟨a, _ | ⟨c, rest⟩⟩ <;> rfl

theorem pad66_killRow (P : List GI) : pad66 (killRow P) = (pad66 P).set 1 (0, 0) := by
  rcases P with _ | ⟨a, _ | ⟨c, rest⟩⟩
  · simp [pad66, killRow, List.replicate_succ]
  · simp [pad66, killRow, List.replicate_succ]
  · simp [pad66, killRow]

theorem flat66_kill01 (P : List GI) (Ps : List (List GI)) (h : P.length ≤ 66) :
    flat66 (kill01 (P :: Ps)) = (flat66 (P :: Ps)).set 1 (0, 0) := by
  have hlen := length_pad66 h
  rw [kill01_cons]
  simp only [flat66]
  rw [List.set_append_left _ _ (by omega), pad66_killRow]

theorem coeff01_eq_getD (P : List GI) (Ps : List (List GI)) (h : P.length ≤ 66) :
    coeff01 (P :: Ps) = (flat66 (P :: Ps)).getD 1 (0, 0) := by
  have hlen := length_pad66 h
  simp only [coeff01, List.headD, flat66, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]
  rcases P with _ | ⟨a, _ | ⟨c, rest⟩⟩
  · simp [pad66, List.replicate_succ]
  · simp [pad66, List.replicate_succ]
  · simp [pad66]

/-! ### The packed check -/

/-- Decode balanced digits into Gaussian integers. -/
def decodeFlat (b : ℕ) (dr di : List ℕ) : List GI :=
  List.zipWith
    (fun (r i : ℕ) => ((r : ℤ) - ((2 ^ (b - 1) : ℕ) : ℤ), (i : ℤ) - ((2 ^ (b - 1) : ℕ) : ℤ)))
    dr di

/-- `|d - h|` in `ℕ`. -/
def dabs (h d : ℕ) : ℕ := if h ≤ d then d - h else h - d

/-- Majorant of one row, read directly from real and imaginary digits. -/
def majDig (W h : ℕ) : List ℕ → List ℕ → ℕ
  | r :: rs, i :: is => (dabs h r + dabs h i) + W * majDig W h rs is
  | _, _ => 0

/-- Majorant of all rows (66 digits each), read directly from digits. -/
def majFlatDig (S W h : ℕ) : ℕ → List ℕ → List ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, dr, di => majDig W h (dr.take 66) (di.take 66) +
      S * majFlatDig S W h k (dr.drop 66) (di.drop 66)

/-- The disc check replayed on packed integers `A` (the packed scaled rows, computed once
per step). The a-priori digit bound is checked once per step, in `stepPre`. -/
def packedCheck (A : List GI) (b S : ℕ) (γ : GI) (W : ℕ) : Bool :=
  let R := hornerP b γ A
  let dr := digits b 528 (R.1 + offset b 528).toNat
  let di := digits b 528 (R.2 + offset b 528).toNat
  let e := (decodeFlat b dr di).getD 1 (0, 0)
  decide (0 < W) &&
    decide ((((majFlatDig S W (2 ^ (b - 1)) 8 dr di - n1 e * W : ℕ) : ℤ)) ^ 2 < nsq e * W ^ 2)

theorem n1_decode (b r i : ℕ) :
    n1 ((r : ℤ) - ((2 ^ (b - 1) : ℕ) : ℤ), (i : ℤ) - ((2 ^ (b - 1) : ℕ) : ℤ)) =
      dabs (2 ^ (b - 1)) r + dabs (2 ^ (b - 1)) i := by
  simp only [n1, dabs]
  split_ifs <;> omega

theorem majDig_eq (W b : ℕ) : ∀ (dr di : List ℕ), dr.length = di.length →
    majDig W (2 ^ (b - 1)) dr di = maj W (decodeFlat b dr di)
  | [], [], _ => rfl
  | r :: rs, i :: is, h => by
    have hd : decodeFlat b (r :: rs) (i :: is) =
        ((r : ℤ) - ((2 ^ (b - 1) : ℕ) : ℤ), (i : ℤ) - ((2 ^ (b - 1) : ℕ) : ℤ)) ::
          decodeFlat b rs is := rfl
    rw [hd, majDig, maj, n1_decode, majDig_eq W b rs is (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem majFlatDig_eq (S W b : ℕ) : ∀ (k : ℕ) (dr di : List ℕ), dr.length = di.length →
    majFlatDig S W (2 ^ (b - 1)) k dr di = majFlat S W k (decodeFlat b dr di)
  | 0, _, _, _ => rfl
  | k + 1, dr, di, h => by
    have ht : (decodeFlat b dr di).take 66 = decodeFlat b (dr.take 66) (di.take 66) := by
      unfold decodeFlat; exact List.take_zipWith
    have hd : (decodeFlat b dr di).drop 66 = decodeFlat b (dr.drop 66) (di.drop 66) := by
      unfold decodeFlat; exact List.drop_zipWith
    rw [majFlatDig, majFlat, ht, hd, majDig_eq W b _ _ (by simp [h]),
      majFlatDig_eq S W b k _ _ (by simp [h])]

/-- `omaj` splits off the killed coefficient. -/
theorem omaj_kill01 (S W : ℕ) (P : List GI) (Ps : List (List GI)) :
    omaj S W (P :: Ps) = omaj S W (kill01 (P :: Ps)) + n1 (coeff01 (P :: Ps)) * W := by
  rcases P with _ | ⟨a, _ | ⟨c, rest⟩⟩ <;> simp [omaj, kill01, coeff01, maj, n1]; ring

theorem maj_mono {W W' : ℕ} (hW : W ≤ W') : ∀ P : List GI, maj W P ≤ maj W' P
  | [] => le_rfl
  | a :: as => by
    simp only [maj]
    exact Nat.add_le_add_left (Nat.mul_le_mul hW (maj_mono hW as)) _

theorem decodeFlat_map (b : ℕ) (F₁ F₂ : GI → ℕ) : ∀ l : List GI,
    decodeFlat b (l.map F₁) (l.map F₂) =
      l.map fun x => ((F₁ x : ℤ) - ((2 ^ (b - 1) : ℕ) : ℤ), (F₂ x : ℤ) - ((2 ^ (b - 1) : ℕ) : ℤ))
  | [] => rfl
  | x :: l => by
    have ih := decodeFlat_map b F₁ F₂ l
    simp only [decodeFlat, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih]

theorem decodeFlat_digits (b : ℕ) (hb : 0 < b) (flat : List GI)
    (hbound : ∀ x ∈ flat, |x.1| < 2 ^ (b - 1) ∧ |x.2| < 2 ^ (b - 1)) :
    decodeFlat b
      (digits b flat.length (ival (2 ^ b) (flat.map Prod.fst) + offset b flat.length).toNat)
      (digits b flat.length (ival (2 ^ b) (flat.map Prod.snd) + offset b flat.length).toNat) =
      flat := by
  have h1 := digits_ival b hb (flat.map Prod.fst) (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact (hbound x hx).1)
  have h2 := digits_ival b hb (flat.map Prod.snd) (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact (hbound x hx).2)
  simp only [List.length_map, List.map_map] at h1 h2
  rw [h1, h2, decodeFlat_map]
  conv_rhs => rw [← List.map_id flat]
  refine List.map_congr_left fun x hx => ?_
  have hx1 := abs_lt.mp (hbound x hx).1
  have hx2 := abs_lt.mp (hbound x hx).2
  simp only [Function.comp_apply, id]
  rw [Int.toNat_of_nonneg (by linarith), Int.toNat_of_nonneg (by linarith)]
  simp

/-- Soundness of packing: the packed check implies the list check. -/
theorem discCheck_of_packedCheck (D : List (List GI)) (K b S : ℕ) (γ : GI) (W : ℕ)
    (hb : 0 < b) (hD : D.length = 8) (hshort : rowsShort D = true)
    (hcrude : ∀ C ∈ D.map (scaleUp K 65), maj (1 + n1 γ) C < 2 ^ (b - 1))
    (h : packedCheck (packCols b (D.map (scaleUp K 65))) b S γ W = true) :
    discCheck D K S γ W = true := by
  set Cs := D.map (scaleUp K 65)
  set E := discRows K γ D with hE
  have hECs : E = Cs.map (pshift γ) := by simp [hE, discRows, Cs, List.map_map]
  simp only [packedCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hW, hdom⟩ := h
  have hDlen : ∀ P ∈ D, P.length ≤ 66 := fun P hP => by
    simpa using List.all_eq_true.mp hshort P hP
  have hElen : ∀ P ∈ E, P.length ≤ 66 := by
    intro P hP
    simp only [hE, discRows, List.mem_map] at hP
    obtain ⟨Q, hQ, rfl⟩ := hP
    rw [length_pshift, length_scaleUp]; exact hDlen Q hQ
  have hElength : E.length = 8 := by simp [hE, discRows, hD]
  have hflatlen : (flat66 E).length = 528 := by rw [length_flat66 E hElen, hElength]
  have hR : hornerP b γ (packCols b Cs) =
      (ival (2 ^ b) ((flat66 E).map Prod.fst), ival (2 ^ b) ((flat66 E).map Prod.snd)) := by
    apply gc_injective
    rw [gc_hornerP, peval_packCols, gc_ival, peval_flat66 _ E hElen, hECs, oeval_map_pshift]
    push_cast
    rw [← pow_mul, add_comm (gc γ), mul_comm b 66]
  have hbound : ∀ x ∈ flat66 E, |x.1| < 2 ^ (b - 1) ∧ |x.2| < 2 ^ (b - 1) := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := mem_flat66 hx
    have hn : n1 x < 2 ^ (b - 1) := by
      rw [hECs, List.mem_map] at hP
      obtain ⟨C, hC, rfl⟩ := hP
      simp only [pad66, List.mem_append, List.mem_replicate] at hxP
      rcases hxP with hxP | ⟨-, rfl⟩
      · exact (n1_pshift_le γ C x hxP).trans_lt (hcrude C hC)
      · simp [n1]
    simp only [n1] at hn
    constructor
    · rw [Int.abs_eq_natAbs]; exact_mod_cast (by omega : x.1.natAbs < 2 ^ (b - 1))
    · rw [Int.abs_eq_natAbs]; exact_mod_cast (by omega : x.2.natAbs < 2 ^ (b - 1))
  have hflat := decodeFlat_digits b hb (flat66 E) hbound
  rw [hflatlen] at hflat
  set dr := digits b 528 (ival (2 ^ b) ((flat66 E).map Prod.fst) + offset b 528).toNat
  set di := digits b 528 (ival (2 ^ b) ((flat66 E).map Prod.snd) + offset b 528).toNat
  have hlen : dr.length = di.length := by
    rw [length_digits, length_digits]
  rw [hR] at hdom
  simp only at hdom
  rw [majFlatDig_eq S W b 8 dr di hlen, hflat] at hdom
  obtain ⟨P, Ps, hPPs⟩ := List.exists_cons_of_ne_nil (fun h0 : E = [] => by
    rw [h0] at hElength; simp at hElength)
  have hPlen : P.length ≤ 66 := hElen P (by simp [hPPs])
  rw [hPPs, ← coeff01_eq_getD P Ps hPlen, ← hPPs,
    ← hElength, majFlat_flat66 S W E hElen, hPPs, omaj_kill01, ← hPPs,
    Nat.add_sub_cancel] at hdom
  simp only [discCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hW, hdom⟩

end Sz8.Monodromy.GaussPoly
