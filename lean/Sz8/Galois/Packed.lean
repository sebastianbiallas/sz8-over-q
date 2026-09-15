import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Packed polynomials: soundness of Kronecker-packed identities

A bivariate polynomial over `ℕ` with coefficients below `2^64` and `t`-degree below `W` is stored
as one natural number: coefficient `(k, j)` (of `X^k t^j`) in 64-bit slot `k W + j`. The Kronecker
map `κ W` (`t ↦ 2^64`, `X ↦ 2^(64 W)`) is a semiring homomorphism, so a `Nat` identity between
packed literals is `κ` of a polynomial identity. This file proves the converse direction that a
certificate needs:

* `κ_decB`: `κ` of the decoding of a literal is the literal;
* `eq_of_κ_eq`: `κ` is injective on polynomials with coefficients `< 2^64` and `t`-degree `< W`;
* `Bd`: coefficient and degree bounds, closed under `+` and `*`, so that both sides of a
  checked identity are shown to be in the injective range;
* `block_lt`: a single `&&&` with a periodic mask bounds every slot, which is how the bounds on
  the literals are checked in the kernel in `O(1)` big-number operations.
-/

open Polynomial Finset

namespace Sz8.Galois.Packed

/-! ### Base-`B` digits of polynomial values -/

theorem eval_div_mod {B : ℕ} (P : ℕ[X]) (hP : ∀ i, P.coeff i < B) (i : ℕ) :
    P.eval B / B ^ i % B = P.coeff i := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hP 0)
  induction i generalizing P with
  | zero =>
    conv_lhs => rw [← divX_mul_X_add P]
    simp only [eval_add, eval_mul, eval_X, eval_C, pow_zero, Nat.div_one]
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (hP 0)]
  | succ i ih =>
    conv_lhs => rw [← divX_mul_X_add P]
    simp only [eval_add, eval_mul, eval_X, eval_C]
    rw [pow_succ', ← Nat.div_div_eq_div_mul,
      show ((divX P).eval B * B + P.coeff 0) / B = (divX P).eval B by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt (hP 0), zero_add],
      ih (divX P) (fun j => by rw [coeff_divX]; exact hP _), coeff_divX]

theorem eval_lt {B : ℕ} (_hB : 0 < B) (n : ℕ) :
    ∀ P : ℕ[X], (∀ i, P.coeff i < B) → (∀ i, n ≤ i → P.coeff i = 0) → P.eval B < B ^ n := by
  induction n with
  | zero =>
    intro P _ h0
    have : P = 0 := Polynomial.ext fun i => by simpa using h0 i (Nat.zero_le _)
    simp [this]
  | succ n ih =>
    intro P hP h0
    have h1 := ih (divX P) (fun j => by rw [coeff_divX]; exact hP _)
      (fun j hj => by rw [coeff_divX]; exact h0 _ (by omega))
    rw [← divX_mul_X_add P]
    simp only [eval_add, eval_mul, eval_X, eval_C]
    have := hP 0
    calc (divX P).eval B * B + P.coeff 0 < (divX P).eval B * B + B := by omega
      _ = ((divX P).eval B + 1) * B := by ring
      _ ≤ B ^ n * B := Nat.mul_le_mul_right _ h1
      _ = B ^ (n + 1) := by ring

theorem sum_digits {B : ℕ} (hB : 0 < B) (n : ℕ) :
    ∀ r, r < B ^ n → ∑ j ∈ range n, r / B ^ j % B * B ^ j = r := by
  induction n with
  | zero => intro r hr; simp at hr; simp [hr]
  | succ n ih =>
    intro r hr
    rw [sum_range_succ']
    have hq : r / B < B ^ n := by
      rw [Nat.div_lt_iff_lt_mul hB]; simpa [pow_succ] using hr
    have e : ∀ j ∈ range n, r / B ^ (j + 1) % B * B ^ (j + 1) = B * (r / B / B ^ j % B * B ^ j) := by
      intro j _
      rw [pow_succ', ← Nat.div_div_eq_div_mul]; ring
    rw [sum_congr rfl e, ← mul_sum, ih _ hq]
    simp only [pow_zero, Nat.div_one, mul_one]
    rw [Nat.add_comm]; exact Nat.mod_add_div r B

/-! ### Decoding -/

/-- Digit `i` of `x` in base `2^s`. -/
def dig (s x i : ℕ) : ℕ := x / (2 ^ s) ^ i % 2 ^ s

/-- A `t`-polynomial from the first `n` 64-bit slots of `x`. -/
noncomputable def decU (x n : ℕ) : ℕ[X] := ∑ j ∈ range n, C (dig 64 x j) * X ^ j

/-- A bivariate polynomial from `nx` rows of `W` slots of `x`. -/
noncomputable def decB (x nx W : ℕ) : ℕ[X][X] :=
  ∑ k ∈ range nx, C (decU (dig (64 * W) x k) W) * X ^ k

theorem coeff_decU (x n j : ℕ) : (decU x n).coeff j = if j < n then dig 64 x j else 0 := by
  simp only [decU, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]; simp

theorem coeff_decB (x nx W k : ℕ) :
    (decB x nx W).coeff k = if k < nx then decU (dig (64 * W) x k) W else 0 := by
  simp only [decB, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]; simp

/-- The Kronecker map `t ↦ 2^64`, `X ↦ 2^(64 W)`. -/
noncomputable def κ (W : ℕ) : ℕ[X][X] →+* ℕ :=
  (evalRingHom (2 ^ (64 * W))).comp (mapRingHom (evalRingHom (2 ^ 64)))

theorem κ_apply (W : ℕ) (P : ℕ[X][X]) :
    κ W P = (P.map (evalRingHom (2 ^ 64))).eval (2 ^ (64 * W)) := rfl

theorem eval_decU (x W : ℕ) (hx : x < 2 ^ (64 * W)) : (decU x W).eval (2 ^ 64) = x := by
  simp only [decU, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, dig]
  exact sum_digits (by positivity) W x (by rwa [← pow_mul])

theorem κ_decB (x nx W : ℕ) (hx : x < 2 ^ (64 * W * nx)) : κ W (decB x nx W) = x := by
  rw [κ_apply, decB, Polynomial.map_sum]
  simp only [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, eval_finset_sum, eval_mul,
    eval_C, eval_pow, eval_X, coe_evalRingHom]
  have hrow : ∀ k, dig (64 * W) x k < 2 ^ (64 * W) := fun k => Nat.mod_lt _ (by positivity)
  rw [sum_congr rfl fun k _ => by rw [eval_decU _ W (hrow k)]]
  have hx' : x < (2 ^ (64 * W)) ^ nx := by rwa [← pow_mul]
  exact sum_digits (by positivity) nx x hx'

/-! ### Injectivity of `κ` in the bounded range -/

theorem eq_of_κ_eq {W : ℕ} {P Q : ℕ[X][X]}
    (hP : ∀ k j, (P.coeff k).coeff j < 2 ^ 64) (hPd : ∀ k, (P.coeff k).natDegree < W)
    (hQ : ∀ k j, (Q.coeff k).coeff j < 2 ^ 64) (hQd : ∀ k, (Q.coeff k).natDegree < W)
    (h : κ W P = κ W Q) : P = Q := by
  have hval : ∀ (R : ℕ[X][X]), (∀ k j, (R.coeff k).coeff j < 2 ^ 64) →
      (∀ k, (R.coeff k).natDegree < W) → ∀ k,
      (R.coeff k).eval (2 ^ 64) = κ W R / (2 ^ (64 * W)) ^ k % 2 ^ (64 * W) := by
    intro R hR hRd k
    rw [κ_apply, eval_div_mod]
    · simp
    · intro i
      rw [coeff_map, coe_evalRingHom, pow_mul]
      exact eval_lt (by positivity) W _ (hR i) fun j hj =>
        coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hRd i) hj)
  ext k j
  have hk : (P.coeff k).eval (2 ^ 64) = (Q.coeff k).eval (2 ^ 64) := by
    rw [hval P hP hPd, hval Q hQ hQd, h]
  have := congrArg (fun v => v / (2 ^ 64) ^ j % 2 ^ 64) hk
  simpa only [eval_div_mod _ (hP k), eval_div_mod _ (hQ k)] using this

/-! ### Bounds closed under `+` and `*` -/

/-- Coefficients `≤ α`, `X`-degree `≤ dx`, `t`-degree `≤ dt`. -/
structure Bd (P : ℕ[X][X]) (α dx dt : ℕ) : Prop where
  coeff_le : ∀ k j, (P.coeff k).coeff j ≤ α
  xdeg : P.natDegree ≤ dx
  tdeg : ∀ k, (P.coeff k).natDegree ≤ dt

theorem Bd.mono {P : ℕ[X][X]} {α dx dt α' dx' dt' : ℕ} (h : Bd P α dx dt) (hα : α ≤ α')
    (hx : dx ≤ dx') (ht : dt ≤ dt') : Bd P α' dx' dt' :=
  ⟨fun k j => (h.coeff_le k j).trans hα, h.xdeg.trans hx, fun k => (h.tdeg k).trans ht⟩

theorem Bd.add {P Q : ℕ[X][X]} {α dx dt β ex et : ℕ} (hP : Bd P α dx dt) (hQ : Bd Q β ex et) :
    Bd (P + Q) (α + β) (max dx ex) (max dt et) where
  coeff_le k j := by
    simp only [coeff_add]; exact Nat.add_le_add (hP.coeff_le k j) (hQ.coeff_le k j)
  xdeg := (natDegree_add_le _ _).trans (max_le_max hP.xdeg hQ.xdeg)
  tdeg k := by
    simp only [coeff_add]; exact (natDegree_add_le _ _).trans (max_le_max (hP.tdeg k) (hQ.tdeg k))

/-- A sum over an antidiagonal of terms that vanish unless the first index is `≤ d`. -/
theorem sum_antidiagonal_le {f : ℕ × ℕ → ℕ} {n d M : ℕ} (h0 : ∀ x, d < x.1 → f x = 0)
    (hM : ∀ x, f x ≤ M) : ∑ x ∈ antidiagonal n, f x ≤ (d + 1) * M := by
  rw [← sum_filter_of_ne (p := fun x => x.1 ≤ d) fun x _ hx => by
    by_contra h; exact hx (h0 x (by omega))]
  refine (sum_le_card_nsmul _ _ M fun x _ => hM x).trans ?_
  rw [smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  have : ((antidiagonal n).filter fun x => x.1 ≤ d).card ≤ (range (d + 1)).card :=
    card_le_card_of_injOn (fun x => x.1) (fun x hx => by
      simp only [coe_filter, Set.mem_setOf_eq, mem_antidiagonal] at hx
      simpa using Nat.lt_succ_of_le hx.2)
      (fun x hx y hy hxy => by
        simp only [coe_filter, Set.mem_setOf_eq, mem_antidiagonal] at hx hy
        ext <;> simp_all; omega)
  simpa using this

theorem Bd.mul {P Q : ℕ[X][X]} {α dx dt β ex et : ℕ} (hP : Bd P α dx dt) (hQ : Bd Q β ex et) :
    Bd (P * Q) ((dx + 1) * ((dt + 1) * (α * β))) (dx + ex) (dt + et) where
  coeff_le k j := by
    rw [coeff_mul, finsetSum_coeff]
    refine sum_antidiagonal_le (d := dx) (fun x hx => ?_) (fun x => ?_)
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP.xdeg hx)]; simp
    · rw [coeff_mul]
      refine sum_antidiagonal_le (d := dt) (fun y hy => ?_) (fun y => ?_)
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hP.tdeg _) hy)]; simp
      · exact Nat.mul_le_mul (hP.coeff_le _ _) (hQ.coeff_le _ _)
  xdeg := natDegree_mul_le.trans (Nat.add_le_add hP.xdeg hQ.xdeg)
  tdeg k := by
    rw [coeff_mul]
    refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
    exact natDegree_mul_le.trans (Nat.add_le_add (hP.tdeg _) (hQ.tdeg _))

theorem Bd_C (c : ℕ) : Bd (C (C c)) c 0 0 where
  coeff_le k j := by
    rw [coeff_C]; split_ifs
    · rw [coeff_C]; split_ifs <;> simp
    · simp
  xdeg := by simp
  tdeg k := by rw [coeff_C]; split_ifs <;> simp

theorem Bd_X : Bd (X : ℕ[X][X]) 1 1 0 where
  coeff_le k j := by
    rw [coeff_X]; split_ifs
    · rw [coeff_one]; split_ifs <;> simp
    · simp
  xdeg := natDegree_X_le
  tdeg k := by rw [coeff_X]; split_ifs <;> simp

/-- Equal images under `κ` and bounds below `2^64` and `W` give equal polynomials. -/
theorem eq_of_κ_eq_Bd {W : ℕ} {P Q : ℕ[X][X]} {α dx dt β ex et : ℕ} (hP : Bd P α dx dt)
    (hQ : Bd Q β ex et) (hα : α < 2 ^ 64) (hβ : β < 2 ^ 64) (hdt : dt < W) (het : et < W)
    (h : κ W P = κ W Q) : P = Q :=
  eq_of_κ_eq (fun k j => lt_of_le_of_lt (hP.coeff_le k j) hα)
    (fun k => lt_of_le_of_lt (hP.tdeg k) hdt) (fun k j => lt_of_le_of_lt (hQ.coeff_le k j) hβ)
    (fun k => lt_of_le_of_lt (hQ.tdeg k) het) h

/-! ### Slot bounds from one mask -/

/-- `k` blocks of `s` bits, each equal to `1`. -/
def ones (s k : ℕ) : ℕ := (2 ^ (s * k) - 1) / (2 ^ s - 1)

theorem ones_eq (s k : ℕ) (hs : 0 < s) : ones s k = ∑ i ∈ range k, (2 ^ s) ^ i := by
  rw [ones, Nat.geomSum_eq (by
    have : 2 ≤ 2 ^ s := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    exact this), pow_mul]

/-- The mask with bits `b..s-1` of each of `k` blocks of `s` bits set. -/
def mask (s b k : ℕ) : ℕ := ones s k * ((2 ^ (s - b) - 1) <<< b)

theorem lt_of_and_eq_zero {n s b : ℕ} (hb : b ≤ s) (hn : n < 2 ^ s)
    (h : n &&& ((2 ^ (s - b) - 1) <<< b) = 0) : n < 2 ^ b := by
  refine Nat.lt_pow_two_of_testBit n fun j hj => ?_
  by_cases hjs : j < s
  · have := congrArg (fun m => m.testBit j) h
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
      Nat.zero_testBit] at this
    simpa [hj, show j - b < s - b by omega] using this
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem block_lt {s b k x : ℕ} (hs : 0 < s) (hb : b ≤ s) (hx : x &&& mask s b k = 0) {i : ℕ}
    (hi : i < k) : dig s x i < 2 ^ b := by
  set c := (2 ^ (s - b) - 1) <<< b with hc
  have hcs : c < 2 ^ s := by
    rw [hc, Nat.shiftLeft_eq]
    have h1 : 2 ^ (s - b) - 1 < 2 ^ (s - b) := Nat.sub_lt (by positivity) (by norm_num)
    calc (2 ^ (s - b) - 1) * 2 ^ b < 2 ^ (s - b) * 2 ^ b :=
          Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 2 ^ s := by rw [← pow_add, Nat.sub_add_cancel hb]
  -- the mask as a polynomial value
  have hmask : mask s b k = (∑ i ∈ range k, C c * X ^ i : ℕ[X]).eval (2 ^ s) := by
    simp only [mask, ones_eq s k hs, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, sum_mul]
    exact sum_congr rfl fun _ _ => mul_comm _ _
  have hdigM : dig s (mask s b k) i = c := by
    rw [dig, hmask, eval_div_mod]
    · simp [finsetSum_coeff, hi]
    · intro j
      simp only [finsetSum_coeff, coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq]; split_ifs
      exacts [hcs, by positivity]
  have hand : dig s x i &&& dig s (mask s b k) i = 0 := by
    have : dig s (x &&& mask s b k) i = 0 := by rw [hx]; simp [dig]
    rw [← this]
    simp only [dig, ← pow_mul, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_and_distrib,
      Nat.and_mod_two_pow]
  rw [hdigM] at hand
  exact lt_of_and_eq_zero hb (Nat.mod_lt _ (by positivity)) hand

/-- Kernel-checkable bound: `x` has at most `k` slots of `s` bits, each `< 2^b`. -/
def fits (s b k x : ℕ) : Bool := x < 2 ^ (s * k) && (x &&& mask s b k) == 0

theorem fits_spec {s b k x : ℕ} (hs : 0 < s) (hb : b ≤ s) (h : fits s b k x = true) :
    x < 2 ^ (s * k) ∧ ∀ i, dig s x i < 2 ^ b := by
  simp only [fits, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨h.1, fun i => ?_⟩
  by_cases hi : i < k
  · exact block_lt hs hb h.2 hi
  · have : dig s x i = 0 := by
      rw [dig, Nat.div_eq_of_lt, Nat.zero_mod]
      calc x < 2 ^ (s * k) := h.1
        _ ≤ (2 ^ s) ^ i := by rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by
          have := Nat.mul_le_mul_left s (not_lt.1 hi); omega)
    rw [this]; positivity

/-! ### Bounds of decoded literals -/

theorem dig_dig {x W k j : ℕ} (hj : j < W) : dig 64 (dig (64 * W) x k) j = dig 64 x (W * k + j) := by
  simp only [dig]
  have e1 : (2 ^ (64 * W)) ^ k = (2 ^ 64) ^ (W * k) := by rw [← pow_mul, ← pow_mul, mul_assoc]
  have e2 : (2 : ℕ) ^ (64 * W) = (2 ^ 64) ^ j * (2 ^ 64 * (2 ^ 64) ^ (W - j - 1)) := by
    rw [← pow_succ', ← pow_mul, ← pow_mul, ← pow_add]; congr 1
    have : 64 * j + 64 * (W - j - 1 + 1) = 64 * W := by
      rw [← Nat.mul_add]; congr 1; omega
    omega
  rw [e1, e2, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod, Nat.div_div_eq_div_mul, ← pow_add]

theorem natDegree_decU_le {r W dt : ℕ} (hr : r < 2 ^ (64 * (dt + 1))) : (decU r W).natDegree ≤ dt := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_decU]
  split_ifs
  · rw [dig, Nat.div_eq_of_lt, Nat.zero_mod]
    calc r < 2 ^ (64 * (dt + 1)) := hr
      _ ≤ (2 ^ 64) ^ j := by
        rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by
          have : dt + 1 ≤ j := by exact_mod_cast hj
          omega)
  · rfl

/-- A literal checked by two masks decodes to a bounded polynomial whose `κ` is the literal. -/
theorem decB_spec {x nx W b dt : ℕ} (hb : b ≤ 64) (hdt : dt + 1 ≤ W)
    (hslots : fits 64 b (W * nx) x = true) (hrows : fits (64 * W) (64 * (dt + 1)) nx x = true) :
    Bd (decB x nx W) (2 ^ b - 1) (nx - 1) dt ∧ κ W (decB x nx W) = x := by
  have hs := fits_spec (by norm_num) hb hslots
  have hW : 0 < W := by omega
  have hr := fits_spec (s := 64 * W) (by positivity) (by nlinarith) hrows
  refine ⟨⟨fun k j => ?_, ?_, fun k => ?_⟩, κ_decB x nx W (by rw [mul_assoc]; exact hs.1)⟩
  · rw [coeff_decB]; split_ifs
    · rw [coeff_decU]; split_ifs with hj
      · rw [dig_dig hj]; have := hs.2 (W * k + j); omega
      · exact Nat.zero_le _
    · simp
  · refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    refine natDegree_C_mul_X_pow_le _ _ |>.trans ?_
    have := mem_range.1 hk; omega
  · rw [coeff_decB]; split_ifs
    · exact natDegree_decU_le (hr.2 k)
    · simp

end Sz8.Galois.Packed
