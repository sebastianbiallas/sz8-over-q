import Sz8.Monodromy.StepDatum

/-!
A faster replay of `discCheck`: the Taylor shift as one product.

`PackedCheck` evaluates the packed step rows at `2^b + γ` by 66 Horner steps on
1.4-million-bit integers, then reads 528 digits sequentially. In the kernel every
intermediate is cached until the declaration ends, so memory grows by ~275 MB per disc.

Here the Taylor shift is a single correlation (Aho–Steiglitz–Ullman):
`65! m! E_m = ∑_n ((m+n)! c_{m+n}) ((65!/n!) γ^n)`. Packing `u_i = i! c_i` (all eight rows,
row stride 131 digits) and `v_t = (65!/(65-t)!) γ^(65-t)` in base `2^b`, the product `U V`
carries `65! m! E_{l,m}` at digit `131 l + 65 + m`; the other digits are bounded junk.
* The packed rows `U` are formed per step by the Kronecker form of the `t`-shift:
  eight Horner steps `∑_j Q_j (2^(131 b) + τ)^j` on packed columns `Q_j`.
* `V` is a 66-step Horner evaluation in `γ` of fixed constants.
* Digits are read by a power-of-two divide-and-conquer tree.

`discCheck_of_convCheck`: the check computes exactly `discCheck`'s majorant and linear
coefficient, so the soundness proof `discCheck_sound` applies unchanged.
-/

open Polynomial

namespace Sz8.Monodromy.GaussPoly

/-! ### Digits -/

/-- The `2^d` base-`2^b` digits of `n` (mod `2^(b 2^d)`), consed onto `acc`. -/
def ddigP (b : ℕ) : ℕ → ℕ → List ℕ → List ℕ
  | 0, n, acc => (n &&& (2 ^ b - 1)) :: acc
  | d + 1, n, acc => ddigP b d (n &&& (2 ^ (b <<< d) - 1)) (ddigP b d (n >>> (b <<< d)) acc)

/-- The 66 digits of a row block above its 65 junk digits. -/
def rowDig (b n : ℕ) : List ℕ :=
  let m := n >>> (65 * b)
  ddigP b 6 m (ddigP b 1 (m >>> (64 * b)) [])

/-- The useful digits of all eight row blocks. -/
def rowsDig (b n : ℕ) : List (List ℕ) := (ddigP (131 * b) 3 n []).map (rowDig b)

/-- The offset `∑_{i<k} 2^(b-1) 2^(b i)` in closed form. -/
def offsetC (b k : ℕ) : ℕ := 2 ^ (b - 1) * ((2 ^ (b * k) - 1) / (2 ^ b - 1))

theorem digits_eq (b : ℕ) : ∀ k n, digits b k n = (List.range k).map fun i => n / 2 ^ (b * i) % 2 ^ b
  | 0, n => rfl
  | k + 1, n => by
    rw [digits, digits_eq b k, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · rw [Nat.and_two_pow_sub_one_eq_mod]; simp
    · refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add,
        Nat.succ_eq_add_one]
      ring_nf

/-- Reading a digit below the top of a masked number. -/
theorem mod_div_mod (n A B C : ℕ) (h : B + C ≤ A) : n % 2 ^ A / 2 ^ B % 2 ^ C = n / 2 ^ B % 2 ^ C := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, pow_add, mul_assoc, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]

theorem ddigP_eq (b : ℕ) : ∀ d n acc, ddigP b d n acc = digits b (2 ^ d) n ++ acc
  | 0, n, acc => by simp [ddigP, digits]
  | d + 1, n, acc => by
    rw [ddigP, ddigP_eq b d, ddigP_eq b d, ← List.append_assoc]
    congr 1
    rw [digits_eq, digits_eq, digits_eq, pow_succ, mul_two, List.range_add, List.map_append,
      List.map_map]
    congr 1
    · refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, mod_div_mod]
      nlinarith
    · refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
        Nat.div_div_eq_div_mul, ← pow_add]
      ring_nf

theorem rowDig_eq (b n : ℕ) :
    rowDig b n = (List.range 66).map fun m => n / 2 ^ (b * (65 + m)) % 2 ^ b := by
  simp only [rowDig, ddigP_eq, List.append_nil, digits_eq]
  rw [show (66 : ℕ) = 2 ^ 6 + 2 ^ 1 by norm_num, List.range_add, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun i _ => ?_
    simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
    ring_nf
  · refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
    ring_nf

theorem rowsDig_eq (b n : ℕ) :
    rowsDig b n = (List.range 8).map fun l =>
      (List.range 66).map fun m => n / 2 ^ (b * (131 * l + 65 + m)) % 2 ^ b := by
  simp only [rowsDig, ddigP_eq, List.append_nil, digits_eq, List.map_map]
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply, rowDig_eq]
  refine List.map_congr_left fun m hm => ?_
  rw [List.mem_range] at hm
  rw [mod_div_mod _ _ _ _ (by nlinarith), Nat.div_div_eq_div_mul, ← pow_add]
  ring_nf

theorem offsetC_eq (b k : ℕ) (hb : 0 < b) : offsetC b k = offset b k := by
  have h2 : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hgeom : ∀ k, (2 ^ (b * k) - 1) / (2 ^ b - 1) = ∑ i ∈ Finset.range k, ((2 : ℕ) ^ b) ^ i := by
    intro k; rw [Nat.geomSum_eq h2, ← pow_mul]
  rw [offsetC, hgeom]
  induction k with
  | zero => simp [offset]
  | succ k ih =>
    have hs : ∑ i ∈ Finset.range (k + 1), ((2 : ℕ) ^ b) ^ i =
        1 + 2 ^ b * ∑ i ∈ Finset.range k, ((2 : ℕ) ^ b) ^ i := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      simp [pow_succ, mul_comm]
    rw [hs, offset, ← ih]
    ring

/-! ### Scalar maps on coefficients -/

def gmulN (k : ℕ) (a : GI) : GI := ((k : ℤ) * a.1, (k : ℤ) * a.2)

theorem gc_gmulN (k : ℕ) (a : GI) : gc (gmulN k a) = (k : ℂ) * gc a := by
  simp only [gc, gmulN]; push_cast; ring

theorem gshl_gadd (a c : GI) (k : ℕ) : gshl (gadd a c) k = gadd (gshl a k) (gshl c k) :=
  gc_injective (by simp only [gc_gshl, gc_add]; ring)

theorem gshl_gmul (c a : GI) (k : ℕ) : gshl (gmul c a) k = gmul c (gshl a k) :=
  gc_injective (by simp only [gc_gshl, gc_mul]; ring)

theorem gshl_gshl (a : GI) (k k' : ℕ) : gshl (gshl a k) k' = gshl (gshl a k') k :=
  gc_injective (by simp only [gc_gshl]; ring)

theorem gmulN_gadd (f : ℕ) (a c : GI) : gmulN f (gadd a c) = gadd (gmulN f a) (gmulN f c) :=
  gc_injective (by simp only [gc_gmulN, gc_add]; ring)

theorem gmulN_gmul (f : ℕ) (c a : GI) : gmulN f (gmul c a) = gmul c (gmulN f a) :=
  gc_injective (by simp only [gc_gmulN, gc_mul]; ring)

theorem gmulN_gshl (f : ℕ) (a : GI) (k : ℕ) : gmulN f (gshl a k) = gshl (gmulN f a) k :=
  gc_injective (by simp only [gc_gmulN, gc_gshl]; ring)

/-- Weight entry `k` by `(i + k)!`. -/
def factw : ℕ → List GI → List GI
  | _, [] => []
  | i, a :: as => gmulN i.factorial a :: factw (i + 1) as

/-- The row map: scale the root variable, then weight coefficient `i` by `i!`. -/
def linR (K : ℕ) (P : List GI) : List GI := factw 0 (scaleUp K 65 P)

theorem scaleUp_padd (K : ℕ) : ∀ (n : ℕ) (P Q : List GI),
    scaleUp K n (padd P Q) = padd (scaleUp K n P) (scaleUp K n Q)
  | _, [], Q => by simp [padd, scaleUp]
  | _, _ :: _, [] => by simp [padd, scaleUp]
  | n, a :: P, c :: Q => by simp [padd, scaleUp, gshl_gadd, scaleUp_padd K (n - 1) P Q]

theorem scaleUp_pmulC (K : ℕ) (c : GI) : ∀ (n : ℕ) (P : List GI),
    scaleUp K n (pmulC c P) = pmulC c (scaleUp K n P)
  | _, [] => rfl
  | n, a :: P => by simp [pmulC, scaleUp, gshl_gmul, scaleUp_pmulC K c (n - 1) P]

theorem scaleUp_pshl (K k : ℕ) : ∀ (n : ℕ) (P : List GI),
    scaleUp K n (pshl k P) = pshl k (scaleUp K n P)
  | _, [] => rfl
  | n, a :: P => by simp [pshl, scaleUp, gshl_gshl, scaleUp_pshl K k (n - 1) P]

theorem factw_padd : ∀ (i : ℕ) (P Q : List GI), factw i (padd P Q) = padd (factw i P) (factw i Q)
  | _, [], Q => by simp [padd, factw]
  | _, _ :: _, [] => by simp [padd, factw]
  | i, a :: P, c :: Q => by simp [padd, factw, gmulN_gadd, factw_padd (i + 1) P Q]

theorem factw_pmulC (c : GI) : ∀ (i : ℕ) (P : List GI), factw i (pmulC c P) = pmulC c (factw i P)
  | _, [] => rfl
  | i, a :: P => by simp [pmulC, factw, gmulN_gmul, factw_pmulC c (i + 1) P]

theorem factw_pshl (k : ℕ) : ∀ (i : ℕ) (P : List GI), factw i (pshl k P) = pshl k (factw i P)
  | _, [] => rfl
  | i, a :: P => by simp [pshl, factw, gmulN_gshl, factw_pshl k (i + 1) P]

theorem linR_padd (K : ℕ) (P Q : List GI) : linR K (padd P Q) = padd (linR K P) (linR K Q) := by
  simp [linR, scaleUp_padd, factw_padd]

theorem linR_pmulC (K : ℕ) (c : GI) (P : List GI) : linR K (pmulC c P) = pmulC c (linR K P) := by
  simp [linR, scaleUp_pmulC, factw_pmulC]

theorem linR_pshl (K k : ℕ) (P : List GI) : linR K (pshl k P) = pshl k (linR K P) := by
  simp [linR, scaleUp_pshl, factw_pshl]

theorem linR_nil (K : ℕ) : linR K [] = [] := rfl

theorem length_factw : ∀ (i : ℕ) (P : List GI), (factw i P).length = P.length
  | _, [] => rfl
  | i, _ :: P => by simp [factw, length_factw (i + 1) P]

theorem length_linR (K : ℕ) (P : List GI) : (linR K P).length = P.length := by
  simp [linR, length_factw, length_scaleUp]

/-! ### Row maps commute with the `t`-shift -/

section Commute
variable (f : List GI → List GI)

theorem oadd_map (hf : ∀ P Q, f (padd P Q) = padd (f P) (f Q)) :
    ∀ Ps Qs : List (List GI), oadd (Ps.map f) (Qs.map f) = (oadd Ps Qs).map f
  | [], Qs => by simp [oadd]
  | _ :: _, [] => by simp [oadd]
  | P :: Ps, Q :: Qs => by simp [oadd, hf, oadd_map hf Ps Qs]

theorem omulC_map (c : GI) (hf : ∀ P, f (pmulC c P) = pmulC c (f P)) :
    ∀ Ps : List (List GI), omulC c (Ps.map f) = (omulC c Ps).map f
  | [] => rfl
  | P :: Ps => by simp [omulC, hf, omulC_map c hf Ps]

theorem oshift_map (γ : GI) (hadd : ∀ P Q, f (padd P Q) = padd (f P) (f Q))
    (hmul : ∀ P, f (pmulC γ P) = pmulC γ (f P)) (hnil : f [] = []) :
    ∀ Ps : List (List GI), oshift γ (Ps.map f) = (oshift γ Ps).map f
  | [] => rfl
  | P :: Ps => by
    have h0 : ([] : List GI) :: (oshift γ Ps).map f = (([] : List GI) :: oshift γ Ps).map f := by
      simp [hnil]
    simp only [List.map_cons, oshift, oshiftStep, oshift_map γ hadd hmul hnil Ps]
    rw [omulC_map f γ hmul, show [f P] = [P].map f from rfl, oadd_map f hadd, h0, oadd_map f hadd]

theorem oscale_map (J : ℕ) (hf : ∀ k P, f (pshl k P) = pshl k (f P)) :
    ∀ (n : ℕ) (Ps : List (List GI)), oscale J n (Ps.map f) = (oscale J n Ps).map f
  | _, [] => rfl
  | n, P :: Ps => by simp [oscale, hf, oscale_map J hf (n - 1) Ps]

end Commute

/-! ### The packed rows `U` (Kronecker form of the `t`-shift) -/

/-- `∑ a_i 2^(b i)`. -/
def packL (b : ℕ) : List GI → GI
  | [] => (0, 0)
  | a :: as => gadd a (gshl (packL b as) b)

theorem gc_packL (b : ℕ) : ∀ L : List GI, gc (packL b L) = peval L (2 ^ b)
  | [] => by simp [packL]
  | a :: as => by simp only [packL, gc_add, gc_gshl, gc_packL b as, peval_cons]

/-- Packed columns `2^(J n) ∑_i i! 2^(K(65-i)) c_i 2^(b i)`. -/
def packQ (J K b : ℕ) : ℕ → List (List GI) → List GI
  | _, [] => []
  | n, c :: cs => gshl (packL b (linR K c)) (J * n) :: packQ J K b (n - 1) cs

theorem peval_packQ (J K b : ℕ) : ∀ (n : ℕ) (cs : List (List GI)) (y : ℂ),
    peval (packQ J K b n cs) y = oeval (oscale J n (cs.map (linR K))) (2 ^ b) y
  | _, [], y => by simp [packQ, oscale]
  | n, c :: cs, y => by
    simp only [packQ, List.map_cons, oscale, peval_cons, oeval_cons, gc_gshl, gc_packL,
      peval_pshl, peval_packQ J K b (n - 1) cs y]

/-- The packed factorial-weighted rows of the step at stride `131` digits. -/
def packU (J K b : ℕ) (τ : GI) : GI := hornerP (131 * b) τ (packQ J K b 7 intCols)

theorem gc_packU (J K b : ℕ) (τ : GI) :
    gc (packU J K b τ) = oeval ((stepRows J τ intCols).map (linR K)) (2 ^ b) (2 ^ (131 * b)) := by
  rw [packU, gc_hornerP, peval_packQ, oscale_map _ J (linR_pshl K), stepRows,
    ← oshift_map (linR K) τ (linR_padd K) (linR_pmulC K τ) (linR_nil K), oeval_oshift, add_comm]

/-! ### `V`: the correlation vector -/

/-- Horner evaluation of a list at `γ`. -/
def hornerG (γ : GI) : List GI → GI
  | [] => (0, 0)
  | c :: cs => gadd c (gmul γ (hornerG γ cs))

theorem gc_hornerG (γ : GI) : ∀ cs : List GI, gc (hornerG γ cs) = peval cs (gc γ)
  | [] => by simp [hornerG]
  | c :: cs => by simp only [hornerG, gc_add, gc_mul, gc_hornerG γ cs, peval_cons]

/-- The constants `(65!/j!) 2^(b(65-j))`. -/
def vconst (b : ℕ) : List GI :=
  (List.range 66).map fun j => ((((Nat.factorial 65 / Nat.factorial j) <<< (b * (65 - j)) : ℕ) : ℤ), 0)

def gpow (γ : GI) : ℕ → GI
  | 0 => (1, 0)
  | n + 1 => gmul γ (gpow γ n)

theorem gc_gpow (γ : GI) : ∀ n, gc (gpow γ n) = gc γ ^ n
  | 0 => by simp [gpow, gc]
  | n + 1 => by rw [gpow, gc_mul, gc_gpow γ n, pow_succ']

/-- The correlation vector `v_t = (65!/(65-t)!) γ^(65-t)`. -/
def vrev (γ : GI) : List GI :=
  (List.range 66).map fun t => gmulN (Nat.factorial 65 / Nat.factorial (65 - t)) (gpow γ (65 - t))

theorem peval_map_range (g : ℕ → GI) (y : ℂ) : ∀ n,
    peval ((List.range n).map g) y = ∑ i ∈ Finset.range n, gc (g i) * y ^ i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, peval_append, peval_map_range g y n, Finset.sum_range_succ]
    simp [mul_comm]

theorem gc_hornerG_vconst (b : ℕ) (γ : GI) : gc (hornerG γ (vconst b)) = peval (vrev γ) (2 ^ b) := by
  rw [gc_hornerG, vconst, vrev, peval_map_range, peval_map_range,
    ← Finset.sum_range_reflect (fun t => gc (gmulN (Nat.factorial 65 / Nat.factorial (65 - t))
      (gpow γ (65 - t))) * (2 ^ b : ℂ) ^ t)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h1 : 66 - 1 - j = 65 - j := rfl
  have h2 : 65 - (65 - j) = j := by omega
  rw [h1, h2, gc_gmulN, gc_gpow]
  generalize Nat.factorial 65 / Nat.factorial j = f
  simp only [gc, Nat.shiftLeft_eq]
  push_cast
  rw [← pow_mul]
  ring

/-! ### The product: digit rows -/

/-- List convolution. -/
def pmul : List GI → List GI → List GI
  | [], _ => []
  | a :: P, Q => padd (pmulC a Q) ((0, 0) :: pmul P Q)

theorem peval_pmul (Q : List GI) (y : ℂ) : ∀ P : List GI, peval (pmul P Q) y = peval P y * peval Q y
  | [] => by simp [pmul]
  | a :: P => by
    simp only [pmul, peval_padd, peval_pmulC, peval_cons, gc_zero, peval_pmul Q y P]; ring

theorem length_pmulC' (c : GI) (P : List GI) : (pmulC c P).length = P.length := length_pmulC c P

theorem length_pmul_le (Q : List GI) (hQ : Q ≠ []) :
    ∀ P : List GI, (pmul P Q).length ≤ P.length + Q.length - 1
  | [] => by simp [pmul]
  | a :: P => by
    have ih := length_pmul_le Q hQ P
    have hQ1 : 1 ≤ Q.length := List.length_pos_iff.mpr hQ
    simp only [pmul, length_padd, length_pmulC, List.length_cons]
    omega

/-- Pad with zeros to length `n`. -/
def padN (n : ℕ) (P : List GI) : List GI := P ++ List.replicate (n - P.length) (0, 0)

theorem peval_padN (n : ℕ) (P : List GI) (y : ℂ) : peval (padN n P) y = peval P y := by
  simp [padN, peval_append, peval_replicate_zero]

theorem length_padN {n : ℕ} {P : List GI} (h : P.length ≤ n) : (padN n P).length = n := by
  simp [padN]; omega

theorem getD_padN (n : ℕ) (P : List GI) (k : ℕ) : (padN n P).getD k (0, 0) = P.getD k (0, 0) := by
  simp only [padN, List.getD_eq_getElem?_getD]
  by_cases hk : k < P.length
  · rw [List.getElem?_append_left hk]
  · rw [List.getElem?_append_right (show P.length ≤ k by omega),
      List.getElem?_eq_none (show P.length ≤ k by omega), List.getElem?_replicate]
    split_ifs <;> rfl

/-- The digit rows of `U V`, one row of 131 digits per step row. -/
def convRows (K : ℕ) (γ : GI) (D : List (List GI)) : List (List GI) :=
  D.map fun C => padN 131 (pmul (linR K C) (vrev γ))

theorem peval_flatten_uniform (n : ℕ) (y : ℂ) : ∀ Rs : List (List GI), (∀ R ∈ Rs, R.length = n) →
    peval Rs.flatten y = oeval Rs y (y ^ n)
  | [], _ => by simp
  | R :: Rs, h => by
    rw [List.flatten_cons, peval_append, h R (List.mem_cons_self ..),
      peval_flatten_uniform n y Rs (fun R' hR' => h R' (List.mem_cons_of_mem _ hR')), oeval_cons]

theorem length_vrev (γ : GI) : (vrev γ).length = 66 := by simp [vrev]

theorem length_convRows (K : ℕ) (γ : GI) (D : List (List GI)) (hD : ∀ C ∈ D, C.length ≤ 66) :
    ∀ R ∈ convRows K γ D, R.length = 131 := by
  intro R hR
  simp only [convRows, List.mem_map] at hR
  obtain ⟨C, hC, rfl⟩ := hR
  apply length_padN
  have := length_pmul_le (vrev γ) (by simp [vrev]) (linR K C)
  rw [length_linR, length_vrev] at this
  have := hD C hC
  omega

theorem oeval_convRows (K : ℕ) (γ : GI) (x σ : ℂ) : ∀ D : List (List GI),
    oeval (D.map (linR K)) x σ * peval (vrev γ) x = oeval (convRows K γ D) x σ
  | [] => by simp [convRows]
  | C :: D => by
    have ih := oeval_convRows K γ x σ D
    simp only [convRows, List.map_cons, oeval_cons] at ih ⊢
    rw [peval_padN, peval_pmul, ← ih]; ring

theorem gc_product (J K b : ℕ) (τ γ : GI) (hD : ∀ C ∈ stepRows J τ intCols, C.length ≤ 66) :
    gc (gmul (packU J K b τ) (hornerG γ (vconst b))) =
      peval (convRows K γ (stepRows J τ intCols)).flatten (2 ^ b) := by
  rw [gc_mul, gc_packU, gc_hornerG_vconst, oeval_convRows,
    peval_flatten_uniform 131 _ _ (length_convRows K γ _ hD), ← pow_mul, mul_comm b 131]

/-! ### Digit bounds -/

theorem n1_le_maj1 : ∀ (Q : List GI), ∀ x ∈ Q, n1 x ≤ maj 1 Q
  | [], _, h => by simp at h
  | a :: Q, x, h => by
    simp only [List.mem_cons] at h
    simp only [maj, one_mul]
    rcases h with rfl | h
    · omega
    · have := n1_le_maj1 Q x h; omega

theorem n1_pmul_le (Q : List GI) : ∀ (P : List GI), ∀ x ∈ pmul P Q, n1 x ≤ maj 1 P * maj 1 Q
  | [], x, h => by simp [pmul] at h
  | a :: P, x, h => by
    have ih := n1_pmul_le Q P
    simp only [pmul] at h
    have h1 := n1_pmulC_le a (n1_le_maj1 Q)
    have h2 : ∀ y ∈ ((0, 0) :: pmul P Q), n1 y ≤ maj 1 P * maj 1 Q := by
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · simp [n1]
      · exact ih y hy
    have := n1_padd_le h1 h2 x h
    simp only [maj, one_mul]
    nlinarith

theorem n1_gmulN (k : ℕ) (a : GI) : n1 (gmulN k a) = k * n1 a := by
  simp only [n1, gmulN, Int.natAbs_mul, Int.natAbs_natCast]; ring

theorem n1_gpow_le (γ : GI) : ∀ n, n1 (gpow γ n) ≤ n1 γ ^ n
  | 0 => by simp [gpow, n1]
  | n + 1 => by
    rw [gpow, pow_succ']
    exact (n1_gmul_le _ _).trans (Nat.mul_le_mul_left _ (n1_gpow_le γ n))

theorem gpow_real (Γ : ℕ) : ∀ n, gpow ((Γ : ℤ), 0) n = (((Γ ^ n : ℕ) : ℤ), 0)
  | 0 => by simp [gpow]
  | n + 1 => by rw [gpow, gpow_real Γ n]; simp [gmul, pow_succ']

theorem maj1_map_le {α : Type*} (g₁ g₂ : α → GI) (h : ∀ x, n1 (g₁ x) ≤ n1 (g₂ x)) :
    ∀ L : List α, maj 1 (L.map g₁) ≤ maj 1 (L.map g₂)
  | [] => le_rfl
  | x :: L => by
    simp only [List.map_cons, maj, one_mul]
    exact Nat.add_le_add (h x) (maj1_map_le g₁ g₂ h L)

theorem maj1_vrev_le {γ : GI} {Γ : ℕ} (h : n1 γ ≤ Γ) : maj 1 (vrev γ) ≤ maj 1 (vrev ((Γ : ℤ), 0)) := by
  apply maj1_map_le
  intro t
  rw [n1_gmulN, n1_gmulN, gpow_real]
  apply Nat.mul_le_mul_left
  refine (n1_gpow_le γ _).trans ?_
  simp only [n1, Int.natAbs_natCast, Int.natAbs_zero, add_zero]
  exact Nat.pow_le_pow_left h _

/-! ### The correlation computes the Taylor shift -/

theorem getD_of_le {L : List GI} {k : ℕ} (h : L.length ≤ k) : L.getD k (0, 0) = (0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem coeff_toPolyC : ∀ (L : List GI) (k : ℕ), (toPolyC L).coeff k = gc (L.getD k (0, 0))
  | [], k => by simp [toPolyC]
  | a :: L, 0 => by simp [toPolyC]
  | a :: L, k + 1 => by simp [toPolyC, coeff_toPolyC L k]

theorem toPolyC_pmul (P Q : List GI) : toPolyC (pmul P Q) = toPolyC P * toPolyC Q :=
  Polynomial.funext fun x => by simp [eval_toPolyC, peval_pmul]

theorem toPolyC_pshift (γ : GI) (P : List GI) : toPolyC (pshift γ P) = taylor (gc γ) (toPolyC P) :=
  Polynomial.funext fun x => by rw [eval_toPolyC, peval_pshift, taylor_eval, eval_toPolyC, add_comm]

theorem getD_factw : ∀ (i : ℕ) (L : List GI) (k : ℕ),
    (factw i L).getD k (0, 0) = gmulN (i + k).factorial (L.getD k (0, 0))
  | i, [], k => by simp [factw, gmulN]
  | i, a :: L, 0 => by simp [factw]
  | i, a :: L, k + 1 => by
    rw [factw, List.getD_cons_succ, List.getD_cons_succ, getD_factw (i + 1) L k,
      show i + 1 + k = i + (k + 1) by omega]

theorem getD_vrev (γ : GI) (t : ℕ) : (vrev γ).getD t (0, 0) =
    if t < 66 then gmulN (Nat.factorial 65 / Nat.factorial (65 - t)) (gpow γ (65 - t)) else (0, 0) := by
  split_ifs with ht
  · simp only [vrev, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]; rfl
  · exact getD_of_le (by rw [length_vrev]; omega)

theorem natDegree_toPolyC_le (L : List GI) (n : ℕ) (h : L.length ≤ n + 1) :
    (toPolyC L).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_toPolyC, getD_of_le (by omega), gc_zero]

theorem gc_getD_pshift (γ : GI) (P : List GI) (hP : P.length ≤ 66) (m : ℕ) :
    gc ((pshift γ P).getD m (0, 0)) =
      ∑ n ∈ Finset.range 66, ((n + m).choose m : ℂ) * gc (P.getD (n + m) (0, 0)) * gc γ ^ n := by
  have hdeg : ((hasseDeriv m) (toPolyC P)).natDegree < 66 :=
    lt_of_le_of_lt ((natDegree_hasseDeriv_le _ _).trans (Nat.sub_le _ _))
      (Nat.lt_succ_of_le (natDegree_toPolyC_le P 65 hP))
  rw [← coeff_toPolyC, toPolyC_pshift, taylor_coeff, eval_eq_sum_range' hdeg]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hasseDeriv_coeff, coeff_toPolyC]

/-- **The correlation identity**: digit `65 + m` of row `P` times `V` is `65! m!` times the
`m`-th Taylor coefficient of `P` at `γ`. -/
theorem conv_coeff (γ : GI) (P : List GI) (hP : P.length ≤ 66) (m : ℕ) :
    (pmul (factw 0 P) (vrev γ)).getD (65 + m) (0, 0) =
      gmulN (Nat.factorial 65 * Nat.factorial m) ((pshift γ P).getD m (0, 0)) := by
  apply gc_injective
  rw [gc_gmulN, gc_getD_pshift γ P hP, ← coeff_toPolyC, toPolyC_pmul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_toPolyC, getD_factw, getD_vrev, zero_add]
  rw [show (65 + m).succ = m + 66 by omega, Finset.sum_range_add, Finset.mul_sum]
  rw [Finset.sum_eq_zero (fun k hk => ?_), zero_add]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    rw [show 65 + m - (m + n) = 65 - n by omega, show 65 - (65 - n) = n by omega]
    simp only [(by omega : 65 - n < 66), ↓reduceIte, gc_gmulN, gc_gpow]
    rw [show m + n = n + m from add_comm m n]
    have h1 := Nat.choose_mul_factorial_mul_factorial (show m ≤ n + m by omega)
    rw [show n + m - m = n by omega] at h1
    have h2 := Nat.div_mul_cancel (Nat.factorial_dvd_factorial (show n ≤ 65 by omega))
    have key : (n + m).factorial * (Nat.factorial 65 / n.factorial) =
        Nat.factorial 65 * m.factorial * (n + m).choose m := by
      calc (n + m).factorial * (Nat.factorial 65 / n.factorial)
          = (n + m).choose m * m.factorial * (Nat.factorial 65 / n.factorial * n.factorial) := by
            rw [← h1]; ring
        _ = _ := by rw [h2]; ring
    have keyC : ((n + m).factorial : ℂ) * ((Nat.factorial 65 / n.factorial : ℕ) : ℂ) =
        ((Nat.factorial 65 * m.factorial : ℕ) : ℂ) * ((n + m).choose m : ℂ) := by
      exact_mod_cast key
    linear_combination (gc (P.getD (n + m) (0, 0)) * gc γ ^ n) * keyC
  · rw [Finset.mem_range] at hk
    have hk' : ¬ (65 + m - k < 66) := by omega
    simp [hk']

/-! ### The check -/

/-- Majorant of one row from its digits, dividing digit `m` by `65! m!`. -/
def majConv (W h : ℕ) : List ℕ → List ℕ → List ℕ → ℕ
  | f :: fs, r :: rs, i :: is => (dabs h r + dabs h i) / f + W * majConv W h fs rs is
  | _, _, _ => 0

def omajConv (S W h : ℕ) (fs : List ℕ) : List (List ℕ) → List (List ℕ) → ℕ
  | r :: rs, i :: is => majConv W h fs r i + S * omajConv S W h fs rs is
  | _, _ => 0

/-- The divisors `65! m!`. -/
def facs : List ℕ := (List.range 66).map fun m => Nat.factorial 65 * Nat.factorial m

/-- The disc check replayed as one product: `U` (packed rows of the step), `vc`
(`vconst b`) and `o` (`offsetC b 1048`) are shared by all discs of a slice. -/
def convCheck (U : GI) (vc : List GI) (o b S : ℕ) (γ : GI) (W : ℕ) : Bool :=
  let P := gmul U (hornerG γ vc)
  let dr := rowsDig b (P.1 + o).toNat
  let di := rowsDig b (P.2 + o).toNat
  let h : ℕ := 2 ^ (b - 1)
  let e : GI := ((((dr.headD []).getD 1 0 : ℕ) - (h : ℤ)) / (Nat.factorial 65 : ℤ),
    (((di.headD []).getD 1 0 : ℕ) - (h : ℤ)) / (Nat.factorial 65 : ℤ))
  decide (0 < W) &&
    decide ((((omajConv S W h facs dr di - n1 e * W : ℕ) : ℤ)) ^ 2 < nsq e * W ^ 2)

/-! ### Soundness -/

theorem getD_flatten_uniform (n : ℕ) : ∀ (Rs : List (List GI)), (∀ R ∈ Rs, R.length = n) →
    ∀ l j, j < n → Rs.flatten.getD (n * l + j) (0, 0) = (Rs.getD l []).getD j (0, 0)
  | [], _, l, j, _ => by simp
  | R :: Rs, h, 0, j, hj => by
    have hR := h R (List.mem_cons_self ..)
    simp only [List.flatten_cons, mul_zero, zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_cons_zero, Option.getD_some]
    rw [List.getElem?_append_left (by omega)]
  | R :: Rs, h, l + 1, j, hj => by
    have hR := h R (List.mem_cons_self ..)
    have ih := getD_flatten_uniform n Rs (fun R' hR' => h R' (List.mem_cons_of_mem _ hR')) l j hj
    rw [List.flatten_cons, List.getD_cons_succ, ← ih, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hR]; nlinarith), hR,
      show n * (l + 1) + j - n = n * l + j by rw [mul_add, mul_one]; omega]

theorem range_map_getD (L : List GI) (n : ℕ) (h : L.length ≤ n) :
    (List.range n).map (fun m => L.getD m (0, 0)) = L ++ List.replicate (n - L.length) (0, 0) := by
  apply List.ext_getElem (by simp; omega)
  intro k hk _
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
  by_cases hkL : k < L.length
  · rw [List.getElem_append_left hkL, List.getElem?_eq_getElem hkL]; rfl
  · rw [List.getElem_append_right (by omega), List.getElem_replicate, List.getElem?_eq_none (by omega)]
    rfl

theorem decode_digit (h : ℕ) (x : ℤ) (hx : |x| < h) : dabs h (x + h).toNat = x.natAbs := by
  have h0 : 0 ≤ x + h := by have := abs_lt.mp hx; linarith
  have hc : (((x + h).toNat : ℕ) : ℤ) = x + h := Int.toNat_of_nonneg h0
  simp only [dabs]
  split_ifs with hle
  · have : ((x + h).toNat - h : ℕ) = ((x + h).toNat : ℤ) - h := by push_cast [hle]; ring
    omega
  · have : (h - (x + h).toNat : ℕ) = (h : ℤ) - (x + h).toNat := by
      push_cast [le_of_lt (not_le.mp hle)]; ring
    omega

theorem majConv_eq (W h : ℕ) (G : ℕ → GI) : ∀ n s,
    (∀ m, s ≤ m → m < s + n → |(gmulN (Nat.factorial 65 * Nat.factorial m) (G m)).1| < h ∧
      |(gmulN (Nat.factorial 65 * Nat.factorial m) (G m)).2| < h) →
    majConv W h ((List.range' s n).map fun m => Nat.factorial 65 * Nat.factorial m)
      ((List.range' s n).map fun m => ((gmulN (Nat.factorial 65 * Nat.factorial m) (G m)).1 + h).toNat)
      ((List.range' s n).map fun m => ((gmulN (Nat.factorial 65 * Nat.factorial m) (G m)).2 + h).toNat) =
      maj W ((List.range' s n).map G)
  | 0, s, _ => rfl
  | n + 1, s, hG => by
    simp only [List.range'_succ, List.map_cons, majConv, maj,
      majConv_eq W h G n (s + 1) (fun m h1 h2 => hG m (by omega) (by omega))]
    congr 1
    have hs := hG s le_rfl (by omega)
    rw [decode_digit h _ hs.1, decode_digit h _ hs.2]
    have : (gmulN (Nat.factorial 65 * Nat.factorial s) (G s)).1.natAbs +
        (gmulN (Nat.factorial 65 * Nat.factorial s) (G s)).2.natAbs =
        n1 (gmulN (Nat.factorial 65 * Nat.factorial s) (G s)) := rfl
    rw [this, n1_gmulN, Nat.mul_div_cancel_left _ (by positivity)]

theorem omajConv_eq (S W h : ℕ) (fs : List ℕ) (R₁ R₂ : ℕ → List ℕ) (E : ℕ → List GI) : ∀ n s,
    (∀ l, s ≤ l → l < s + n → majConv W h fs (R₁ l) (R₂ l) = maj W (E l)) →
    omajConv S W h fs ((List.range' s n).map R₁) ((List.range' s n).map R₂) =
      omaj S W ((List.range' s n).map E)
  | 0, s, _ => rfl
  | n + 1, s, hrow => by
    simp only [List.range'_succ, List.map_cons, omajConv, omaj, hrow s le_rfl (by omega),
      omajConv_eq S W h fs R₁ R₂ E n (s + 1) (fun l h1 h2 => hrow l (by omega) (by omega))]

theorem length_stepRows_le (J : ℕ) (τ : GI) (h : rowsShort (stepRows J τ intCols) = true) :
    ∀ C ∈ stepRows J τ intCols, C.length ≤ 66 := fun C hC => by
  simpa using List.all_eq_true.mp h C hC

/-- **Soundness of the product check**: it implies the list check `discCheck`. -/
theorem discCheck_of_convCheck (J K b : ℕ) (τ : GI) (S : ℕ) (γ : GI) (W Γ : ℕ)
    (hb : 0 < b) (hD : (stepRows J τ intCols).length = 8)
    (hshort : rowsShort (stepRows J τ intCols) = true) (hγ : n1 γ ≤ Γ)
    (hbound : ∀ C ∈ stepRows J τ intCols, maj 1 (linR K C) * maj 1 (vrev ((Γ : ℤ), 0)) < 2 ^ (b - 1))
    (hc : convCheck (packU J K b τ) (vconst b) (offsetC b 1048) b S γ W = true) :
    discCheck (stepRows J τ intCols) K S γ W = true := by
  set D := stepRows J τ intCols with hDdef
  have hDlen := length_stepRows_le J τ hshort
  set Rs := convRows K γ D with hRs
  have hRlen := length_convRows K γ D hDlen
  have hRslen : Rs.length = 8 := by simp [hRs, convRows, hD]
  set flat := Rs.flatten with hflat
  have hflatlen : flat.length = 1048 := by
    rw [hflat, List.length_flatten, List.map_congr_left (fun R hR => hRlen R hR), List.map_const',
      List.sum_replicate, hRslen, smul_eq_mul]
  -- The product is the packed digit list.
  have hP : gmul (packU J K b τ) (hornerG γ (vconst b)) =
      (ival (2 ^ b) (flat.map Prod.fst), ival (2 ^ b) (flat.map Prod.snd)) := by
    apply gc_injective
    rw [gc_product J K b τ γ hDlen, gc_ival]
    push_cast; rfl
  -- Every digit is below `2^(b-1)`.
  have hbnd : ∀ x ∈ flat, |x.1| < 2 ^ (b - 1) ∧ |x.2| < 2 ^ (b - 1) := by
    intro x hx
    obtain ⟨R, hR, hxR⟩ := List.mem_flatten.mp hx
    simp only [hRs, convRows, List.mem_map] at hR
    obtain ⟨C, hC, rfl⟩ := hR
    have hn : n1 x < 2 ^ (b - 1) := by
      simp only [padN, List.mem_append, List.mem_replicate] at hxR
      rcases hxR with hxR | ⟨-, rfl⟩
      · calc n1 x ≤ maj 1 (linR K C) * maj 1 (vrev γ) := n1_pmul_le _ _ x hxR
          _ ≤ maj 1 (linR K C) * maj 1 (vrev ((Γ : ℤ), 0)) :=
            Nat.mul_le_mul_left _ (maj1_vrev_le hγ)
          _ < 2 ^ (b - 1) := hbound C hC
      · simp [n1]
    simp only [n1] at hn
    constructor
    · rw [Int.abs_eq_natAbs]; exact_mod_cast (by omega : x.1.natAbs < 2 ^ (b - 1))
    · rw [Int.abs_eq_natAbs]; exact_mod_cast (by omega : x.2.natAbs < 2 ^ (b - 1))
  -- Digits of the offset numbers.
  have hdig : ∀ (F : GI → ℤ), (∀ x ∈ flat, |F x| < 2 ^ (b - 1)) → ∀ k < 1048,
      (ival (2 ^ b) (flat.map F) + offsetC b 1048).toNat / 2 ^ (b * k) % 2 ^ b =
        (F (flat.getD k (0, 0)) + 2 ^ (b - 1)).toNat := by
    intro F hF k hk
    have h1 := digits_ival b hb (flat.map F) (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hF x hx)
    rw [List.length_map, hflatlen, ← offsetC_eq b 1048 hb, digits_eq] at h1
    have h2 := congrArg (fun L => L[k]?) h1
    simp only [List.getElem?_map, List.getElem?_range hk] at h2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simpa [List.getElem?_eq_getElem (show k < flat.length by omega)] using h2
  -- The Taylor coefficients.
  set E := discRows K γ D with hE
  have hElen : E.length = 8 := by simp [hE, discRows, hD]
  set G : ℕ → ℕ → GI := fun l m => (E.getD l []).getD m (0, 0) with hG
  have hflatG : ∀ l < 8, ∀ m < 66, flat.getD (131 * l + 65 + m) (0, 0) =
      gmulN (Nat.factorial 65 * Nat.factorial m) (G l m) := by
    intro l hl m hm
    rw [show 131 * l + 65 + m = 131 * l + (65 + m) by ring,
      getD_flatten_uniform 131 Rs hRlen l (65 + m) (by omega)]
    have hl' : l < D.length := by omega
    have hRl : Rs.getD l [] = padN 131 (pmul (linR K D[l]) (vrev γ)) := by
      simp [hRs, convRows, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl']
    have hEl : E.getD l [] = pshift γ (scaleUp K 65 D[l]) := by
      simp [hE, discRows, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl']
    rw [hRl, getD_padN, hG]
    simp only [hEl]
    exact conv_coeff γ _ (by rw [length_scaleUp]; exact hDlen _ (List.getElem_mem _)) m
  -- The digit rows.
  have hrows : ∀ (F : GI → ℤ), (∀ x ∈ flat, |F x| < 2 ^ (b - 1)) →
      rowsDig b (ival (2 ^ b) (flat.map F) + offsetC b 1048).toNat =
        (List.range 8).map fun l => (List.range 66).map fun m =>
          (F (gmulN (Nat.factorial 65 * Nat.factorial m) (G l m)) + 2 ^ (b - 1)).toNat := by
    intro F hF
    rw [rowsDig_eq]
    refine List.map_congr_left fun l hl => List.map_congr_left fun m hm => ?_
    rw [List.mem_range] at hl hm
    rw [hdig F hF _ (by omega), hflatG l hl m hm]
  have hF1 : ∀ x ∈ flat, |x.1| < 2 ^ (b - 1) := fun x hx => (hbnd x hx).1
  have hF2 : ∀ x ∈ flat, |x.2| < 2 ^ (b - 1) := fun x hx => (hbnd x hx).2
  have hGb : ∀ l < 8, ∀ m < 66, |(gmulN (Nat.factorial 65 * Nat.factorial m) (G l m)).1| < 2 ^ (b - 1) ∧
      |(gmulN (Nat.factorial 65 * Nat.factorial m) (G l m)).2| < 2 ^ (b - 1) := by
    intro l hl m hm
    rw [← hflatG l hl m hm]
    have hmem : flat.getD (131 * l + 65 + m) (0, 0) ∈ flat := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    exact hbnd _ hmem
  -- Unfold the check.
  simp only [convCheck, hP, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [hrows Prod.fst (fun x hx => hF1 x hx), hrows Prod.snd (fun x hx => hF2 x hx)] at hc
  obtain ⟨hW, hdom⟩ := hc
  set h : ℕ := 2 ^ (b - 1) with hh
  -- The majorant.
  have hElt : ∀ l < 8, (E.getD l []).length ≤ 66 := by
    intro l hl
    have hl' : l < D.length := by omega
    simp only [hE, discRows, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hl', Option.map_some, Option.getD_some]
    rw [length_pshift, length_scaleUp]; exact hDlen _ (List.getElem_mem _)
  have hmaj : omajConv S W h facs
      ((List.range 8).map fun l => (List.range 66).map fun m =>
        ((gmulN (Nat.factorial 65 * Nat.factorial m) (G l m)).1 + (h : ℤ)).toNat)
      ((List.range 8).map fun l => (List.range 66).map fun m =>
        ((gmulN (Nat.factorial 65 * Nat.factorial m) (G l m)).2 + (h : ℤ)).toNat) = omaj S W E := by
    have hE8 : (List.range 8).map (fun l => E.getD l []) = E := by
      apply List.ext_getElem (by simp [hElen])
      intro k hk _
      simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show k < E.length by simp at hk; omega), Option.getD_some]
    conv_rhs => rw [← hE8]
    simp only [List.range_eq_range', facs]
    apply omajConv_eq
    intro l _ hl
    simp only [zero_add] at hl
    rw [majConv_eq W h (G l) 66 0 (fun m _ hm => hGb l hl m (by omega)), ← List.range_eq_range',
      hG, range_map_getD _ _ (hElt l hl), maj_append_zeros]
  have hcast : ∀ x : ℤ, |x| < h → (((x + h).toNat : ℕ) : ℤ) - h = x := by
    intro x hx
    rw [Int.toNat_of_nonneg (by have := abs_lt.mp hx; linarith)]; ring
  have he : (((((List.range 66).map fun m =>
        ((gmulN (Nat.factorial 65 * Nat.factorial m) (G 0 m)).1 + (h : ℤ)).toNat).getD 1 0 : ℕ) - (h : ℤ)) /
        (Nat.factorial 65 : ℤ), ((((List.range 66).map fun m =>
        ((gmulN (Nat.factorial 65 * Nat.factorial m) (G 0 m)).2 + (h : ℤ)).toNat).getD 1 0 : ℕ) - (h : ℤ)) /
        (Nat.factorial 65 : ℤ)) = coeff01 E := by
    have hg1 := hGb 0 (by norm_num) 1 (by norm_num)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show 1 < 66 by norm_num),
      Option.map_some, Option.getD_some]
    rw [hcast _ hg1.1, hcast _ hg1.2]
    simp only [gmulN, Nat.factorial_one, mul_one]
    rw [Int.mul_ediv_cancel_left _ (by positivity), Int.mul_ediv_cancel_left _ (by positivity)]
    obtain ⟨E₀, Es, hEs⟩ := List.exists_cons_of_ne_nil (fun h0 : E = [] => by simp [h0] at hElen)
    simp [hG, coeff01, hEs]
  have hhead : ∀ (F : ℕ → List ℕ), ((List.range 8).map F).headD [] = F 0 := by
    intro F; simp [List.range_succ_eq_map]
  have h2h : (2 : ℤ) ^ (b - 1) = ((h : ℕ) : ℤ) := by rw [hh]; push_cast; rfl
  rw [h2h, hhead, hhead, he, hmaj] at hdom
  obtain ⟨E₀, Es, hEs⟩ := List.exists_cons_of_ne_nil (fun h0 : E = [] => by simp [h0] at hElen)
  rw [hEs, omaj_kill01, Nat.add_sub_cancel] at hdom
  simp only [discCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hW, ?_⟩
  rw [← hE, hEs]
  exact hdom

/-! ### Per-step conditions -/

/-- `maj 1 (vrev (Γ, 0)) = ∑_j (65!/j!) Γ^j`, on natural numbers. -/
def vmajN (Γ : ℕ) : ℕ :=
  ((List.range 66).map fun t => Nat.factorial 65 / Nat.factorial (65 - t) * Γ ^ (65 - t)).sum

theorem maj1_eq_sum : ∀ L : List GI, maj 1 L = (L.map n1).sum
  | [] => rfl
  | a :: L => by simp [maj, maj1_eq_sum L]

theorem maj1_vrev_real (Γ : ℕ) : maj 1 (vrev ((Γ : ℤ), 0)) = vmajN Γ := by
  rw [maj1_eq_sum, vmajN, vrev, List.map_map]
  apply congrArg List.sum
  refine List.map_congr_left fun t _ => ?_
  rw [Function.comp_apply, n1_gmulN, gpow_real]
  simp [n1]

/-! ### A row bound without computing the step rows -/

theorem maj1_padd_le : ∀ P Q : List GI, maj 1 (padd P Q) ≤ maj 1 P + maj 1 Q
  | [], Q => by simp [padd, maj]
  | a :: P, [] => by simp [padd]
  | a :: P, c :: Q => by
    simp only [padd, maj, one_mul]
    have := n1_gadd_le a c; have := maj1_padd_le P Q; omega

theorem maj1_pmulC_le (c : GI) : ∀ P : List GI, maj 1 (pmulC c P) ≤ n1 c * maj 1 P
  | [] => by simp [pmulC, maj]
  | a :: P => by
    simp only [pmulC, maj, one_mul]
    have := n1_gmul_le c a; have := maj1_pmulC_le c P; nlinarith

theorem maj1_oadd_le : ∀ {Xs Ys : List (List GI)} {bX bY : ℕ}, (∀ R ∈ Xs, maj 1 R ≤ bX) →
    (∀ R ∈ Ys, maj 1 R ≤ bY) → ∀ R ∈ oadd Xs Ys, maj 1 R ≤ bX + bY
  | [], Ys, _, _, _, hY => fun R hR => by simp only [oadd] at hR; exact (hY R hR).trans (by omega)
  | X :: Xs, [], _, _, hX, _ => fun R hR => by simp only [oadd] at hR; exact (hX R hR).trans (by omega)
  | X :: Xs, Y :: Ys, _, _, hX, hY => fun R hR => by
    simp only [oadd, List.mem_cons] at hR
    rcases hR with rfl | hR
    · exact (maj1_padd_le X Y).trans
        (Nat.add_le_add (hX X (List.mem_cons_self ..)) (hY Y (List.mem_cons_self ..)))
    · exact maj1_oadd_le (fun R h => hX R (List.mem_cons_of_mem _ h))
        (fun R h => hY R (List.mem_cons_of_mem _ h)) R hR

theorem maj1_omulC_le (c : GI) {bX : ℕ} : ∀ {Xs : List (List GI)}, (∀ R ∈ Xs, maj 1 R ≤ bX) →
    ∀ R ∈ omulC c Xs, maj 1 R ≤ n1 c * bX
  | [], _ => by simp [omulC]
  | X :: Xs, hX => fun R hR => by
    simp only [omulC, List.mem_cons] at hR
    rcases hR with rfl | hR
    · exact (maj1_pmulC_le c X).trans (Nat.mul_le_mul_left _ (hX X (List.mem_cons_self ..)))
    · exact maj1_omulC_le c (fun R h => hX R (List.mem_cons_of_mem _ h)) R hR

/-- Every row of `Φ(x, γ + σ)` is bounded by the majorant of `Φ` at `σ = 1 + |γ|₁`. -/
theorem maj1_oshift_le (γ : GI) : ∀ (Ps : List (List GI)), ∀ R ∈ oshift γ Ps,
    maj 1 R ≤ omaj (1 + n1 γ) 1 Ps
  | [] => by simp [oshift]
  | P :: Ps => by
    have ih := maj1_oshift_le γ Ps
    intro R hR
    simp only [oshift, oshiftStep] at hR
    have h1 : ∀ R ∈ oadd [P] (omulC γ (oshift γ Ps)),
        maj 1 R ≤ maj 1 P + n1 γ * omaj (1 + n1 γ) 1 Ps :=
      maj1_oadd_le (by simp) (maj1_omulC_le γ ih)
    have h2 : ∀ R ∈ (([] : List GI) :: oshift γ Ps), maj 1 R ≤ omaj (1 + n1 γ) 1 Ps := by
      intro R hR
      simp only [List.mem_cons] at hR
      rcases hR with rfl | hR
      · simp [maj]
      · exact ih R hR
    have := maj1_oadd_le h1 h2 R hR
    simp only [omaj]
    nlinarith

/-- A bound for `maj₁` of every weighted step row, from the (fixed) columns. -/
def rowBound (J K : ℕ) (τ : GI) : ℕ := omaj (1 + n1 τ) 1 (oscale J 7 (intCols.map (linR K)))

theorem maj1_linR_stepRows_le (J K : ℕ) (τ : GI) :
    ∀ C ∈ stepRows J τ intCols, maj 1 (linR K C) ≤ rowBound J K τ := by
  intro C hC
  have hmem : linR K C ∈ (stepRows J τ intCols).map (linR K) := List.mem_map_of_mem hC
  rw [stepRows, ← oshift_map (linR K) τ (linR_padd K) (linR_pmulC K τ) (linR_nil K),
    ← oscale_map _ J (linR_pshl K)] at hmem
  exact maj1_oshift_le τ _ _ hmem

end Sz8.Monodromy.GaussPoly

namespace Sz8.Monodromy
open GaussPoly Metric

set_option maxRecDepth 100000

/-- Per-step conditions for the product check: structure (only list shapes of the step
rows are computed), 65 separated discs, centres bounded by `Γ`, and the a-priori digit bound
`maj₁(row) · maj₁(v) < 2^(b-1)` through `rowBound`. -/
def convPre (J K b : ℕ) (τ : GI) (Γ : ℕ) (discs : List (GI × ℕ)) : Bool :=
  let D := stepRows J τ intCols
  decide (0 < b) && (D.length == 8) && rowsShort D && (discs.length == 65) &&
    pairwiseSeparated discs && (discs.all fun q => decide (n1 q.1 ≤ Γ)) &&
    decide (rowBound J K τ * vmajN Γ < 2 ^ (b - 1))

/-- The product checks for a slice of the discs (one kernel declaration each). -/
def convSlice (J K b : ℕ) (τ : GI) (S : ℕ) (slice : List (GI × ℕ)) : Bool :=
  let U := packU J K b τ
  let vc := vconst b
  let o := offsetC b 1048
  slice.all fun q => convCheck U vc o b S q.1 q.2

theorem stepCertified_of_conv {J K b Γ : ℕ} {τ : GI} {S : ℕ}
    {slices : List (List (GI × ℕ))}
    (hpre : convPre J K b τ Γ slices.flatten = true)
    (hslices : ∀ sl ∈ slices, convSlice J K b τ S sl = true) :
    StepCertified J K τ S slices.flatten := by
  intro t ht
  set discs := slices.flatten
  simp only [convPre, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hpre
  obtain ⟨⟨⟨⟨⟨⟨hb, hD⟩, hshort⟩, hlen⟩, hsep⟩, hΓ⟩, hbound⟩ := hpre
  have hL : (((13 ^ 182 : ℚ) : ℂ)⁻¹) ≠ 0 := by norm_num
  have hbound' : ∀ C ∈ stepRows J τ intCols,
      maj 1 (linR K C) * maj 1 (vrev ((Γ : ℤ), 0)) < 2 ^ (b - 1) := by
    intro C hC
    rw [maj1_vrev_real]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (maj1_linR_stepRows_le J K τ C hC)) hbound
  have hdisc : ∀ q ∈ discs,
      (∀ x ∈ sphere (discCentre K q) (discRadius K q), (paperFamily t).eval x ≠ 0) ∧
      HexRootsMathlib.rootsInDisc (paperFamily t) (discCentre K q) (discRadius K q) = 1 := by
    intro q hq
    obtain ⟨sl, hsl, hqsl⟩ := List.mem_flatten.mp hq
    have hpk := List.all_eq_true.mp (hslices sl hsl) q hqsl
    have hc := discCheck_of_convCheck J K b τ S q.1 q.2 Γ hb hD hshort (hΓ q hq) hbound' hpk
    obtain ⟨h1, h2⟩ := discCheck_sound intCols (by rw [intCols_length]) J K τ S q.1 q.2
      hshort hc ht
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [paperFamily_eq_famPoly, eval_mul, eval_C]
      exact mul_ne_zero hL (h1 x hx)
    · simp only [HexRootsMathlib.rootsInDisc, paperFamily_eq_famPoly, roots_C_mul _ hL] at h2 ⊢
      exact h2
  refine ⟨hdisc, ?_⟩
  exact regular_of_discs (paperFamily t) (paperFamily_monic t).ne_zero
    (discs.map fun q => (discCentre K q, discRadius K q))
    (by rw [paperFamily_natDegree, List.length_map, hlen])
    (by rw [List.pairwise_map]; exact pairwise_of_pairwiseSeparated K hsep)
    (by
      intro d hd
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
      exact (hdisc q hq).2)

theorem StepDatum.cert_of_conv {J K b Γ : ℕ} {τ : GI} {S : ℕ} {slices : List (List (GI × ℕ))}
    {gaps : List ℕ} (hpre : convPre J K b τ Γ slices.flatten = true)
    (hgap : gapsOK slices.flatten gaps = true)
    (hslices : ∀ sl ∈ slices, convSlice J K b τ S sl = true) :
    StepDatum.Cert J K ⟨τ, S, slices.flatten, gaps⟩ := by
  refine ⟨stepCertified_of_conv hpre hslices, ?_⟩
  simp only [convPre, Bool.and_eq_true, beq_iff_eq] at hpre
  exact ⟨hpre.1.1.1.2, hpre.1.1.2, hgap⟩

end Sz8.Monodromy
