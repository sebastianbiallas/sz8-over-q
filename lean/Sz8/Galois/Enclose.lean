import Sz8.Monodromy.StepCheck
import Mathlib.Algebra.BigOperators.Fin

/-!
# Root enclosures from one exact evaluation

At a dyadic parameter `t = τ / 2^J` and a dyadic point `c = γ / 2^K`, the kernel evaluates the scaled
family exactly (`hornerGI` on `scaleUp K 65 (ocollapse τ (oscale J 7 intCols))`, no Taylor shift).
If the family is the product over roots `z j` lying in given discs, and `c` is at distance at least
`L j / 2^20` from every disc `j ≠ i`, then `‖c - z i‖ · ∏_{j ≠ i} L j / 2^20 ≤ ‖f(c, t)‖`, so an exact
integer inequality gives `‖c - z i‖ ≤ E / 2^K` (`encCheck_sound`).
-/

open Polynomial Metric

namespace Sz8.Galois.Enclose

open Sz8.Monodromy Sz8.Monodromy.GaussPoly

/-- Evaluate the parameter variable of a family of columns at `τ`. -/
def ocollapse (τ : GI) : List (List GI) → List GI
  | [] => []
  | P :: Ps => padd P (pmulC τ (ocollapse τ Ps))

theorem peval_ocollapse (τ : GI) : ∀ (Ps : List (List GI)) (x : ℂ),
    peval (ocollapse τ Ps) x = oeval Ps x (gc τ)
  | [], x => by simp [ocollapse]
  | P :: Ps, x => by
    simp only [ocollapse, peval_padd, peval_pmulC, peval_ocollapse τ Ps x, oeval_cons]

/-- Exact Horner evaluation over the Gaussian integers. -/
def hornerGI : List GI → GI → GI
  | [], _ => (0, 0)
  | a :: as, x => gadd a (gmul x (hornerGI as x))

theorem gc_hornerGI : ∀ (as : List GI) (x : GI), gc (hornerGI as x) = peval as (gc x)
  | [], x => by simp [hornerGI]
  | a :: as, x => by simp only [hornerGI, gc_add, gc_mul, gc_hornerGI as x, peval_cons]

/-- The scaled coefficients at `t = τ / 2^J`. -/
def evalRow (K J : ℕ) (τ : GI) : List GI := scaleUp K 65 (ocollapse τ (oscale J 7 intCols))

/-- The enclosure check for root `i`. -/
def encCheck (K J : ℕ) (τ : GI) (d : Fin 65 → GI × ℕ) (E : ℕ) (γ : GI) (i : Fin 65)
    (L : Fin 65 → ℕ) : Bool :=
  let G := hornerGI (evalRow K J τ) γ
  ((List.finRange 65).all fun j => j == i || (decide (0 < L j) &&
      decide (((L j + (d j).2 : ℕ) : ℤ) ^ 2 * 2 ^ (2 * (K - 20)) ≤
        nsq (γ.1 - (d j).1.1 * 2 ^ (K - 20), γ.2 - (d j).1.2 * 2 ^ (K - 20))))) &&
    decide (nsq G * 2 ^ (2 * (K + 20 * 65)) ≤
      ((E * ((List.finRange 65).map fun j => if j = i then 2 ^ 20 else L j).prod : ℕ) : ℤ) ^ 2 *
        13 ^ 364 * 2 ^ (2 * (65 * K + 7 * J)))

set_option exponentiation.threshold 400 in
/-- **Soundness of the enclosure check.** -/
theorem encCheck_sound {K J : ℕ} (hK : 20 ≤ K) {τ γ : GI} {E : ℕ} {i : Fin 65}
    {d : Fin 65 → GI × ℕ} {L : Fin 65 → ℕ} (hshort : (ocollapse τ (oscale J 7 intCols)).length ≤ 66)
    (hcheck : encCheck K J τ d E γ i L = true) {z : Fin 65 → ℂ}
    (hprod : ∀ x, ‖(paperFamily (gc τ / 2 ^ J)).eval x‖ = ∏ j, ‖x - z j‖)
    (hzd : ∀ j, z j ∈ ball (discCentre 20 (d j)) (discRadius 20 (d j))) :
    ‖gc γ / 2 ^ K - z i‖ ≤ (E : ℝ) / 2 ^ K := by
  classical
  set c : ℂ := gc γ / 2 ^ K with hc
  set t : ℂ := gc τ / 2 ^ J with ht
  set G := hornerGI (evalRow K J τ) γ with hG
  set m : Fin 65 → ℕ := fun j => if j = i then 2 ^ 20 else L j with hm
  simp only [encCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    beq_iff_eq] at hcheck
  obtain ⟨hdist, hfin⟩ := hcheck
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  -- the exact value
  have hval : gc G = (2 : ℂ) ^ (K * 65) * ((2 : ℂ) ^ (J * 7) * oeval intCols c t) := by
    rw [hG, gc_hornerGI, evalRow, peval_scaleUp K 65 _ hshort, peval_ocollapse,
      oeval_oscale J 7 intCols (by rw [intCols_length])]
  have hf : (paperFamily t).eval c = (((13 ^ 182 : ℚ) : ℂ))⁻¹ * oeval intCols c t := by
    rw [paperFamily_eq_famPoly, eval_mul, eval_C, eval_famPoly]
  have hnormf : ‖(paperFamily t).eval c‖ * ((13 : ℝ) ^ 182 * 2 ^ (65 * K + 7 * J)) = ‖gc G‖ := by
    rw [hf, hval, norm_mul, norm_mul, norm_mul, norm_inv, norm_pow, norm_pow]
    simp only [Complex.norm_ofNat, Complex.norm_ratCast]
    push_cast
    rw [abs_of_pos (by positivity : (0 : ℝ) < 13 ^ 182)]
    field_simp
    ring
  -- distances to the other discs
  have hℓ : ∀ j, j ≠ i → (L j : ℝ) / 2 ^ 20 ≤ ‖c - z j‖ := by
    intro j hj
    have h := (hdist j (List.mem_finRange j)).resolve_left hj
    obtain ⟨-, hineq⟩ := h
    set C := (d j).1
    set R := (d j).2
    have hsq : (((L j + R : ℕ) : ℝ) * 2 ^ (K - 20)) ^ 2 ≤ ‖gc γ - 2 ^ (K - 20) * gc C‖ ^ 2 := by
      have e : gc γ - 2 ^ (K - 20) * gc C = gc (γ.1 - C.1 * 2 ^ (K - 20), γ.2 - C.2 * 2 ^ (K - 20)) := by
        simp only [gc]; push_cast; ring
      rw [e, normSq_gc]
      have := hineq
      rw [mul_pow, ← pow_mul]
      exact_mod_cast (by simpa [mul_comm] using this)
    have hle : ((L j + R : ℕ) : ℝ) * 2 ^ (K - 20) ≤ ‖gc γ - 2 ^ (K - 20) * gc C‖ :=
      le_of_sq_le_sq hsq (norm_nonneg _) |>.trans' le_rfl
    have hcen : ‖c - discCentre 20 (d j)‖ = ‖gc γ - 2 ^ (K - 20) * gc C‖ / 2 ^ K := by
      have e : (2 : ℂ) ^ K = 2 ^ (K - 20) * 2 ^ 20 := by rw [← pow_add]; congr 1; omega
      have hid : c - discCentre 20 (d j) = (gc γ - 2 ^ (K - 20) * gc C) / 2 ^ K := by
        rw [hc, discCentre, e]; field_simp; rfl
      rw [hid, norm_div, norm_pow, Complex.norm_ofNat]
    have hball := mem_ball.1 (hzd j)
    rw [dist_eq_norm, discRadius] at hball
    have htri : ‖c - discCentre 20 (d j)‖ ≤ ‖c - z j‖ + ‖z j - discCentre 20 (d j)‖ := by
      calc ‖c - discCentre 20 (d j)‖ = ‖(c - z j) + (z j - discCentre 20 (d j))‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have e20 : ((L j + R : ℕ) : ℝ) * 2 ^ (K - 20) / 2 ^ K = ((L j : ℝ) + R) / 2 ^ 20 := by
      have e : (2 : ℝ) ^ K = 2 ^ (K - 20) * 2 ^ 20 := by rw [← pow_add]; congr 1; omega
      rw [e]; push_cast; field_simp
    have : ((L j : ℝ) + R) / 2 ^ 20 ≤ ‖c - discCentre 20 (d j)‖ := by
      rw [hcen, ← e20]; exact div_le_div_of_nonneg_right hle h2K.le
    have : (L j : ℝ) / 2 ^ 20 + (R : ℝ) / 2 ^ 20 ≤ ‖c - z j‖ + (R : ℝ) / 2 ^ 20 := by
      rw [← add_div]; linarith
    linarith
  -- the product of the lower bounds
  have hprodm : (((List.finRange 65).map fun j => if j = i then 2 ^ 20 else L j).prod : ℕ) =
      ∏ j, m j := by
    rw [Fin.prod_univ_def]
  rw [hprodm] at hfin
  have hmpos : ∀ j, (0 : ℝ) < m j := fun j => by
    by_cases hj : j = i
    · simp [hm, hj]
    · have := ((hdist j (List.mem_finRange j)).resolve_left hj).1
      simp only [hm, hj, ↓reduceIte]; exact_mod_cast this
  have hPmpos : (0 : ℝ) < ∏ j, (m j : ℝ) := Finset.prod_pos fun j _ => hmpos j
  set Pm := ∏ j, (m j : ℝ) with hPm
  set A := 65 * K + 7 * J with hA
  have hfin' : ‖gc G‖ * 2 ^ (K + 20 * 65) ≤ (E : ℝ) * Pm * 13 ^ 182 * 2 ^ A := by
    set a : ℝ := 13 ^ 182 with ha
    set b : ℝ := 2 ^ A with hb
    set e : ℝ := 2 ^ (K + 20 * 65) with he
    have h' : ((nsq G : ℤ) : ℝ) * 2 ^ (2 * (K + 20 * 65)) ≤
        (((E * ∏ j, m j : ℕ) : ℤ) : ℝ) ^ 2 * 13 ^ 364 * 2 ^ (2 * A) := by exact_mod_cast hfin
    rw [← normSq_gc] at h'
    have ePm : (((E * ∏ j, m j : ℕ) : ℤ) : ℝ) = (E : ℝ) * Pm := by rw [hPm]; push_cast; rfl
    have h13 : (13 : ℝ) ^ 364 = a ^ 2 := by rw [ha, ← pow_mul]
    have h2A : (2 : ℝ) ^ (2 * A) = b ^ 2 := by rw [hb, ← pow_mul, mul_comm]
    have h2e : (2 : ℝ) ^ (2 * (K + 20 * 65)) = e ^ 2 := by rw [he, ← pow_mul, mul_comm]
    rw [ePm, h13, h2A, h2e] at h'
    have hcast : (‖gc G‖ * e) ^ 2 ≤ ((E : ℝ) * Pm * a * b) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow]
      calc ‖gc G‖ ^ 2 * e ^ 2 ≤ ((E : ℝ) * Pm) ^ 2 * a ^ 2 * b ^ 2 := h'
        _ = _ := by rw [mul_pow]
    have hpa : 0 ≤ a := by rw [ha]; positivity
    have hpb : 0 ≤ b := by rw [hb]; positivity
    have hE : (0 : ℝ) ≤ E := Nat.cast_nonneg E
    clear_value a b e
    exact le_of_pow_le_pow_left₀ two_ne_zero
      (mul_nonneg (mul_nonneg (mul_nonneg hE hPmpos.le) hpa) hpb) hcast
  -- the enclosure
  have hmain : ‖c - z i‖ * ∏ j, ((m j : ℝ) / 2 ^ 20) ≤ ‖(paperFamily t).eval c‖ := by
    rw [hprod c, ← Finset.mul_prod_erase _ (fun j => ‖c - z j‖) (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun j => (m j : ℝ) / 2 ^ 20) (Finset.mem_univ i)]
    have hmi : (m i : ℝ) / 2 ^ 20 = 1 := by simp only [hm, ↓reduceIte]; norm_num
    rw [hmi, one_mul]
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod
      (fun j _ => div_nonneg (hmpos j).le (pow_nonneg zero_le_two 20))
      (fun j hj => by
        have hji := Finset.ne_of_mem_erase hj
        simpa [hm, hji] using hℓ j hji)) (norm_nonneg _)
  have hprodeq : ∏ j, ((m j : ℝ) / 2 ^ 20) = Pm / 2 ^ (20 * 65) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [hprodeq] at hmain
  have hkey : ‖c - z i‖ * 2 ^ K * (Pm * 13 ^ 182 * 2 ^ A) ≤ (E : ℝ) * (Pm * 13 ^ 182 * 2 ^ A) := by
    have h1 := mul_le_mul_of_nonneg_right hmain
      (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg zero_le_two _) : (0 : ℝ) ≤ 13 ^ 182 * 2 ^ A)
    rw [hnormf] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg zero_le_two _ : (0 : ℝ) ≤ 2 ^ (K + 20 * 65))
    have e : ‖c - z i‖ * (Pm / 2 ^ (20 * 65)) * (13 ^ 182 * 2 ^ A) * 2 ^ (K + 20 * 65) =
        ‖c - z i‖ * 2 ^ K * (Pm * 13 ^ 182 * 2 ^ A) := by
      rw [show (2 : ℝ) ^ (K + 20 * 65) = 2 ^ K * 2 ^ (20 * 65) from pow_add _ _ _]
      field_simp
    rw [e] at h2
    linarith
  have hpos : (0 : ℝ) < Pm * 13 ^ 182 * 2 ^ A :=
    mul_pos (mul_pos hPmpos (pow_pos (by norm_num) _)) (pow_pos two_pos _)
  have := le_of_mul_le_mul_right hkey hpos
  rw [le_div_iff₀ h2K]
  exact this

end Sz8.Galois.Enclose
