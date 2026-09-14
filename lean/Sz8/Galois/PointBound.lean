import Sz8.Galois.ThetaEval

/-!
# The value bound at one pinning point

From exact Gaussian-integer values `G₀, G₁, G₂` of the invariant at centres `y / 2^420` (with
`|y / 2^420| < 2^17`), and roots `z` with `‖y/13³/2^420 − z‖ ≤ 2⁻³⁸⁰`, a kernel comparison of the
symmetric functions of `G` with an integer polynomial `Z` at `t = τ / 2^11` (`symCheck`) gives
`‖(symmetric function of Θ(13³ z)) − Z(t)‖ ≤ 2⁻⁶⁹` (`point_bound`).
-/

namespace Sz8.Galois.PointBound

open Sz8.Monodromy Sz8.Monodromy.GaussPoly Resolvent Lipschitz

/-- The symmetric functions over the Gaussian integers. -/
def gsym (u v w : GI) : Fin 3 → GI :=
  ![gadd (gadd u v) w, gadd (gadd (gmul u v) (gmul u w)) (gmul v w), gmul (gmul u v) w]

theorem gc_gsym (u v w : GI) (m : Fin 3) : gc (gsym u v w m) = sym3 (gc u) (gc v) (gc w) m := by
  fin_cases m <;> simp [gsym, sym3, gc_add, gc_mul]

/-- `Σ c_k τ^k 2^(11 (d - k))` for a coefficient list of length `d + 1`. -/
def zval (τ : GI) (d : ℕ) : List ℤ → GI
  | [] => (0, 0)
  | c :: cs => gadd (gscale (c * 2 ^ (11 * d)) (1, 0)) (gmul τ (zval τ (d - 1) cs))

/-- `Σ c_k t^k`. -/
noncomputable def aevalList (t : ℂ) : List ℤ → ℂ
  | [] => 0
  | c :: cs => (c : ℂ) + t * aevalList t cs

theorem gc_zval (τ : GI) : ∀ (d : ℕ) (cs : List ℤ), cs.length ≤ d + 1 →
    gc (zval τ d cs) = 2 ^ (11 * d) * aevalList (gc τ / 2 ^ 11) cs
  | _, [], _ => by simp [zval, aevalList, gc]
  | 0, c :: cs, h => by
    have : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this
    simp [zval, aevalList, gc, gscale, gadd, gmul]
  | d + 1, c :: cs, h => by
    simp only [zval, aevalList, gc_add, gc_mul, gc_scale, Nat.add_sub_cancel,
      gc_zval τ d cs (by simpa using h)]
    simp only [gc]; push_cast
    rw [show 11 * (d + 1) = 11 * d + 11 from by ring, pow_add]
    field_simp
    simp

/-- The kernel comparison at one point. -/
def symCheck (τ : GI) (G0 G1 G2 : GI) (m : Fin 3) (cs : List ℤ) : Bool :=
  let d := cs.length - 1
  let S := gsym G0 G1 G2 m
  let Zv := zval τ d cs
  let e := 1680 * ((m : ℕ) + 1)
  decide (nsq (S.1 * 2 ^ (11 * d) - Zv.1 * 2 ^ e, S.2 * 2 ^ (11 * d) - Zv.2 * 2 ^ e) ≤
    ((2 : ℤ) ^ (e + 11 * d - 70)) ^ 2)

set_option exponentiation.threshold 2000 in
theorem symErr_small (m : Fin 3) :
    symErr (29120 * ((2 : ℝ) ^ 17) ^ 4) (29120 * (4 * ((2 : ℝ) ^ 17) ^ 3 * (13 ^ 3 * (2 ^ 40 / 2 ^ 420)))) m ≤
      1 / 2 ^ 70 := by
  fin_cases m <;> simp only [symErr, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> norm_num

theorem Θ_const_mul (c : ℂ) (x : Fin 65 → ℂ) (N : Subgroup (Equiv.Perm (Fin 65)))
    (π : Equiv.Perm (Fin 65)) : Θ (fun i => c * x i) N π = c ^ 4 * Θ x N π := by
  classical
  unfold Θ mono
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem sym3_div (u v w : ℂ) (s : ℂ) (hs : s ≠ 0) (m : Fin 3) :
    sym3 (u / s) (v / s) (w / s) m = sym3 u v w m / s ^ ((m : ℕ) + 1) := by
  fin_cases m <;> simp [sym3] <;> field_simp

set_option exponentiation.threshold 2000 in
/-- **The value bound at one point.** -/
theorem point_bound {N : Subgroup (Equiv.Perm (Fin 65))} (hN : Nat.card N = 29120)
    {π₁ π₂ : Equiv.Perm (Fin 65)} {y : Fin 65 → GI} {G0 G1 G2 : GI}
    (hG0 : Θ (fun i => gc (y i)) N 1 = gc G0) (hG1 : Θ (fun i => gc (y i)) N π₁ = gc G1)
    (hG2 : Θ (fun i => gc (y i)) N π₂ = gc G2)
    (hy : ∀ i, nsq (y i) ≤ ((2 ^ 17 - 1) * 2 ^ 420 : ℤ) ^ 2)
    {z : Fin 65 → ℂ} (hz : ∀ i, ‖gc (y i) / 2 ^ 420 - 13 ^ 3 * z i‖ ≤ 13 ^ 3 * (2 ^ 40 / 2 ^ 420))
    {τ : GI} {m : Fin 3} {cs : List ℤ} (hcheck : symCheck τ G0 G1 G2 m cs = true) :
    ‖sym3 (Θ (fun i => 13 ^ 3 * z i) N 1) (Θ (fun i => 13 ^ 3 * z i) N π₁)
        (Θ (fun i => 13 ^ 3 * z i) N π₂) m - aevalList (gc τ / 2 ^ 11) cs‖ ≤ 1 / 2 ^ 69 := by
  set x : Fin 65 → ℂ := fun i => gc (y i) / 2 ^ 420 with hx
  set M : ℝ := 2 ^ 17
  set η : ℝ := 13 ^ 3 * (2 ^ 40 / 2 ^ 420) with hη
  have hηle : η ≤ 1 := by rw [hη]; norm_num
  -- bounds on the centres and the roots
  have hxb : ∀ i, ‖x i‖ ≤ M - 1 := by
    intro i
    have h1 : ‖gc (y i)‖ ^ 2 ≤ (((2 : ℝ) ^ 17 - 1) * 2 ^ 420) ^ 2 := by
      rw [normSq_gc]; exact_mod_cast hy i
    have h2 : ‖gc (y i)‖ ≤ ((2 : ℝ) ^ 17 - 1) * 2 ^ 420 :=
      le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) h1
    simp only [hx, norm_div, norm_pow, Complex.norm_ofNat]
    rw [div_le_iff₀ (by positivity)]
    exact h2
  have hxM : ∀ i, ‖x i‖ ≤ M := fun i => (hxb i).trans (by linarith)
  have hzd : ∀ i, ‖13 ^ 3 * z i - x i‖ ≤ η := fun i => by rw [norm_sub_rev]; exact hz i
  have hzM : ∀ i, ‖13 ^ 3 * z i‖ ≤ M := fun i => by
    calc ‖13 ^ 3 * z i‖ = ‖x i + (13 ^ 3 * z i - x i)‖ := by ring_nf
      _ ≤ ‖x i‖ + ‖13 ^ 3 * z i - x i‖ := norm_add_le _ _
      _ ≤ (M - 1) + 1 := add_le_add (hxb i) ((hzd i).trans hηle)
      _ = M := by ring
  -- the invariant at the roots and at the centres
  have hd : ∀ π, ‖Θ (fun i => 13 ^ 3 * z i) N π - Θ x N π‖ ≤ 29120 * (4 * M ^ 3 * η) := fun π => by
    have := norm_Θ_sub_le hzM hxM hzd N π; rw [hN] at this; exact_mod_cast this
  have hT : ∀ π, ‖Θ (fun i => 13 ^ 3 * z i) N π‖ ≤ 29120 * M ^ 4 := fun π => by
    have := norm_Θ_le hzM N π; rw [hN] at this; exact_mod_cast this
  have hT' : ∀ π, ‖Θ x N π‖ ≤ 29120 * M ^ 4 := fun π => by
    have := norm_Θ_le hxM N π; rw [hN] at this; exact_mod_cast this
  have hsym := norm_sym3_sub_le (hT 1) (hT π₁) (hT π₂) (hT' 1) (hT' π₁) (hT' π₂) (hd 1) (hd π₁)
    (hd π₂) m
  have hErr : symErr (29120 * M ^ 4) (29120 * (4 * M ^ 3 * η)) m ≤ 1 / 2 ^ 70 := symErr_small m
  -- the centres' invariant is the exact value
  have hscale : ∀ π, Θ x N π = Θ (fun i => gc (y i)) N π / (2 ^ 420) ^ 4 := fun π => by
    have h := Θ_const_mul ((2 : ℂ) ^ 420)⁻¹ (fun i => gc (y i)) N π
    rw [show (fun i => ((2 : ℂ) ^ 420)⁻¹ * gc (y i)) = x from funext fun i => by
      rw [hx]; ring] at h
    rw [h, inv_pow]; ring
  have hcent : sym3 (Θ x N 1) (Θ x N π₁) (Θ x N π₂) m =
      gc (gsym G0 G1 G2 m) / ((2 : ℂ) ^ 1680) ^ ((m : ℕ) + 1) := by
    rw [hscale, hscale, hscale, hG0, hG1, hG2, gc_gsym, ← pow_mul,
      show 420 * 4 = 1680 from rfl]
    exact sym3_div _ _ _ _ (pow_ne_zero _ two_ne_zero) m
  -- the kernel comparison
  set d := cs.length - 1 with hdd
  set e := 1680 * ((m : ℕ) + 1) with he
  have hZ : aevalList (gc τ / 2 ^ 11) cs = gc (zval τ d cs) / 2 ^ (11 * d) := by
    rw [gc_zval τ d cs (by omega)]; field_simp
  have hcmp : ‖gc (gsym G0 G1 G2 m) / ((2 : ℂ) ^ 1680) ^ ((m : ℕ) + 1) -
      gc (zval τ d cs) / 2 ^ (11 * d)‖ ≤ 1 / 2 ^ 70 := by
    simp only [symCheck, decide_eq_true_eq] at hcheck
    set S := gsym G0 G1 G2 m
    set Zv := zval τ d cs
    have hsq : ‖gc S * 2 ^ (11 * d) - gc Zv * 2 ^ e‖ ^ 2 ≤ ((2 : ℝ) ^ (e + 11 * d - 70)) ^ 2 := by
      have h := hcheck
      have e1 : gc S * 2 ^ (11 * d) - gc Zv * 2 ^ e =
          gc (S.1 * 2 ^ (11 * d) - Zv.1 * 2 ^ e, S.2 * 2 ^ (11 * d) - Zv.2 * 2 ^ e) := by
        simp only [gc]; push_cast; ring
      rw [e1, normSq_gc]; exact_mod_cast h
    have hle := le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
    have hpos : (0 : ℝ) < 2 ^ (e + 11 * d) := by positivity
    have e2 : gc S / ((2 : ℂ) ^ 1680) ^ ((m : ℕ) + 1) - gc Zv / 2 ^ (11 * d) =
        (gc S * 2 ^ (11 * d) - gc Zv * 2 ^ e) / 2 ^ (e + 11 * d) := by
      rw [he, ← pow_mul, pow_add]; field_simp
    rw [e2, norm_div, norm_pow, Complex.norm_ofNat, div_le_iff₀ hpos]
    calc _ ≤ (2 : ℝ) ^ (e + 11 * d - 70) := hle
      _ = 1 / 2 ^ 70 * 2 ^ (e + 11 * d) := by
        have h70 : 70 ≤ e + 11 * d := by rw [he]; have := m.isLt; omega
        have h2 : (2 : ℝ) ^ (e + 11 * d) = 2 ^ (e + 11 * d - 70) * 2 ^ 70 := by
          rw [← pow_add]; congr 1; omega
        rw [h2]; field_simp
  -- combine
  calc _ = ‖(sym3 (Θ (fun i => 13 ^ 3 * z i) N 1) (Θ (fun i => 13 ^ 3 * z i) N π₁)
          (Θ (fun i => 13 ^ 3 * z i) N π₂) m - sym3 (Θ x N 1) (Θ x N π₁) (Θ x N π₂) m) +
        (sym3 (Θ x N 1) (Θ x N π₁) (Θ x N π₂) m - aevalList (gc τ / 2 ^ 11) cs)‖ := by ring_nf
    _ ≤ symErr (29120 * M ^ 4) (29120 * (4 * M ^ 3 * η)) m + 1 / 2 ^ 70 := by
      refine (norm_add_le _ _).trans (add_le_add hsym ?_)
      rw [hcent, hZ]; exact hcmp
    _ ≤ 1 / 2 ^ 70 + 1 / 2 ^ 70 := by gcongr
    _ = 1 / 2 ^ 69 := by norm_num

end Sz8.Galois.PointBound
