import Sz8.Monodromy.GaussPoly
import HexRootsMathlib.Rouche

/-!
Rouché certificates for one root disc along one parameter step.

A family `F(x, t) = ∑_j t^j P_j(x)` is given by Gaussian-integer columns `P_j`. A step is
centred at `t₀ = τ / 2^J` with radius `h = S / 2^J`, and a disc at `c = γ / 2^K` with
radius `R = W / 2^K`. `discCheck` computes the exact Taylor expansion
`2^(65K + 7J) F(c + w/2^K, t₀ + σ/2^J) = ∑ E_{l,m} w^m σ^l`, and checks that the linear
term `E_{0,1} w` dominates the majorant of all other terms on `|w| = W`, `|σ| ≤ S`.

`discCheck_sound`: for every `t` with `|t - t₀| ≤ h`, `F(·, t)` has exactly one root in
the open disc (with multiplicity) and none on its boundary circle.
-/

open Polynomial Metric

namespace Sz8.Monodromy.GaussPoly

/-- The polynomial with coefficient list `l`. -/
noncomputable def toPolyC : List GI → ℂ[X]
  | [] => 0
  | a :: as => C (gc a) + X * toPolyC as

theorem eval_toPolyC : ∀ (l : List GI) (x : ℂ), (toPolyC l).eval x = peval l x
  | [], x => by simp [toPolyC]
  | a :: as, x => by simp [toPolyC, eval_toPolyC as x]

/-- The family `∑_j t^j P_j` at parameter `t`. -/
noncomputable def famPoly : List (List GI) → ℂ → ℂ[X]
  | [], _ => 0
  | P :: Ps, t => toPolyC P + C t * famPoly Ps t

theorem eval_famPoly : ∀ (Ps : List (List GI)) (t x : ℂ), (famPoly Ps t).eval x = oeval Ps x t
  | [], t, x => by simp [famPoly]
  | P :: Ps, t, x => by simp [famPoly, eval_toPolyC, eval_famPoly Ps t x]

/-- Shift every row to the disc centre after scaling the root variable. -/
def discRows (K : ℕ) (γ : GI) (D : List (List GI)) : List (List GI) :=
  D.map fun P => pshift γ (scaleUp K 65 P)

theorem oeval_discRows (K : ℕ) (γ : GI) :
    ∀ (D : List (List GI)), (∀ P ∈ D, P.length ≤ 66) → ∀ w σ : ℂ,
      oeval (discRows K γ D) w σ = (2 : ℂ) ^ (K * 65) * oeval D ((gc γ + w) / 2 ^ K) σ
  | [], _, w, σ => by simp [discRows]
  | P :: D, h, w, σ => by
    have hP := h P (List.mem_cons_self ..)
    have ih := oeval_discRows K γ D (fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)) w σ
    simp only [discRows, List.map_cons, oeval_cons] at ih ⊢
    rw [ih, peval_pshift, peval_scaleUp K 65 P (by omega)]
    ring

/-- The step polynomial rows: scale `t` by `2^J` and shift to `τ`. -/
def stepRows (J : ℕ) (τ : GI) (cols : List (List GI)) : List (List GI) :=
  oshift τ (oscale J 7 cols)

/-- Row lengths are preserved by the step transformation (as an upper bound). -/
def rowsShort (D : List (List GI)) : Bool := D.all fun P => decide (P.length ≤ 66)

/-- The certificate for one disc: the linear term dominates the majorant of the rest. -/
def discCheck (D : List (List GI)) (K S : ℕ) (γ : GI) (W : ℕ) : Bool :=
  let E := discRows K γ D
  decide (0 < W) && decide (((omaj S W (kill01 E) : ℕ) : ℤ) ^ 2 < nsq (coeff01 E) * W ^ 2)

/-- The disc certificate is sound: one root in the disc, none on its boundary, for every
parameter in the step. -/
theorem discCheck_sound (cols : List (List GI)) (hcols : cols.length ≤ 8)
    (J K : ℕ) (τ : GI) (S : ℕ) (γ : GI) (W : ℕ)
    (hshort : rowsShort (stepRows J τ cols) = true)
    (hcheck : discCheck (stepRows J τ cols) K S γ W = true)
    {t : ℂ} (ht : ‖t - gc τ / 2 ^ J‖ ≤ (S : ℝ) / 2 ^ J) :
    (∀ x ∈ sphere (gc γ / 2 ^ K) ((W : ℝ) / 2 ^ K), (famPoly cols t).eval x ≠ 0) ∧
      HexRootsMathlib.rootsInDisc (famPoly cols t) (gc γ / 2 ^ K) ((W : ℝ) / 2 ^ K) = 1 := by
  set D := stepRows J τ cols
  set E := discRows K γ D
  simp only [discCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨hW, hdom⟩ := hcheck
  have hlen : ∀ P ∈ D, P.length ≤ 66 := by
    intro P hP; simpa using List.all_eq_true.mp hshort P hP
  set c : ℂ := gc γ / 2 ^ K
  set R : ℝ := (W : ℝ) / 2 ^ K
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  have h2J : (0 : ℝ) < 2 ^ J := by positivity
  have hRpos : 0 < R := by positivity
  set lam : ℂ := (2 : ℂ) ^ (K * 65) * 2 ^ (J * 7)
  have hlam : lam ≠ 0 := by simp [lam]
  -- The exact identity between the expansion and the family.
  have key : ∀ x : ℂ, oeval E ((2 : ℂ) ^ K * x - gc γ) ((2 : ℂ) ^ J * t - gc τ) =
      lam * (famPoly cols t).eval x := by
    intro x
    rw [oeval_discRows K γ D hlen]
    simp only [D, stepRows]
    rw [oeval_oshift, oeval_oscale J 7 cols (by omega), eval_famPoly]
    have h2 : (2 : ℂ) ^ K ≠ 0 := pow_ne_zero _ two_ne_zero
    have h2' : (2 : ℂ) ^ J ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [show (gc γ + ((2 : ℂ) ^ K * x - gc γ)) / 2 ^ K = x by field_simp; ring,
      show (gc τ + ((2 : ℂ) ^ J * t - gc τ)) / 2 ^ J = t by field_simp; ring]
    simp only [lam]; ring
  -- The comparison polynomial `g(x) = λ⁻¹ E₀₁ (2^K x - γ)`.
  set e := gc (coeff01 E)
  let g : ℂ[X] := C (lam⁻¹ * e * 2 ^ K) * (X - C c)
  have hg_eval : ∀ x, g.eval x = lam⁻¹ * e * ((2 : ℂ) ^ K * x - gc γ) := by
    intro x
    simp only [g, eval_mul, eval_C, eval_sub, eval_X, c]
    field_simp
  -- `|σ| ≤ S`, and `|w| = W` on the circle.
  have hσ : ‖(2 : ℂ) ^ J * t - gc τ‖ ≤ S := by
    have : (2 : ℂ) ^ J * t - gc τ = (2 : ℂ) ^ J * (t - gc τ / 2 ^ J) := by
      field_simp
    rw [this, norm_mul, norm_pow, Complex.norm_ofNat]
    calc (2 : ℝ) ^ J * ‖t - gc τ / 2 ^ J‖ ≤ 2 ^ J * ((S : ℝ) / 2 ^ J) := by gcongr
      _ = S := by field_simp
  have hw : ∀ x ∈ sphere c R, ‖(2 : ℂ) ^ K * x - gc γ‖ = W := by
    intro x hx
    have hx' : ‖x - c‖ = R := by simpa [dist_eq_norm] using hx
    have : (2 : ℂ) ^ K * x - gc γ = (2 : ℂ) ^ K * (x - c) := by simp only [c]; field_simp
    rw [this, norm_mul, norm_pow, Complex.norm_ofNat, hx']
    simp only [R]; field_simp
  -- Domination: the majorant is below `|E₀₁| W`.
  have hM : (omaj S W (kill01 E) : ℝ) < ‖e‖ * W := by
    have hsq : ((omaj S W (kill01 E) : ℝ)) ^ 2 < (‖e‖ * W) ^ 2 := by
      rw [mul_pow, normSq_gc]
      exact_mod_cast hdom
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  have hlam_norm : 0 < ‖lam⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hlam)
  have hstrict : ∀ x ∈ sphere c R,
      ‖(famPoly cols t).eval x - g.eval x‖ < ‖g.eval x‖ := by
    intro x hx
    have hdiff : (famPoly cols t).eval x - g.eval x =
        lam⁻¹ * oeval (kill01 E) ((2 : ℂ) ^ K * x - gc γ) ((2 : ℂ) ^ J * t - gc τ) := by
      have hk := oeval_kill01 E ((2 : ℂ) ^ K * x - gc γ) ((2 : ℂ) ^ J * t - gc τ)
      rw [key x] at hk
      rw [hg_eval]
      field_simp
      linear_combination hk
    rw [hdiff, hg_eval, norm_mul, norm_mul, norm_mul, hw x hx]
    have hbound := norm_oeval_le S W (kill01 E) (le_of_eq (hw x hx)) hσ
    calc ‖lam⁻¹‖ * ‖oeval (kill01 E) ((2 : ℂ) ^ K * x - gc γ) ((2 : ℂ) ^ J * t - gc τ)‖
        ≤ ‖lam⁻¹‖ * omaj S W (kill01 E) := by gcongr
      _ < ‖lam⁻¹‖ * (‖e‖ * W) := by gcongr
      _ = ‖lam⁻¹‖ * ‖e‖ * W := by ring
  refine ⟨fun x hx h0 => ?_, ?_⟩
  · have := hstrict x hx
    rw [h0, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  · rw [HexRootsMathlib.rouche hRpos.le hstrict]
    -- `g` is a nonzero multiple of `X - c`.
    have he : e ≠ 0 := by
      intro he0
      rw [he0, norm_zero, zero_mul] at hM
      exact absurd hM (not_lt.mpr (Nat.cast_nonneg _))
    have hcoef : lam⁻¹ * e * 2 ^ K ≠ 0 := by
      simp [hlam, he]
    classical
    simp only [HexRootsMathlib.rootsInDisc, g, roots_C_mul _ hcoef, roots_X_sub_C]
    rw [show ({c} : Multiset ℂ) = c ::ₘ 0 from rfl,
      Multiset.countP_cons_of_pos _ (by simpa using hRpos), Multiset.countP_zero]

end Sz8.Monodromy.GaussPoly
