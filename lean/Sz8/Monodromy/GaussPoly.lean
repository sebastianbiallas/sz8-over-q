import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
Kernel-friendly polynomials with Gaussian-integer coefficients, for Rouché certificates.

Coefficients are pairs `(re, im)` of integers, and polynomials are ascending lists. Every
operation is structurally recursive and uses only integer arithmetic. `pshift γ p` is the
exact Taylor shift `p(γ + w)`. Families in a second variable are lists of polynomials,
with the same operations one level up. `maj` and `omaj` are majorants with
`|re| + |im| ≥ |z|`. The soundness lemmas relate all of this to evaluation in `ℂ`.
-/

namespace Sz8.Monodromy.GaussPoly

/-- A Gaussian integer `re + im·i`. -/
abbrev GI := ℤ × ℤ

def gadd (a b : GI) : GI := (a.1 + b.1, a.2 + b.2)
def gmul (a b : GI) : GI := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)
def gscale (k : ℤ) (a : GI) : GI := (k * a.1, k * a.2)

/-- The complex number represented. -/
noncomputable def gc (a : GI) : ℂ := (a.1 : ℂ) + (a.2 : ℂ) * Complex.I

@[simp] theorem gc_zero : gc (0, 0) = 0 := by simp [gc]

theorem gc_add (a b : GI) : gc (gadd a b) = gc a + gc b := by
  simp only [gc, gadd]; push_cast; ring

theorem gc_mul (a b : GI) : gc (gmul a b) = gc a * gc b := by
  simp only [gc, gmul]; push_cast; ring_nf; rw [Complex.I_sq]; ring

theorem gc_scale (k : ℤ) (a : GI) : gc (gscale k a) = (k : ℂ) * gc a := by
  simp only [gc, gscale]; push_cast; ring

/-- `a * 2^k`, through the GMP-accelerated `Nat.shiftLeft`. -/
def ishl (a : ℤ) (k : ℕ) : ℤ :=
  match a with
  | Int.ofNat n => Int.ofNat (n <<< k)
  | Int.negSucc n => -Int.ofNat ((n + 1) <<< k)

theorem ishl_eq (a : ℤ) (k : ℕ) : ishl a k = a * 2 ^ k := by
  cases a with
  | ofNat n => simp [ishl, Nat.shiftLeft_eq]
  | negSucc n =>
    simp only [ishl, Nat.shiftLeft_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]
    push_cast; ring

def gshl (a : GI) (k : ℕ) : GI := (ishl a.1 k, ishl a.2 k)

theorem gc_gshl (a : GI) (k : ℕ) : gc (gshl a k) = 2 ^ k * gc a := by
  simp only [gshl, gc, ishl_eq]; push_cast; ring

/-- `|re| + |im|`, an upper bound for the modulus. -/
def n1 (a : GI) : ℕ := a.1.natAbs + a.2.natAbs

theorem norm_gc_le (a : GI) : ‖gc a‖ ≤ n1 a := by
  simp only [gc, n1]
  push_cast
  calc ‖(a.1 : ℂ) + (a.2 : ℂ) * Complex.I‖ ≤ ‖(a.1 : ℂ)‖ + ‖(a.2 : ℂ) * Complex.I‖ :=
        norm_add_le _ _
    _ = |(a.1 : ℝ)| + |(a.2 : ℝ)| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast, Complex.norm_intCast]
    _ = _ := by push_cast [Nat.cast_natAbs, Int.cast_abs]; rfl

/-- Squared modulus. -/
def nsq (a : GI) : ℤ := a.1 * a.1 + a.2 * a.2

theorem normSq_gc (a : GI) : ‖gc a‖ ^ 2 = nsq a := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [gc, nsq]

/-! ### Polynomials -/

def padd : List GI → List GI → List GI
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => gadd a b :: padd as bs

def pmulC (c : GI) : List GI → List GI
  | [] => []
  | a :: as => gmul c a :: pmulC c as

def pshl (k : ℕ) : List GI → List GI
  | [] => []
  | a :: as => gshl a k :: pshl k as

/-- One Horner step `a + (γ + w) S`. Taking `S` as an argument keeps it shared. -/
def shiftStep (γ a : GI) (S : List GI) : List GI :=
  padd (padd [a] (pmulC γ S)) ((0, 0) :: S)

/-- Taylor shift: the coefficients of `p(γ + w)`. -/
def pshift (γ : GI) : List GI → List GI
  | [] => []
  | a :: as => shiftStep γ a (pshift γ as)

/-- Multiply the coefficient of `x^i` by `2^(K(n-i))`: `2^(Kn) p(x / 2^K)`. -/
def scaleUp (K : ℕ) : ℕ → List GI → List GI
  | _, [] => []
  | n, a :: as => gshl a (K * n) :: scaleUp K (n - 1) as

/-- Horner evaluation in `ℂ`. -/
noncomputable def peval : List GI → ℂ → ℂ
  | [], _ => 0
  | a :: as, w => gc a + w * peval as w

@[simp] theorem peval_nil (w : ℂ) : peval [] w = 0 := rfl
@[simp] theorem peval_cons (a : GI) (as : List GI) (w : ℂ) :
    peval (a :: as) w = gc a + w * peval as w := rfl

theorem peval_padd : ∀ (as bs : List GI) (w : ℂ), peval (padd as bs) w = peval as w + peval bs w
  | [], bs, w => by simp [padd]
  | a :: as, [], w => by simp [padd]
  | a :: as, b :: bs, w => by
    simp only [padd, peval_cons, gc_add, peval_padd as bs w]; ring

theorem peval_pmulC (c : GI) : ∀ (as : List GI) (w : ℂ), peval (pmulC c as) w = gc c * peval as w
  | [], w => by simp [pmulC]
  | a :: as, w => by simp only [pmulC, peval_cons, gc_mul, peval_pmulC c as w]; ring

theorem peval_pshl (k : ℕ) : ∀ (as : List GI) (y : ℂ), peval (pshl k as) y = 2 ^ k * peval as y
  | [], y => by simp [pshl]
  | a :: as, y => by simp only [pshl, peval_cons, gc_gshl, peval_pshl k as y]; ring

theorem peval_pshift (γ : GI) : ∀ (as : List GI) (w : ℂ), peval (pshift γ as) w = peval as (gc γ + w)
  | [], w => by simp [pshift]
  | a :: as, w => by
    simp only [pshift, shiftStep, peval_padd, peval_pmulC, peval_cons, peval_nil, gc_zero,
      peval_pshift γ as w]
    ring

theorem peval_scaleUp (K : ℕ) : ∀ (n : ℕ) (as : List GI), as.length ≤ n + 1 → ∀ w : ℂ,
    peval (scaleUp K n as) w = (2 : ℂ) ^ (K * n) * peval as (w / 2 ^ K)
  | _, [], _, w => by simp [scaleUp]
  | 0, a :: as, h, w => by
    have : as = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this
    simp [scaleUp, gc_gshl]
  | n + 1, a :: as, h, w => by
    simp only [scaleUp, peval_cons, gc_gshl, Nat.add_sub_cancel,
      peval_scaleUp K n as (by simpa using h) w]
    have h2 : (2 : ℂ) ^ K ≠ 0 := pow_ne_zero _ two_ne_zero
    simp only [mul_add, mul_one, pow_add]
    field_simp

/-- Majorant `∑ (|re| + |im|) W^m`. -/
def maj (W : ℕ) : List GI → ℕ
  | [] => 0
  | a :: as => n1 a + W * maj W as

theorem norm_peval_le (W : ℕ) : ∀ (as : List GI) {w : ℂ}, ‖w‖ ≤ W → ‖peval as w‖ ≤ maj W as
  | [], w, _ => by simp [maj]
  | a :: as, w, hw => by
    simp only [peval_cons, maj]
    push_cast
    calc ‖gc a + w * peval as w‖ ≤ ‖gc a‖ + ‖w‖ * ‖peval as w‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ n1 a + W * maj W as := by
          gcongr
          · exact norm_gc_le a
          · exact norm_peval_le W as hw

/-! ### Families: polynomials in a second variable `σ` with polynomial coefficients -/

def oadd : List (List GI) → List (List GI) → List (List GI)
  | [], Qs => Qs
  | P :: Ps, [] => P :: Ps
  | P :: Ps, Q :: Qs => padd P Q :: oadd Ps Qs

def omulC (c : GI) : List (List GI) → List (List GI)
  | [] => []
  | P :: Ps => pmulC c P :: omulC c Ps

def oshiftStep (γ : GI) (P : List GI) (S : List (List GI)) : List (List GI) :=
  oadd (oadd [P] (omulC γ S)) ([] :: S)

/-- Taylor shift in the outer variable: the coefficients of `Φ(x, γ + σ)` in `σ`. -/
def oshift (γ : GI) : List (List GI) → List (List GI)
  | [] => []
  | P :: Ps => oshiftStep γ P (oshift γ Ps)

/-- Scale the coefficient of `σ^j` by `2^(J(n-j))`. -/
def oscale (J : ℕ) : ℕ → List (List GI) → List (List GI)
  | _, [] => []
  | n, P :: Ps => pshl (J * n) P :: oscale J (n - 1) Ps

/-- `∑_j σ^j P_j(x)`. -/
noncomputable def oeval : List (List GI) → ℂ → ℂ → ℂ
  | [], _, _ => 0
  | P :: Ps, x, σ => peval P x + σ * oeval Ps x σ

@[simp] theorem oeval_nil (x σ : ℂ) : oeval [] x σ = 0 := rfl
@[simp] theorem oeval_cons (P : List GI) (Ps : List (List GI)) (x σ : ℂ) :
    oeval (P :: Ps) x σ = peval P x + σ * oeval Ps x σ := rfl

theorem oeval_oadd : ∀ (Ps Qs : List (List GI)) (x σ : ℂ),
    oeval (oadd Ps Qs) x σ = oeval Ps x σ + oeval Qs x σ
  | [], Qs, x, σ => by simp [oadd]
  | P :: Ps, [], x, σ => by simp [oadd]
  | P :: Ps, Q :: Qs, x, σ => by
    simp only [oadd, oeval_cons, peval_padd, oeval_oadd Ps Qs x σ]; ring

theorem oeval_omulC (c : GI) : ∀ (Ps : List (List GI)) (x σ : ℂ),
    oeval (omulC c Ps) x σ = gc c * oeval Ps x σ
  | [], x, σ => by simp [omulC]
  | P :: Ps, x, σ => by
    simp only [omulC, oeval_cons, peval_pmulC, oeval_omulC c Ps x σ]; ring

theorem oeval_oshift (γ : GI) : ∀ (Ps : List (List GI)) (x σ : ℂ),
    oeval (oshift γ Ps) x σ = oeval Ps x (gc γ + σ)
  | [], x, σ => by simp [oshift]
  | P :: Ps, x, σ => by
    simp only [oshift, oshiftStep, oeval_oadd, oeval_omulC, oeval_cons, oeval_nil, peval_nil,
      oeval_oshift γ Ps x σ]
    ring

theorem oeval_oscale (J : ℕ) : ∀ (n : ℕ) (Ps : List (List GI)), Ps.length ≤ n + 1 → ∀ x σ : ℂ,
    oeval (oscale J n Ps) x σ = (2 : ℂ) ^ (J * n) * oeval Ps x (σ / 2 ^ J)
  | _, [], _, x, σ => by simp [oscale]
  | 0, P :: Ps, h, x, σ => by
    have : Ps = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this
    simp [oscale, peval_pshl]
  | n + 1, P :: Ps, h, x, σ => by
    simp only [oscale, oeval_cons, peval_pshl, Nat.add_sub_cancel,
      oeval_oscale J n Ps (by simpa using h) x σ]
    have h2 : (2 : ℂ) ^ J ≠ 0 := pow_ne_zero _ two_ne_zero
    simp only [mul_add, mul_one, pow_add]
    field_simp

/-- Majorant in two variables: `∑_j S^j maj W P_j`. -/
def omaj (S W : ℕ) : List (List GI) → ℕ
  | [] => 0
  | P :: Ps => maj W P + S * omaj S W Ps

theorem norm_oeval_le (S W : ℕ) : ∀ (Ps : List (List GI)) {x σ : ℂ}, ‖x‖ ≤ W → ‖σ‖ ≤ S →
    ‖oeval Ps x σ‖ ≤ omaj S W Ps
  | [], x, σ, _, _ => by simp [omaj]
  | P :: Ps, x, σ, hx, hσ => by
    simp only [oeval_cons, omaj]
    push_cast
    calc ‖peval P x + σ * oeval Ps x σ‖ ≤ ‖peval P x‖ + ‖σ‖ * ‖oeval Ps x σ‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ maj W P + S * omaj S W Ps := by
          gcongr
          · exact norm_peval_le W P hx
          · exact norm_oeval_le S W Ps hx hσ

/-- Remove the coefficient of `σ^0 x^1`. -/
def kill01 : List (List GI) → List (List GI)
  | [] => []
  | P :: Ps => (match P with
      | [] => []
      | a :: [] => [a]
      | a :: _ :: rest => a :: (0, 0) :: rest) :: Ps

/-- The coefficient of `σ^0 x^1`. -/
def coeff01 (Ps : List (List GI)) : GI := (Ps.headD []).getD 1 (0, 0)

theorem oeval_kill01 (Ps : List (List GI)) (x σ : ℂ) :
    oeval Ps x σ = oeval (kill01 Ps) x σ + gc (coeff01 Ps) * x := by
  rcases Ps with _ | ⟨P, Ps⟩
  · simp [kill01, coeff01]
  · rcases P with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp [kill01, coeff01]; ring

end Sz8.Monodromy.GaussPoly
