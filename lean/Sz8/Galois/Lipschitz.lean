import Sz8.Galois.Resolvent
import Mathlib.Analysis.Complex.Basic

/-!
# Error propagation for the relative invariant

Elementary bounds used to pass from the invariant at approximate root centres to the invariant at the
certified roots: a degree-4 monomial moves by at most `4 M³ η` (`norm_mono_sub_le`), `Θ` by at most
`|N| · 4 M³ η` (`norm_Θ_sub_le`), and the three symmetric functions by `3d`, `6Td`, `3T²d`
(`norm_sym3_sub_le`).
-/

namespace Sz8.Galois.Lipschitz

open Resolvent

theorem norm_mono_sub_le {a b c a' b' c' : ℂ} {M η : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
    (ha' : ‖a'‖ ≤ M) (hb' : ‖b'‖ ≤ M) (hda : ‖a - a'‖ ≤ η) (hdb : ‖b - b'‖ ≤ η) (hdc : ‖c - c'‖ ≤ η) :
    ‖a ^ 2 * b * c - a' ^ 2 * b' * c'‖ ≤ 4 * M ^ 3 * η := by
  have hM : 0 ≤ M := (norm_nonneg _).trans ha
  have hη : 0 ≤ η := (norm_nonneg _).trans hda
  have e : a ^ 2 * b * c - a' ^ 2 * b' * c' =
      (a - a') * (a + a') * b * c + a' ^ 2 * (b - b') * c + a' ^ 2 * b' * (c - c') := by ring
  rw [e]
  have h1 : ‖(a - a') * (a + a') * b * c‖ ≤ η * (2 * M) * M * M := by
    rw [norm_mul, norm_mul, norm_mul]
    have hs : ‖a + a'‖ ≤ 2 * M := (norm_add_le _ _).trans (by linarith)
    gcongr
  have h2 : ‖a' ^ 2 * (b - b') * c‖ ≤ M ^ 2 * η * M := by
    rw [norm_mul, norm_mul, norm_pow]; gcongr
  have h3 : ‖a' ^ 2 * b' * (c - c')‖ ≤ M ^ 2 * M * η := by
    rw [norm_mul, norm_mul, norm_pow]; gcongr
  calc _ ≤ ‖(a - a') * (a + a') * b * c‖ + ‖a' ^ 2 * (b - b') * c‖ + ‖a' ^ 2 * b' * (c - c')‖ :=
        norm_add₃_le
    _ ≤ η * (2 * M) * M * M + M ^ 2 * η * M + M ^ 2 * M * η := by gcongr
    _ = 4 * M ^ 3 * η := by ring

theorem norm_mono_le {a b c : ℂ} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M) :
    ‖a ^ 2 * b * c‖ ≤ M ^ 4 := by
  rw [norm_mul, norm_mul, norm_pow]
  have hM : 0 ≤ M := (norm_nonneg _).trans ha
  calc ‖a‖ ^ 2 * ‖b‖ * ‖c‖ ≤ M ^ 2 * M * M := by gcongr
    _ = M ^ 4 := by ring

theorem norm_Θ_sub_le {x x' : Fin 65 → ℂ} {M η : ℝ} (hx : ∀ i, ‖x i‖ ≤ M) (hx' : ∀ i, ‖x' i‖ ≤ M)
    (hd : ∀ i, ‖x i - x' i‖ ≤ η) (N : Subgroup (Equiv.Perm (Fin 65))) (π : Equiv.Perm (Fin 65)) :
    ‖Θ x N π - Θ x' N π‖ ≤ Nat.card N * (4 * M ^ 3 * η) := by
  classical
  unfold Θ mono
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n : N, ‖x ((π * n) 0) ^ 2 * x ((π * n) 1) * x ((π * n) 3) -
        x' ((π * n) 0) ^ 2 * x' ((π * n) 1) * x' ((π * n) 3)‖
      ≤ ∑ _n : N, 4 * M ^ 3 * η :=
        Finset.sum_le_sum fun n _ => norm_mono_sub_le (hx _) (hx _) (hx _) (hx' _) (hx' _) (hd _)
          (hd _) (hd _)
    _ = Nat.card N * (4 * M ^ 3 * η) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem norm_Θ_le {x : Fin 65 → ℂ} {M : ℝ} (hx : ∀ i, ‖x i‖ ≤ M)
    (N : Subgroup (Equiv.Perm (Fin 65))) (π : Equiv.Perm (Fin 65)) :
    ‖Θ x N π‖ ≤ Nat.card N * M ^ 4 := by
  classical
  unfold Θ mono
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n : N, ‖x ((π * n) 0) ^ 2 * x ((π * n) 1) * x ((π * n) 3)‖ ≤ ∑ _n : N, M ^ 4 :=
        Finset.sum_le_sum fun n _ => norm_mono_le (hx _) (hx _) (hx _)
    _ = Nat.card N * M ^ 4 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- The symmetric functions of three values. -/
def sym3 {A : Type*} [CommRing A] (u v w : A) : Fin 3 → A :=
  ![u + v + w, u * v + u * w + v * w, u * v * w]

/-- The error bounds for the three symmetric functions. -/
def symErr (T d : ℝ) : Fin 3 → ℝ := ![3 * d, 6 * T * d, 3 * T ^ 2 * d]

theorem norm_mul_sub_le {p q p' q' : ℂ} {T d : ℝ} (hp : ‖p‖ ≤ T) (hq' : ‖q'‖ ≤ T)
    (hdp : ‖p - p'‖ ≤ d) (hdq : ‖q - q'‖ ≤ d) : ‖p * q - p' * q'‖ ≤ 2 * T * d := by
  have hT : 0 ≤ T := (norm_nonneg _).trans hp
  have hd : 0 ≤ d := (norm_nonneg _).trans hdp
  have e : p * q - p' * q' = p * (q - q') + (p - p') * q' := by ring
  rw [e]
  calc _ ≤ ‖p * (q - q')‖ + ‖(p - p') * q'‖ := norm_add_le _ _
    _ ≤ T * d + d * T := by rw [norm_mul, norm_mul]; gcongr
    _ = 2 * T * d := by ring

theorem norm_sym3_sub_le {u v w u' v' w' : ℂ} {T d : ℝ} (hu : ‖u‖ ≤ T) (hv : ‖v‖ ≤ T)
    (hw : ‖w‖ ≤ T) (hu' : ‖u'‖ ≤ T) (hv' : ‖v'‖ ≤ T) (hw' : ‖w'‖ ≤ T) (hdu : ‖u - u'‖ ≤ d) (hdv : ‖v - v'‖ ≤ d)
    (hdw : ‖w - w'‖ ≤ d) (m : Fin 3) :
    ‖sym3 u v w m - sym3 u' v' w' m‖ ≤ symErr T d m := by
  have hT : 0 ≤ T := (norm_nonneg _).trans hu
  have hd : 0 ≤ d := (norm_nonneg _).trans hdu
  fin_cases m
  · show ‖(u + v + w) - (u' + v' + w')‖ ≤ 3 * d
    have e : u + v + w - (u' + v' + w') = (u - u') + (v - v') + (w - w') := by ring
    rw [e]
    calc _ ≤ ‖u - u'‖ + ‖v - v'‖ + ‖w - w'‖ := norm_add₃_le
      _ ≤ d + d + d := by gcongr
      _ = 3 * d := by ring
  · show ‖(u * v + u * w + v * w) - (u' * v' + u' * w' + v' * w')‖ ≤ 6 * T * d
    have e : u * v + u * w + v * w - (u' * v' + u' * w' + v' * w') =
        (u * v - u' * v') + (u * w - u' * w') + (v * w - v' * w') := by ring
    rw [e]
    calc _ ≤ ‖u * v - u' * v'‖ + ‖u * w - u' * w'‖ + ‖v * w - v' * w'‖ := norm_add₃_le
      _ ≤ 2 * T * d + 2 * T * d + 2 * T * d := by
        gcongr
        · exact norm_mul_sub_le hu hv' hdu hdv
        · exact norm_mul_sub_le hu hw' hdu hdw
        · exact norm_mul_sub_le hv hw' hdv hdw
      _ = 6 * T * d := by ring
  · show ‖u * v * w - u' * v' * w'‖ ≤ 3 * T ^ 2 * d
    have e : u * v * w - u' * v' * w' = (u * v - u' * v') * w + u' * v' * (w - w') := by ring
    rw [e]
    have huv : ‖u * v - u' * v'‖ ≤ 2 * T * d := norm_mul_sub_le hu hv' hdu hdv
    calc _ ≤ ‖(u * v - u' * v') * w‖ + ‖u' * v' * (w - w')‖ := norm_add_le _ _
      _ ≤ 2 * T * d * T + T * T * d := by
        rw [norm_mul, norm_mul, norm_mul]
        gcongr
      _ = 3 * T ^ 2 * d := by ring

end Sz8.Galois.Lipschitz
