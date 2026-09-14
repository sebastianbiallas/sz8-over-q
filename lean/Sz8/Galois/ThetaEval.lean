import Sz8.Galois.NSum
import Sz8.Galois.Enclose
import Sz8.Galois.Lipschitz

/-!
# Exact evaluation of the grouped invariant over the Gaussian integers

`thetaGI y π = Σ_a y(π t₀(0))² Σ_b y(π t₀t₁(1)) Σ_c y(π t₀t₁t₂(3))` computed on Gaussian integers, with
`t₀ = Ntv0[a]`, `t₁ = Ntv1[b]`, `t₂ = Ntv2[c]`; `thetaA` is the summand for one `a`, so the kernel
check can be split. `gc_thetaGI`: its value is the grouped complex sum of MainTheorem's `Θ_eq_grouped`.
-/

namespace Sz8.Galois.ThetaEval

open Sz8.Monodromy Sz8.Monodromy.GaussPoly

/-- Sum over `Fin n`. -/
def gsum {n : ℕ} (f : Fin n → GI) : GI := ((List.finRange n).map f).foldr gadd (0, 0)

theorem gc_foldr (l : List GI) : gc (l.foldr gadd (0, 0)) = (l.map gc).sum := by
  induction l with
  | nil => simp [gc]
  | cons a l ih => simp [gc_add, ih]

theorem gc_gsum {n : ℕ} (f : Fin n → GI) : gc (gsum f) = ∑ i, gc (f i) := by
  rw [gsum, gc_foldr, Fin.sum_univ_def, List.map_map]; rfl

/-- The summand for one first transversal. -/
def thetaA (y : Fin 65 → GI) (π : Fin 65 → Fin 65) (a : Fin 65) : GI :=
  gmul (gmul (y (π (Ntv0.getD a 1 0))) (y (π (Ntv0.getD a 1 0))))
    (gsum fun b : Fin 64 => gmul (y (π (Ntv0.getD a 1 (Ntv1.getD b 1 1))))
      (gsum fun c : Fin 7 => y (π (Ntv0.getD a 1 (Ntv1.getD b 1 (Ntv2.getD c 1 3))))))

/-- The grouped invariant. -/
def thetaGI (y : Fin 65 → GI) (π : Fin 65 → Fin 65) : GI := gsum (thetaA y π)

theorem gc_thetaGI (y : Fin 65 → GI) (π : Fin 65 → Fin 65) :
    gc (thetaGI y π) = ∑ a : Fin 65, gc (y (π (Ntv0.getD a 1 0))) ^ 2 *
      ∑ b : Fin 64, gc (y (π (Ntv0.getD a 1 (Ntv1.getD b 1 1)))) *
        ∑ c : Fin 7, gc (y (π (Ntv0.getD a 1 (Ntv1.getD b 1 (Ntv2.getD c 1 3))))) := by
  simp only [thetaGI, gc_gsum, thetaA, gc_mul, pow_two]

end Sz8.Galois.ThetaEval
