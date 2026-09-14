import Sz8.Galois.Germs
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# From relations among root germs to relations among root branches

`eventually_eval_eq_zero`: if a polynomial `P` in the root germs at `b`, with coefficients in `ℚ[t]`
(read as polynomial germs), vanishes in the field of meromorphic germs, then the same polynomial in the
root branches, with coefficients evaluated at `t`, vanishes for all `t` near `b`.
-/

open Polynomial Topology Filter

namespace Sz8.Galois.GermEval

open Sz8.Monodromy Sz8.Monodromy.MonicFamily Germs

variable (M : MonicFamily) (b : M.Base) {ι : Type*} (x : ι → M.Fiber b)

/-- `ℚ[t] → ℂ[t]`. -/
noncomputable abbrev κ : ℚ[X] →+* ℂ[X] := mapRingHom (algebraMap ℚ ℂ)

/-- Evaluation of `ℚ[t]` at `t`. -/
noncomputable abbrev evalAt (t : ℂ) : ℚ[X] →+* ℂ := eval₂RingHom (algebraMap ℚ ℂ) t

theorem eventually_eval_eq_zero (P : MvPolynomial ι ℚ[X])
    (hP : MvPolynomial.eval₂ ((algebraMap (anGerm b.1) (Mer b.1)).comp ((polyGerm b.1).comp κ))
      (fun i => rootGerm M b (x i)) P = 0) :
    ∀ᶠ t in 𝓝 b.1, MvPolynomial.eval₂ (evalAt t) (fun i => rootFun M b (x i) t) P = 0 := by
  -- the relation already holds among analytic germs
  set A := MvPolynomial.eval₂ ((polyGerm b.1).comp κ) (fun i => rootAn M b (x i)) P with hA
  have hA0 : A = 0 := by
    apply IsFractionRing.injective (anGerm b.1) (Mer b.1)
    rw [map_zero, hA, MvPolynomial.hom_eval₂]
    exact hP
  -- and among functions near `b`
  let polyFun : ℚ[X] →+* (ℂ → ℂ) := RingHom.pi fun t => evalAt t
  let F : ℂ → ℂ := MvPolynomial.eval₂ polyFun (fun i => rootFun M b (x i)) P
  have hcoef : (anGerm b.1).subtype.comp ((polyGerm b.1).comp κ) =
      (Germ.coeRingHom (𝓝 b.1)).comp polyFun := by
    refine RingHom.ext fun Q => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Subring.coe_subtype, polyGerm, anMk,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Germ.coeRingHom, polyFun]
    congr 1
    funext t
    simp [evalAt, eval_map]
  have hgerm : ((A : Germ (𝓝 b.1) ℂ)) = (F : Germ (𝓝 b.1) ℂ) := by
    change (anGerm b.1).subtype A = Germ.coeRingHom (𝓝 b.1) F
    rw [hA, MvPolynomial.hom_eval₂, hcoef, MvPolynomial.hom_eval₂]
    rfl
  rw [hA0] at hgerm
  have hF : F =ᶠ[𝓝 b.1] 0 := (Germ.coe_eq.1 hgerm.symm)
  filter_upwards [hF] with t ht
  change F t = 0 at ht
  rw [← ht]
  have h := MvPolynomial.hom_eval₂ P polyFun (Pi.evalRingHom (fun _ : ℂ => ℂ) t)
    (fun i => rootFun M b (x i))
  change _ = Pi.evalRingHom (fun _ : ℂ => ℂ) t F
  rw [h]
  rfl

/-- A polynomial with `ℚ[t]` coefficients in analytic functions is analytic. -/
theorem analyticAt_eval₂ {κι : Type*} (w : κι → ℂ → ℂ) {s : ℂ} (hw : ∀ i, AnalyticAt ℂ (w i) s)
    (P : MvPolynomial κι ℚ[X]) :
    AnalyticAt ℂ (fun s => MvPolynomial.eval₂ (evalAt s) (fun i => w i s) P) s := by
  induction P using MvPolynomial.induction_on with
  | C Q =>
    simp only [MvPolynomial.eval₂_C, evalAt, coe_eval₂RingHom]
    have : (fun s => Q.eval₂ (algebraMap ℚ ℂ) s) = fun s => (Q.map (algebraMap ℚ ℂ)).eval s :=
      funext fun s => (eval_map _ _).symm
    rw [this]; exact (Q.map (algebraMap ℚ ℂ)).differentiable.analyticAt s
  | add p q hp hq =>
    simp only [MvPolynomial.eval₂_add]
    exact hp.add hq
  | mul_X p n hp =>
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact hp.mul (hw n)

end Sz8.Galois.GermEval
