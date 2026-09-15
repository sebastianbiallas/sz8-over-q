import Sz8.Monodromy.RootCovering
import Mathlib.Topology.Homotopy.Lifting

/-!
Certified transport of roots along paths of regular parameters.

`monodromy_root_mem_ball` is the bridge from numerical certificates to Mathlib's
covering-space monodromy. If no root of `P t` lies on a circle `|x - c| = R` for any `t`
on the path, the lift starting inside the disc ends inside it (intermediate value
theorem along the lift). No continuous root selection is needed: the covering supplies
the lift, and the certificate only confines it. `monodromy_eq_of_ball` adds endpoint
uniqueness, and `monodromy_trans` composes certified paths.
-/

namespace Sz8.Monodromy.MonicFamily

open Polynomial Topology Set Metric

variable (M : MonicFamily)

/-- The covering over the regular parameters, in Mathlib's sense. -/
theorem isCoveringMap : IsCoveringMap (M.regular.restrictPreimage M.proj) :=
  M.isCoveringMapOn_proj.isCoveringMap_restrictPreimage

/-- Regular parameters. -/
abbrev Base : Type := M.regular

/-- The fibre over a regular parameter. -/
abbrev Fiber (t : M.Base) : Type := (M.regular.restrictPreimage M.proj) ⁻¹' {t}

variable {M}

/-- The root represented by a fibre point. -/
def Fiber.root {t : M.Base} (e : M.Fiber t) : ℂ := e.1.1.1.2

theorem Fiber.param {t : M.Base} (e : M.Fiber t) : e.1.1.1.1 = t.1 :=
  congrArg Subtype.val e.2

theorem Fiber.isRoot {t : M.Base} (e : M.Fiber t) : (M.P t.1).eval e.root = 0 := by
  have h := e.1.1.2
  rw [← e.param]
  exact h

theorem Fiber.ext {t : M.Base} {e e' : M.Fiber t} (h : e.root = e'.root) : e = e' := by
  obtain ⟨⟨⟨⟨t₁, x₁⟩, h₁⟩, r₁⟩, p₁⟩ := e
  obtain ⟨⟨⟨⟨t₂, x₂⟩, h₂⟩, r₂⟩, p₂⟩ := e'
  have e₁ : t₁ = t.1 := congrArg Subtype.val p₁
  have e₂ : t₂ = t.1 := congrArg Subtype.val p₂
  simp only [Fiber.root] at h
  subst e₁ e₂ h
  rfl

variable (M) in
/-- The fibre point over `t` given by a root `x` of `P t`. -/
def mkFiber (t : M.Base) (x : ℂ) (hx : (M.P t.1).eval x = 0) : M.Fiber t :=
  ⟨⟨⟨(t.1, x), hx⟩, t.2⟩, rfl⟩

@[simp] theorem mkFiber_root (t : M.Base) (x : ℂ) (hx) : (M.mkFiber t x hx).root = x := rfl

/-- **Certified transport.** Along a path of regular parameters, if no root of `P t` lies
on the circle `|x - c| = R`, then the lift of the path starting at a root inside the disc
ends at a root inside the disc. The covering supplies the lift; the certificate only
confines it. -/
theorem monodromy_root_mem_ball {a b : M.Base} (γ : Path a b) (e : M.Fiber a)
    {c : ℂ} {R : ℝ} (hsphere : ∀ u, ∀ x ∈ sphere c R, (M.P (γ u).1).eval x ≠ 0)
    (hstart : e.root ∈ ball c R) :
    Fiber.root (t := b) (M.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) e) ∈ ball c R := by
  have hγ0 : γ.toContinuousMap 0 = M.regular.restrictPreimage M.proj e.1 := by
    simpa using e.2.symm
  set Γ := M.isCoveringMap.liftPath γ.toContinuousMap e.1 hγ0 with hΓ
  have hlift := M.isCoveringMap.liftPath_lifts γ.toContinuousMap e.1 hγ0
  have hzero := M.isCoveringMap.liftPath_zero γ.toContinuousMap e.1 hγ0
  have hend : Fiber.root (t := b) (M.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) e) =
      (Γ 1).1.1.2 := rfl
  rw [hend]
  let ρ : unitInterval → ℂ := fun u => (Γ u).1.1.2
  have hρ : Continuous ρ :=
    continuous_snd.comp (continuous_subtype_val.comp (continuous_subtype_val.comp Γ.continuous))
  have hparam : ∀ u, (Γ u).1.1.1 = (γ u).1 := fun u =>
    congrArg Subtype.val (congrFun hlift u)
  have hroot : ∀ u, (M.P (γ u).1).eval (ρ u) = 0 := fun u => by
    have h := (Γ u).1.2
    rw [← hparam u]
    exact h
  by_contra hout
  have h0 : dist (ρ 0) c < R := by
    show dist (Γ 0).1.1.2 c < R
    rw [hzero]
    exact mem_ball.mp hstart
  have h1 : R ≤ dist (ρ 1) c := not_lt.mp hout
  obtain ⟨u, hu⟩ := intermediate_value_univ 0 1 (hρ.dist continuous_const) ⟨h0.le, h1⟩
  exact hsphere u (ρ u) (mem_sphere.mpr hu) (hroot u)

end Sz8.Monodromy.MonicFamily

namespace Sz8.Monodromy.MonicFamily

open Polynomial Topology Set Metric

/-- The straight segment from `a` to `b` in `ℂ`. -/
noncomputable def segment (a b : ℂ) : Path a b where
  toFun u := a + ((u : ℝ) : ℂ) * (b - a)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

variable {M : MonicFamily}

/-- A path of complex parameters avoiding the non-regular set, as a path in the base. -/
noncomputable def basePath {a b : M.Base} (γ : Path a.1 b.1) (h : ∀ u, γ u ∈ M.regular) : Path a b where
  toFun u := ⟨γ u, h u⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

@[simp] theorem basePath_apply {a b : M.Base} (γ : Path a.1 b.1) (h) (u : unitInterval) :
    (basePath γ h u).1 = γ u := rfl

omit M in
@[simp] theorem segment_apply (a b : ℂ) (u : unitInterval) :
    segment a b u = a + ((u : ℝ) : ℂ) * (b - a) := rfl

/-- Composition of certified paths: the monodromy of a concatenation is the composite. -/
theorem monodromy_trans {a b c : M.Base} (γ : Path a b) (γ' : Path b c) (e : M.Fiber a) :
    M.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (γ.trans γ')) e =
      M.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ')
        (M.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) e) := by
  rw [Path.Homotopic.Quotient.mk_trans, IsCoveringMap.monodromy_trans_apply]

/-- A disc certificate identifies the endpoint: if the transported root stays in a disc
that contains exactly the root `e'` at the endpoint, the monodromy sends `e` to `e'`. -/
theorem monodromy_eq_of_ball {a b : M.Base} (γ : Path a b) (e : M.Fiber a) (e' : M.Fiber b)
    {c : ℂ} {R : ℝ} (hsphere : ∀ u, ∀ x ∈ sphere c R, (M.P (γ u).1).eval x ≠ 0)
    (hstart : e.root ∈ ball c R)
    (huniq : ∀ x, (M.P b.1).eval x = 0 → x ∈ ball c R → x = e'.root) :
    M.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) e = e' := by
  have hmem := monodromy_root_mem_ball γ e hsphere hstart
  exact Fiber.ext (huniq _ (Fiber.isRoot _) hmem)

end Sz8.Monodromy.MonicFamily

