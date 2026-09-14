import HexRootsMathlib.Rouche

open Complex Metric Polynomial Set

namespace Sz8.Monodromy

/-- A certified parameter step preserves the multiplicity-counted number of roots
in an isolating disc. The estimates are uniform over the whole parameter step. -/
theorem continuation_step
    (F : ℂ → Polynomial ℂ) (t₀ : ℂ) (parameters : Set ℂ)
    (c : ℂ) (R lower upper : ℝ)
    (hR : 0 ≤ R) (hgap : upper < lower)
    (hbase : ∀ z ∈ sphere c R, lower ≤ ‖(F t₀).eval z‖)
    (hchange : ∀ t ∈ parameters, ∀ z ∈ sphere c R,
      ‖(F t).eval z - (F t₀).eval z‖ ≤ upper) :
    ∀ t ∈ parameters,
      HexRootsMathlib.rootsInDisc (F t) c R =
        HexRootsMathlib.rootsInDisc (F t₀) c R := by
  intro t ht
  apply HexRootsMathlib.rouche hR
  intro z hz
  exact lt_of_le_of_lt (hchange t ht z hz) (lt_of_lt_of_le hgap (hbase z hz))

/-- In particular, a disc containing one root continues to contain one root,
counted with multiplicity, at every parameter covered by the certificate. -/
theorem continuation_step_one
    (F : ℂ → Polynomial ℂ) (t₀ : ℂ) (parameters : Set ℂ)
    (c : ℂ) (R lower upper : ℝ)
    (hR : 0 ≤ R) (hgap : upper < lower)
    (hbase : ∀ z ∈ sphere c R, lower ≤ ‖(F t₀).eval z‖)
    (hchange : ∀ t ∈ parameters, ∀ z ∈ sphere c R,
      ‖(F t).eval z - (F t₀).eval z‖ ≤ upper)
    (hone : HexRootsMathlib.rootsInDisc (F t₀) c R = 1) :
    ∀ t ∈ parameters, HexRootsMathlib.rootsInDisc (F t) c R = 1 := by
  intro t ht
  rw [continuation_step F t₀ parameters c R lower upper hR hgap hbase hchange t ht]
  exact hone

end Sz8.Monodromy
