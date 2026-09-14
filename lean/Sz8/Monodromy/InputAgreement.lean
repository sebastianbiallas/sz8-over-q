import Sz8.Monodromy.Inputs
import Sz8.Monodromy.StepData

namespace Sz8.Monodromy

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- Re-encode the continuation input as the same sparse rational terms used
by the modular input, in ascending (X degree, t degree) order. -/
def columnTerms : List (Nat × Nat × ℚ) :=
  (List.range 66).flatMap fun i =>
    (List.range 8).filterMap fun j =>
      let a := (originalColumns.getD j []).getD i 0
      if a = 0 then none else some (i, j, a)

theorem column_dimensions : originalColumns.length = 8 ∧
    originalColumns.all (fun cs => cs.length ≤ 66) = true := by decide +kernel

/-- Exact agreement of all rational coefficients, not just file hashes.
Together with column_dimensions, no continuation coefficients are omitted. -/
theorem inputs_agree : columnTerms =
    inputTerms.map (fun a => (a.1, a.2.1, (a.2.2.1 : ℚ) / a.2.2.2)) := by
  decide +kernel

end Sz8.Monodromy
