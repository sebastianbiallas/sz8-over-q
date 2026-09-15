import Sz8.Galois.ResDegree
import Sz8.Galois.ResEvals.B00
import Sz8.Galois.ResEvals.B01
import Sz8.Galois.ResEvals.B02
import Sz8.Galois.ResEvals.B03
import Sz8.Galois.ResEvals.B04
import Sz8.Galois.ResEvals.B05
import Sz8.Galois.ResEvals.B06
import Sz8.Galois.ResEvals.B07
import Sz8.Galois.ResEvals.B08
import Sz8.Galois.ResEvals.B09
import Sz8.Galois.ResEvals.B10
import Sz8.Galois.ResEvals.B11
import Sz8.Galois.ResEvals.B12
import Sz8.Galois.ResEvals.B13
import Sz8.Galois.ResEvals.B14
import Sz8.Galois.ResEvals.B15
import Sz8.Galois.Nodes

/-!
# The resultant identity, unconditionally

The 813 kernel evaluations of `Sz8.Galois.ResEvals.B00`–`B15` (points `t = k - 406`, `k < 813`),
with `ResEval.resultant_P_identity` (degree bound 812, interpolation, algorithm correctness):

    Res_X(f(·, t), f_X(·, t)) = c̃ · (t² + t + 1)^40 · S̃(t)²   for every complex `t`.
-/

namespace Sz8.Galois.ResEval

theorem all_evals : ∀ k : ℕ, k < 813 → evalOK ((k : ℚ) - 406) = true := by
  intro k hk
  by_cases h0 : k < 51
  · exact batch_0 k (by omega) h0
  by_cases h1 : k < 102
  · exact batch_1 k (by omega) h1
  by_cases h2 : k < 153
  · exact batch_2 k (by omega) h2
  by_cases h3 : k < 204
  · exact batch_3 k (by omega) h3
  by_cases h4 : k < 255
  · exact batch_4 k (by omega) h4
  by_cases h5 : k < 306
  · exact batch_5 k (by omega) h5
  by_cases h6 : k < 357
  · exact batch_6 k (by omega) h6
  by_cases h7 : k < 408
  · exact batch_7 k (by omega) h7
  by_cases h8 : k < 459
  · exact batch_8 k (by omega) h8
  by_cases h9 : k < 510
  · exact batch_9 k (by omega) h9
  by_cases h10 : k < 561
  · exact batch_10 k (by omega) h10
  by_cases h11 : k < 612
  · exact batch_11 k (by omega) h11
  by_cases h12 : k < 663
  · exact batch_12 k (by omega) h12
  by_cases h13 : k < 714
  · exact batch_13 k (by omega) h13
  by_cases h14 : k < 765
  · exact batch_14 k (by omega) h14
  exact batch_15 k (by omega) hk

/-- **The resultant identity.** -/
theorem identity : Nodes.Identity := resultant_P_identity all_evals

end Sz8.Galois.ResEval
