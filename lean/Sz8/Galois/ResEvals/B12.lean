import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `612 ≤ k < 663`. -/

namespace Sz8.Galois.ResEval

theorem ok_612 : evalOK ((((612 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_613 : evalOK ((((613 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_614 : evalOK ((((614 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_615 : evalOK ((((615 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_616 : evalOK ((((616 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_617 : evalOK ((((617 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_618 : evalOK ((((618 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_619 : evalOK ((((619 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_620 : evalOK ((((620 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_621 : evalOK ((((621 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_622 : evalOK ((((622 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_623 : evalOK ((((623 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_624 : evalOK ((((624 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_625 : evalOK ((((625 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_626 : evalOK ((((626 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_627 : evalOK ((((627 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_628 : evalOK ((((628 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_629 : evalOK ((((629 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_630 : evalOK ((((630 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_631 : evalOK ((((631 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_632 : evalOK ((((632 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_633 : evalOK ((((633 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_634 : evalOK ((((634 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_635 : evalOK ((((635 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_636 : evalOK ((((636 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_637 : evalOK ((((637 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_638 : evalOK ((((638 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_639 : evalOK ((((639 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_640 : evalOK ((((640 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_641 : evalOK ((((641 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_642 : evalOK ((((642 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_643 : evalOK ((((643 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_644 : evalOK ((((644 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_645 : evalOK ((((645 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_646 : evalOK ((((646 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_647 : evalOK ((((647 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_648 : evalOK ((((648 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_649 : evalOK ((((649 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_650 : evalOK ((((650 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_651 : evalOK ((((651 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_652 : evalOK ((((652 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_653 : evalOK ((((653 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_654 : evalOK ((((654 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_655 : evalOK ((((655 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_656 : evalOK ((((656 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_657 : evalOK ((((657 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_658 : evalOK ((((658 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_659 : evalOK ((((659 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_660 : evalOK ((((660 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_661 : evalOK ((((661 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_662 : evalOK ((((662 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_12 : ∀ k : ℕ, 612 ≤ k → k < 663 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_612, ok_613, ok_614, ok_615, ok_616, ok_617, ok_618, ok_619, ok_620, ok_621, ok_622, ok_623, ok_624, ok_625, ok_626, ok_627, ok_628, ok_629, ok_630, ok_631, ok_632, ok_633, ok_634, ok_635, ok_636, ok_637, ok_638, ok_639, ok_640, ok_641, ok_642, ok_643, ok_644, ok_645, ok_646, ok_647, ok_648, ok_649, ok_650, ok_651, ok_652, ok_653, ok_654, ok_655, ok_656, ok_657, ok_658, ok_659, ok_660, ok_661, ok_662]

end Sz8.Galois.ResEval
