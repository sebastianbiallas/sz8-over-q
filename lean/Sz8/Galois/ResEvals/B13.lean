import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `663 ≤ k < 714`. -/

namespace Sz8.Galois.ResEval

theorem ok_663 : evalOK ((((663 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_664 : evalOK ((((664 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_665 : evalOK ((((665 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_666 : evalOK ((((666 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_667 : evalOK ((((667 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_668 : evalOK ((((668 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_669 : evalOK ((((669 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_670 : evalOK ((((670 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_671 : evalOK ((((671 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_672 : evalOK ((((672 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_673 : evalOK ((((673 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_674 : evalOK ((((674 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_675 : evalOK ((((675 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_676 : evalOK ((((676 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_677 : evalOK ((((677 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_678 : evalOK ((((678 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_679 : evalOK ((((679 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_680 : evalOK ((((680 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_681 : evalOK ((((681 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_682 : evalOK ((((682 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_683 : evalOK ((((683 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_684 : evalOK ((((684 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_685 : evalOK ((((685 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_686 : evalOK ((((686 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_687 : evalOK ((((687 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_688 : evalOK ((((688 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_689 : evalOK ((((689 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_690 : evalOK ((((690 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_691 : evalOK ((((691 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_692 : evalOK ((((692 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_693 : evalOK ((((693 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_694 : evalOK ((((694 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_695 : evalOK ((((695 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_696 : evalOK ((((696 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_697 : evalOK ((((697 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_698 : evalOK ((((698 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_699 : evalOK ((((699 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_700 : evalOK ((((700 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_701 : evalOK ((((701 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_702 : evalOK ((((702 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_703 : evalOK ((((703 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_704 : evalOK ((((704 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_705 : evalOK ((((705 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_706 : evalOK ((((706 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_707 : evalOK ((((707 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_708 : evalOK ((((708 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_709 : evalOK ((((709 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_710 : evalOK ((((710 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_711 : evalOK ((((711 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_712 : evalOK ((((712 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_713 : evalOK ((((713 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_13 : ∀ k : ℕ, 663 ≤ k → k < 714 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_663, ok_664, ok_665, ok_666, ok_667, ok_668, ok_669, ok_670, ok_671, ok_672, ok_673, ok_674, ok_675, ok_676, ok_677, ok_678, ok_679, ok_680, ok_681, ok_682, ok_683, ok_684, ok_685, ok_686, ok_687, ok_688, ok_689, ok_690, ok_691, ok_692, ok_693, ok_694, ok_695, ok_696, ok_697, ok_698, ok_699, ok_700, ok_701, ok_702, ok_703, ok_704, ok_705, ok_706, ok_707, ok_708, ok_709, ok_710, ok_711, ok_712, ok_713]

end Sz8.Galois.ResEval
