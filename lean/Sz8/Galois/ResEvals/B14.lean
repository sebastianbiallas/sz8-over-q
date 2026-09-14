import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `714 ≤ k < 765`. -/

namespace Sz8.Galois.ResEval

theorem ok_714 : evalOK ((((714 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_715 : evalOK ((((715 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_716 : evalOK ((((716 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_717 : evalOK ((((717 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_718 : evalOK ((((718 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_719 : evalOK ((((719 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_720 : evalOK ((((720 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_721 : evalOK ((((721 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_722 : evalOK ((((722 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_723 : evalOK ((((723 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_724 : evalOK ((((724 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_725 : evalOK ((((725 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_726 : evalOK ((((726 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_727 : evalOK ((((727 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_728 : evalOK ((((728 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_729 : evalOK ((((729 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_730 : evalOK ((((730 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_731 : evalOK ((((731 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_732 : evalOK ((((732 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_733 : evalOK ((((733 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_734 : evalOK ((((734 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_735 : evalOK ((((735 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_736 : evalOK ((((736 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_737 : evalOK ((((737 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_738 : evalOK ((((738 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_739 : evalOK ((((739 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_740 : evalOK ((((740 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_741 : evalOK ((((741 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_742 : evalOK ((((742 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_743 : evalOK ((((743 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_744 : evalOK ((((744 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_745 : evalOK ((((745 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_746 : evalOK ((((746 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_747 : evalOK ((((747 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_748 : evalOK ((((748 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_749 : evalOK ((((749 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_750 : evalOK ((((750 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_751 : evalOK ((((751 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_752 : evalOK ((((752 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_753 : evalOK ((((753 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_754 : evalOK ((((754 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_755 : evalOK ((((755 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_756 : evalOK ((((756 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_757 : evalOK ((((757 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_758 : evalOK ((((758 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_759 : evalOK ((((759 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_760 : evalOK ((((760 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_761 : evalOK ((((761 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_762 : evalOK ((((762 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_763 : evalOK ((((763 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_764 : evalOK ((((764 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_14 : ∀ k : ℕ, 714 ≤ k → k < 765 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_714, ok_715, ok_716, ok_717, ok_718, ok_719, ok_720, ok_721, ok_722, ok_723, ok_724, ok_725, ok_726, ok_727, ok_728, ok_729, ok_730, ok_731, ok_732, ok_733, ok_734, ok_735, ok_736, ok_737, ok_738, ok_739, ok_740, ok_741, ok_742, ok_743, ok_744, ok_745, ok_746, ok_747, ok_748, ok_749, ok_750, ok_751, ok_752, ok_753, ok_754, ok_755, ok_756, ok_757, ok_758, ok_759, ok_760, ok_761, ok_762, ok_763, ok_764]

end Sz8.Galois.ResEval
