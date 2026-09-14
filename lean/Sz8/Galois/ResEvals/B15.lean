import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `765 ≤ k < 813`. -/

namespace Sz8.Galois.ResEval

theorem ok_765 : evalOK ((((765 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_766 : evalOK ((((766 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_767 : evalOK ((((767 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_768 : evalOK ((((768 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_769 : evalOK ((((769 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_770 : evalOK ((((770 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_771 : evalOK ((((771 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_772 : evalOK ((((772 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_773 : evalOK ((((773 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_774 : evalOK ((((774 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_775 : evalOK ((((775 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_776 : evalOK ((((776 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_777 : evalOK ((((777 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_778 : evalOK ((((778 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_779 : evalOK ((((779 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_780 : evalOK ((((780 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_781 : evalOK ((((781 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_782 : evalOK ((((782 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_783 : evalOK ((((783 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_784 : evalOK ((((784 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_785 : evalOK ((((785 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_786 : evalOK ((((786 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_787 : evalOK ((((787 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_788 : evalOK ((((788 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_789 : evalOK ((((789 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_790 : evalOK ((((790 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_791 : evalOK ((((791 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_792 : evalOK ((((792 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_793 : evalOK ((((793 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_794 : evalOK ((((794 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_795 : evalOK ((((795 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_796 : evalOK ((((796 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_797 : evalOK ((((797 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_798 : evalOK ((((798 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_799 : evalOK ((((799 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_800 : evalOK ((((800 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_801 : evalOK ((((801 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_802 : evalOK ((((802 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_803 : evalOK ((((803 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_804 : evalOK ((((804 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_805 : evalOK ((((805 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_806 : evalOK ((((806 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_807 : evalOK ((((807 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_808 : evalOK ((((808 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_809 : evalOK ((((809 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_810 : evalOK ((((810 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_811 : evalOK ((((811 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_812 : evalOK ((((812 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_15 : ∀ k : ℕ, 765 ≤ k → k < 813 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_765, ok_766, ok_767, ok_768, ok_769, ok_770, ok_771, ok_772, ok_773, ok_774, ok_775, ok_776, ok_777, ok_778, ok_779, ok_780, ok_781, ok_782, ok_783, ok_784, ok_785, ok_786, ok_787, ok_788, ok_789, ok_790, ok_791, ok_792, ok_793, ok_794, ok_795, ok_796, ok_797, ok_798, ok_799, ok_800, ok_801, ok_802, ok_803, ok_804, ok_805, ok_806, ok_807, ok_808, ok_809, ok_810, ok_811, ok_812]

end Sz8.Galois.ResEval
