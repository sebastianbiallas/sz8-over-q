import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `0 ≤ k < 51`. -/

namespace Sz8.Galois.ResEval

theorem ok_0 : evalOK ((((0 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_1 : evalOK ((((1 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_2 : evalOK ((((2 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_3 : evalOK ((((3 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_4 : evalOK ((((4 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_5 : evalOK ((((5 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_6 : evalOK ((((6 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_7 : evalOK ((((7 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_8 : evalOK ((((8 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_9 : evalOK ((((9 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_10 : evalOK ((((10 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_11 : evalOK ((((11 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_12 : evalOK ((((12 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_13 : evalOK ((((13 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_14 : evalOK ((((14 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_15 : evalOK ((((15 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_16 : evalOK ((((16 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_17 : evalOK ((((17 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_18 : evalOK ((((18 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_19 : evalOK ((((19 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_20 : evalOK ((((20 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_21 : evalOK ((((21 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_22 : evalOK ((((22 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_23 : evalOK ((((23 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_24 : evalOK ((((24 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_25 : evalOK ((((25 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_26 : evalOK ((((26 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_27 : evalOK ((((27 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_28 : evalOK ((((28 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_29 : evalOK ((((29 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_30 : evalOK ((((30 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_31 : evalOK ((((31 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_32 : evalOK ((((32 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_33 : evalOK ((((33 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_34 : evalOK ((((34 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_35 : evalOK ((((35 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_36 : evalOK ((((36 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_37 : evalOK ((((37 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_38 : evalOK ((((38 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_39 : evalOK ((((39 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_40 : evalOK ((((40 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_41 : evalOK ((((41 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_42 : evalOK ((((42 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_43 : evalOK ((((43 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_44 : evalOK ((((44 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_45 : evalOK ((((45 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_46 : evalOK ((((46 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_47 : evalOK ((((47 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_48 : evalOK ((((48 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_49 : evalOK ((((49 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_50 : evalOK ((((50 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_0 : ∀ k : ℕ, 0 ≤ k → k < 51 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_0, ok_1, ok_2, ok_3, ok_4, ok_5, ok_6, ok_7, ok_8, ok_9, ok_10, ok_11, ok_12, ok_13, ok_14, ok_15, ok_16, ok_17, ok_18, ok_19, ok_20, ok_21, ok_22, ok_23, ok_24, ok_25, ok_26, ok_27, ok_28, ok_29, ok_30, ok_31, ok_32, ok_33, ok_34, ok_35, ok_36, ok_37, ok_38, ok_39, ok_40, ok_41, ok_42, ok_43, ok_44, ok_45, ok_46, ok_47, ok_48, ok_49, ok_50]

end Sz8.Galois.ResEval
