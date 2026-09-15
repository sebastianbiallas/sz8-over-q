import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `51 ≤ k < 102`. -/

namespace Sz8.Galois.ResEval

theorem ok_51 : evalOK ((((51 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_52 : evalOK ((((52 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_53 : evalOK ((((53 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_54 : evalOK ((((54 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_55 : evalOK ((((55 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_56 : evalOK ((((56 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_57 : evalOK ((((57 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_58 : evalOK ((((58 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_59 : evalOK ((((59 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_60 : evalOK ((((60 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_61 : evalOK ((((61 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_62 : evalOK ((((62 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_63 : evalOK ((((63 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_64 : evalOK ((((64 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_65 : evalOK ((((65 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_66 : evalOK ((((66 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_67 : evalOK ((((67 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_68 : evalOK ((((68 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_69 : evalOK ((((69 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_70 : evalOK ((((70 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_71 : evalOK ((((71 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_72 : evalOK ((((72 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_73 : evalOK ((((73 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_74 : evalOK ((((74 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_75 : evalOK ((((75 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_76 : evalOK ((((76 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_77 : evalOK ((((77 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_78 : evalOK ((((78 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_79 : evalOK ((((79 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_80 : evalOK ((((80 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_81 : evalOK ((((81 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_82 : evalOK ((((82 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_83 : evalOK ((((83 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_84 : evalOK ((((84 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_85 : evalOK ((((85 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_86 : evalOK ((((86 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_87 : evalOK ((((87 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_88 : evalOK ((((88 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_89 : evalOK ((((89 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_90 : evalOK ((((90 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_91 : evalOK ((((91 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_92 : evalOK ((((92 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_93 : evalOK ((((93 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_94 : evalOK ((((94 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_95 : evalOK ((((95 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_96 : evalOK ((((96 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_97 : evalOK ((((97 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_98 : evalOK ((((98 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_99 : evalOK ((((99 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_100 : evalOK ((((100 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_101 : evalOK ((((101 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_1 : ∀ k : ℕ, 51 ≤ k → k < 102 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_51, ok_52, ok_53, ok_54, ok_55, ok_56, ok_57, ok_58, ok_59, ok_60, ok_61, ok_62, ok_63, ok_64, ok_65, ok_66, ok_67, ok_68, ok_69, ok_70, ok_71, ok_72, ok_73, ok_74, ok_75, ok_76, ok_77, ok_78, ok_79, ok_80, ok_81, ok_82, ok_83, ok_84, ok_85, ok_86, ok_87, ok_88, ok_89, ok_90, ok_91, ok_92, ok_93, ok_94, ok_95, ok_96, ok_97, ok_98, ok_99, ok_100, ok_101]

end Sz8.Galois.ResEval
