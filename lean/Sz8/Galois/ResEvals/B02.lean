import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `102 ≤ k < 153`. -/

namespace Sz8.Galois.ResEval

theorem ok_102 : evalOK ((((102 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_103 : evalOK ((((103 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_104 : evalOK ((((104 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_105 : evalOK ((((105 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_106 : evalOK ((((106 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_107 : evalOK ((((107 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_108 : evalOK ((((108 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_109 : evalOK ((((109 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_110 : evalOK ((((110 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_111 : evalOK ((((111 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_112 : evalOK ((((112 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_113 : evalOK ((((113 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_114 : evalOK ((((114 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_115 : evalOK ((((115 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_116 : evalOK ((((116 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_117 : evalOK ((((117 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_118 : evalOK ((((118 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_119 : evalOK ((((119 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_120 : evalOK ((((120 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_121 : evalOK ((((121 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_122 : evalOK ((((122 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_123 : evalOK ((((123 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_124 : evalOK ((((124 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_125 : evalOK ((((125 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_126 : evalOK ((((126 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_127 : evalOK ((((127 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_128 : evalOK ((((128 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_129 : evalOK ((((129 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_130 : evalOK ((((130 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_131 : evalOK ((((131 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_132 : evalOK ((((132 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_133 : evalOK ((((133 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_134 : evalOK ((((134 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_135 : evalOK ((((135 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_136 : evalOK ((((136 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_137 : evalOK ((((137 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_138 : evalOK ((((138 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_139 : evalOK ((((139 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_140 : evalOK ((((140 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_141 : evalOK ((((141 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_142 : evalOK ((((142 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_143 : evalOK ((((143 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_144 : evalOK ((((144 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_145 : evalOK ((((145 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_146 : evalOK ((((146 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_147 : evalOK ((((147 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_148 : evalOK ((((148 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_149 : evalOK ((((149 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_150 : evalOK ((((150 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_151 : evalOK ((((151 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_152 : evalOK ((((152 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_2 : ∀ k : ℕ, 102 ≤ k → k < 153 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_102, ok_103, ok_104, ok_105, ok_106, ok_107, ok_108, ok_109, ok_110, ok_111, ok_112, ok_113, ok_114, ok_115, ok_116, ok_117, ok_118, ok_119, ok_120, ok_121, ok_122, ok_123, ok_124, ok_125, ok_126, ok_127, ok_128, ok_129, ok_130, ok_131, ok_132, ok_133, ok_134, ok_135, ok_136, ok_137, ok_138, ok_139, ok_140, ok_141, ok_142, ok_143, ok_144, ok_145, ok_146, ok_147, ok_148, ok_149, ok_150, ok_151, ok_152]

end Sz8.Galois.ResEval
