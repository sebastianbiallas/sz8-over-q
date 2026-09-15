import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `153 ≤ k < 204`. -/

namespace Sz8.Galois.ResEval

theorem ok_153 : evalOK ((((153 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_154 : evalOK ((((154 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_155 : evalOK ((((155 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_156 : evalOK ((((156 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_157 : evalOK ((((157 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_158 : evalOK ((((158 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_159 : evalOK ((((159 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_160 : evalOK ((((160 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_161 : evalOK ((((161 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_162 : evalOK ((((162 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_163 : evalOK ((((163 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_164 : evalOK ((((164 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_165 : evalOK ((((165 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_166 : evalOK ((((166 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_167 : evalOK ((((167 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_168 : evalOK ((((168 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_169 : evalOK ((((169 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_170 : evalOK ((((170 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_171 : evalOK ((((171 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_172 : evalOK ((((172 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_173 : evalOK ((((173 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_174 : evalOK ((((174 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_175 : evalOK ((((175 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_176 : evalOK ((((176 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_177 : evalOK ((((177 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_178 : evalOK ((((178 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_179 : evalOK ((((179 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_180 : evalOK ((((180 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_181 : evalOK ((((181 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_182 : evalOK ((((182 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_183 : evalOK ((((183 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_184 : evalOK ((((184 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_185 : evalOK ((((185 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_186 : evalOK ((((186 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_187 : evalOK ((((187 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_188 : evalOK ((((188 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_189 : evalOK ((((189 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_190 : evalOK ((((190 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_191 : evalOK ((((191 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_192 : evalOK ((((192 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_193 : evalOK ((((193 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_194 : evalOK ((((194 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_195 : evalOK ((((195 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_196 : evalOK ((((196 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_197 : evalOK ((((197 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_198 : evalOK ((((198 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_199 : evalOK ((((199 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_200 : evalOK ((((200 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_201 : evalOK ((((201 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_202 : evalOK ((((202 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_203 : evalOK ((((203 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_3 : ∀ k : ℕ, 153 ≤ k → k < 204 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_153, ok_154, ok_155, ok_156, ok_157, ok_158, ok_159, ok_160, ok_161, ok_162, ok_163, ok_164, ok_165, ok_166, ok_167, ok_168, ok_169, ok_170, ok_171, ok_172, ok_173, ok_174, ok_175, ok_176, ok_177, ok_178, ok_179, ok_180, ok_181, ok_182, ok_183, ok_184, ok_185, ok_186, ok_187, ok_188, ok_189, ok_190, ok_191, ok_192, ok_193, ok_194, ok_195, ok_196, ok_197, ok_198, ok_199, ok_200, ok_201, ok_202, ok_203]

end Sz8.Galois.ResEval
