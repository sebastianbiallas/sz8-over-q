import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `204 ≤ k < 255`. -/

namespace Sz8.Galois.ResEval

theorem ok_204 : evalOK ((((204 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_205 : evalOK ((((205 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_206 : evalOK ((((206 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_207 : evalOK ((((207 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_208 : evalOK ((((208 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_209 : evalOK ((((209 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_210 : evalOK ((((210 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_211 : evalOK ((((211 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_212 : evalOK ((((212 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_213 : evalOK ((((213 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_214 : evalOK ((((214 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_215 : evalOK ((((215 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_216 : evalOK ((((216 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_217 : evalOK ((((217 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_218 : evalOK ((((218 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_219 : evalOK ((((219 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_220 : evalOK ((((220 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_221 : evalOK ((((221 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_222 : evalOK ((((222 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_223 : evalOK ((((223 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_224 : evalOK ((((224 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_225 : evalOK ((((225 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_226 : evalOK ((((226 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_227 : evalOK ((((227 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_228 : evalOK ((((228 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_229 : evalOK ((((229 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_230 : evalOK ((((230 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_231 : evalOK ((((231 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_232 : evalOK ((((232 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_233 : evalOK ((((233 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_234 : evalOK ((((234 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_235 : evalOK ((((235 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_236 : evalOK ((((236 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_237 : evalOK ((((237 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_238 : evalOK ((((238 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_239 : evalOK ((((239 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_240 : evalOK ((((240 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_241 : evalOK ((((241 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_242 : evalOK ((((242 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_243 : evalOK ((((243 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_244 : evalOK ((((244 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_245 : evalOK ((((245 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_246 : evalOK ((((246 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_247 : evalOK ((((247 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_248 : evalOK ((((248 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_249 : evalOK ((((249 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_250 : evalOK ((((250 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_251 : evalOK ((((251 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_252 : evalOK ((((252 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_253 : evalOK ((((253 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_254 : evalOK ((((254 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_4 : ∀ k : ℕ, 204 ≤ k → k < 255 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_204, ok_205, ok_206, ok_207, ok_208, ok_209, ok_210, ok_211, ok_212, ok_213, ok_214, ok_215, ok_216, ok_217, ok_218, ok_219, ok_220, ok_221, ok_222, ok_223, ok_224, ok_225, ok_226, ok_227, ok_228, ok_229, ok_230, ok_231, ok_232, ok_233, ok_234, ok_235, ok_236, ok_237, ok_238, ok_239, ok_240, ok_241, ok_242, ok_243, ok_244, ok_245, ok_246, ok_247, ok_248, ok_249, ok_250, ok_251, ok_252, ok_253, ok_254]

end Sz8.Galois.ResEval
