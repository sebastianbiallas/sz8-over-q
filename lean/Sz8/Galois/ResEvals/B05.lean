import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `255 ≤ k < 306`. -/

namespace Sz8.Galois.ResEval

theorem ok_255 : evalOK ((((255 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_256 : evalOK ((((256 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_257 : evalOK ((((257 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_258 : evalOK ((((258 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_259 : evalOK ((((259 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_260 : evalOK ((((260 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_261 : evalOK ((((261 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_262 : evalOK ((((262 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_263 : evalOK ((((263 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_264 : evalOK ((((264 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_265 : evalOK ((((265 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_266 : evalOK ((((266 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_267 : evalOK ((((267 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_268 : evalOK ((((268 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_269 : evalOK ((((269 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_270 : evalOK ((((270 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_271 : evalOK ((((271 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_272 : evalOK ((((272 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_273 : evalOK ((((273 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_274 : evalOK ((((274 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_275 : evalOK ((((275 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_276 : evalOK ((((276 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_277 : evalOK ((((277 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_278 : evalOK ((((278 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_279 : evalOK ((((279 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_280 : evalOK ((((280 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_281 : evalOK ((((281 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_282 : evalOK ((((282 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_283 : evalOK ((((283 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_284 : evalOK ((((284 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_285 : evalOK ((((285 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_286 : evalOK ((((286 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_287 : evalOK ((((287 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_288 : evalOK ((((288 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_289 : evalOK ((((289 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_290 : evalOK ((((290 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_291 : evalOK ((((291 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_292 : evalOK ((((292 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_293 : evalOK ((((293 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_294 : evalOK ((((294 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_295 : evalOK ((((295 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_296 : evalOK ((((296 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_297 : evalOK ((((297 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_298 : evalOK ((((298 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_299 : evalOK ((((299 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_300 : evalOK ((((300 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_301 : evalOK ((((301 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_302 : evalOK ((((302 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_303 : evalOK ((((303 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_304 : evalOK ((((304 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_305 : evalOK ((((305 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_5 : ∀ k : ℕ, 255 ≤ k → k < 306 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_255, ok_256, ok_257, ok_258, ok_259, ok_260, ok_261, ok_262, ok_263, ok_264, ok_265, ok_266, ok_267, ok_268, ok_269, ok_270, ok_271, ok_272, ok_273, ok_274, ok_275, ok_276, ok_277, ok_278, ok_279, ok_280, ok_281, ok_282, ok_283, ok_284, ok_285, ok_286, ok_287, ok_288, ok_289, ok_290, ok_291, ok_292, ok_293, ok_294, ok_295, ok_296, ok_297, ok_298, ok_299, ok_300, ok_301, ok_302, ok_303, ok_304, ok_305]

end Sz8.Galois.ResEval
