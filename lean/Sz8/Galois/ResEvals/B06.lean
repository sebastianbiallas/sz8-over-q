import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `306 ≤ k < 357`. -/

namespace Sz8.Galois.ResEval

theorem ok_306 : evalOK ((((306 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_307 : evalOK ((((307 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_308 : evalOK ((((308 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_309 : evalOK ((((309 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_310 : evalOK ((((310 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_311 : evalOK ((((311 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_312 : evalOK ((((312 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_313 : evalOK ((((313 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_314 : evalOK ((((314 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_315 : evalOK ((((315 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_316 : evalOK ((((316 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_317 : evalOK ((((317 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_318 : evalOK ((((318 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_319 : evalOK ((((319 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_320 : evalOK ((((320 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_321 : evalOK ((((321 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_322 : evalOK ((((322 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_323 : evalOK ((((323 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_324 : evalOK ((((324 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_325 : evalOK ((((325 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_326 : evalOK ((((326 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_327 : evalOK ((((327 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_328 : evalOK ((((328 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_329 : evalOK ((((329 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_330 : evalOK ((((330 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_331 : evalOK ((((331 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_332 : evalOK ((((332 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_333 : evalOK ((((333 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_334 : evalOK ((((334 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_335 : evalOK ((((335 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_336 : evalOK ((((336 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_337 : evalOK ((((337 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_338 : evalOK ((((338 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_339 : evalOK ((((339 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_340 : evalOK ((((340 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_341 : evalOK ((((341 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_342 : evalOK ((((342 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_343 : evalOK ((((343 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_344 : evalOK ((((344 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_345 : evalOK ((((345 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_346 : evalOK ((((346 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_347 : evalOK ((((347 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_348 : evalOK ((((348 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_349 : evalOK ((((349 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_350 : evalOK ((((350 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_351 : evalOK ((((351 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_352 : evalOK ((((352 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_353 : evalOK ((((353 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_354 : evalOK ((((354 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_355 : evalOK ((((355 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_356 : evalOK ((((356 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_6 : ∀ k : ℕ, 306 ≤ k → k < 357 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_306, ok_307, ok_308, ok_309, ok_310, ok_311, ok_312, ok_313, ok_314, ok_315, ok_316, ok_317, ok_318, ok_319, ok_320, ok_321, ok_322, ok_323, ok_324, ok_325, ok_326, ok_327, ok_328, ok_329, ok_330, ok_331, ok_332, ok_333, ok_334, ok_335, ok_336, ok_337, ok_338, ok_339, ok_340, ok_341, ok_342, ok_343, ok_344, ok_345, ok_346, ok_347, ok_348, ok_349, ok_350, ok_351, ok_352, ok_353, ok_354, ok_355, ok_356]

end Sz8.Galois.ResEval
