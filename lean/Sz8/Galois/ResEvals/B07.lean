import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `357 ≤ k < 408`. -/

namespace Sz8.Galois.ResEval

theorem ok_357 : evalOK ((((357 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_358 : evalOK ((((358 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_359 : evalOK ((((359 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_360 : evalOK ((((360 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_361 : evalOK ((((361 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_362 : evalOK ((((362 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_363 : evalOK ((((363 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_364 : evalOK ((((364 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_365 : evalOK ((((365 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_366 : evalOK ((((366 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_367 : evalOK ((((367 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_368 : evalOK ((((368 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_369 : evalOK ((((369 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_370 : evalOK ((((370 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_371 : evalOK ((((371 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_372 : evalOK ((((372 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_373 : evalOK ((((373 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_374 : evalOK ((((374 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_375 : evalOK ((((375 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_376 : evalOK ((((376 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_377 : evalOK ((((377 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_378 : evalOK ((((378 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_379 : evalOK ((((379 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_380 : evalOK ((((380 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_381 : evalOK ((((381 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_382 : evalOK ((((382 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_383 : evalOK ((((383 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_384 : evalOK ((((384 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_385 : evalOK ((((385 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_386 : evalOK ((((386 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_387 : evalOK ((((387 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_388 : evalOK ((((388 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_389 : evalOK ((((389 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_390 : evalOK ((((390 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_391 : evalOK ((((391 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_392 : evalOK ((((392 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_393 : evalOK ((((393 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_394 : evalOK ((((394 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_395 : evalOK ((((395 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_396 : evalOK ((((396 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_397 : evalOK ((((397 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_398 : evalOK ((((398 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_399 : evalOK ((((399 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_400 : evalOK ((((400 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_401 : evalOK ((((401 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_402 : evalOK ((((402 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_403 : evalOK ((((403 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_404 : evalOK ((((404 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_405 : evalOK ((((405 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_406 : evalOK ((((406 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_407 : evalOK ((((407 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_7 : ∀ k : ℕ, 357 ≤ k → k < 408 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_357, ok_358, ok_359, ok_360, ok_361, ok_362, ok_363, ok_364, ok_365, ok_366, ok_367, ok_368, ok_369, ok_370, ok_371, ok_372, ok_373, ok_374, ok_375, ok_376, ok_377, ok_378, ok_379, ok_380, ok_381, ok_382, ok_383, ok_384, ok_385, ok_386, ok_387, ok_388, ok_389, ok_390, ok_391, ok_392, ok_393, ok_394, ok_395, ok_396, ok_397, ok_398, ok_399, ok_400, ok_401, ok_402, ok_403, ok_404, ok_405, ok_406, ok_407]

end Sz8.Galois.ResEval
