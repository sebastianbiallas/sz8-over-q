import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `408 ≤ k < 459`. -/

namespace Sz8.Galois.ResEval

theorem ok_408 : evalOK ((((408 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_409 : evalOK ((((409 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_410 : evalOK ((((410 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_411 : evalOK ((((411 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_412 : evalOK ((((412 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_413 : evalOK ((((413 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_414 : evalOK ((((414 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_415 : evalOK ((((415 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_416 : evalOK ((((416 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_417 : evalOK ((((417 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_418 : evalOK ((((418 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_419 : evalOK ((((419 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_420 : evalOK ((((420 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_421 : evalOK ((((421 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_422 : evalOK ((((422 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_423 : evalOK ((((423 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_424 : evalOK ((((424 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_425 : evalOK ((((425 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_426 : evalOK ((((426 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_427 : evalOK ((((427 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_428 : evalOK ((((428 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_429 : evalOK ((((429 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_430 : evalOK ((((430 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_431 : evalOK ((((431 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_432 : evalOK ((((432 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_433 : evalOK ((((433 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_434 : evalOK ((((434 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_435 : evalOK ((((435 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_436 : evalOK ((((436 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_437 : evalOK ((((437 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_438 : evalOK ((((438 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_439 : evalOK ((((439 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_440 : evalOK ((((440 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_441 : evalOK ((((441 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_442 : evalOK ((((442 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_443 : evalOK ((((443 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_444 : evalOK ((((444 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_445 : evalOK ((((445 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_446 : evalOK ((((446 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_447 : evalOK ((((447 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_448 : evalOK ((((448 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_449 : evalOK ((((449 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_450 : evalOK ((((450 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_451 : evalOK ((((451 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_452 : evalOK ((((452 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_453 : evalOK ((((453 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_454 : evalOK ((((454 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_455 : evalOK ((((455 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_456 : evalOK ((((456 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_457 : evalOK ((((457 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_458 : evalOK ((((458 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_8 : ∀ k : ℕ, 408 ≤ k → k < 459 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_408, ok_409, ok_410, ok_411, ok_412, ok_413, ok_414, ok_415, ok_416, ok_417, ok_418, ok_419, ok_420, ok_421, ok_422, ok_423, ok_424, ok_425, ok_426, ok_427, ok_428, ok_429, ok_430, ok_431, ok_432, ok_433, ok_434, ok_435, ok_436, ok_437, ok_438, ok_439, ok_440, ok_441, ok_442, ok_443, ok_444, ok_445, ok_446, ok_447, ok_448, ok_449, ok_450, ok_451, ok_452, ok_453, ok_454, ok_455, ok_456, ok_457, ok_458]

end Sz8.Galois.ResEval
