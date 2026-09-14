import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `459 ≤ k < 510`. -/

namespace Sz8.Galois.ResEval

theorem ok_459 : evalOK ((((459 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_460 : evalOK ((((460 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_461 : evalOK ((((461 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_462 : evalOK ((((462 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_463 : evalOK ((((463 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_464 : evalOK ((((464 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_465 : evalOK ((((465 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_466 : evalOK ((((466 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_467 : evalOK ((((467 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_468 : evalOK ((((468 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_469 : evalOK ((((469 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_470 : evalOK ((((470 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_471 : evalOK ((((471 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_472 : evalOK ((((472 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_473 : evalOK ((((473 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_474 : evalOK ((((474 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_475 : evalOK ((((475 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_476 : evalOK ((((476 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_477 : evalOK ((((477 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_478 : evalOK ((((478 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_479 : evalOK ((((479 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_480 : evalOK ((((480 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_481 : evalOK ((((481 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_482 : evalOK ((((482 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_483 : evalOK ((((483 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_484 : evalOK ((((484 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_485 : evalOK ((((485 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_486 : evalOK ((((486 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_487 : evalOK ((((487 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_488 : evalOK ((((488 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_489 : evalOK ((((489 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_490 : evalOK ((((490 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_491 : evalOK ((((491 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_492 : evalOK ((((492 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_493 : evalOK ((((493 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_494 : evalOK ((((494 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_495 : evalOK ((((495 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_496 : evalOK ((((496 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_497 : evalOK ((((497 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_498 : evalOK ((((498 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_499 : evalOK ((((499 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_500 : evalOK ((((500 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_501 : evalOK ((((501 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_502 : evalOK ((((502 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_503 : evalOK ((((503 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_504 : evalOK ((((504 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_505 : evalOK ((((505 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_506 : evalOK ((((506 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_507 : evalOK ((((507 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_508 : evalOK ((((508 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_509 : evalOK ((((509 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_9 : ∀ k : ℕ, 459 ≤ k → k < 510 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_459, ok_460, ok_461, ok_462, ok_463, ok_464, ok_465, ok_466, ok_467, ok_468, ok_469, ok_470, ok_471, ok_472, ok_473, ok_474, ok_475, ok_476, ok_477, ok_478, ok_479, ok_480, ok_481, ok_482, ok_483, ok_484, ok_485, ok_486, ok_487, ok_488, ok_489, ok_490, ok_491, ok_492, ok_493, ok_494, ok_495, ok_496, ok_497, ok_498, ok_499, ok_500, ok_501, ok_502, ok_503, ok_504, ok_505, ok_506, ok_507, ok_508, ok_509]

end Sz8.Galois.ResEval
