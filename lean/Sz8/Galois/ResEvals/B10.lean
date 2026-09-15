import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `510 ≤ k < 561`. -/

namespace Sz8.Galois.ResEval

theorem ok_510 : evalOK ((((510 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_511 : evalOK ((((511 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_512 : evalOK ((((512 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_513 : evalOK ((((513 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_514 : evalOK ((((514 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_515 : evalOK ((((515 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_516 : evalOK ((((516 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_517 : evalOK ((((517 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_518 : evalOK ((((518 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_519 : evalOK ((((519 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_520 : evalOK ((((520 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_521 : evalOK ((((521 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_522 : evalOK ((((522 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_523 : evalOK ((((523 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_524 : evalOK ((((524 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_525 : evalOK ((((525 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_526 : evalOK ((((526 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_527 : evalOK ((((527 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_528 : evalOK ((((528 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_529 : evalOK ((((529 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_530 : evalOK ((((530 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_531 : evalOK ((((531 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_532 : evalOK ((((532 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_533 : evalOK ((((533 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_534 : evalOK ((((534 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_535 : evalOK ((((535 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_536 : evalOK ((((536 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_537 : evalOK ((((537 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_538 : evalOK ((((538 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_539 : evalOK ((((539 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_540 : evalOK ((((540 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_541 : evalOK ((((541 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_542 : evalOK ((((542 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_543 : evalOK ((((543 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_544 : evalOK ((((544 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_545 : evalOK ((((545 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_546 : evalOK ((((546 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_547 : evalOK ((((547 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_548 : evalOK ((((548 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_549 : evalOK ((((549 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_550 : evalOK ((((550 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_551 : evalOK ((((551 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_552 : evalOK ((((552 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_553 : evalOK ((((553 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_554 : evalOK ((((554 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_555 : evalOK ((((555 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_556 : evalOK ((((556 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_557 : evalOK ((((557 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_558 : evalOK ((((558 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_559 : evalOK ((((559 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_560 : evalOK ((((560 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_10 : ∀ k : ℕ, 510 ≤ k → k < 561 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_510, ok_511, ok_512, ok_513, ok_514, ok_515, ok_516, ok_517, ok_518, ok_519, ok_520, ok_521, ok_522, ok_523, ok_524, ok_525, ok_526, ok_527, ok_528, ok_529, ok_530, ok_531, ok_532, ok_533, ok_534, ok_535, ok_536, ok_537, ok_538, ok_539, ok_540, ok_541, ok_542, ok_543, ok_544, ok_545, ok_546, ok_547, ok_548, ok_549, ok_550, ok_551, ok_552, ok_553, ok_554, ok_555, ok_556, ok_557, ok_558, ok_559, ok_560]

end Sz8.Galois.ResEval
