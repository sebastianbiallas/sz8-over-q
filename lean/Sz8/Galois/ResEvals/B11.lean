import Sz8.Galois.ResEvalCore
import Mathlib.Tactic.IntervalCases

/-! Kernel evaluations of the resultant identity at `t = k - 406`, `561 ≤ k < 612`. -/

namespace Sz8.Galois.ResEval

theorem ok_561 : evalOK ((((561 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_562 : evalOK ((((562 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_563 : evalOK ((((563 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_564 : evalOK ((((564 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_565 : evalOK ((((565 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_566 : evalOK ((((566 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_567 : evalOK ((((567 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_568 : evalOK ((((568 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_569 : evalOK ((((569 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_570 : evalOK ((((570 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_571 : evalOK ((((571 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_572 : evalOK ((((572 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_573 : evalOK ((((573 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_574 : evalOK ((((574 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_575 : evalOK ((((575 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_576 : evalOK ((((576 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_577 : evalOK ((((577 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_578 : evalOK ((((578 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_579 : evalOK ((((579 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_580 : evalOK ((((580 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_581 : evalOK ((((581 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_582 : evalOK ((((582 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_583 : evalOK ((((583 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_584 : evalOK ((((584 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_585 : evalOK ((((585 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_586 : evalOK ((((586 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_587 : evalOK ((((587 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_588 : evalOK ((((588 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_589 : evalOK ((((589 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_590 : evalOK ((((590 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_591 : evalOK ((((591 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_592 : evalOK ((((592 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_593 : evalOK ((((593 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_594 : evalOK ((((594 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_595 : evalOK ((((595 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_596 : evalOK ((((596 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_597 : evalOK ((((597 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_598 : evalOK ((((598 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_599 : evalOK ((((599 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_600 : evalOK ((((600 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_601 : evalOK ((((601 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_602 : evalOK ((((602 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_603 : evalOK ((((603 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_604 : evalOK ((((604 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_605 : evalOK ((((605 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_606 : evalOK ((((606 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_607 : evalOK ((((607 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_608 : evalOK ((((608 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_609 : evalOK ((((609 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_610 : evalOK ((((610 : ℕ)) : ℚ) - 406) = true := by decide +kernel
theorem ok_611 : evalOK ((((611 : ℕ)) : ℚ) - 406) = true := by decide +kernel

theorem batch_11 : ∀ k : ℕ, 561 ≤ k → k < 612 → evalOK ((k : ℚ) - 406) = true := by
  intro k h1 h2
  interval_cases k
  exacts [ok_561, ok_562, ok_563, ok_564, ok_565, ok_566, ok_567, ok_568, ok_569, ok_570, ok_571, ok_572, ok_573, ok_574, ok_575, ok_576, ok_577, ok_578, ok_579, ok_580, ok_581, ok_582, ok_583, ok_584, ok_585, ok_586, ok_587, ok_588, ok_589, ok_590, ok_591, ok_592, ok_593, ok_594, ok_595, ok_596, ok_597, ok_598, ok_599, ok_600, ok_601, ok_602, ok_603, ok_604, ok_605, ok_606, ok_607, ok_608, ok_609, ok_610, ok_611]

end Sz8.Galois.ResEval
