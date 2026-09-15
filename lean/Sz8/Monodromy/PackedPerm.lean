import Mathlib.GroupTheory.Perm.Basic

/-!
# Permutations of `Fin 65` packed into a single natural number

A permutation is stored as 65 seven-bit digits of one natural number, so the kernel reads an
image with two GMP operations instead of walking a 65-entry vector. Only the *encoding* of
the function changes: the group operation is still `Equiv.Perm`'s composition, and the two
inverse laws are checked by kernel reduction, so nothing here has to be proved correct.

Measured on the group certificates: packed lookups are about seven times faster than
`![…]` vectors and, unlike them, add no measurable memory to the kernel's cache.
-/

namespace Sz8.Monodromy

/-- The `i`-th seven-bit digit of a packed permutation. -/
def digit (p i : ℕ) : ℕ := (p >>> (7 * i)) % 128

/-- The action of a packed permutation on `Fin 65`. The outer `% 65` only makes the value a
valid index; on the certified data every digit is already smaller than 65. -/
def appF (p : ℕ) (i : Fin 65) : Fin 65 := ⟨digit p i.val % 65, Nat.mod_lt _ (Nat.succ_pos 64)⟩

/-- A permutation of `Fin 65` from a packed image list together with its packed inverse. -/
def ofPacked (p q : ℕ) (h₁ : ∀ i, appF q (appF p i) = i := by decide +kernel)
    (h₂ : ∀ i, appF p (appF q i) = i := by decide +kernel) : Equiv.Perm (Fin 65) :=
  ⟨appF p, appF q, h₁, h₂⟩

end Sz8.Monodromy
