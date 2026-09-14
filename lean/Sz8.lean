import Sz8.Monodromy
import Sz8.Galois

/-!
# The Galois group of `f(X, -7/5)` over `ℚ` is Suzuki's group `Sz(8)`

`Sz8.Monodromy` certifies the inputs: the modular factorizations and Galois-order divisibility of the
specialization, the root covering and continuation steps, the two meridians, and the group certificates.
`Sz8.Galois` proves the generic Galois group (`Sz8.Galois.generic_galois`), the specialization theorem
(`Sz8.Galois.card_gal_specialization`, `Sz8.Galois.gal_specialization_eq_N`) and the identification with
`Sz(8)` (`Sz8.Galois.N_equiv_suzuki`, `Sz8.Galois.gal_specialization_equiv_suzuki`).
-/
