import Sz8.Monodromy.Modular
import Mathlib.FieldTheory.Separable

open Polynomial HexBerlekampMathlib

namespace Sz8.Monodromy

/-- The actual reduction at 11 has a separable irreducible factorization
of degrees 1,1,7,7,7,7,7,7,7,7,7, expressed entirely in Mathlib's types. -/
theorem modular_certificate_11 :
    ∃ fs : List (Polynomial (ZMod 11)),
      fs.prod = toMathlibPolynomial (paperFp 11) ∧
      (∀ q ∈ fs, Irreducible q) ∧
      fs.map Polynomial.natDegree = [1, 1, 7, 7, 7, 7, 7, 7, 7, 7, 7] ∧
      (toMathlibPolynomial (paperFp 11)).Separable := by
  refine ⟨factors11.map toMathlibPolynomial, factorization_11, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hq
    exact irreducible_11 f hf
  · simpa only [List.map_map, Function.comp_def, natDegree_toMathlibPolynomial] using degrees_11
  · rw [reduction_11]
    exact squarefree_11

/-- The actual reduction at 31 has five irreducible factors of degree 13
and is separable, expressed entirely in Mathlib's types. -/
theorem modular_certificate_31 :
    ∃ fs : List (Polynomial (ZMod 31)),
      fs.prod = toMathlibPolynomial (paperFp 31) ∧
      (∀ q ∈ fs, Irreducible q) ∧
      fs.map Polynomial.natDegree = [13, 13, 13, 13, 13] ∧
      (toMathlibPolynomial (paperFp 31)).Separable := by
  refine ⟨factors31.map toMathlibPolynomial, factorization_31, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hq
    exact irreducible_31 f hf
  · simpa only [List.map_map, Function.comp_def, natDegree_toMathlibPolynomial] using degrees_31
  · rw [reduction_31]
    exact squarefree_31

end Sz8.Monodromy
