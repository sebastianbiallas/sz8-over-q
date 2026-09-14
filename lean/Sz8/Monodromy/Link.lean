import Sz8.Monodromy.ConcreteStep
import Sz8.Monodromy.InputAgreement
import Sz8.Monodromy.Irreducibility

/-!
The continuation theorems and the arithmetic theorems concern the same polynomial.

`paperFamily t` is the column representation used for continuation. `paperSpecialization`
is the term-by-term specialization at `-7/5` used for the Galois-group results. Using the
exact agreement `inputs_agree` and `column_dimensions`, we prove:

* `paperFamily_eq_sparse`: for every complex `t`, `paperFamily t` is the sparse sum
  `∑ (n/d) tʲ Xⁱ` over the 472 input terms;
* `paperFamily_specialization`: `paperFamily (-7/5)` is the image of
  `paperSpecialization` in `ℂ[X]`.
-/

open Polynomial Finset

namespace Sz8.Monodromy

/-- Sparse evaluation of rational terms `(i, j, a) ↦ a tʲ Xⁱ` at a complex parameter. -/
noncomputable def sparseFamily (ts : List (ℕ × ℕ × ℚ)) (t : ℂ) : ℂ[X] :=
  (ts.map fun a => C ((a.2.2 : ℂ) * t ^ a.2.1) * X ^ a.1).sum

private theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.sum_range_succ, list_sum_range f n, Finset.sum_range_succ]

theorem complexPoly_eq_sum : ∀ (cs : List ℚ) (N : ℕ), cs.length ≤ N →
    complexPoly cs = ∑ i ∈ range N, C ((cs.getD i 0 : ℚ) : ℂ) * X ^ i
  | [], N, _ => by simp [complexPoly]
  | a :: cs, 0, h => by simp at h
  | a :: cs, N + 1, h => by
    rw [Finset.sum_range_succ', complexPoly, complexPoly_eq_sum cs N (by simpa using h),
      Finset.mul_sum, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

theorem complexFamily_eq_sum (t : ℂ) : ∀ (cols : List (List ℚ)) (M : ℕ), cols.length ≤ M →
    complexFamily cols t = ∑ j ∈ range M, C t ^ j * complexPoly (cols.getD j [])
  | [], M, _ => by simp [complexFamily, complexPoly]
  | cs :: rest, 0, h => by simp at h
  | cs :: rest, M + 1, h => by
    rw [Finset.sum_range_succ', complexFamily, complexFamily_eq_sum t rest M (by simpa using h),
      Finset.mul_sum, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul, pow_succ]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring

theorem sparseFamily_append (l₁ l₂ : List (ℕ × ℕ × ℚ)) (t : ℂ) :
    sparseFamily (l₁ ++ l₂) t = sparseFamily l₁ t + sparseFamily l₂ t := by
  simp [sparseFamily]

theorem sparseFamily_flatMap {α : Type*} (f : α → List (ℕ × ℕ × ℚ)) (t : ℂ) :
    ∀ l : List α, sparseFamily (l.flatMap f) t = (l.map fun x => sparseFamily (f x) t).sum
  | [] => by simp [sparseFamily]
  | x :: l => by
    rw [List.flatMap_cons, sparseFamily_append, sparseFamily_flatMap f t l]
    simp

theorem sparseFamily_filterMap (i : ℕ) (a : ℕ → ℚ) (t : ℂ) : ∀ L : List ℕ,
    sparseFamily (L.filterMap fun j => if a j = 0 then none else some (i, j, a j)) t =
      (L.map fun j => C ((a j : ℂ) * t ^ j) * X ^ i).sum
  | [] => by simp [sparseFamily]
  | j :: L => by
    have ih := sparseFamily_filterMap i a t L
    by_cases h : a j = 0
    · simp [h, ih]
    · simp only [List.filterMap_cons, h, ↓reduceIte, List.map_cons, List.sum_cons, ← ih]
      simp [sparseFamily]

/-- The coefficient of `tʲ Xⁱ` in the column representation. -/
def colCoeff (i j : ℕ) : ℚ := (originalColumns.getD j []).getD i 0

theorem columnTerms_eq : columnTerms = (List.range 66).flatMap fun i =>
    (List.range 8).filterMap fun j =>
      if colCoeff i j = 0 then none else some (i, j, colCoeff i j) := rfl

theorem column_length_le (j : ℕ) : (originalColumns.getD j []).length ≤ 66 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : originalColumns[j]? with
  | none => simp
  | some cs =>
    have := List.all_eq_true.mp column_dimensions.2 cs (List.mem_of_getElem? h)
    simpa using this

/-- The column family is the sparse sum of its nonzero column coefficients. -/
theorem paperFamily_eq_columnTerms (t : ℂ) : paperFamily t = sparseFamily columnTerms t := by
  rw [paperFamily, complexFamily_eq_sum t _ 8 column_dimensions.1.le, columnTerms_eq,
    sparseFamily_flatMap, list_sum_range]
  simp only [sparseFamily_filterMap, list_sum_range]
  simp only [fun j => complexPoly_eq_sum _ 66 (column_length_le j), Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [colCoeff, C_mul, C_pow]
  ring

/-- For every complex `t`, the continuation family is the sparse sum over the exact
input terms. -/
theorem paperFamily_eq_sparse (t : ℂ) :
    paperFamily t = sparseFamily
      (inputTerms.map fun a => (a.1, a.2.1, (a.2.2.1 : ℚ) / a.2.2.2)) t := by
  rw [paperFamily_eq_columnTerms, inputs_agree]

theorem sparseFamily_ratCast (r : ℚ) : ∀ ts : List (ℕ × ℕ × ℤ × ℕ),
    sparseFamily (ts.map fun a => (a.1, a.2.1, (a.2.2.1 : ℚ) / a.2.2.2)) (r : ℂ) =
      (ts.foldr (fun (a : ℕ × ℕ × ℤ × ℕ) acc =>
        C ((a.2.2.1 : ℚ) / a.2.2.2 * r ^ a.2.1) * X ^ a.1 + acc) 0).map (algebraMap ℚ ℂ)
  | [] => by simp [sparseFamily]
  | a :: ts => by
    have ih := sparseFamily_ratCast r ts
    simp only [sparseFamily, List.map_cons, List.sum_cons, List.foldr_cons] at ih ⊢
    rw [ih, Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X]
    simp

/-- The continuation family at `t = -7/5` is the specialization used in the
arithmetic theorems. -/
theorem paperFamily_specialization :
    paperFamily (-7 / 5) = paperSpecialization.map (algebraMap ℚ ℂ) := by
  have h : ((-7 / 5 : ℚ) : ℂ) = -7 / 5 := by push_cast; ring
  rw [← h, paperFamily_eq_sparse, sparseFamily_ratCast, paperSpecialization]

/-- Consequently `paperFamily (-7/5)` is separable: its 65 complex roots are distinct. -/
theorem paperFamily_specialization_separable : (paperFamily (-7 / 5)).Separable := by
  rw [paperFamily_specialization]
  exact paperSpecialization_separable.map

end Sz8.Monodromy
