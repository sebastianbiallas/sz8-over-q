import Sz8.Monodromy.PaperCovering
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.NormNum.Prime

/-!
# The first Newton edge of `f` at `t = ∞`

**Abstract lemma** (`units_map_residue`, `card_units`). In a local domain `R`, if the roots `s` of a
split monic polynomial reduce to `X^a · H` with `H(0) ≠ 0` and `H` separable, then the unit roots
reduce exactly onto the roots of `H` (each once), and there are `deg H` of them. No Hensel lifting.

**Ratio corollary** (`exists_primitive_ratio`). For `H = X^13 + c`, `c ≠ 0`, two unit roots have a
ratio whose residue is a primitive 13th root of unity.

**Data** (`edge_terms`, `specialize_zero`, `edge_eval`). For the paper's `f = Σ c_{ij} X^i t^j`, every term
has `7i + 13j ≤ 455`, with equality exactly for `X⁶⁵` and `c X⁵² t⁷`, `c = c₅₂,₇ ≠ 0`. So
`F(Y, τ) = Σ c_{ij} τ^(455 - 7i - 13j) Y^i` is monic, `F(Y, 0) = Y⁵² (Y¹³ + c)`, and
`F(τ⁷ x, τ) = τ⁴⁵⁵ f(x, t)` whenever `τ¹³ t = 1`.
-/

open Polynomial IsLocalRing

namespace Sz8.Galois.FirstEdge

section Abstract

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem roots_map_residue (s : Multiset R) {a : ℕ} {H : (ResidueField R)[X]}
    (h : ((s.map fun y => X - C y).prod).map (residue R) = X ^ a * H) (hH : H ≠ 0) :
    s.map (residue R) = a • {0} + H.roots := by
  have h1 : ((s.map fun y => X - C y).prod).map (residue R) =
      ((s.map (residue R)).map fun y => X - C y).prod := by
    rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun y _ => ?_
    simp
  have h2 := roots_multiset_prod_X_sub_C (s.map (residue R))
  rw [← h1, h, roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hH), roots_X_pow] at h2
  exact h2.symm

open scoped Classical in
/-- **The unit roots reduce onto the roots of `H`.** -/
theorem units_map_residue (s : Multiset R) {a : ℕ} {H : (ResidueField R)[X]}
    (h : ((s.map fun y => X - C y).prod).map (residue R) = X ^ a * H) (hH0 : H.eval 0 ≠ 0) :
    (s.filter IsUnit).map (residue R) = H.roots := by
  classical
  have hH : H ≠ 0 := fun h => hH0 (by simp [h])
  have hr := roots_map_residue s h hH
  have hfilter : (s.filter IsUnit).map (residue R) = (s.map (residue R)).filter (· ≠ 0) := by
    rw [Multiset.filter_map]
    congr 1
    exact Multiset.filter_congr fun y _ => (residue_ne_zero_iff_isUnit y).symm
  rw [hfilter, hr, Multiset.filter_add]
  have h0 : (a • ({0} : Multiset (ResidueField R))).filter (· ≠ 0) = 0 := by
    rw [Multiset.filter_eq_nil]; intro x hx; simpa using Multiset.mem_of_mem_nsmul hx
  have h1 : H.roots.filter (· ≠ 0) = H.roots := by
    rw [Multiset.filter_eq_self]; intro x hx hx0
    subst hx0; exact hH0 ((mem_roots hH).1 hx)
  rw [h0, h1, zero_add]

/-- **Ratio corollary.** -/
theorem exists_primitive_ratio [CharZero (ResidueField R)] (s : Multiset R) {a : ℕ}
    {c : ResidueField R} (hc : c ≠ 0)
    (h : ((s.map fun y => X - C y).prod).map (residue R) = X ^ a * (X ^ 13 + C c)) :
    ∃ y₁ ∈ s, ∃ y₂ ∈ s, IsUnit y₁ ∧ IsUnit y₂ ∧
      IsPrimitiveRoot (residue R y₁ / residue R y₂) 13 := by
  classical
  set H : (ResidueField R)[X] := X ^ 13 + C c with hHdef
  have hH' : H = X ^ 13 - C (-c) := by simp [hHdef, sub_eq_add_neg]
  have hH0 : H.eval 0 ≠ 0 := by simpa [hHdef] using hc
  have hmon : H.Monic := by rw [hH']; exact monic_X_pow_sub_C _ (by norm_num)
  have hsep : H.Separable := by
    rw [hH']; exact separable_X_pow_sub_C _ (by norm_num) (neg_ne_zero.2 hc)
  have hunits := units_map_residue s h hH0
  have hr := roots_map_residue s h hmon.ne_zero
  have hcard : Multiset.card H.roots = 13 := by
    have e1 := congrArg Multiset.card hr
    simp only [Multiset.card_map, Multiset.card_add, Multiset.card_nsmul, Multiset.card_singleton,
      mul_one] at e1
    have e2 : (((s.map fun y => X - C y).prod).map (residue R)).natDegree = Multiset.card s := by
      rw [(monic_multiset_prod_of_monic _ _ fun y _ => monic_X_sub_C y).natDegree_map,
        natDegree_multiset_prod_X_sub_C_eq_card]
    have e3 : (X ^ a * H).natDegree = a + 13 := by
      rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hmon.ne_zero, natDegree_X_pow, hHdef,
        natDegree_X_pow_add_C]
    rw [h, e3] at e2
    omega
  -- two distinct roots of `H`
  have hnd := nodup_roots hsep
  obtain ⟨r₂, hr₂⟩ : ∃ r, r ∈ H.roots := Multiset.card_pos_iff_exists_mem.1 (by rw [hcard]; norm_num)
  obtain ⟨r₁, hr₁⟩ : ∃ r, r ∈ H.roots.erase r₂ :=
    Multiset.card_pos_iff_exists_mem.1 (by rw [Multiset.card_erase_of_mem hr₂, hcard]; norm_num)
  have hne : r₁ ≠ r₂ := fun he => by
    subst he; exact (Multiset.Nodup.notMem_erase hnd) hr₁
  have hr₁' := Multiset.mem_of_mem_erase hr₁
  have hroot : ∀ r ∈ H.roots, r ^ 13 = -c := fun r hr => by
    have := (mem_roots hmon.ne_zero).1 hr
    simp only [IsRoot.def, hHdef, eval_add, eval_pow, eval_X, eval_C] at this
    exact eq_neg_of_add_eq_zero_left this
  have hr₂0 : r₂ ≠ 0 := fun h0 => hH0 (by
    have := (mem_roots hmon.ne_zero).1 hr₂; rw [h0] at this; exact this)
  have hpow : (r₁ / r₂) ^ 13 = 1 := by
    rw [div_pow, hroot r₁ hr₁', hroot r₂ hr₂, div_self (neg_ne_zero.2 hc)]
  have hprim : IsPrimitiveRoot (r₁ / r₂) 13 := by
    have hord : orderOf (r₁ / r₂) ∣ 13 := orderOf_dvd_of_pow_eq_one hpow
    rcases (Nat.dvd_prime (by norm_num)).1 hord with h1 | h13
    · exact absurd (div_eq_one_iff_eq hr₂0 |>.1 (orderOf_eq_one_iff.1 h1)) hne
    · rw [← h13]; exact IsPrimitiveRoot.orderOf _
  -- lift the two roots to unit roots in `s`
  rw [← hunits] at hr₁' hr₂
  obtain ⟨y₁, hy₁, rfl⟩ := Multiset.mem_map.1 hr₁'
  obtain ⟨y₂, hy₂, rfl⟩ := Multiset.mem_map.1 hr₂
  exact ⟨y₁, (Multiset.mem_filter.1 hy₁).1, y₂, (Multiset.mem_filter.1 hy₂).1,
    (Multiset.mem_filter.1 hy₁).2, (Multiset.mem_filter.1 hy₂).2, hprim⟩

end Abstract

/-! ## The edge for the paper's family -/

open Sz8.Monodromy

/-- The coefficient `c₅₂,₇`. -/
def c52 : ℚ := 101782304398098151414464803149258684619176997680402969657344 /
  27783742160348572763840067510872319734178277

/-- Every term lies on or below the edge `7i + 13j = 455`, and exactly two lie on it. -/
theorem edge_terms : famTerms.all (fun a => 7 * a.1 + 13 * a.2.1 ≤ 455) = true ∧
    famTerms.filter (fun a => 7 * a.1 + 13 * a.2.1 == 455) = [(52, 7, c52), (65, 0, 1)] := by
  decide +kernel

theorem c52_ne_zero : c52 ≠ 0 := by decide +kernel

/-- `F(Y, τ) = Σ c τ^(455 - 7i - 13j) Y^i` (outer variable `Y`, inner `τ`). -/
noncomputable def Fτ (ts : List (ℕ × ℕ × ℚ)) : ℚ[X][X] :=
  ts.foldr (fun a acc => C (C a.2.2 * X ^ (455 - 7 * a.1 - 13 * a.2.1)) * X ^ a.1 + acc) 0

theorem Fτ_zero (ts : List (ℕ × ℕ × ℚ)) (h : ∀ a ∈ ts, 7 * a.1 + 13 * a.2.1 ≤ 455) :
    (Fτ ts).map (evalRingHom 0) =
      (ts.filter fun a => 7 * a.1 + 13 * a.2.1 == 455).foldr (fun a acc => C a.2.2 * X ^ a.1 + acc) 0 := by
  induction ts with
  | nil => simp [Fτ]
  | cons a l ih =>
    have ha := h a (List.mem_cons_self ..)
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [Fτ, List.foldr_cons] at ih' ⊢
    rw [Polynomial.map_add, ih', Polynomial.map_mul, map_C, Polynomial.map_pow, map_X]
    by_cases he : 7 * a.1 + 13 * a.2.1 = 455
    · rw [List.filter_cons_of_pos (by simpa using he), List.foldr_cons]
      simp [show 455 - 7 * a.1 - 13 * a.2.1 = 0 by omega]
    · rw [List.filter_cons_of_neg (by simpa using he)]
      simp [show 455 - 7 * a.1 - 13 * a.2.1 ≠ 0 by omega]

/-- **The reduction at `τ = 0`.** -/
theorem specialize_zero : (Fτ famTerms).map (evalRingHom 0) = X ^ 52 * (X ^ 13 + C c52) := by
  rw [Fτ_zero famTerms (by simpa using edge_terms.1), edge_terms.2]
  simp only [List.foldr_cons, List.foldr_nil, map_one, one_mul, add_zero]
  ring

/-- **Evaluation identity**: `F(τ⁷ x, τ) = τ⁴⁵⁵ f(x, t)` when `τ¹³ t = 1`. -/
theorem Fτ_eval (ts : List (ℕ × ℕ × ℚ)) (h : ∀ a ∈ ts, 7 * a.1 + 13 * a.2.1 ≤ 455)
    {K : Type*} [Field K] [Algebra ℚ K] {τ t x : K} (hτ : τ ^ 13 * t = 1) :
    (Fτ ts).eval₂ (eval₂RingHom (algebraMap ℚ K) τ) (τ ^ 7 * x) =
      τ ^ 455 * ts.foldr (fun a acc => algebraMap ℚ K a.2.2 * t ^ a.2.1 * x ^ a.1 + acc) 0 := by
  induction ts with
  | nil => simp [Fτ]
  | cons a l ih =>
    have ha := h a (List.mem_cons_self ..)
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [Fτ, List.foldr_cons] at ih' ⊢
    rw [eval₂_add, ih', eval₂_mul, eval₂_C, eval₂_X_pow, coe_eval₂RingHom, eval₂_mul, eval₂_C,
      eval₂_X_pow, mul_add]
    congr 1
    have hsplit : τ ^ 455 * t ^ a.2.1 = τ ^ (455 - 7 * a.1 - 13 * a.2.1) * τ ^ (7 * a.1) := by
      have e : 455 = (455 - 7 * a.1 - 13 * a.2.1) + 7 * a.1 + 13 * a.2.1 := by omega
      conv_lhs => rw [e, pow_add, pow_add, mul_assoc, pow_mul τ 13, ← mul_pow, hτ, one_pow, mul_one]
    rw [mul_pow, ← pow_mul]
    calc algebraMap ℚ K a.2.2 * τ ^ (455 - 7 * a.1 - 13 * a.2.1) * (τ ^ (7 * a.1) * x ^ a.1)
        = algebraMap ℚ K a.2.2 * (τ ^ (455 - 7 * a.1 - 13 * a.2.1) * τ ^ (7 * a.1)) * x ^ a.1 := by ring
      _ = τ ^ 455 * (algebraMap ℚ K a.2.2 * t ^ a.2.1 * x ^ a.1) := by rw [← hsplit]; ring

theorem Fτ_coeff (ts : List (ℕ × ℕ × ℚ)) (m : ℕ) :
    (Fτ ts).coeff m = ((ts.filter fun a => a.1 == m).map
      fun a => C a.2.2 * X ^ (455 - 7 * a.1 - 13 * a.2.1)).sum := by
  induction ts with
  | nil => simp [Fτ]
  | cons a l ih =>
    simp only [Fτ, List.foldr_cons] at ih ⊢
    rw [coeff_add, ih, coeff_C_mul_X_pow]
    by_cases h : a.1 = m
    · simp [h]
    · simp [h, Ne.symm h]

/-- **`F` is monic of degree 65 in `Y`.** -/
theorem Fτ_monic : (Fτ famTerms).Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one 65 ?_ ?_
  · refine natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    rw [Fτ_coeff]
    have hnil : famTerms.filter (fun a => a.1 == m) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      have := List.all_eq_true.1 famTerms_degree_le a ha
      simp only [decide_eq_true_eq] at this
      have hm' : 65 < m := by exact_mod_cast hm
      simp only [beq_iff_eq]; omega
    simp [hnil]
  · rw [Fτ_coeff, famTerms_top]
    simp

end Sz8.Galois.FirstEdge
