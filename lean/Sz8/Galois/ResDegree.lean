import Sz8.Galois.ResLink
import Sz8.Galois.ResDegreeData

/-!
# The resultant identity: degree bound and interpolation

* `natDegree_det_le`: if every nonzero entry of a square polynomial matrix satisfies
  `deg M i j ≤ u i + v j`, then `deg det M ≤ ∑ u + ∑ v`.
* `natDegree_resultant_Fq`: with the integer potentials of `ResDegreeData` (the assignment
  certificate, checked in the kernel on Mathlib's own Sylvester layout), `deg_t Res_X(f, f_X) ≤ 812`.
* `natDegree_rhsPoly`: the candidate `c̃ q^40 S̃²` has degree `≤ 764`.
* `identity_of_evals`: equality at the 813 integer points `-406, …, 406` (kernel checks
  `evalOK`) gives `Res_X(f, f_X) = c̃ q^40 S̃²` in `ℚ[t]`, and `resultant_P_identity` specialises it
  to every complex `t`.
-/

open Polynomial

set_option maxRecDepth 100000

namespace Sz8.Galois.ResEval

open Sz8.Monodromy ResAlg NodeData NodeM2 ResDegreeData

/-! ### Kernel checks -/

def entryOK (i j : ℕ) : Bool :=
  if j < 65 then
    (if j ≤ i ∧ i ≤ j + 64 then decide ((dF.getD (i - j + 1) 0 : ℤ) ≤ uP.getD i 0 + vP.getD j 0)
      else true)
  else
    (if j - 65 ≤ i ∧ i ≤ j - 65 + 65 then
      decide ((dF.getD (i - (j - 65)) 0 : ℤ) ≤ uP.getD i 0 + vP.getD j 0) else true)

def degCheck : Bool := (List.range 129).all fun i => (List.range 129).all fun j => entryOK i j

theorem deg_ok : degCheck = true := by decide +kernel

theorem sum_ok : uP.sum + vP.sum = 812 ∧ uP.length = 129 ∧ vP.length = 129 := by decide +kernel

def dFCheck : Bool :=
  (List.range 66).all fun k => (List.range 8).all fun j =>
    !decide (dF.getD k 0 < j) || ((originalColumns.getD j []).getD k 0 == 0)

theorem dF_ok : dFCheck = true := by decide +kernel

theorem columns_length : originalColumns.length = 8 := by decide +kernel

/-! ### Coefficient degrees of `Fq` -/

theorem coeff_coeff_qFam : ∀ (cs : List (List ℚ)) (k j : ℕ),
    ((qFam cs).coeff k).coeff j = (cs.getD j []).getD k 0
  | [], k, j => by simp [qFam]
  | P :: Ps, k, j => by
    have hP : ∀ (l : List ℚ) (i : ℕ), (qPoly l).coeff i = C (l.getD i 0) := by
      intro l
      induction l with
      | nil => intro i; simp [qPoly]
      | cons a as ih =>
        intro i
        rcases i with _ | i
        · simp [qPoly]
        · simp [qPoly, ih i]
    rcases j with _ | j
    · simp [qFam, hP, coeff_C_mul, coeff_C]
    · simp [qFam, hP, coeff_C_mul, coeff_C, coeff_coeff_qFam Ps k j]

theorem natDegree_Fq_coeff (k : ℕ) : (Fq.coeff k).natDegree ≤ dF.getD k 0 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  have hj' : dF.getD k 0 < j := by exact_mod_cast hj
  rw [Fq, coeff_coeff_qFam]
  rcases lt_or_ge j 8 with hj8 | hj8
  · have hjl : j < originalColumns.length := by rw [columns_length]; exact hj8
    rcases lt_or_ge k 66 with hk | hk
    · have h := List.all_eq_true.1 (List.all_eq_true.1 dF_ok k (List.mem_range.2 hk)) j
        (List.mem_range.2 hj8)
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt,
        beq_iff_eq] at h
      rcases h with h | h
      · omega
      · exact h
    · have hmem : originalColumns.getD j [] ∈ originalColumns := by
        rw [List.getD_eq_getElem (hn := hjl)]; exact List.getElem_mem _
      have hshort := List.all_eq_true.1 columns_short _ hmem
      simp only [decide_eq_true_eq] at hshort
      rw [List.getD_eq_getElem?_getD (l := originalColumns.getD j []),
        List.getElem?_eq_none (by omega)]
      rfl
  · rw [List.getD_eq_default (l := originalColumns) (hn := by rw [columns_length]; exact hj8)]; simp

theorem natDegree_derivative_Fq_coeff (k : ℕ) :
    ((derivative Fq).coeff k).natDegree ≤ dF.getD (k + 1) 0 := by
  rw [coeff_derivative]
  refine natDegree_mul_le.trans ?_
  have : ((k : ℚ[X]) + 1).natDegree = 0 := by
    rw [show ((k : ℚ[X]) + 1) = C ((k : ℚ) + 1) by simp]; exact natDegree_C _
  rw [this, add_zero]
  exact natDegree_Fq_coeff (k + 1)

/-! ### Determinant degree bound -/

theorem natDegree_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ[X]) (u v : Fin n → ℤ) (B : ℕ)
    (hsum : ∑ i, u i + ∑ j, v j = B)
    (h : ∀ i j, M i j ≠ 0 → ((M i j).natDegree : ℤ) ≤ u i + v j) : M.det.natDegree ≤ B := by
  classical
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => (natDegree_smul_le _ _).trans ?_
  by_cases hz : ∃ i, M (σ i) i = 0
  · obtain ⟨i, hi⟩ := hz
    have h0 : ∏ i, M (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [h0, natDegree_zero]; exact Nat.zero_le _
  · push_neg at hz
    refine (natDegree_prod_le (s := Finset.univ) (f := fun i => M (σ i) i)).trans ?_
    have hle : ∀ i ∈ Finset.univ, (((M (σ i) i).natDegree : ℕ) : ℤ) ≤ u (σ i) + v i :=
      fun i _ => h _ _ (hz i)
    have := Finset.sum_le_sum hle
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ u, hsum] at this
    exact_mod_cast (show ((∑ i, (M (σ i) i).natDegree : ℕ) : ℤ) ≤ B by push_cast; exact this)

theorem sum_getD (l : List ℤ) : ∑ i ∈ Finset.range l.length, l.getD i 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a as ih => rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, ← ih]; simp [add_comm]

/-- **Degree bound.** `deg_t Res_X(f, f_X) ≤ 812`. -/
theorem natDegree_resultant_Fq : (resultant Fq (derivative Fq) 65 64).natDegree ≤ 812 := by
  obtain ⟨hs, hu, hv⟩ := sum_ok
  refine natDegree_det_le _ (fun i => uP.getD i 0) (fun j => vP.getD j 0) 812 ?_ ?_
  · rw [Fin.sum_univ_eq_sum_range (fun i => uP.getD i 0), Fin.sum_univ_eq_sum_range (fun j => vP.getD j 0),
      show (65 + 64 : ℕ) = uP.length by rw [hu], sum_getD, hu, ← hv, sum_getD]
    exact_mod_cast hs
  · intro i j hne
    have hij := List.all_eq_true.1 (List.all_eq_true.1 deg_ok i (List.mem_range.2 i.2)) j
      (List.mem_range.2 j.2)
    simp only [sylvester, Matrix.of_apply] at hne ⊢
    induction j using Fin.addCases with
    | left j =>
      simp only [Fin.addCases_left] at hne ⊢
      split_ifs at hne with hc
      · simp only [Set.mem_Icc] at hc
        simp only [entryOK, Fin.val_castAdd, j.2, if_true, hc, and_self, decide_eq_true_eq] at hij
        rw [if_pos (Set.mem_Icc.2 hc)]
        have h1 := natDegree_derivative_Fq_coeff ((i : ℕ) - j)
        simp only [Fin.val_castAdd]
        have h2 : (((derivative Fq).coeff ((i : ℕ) - j)).natDegree : ℤ) ≤ (dF.getD ((i : ℕ) - j + 1) 0 : ℤ) := by
          exact_mod_cast h1
        exact le_trans h2 hij
      · exact absurd rfl hne
    | right j =>
      simp only [Fin.addCases_right] at hne ⊢
      split_ifs at hne with hc
      · simp only [Set.mem_Icc] at hc
        simp only [entryOK, Fin.val_natAdd, show ¬ 65 + (j : ℕ) < 65 by omega, if_false,
          show 65 + (j : ℕ) - 65 = j by omega] at hij
        rw [if_pos ⟨by omega, by omega⟩] at hij
        simp only [decide_eq_true_eq] at hij
        rw [if_pos (Set.mem_Icc.2 hc)]
        have h1 := natDegree_Fq_coeff ((i : ℕ) - j)
        simp only [Fin.val_natAdd]
        have h2 : ((Fq.coeff ((i : ℕ) - j)).natDegree : ℤ) ≤ (dF.getD ((i : ℕ) - j) 0 : ℤ) := by
          exact_mod_cast h1
        exact le_trans h2 hij
      · exact absurd rfl hne

/-! ### The candidate and interpolation -/

theorem natDegree_Stil_map : (Stil.map (Int.castRingHom ℚ)).natDegree ≤ 342 :=
  natDegree_map_le.trans Stil_natDegree.le

theorem natDegree_rhsPoly : rhsPoly.natDegree ≤ 764 := by
  unfold rhsPoly
  refine natDegree_mul_le.trans ?_
  have h1 : (C ctil * (X ^ 2 + X + 1 : ℚ[X]) ^ 40).natDegree ≤ 80 := by
    refine natDegree_mul_le.trans ?_
    rw [natDegree_C, zero_add]
    refine natDegree_pow_le.trans ?_
    have : (X ^ 2 + X + 1 : ℚ[X]).natDegree ≤ 2 := by compute_degree
    omega
  have h2 : ((Stil.map (Int.castRingHom ℚ)) ^ 2).natDegree ≤ 684 :=
    natDegree_pow_le.trans (by have := natDegree_Stil_map; omega)
  omega

/-- **Interpolation.** Agreement at the 813 integer points gives the identity in `ℚ[t]`. -/
theorem identity_of_evals (hall : ∀ k : ℕ, k < 813 → evalOK ((k : ℚ) - 406) = true) :
    resultant Fq (derivative Fq) 65 64 = rhsPoly := by
  have hE : (resultant Fq (derivative Fq) 65 64 - rhsPoly).natDegree < Fintype.card (Fin 813) := by
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt (natDegree_sub_le _ _)
      (max_lt (lt_of_le_of_lt natDegree_resultant_Fq (by norm_num))
        (lt_of_le_of_lt natDegree_rhsPoly (by norm_num)))
  refine sub_eq_zero.1 (eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
    (f := fun i : Fin 813 => ((i : ℕ) : ℚ) - 406) (fun a b hab => Fin.ext (by
      simp only [sub_left_inj, Nat.cast_inj] at hab; exact hab)) (fun i => ?_) hE)
  rw [eval_sub, eval_resultant_Fq, eval_rhsPoly, sub_eq_zero]
  have := hall i.val i.isLt
  simpa [evalOK] using this

/-- **The identity for the actual family.** -/
theorem resultant_P_identity (hall : ∀ k : ℕ, k < 813 → evalOK ((k : ℚ) - 406) = true) (z : ℂ) :
    resultant (paperMonicFamily.P z) (derivative (paperMonicFamily.P z))
      = (ctil : ℂ) * (z ^ 2 + z + 1) ^ 40 * ((Stil.map (Int.castRingHom ℂ)).eval z) ^ 2 := by
  have hdeg : (paperMonicFamily.P z).natDegree = 65 := paperMonicFamily.natDegree_eq z
  rw [show resultant (paperMonicFamily.P z) (derivative (paperMonicFamily.P z))
      = resultant (paperMonicFamily.P z) (derivative (paperMonicFamily.P z)) 65 64 by
    rw [natDegree_derivative, hdeg], P_eq_Fq, derivative_map, resultant_map_map,
    identity_of_evals hall]
  have hS : eval₂ (algebraMap ℚ ℂ) z (Stil.map (Int.castRingHom ℚ))
      = (Stil.map (Int.castRingHom ℂ)).eval z := by
    rw [eval₂_map, eval_map]
    congr 1
  simp only [rhsPoly, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_pow, eval₂_add, eval₂_X,
    eval₂_one, hS]
  rfl

end Sz8.Galois.ResEval
