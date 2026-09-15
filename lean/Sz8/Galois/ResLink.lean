import Sz8.Galois.ResEvalCore
import Sz8.Galois.NodeM2

/-!
# The resultant identity: link from the kernel checks to Mathlib's resultant

* `Fq ∈ ℚ[t][X]` from `originalColumns`; `P_eq_Fq`: `paperMonicFamily.P z` is its specialisation.
* `eval_resultant_Fq`: `Res_X(Fq, Fq_X)(t) = res 70 (fDesc t) (dDesc t)` for every rational `t`
  — the representation and algorithm-correctness steps, proved once for all points.
* `rhsPoly = C c̃ · (t² + t + 1)^40 · S̃²` and `eval_rhsPoly`: its value is `rhsVal t`.
* `resultant_P_eq_of_evalOK`: a kernel check `evalOK t = true` at an integer point gives the
  identity `Res(P_t, P_t') = c̃ (t² + t + 1)^40 S̃(t)²` for the actual family at that point.
-/

open Polynomial

set_option maxRecDepth 100000

namespace Sz8.Galois.ResEval

open Sz8.Monodromy ResAlg NodeData NodeM2

/-! ### `Fq` -/

noncomputable def qPoly : List ℚ → ℚ[X][X]
  | [] => 0
  | a :: as => C (C a) + X * qPoly as

noncomputable def qFam : List (List ℚ) → ℚ[X][X]
  | [] => 0
  | P :: Ps => qPoly P + C X * qFam Ps

/-- `f ∈ ℚ[t][X]`. -/
noncomputable def Fq : ℚ[X][X] := qFam originalColumns

theorem map_qPoly (t : ℂ) : ∀ l : List ℚ,
    (qPoly l).map (eval₂RingHom (algebraMap ℚ ℂ) t) = complexPoly l
  | [] => by simp [qPoly, complexPoly]
  | a :: as => by simp [qPoly, complexPoly, map_qPoly t as]

theorem map_qFam (t : ℂ) : ∀ cs : List (List ℚ),
    (qFam cs).map (eval₂RingHom (algebraMap ℚ ℂ) t) = complexFamily cs t
  | [] => by simp [qFam, complexFamily]
  | P :: Ps => by simp [qFam, complexFamily, map_qPoly t P, map_qFam t Ps]

theorem P_eq_Fq (z : ℂ) : paperMonicFamily.P z = Fq.map (eval₂RingHom (algebraMap ℚ ℂ) z) := by
  show paperFamily z = _
  rw [paperFamily, Fq, map_qFam]

/-! ### Lists and polynomials -/

/-- The polynomial of an ascending coefficient list. -/
noncomputable def ofAsc : List ℚ → ℚ[X]
  | [] => 0
  | a :: as => C a + X * ofAsc as

theorem coeff_ofAsc : ∀ (l : List ℚ) (i : ℕ), (ofAsc l).coeff i = l.getD i 0
  | [], i => by simp [ofAsc]
  | a :: as, 0 => by simp [ofAsc]
  | a :: as, i + 1 => by simp [ofAsc, coeff_ofAsc as i]

theorem ofDesc_append_single : ∀ (l : List ℚ) (a : ℚ), ofDesc (l ++ [a]) = ofDesc l * X + C a
  | [], a => by simp [ofDesc]
  | b :: bs, a => by
    simp only [List.cons_append, ofDesc, List.length_append, List.length_singleton,
      ofDesc_append_single bs a]
    ring

theorem ofDesc_reverse : ∀ l : List ℚ, ofDesc l.reverse = ofAsc l
  | [] => by simp [ofDesc, ofAsc]
  | a :: as => by
    rw [List.reverse_cons, ofDesc_append_single, ofDesc_reverse as, ofAsc]
    ring

theorem ofAsc_derivAux : ∀ (k : ℕ) (l : List ℚ),
    ofAsc (derivAux k l) = C (k : ℚ) * ofAsc l + X * derivative (ofAsc l)
  | k, [] => by simp [derivAux, ofAsc]
  | k, a :: as => by
    simp only [derivAux, ofAsc, ofAsc_derivAux (k + 1) as, derivative_add, derivative_C,
      derivative_mul, derivative_X, zero_add, one_mul, C_mul]
    push_cast
    simp only [C_add, C_1]
    ring

theorem ofAsc_derivAsc (l : List ℚ) : ofAsc (derivAsc l) = derivative (ofAsc l) := by
  rcases l with _ | ⟨a, as⟩
  · simp [derivAsc, ofAsc]
  · simp only [derivAsc, ofAsc_derivAux, ofAsc, derivative_add, derivative_C, derivative_mul,
      derivative_X, zero_add, one_mul]
    simp

theorem length_derivAux : ∀ (k : ℕ) (l : List ℚ), (derivAux k l).length = l.length
  | _, [] => rfl
  | k, _ :: as => by simp [derivAux, length_derivAux (k + 1) as]

theorem stripped_reverse {l : List ℚ} (h : l.getLast? ≠ some 0) (hne : l ≠ []) :
    Stripped l.reverse := by
  obtain ⟨l', a, rfl⟩ := List.eq_nil_or_concat l |>.resolve_left hne
  simp only [List.reverse_concat', List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
    Option.some_or] at h ⊢
  show a ≠ 0
  intro ha; exact h (by rw [ha])

/-! ### The specialisation of `Fq` at a rational point -/

theorem columns_short : originalColumns.all (fun c => decide (c.length ≤ 66)) = true := by
  decide +kernel

theorem columns_top : originalColumns.map (fun c => c.getD 65 0) = [1, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem eval_coeff_qFam (t : ℚ) : ∀ (cs : List (List ℚ)) (i : ℕ),
    ((qFam cs).coeff i).eval t = cs.foldr (fun col acc => col.getD i 0 + t * acc) 0
  | [], i => by simp [qFam]
  | P :: Ps, i => by
    have hP : ∀ (l : List ℚ) (i : ℕ), (qPoly l).coeff i = C (l.getD i 0) := by
      intro l
      induction l with
      | nil => intro i; simp [qPoly]
      | cons a as ih =>
        intro i
        rcases i with _ | i
        · simp [qPoly]
        · simp [qPoly, ih i]
    simp [qFam, hP, coeff_C_mul, eval_coeff_qFam t Ps i]

theorem foldr_eq_zero (t : ℚ) {i : ℕ} (hi : 66 ≤ i) : ∀ cs : List (List ℚ),
    cs.all (fun c => decide (c.length ≤ 66)) = true →
      cs.foldr (fun col acc => col.getD i 0 + t * acc) 0 = 0
  | [], _ => rfl
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.foldr_cons, foldr_eq_zero t hi cs h.2]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

theorem colCoeff_eq_zero (t : ℚ) {i : ℕ} (hi : 66 ≤ i) : colCoeff t i = 0 :=
  foldr_eq_zero t hi _ columns_short

theorem map_Fq_eval (t : ℚ) : Fq.map (evalRingHom t) = ofAsc (fAsc t) := by
  ext i
  rw [coeff_map, coe_evalRingHom, Fq, eval_coeff_qFam, coeff_ofAsc, fAsc]
  rcases lt_or_ge i 66 with hi | hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by simpa using hi)]
    exact colCoeff_eq_zero t hi

theorem colCoeff_65 (t : ℚ) : colCoeff t 65 = 1 := by
  have h := congrArg (fun l => l.foldr (fun a acc => a + t * acc) (0 : ℚ)) columns_top
  simp only [List.foldr_map] at h
  simpa [colCoeff] using h

theorem fAsc_natDegree (t : ℚ) : (ofAsc (fAsc t)).natDegree = 65 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_ofAsc, fAsc, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (by simp; exact_mod_cast hi)]
    rfl
  · rw [coeff_ofAsc, fAsc, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by norm_num)]
    simp [colCoeff_65]

theorem fDesc_stripped (t : ℚ) : Stripped (fDesc t) := by
  have h65 : (fAsc t).getLast? = some 1 := by
    rw [List.getLast?_eq_getElem?, fAsc, List.length_map, List.length_range, List.getElem?_map,
      List.getElem?_range (by norm_num)]
    simp [colCoeff_65]
  exact stripped_reverse (by rw [h65]; simp) (by simp [fAsc])

theorem ofDesc_fDesc (t : ℚ) : ofDesc (fDesc t) = ofAsc (fAsc t) := ofDesc_reverse _

theorem ofDesc_dDesc (t : ℚ) : ofDesc (dDesc t) = derivative (ofAsc (fAsc t)) := by
  rw [dDesc, ofDesc_reverse, ofAsc_derivAsc]

theorem getLast?_eq_coeff : ∀ {l : List ℚ}, l ≠ [] →
    l.getLast? = some ((ofAsc l).coeff (l.length - 1)) := by
  intro l hl
  rw [coeff_ofAsc, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rcases l with _ | _ <;> simp_all)]
  rfl

theorem dDesc_stripped (t : ℚ) : Stripped (dDesc t) := by
  have hlen : (derivAsc (fAsc t)).length = 65 := by
    simp [derivAsc, fAsc, List.range_succ_eq_map, length_derivAux]
  have hne : derivAsc (fAsc t) ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  have hlast : (derivAsc (fAsc t)).getLast? = some 65 := by
    rw [getLast?_eq_coeff hne, hlen, ofAsc_derivAsc, coeff_derivative, coeff_ofAsc, fAsc,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by norm_num)]
    simp only [Option.map_some, Option.getD_some]
    norm_num [colCoeff_65]
  exact stripped_reverse (by rw [hlast]; simp) hne

/-- **Representation and correctness, for every rational point.** -/
theorem eval_resultant_Fq (t : ℚ) :
    (resultant Fq (derivative Fq) 65 64).eval t = res 70 (fDesc t) (dDesc t) := by
  rw [← coe_evalRingHom, ← resultant_map_map, ← derivative_map, map_Fq_eval,
    res_eq 70 _ _ (fDesc_stripped t) (dDesc_stripped t) (by
      simp [dDesc, derivAsc, fAsc, List.range_succ_eq_map, length_derivAux]),
    ofDesc_fDesc, ofDesc_dDesc]
  rw [show resultant (ofAsc (fAsc t)) (derivative (ofAsc (fAsc t)))
      = resultant (ofAsc (fAsc t)) (derivative (ofAsc (fAsc t))) 65 64 by
    rw [natDegree_derivative, fAsc_natDegree]]

/-! ### The candidate -/

/-- `c̃ · (t² + t + 1)^40 · S̃²`. -/
noncomputable def rhsPoly : ℚ[X] :=
  C ctil * (X ^ 2 + X + 1) ^ 40 * (Stil.map (Int.castRingHom ℚ)) ^ 2

theorem eval_horner (x : ℚ) : ∀ (l : List ℤ) , horner (l.map fun a : ℤ => (a : ℚ)) x
    = ∑ i ∈ Finset.range l.length, (l.getD i 0 : ℚ) * x ^ i
  | [] => by simp [horner]
  | a :: as => by
    rw [List.map_cons, horner, List.foldr_cons, ← horner, eval_horner x as, List.length_cons,
      Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]; congr 1
    refine Finset.sum_congr rfl fun i _ => by ring

theorem eval_rhsPoly (t : ℚ) : rhsPoly.eval t = rhsVal t := by
  have hS : (Stil.map (Int.castRingHom ℚ)).eval t = horner (Slist.map fun a : ℤ => (a : ℚ)) t := by
    rw [eval_horner, Stil, Polynomial.map_sum, eval_finset_sum]
    simp
  simp only [rhsPoly, rhsVal, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one, hS]
  ring

/-! ### One point, end to end -/

theorem resultant_P_eq_of_evalOK {t : ℚ} (h : evalOK t = true) :
    resultant (paperMonicFamily.P t) (derivative (paperMonicFamily.P t))
      = (ctil : ℂ) * ((t : ℂ) ^ 2 + t + 1) ^ 40 * ((Stil.map (Int.castRingHom ℂ)).eval (t : ℂ)) ^ 2 := by
  have hv : (resultant Fq (derivative Fq) 65 64).eval t = rhsPoly.eval t := by
    rw [eval_resultant_Fq, eval_rhsPoly]
    simpa [evalOK] using h
  have hdeg : (paperMonicFamily.P t).natDegree = 65 := paperMonicFamily.natDegree_eq t
  rw [show resultant (paperMonicFamily.P t) (derivative (paperMonicFamily.P t))
      = resultant (paperMonicFamily.P t) (derivative (paperMonicFamily.P t)) 65 64 by
    rw [natDegree_derivative, hdeg], P_eq_Fq, derivative_map, resultant_map_map]
  have e1 : ∀ p : ℚ[X], (eval₂RingHom (algebraMap ℚ ℂ) (t : ℂ)) p = algebraMap ℚ ℂ (p.eval t) := by
    intro p
    rw [coe_eval₂RingHom, ← eval₂_at_apply]; rfl
  rw [e1, hv, ← e1]
  have hS : eval₂ (algebraMap ℚ ℂ) (t : ℂ) (Stil.map (Int.castRingHom ℚ))
      = (Stil.map (Int.castRingHom ℂ)).eval (t : ℂ) := by
    rw [eval₂_map, eval_map]
    congr 1
  simp only [rhsPoly, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_pow, eval₂_add, eval₂_X,
    eval₂_one, hS]
  rfl

end Sz8.Galois.ResEval
