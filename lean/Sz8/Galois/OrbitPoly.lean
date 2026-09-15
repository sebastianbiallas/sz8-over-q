import Sz8.Galois.Orbit
import Sz8.Galois.PolyGrowth

/-!
# (O), second checkpoint: the orbit polynomial has polynomial coefficients

* `norm_coeff_prod_le` — `‖coeff_k ∏ (Z - aₕ)‖ ≤ ∏ (1 + ‖aₕ‖)`, for every `k`;
* `norm_orbitCoeff_le` — hence every orbit coefficient is at most `(1 + C_c R)^m` where the roots
  are bounded by `R` (`m = |M|`, `C_c = Σ ‖cₓ‖`, both symbolic);
* `exists_growth` — for polynomial coefficients, `‖orbitCoeff_k t‖ ≤ K ‖t‖^(m D)` for `‖t‖ ≥ 1`;
* `exists_orbitCoeff_poly` — Lemma L: each coefficient agrees with a polynomial on the regular locus;
* `orbitPhi`, `orbitPhi_spec` — `Φ ∈ ℂ[t][Z]` whose specialization at every regular `t` is the
  orbit polynomial.
-/

open Polynomial Topology Filter Metric Set

namespace Sz8.Galois.OrbitPoly

open Sz8.Monodromy Sz8.Monodromy.MonicFamily Germs Orbit

theorem norm_coeff_prod_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    ∀ k, ‖(∏ i ∈ s, (X - C (a i))).coeff k‖ ≤ ∏ i ∈ s, (1 + ‖a i‖) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro k
    simp only [Finset.prod_empty, coeff_one]
    split_ifs <;> simp
  | insert j s hj ih =>
    intro k
    have hB : 0 ≤ ∏ i ∈ s, (1 + ‖a i‖) := Finset.prod_nonneg fun i _ => by positivity
    rw [Finset.prod_insert hj, Finset.prod_insert hj, mul_comm (X - C _), mul_comm (1 + _)]
    cases k with
    | zero =>
      rw [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, norm_mul, norm_neg]
      nlinarith [ih 0, norm_nonneg (a j), norm_nonneg ((∏ i ∈ s, (X - C (a i))).coeff 0)]
    | succ k =>
      rw [coeff_mul_X_sub_C]
      calc ‖(∏ i ∈ s, (X - C (a i))).coeff k - (∏ i ∈ s, (X - C (a i))).coeff (k + 1) * a j‖
          ≤ ‖(∏ i ∈ s, (X - C (a i))).coeff k‖ + ‖(∏ i ∈ s, (X - C (a i))).coeff (k + 1)‖ * ‖a j‖ := by
            rw [← norm_mul]; exact norm_sub_le _ _
        _ ≤ (∏ i ∈ s, (1 + ‖a i‖)) + (∏ i ∈ s, (1 + ‖a i‖)) * ‖a j‖ := by
            gcongr
            · exact ih k
            · exact ih (k + 1)
        _ = (∏ i ∈ s, (1 + ‖a i‖)) * (1 + ‖a j‖) := by ring

/-- Cauchy's bound, pointwise. -/
theorem root_norm_le (M : MonicFamily) {t x : ℂ} (hx : (M.P t).eval x = 0) :
    ‖x‖ ≤ ∑ i ∈ Finset.range M.n, ‖(M.P t).coeff i‖ + 1 := by
  have hroot := IsRoot.norm_lt_cauchyBound (M.monic t).ne_zero hx
  have hbound : (cauchyBound (M.P t) : ℝ) ≤ ∑ i ∈ Finset.range M.n, ‖(M.P t).coeff i‖ + 1 := by
    rw [cauchyBound, (M.monic t).leadingCoeff, nnnorm_one, div_one, M.natDegree_eq]
    have hsup : ((Finset.range M.n).sup fun i => ‖(M.P t).coeff i‖₊) ≤
        ∑ i ∈ Finset.range M.n, ‖(M.P t).coeff i‖₊ :=
      Finset.sup_le fun i hi => Finset.single_le_sum (f := fun i => ‖(M.P t).coeff i‖₊)
        (fun _ _ => zero_le) hi
    have : (((Finset.range M.n).sup fun i => ‖(M.P t).coeff i‖₊ : NNReal) : ℝ) ≤
        ∑ i ∈ Finset.range M.n, ‖(M.P t).coeff i‖ := by
      have := NNReal.coe_le_coe.mpr hsup
      simpa [NNReal.coe_sum] using this
    push_cast
    linarith
  have : ‖x‖ < (cauchyBound (M.P t) : ℝ) := by exact_mod_cast hroot
  linarith

variable {M : MonicFamily} {b : M.Base}

/-- **The product estimate for orbit coefficients.** -/
theorem norm_orbitCoeff_le (c : M.Fiber b → ℂ) (k : ℕ) {t : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hroots : ∀ x, (M.P t).eval x = 0 → ‖x‖ ≤ R) :
    ‖orbitCoeff M b c k t‖ ≤ (1 + (∑ x, ‖c x‖) * R) ^ Fintype.card (Mon M b) := by
  have h1 : 1 ≤ (1 + (∑ x, ‖c x‖) * R) ^ Fintype.card (Mon M b) :=
    one_le_pow₀ (by have := Finset.sum_nonneg fun x (_ : x ∈ Finset.univ) => norm_nonneg (c x); nlinarith)
  unfold orbitCoeff
  split_ifs with ht
  · unfold orbitPoly
    split_ifs with hp
    · unfold orbitPolyOf
      refine (norm_coeff_prod_le _ _ k).trans ?_
      rw [← Finset.card_univ, ← Finset.prod_const]
      refine Finset.prod_le_prod (fun h _ => by positivity) fun h _ => ?_
      gcongr
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [norm_mul]
      gcongr
      exact hroots _ (by
        have := (Fiber.isRoot (t := ⟨t, ht⟩) (M.isCoveringMap.monodromy
          (Path.Homotopic.Quotient.mk hp.some) (h.1 x)))
        simpa using this)
    · simp only [coeff_one]
      split_ifs <;> simp [h1, zero_le_one.trans h1]
  · simp [zero_le_one.trans h1]

omit b in
theorem norm_eval_le (p : ℂ[X]) {t : ℂ} (ht : 1 ≤ ‖t‖) :
    ‖p.eval t‖ ≤ (∑ j ∈ Finset.range (p.natDegree + 1), ‖p.coeff j‖) * ‖t‖ ^ p.natDegree := by
  rw [eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) (norm_nonneg _)

omit b in
/-- Roots grow at most polynomially. -/
theorem exists_root_growth (Fpol : ℂ[X][X]) (hF : ∀ t, M.P t = Fpol.map (evalRingHom t)) :
    ∃ D : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℂ, 1 ≤ ‖t‖ → ∀ x, (M.P t).eval x = 0 → ‖x‖ ≤ A * ‖t‖ ^ D := by
  set d : ℕ → ℕ := fun i => (Fpol.coeff i).natDegree
  set K : ℕ → ℝ := fun i => ∑ j ∈ Finset.range (d i + 1), ‖(Fpol.coeff i).coeff j‖
  set D := ∑ i ∈ Finset.range M.n, d i
  have hK : ∀ i, 0 ≤ K i := fun i => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨D, ∑ i ∈ Finset.range M.n, K i + 1, by positivity, fun t ht x hx => ?_⟩
  have htD : 1 ≤ ‖t‖ ^ D := one_le_pow₀ ht
  have hc : ∀ i ∈ Finset.range M.n, ‖(M.P t).coeff i‖ ≤ K i * ‖t‖ ^ D := by
    intro i hi
    rw [hF, coeff_map, coe_evalRingHom]
    refine (norm_eval_le _ ht).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht ?_) (hK i))
    exact Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) hi
  calc ‖x‖ ≤ ∑ i ∈ Finset.range M.n, ‖(M.P t).coeff i‖ + 1 := root_norm_le M hx
    _ ≤ ∑ i ∈ Finset.range M.n, K i * ‖t‖ ^ D + ‖t‖ ^ D := by gcongr with i hi; exact hc i hi
    _ = (∑ i ∈ Finset.range M.n, K i + 1) * ‖t‖ ^ D := by rw [add_mul, Finset.sum_mul, one_mul]

/-- **Lemma L applied**: every orbit coefficient is a polynomial on the regular locus. -/
theorem exists_orbitCoeff_poly (Fpol : ℂ[X][X]) (hF : ∀ t, M.P t = Fpol.map (evalRingHom t))
    (c : M.Fiber b → ℂ) (k : ℕ) :
    ∃ p : ℂ[X], ∀ t ∈ M.regular, orbitCoeff M b c k t = p.eval t := by
  classical
  have hfin := regular_compl_finite M b Fpol hF
  set S := hfin.toFinset
  have hS : ∀ z, z ∉ S ↔ z ∈ M.regular := fun z => by simp [S]
  set m := Fintype.card (Mon M b)
  set Cc := ∑ x, ‖c x‖
  have hCc : 0 ≤ Cc := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hd : DifferentiableOn ℂ (orbitCoeff M b c k) (↑S)ᶜ := by
    have : ((↑S)ᶜ : Set ℂ) = M.regular := by ext z; simpa using hS z
    rw [this]
    exact (orbitCoeff_analyticOnNhd M b Fpol hF c k).differentiableOn
  have hb : ∀ s ∈ S, ∃ ε > 0, ∃ B : ℝ, ∀ z ∈ ball s ε, z ∉ S → ‖orbitCoeff M b c k z‖ ≤ B := by
    intro s _
    obtain ⟨C₀, hC₀⟩ := M.exists_root_bound (isCompact_closedBall s 1)
    refine ⟨1, one_pos, _, fun z hz _ => norm_orbitCoeff_le c k (le_max_right C₀ 0)
      fun x hx => (hC₀ z (ball_subset_closedBall hz) x hx).trans (le_max_left _ _)⟩
  obtain ⟨D, A, hA, hgrowth⟩ := exists_root_growth Fpol hF
  have hg : ∀ z : ℂ, 1 ≤ ‖z‖ → z ∉ S →
      ‖orbitCoeff M b c k z‖ ≤ (1 + Cc * A) ^ m * ‖z‖ ^ (D * m) := by
    intro z hz _
    have hzD : 1 ≤ ‖z‖ ^ D := one_le_pow₀ hz
    refine (norm_orbitCoeff_le c k (by positivity) (hgrowth z hz)).trans ?_
    rw [pow_mul, ← mul_pow]
    gcongr
    nlinarith [mul_nonneg hCc hA]
  obtain ⟨p, -, hp⟩ := Sz8.Galois.PolyGrowth.eq_polynomial_of_growth hd hb hg
  exact ⟨p, fun t ht => hp t ((hS t).2 ht)⟩

variable (M b) in
/-- The assembled orbit polynomial `Φ ∈ ℂ[t][Z]`. -/
noncomputable def orbitPhi (Fpol : ℂ[X][X]) (hF : ∀ t, M.P t = Fpol.map (evalRingHom t))
    (c : M.Fiber b → ℂ) : ℂ[X][X] :=
  ∑ k ∈ Finset.range (Fintype.card (Mon M b) + 1),
    C (exists_orbitCoeff_poly Fpol hF c k).choose * X ^ k

theorem natDegree_orbitPoly_le (c : M.Fiber b → ℂ) (t : M.Base) :
    (orbitPoly M b c t).natDegree ≤ Fintype.card (Mon M b) := by
  unfold orbitPoly
  split_ifs
  · unfold orbitPolyOf
    rw [natDegree_prod_of_monic _ _ fun h _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, le_refl]
  · simp

/-- **Specialization identity.** -/
theorem orbitPhi_spec (Fpol : ℂ[X][X]) (hF : ∀ t, M.P t = Fpol.map (evalRingHom t))
    (c : M.Fiber b → ℂ) (t : ℂ) (ht : t ∈ M.regular) :
    (orbitPhi M b Fpol hF c).map (evalRingHom t) = orbitPoly M b c ⟨t, ht⟩ := by
  classical
  ext k
  rw [coeff_map, orbitPhi, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rw [coe_evalRingHom, ← (exists_orbitCoeff_poly Fpol hF c k).choose_spec t ht, orbitCoeff,
      dif_pos ht]
  · rw [map_zero, coeff_eq_zero_of_natDegree_lt]
    exact (natDegree_orbitPoly_le c _).trans_lt (by simpa using hk)

end Sz8.Galois.OrbitPoly
