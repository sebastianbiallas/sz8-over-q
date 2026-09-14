import Sz8.Galois.Loops
import Sz8.Galois.PolyIndex
import Sz8.Galois.Retract
import Sz8.Galois.VanKampen
import Sz8.Galois.Circuit

/-!
# The two recorded polylines generate `π₁(ℂ ∖ {ζ₃, ζ₃²})`
-/

open Complex Sz8.Monodromy Sz8.Monodromy.GaussPoly Sz8.Galois.Loops Sz8.Galois.PolyIndex

namespace Sz8.Galois.TwoPunctures

/-- `ζ₃` (`up`) and `ζ₃²` (not `up`). -/
noncomputable def pz (up : Bool) : ℂ := ⟨-1 / 2, if up then Real.sqrt 3 / 2 else -(Real.sqrt 3 / 2)⟩

/-- Vertex `i` of a recorded waypoint list, as a complex number. -/
noncomputable def P (l : List (ℤ × ℤ)) (i : ℕ) : ℂ := ptC 40 (l.getD i (0, 0))

/-- The same vertex, translated so that the puncture is at the origin. -/
noncomputable def W (up : Bool) (l : List (ℤ × ℤ)) (i : ℕ) : ℂ := P l i - pz up

theorem P_re (l : List (ℤ × ℤ)) (i : ℕ) : (P l i).re = ((l.getD i (0, 0)).1 : ℝ) / 2 ^ 40 := by
  rw [P, Circuit.ptC_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]; ring

theorem P_im (l : List (ℤ × ℤ)) (i : ℕ) : (P l i).im = ((l.getD i (0, 0)).2 : ℝ) / 2 ^ 40 := by
  rw [P, Circuit.ptC_eq]
  simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]; ring

theorem W_re (up l i) : (W up l i).re = ((l.getD i (0, 0)).1 : ℝ) / 2 ^ 40 + 1 / 2 := by
  simp only [W, Complex.sub_re, P_re, pz]; ring

theorem W_im (up l i) : (W up l i).im =
    ((l.getD i (0, 0)).2 : ℝ) / 2 ^ 40 - (if up then Real.sqrt 3 / 2 else -(Real.sqrt 3 / 2)) := by
  simp [W, P_im, pz]

theorem W_im_pos {up l i} (h : imPosB up (l.getD i (0, 0)) = true) : 0 < (W up l i).im := by
  rw [W_im]
  cases up
  · simp only [imPosB, decide_eq_true_eq, Bool.false_eq_true, ite_false] at h ⊢
    rcases h with h | h
    · have : (0 : ℝ) ≤ ((l.getD i (0, 0)).2 : ℝ) / 2 ^ 40 := by
        have : (0 : ℝ) ≤ ((l.getD i (0, 0)).2 : ℝ) := by exact_mod_cast h
        positivity
      have : 0 < Real.sqrt 3 := by positivity
      linarith
    · have := Circuit.lt_sqrt3_half (y := -(l.getD i (0, 0)).2) (Or.inr (by nlinarith))
      push_cast at this; linarith
  · simp only [imPosB, decide_eq_true_eq, ite_true] at h ⊢
    linarith [Circuit.sqrt3_half_lt h.1 h.2]

theorem W_im_neg {up l i} (h : imNegB up (l.getD i (0, 0)) = true) : (W up l i).im < 0 := by
  rw [W_im]
  cases up
  · simp only [imNegB, decide_eq_true_eq, Bool.false_eq_true, ite_false] at h ⊢
    have := Circuit.sqrt3_half_lt (y := -(l.getD i (0, 0)).2) (by omega) (by nlinarith)
    push_cast at this; linarith
  · simp only [imNegB, decide_eq_true_eq, ite_true] at h ⊢
    linarith [Circuit.lt_sqrt3_half h]

theorem W_re_pos {up l i} (h : rePosB (l.getD i (0, 0)) = true) : 0 < (W up l i).re := by
  simp only [rePosB, decide_eq_true_eq] at h
  have h' : (0 : ℝ) < 2 * ((l.getD i (0, 0)).1 : ℝ) + 2 ^ 40 := by exact_mod_cast h
  rw [W_re]; linarith

theorem W_re_neg {up l i} (h : reNegB (l.getD i (0, 0)) = true) : (W up l i).re < 0 := by
  simp only [reNegB, decide_eq_true_eq] at h
  have h' : 2 * ((l.getD i (0, 0)).1 : ℝ) + 2 ^ 40 < 0 := by exact_mod_cast h
  rw [W_re]; linarith

/-! ### Segments of a certified loop -/

theorem seg_slit {up : Bool} {l : List (ℤ × ℤ)} {k : ℕ}
    (h : slitB up (fun i => l.getD i (0, 0)) k = true) (u : unitInterval) :
    seg (W up l) k u ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  simp only [slitB, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩
  · have := Circuit.pos_between (W_im_pos ha) (W_im_pos hb) u.2.1 u.2.2
    exact Or.inr (by rw [Circuit.seg_im]; exact this.ne')
  · have := Circuit.neg_between (W_im_neg ha) (W_im_neg hb) u.2.1 u.2.2
    exact Or.inr (by rw [Circuit.seg_im]; exact this.ne)
  · have := Circuit.pos_between (W_re_pos (up := up) ha) (W_re_pos (up := up) hb) u.2.1 u.2.2
    exact Or.inl (by rw [Circuit.seg_re]; exact this)

theorem seg_negSlit {up : Bool} {l : List (ℤ × ℤ)} {k : ℕ}
    (h : negSlitB up (fun i => l.getD i (0, 0)) k = true) (u : unitInterval) :
    -seg (W up l) k u ∈ slitPlane := by
  rw [mem_slitPlane_iff, Complex.neg_re, Complex.neg_im]
  simp only [negSlitB, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩
  · have := Circuit.pos_between (W_im_pos ha) (W_im_pos hb) u.2.1 u.2.2
    exact Or.inr (by rw [Circuit.seg_im]; exact neg_ne_zero.2 this.ne')
  · have := Circuit.neg_between (W_im_neg ha) (W_im_neg hb) u.2.1 u.2.2
    exact Or.inr (by rw [Circuit.seg_im]; exact neg_ne_zero.2 this.ne)
  · have := Circuit.neg_between (W_re_neg (up := up) ha) (W_re_neg (up := up) hb) u.2.1 u.2.2
    exact Or.inl (by rw [Circuit.seg_re]; linarith)

theorem getD_eq_of_closed {l : List (ℤ × ℤ)} (h : l.getLast? = l.head?) {N : ℕ}
    (hN : l.length = N + 1) : l.getD N (0, 0) = l.getD 0 (0, 0) := by
  have h1 : l.getD N (0, 0) = l.getLast?.getD (0, 0) := by
    simp [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD, hN]
  have h2 : l.getD 0 (0, 0) = l.head?.getD (0, 0) := by
    cases l <;> rfl
  rw [h1, h2, h]

/-- **A certified recorded loop has index one**, as a loop about its puncture. -/
theorem certified_liftIndex {up : Bool} {l : List (ℤ × ℤ)} {n q r : ℕ} (hq0 : 0 < q) (hqr : q < r)
    (hrn : r ≤ n) (hlen : l.length = n + 2) (hc : loopCert up l q r = true) :
    ∃ (hs : ∀ k ≤ n, (k < q ∨ r ≤ k) → ∀ u, seg (W up l) k u ∈ slitPlane)
      (hns : ∀ k ≤ n, q ≤ k → k < r → ∀ u, -(seg (W up l) k u) ∈ slitPlane)
      (hclose : W up l (n + 1) = W up l 0),
      Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (loopC (W up l) n hs hns hqr hclose))) = ⊤ := by
  obtain ⟨h1, h2, h3, -, hq, hr, hcl⟩ := loopCert_spec hqr.le hc
  have hs : ∀ k ≤ n, (k < q ∨ r ≤ k) → ∀ u, seg (W up l) k u ∈ slitPlane := by
    intro k hk hk' u
    rcases hk' with hk' | hk'
    · exact seg_slit (h1 k (by omega) hk') u
    · exact seg_slit (h3 k (by omega) hk') u
  have hns : ∀ k ≤ n, q ≤ k → k < r → ∀ u, -(seg (W up l) k u) ∈ slitPlane :=
    fun k hk hqk hkr u => seg_negSlit (h2 k (by omega) hqk hkr) u
  have hclose : W up l (n + 1) = W up l 0 := by
    show ptC 40 (l.getD (n + 1) (0, 0)) - pz up = ptC 40 (l.getD 0 (0, 0)) - pz up
    rw [getD_eq_of_closed hcl (by omega)]
  refine ⟨hs, hns, hclose, ?_⟩
  refine zpowers_eq_top_of_abs_liftIndex (⟨log (W up l 0), expMap_log (baseC (W up l) n hs hns hqr)⟩ :
    expMap ⁻¹' {baseC (W up l) n hs hns hqr}) ?_
  rw [liftIndex_loopC (W up l) n hs hns hqr (W_im_pos hq) (W_im_neg hr) hclose hq0 hrn]
  rfl

/-! ### The half-planes and the translation of the polyline -/

theorem one_lt_sqrt3 : 1 < Real.sqrt 3 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem sqrt3_lt_two : Real.sqrt 3 < 2 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `Im z > -1/2` (`up`) or `Im z < 1/2` (not `up`). -/
def U (up : Bool) : Set ℂ := if up then {z | -1 / 2 < z.im} else {z | z.im < 1 / 2}

theorem convex_U (up : Bool) : Convex ℝ (U up) := by
  cases up
  · exact convex_halfSpace_lt Complex.imLm.isLinear _
  · exact convex_halfSpace_gt Complex.imLm.isLinear _

theorem ball_sub_U (up : Bool) : Metric.closedBall (pz up) 1 ⊆ U up := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h := (abs_le.mp ((Complex.abs_im_le_norm (z - pz up)).trans hz))
  simp only [Complex.sub_im, pz] at h
  have := one_lt_sqrt3
  cases up
  · simp only [U, Bool.false_eq_true, ite_false, Set.mem_ofPred_eq] at h ⊢; linarith [h.2]
  · simp only [U, ite_true, Set.mem_ofPred_eq] at h ⊢; linarith [h.1]

theorem ne_other_of_mem_U {up : Bool} {z : ℂ} (hz : z ∈ U up) : z ≠ pz (!up) := by
  intro h; subst h
  have := one_lt_sqrt3
  cases up <;> simp [U, pz] at hz <;> linarith

theorem norm_pz (up : Bool) : ‖pz up‖ = 1 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h : Complex.normSq (pz up) = 1 := by
    rw [Complex.normSq_apply]; cases up <;> simp [pz] <;> nlinarith [h3]
  rw [Complex.norm_def, h, Real.sqrt_one]

theorem segment_sub (a b c : ℂ) (u : unitInterval) :
    MonicFamily.segment (a - c) (b - c) u = MonicFamily.segment a b u - c := by
  show (a - c) + ((u : ℝ) : ℂ) * ((b - c) - (a - c)) = (a + ((u : ℝ) : ℂ) * (b - a)) - c
  ring

theorem polyC_sub (up : Bool) (l : List (ℤ × ℤ)) :
    ∀ m u, polyC (W up l) m u = polyC (P l) m u - pz up
  | 0, u => segment_sub _ _ _ u
  | m + 1, u => by
    simp only [polyC, Path.trans_apply]
    split_ifs
    · exact polyC_sub up l m _
    · exact segment_sub _ _ _ _

theorem seg_mem_U {up : Bool} {l : List (ℤ × ℤ)} {k : ℕ}
    (h : halfB up (l.getD k (0, 0)) = true ∧ halfB up (l.getD (k + 1) (0, 0)) = true)
    (u : unitInterval) : seg (P l) k u ∈ U up := by
  obtain ⟨ha, hb⟩ := h
  cases up
  · simp only [halfB, decide_eq_true_eq, Bool.false_eq_true, ite_false] at ha hb
    have ha' : ((l.getD k (0, 0)).2 : ℝ) < 2 ^ 39 := by exact_mod_cast ha
    have hb' : ((l.getD (k + 1) (0, 0)).2 : ℝ) < 2 ^ 39 := by exact_mod_cast hb
    have := Circuit.neg_between (x := (P l k).im - 1 / 2) (y := (P l (k + 1)).im - 1 / 2)
      (by rw [P_im]; linarith) (by rw [P_im]; linarith) u.2.1 u.2.2
    simp only [U, Bool.false_eq_true, ite_false, Set.mem_ofPred_eq, seg, Circuit.seg_im]
    linarith
  · simp only [halfB, decide_eq_true_eq, ite_true] at ha hb
    have ha' : -(2 : ℝ) ^ 39 < ((l.getD k (0, 0)).2 : ℝ) := by exact_mod_cast ha
    have hb' : -(2 : ℝ) ^ 39 < ((l.getD (k + 1) (0, 0)).2 : ℝ) := by exact_mod_cast hb
    have := Circuit.pos_between (x := (P l k).im + 1 / 2) (y := (P l (k + 1)).im + 1 / 2)
      (by rw [P_im]; linarith) (by rw [P_im]; linarith) u.2.1 u.2.2
    simp only [U, ite_true, Set.mem_ofPred_eq, seg, Circuit.seg_im]
    linarith

/-! ### The twice-punctured plane -/

/-- `ℂ ∖ {ζ₃, ζ₃²}`. -/
abbrev X2 := {z : ℂ // z ≠ pz true ∧ z ≠ pz false}

theorem zero_mem_U (up : Bool) : (0 : ℂ) ∈ U up := by cases up <;> simp [U] <;> norm_num

theorem zero_ne_pz (up : Bool) : (0 : ℂ) ≠ pz up := by
  intro h; have := congrArg Complex.re h; simp [pz] at this; norm_num at this

/-- The base point `0`. -/
def x0 : X2 := ⟨0, zero_ne_pz true, zero_ne_pz false⟩

/-- The half-plane `U up` inside the twice-punctured plane. -/
def U' (up : Bool) : Set X2 := {w | (w : ℂ) ∈ U up}

theorem x0_mem_U' (up : Bool) : x0 ∈ U' up := zero_mem_U up

def xU (up : Bool) : U' up := ⟨x0, x0_mem_U' up⟩

theorem ownNe (up : Bool) (w : X2) : (w : ℂ) ≠ pz up := by cases up; exacts [w.2.2, w.2.1]

theorem bothNe {up : Bool} {z : ℂ} (hz : z ∈ U up) (hne : z ≠ pz up) :
    z ≠ pz true ∧ z ≠ pz false := by
  cases up
  · exact ⟨ne_other_of_mem_U hz, hne⟩
  · exact ⟨hne, ne_other_of_mem_U hz⟩

/-- `U' up`, read as the punctured half-plane. -/
def toY (up : Bool) : C(U' up, Retract.Y (pz up) (U up)) :=
  ⟨fun w => ⟨w.1.1, w.2, ownNe up w.1⟩, by fun_prop⟩

def fromY (up : Bool) : C(Retract.Y (pz up) (U up), U' up) :=
  ⟨fun z => ⟨⟨z.1, bothNe z.2.1 z.2.2⟩, z.2.1⟩, by fun_prop⟩

theorem zpowers_cast_eq_top {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y) {γ : Path x x}
    (hγ : Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = ⊤) :
    Subgroup.zpowers (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (γ.cast h.symm h.symm))) = ⊤ := by
  subst h; simpa using hγ

theorem P_zero {l : List (ℤ × ℤ)} (hl0 : l.getD 0 (0, 0) = (0, 0)) : P l 0 = 0 := by
  rw [P, hl0]; simp [ptC]

/-- **One side.** A certified recorded loop, starting at `0`, generates the fundamental group of
its punctured half-plane, read inside `ℂ ∖ {ζ₃, ζ₃²}`. -/
theorem side_zpowers {up : Bool} {l : List (ℤ × ℤ)} {n q r : ℕ} (hq0 : 0 < q) (hqr : q < r)
    (hrn : r ≤ n) (hlen : l.length = n + 2) (hc : loopCert up l q r = true)
    (hl0 : l.getD 0 (0, 0) = (0, 0)) :
    ∃ γ : Path (xU up) (xU up), (∀ u, ((γ u : X2) : ℂ) = polyC (P l) n u) ∧
      Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = ⊤ := by
  obtain ⟨hs, hns, hclose, hgen⟩ := certified_liftIndex hq0 hqr hrn hlen hc
  obtain ⟨-, -, -, h4, -, -, hcl⟩ := loopCert_spec hqr.le hc
  have hmem : ∀ u, polyC (P l) n u ∈ U up :=
    polyC_mem (P l) n (fun k hk u => seg_mem_U (h4 k (by omega)) u)
  have hne : ∀ u, polyC (P l) n u ≠ pz up := fun u h => by
    have := polyC_ne_zero (W up l) n hs hns hqr u
    rw [polyC_sub, h, sub_self] at this; exact this rfl
  have hP1 : polyC (P l) n 1 = 0 := (polyC (P l) n).target.trans (by
    show ptC 40 (l.getD (n + 1) (0, 0)) = 0
    rw [getD_eq_of_closed hcl (by omega)]; exact P_zero hl0)
  have hP0 : polyC (P l) n 0 = 0 := (polyC (P l) n).source.trans (P_zero hl0)
  -- the loop in the punctured half-plane
  let yU : Retract.Y (pz up) (U up) := ⟨0, zero_mem_U up, zero_ne_pz up⟩
  let δY : Path yU yU :=
    { toFun := fun u => ⟨polyC (P l) n u, hmem u, hne u⟩
      continuous_toFun := (polyC (P l) n).continuous.subtype_mk _
      source' := Subtype.ext hP0
      target' := Subtype.ext hP1 }
  have hbase : baseC (W up l) n hs hns hqr = Retract.incl (pz up) (U up) yU :=
    Subtype.ext (show P l 0 - pz up = 0 - pz up by rw [P_zero hl0])
  have hmap : FundamentalGroup.map (Retract.incl (pz up) (U up)) yU
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δY))
      = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((loopC (W up l) n hs hns hqr hclose).cast hbase.symm hbase.symm)) := by
    have : δY.map (Retract.incl (pz up) (U up)).continuous
        = (loopC (W up l) n hs hns hqr hclose).cast hbase.symm hbase.symm := by
      ext u; show polyC (P l) n u - pz up = polyC (W up l) n u; rw [polyC_sub]
    exact congrArg Path.Homotopic.Quotient.mk this
  have hx : ‖(yU : ℂ) - pz up‖ = 1 := by simp [yU, norm_pz]
  have hY : Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δY)) = ⊤ :=
    Retract.zpowers_eq_top_of_map_incl (convex_U up) (ball_sub_U up) hx
      (by rw [hmap]; exact zpowers_cast_eq_top hbase hgen)
  -- the same loop inside `U' up ⊆ ℂ ∖ {ζ₃, ζ₃²}`
  let γ : Path (xU up) (xU up) :=
    { toFun := fun u => ⟨⟨polyC (P l) n u, bothNe (hmem u) (hne u)⟩, hmem u⟩
      continuous_toFun := ((polyC (P l) n).continuous.subtype_mk _).subtype_mk _
      source' := Subtype.ext (Subtype.ext hP0)
      target' := Subtype.ext (Subtype.ext hP1) }
  refine ⟨γ, fun u => rfl, ?_⟩
  have hmapγ : FundamentalGroup.map (toY up) (xU up)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))
      = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δY) := rfl
  have hback : ∀ p : FundamentalGroup (U' up) (xU up),
      FundamentalGroup.map (fromY up) _ (FundamentalGroup.map (toY up) (xU up) p) = p := by
    intro p
    induction p using Path.Homotopic.Quotient.ind with | _ δ => rfl
  rw [Subgroup.eq_top_iff'] at hY ⊢
  intro δ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hY (FundamentalGroup.map (toY up) (xU up) δ))
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have key : FundamentalGroup.map (toY up) (xU up)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) ^ k)
      = FundamentalGroup.map (toY up) (xU up) δ := by
    rw [map_zpow, hmapγ]; exact hk
  have := congrArg (FundamentalGroup.map (fromY up) ((toY up) (xU up))) key
  rwa [hback, hback] at this

/-! ### Path connectedness of the cover -/

theorem isPathConnected_X2 {S : Set X2} {T : Set ℂ} (hT : IsPathConnected T)
    (hST : ∀ w : X2, w ∈ S ↔ (w : ℂ) ∈ T) (hTX : ∀ z ∈ T, z ≠ pz true ∧ z ≠ pz false) :
    IsPathConnected S := by
  obtain ⟨x, hx, hj⟩ := hT
  refine ⟨⟨x, hTX x hx⟩, (hST _).2 hx, fun {y} hy => ?_⟩
  obtain ⟨γ, hγ⟩ := hj ((hST y).1 hy)
  exact ⟨{ toFun := fun t => ⟨γ t, hTX _ (hγ t)⟩
           continuous_toFun := γ.continuous.subtype_mk _
           source' := Subtype.ext γ.source
           target' := Subtype.ext γ.target },
    fun t => (hST _).2 (hγ t)⟩

theorem pz_re (up : Bool) : (pz up).re = -1 / 2 := rfl

/-- A half-plane punctured at `pz up` is path connected: it is the union of four convex pieces,
chained through nonempty overlaps. -/
theorem isPathConnected_U_diff (up : Bool) : IsPathConnected (U up \ {pz up}) := by
  set A := U up ∩ {z : ℂ | z.im < (pz up).im}
  set B := U up ∩ {z : ℂ | (pz up).im < z.im}
  set C := U up ∩ {z : ℂ | z.re < -1 / 2}
  set D := U up ∩ {z : ℂ | -1 / 2 < z.re}
  have h2 := sqrt3_lt_two
  have h1 := one_lt_sqrt3
  have cA : Convex ℝ A := (convex_U up).inter (convex_halfSpace_lt Complex.imLm.isLinear _)
  have cB : Convex ℝ B := (convex_U up).inter (convex_halfSpace_gt Complex.imLm.isLinear _)
  have cC : Convex ℝ C := (convex_U up).inter (convex_halfSpace_lt Complex.reLm.isLinear _)
  have cD : Convex ℝ D := (convex_U up).inter (convex_halfSpace_gt Complex.reLm.isLinear _)
  -- witnesses
  have wAC : (A ∩ C).Nonempty := by
    cases up
    · exact ⟨⟨-1, -1⟩, ⟨⟨by simp [U] <;> norm_num, by simp [pz] <;> linarith⟩, by simp [U] <;> norm_num,
        by simp <;> norm_num⟩⟩
    · exact ⟨⟨-1, 0⟩, ⟨⟨by simp [U] <;> norm_num, by simp [pz] <;> positivity⟩, by simp [U] <;> norm_num,
        by simp <;> norm_num⟩⟩
  have wCB : ((A ∪ C) ∩ B).Nonempty := by
    cases up
    · exact ⟨⟨-1, 0⟩, Or.inr ⟨by simp [U] <;> norm_num, by simp <;> norm_num⟩,
        by simp [U] <;> norm_num, by simp [pz] <;> positivity⟩
    · exact ⟨⟨-1, 1⟩, Or.inr ⟨by simp [U] <;> norm_num, by simp <;> norm_num⟩,
        by simp [U] <;> norm_num, by simp [pz] <;> linarith⟩
  have wBD : ((A ∪ C ∪ B) ∩ D).Nonempty := by
    cases up
    · exact ⟨⟨0, 0⟩, Or.inr ⟨by simp [U] <;> norm_num, by simp [pz] <;> positivity⟩,
        by simp [U] <;> norm_num, by simp <;> norm_num⟩
    · exact ⟨⟨0, 1⟩, Or.inr ⟨by simp [U] <;> norm_num, by simp [pz] <;> linarith⟩,
        by simp [U] <;> norm_num, by simp <;> norm_num⟩
  have hunion : U up \ {pz up} = A ∪ C ∪ B ∪ D := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff, A, B, C, D,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hz, hne⟩
      rcases lt_trichotomy z.im (pz up).im with h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hz, h⟩))
      · rcases lt_trichotomy z.re (-1 / 2) with h' | h' | h'
        · exact Or.inl (Or.inl (Or.inr ⟨hz, h'⟩))
        · exact absurd (Complex.ext (by rw [h', pz_re]) h) hne
        · exact Or.inr ⟨hz, h'⟩
      · exact Or.inl (Or.inr ⟨hz, h⟩)
    · rintro (((⟨hz, h⟩ | ⟨hz, h⟩) | ⟨hz, h⟩) | ⟨hz, h⟩)
      · exact ⟨hz, fun e => by rw [e] at h; exact lt_irrefl _ h⟩
      · exact ⟨hz, fun e => by rw [e, pz_re] at h; exact lt_irrefl _ h⟩
      · exact ⟨hz, fun e => by rw [e] at h; exact lt_irrefl _ h⟩
      · exact ⟨hz, fun e => by rw [e, pz_re] at h; exact lt_irrefl _ h⟩
  rw [hunion]
  refine (((cA.isPathConnected ?_).union (cC.isPathConnected ?_) wAC).union
    (cB.isPathConnected ?_) wCB).union (cD.isPathConnected ?_) wBD
  · exact wAC.mono Set.inter_subset_left
  · exact wAC.mono Set.inter_subset_right
  · exact wCB.mono Set.inter_subset_right
  · exact wBD.mono Set.inter_subset_right

theorem isOpen_U (up : Bool) : IsOpen (U up) := by
  cases up
  · exact isOpen_lt Complex.continuous_im continuous_const
  · exact isOpen_lt continuous_const Complex.continuous_im

theorem isPathConnected_U' (up : Bool) : IsPathConnected (U' up) :=
  isPathConnected_X2 (isPathConnected_U_diff up) (fun w => ⟨fun h => ⟨h, ownNe up w⟩, fun h => h.1⟩)
    (fun z hz => bothNe hz.1 hz.2)

theorem isPathConnected_U'_inter : IsPathConnected (U' true ∩ U' false) := by
  refine isPathConnected_X2 (T := U true ∩ U false)
    (((convex_U true).inter (convex_U false)).isPathConnected ⟨0, zero_mem_U true, zero_mem_U false⟩)
    (fun w => Iff.rfl) (fun z hz => bothNe hz.1 ?_)
  intro h; have := hz.2; rw [h] at this
  have := one_lt_sqrt3; simp [U, pz] at *; linarith

/-- The recorded polylines, in the form built here. -/
theorem chain_poly_eq (C : Chain) : ∀ m u, C.poly 40 m u = polyC (P C.wps) m u
  | 0, _ => rfl
  | m + 1, u => by
    simp only [Chain.poly, polyC, Path.trans_apply]
    split_ifs
    · exact chain_poly_eq C m _
    · rfl

theorem chain_len : Meridian1.chain.wps.length = 1152 + 2 := by decide +kernel
theorem chain2_len : Meridian1.chain2.wps.length = 1153 + 2 := by decide +kernel
theorem chain_n : Meridian1.chain.n = 1153 := by decide +kernel
theorem chain2_n : Meridian1.chain2.n = 1154 := by decide +kernel
theorem chain_wp0 : Meridian1.chain.wps.getD 0 (0, 0) = (0, 0) := by decide +kernel
theorem chain2_wp0 : Meridian1.chain2.wps.getD 0 (0, 0) = (0, 0) := by decide +kernel

/-- **Two-puncture generation.** The two recorded complex polylines — the certified meridians about `ζ₃` and
`ζ₃²`, exactly as `Chain.poly` builds them — generate the fundamental group of the
twice-punctured plane `ℂ ∖ {ζ₃, ζ₃²}` at `0`. No meridian system is chosen: the cover is fitted to
these loops, so no conjugating paths ever appear. -/
theorem polylines_generate :
    ∃ γ₁ γ₂ : Path x0 x0,
      (∀ u, (γ₁ u : ℂ) = Meridian1.chain.poly 40 (Meridian1.chain.n - 1) u) ∧
      (∀ u, (γ₂ u : ℂ) = Meridian1.chain2.poly 40 (Meridian1.chain2.n - 1) u) ∧
      Subgroup.closure {FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₁),
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₂)} = ⊤ := by
  obtain ⟨g₁, hg₁, hz₁⟩ := side_zpowers (up := true) (by norm_num) (by norm_num) (by norm_num)
    chain_len Loops.cert1 chain_wp0
  obtain ⟨g₂, hg₂, hz₂⟩ := side_zpowers (up := false) (by norm_num) (by norm_num) (by norm_num)
    chain2_len Loops.cert2 chain2_wp0
  refine ⟨g₁.map continuous_subtype_val, g₂.map continuous_subtype_val,
    fun u => by rw [chain_n]; exact (hg₁ u).trans (chain_poly_eq _ _ u).symm,
    fun u => by rw [chain2_n]; exact (hg₂ u).trans (chain_poly_eq _ _ u).symm, ?_⟩
  have hcover : U' true ∪ U' false = Set.univ := by
    refine Set.eq_univ_of_forall fun w => ?_
    simp only [Set.mem_union, U', U, Set.mem_ofPred_eq, ite_true, Bool.false_eq_true, ite_false]
    by_cases h : -1 / 2 < (w : ℂ).im
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hvk := vanKampen_generation X2 (U' true) (U' false) x0 (x0_mem_U' true) (x0_mem_U' false)
    ((isOpen_U true).preimage continuous_subtype_val)
    ((isOpen_U false).preimage continuous_subtype_val) hcover
    (isPathConnected_U' true) (isPathConnected_U' false) isPathConnected_U'_inter
  have e₁ : (inclHom (U' true) (x0_mem_U' true))
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk g₁))
      = (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (g₁.map continuous_subtype_val)) :
          FundamentalGroup X2 x0) := by
    rw [inclHom, FundamentalGroup.mapOfEq_apply]; rfl
  have hr₁ : (inclHom (U' true) (x0_mem_U' true)).range = Subgroup.zpowers
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (g₁.map continuous_subtype_val)) :
        FundamentalGroup X2 x0) := by
    rw [← e₁, ← MonoidHom.map_zpowers, MonoidHom.range_eq_map]; exact congrArg _ hz₁.symm
  have e₂ : (inclHom (U' false) (x0_mem_U' false))
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk g₂))
      = (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (g₂.map continuous_subtype_val)) :
          FundamentalGroup X2 x0) := by
    rw [inclHom, FundamentalGroup.mapOfEq_apply]; rfl
  have hr₂ : (inclHom (U' false) (x0_mem_U' false)).range = Subgroup.zpowers
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (g₂.map continuous_subtype_val)) :
        FundamentalGroup X2 x0) := by
    rw [← e₂, ← MonoidHom.map_zpowers, MonoidHom.range_eq_map]; exact congrArg _ hz₂.symm
  rw [hr₁, hr₂] at hvk
  rw [eq_top_iff, ← hvk]
  exact sup_le (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))
    (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))

end Sz8.Galois.TwoPunctures
