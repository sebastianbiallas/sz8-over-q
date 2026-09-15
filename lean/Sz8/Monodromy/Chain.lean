import Sz8.Monodromy.StepChain
import Sz8.Monodromy.StepDatum

/-!
Composing certified steps into the monodromy of a polygonal path.

A `Chain` is a list of waypoints `w₀, …, wₙ` (Gaussian integers scaled by `2^J`), a list of
distinct step data, and for every leg `k < n` the index of the step certifying it and a
label map `πₖ` for the junction at `wₖ₊₁` (the empty list is the identity). The junction
after the last leg goes back to the first step, so a closed chain reads off its monodromy
in the labelling of the first step.

`legB C k` is checked by the kernel, one chunk of legs per declaration:
* the step index is in range;
* both endpoints of the leg lie in the step's parameter disc, and `wₖ₊₁` lies in the next
  step's parameter disc;
* disc `i` of the step lies in disc `πₖ(i)` of the next step enlarged by its certified gap
  (`junctionG`); this implies that it is separated from every other disc (`junctionB`).

`chain_root`: along the polyline (lifted to the regular parameters), Mathlib's monodromy
sends a fibre point whose root lies in disc `i` of step 0 to one whose root lies in disc
`lab C (m+1) i` of the next step after leg `m`. Nothing about the path is numerical: the
waypoints are exact, every parameter on every segment lies in a certified disc.
-/

open Polynomial Metric

namespace Sz8.Monodromy
open GaussPoly MonicFamily

variable (J K : ℕ)

/-- The parameter represented by a waypoint. -/
noncomputable def ptC (w : GI) : ℂ := gc w / 2 ^ J

/-- The waypoint lies in the step's parameter disc. -/
def inStepB (st : StepDatum) (w : GI) : Bool :=
  decide (nsq (w.1 - st.τ.1, w.2 - st.τ.2) ≤ (st.S : ℤ) ^ 2)

/-- Disc `i` of a step. -/
def StepDatum.disc (st : StepDatum) (i : ℕ) : GI × ℕ := st.discs.getD i ((0, 0), 0)

/-- Disc `q` is separated from the discs `rs` (numbered from `j`), except number `k`. -/
def sepRow (q : GI × ℕ) (k : ℕ) : ℕ → List (GI × ℕ) → Bool
  | _, [] => true
  | j, r :: rs => ((j == k) || separated q r) && sepRow q k (j + 1) rs

/-- `sepRow` for each disc `qs` (numbered from `i`) against `ds'`, excepting its image under `π`. -/
def junRows (π : List ℕ) (ds' : List (GI × ℕ)) : ℕ → List (GI × ℕ) → Bool
  | _, [] => true
  | i, q :: qs => decide (π.getD i i < 65) && sepRow q (π.getD i i) 0 ds' && junRows π ds' (i + 1) qs

/-- Junction check: disc `i` of `st` is separated from every disc `j ≠ π i` of `st'`. -/
def junctionB (st st' : StepDatum) (π : List ℕ) : Bool := junRows π st'.discs 0 st.discs

theorem sepRow_spec {q : GI × ℕ} {k : ℕ} : ∀ {j₀ : ℕ} {rs : List (GI × ℕ)}, sepRow q k j₀ rs = true →
    ∀ j (hj : j < rs.length), j₀ + j = k ∨ separated q rs[j] = true
  | _, [], _, j, hj => absurd hj (by simp)
  | j₀, r :: rs, h, j, hj => by
    simp only [sepRow, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := sepRow_spec h.2 j (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem junRows_spec {π : List ℕ} {ds' : List (GI × ℕ)} : ∀ {i₀ : ℕ} {qs : List (GI × ℕ)},
    junRows π ds' i₀ qs = true → ∀ i (hi : i < qs.length),
      π.getD (i₀ + i) (i₀ + i) < 65 ∧ sepRow qs[i] (π.getD (i₀ + i) (i₀ + i)) 0 ds' = true
  | _, [], _, i, hi => absurd hi (by simp)
  | i₀, q :: qs, h, i, hi => by
    simp only [junRows, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := junRows_spec h.2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem sepRow_of {q : GI × ℕ} {k : ℕ} : ∀ {j₀ : ℕ} {rs : List (GI × ℕ)},
    (∀ j (hj : j < rs.length), j₀ + j = k ∨ separated q rs[j] = true) → sepRow q k j₀ rs = true
  | _, [], _ => rfl
  | j₀, r :: rs, h => by
    simp only [sepRow, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    refine ⟨h0, sepRow_of fun j hj => ?_⟩
    have := h (j + 1) (by simpa using hj)
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem junRows_of {π : List ℕ} {ds' : List (GI × ℕ)} : ∀ {i₀ : ℕ} {qs : List (GI × ℕ)},
    (∀ i (hi : i < qs.length),
      π.getD (i₀ + i) (i₀ + i) < 65 ∧ sepRow qs[i] (π.getD (i₀ + i) (i₀ + i)) 0 ds' = true) →
    junRows π ds' i₀ qs = true
  | _, [], _ => rfl
  | i₀, q :: qs, h => by
    simp only [junRows, Bool.and_eq_true, decide_eq_true_eq]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    refine ⟨h0, junRows_of fun i hi => ?_⟩
    have := h (i + 1) (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-! ### Cheap junctions through certified gaps -/

/-- Source disc `q` lies in target disc `r` enlarged by `δ`: `|c_q - c_r| + R_q ≤ r_r + δ`
(nonnegativity of `r_r + δ - R_q` is checked before squaring). -/
def inclB (q r : GI × ℕ) (δ : ℕ) : Bool :=
  decide (q.2 ≤ r.2 + δ) && decide (nsq (q.1.1 - r.1.1, q.1.2 - r.1.2) ≤ ((r.2 + δ - q.2 : ℕ) : ℤ) ^ 2)

/-- Identity junction: disc `i` of `qs` lies in the enlarged disc `i` of `rs`. -/
def inclZip : List (GI × ℕ) → List (GI × ℕ) → List ℕ → Bool
  | [], _, _ => true
  | q :: qs, r :: rs, g :: gs => inclB q r g && inclZip qs rs gs
  | _ :: _, _, _ => false

/-- Permuted junction: disc `i` (numbered from `i₀`) lies in the enlarged disc `π i`. -/
def inclRows (π : List ℕ) (ds' : List (GI × ℕ)) (gs' : List ℕ) : ℕ → List (GI × ℕ) → Bool
  | _, [] => true
  | i, q :: qs => decide (π.getD i i < 65) &&
      inclB q (ds'.getD (π.getD i i) ((0, 0), 0)) (gs'.getD (π.getD i i) 0) &&
      inclRows π ds' gs' (i + 1) qs

/-- The junction check of a leg: 65 inclusions into enlarged discs of the next step (whose
gaps are certified once, with the step). -/
def junctionG (st st' : StepDatum) (π : List ℕ) : Bool :=
  match π with
  | [] => inclZip st.discs st'.discs st'.gaps
  | _ :: _ => inclRows π st'.discs st'.gaps 0 st.discs

theorem inclZip_spec : ∀ {qs rs : List (GI × ℕ)} {gs : List ℕ}, inclZip qs rs gs = true →
    ∀ i (hi : i < qs.length), i < rs.length ∧ inclB qs[i] (rs.getD i ((0, 0), 0)) (gs.getD i 0) = true
  | [], _, _, _, i, hi => absurd hi (by simp)
  | _ :: _, [], _, h, _, _ => by simp [inclZip] at h
  | _ :: _, _ :: _, [], h, _, _ => by simp [inclZip] at h
  | q :: qs, r :: rs, g :: gs, h, i, hi => by
    simp only [inclZip, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := inclZip_spec h.2 i (by simpa using hi)
      simpa using this

theorem inclRows_spec {π : List ℕ} {ds' : List (GI × ℕ)} {gs' : List ℕ} :
    ∀ {i₀ : ℕ} {qs : List (GI × ℕ)}, inclRows π ds' gs' i₀ qs = true → ∀ i (hi : i < qs.length),
      π.getD (i₀ + i) (i₀ + i) < 65 ∧ inclB qs[i] (ds'.getD (π.getD (i₀ + i) (i₀ + i)) ((0, 0), 0))
        (gs'.getD (π.getD (i₀ + i) (i₀ + i)) 0) = true
  | _, [], _, i, hi => absurd hi (by simp)
  | i₀, q :: qs, h, i, hi => by
    simp only [inclRows, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := inclRows_spec h.2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem junctionG_spec {st st' : StepDatum} {π : List ℕ} (hlen' : st'.discs.length = 65)
    (h : junctionG st st' π = true) : ∀ i (hi : i < st.discs.length), π.getD i i < 65 ∧
      inclB st.discs[i] (st'.disc (π.getD i i)) (st'.gaps.getD (π.getD i i) 0) = true := by
  intro i hi
  match π, h with
  | [], h =>
    obtain ⟨hr, hinc⟩ := inclZip_spec h i hi
    simp only [List.getD_nil]
    exact ⟨hlen' ▸ hr, hinc⟩
  | a :: π, h =>
    have := inclRows_spec h i hi
    simpa [StepDatum.disc, List.getD_eq_getElem?_getD] using this

theorem sepGap_comm (δ : ℕ) (q r : GI × ℕ) : sepGap δ q r = sepGap δ r q := by
  have h : nsq (q.1.1 - r.1.1, q.1.2 - r.1.2) = nsq (r.1.1 - q.1.1, r.1.2 - q.1.2) := by
    simp only [nsq]; ring
  simp only [sepGap, h, Nat.add_comm q.2 r.2]

theorem gapRow_spec {q : GI × ℕ} {g : ℕ} : ∀ {rs : List (GI × ℕ)} {hs : List ℕ},
    gapRow q g rs hs = true → ∀ j, j < rs.length →
      sepGap (max g (hs.getD j 0)) q (rs.getD j ((0, 0), 0)) = true
  | [], _, _, j, hj => absurd hj (by simp)
  | _ :: _, [], h, _, _ => by simp [gapRow] at h
  | r :: rs, h :: hs, hr, j, hj => by
    simp only [gapRow, Bool.and_eq_true] at hr
    cases j with
    | zero => simpa using hr.1
    | succ j => simpa using gapRow_spec hr.2 j (by simpa using hj)

theorem gapsOK_spec_lt : ∀ {ds : List (GI × ℕ)} {gs : List ℕ}, gapsOK ds gs = true →
    ∀ i j, i < j → j < ds.length →
      sepGap (max (gs.getD i 0) (gs.getD j 0)) (ds.getD i ((0, 0), 0)) (ds.getD j ((0, 0), 0)) = true
  | [], _, _, _, j, _, hj => absurd hj (by simp)
  | _ :: _, [], h, _, _, _, _ => by simp [gapsOK] at h
  | q :: qs, g :: gs, h, i, j, hij, hj => by
    simp only [gapsOK, Bool.and_eq_true] at h
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    cases i with
    | zero => simpa using gapRow_spec h.1 j (by simpa using hj)
    | succ i => simpa using gapsOK_spec_lt h.2 i j (by omega) (by simpa using hj)

theorem gapsOK_spec {ds : List (GI × ℕ)} {gs : List ℕ} (h : gapsOK ds gs = true) {i j : ℕ}
    (hi : i < ds.length) (hj : j < ds.length) (hij : i ≠ j) :
    sepGap (max (gs.getD i 0) (gs.getD j 0)) (ds.getD i ((0, 0), 0)) (ds.getD j ((0, 0), 0)) = true := by
  rcases Nat.lt_or_gt_of_ne hij with h' | h'
  · exact gapsOK_spec_lt h i j h' hj
  · rw [sepGap_comm, max_comm]; exact gapsOK_spec_lt h j i h' hi

theorem sq_nsq_sub (x y : GI) : (nsq (x.1 - y.1, x.2 - y.2) : ℝ) = ‖gc x - gc y‖ ^ 2 := by
  rw [← normSq_gc]
  congr 2
  simp only [gc]; push_cast; ring

/-- **Gap junctions imply separation.** If `q` lies in the enlarged disc `r` (gap `δ ≤ δ'`)
and `r`, `s` are separated with margin `δ'`, then `q` and `s` are separated. -/
theorem separated_of_incl {q r s : GI × ℕ} {δ δ' : ℕ} (hδ : δ ≤ δ') (hin : inclB q r δ = true)
    (hs : sepGap δ' r s = true) : separated q s = true := by
  simp only [inclB, sepGap, separated, Bool.and_eq_true, decide_eq_true_eq] at hin hs ⊢
  obtain ⟨hR, hd⟩ := hin
  have h1 : ((r.2 + s.2 + δ' : ℕ) : ℝ) ≤ ‖gc r.1 - gc s.1‖ := by
    have : ((r.2 + s.2 + δ' : ℕ) : ℝ) ^ 2 ≤ ‖gc r.1 - gc s.1‖ ^ 2 := by
      rw [← sq_nsq_sub]; exact_mod_cast hs
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) this
  have h2 : ‖gc q.1 - gc r.1‖ ≤ ((r.2 + δ - q.2 : ℕ) : ℝ) := by
    have : ‖gc q.1 - gc r.1‖ ^ 2 ≤ ((r.2 + δ - q.2 : ℕ) : ℝ) ^ 2 := by
      rw [← sq_nsq_sub]; exact_mod_cast hd
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) this
  have h3 : ‖gc r.1 - gc s.1‖ ≤ ‖gc q.1 - gc r.1‖ + ‖gc q.1 - gc s.1‖ := by
    calc ‖gc r.1 - gc s.1‖ = ‖(gc q.1 - gc s.1) - (gc q.1 - gc r.1)‖ := by congr 1; ring
      _ ≤ ‖gc q.1 - gc s.1‖ + ‖gc q.1 - gc r.1‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have hcast : ((r.2 + δ - q.2 : ℕ) : ℝ) = (r.2 : ℝ) + δ - q.2 := by
    rw [Nat.cast_sub hR]; push_cast; ring
  have h4 : ((q.2 + s.2 : ℕ) : ℝ) ≤ ‖gc q.1 - gc s.1‖ := by
    push_cast at h1 ⊢
    have : (δ : ℝ) ≤ δ' := by exact_mod_cast hδ
    linarith
  have : ((q.2 + s.2 : ℕ) : ℝ) ^ 2 ≤ (nsq (q.1.1 - s.1.1, q.1.2 - s.1.2) : ℝ) := by
    rw [sq_nsq_sub]; exact pow_le_pow_left₀ (by positivity) h4 2
  exact_mod_cast this

/-- **Compatibility**: the cheap junction check implies the separation check `junctionB`. -/
theorem junctionB_of_junctionG {st st' : StepDatum} {π : List ℕ} (hlen' : st'.discs.length = 65)
    (hgap : gapsOK st'.discs st'.gaps = true) (hj : junctionG st st' π = true) :
    junctionB st st' π = true := by
  apply junRows_of
  intro i hi
  simp only [Nat.zero_add]
  obtain ⟨hk, hinc⟩ := junctionG_spec hlen' hj i hi
  refine ⟨hk, sepRow_of fun j hj => ?_⟩
  rw [Nat.zero_add]
  by_cases hjk : j = π.getD i i
  · exact Or.inl hjk
  · right
    have hs := gapsOK_spec hgap (hlen' ▸ hk) hj (Ne.symm hjk)
    have hdj : st'.discs.getD j ((0, 0), 0) = st'.discs[j] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rw [hdj] at hs
    exact separated_of_incl (le_max_left _ _) hinc hs

/-- A closed chain of certified steps. -/
structure Chain where
  wps : List GI
  steps : List StepDatum
  legIdx : List ℕ
  pis : List (List ℕ)

namespace Chain

variable (C : Chain)

def n : ℕ := C.legIdx.length
def wp (k : ℕ) : GI := C.wps.getD k (0, 0)
def st (k : ℕ) : StepDatum := C.steps.getD (C.legIdx.getD k 0) ⟨(0, 0), 0, [], []⟩
def pi (k : ℕ) : List ℕ := C.pis.getD k []
/-- The step after leg `k`; the last leg is followed by the first. -/
def next (k : ℕ) : ℕ := if k + 1 = C.n then 0 else k + 1

/-- The leg check. -/
def legB (k : ℕ) : Bool :=
  decide (C.legIdx.getD k 0 < C.steps.length) &&
    inStepB (C.st k) (C.wp k) && inStepB (C.st k) (C.wp (k + 1)) &&
    inStepB (C.st (C.next k)) (C.wp (k + 1)) && junctionG (C.st k) (C.st (C.next k)) (C.pi k)

/-- One chunk of legs, one kernel declaration each. -/
def chunkB (lo len : ℕ) : Bool := (List.range' lo len).all C.legB

/-- Label after `m` junctions, in the labelling of the step following leg `m - 1`. -/
def lab (m i : ℕ) : ℕ := (C.pis.take m).foldl (fun x π => π.getD x x) i

theorem lab_zero (i : ℕ) : C.lab 0 i = i := by simp [lab]

theorem lab_succ (m i : ℕ) : C.lab (m + 1) i = (C.pi m).getD (C.lab m i) (C.lab m i) := by
  simp only [lab, pi, List.take_add_one, List.foldl_append]
  rcases h : C.pis[m]? with _ | π
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

/-- The closed monodromy, as a list of labels. -/
def closure : List ℕ := (List.range 65).map (C.lab C.n)

/-- The polyline through waypoints `0, …, m + 1`. -/
noncomputable def poly : (m : ℕ) → Path (ptC J (C.wp 0)) (ptC J (C.wp (m + 1)))
  | 0 => MonicFamily.segment _ _
  | m + 1 => (poly m).trans (MonicFamily.segment _ _)

end Chain

variable {J K}

theorem norm_le_of_inStepB {st : StepDatum} {w : GI} (h : inStepB st w = true) :
    ‖ptC J w - gc st.τ / 2 ^ J‖ ≤ (st.S : ℝ) / 2 ^ J := by
  simp only [inStepB, decide_eq_true_eq] at h
  have hdiff : ptC J w - gc st.τ / 2 ^ J = gc (w.1 - st.τ.1, w.2 - st.τ.2) / 2 ^ J := by
    simp only [ptC, gc]; push_cast; ring
  rw [hdiff, norm_div, norm_pow, Complex.norm_ofNat]
  gcongr
  have hsq : ‖gc (w.1 - st.τ.1, w.2 - st.τ.2)‖ ^ 2 ≤ (st.S : ℝ) ^ 2 := by
    rw [normSq_gc]; exact_mod_cast h
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

/-- Points of a segment between two points of a closed disc stay in the disc. -/
theorem segment_mem {a b c : ℂ} {r : ℝ} (ha : ‖a - c‖ ≤ r) (hb : ‖b - c‖ ≤ r) (u : unitInterval) :
    ‖MonicFamily.segment a b u - c‖ ≤ r := by
  rw [segment_apply]
  have hu0 := u.2.1
  have hu1 := u.2.2
  have : a + ((u : ℝ) : ℂ) * (b - a) - c = ((1 - (u : ℝ) : ℝ) : ℂ) * (a - c) + ((u : ℝ) : ℂ) * (b - c) := by
    push_cast; ring
  rw [this]
  calc ‖((1 - (u : ℝ) : ℝ) : ℂ) * (a - c) + ((u : ℝ) : ℂ) * (b - c)‖
      ≤ ‖((1 - (u : ℝ) : ℝ) : ℂ) * (a - c)‖ + ‖((u : ℝ) : ℂ) * (b - c)‖ := norm_add_le _ _
    _ = (1 - u) * ‖a - c‖ + u * ‖b - c‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
          Real.norm_of_nonneg hu0]
    _ ≤ (1 - u) * r + u * r := by gcongr
    _ = r := by ring

theorem regular_of_cert {st : StepDatum} (hc : st.Cert J K) {t : ℂ}
    (ht : ‖t - gc st.τ / 2 ^ J‖ ≤ (st.S : ℝ) / 2 ^ J) : t ∈ paperMonicFamily.regular :=
  (hc.1 t ht).2

theorem StepDatum.disc_mem {st : StepDatum} (hc : st.Cert J K) {i : ℕ} (hi : i < 65) :
    st.disc i ∈ st.discs := by
  have hlen := hc.2.1
  simp only [StepDatum.disc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hi),
    Option.getD_some]
  exact List.getElem_mem _

/-- The index version of `junction`. -/
theorem junction_idx {st st' : StepDatum} {π : List ℕ} (hj : junctionB st st' π = true)
    (hc : st.Cert J K) (hc' : st'.Cert J K) {i : ℕ} (hi : i < 65) {t : ℂ}
    (ht : ‖t - gc st'.τ / 2 ^ J‖ ≤ (st'.S : ℝ) / 2 ^ J) {x : ℂ} (hx : (paperFamily t).eval x = 0)
    (hxi : x ∈ ball (discCentre K (st.disc i)) (discRadius K (st.disc i))) :
    π.getD i i < 65 ∧ x ∈ ball (discCentre K (st'.disc (π.getD i i))) (discRadius K (st'.disc (π.getD i i))) := by
  have hlen := hc.2.1
  obtain ⟨hπ, hrow⟩ := junRows_spec hj i (hlen ▸ hi)
  rw [Nat.zero_add] at hπ hrow
  refine ⟨hπ, ?_⟩
  obtain ⟨hstep', hlen', hps', -⟩ := hc'
  obtain ⟨r, hr, hxr⟩ := exists_disc_of_root hstep' hlen' (pairwise_of_pairwiseSeparated K hps') ht hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  have hdi : st.disc i = st.discs[i]'(hlen ▸ hi) := by
    simp only [StepDatum.disc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hi),
      Option.getD_some]
  have hdj : st'.disc j = st'.discs[j] := by
    simp only [StepDatum.disc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  rcases sepRow_spec hrow j hj with h | h
  · rw [Nat.zero_add] at h
    rw [← h, hdj]; exact hxr
  · rw [hdi] at hxi
    exact absurd hxr (Set.disjoint_left.mp (disjoint_of_separated K h) hxi)

/-! ### Paths in the base -/

theorem basePath_trans {M : MonicFamily} {a b c : M.Base} (γ : Path a.1 b.1) (γ' : Path b.1 c.1)
    (h : ∀ u, (γ.trans γ') u ∈ M.regular) (h₁ : ∀ u, γ u ∈ M.regular) (h₂ : ∀ u, γ' u ∈ M.regular) :
    basePath (γ.trans γ') h = (basePath γ h₁).trans (basePath γ' h₂) := by
  ext u
  simp only [basePath_apply, Path.trans_apply]
  split_ifs <;> rfl

namespace Chain

variable {C : Chain}

/-- The checks, unpacked for leg `k`. -/
structure LegOK (J K : ℕ) (C : Chain) (k : ℕ) : Prop where
  cert : (C.st k).Cert J K
  certNext : (C.st (C.next k)).Cert J K
  start : ‖ptC J (C.wp k) - gc (C.st k).τ / 2 ^ J‖ ≤ ((C.st k).S : ℝ) / 2 ^ J
  stop : ‖ptC J (C.wp (k + 1)) - gc (C.st k).τ / 2 ^ J‖ ≤ ((C.st k).S : ℝ) / 2 ^ J
  stopNext : ‖ptC J (C.wp (k + 1)) - gc (C.st (C.next k)).τ / 2 ^ J‖ ≤
    ((C.st (C.next k)).S : ℝ) / 2 ^ J
  junction : junctionB (C.st k) (C.st (C.next k)) (C.pi k) = true

theorem st_mem {k : ℕ} (h : C.legIdx.getD k 0 < C.steps.length) : C.st k ∈ C.steps := by
  unfold st
  generalize C.legIdx.getD k 0 = j at h ⊢
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem _

theorem legOK (hcert : ∀ s ∈ C.steps, s.Cert J K) (hlegs : ∀ k < C.n, C.legB k = true)
    {k : ℕ} (hk : k < C.n) : LegOK J K C k := by
  have h := hlegs k hk
  simp only [legB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hidx, h1⟩, h2⟩, h3⟩, hj⟩ := h
  have hnext : C.next k < C.n := by
    unfold next; split_ifs <;> omega
  have hidx' : C.legIdx.getD (C.next k) 0 < C.steps.length := by
    have h' := hlegs _ hnext
    simp only [legB, Bool.and_eq_true, decide_eq_true_eq] at h'
    exact h'.1.1.1.1
  have hc' := hcert _ (st_mem hidx')
  exact ⟨hcert _ (st_mem hidx), hc', norm_le_of_inStepB h1,
    norm_le_of_inStepB h2, norm_le_of_inStepB h3, junctionB_of_junctionG hc'.2.1 hc'.2.2.2 hj⟩

theorem poly_regular (hcert : ∀ s ∈ C.steps, s.Cert J K) (hlegs : ∀ k < C.n, C.legB k = true) :
    ∀ m < C.n, ∀ u, C.poly J m u ∈ paperMonicFamily.regular
  | 0, hm, u => by
    have hl := legOK hcert hlegs hm
    exact regular_of_cert hl.cert (segment_mem hl.start hl.stop u)
  | m + 1, hm, u => by
    have hl := legOK hcert hlegs hm
    simp only [poly, Path.trans_apply]
    split_ifs
    · exact poly_regular hcert hlegs m (by omega) _
    · exact regular_of_cert hl.cert (segment_mem hl.start hl.stop _)

theorem lab_lt (hcert : ∀ s ∈ C.steps, s.Cert J K) (hlegs : ∀ k < C.n, C.legB k = true) :
    ∀ m ≤ C.n, ∀ i < 65, C.lab m i < 65
  | 0, _, i, hi => by rw [lab_zero]; exact hi
  | m + 1, hm, i, hi => by
    rw [lab_succ]
    have hl := legOK hcert hlegs (show m < C.n by omega)
    have hlab := lab_lt hcert hlegs m (by omega) i hi
    have := (junRows_spec hl.junction _ (hl.cert.2.1 ▸ hlab)).1
    rwa [Nat.zero_add] at this

/-- One leg: along the segment of leg `k`, the root in disc `j` of step `k` ends in disc
`πₖ(j)` of the next step. -/
theorem leg_root (hl : LegOK J K C k) {c b : paperMonicFamily.Base} (hc : c.1 = ptC J (C.wp k))
    (hb : b.1 = ptC J (C.wp (k + 1)))
    (hreg : ∀ u, (MonicFamily.segment (ptC J (C.wp k)) (ptC J (C.wp (k + 1)))).cast hc hb u ∈
      paperMonicFamily.regular)
    {j : ℕ} (hj : j < 65) (f : paperMonicFamily.Fiber c)
    (hf : f.root ∈ ball (discCentre K ((C.st k).disc j)) (discRadius K ((C.st k).disc j))) :
    Fiber.root (t := b) (paperMonicFamily.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (basePath ((MonicFamily.segment _ _).cast hc hb) hreg)) f) ∈
      ball (discCentre K ((C.st (C.next k)).disc ((C.pi k).getD j j)))
        (discRadius K ((C.st (C.next k)).disc ((C.pi k).getD j j))) := by
  have hmem := (C.st k).disc_mem hl.cert hj
  have hin := monodromy_root_mem_ball (basePath ((MonicFamily.segment _ _).cast hc hb) hreg) f
    (c := discCentre K ((C.st k).disc j)) (R := discRadius K ((C.st k).disc j))
    (fun u x hx => by
      rw [paperMonicFamily_P]
      exact ((hl.cert.1 _ (segment_mem hl.start hl.stop u)).1 _ hmem).1 x hx) hf
  have hroot := Fiber.isRoot (M := paperMonicFamily) (t := b)
    (paperMonicFamily.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (basePath ((MonicFamily.segment _ _).cast hc hb) hreg)) f)
  rw [paperMonicFamily_P] at hroot
  exact (junction_idx hl.junction hl.cert hl.certNext hj (by rw [hb]; exact hl.stopNext) hroot hin).2

/-- **Chain transport.** After legs `0, …, m`, the root that started in disc `i` of step 0
lies in disc `lab (m+1) i` of the step following leg `m`. -/
theorem chain_root (hcert : ∀ s ∈ C.steps, s.Cert J K) (hlegs : ∀ k < C.n, C.legB k = true) :
    ∀ m < C.n, ∀ (a b : paperMonicFamily.Base) (ha : a.1 = ptC J (C.wp 0))
      (hb : b.1 = ptC J (C.wp (m + 1))) (hreg : ∀ u, (C.poly J m).cast ha hb u ∈ paperMonicFamily.regular)
      (i : ℕ), i < 65 → ∀ e : paperMonicFamily.Fiber a,
      e.root ∈ ball (discCentre K ((C.st 0).disc i)) (discRadius K ((C.st 0).disc i)) →
      Fiber.root (t := b) (paperMonicFamily.isCoveringMap.monodromy
        (Path.Homotopic.Quotient.mk (basePath ((C.poly J m).cast ha hb) hreg)) e) ∈
        ball (discCentre K ((C.st (C.next m)).disc (C.lab (m + 1) i)))
          (discRadius K ((C.st (C.next m)).disc (C.lab (m + 1) i)))
    := by
  intro m
  induction m with
  | zero =>
    intro hm a b ha hb hreg i hi e he
    rw [lab_succ, lab_zero]
    exact leg_root (legOK hcert hlegs hm) ha hb hreg hi e he
  | succ m ih =>
    intro hm a b ha hb hreg i hi e he
    have hl := legOK hcert hlegs hm
    let c : paperMonicFamily.Base := ⟨ptC J (C.wp (m + 1)), regular_of_cert hl.cert hl.start⟩
    have hreg₁ : ∀ u, (C.poly J m).cast ha (rfl : c.1 = _) u ∈ paperMonicFamily.regular :=
      poly_regular hcert hlegs m (by omega)
    have hreg₂ : ∀ u, (MonicFamily.segment (ptC J (C.wp (m + 1))) (ptC J (C.wp (m + 1 + 1)))).cast
        (rfl : c.1 = _) hb u ∈ paperMonicFamily.regular :=
      fun u => regular_of_cert hl.cert (segment_mem hl.start hl.stop u)
    have hsplit : basePath ((C.poly J (m + 1)).cast ha hb) hreg =
        (basePath ((C.poly J m).cast ha (rfl : c.1 = _)) hreg₁).trans
          (basePath ((MonicFamily.segment _ _).cast rfl hb) hreg₂) := by
      ext u
      show (C.poly J (m + 1)) u = _
      rw [poly, Path.trans_apply]
      simp only [Path.trans_apply]
      split_ifs <;> rfl
    rw [hsplit, monodromy_trans]
    have hnext : C.next m = m + 1 := by unfold next; split_ifs <;> omega
    have ih' := ih (by omega) a c ha rfl hreg₁ i hi e he
    rw [hnext] at ih'
    rw [lab_succ C (m + 1)]
    exact leg_root hl rfl hb hreg₂ (lab_lt hcert hlegs (m + 1) (by omega) i hi) _ ih'

/-- **Closed chains.** If the last waypoint is the first, the polyline is a loop at the
base point, and its monodromy acts on disc labels of step 0 by `lab C C.n`. -/
theorem loop_root (hcert : ∀ s ∈ C.steps, s.Cert J K) (hlegs : ∀ k < C.n, C.legB k = true)
    (hn : 0 < C.n) (hclose : C.wp C.n = C.wp 0) (b : paperMonicFamily.Base)
    (hb0 : b.1 = ptC J (C.wp 0)) :
    ∃ γ : Path b b, (∀ u, (γ u).1 = C.poly J (C.n - 1) u) ∧
      ∀ i < 65, ∀ f : paperMonicFamily.Fiber b,
        f.root ∈ ball (discCentre K ((C.st 0).disc i)) (discRadius K ((C.st 0).disc i)) →
        Fiber.root (t := b) (paperMonicFamily.isCoveringMap.monodromy
          (Path.Homotopic.Quotient.mk γ) f) ∈
          ball (discCentre K ((C.st 0).disc (C.lab C.n i))) (discRadius K ((C.st 0).disc (C.lab C.n i))) := by
  have hm : C.n - 1 < C.n := by omega
  have hb : b.1 = ptC J (C.wp (C.n - 1 + 1)) := by rw [Nat.sub_add_cancel hn, hclose, hb0]
  have hreg : ∀ u, (C.poly J (C.n - 1)).cast hb0 hb u ∈ paperMonicFamily.regular :=
    poly_regular hcert hlegs _ hm
  refine ⟨basePath ((C.poly J (C.n - 1)).cast hb0 hb) hreg, fun u => rfl, fun i hi f hf => ?_⟩
  have h := chain_root hcert hlegs (C.n - 1) hm b b hb0 hb hreg i hi f hf
  have hnext : C.next (C.n - 1) = 0 := by unfold next; simp [Nat.sub_add_cancel hn]
  have hlab : C.lab (C.n - 1 + 1) i = C.lab C.n i := by rw [Nat.sub_add_cancel hn]
  rwa [hnext, hlab] at h

end Chain

/-! ### Labelling a fibre by the discs of a step -/

section Labels

variable {st : StepDatum} (hc : st.Cert J K) {t : paperMonicFamily.Base}
  (ht : ‖t.1 - gc st.τ / 2 ^ J‖ ≤ (st.S : ℝ) / 2 ^ J)

variable (K) in
/-- The root `x` lies in disc `i` of the step. -/
def InDisc (st : StepDatum) (i : ℕ) (x : ℂ) : Prop :=
  x ∈ ball (discCentre K (st.disc i)) (discRadius K (st.disc i))

include hc ht in
theorem exists_label (f : paperMonicFamily.Fiber t) : ∃ i, i < 65 ∧ InDisc K st i f.root := by
  obtain ⟨hstep, hlen, hps, -⟩ := hc
  have hx := Fiber.isRoot f
  rw [paperMonicFamily_P] at hx
  obtain ⟨r, hr, hxr⟩ := exists_disc_of_root hstep hlen (pairwise_of_pairwiseSeparated K hps) ht hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  refine ⟨j, hlen ▸ hj, ?_⟩
  simp only [InDisc, StepDatum.disc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some]
  exact hxr

include hc in
theorem label_unique {i j : ℕ} (hi : i < 65) (hj : j < 65) {x : ℂ} (hxi : InDisc K st i x)
    (hxj : InDisc K st j x) : i = j := by
  obtain ⟨-, hlen, hps, -⟩ := hc
  have hpw := List.pairwise_iff_getElem.mp (pairwise_of_pairwiseSeparated K hps)
  have hd : ∀ k (hk : k < 65), st.disc k = st.discs[k]'(hlen ▸ hk) := fun k hk => by
    simp only [StepDatum.disc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hk),
      Option.getD_some]
  simp only [InDisc, hd i hi, hd j hj] at hxi hxj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact Set.disjoint_left.mp (hpw i j (hlen ▸ hi) (hlen ▸ hj) h) hxi hxj
  · exact Set.disjoint_left.mp (hpw j i (hlen ▸ hj) (hlen ▸ hi) h) hxj hxi

include hc ht in
theorem exists_fiber_in (i : ℕ) (hi : i < 65) : ∃ f : paperMonicFamily.Fiber t, InDisc K st i f.root := by
  classical
  have hmem := st.disc_mem hc hi
  have h1 := ((hc.1 t.1 ht).1 _ hmem).2
  unfold HexRootsMathlib.rootsInDisc at h1
  obtain ⟨x, hx, hxb⟩ := Multiset.countP_pos.mp (by rw [h1]; exact Nat.one_pos)
  have hp := (paperFamily_monic t.1).ne_zero
  have hroot : (paperMonicFamily.P t.1).eval x = 0 := by
    rw [paperMonicFamily_P]; exact (mem_roots hp).mp hx
  exact ⟨paperMonicFamily.mkFiber t x hroot, hxb⟩

include hc ht in
theorem fiber_unique {i : ℕ} (hi : i < 65) {f g : paperMonicFamily.Fiber t}
    (hf : InDisc K st i f.root) (hg : InDisc K st i g.root) : f = g := by
  have hmem := st.disc_mem hc hi
  have h1 := ((hc.1 t.1 ht).1 _ hmem).2
  have hfr := Fiber.isRoot f
  have hgr := Fiber.isRoot g
  rw [paperMonicFamily_P] at hfr hgr
  exact Fiber.ext (eq_of_rootsInDisc_eq_one (paperFamily_monic t.1).ne_zero h1 hfr hf hgr hg)

/-- The label of a fibre point: the disc of the step containing its root. -/
noncomputable def label (f : paperMonicFamily.Fiber t) : Fin 65 :=
  ⟨Classical.choose (exists_label hc ht f), (Classical.choose_spec (exists_label hc ht f)).1⟩

theorem label_spec (f : paperMonicFamily.Fiber t) : InDisc K st (label hc ht f) f.root :=
  (Classical.choose_spec (exists_label hc ht f)).2

theorem label_eq {f : paperMonicFamily.Fiber t} {i : ℕ} (hi : i < 65) (h : InDisc K st i f.root) :
    (label hc ht f : ℕ) = i :=
  label_unique hc (label hc ht f).2 hi (label_spec hc ht f) h

/-- Fibre points are in bijection with the 65 discs of a certified step. -/
noncomputable def labelEquiv : paperMonicFamily.Fiber t ≃ Fin 65 :=
  Equiv.ofBijective (label hc ht) ⟨fun f g h =>
    fiber_unique hc ht (label hc ht f).2 (label_spec hc ht f) (h ▸ label_spec hc ht g),
    fun i => by
      obtain ⟨f, hf⟩ := exists_fiber_in hc ht i i.2
      exact ⟨f, Fin.ext (label_eq hc ht i.2 hf)⟩⟩

theorem labelEquiv_symm_spec (i : Fin 65) : InDisc K st i ((labelEquiv hc ht).symm i).root := by
  have h := label_spec hc ht ((labelEquiv hc ht).symm i)
  have : label hc ht ((labelEquiv hc ht).symm i) = i := (labelEquiv hc ht).apply_symm_apply i
  rwa [this] at h

end Labels

namespace Chain

variable {C : Chain}

/-- **Loop monodromy in labels.** For a closed chain based at a parameter of step 0, with
fibre points labelled by the discs of step 0, the monodromy of the polyline loop is
`i ↦ lab C C.n i`. -/
theorem loop_monodromy (hcert : ∀ s ∈ C.steps, s.Cert J K) (hlegs : ∀ k < C.n, C.legB k = true)
    (hn : 0 < C.n) (hclose : C.wp C.n = C.wp 0) (b : paperMonicFamily.Base)
    (hb0 : b.1 = ptC J (C.wp 0)) (st : StepDatum) (hst : C.st 0 = st) :
    ∃ (hc : st.Cert J K) (ht : ‖b.1 - gc st.τ / 2 ^ J‖ ≤ (st.S : ℝ) / 2 ^ J)
      (γ : Path b b), (∀ u, (γ u).1 = C.poly J (C.n - 1) u) ∧
      ∀ i : Fin 65, (labelEquiv hc ht (paperMonicFamily.isCoveringMap.monodromy
        (Path.Homotopic.Quotient.mk γ) ((labelEquiv hc ht).symm i))).val = C.lab C.n i := by
  subst hst
  have hl := legOK hcert hlegs hn
  have ht : ‖b.1 - gc (C.st 0).τ / 2 ^ J‖ ≤ ((C.st 0).S : ℝ) / 2 ^ J := hb0 ▸ hl.start
  obtain ⟨γ, hγ, hmono⟩ := loop_root hcert hlegs hn hclose b hb0
  refine ⟨hl.cert, ht, γ, hγ, fun i => ?_⟩
  exact label_eq hl.cert ht (lab_lt hcert hlegs C.n le_rfl i i.2)
    (hmono i i.2 _ (labelEquiv_symm_spec hl.cert ht i))

/-- Chunked leg checks assemble into all legs. -/
def chunkStarts : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | lo, l :: ls => (lo, l) :: chunkStarts (lo + l) ls

theorem chunkB_of_chunks : ∀ (lo : ℕ) (lens : List ℕ),
    (∀ p ∈ chunkStarts lo lens, C.chunkB p.1 p.2 = true) → C.chunkB lo lens.sum = true
  | lo, [], _ => by simp [chunkB]
  | lo, l :: ls, h => by
    simp only [chunkStarts, List.forall_mem_cons] at h
    have ih := chunkB_of_chunks (lo + l) ls h.2
    simp only [chunkB, List.sum_cons, List.all_eq_true] at h ih ⊢
    intro k hk
    rw [← List.range'_append (s := lo) (m := l) (n := ls.sum) (step := 1)] at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact h.1 k hk
    · exact ih k (by simpa using hk)

theorem legs_of_chunkB (h : C.chunkB 0 C.n = true) : ∀ k < C.n, C.legB k = true := by
  intro k hk
  simp only [chunkB, List.all_eq_true] at h
  exact h k (by simp [List.mem_range'_1]; omega)

end Chain

end Sz8.Monodromy
