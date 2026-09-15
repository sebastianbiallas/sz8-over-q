import Sz8.Monodromy.PackedCheck
import Sz8.Monodromy.IntColumns
import Sz8.Monodromy.PaperCovering

/-!
A certified continuation step for the paper's family.

`stepCheck` bundles, for one parameter disc `|t - t₀| ≤ h`:
* the packed Rouché check of each of 65 root discs;
* pairwise disjointness of the root discs;
* the structural conditions used by the soundness proofs.

`stepCheck_sound`: for every `t` in the parameter disc, each root disc contains exactly
one root of `f(X, t)` and none on its boundary circle, and `t` is regular (all 65 roots
simple). The integer columns are `13^182` times the exact rational columns, checked
entry by entry.
-/

open Polynomial Metric

namespace Sz8.Monodromy
open GaussPoly

set_option maxRecDepth 100000

/-! ### The integer columns are `13^182` times the rational ones -/

def rowMatch (L : ℚ) : List ℚ → List GI → Bool
  | [], [] => true
  | a :: as, g :: gs => (a * L == (g.1 : ℚ)) && (g.2 == 0) && rowMatch L as gs
  | _, _ => false

def colsMatch (L : ℚ) : List (List ℚ) → List (List GI) → Bool
  | [], [] => true
  | q :: qs, z :: zs => rowMatch L q z && colsMatch L qs zs
  | _, _ => false

theorem complexPoly_eq_toPolyC (L : ℚ) (hL : L ≠ 0) :
    ∀ (q : List ℚ) (z : List GI), rowMatch L q z = true →
      complexPoly q = C ((L : ℂ)⁻¹) * toPolyC z
  | [], [], _ => by simp [complexPoly, toPolyC]
  | a :: as, g :: gs, h => by
    simp only [rowMatch, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨ha, hg⟩, hrest⟩ := h
    rw [complexPoly, toPolyC, complexPoly_eq_toPolyC L hL as gs hrest]
    have : (a : ℂ) = (L : ℂ)⁻¹ * gc g := by
      simp only [gc, hg, Int.cast_zero, zero_mul, add_zero]
      have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
      rw [show ((g.1 : ℤ) : ℂ) = ((g.1 : ℚ) : ℂ) by push_cast; rfl, ← ha]
      push_cast; field_simp
    rw [this, C_mul, mul_add, mul_left_comm]
  | [], _ :: _, h => by simp [rowMatch] at h
  | _ :: _, [], h => by simp [rowMatch] at h

theorem complexFamily_eq_famPoly (L : ℚ) (hL : L ≠ 0) (t : ℂ) :
    ∀ (qs : List (List ℚ)) (zs : List (List GI)), colsMatch L qs zs = true →
      complexFamily qs t = C ((L : ℂ)⁻¹) * famPoly zs t
  | [], [], _ => by simp [complexFamily, famPoly]
  | q :: qs, z :: zs, h => by
    simp only [colsMatch, Bool.and_eq_true] at h
    rw [complexFamily, famPoly, complexPoly_eq_toPolyC L hL q z h.1,
      complexFamily_eq_famPoly L hL t qs zs h.2]
    ring
  | [], _ :: _, h => by simp [colsMatch] at h
  | _ :: _, [], h => by simp [colsMatch] at h

theorem intCols_match : colsMatch (13 ^ 182) originalColumns intCols = true := by decide +kernel

theorem paperFamily_eq_famPoly (t : ℂ) :
    paperFamily t = C (((13 ^ 182 : ℚ) : ℂ)⁻¹) * famPoly intCols t :=
  complexFamily_eq_famPoly _ (by norm_num) t _ _ intCols_match

theorem intCols_length : intCols.length = 8 := by decide +kernel

/-! ### Disjoint discs -/

/-- The centre and radius of a disc datum. -/
noncomputable def discCentre (K : ℕ) (q : GI × ℕ) : ℂ := gc q.1 / 2 ^ K
noncomputable def discRadius (K : ℕ) (q : GI × ℕ) : ℝ := (q.2 : ℝ) / 2 ^ K

/-- Squared-distance separation of two discs (same scale). -/
def separated (q q' : GI × ℕ) : Bool :=
  decide (((q.2 + q'.2 : ℕ) : ℤ) ^ 2 ≤ nsq (q.1.1 - q'.1.1, q.1.2 - q'.1.2))

def pairwiseSeparated : List (GI × ℕ) → Bool
  | [] => true
  | q :: qs => qs.all (separated q) && pairwiseSeparated qs

theorem disjoint_of_separated (K : ℕ) {q q' : GI × ℕ} (h : separated q q' = true) :
    Disjoint (ball (discCentre K q) (discRadius K q)) (ball (discCentre K q') (discRadius K q')) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [mem_ball, dist_eq_norm, discCentre, discRadius] at hx hx'
  simp only [separated, decide_eq_true_eq] at h
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  have hsep : (q.2 + q'.2 : ℝ) ≤ ‖gc q.1 - gc q'.1‖ := by
    have hsq : ((q.2 + q'.2 : ℕ) : ℝ) ^ 2 ≤ ‖gc (q.1.1 - q'.1.1, q.1.2 - q'.1.2)‖ ^ 2 := by
      rw [normSq_gc]; exact_mod_cast h
    have : gc (q.1.1 - q'.1.1, q.1.2 - q'.1.2) = gc q.1 - gc q'.1 := by
      simp only [gc]; push_cast; ring
    rw [this] at hsq
    have := le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq
    exact_mod_cast this
  have htri : ‖gc q.1 / 2 ^ K - gc q'.1 / 2 ^ K‖ ≤ ‖x - gc q.1 / 2 ^ K‖ + ‖x - gc q'.1 / 2 ^ K‖ := by
    calc ‖gc q.1 / 2 ^ K - gc q'.1 / 2 ^ K‖ = ‖(x - gc q'.1 / 2 ^ K) - (x - gc q.1 / 2 ^ K)‖ := by
          congr 1; ring
      _ ≤ ‖x - gc q'.1 / 2 ^ K‖ + ‖x - gc q.1 / 2 ^ K‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have hscale : ‖gc q.1 / 2 ^ K - gc q'.1 / 2 ^ K‖ = ‖gc q.1 - gc q'.1‖ / 2 ^ K := by
    rw [← sub_div, norm_div, norm_pow, Complex.norm_ofNat]
  rw [hscale] at htri
  have : (q.2 + q'.2 : ℝ) / 2 ^ K ≤ ‖gc q.1 - gc q'.1‖ / 2 ^ K := by gcongr
  have h1 : (q.2 : ℝ) / 2 ^ K + q'.2 / 2 ^ K < ‖x - gc q.1 / 2 ^ K‖ + ‖x - gc q'.1 / 2 ^ K‖ + 0 := by
    linarith [add_div (q.2 : ℝ) q'.2 (2 ^ K)]
  linarith

theorem pairwise_of_pairwiseSeparated (K : ℕ) : ∀ {ds : List (GI × ℕ)}, pairwiseSeparated ds = true →
    ds.Pairwise fun q q' =>
      Disjoint (ball (discCentre K q) (discRadius K q)) (ball (discCentre K q') (discRadius K q'))
  | [], _ => List.Pairwise.nil
  | q :: qs, h => by
    simp only [pairwiseSeparated, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons (fun q' hq' => disjoint_of_separated K (h.1 q' hq'))
      (pairwise_of_pairwiseSeparated K h.2)

/-! ### Counting: 65 disjoint discs with one root each make every root simple -/

theorem countP_or_of_disjoint {α : Type*} (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (s : Multiset α) (h : ∀ x ∈ s, ¬ (p x ∧ q x)) :
    s.countP (fun x => p x ∨ q x) = s.countP p + s.countP q := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have ih' := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    have ha := h a (Multiset.mem_cons_self _ _)
    simp only [Multiset.countP_cons, ih']
    by_cases hp : p a <;> by_cases hq : q a <;> simp_all <;> omega

theorem count_le_countP {α : Type*} [DecidableEq α] (p : α → Prop) [DecidablePred p]
    (s : Multiset α) {a : α} (ha : p a) : s.count a ≤ s.countP p := by
  induction s using Multiset.induction with
  | empty => simp
  | cons b s ih =>
    simp only [Multiset.count_cons, Multiset.countP_cons]
    split_ifs with h1 h2 <;> subst_vars <;> first | omega | exact absurd ha ‹_›

theorem regular_of_discs (p : ℂ[X]) (hp : p ≠ 0) (ds : List (ℂ × ℝ))
    (hdeg : p.natDegree = ds.length)
    (hdisj : ds.Pairwise fun d d' => Disjoint (ball d.1 d.2) (ball d'.1 d'.2))
    (hone : ∀ d ∈ ds, HexRootsMathlib.rootsInDisc p d.1 d.2 = 1) :
    ∀ x, p.eval x = 0 → p.derivative.eval x ≠ 0 := by
  classical
  set M := p.roots
  have hcard : M.card = ds.length := by
    rw [← hdeg, (IsAlgClosed.splits p).natDegree_eq_card_roots]
  -- The discs cover all roots.
  have hcover : M.countP (fun x => ∃ d ∈ ds, x ∈ ball d.1 d.2) = ds.length := by
    clear hcard hdeg
    induction ds with
    | nil => simp
    | cons d ds ih =>
      have hd := hone d (List.mem_cons_self ..)
      simp only [List.mem_cons, exists_eq_or_imp]
      rw [countP_or_of_disjoint]
      · rw [ih (List.pairwise_cons.mp hdisj).2 (fun d' hd' => hone d' (List.mem_cons_of_mem _ hd'))]
        simp only [HexRootsMathlib.rootsInDisc] at hd
        rw [hd, List.length_cons, add_comm]
      · rintro x - ⟨hx, d', hd', hx'⟩
        exact Set.disjoint_left.mp ((List.pairwise_cons.mp hdisj).1 d' hd') hx hx'
  have hall : ∀ x ∈ M, ∃ d ∈ ds, x ∈ ball d.1 d.2 :=
    Multiset.countP_eq_card.mp (hcover.trans hcard.symm)
  intro x hx hd
  have hxM : x ∈ M := (mem_roots hp).mpr hx
  obtain ⟨d, hdmem, hxd⟩ := hall x hxM
  have hmult : 1 < rootMultiplicity x p :=
    (one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hx, hd⟩
  have hle : M.count x ≤ M.countP (fun y => y ∈ ball d.1 d.2) := count_le_countP _ M hxd
  have h1 := hone d hdmem
  simp only [HexRootsMathlib.rootsInDisc] at h1
  rw [count_roots, h1] at hle
  omega

/-! ### The step check -/

/-- Per-step conditions: structure, 65 separated discs, and the a-priori digit bound
(against `Wmax ≥ 1 + n1 γ` for every centre). -/
def stepPre (J K b : ℕ) (τ : GI) (Wmax : ℕ) (discs : List (GI × ℕ)) : Bool :=
  let D := stepRows J τ intCols
  decide (0 < b) && (D.length == 8) && rowsShort D && (discs.length == 65) &&
    pairwiseSeparated discs && (discs.all fun q => decide (1 + n1 q.1 ≤ Wmax)) &&
    ((D.map (scaleUp K 65)).all fun C => decide (maj Wmax C < 2 ^ (b - 1)))

/-- The packed Rouché checks for a slice of the discs (one kernel declaration each). -/
def sliceCheck (J K b : ℕ) (τ : GI) (S : ℕ) (slice : List (GI × ℕ)) : Bool :=
  let A := packCols b ((stepRows J τ intCols).map (scaleUp K 65))
  slice.all fun q => packedCheck A b S q.1 q.2

/-- What a certified step provides, for every parameter in the step disc. -/
def StepCertified (J K : ℕ) (τ : GI) (S : ℕ) (discs : List (GI × ℕ)) : Prop :=
  ∀ t : ℂ, ‖t - gc τ / 2 ^ J‖ ≤ (S : ℝ) / 2 ^ J →
    (∀ q ∈ discs,
      (∀ x ∈ sphere (discCentre K q) (discRadius K q), (paperFamily t).eval x ≠ 0) ∧
      HexRootsMathlib.rootsInDisc (paperFamily t) (discCentre K q) (discRadius K q) = 1) ∧
    t ∈ paperMonicFamily.regular

theorem stepCertified_of_checks {J K b : ℕ} {τ : GI} {S Wmax : ℕ}
    {slices : List (List (GI × ℕ))}
    (hpre : stepPre J K b τ Wmax slices.flatten = true)
    (hslices : ∀ sl ∈ slices, sliceCheck J K b τ S sl = true) :
    StepCertified J K τ S slices.flatten := by
  intro t ht
  set discs := slices.flatten
  simp only [stepPre, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hpre
  obtain ⟨⟨⟨⟨⟨⟨hb, hD⟩, hshort⟩, hlen⟩, hsep⟩, hW⟩, hcrude⟩ := hpre
  have hL : (((13 ^ 182 : ℚ) : ℂ)⁻¹) ≠ 0 := by norm_num
  have hdisc : ∀ q ∈ discs,
      (∀ x ∈ sphere (discCentre K q) (discRadius K q), (paperFamily t).eval x ≠ 0) ∧
      HexRootsMathlib.rootsInDisc (paperFamily t) (discCentre K q) (discRadius K q) = 1 := by
    intro q hq
    obtain ⟨sl, hsl, hqsl⟩ := List.mem_flatten.mp hq
    have hpk := List.all_eq_true.mp (hslices sl hsl) q hqsl
    have hcrude' : ∀ C ∈ (stepRows J τ intCols).map (scaleUp K 65), maj (1 + n1 q.1) C < 2 ^ (b - 1) :=
      fun C hC => (maj_mono (hW q hq) C).trans_lt (hcrude C hC)
    have hc := discCheck_of_packedCheck _ K b S q.1 q.2 hb hD hshort hcrude' hpk
    obtain ⟨h1, h2⟩ := discCheck_sound intCols (by rw [intCols_length]) J K τ S q.1 q.2
      hshort hc ht
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [paperFamily_eq_famPoly, eval_mul, eval_C]
      exact mul_ne_zero hL (h1 x hx)
    · simp only [HexRootsMathlib.rootsInDisc, paperFamily_eq_famPoly, roots_C_mul _ hL] at h2 ⊢
      exact h2
  refine ⟨hdisc, ?_⟩
  exact regular_of_discs (paperFamily t) (paperFamily_monic t).ne_zero
    (discs.map fun q => (discCentre K q, discRadius K q))
    (by rw [paperFamily_natDegree, List.length_map, hlen])
    (by rw [List.pairwise_map]; exact pairwise_of_pairwiseSeparated K hsep)
    (by
      intro d hd
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
      exact (hdisc q hq).2)

end Sz8.Monodromy
