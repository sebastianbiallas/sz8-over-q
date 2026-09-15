import Sz8.Monodromy.StepCheck
import Sz8.Monodromy.RootTransport

/-!
Chaining certified steps into Mathlib monodromy.

* `eq_of_rootsInDisc_eq_one`: a disc with root count 1 contains at most one root.
* `exists_disc_of_root`: at a certified parameter, every root lies in one of the discs.
* `step_monodromy`: along any path of parameters inside a certified step disc, Mathlib's
  monodromy sends the root in disc `q` to the root in the same disc at the endpoint.
* `junction`: if disc `q` of one step is separated from every other disc of the next step,
  then at a shared parameter the root in `q` is the root in the matching disc `q'`.
-/

open Polynomial Metric

namespace Sz8.Monodromy
open GaussPoly MonicFamily

theorem eq_of_rootsInDisc_eq_one {p : ℂ[X]} (hp : p ≠ 0) {c : ℂ} {R : ℝ}
    (h : HexRootsMathlib.rootsInDisc p c R = 1) {x y : ℂ} (hx : p.eval x = 0) (hxb : x ∈ ball c R)
    (hy : p.eval y = 0) (hyb : y ∈ ball c R) : x = y := by
  classical
  by_contra hne
  unfold HexRootsMathlib.rootsInDisc at h
  rw [Multiset.countP_eq_card_filter] at h
  have hsub : (x ::ₘ y ::ₘ 0) ≤ p.roots.filter (· ∈ ball c R) := by
    rw [Multiset.le_iff_subset (by simp [hne])]
    intro z hz
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hz
    rcases hz with rfl | rfl
    · exact Multiset.mem_filter.mpr ⟨(mem_roots hp).mpr hx, hxb⟩
    · exact Multiset.mem_filter.mpr ⟨(mem_roots hp).mpr hy, hyb⟩
  have := Multiset.card_le_card hsub
  rw [h] at this
  simp at this

/-- Disjoint discs with one root each, as many as the degree, cover all roots. -/
theorem covers_of_discs (p : ℂ[X]) (hp : p ≠ 0) (ds : List (ℂ × ℝ))
    (hdeg : p.natDegree = ds.length)
    (hdisj : ds.Pairwise fun d d' => Disjoint (ball d.1 d.2) (ball d'.1 d'.2))
    (hone : ∀ d ∈ ds, HexRootsMathlib.rootsInDisc p d.1 d.2 = 1) :
    ∀ x, p.eval x = 0 → ∃ d ∈ ds, x ∈ ball d.1 d.2 := by
  classical
  set M := p.roots
  have hcard : M.card = ds.length := by
    rw [← hdeg, (IsAlgClosed.splits p).natDegree_eq_card_roots]
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
  intro x hx
  exact Multiset.countP_eq_card.mp (hcover.trans hcard.symm) x ((mem_roots hp).mpr hx)

/-- At a certified parameter, every root lies in one of the discs. -/
theorem exists_disc_of_root {J K : ℕ} {τ : GI} {S : ℕ} {discs : List (GI × ℕ)}
    (hstep : StepCertified J K τ S discs) (hlen : discs.length = 65)
    (hsep : discs.Pairwise fun q q' =>
      Disjoint (ball (discCentre K q) (discRadius K q)) (ball (discCentre K q') (discRadius K q')))
    {t : ℂ} (ht : ‖t - gc τ / 2 ^ J‖ ≤ (S : ℝ) / 2 ^ J) {x : ℂ} (hx : (paperFamily t).eval x = 0) :
    ∃ q ∈ discs, x ∈ ball (discCentre K q) (discRadius K q) := by
  obtain ⟨hdisc, -⟩ := hstep t ht
  obtain ⟨d, hd, hxd⟩ := covers_of_discs (paperFamily t) (paperFamily_monic t).ne_zero
    (discs.map fun q => (discCentre K q, discRadius K q))
    (by rw [paperFamily_natDegree, List.length_map, hlen])
    (by rw [List.pairwise_map]; exact hsep)
    (by
      intro d hd
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
      exact (hdisc q hq).2) x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
  exact ⟨q, hq, hxd⟩

theorem paperMonicFamily_P : paperMonicFamily.P = paperFamily := by simp only [paperMonicFamily]

/-- One certified step, as Mathlib monodromy along any path inside the step disc. -/
theorem step_monodromy {J K : ℕ} {τ : GI} {S : ℕ} {discs : List (GI × ℕ)}
    (hstep : StepCertified J K τ S discs) {q : GI × ℕ} (hq : q ∈ discs)
    {a b : paperMonicFamily.Base} (γ : Path a b)
    (hγ : ∀ u, ‖(γ u).1 - gc τ / 2 ^ J‖ ≤ (S : ℝ) / 2 ^ J)
    (ea : paperMonicFamily.Fiber a) (eb : paperMonicFamily.Fiber b)
    (ha : ea.root ∈ ball (discCentre K q) (discRadius K q))
    (hb : eb.root ∈ ball (discCentre K q) (discRadius K q)) :
    paperMonicFamily.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) ea = eb := by
  apply monodromy_eq_of_ball γ ea eb (c := discCentre K q) (R := discRadius K q)
  · intro u x hx
    rw [paperMonicFamily_P]
    exact ((hstep _ (hγ u)).1 q hq).1 x hx
  · exact ha
  · intro x hx hxb
    rw [paperMonicFamily_P] at hx
    have hend : ‖b.1 - gc τ / 2 ^ J‖ ≤ (S : ℝ) / 2 ^ J := by
      have := hγ 1
      rwa [γ.target] at this
    have heb := Fiber.isRoot eb
    rw [paperMonicFamily_P] at heb
    exact eq_of_rootsInDisc_eq_one (paperFamily_monic b.1).ne_zero
      ((hstep _ hend).1 q hq).2 hx hxb heb hb

/-- Labels persist across a junction: at a parameter certified by both steps, if disc `q` of
the first step is separated from every disc of the second step except `q'`, then a root in
`q` lies in `q'`. -/
theorem junction {J K : ℕ} {τ' : GI} {S' : ℕ} {discs' : List (GI × ℕ)}
    (hstep' : StepCertified J K τ' S' discs') (hlen' : discs'.length = 65)
    (hsep' : discs'.Pairwise fun q q' =>
      Disjoint (ball (discCentre K q) (discRadius K q)) (ball (discCentre K q') (discRadius K q')))
    {q q' : GI × ℕ}
    (hmatch : ∀ r ∈ discs', r ≠ q' → separated q r = true)
    {t : ℂ} (ht' : ‖t - gc τ' / 2 ^ J‖ ≤ (S' : ℝ) / 2 ^ J)
    {x : ℂ} (hx : (paperFamily t).eval x = 0) (hxq : x ∈ ball (discCentre K q) (discRadius K q)) :
    x ∈ ball (discCentre K q') (discRadius K q') := by
  obtain ⟨r, hr, hxr⟩ := exists_disc_of_root hstep' hlen' hsep' ht' hx
  by_cases hrq : r = q'
  · exact hrq ▸ hxr
  · exact absurd hxr (Set.disjoint_left.mp (disjoint_of_separated K (hmatch r hr hrq)) hxq)

end Sz8.Monodromy
