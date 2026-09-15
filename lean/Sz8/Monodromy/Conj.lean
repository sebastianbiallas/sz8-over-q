import Sz8.Monodromy.Chain

/-!
Complex conjugation of step certificates.

The family has rational coefficients, so `f(conj x, conj t) = conj f(x, t)`. A certified step
therefore certifies its mirror image: `StepDatum.Cert.conj`. The meridian around `ζ₃²` is the
mirror image of the meridian around `ζ₃` traversed backwards, so its chain reuses every kernel
certificate of the first one; only its (cheap) chain checks are replayed.
-/

open Polynomial Metric ComplexConjugate

namespace Sz8.Monodromy
open GaussPoly

/-- Conjugate Gaussian integer. -/
def conjGI (a : GI) : GI := (a.1, -a.2)

def conjDisc (q : GI × ℕ) : GI × ℕ := (conjGI q.1, q.2)

/-- The mirror image of a step. -/
def StepDatum.conj (st : StepDatum) : StepDatum := ⟨conjGI st.τ, st.S, st.discs.map conjDisc, st.gaps⟩

theorem gc_conjGI (a : GI) : gc (conjGI a) = conj (gc a) := by
  apply Complex.ext <;> simp [gc, conjGI]

theorem conj_div_two_pow (z : ℂ) (n : ℕ) : conj (z / 2 ^ n) = conj z / 2 ^ n := by
  rw [map_div₀, map_pow, map_ofNat]

theorem discCentre_conjDisc (K : ℕ) (q : GI × ℕ) : discCentre K (conjDisc q) = conj (discCentre K q) := by
  simp only [discCentre, conjDisc, gc_conjGI, conj_div_two_pow]

theorem discRadius_conjDisc (K : ℕ) (q : GI × ℕ) : discRadius K (conjDisc q) = discRadius K q := rfl

theorem complexPoly_map_conj : ∀ cs : List ℚ, (complexPoly cs).map (starRingEnd ℂ) = complexPoly cs
  | [] => by simp [complexPoly]
  | a :: cs => by
    simp only [complexPoly, Polynomial.map_add, Polynomial.map_mul, map_C, map_X, complexPoly_map_conj cs,
      map_ratCast]

theorem complexFamily_conj : ∀ (cols : List (List ℚ)) (t : ℂ),
    complexFamily cols (conj t) = (complexFamily cols t).map (starRingEnd ℂ)
  | [], _ => by simp [complexFamily]
  | cs :: rest, t => by
    simp only [complexFamily, Polynomial.map_add, Polynomial.map_mul, map_C, complexPoly_map_conj,
      complexFamily_conj rest t]

theorem paperFamily_conj (t : ℂ) : paperFamily (conj t) = (paperFamily t).map (starRingEnd ℂ) :=
  complexFamily_conj _ t

theorem eval_map_conj (p : ℂ[X]) (x : ℂ) : (p.map (starRingEnd ℂ)).eval (conj x) = conj (p.eval x) := by
  rw [eval_map, Polynomial.eval, Polynomial.hom_eval₂, RingHom.comp_id]

theorem rootsInDisc_map_conj (p : ℂ[X]) (c : ℂ) (R : ℝ) :
    HexRootsMathlib.rootsInDisc (p.map (starRingEnd ℂ)) (conj c) R = HexRootsMathlib.rootsInDisc p c R := by
  classical
  unfold HexRootsMathlib.rootsInDisc
  rw [(IsAlgClosed.splits p).roots_map_of_injective (starRingEnd ℂ).injective, Multiset.countP_map,
    Multiset.countP_eq_card_filter]
  simp only [mem_ball, Complex.dist_conj_conj]

theorem separated_conjDisc (q r : GI × ℕ) : separated (conjDisc q) (conjDisc r) = separated q r := by
  simp only [separated, conjDisc, conjGI, nsq]
  congr 2
  ring

theorem pairwiseSeparated_map_conjDisc : ∀ ds : List (GI × ℕ),
    pairwiseSeparated (ds.map conjDisc) = pairwiseSeparated ds
  | [] => rfl
  | q :: qs => by
    simp only [List.map_cons, pairwiseSeparated, List.all_map, pairwiseSeparated_map_conjDisc qs]
    congr 1
    exact List.all_congr rfl (fun r => separated_conjDisc q r)

theorem sepGap_conjDisc (δ : ℕ) (q r : GI × ℕ) : sepGap δ (conjDisc q) (conjDisc r) = sepGap δ q r := by
  simp only [sepGap, conjDisc, conjGI, nsq]
  congr 2
  ring

theorem gapRow_map_conjDisc (q : GI × ℕ) (g : ℕ) : ∀ (rs : List (GI × ℕ)) (hs : List ℕ),
    gapRow (conjDisc q) g (rs.map conjDisc) hs = gapRow q g rs hs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | r :: rs, h :: hs => by simp only [List.map_cons, gapRow, sepGap_conjDisc, gapRow_map_conjDisc q g rs hs]

theorem gapsOK_map_conjDisc : ∀ (ds : List (GI × ℕ)) (gs : List ℕ),
    gapsOK (ds.map conjDisc) gs = gapsOK ds gs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | q :: qs, g :: gs => by
    simp only [List.map_cons, gapsOK, gapRow_map_conjDisc, gapsOK_map_conjDisc qs gs]

variable {J K : ℕ}

/-- **Mirror certificates.** -/
theorem StepDatum.Cert.conj {st : StepDatum} (hc : st.Cert J K) : st.conj.Cert J K := by
  obtain ⟨hstep, hlen, hps, hgap⟩ := hc
  refine ⟨fun t ht => ?_, by simp [StepDatum.conj, hlen],
    by simpa [StepDatum.conj, pairwiseSeparated_map_conjDisc] using hps,
    by simpa [StepDatum.conj, gapsOK_map_conjDisc] using hgap⟩
  have ht' : ‖conj t - gc st.τ / 2 ^ J‖ ≤ (st.S : ℝ) / 2 ^ J := by
    have : conj t - gc st.τ / 2 ^ J = conj (t - gc (conjGI st.τ) / 2 ^ J) := by
      rw [map_sub, conj_div_two_pow, gc_conjGI, Complex.conj_conj]
    rw [this, Complex.norm_conj]
    exact ht
  obtain ⟨hdisc, -⟩ := hstep _ ht'
  have hP : paperFamily t = (paperFamily (conj t)).map (starRingEnd ℂ) := by
    rw [← paperFamily_conj, Complex.conj_conj]
  have hdisc' : ∀ q ∈ st.conj.discs,
      (∀ x ∈ sphere (discCentre K q) (discRadius K q), (paperFamily t).eval x ≠ 0) ∧
      HexRootsMathlib.rootsInDisc (paperFamily t) (discCentre K q) (discRadius K q) = 1 := by
    intro q hq
    obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
    obtain ⟨h1, h2⟩ := hdisc q₀ hq₀
    refine ⟨fun x hx h0 => ?_, ?_⟩
    · have hx' : conj x ∈ sphere (discCentre K q₀) (discRadius K q₀) := by
        rw [mem_sphere, dist_eq_norm] at hx ⊢
        rw [discCentre_conjDisc, discRadius_conjDisc, ← Complex.norm_conj, map_sub,
          Complex.conj_conj] at hx
        exact hx
      apply h1 _ hx'
      have := eval_map_conj (paperFamily t) x
      rw [← paperFamily_conj, h0, map_zero] at this
      exact this
    · rw [hP, discCentre_conjDisc, discRadius_conjDisc, rootsInDisc_map_conj]
      exact h2
  refine ⟨hdisc', ?_⟩
  have hlen' : st.conj.discs.length = 65 := by simp [StepDatum.conj, hlen]
  have hps' : pairwiseSeparated st.conj.discs = true := by
    simpa [StepDatum.conj, pairwiseSeparated_map_conjDisc] using hps
  have hreg := regular_of_discs (paperFamily t) (paperFamily_monic t).ne_zero
    (st.conj.discs.map fun q => (discCentre K q, discRadius K q))
    (by rw [paperFamily_natDegree, List.length_map, hlen'])
    (by rw [List.pairwise_map]; exact pairwise_of_pairwiseSeparated K hps')
    (by
      intro d hd
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
      exact (hdisc' q hq).2)
  show ∀ x, (paperMonicFamily.P t).eval x = 0 → (paperMonicFamily.P t).derivative.eval x ≠ 0
  rw [paperMonicFamily_P]
  exact hreg

end Sz8.Monodromy
