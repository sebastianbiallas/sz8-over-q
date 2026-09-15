import Sz8.Monodromy.StepCheck

/-!
Step data for certified continuation: a parameter disc and 65 labelled root discs, and the
facts a kernel-checked step certificate provides. Kept minimal so that generated certificate
files depend only on the step checker.
-/

namespace Sz8.Monodromy
open GaussPoly

/-- One certified step: parameter disc `|t - τ/2^J| ≤ S/2^J`, 65 labelled root discs, and a
gap `δᵢ` per disc: the enlarged disc `B(cᵢ, rᵢ + δᵢ)` misses every other disc of the step. -/
structure StepDatum where
  τ : GI
  S : ℕ
  discs : List (GI × ℕ)
  gaps : List ℕ

/-- Discs `q, r` are separated with margin `δ`: `(r_q + r_r + δ)² ≤ |c_q - c_r|²`. -/
def sepGap (δ : ℕ) (q r : GI × ℕ) : Bool :=
  decide (((q.2 + r.2 + δ : ℕ) : ℤ) ^ 2 ≤ nsq (q.1.1 - r.1.1, q.1.2 - r.1.2))

/-- Disc `q` (gap `g`) against the later discs `rs` (gaps `gs`), with margin `max g h`. -/
def gapRow (q : GI × ℕ) (g : ℕ) : List (GI × ℕ) → List ℕ → Bool
  | [], [] => true
  | r :: rs, h :: hs => sepGap (max g h) q r && gapRow q g rs hs
  | _, _ => false

/-- The gaps are valid: every pair of discs is separated with margin the larger gap of the
two. This gives `|cᵢ - cⱼ| ≥ rᵢ + rⱼ + δᵢ` for all `j ≠ i` (2080 checks, once per step). -/
def gapsOK : List (GI × ℕ) → List ℕ → Bool
  | [], [] => true
  | q :: qs, g :: gs => gapRow q g qs gs && gapsOK qs gs
  | _, _ => false

variable (J K : ℕ)

/-- What a step certificate provides. -/
def StepDatum.Cert (st : StepDatum) : Prop :=
  StepCertified J K st.τ st.S st.discs ∧ st.discs.length = 65 ∧ pairwiseSeparated st.discs = true ∧
    gapsOK st.discs st.gaps = true

variable {J K} in
theorem StepDatum.cert_of_checks {b Wmax : ℕ} {τ : GI} {S : ℕ} {slices : List (List (GI × ℕ))}
    {gaps : List ℕ} (hpre : stepPre J K b τ Wmax slices.flatten = true)
    (hgap : gapsOK slices.flatten gaps = true)
    (hslices : ∀ sl ∈ slices, sliceCheck J K b τ S sl = true) :
    StepDatum.Cert J K ⟨τ, S, slices.flatten, gaps⟩ := by
  refine ⟨stepCertified_of_checks hpre hslices, ?_⟩
  simp only [stepPre, Bool.and_eq_true, beq_iff_eq] at hpre
  exact ⟨hpre.1.1.1.2, hpre.1.1.2, hgap⟩

end Sz8.Monodromy
