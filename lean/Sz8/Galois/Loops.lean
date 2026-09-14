import Sz8.Monodromy.Meridian.Chain2

open Sz8.Monodromy Sz8.Monodromy.GaussPoly

namespace Sz8.Galois.Loops

/-- Sign of `Im (z - a)` for `a = -1/2 ± (√3/2) i` (`up` chooses the sign), at scale `2^40`. -/
def imPosB (up : Bool) (w : ℤ × ℤ) : Bool :=
  if up then decide (0 < w.2 ∧ 3 * 2 ^ 80 < 4 * w.2 ^ 2) else decide (0 ≤ w.2 ∨ 4 * w.2 ^ 2 < 3 * 2 ^ 80)
def imNegB (up : Bool) (w : ℤ × ℤ) : Bool :=
  if up then decide (w.2 ≤ 0 ∨ 4 * w.2 ^ 2 < 3 * 2 ^ 80) else decide (w.2 < 0 ∧ 3 * 2 ^ 80 < 4 * w.2 ^ 2)
def rePosB (w : ℤ × ℤ) : Bool := decide (0 < 2 * w.1 + 2 ^ 40)
def reNegB (w : ℤ × ℤ) : Bool := decide (2 * w.1 + 2 ^ 40 < 0)

/-- The vertex lies in the open half-plane `Im > -1/2` (`up`) or `Im < 1/2` (not `up`). -/
def halfB (up : Bool) (w : ℤ × ℤ) : Bool :=
  if up then decide (-2 ^ 39 < w.2) else decide (w.2 < 2 ^ 39)

def slitB (up : Bool) (v : ℕ → ℤ × ℤ) (k : ℕ) : Bool :=
  (imPosB up (v k) && imPosB up (v (k + 1))) || (imNegB up (v k) && imNegB up (v (k + 1))) ||
    (rePosB (v k) && rePosB (v (k + 1)))
def negSlitB (up : Bool) (v : ℕ → ℤ × ℤ) (k : ℕ) : Bool :=
  (imPosB up (v k) && imPosB up (v (k + 1))) || (imNegB up (v k) && imNegB up (v (k + 1))) ||
    (reNegB (v k) && reNegB (v (k + 1)))

/-- The edge test for global edge index `k`, for cuts `q < r`. -/
def edgeOK (up : Bool) (q r : ℕ) (k : ℕ) (a b : ℤ × ℤ) : Bool :=
  let v : ℕ → ℤ × ℤ := fun i => if i = k then a else b
  halfB up a && halfB up b &&
    if k < q then slitB up v k else if k < r then negSlitB up v k else slitB up v k

/-- One pass over consecutive waypoint pairs, starting at global edge index `k`. -/
def walk (ok : ℕ → ℤ × ℤ → ℤ × ℤ → Bool) : ℕ → List (ℤ × ℤ) → Bool
  | k, a :: b :: t => ok k a b && walk ok (k + 1) (b :: t)
  | _, _ => true

def loopCert (up : Bool) (l : List (ℤ × ℤ)) (q r : ℕ) : Bool :=
  walk (edgeOK up q r) 0 l && imPosB up (l.getD q (0, 0)) && imNegB up (l.getD r (0, 0)) &&
    decide (l.getLast? = l.head?)

theorem slitB_congr {up : Bool} {v w : ℕ → ℤ × ℤ} {k : ℕ} (h0 : v k = w k)
    (h1 : v (k + 1) = w (k + 1)) : slitB up v k = slitB up w k := by simp [slitB, h0, h1]

theorem negSlitB_congr {up : Bool} {v w : ℕ → ℤ × ℤ} {k : ℕ} (h0 : v k = w k)
    (h1 : v (k + 1) = w (k + 1)) : negSlitB up v k = negSlitB up w k := by simp [negSlitB, h0, h1]

theorem walk_spec (ok : ℕ → ℤ × ℤ → ℤ × ℤ → Bool) :
    ∀ (l : List (ℤ × ℤ)) (k : ℕ), walk ok k l = true → ∀ i, i + 1 < l.length →
      ok (k + i) (l.getD i (0, 0)) (l.getD (i + 1) (0, 0)) = true
  | [], _, _, _, hi => by simp at hi
  | [_], _, _, _, hi => by simp at hi
  | a :: b :: t, k, h, i, hi => by
    simp only [walk, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := walk_spec ok (b :: t) (k + 1) h.2 i (by simp at hi ⊢; omega)
      rw [show k + (i + 1) = k + 1 + i by omega]
      simpa using this

/-- What a passing certificate gives, edge by edge, for `v i = l.getD i (0, 0)`. -/
theorem loopCert_spec {up : Bool} {l : List (ℤ × ℤ)} {q r : ℕ} (hqr : q ≤ r)
    (h : loopCert up l q r = true) :
    let v := fun i => l.getD i (0, 0)
    (∀ k, k + 1 < l.length → k < q → slitB up v k = true) ∧
    (∀ k, k + 1 < l.length → q ≤ k → k < r → negSlitB up v k = true) ∧
    (∀ k, k + 1 < l.length → r ≤ k → slitB up v k = true) ∧
    (∀ k, k + 1 < l.length → halfB up (v k) = true ∧ halfB up (v (k + 1)) = true) ∧
    imPosB up (v q) = true ∧ imNegB up (v r) = true ∧ l.getLast? = l.head? := by
  simp only [loopCert, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hw, hq⟩, hr⟩, hc⟩ := h
  have e := fun k hk => walk_spec _ l 0 hw k hk
  simp only [zero_add] at e
  refine ⟨fun k hk hkq => ?_, fun k hk hqk hkr => ?_, fun k hk hrk => ?_, fun k hk => ?_, hq, hr, hc⟩
  · have := e k hk
    simp only [edgeOK, hkq, if_true, Bool.and_eq_true] at this
    replace this := this.2
    simpa [slitB] using this
  · have := e k hk
    simp only [edgeOK, show ¬ k < q by omega, hkr, if_true, ite_false, Bool.and_eq_true] at this
    replace this := this.2
    simpa [negSlitB] using this
  · have := e k hk
    simp only [edgeOK, show ¬ k < q by omega, show ¬ k < r by omega, ite_false,
      Bool.and_eq_true] at this
    simpa [slitB] using this.2
  · have := e k hk
    simp only [edgeOK, Bool.and_eq_true] at this
    exact this.1

theorem cert1 : loopCert true Meridian1.chain.wps 529 600 = true := by decide +kernel
theorem cert2 : loopCert false Meridian1.chain2.wps 1 555 = true := by decide +kernel

end Sz8.Galois.Loops
