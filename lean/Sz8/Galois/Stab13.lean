import Sz8.Galois.Stab13Core
import Sz8.Galois.Stab13Data
import Sz8.Monodromy.GroupCerts
import Mathlib.Tactic.FinCases

/-!
# The setwise stabilizers of the five `⟨σ₂σ₁⟩`-orbits have order at most 156

`G = ⟨σ₁, σ₂⟩`, `c = σ₂ * σ₁` (the paper's `σ₁σ₂`, of type `13⁵`). For each of its five orbits
`O_k`, `stab_le k : Nat.card (stabilizer G O_k) ≤ 156` — kernel-checked from

* words taking `(0, 1)` to every ordered pair of distinct points (`G` is 2-transitive, so the
  two-point stabilizers have order `87360 / 4160 = 21`), and
* the 21 elements of `G_(a,b)` for a pair `a ≠ b` in `O_k`, as words, of which only the identity
  preserves `O_k`,

through `card_stabilizer_set_le` (`|Stab(O)| ≤ 13 · 12`). The exact orders are 156 and `39` (four
times); only the bound is used.
-/

open Pointwise MulAction Sz8.Monodromy

namespace Sz8.Galois.Stab13

set_option maxRecDepth 100000

/-- The recorded meridian group. -/
abbrev G : Subgroup (Equiv.Perm (Fin 65)) := Subgroup.closure {σ₁, σ₂}

theorem Gs1_eq : Gs1 = σ₁ := by decide +kernel
theorem Gs2_eq : Gs2 = σ₂ := by decide +kernel

/-- A word (sentinel bit, lowest bit acting last; `0 = σ₁`, `1 = σ₂`) as a permutation. -/
def wordPerm : ℕ → ℕ → Equiv.Perm (Fin 65)
  | 0, _ => 1
  | f + 1, w => if w ≤ 1 then 1 else (if w % 2 = 1 then Gs2 else Gs1) * wordPerm f (w / 2)

theorem wordPerm_mem : ∀ f w, wordPerm f w ∈ G
  | 0, _ => G.one_mem
  | f + 1, w => by
    unfold wordPerm
    split_ifs
    · exact G.one_mem
    · exact G.mul_mem (by rw [Gs2_eq]; exact Subgroup.subset_closure (by simp)) (wordPerm_mem f _)
    · exact G.mul_mem (by rw [Gs1_eq]; exact Subgroup.subset_closure (by simp)) (wordPerm_mem f _)

/-! ## Two-transitivity -/

def pairTargets : List (Fin 65 × Fin 65) :=
  (List.finRange 65).flatMap fun x => ((List.finRange 65).filter (· ≠ x)).map (x, ·)

def pairChk : List ℕ → List (Fin 65 × Fin 65) → Bool
  | w :: ws, t :: ts => (wordPerm 64 w 0 == t.1 && wordPerm 64 w 1 == t.2) && pairChk ws ts
  | [], [] => true
  | _, _ => false

theorem pairChk_sound : ∀ (ws : List ℕ) (ts : List (Fin 65 × Fin 65)), pairChk ws ts = true →
    ∀ t ∈ ts, ∃ w, wordPerm 64 w 0 = t.1 ∧ wordPerm 64 w 1 = t.2
  | w :: ws, t :: ts, h, t', ht' => by
    simp only [pairChk, Bool.and_eq_true, beq_iff_eq] at h
    rcases List.mem_cons.1 ht' with rfl | ht'
    · exact ⟨w, h.1.1, h.1.2⟩
    · exact pairChk_sound ws ts h.2 t' ht'
  | [], [], _, _, ht => absurd ht (List.not_mem_nil)
  | [], _ :: _, h, _, _ => by simp [pairChk] at h
  | _ :: _, [], h, _, _ => by simp [pairChk] at h

theorem pair_ok : pairChk pairWords pairTargets = true := by decide +kernel

theorem reach (x y : Fin 65) (hxy : x ≠ y) : ∃ g ∈ G, g 0 = x ∧ g 1 = y := by
  have hmem : (x, y) ∈ pairTargets := by
    simp only [pairTargets, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
      true_and, decide_eq_true_eq, Prod.mk.injEq]
    exact ⟨x, y, fun h => hxy h.symm, rfl, rfl⟩
  obtain ⟨w, h0, h1⟩ := pairChk_sound _ _ pair_ok _ hmem
  exact ⟨_, wordPerm_mem 64 w, h0, h1⟩

theorem card_G : Nat.card G = 87360 := card_closure_sigma

theorem stab_pair_le {a b : Fin 65} (hab : a ≠ b) : Nat.card (stabilizer G (a, b)) ≤ 21 :=
  card_stabilizer_pair_le G reach hab (by rw [card_G])

/-! ## The five orbits -/

/-- Everything the bound needs about one orbit, as one Boolean check. -/
def orbitChk (O : List (Fin 65)) (a b p q : Fin 65) (H : List ℕ) : Bool :=
  let E := H.map (wordPerm 64)
  (a ∈ O && b ∈ O && a != b) &&
  E.all (fun e => e a == a && e b == b) &&
  (E.map fun e => (e p, e q)).Nodup &&
  (H.head? == some 1) &&
  E.tail.all (fun e => O.any fun x => !(O.contains (e x)))

theorem stab_le_of_chk {O : List (Fin 65)} {a b p q : Fin 65} {H : List ℕ}
    (hc : orbitChk O a b p q H = true) (hlen : H.length = 21) :
    Nat.card (stabilizer G (O.toFinset : Set (Fin 65))) ≤ O.toFinset.card * (O.toFinset.card - 1) := by
  simp only [orbitChk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq, List.any_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hc
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hab⟩, hfix⟩, hnd⟩, hhead⟩, htail⟩ := hc
  refine card_stabilizer_set_le G O.toFinset (List.mem_toFinset.2 ha) (List.mem_toFinset.2 hb)
    hab (stab_pair_le hab) (H.map (wordPerm 64)) (fun e he => ⟨?_, hfix e he⟩)
    (List.Nodup.of_map _ hnd) (by simp [hlen]) ?_
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 he
    exact wordPerm_mem 64 w
  · intro e he hpres
    cases H with
    | nil => simp at hlen
    | cons w H =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      simp only [List.map_cons, List.mem_cons] at he
      rcases he with rfl | he
      · rfl
      · obtain ⟨x, hx, hex⟩ := htail e (by simpa using he)
        exact absurd (List.mem_toFinset.1 (hpres x (List.mem_toFinset.2 hx))) hex

theorem chk1 : orbitChk O1 a1 b1 p1 q1 H1 = true := by decide +kernel
theorem chk2 : orbitChk O2 a2 b2 p2 q2 H2 = true := by decide +kernel
theorem chk3 : orbitChk O3 a3 b3 p3 q3 H3 = true := by decide +kernel
theorem chk4 : orbitChk O4 a4 b4 p4 q4 H4 = true := by decide +kernel
theorem chk5 : orbitChk O5 a5 b5 p5 q5 H5 = true := by decide +kernel

/-- The five orbits, as finsets. -/
def orbit (k : Fin 5) : Finset (Fin 65) := ([O1, O2, O3, O4, O5].getD k []).toFinset

theorem card_orbit (k : Fin 5) : (orbit k).card = 13 := by
  fin_cases k <;> decide +kernel

/-- **The five setwise-stabilizer bounds.** -/
theorem stab_le (k : Fin 5) : Nat.card (stabilizer G (orbit k : Set (Fin 65))) ≤ 156 := by
  have h : Nat.card (stabilizer G (orbit k : Set (Fin 65))) ≤ (orbit k).card * ((orbit k).card - 1) := by
    fin_cases k
    · exact stab_le_of_chk chk1 rfl
    · exact stab_le_of_chk chk2 rfl
    · exact stab_le_of_chk chk3 rfl
    · exact stab_le_of_chk chk4 rfl
    · exact stab_le_of_chk chk5 rfl
  rw [card_orbit] at h
  exact h

/-- They are the orbits of `c = σ₂ * σ₁`: each is `c`-stable, and they cover `Fin 65`. -/
theorem orbit_stable (k : Fin 5) : ∀ x ∈ orbit k, (σ₂ * σ₁) x ∈ orbit k := by
  fin_cases k <;> decide +kernel

theorem orbit_cover (x : Fin 65) : ∃ k, x ∈ orbit k := by
  revert x; decide +kernel

end Sz8.Galois.Stab13
