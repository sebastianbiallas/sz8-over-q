import Sz8.Monodromy.PermChain
import Mathlib.Data.List.GetD

/-!
# A certified backtrack search for a normalizer

Let `G ≤ Sym Ω` be transitive on `Ω`, `G₀` the stabiliser of a point `0`, and `H` the
stabiliser in `G₀` of a second point `b`. A permutation `u` normalising `G` and fixing both
points conjugates `H` to itself, hence is *equivariant* for the induced automorphism: writing
every point as a word in fixed generators of `H` applied to one of finitely many base points,
`u` is determined by the images of those base points (`rowOK_false`, via `word_conj`).

The search over those images is pruned by one invariant. `G₀` acts on the ordered pairs of
points `≠ 0`, and `colour_transport` says that the orbit of `(u p, u q)` is the `u`-image of
the orbit of `(p, q)`: with `t p` a transversal element taking `b` to `p`, the `H`-orbit label
of `(t (u p))⁻¹ (u q)` equals that of `u ((t p)⁻¹ q)`. Every partial assignment that breaks
this, or that makes `u` non-injective, is rejected by `rowOK`, and the surviving assignment is
read off level by level.

Nothing here is specific to the recorded group; the data are supplied by
`Sz8.Monodromy.NormalizerCerts`.
-/

namespace Sz8.Monodromy

open Equiv Subgroup

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Labels -/

omit [DecidableEq α] [Fintype α] in
/-- Inverting a known image. -/
theorem inv_apply_eq {g : Equiv.Perm α} {x y : α} (h : g x = y) : g⁻¹ y = x := by rw [← h]; simp

omit [DecidableEq α] [Fintype α] in
/-- A label preserved by the generators is preserved by the group they generate. -/
theorem label_of_gens {S : List (Equiv.Perm α)} {f : α → ℕ}
    (h : ∀ g ∈ S, ∀ z, f (g z) = f z) : ∀ g ∈ lclosure S, ∀ z, f (g z) = f z := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => intro z; simp
  | mul x y _ _ ihx ihy => intro z; rw [Equiv.Perm.mul_apply, ihx, ihy]
  | inv x _ ihx => intro z; simpa using (ihx (x⁻¹ z)).symm

/-- A label preserved by a list of permutations is preserved by every word in them. -/
theorem label_wordProd {T : List (Equiv.Perm α)} {f : α → ℕ}
    (h : ∀ g ∈ T, ∀ z, f (g z) = f z) (w : List ℕ) (x : α) : f (wordProd T w x) = f x := by
  have hg : ∀ i z, f ((T.getD i 1) z) = f z := by
    intro i z
    by_cases hi : i < T.length
    · exact h _ (getD_mem_self hi) z
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]; simp
  induction w with
  | nil => simp [wordProd]
  | cons i w ih => rw [wordProd, Equiv.Perm.mul_apply, hg, ih]

omit [DecidableEq α] [Fintype α] in
/-- A point fixed by the generators is fixed by the group they generate. -/
theorem fix_of_gens {S : List (Equiv.Perm α)} {b : α} (h : ∀ g ∈ S, g b = b) :
    ∀ g ∈ lclosure S, g b = b := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => simp
  | mul x y _ _ ihx ihy => rw [Equiv.Perm.mul_apply, ihy, ihx]
  | inv x _ ihx => exact inv_apply_eq ihx

/-! ## Equivariance -/

omit [DecidableEq α] [Fintype α] in
/-- Conjugation transports words: if `u` conjugates the list `S` to the list `T` entrywise,
it carries the value of a word in `S` to the value of the same word in `T`. -/
theorem word_conj {S T : List (Equiv.Perm α)} {u : Equiv.Perm α}
    (h : ∀ i, u * S.getD i 1 = T.getD i 1 * u) (w : List ℕ) (x : α) :
    u (wordProd S w x) = wordProd T w (u x) := by
  induction w generalizing x with
  | nil => simp [wordProd]
  | cons i w ih =>
    have hi := congrArg (fun p : Equiv.Perm α => p (wordProd S w x)) (h i)
    simp only [Equiv.Perm.mul_apply] at hi
    rw [wordProd, Equiv.Perm.mul_apply, hi, ih, wordProd, Equiv.Perm.mul_apply]

omit [DecidableEq α] [Fintype α] in
/-- Two conjugation equations on a two-element list, in the form `word_conj` wants. -/
theorem conj_getD₂ {a b a' b' u : Equiv.Perm α} (ha : u * a = a' * u) (hb : u * b = b' * u) :
    ∀ i, u * ([a, b].getD i 1) = ([a', b'].getD i 1) * u := by
  intro i
  match i with
  | 0 => exact ha
  | 1 => exact hb
  | (n + 2) => simp

omit [DecidableEq α] [Fintype α] in
/-- Two conjugation equations on a two-element list, in the form `wordProd_conj` wants. -/
theorem conj_getD₂' {a b a' b' u : Equiv.Perm α} (ha : u * a * u⁻¹ = a') (hb : u * b * u⁻¹ = b') :
    ∀ i, u * ([a, b].getD i 1) * u⁻¹ = ([a', b'].getD i 1) := by
  intro i
  match i with
  | 0 => exact ha
  | 1 => exact hb
  | (n + 2) => simp

omit [DecidableEq α] [Fintype α] in
/-- Conjugation transports words, as an identity of permutations. -/
theorem wordProd_conj {S T : List (Equiv.Perm α)} {u : Equiv.Perm α}
    (h : ∀ i, u * S.getD i 1 * u⁻¹ = T.getD i 1) (w : List ℕ) :
    u * wordProd S w * u⁻¹ = wordProd T w := by
  induction w with
  | nil => simp [wordProd]
  | cons i w ih => rw [wordProd, wordProd, ← h i, ← ih]; group

/-! ## The pair invariant -/

omit [DecidableEq α] [Fintype α] in
/-- **Colour transport.** `t` is a transversal of `H` in `G₀` for the point `b`, and `f` is a
label constant on `H`-orbits. A permutation `u` normalising `G₀` and fixing `b` then satisfies
`f ((t (u p))⁻¹ (u q)) = f (u ((t p)⁻¹ q))`: the `G₀`-orbit of a pair is carried along. -/
theorem colour_transport {G₀ H : Subgroup (Equiv.Perm α)} {f : α → ℕ} {t : α → Equiv.Perm α}
    {b : α} {O : List α} (hlab : ∀ h ∈ H, ∀ z, f (h z) = f z)
    (ht : ∀ p, t p ∈ G₀) (htb : ∀ p ∈ O, (t p) b = p)
    (hstab : ∀ g ∈ G₀, g b = b → g ∈ H)
    {u : Equiv.Perm α} (hu : ∀ g ∈ G₀, u * g * u⁻¹ ∈ G₀) (hub : u b = b)
    (hO : ∀ p ∈ O, u p ∈ O) (p q : α) (hp : p ∈ O) :
    f ((t (u p))⁻¹ (u q)) = f (u ((t p)⁻¹ q)) := by
  have hinv : ∀ (g : Equiv.Perm α) (x y : α), g x = y → g⁻¹ y = x := by
    intro g x y hgx; rw [← hgx]; simp
  have hub' : u⁻¹ b = b := hinv u b b hub
  set h : Equiv.Perm α := (t (u p))⁻¹ * (u * t p * u⁻¹) with hh
  have hmem : h ∈ G₀ := mul_mem (inv_mem (ht _)) (hu _ (ht p))
  have hfix : h b = b := by
    rw [hh]
    simp only [Equiv.Perm.mul_apply]
    rw [hub', htb p hp, hinv _ _ _ (htb (u p) (hO p hp))]
  have hkey : ((t (u p))⁻¹ : Equiv.Perm α) (u q) = h (u ((t p)⁻¹ q)) := by
    rw [hh]
    simp
  rw [hkey, hlab h (hstab h hmem hfix)]

/-! ## The search -/

section Search

variable (wi : α → ℕ) (ww : α → List ℕ) (f : α → ℕ) (t : α → Equiv.Perm α)
  (AB : List (Equiv.Perm α)) (ys : List α) (d : α)

/-- The value of `u` at `z`, read off from the word table and the assigned base images. -/
def uAt (z : α) : α := wordProd AB (ww z) (ys.getD (wi z) d)

/-- A base image is *assigned* at level `k` if its orbit index is already fixed; `5` and `6`
index the two points that `u` fixes outright. -/
def assigned (k i : ℕ) : Bool := decide (i < k ∨ i = 5 ∨ i = 6)

/-- The rejection test for one candidate base image, with a witness pair `(p, q)`: the partial
map is not injective, or it breaks the colour invariant. -/
def rowOK (O : List α) (k : ℕ) (p q : α) : Bool :=
  let P := uAt wi ww AB ys d p
  let Q := uAt wi ww AB ys d q
  let z := ((t p)⁻¹ : Equiv.Perm α) q
  decide (p ∈ O) && assigned k (wi p) && assigned k (wi q) && assigned k (wi z) &&
    ((decide (P = Q) && decide (p ≠ q)) || decide (f ((t P)⁻¹ Q) ≠ f (ys.getD (wi z) d)))

variable {wi ww f t AB ys d}

/-- **The rejection test is sound**: no permutation with the stated properties and the stated
base images can make it fire. -/
theorem rowOK_false {A : List (Equiv.Perm α)} {Xp O : List α} {u : Equiv.Perm α} {k : ℕ}
    (hw : ∀ z, z = wordProd A (ww z) (Xp.getD (wi z) d))
    (hlab : ∀ g ∈ AB, ∀ z, f (g z) = f z)
    (hconj : ∀ i, u * A.getD i 1 = AB.getD i 1 * u)
    (hys : ∀ i, (i < k ∨ i = 5 ∨ i = 6) → ys.getD i d = u (Xp.getD i d))
    (hcol : ∀ p q : α, p ∈ O → f ((t (u p))⁻¹ (u q)) = f (u ((t p)⁻¹ q)))
    (p q : α) : rowOK wi ww f t AB ys d O k p q = false := by
  have key : ∀ y : α, assigned k (wi y) = true → u y = uAt wi ww AB ys d y := by
    intro y hy
    rw [assigned, decide_eq_true_eq] at hy
    conv_lhs => rw [hw y]
    rw [word_conj hconj, uAt, hys _ hy]
  by_contra hne
  rw [Bool.not_eq_false] at hne
  simp only [rowOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hne
  obtain ⟨⟨⟨⟨hpO, hp⟩, hq⟩, hz⟩, hrest⟩ := hne
  rw [← key p hp, ← key q hq] at hrest
  rcases hrest with ⟨heq, hne'⟩ | hcolour
  · exact hne' (u.injective heq)
  · refine hcolour ?_
    rw [hcol p q hpO, key _ hz, uAt, label_wordProd hlab]

end Search

omit [DecidableEq α] [Fintype α] in
/-- The empty list generates the trivial group. -/
theorem eq_one_of_mem_nil {x : Equiv.Perm α}
    (h : x ∈ lclosure ([] : List (Equiv.Perm α))) : x = 1 := by
  have he : ({x | x ∈ ([] : List (Equiv.Perm α))} : Set (Equiv.Perm α)) = ∅ := by simp
  rw [lclosure, he, Subgroup.closure_empty] at h
  simpa using h

/-! ## Reading an element off a transversal -/

/-- When the next level of the chain is trivial, every group element *is* a transversal
element: the sift terminates at once. -/
theorem eq_getAt_of_trivial {S TV : List (Equiv.Perm α)} {O : List α} {b : α}
    (hclosed : ∀ s ∈ S, ∀ o ∈ O, s o ∈ O) (hb : b ∈ O)
    (hto : ∀ o ∈ O, getAt TV O o b = o)
    (htv : ∀ k, TV.getD k 1 ∈ lclosure S)
    (hfix : ∀ k ∈ lclosure S, k b = b → k = 1)
    {x : Equiv.Perm α} (hx : x ∈ lclosure S) : x = getAt TV O (x b) := by
  have hxb : x b ∈ O := mem_of_lclosure_apply hclosed x hx b hb
  have htm : getAt TV O (x b) ∈ lclosure S := htv _
  have h1 : ((getAt TV O (x b))⁻¹ * x) b = b := by
    rw [Equiv.Perm.mul_apply]; exact inv_apply_eq (hto _ hxb)
  have h2 := hfix _ (mul_mem (inv_mem htm) hx) h1
  have := congrArg (fun y : Equiv.Perm α => getAt TV O (x b) * y) h2
  simpa [mul_assoc] using this

/-- The same, as list membership. -/
theorem mem_tv_of_trivial {S TV : List (Equiv.Perm α)} {O : List α} {b : α}
    (hclosed : ∀ s ∈ S, ∀ o ∈ O, s o ∈ O) (hb : b ∈ O)
    (hto : ∀ o ∈ O, getAt TV O o b = o)
    (htv : ∀ k, TV.getD k 1 ∈ lclosure S)
    (hfix : ∀ k ∈ lclosure S, k b = b → k = 1)
    (hlen : O.length ≤ TV.length)
    {x : Equiv.Perm α} (hx : x ∈ lclosure S) : x ∈ TV := by
  rw [eq_getAt_of_trivial hclosed hb hto htv hfix hx, getAt]
  exact getD_mem (lt_of_lt_of_le (List.idxOf_lt_length_of_mem
    (mem_of_lclosure_apply hclosed x hx b hb)) hlen)

/-! ## Pairs from two lists -/

/-- All pairs from two lists, in the order the certificates use. -/
def listPairs {β γ : Type*} (L : List β) (M : List γ) : List (β × γ) :=
  L.flatMap fun x => M.map fun y => (x, y)

theorem mem_listPairs {β γ : Type*} {L : List β} {M : List γ} {x : β} {y : γ}
    (hx : x ∈ L) (hy : y ∈ M) : (x, y) ∈ listPairs L M :=
  List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩

end Sz8.Monodromy
