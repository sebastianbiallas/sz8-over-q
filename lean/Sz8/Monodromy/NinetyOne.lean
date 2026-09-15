import Sz8.Monodromy.PermChain
import Sz8.Monodromy.GroupTools
import Mathlib.Tactic.NormNum.Prime

/-!
# A subgroup of order divisible by 91 is everything

The argument behind `Sz8.Galois.eq_N_of_ninetyOne_dvd`, stated once and abstractly so that the
generated certificates only have to supply data.

Let `Nn = ⟨gens⟩` have order 29120 = 2⁶·5·7·13, let `Pc ∈ Nn` have order 13, and let `Q₀ ≤ Nn`
be the pointwise stabiliser of two points `b₀ ≠ b₁`, of order 7. If `H ≤ Nn` and `91 ∣ |H|`,
Cauchy gives subgroups of `H` of orders 13 and 7; Sylow's second theorem (both primes divide
`|Nn|` exactly once) conjugates the first onto `⟨Pc⟩`. The second is then some conjugate
`u Q₀ u⁻¹`, determined by the pair of points `(u b₀, u b₁)`: this is where `Q₀` being the *full*
stabiliser of `(b₀, b₁)` in `Nn` is used. A further conjugation by an element of the normaliser
of `⟨Pc⟩` — the table `htab` supplies it, one entry per ordered pair of distinct points — moves
that pair to a representative for which `Pc` and a generator of the stabiliser visibly generate
`Nn`, by explicit words in `gens`.
-/

namespace Sz8.Monodromy

open Subgroup

/-- Every ordered pair of points, in a fixed order. -/
def ptPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun a => (List.finRange n).map fun b => (a, b)

theorem mem_ptPairs {n : ℕ} (a b : Fin n) : (a, b) ∈ ptPairs n :=
  List.mem_flatMap.mpr ⟨a, List.mem_finRange a, List.mem_map.mpr ⟨b, List.mem_finRange b, rfl⟩⟩

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] [Fintype α] in
theorem conjSub_mono {k : Equiv.Perm α} {H K : Subgroup (Equiv.Perm α)} (h : H ≤ K) :
    conjSub k H ≤ conjSub k K := fun _ hx => mem_conjSub.mpr (h (mem_conjSub.mp hx))

private theorem fact13 : (29120 : ℕ).factorization 13 = 1 := by
  have hp : Nat.Prime 13 := by norm_num
  have h1 : 1 ≤ (29120 : ℕ).factorization 13 := by
    rw [← hp.pow_dvd_iff_le_factorization (by norm_num)]; norm_num
  have h2 : ¬ 2 ≤ (29120 : ℕ).factorization 13 := by
    rw [← hp.pow_dvd_iff_le_factorization (by norm_num)]; decide
  omega

private theorem fact7 : (29120 : ℕ).factorization 7 = 1 := by
  have hp : Nat.Prime 7 := by norm_num
  have h1 : 1 ≤ (29120 : ℕ).factorization 7 := by
    rw [← hp.pow_dvd_iff_le_factorization (by norm_num)]; norm_num
  have h2 : ¬ 2 ≤ (29120 : ℕ).factorization 7 := by
    rw [← hp.pow_dvd_iff_le_factorization (by norm_num)]; decide
  omega

/-- **Order 91 forces everything.** -/
theorem eq_of_card_dvd
    {Nn : Subgroup (Equiv.Perm α)} {gens : List (Equiv.Perm α)}
    (hNn : Nn = lclosure gens) (hcard : Nat.card Nn = 29120)
    {b₀ b₁ : α} (hb : b₀ ≠ b₁) {Q₀ : Subgroup (Equiv.Perm α)}
    (hQle : Q₀ ≤ Nn) (hQcard : Nat.card Q₀ = 7)
    (hQfix : ∀ k ∈ Nn, k b₀ = b₀ → k b₁ = b₁ → k ∈ Q₀)
    {Pc : Equiv.Perm α} (hPcmem : Pc ∈ Nn) (hPcard : Nat.card (zpowers Pc) = 13)
    (htab : ∀ a b : α, a ≠ b → ∃ W ∈ Nn, ∃ q ∈ Nn,
        W⁻¹ * Pc * W ∈ zpowers Pc ∧ q (W a) = W a ∧ q (W b) = W b ∧
        ∀ y ∈ gens, y ∈ lclosure [Pc, Pc⁻¹, q, q⁻¹])
    {H : Subgroup (Equiv.Perm α)} (hH : H ≤ Nn) (h91 : 91 ∣ Nat.card H) :
    H = Nn := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfac13 : (Nat.card Nn).factorization 13 = 1 := by rw [hcard]; exact fact13
  have hfac7 : (Nat.card Nn).factorization 7 = 1 := by rw [hcard]; exact fact7
  -- Cauchy: cyclic subgroups of `H` of orders 13 and 7
  obtain ⟨c', hc'H, hc'card, hCle⟩ :=
    exists_zpowers_card_eq (H := H) (p := 13) (dvd_trans (by norm_num) h91)
  obtain ⟨q', hq'H, hq'card, hDle⟩ :=
    exists_zpowers_card_eq (H := H) (p := 7) (dvd_trans (by norm_num) h91)
  -- Sylow 13: conjugate `⟨c'⟩` onto `⟨Pc⟩`
  obtain ⟨g, hgN, hg⟩ := exists_conj_mem_of_card_eq_prime (K := Nn) (A := zpowers Pc)
    (B := zpowers c') (zpowers_le.mpr hPcmem) (zpowers_le.mpr (hH hc'H)) hPcard hc'card hfac13
  set H₁ : Subgroup (Equiv.Perm α) := conjSub g⁻¹ H with hH₁
  have hH₁le : H₁ ≤ Nn := conjSub_le hH (inv_mem hgN)
  have hPcH₁ : Pc ∈ H₁ := by
    refine mem_conjSub.mpr ?_
    have hx : g * Pc * g⁻¹ ∈ Nn := mul_mem (mul_mem hgN hPcmem) (inv_mem hgN)
    have : g * Pc * g⁻¹ ∈ zpowers c' := by
      refine (hg _ hx).mpr ?_
      have : g⁻¹ * (g * Pc * g⁻¹) * g = Pc := by group
      rw [this]; exact mem_zpowers Pc
    simpa [mul_assoc] using hCle this
  -- Sylow 7: the conjugated `⟨q'⟩` is a conjugate of `Q₀`
  have hDN : conjSub g⁻¹ (zpowers q') ≤ Nn :=
    conjSub_le ((zpowers_le.mpr (hH hq'H)).trans le_rfl) (inv_mem hgN)
  obtain ⟨u, huN, hu⟩ := exists_conj_mem_of_card_eq_prime (K := Nn) (A := Q₀)
    (B := conjSub g⁻¹ (zpowers q')) hQle hDN hQcard (by rw [card_conjSub, hq'card]) hfac7
  -- the pair of points attached to that conjugate
  have hab : u b₀ ≠ u b₁ := fun h => hb (u.injective h)
  obtain ⟨W, hWN, q, hqN, hWconj, hqa, hqb, hwords⟩ := htab (u b₀) (u b₁) hab
  set v : Equiv.Perm α := W * u with hv
  have hvN : v ∈ Nn := mul_mem hWN huN
  have hv₀ : v b₀ = W (u b₀) := rfl
  have hv₁ : v b₁ = W (u b₁) := rfl
  -- `q` lies in the twice-conjugated `H`
  have hqH₂ : q ∈ conjSub W H₁ := by
    refine mem_conjSub.mpr ?_
    refine conjSub_mono hDle ?_
    have hx : W⁻¹ * q * W ∈ Nn := mul_mem (mul_mem (inv_mem hWN) hqN) hWN
    refine (hu _ hx).mpr ?_
    have hrw : u⁻¹ * (W⁻¹ * q * W) * u = v⁻¹ * q * v := by rw [hv]; group
    rw [hrw]
    refine hQfix _ (mul_mem (mul_mem (inv_mem hvN) hqN) hvN) ?_ ?_
    · show v⁻¹ (q (v b₀)) = b₀
      rw [hv₀, hqa, ← hv₀]; exact v.symm_apply_apply b₀
    · show v⁻¹ (q (v b₁)) = b₁
      rw [hv₁, hqb, ← hv₁]; exact v.symm_apply_apply b₁
  have hPcH₂ : Pc ∈ conjSub W H₁ :=
    mem_conjSub.mpr ((zpowers_le.mpr hPcH₁) hWconj)
  -- and so does everything the words generate
  have hgen : lclosure [Pc, Pc⁻¹, q, q⁻¹] ≤ conjSub W H₁ := by
    refine lclosure_le ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hPcH₂
    · exact inv_mem hPcH₂
    · exact hqH₂
    · exact inv_mem hqH₂
  have hNle : Nn ≤ conjSub W H₁ := by
    rw [hNn]; exact lclosure_le (fun y hy => hgen (hwords y hy))
  have hle : conjSub W H₁ ≤ Nn := conjSub_le hH₁le hWN
  have hEq : conjSub W H₁ = Nn := le_antisymm hle hNle
  have hcards : Nat.card H = Nat.card Nn := by
    rw [← hEq, hH₁, card_conjSub, card_conjSub]
  exact Subgroup.eq_of_le_of_card_ge hH (le_of_eq hcards.symm)

end Sz8.Monodromy
