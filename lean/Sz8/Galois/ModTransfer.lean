import Sz8.Galois.FixedMinor
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Complex.Basic

/-!
# M2: from residue-ring witnesses modulo `p` to the nodes in characteristic zero

`F ∈ ℤ[t][X]` is an integer model of the family, `S ∈ ℤ[t]` an integer model of the node
polynomial, `B(t) = B(F, F_X)` the fixed minor of `Sz8.Galois.FixedMinor`, never expanded.

* `no_common_root_of_modp`: if the reduction of `S` keeps its degree, `deg S ≠ 0`, and `B̄` is
  nonzero at every root of `S̄` in `\bar{F_p}`, then `B` is nonzero at every complex root of `S`.
  The route is the integer resultant `Res(S, B)` with formal degrees `(deg S, deg B)`: it
  specializes to `F_p` (`resultant_map_map`), is nonzero there by coprimality over the algebraic
  closure (after removing the padding, `resultant_add_right_deg`), hence nonzero in `ℤ`, and a
  common complex root would kill it through the Bézout form `exists_mul_add_mul_eq_C_resultant`.
  No bound on `deg B` is needed: its own degree is used as the formal degree.
* `ResidueWitness`: for a factor `P` of `S̄`, the witness data over the residue ring
  `AdjoinRoot P` — the common root `ρ`, cofactors `Pq`, `Qq` with `F = (X - ρ) Pq`,
  `F_X = (X - ρ) Qq`, and a Bézout pair for `Pq`, `Qq`. `P` need not be irreducible.
* `B_ne_zero_at_roots`: witnesses for factors whose product is `S̄` give `B ≠ 0` at every complex
  root of `S`, provided the leading coefficient of `F` in `X` is a constant `L` with `p ∤ L`.
* `node_multiplicity`: hence, at every complex root of `S`, every root of `F(z, ·)` has
  multiplicity at most two and at most one has multiplicity two.
-/

open Polynomial

namespace Sz8.Galois.FixedMinor

/-- The fixed minor commutes with ring homomorphisms. -/
theorem B_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f g : R[X]) (n : ℕ) :
    B (f.map φ) (g.map φ) n = φ (B f g n) := by
  unfold B
  rw [RingHom.map_det]
  congr 1
  ext i j
  have hcol : col (f.map φ) (g.map φ) n j = (col f g n j).map φ := by
    unfold col; split_ifs <;> simp [Polynomial.map_mul]
  simp [mat, hcol, coeff_map]

variable {p : ℕ} [Fact p.Prime]

/-- **Transfer.** `B̄ ≠ 0` at the roots of `S̄` over `\bar{F_p}` gives `B ≠ 0` at the complex roots of
`S`, when reduction keeps the degree of `S`. -/
theorem no_common_root_of_modp (S Bt : ℤ[X])
    (hS : (S.map (Int.castRingHom (ZMod p))).natDegree = S.natDegree) (hS0 : S.natDegree ≠ 0)
    (hmod : ∀ a : AlgebraicClosure (ZMod p),
      (S.map (Int.castRingHom _)).eval a = 0 → (Bt.map (Int.castRingHom _)).eval a ≠ 0)
    (z : ℂ) (hz : (S.map (Int.castRingHom ℂ)).eval z = 0) :
    (Bt.map (Int.castRingHom ℂ)).eval z ≠ 0 := by
  set K := AlgebraicClosure (ZMod p)
  set m := S.natDegree with hm
  set N := Bt.natDegree with hN
  have hres : resultant S Bt m N ≠ 0 := by
    intro h0
    set φ : ℤ →+* K := Int.castRingHom K
    have hSK : (S.map φ).natDegree = m := by
      have : S.map φ = (S.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p) K) := by
        rw [Polynomial.map_map]; congr 1
      rw [this, natDegree_map_eq_of_injective (algebraMap (ZMod p) K).injective, hS]
    have hS0K : S.map φ ≠ 0 := by
      intro h; rw [h, natDegree_zero] at hSK; exact hS0 hSK.symm
    have hBK : (Bt.map φ).natDegree ≤ N := natDegree_map_le
    have hcop : IsCoprime (S.map φ) (Bt.map φ) := by
      refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) K _ _).2 fun a => ?_
      simp only [aeval_def, eval₂_eq_eval_map, Algebra.algebraMap_self, Polynomial.map_id]
      by_cases ha : (S.map φ).eval a = 0
      · exact Or.inr (hmod a ha)
      · exact Or.inl ha
    have h1 : resultant (S.map φ) (Bt.map φ) m N = 0 := by
      rw [resultant_map_map, h0, map_zero]
    have h2 : resultant (S.map φ) (Bt.map φ) m N
        = (S.map φ).coeff m ^ (N - (Bt.map φ).natDegree) * resultant (S.map φ) (Bt.map φ) := by
      conv_lhs => rw [show N = (Bt.map φ).natDegree + (N - (Bt.map φ).natDegree) by omega]
      rw [resultant_add_right_deg _ _ _ _ _ le_rfl, hSK]
    have hlc : (S.map φ).coeff m ≠ 0 := by
      rw [← hSK]; exact leadingCoeff_ne_zero.2 hS0K
    have h3 : resultant (S.map φ) (Bt.map φ) ≠ 0 := by
      intro h; rw [resultant_eq_zero_iff] at h; exact h.2 hcop
    rw [h2] at h1
    exact (mul_ne_zero (pow_ne_zero _ hlc) h3) h1
  intro hB
  obtain ⟨u, v, -, -, huv⟩ := exists_mul_add_mul_eq_C_resultant
    (S.map (Int.castRingHom ℂ)) (Bt.map (Int.castRingHom ℂ)) (m := m) (n := N)
    natDegree_map_le natDegree_map_le (Or.inl hS0)
  have h := congrArg (eval z) huv
  rw [eval_add, eval_mul, eval_mul, hz, hB, zero_mul, zero_mul, add_zero, eval_C,
    resultant_map_map] at h
  exact hres (by simpa using h.symm)

/-- `t ↦ root P`, from `ℤ[t]` into the residue ring `AdjoinRoot P`. -/
noncomputable def toAdj (P : (ZMod p)[X]) : ℤ[X] →+* AdjoinRoot P :=
  eval₂RingHom (Int.castRingHom _) (AdjoinRoot.root P)

/-- Witness data over the residue ring of one factor `P` of `S̄`: a common root of `F` and `F_X`
and a Bézout pair for the cofactors. `P` need not be irreducible. -/
structure ResidueWitness (F : ℤ[X][X]) (p : ℕ) [Fact p.Prime] where
  P : (ZMod p)[X]
  ρ : AdjoinRoot P
  Pq : (AdjoinRoot P)[X]
  Qq : (AdjoinRoot P)[X]
  a : (AdjoinRoot P)[X]
  b : (AdjoinRoot P)[X]
  hf : F.map (toAdj P) = (X - C ρ) * Pq
  hg : (derivative F).map (toAdj P) = (X - C ρ) * Qq
  hab : a * Pq + b * Qq = 1

/-- **Residue witnesses give `B ≠ 0` at the complex roots of `S`.** Every hypothesis on degrees is
explicit: `F` has degree `n + 1` in `X` with constant leading coefficient `L`, `p ∤ L`, and the
reduction of `S` keeps its (nonzero) degree. -/
theorem B_ne_zero_at_roots (F : ℤ[X][X]) (S : ℤ[X]) (L : ℤ) (n : ℕ) (hF : F.natDegree = n + 1)
    (hlc : F.leadingCoeff = C L) (hL : (L : ZMod p) ≠ 0)
    (hS : (S.map (Int.castRingHom (ZMod p))).natDegree = S.natDegree) (hS0 : S.natDegree ≠ 0)
    (ws : List (ResidueWitness F p))
    (u : ZMod p) (hu : u ≠ 0)
    (hprod : C u * (ws.map ResidueWitness.P).prod = S.map (Int.castRingHom (ZMod p)))
    (z : ℂ) (hz : (S.map (Int.castRingHom ℂ)).eval z = 0) :
    B (F.map (eval₂RingHom (Int.castRingHom ℂ) z))
      (derivative (F.map (eval₂RingHom (Int.castRingHom ℂ) z))) n ≠ 0 := by
  set K := AlgebraicClosure (ZMod p)
  -- `B` evaluated at a point is `B` of the evaluated family
  have hevalB : ∀ {T : Type} [CommRing T] (φ : ℤ →+* T) (x : T),
      ((B F (derivative F) n).map φ).eval x
        = B (F.map (eval₂RingHom φ x)) (derivative (F.map (eval₂RingHom φ x))) n := by
    intro T _ φ x
    rw [eval_map, ← coe_eval₂RingHom, ← B_map, derivative_map]
  -- the degree of an evaluated family
  have hdeg : ∀ {T : Type} [CommRing T] [Nontrivial T] (ψ : ℤ[X] →+* T), ψ (C L) ≠ 0 →
      (F.map ψ).natDegree = n + 1 := by
    intro T _ _ ψ h
    rw [natDegree_map_of_leadingCoeff_ne_zero _ (by rwa [hlc]), hF]
  have hdegD : ∀ {T : Type} [CommRing T] (ψ : ℤ[X] →+* T),
      (derivative (F.map ψ)).natDegree ≤ n := by
    intro T _ ψ
    exact (natDegree_derivative_le _).trans (by have := natDegree_map_le (f := ψ) (p := F); omega)
  rw [← hevalB]
  refine no_common_root_of_modp S (B F (derivative F) n) hS hS0 (fun a ha => ?_) z hz
  rw [hevalB]
  -- `a` is a root of one factor
  have ha' : (ws.map ResidueWitness.P).prod.eval₂ (algebraMap (ZMod p) K) a = 0 := by
    have hu' : algebraMap (ZMod p) K u ≠ 0 := (map_ne_zero_iff _ (algebraMap (ZMod p) K).injective).2 hu
    refine (mul_eq_zero.1 ?_).resolve_left hu'
    rw [← eval₂_C (algebraMap (ZMod p) K) a, ← eval₂_mul, hprod, eval₂_map]
    have : (algebraMap (ZMod p) K).comp (Int.castRingHom (ZMod p)) = Int.castRingHom K :=
      RingHom.ext_int _ _
    rw [this, ← eval_map]; exact ha
  rw [← aeval_def, map_list_prod, List.prod_eq_zero_iff] at ha'
  obtain ⟨q, hq, hq0⟩ := List.mem_map.1 ha'
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hq
  have hroot : w.P.eval₂ (algebraMap (ZMod p) K) a = 0 := by rwa [aeval_def] at hq0
  set ψw := AdjoinRoot.lift (algebraMap (ZMod p) K) a hroot with hψw
  have hcomp : ψw.comp (toAdj w.P) = eval₂RingHom (Int.castRingHom K) a := by
    apply Polynomial.ringHom_ext
    · intro c; simp [toAdj]
    · simp [toAdj, hψw, AdjoinRoot.lift_root]
  have hmapF : F.map (eval₂RingHom (Int.castRingHom K) a) = ((X - C w.ρ) * w.Pq).map ψw := by
    rw [← w.hf, Polynomial.map_map, hcomp]
  have hmapD : derivative (F.map (eval₂RingHom (Int.castRingHom K) a))
      = ((X - C w.ρ) * w.Qq).map ψw := by
    rw [derivative_map, ← hcomp, ← Polynomial.map_map, w.hg]
  have hLK : eval₂RingHom (Int.castRingHom K) a (C L) ≠ 0 := by
    rw [coe_eval₂RingHom, eval₂_C, eq_intCast, ← map_intCast (algebraMap (ZMod p) K)]
    exact (map_ne_zero_iff _ (algebraMap (ZMod p) K).injective).2 hL
  have hF1 := hdeg (eval₂RingHom (Int.castRingHom K) a) hLK
  have hD1 := hdegD (eval₂RingHom (Int.castRingHom K) a)
  rw [hmapD] at hD1 ⊢
  rw [hmapF] at hF1 ⊢
  refine B_ne_zero (d := X - C (ψw w.ρ)) (P := w.Pq.map ψw) (Q := w.Qq.map ψw) hF1 hD1
    (natDegree_X_sub_C _) (by simp [Polynomial.map_mul]) (by simp [Polynomial.map_mul])
    ⟨w.a.map ψw, w.b.map ψw, ?_⟩
  rw [← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, w.hab, Polynomial.map_one]

/-- **M2 at the nodes.** Under the hypotheses of `B_ne_zero_at_roots`, at every complex root `z` of
`S` every root of `F(z, ·)` has multiplicity at most two, and at most one has multiplicity two. -/
theorem node_multiplicity (F : ℤ[X][X]) (S : ℤ[X]) (L : ℤ) (n : ℕ) (hF : F.natDegree = n + 1)
    (hlc : F.leadingCoeff = C L) (hL : (L : ZMod p) ≠ 0)
    (hS : (S.map (Int.castRingHom (ZMod p))).natDegree = S.natDegree) (hS0 : S.natDegree ≠ 0)
    (ws : List (ResidueWitness F p))
    (u : ZMod p) (hu : u ≠ 0)
    (hprod : C u * (ws.map ResidueWitness.P).prod = S.map (Int.castRingHom (ZMod p)))
    (z : ℂ) (hz : (S.map (Int.castRingHom ℂ)).eval z = 0) :
    (∀ r, (F.map (eval₂RingHom (Int.castRingHom ℂ) z)).rootMultiplicity r ≤ 2) ∧
      ∀ r s, 2 ≤ (F.map (eval₂RingHom (Int.castRingHom ℂ) z)).rootMultiplicity r →
        2 ≤ (F.map (eval₂RingHom (Int.castRingHom ℂ) z)).rootMultiplicity s → r = s := by
  have hL0 : (L : ℂ) ≠ 0 := by
    have : L ≠ 0 := by rintro rfl; simp at hL
    exact_mod_cast this
  refine rootMultiplicity_of_B_ne_zero ?_
    (B_ne_zero_at_roots F S L n hF hlc hL hS hS0 ws u hu hprod z hz)
  rw [natDegree_map_of_leadingCoeff_ne_zero _ (by rw [hlc]; simpa using hL0), hF]

end Sz8.Galois.FixedMinor
