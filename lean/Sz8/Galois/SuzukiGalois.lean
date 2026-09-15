import Sz8.Galois.MainTheorem
import Sz8.Galois.SuzukiIso

/-!
# The Galois group of the specialization is Suzuki's group `Sz(8)`

`Suzuki θ8 = ⟨T(a,b), M(κ), W⟩ ≤ SL₄(𝔽₈)` is Suzuki's own definition of `Sz(8)`. The ovoid action
(`Suzuki.suzukiEquiv`) identifies it with the chain group `lclosure Ngens0 = N`, and
`gal_specialization_eq_N` identifies `N` with the Galois group acting on the 65 roots.
-/

namespace Sz8.Galois

open Polynomial Sz8.Monodromy

/-- **`N ≅ Sz(8)`.** -/
noncomputable def N_equiv_suzuki : N ≃* Suzuki.Suzuki Suzuki.θ8 :=
  (MulEquiv.subgroupCongr N_eq_lclosure).trans Suzuki.suzukiEquiv.symm

/-- **`Gal(f(X, -7/5)/ℚ) ≅ Sz(8)`**, with `Sz(8)` Suzuki's matrix group over `𝔽₈`. -/
theorem gal_specialization_equiv_suzuki :
    Nonempty (paperSpecialization.Gal ≃* Suzuki.Suzuki Suzuki.θ8) := by
  obtain ⟨β, hβ⟩ := gal_specialization_eq_N
  exact ⟨((MonoidHom.ofInjective (Gal.galActionHom_injective paperSpecialization ℂ)).trans
    (Subgroup.equivMapOfInjective _ _ (Equiv.permCongrHom β).injective)).trans
    ((MulEquiv.subgroupCongr hβ).trans N_equiv_suzuki)⟩

end Sz8.Galois
