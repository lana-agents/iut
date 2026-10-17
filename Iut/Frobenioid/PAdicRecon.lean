/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.BaseEquiv
import Iut.Frobenioid.GaloisRecon
import Iut.Frobenioid.PAdicSlim

/-!
# `G_E ≅ G_{E'}` from an equivalence of `p`-adic Frobenioids ([FrdII], Theorem 2.4, base step)

**`PAdicGalois.exists_continuousMulEquiv`**: an equivalence `C^⊢(E) ≌ C^⊢(E')` of the `p`-adic
Frobenioids of `PAdicGalois.lean` lies over an equivalence `B(G_E)⁰ ≌ B(G_{E'})⁰`
(`Model.thm34_galois_preservesBase` for `F` and `F⁻¹`, `isEquivalence_base`), hence induces an
isomorphism of topological groups `G_E ≅ G_{E'}` (`OrbitObj.exists_continuousMulEquiv`), well
defined up to the choice of base points, i.e. up to inner automorphisms.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

namespace PAdicGalois

variable {p : ℕ} [hp : Fact p.Prime]
variable {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
  [FiniteDimensional ℚ_[p] E']

local notation "𝐏E" => Model.toElem (constPhi (OrbitObj (GK p E)) gammaZ)
  (bGal (GK p E) (ord p) (ord_smul p E) gammaZ) (divGal (GK p E) (ord p) (ord_smul p E) gammaZ)

local notation "𝐏E'" => Model.toElem (constPhi (OrbitObj (GK p E')) gammaZ)
  (bGal (GK p E') (ord p) (ord_smul p E') gammaZ)
  (divGal (GK p E') (ord p) (ord_smul p E') gammaZ)

/-- **[FrdII], Theorem 2.4 (base step), for the `p`-adic Frobenioids `C^⊢`**: an equivalence
`C^⊢(E) ≌ C^⊢(E')` induces an equivalence `G : B(G_E)⁰ ≌ B(G_{E'})⁰` of base categories
(compatible with `Base`), hence an isomorphism of topological groups `α : G_E ≅ G_{E'}` with
`G(G_E/N) = G_{E'}/α(N)` for every open normal `N`. -/
theorem exists_continuousMulEquiv (F : Frob p E ⥤ Frob p E') [F.IsEquivalence] :
    ∃ (G : OrbitObj (GK p E) ⥤ OrbitObj (GK p E')) (_ : G.IsEquivalence)
      (α : GK p E ≃ₜ* GK p E'),
      Nonempty (F ⋙ 𝐏E' ⋙ Elem.proj ≅ (𝐏E ⋙ Elem.proj) ⋙ G) ∧
      ∀ N : OpenNormalSubgroup (GK p E),
        (G.obj (OrbitObj.ofONS N)).H = N.toSubgroup.map (α : GK p E →* GK p E') := by
  obtain ⟨G, ⟨hG⟩⟩ := Model.thm34_galois_preservesBase isSlimGroup
    (GaloisModel.hasAllTorsion (torsion p E))
    (GaloisModel.hasAllTorsion (torsion p E')) F
  obtain ⟨G', ⟨hG'⟩⟩ := Model.thm34_galois_preservesBase isSlimGroup
    (GaloisModel.hasAllTorsion (torsion p E'))
    (GaloisModel.hasAllTorsion (torsion p E)) F.inv
  haveI hGe : G.IsEquivalence :=
    isEquivalence_base (frob_isFrobenioid p E) (frob_isFrobenioid p E') F G G' hG hG'
  obtain ⟨α, -, hα, -, -⟩ := OrbitObj.exists_continuousMulEquiv G
  exact ⟨G, hGe, α, ⟨hG⟩, hα⟩

end PAdicGalois

end Frobenioid

end Iut
