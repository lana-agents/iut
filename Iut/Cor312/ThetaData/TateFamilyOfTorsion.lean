/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.SqrtAtBadPlace

/-!
# The Tate family from multiplicative reduction and rational ℓ-torsion

For `E/F` with multiplicative reduction at the places of `F` over `V_mod^bad` (of odd residue
characteristic) and a number field `K ⊇ F` over which `E` has `ℓ²` rational ℓ-torsion points
(`ℓ` an odd prime), every finite place of `K` over `V_mod^bad` is a place of split
multiplicative reduction (`Iut.exists_sq_eq_neg_c₄_mul_c₆`), so `E` is a Tate curve over each
such completion, and the Tate structures assemble to the Galois-equivariant Tate family of the
Θ-data (`Iut.tateFamilyOfTorsion`). No input beyond the reduction type over `F` and the
rationality of the torsion is used.
-/

namespace Iut

open NumberField WeierstrassCurve Iut.Anabelian TateCurvesTheta
open scoped Classical Valued

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

/-- The classical decidable equality on `K`, as used by the model orbicurves. -/
local instance (priority := 1100) instDecidableEqIntermediateField'''' : DecidableEq ↥K :=
  fun a b => Classical.propDecidable (a = b)

variable (ℓ : ℕ)
  (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
  (hmult : ∀ v ∈ VBad, ∀ w : FinitePlace F, FinitePlace.LiesOver w v →
    HasMultiplicativeReductionAt E w)
  (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
  (TK : AddSubgroup (E.map (algebraMap F ↥K)).toAffine.Point)
  (hTK : TK ≤ AddSubgroup.torsionBy (E.map (algebraMap F ↥K)).toAffine.Point ℓ)
  (hcard : ℓ * ℓ ≤ Nat.card ↥TK)

include hVBad hmult hℓ hodd hTK hcard in
/-- **The tangent quadratic has a root at every bad place of `K`** (split multiplicative
reduction). -/
theorem exists_tangent_root_of_torsion {w : FinitePlace ↥K} (hw : IsBadPlace E K VBad w) :
    ∃ r : localCompletion w, ‖(curveKw E K w).c₄ * r ^ 2 +
      (curveKw E K w).a₁ * (curveKw E K w).c₄ * r - (54 * (curveKw E K w).b₆ -
        3 * (curveKw E K w).b₂ * (curveKw E K w).b₄ + (curveKw E K w).a₂ * (curveKw E K w).c₄)‖
      < 1 := by
  obtain ⟨s, hs⟩ := exists_sq_eq_neg_c₄_mul_c₆ E K hVBad hmult hℓ hodd TK hTK hcard hw
  have h2 : ‖(2 : localCompletion w)‖ = 1 :=
    norm_two_eq_one_of_notMem (two_notMem_of_isBadPlace E K hVBad hw)
  have h2' : (2 : localCompletion w) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    exact zero_ne_one h2
  have hc₄ : ‖(curveKw E K w).c₄‖ = 1 :=
    norm_c₄_curveLoc E (liesOver_placeUnder w) (mult_placeUnder E K hmult hw)
  have hc₄' : (curveKw E K w).c₄ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc₄
    exact zero_ne_one hc₄
  exact exists_tangent_root_of_sq _ h2' hc₄' (hs.trans (neg_c₄_mul_c₆_curveLoc E w).symm)

/-- **The Tate family of `E` over `K`** from multiplicative reduction over `F` and the
rationality of the ℓ-torsion over `K`. -/
def tateFamilyOfTorsion : TateFamily E K ℓ VBad :=
  TateFamily.ofStructures E K ℓ VBad fun w hw =>
    tateStructureOfNorms E K w
      (norm_two_eq_one_of_notMem (two_notMem_of_isBadPlace E K hVBad hw))
      (norm_c₄_curveLoc E (liesOver_placeUnder w) (mult_placeUnder E K hmult hw))
      (norm_Δ_curveLoc E (liesOver_placeUnder w) (mult_placeUnder E K hmult hw))
      (exists_tangent_root_of_torsion E K ℓ hVBad hmult hℓ hodd TK hTK hcard hw)

end

end Iut
