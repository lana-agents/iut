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
rationality of the torsion is used. The norm conditions `‖c₄‖ = 1`, `‖Δ‖ < 1` of Tate's
isomorphism theorem hold for a model `C • E` (`Iut.exists_variableChange_of_mult`), whose Tate
structure is transported to the given model `E` along the composite change of variables.
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

omit [NumberField F] [E.IsElliptic] [IsAlgClosure F Fbar] in
/-- The model `C • E` over `K_w` is the change of variables `C` (mapped to `K_w`) of `E` over
`K_w`. -/
lemma curveKw_variableChange (C : VariableChange F) (w : FinitePlace ↥K) :
    curveKw (C • E) K w = ((C.map (algebraMap F ↥K)).map (emb K w)) • curveKw E K w := by
  rw [curveKw, curveK, map_variableChange, map_variableChange]

include hmult in
/-- `c₄(E) ≠ 0`: some model `C • E` has `v(c₄) = 1` at a bad place. -/
lemma c₄_ne_zero_of_bad {w : FinitePlace ↥K} (hw : IsBadPlace E K VBad w) : E.c₄ ≠ 0 := by
  obtain ⟨C, -, hc₄, -⟩ := exists_variableChange_of_mult E _ (mult_placeUnder E K hmult hw)
  intro h
  rw [variableChange_c₄, h, mul_zero, map_zero] at hc₄
  exact zero_ne_one hc₄

include hVBad hmult hℓ hodd hTK hcard in
/-- **The tangent quadratic has a root at every bad place of `K`** (split multiplicative
reduction), for the given model `E`. -/
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
  have hc₄' : (curveKw E K w).c₄ ≠ 0 := by
    simp only [curveKw, curveK, map_c₄]
    exact (map_ne_zero _).2 ((map_ne_zero _).2 (c₄_ne_zero_of_bad E K hmult hw))
  exact exists_tangent_root_of_sq _ h2' hc₄' (hs.trans (neg_c₄_mul_c₆_curveLoc E w).symm)

include hVBad hmult hℓ hodd hTK hcard in
/-- **The tangent quadratic of a model `C • E` has a root at every bad place of `K`**: the
square root of `−c₄c₆(E)` in `K_w` is transported to one of `−c₄c₆(C • E) = u⁻¹⁰ · (−c₄c₆(E))`. -/
theorem exists_tangent_root_of_torsion_variableChange {w : FinitePlace ↥K}
    (hw : IsBadPlace E K VBad w) (C : VariableChange F) :
    ∃ r : localCompletion w, ‖(curveKw (C • E) K w).c₄ * r ^ 2 +
      (curveKw (C • E) K w).a₁ * (curveKw (C • E) K w).c₄ * r - (54 * (curveKw (C • E) K w).b₆ -
        3 * (curveKw (C • E) K w).b₂ * (curveKw (C • E) K w).b₄ +
          (curveKw (C • E) K w).a₂ * (curveKw (C • E) K w).c₄)‖ < 1 := by
  obtain ⟨s, hs⟩ := exists_sq_eq_neg_c₄_mul_c₆ E K hVBad hmult hℓ hodd TK hTK hcard hw
  have h2 : ‖(2 : localCompletion w)‖ = 1 :=
    norm_two_eq_one_of_notMem (two_notMem_of_isBadPlace E K hVBad hw)
  have h2' : (2 : localCompletion w) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    exact zero_ne_one h2
  have hc₄0 : (C • E).c₄ ≠ 0 := by
    rw [variableChange_c₄]
    exact mul_ne_zero (pow_ne_zero _ (C.u⁻¹).ne_zero) (c₄_ne_zero_of_bad E K hmult hw)
  have hc₄' : (curveKw (C • E) K w).c₄ ≠ 0 := by
    simp only [curveKw, curveK, map_c₄]
    exact (map_ne_zero _).2 ((map_ne_zero _).2 hc₄0)
  set ui : F := ((C.u⁻¹ : Fˣ) : F) with hui
  have hd : (ui ^ 5) ^ 2 * (-(E.c₄ * E.c₆)) = -((C • E).c₄ * (C • E).c₆) := by
    rw [variableChange_c₄, variableChange_c₆]
    ring
  have hs' : (emb K w (algebraMap F ↥K (ui ^ 5)) * s) ^ 2 =
      -((curveLoc (C • E) ↥K w).c₄ * (curveLoc (C • E) ↥K w).c₆) := by
    rw [neg_c₄_mul_c₆_curveLoc (C • E) w, mul_pow, hs, ← map_pow, ← map_pow, ← map_mul,
      ← map_mul, hd]
  exact exists_tangent_root_of_sq _ h2' hc₄' hs'

include hVBad hmult hℓ hodd hTK hcard in
/-- **The Tate structure of `E` over `K_w`** at a bad place: the model `C • E` given by
`Iut.exists_variableChange_of_mult` at the place of `F` below `w` satisfies the norm conditions
of `Iut.tateStructureOfNorms`, and its Tate structure is transported to `E` along the composite
change of variables (`Iut.TateStructure.ofCurveVariableChange`). -/
def tateStructureOfTorsion {w : FinitePlace ↥K} (hw : IsBadPlace E K VBad w) :
    TateStructure (curveKw E K w) :=
  let C := Classical.choose (exists_variableChange_of_mult E _ (mult_placeUnder E K hmult hw))
  have hC := Classical.choose_spec
    (exists_variableChange_of_mult E _ (mult_placeUnder E K hmult hw))
  have h2 : ‖(2 : localCompletion w)‖ = 1 :=
    norm_two_eq_one_of_notMem (two_notMem_of_isBadPlace E K hVBad hw)
  TateStructure.ofCurveVariableChange _ (curveKw_variableChange E K C w).symm
    (tateStructureOfNorms (C • E) K w h2
      (norm_c₄_curveLoc (C • E) (liesOver_placeUnder w) hC.2.1)
      (norm_Δ_curveLoc (C • E) (liesOver_placeUnder w) hC.2.2)
      (exists_tangent_root_of_torsion_variableChange E K ℓ hVBad hmult hℓ hodd TK hTK hcard hw C))
    ⟨h2, twelve_ne_zero w⟩

/-- **The Tate family of `E` over `K`** from multiplicative reduction over `F` and the
rationality of the ℓ-torsion over `K`. -/
def tateFamilyOfTorsion : TateFamily E K ℓ VBad :=
  TateFamily.ofStructures E K ℓ VBad fun _ hw =>
    tateStructureOfTorsion E K ℓ hVBad hmult hℓ hodd TK hTK hcard hw

end

end Iut
