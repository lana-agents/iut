/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.TateIsomorphism
import Iut.Cor312.ThetaData.TateStructureOfIso
import Iut.Cor312.ThetaData.BadPlaceNorm
import Iut.Cor312.ThetaData.TateFamilyGalois

/-!
# Tate structures from split multiplicative reduction

At a finite place `w` of the torsion field `K` at which `E` has split multiplicative reduction
(Mathlib's `WeierstrassCurve.HasSplitMultiplicativeReduction` over the completed integers), the
curve `E ×_K K_w` is a Tate curve (`Iut.exists_variableChange_tateCurve`), and carries the Tate
structure `Iut.tateStructureOfSplit` (`Iut.TateStructure.ofVariableChange`). Doing this at every
place of `K` over `V_mod^bad` gives the Tate family `Iut.tateFamilyOfSplit`: its Galois
equivariance is automatic from the uniqueness of Tate structures
(`Iut.TateFamily.ofStructures`).
-/

namespace Iut

open WeierstrassCurve TateCurvesTheta NumberField
open scoped Classical Valued

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]

/-- The classical decidable equality on `K`, as used by the model orbicurves. -/
local instance (priority := 1100) instDecidableEqIntermediateField' : DecidableEq ↥K :=
  fun a b => Classical.propDecidable (a = b)

variable (w : FinitePlace ↥K)

/-- **`E` over `K_w` is a Tate curve** at a place where `‖2‖ = 1`, `‖c₄‖ = 1`, `‖Δ‖ < 1` and the
tangent quadratic at the node has a root modulo the maximal ideal. -/
theorem exists_tateParameter_of_norms (h2 : ‖(2 : localCompletion w)‖ = 1)
    (hc₄ : ‖(curveKw E K w).c₄‖ = 1) (hΔ : ‖(curveKw E K w).Δ‖ < 1)
    (hroot : ∃ r : localCompletion w, ‖(curveKw E K w).c₄ * r ^ 2 +
      (curveKw E K w).a₁ * (curveKw E K w).c₄ * r - (54 * (curveKw E K w).b₆ -
        3 * (curveKw E K w).b₂ * (curveKw E K w).b₄ + (curveKw E K w).a₂ * (curveKw E K w).c₄)‖
      < 1) :
    ∃ (t : TateParameter (localCompletion w)) (C : VariableChange (localCompletion w)),
      C • curveKw E K w = t.tateCurve ∧ t.tateJ = (curveKw E K w).j :=
  exists_variableChange_tateCurve h2 (twelve_ne_zero w) (curveKw E K w) hc₄ hΔ hroot

/-- **The Tate structure of `E` over `K_w`** from the norm conditions. -/
def tateStructureOfNorms (h2 : ‖(2 : localCompletion w)‖ = 1)
    (hc₄ : ‖(curveKw E K w).c₄‖ = 1) (hΔ : ‖(curveKw E K w).Δ‖ < 1)
    (hroot : ∃ r : localCompletion w, ‖(curveKw E K w).c₄ * r ^ 2 +
      (curveKw E K w).a₁ * (curveKw E K w).c₄ * r - (54 * (curveKw E K w).b₆ -
        3 * (curveKw E K w).b₂ * (curveKw E K w).b₄ + (curveKw E K w).a₂ * (curveKw E K w).c₄)‖
      < 1) :
    TateStructure (curveKw E K w) :=
  TateStructure.ofVariableChange
    (Classical.choose (exists_tateParameter_of_norms E K w h2 hc₄ hΔ hroot))
    (Classical.choose (Classical.choose_spec (exists_tateParameter_of_norms E K w h2 hc₄ hΔ hroot)))
    (Classical.choose_spec
      (Classical.choose_spec (exists_tateParameter_of_norms E K w h2 hc₄ hΔ hroot))).1
    ⟨h2, twelve_ne_zero w⟩

/-- **`E` over `K_w` is a Tate curve** at a place of split multiplicative reduction with `‖2‖ = 1`:
there are a Tate parameter `q` and a change of variables `C` with `C • (E ×_K K_w) = E_q`. -/
theorem exists_tateParameter_of_split (h2 : ‖(2 : localCompletion w)‖ = 1)
    [(curveKw E K w).HasSplitMultiplicativeReduction (w.maximalIdeal.adicCompletionIntegers ↥K)] :
    ∃ (t : TateParameter (localCompletion w)) (C : VariableChange (localCompletion w)),
      C • curveKw E K w = t.tateCurve ∧ t.tateJ = (curveKw E K w).j :=
  exists_tateParameter_of_norms E K w h2 (norm_c₄_eq_one (curveKw E K w))
    (norm_Δ_lt_one (curveKw E K w)) ((exists_tangent_root (curveKw E K w)).imp fun _ hr => hr.2)

/-- **The Tate structure of `E` over `K_w`** at a place of split multiplicative reduction. -/
def tateStructureOfSplit (h2 : ‖(2 : localCompletion w)‖ = 1)
    [(curveKw E K w).HasSplitMultiplicativeReduction (w.maximalIdeal.adicCompletionIntegers ↥K)] :
    TateStructure (curveKw E K w) :=
  tateStructureOfNorms E K w h2 (norm_c₄_eq_one (curveKw E K w)) (norm_Δ_lt_one (curveKw E K w))
    ((exists_tangent_root (curveKw E K w)).imp fun _ hr => hr.2)

variable (ℓ : ℕ) {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

/-- **The Tate family of `E` over the torsion field** from split multiplicative reduction at
the places over `V_mod^bad` (of odd residue characteristic). -/
def tateFamilyOfSplit (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
    (hsplit : ∀ w : FinitePlace ↥K, IsBadPlace E K VBad w →
      (curveKw E K w).HasSplitMultiplicativeReduction (w.maximalIdeal.adicCompletionIntegers ↥K)) :
    TateFamily E K ℓ VBad :=
  TateFamily.ofStructures E K ℓ VBad fun w hw =>
    haveI := hsplit w hw
    tateStructureOfSplit E K w (norm_two_eq_one_of_notMem (two_notMem_of_isBadPlace E K hVBad hw))

end

end Iut
