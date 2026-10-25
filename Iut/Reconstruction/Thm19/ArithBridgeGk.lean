/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ArithBridgeDecomp
import CurvesJacobian.Kummer.JacobianBridge

/-!
# [AbsTopIII] Thm 1.9: the bridge as an isomorphism of extensions over `G_K`

`Thm19/ArithBridge.lean` and `Thm19/ArithBridgeDecomp.lean` identify the Galois model `Π_U` of
the Kummer side with the `Π_U` of curves-jacobian's `arithmeticExt` (`piBridge`), matching the
geometric subgroups `Δ_U` (`projGk_piBridge_eq_one_iff`). Both `Π_U → G_K` are surjective
(`hToGk_surjective`: `K` is algebraically closed in `K(X̄)`; `projGk_surjective`), so `piBridge`
induces an isomorphism of the quotients:

* **`gkBridge : Gal(k̄ / K) ≃* G_K = π₁ᵉᵗ(Spec K)`** (the `G` of `arithmeticExt`, whose `pr` is
  `projGk`), with **`gkBridge_piToGk`**: `gkBridge ∘ piToGk = projGk ∘ piBridge`, i.e.
  `piBridge` is an isomorphism of the extensions `1 → Δ_U → Π_U → G_K → 1` ([AbsTopIII]
  Thm 1.9: the input `1 → Δ_X → Π_X → G_k → 1`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian CurvesJacobian.Cusp AffOrbicurve KummerTheory
  KummerTheory.Curve CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)

lemma piToGk_surjective_curve : Function.Surjective (piToGk (curveGaloisData K hτ)) := by
  intro g
  obtain ⟨h, rfl⟩ := hToGk_surjective (curveGaloisData K hτ) (mem_range_of_isAlgebraic_F K hτ) g
  exact ⟨h, piToGk_mk _ h⟩

/-- `Π_U (Galois model) → G_K (arithmeticExt)` through `piBridge`. -/
abbrev prBridge :
    Pi (curveGaloisData K hτ) →* π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  (projGk Ω C hc.out).toMonoidHom.comp (piBridge (Ω := Ω) hτ hU).toMulEquiv.toMonoidHom

lemma prBridge_surjective : Function.Surjective (prBridge (Ω := Ω) hτ hU) :=
  (projGk_surjective Ω C hc.out).comp (piBridge (Ω := Ω) hτ hU).surjective

lemma ker_piToGk_eq_ker_prBridge :
    (piToGk (curveGaloisData K hτ)).ker = (prBridge (Ω := Ω) hτ hU).ker := by
  ext p
  have key := (projGk_piBridge_eq_one_iff (Ω := Ω) hτ hU p).symm
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply]
  exact key

/-- **The induced isomorphism `Gal(k̄ / K) ≃* G_K`** of the two quotients `Π_U ↠ G_K`. -/
def gkBridge : Gk K (FFClosure C.Xbar) ≃* π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (piToGk_surjective_curve hτ)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_piToGk_eq_ker_prBridge (Ω := Ω) hτ hU)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (prBridge_surjective (Ω := Ω) hτ hU)))

/-- **`piBridge` is an isomorphism of extensions over `G_K`**:
`gkBridge (piToGk p) = projGk (piBridge p)`. -/
theorem gkBridge_piToGk (p : Pi (curveGaloisData K hτ)) :
    gkBridge (Ω := Ω) hτ hU (piToGk (curveGaloisData K hτ) p) =
      projGk Ω C hc.out (piBridge (Ω := Ω) hτ hU p) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective _ (piToGk_surjective_curve hτ)).symm
      (piToGk (curveGaloisData K hτ) p) = (p : _ ⧸ (piToGk (curveGaloisData K hτ)).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [gkBridge, MulEquiv.trans_apply, h1, MulEquiv.trans_apply]
  rfl

end Iut.Reconstruction.Thm19
