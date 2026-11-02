/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.LimEquiv

/-!
# `h1LimEquiv` on the classes of geometric stages (MR9 item 4, step 4)

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178) along `Φ`:
the isomorphism `h1LimEquiv : H1Lim D ≃* H1Lim D'` (`Thm19/LimEquiv.lean`) sends the class
`[g, y]` of `y ∈ H¹(Π_{V_{K₁}})` at a geometric stage `g` to the class of `L.S y` at the target
stage `L.tgt` of the chosen lift data `L`:

* `gLimEquiv_mk`, `h1LimEquiv_apply`, `h1LimEquivG_ofG`, `h1LimEquivG_symm_mk`,
  **`h1LimEquiv_ofG`**.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp Belyi Belyi.Anabelian

universe u

noncomputable section

namespace Iut.Reconstruction

open Thm19

set_option linter.unusedSectionVars false

section Lift

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}
  [hc₂ : Fact (C₂.U : Set C₂.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic

variable {τ : C.Xbar.functionField} {hτ : Transcendental K τ}
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] {hU : C.U = chartOne K C.Xbar τ}
  {τ₂ : C₂.Xbar.functionField} {hτ₂ : Transcendental K₂ τ₂}
  [IsGalois (K₀ K₂ (coordT τ₂)) (FFClosure C₂.Xbar)] {hU₂ : C₂.U = chartOne K₂ C₂.Xbar τ₂}
  {Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out)}
  (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))
  (hχU : CycloEquivariant (bridgeIso hτ hU hτ₂ hU₂ Φ) χU)
  (hS : BelyiCuspSpec Ω C hc.out)
  [CharZero (FFClosure C.Xbar)] [CharZero (FFClosure C₂.Xbar)]
  (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
  (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
  (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
  (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
  (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
  (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0)
  (hS₂ : BelyiCuspSpec Ω₂ C₂ hc₂.out)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- `gLimEquiv` on a generator: `[g, y] ↦ [L.tgt, L.S y]`. -/
lemma gLimEquiv_mk (hDGC : RelIsomDGC.Exists K₂) (hDGC₁ : RelIsomDGC.Exists K)
    (g : GStage K hτ) (y : H1G g) :
    gLimEquiv χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁ ⟦⟨g, y⟩⟧ =
      ⟦⟨(LiftData.choose Φ hS g).tgt, (LiftData.choose Φ hS g).S χU hχU y⟩⟧ :=
  (coc_apply χU hχU hS g y).trans (limOf_apply (F := H1G (hτ := hτ₂)) (fun _ _ h => resG h)
    (LiftData.choose Φ hS g).tgt ((LiftData.choose Φ hS g).S χU hχU y))


set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
lemma h1LimEquiv_apply (hDGC : RelIsomDGC.Exists K₂) (hDGC₁ : RelIsomDGC.Exists K)
    (x : H1Lim (curveGaloisData K hτ)) :
    h1LimEquiv χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁ x =
      h1LimEquivG.symm (gLimEquiv χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁
        (h1LimEquivG x)) := rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
omit [CharZero (FFClosure C.Xbar)] in
lemma h1LimEquivG_ofG (g : GStage K hτ) (y : H1G g) :
    h1LimEquivG (ofG g y) = (⟦⟨g, y⟩⟧ : GLim K hτ) :=
  toG_ofG g y

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
omit [CharZero (FFClosure C₂.Xbar)] in
lemma h1LimEquivG_symm_mk (g : GStage K₂ hτ₂) (y : H1G g) :
    h1LimEquivG.symm (⟦⟨g, y⟩⟧ : GLim K₂ hτ₂) = ofG g y :=
  (MulEquiv.symm_apply_eq _).2 (toG_ofG g y).symm

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- **`h1LimEquiv` on a geometric stage**: `[g, y] ↦ [L.tgt, L.S y]` for the chosen lift data
`L = LiftData.choose Φ hS g` (`toG_ofG`, `gLimEquiv_mk`). -/
theorem h1LimEquiv_ofG (hDGC : RelIsomDGC.Exists K₂) (hDGC₁ : RelIsomDGC.Exists K)
    (g : GStage K hτ) (y : H1G g) :
    h1LimEquiv χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁ (ofG g y) =
      ofG (LiftData.choose Φ hS g).tgt ((LiftData.choose Φ hS g).S χU hχU y) :=
  (h1LimEquiv_apply χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁ (ofG g y)).trans
    ((congrArg (fun z => h1LimEquivG.symm (gLimEquiv χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC
      hDGC₁ z)) (h1LimEquivG_ofG g y)).trans
      ((congrArg h1LimEquivG.symm
        (gLimEquiv_mk χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁ g y)).trans
        (h1LimEquivG_symm_mk _ _)))

end Lift

end Iut.Reconstruction
