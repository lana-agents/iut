/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ResStage
import Iut.Reconstruction.Thm19.PiJCongr
import Iut.Reconstruction.Thm19.ConstGk

/-!
# `G_{K₁}`, `Π_{X}`, `Π_{J¹}`, `Δ_X^{ab}` and `η_D` along lift data (MR9 item 4, step 3)

For lift data `L` at a geometric stage `g = (K₁, τ₀)` (`Thm19/LimIso.lean`), the stage isomorphism
`constIso L.e` preserves cuspidal inertia (`Thm19/ResStage.lean`), hence induces the isomorphisms
needed to transport the criterion of [AbsTopIII] Prop 1.6 (ii)
(`Topics in Absolute Anabelian Geometry III.txt` l.1993–2000) used for `P_V` in Thm 1.9 (c):

* `GStage.instFactPiJ1`; **`LiftData.gk`** (`G_{K₁} ≃ₜ* G_{ψ(K₁)}`, `gkConstIso`),
  `LiftData.piToGk_e`;
* **`LiftData.piX`** (`piXCongr`, kernels of the fillings matched by
  `piUToPiX_eq_one_iff_of_maps`), `LiftData.piXToGk_piX`, **`LiftData.piJ1`**,
  **`LiftData.deltaAb`**;
* **`LiftData.eta_mapDomain`**: `η_{β_* f} = h1Congr (η_f)` for a map `β` of `K₁`-rational points
  with matching sections `t_x` (`Thm19/PiJCongr.lean`).
-/

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian.Cusp

namespace Iut.Reconstruction

open Thm19 Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve AffOrbicurve CurvesJacobian
  CurvesJacobian.Kummer

section StageJ

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}
  [hc₂ : Fact (C₂.U : Set C₂.Xbar)ᶜ.Nonempty]
  [CharZero (FFClosure C.Xbar)] [CharZero (FFClosure C₂.Xbar)]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic

variable {τ : C.Xbar.functionField} {hτ : Transcendental K τ}
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] {hU : C.U = chartOne K C.Xbar τ}
  {τ₂ : C₂.Xbar.functionField} {hτ₂ : Transcendental K₂ τ₂}
  [IsGalois (K₀ K₂ (coordT τ₂)) (FFClosure C₂.Xbar)] {hU₂ : C₂.U = chartOne K₂ C₂.Xbar τ₂}
  {Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out)} {g : GStage K hτ}

/-- `Π_{J¹} ↠ G_{K₁}` is surjective at a geometric stage (`K₁` is the field of constants). -/
instance GStage.instFactPiJ1 (g' : GStage K hτ) :
    Fact (Function.Surjective (piJ1ToGk g'.data)) :=
  CurvesJacobian.Kummer.fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F_constExt g'.K
    (mem_range_of_isAlgebraic_F K g'.hτ₀))

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **`G_{K₁} ≃ₜ* G_{ψ(K₁)}`** under the stage isomorphism of lift data. -/
def LiftData.gk (L : LiftData hτ hU hτ₂ hU₂ Φ g) :
    Gk g.K (FFClosure C.Xbar) ≃ₜ* Gk L.tgt.K (FFClosure C₂.Xbar) :=
  gkConstIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K
    (mem_range_of_isAlgebraic_F K g.hτ₀) (mem_range_of_isAlgebraic_F K₂ L.hυ)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
lemma LiftData.piToGk_e (L : LiftData hτ hU hτ₂ hU₂ Φ g) (p : Pi g.data) :
    piToGk L.tgt.data
        (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K p) =
      L.gk (piToGk g.data p) :=
  piToGk_constIso _ _ _ _ _ _ _ p

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **`Π_{X_{K₁}} ≃ₜ* Π_{X'_{ψ(K₁)}}`** at a stage (the stage isomorphism matches the kernels of
the fillings: `piUToPiX_eq_one_iff_of_maps`). -/
def LiftData.piX (L : LiftData hτ hU hτ₂ hU₂ Φ g) : PiX g.data ≃ₜ* PiX L.tgt.data :=
  piXCongr (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K)
    (piUToPiX_eq_one_iff_of_maps g.data_H_le L.tgt.data_H_le _
      (mapsCuspInertia_constIso _ _ _ _ g.K L.mapsCuspInertia_e)
      (mapsCuspInertia_constIso_symm _ _ _ _ g.K L.mapsCuspInertia_e_symm))

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
lemma LiftData.piXToGk_piX (L : LiftData hτ hU hτ₂ hU₂ Φ g) (y : PiX g.data) :
    piXToGk L.tgt.data (L.piX y) = L.gk (piXToGk g.data y) :=
  piXToGk_piXCongr _ _ L.gk.toMulEquiv L.piToGk_e y

/-- **`Π_{J¹}` at a stage**, along the lift data. -/
def LiftData.piJ1 (L : LiftData hτ hU hτ₂ hU₂ Φ g) : PiJ1 g.data ≃ₜ* PiJ1 L.tgt.data :=
  piJ1Congr L.piX L.gk L.piXToGk_piX

/-- **`Δ_X^{ab}` at a stage**, along the lift data. -/
def LiftData.deltaAb (L : LiftData hτ hU hτ₂ hU₂ Φ g) : DeltaAb g.data ≃ₜ* DeltaAb L.tgt.data :=
  deltaAbCongr L.piX L.gk L.piXToGk_piX

set_option synthInstance.maxHeartbeats 400000 in
-- the action of `G_{K₁}` on `Δ_X^{ab}` is found slowly
/-- **`η_D` at a stage along the lift data**, for a map `β` of `K₁`-rational points whose sections
`t_{β x}` have trivial difference class against the transported `t_x`. -/
theorem LiftData.eta_mapDomain (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (β : RatPoint g.data → RatPoint L.tgt.data)
    (hβ : ∀ x, diffClass (sectionCongr L.piX L.gk L.piXToGk_piX (tSection x)) (tSection (β x)) = 1)
    (f : RatPoint g.data →₀ ℤ) (hf : (f.sum fun _ n => n) = 0) :
    eta (f.mapDomain β) =
      h1Congr L.gk L.deltaAb (deltaAbCongr_smul' L.piX L.gk L.piXToGk_piX) (eta f) :=
  Thm19.eta_mapDomain L.piX L.gk L.piXToGk_piX β hβ f hf

end StageJ

end Iut.Reconstruction
