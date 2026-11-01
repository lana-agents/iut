/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.StageLift
import Iut.Reconstruction.Thm19.ResIso

/-!
# Cuspidal inertia along the lifts in the Galois models (MR9 item 4, step 1 at the stages)

For a lift `φ : Π_V ≃ₜ* Π_{V₂}` of [AbsTopII] Cor 3.8 (`IsCor38Lift`, an isomorphism of cuspidal
extensions by [AbsTopI] Lemma 4.5 (v), `IsCor38Lift.iso`), `galLift φ` carries the cuspidal
inertia groups of `V` onto those of `V₂` in the Galois models
(**`IsCor38Lift.exists_map_inertiaH_galLift`**, from `exists_map_inertiaH_bridgeIso`).
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian.Cusp

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction

open Thm19 Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve AffOrbicurve CurvesJacobian
  CurvesJacobian.Kummer

section GalLift

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}
  [hc₂ : Fact (C₂.U : Set C₂.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)
  {τ₂ : C₂.Xbar.functionField} (hτ₂ : Transcendental K₂ τ₂)
  [IsGalois (K₀ K₂ (coordT τ₂)) (FFClosure C₂.Xbar)] (hU₂ : C₂.U = chartOne K₂ C₂.Xbar τ₂)
  (Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out))
  {V : C.Xbar.Opens} {hV : V ≤ C.U} {hne : (V : Set C.Xbar).Nonempty}
  [hcV : Fact ((subCurve C V hV hne).U : Set (subCurve C V hV hne).Xbar)ᶜ.Nonempty]
  {V₂ : C₂.Xbar.Opens} {hV₂ : V₂ ≤ C₂.U} {hne₂ : (V₂ : Set C₂.Xbar).Nonempty}
  [hcV₂ : Fact ((subCurve C₂ V₂ hV₂ hne₂).U : Set (subCurve C₂ V₂ hV₂ hne₂).Xbar)ᶜ.Nonempty]
  {τ₀ : C.Xbar.functionField} (hτ₀ : Transcendental K τ₀)
  [IsGalois (K₀ K (coordT τ₀)) (FFClosure C.Xbar)] (hU₀ : V = chartOne K C.Xbar τ₀)
  {υ : C₂.Xbar.functionField} (hυ : Transcendental K₂ υ)
  [IsGalois (K₀ K₂ (coordT υ)) (FFClosure C₂.Xbar)] (hUυ : V₂ = chartOne K₂ C₂.Xbar υ)
  (hF : ∀ x ∈ F (curveGaloisData K hτ), x ∈ F (curveGaloisData K hτ₀))
  (hW : ∀ W : ValuationSubring (FFClosure C.Xbar),
    (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) → coordT τ₀ ∈ W →
      (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) ∧ coordT τ ∈ W)
  (hF₂ : ∀ x ∈ F (curveGaloisData K₂ hτ₂), x ∈ F (curveGaloisData K₂ hυ))
  (hW₂ : ∀ W : ValuationSubring (FFClosure C₂.Xbar),
    (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) → coordT υ ∈ W →
      (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) ∧ coordT τ₂ ∈ W)
  (φ : (arithmeticExt Ω (subCurve C V hV hne) hcV.out).Pi ≃ₜ*
    (arithmeticExt Ω₂ (subCurve C₂ V₂ hV₂ hne₂) hcV₂.out).Pi)


set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **A Cor 3.8 lift carries cuspidal inertia onto cuspidal inertia** in the Galois models. -/
theorem IsCor38Lift.exists_map_inertiaH_galLift
    (h : IsCor38Lift Φ.pi.toMulEquiv hV hne hV₂ hne₂ φ) (W : ValuationSubring (FFClosure C.Xbar))
    (hW : W ∈ CuspW (k := K) (t := coordT τ₀)) :
    ∃ W' ∈ CuspW (k := K₂) (t := coordT υ),
      ((inertiaH (curveGaloisData K hτ₀) W).map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ₀).H
            (curveGaloisData K hτ₀).S))).map
          (galLift (Ω := Ω) (Ω₂ := Ω₂) hτ₀ hU₀ hυ hUυ φ).toMulEquiv.toMonoidHom =
        (inertiaH (curveGaloisData K₂ hυ) W').map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K₂ hυ).H
            (curveGaloisData K₂ hυ).S)) :=
  exists_map_inertiaH_bridgeIso (C := subCurve C V hV hne) (C' := subCurve C₂ V₂ hV₂ hne₂)
    hτ₀ hU₀ hυ hUυ (h.iso Φ.g Φ.pr_comm) W hW

end GalLift

end Iut.Reconstruction
