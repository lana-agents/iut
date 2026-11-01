/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.LimIso

/-!
# `lim→ H¹(Π_V, Ẑ(1)) ≃* lim→ H¹(Π_{V'}, Ẑ(1))` over `Π_U ≃ Π_{U'}` (MR9 item 3, step 6, assembly)

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178) is
functorial in isomorphisms `Π_U ≃ Π_{U'}`. With the lift data and their compatibility of
`Thm19/LimIso.lean`:

* `LiftData.inv`: `φ⁻¹`, `e⁻¹` give lift data for `Φ⁻¹` at the target stage, and
  **`LiftData.inv_S_S`**: `L.inv.S ∘ L.S` is the transition map (`h1Congr_eq_resT`);
* **`gLimEquiv : GLim K hτ ≃* GLim K₂ hτ₂`** (`mulEquivOfCocones`) and
  **`h1LimEquiv : H1Lim D ≃* H1Lim D'`** (with `h1LimEquivG`), **`h1LimCycloEquiv`** with the
  cyclotome `cycloIso Φ`.

Hypotheses carried (named debts, unchanged): rel-isom-DGC on both sides (MR7), Belyi
cuspidalization `BelyiCuspSpec` on both sides (MR8), rational points and genus `≠ 0` on both
compactifications (item 1).
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian.Cusp

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction

open Thm19 Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve AffOrbicurve CurvesJacobian
  CurvesJacobian.Kummer WeilCurves.FunctionField


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

/-! ### The inverse lift data -/

section Inv

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
lemma bridgeIso_symm_bridgeIso (z : Pi (curveGaloisData K hτ)) :
    bridgeIso hτ₂ hU₂ hτ hU Φ.symm (bridgeIso hτ hU hτ₂ hU₂ Φ z) = z := by
  apply (piBridge (Ω := Ω) hτ hU).injective
  rw [piBridge_bridgeIso hτ₂ hU₂ hτ hU Φ.symm, piBridge_bridgeIso hτ hU hτ₂ hU₂ Φ]
  exact Φ.pi.symm_apply_apply _

lemma gkIso_symm :
    gkIso hτ₂ hU₂ hτ hU Φ.symm = (gkIso hτ hU hτ₂ hU₂ Φ).symm :=
  MulEquiv.ext fun _ => rfl

set_option maxHeartbeats 800000 in
-- the actions on `Ẑ(1)` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the actions on `Ẑ(1)` are found slowly
/-- `χU⁻¹` is equivariant along `bridgeIso Φ⁻¹`. -/
lemma symm_smul_of_smul (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))
    (hχU : CycloEquivariant (bridgeIso hτ hU hτ₂ hU₂ Φ) χU) :
    CycloEquivariant (bridgeIso hτ₂ hU₂ hτ hU Φ.symm) χU.symm := by
  intro p z
  obtain ⟨q, rfl⟩ := (bridgeIso hτ hU hτ₂ hU₂ Φ).surjective p
  have h1 : bridgeIso hτ₂ hU₂ hτ hU Φ.symm (bridgeIso hτ hU hτ₂ hU₂ Φ q) = q :=
    bridgeIso_symm_bridgeIso q
  calc χU.symm (bridgeIso hτ hU hτ₂ hU₂ Φ q • z)
      = χU.symm (bridgeIso hτ hU hτ₂ hU₂ Φ q • χU (χU.symm z)) :=
        congrArg (fun w => χU.symm (bridgeIso hτ hU hτ₂ hU₂ Φ q • w)) (χU.apply_symm_apply z).symm
    _ = χU.symm (χU (q • χU.symm z)) := congrArg χU.symm (hχU q (χU.symm z)).symm
    _ = q • χU.symm z := χU.symm_apply_apply _
    _ = bridgeIso hτ₂ hU₂ hτ hU Φ.symm (bridgeIso hτ hU hτ₂ hU₂ Φ q) • χU.symm z :=
        congrArg (· • χU.symm z) h1.symm

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
lemma galLift_symm_apply {g : GStage K hτ} (L : LiftData hτ hU hτ₂ hU₂ Φ g) (y) :
    galLift (Ω := Ω₂) (Ω₂ := Ω) L.hυ rfl g.hτ₀ rfl L.φ.symm y =
      (galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ).symm y := rfl

/-- The inverse of `conj b ∘ G` (plain group theory). -/
lemma symm_eq_conj_symm {P Q : Type*} [Group P] [Group Q] (e G : P ≃* Q) (b : Q)
    (h : ∀ x, e x = b * G x * b⁻¹) (y : Q) :
    e.symm y = G.symm (b⁻¹) * G.symm y * (G.symm (b⁻¹))⁻¹ := by
  apply e.injective
  rw [MulEquiv.apply_symm_apply, h]
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv]
  group

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- The normalisation of the inverse lift data. -/
lemma LiftData.he_inv {g : GStage K hτ} (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (y : Pi (curveGaloisData K₂ L.hυ)) :
    piT (curveGaloisData K hτ) (curveGaloisData K g.hτ₀) (F_cGD hτ g.hτ₀) (hW_chart g.htV)
        (curveGaloisData_H_le K hτ) (L.e.symm y) =
      bridgeIso hτ₂ hU₂ hτ hU Φ.symm (piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ L.hυ)
        (F_cGD hτ₂ L.hυ) (hW_chart L.htV) (curveGaloisData_H_le K₂ hτ₂) y) :=
  (bridgeIso_symm_bridgeIso (Φ := Φ) _).symm.trans
    (congrArg (bridgeIso hτ₂ hU₂ hτ hU Φ.symm)
      ((L.he (L.e.symm y)).symm.trans
        (congrArg (piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ L.hυ) (F_cGD hτ₂ L.hυ)
          (hW_chart L.htV) (curveGaloisData_H_le K₂ hτ₂)) (L.e.apply_symm_apply y))))

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- The inverse lift data is conjugate to `galLift φ⁻¹`. -/
lemma LiftData.hb_inv {g : GStage K hτ} (L : LiftData hτ hU hτ₂ hU₂ Φ g) :
    ∃ b, ∀ y, L.e.symm y =
      b * galLift (Ω := Ω₂) (Ω₂ := Ω) L.hυ rfl g.hτ₀ rfl L.φ.symm y * b⁻¹ := by
  obtain ⟨b, hb⟩ := L.hb
  exact ⟨(galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ).symm (b⁻¹), fun y =>
    (symm_eq_conj_symm L.e.toMulEquiv
      (galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ).toMulEquiv b hb y).trans
      (congrArg (fun z => (galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ).symm (b⁻¹) * z *
        ((galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ).symm (b⁻¹))⁻¹)
        (galLift_symm_apply L y).symm)⟩

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- **The inverse lift data**: `φ⁻¹`, `e⁻¹` at the target stage, for `Φ⁻¹`. -/
abbrev LiftData.inv {g : GStage K hτ} (L : LiftData hτ hU hτ₂ hU₂ Φ g) :
    LiftData hτ₂ hU₂ hτ hU Φ.symm L.tgt where
  υ := g.τ₀
  hυ := g.hτ₀
  htV := g.htV
  φ := L.φ.symm
  hφ := L.hφ.symm
  e := L.e.symm
  he := L.he_inv
  hb := L.hb_inv

variable (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))
  (hχU : CycloEquivariant (bridgeIso hτ hU hτ₂ hU₂ Φ) χU)

set_option maxHeartbeats 3200000 in
-- the quotients `Π_V`, their base changes and the coefficients unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **`L.inv.S ∘ L.S` is the transition map** to `(ψ⁻¹ψ(K₁), τ₀) ≥ (K₁, τ₀)`. -/
theorem LiftData.inv_S_S {g : GStage K hτ} (L : LiftData hτ hU hτ₂ hU₂ Φ g) (x : H1G g) :
    limOf (fun _ _ h => resG h) L.inv.tgt
      (L.inv.S χU.symm (symm_smul_of_smul χU hχU) (L.S χU hχU x)) =
      limOf (fun _ _ h => resG h) g x := by
  have hK : g.K ≤ constField (gkIso hτ₂ hU₂ hτ hU Φ.symm)
      (constField (gkIso hτ hU hτ₂ hU₂ Φ) g.K) := by
    rw [gkIso_symm]
    exact le_constField_symm L.e _ L.he_gk (piToGk_surjective_curve g.hτ₀) g.K
  have hle : g ≤ L.inv.tgt := ⟨hK, self_mem_chartRing K _⟩
  have hE : ∀ y, piT g.data L.inv.tgt.data (GStage.F_mono (g := g) (g' := L.inv.tgt) hle)
      (GStage.hW_mono (g := g) (g' := L.inv.tgt) hle) g.data_H_le
      (((constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K).trans
        (constIso L.inv.e (gkIso hτ₂ hU₂ hτ hU Φ.symm) L.inv.he_gk
          (piToGk_surjective_curve L.tgt.hτ₀) L.tgt.K)) y) = y := fun y => by
    refine piRes_injective (K := g.K) (curveGaloisData K g.hτ₀) ?_
    have e1 := piRes_piT (K₁ := g.K) (K₂ := L.inv.tgt.K) (D₁ := curveGaloisData K g.hτ₀)
      (D₂ := curveGaloisData K g.hτ₀) (GStage.F_mono (g := g) (g' := L.inv.tgt) hle)
      (GStage.hW_mono (g := g) (g' := L.inv.tgt) hle) g.data_H_le (F_cGD g.hτ₀ g.hτ₀)
      (hW_chart (self_mem_chartRing K _)) (curveGaloisData_H_le K g.hτ₀)
      (((constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
        g.K).trans (constIso L.inv.e (gkIso hτ₂ hU₂ hτ hU Φ.symm) L.inv.he_gk
          (piToGk_surjective_curve L.tgt.hτ₀) L.tgt.K)) y)
    have e2 := piRes_constIso L.inv.e (gkIso hτ₂ hU₂ hτ hU Φ.symm) L.inv.he_gk
      (piToGk_surjective_curve L.tgt.hτ₀) L.tgt.K
      (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K y)
    have e3 := piRes_constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk
      (piToGk_surjective_curve g.hτ₀) g.K y
    exact e1.trans ((piT_self _ _ _ _).trans (e2.trans ((congrArg L.e.symm e3).trans
      (L.e.symm_apply_apply _))))
  have hc : ∀ z, ((constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K).trans
      (constCyclo (gkIso hτ₂ hU₂ hτ hU Φ.symm) (cycloVχ χU.symm L.tgt.hτ₀ L.inv.hυ) L.tgt.K)) z =
      zT g.data L.inv.tgt.data z := fun z => by
    have s1 := constCyclo_cycloVχ χU.symm L.inv
      (constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K z)
    have s2 := constCyclo_cycloVχ χU L z
    have s3 := (zHatRes_zHatRes (F (curveGaloisData K₂ hτ₂)) (F L.tgt.data)
      (F (curveGaloisData K₂ hτ₂)) (χU (zHatRes (F g.data) (F (curveGaloisData K hτ))
        (FFClosure C.Xbar) (FFClosure C.Xbar) z))).trans (zHatRes_self _ _)
    have s4 := χU.symm_apply_apply (zHatRes (F g.data) (F (curveGaloisData K hτ))
      (FFClosure C.Xbar) (FFClosure C.Xbar) z)
    have s5 := zHatRes_zHatRes (F g.data) (F (curveGaloisData K hτ)) (F L.inv.tgt.data) z
    refine s1.trans (Eq.trans ?_ s5)
    refine congrArg (zHatRes (F (curveGaloisData K hτ)) (F L.inv.tgt.data) (FFClosure C.Xbar)
      (FFClosure C.Xbar)) (Eq.trans ?_ s4)
    exact congrArg χU.symm ((congrArg (zHatRes (F L.tgt.data) (F (curveGaloisData K₂ hτ₂))
      (FFClosure C₂.Xbar) (FFClosure C₂.Xbar)) s2).trans s3)
  refine Eq.trans (congrArg (limOf (F := H1G (hτ := hτ)) (fun _ _ h => resG h) L.inv.tgt) ?_)
    (limOf_f (F := H1G (hτ := hτ)) (fun _ _ h => resG h) hle x)
  exact (h1Congr_h1Congr
    (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K)
    (constIso L.inv.e (gkIso hτ₂ hU₂ hτ hU Φ.symm) L.inv.he_gk
      (piToGk_surjective_curve L.tgt.hτ₀) L.tgt.K)
    (constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K)
    (constCyclo (gkIso hτ₂ hU₂ hτ hU Φ.symm) (cycloVχ χU.symm L.tgt.hτ₀ L.inv.hυ) L.tgt.K)
    (constCyclo_smul L.e _ L.he_gk _ _ (cycloVχ_smul χU _ hχU g.hτ₀ L.hυ L.he) g.K)
    (constCyclo_smul L.inv.e _ L.inv.he_gk _ _
      (cycloVχ_smul χU.symm _ (symm_smul_of_smul χU hχU) L.tgt.hτ₀ L.inv.hυ L.inv.he) L.tgt.K)
    x).trans
    (h1Congr_eq_resT (D₁ := g.data) (D₂ := L.inv.tgt.data)
      (hF := GStage.F_mono (g := g) (g' := L.inv.tgt) hle)
      (hW := GStage.hW_mono (g := g) (g' := L.inv.tgt) hle) (hH := g.data_H_le) _ _ _ hE hc x)

end Inv

/-! ### The isomorphism of the colimits -/

section Assembly

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- A choice of lift data. -/
def LiftData.choose (Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out))
    (hS : BelyiCuspSpec Ω C hc.out) (g : GStage K hτ) : LiftData hτ hU hτ₂ hU₂ Φ g :=
  (LiftData.nonempty hS g).some

lemma resG_refl {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsIntegral X] [IsFunctionField k X.functionField] {τ : X.functionField}
    {hτ : Transcendental k τ} (g : GStage k hτ) (y : H1G g) : resG (le_refl g) y = y :=
  resT_self _ _ _ y

variable (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))
  (hχU : CycloEquivariant (bridgeIso hτ hU hτ₂ hU₂ Φ) χU)
  (hS : BelyiCuspSpec Ω C hc.out)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- **The cocone** `H¹(Π_{V_{K₁}}) → GLim'` at a geometric stage (a choice of lift data). -/
def coc (g : GStage K hτ) : H1G g →* GLim K₂ hτ₂ :=
  (limOf (fun _ _ h => resG h) (LiftData.choose Φ hS g).tgt).comp
    ((LiftData.choose Φ hS g).S χU hχU).toMonoidHom

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
lemma coc_apply (g : GStage K hτ) (x : H1G g) :
    coc χU hχU hS g x = limOf (F := H1G (hτ := hτ₂)) (fun _ _ h => resG h)
      (LiftData.choose Φ hS g).tgt ((LiftData.choose Φ hS g).S χU hχU x) := rfl

variable [CharZero (FFClosure C.Xbar)] [CharZero (FFClosure C₂.Xbar)]
  (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
  (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
  (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
  (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
  (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
  (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ in
lemma coc_compat (hDGC : RelIsomDGC.Exists K₂) (g g₂ : GStage K hτ) (h : g ≤ g₂) (x : H1G g) :
    coc χU hχU hS g x = coc χU hχU hS g₂ (resG h x) :=
  (coc_apply χU hχU hS g x).trans ((LiftData.compat χU hχU σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC h
    (LiftData.choose Φ hS g) (LiftData.choose Φ hS g₂) x).trans
      (coc_apply χU hχU hS g₂ (resG h x)).symm)

variable (hS₂ : BelyiCuspSpec Ω₂ C₂ hc₂.out)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ in
/-- **The reverse cocone is a left inverse** on generators. -/
theorem coc_inv (hDGC₁ : RelIsomDGC.Exists K)
    (g : GStage K hτ) (x : H1G g) :
    limLift (fun _ _ h => resG h) (coc χU.symm (symm_smul_of_smul χU hχU) hS₂)
      (coc_compat χU.symm (symm_smul_of_smul χU hχU) hS₂ σ₂ hσ₂ hg₂ σ₀ hσ₀ hg hDGC₁)
      (coc χU hχU hS g x) = ⟦⟨g, x⟩⟧ := by
  have e1 := LiftData.compat χU.symm (symm_smul_of_smul χU hχU) σ₂ hσ₂ hg₂ σ₀ hσ₀ hg hDGC₁
    (le_refl _) (LiftData.choose Φ.symm hS₂ (LiftData.choose Φ hS g).tgt)
    (LiftData.choose Φ hS g).inv ((LiftData.choose Φ hS g).S χU hχU x)
  have e2 := congrArg (limLift (fun _ _ h => resG h) (coc χU.symm (symm_smul_of_smul χU hχU) hS₂)
      (coc_compat χU.symm (symm_smul_of_smul χU hχU) hS₂ σ₂ hσ₂ hg₂ σ₀ hσ₀ hg hDGC₁))
    (coc_apply χU hχU hS g x)
  have e3 := limLift_limOf (fun _ _ h => resG h) (coc χU.symm (symm_smul_of_smul χU hχU) hS₂)
      (coc_compat χU.symm (symm_smul_of_smul χU hχU) hS₂ σ₂ hσ₂ hg₂ σ₀ hσ₀ hg hDGC₁)
      (LiftData.choose Φ hS g).tgt ((LiftData.choose Φ hS g).S χU hχU x)
  have e4 := coc_apply χU.symm (symm_smul_of_smul χU hχU) hS₂ (LiftData.choose Φ hS g).tgt
    ((LiftData.choose Φ hS g).S χU hχU x)
  have e5 := congrArg (fun v => limOf (F := H1G (hτ := hτ)) (fun _ _ h => resG h)
      (LiftData.choose Φ hS g).inv.tgt
      ((LiftData.choose Φ hS g).inv.S χU.symm (symm_smul_of_smul χU hχU) v))
    (resG_refl _ ((LiftData.choose Φ hS g).S χU hχU x))
  exact e2.trans (e3.trans (e4.trans (e1.trans (e5.trans
    (((LiftData.choose Φ hS g).inv_S_S χU hχU x).trans
      (limOf_apply (F := H1G (hτ := hτ)) (fun _ _ h => resG h) g x))))))

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ in
/-- **`GLim ≃* GLim'`** over an isomorphism `Φ` of the `arithmeticExt`, for any `Φ`-equivariant
identification `χU` of the cyclotomes (e.g. `cycloIso Φ`). -/
def gLimEquiv (hDGC : RelIsomDGC.Exists K₂) (hDGC₁ : RelIsomDGC.Exists K) :
    GLim K hτ ≃* GLim K₂ hτ₂ :=
  mulEquivOfCocones (fun _ _ h => resG h) (fun _ _ h => resG h) (coc χU hχU hS)
    (coc_compat χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC)
    (coc χU.symm (symm_smul_of_smul χU hχU) hS₂)
    (coc_compat χU.symm (symm_smul_of_smul χU hχU) hS₂ σ₂ hσ₂ hg₂ σ₀ hσ₀ hg hDGC₁)
    (coc_inv χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC₁)
    (coc_inv χU.symm (symm_smul_of_smul χU hχU) hS₂ σ₂ hσ₂ hg₂ σ₀ hσ₀ hg hS hDGC)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ in
/-- **`lim→_V H¹(Π_V, Ẑ(1)) ≃* lim→_{V'} H¹(Π_{V'}, Ẑ(1))`** ([AbsTopIII] Thm 1.9 (d) is
functorial in `Π_U ≃ Π_{U'}`), through the geometric stages (`h1LimEquivG`). -/
def h1LimEquiv (hDGC : RelIsomDGC.Exists K₂) (hDGC₁ : RelIsomDGC.Exists K) :
    H1Lim (curveGaloisData K hτ) ≃* H1Lim (curveGaloisData K₂ hτ₂) :=
  h1LimEquivG.trans ((gLimEquiv χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC
    hDGC₁).trans h1LimEquivG.symm)

end Assembly

section CycloAssembly

variable [Fact (0 < (CurvesJacobian.curveGenus K C.Xbar).toNat)]
  [Fact (0 < (CurvesJacobian.curveGenus K₂ C₂.Xbar).toNat)]
  [CharZero (FFClosure C.Xbar)] [CharZero (FFClosure C₂.Xbar)]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
variable (hτ hU hτ₂ hU₂ Φ) in
/-- **[AbsTopIII] Thm 1.9 (d) over `Φ`**: `lim→_V H¹(Π_V, Ẑ(1)) ≃* lim→_{V'} H¹(Π_{V'}, Ẑ(1))`
with the cyclotome `cycloIso Φ` (genus `≥ 1`). Debts: `hS`, `hS₂` (`BelyiCuspSpec`, MR8),
`hDGC`, `hDGC₁` (rel-isom-DGC, MR7); rational points `σ₀`, `σ₂` (item 1). -/
def h1LimCycloEquiv (hS : BelyiCuspSpec Ω C hc.out) (hS₂ : BelyiCuspSpec Ω₂ C₂ hc₂.out)
    (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
    (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
    (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
    (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
    (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
    (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0)
    (hDGC : RelIsomDGC.Exists K₂) (hDGC₁ : RelIsomDGC.Exists K) :
    H1Lim (curveGaloisData K hτ) ≃* H1Lim (curveGaloisData K₂ hτ₂) :=
  h1LimEquiv (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ) hS
    σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁

end CycloAssembly

end Lift

end Iut.Reconstruction
