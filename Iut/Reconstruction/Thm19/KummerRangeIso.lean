/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.KummerLift
import Iut.Reconstruction.Thm19.KummerRangeG
import Iut.Reconstruction.Thm19.LimOfG

/-!
# `K^×_{Z_NF}` is carried along `Φ` (MR9 item 4, step 4, "H")

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178)
reconstructs `K^×_{Z_NF} ⊆ lim→_V H¹(Π_V, μ_Ẑ(Π_U))` group-theoretically from `Π_U`. Here this is
made precise as functoriality: the isomorphism `h1LimCycloEquiv` of the colimits over an
isomorphism `Φ` of the arithmetic fundamental groups (cyclotome `cycloIso Φ`,
`Thm19/LimEquiv.lean`) maps `kummerNFRange` onto `kummerNFRange`:

* `tameBridge_cycloIso_symm`: `(cycloIso Φ).symm` carries tame generators along `Φ.symm`, hence
  `TameCompat` for the lift data of `Φ.symm` (`LiftData.tameCompat_of_tameBridge`);
* `gLimEquiv_symm_mk`, `h1LimEquiv_symm_apply`, **`h1LimEquiv_symm_ofG`**: the inverse on the
  classes of geometric stages; `h1LimCycloEquiv_ofG`, `h1LimCycloEquiv_symm_ofG` for `cycloIso Φ`;
* `LiftData.ofG_S_mem_kummerNFRange`, `LiftData.ofG_S_symm_mem_kummerNFRange`: for any lift data at
  a stage with rational cusps, `[L.tgt, L.S κ(v)] ∈ kummerNFRange` (G, `S_mem_PU`, A);
* **`h1LimCycloEquiv_mem_kummerNFRange`**, **`h1LimCycloEquiv_symm_mem_kummerNFRange`**: a class of
  `kummerNFRange` is `ofG g (κ v)` at a stage with rational cusps (`exists_ratStage_of_mem`, B), is
  sent to `ofG L.tgt (L.S κ v)` (`h1LimEquiv_ofG`, C), a class of `P_{V'}`
  (`S_mem_PU`) with a Kummer class as a positive power (`LiftData.S_kummer_pow`, G), which lies in
  `kummerNFRange` (`ofG_mem_kummerNFRange`, A);
* **`map_kummerNFRange_h1LimCycloEquiv`**: `(kummerNFRange N).map φ = kummerNFRange N'`.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian

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

variable [Fact (0 < (CurvesJacobian.curveGenus K C.Xbar).toNat)]
  [Fact (0 < (CurvesJacobian.curveGenus K₂ C₂.Xbar).toNat)]
  [CharZero (FFClosure C.Xbar)] [CharZero (FFClosure C₂.Xbar)]

set_option maxHeartbeats 1600000 in
-- the quotients `Π_U` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
variable (hτ hU hτ₂ hU₂ Φ) in
/-- **`(cycloIso Φ).symm` carries tame generators along `Φ.symm`** (`tameBridge_cycloIso` for the
cusps matched by `bridgeIso Φ`, `bridgeIso_symm_bridgeIso`). -/
theorem tameBridge_cycloIso_symm :
    TameBridge hτ₂ hU₂ hτ hU Φ.symm (cycloIso hτ hU hτ₂ hU₂ Φ).symm := by
  intro p p' hp hp' hWB hσB
  have hinv : ∀ x, bridgeIso hτ hU hτ₂ hU₂ Φ (bridgeIso hτ₂ hU₂ hτ hU Φ.symm x) = x := fun x => by
    obtain ⟨q, rfl⟩ := (bridgeIso hτ hU hτ₂ hU₂ Φ).surjective x
    rw [bridgeIso_symm_bridgeIso]
  have hWB' : (inertiaPi (curveGaloisData K hτ) p'.1.1).map
      (bridgeIso hτ hU hτ₂ hU₂ Φ).toMulEquiv.toMonoidHom =
      inertiaPi (curveGaloisData K₂ hτ₂) p.1.1 := by
    have hid : (bridgeIso hτ hU hτ₂ hU₂ Φ).toMulEquiv.toMonoidHom.comp
        (bridgeIso hτ₂ hU₂ hτ hU Φ.symm).toMulEquiv.toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext hinv
    rw [← hWB, Subgroup.map_map, hid, Subgroup.map_id]
  have hσB' : bridgeIso hτ hU hτ₂ hU₂ Φ
      ((p'.1.2 : (curveGaloisData K hτ).H) : Pi (curveGaloisData K hτ)) =
      ((p.1.2 : (curveGaloisData K₂ hτ₂).H) : Pi (curveGaloisData K₂ hτ₂)) := by
    rw [← hσB, hinv]
  rw [ContinuousMulEquiv.symm_apply_eq]
  exact (tameBridge_cycloIso hτ hU hτ₂ hU₂ Φ p' p hp' hp hWB' hσB').symm

section Inverse

variable (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))
  (hχU : CycloEquivariant (bridgeIso hτ hU hτ₂ hU₂ Φ) χU)
  (hS : BelyiCuspSpec Ω C hc.out)
  (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
  (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
  (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
  (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
  (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
  (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0)
  (hS₂ : BelyiCuspSpec Ω₂ C₂ hc₂.out)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- The inverse of `gLimEquiv` on a generator: `[g₂, y] ↦ [L'.tgt, L'.S y]` for the lift data
`L' = LiftData.choose Φ.symm hS₂ g₂`. -/
lemma gLimEquiv_symm_mk (hDGC : RelIsomDGC.Exists K₂) (hDGC₁ : RelIsomDGC.Exists K)
    (g : GStage K₂ hτ₂) (y : H1G g) :
    (gLimEquiv χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁).symm ⟦⟨g, y⟩⟧ =
      ⟦⟨(LiftData.choose (hτ := hτ₂) (hU := hU₂) (hτ₂ := hτ) (hU₂ := hU) Φ.symm hS₂ g).tgt,
        (LiftData.choose (hτ := hτ₂) (hU := hU₂) (hτ₂ := hτ) (hU₂ := hU) Φ.symm hS₂ g).S
          χU.symm (symm_smul_of_smul χU hχU) y⟩⟧ :=
  (coc_apply χU.symm (symm_smul_of_smul χU hχU) hS₂ g y).trans
    (limOf_apply (F := H1G (hτ := hτ)) (fun _ _ h => resG h) _ _)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
lemma h1LimEquiv_symm_apply (hDGC : RelIsomDGC.Exists K₂) (hDGC₁ : RelIsomDGC.Exists K)
    (x : H1Lim (curveGaloisData K₂ hτ₂)) :
    (h1LimEquiv χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁).symm x =
      h1LimEquivG.symm ((gLimEquiv χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁).symm
        (h1LimEquivG x)) :=
  (MulEquiv.symm_trans_apply _ _ x).trans (congrArg h1LimEquivG.symm
    ((MulEquiv.symm_trans_apply _ _ x).trans
      (congrArg (gLimEquiv χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁).symm
        (congrFun (congrArg DFunLike.coe (MulEquiv.symm_symm (h1LimEquivG (k := K₂) (hτ := hτ₂))))
          x))))

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
theorem h1LimEquiv_symm_ofG (hDGC : RelIsomDGC.Exists K₂) (hDGC₁ : RelIsomDGC.Exists K)
    (g : GStage K₂ hτ₂) (y : H1G g) :
    (h1LimEquiv χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁).symm (ofG g y) =
      ofG (LiftData.choose (hτ := hτ₂) (hU := hU₂) (hτ₂ := hτ) (hU₂ := hU) Φ.symm hS₂ g).tgt
        ((LiftData.choose (hτ := hτ₂) (hU := hU₂) (hτ₂ := hτ) (hU₂ := hU) Φ.symm hS₂ g).S
          χU.symm (symm_smul_of_smul χU hχU) y) :=
  (h1LimEquiv_symm_apply χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁ (ofG g y)).trans
    ((congrArg (fun z => h1LimEquivG.symm
      ((gLimEquiv χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁).symm z))
      (h1LimEquivG_ofG g y)).trans
      ((congrArg h1LimEquivG.symm
        (gLimEquiv_symm_mk χU hχU hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁ g y)).trans
        (h1LimEquivG_symm_mk _ _)))


end Inverse

section Range

variable (hS : BelyiCuspSpec Ω C hc.out) (hS₂ : BelyiCuspSpec Ω₂ C₂ hc₂.out)
  (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
  (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
  (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
  (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
  (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
  (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0)
  (hDGC : RelIsomDGC.Exists K₂) (hDGC₁ : RelIsomDGC.Exists K)
  (N : NFModel (curveGaloisData K hτ)) (N₂ : NFModel (curveGaloisData K₂ hτ₂))

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- `h1LimCycloEquiv` on a geometric stage (`h1LimEquiv_ofG` for `cycloIso Φ`). -/
lemma h1LimCycloEquiv_ofG (g : GStage K hτ) (y : H1G g) :
    h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ (ofG g y) =
      ofG (LiftData.choose Φ hS g).tgt ((LiftData.choose Φ hS g).S
        (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ) y) :=
  h1LimEquiv_ofG (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ) hS σ₀ hσ₀ hg σ₂ hσ₂
    hg₂ hS₂ hDGC hDGC₁ g y

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- The inverse of `h1LimCycloEquiv` on a geometric stage (`h1LimEquiv_symm_ofG`). -/
lemma h1LimCycloEquiv_symm_ofG (g : GStage K₂ hτ₂) (y : H1G g) :
    (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).symm (ofG g y) =
      ofG (LiftData.choose (hτ := hτ₂) (hU := hU₂) (hτ₂ := hτ) (hU₂ := hU) Φ.symm hS₂ g).tgt
        ((LiftData.choose (hτ := hτ₂) (hU := hU₂) (hτ₂ := hτ) (hU₂ := hU) Φ.symm hS₂ g).S
          (cycloIso hτ hU hτ₂ hU₂ Φ).symm
          (symm_smul_of_smul _ (cycloIso_smul hτ hU hτ₂ hU₂ Φ)) y) :=
  h1LimEquiv_symm_ofG (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ) hS σ₀ hσ₀ hg
    σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁ g y

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` and the classes at two stages unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
include hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC in
/-- At a stage with rational cusps carrying a unit that is not an algebraic number, the image
`[L.tgt, L.S κ(v)]` of a Kummer class lies in `kummerNFRange` (G, `S_mem_PU_cycloIso`, A). -/
theorem LiftData.ofG_S_mem_kummerNFRange {g : GStage K hτ} (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (hrat : ∀ P : Place g.K (F g.data), IsCuspPlaceF P → ∃ x : RatPoint g.data, placeOfF x = P)
    (v f₀ : units g.data)
    (hf₀ : ¬ IsAlgebraic ℚ (((f₀ : (F g.data)ˣ) : F g.data) : FFClosure C.Xbar)) :
    ofG L.tgt (L.S (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ)
      (kummerMapZHat g.data v)) ∈ kummerNFRange N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂) :=
  (L.S_kummer_pow (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ) σ₀ hσ₀ hg σ₂ hσ₂
    hg₂ hDGC hS hrat L.tameCompat_cycloIso v f₀ hf₀).elim fun _ hM => hM.2.elim fun _ hw' =>
      ofG_mem_kummerNFRange N₂ σ₂ hσ₂ _ (L.S_mem_PU_cycloIso σ₀ hσ₀ σ₂ hσ₂ hrat
        (kummerMapZHat g.data v) ⟨v, rfl⟩) hM.1 hw'

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` and the classes at two stages unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
include hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC₁ in
/-- The same for the lift data of `Φ.symm` and `(cycloIso Φ).symm` (`tameBridge_cycloIso_symm`). -/
theorem LiftData.ofG_S_symm_mem_kummerNFRange {g : GStage K₂ hτ₂}
    (L : LiftData hτ₂ hU₂ hτ hU Φ.symm g)
    (hrat : ∀ P : Place g.K (F g.data), IsCuspPlaceF P → ∃ x : RatPoint g.data, placeOfF x = P)
    (v f₀ : units g.data)
    (hf₀ : ¬ IsAlgebraic ℚ (((f₀ : (F g.data)ˣ) : F g.data) : FFClosure C₂.Xbar)) :
    ofG L.tgt (L.S (cycloIso hτ hU hτ₂ hU₂ Φ).symm
      (symm_smul_of_smul _ (cycloIso_smul hτ hU hτ₂ hU₂ Φ)) (kummerMapZHat g.data v)) ∈
      kummerNFRange N (mem_range_of_isAlgebraic_F K hτ) :=
  (L.S_kummer_pow (cycloIso hτ hU hτ₂ hU₂ Φ).symm
    (symm_smul_of_smul _ (cycloIso_smul hτ hU hτ₂ hU₂ Φ)) σ₂ hσ₂ hg₂ σ₀ hσ₀ hg hDGC₁ hS₂ hrat
    (L.tameCompat_of_tameBridge _ (tameBridge_cycloIso_symm hτ hU hτ₂ hU₂ Φ)) v f₀ hf₀).elim
    fun _ hM => hM.2.elim fun _ hw' =>
      ofG_mem_kummerNFRange N σ₀ hσ₀ _ (L.S_mem_PU _ _ σ₂ hσ₂ σ₀ hσ₀ hrat
        (L.tameCompat_of_tameBridge _ (tameBridge_cycloIso_symm hτ hU hτ₂ hU₂ Φ))
        (kummerMapZHat g.data v) ⟨v, rfl⟩) hM.1 hw'

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- **`h1LimCycloEquiv` maps `kummerNFRange` into `kummerNFRange`** (B, C, G, A). -/
theorem h1LimCycloEquiv_mem_kummerNFRange {ξ : H1Lim (curveGaloisData K hτ)}
    (hξ : ξ ∈ kummerNFRange N (mem_range_of_isAlgebraic_F K hτ)) :
    h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ ξ ∈
      kummerNFRange N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂) :=
  (exists_ratStage_of_mem N hξ).elim fun g hgx => hgx.elim fun v hv => hv.elim fun f₀ h =>
    Eq.subst (motive := fun z => h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC
        hDGC₁ z ∈ kummerNFRange N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)) h.2.1
      (Eq.subst (motive := fun z => z ∈ kummerNFRange N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂))
        (h1LimCycloEquiv_ofG hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ g
          (kummerMapZHat g.data v)).symm
        ((LiftData.choose Φ hS g).ofG_S_mem_kummerNFRange hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC N₂
          h.1 v f₀ h.2.2))

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- **The inverse of `h1LimCycloEquiv` maps `kummerNFRange` into `kummerNFRange`** (B, C, G, A for
`Φ.symm` and `(cycloIso Φ).symm`, `tameBridge_cycloIso_symm`). -/
theorem h1LimCycloEquiv_symm_mem_kummerNFRange {ξ : H1Lim (curveGaloisData K₂ hτ₂)}
    (hξ : ξ ∈ kummerNFRange N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)) :
    (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).symm ξ ∈
      kummerNFRange N (mem_range_of_isAlgebraic_F K hτ) :=
  (exists_ratStage_of_mem N₂ hξ).elim fun g hgx => hgx.elim fun v hv => hv.elim fun f₀ h =>
    Eq.subst (motive := fun z => (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC
        hDGC₁).symm z ∈ kummerNFRange N (mem_range_of_isAlgebraic_F K hτ)) h.2.1
      (Eq.subst (motive := fun z => z ∈ kummerNFRange N (mem_range_of_isAlgebraic_F K hτ))
        (h1LimCycloEquiv_symm_ofG hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ g
          (kummerMapZHat g.data v)).symm
        ((LiftData.choose (hτ := hτ₂) (hU := hU₂) (hτ₂ := hτ) (hU₂ := hU) Φ.symm hS₂
          g).ofG_S_symm_mem_kummerNFRange hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC₁ N h.1 v f₀ h.2.2))

/-- **[AbsTopIII] Thm 1.9 (d) is functorial in `Φ`**: the isomorphism `h1LimCycloEquiv` of the
colimits `lim→_V H¹(Π_V, Ẑ(1))` maps the image `kummerNFRange` of `K^×_{Z_NF}` onto that of
`K'^×_{Z'_NF}`. Debts as for `h1LimCycloEquiv` (`BelyiCuspSpec`, `RelIsomDGC.Exists`, rational
points, genus `≠ 0`). -/
theorem map_kummerNFRange_h1LimCycloEquiv :
    (kummerNFRange N (mem_range_of_isAlgebraic_F K hτ)).map
        (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).toMonoidHom =
      kummerNFRange N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂) :=
  le_antisymm
    (fun _ ⟨_, hξ, hξe⟩ => hξe ▸
      h1LimCycloEquiv_mem_kummerNFRange hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ hξ)
    (fun _ hξ => ⟨_, h1LimCycloEquiv_symm_mem_kummerNFRange hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC
      hDGC₁ N N₂ hξ, MulEquiv.apply_symm_apply _ _⟩)

end Range

end Lift

end Iut.Reconstruction
