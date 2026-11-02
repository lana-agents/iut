/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.SyncStage

/-!
# `TameCompat` at the stages (MR9 item 4 (b-i))

For lift data `L` at a geometric stage `g = (K₁, τ₀)` ([AbsTopIII] Thm 1.9 (b), (c),
`Topics in Absolute Anabelian Geometry III.txt` l.2144–2157, along the isomorphisms of the
stages):

* `LiftData.hfill`, `gStage_cuspSep`, `LiftData.cuspSep`:
  the inputs of `cycloCongr_tameGen_of_cusps` for the normalised lift `L.e`;
* `TameBridge hτ hU hτ₂ hU₂ Φ χU` (the Prop-valued def "`χU` maps the tame generator of a cusp to
  that of the cusp matched by `bridgeIso Φ`"), **`tameBridge_cycloIso`**;
  `LiftData.cycloVχ_of_tameBridge`, `LiftData.tameCompat_of_tameBridge`: the results below for
  every `χU` with `TameBridge` (used for `(cycloIso Φ).symm` along `Φ.symm`);
* **`LiftData.cycloVχ_cycloIso`**: the coefficients `cycloVχ (cycloIso Φ)` of the stage are the
  cyclotome `cycloCongr L.e` (at a cusp `W` of `U`, every element of `Ẑ(1)` is a tame generator
  `θ_{(W, σ)}`, `tameChar_surjective`; both isomorphisms send it to the tame generator of the image
  cusp, by `cycloCongr_tameGen_of_cusps` for `L.e` and for `bridgeIso Φ`, compared through the
  two charts `τ`, `τ₀` of the same curve, `zHatRes_tameGen_eq`);
* **`LiftData.tameCompat_cycloIso`**: `LiftData.TameCompat (cycloIso Φ) L` — the named debt of
  `LiftData.S_mem_PU` is discharged (the extension `F ⊆ F_{K₁}` is unramified,
  `isUnif_baseChange`); **`LiftData.S_mem_PU_cycloIso`**: `LiftData.S (P_V) ⊆ P_{V'}` for
  `cycloIso Φ` without that debt.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian

universe u

noncomputable section

namespace Iut.Reconstruction

open Thm19

set_option linter.unusedSectionVars false

section Stage

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

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- The normalised lift matches the kernels of the fillings `Π_V ↠ Π_X`. -/
lemma LiftData.hfill (L : LiftData hτ hU hτ₂ hU₂ Φ g) (x : Pi (curveGaloisData K g.hτ₀)) :
    piUToPiX (curveGaloisData K₂ L.hυ) (L.e x) = 1 ↔ piUToPiX (curveGaloisData K g.hτ₀) x = 1 :=
  piUToPiX_eq_one_iff_of_maps (curveGaloisData_H_le K g.hτ₀) (curveGaloisData_H_le K₂ L.hυ) L.e
    L.mapsCuspInertia_e L.mapsCuspInertia_e_symm x

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
include Ω hc hU in
/-- `CuspSep` at the stage curve `V = chartOne τ₀`. -/
lemma gStage_cuspSep (g : GStage K hτ) : CuspSep (curveGaloisData K g.hτ₀) :=
  cuspSep_curve Ω (C := subCurve C (chartOne K C.Xbar g.τ₀) (chartOne_le_U hτ hU g.hτ₀ g.htV)
    (chartOne_ne g.τ₀)) g.hτ₀ rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- `CuspSep` at the target curve `V' = chartOne υ`. -/
lemma LiftData.cuspSep (L : LiftData hτ hU hτ₂ hU₂ Φ g) : CuspSep (curveGaloisData K₂ L.hυ) :=
  cuspSep_curve Ω₂ (C := subCurve C₂ (chartOne K₂ C₂.Xbar L.υ) (chartOne_le_U hτ₂ hU₂ L.hυ L.htV)
    (chartOne_ne L.υ)) L.hυ rfl

variable (hτ hU hτ₂ hU₂ Φ) in
/-- **`χU` carries tame generators of cusps matched by `bridgeIso Φ`**: for cusps `p`, `p'` of `U`,
`U'` with `bridgeIso Φ (I_p) = I_{p'}` and `bridgeIso Φ [σ_p] = [σ_{p'}]`, `χU (θ_p) = θ_{p'}`.
Proved for `cycloIso Φ` (`tameBridge_cycloIso`) and for `(cycloIso Φ).symm` along `Φ.symm`
(`tameBridge_cycloIso_symm`, `Thm19/KummerLift.lean`); used only as an explicit argument of the
generic forms below. -/
def TameBridge (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar)) : Prop :=
  ∀ (p : InertiaIndex (curveGaloisData K hτ)) (p' : InertiaIndex (curveGaloisData K₂ hτ₂)),
    coordT τ ∉ p.1.1 → coordT τ₂ ∉ p'.1.1 →
    (inertiaPi (curveGaloisData K hτ) p.1.1).map
        (bridgeIso hτ hU hτ₂ hU₂ Φ).toMulEquiv.toMonoidHom =
      inertiaPi (curveGaloisData K₂ hτ₂) p'.1.1 →
    bridgeIso hτ hU hτ₂ hU₂ Φ ((p.1.2 : (curveGaloisData K hτ).H) : Pi (curveGaloisData K hτ)) =
      ((p'.1.2 : (curveGaloisData K₂ hτ₂).H) : Pi (curveGaloisData K₂ hτ₂)) →
    χU (tameGen p) = tameGen p'

variable [Fact (0 < (CurvesJacobian.curveGenus K C.Xbar).toNat)]
  [Fact (0 < (CurvesJacobian.curveGenus K₂ C₂.Xbar).toNat)]

set_option maxHeartbeats 1600000 in
-- the quotients `Π_U`, the modules `M_X` and `Ẑ(1)` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
variable (hτ hU hτ₂ hU₂ Φ) in
/-- **`cycloIso Φ` carries tame generators to tame generators** (`cycloCongr_tameGen_of_cusps` for
`bridgeIso Φ`, `cuspSep_curve` on both sides). -/
theorem tameBridge_cycloIso : TameBridge hτ hU hτ₂ hU₂ Φ (cycloIso hτ hU hτ₂ hU₂ Φ) :=
  fun p p' hp hp' hWB hσB =>
    cycloCongr_tameGen_of_cusps (bridgeIso hτ hU hτ₂ hU₂ Φ) (bridgeIso_fill hτ hU hτ₂ hU₂ Φ)
      (gkIso hτ hU hτ₂ hU₂ Φ) (bridgeIso_gk hτ hU hτ₂ hU₂ Φ)
      (fun W hW => exists_map_inertiaH_bridgeIso hτ hU hτ₂ hU₂ Φ W hW)
      (fun W hW => exists_map_inertiaH_bridgeIso_symm hτ hU hτ₂ hU₂ Φ W hW)
      (cuspSep_curve Ω hτ hU) (cuspSep_curve Ω₂ hτ₂ hU₂) p p' hp hp' hWB hσB

set_option maxHeartbeats 3200000 in
-- the quotients `Π_U`, `Π_V`, the modules `M_X` and `Ẑ(1)` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **The coefficients of the stage are the cyclotome of the normalised lift**, for any `χU`
carrying tame generators along `bridgeIso Φ` (`TameBridge`):
`cycloVχ χU = cycloCongr L.e`. -/
theorem LiftData.cycloVχ_of_tameBridge
    (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
      ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))
    (hR : TameBridge hτ hU hτ₂ hU₂ Φ χU) (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (z : ZHatOne (F (curveGaloisData K g.hτ₀)) (FFClosure C.Xbar)) :
    cycloVχ χU g.hτ₀ L.hυ z =
      cycloCongr L.e L.hfill (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk z := by
  -- a cusp `W` of `U`
  obtain ⟨W₁, hW₁⟩ := exists_isCuspPlace₂ Ω C hc.out
  set W : ValuationSubring (FFClosure C.Xbar) :=
    W₁.comap ((σc (Ω := Ω) (C := C)) : FFClosure C.Xbar →+* FFClosure (geomCurve Ω C))
  have hW : W ∈ CuspW (k := K) (t := coordT τ) :=
    (isCuspPlace_comap_iff (Ω := Ω) hτ hU W).1 (by rw [comap_comap_σc]; exact hW₁)
  have hW₀ : W ∈ CuspW (k := K) (t := coordT g.τ₀) :=
    ⟨hW.1, fun h => hW.2 (hW_chart g.htV W hW.1 h).2⟩
  -- every `z` is a tame generator at `W` (on `V`)
  set q₁ : InertiaIndex (curveGaloisData K g.hτ₀) :=
    ⟨(W, 1), hW.1, (inertiaH (curveGaloisData K g.hτ₀) W).one_mem⟩
  have hne₁ := idxVal_ne_top_of_cusp q₁ hW₀.2
  obtain ⟨σ, hσz⟩ := tameChar_surjective hW.1 (unif_valuation_lt_one q₁ hne₁)
    (valuation_le_unif q₁ hne₁) z
  set q : InertiaIndex (curveGaloisData K g.hτ₀) := ⟨(W, (σ : (curveGaloisData K g.hτ₀).H)),
    hW.1, σ.2⟩
  have hq : tameGen q = z := hσz
  -- the image cusp under `L.e`
  obtain ⟨W'', hW'', heW⟩ := L.exists_map_inertiaH_e W hW₀
  have hx : L.e ((σ : (curveGaloisData K g.hτ₀).H) : Pi (curveGaloisData K g.hτ₀)) ∈
      inertiaPi (curveGaloisData K₂ L.hυ) W'' := heW.le ⟨_, ⟨σ, σ.2, rfl⟩, rfl⟩
  obtain ⟨σ'', hσ'', he''⟩ := hx
  set q' : InertiaIndex (curveGaloisData K₂ L.hυ) := ⟨(W'', σ''), hW''.1, hσ''⟩
  have R2 : cycloCongr L.e L.hfill (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (tameGen q) = tameGen q' :=
    cycloCongr_tameGen_of_cusps L.e L.hfill (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk
      (fun W hW => L.exists_map_inertiaH_e W hW) (fun W hW => L.exists_map_inertiaH_e_symm W hW)
      (gStage_cuspSep (Ω := Ω) (hU := hU) g) L.cuspSep q q' hW₀.2 hW''.2 heW he''.symm
  -- the same cusps on `U`, `U'`
  set p : InertiaIndex (curveGaloisData K hτ) :=
    ⟨(W, hT (curveGaloisData K hτ) (curveGaloisData K g.hτ₀) (F_cGD hτ g.hτ₀) σ), hW.1,
      fun a ha => σ.2 a ha⟩
  set p' : InertiaIndex (curveGaloisData K₂ hτ₂) :=
    ⟨(W'', hT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ L.hυ) (F_cGD hτ₂ L.hυ) σ''),
      hW''.1, fun a ha => hσ'' a ha⟩
  have hpq : zHatRes (F (curveGaloisData K hτ)) (F (curveGaloisData K g.hτ₀)) (FFClosure C.Xbar)
      (FFClosure C.Xbar) (tameGen p) = tameGen q :=
    zHatRes_tameGen_eq p q (fun _ => rfl) (valuation_unif_eq_of_eq p q
      (fun x => ⟨F_cGD hτ g.hτ₀ x, F_cGD g.hτ₀ hτ x⟩) rfl (idxVal_ne_top_of_cusp p hW.2)
      (idxVal_ne_top_of_cusp q hW₀.2))
  have hWB : (inertiaPi (curveGaloisData K hτ) W).map
      (bridgeIso hτ hU hτ₂ hU₂ Φ).toMulEquiv.toMonoidHom =
      inertiaPi (curveGaloisData K₂ hτ₂) W'' :=
    (congrArg (fun S => S.map (bridgeIso hτ hU hτ₂ hU₂ Φ).toMulEquiv.toMonoidHom)
      (map_piT_inertiaPi (F_cGD hτ g.hτ₀) (F_cGD g.hτ₀ hτ) (hW_chart g.htV)
        (curveGaloisData_H_le K hτ) W).symm).trans
      ((map_map_eq_of_comm _ L.e.toMulEquiv.toMonoidHom _ _ _ L.he).symm.trans
        ((congrArg (fun S => S.map (piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ L.hυ)
            (F_cGD hτ₂ L.hυ) (hW_chart L.htV) (curveGaloisData_H_le K₂ hτ₂))) heW).trans
          (map_piT_inertiaPi (F_cGD hτ₂ L.hυ) (F_cGD L.hυ hτ₂) (hW_chart L.htV)
            (curveGaloisData_H_le K₂ hτ₂) W'')))
  have ht₂ : coordT τ₂ ∉ W'' := coordT_notMem_of_map _ hW hW''.1 hWB
  have hσB : bridgeIso hτ hU hτ₂ hU₂ Φ ((p.1.2 : (curveGaloisData K hτ).H) :
      Pi (curveGaloisData K hτ)) =
      ((p'.1.2 : (curveGaloisData K₂ hτ₂).H) : Pi (curveGaloisData K₂ hτ₂)) :=
    ((congrArg (piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ L.hυ) (F_cGD hτ₂ L.hυ)
      (hW_chart L.htV) (curveGaloisData_H_le K₂ hτ₂)) he'').trans
      (L.he ((σ : (curveGaloisData K g.hτ₀).H) : Pi (curveGaloisData K g.hτ₀)))).symm
  have R1 : χU (tameGen p) = tameGen p' := hR p p' hW.2 ht₂ hWB hσB
  have hpq' : zHatRes (F (curveGaloisData K₂ hτ₂)) (F (curveGaloisData K₂ L.hυ))
      (FFClosure C₂.Xbar) (FFClosure C₂.Xbar) (tameGen p') = tameGen q' :=
    zHatRes_tameGen_eq p' q' (fun _ => rfl) (valuation_unif_eq_of_eq p' q'
      (fun x => ⟨F_cGD hτ₂ L.hυ x, F_cGD L.hυ hτ₂ x⟩) rfl (idxVal_ne_top_of_cusp p' ht₂)
      (idxVal_ne_top_of_cusp q' hW''.2))
  have e1 : (zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
      (F (curveGaloisData K g.hτ₀))).symm (tameGen q) = tameGen p := by
    rw [ContinuousMulEquiv.symm_apply_eq]
    exact hpq.symm
  rw [← hq]
  calc cycloVχ χU g.hτ₀ L.hυ (tameGen q) =
        zHatResEquiv (FFClosure C₂.Xbar) (F (curveGaloisData K₂ hτ₂))
          (F (curveGaloisData K₂ L.hυ)) (χU
            ((zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
              (F (curveGaloisData K g.hτ₀))).symm (tameGen q))) := rfl
    _ = zHatResEquiv (FFClosure C₂.Xbar) (F (curveGaloisData K₂ hτ₂))
          (F (curveGaloisData K₂ L.hυ)) (tameGen p') := by rw [e1, R1]
    _ = tameGen q' := hpq'
    _ = _ := R2.symm

/-- **The coefficients of the stage are the cyclotome of the normalised lift**:
`cycloVχ (cycloIso Φ) = cycloCongr L.e`. -/
theorem LiftData.cycloVχ_cycloIso (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (z : ZHatOne (F (curveGaloisData K g.hτ₀)) (FFClosure C.Xbar)) :
    cycloVχ (cycloIso hτ hU hτ₂ hU₂ Φ) g.hτ₀ L.hυ z =
      cycloCongr L.e L.hfill (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk z :=
  L.cycloVχ_of_tameBridge _ (tameBridge_cycloIso hτ hU hτ₂ hU₂ Φ) z

set_option maxHeartbeats 3200000 in
-- the quotients `Π_V`, the modules `M_X` and `Ẑ(1)` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **`TameCompat` for every `χU` with `TameBridge`** (e.g. `χU = cycloIso Φ`; [AbsTopIII]
Thm 1.9 (b), (c) along the stage isomorphisms): the tame generator of a cusp of the stage
`U_{K₁}` is that of `U` read in `Ẑ(1)_{F_{K₁}}` (`zHatRes_tameGen_eq`; `F ⊆ F_{K₁} ⊆ F k̄` is
unramified, `isUnif_baseChange`), and `cycloVχ χU = cycloCongr L.e` carries tame generators to
tame generators (`cycloVχ_of_tameBridge`, `cycloCongr_tameGen_of_cusps`). -/
theorem LiftData.tameCompat_of_tameBridge
    (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
      ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))
    (hR : TameBridge hτ hU hτ₂ hU₂ Φ χU) (L : LiftData hτ hU hτ₂ hU₂ Φ g) :
    L.TameCompat χU := by
  intro p p' hp hp' hEq hσ
  have hk₀ : ∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ p.1.1 := fun c => by
    have := p.2.1 (algebraMap K g.K c)
    rwa [← IsScalarTower.algebraMap_apply] at this
  have hk₀' : ∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ p'.1.1 := fun c => by
    have := p'.2.1 (algebraMap K₂ L.tgt.K c)
    rwa [← IsScalarTower.algebraMap_apply] at this
  set p₀ : InertiaIndex (curveGaloisData K g.hτ₀) :=
    ⟨(p.1.1, hRes g.K (curveGaloisData K g.hτ₀) p.1.2), hk₀, hRes_mem_inertiaH p.2.2⟩
  set p₀' : InertiaIndex (curveGaloisData K₂ L.hυ) :=
    ⟨(p'.1.1, hRes L.tgt.K (curveGaloisData K₂ L.hυ) p'.1.2), hk₀', hRes_mem_inertiaH p'.2.2⟩
  have hne := idxVal_ne_top_of_cusp p hp
  have hne' := idxVal_ne_top_of_cusp p' hp'
  have hne₀ := idxVal_ne_top_of_cusp p₀ hp
  have hne₀' := idxVal_ne_top_of_cusp p₀' hp'
  have T0 : zHatRes (F (curveGaloisData K g.hτ₀)) (F g.data) (FFClosure C.Xbar)
      (FFClosure C.Xbar) (tameGen p₀) = tameGen p :=
    zHatRes_tameGen_eq p₀ p (fun _ => rfl) (valuation_unif_eq_of_le p₀ p
      (fun x hx => le_F_constExt (K := g.K) _ hx) rfl hne₀ hne fun f hf hlt =>
        isUnif_baseChange hk₀ (unif_valuation_lt_one p₀ hne₀) (valuation_le_unif p₀ hne₀) f
          (mem_F_baseChange_of_constExt g.K hf) hlt)
  have T0' : zHatRes (F (curveGaloisData K₂ L.hυ)) (F L.tgt.data) (FFClosure C₂.Xbar)
      (FFClosure C₂.Xbar) (tameGen p₀') = tameGen p' :=
    zHatRes_tameGen_eq p₀' p' (fun _ => rfl) (valuation_unif_eq_of_le p₀' p'
      (fun x hx => le_F_constExt (K := L.tgt.K) _ hx) rfl hne₀' hne' fun f hf hlt =>
        isUnif_baseChange hk₀' (unif_valuation_lt_one p₀' hne₀') (valuation_le_unif p₀' hne₀') f
          (mem_F_baseChange_of_constExt L.tgt.K hf) hlt)
  have hσ₀ : L.e ((p₀.1.2 : (curveGaloisData K g.hτ₀).H) : Pi (curveGaloisData K g.hτ₀)) =
      ((p₀'.1.2 : (curveGaloisData K₂ L.hυ).H) : Pi (curveGaloisData K₂ L.hυ)) :=
    (piRes_constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K
      ((p.1.2 : g.data.H) : Pi g.data)).symm.trans
      (congrArg (piRes L.tgt.K (curveGaloisData K₂ L.hυ)) hσ.symm)
  have hW₀ : (inertiaPi (curveGaloisData K g.hτ₀) p.1.1).map L.e.toMulEquiv.toMonoidHom =
      inertiaPi (curveGaloisData K₂ L.hυ) p'.1.1 :=
    (congrArg (fun S => S.map L.e.toMulEquiv.toMonoidHom)
      (map_piRes_inertiaH (K₁ := g.K) hk₀).symm).trans
      ((map_map_eq_of_comm _ (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk
        (piToGk_surjective_curve g.hτ₀) g.K).toMulEquiv.toMonoidHom _ _ _
        (piRes_constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk
          (piToGk_surjective_curve g.hτ₀) g.K)).symm.trans
        ((congrArg (fun S => S.map (piRes L.tgt.K (curveGaloisData K₂ L.hυ))) hEq).trans
          (map_piRes_inertiaH (K₁ := L.tgt.K) hk₀')))
  have hT := cycloCongr_tameGen_of_cusps L.e L.hfill (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk
    (fun W hW => L.exists_map_inertiaH_e W hW) (fun W hW => L.exists_map_inertiaH_e_symm W hW)
    (gStage_cuspSep (Ω := Ω) (hU := hU) g) L.cuspSep p₀ p₀' hp hp' hW₀ hσ₀
  have e1 : (zKEquiv (curveGaloisData K g.hτ₀) g.K).symm (tameGen p) = tameGen p₀ := by
    rw [ContinuousMulEquiv.symm_apply_eq]
    exact T0.symm
  calc constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K
        (tameGen p) =
        zKEquiv (curveGaloisData K₂ L.hυ) L.tgt.K (cycloVχ χU g.hτ₀ L.hυ
          ((zKEquiv (curveGaloisData K g.hτ₀) g.K).symm (tameGen p))) := rfl
    _ = zKEquiv (curveGaloisData K₂ L.hυ) L.tgt.K (tameGen p₀') := by
        rw [e1, L.cycloVχ_of_tameBridge χU hR, hT]
    _ = tameGen p' := T0'

/-- **`TameCompat` for `χU = cycloIso Φ`** ([AbsTopIII] Thm 1.9 (b), (c) along the stage
isomorphisms). -/
theorem LiftData.tameCompat_cycloIso (L : LiftData hτ hU hτ₂ hU₂ Φ g) :
    L.TameCompat (cycloIso hτ hU hτ₂ hU₂ Φ) :=
  L.tameCompat_of_tameBridge _ (tameBridge_cycloIso hτ hU hτ₂ hU₂ Φ)

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V`, the coefficients and the sections unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **[AbsTopIII] Thm 1.9 (c) along the stage isomorphisms, without the debt `TameCompat`**:
for the cyclotome `cycloIso Φ`, `LiftData.S (P_V) ⊆ P_{V'}` at stages whose cusps are
`K₁`-rational (`S_mem_PU` with `tameCompat_cycloIso`). -/
theorem LiftData.S_mem_PU_cycloIso (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
    (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
    (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
    (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
    (hrat : ∀ P : Place g.K (F g.data), IsCuspPlaceF P → ∃ x : RatPoint g.data, placeOfF x = P)
    (η : H1G g) (hη : η ∈ PU g.data) :
    L.S (cycloIso hτ hU hτ₂ hU₂ Φ) (fun p z => cycloIso_smul hτ hU hτ₂ hU₂ Φ p z) η ∈
      PU L.tgt.data :=
  LiftData.S_mem_PU (cycloIso hτ hU hτ₂ hU₂ Φ) (fun p z => cycloIso_smul hτ hU hτ₂ hU₂ Φ p z) L
    σ₀ hσ₀ σ₂ hσ₂ hrat L.tameCompat_cycloIso η hη

end Stage

end Iut.Reconstruction
