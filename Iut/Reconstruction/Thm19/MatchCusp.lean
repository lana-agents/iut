/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.OrdMatch

/-!
# Matched cusps of the stage isomorphisms (MR9 item 4, step 5)

The bijection of the points of the triples of [AbsTopIII] Thm 1.9 (e) along `Φ` sends a point `x`
of `Z_NF` (a cusp `W` of a geometric stage `g` on which `x` has been removed) to the cusp `W''`
of the target stage `L.tgt` whose inertia group is the image of that of `W`
(`exists_map_inertiaH_constIso`).
Here the tools for the well-definedness of `x ↦ W'' ∩ F k̄₂`:

* **`mem_iff_of_ratPoint`**: two places over the same rational point of `F` agree on `F k̄`
  (`eq_placeOf_of_liesOver`: `x_{k̄}` is the only place of `F k̄` over `x`);
* `mem_F_curveGaloisData_iff`: the function field of the Galois model of a curve does not depend
  on the coordinate;
* **`GStage.map_piT_inertiaPi`**: for geometric stages `g ≤ g'` the transition `Π_{V'} → Π_V` maps
  the inertia group of `W` onto that of `W` (`piRes_piT`, `map_piRes_inertiaH`,
  `map_piT_inertiaPi'`, `piRes_injective`);
* **`LiftData.comap_eq_of_le`**: the matched cusp does not depend on the stage — for `g ≤ g₃` the
  cusps of `L.tgt` and `L₃.tgt` matched with the same cusp `W` agree on the function field of
  `L.tgt`;
* **`LiftData.mem_iff_of_le`**: for a rational cusp, the matched cusps agree on `F k̄₂`.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian IsLocalRing

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- The place of `F k̄` cut out by a place `W ⊇ k` of `Ω` over a rational point `x` of `F`. -/
def placeBarOfRat (x : RatPoint D) (W : ValuationSubring Ω)
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : ∀ y : F D, (y : Ω) ∈ W ↔ (y : Ω) ∈ x.A) :
    Place (kbar k Ω) (F (baseChange D)) :=
  ⟨W.comap (algebraMap (F (baseChange D)) Ω), fun htop => (placeOfF x).ne_top (by
    refine eq_top_iff.2 fun y _ => ?_
    have : ιF D y ∈ W.comap (algebraMap (F (baseChange D)) Ω) :=
      htop ▸ ValuationSubring.mem_top _
    change ((ιF D y : F (baseChange D)) : Ω) ∈ W at this
    rw [coe_ιF] at this
    exact (hW y).1 this), fun c => kbar_mem W hk c⟩

lemma placeBarOfRat_eq (x : RatPoint D) (W : ValuationSubring Ω)
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : ∀ y : F D, (y : Ω) ∈ W ↔ (y : Ω) ∈ x.A) :
    placeBarOfRat x W hk hW = placeOf x :=
  eq_placeOf_of_liesOver x _ fun u => by
    change ((ιF D u : F (baseChange D)) : Ω) ∈ W ↔ _
    rw [coe_ιF, mem_placeOfF]
    exact hW u

/-- **Places over a rational point agree on `F k̄`**: if `W₁, W₂ ⊇ k` both lie over the
rational point `x` of `F`, they contain the same elements of `F k̄` (`x_{k̄}` is the only place
of `F k̄` over `x`, `eq_placeOf_of_liesOver`). -/
theorem mem_iff_of_ratPoint (x : RatPoint D) {W₁ W₂ : ValuationSubring Ω}
    (hk₁ : ∀ c : k, algebraMap k Ω c ∈ W₁) (hk₂ : ∀ c : k, algebraMap k Ω c ∈ W₂)
    (hW₁ : ∀ y : F D, (y : Ω) ∈ W₁ ↔ (y : Ω) ∈ x.A)
    (hW₂ : ∀ y : F D, (y : Ω) ∈ W₂ ↔ (y : Ω) ∈ x.A) {y : Ω} (hy : y ∈ F (baseChange D)) :
    y ∈ W₁ ↔ y ∈ W₂ := by
  have e := (placeBarOfRat_eq x W₁ hk₁ hW₁).trans (placeBarOfRat_eq x W₂ hk₂ hW₂).symm
  have h := congrArg
    (fun Q : Place (kbar k Ω) (F (baseChange D)) => (⟨y, hy⟩ : F (baseChange D)) ∈ Q.1) e
  exact (Eq.to_iff h :)

end Generic

section Geom

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [IsFunctionField k X.functionField] {τ : X.functionField}
  {hτ : Transcendental k τ} [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

/-- **The function field of the Galois model of a curve does not depend on the coordinate.** -/
lemma mem_F_curveGaloisData_iff {τ' : X.functionField} (hτ' : Transcendental k τ')
    {x : FFClosure X} :
    x ∈ F (curveGaloisData k hτ') ↔ x ∈ Set.range (algebraMap X.functionField (FFClosure X)) := by
  change x ∈ (curveGaloisData k hτ').L ↔ _
  rw [curveGaloisData_L]
  exact Iff.rfl

variable [IsAlgClosed (FFClosure X)]

set_option maxHeartbeats 800000 in
-- the quotients `Π_V` of two stages and of two charts unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **Inertia groups along the transition of geometric stages** `g ≤ g'`: the transition
`Π_{V'} → Π_V` maps the inertia group of `W ⊇ K₁'` onto that of `W` (compare in `Π_{U_{τ₀}}` by
`piRes`, which is injective: `piRes_piT`, `map_piRes_inertiaH`, `map_piT_inertiaPi'`). -/
theorem GStage.map_piT_inertiaPi {g g' : GStage k hτ} (h : g ≤ g')
    {W : ValuationSubring (FFClosure X)} (hkW : ∀ c : g'.K, algebraMap g'.K (FFClosure X) c ∈ W) :
    (inertiaPi g'.data W).map (piT g.data g'.data (F_mono h) (hW_mono h) g.data_H_le) =
      inertiaPi g.data W := by
  have hk : ∀ c : k, algebraMap k (FFClosure X) c ∈ W := fun c => by
    rw [IsScalarTower.algebraMap_apply k g'.K (FFClosure X)]
    exact hkW _
  have hkW₁ : ∀ c : g.K, algebraMap g.K (FFClosure X) c ∈ W := fun c => hkW ⟨c, h.1 c.2⟩
  have hF : ∀ x ∈ F (curveGaloisData k g.hτ₀), x ∈ F (curveGaloisData k g'.hτ₀) := fun _ hx =>
    (mem_F_curveGaloisData_iff g'.hτ₀).2 ((mem_F_curveGaloisData_iff g.hτ₀).1 hx)
  have hF' : ∀ x ∈ F (curveGaloisData k g'.hτ₀), x ∈ F (curveGaloisData k g.hτ₀) := fun _ hx =>
    (mem_F_curveGaloisData_iff g.hτ₀).2 ((mem_F_curveGaloisData_iff g'.hτ₀).1 hx)
  have hW' : ∀ W : ValuationSubring (FFClosure X), (∀ c : k, algebraMap k (FFClosure X) c ∈ W) →
      coordT g'.τ₀ ∈ W → (∀ c : k, algebraMap k (FFClosure X) c ∈ W) ∧ coordT g.τ₀ ∈ W :=
    fun W hk ht => ⟨hk, mem_of_mem_chartRing W hk ht h.2⟩
  have hsq : ∀ y : Pi g'.data, piRes g.K (curveGaloisData k g.hτ₀)
      (piT g.data g'.data (F_mono h) (hW_mono h) g.data_H_le y) =
      piT (curveGaloisData k g.hτ₀) (curveGaloisData k g'.hτ₀) hF hW'
        (curveGaloisData_H_le k g.hτ₀) (piRes g'.K (curveGaloisData k g'.hτ₀) y) := fun y =>
    piRes_piT (K₁ := g.K) (K₂ := g'.K) (D₁ := curveGaloisData k g.hτ₀)
      (D₂ := curveGaloisData k g'.hτ₀) (F_mono h) (hW_mono h) g.data_H_le hF hW'
      (curveGaloisData_H_le k g.hτ₀) y
  refine Subgroup.map_injective (piRes_injective (K := g.K) (curveGaloisData k g.hτ₀))
    ((Subgroup.map_map _ _ _).trans ((congrArg (fun φ => (inertiaPi g'.data W).map φ)
      (MonoidHom.ext hsq)).trans
      ((Subgroup.map_map _ _ _).symm.trans ((congrArg (fun S => S.map (piT
        (curveGaloisData k g.hτ₀) (curveGaloisData k g'.hτ₀) hF hW'
        (curveGaloisData_H_le k g.hτ₀))) (map_piRes_inertiaH g'.K hk)).trans
        ((map_piT_inertiaPi' hF hF' hW' (curveGaloisData_H_le k g.hτ₀) W).trans
          (map_piRes_inertiaH g.K hk).symm)))))

end Geom

end Iut.Reconstruction.Thm19

namespace Iut.Reconstruction

open Thm19

section Lift

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
  {Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out)}
  (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
  (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
  (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
  (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
  (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
  (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0) (hDGC : RelIsomDGC.Exists K₂)

variable [Fact (0 < (CurvesJacobian.curveGenus K₂ C₂.Xbar).toNat)]

set_option maxHeartbeats 3200000 in
-- the quotients `Π_V` of four stages unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC in
/-- **The matched cusp does not depend on the stage**: for geometric stages `g ≤ g₃` with lift
data `L`, `L₃`, a cusp `W` of `g` (`W ⊇ K₁(g₃)`), and cusps `W''` of `L.tgt`, `W₃''` of `L₃.tgt`
whose inertia groups are the images of that of `W`, the places `W₃''` and `W''` agree on the
function field of `L.tgt` (`exists_conj_const`, `GStage.map_piT_inertiaPi` on both sides,
`GStage.comap_eq_of_conj_inertiaH` at `L.tgt`). -/
theorem LiftData.comap_eq_of_le {g g₃ : GStage K hτ} (h : g ≤ g₃)
    (L : LiftData hτ hU hτ₂ hU₂ Φ g) (L₃ : LiftData hτ hU hτ₂ hU₂ Φ g₃)
    (W : ValuationSubring (FFClosure C.Xbar))
    (hkW : ∀ c : g₃.K, algebraMap g₃.K (FFClosure C.Xbar) c ∈ W)
    (W'' W₃'' : ValuationSubring (FFClosure C₂.Xbar))
    (hW'' : W'' ∈ CuspW (k := L.tgt.K) (t := coordT L.υ))
    (hk₃'' : ∀ c : L₃.tgt.K, algebraMap L₃.tgt.K (FFClosure C₂.Xbar) c ∈ W₃'')
    (hI : (inertiaPi g.data W).map
        (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
          g.K).toMulEquiv.toMonoidHom = inertiaPi L.tgt.data W'')
    (hI₃ : (inertiaPi g₃.data W).map
        (constIso L₃.e (gkIso hτ hU hτ₂ hU₂ Φ) L₃.he_gk (piToGk_surjective_curve g₃.hτ₀)
          g₃.K).toMulEquiv.toMonoidHom = inertiaPi L₃.tgt.data W₃'') :
    W₃''.comap (algebraMap (F L.tgt.data) (FFClosure C₂.Xbar)) =
      W''.comap (algebraMap (F L.tgt.data) (FFClosure C₂.Xbar)) := by
  have hle : L.tgt ≤ L₃.tgt := L.le_tgt σ₂ hσ₂ hg₂ h L₃
  obtain ⟨m, -, hm⟩ := L.exists_conj_const σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC h L₃
  have e1 := map_eq_conj_of_square
    (piT g.data g₃.data (GStage.F_mono h) (GStage.hW_mono h) g.data_H_le)
    (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
      g.K).toMulEquiv.toMonoidHom
    (constIso L₃.e (gkIso hτ hU hτ₂ hU₂ Φ) L₃.he_gk (piToGk_surjective_curve g₃.hτ₀)
      g₃.K).toMulEquiv.toMonoidHom
    (piT L.tgt.data L₃.tgt.data (GStage.F_mono hle) (GStage.hW_mono hle) L.tgt.data_H_le)
    m hm (S₁ := inertiaPi g₃.data W) (R₂ := inertiaPi g.data W)
    (R₃ := inertiaPi L.tgt.data W₃'')
    (GStage.map_piT_inertiaPi h hkW) hI₃ (GStage.map_piT_inertiaPi hle hk₃'') rfl rfl
  -- `I_{W''} = m⁻¹ I_{W₃''} m` in `Π_{V'}`
  have e2 : (inertiaPi L.tgt.data W₃'').map (MulAut.conj m⁻¹).toMonoidHom =
      inertiaPi L.tgt.data W'' := e1.symm.trans hI
  have hkW₃ : ∀ c : L.tgt.K, algebraMap L.tgt.K (FFClosure C₂.Xbar) c ∈ W₃'' :=
    fun c => hk₃'' ⟨c, hle.1 c.2⟩
  have hne : inertiaPi L.tgt.data W'' ≠ ⊥ := fun h0 =>
    hW''.2 (L.coordT_mem_of_inertiaPi_eq_bot W'' hW''.1 h0)
  have hW₃'' : W₃'' ∈ CuspW (k := L.tgt.K) (t := coordT L.υ) := by
    refine ⟨hkW₃, fun ht => hne ?_⟩
    rw [← e2, inertiaPi_eq_bot_of_mem L.tgt.data_H_le hkW₃ ht, Subgroup.map_bot]
  exact GStage.comap_eq_of_conj_inertiaH Ω₂ hτ₂ hU₂ L.tgt W₃'' W'' hW₃'' hW'' m⁻¹ e2

omit hc [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] [CharZero (FFClosure C.Xbar)] in
/-- A place of `Ω` containing `K₁` of a geometric stage contains every finite extension of `K`
inside `Ω` (the algebraic elements). -/
lemma Thm19.GStage.mem_of_le_K {g g₃ : GStage K hτ} {A : ValuationSubring (FFClosure C.Xbar)}
    (hk : ∀ c : g.K, algebraMap g.K (FFClosure C.Xbar) c ∈ A) (c : g₃.K) :
    algebraMap g₃.K (FFClosure C.Xbar) c ∈ A := by
  have hK : ∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ A := fun c => by
    rw [IsScalarTower.algebraMap_apply K g.K (FFClosure C.Xbar)]
    exact hk _
  exact Curve.mem_of_isIntegral hK ((Algebra.IsIntegral.isIntegral (R := K) c).algebraMap)

set_option maxHeartbeats 3200000 in
-- the quotients `Π_V` of four stages unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC in
/-- **The matched cusp of a rational cusp, on `F k̄₂`**: for `g ≤ g₃`, a `K₁`-rational cusp
`x.A` of `g` and the cusps `W''` of `L.tgt`, `W₃''` of `L₃.tgt` matched with it, `W₃''` and `W''`
contain the same elements of `F k̄₂` (`LiftData.comap_eq_of_le`; `W''` is rational,
`LiftData.cuspPoint`, so `mem_iff_of_ratPoint` applies). -/
theorem LiftData.mem_iff_of_le {g g₃ : GStage K hτ} (h : g ≤ g₃)
    (L : LiftData hτ hU hτ₂ hU₂ Φ g) (L₃ : LiftData hτ hU hτ₂ hU₂ Φ g₃)
    (x : RatPoint g.data) (hx : x.A ∈ CuspW (k := g.K) (t := coordT g.τ₀))
    (W'' W₃'' : ValuationSubring (FFClosure C₂.Xbar))
    (hW'' : W'' ∈ CuspW (k := L.tgt.K) (t := coordT L.υ))
    (hk₃'' : ∀ c : L₃.tgt.K, algebraMap L₃.tgt.K (FFClosure C₂.Xbar) c ∈ W₃'')
    (hI : (inertiaPi g.data x.A).map
        (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
          g.K).toMulEquiv.toMonoidHom = inertiaPi L.tgt.data W'')
    (hI₃ : (inertiaPi g₃.data x.A).map
        (constIso L₃.e (gkIso hτ hU hτ₂ hU₂ Φ) L₃.he_gk (piToGk_surjective_curve g₃.hτ₀)
          g₃.K).toMulEquiv.toMonoidHom = inertiaPi L₃.tgt.data W₃'')
    {y : FFClosure C₂.Xbar} (hy : y ∈ F (baseChange (curveGaloisData K₂ hτ₂))) :
    y ∈ W₃'' ↔ y ∈ W'' := by
  have hle : L.tgt ≤ L₃.tgt := L.le_tgt σ₂ hσ₂ hg₂ h L₃
  have hc := L.comap_eq_of_le σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC h L₃ x.A
    (GStage.mem_of_le_K x.hk) W'' W₃'' hW'' hk₃'' hI hI₃
  have hD := L.map_decompH_constIso x.A hx W'' hW'' hI
  have hy' : y ∈ F (baseChange L.tgt.data) := by
    have h' := (mem_F_baseChange_stage_iff L.tgt.toStage).2 hy
    rwa [GStage.toStage_data] at h'
  exact mem_iff_of_ratPoint (L.cuspPoint x W'' hW'' hD) (fun c => hk₃'' ⟨c, hle.1 c.2⟩) hW''.1
    (fun z => (SetLike.ext_iff.1 hc z :)) (fun _ => Iff.rfl) hy'

end Lift

end Iut.Reconstruction
