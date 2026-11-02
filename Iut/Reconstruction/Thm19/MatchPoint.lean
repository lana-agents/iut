/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.OrdCompat

/-!
# Every point of `Z_NF` is a rational cusp of a geometric stage (MR9 item 4, step 5)

For the bijection of the points of the triples of [AbsTopIII] Thm 1.9 (e) along `Φ`, every point
`x` of `Z_NF` (a place of `F_NF = F k̄`) is represented by a rational cusp `x.A` of a geometric
stage (`x` removed from the open, all cusps rational), the input of `val_eq_of_matched`:

* **`exists_ratCusp_nfPlace`**: a function `y ∉ W` of `F_NF` lies on a stage `(K', τ)`
  (`exists_finite_mem_F_constExt`), `W` becomes a cusp of a stage by a coordinate with a pole at
  `W` (`exists_coord_pole`), the cusps become rational after a finite extension
  (`GStage.exists_ge_ratCusps`), and the rational point `x` over `W ∩ F` cuts out the same point of
  `F k̄` (`mem_iff_of_ratPoint`).
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian IsLocalRing

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section Geom

variable {k : Type u} [Field k] [CharZero k] [NumberField k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X] {τ : X.functionField}
  {hτ : Transcendental k τ} [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)]
  [IsAlgClosed (FFClosure X)]

attribute [local instance] isAlgClosed_algebraicClosure isFunctionField_fnf

omit [NumberField k] [CharZero (FFClosure X)] [IsAlgClosed (FFClosure X)] in
/-- A place containing `k` contains the field of constants of every geometric stage. -/
lemma GStage.mem_K_of_mem_k (g : GStage k hτ) {W : ValuationSubring (FFClosure X)}
    (hk : ∀ c : k, algebraMap k (FFClosure X) c ∈ W) (c : g.K) :
    algebraMap g.K (FFClosure X) c ∈ W :=
  Curve.mem_of_isIntegral hk ((Algebra.IsIntegral.isIntegral (R := k) c).algebraMap)

set_option maxHeartbeats 1600000 in
-- the function fields of three stages unify slowly
/-- **Every point of `Z_NF` is a rational cusp of a geometric stage**: for every place `P` of
`F_NF / k̄_NF` there are a geometric stage `g` with all cusps rational and a rational point
`x` of `g` which is a cusp of `g` and an NF-point with `W ∩ F_NF = P` for `W = x.A`. -/
theorem exists_ratCusp_nfPlace (N : NFModel (curveGaloisData k hτ))
    (P : Place (algebraicClosure ℚ (FFClosure X)) (fnf N)) :
    ∃ (g : GStage k hτ) (x : RatPoint g.data) (_ : x.A ∈ CuspW (k := g.K) (t := coordT g.τ₀))
      (hk : ∀ c : k, algebraMap k (FFClosure X) c ∈ x.A) (hW : N.IsNFPoint x.A),
      nfPlace hk hW = P := by
  obtain ⟨W, hk, hW, rfl⟩ := exists_nfPlace_eq P
  obtain ⟨y, hyN, hyW⟩ := hW
  obtain ⟨K', hK', hyK'⟩ := exists_finite_mem_F_constExt (curveGaloisData k hτ)
    (mem_range_of_isAlgebraic_F k hτ) (N.mem_F y hyN)
  obtain ⟨g, hyg⟩ : ∃ g : GStage k hτ, y ∈ F g.data :=
    ⟨⟨K', τ, hτ, self_mem_chartRing k _⟩, hyK'⟩
  -- `W` is a cusp of a stage `g''`
  obtain ⟨τ₀'', hτ₀'', h₀, hA⟩ := exists_coord_pole g W (g.mem_K_of_mem_k hk) ⟨⟨y, hyg⟩, hyW⟩
  obtain ⟨g'', hAc⟩ : ∃ g'' : GStage k hτ, coordT g''.τ₀ ∉ W :=
    ⟨⟨g.K, τ₀'', hτ₀'', GStage.mem_chartRing_trans' g.htV h₀⟩, hA⟩
  -- all cusps rational on `g₀ ≥ g''` (same coordinate)
  obtain ⟨g₀, -, hτeq, hrat⟩ := g''.exists_ge_ratCusps
  have ht₀ : coordT g₀.τ₀ ∉ W := hτeq ▸ hAc
  have hk₀ := g₀.mem_K_of_mem_k hk
  let P₀ : Place g₀.K (F g₀.data) := ⟨W.comap (algebraMap (F g₀.data) (FFClosure X)),
    fun htop => ht₀ (by
      have : tF g₀.data ∈ W.comap (algebraMap (F g₀.data) (FFClosure X)) :=
        htop ▸ ValuationSubring.mem_top _
      exact this), fun c => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact hk₀ c⟩
  obtain ⟨x, hx⟩ := hrat P₀ ht₀
  have hiff : ∀ z : F g₀.data, (z : FFClosure X) ∈ x.A ↔ (z : FFClosure X) ∈ W := fun z => by
    have h := congrArg (fun Q : Place g₀.K (F g₀.data) => z ∈ Q.1) hx
    exact (Eq.to_iff h :)
  have hxc : x.A ∈ CuspW (k := g₀.K) (t := coordT g₀.τ₀) :=
    ⟨x.hk, fun h => ht₀ ((hiff (tF g₀.data)).1 h)⟩
  have hkx : ∀ c : k, algebraMap k (FFClosure X) c ∈ x.A := fun c => by
    rw [IsScalarTower.algebraMap_apply k g₀.K (FFClosure X)]
    exact x.hk _
  have hWx : N.IsNFPoint x.A :=
    ⟨coordT g₀.τ₀, (NFModel.mem_FNF_iff_numberField N _).2
      (mem_F_baseChange_of_stage g₀.toStage (GStage.F_toStage g₀ _ (tF g₀.data).2)), hxc.2⟩
  refine ⟨g₀, x, hxc, hkx, hWx, Place.ext (SetLike.ext fun (z : fnf N) => ?_)⟩
  have hz : (z : FFClosure X) ∈ F (baseChange g₀.data) := by
    have h := (mem_F_baseChange_stage_iff g₀.toStage).2
      ((NFModel.mem_FNF_iff_numberField N _).1 z.2)
    rwa [GStage.toStage_data] at h
  exact mem_iff_of_ratPoint x x.hk hk₀ (fun _ => Iff.rfl) (fun w => (hiff w).symm) hz

end Geom

end Iut.Reconstruction.Thm19
