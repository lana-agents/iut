/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.KummerRangeIso
import Iut.Reconstruction.Thm19.RecOrd

/-!
# `ord_x` along the stage isomorphisms (MR9 item 4, step 5)

[AbsTopIII] Thm 1.9 (b), (c), (e) (`Topics in Absolute Anabelian Geometry III.txt` l.2109–2185):
`ord_x` of an NF-rational function is read off from the residue of its Kummer class at the inertia
group of `x` (a cusp of a stage on which `x` has been removed), in units of the tame generator.
Here this is carried along the stage isomorphisms `LiftData.S`:

* `res_kummerMapZHat_eq_tameGen_zpow_of_data`: `res_kummerMapZHat_eq_tameGen_zpow` for a Galois
  model equal to that of a stage (for the geometric stages, `toStage_data`);
* `GStage.exists_inertiaIndex`, **`GStage.exists_unif_nf`**: a nontrivial inertia element, and a
  uniformiser of `Z_NF` in the function field of a geometric stage at a place nontrivial on it;
* **`LiftData.val_eq_mul_of_pow`**: for matched cusps `W` of `g` and `W''` of `L.tgt` (inertia
  groups and inertia elements matched by `constIso L.e`, `L.TameCompat χU`), if
  `(L.S κ(v))^M = κ(w')` with `v = f` and `w' = f₂` as NF-rational functions, then
  `ord_{x''}(f₂) = M · ord_x(f)`.
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
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [CharZero Ω] [Fact (D.H ≤ D.HL)] [NumberField k] (N : NFModel D)
  (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))

attribute [local instance] isAlgClosed_algebraicClosure isFunctionField_fnf
  CurvesJacobian.isFunctionField_F

/-- `res_kummerMapZHat_eq_tameGen_zpow` for a Galois model `D'` equal to that of the stage `s`. -/
theorem res_kummerMapZHat_eq_tameGen_zpow_of_data (f : (fnf N)ˣ) (s : StageIdx D)
    {D' : Pi1.Orbifold.GaloisData s.K s.t'} (hD : s.data = D') (v : units D')
    (hv : (((v : (F D')ˣ) : F D') : Ω) = ((f : fnf N) : Ω)) (p : InertiaIndex D')
    (hk : ∀ c : k, algebraMap k Ω c ∈ p.1.1) (hW : N.IsNFPoint p.1.1) (π : fnf N)
    (hπ : (nfPlace hk hW).ord π = 1) (hπs : (π : Ω) ∈ F D') :
    res D' (kummerMapZHat D' v) p =
      tameGen p ^ (recTriple N hkF).val (nfPlace hk hW) (kummerNFEquiv N hkF f) := by
  subst hD
  exact res_kummerMapZHat_eq_tameGen_zpow N hkF f hk hW s v hv p rfl π hπ hπs

/-- `idxVal_ne_top_of_uniformiser` for a Galois model `D'` equal to that of the stage `s`. -/
lemma idxVal_ne_top_of_data (s : StageIdx D) {D' : Pi1.Orbifold.GaloisData s.K s.t'}
    (hD : s.data = D') (p : InertiaIndex D') (hk : ∀ c : k, algebraMap k Ω c ∈ p.1.1)
    (hW : N.IsNFPoint p.1.1) (π : fnf N) (hπ : (nfPlace hk hW).ord π = 1)
    (hπs : (π : Ω) ∈ F D') : idxVal p ≠ ⊤ := by
  subst hD
  exact idxVal_ne_top_of_uniformiser N hk hW s p rfl π hπ hπs

end Generic

section Geom

variable {k : Type u} [Field k] [CharZero k] [NumberField k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsIntegral X] [IsFunctionField k X.functionField] {τ : X.functionField}
  {hτ : Transcendental k τ} [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)]
  [IsAlgClosed (FFClosure X)]

attribute [local instance] isAlgClosed_algebraicClosure isFunctionField_fnf
  CurvesJacobian.isFunctionField_F

/-- **A nontrivial inertia element at a place of a geometric stage** (`exists_inertiaH_ne_one`). -/
lemma GStage.exists_inertiaIndex (g : GStage k hτ) {W : ValuationSubring (FFClosure X)}
    (hkW : ∀ c : g.K, algebraMap g.K (FFClosure X) c ∈ W)
    (hne : ∃ f ∈ F g.data, f ≠ 0 ∧ W.valuation f < 1) :
    ∃ p : InertiaIndex g.data, p.1.1 = W ∧ p.1.2 ≠ 1 :=
  (exists_inertiaH_ne_one (D := g.data) hkW hne).elim fun σ hσ =>
    ⟨⟨(W, σ), hkW, hσ.1⟩, rfl, hσ.2⟩

set_option maxHeartbeats 800000 in
-- the function fields of the stage and of `F k̄` unify slowly
/-- **A uniformiser of `Z_NF` on a geometric stage**: at a place `W ⊇ K₁` nontrivial on the
function field of the stage `g`, a uniformiser of `W ∩ F_g` is one of `Z_NF = F k̄` at the
NF-point `W` (the extension `F_g ⊆ F k̄` of the field of constants is unramified,
`isUnif_baseChange`; `F k̄` of the stage is that of `U`, `mem_F_baseChange_stage_iff`). -/
theorem GStage.exists_unif_nf (N : NFModel (curveGaloisData k hτ)) (g : GStage k hτ)
    {W : ValuationSubring (FFClosure X)} (hk : ∀ c : k, algebraMap k (FFClosure X) c ∈ W)
    (hW : N.IsNFPoint W) (hkW : ∀ c : g.K, algebraMap g.K (FFClosure X) c ∈ W)
    (hne : ∃ f ∈ F g.data, f ≠ 0 ∧ W.valuation f < 1) :
    ∃ π : fnf N, (nfPlace hk hW).ord π = 1 ∧ (π : FFClosure X) ∈ F g.data := by
  obtain ⟨f, hf, hf0, hfW⟩ := hne
  let P : Place g.K (F g.data) := ⟨W.comap (algebraMap (F g.data) (FFClosure X)), fun htop => by
      have h : (⟨f, hf⟩ : F g.data)⁻¹ ∈ W.comap (algebraMap (F g.data) (FFClosure X)) :=
        htop ▸ ValuationSubring.mem_top _
      change (((⟨f, hf⟩ : F g.data)⁻¹ : F g.data) : FFClosure X) ∈ W at h
      rw [IntermediateField.coe_inv] at h
      exact inv_notMem_of_valuation_lt_one hf0 hfW h, fun c => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact hkW c⟩
  obtain ⟨ϖ, -, hϖW, hϖ⟩ :=
    CurvesJacobian.ChernClass.exists_uniformiser (P := P) (W := W) fun _ => Iff.rfl
  have hbc := isUnif_baseChange (D := g.data) hkW hϖW hϖ
  have hϖF : ((ϖ : F g.data) : FFClosure X) ∈ F (baseChange (curveGaloisData k hτ)) :=
    mem_F_baseChange_of_stage g.toStage (F_toStage g _ (ϖ : F g.data).2)
  let π : fnf N := ⟨_, (NFModel.mem_FNF_iff_numberField N _).2 hϖF⟩
  refine ⟨π, ?_, (ϖ : F g.data).2⟩
  obtain ⟨π₀, hπ₀⟩ := (nfPlace hk hW).exists_ord_eq_one
  have hπ₀0 : π₀ ≠ 0 := fun h => by
    rw [h, (nfPlace hk hW).ord_zero] at hπ₀; exact zero_ne_one hπ₀
  have hπ0 : π ≠ 0 := fun h => ϖ.ne_zero (Subtype.ext (congrArg Subtype.val h :))
  have hπ₀W : W.valuation (π₀ : FFClosure X) < 1 :=
    valuation_lt_one_of_ord_eq_one (nfPlace hk hW) (algebraMap (fnf N) (FFClosure X)) rfl hπ₀
  have hπ₀bc : (π₀ : FFClosure X) ∈ F (baseChange g.data) := by
    have h := (mem_F_baseChange_stage_iff g.toStage).2
      ((NFModel.mem_FNF_iff_numberField N _).1 π₀.2)
    rwa [GStage.toStage_data] at h
  have h₁ : W.valuation (π₀ : FFClosure X) ≤ W.valuation (π : FFClosure X) :=
    hbc _ hπ₀bc hπ₀W
  have h₂ : W.valuation (π : FFClosure X) ≤ W.valuation (π₀ : FFClosure X) :=
    valuation_le_of_ord_eq_one (nfPlace hk hW) (algebraMap (fnf N) (FFClosure X)) rfl hπ₀ π hϖW
  exact ((ord_eq_ord_iff_val (nfPlace hk hW) (algebraMap (fnf N) (FFClosure X)) rfl hπ0
    hπ₀0).2 (le_antisymm h₂ h₁)).trans hπ₀

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
  Thm19.isAlgClosed_algebraicClosure Thm19.isFunctionField_fnf

variable {τ : C.Xbar.functionField} {hτ : Transcendental K τ}
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] {hU : C.U = chartOne K C.Xbar τ}
  {τ₂ : C₂.Xbar.functionField} {hτ₂ : Transcendental K₂ τ₂}
  [IsGalois (K₀ K₂ (coordT τ₂)) (FFClosure C₂.Xbar)] {hU₂ : C₂.U = chartOne K₂ C₂.Xbar τ₂}
  {Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out)} {g : GStage K hτ}
  (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))
  (hχU : CycloEquivariant (bridgeIso hτ hU hτ₂ hU₂ Φ) χU)
  (N : NFModel (curveGaloisData K hτ)) (N₂ : NFModel (curveGaloisData K₂ hτ₂))

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` and the coefficients of two stages unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- **`ord_x` along the stage isomorphism**: for a cusp `W = p.1.1` of `g` and a cusp
`W'' = p''.1.1` of `L.tgt` whose inertia groups and inertia elements are matched by
`constIso L.e`, with uniformisers of `Z_NF` and `Z'_NF` on the stages, if
`(L.S κ(v))^M = κ(w')` with `v = f`, `w' = f₂` as NF-rational functions, then
`ord_{x''}(f₂) = M · ord_x(f)` (residues: `res_h1Congr_of_eq`, tame generators: `TameCompat`). -/
theorem LiftData.val_eq_mul_of_pow (L : LiftData hτ hU hτ₂ hU₂ Φ g) (hT : L.TameCompat χU)
    (f : (fnf N)ˣ) (v : units g.data)
    (hv : (((v : (F g.data)ˣ) : F g.data) : FFClosure C.Xbar) = ((f : fnf N) : FFClosure C.Xbar))
    (p : InertiaIndex g.data) (hk : ∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ p.1.1)
    (hW : N.IsNFPoint p.1.1) (hpc : coordT g.τ₀ ∉ p.1.1) (hσ : p.1.2 ≠ 1)
    (π : fnf N) (hπ : (nfPlace hk hW).ord π = 1) (hπs : (π : FFClosure C.Xbar) ∈ F g.data)
    (p'' : InertiaIndex L.tgt.data) (hk'' : ∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ p''.1.1)
    (hW'' : N₂.IsNFPoint p''.1.1) (hpc'' : coordT L.υ ∉ p''.1.1)
    (hI : ((inertiaH g.data p.1.1).map (QuotientGroup.mk' (GaloisPi1.kernel g.data.H g.data.S))).map
        (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
          g.K).toMulEquiv.toMonoidHom =
      (inertiaH L.tgt.data p''.1.1).map
        (QuotientGroup.mk' (GaloisPi1.kernel L.tgt.data.H L.tgt.data.S)))
    (hel : ((p''.1.2 : L.tgt.data.H) : Pi L.tgt.data) =
      constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K
        ((p.1.2 : g.data.H) : Pi g.data))
    (π'' : fnf N₂) (hπ'' : (nfPlace hk'' hW'').ord π'' = 1)
    (hπs'' : (π'' : FFClosure C₂.Xbar) ∈ F L.tgt.data)
    (M : ℕ) (w' : units L.tgt.data)
    (hw' : L.S χU hχU (kummerMapZHat g.data v) ^ M = kummerMapZHat L.tgt.data w')
    (f₂ : (fnf N₂)ˣ)
    (hf₂ : (((w' : (F L.tgt.data)ˣ) : F L.tgt.data) : FFClosure C₂.Xbar) =
      ((f₂ : fnf N₂) : FFClosure C₂.Xbar)) :
    (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val (nfPlace hk'' hW'')
        (kummerNFEquiv N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂) f₂) =
      M * (recTriple N (mem_range_of_isAlgebraic_F K hτ)).val (nfPlace hk hW)
        (kummerNFEquiv N (mem_range_of_isAlgebraic_F K hτ) f) := by
  -- the source residue
  have h1 := res_kummerMapZHat_eq_tameGen_zpow_of_data N (mem_range_of_isAlgebraic_F K hτ) f
    g.toStage (GStage.toStage_data g) v hv p hk hW π hπ hπs
  -- the target residue
  have h2 := res_kummerMapZHat_eq_tameGen_zpow_of_data N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂) f₂
    L.tgt.toStage (GStage.toStage_data L.tgt) w' hf₂ p'' hk'' hW'' π'' hπ'' hπs''
  -- the residue of `L.S κ(v)`
  have h3 : res L.tgt.data (L.S χU hχU (kummerMapZHat g.data v)) p'' =
      constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K
        (res g.data (kummerMapZHat g.data v) p) :=
    (congrArg (fun η => res L.tgt.data η p'') (L.S_apply χU hχU _)).trans
      (res_h1Congr_of_eq _ _ _ p p'' hel _)
  have hθ := hT p p'' hpc hpc'' hI hel
  have hne : tameGen p'' ≠ 1 := fun h0 =>
    tameGen_ne_one p (idxVal_ne_top_of_data N g.toStage (GStage.toStage_data g) p hk hW π hπ hπs)
      hσ ((constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K).injective
        ((hθ.trans h0).trans (map_one _).symm))
  have h4 : res L.tgt.data (kummerMapZHat L.tgt.data w') p'' =
      res L.tgt.data (L.S χU hχU (kummerMapZHat g.data v)) p'' ^ M :=
    (congrArg (fun η => res L.tgt.data η p'') hw'.symm).trans
      (congrFun (map_pow (res L.tgt.data) _ M) p'')
  have h5 : (tameGen p'' ^ (recTriple N (mem_range_of_isAlgebraic_F K hτ)).val (nfPlace hk hW)
      (kummerNFEquiv N (mem_range_of_isAlgebraic_F K hτ) f)) ^ M =
      tameGen p'' ^ ((M : ℤ) * (recTriple N (mem_range_of_isAlgebraic_F K hτ)).val
        (nfPlace hk hW) (kummerNFEquiv N (mem_range_of_isAlgebraic_F K hτ) f)) := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  refine zHatOne_zpow_injective hne (h2.symm.trans (h4.trans ((congrArg (· ^ M) h3).trans
    ((congrArg (fun z => (constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K z) ^ M)
      h1).trans ((congrArg (· ^ M) ((map_zpow _ _ _).trans (congrArg (· ^ _) hθ))).trans h5)))))

end Lift

end Iut.Reconstruction
