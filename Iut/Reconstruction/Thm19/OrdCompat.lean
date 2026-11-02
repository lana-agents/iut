/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.MatchCusp

/-!
# `ord_x` is carried along `Φ` (MR9 item 4, step 5)

[AbsTopIII] Thm 1.9 (b), (c), (e): along an isomorphism `ψ` of the colimits
`lim→_V H¹(Π_V, Ẑ(1))` given on the geometric stages by the lift data (`ψ [g, y] =
[L.tgt, L.S y]`, as `h1LimCycloEquiv` and its inverse), the valuation of a class of
`kummerNFRange` at a point `x` of `Z_NF` is the valuation of its image at the matched point
`x''`: `x` is a rational cusp `x.A` of a stage `g₀`, `x''` the cusp `W''` of `L₀.tgt` whose inertia
group is the image of that of `x.A`.

* `GStage.exists_fnf_unit`: a unit of a geometric stage as an NF-rational function;
* `val_pow_recTriple`: `ord_x(ξ^M) = M · ord_x(ξ)`;
* **`val_eq_of_matched`**.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian IsLocalRing

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

/-- `ord_x(ξ^M) = M · ord_x(ξ)` in a triple. -/
lemma _root_.Iut.Reconstruction.Uchida.ValEvalData.val_pow (D : Uchida.ValEvalData.{u})
    (x : D.P) (a : D.G) (M : ℕ) : D.val x (a ^ M) = M * D.val x a := by
  unfold Uchida.ValEvalData.val
  rw [map_pow, toAdd_pow, nsmul_eq_mul]

section Geom

variable {k : Type u} [Field k] [CharZero k] [NumberField k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X] {τ : X.functionField}
  {hτ : Transcendental k τ} [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)]
  [IsAlgClosed (FFClosure X)]

/-- **A unit of a geometric stage as an NF-rational function**, with its Kummer class
(`ofG_kummerMapZHat`; over a number field `F_NF = F k̄`). -/
lemma GStage.exists_fnf_unit (N : NFModel (curveGaloisData k hτ)) (g : GStage k hτ)
    (v : units g.data) :
    ∃ f : (fnf N)ˣ, ((f : fnf N) : FFClosure X) =
        (((v : (F g.data)ˣ) : F g.data) : FFClosure X) ∧
      ofG g (kummerMapZHat g.data v) = kummerNF N (mem_range_of_isAlgebraic_F k hτ) f := by
  have hm : (((v : (F g.data)ˣ) : F g.data) : FFClosure X) ∈ N.FNF :=
    (NFModel.mem_FNF_iff_numberField N _).2
      (mem_F_baseChange_of_stage g.toStage (F_toStage g _ ((v : (F g.data)ˣ) : F g.data).2))
  have h0 : (⟨_, hm⟩ : fnf N) ≠ 0 := fun h =>
    (v : (F g.data)ˣ).ne_zero (Subtype.ext (congrArg Subtype.val h :))
  exact ⟨Units.mk0 ⟨_, hm⟩ h0, rfl, ofG_kummerMapZHat N g v _ rfl⟩

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
  {Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out)}
  (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))
  (hχU : CycloEquivariant (bridgeIso hτ hU hτ₂ hU₂ Φ) χU)
  (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
  (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
  (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
  (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
  (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
  (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0) (hDGC : RelIsomDGC.Exists K₂)
  (N : NFModel (curveGaloisData K hτ)) (N₂ : NFModel (curveGaloisData K₂ hτ₂))

variable [Fact (0 < (CurvesJacobian.curveGenus K₂ C₂.Xbar).toNat)]

set_option maxHeartbeats 3200000 in
-- the quotients `Π_V` and the classes at several stages unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC in
/-- **`ord_x` along `ψ`**: let `ψ` be a homomorphism of the colimits given on the geometric stages
by the chosen lift data (`ψ [g, y] = [L.tgt, L.S y]`), with `TameCompat` for all lift data. For a
rational cusp `x.A` of a stage `g₀` (an NF-point) and the cusp `W''` of `L₀.tgt` whose inertia
group is the image of that of `x.A`, `ord_{W''}(ψ ξ) = ord_{x.A}(ξ)` for every class `ξ` of
`kummerNFRange` with `ψ ξ ∈ kummerNFRange`. -/
theorem val_eq_of_matched (hS : BelyiCuspSpec Ω C hc.out)
    (hT : ∀ (g : GStage K hτ) (L : LiftData hτ hU hτ₂ hU₂ Φ g), L.TameCompat χU)
    (ψ : H1Lim (curveGaloisData K hτ) →* H1Lim (curveGaloisData K₂ hτ₂))
    (hψ : ∀ (g : GStage K hτ) (y : H1G g), ψ (ofG g y) =
      ofG (LiftData.choose Φ hS g).tgt ((LiftData.choose Φ hS g).S χU hχU y))
    {g₀ : GStage K hτ} (L₀ : LiftData hτ hU hτ₂ hU₂ Φ g₀) (x : RatPoint g₀.data)
    (hx : x.A ∈ CuspW (k := g₀.K) (t := coordT g₀.τ₀))
    (hk : ∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ x.A) (hW : N.IsNFPoint x.A)
    (W'' : ValuationSubring (FFClosure C₂.Xbar))
    (hW'' : W'' ∈ CuspW (k := L₀.tgt.K) (t := coordT L₀.υ))
    (hI : (inertiaPi g₀.data x.A).map
        (constIso L₀.e (gkIso hτ hU hτ₂ hU₂ Φ) L₀.he_gk (piToGk_surjective_curve g₀.hτ₀)
          g₀.K).toMulEquiv.toMonoidHom = inertiaPi L₀.tgt.data W'')
    (hk'' : ∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W'') (hW''N : N₂.IsNFPoint W'')
    (ξ : (recTriple N (mem_range_of_isAlgebraic_F K hτ)).G)
    (hψξ : ψ ξ.1 ∈ kummerNFRange N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)) :
    (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val (nfPlace hk'' hW''N) ⟨ψ ξ.1, hψξ⟩ =
      (recTriple N (mem_range_of_isAlgebraic_F K hτ)).val (nfPlace hk hW) ξ := by
  -- a stage `g₂ ≥ g₀` with rational cusps on which `ξ` is a Kummer class
  obtain ⟨g₁, v₁, f₁, -, hξ₁, hf₁⟩ := exists_ratStage_of_mem N ξ.2
  obtain ⟨g₂', h₀', h₁'⟩ := exists_ge_ge g₀ g₁
  obtain ⟨g₂, h₂, -, hrat⟩ := g₂'.exists_ge_ratCusps
  have H₀ : g₀ ≤ g₂ := h₀'.trans h₂
  have H₁ : g₁ ≤ g₂ := h₁'.trans h₂
  obtain ⟨v, hv⟩ : ∃ v : units g₂.data,
      v = unitsT g₁.data g₂.data (GStage.F_mono H₁) (GStage.hW_mono H₁) v₁ := ⟨_, rfl⟩
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : units g₂.data,
      f₀ = unitsT g₁.data g₂.data (GStage.F_mono H₁) (GStage.hW_mono H₁) f₁ := ⟨_, rfl⟩
  have hf₀a : ¬ IsAlgebraic ℚ (((f₀ : (F g₂.data)ˣ) : F g₂.data) : FFClosure C.Xbar) := by
    rw [hf₀, coe_unitsT]
    exact hf₁
  have hξ₂ : ofG g₂ (kummerMapZHat g₂.data v) = ξ.1 := by
    rw [hv, ← resT_kummerMapZHat]
    exact (ofG_compat g₁ g₂ H₁ _).symm.trans hξ₁
  obtain ⟨fv, hfv, hfvκ⟩ := GStage.exists_fnf_unit N g₂ v
  have hξf : ξ = kummerNFEquiv N (mem_range_of_isAlgebraic_F K hτ) fv :=
    Subtype.ext (hξ₂.symm.trans hfvκ)
  -- the image class: a power is the Kummer class of an NF-rational function `f₂`
  obtain ⟨L, hψξ'⟩ : ∃ L : LiftData hτ hU hτ₂ hU₂ Φ g₂,
      ψ ξ.1 = ofG L.tgt (L.S χU hχU (kummerMapZHat g₂.data v)) :=
    ⟨_, (congrArg ψ hξ₂.symm).trans (hψ g₂ _)⟩
  obtain ⟨M, hM, w', hw'⟩ := L.S_kummer_pow χU hχU σ₀ hσ₀ hg σ₂ hσ₂
    hg₂ hDGC hS hrat (hT g₂ L) v f₀ hf₀a
  obtain ⟨f₂, hf₂, hf₂κ⟩ := GStage.exists_fnf_unit N₂ L.tgt w'
  have hpow : (⟨ψ ξ.1, hψξ⟩ : (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).G) ^ M =
      kummerNFEquiv N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂) f₂ := by
    apply Subtype.ext
    change ψ ξ.1 ^ M = _
    rw [hψξ', ← map_pow, hw']
    exact hf₂κ
  -- `x.A` is a cusp of `g₂`, matched with a cusp `W₂''` of `L.tgt`
  have hx₂ : x.A ∈ CuspW (k := g₂.K) (t := coordT g₂.τ₀) :=
    ⟨GStage.mem_of_le_K x.hk, fun ht => hx.2 (mem_of_mem_chartRing x.A hk ht H₀.2)⟩
  obtain ⟨W₂'', hW₂'', hI₂⟩ := L.exists_map_inertiaH_constIso x.A hx₂
  -- a nontrivial inertia element at `x.A` and a uniformiser on `g₂`
  have htF : ∃ f ∈ F g₂.data, f ≠ 0 ∧ x.A.valuation f < 1 :=
    ⟨(coordT g₂.τ₀)⁻¹, inv_mem (tF g₂.data).2,
      inv_ne_zero (fun h => hx₂.2 (h ▸ x.A.zero_mem)), by
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ (lt_of_not_ge fun h =>
          hx₂.2 ((x.A.valuation_le_one_iff _).1 h))⟩
  obtain ⟨σ, hσI, hσ1⟩ := exists_inertiaH_ne_one (D := g₂.data) hx₂.1 htF
  obtain ⟨π, hπ, hπs⟩ := GStage.exists_unif_nf N g₂ hk hW hx₂.1 htF
  -- the matched inertia element on the target
  have hmem := (SetLike.ext_iff.1 hI₂ _).1 (Subgroup.mem_map_of_mem
    (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk
      (piToGk_surjective_curve g₂.hτ₀) g₂.K).toMulEquiv.toMonoidHom
    (⟨σ, hσI, rfl⟩ : ((σ : g₂.data.H) : Pi g₂.data) ∈ inertiaPi g₂.data x.A))
  obtain ⟨σ'', hσ''I, hσ''e⟩ := hmem
  -- the target is an NF-point with a uniformiser on `L.tgt`
  have hk₂'' : ∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W₂'' := fun c => by
    rw [IsScalarTower.algebraMap_apply K₂ L.tgt.K (FFClosure C₂.Xbar)]
    exact hW₂''.1 _
  have hυF : coordT L.υ ∈ N₂.FNF :=
    (NFModel.mem_FNF_iff_numberField N₂ _).2
      (mem_F_baseChange_of_stage L.tgt.toStage
        (GStage.F_toStage _ _ (tF L.tgt.data).2))
  have hW₂''N : N₂.IsNFPoint W₂'' := ⟨_, hυF, hW₂''.2⟩
  have htF'' : ∃ f ∈ F L.tgt.data, f ≠ 0 ∧ W₂''.valuation f < 1 :=
    ⟨(coordT L.υ)⁻¹, inv_mem (tF L.tgt.data).2,
      inv_ne_zero (fun h => hW₂''.2 (h ▸ W₂''.zero_mem)), by
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ (lt_of_not_ge fun h =>
          hW₂''.2 ((W₂''.valuation_le_one_iff _).1 h))⟩
  obtain ⟨π'', hπ'', hπs''⟩ :=
    GStage.exists_unif_nf N₂ L.tgt hk₂'' hW₂''N hW₂''.1 htF''
  -- `ord` along the stage isomorphism
  have key := L.val_eq_mul_of_pow χU hχU N N₂ (hT g₂ L) fv v hfv.symm
    ⟨(x.A, σ), hx₂.1, hσI⟩ hk hW hx₂.2 hσ1 π hπ hπs ⟨(W₂'', σ''), hW₂''.1, hσ''I⟩ hk₂'' hW₂''N
    hW₂''.2 hI₂ hσ''e π'' hπ'' hπs'' M w' hw' f₂ hf₂.symm
  -- the matched places agree on `F k̄₂`
  have hP : nfPlace hk₂'' hW₂''N = nfPlace hk'' hW''N :=
    Place.ext (SetLike.ext fun (y : fnf N₂) =>
      LiftData.mem_iff_of_le σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC H₀ L₀ L x hx W''
        W₂'' hW'' hW₂''.1 hI hI₂ ((NFModel.mem_FNF_iff_numberField N₂ _).1 y.2))
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have e2 : (M : ℤ) * (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val
      (nfPlace hk₂'' hW₂''N) ⟨ψ ξ.1, hψξ⟩ =
      M * (recTriple N (mem_range_of_isAlgebraic_F K hτ)).val (nfPlace hk hW) ξ :=
    (Uchida.ValEvalData.val_pow _ _ _ M).symm.trans
      ((congrArg ((recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val
        (nfPlace hk₂'' hW₂''N)) hpow).trans (key.trans
          (congrArg (fun z => (M : ℤ) * (recTriple N (mem_range_of_isAlgebraic_F K hτ)).val
            (nfPlace hk hW) z) hξf.symm)))
  exact (congrArg (fun P => (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val P
    ⟨ψ ξ.1, hψξ⟩) hP).symm.trans (mul_left_cancel₀ hM0 e2)

end Lift

end Iut.Reconstruction
