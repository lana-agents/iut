/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.OrdCompat
import Iut.Reconstruction.Thm19.CuspEval
import Iut.Reconstruction.Thm19.TripleIso

/-!
# `U_x` is carried along `Φ` (MR9 item 4, step 5)

[AbsTopIII] Thm 1.9 (a), (e): along an isomorphism `ψ` of the colimits given on the geometric
stages by the lift data (`ψ [g, y] = [L.tgt, L.S y]`, as `h1LimCycloEquiv` and its inverse), a
class of `kummerNFRange` in `U_x` is mapped into `U_{x''}` at the matched point `x''`. Every point
`x` of `Z_NF` is a rational cusp `x.A` of a geometric stage (`exists_ratCusp_nfPlace`), so the
cuspidal decomposition groups suffice (points of `U` and cusps of `U` alike):

* on the source, `f(x) = 1` gives `DecompTriv` of the Kummer class at `D_x` (`decompTriv_kummer`);
* the stage isomorphism maps `D_x` onto `D_{x''}` (`LiftData.map_decompH_constIso`), so
  `DecompTriv` holds for `L.S κ(v)` at `D_{x''}` (`decompTriv_h1Congr_iff`);
* on the target, `L.S κ(v) = κ(u) · c` with a class of constants `c`
  (`exists_eq_kummerMapZHat_mul_constMapZHat`, `L.S κ(v) ∈ P_{V'}`, a power is a Kummer class);
  `u` is a unit at `x''` (`ord_{x''} = 0` by `val_eq_of_matched`), and `x''` is rational
  (`LiftData.cuspPoint`), so `exists_kummer_of_decompTriv` gives `L.S κ(v) = κ(u a)` with
  `(u a)(x'') = 1`.

Results: `GStage.ratPointOfCusp` (a cusp of a stage with rational cusps is a rational point
there, `ratPointOfComap`), `valuation_eq_one_of_val_eq_zero`, **`mem_U_of_matched`**.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian IsLocalRing

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

attribute [local instance] isAlgClosed_algebraicClosure isFunctionField_fnf

section Geom

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X] {τ : X.functionField}
  {hτ : Transcendental k τ} [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)]
  [IsAlgClosed (FFClosure X)]

/-- **A cusp of a stage whose cusps are rational, as a rational point** of that stage (with the
same place of `Ω`, `ratPointOfCusp_A`; `ratPointOfComap`). -/
def GStage.ratPointOfCusp (g : GStage k hτ)
    (hrat : ∀ P : Place g.K (F g.data), IsCuspPlaceF P → ∃ x : RatPoint g.data, placeOfF x = P)
    {A : ValuationSubring (FFClosure X)} (hA : A ∈ CuspW (k := g.K) (t := coordT g.τ₀)) :
    RatPoint g.data :=
  let P : Place g.K (F g.data) := ⟨A.comap (algebraMap (F g.data) (FFClosure X)), fun htop => hA.2
    (by
      have h : tF g.data ∈ A.comap (algebraMap (F g.data) (FFClosure X)) :=
        htop ▸ ValuationSubring.mem_top _
      exact h), fun c => by
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hA.1 c⟩
  ratPointOfComap g.data (hrat P hA.2).choose A hA.1
    (isIntegral_residueField_of_ne (D := g.data) A hA.1 ⟨tF g.data, hA.2⟩) fun y => by
      rw [← mem_placeOfF, (hrat P hA.2).choose_spec]
      rfl

lemma GStage.ratPointOfCusp_A (g : GStage k hτ)
    (hrat : ∀ P : Place g.K (F g.data), IsCuspPlaceF P → ∃ x : RatPoint g.data, placeOfF x = P)
    {A : ValuationSubring (FFClosure X)} (hA : A ∈ CuspW (k := g.K) (t := coordT g.τ₀)) :
    (g.ratPointOfCusp hrat hA).A = A := rfl

variable {N : NFModel (curveGaloisData k hτ)}

/-- **`ord_x f = 0` gives `|f|_W = 1`** at an NF-point `W` over `x`. -/
lemma valuation_eq_one_of_ord_eq_zero {W : ValuationSubring (FFClosure X)}
    (hk : ∀ c : k, algebraMap k (FFClosure X) c ∈ W) (hW : N.IsNFPoint W) (f : (fnf N)ˣ)
    (h : (nfPlace hk hW).ord (f : fnf N) = 0) :
    W.valuation ((f : fnf N) : FFClosure X) = 1 := by
  have e := (ord_eq_ord_iff_val (nfPlace hk hW) (algebraMap (fnf N) (FFClosure X)) rfl
    f.ne_zero one_ne_zero).1 (by rw [h, Place.ord_one])
  rw [map_one, map_one] at e
  exact e

/-- `|y - 1|_V < 1` makes `y` a unit of `V`. -/
lemma mem_and_inv_mem_of_valuation_sub_one {Ω : Type*} [Field Ω] {V : ValuationSubring Ω} {y : Ω}
    (h : V.valuation (y - 1) < 1) : y ∈ V ∧ y⁻¹ ∈ V := by
  have h1 : V.valuation y = 1 := by
    have := Valuation.map_eq_of_sub_lt V.valuation (y := y) (x := 1) (by rwa [map_one])
    rwa [map_one] at this
  exact ⟨(V.valuation_le_one_iff y).1 h1.le,
    (V.valuation_le_one_iff _).1 (by rw [map_inv₀, h1, inv_one])⟩

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

/-- The subgroup `S.map (conj 1) = S`. -/
lemma map_conj_one {G : Type*} [Group G] (S : Subgroup G) :
    S.map (MulAut.conj (1 : G)).toMonoidHom = S := by
  rw [map_one]
  exact Subgroup.map_id S

set_option maxHeartbeats 3200000 in
-- the quotients `Π_V`, the classes at several stages and the restrictions unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC in
/-- **`U_x` along `ψ`**: in the situation of `val_eq_of_matched` (`ψ [g, y] = [L.tgt, L.S y]`,
`TameCompat` for all lift data, `x.A` a rational cusp of `g₀`, `W''` the matched cusp of
`L₀.tgt`), every class `ξ ∈ U_{x.A}` of `kummerNFRange` with `ψ ξ ∈ kummerNFRange` has
`ψ ξ ∈ U_{W''}`. -/
theorem mem_U_of_matched (hS : BelyiCuspSpec Ω C hc.out)
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
    (hψξ : ψ ξ.1 ∈ kummerNFRange N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂))
    (hξU : ξ ∈ (recTriple N (mem_range_of_isAlgebraic_F K hτ)).U (nfPlace hk hW)) :
    (⟨ψ ξ.1, hψξ⟩ : (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).G) ∈
      (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).U (nfPlace hk'' hW''N) := by
  -- `ord_{W''}(ψ ξ) = 0`
  have hval : (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val (nfPlace hk'' hW''N)
      ⟨ψ ξ.1, hψξ⟩ = 0 :=
    (val_eq_of_matched χU hχU σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC N N₂ hS hT ψ hψ L₀ x hx hk hW W'' hW''
      hI hk'' hW''N ξ hψξ).trans
      (recTriple_uInKer N (mem_range_of_isAlgebraic_F K hτ) _ ξ hξU)
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
  -- the image class
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
  -- `x.A` is a rational cusp of `g₂`, matched with a cusp `W₂''` of `L.tgt`
  have hx₂ : x.A ∈ CuspW (k := g₂.K) (t := coordT g₂.τ₀) :=
    ⟨GStage.mem_of_le_K x.hk, fun ht => hx.2 (mem_of_mem_chartRing x.A hk ht H₀.2)⟩
  obtain ⟨W₂'', hW₂'', hI₂⟩ := L.exists_map_inertiaH_constIso x.A hx₂
  have hD := L.map_decompH_constIso x.A hx₂ W₂'' hW₂'' hI₂
  obtain ⟨x'', hx''A⟩ : ∃ x'' : RatPoint L.tgt.data, x''.A = W₂'' :=
    ⟨L.cuspPoint (g₂.ratPointOfCusp hrat hx₂) W₂'' hW₂'' hD, rfl⟩
  subst hx''A
  have hk₂'' : ∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ x''.A := fun c => by
    rw [IsScalarTower.algebraMap_apply K₂ L.tgt.K (FFClosure C₂.Xbar)]
    exact hW₂''.1 _
  have hυF : coordT L.υ ∈ N₂.FNF :=
    (NFModel.mem_FNF_iff_numberField N₂ _).2
      (mem_F_baseChange_of_stage L.tgt.toStage
        (GStage.F_toStage _ _ (tF L.tgt.data).2))
  have hW₂''N : N₂.IsNFPoint x''.A := ⟨_, hυF, hW₂''.2⟩
  -- the matched places agree on `F k̄₂`
  have hP : nfPlace hk₂'' hW₂''N = nfPlace hk'' hW''N :=
    Place.ext (SetLike.ext fun (y : fnf N₂) =>
      LiftData.mem_iff_of_le σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC H₀ L₀ L x hx W''
        x''.A hW'' hW₂''.1 hI hI₂ ((NFModel.mem_FNF_iff_numberField N₂ _).1 y.2))
  -- the source: `v(x) = 1`, so `κ(v)` restricts trivially to `D_x`
  have hfvU : fv ∈ (nfTriple N).U (nfPlace hk hW) :=
    ((recIso N (mem_range_of_isAlgebraic_F K hτ)).mem_U_iff (nfPlace hk hW) fv).1 (hξf ▸ hξU)
  have hv1 : x.A.valuation ((((v : (F g₂.data)ˣ) : F g₂.data) : FFClosure C.Xbar) - 1) < 1 := by
    have := (mem_U_nfTriple_iff hk hW fv).1 hfvU
    rwa [hfv] at this
  obtain ⟨hvA, hvA'⟩ := mem_and_inv_mem_of_valuation_sub_one hv1
  have hvA'' : ((((v : (F g₂.data)ˣ)⁻¹ : (F g₂.data)ˣ) : F g₂.data) : FFClosure C.Xbar) ∈ x.A := by
    rw [coe_units_inv]
    exact hvA'
  letI : Algebra g₂.K (ResidueField x.A) := resAlg x.A hx₂.1
  haveI : Algebra.IsIntegral g₂.K (ResidueField x.A) := (g₂.ratPointOfCusp hrat hx₂).isIntegral
  have hsrc := decompTriv_kummer g₂.data x.A hx₂.1 (fun _ => rfl) v hvA hvA'' hv1
  -- along the stage isomorphism
  have hdec : (decompToPi g₂.data x.A).range.map
      (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g₂.hτ₀)
        g₂.K).toMulEquiv.toMonoidHom =
      (decompToPi L.tgt.data x''.A).range.map (MulAut.conj 1).toMonoidHom := by
    rw [map_conj_one, range_decompToPi_eq_map_decompH', range_decompToPi_eq_map_decompH']
    exact hD
  have htgt : DecompTriv L.tgt.data x''.A x''.hk x''.hkres
      (L.S χU hχU (kummerMapZHat g₂.data v)) :=
    (decompTriv_h1Congr_iff x.A hx₂.1 (fun _ => rfl) x''.A x''.hk x''.hkres
      (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g₂.hτ₀) g₂.K)
      (constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g₂.hτ₀ L.hυ) g₂.K)
      (constCyclo_smul L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g₂.hτ₀)
        (cycloVχ χU g₂.hτ₀ L.hυ) (cycloVχ_smul χU _ hχU g₂.hτ₀ L.hυ L.he) g₂.K) 1 hdec
      (kummerMapZHat g₂.data v)).1 hsrc
  -- the target: `L.S κ(v) = κ(u) · c`
  have hPU := L.S_mem_PU χU hχU σ₀ hσ₀ σ₂ hσ₂ hrat (hT g₂ L) (kummerMapZHat g₂.data v) ⟨v, rfl⟩
  obtain ⟨u, c, b, hyc, -, hw'u⟩ := exists_eq_kummerMapZHat_mul_constMapZHat
    (L.tgt.isKummerFaithfulJac σ₂ hσ₂) L.tgt.hkF hPU hw'
  -- `u` is a unit at `x''`
  have h1 : (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val (nfPlace hk₂'' hW₂''N)
      (kummerNFEquiv N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂) f₂) = 0 := by
    have hval₂ : (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val
        (nfPlace hk₂'' hW₂''N) ⟨ψ ξ.1, hψξ⟩ = 0 := hP ▸ hval
    exact (congrArg ((recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val
      (nfPlace hk₂'' hW₂''N)) hpow).symm.trans
        ((Uchida.ValEvalData.val_pow _ _ _ M).trans (by rw [hval₂, mul_zero]))
  have h2 : (nfPlace hk₂'' hW₂''N).ord (f₂ : fnf N₂) = 0 :=
    ((recIso N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val_eq _ f₂).symm.trans h1
  have h3 := valuation_eq_one_of_ord_eq_zero hk₂'' hW₂''N f₂ h2
  have hb1 : x''.A.valuation (algebraMap L.tgt.K (FFClosure C₂.Xbar) (b : L.tgt.K)) = 1 := by
    refine le_antisymm ((x''.A.valuation_le_one_iff _).2 (x''.hk _)) ?_
    have hb' := (x''.A.valuation_le_one_iff _).2 (x''.hk ((b⁻¹ : L.tgt.Kˣ) : L.tgt.K))
    rw [Units.val_inv_eq_inv_val, map_inv₀, map_inv₀] at hb'
    have hne : x''.A.valuation (algebraMap L.tgt.K (FFClosure C₂.Xbar) (b : L.tgt.K)) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero _).2 b.ne_zero)
    exact (inv_le_one₀ (zero_lt_iff.2 hne)).1 hb'
  have hu1 :
      x''.A.valuation ((((u : (F L.tgt.data)ˣ) : F L.tgt.data) : FFClosure C₂.Xbar)) = 1 := by
    have e : ((((w' : (F L.tgt.data)ˣ) : F L.tgt.data) : FFClosure C₂.Xbar)) =
        ((((u : (F L.tgt.data)ˣ) : F L.tgt.data) : FFClosure C₂.Xbar)) ^ M *
          algebraMap L.tgt.K (FFClosure C₂.Xbar) (b : L.tgt.K) := by
      rw [hw'u, coe_mul_constUnit]
      congr 1
    rw [hf₂, e, map_mul, hb1, mul_one, map_pow] at h3
    exact (pow_eq_one_iff.1 h3).resolve_right hM.ne'
  have huA : ((((u : (F L.tgt.data)ˣ) : F L.tgt.data) : FFClosure C₂.Xbar)) ∈ x''.A :=
    (x''.A.valuation_le_one_iff _).1 hu1.le
  have huA' : ((((u : (F L.tgt.data)ˣ)⁻¹ : (F L.tgt.data)ˣ) : F L.tgt.data) : FFClosure C₂.Xbar) ∈
      x''.A := by
    rw [coe_units_inv]
    exact (x''.A.valuation_le_one_iff _).1 (by rw [map_inv₀, hu1, inv_one])
  -- `c = κ(a)` and `(u a)(x'') = 1`
  have htgt' := htgt
  rw [hyc] at htgt'
  obtain ⟨a, hya, hva⟩ := exists_kummer_of_decompTriv L.tgt.data x'' u huA huA' c htgt'
  obtain ⟨f', hf', hf'κ⟩ := GStage.exists_fnf_unit N₂ L.tgt (u * constUnit L.tgt.data a)
  have hψf : (⟨ψ ξ.1, hψξ⟩ : (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).G) =
      kummerNFEquiv N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂) f' :=
    Subtype.ext (hψξ'.trans ((congrArg (ofG L.tgt) (hyc.trans hya)).trans hf'κ))
  have hfin : (⟨ψ ξ.1, hψξ⟩ : (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).G) ∈
      (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).U (nfPlace hk₂'' hW₂''N) := by
    rw [hψf]
    exact ((recIso N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).mem_U_iff _ f').2
      ((mem_U_nfTriple_iff hk₂'' hW₂''N f').2 (hf' ▸ hva))
  exact hP ▸ hfin

end Lift

end Iut.Reconstruction
