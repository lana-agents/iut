/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.RecRange
import Iut.Reconstruction.Thm19.NFCanon
import Iut.Reconstruction.Thm19.RatCusps
import Iut.Reconstruction.Thm19.GeomLim

/-!
# `K^×_{Z_NF}` on the geometric stages (MR9 item 4, step 4, pieces A and B)

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178) embeds
`K^×_{Z_NF}` into `lim→_V H¹(Π_V, μ_Ẑ(Π_U))` (`kummerNFRange`, `Thm19/RecFunctionField.lean`).
For the functoriality of this image along `Φ` the classes are read at geometric stages
(`Thm19/GeomLim.lean`), on which `h1LimEquiv` is computed (`h1LimEquiv_ofG`):

* `mk_mem_kummerNFRange_of_pow` (generic, over a number field): if `η ∈ P_V` and some positive
  power `η^M` is the Kummer class `κ_V(w)` of a unit of the stage `V`, then `[V, η]` lies in
  `kummerNFRange` (the root `v` of `w` over `V′ = V_{K(b^{1/M})}`, `exists_resKH1_eq_kummerMapZHat`;
  over a number field every function of `F k̄` is NF-rational, `NFModel.mem_FNF_iff_numberField`);
* `resT_mem_PU_of_eq`: `P_V` is carried along the transition between equal Galois models;
* **`ofG_mem_kummerNFRange`** (piece A): the same at a geometric stage `g`, for `y ∈ P_{V_g}`;
* `ofG_kummerMapZHat`: `ofG g (κ(v)) = [V, κ(v)]` is the Kummer class of the value of `v`;
* **`exists_ratStage_of_mem`** (piece B): every class of `kummerNFRange` is `ofG g (κ(v))` at a
  geometric stage `g` whose cusps are rational (`GStage.exists_ge_ratCusps`) and which carries a
  unit `f₀` that is not an algebraic number.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer IsLocalRing

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

open CurvesJacobian StageIdx

set_option linter.unusedSectionVars false

attribute [local instance] isAlgClosed_algebraicClosure isFunctionField_fnf
  CurvesJacobian.isFunctionField_F

section Rec

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [CharZero Ω] [hH : Fact (D.H ≤ D.HL)] [NumberField k] (N : NFModel D)
  (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))

set_option maxHeartbeats 4000000 in
-- `ContH1` and unit terms over the stages unify slowly
/-- **A class of `P_V` with a Kummer class as positive power lies in `kummerNFRange`** (over a
number field): if `η ∈ P_V` and `η^M = κ_V(w)` with `M > 0`, then `[V, η] = [V′, κ(v)]` at the
stage `V′` over `K(b^{1/M})` with `v^M = w` (`exists_resKH1_eq_kummerMapZHat`), and `v` is an
NF-rational function (`NFModel.mem_FNF_iff_numberField`). -/
theorem mk_mem_kummerNFRange_of_pow (s : StageIdx D) (hJ : IsKummerFaithfulJac s.data)
    {η : H1S D s} (hη : η ∈ PU s.data) {M : ℕ} (hM : 0 < M) {w : US D s}
    (hw : η ^ M = kummerMapZHat s.data w) :
    H1Lim.mk s η ∈ kummerNFRange N hkF := by
  haveI : NumberField s.K := NumberField.of_module_finite k s.K
  have hkFs := mem_range_of_isAlgebraic_stage (D := D) (K := s.K) (ht' := s.ht')
    (htr' := s.htr') hH.out hkF
  obtain ⟨u, b, -, hb⟩ := exists_resKH1_eq_kummerMapZHat hJ hkFs hη hM hw
  -- an `M`-th root `β₀` of `b`, and the stage `V′` over `K′ = K(β₀)`
  obtain ⟨β₀, hβ₀⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap s.K Ω b) hM
  have hβint : IsIntegral k β₀ := by
    have h1 : IsIntegral k (algebraMap s.K Ω b) := by
      have := (Algebra.IsIntegral.isIntegral (R := k) (b : s.K))
      exact this.map (IsScalarTower.toAlgHom k s.K Ω)
    exact IsIntegral.of_pow hM (hβ₀ ▸ h1)
  haveI : FiniteDimensional k (IntermediateField.adjoin k {β₀}) :=
    IntermediateField.adjoin.finiteDimensional hβint
  set K' : IntermediateField k Ω := s.K ⊔ IntermediateField.adjoin k {β₀} with hK'
  have hK : s.K ≤ K' := le_sup_left
  have hβK' : β₀ ∈ K' :=
    (show IntermediateField.adjoin k {β₀} ≤ K' from le_sup_right)
      (IntermediateField.mem_adjoin_simple_self k β₀)
  have hβ0 : β₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hβ₀
    exact b.ne_zero ((algebraMap s.K Ω).injective (by rw [← hβ₀, map_zero]))
  let β : (extK s K' hK)ˣ := Units.mk0 ⟨β₀, hβK'⟩ (fun h => hβ0 (congrArg Subtype.val h))
  have hβ : β ^ M = Units.map (algebraMap s.K (extK s K' hK) : s.K →* extK s K' hK) b := by
    apply Units.ext
    apply Subtype.ext
    change β₀ ^ M = algebraMap s.K Ω b
    exact hβ₀
  obtain ⟨v, hv, -⟩ := hb (extK s K' hK) β hβ
  set s' := s.extend K' hK with hs'def
  set v' : US D s' := unitsT (constExt (extK s K' hK) s.data) s'.data
    (fun _ hx => F_extK_le s K' hK hx) (hW_extK s K' hK) v with hv'def
  have hv'0 : (((v' : (F s'.data)ˣ) : F s'.data) : Ω) ≠ 0 := fun h =>
    (v' : (F s'.data)ˣ).ne_zero (Subtype.ext h)
  have hv'NF : (((v' : (F s'.data)ˣ) : F s'.data) : Ω) ∈ N.FNF :=
    (NFModel.mem_FNF_iff_numberField N _).2
      (mem_F_baseChange_of_stage s' ((v' : (F s'.data)ˣ) : F s'.data).2)
  let f : (fnf N)ˣ := Units.mk0 ⟨_, hv'NF⟩ (fun h => hv'0 (congrArg Subtype.val h))
  refine ⟨f, ?_⟩
  rw [kummerNF_eq_mk N hkF f s' v' rfl, H1Lim.mk_eq_mk_resS (s.le_extend K' hK) η,
    resS_extend_eq s K' hK η, hv, resT_kummerMapZHat]

end Rec

section Transport

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} [IsGalois (K₀ k t) Ω]
  [CharZero k] [IsAlgClosed Ω]

/-- **`P_V` along the transition between equal Galois models.** -/
lemma resT_mem_PU_of_eq {D₁ D₂ : Pi1.Orbifold.GaloisData k t} (h : D₁ = D₂)
    (hF : ∀ x ∈ F D₁, x ∈ F D₂)
    (hW : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → t ∈ W →
      (∀ c : k, algebraMap k Ω c ∈ W) ∧ t ∈ W) (hH : D₁.H ≤ D₁.HL)
    {η : ContH1 (Pi D₁) (ZHatOne (F D₁) Ω)} (hη : η ∈ PU D₁) :
    resT D₁ D₂ hF hW hH η ∈ PU D₂ := by
  subst h
  rwa [resT_self]

end Transport

section Curve

open CategoryTheory AlgebraicGeometry Belyi CurvesJacobian.Cusp GStage

variable {k : Type u} [Field k] [CharZero k] [NumberField k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X] {τ : X.functionField}
  {hτ : Transcendental k τ} [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)]
  [IsAlgClosed (FFClosure X)]

/-- `ofG g y` is the class of `y` at the stage `g.toStage`. -/
lemma ofG_eq_mk (g : GStage k hτ) (y : H1G g) :
    ofG g y = H1Lim.mk g.toStage
      (resT g.data g.toStage.data (F_toStage g) (fun _ hK ht => ⟨hK, ht⟩) g.data_H_le y) := rfl

set_option maxHeartbeats 4000000 in
-- `ContH1` and unit terms over the stages unify slowly
/-- **Piece A: a class of `P_V` at a geometric stage with a Kummer class as positive power lies
in `kummerNFRange`** (curve over a number field with a rational point). -/
theorem ofG_mem_kummerNFRange (N : NFModel (curveGaloisData k hτ))
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (g : GStage k hτ) {y : H1G g} (hy : y ∈ PU g.data) {M : ℕ} (hM : 0 < M)
    {w : units g.data} (hw : y ^ M = kummerMapZHat g.data w) :
    ofG g y ∈ kummerNFRange N (mem_range_of_isAlgebraic_F k hτ) := by
  rw [ofG_eq_mk]
  refine mk_mem_kummerNFRange_of_pow N (mem_range_of_isAlgebraic_F k hτ) g.toStage
    (isKummerFaithfulJac_stage_curve_numberField k hτ σ hσ g.toStage)
    (resT_mem_PU_of_eq (toStage_data g).symm _ _ _ hy) hM
    (w := unitsT g.data g.toStage.data (F_toStage g) (fun _ hK ht => ⟨hK, ht⟩) w) ?_
  rw [← map_pow, hw, resT_kummerMapZHat]

set_option maxHeartbeats 4000000 in
-- `ContH1` and unit terms over the stages unify slowly
/-- `ofG g (κ(v))` is the Kummer class of the NF-rational function `v`. -/
lemma ofG_kummerMapZHat (N : NFModel (curveGaloisData k hτ)) (g : GStage k hτ)
    (v : units g.data) (f : (fnf N)ˣ)
    (hv : (((v : (F g.data)ˣ) : F g.data) : FFClosure X) = ((f : fnf N) : FFClosure X)) :
    ofG g (kummerMapZHat g.data v) = kummerNF N (mem_range_of_isAlgebraic_F k hτ) f := by
  rw [ofG_eq_mk, resT_kummerMapZHat]
  exact (kummerNF_eq_mk N _ f g.toStage _ ((coe_unitsT _ _ _ _ v).trans hv)).symm

/-- A unit of a stage `s` below `g.toStage` as a unit of `g`. -/
lemma exists_units_of_le {s : StageIdx (curveGaloisData k hτ)} {g : GStage k hτ}
    (h : s ≤ g.toStage) (v : US (curveGaloisData k hτ) s) :
    ∃ v' : units g.data, (((v' : (F g.data)ˣ) : F g.data) : FFClosure X) =
      (((v : (F s.data)ˣ) : F s.data) : FFClosure X) :=
  ⟨unitsT s.data g.data (F_le_of_le_toStage h) (hW_le h) v, coe_unitsT _ _ _ _ v⟩

/-- A unit of `g` as a unit of `g′ ≥ g`. -/
lemma exists_units_of_gle {g g' : GStage k hτ} (h : g ≤ g') (v : units g.data) :
    ∃ v' : units g'.data, (((v' : (F g'.data)ˣ) : F g'.data) : FFClosure X) =
      (((v : (F g.data)ˣ) : F g.data) : FFClosure X) :=
  ⟨unitsT g.data g'.data (F_mono h) (hW_mono h) v, coe_unitsT _ _ _ _ v⟩

set_option maxHeartbeats 4000000 in
-- `ContH1` and unit terms over the stages unify slowly
/-- **Piece B: every class of `kummerNFRange` is a Kummer class at a geometric stage with
rational cusps carrying a unit that is not an algebraic number.** -/
theorem exists_ratStage_of_mem (N : NFModel (curveGaloisData k hτ))
    {ξ : H1Lim (curveGaloisData k hτ)}
    (hξ : ξ ∈ kummerNFRange N (mem_range_of_isAlgebraic_F k hτ)) :
    ∃ (g : GStage k hτ) (v f₀ : units g.data),
      (∀ P : Place g.K (F g.data), IsCuspPlaceF P → ∃ x : RatPoint g.data, placeOfF x = P) ∧
      ofG g (kummerMapZHat g.data v) = ξ ∧
      ¬ IsAlgebraic ℚ (((f₀ : (F g.data)ˣ) : F g.data) : FFClosure X) := by
  obtain ⟨f, rfl⟩ := hξ
  obtain ⟨s₁, -, -, v₁, hv₁⟩ := exists_nfStage_units N (mem_range_of_isAlgebraic_F k hτ) ⊥
    (f : fnf N).2 (fun h => f.ne_zero (Subtype.ext h))
  obtain ⟨y, hy, hyt⟩ := N.exists_transcendental
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hyt isAlgebraic_zero
  obtain ⟨s₂, -, -, v₂, hv₂⟩ := exists_nfStage_units N (mem_range_of_isAlgebraic_F k hτ) ⊥ hy hy0
  obtain ⟨s, h₁, h₂⟩ := exists_ge_ge s₁ s₂
  obtain ⟨g₀, hg₀⟩ := exists_ge_toStage s
  obtain ⟨g, hg, -, hrat⟩ := g₀.exists_ge_ratCusps
  have hs₁ : s₁ ≤ g.toStage := h₁.trans (hg₀.trans (toStage_le_iff.2 hg))
  have hs₂ : s₂ ≤ g.toStage := h₂.trans (hg₀.trans (toStage_le_iff.2 hg))
  obtain ⟨v, hv⟩ := exists_units_of_le hs₁ v₁
  obtain ⟨f₀, hf₀⟩ := exists_units_of_le hs₂ v₂
  refine ⟨g, v, f₀, hrat, ofG_kummerMapZHat N g v f (hv.trans hv₁), ?_⟩
  rw [hf₀, hv₂]
  intro halg
  have hk : IsAlgebraic k y := halg.extendScalars (algebraMap ℚ k).injective
  exact hyt (isAlgebraic_algebraMap (⟨y, mem_algebraicClosure_iff.2 hk⟩ :
    kbar k (FFClosure X)))

end Curve

end Iut.Reconstruction.Thm19
