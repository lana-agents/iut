/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.StageLift
import Iut.Reconstruction.Thm19.BelyiMono
import Iut.Reconstruction.Thm19.StageCompat

/-!
# `lim→ H¹(Π_V, Ẑ(1)) ≃* lim→ H¹(Π_{V'}, Ẑ(1))` over `Π_U ≃ Π_{U'}` (MR9 item 3, step 6)

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178) works in
`lim→_V H¹(Π_V, μ_Ẑ(Π_U))`; the construction is functorial in isomorphisms `Π_U ≃ Π_{U'}`: the
opens `V ⊆ U` correspond to opens `V' ⊆ U'` by Belyi cuspidalization ([AbsTopII] Cor 3.8, the
lifts `IsCor38Lift`), and the field-of-constants extensions by `G_{K₁'} = ψ(G_{K₁})`. Here, for an
isomorphism `Φ` of the `arithmeticExt` of two affine hyperbolic curves over number fields, over
the geometric stages of `Thm19/GeomLim.lean`:

* `LiftData Φ g`: at a geometric stage `g = (K₁, τ₀)` a Cor 3.8 lift `φ` of `Φ` on
  `V = chartOne τ₀`, a coordinate `υ` of its image `V₂ = chartOne υ`, and a normalised lift `e`
  in the Galois models (`piT' ∘ e = bridgeIso Φ ∘ piT`); it exists (`LiftData.nonempty`,
  `BelyiCuspSpec`); the target stage `LiftData.tgt = (ψ(K₁), υ)` and the stage isomorphism
  `LiftData.S` (`constH1Iso`, coefficients `cycloVχ χU` for any `Φ`-equivariant `χU`, e.g.
  `cycloIso Φ`);
* **`LiftData.compat`**: for `g ≤ g₂` and any choices `L`, `L₂`, the classes of `L.S x` and of
  `L₂.S (resG x)` agree in the colimit (`IsCor38Lift.le_of_le`, `IsCor38Lift.exists_conj`,
  `exists_galLift_conj`, `piToGk_eq_one_of_conj`, `h1Congr_resT_conj`);
* (`Thm19/LimEquiv.lean`) the inverse lift data and the isomorphisms of the colimits.

Hypotheses carried (named debts, unchanged): rel-isom-DGC `hDGC` on both sides (MR7), Belyi
cuspidalization `BelyiCuspSpec` on both sides (MR8), rational points `σ₀`, `σ₂` and genus `≠ 0`
on both compactifications (item 1).
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian.Cusp

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction

open Thm19 Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve AffOrbicurve CurvesJacobian
  CurvesJacobian.Kummer WeilCurves.FunctionField


section Basic

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [IsFunctionField k X.functionField]

/-- The function fields of the Galois models of a curve do not depend on the coordinate. -/
lemma F_cGD {τ₁ τ₂ : X.functionField} (h₁ : Transcendental k τ₁) (h₂ : Transcendental k τ₂) :
    ∀ x ∈ F (curveGaloisData k h₁), x ∈ F (curveGaloisData k h₂) := fun x hx => by
  haveI := isGalois_K₀_algebraicClosure (k := k) τ₁ h₁
  have h : x ∈ (curveGaloisData k h₁).L := hx
  rw [curveGaloisData_L] at h
  exact (IntermediateField.mem_fixedField_iff _ _).2 fun _ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x h

end Basic

lemma hW_chart {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t₁ t₂ : Ω}
    (h : t₁ ∈ chartRing k t₂) : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) →
      t₂ ∈ W → (∀ c : k, algebraMap k Ω c ∈ W) ∧ t₁ ∈ W :=
  fun W hk ht => ⟨hk, mem_of_mem_chartRing W hk ht h⟩

section Opens

variable {K : Type u} [Field K] [NumberField K] {C : HypCurve K}

attribute [local instance] isIntegral_Xbar

lemma chartOne_ne (τ₀ : C.Xbar.functionField) : (chartOne K C.Xbar τ₀ : Set C.Xbar).Nonempty :=
  ⟨genericPoint _, genericPoint_mem_chartOne (k := K) τ₀⟩

lemma chartOne_le_U {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
    (hU : C.U = chartOne K C.Xbar τ) {τ₀ : C.Xbar.functionField} (hτ₀ : Transcendental K τ₀)
    (h : coordT τ ∈ chartRing K (coordT τ₀)) : chartOne K C.Xbar τ₀ ≤ C.U := by
  rw [hU]
  exact (chartOne_le_iff K hτ hτ₀).2 h

/-- The complement of an open of a hyperbolic curve is nonempty. -/
instance factSubCurve [h : Fact (C.U : Set C.Xbar)ᶜ.Nonempty] {V : C.Xbar.Opens} {hV : V ≤ C.U}
    {hne : (V : Set C.Xbar).Nonempty} :
    Fact ((subCurve C V hV hne).U : Set (subCurve C V hV hne).Xbar)ᶜ.Nonempty :=
  ⟨compl_nonempty_of_le hV h.out⟩

end Opens

section Lift

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

set_option synthInstance.maxHeartbeats 400000 in
-- the action of `Π_U` on `Ẑ(1)` is found slowly
variable {hτ hτ₂} in
/-- `χU : Ẑ(1) ≃ₜ* Ẑ(1)'` is equivariant along `B : Π_U ≃ₜ* Π_{U'}`. -/
def CycloEquivariant (B : Pi (curveGaloisData K hτ) ≃ₜ* Pi (curveGaloisData K₂ hτ₂))
    (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
      ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar)) : Prop :=
  ∀ p z, χU (p • z) = B p • χU z

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- `G_{ψ(K₁)}` for the isomorphism `ψ = gkIso Φ` is finite over `K₂`. -/
instance fd_constField (K₁ : IntermediateField K (FFClosure C.Xbar)) [FiniteDimensional K K₁] :
    FiniteDimensional K₂ (constField (gkIso hτ hU hτ₂ hU₂ Φ) K₁) :=
  finiteDimensional_constField (bridgeIso hτ hU hτ₂ hU₂ Φ) (gkIso hτ hU hτ₂ hU₂ Φ)
    (bridgeIso_gk hτ hU hτ₂ hU₂ Φ) (piToGk_surjective_curve hτ) K₁

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- **Lift data at a geometric stage `g = (K₁, τ₀)`**: a Cor 3.8 lift `φ` of `Φ` on
`V = chartOne τ₀`, with image `chartOne υ ⊆ U'`, and a normalised lift `e` of `φ` in the Galois
models (`piT' ∘ e = bridgeIso Φ ∘ piT`, `e = conj b ∘ galLift φ`). -/
structure LiftData (g : GStage K hτ) where
  /-- The coordinate of the image open. -/
  υ : C₂.Xbar.functionField
  hυ : Transcendental K₂ υ
  [gal : IsGalois (K₀ K₂ (coordT υ)) (FFClosure C₂.Xbar)]
  htV : coordT τ₂ ∈ chartRing K₂ (coordT υ)
  /-- The Cor 3.8 lift. -/
  φ : (arithmeticExt Ω (subCurve C (chartOne K C.Xbar g.τ₀) (chartOne_le_U hτ hU g.hτ₀ g.htV)
      (chartOne_ne g.τ₀)) (compl_nonempty_of_le (chartOne_le_U hτ hU g.hτ₀ g.htV) hc.out)).Pi ≃ₜ*
    (arithmeticExt Ω₂ (subCurve C₂ (chartOne K₂ C₂.Xbar υ) (chartOne_le_U hτ₂ hU₂ hυ htV)
      (chartOne_ne υ)) (compl_nonempty_of_le (chartOne_le_U hτ₂ hU₂ hυ htV) hc₂.out)).Pi
  hφ : IsCor38Lift Φ.pi.toMulEquiv (chartOne_le_U hτ hU g.hτ₀ g.htV) (chartOne_ne g.τ₀)
    (chartOne_le_U hτ₂ hU₂ hυ htV) (chartOne_ne υ) φ
  /-- The normalised lift in the Galois models. -/
  e : Pi (curveGaloisData K g.hτ₀) ≃ₜ* Pi (curveGaloisData K₂ hυ)
  he : ∀ x, piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) (F_cGD hτ₂ hυ) (hW_chart htV)
      (curveGaloisData_H_le K₂ hτ₂) (e x) =
    bridgeIso hτ hU hτ₂ hU₂ Φ (piT (curveGaloisData K hτ) (curveGaloisData K g.hτ₀)
      (F_cGD hτ g.hτ₀) (hW_chart g.htV) (curveGaloisData_H_le K hτ) x)
  hb : ∃ b, ∀ x, e x = b * galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl hυ rfl φ x * b⁻¹

attribute [instance] LiftData.gal

variable {hτ hU hτ₂ hU₂ Φ}

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
include hτ hU hτ₂ hU₂ in
/-- **Lift data exist** (`BelyiCuspSpec` (d), `exists_coord`, `exists_galNormal`). -/
theorem LiftData.nonempty (hS : BelyiCuspSpec Ω C hc.out) (g : GStage K hτ) :
    Nonempty (LiftData hτ hU hτ₂ hU₂ Φ g) := by
  obtain ⟨V₂, hV₂, hne₂, φ, hφ⟩ := exists_isCor38Lift hS Φ (chartOne K C.Xbar g.τ₀)
    (chartOne_le_U hτ hU g.hτ₀ g.htV) (chartOne_ne g.τ₀)
  obtain ⟨υ, hυ, hUυ⟩ : ∃ υ : C₂.Xbar.functionField, Transcendental K₂ υ ∧
      V₂ = chartOne K₂ C₂.Xbar υ := exists_coord (subCurve C₂ V₂ hV₂ hne₂)
  subst hUυ
  haveI := isGalois_K₀_algebraicClosure (k := K₂) υ hυ
  have htV : coordT τ₂ ∈ chartRing K₂ (coordT υ) := by
    rw [← chartOne_le_iff K₂ hτ₂ hυ, ← hU₂]
    exact hV₂
  obtain ⟨e, he, hb⟩ := hφ.exists_galNormal hτ hU hτ₂ hU₂ g.hτ₀ rfl hυ rfl (F_cGD hτ g.hτ₀)
    (hW_chart g.htV) (F_cGD hτ₂ hυ) (hW_chart htV)
  exact ⟨⟨υ, hυ, htV, φ, hφ, e, he, hb⟩⟩

variable {g : GStage K hτ}

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- The normalised lift lies over `gkIso Φ`. -/
lemma LiftData.he_gk (L : LiftData hτ hU hτ₂ hU₂ Φ g) (x) :
    piToGk (curveGaloisData K₂ L.hυ) (L.e x) =
      gkIso hτ hU hτ₂ hU₂ Φ (piToGk (curveGaloisData K g.hτ₀) x) :=
  piToGk_of_piT_eq hτ hU hτ₂ hU₂ g.hτ₀ L.hυ _ _ _ _ L.he x

/-- **The target stage** `(ψ(K₁), υ)`. -/
abbrev LiftData.tgt (L : LiftData hτ hU hτ₂ hU₂ Φ g) : GStage K₂ hτ₂ where
  K := constField (gkIso hτ hU hτ₂ hU₂ Φ) g.K
  τ₀ := L.υ
  hτ₀ := L.hυ
  htV := L.htV

section Cyclo

variable (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- The coefficients at `V`: `χU` read through the identifications `zT` along `V ⊆ U`. -/
def cycloVχ {τ₀ : C.Xbar.functionField} (hτ₀ : Transcendental K τ₀)
    {υ : C₂.Xbar.functionField} (hυ : Transcendental K₂ υ) :
    ZHatOne (F (curveGaloisData K hτ₀)) (FFClosure C.Xbar) ≃ₜ*
      ZHatOne (F (curveGaloisData K₂ hυ)) (FFClosure C₂.Xbar) :=
  (zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
      (F (curveGaloisData K hτ₀))).symm.trans
    (χU.trans (zHatResEquiv (FFClosure C₂.Xbar) (F (curveGaloisData K₂ hτ₂))
      (F (curveGaloisData K₂ hυ))))

set_option maxHeartbeats 1600000 in
-- the quotients `Π_U`, `Π_V` are slow for unification
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
omit hc hc₂ in
/-- `cycloVχ` is equivariant along a normalised lift. -/
theorem cycloVχ_smul (B : Pi (curveGaloisData K hτ) ≃ₜ* Pi (curveGaloisData K₂ hτ₂))
    (hχU : ∀ p z, χU (p • z) = B p • χU z)
    {τ₀ : C.Xbar.functionField} (hτ₀ : Transcendental K τ₀)
    [IsGalois (K₀ K (coordT τ₀)) (FFClosure C.Xbar)]
    {υ : C₂.Xbar.functionField} (hυ : Transcendental K₂ υ)
    [IsGalois (K₀ K₂ (coordT υ)) (FFClosure C₂.Xbar)]
    {hF : ∀ x ∈ F (curveGaloisData K hτ), x ∈ F (curveGaloisData K hτ₀)}
    {hW : ∀ W : ValuationSubring (FFClosure C.Xbar),
      (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) → coordT τ₀ ∈ W →
        (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) ∧ coordT τ ∈ W}
    {hF₂ : ∀ x ∈ F (curveGaloisData K₂ hτ₂), x ∈ F (curveGaloisData K₂ hυ)}
    {hW₂ : ∀ W : ValuationSubring (FFClosure C₂.Xbar),
      (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) → coordT υ ∈ W →
        (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) ∧ coordT τ₂ ∈ W}
    {e : Pi (curveGaloisData K hτ₀) ≃ₜ* Pi (curveGaloisData K₂ hυ)}
    (he : ∀ x, piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) hF₂ hW₂
          (curveGaloisData_H_le K₂ hτ₂) (e x) =
        B (piT (curveGaloisData K hτ) (curveGaloisData K hτ₀) hF hW
          (curveGaloisData_H_le K hτ) x))
    (p : Pi (curveGaloisData K hτ₀)) (z : ZHatOne (F (curveGaloisData K hτ₀)) (FFClosure C.Xbar)) :
    cycloVχ χU hτ₀ hυ (p • z) = e p • cycloVχ χU hτ₀ hυ z := by
  obtain ⟨w, rfl⟩ := (zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
    (F (curveGaloisData K hτ₀))).surjective z
  have h1 : ∀ y, (zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
      (F (curveGaloisData K hτ₀))).symm (zHatResEquiv (FFClosure C.Xbar)
        (F (curveGaloisData K hτ)) (F (curveGaloisData K hτ₀)) y) = y :=
    fun y => ContinuousMulEquiv.symm_apply_apply _ y
  have h2 : p • zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
      (F (curveGaloisData K hτ₀)) w =
      zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ)) (F (curveGaloisData K hτ₀))
        (piT (curveGaloisData K hτ) (curveGaloisData K hτ₀) hF hW (curveGaloisData_H_le K hτ) p •
          w) :=
    (zT_piT_smul (curveGaloisData K hτ) (curveGaloisData K hτ₀) hF hW
      (curveGaloisData_H_le K hτ) p w).symm
  change zT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) (χU
      ((zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
        (F (curveGaloisData K hτ₀))).symm (p • _))) =
    e p • zT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) (χU
      ((zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
        (F (curveGaloisData K hτ₀))).symm _))
  rw [h2, h1, h1, hχU, ← he, zT_piT_smul]

variable (hχU : CycloEquivariant (bridgeIso hτ hU hτ₂ hU₂ Φ) χU)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- **The stage isomorphism** `H¹(Π_{V_{K₁}}, Ẑ(1)) ≃* H¹(Π_{V₂,ψ(K₁)}, Ẑ(1))` of lift data
(`constH1Iso` along `e`, coefficients `cycloVχ χU`). -/
def LiftData.S (L : LiftData hτ hU hτ₂ hU₂ Φ g) : H1G g ≃* H1G L.tgt :=
  constH1Iso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
    (cycloVχ χU g.hτ₀ L.hυ) (cycloVχ_smul χU _ hχU g.hτ₀ L.hυ L.he) g.K

end Cyclo

/-! ### Compatibility with the transition maps -/

section Compat

/-- Changes of base point to a filled open exist. -/
lemma nonempty_fillIso {K' : Type u} [Field K'] [NumberField K'] (Ω' : Type u) [Field Ω']
    [Algebra K' Ω'] [IsAlgClosed Ω'] [Algebra.IsAlgebraic K' Ω'] [CharZero Ω'] (C' : HypCurve K')
    (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty) (V : C'.Xbar.Opens) (hV : V ≤ C'.U)
    (hne : (V : Set C'.Xbar).Nonempty) :
    Nonempty (fiber (basePoint Ω' C' hc') ≅
      fiber (fillPoint Ω' (subCurve C' V hV hne) (compl_nonempty_of_le hV hc') hV)) := by
  haveI := isIntegral_specTensor Ω' C' hc'
  exact nonempty_iso_of_fiberFunctor _ _

omit [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
/-- Changes of base point for `V ⊆ V♮` (all opens given explicitly: `chartOne` is reducible and
must not be unfolded by unification). -/
lemma nonempty_fillIso₂ {K' : Type u} [Field K'] [NumberField K'] (Ω' : Type u) [Field Ω']
    [Algebra K' Ω'] [IsAlgClosed Ω'] [Algebra.IsAlgebraic K' Ω'] [CharZero Ω'] (C' : HypCurve K')
    (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty) (VB V : C'.Xbar.Opens) (hVB : VB ≤ C'.U)
    (hneB : (VB : Set C'.Xbar).Nonempty) (hVV : V ≤ VB) (hne : (V : Set C'.Xbar).Nonempty) :
    Nonempty (fiber (basePoint Ω' (subCurve C' VB hVB hneB) (compl_nonempty_of_le hVB hc')) ≅
      fiber (fillPoint Ω' (subCurve (subCurve C' VB hVB hneB) V hVV hne)
        (compl_nonempty_of_le hVV (compl_nonempty_of_le hVB hc')) hVV)) :=
  nonempty_fillIso Ω' (subCurve C' VB hVB hneB) (compl_nonempty_of_le hVB hc') V hVV hne

variable (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))
  (hχU : CycloEquivariant (bridgeIso hτ hU hτ₂ hU₂ Φ) χU)
  [CharZero (FFClosure C.Xbar)] [CharZero (FFClosure C₂.Xbar)]
  (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
  (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
  (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
  (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
  (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
  (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0) (hDGC : RelIsomDGC.Exists K₂)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
omit [CharZero (FFClosure C.Xbar)] in
include σ₂ hσ₂ hg₂ in
lemma LiftData.le_tgt {g g₂ : GStage K hτ} (h : g ≤ g₂)
    (L : LiftData hτ hU hτ₂ hU₂ Φ g) (L₂ : LiftData hτ hU hτ₂ hU₂ Φ g₂) : L.tgt ≤ L₂.tgt :=
  ⟨constField_mono _ h.1, (chartOne_le_iff K₂ L.hυ L₂.hυ).1
    (IsCor38Lift.le_of_le hτ₂ hU₂ σ₂ hσ₂ hg₂ Φ L₂.hφ L.hφ ((chartOne_le_iff K g.hτ₀ g₂.hτ₀).2 h.2))⟩

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC in
/-- **Lifts on `V ⊆ V♮` agree up to an element over `1 ∈ G_{K'}`** in the Galois models
(`IsCor38Lift.exists_conj`, `exists_galLift_conj`, normalisations, `piToGk_eq_one_of_conj`). -/
theorem LiftData.exists_conj_e {g g₂ : GStage K hτ} (h : g ≤ g₂)
    (L : LiftData hτ hU hτ₂ hU₂ Φ g) (L₂ : LiftData hτ hU hτ₂ hU₂ Φ g₂) :
    ∃ M, piToGk (curveGaloisData K₂ L.hυ) M = 1 ∧ ∀ y,
      piT (curveGaloisData K₂ L.hυ) (curveGaloisData K₂ L₂.hυ) (F_cGD L.hυ L₂.hυ)
        (hW_chart (L.le_tgt σ₂ hσ₂ hg₂ h L₂).2) (curveGaloisData_H_le K₂ L.hυ) (L₂.e y) =
      M * L.e (piT (curveGaloisData K g.hτ₀) (curveGaloisData K g₂.hτ₀) (F_cGD g.hτ₀ g₂.hτ₀)
        (hW_chart h.2) (curveGaloisData_H_le K g.hτ₀) y) * M⁻¹ := by
  have hVV : chartOne K C.Xbar g₂.τ₀ ≤ chartOne K C.Xbar g.τ₀ :=
    (chartOne_le_iff K g.hτ₀ g₂.hτ₀).2 h.2
  have hVV₂ : chartOne K₂ C₂.Xbar L₂.υ ≤ chartOne K₂ C₂.Xbar L.υ :=
    IsCor38Lift.le_of_le hτ₂ hU₂ σ₂ hσ₂ hg₂ Φ L₂.hφ L.hφ hVV
  have hle := L.le_tgt σ₂ hσ₂ hg₂ h L₂
  obtain ⟨α₁⟩ := nonempty_fillIso₂ Ω C hc.out (chartOne K C.Xbar g.τ₀) (chartOne K C.Xbar g₂.τ₀)
    (chartOne_le_U hτ hU g.hτ₀ g.htV) (chartOne_ne g.τ₀) hVV (chartOne_ne g₂.τ₀)
  obtain ⟨α₂⟩ := nonempty_fillIso₂ Ω₂ C₂ hc₂.out (chartOne K₂ C₂.Xbar L.υ)
    (chartOne K₂ C₂.Xbar L₂.υ) (chartOne_le_U hτ₂ hU₂ L.hυ L.htV) (chartOne_ne L.υ) hVV₂
    (chartOne_ne L₂.υ)
  obtain ⟨m₀, hm₀⟩ := L₂.hφ.exists_conj hτ hU σ₀ hσ₀ hg hτ₂ hU₂ σ₂ hσ₂ hg₂ hDGC Φ.pr_comm L.hφ
    hVV hVV₂ α₁ α₂
  obtain ⟨m, hm⟩ := exists_galLift_conj hVV hVV₂ g.hτ₀ rfl g₂.hτ₀ rfl L.hυ rfl L₂.hυ rfl
    (F_cGD g.hτ₀ g₂.hτ₀) (hW_chart h.2) (F_cGD L.hυ L₂.hυ) (hW_chart hle.2) L₂.φ L.φ α₁ α₂
    ⟨m₀, hm₀⟩
  obtain ⟨b, hb⟩ := L.hb
  obtain ⟨b₂, hb₂⟩ := L₂.hb
  have hgl : ∀ y, galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ y = b⁻¹ * L.e y * b :=
    fun y => by rw [hb]; group
  have hm' : ∀ y, piT (curveGaloisData K₂ L.hυ) (curveGaloisData K₂ L₂.hυ) (F_cGD L.hυ L₂.hυ)
      (hW_chart hle.2) (curveGaloisData_H_le K₂ L.hυ) (L₂.e y) =
      (piT (curveGaloisData K₂ L.hυ) (curveGaloisData K₂ L₂.hυ) (F_cGD L.hυ L₂.hυ)
        (hW_chart hle.2) (curveGaloisData_H_le K₂ L.hυ) b₂ * m * b⁻¹) *
      L.e (piT (curveGaloisData K g.hτ₀) (curveGaloisData K g₂.hτ₀) (F_cGD g.hτ₀ g₂.hτ₀)
        (hW_chart h.2) (curveGaloisData_H_le K g.hτ₀) y) *
      (piT (curveGaloisData K₂ L.hυ) (curveGaloisData K₂ L₂.hυ) (F_cGD L.hυ L₂.hυ)
        (hW_chart hle.2) (curveGaloisData_H_le K₂ L.hυ) b₂ * m * b⁻¹)⁻¹ := by
    intro y
    rw [hb₂, map_mul, map_mul, map_inv, hm, hgl]
    group
  exact ⟨_, piToGk_eq_one_of_conj hτ hU hτ₂ hU₂ Φ g.hτ₀ g₂.hτ₀ rfl L.hυ L₂.hυ _ _ _ _ _ _ _ _
    _ _ _ _ (hV := chartOne_le_U hτ hU g₂.hτ₀ g₂.htV) (hne := chartOne_ne g₂.τ₀) L₂.he L.he hm',
    hm'⟩

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` and their base changes unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC in
/-- **The restrictions to the fields of constants agree up to an element acting trivially on
`Ẑ(1)`** (`piRes_constIso`, `piRes_piT`, `smul_eq_self_of_piToGk`). Stated with the Galois models
`g.data`, `L.tgt.data` of the stages, as at the use site (`LiftData.compat`). -/
theorem LiftData.exists_conj_const {g g₂ : GStage K hτ} (h : g ≤ g₂)
    (L : LiftData hτ hU hτ₂ hU₂ Φ g) (L₂ : LiftData hτ hU hτ₂ hU₂ Φ g₂) :
    ∃ m'' : Pi L.tgt.data, (∀ z : ZHatOne (F L.tgt.data) (FFClosure C₂.Xbar), m'' • z = z) ∧
      ∀ y : Pi g₂.data,
      piT L.tgt.data L₂.tgt.data (GStage.F_mono (g := L.tgt) (g' := L₂.tgt)
          (L.le_tgt σ₂ hσ₂ hg₂ h L₂))
        (GStage.hW_mono (g := L.tgt) (g' := L₂.tgt) (L.le_tgt σ₂ hσ₂ hg₂ h L₂)) L.tgt.data_H_le
        (constIso L₂.e (gkIso hτ hU hτ₂ hU₂ Φ) L₂.he_gk (piToGk_surjective_curve g₂.hτ₀) g₂.K y) =
      m'' * constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K
        (piT g.data g₂.data (GStage.F_mono (g := g) (g' := g₂) h)
          (GStage.hW_mono (g := g) (g' := g₂) h) g.data_H_le y) * m''⁻¹ := by
  have hle := L.le_tgt σ₂ hσ₂ hg₂ h L₂
  obtain ⟨M, hM1, hM⟩ := L.exists_conj_e σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC h L₂
  obtain ⟨m'', hm''⟩ : M ∈
      (piRes (constField (gkIso hτ hU hτ₂ hU₂ Φ) g.K) (curveGaloisData K₂ L.hυ)).range := by
    rw [mem_range_piRes_iff]
    intro c
    rw [hM1]
    rfl
  have hm1 : piToGk (curveGaloisData K₂ L.hυ)
      (piRes (constField (gkIso hτ hU hτ₂ hU₂ Φ) g.K) (curveGaloisData K₂ L.hυ) m'') = 1 :=
    (congrArg (piToGk (curveGaloisData K₂ L.hυ)) hm'').trans hM1
  refine ⟨m'', smul_eq_self_of_piToGk (K₁ := constField (gkIso hτ hU hτ₂ hU₂ Φ) g.K)
    (D₁ := curveGaloisData K₂ L.hυ) m'' hm1, fun y => ?_⟩
  refine piRes_injective (K := constField (gkIso hτ hU hτ₂ hU₂ Φ) g.K)
    (curveGaloisData K₂ L.hυ) ?_
  have e1 : piRes (constField (gkIso hτ hU hτ₂ hU₂ Φ) g.K) (curveGaloisData K₂ L.hυ)
      (piT L.tgt.data L₂.tgt.data (GStage.F_mono (g := L.tgt) (g' := L₂.tgt) hle)
        (GStage.hW_mono (g := L.tgt) (g' := L₂.tgt) hle) L.tgt.data_H_le
        (constIso L₂.e (gkIso hτ hU hτ₂ hU₂ Φ) L₂.he_gk (piToGk_surjective_curve g₂.hτ₀) g₂.K
          y)) =
      piT (curveGaloisData K₂ L.hυ) (curveGaloisData K₂ L₂.hυ) (F_cGD L.hυ L₂.hυ)
        (hW_chart hle.2) (curveGaloisData_H_le K₂ L.hυ)
        (L₂.e (piRes g₂.K (curveGaloisData K g₂.hτ₀) y)) :=
    (piRes_piT (K₁ := constField (gkIso hτ hU hτ₂ hU₂ Φ) g.K)
      (K₂ := constField (gkIso hτ hU hτ₂ hU₂ Φ) g₂.K) (D₁ := curveGaloisData K₂ L.hυ)
      (D₂ := curveGaloisData K₂ L₂.hυ) (GStage.F_mono (g := L.tgt) (g' := L₂.tgt) hle)
      (GStage.hW_mono (g := L.tgt) (g' := L₂.tgt) hle) L.tgt.data_H_le (F_cGD L.hυ L₂.hυ)
      (hW_chart hle.2) (curveGaloisData_H_le K₂ L.hυ)
      (constIso L₂.e (gkIso hτ hU hτ₂ hU₂ Φ) L₂.he_gk (piToGk_surjective_curve g₂.hτ₀) g₂.K
        y)).trans
      (congrArg (piT (curveGaloisData K₂ L.hυ) (curveGaloisData K₂ L₂.hυ) (F_cGD L.hυ L₂.hυ)
        (hW_chart hle.2) (curveGaloisData_H_le K₂ L.hυ))
        (piRes_constIso L₂.e (gkIso hτ hU hτ₂ hU₂ Φ) L₂.he_gk (piToGk_surjective_curve g₂.hτ₀)
          g₂.K y))
  have e3 : piRes g.K (curveGaloisData K g.hτ₀)
      (piT g.data g₂.data (GStage.F_mono (g := g) (g' := g₂) h)
        (GStage.hW_mono (g := g) (g' := g₂) h) g.data_H_le y) =
      piT (curveGaloisData K g.hτ₀) (curveGaloisData K g₂.hτ₀) (F_cGD g.hτ₀ g₂.hτ₀)
        (hW_chart h.2) (curveGaloisData_H_le K g.hτ₀) (piRes g₂.K (curveGaloisData K g₂.hτ₀) y) :=
    piRes_piT (K₁ := g.K) (K₂ := g₂.K) (D₁ := curveGaloisData K g.hτ₀)
      (D₂ := curveGaloisData K g₂.hτ₀) (GStage.F_mono (g := g) (g' := g₂) h)
      (GStage.hW_mono (g := g) (g' := g₂) h) g.data_H_le (F_cGD g.hτ₀ g₂.hτ₀)
      (hW_chart h.2) (curveGaloisData_H_le K g.hτ₀) y
  have hX := piRes_constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
    g.K (piT g.data g₂.data (GStage.F_mono (g := g) (g' := g₂) h)
      (GStage.hW_mono (g := g) (g' := g₂) h) g.data_H_le y)
  have e2 : ∀ a b : Pi (constExt (constField (gkIso hτ hU hτ₂ hU₂ Φ) g.K)
      (curveGaloisData K₂ L.hυ)),
      piRes (constField (gkIso hτ hU hτ₂ hU₂ Φ) g.K) (curveGaloisData K₂ L.hυ) (a * b * a⁻¹) =
        piRes (constField (gkIso hτ hU hτ₂ hU₂ Φ) g.K) (curveGaloisData K₂ L.hυ) a *
          piRes (constField (gkIso hτ hU hτ₂ hU₂ Φ) g.K) (curveGaloisData K₂ L.hυ) b *
          (piRes (constField (gkIso hτ hU hτ₂ hU₂ Φ) g.K) (curveGaloisData K₂ L.hυ) a)⁻¹ :=
    fun a b => (map_mul _ _ _).trans (congrArg₂ (· * ·) (map_mul _ _ _) (map_inv _ _))
  refine e1.trans ((hM _).trans ?_)
  refine (congrArg (fun w => M * L.e w * M⁻¹) e3.symm).trans ?_
  refine Eq.trans ?_ (e2 _ _).symm
  exact (congrArg₂ (fun a b => a * b * a⁻¹) hm'' hX).symm

set_option maxHeartbeats 1600000 in
-- the coefficients of the base changes unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the actions on `Ẑ(1)` are found slowly
omit [CharZero (FFClosure C.Xbar)] [CharZero (FFClosure C₂.Xbar)] in
/-- `constCyclo` of `cycloVχ` is the restriction map through `χU`. -/
lemma constCyclo_cycloVχ {g : GStage K hτ} (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (w : ZHatOne (F g.data) (FFClosure C.Xbar)) :
    constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K w =
      zHatRes (F (curveGaloisData K₂ hτ₂)) (F L.tgt.data) (FFClosure C₂.Xbar) (FFClosure C₂.Xbar)
        (χU (zHatRes (F g.data) (F (curveGaloisData K hτ)) (FFClosure C.Xbar) (FFClosure C.Xbar)
          w)) :=
  (zHatRes_zHatRes (F (curveGaloisData K₂ hτ₂)) (F (curveGaloisData K₂ L.hυ)) (F L.tgt.data)
      (χU (zHatRes (F (curveGaloisData K g.hτ₀)) (F (curveGaloisData K hτ)) (FFClosure C.Xbar)
        (FFClosure C.Xbar) (zHatRes (F g.data) (F (curveGaloisData K g.hτ₀)) (FFClosure C.Xbar)
          (FFClosure C.Xbar) w)))).trans
    (congrArg (fun v => zHatRes (F (curveGaloisData K₂ hτ₂)) (F L.tgt.data) (FFClosure C₂.Xbar)
        (FFClosure C₂.Xbar) (χU v))
      (zHatRes_zHatRes (F g.data) (F (curveGaloisData K g.hτ₀)) (F (curveGaloisData K hτ)) w))

set_option maxHeartbeats 1600000 in
-- the coefficients of the base changes unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the actions on `Ẑ(1)` are found slowly
omit [CharZero (FFClosure C.Xbar)] [CharZero (FFClosure C₂.Xbar)] in
/-- The coefficients commute with the transition maps (all maps are the identity on roots of
unity). -/
lemma cycloVχ_zT {g g₂ : GStage K hτ} (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (L₂ : LiftData hτ hU hτ₂ hU₂ Φ g₂) (z : ZHatOne (F g.data) (FFClosure C.Xbar)) :
    constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g₂.hτ₀ L₂.hυ) g₂.K (zT g.data g₂.data z) =
      zT L.tgt.data L₂.tgt.data
        (constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K z) :=
  (constCyclo_cycloVχ χU L₂ _).trans <|
    (congrArg (fun v => zHatRes (F (curveGaloisData K₂ hτ₂)) (F L₂.tgt.data) (FFClosure C₂.Xbar)
        (FFClosure C₂.Xbar) (χU v))
      (zHatRes_zHatRes (F g.data) (F g₂.data) (F (curveGaloisData K hτ)) z)).trans <|
    (zHatRes_zHatRes (F (curveGaloisData K₂ hτ₂)) (F L.tgt.data) (F L₂.tgt.data)
      (χU (zHatRes (F g.data) (F (curveGaloisData K hτ)) (FFClosure C.Xbar) (FFClosure C.Xbar)
        z))).symm.trans
    (congrArg (zHatRes (F L.tgt.data) (F L₂.tgt.data) (FFClosure C₂.Xbar) (FFClosure C₂.Xbar))
      (constCyclo_cycloVχ χU L z).symm)

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V`, their base changes and the coefficients unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC in
/-- **The stage isomorphisms are compatible with the transition maps**, for any choices of lift
data: for `g ≤ g₂`, `[L.S x] = [L₂.S (x|_{g₂})]` in the colimit. -/
theorem LiftData.compat {g g₂ : GStage K hτ} (h : g ≤ g₂) (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (L₂ : LiftData hτ hU hτ₂ hU₂ Φ g₂) (x : H1G g) :
    limOf (fun _ _ h => resG h) L.tgt (L.S χU hχU x) =
      limOf (fun _ _ h => resG h) L₂.tgt (L₂.S χU hχU (resG h x)) := by
  have hle := L.le_tgt σ₂ hσ₂ hg₂ h L₂
  obtain ⟨m'', hmtriv, hrel⟩ := L.exists_conj_const σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC h L₂
  have key := h1Congr_resT_conj (D₁ := g.data) (D₂ := g₂.data) (D₁' := L.tgt.data)
    (D₂' := L₂.tgt.data) (hF := GStage.F_mono (g := g) (g' := g₂) h)
    (hW := GStage.hW_mono (g := g) (g' := g₂) h) (hH := g.data_H_le)
    (hF' := GStage.F_mono (g := L.tgt) (g' := L₂.tgt) hle)
    (hW' := GStage.hW_mono (g := L.tgt) (g' := L₂.tgt) hle) (hH' := L.tgt.data_H_le)
    (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K)
    (constIso L₂.e (gkIso hτ hU hτ₂ hU₂ Φ) L₂.he_gk (piToGk_surjective_curve g₂.hτ₀) g₂.K)
    (constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K)
    (constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g₂.hτ₀ L₂.hυ) g₂.K)
    (constCyclo_smul L.e _ L.he_gk _ _ (cycloVχ_smul χU _ hχU g.hτ₀ L.hυ L.he) g.K)
    (constCyclo_smul L₂.e _ L₂.he_gk _ _ (cycloVχ_smul χU _ hχU g₂.hτ₀ L₂.hυ L₂.he) g₂.K)
    m'' hrel hmtriv (cycloVχ_zT χU L L₂) x
  exact (limOf_f (fun _ _ h => resG h) hle _).symm.trans
    (congrArg (limOf (fun _ _ h => resG h) L₂.tgt) key.symm)

end Compat

end Lift

end Iut.Reconstruction
