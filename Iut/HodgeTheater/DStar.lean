/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.FStarMod
import Iut.Frobenioid.OrbitMap
import Iut.Reconstruction.Cusp.HemiGenuineField

/-!
# `†D^⊛ = B(π₁(C_{F_mod}))⁰` and the global Frobenioid `F^⊛` over it (IUT I, Example 5.1)

IUT I, Example 5.1 (i) (l.8234–8262 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller
Theory I.txt`): "one may construct group-theoretically from `π₁(†D^⊚)` […] a profinite group
corresponding to "`C_{F_mod}`" […] which contains `π₁(†D^⊚)` as an open subgroup; write `†D^⊛`
for `B(−)⁰` of this profinite group". Example 5.1 (ii) (l.8392–8411): the monoid `Φ^⊛(†D^⊚)` on
`†D^⊛` assigns to `A` the arithmetic divisors on the corresponding subfield of `F̄`, and determines
"a model Frobenioid `F^⊛(†D^⊚)` over the base category `†D^⊛`"; (iii) (l.8434–8466):
`†F^⊛_mod` is the restriction to the terminal objects. This file builds the field-theoretic
models over IUT's base `†D^⊛`:

* `piCmod D = π₁(C_{F_mod})`, iut's genuine `π₁` of `C_{F_mod} = (E_mod ∖ {O}) / ±1`
  (`E_mod = WeierstrassCurve.ofJ j(E_F)` over `F_mod = ℚ(j)`, `curveMod`), and
  **`DStar D = B(π₁(C_{F_mod}))⁰`**;
* `piCmodPr D : π₁(C_{F_mod}) ↠ Gal(F̄/F_mod)` (continuous, surjective: restriction to the field
  of constants, curves-jacobian's `piConstC`, via `genuinePi1HemiEquiv`; `F̄` is identified with the
  algebraic closure of `F_mod` inside the function field closure);
* `toGalBase D : B(π₁(C_{F_mod}))⁰ ⥤ B(Gal(F̄/F_mod))⁰`, `A ↦` its image;
* **`globalFrobenioidStar D = F^⊛`** over `DStar D`: the model Frobenioid of [FrdI], Example 6.3
  pulled back along `toGalBase D` (`Φ^⊛(A)` = arithmetic divisors of the subfield of `F̄` fixed by
  the image of `A`), a Frobenioid (`globalFrobenioidStar_isFrobenioid`);
* **`globalFrobenioidStarMod D = F^⊛_mod`** (objects over the terminal object `Π/Π`, i.e.
  "`C_{F_mod}`"), with **`starModEquiv D : F^⊛_mod ≌ globalFrobenioidMod D`** (the Galois-base
  version of `HodgeTheater/FStarMod.lean`) and `starModEquivC D : C(F_mod) ≌ F^⊛_mod`;
* `cfToStar D : B(π₁(C_F))⁰ ⥤ †D^⊛` from the open embedding `π₁(C_F) ↪ π₁(C_{F_mod})`
  (`genuine_CF_emb_Fmod_theta`), the category-theoretic version of `C_F → C_{F_mod}`, and
  **`dCircToStar D : †D^⊚ = B(π₁(C̲_K))⁰ ⥤ †D^⊛`** (`C̲_K → C_K → C_{F_mod}`).

The group-theoretic reconstruction of `π₁(†D^⊛)` from `π₁(†D^⊚)` (via [AbsTopII], Cor. 3.3 (i))
and of `M^⊛(†D^⊚)` ([AbsTopIII], Thm. 1.9) are not part of this file.
-/

noncomputable section

namespace Iut

namespace HodgeTheater

open CategoryTheory CategoryTheory.Limits NumberField Frobenioid CurvesJacobian CurvesJacobian.Cusp
  Pi1.Orbifold Iut.Reconstruction.HemiGenuine Iut.Anabelian AlgebraicGeometry Belyi Belyi.Anabelian
  AffOrbicurve

-- the decidability instances of `Iut.Anabelian.Genuine` (classical)
attribute [local instance low] Classical.propDecidable

variable (D : InitialThetaData.{0})

/-- **`π₁(C_{F_mod})`**: iut's genuine `π₁` of `C_{F_mod} = (E_mod ∖ {O}) / ±1`. -/
abbrev piCmod : Type :=
  (Orbicurve.pmQuotient (Orbicurve.oncePunctured (curveMod D.E))).genuinePi1

/-- **`†D^⊛ = B(π₁(C_{F_mod}))⁰`** (IUT I, Example 5.1 (i)). -/
abbrev DStar : Type := OrbitObj (piCmod D)

/-- The algebraic closure of `F_mod` in curves-jacobian's closure of the function field of
`E_mod`. -/
abbrev constFmod : IntermediateField (Fmod D) (FFClosure (curveE (curveMod D.E))) :=
  ConstField₂ (Fmod D) (FFClosure (curveE (curveMod D.E)))

set_option synthInstance.maxHeartbeats 200000 in
-- the search goes through the `IntermediateField` algebra instances `F_mod → k̄ → K(Ē)^alg`
/-- It is `F̄` (as an algebraic closure of `F_mod`). -/
def constFmodEquiv : constFmod D ≃ₐ[Fmod D] D.Fbar :=
  IsAlgClosure.equiv (Fmod D) (constFmod D) D.Fbar

/-- `Gal(k̄ / F_mod) ≃ₜ* Gal(F̄ / F_mod)`. -/
def galConstEquiv : (constFmod D ≃ₐ[Fmod D] constFmod D) ≃ₜ* GalG (Fmod D) D.Fbar :=
  galConj (constFmodEquiv D).toRingEquiv fun x => by
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, ((constFmodEquiv D).commutes c).symm⟩
    · rintro ⟨c, hc⟩
      refine ⟨c, (constFmodEquiv D).injective ?_⟩
      rw [AlgEquiv.commutes]
      exact hc

/-- **`π₁(C_{F_mod}) ↠ Gal(F̄/F_mod)`** (restriction to the field of constants). -/
def piCmodPr : piCmod D →* GalG (Fmod D) D.Fbar :=
  (galConstEquiv D).toMonoidHom.comp
    ((piConstC (hemiData (curveMod D.E))).comp (genuinePi1HemiEquiv (curveMod D.E)).toMonoidHom)

lemma continuous_piCmodPr : Continuous (piCmodPr D) := by
  rw [piCmodPr, MonoidHom.coe_comp, MonoidHom.coe_comp]
  exact (galConstEquiv D).continuous.comp ((continuous_piConst _ _ _
    fun _ hs => galResConst_S _ hs).comp (genuinePi1HemiEquiv (curveMod D.E)).continuous)

/-- `Π_C ↠ Gal(k̄ / K)` (geometric connectedness, `galResConst_surjective_hemi`). -/
lemma piConstC_hemi_surjective {K : Type} [Field K] [NumberField K] (E' : WeierstrassCurve K)
    [E'.IsElliptic] : Function.Surjective (piConstC (hemiData E')) := fun g => by
  obtain ⟨σ, hσ⟩ := galResConst_surjective_hemi E' g
  exact ⟨QuotientGroup.mk ⟨σ, Subgroup.mem_top σ⟩, hσ⟩

lemma piCmodPr_surjective : Function.Surjective (piCmodPr D) := by
  rw [piCmodPr, MonoidHom.coe_comp, MonoidHom.coe_comp]
  exact (galConstEquiv D).surjective.comp ((piConstC_hemi_surjective (curveMod D.E)).comp
    (genuinePi1HemiEquiv (curveMod D.E)).surjective)

lemma isOpen_map_piCmodPr (U : Subgroup (piCmod D)) (hU : IsOpen (U : Set (piCmod D))) :
    IsOpen (U.map (piCmodPr D) : Set (GalG (Fmod D) D.Fbar)) :=
  isOpen_map_of_surjective _ (continuous_piCmodPr D) (piCmodPr_surjective D) U hU

/-- **`B(π₁(C_{F_mod}))⁰ ⥤ B(Gal(F̄/F_mod))⁰`**, `A ↦` its image under `piCmodPr`. -/
def toGalBase : DStar D ⥤ OrbitObj (GalG (Fmod D) D.Fbar) :=
  OrbitObj.mapFunctor (piCmodPr D) (isOpen_map_piCmodPr D)

lemma toGalBase_isFSM {A B : DStar D} (f : A ⟶ B) (hf : IsFSM f) : IsFSM ((toGalBase D).map f) :=
  isFSM_map_of_orbit _ f hf

/-- The monoid `Φ^⊛` on `†D^⊛` (IUT I, Example 5.1 (ii)): the arithmetic divisors of the subfield
of `F̄` fixed by the image of `A` in `Gal(F̄/F_mod)`. -/
abbrev phiStar : DivMonoid.{0} (DStar D) :=
  (phiGal (Fmod D) D.Fbar).comap (toGalBase D) (toGalBase_isFSM D)

/-- The rational functions `L^×` on `†D^⊛`. -/
abbrev bStar : GrpOn.{0} (DStar D) :=
  (bGalNF (Fmod D) D.Fbar).comap (toGalBase D) (toGalBase_isFSM D)

/-- `Div : L^× → Φ^⊛(A)^gp`. -/
abbrev divStar : DivHom (bStar D) (phiStar D).toGrpOn :=
  (divGalNF (Fmod D) D.Fbar).comap (toGalBase D) (toGalBase_isFSM D)

/-- **The global Frobenioid `F^⊛` over `†D^⊛ = B(π₁(C_{F_mod}))⁰`** (IUT I, Example 5.1 (ii),
field-theoretic; [FrdI], Example 6.3, Theorem 5.2 (ii)). -/
abbrev globalFrobenioidStar : Type := Model (phiStar D) (bStar D) (divStar D)

/-- **`F^⊛` is a Frobenioid** ([FrdI], Theorem 5.2 (ii)). -/
theorem globalFrobenioidStar_isFrobenioid :
    IsFrobenioid (Model.toElem (phiStar D) (bStar D) (divStar D)) :=
  Model.isFrobenioid

/-- The change of base `F^⊛ → C_{F̄/F_mod}` (`globalFrobenioid D`, over `B(Gal(F̄/F_mod))⁰`). -/
def starToGal : globalFrobenioidStar D ⥤ globalFrobenioid D :=
  Model.comapFunctor (toGalBase D) (toGalBase_isFSM D)

/-! ### The terminal objects of `†D^⊛` and `F^⊛_mod` -/

/-- **`Π/Π` is terminal in `†D^⊛`** ("`C_{F_mod}`"). -/
def isTerminalTopStar : IsTerminal (OrbitObj.top : DStar D) :=
  IsTerminal.ofUniqueHom (fun A => OrbitObj.toTop A) fun _ _ => Subsingleton.elim _ _

/-- **`F^⊛_mod = F^⊛|terminal objects`** (IUT I, Example 5.1 (iii)). -/
abbrev globalFrobenioidStarMod : Type :=
  (Model.over (Φ := phiStar D) (B := bStar D) (divB := divStar D) OrbitObj.top).FullSubcategory

lemma toGalBase_top : (toGalBase D).obj OrbitObj.top = topObj (Fmod D) D.Fbar :=
  map_top_eq _ (isOpen_map_piCmodPr D) (piCmodPr_surjective D)

instance : Subsingleton ((toGalBase D).obj OrbitObj.top ⟶ (toGalBase D).obj OrbitObj.top) :=
  subsingleton_hom_map_top _ (isOpen_map_piCmodPr D) (piCmodPr_surjective D) _

/-- **`F^⊛_mod` over `†D^⊛` is `F^⊛_mod` over `B(Gal(F̄/F_mod))⁰`** (`globalFrobenioidMod D`). -/
def starModEquiv : globalFrobenioidStarMod D ≌ globalFrobenioidMod D :=
  (Model.comapOverEquiv (toGalBase D) (toGalBase_isFSM D) OrbitObj.top).trans
    (Model.overEquivOfEq (toGalBase_top D))

/-- **`C(F_mod) ≌ F^⊛_mod`** over IUT's base `†D^⊛` (IUT I, Example 5.1 (iii): "the Frobenioid of
arithmetic line bundles"). -/
def starModEquivC : GlobalFrobenioid (Fmod D) ≌ globalFrobenioidStarMod D :=
  (modEquiv D).trans (starModEquiv D).symm

/-! ### `C_F → C_{F_mod}` -/

/-- The open embedding `π₁(C_F) ↪ π₁(C_{F_mod})` (`genuine_CF_emb_Fmod_theta`). -/
def piCFToCmod : (OrbicurveDataSection.CF D.F D.E).genuinePi1 →ₜ* piCmod D :=
  (genuine_CF_emb_Fmod_theta D).choose

lemma piCFToCmod_spec :
    Topology.IsOpenEmbedding (piCFToCmod D) ∧ (piCFToCmod D).toMonoidHom.range.Normal ∧
      (piCFToCmod D).toMonoidHom.range.index = Module.finrank (fieldOfModuli D.F D.E) D.F :=
  (genuine_CF_emb_Fmod_theta D).choose_spec

/-- **`B(π₁(C_F))⁰ ⥤ †D^⊛`**, the category-theoretic version of `C_F → C_{F_mod}`. -/
def cfToStar : OrbitObj (OrbicurveDataSection.CF D.F D.E).genuinePi1 ⥤ DStar D :=
  OrbitObj.mapFunctor (piCFToCmod D).toMonoidHom fun U hU => by
    rw [Subgroup.coe_map]
    exact (piCFToCmod_spec D).1.isOpenMap _ hU

/-! ### `†D^⊚ → †D^⊛` -/

/-- Equal orbicurves have the same genuine `π₁`. -/
def genuinePi1EqEquiv {k : Type} [Field k] {X Y : Orbicurve k} (h : X = Y) :
    X.genuinePi1 ≃ₜ* Y.genuinePi1 := by
  subst h
  exact ContinuousMulEquiv.refl _

lemma jMod_ne : (jMod D.E ≠ 0) ∧ (jMod D.E ≠ 1728) := by
  obtain ⟨v, hv⟩ := D.global.bad_nonempty
  obtain ⟨w, hw⟩ := FinitePlace.exists_liesOver (K := D.F) v
  obtain ⟨h0, h1728⟩ := j_ne_of_mult D.E (D.global.bad_multiplicative v hv w hw)
  refine ⟨fun h => h0 (congrArg Subtype.val h), fun h => h1728 ?_⟩
  have h' := congrArg (algebraMap (fieldOfModuli D.F D.E) D.F) h
  rw [map_ofNat] at h'
  exact h'

/-- **`π₁(C̲_K) ↪ π₁(C_{F_mod})`**: the covering `C̲_K → C_K` (IUT I, Def. 3.1 (d)) followed by
`π₁(C_K) ↪ π₁(C_{F_mod})` (`genuine_CF_emb`, `K/F_mod` Galois, IUT I Rem. 3.1.5). -/
theorem exists_piCKu_emb :
    ∃ f : D.orb.CKu.genuinePi1 →* piCmod D, Topology.IsOpenEmbedding f := by
  have hCK : OrbicurveDataSection.CK D.F D.E D.Fbar D.VBad D.prime = Orbicurve.pmQuotient
      (Orbicurve.oncePunctured (D.E.map (algebraMap D.F D.Kt))) := by
    rw [OrbicurveDataSection.CK, OrbicurveDataSection.CF, Orbicurve.baseChange_pmQuotient,
      Orbicurve.baseChange_oncePunctured]
  have hj : (D.E.map (algebraMap D.F D.Kt)).j =
      algebraMap (fieldOfModuli D.F D.E) D.Kt (curveMod D.E).j := by
    rw [WeierstrassCurve.map_j, show (curveMod D.E).j = jMod D.E from WeierstrassCurve.ofJ_j _]
    rfl
  have hj0 : (curveMod D.E).j = jMod D.E := WeierstrassCurve.ofJ_j _
  obtain ⟨g, hg, -, -⟩ := genuine_CF_emb (K := fieldOfModuli D.F D.E) (F := D.Kt) (curveMod D.E)
    (D.E.map (algebraMap D.F D.Kt)) hj (by rw [hj0]; exact (jMod_ne D).1)
    (by rw [hj0]; exact (jMod_ne D).2)
  let e := genuinePi1EqEquiv hCK
  refine ⟨g.toMonoidHom.comp (e.toMonoidHom.comp (genuinePi1Cover D.orb.CKu_to_CK)), ?_⟩
  have hf : ⇑(g.toMonoidHom.comp (e.toMonoidHom.comp (genuinePi1Cover D.orb.CKu_to_CK))) =
      g ∘ e ∘ genuinePi1Cover D.orb.CKu_to_CK := rfl
  rw [hf]
  exact hg.comp (e.toHomeomorph.isOpenEmbedding.comp
    (genuinePi1Cover_isOpenEmbedding D.orb.CKu_to_CK))

/-- The chosen embedding `π₁(†D^⊚) = π₁(C̲_K) ↪ π₁(C_{F_mod})`. -/
def piCKuToCmod : D.orb.CKu.genuinePi1 →* piCmod D := (exists_piCKu_emb D).choose

/-- **The natural morphism `†D^⊚ → †D^⊛`** (IUT I, Example 5.1 (i): "a "category-theoretic
version" of the natural morphism of hyperbolic orbicurves `C_K → C_{F_mod}`"), with
`†D^⊚ = B(π₁(C̲_K))⁰`. -/
def dCircToStar : OrbitObj D.orb.CKu.genuinePi1 ⥤ DStar D :=
  OrbitObj.mapFunctor (piCKuToCmod D) fun U hU => by
    rw [Subgroup.coe_map]
    exact (exists_piCKu_emb D).choose_spec.isOpenMap _ hU

end HodgeTheater

end Iut
