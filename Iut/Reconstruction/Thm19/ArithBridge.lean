/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.Cor37c
import CurvesJacobian.Galois.EtalePi1Open
import CurvesJacobian.Cusp.FieldChange
import ContinuousKummerTheory.Curve.Kummer
import ContinuousKummerTheory.Curve.InertiaZHat

/-!
# [AbsTopIII] Thm 1.9: the Galois model of the Kummer side and the arithmetic `Π_U`

[AbsTopIII] Thm 1.9 (`Topics in Absolute Anabelian Geometry III.txt` l.2109–2199) works with one
group `Π_U`: step (a) produces it with its cuspidal subgroups by Belyi cuspidalization
(`Reconstruction/Cusp/BelyiSpec.lean`, `Cor37c.lean`, on curves-jacobian's étale
`arithmeticExt Ω C hc`), steps (b)–(e) use the Kummer classes in `H¹(Π_U, Ẑ(1))`
(`Thm19/*.lean`, on the Galois model `Pi (curveGaloisData K hτ) = H ⧸ ⟨⟨S⟩⟩` of
continuous-kummer-theory). This file identifies the two, compatibly with the inertia groups,
for an affine hyperbolic curve `C` over a number field `K` (`U = X̄ ∖ {cusps}`, `hc`: a cusp
exists) and a coordinate `τ` of `X̄` with `U = chartOne τ` (`exists_coord`):

* `bridgeGen`: `Π_U ≃ₜ* π₁ᵉᵗ(U)` at the generic geometric point, from curves-jacobian
  `genericL_spec` (SGA 1 V.8.2; `S_U = S` by `SU_chartOne`);
* `bridgeSpec`: `U ≅ Spec Γ(U)`; `closureEquiv`: `K(X̄)^alg ≃ K(X̄_Ω)^alg` over
  `K(X̄) ≅ L₀ = arithFF`, and the change of field `fieldChangeIso` (curves-jacobian
  `Cusp/FieldChange`); `arithFiberIso`: the base point of `arithmeticExt`;
* **`piBridge : Π_U (Galois model) ≃ₜ* Π_U (arithmeticExt)`** and **`piBridge_mk`**: `h ∈ H` goes
  to `arithAction (σ h σ⁻¹)` (`arithAut`), the arithmetic Galois action of its transport;
* **`map_inertiaH_piBridge`**: the image of `I_W ∩ H` is `arithInertia (σ W)`;
* **`mem_cusps_iff_piBridge`**: the cuspidal subgroups of `arithmeticExt` are exactly the images
  of the `I_W ∩ H` for the places `W` over the cusps.

So the cusp data of (a) and the Kummer side of (b)–(e) live on one `Π_U` (the T1 bridge of
`Plans/MR9Plan.md`); no input beyond the pinned curves-jacobian is used.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian CurvesJacobian.Cusp AffOrbicurve KummerTheory Curve

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section FG

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- `π₁ᵉᵗ` along an isomorphism of schemes, to a prescribed geometric point. -/
def fgEquiv {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsIso f] {x₀ : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ Z} (h : x₀ ≫ f = η) : π₁ᵉᵗ(x₀) ≃ₜ* π₁ᵉᵗ(η) :=
  let φ := fundamentalGroupMap f h
  let m : π₁ᵉᵗ(x₀) ≃* π₁ᵉᵗ(η) := MulEquiv.ofBijective φ.toMonoidHom
    (fundamentalGroupMap_bijective_of_isIso f h)
  let e : π₁ᵉᵗ(x₀) ≃ₜ π₁ᵉᵗ(η) :=
    Continuous.homeoOfEquivCompactToT2 (f := m.toEquiv) φ.continuous_toFun
  { m with
    continuous_toFun := e.continuous_toFun
    continuous_invFun := e.continuous_invFun }

lemma fgEquiv_apply {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsIso f] {x₀ : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ Z} (h : x₀ ≫ f = η) (γ : π₁ᵉᵗ(x₀)) :
    fgEquiv f h γ = fundamentalGroupMap f h γ := rfl

end FG

section Bridge

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

local instance isIntegral_Xbar : IsIntegral C.Xbar := IsCurveOver.isIntegral K C.Xbar

/-- `K(X̄) ≅ L₀ ⊆ K(X̄_Ω)^alg`. -/
def ffEquiv : C.Xbar.functionField ≃+* arithFF Ω C hc.out :=
  RingEquiv.ofBijective _ (ffEmb Ω C hc.out).rangeRestrictField_bijective

/-- `K(X̄_Ω)^alg` as a `K(X̄)`-algebra (through `ffEmb`). -/
@[reducible] def algFF : Algebra C.Xbar.functionField (FFClosure (geomCurve Ω C)) :=
  ((algebraMap (arithFF Ω C hc.out) (FFClosure (geomCurve Ω C))).comp
    (ffEquiv Ω C).toRingHom).toAlgebra

attribute [local instance] algFF

lemma algebraMap_algFF (x : C.Xbar.functionField) :
    algebraMap C.Xbar.functionField (FFClosure (geomCurve Ω C)) x = ffEmb Ω C hc.out x := rfl

/-- `K(X̄)` as an algebra over itself through `L₀` (local). -/
@[reducible] def algFFL₀ : Algebra C.Xbar.functionField (arithFF Ω C hc.out) :=
  (ffEquiv Ω C).toRingHom.toAlgebra

attribute [local instance] algFFL₀

instance isScalarTower_algFF :
    IsScalarTower C.Xbar.functionField (arithFF Ω C hc.out) (FFClosure (geomCurve Ω C)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance isTorsionFree_algFF :
    Module.IsTorsionFree C.Xbar.functionField (FFClosure (geomCurve Ω C)) :=
  Module.isTorsionFree_iff_algebraMap_injective.2
    (algebraMap C.Xbar.functionField (FFClosure (geomCurve Ω C))).injective

instance isAlgClosure_algFF :
    IsAlgClosure C.Xbar.functionField (FFClosure (geomCurve Ω C)) := by
  haveI : Algebra.IsAlgebraic C.Xbar.functionField (arithFF Ω C hc.out) :=
    ⟨fun y => by
      obtain ⟨x, rfl⟩ := (ffEquiv Ω C).surjective y
      exact isAlgebraic_algebraMap x⟩
  exact ⟨inferInstance, Algebra.IsAlgebraic.trans C.Xbar.functionField (arithFF Ω C hc.out) _⟩

instance charZero_Xbar_functionField : CharZero C.Xbar.functionField :=
  charZero_of_injective_algebraMap (algebraMap K C.Xbar.functionField).injective

instance isGalois_algFF : _root_.IsGalois C.Xbar.functionField (FFClosure (geomCurve Ω C)) :=
  inferInstance

/-- An isomorphism `K(X̄)^alg ≃ K(X̄_Ω)^alg` over `K(X̄)`. -/
def closureEquiv : FFClosure C.Xbar ≃ₐ[C.Xbar.functionField] FFClosure (geomCurve Ω C) :=
  IsAlgClosure.equiv C.Xbar.functionField (FFClosure C.Xbar) (FFClosure (geomCurve Ω C))

lemma closureEquiv_algebraMap (x : C.Xbar.functionField) :
    closureEquiv Ω C (algebraMap C.Xbar.functionField (FFClosure C.Xbar) x) =
      ffEmb Ω C hc.out x :=
  (closureEquiv Ω C).commutes x

/-! ### The Galois model of the curve -/

/-- A coordinate `τ` with `U = chartOne τ` (`U ≠ X̄` has finite complement): the input `hU`
below. -/
theorem exists_coord : ∃ τ : C.Xbar.functionField, Transcendental K τ ∧
    C.U = chartOne K C.Xbar τ := by
  haveI : Nonempty C.U := C.nonempty.to_subtype
  refine exists_chartOne_eq K C.U C.cusps_finite fun h => ?_
  obtain ⟨x, hx⟩ := hc.out
  exact hx (by rw [h]; trivial)

variable {Ω C} {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)

local instance nonempty_U : Nonempty C.U := C.nonempty.to_subtype

lemma SU_congr {D : Pi1.Orbifold.GaloisData K (coordT τ)} {eL : C.Xbar.functionField ≃+* D.L}
    {U V : C.Xbar.Opens} (h : U = V) [Nonempty U] [Nonempty V] :
    SU D C.Xbar eL U = SU D C.Xbar eL V := by
  subst h
  rfl

include hU in
/-- The inertia elements at the places centred on `U` are the `S` of the Galois model. -/
lemma SU_eq_S :
    SU (curveGaloisData K hτ) C.Xbar (curveEquivL K hτ) C.U = (curveGaloisData K hτ).S :=
  (SU_congr hU).trans (SU_chartOne (curveGaloisData K hτ) C.Xbar (curveEquivL K hτ)
    (curveEquivL_algebraMap K hτ) le_rfl hτ)

include hU in
lemma genericL_spec_U :
    ((curveGaloisData K hτ).chartHom le_rfl
        (genericL (curveGaloisData K hτ) C.Xbar (curveEquivL K hτ) C.U)).ker =
      GaloisPi1.kernel (curveGaloisData K hτ).H (curveGaloisData K hτ).S ∧
    Function.Surjective ((curveGaloisData K hτ).chartHom le_rfl
        (genericL (curveGaloisData K hτ) C.Xbar (curveEquivL K hτ) C.U)) := by
  have := genericL_spec (curveGaloisData K hτ) C.Xbar (curveEquivL K hτ)
    (curveEquivL_algebraMap K hτ) le_rfl (τ := τ) rfl C.U C.cusps_finite
  rwa [SU_eq_S hτ hU] at this

/-- `Π_U ≃ π₁ᵉᵗ(U)` at the generic geometric point (SGA 1 V.8.2, curves-jacobian
`genericL_spec`). -/
def bridgeGen : Pi (curveGaloisData K hτ) ≃ₜ*
    π₁ᵉᵗ(specPoint (curveGaloisData K hτ).L (FFClosure C.Xbar) ≫
      genericL (curveGaloisData K hτ) C.Xbar (curveEquivL K hτ) C.U) :=
  (GaloisPi1.equivOfSurjective (curveGaloisData K hτ).H (curveGaloisData K hτ).isClosed_H
    (curveGaloisData K hτ).S _ ((curveGaloisData K hτ).continuous_chartHom le_rfl _)
    (genericL_spec_U hτ hU).2 (genericL_spec_U hτ hU).1).symm

lemma bridgeGen_mk (h : (curveGaloisData K hτ).H) :
    bridgeGen hτ hU (h : Pi (curveGaloisData K hτ)) =
      (curveGaloisData K hτ).chartHom le_rfl
        (genericL (curveGaloisData K hτ) C.Xbar (curveEquivL K hτ) C.U) h :=
  rfl

/-! ### From the generic point of `U` to the generic point of `Spec Γ(U)` -/

/-- The generic point `Spec K(X̄) ⟶ Spec Γ(U)`. -/
abbrev genSpec : Spec (.of C.Xbar.functionField) ⟶ Spec Γ(C.Xbar, C.U) :=
  Spec.map (C.Xbar.germToFunctionField C.U)

/-- The geometric generic point `Spec K(X̄)^alg ⟶ Spec Γ(U)`. -/
abbrev etaSpec : Spec (.of (FFClosure C.Xbar)) ⟶ Spec Γ(C.Xbar, C.U) :=
  Spec.map (CommRingCat.ofHom (algebraMap C.Xbar.functionField (FFClosure C.Xbar))) ≫
    genSpec (C := C)

lemma genericToOpen_isoSpec :
    genericToOpen C.U ≫ (isAffineOpen_U C hc.out).isoSpec.hom = genSpec (C := C) := by
  have := genericToOpen_homOfLE_isoSpec_hom (X := C.Xbar) (le_refl C.U) (isAffineOpen_U C hc.out)
  rwa [Scheme.homOfLE_rfl, Category.id_comp] at this

lemma specPoint_genericL :
    specPoint (curveGaloisData K hτ).L (FFClosure C.Xbar) ≫
        genericL (curveGaloisData K hτ) C.Xbar (curveEquivL K hτ) C.U =
      Spec.map (CommRingCat.ofHom (algebraMap C.Xbar.functionField (FFClosure C.Xbar))) ≫
        genericToOpen C.U := by
  rw [genericL, ← Category.assoc, specPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

lemma etaSpec_eq :
    (specPoint (curveGaloisData K hτ).L (FFClosure C.Xbar) ≫
        genericL (curveGaloisData K hτ) C.Xbar (curveEquivL K hτ) C.U) ≫
      (isAffineOpen_U C hc.out).isoSpec.hom = etaSpec (C := C) := by
  rw [specPoint_genericL, Category.assoc, genericToOpen_isoSpec]

/-- `π₁ᵉᵗ(U) ≃ π₁ᵉᵗ(Spec Γ(U))` at the geometric generic point. -/
def bridgeSpec : π₁ᵉᵗ(specPoint (curveGaloisData K hτ).L (FFClosure C.Xbar) ≫
      genericL (curveGaloisData K hτ) C.Xbar (curveEquivL K hτ) C.U) ≃ₜ*
    π₁ᵉᵗ(etaSpec (C := C)) :=
  fgEquiv (isAffineOpen_U C hc.out).isoSpec.hom (etaSpec_eq hτ)

/-! ### Change of the algebraically closed field and of the base point -/

/-- `K(X̄)^alg ≃ K(X̄_Ω)^alg` as a ring isomorphism. -/
abbrev σc : FFClosure C.Xbar ≃+* FFClosure (geomCurve Ω C) := (closureEquiv Ω C).toRingEquiv

lemma σc_algebraMap (x : C.Xbar.functionField) :
    σc (Ω := Ω) (C := C) (algebraMap C.Xbar.functionField (FFClosure C.Xbar) x) =
      algebraMap C.Xbar.functionField (FFClosure (geomCurve Ω C)) x :=
  (closureEquiv Ω C).commutes x

/-- The generic geometric point of `Spec Γ(U)` used by `arithAction`. -/
abbrev etaArith : Spec (.of (FFClosure (geomCurve Ω C))) ⟶ Spec Γ(C.Xbar, C.U) :=
  (specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫ genOpen Ω C C.U) ≫
    geomToSpec Ω C hc.out

lemma specIso_etaSpec :
    specIso (σc (Ω := Ω) (C := C)) ≫ etaSpec (C := C) = etaArith (Ω := Ω) (C := C) := by
  change _ = (specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫ genOpen Ω C C.U) ≫
    geomToSpec Ω C hc.out
  rw [← specMap_algebraMap_arithGenPt Ω C hc.out, etaSpec, genSpec, specIso, arithGenPt,
    ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  ext a
  change σc (algebraMap C.Xbar.functionField (FFClosure C.Xbar)
    ((C.Xbar.germToFunctionField C.U).hom a)) = _
  rw [σc_algebraMap, algebraMap_algFF]
  exact ffEmb_germ Ω C hc.out a

/-- **`Π_U` (Galois model of the Kummer side) `≃ₜ* Π_U` of `arithmeticExt`**. -/
def piBridge : Pi (curveGaloisData K hτ) ≃ₜ* (arithmeticExt Ω C hc.out).Pi :=
  (bridgeGen hτ hU).trans ((bridgeSpec hτ).trans
    ((autContinuousMulEquivOfIso (fieldChangeIso (σc (Ω := Ω) (C := C))
      (etaSpec (C := C)))).symm.trans
    ((fgEquiv (𝟙 _) ((Category.comp_id _).trans (specIso_etaSpec (Ω := Ω) (C := C)))).trans
      (autContinuousMulEquivOfIso (arithFiberIso Ω C hc.out)))))

/-! ### The bridge on elements -/

/-- Elements of `H` fix `K(X̄) ⊆ K(X̄)^alg`. -/
lemma fix_algebraMap (h : (curveGaloisData K hτ).H) (x : C.Xbar.functionField) :
    (h : FFClosure C.Xbar ≃ₐ[K₀ K (coordT τ)] FFClosure C.Xbar)
        (algebraMap C.Xbar.functionField (FFClosure C.Xbar) x) =
      algebraMap C.Xbar.functionField (FFClosure C.Xbar) x := by
  have h2 : (h : FFClosure C.Xbar ≃ₐ[K₀ K (coordT τ)] FFClosure C.Xbar) ∈
      (imageL (k := K) τ).fixingSubgroup := h.2
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h2 _ ((mem_imageL_iff _).2 ⟨x, rfl⟩)

/-- `h ∈ H` as an automorphism of `K(X̄)^alg` over `K(X̄)`. -/
def galFF (h : (curveGaloisData K hτ).H) :
    FFClosure C.Xbar ≃ₐ[C.Xbar.functionField] FFClosure C.Xbar :=
  AlgEquiv.ofRingEquiv
    (f := (h : FFClosure C.Xbar ≃ₐ[K₀ K (coordT τ)] FFClosure C.Xbar).toRingEquiv)
    (fix_algebraMap hτ h)

/-- `h ∈ H` transported to `K(X̄_Ω)^alg`, as an element of `Gal(K(X̄_Ω)^alg / L₀)`. -/
def arithAut (h : (curveGaloisData K hτ).H) :
    FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc.out] FFClosure (geomCurve Ω C) :=
  AlgEquiv.ofRingEquiv
    (f := ((σc (Ω := Ω) (C := C)).symm.trans
      (h : FFClosure C.Xbar ≃ₐ[K₀ K (coordT τ)] FFClosure C.Xbar).toRingEquiv).trans σc)
    fun y => by
      obtain ⟨x, rfl⟩ := (ffEquiv Ω C).surjective y
      change σc ((h : FFClosure C.Xbar ≃ₐ[K₀ K (coordT τ)] FFClosure C.Xbar)
        (σc.symm (ffEmb Ω C hc.out x))) = ffEmb Ω C hc.out x
      rw [← algebraMap_algFF, ← σc_algebraMap, RingEquiv.symm_apply_apply, fix_algebraMap]

lemma arithAut_apply (h : (curveGaloisData K hτ).H) (y : FFClosure (geomCurve Ω C)) :
    arithAut hτ h y = σc (Ω := Ω) (C := C)
      ((h : FFClosure C.Xbar ≃ₐ[K₀ K (coordT τ)] FFClosure C.Xbar)
        ((σc (Ω := Ω) (C := C)).symm y)) :=
  rfl

set_option maxHeartbeats 1600000 in
-- the composite of five isomorphisms of fundamental groups is unfolded step by step
/-- **The bridge on elements**: `h ∈ H` goes to the arithmetic Galois action of its transport
`σ h σ⁻¹` to `K(X̄_Ω)^alg`. -/
theorem piBridge_mk (h : (curveGaloisData K hτ).H) :
    piBridge (Ω := Ω) hτ hU (h : Pi (curveGaloisData K hτ)) =
      arithAction Ω C hc.out (arithAut hτ h) := by
  have hσ := σc_algebraMap (Ω := Ω) (C := C)
  have e1 : bridgeGen hτ hU (h : Pi (curveGaloisData K hτ)) =
      galoisAction C.Xbar.functionField (genericToOpen C.U) (specPoint_genericL hτ).symm
        (galFF hτ h) := by
    rw [bridgeGen_mk, Pi1.Orbifold.GaloisData.chartHom_apply]
    exact galoisAction_eq_of_apply_eq _ _ _ _ _ _ _ fun _ => rfl
  have e2 : bridgeSpec hτ (galoisAction C.Xbar.functionField (genericToOpen C.U)
      (specPoint_genericL hτ).symm (galFF hτ h)) =
      galoisAction C.Xbar.functionField (genSpec (C := C)) rfl (galFF hτ h) :=
    fundamentalGroupMap_galoisAction_eq _ _ _ (genericToOpen_isoSpec (C := C)) _ _ _ _
  have e3 : (autContinuousMulEquivOfIso (fieldChangeIso (σc (Ω := Ω) (C := C))
      (etaSpec (C := C)))).symm
        (galoisAction C.Xbar.functionField (genSpec (C := C)) rfl (galFF hτ h)) =
      galoisAction C.Xbar.functionField (genSpec (C := C))
        (specAlgebraMap_comp_fieldChange σc (etaSpec (C := C)) C.Xbar.functionField hσ
          (genSpec (C := C)) rfl)
        ((galConj σc C.Xbar.functionField hσ).symm (galFF hτ h)) := by
    rw [ContinuousMulEquiv.symm_apply_eq, galoisAction_fieldChange σc (etaSpec (C := C))
      C.Xbar.functionField hσ (genSpec (C := C)) rfl, MulEquiv.apply_symm_apply]
  have h'' : Spec.map (CommRingCat.ofHom
      (algebraMap C.Xbar.functionField (FFClosure (geomCurve Ω C)))) ≫ genSpec (C := C) =
        etaArith (Ω := Ω) (C := C) :=
    (specAlgebraMap_comp_fieldChange σc (etaSpec (C := C)) C.Xbar.functionField hσ
      (genSpec (C := C)) rfl).trans (specIso_etaSpec (Ω := Ω) (C := C))
  have e4 : fgEquiv (𝟙 _) ((Category.comp_id _).trans (specIso_etaSpec (Ω := Ω) (C := C)))
      (galoisAction C.Xbar.functionField (genSpec (C := C))
        (specAlgebraMap_comp_fieldChange σc (etaSpec (C := C)) C.Xbar.functionField hσ
          (genSpec (C := C)) rfl)
        ((galConj σc C.Xbar.functionField hσ).symm (galFF hτ h))) =
      galoisAction C.Xbar.functionField (genSpec (C := C)) h''
        ((galConj σc C.Xbar.functionField hσ).symm (galFF hτ h)) :=
    fundamentalGroupMap_galoisAction_eq _ _ _ (Category.comp_id _) _ _ _ _
  have e5 : galoisAction C.Xbar.functionField (genSpec (C := C)) h''
        ((galConj σc C.Xbar.functionField hσ).symm (galFF hτ h)) =
      galoisAction (arithFF Ω C hc.out) (arithGenPt Ω C hc.out)
        (specMap_algebraMap_arithGenPt Ω C hc.out) (arithAut hτ h) :=
    galoisAction_eq_of_apply_eq _ _ _ _ _ _ _ fun _ => rfl
  rw [piBridge, ContinuousMulEquiv.trans_apply, e1, ContinuousMulEquiv.trans_apply, e2,
    ContinuousMulEquiv.trans_apply, e3, ContinuousMulEquiv.trans_apply, e4, e5]
  rfl

attribute [irreducible] piBridge

/-! ### Inertia groups -/

/-- **Inertia under the bridge**: `h ∈ H` lies in the inertia group of `W ⊆ K(X̄)^alg` iff its
transport lies in the inertia group of `σ(W) ⊆ K(X̄_Ω)^alg`. -/
lemma arithAut_mem_inertia_iff (h : (curveGaloisData K hτ).H)
    (W : ValuationSubring (FFClosure C.Xbar)) :
    arithAut (Ω := Ω) hτ h ∈ GaloisPi1.inertia
        (W.comap ((σc (Ω := Ω) (C := C)).symm : FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) ↔
      (h : FFClosure C.Xbar ≃ₐ[K₀ K (coordT τ)] FFClosure C.Xbar) ∈ GaloisPi1.inertia W := by
  simp only [GaloisPi1.inertia, Set.mem_setOf_eq]
  have key : ∀ x : FFClosure (geomCurve Ω C),
      (W.comap ((σc (Ω := Ω) (C := C)).symm :
        FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)).valuation x < 1 ↔
        W.valuation ((σc (Ω := Ω) (C := C)).symm x) < 1 := by
    intro x
    rw [valuation_lt_one_iff_inv, valuation_lt_one_iff_inv, ValuationSubring.mem_comap]
    simp
  constructor
  · intro hg a ha
    have := hg (σc a) (by simpa [ValuationSubring.mem_comap] using ha)
    rw [key, arithAut_apply, map_sub, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
      at this
    exact this
  · intro hh a ha
    rw [key, arithAut_apply, map_sub, RingEquiv.symm_apply_apply]
    exact hh _ ha

/-- An element of `Gal(K(X̄_Ω)^alg / L₀)` transported back to `K(X̄)^alg`. -/
def hOf (g : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc.out] FFClosure (geomCurve Ω C)) :
    FFClosure C.Xbar ≃ₐ[K₀ K (coordT τ)] FFClosure C.Xbar :=
  AlgEquiv.ofRingEquiv (f := ((σc (Ω := Ω) (C := C)).trans g.toRingEquiv).trans σc.symm)
    fun c => by
      obtain ⟨x, hx⟩ : (c : FFClosure C.Xbar) ∈
          Set.range (algebraMap C.Xbar.functionField (FFClosure C.Xbar)) :=
        K₀_le_imageK (k := K) τ c.2
      change σc.symm (g (σc (c : FFClosure C.Xbar))) = c
      rw [← hx, σc_algebraMap, algebraMap_algFF]
      have hg : g (ffEmb Ω C hc.out x) = ffEmb Ω C hc.out x :=
        g.commutes ⟨_, x, rfl⟩
      rw [hg, ← algebraMap_algFF, ← σc_algebraMap, RingEquiv.symm_apply_apply]

lemma hOf_mem (g : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc.out] FFClosure (geomCurve Ω C)) :
    hOf (τ := τ) g ∈ (curveGaloisData K hτ).H := by
  change hOf g ∈ (imageL (k := K) τ).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := (mem_imageL_iff _).1 hy
  change σc.symm (g (σc (algebraMap C.Xbar.functionField (FFClosure C.Xbar) x))) = _
  rw [σc_algebraMap, algebraMap_algFF]
  have hg : g (ffEmb Ω C hc.out x) = ffEmb Ω C hc.out x := g.commutes ⟨_, x, rfl⟩
  rw [hg, ← algebraMap_algFF, ← σc_algebraMap, RingEquiv.symm_apply_apply]

lemma arithAut_hOf
    (g : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc.out] FFClosure (geomCurve Ω C)) :
    arithAut hτ ⟨hOf g, hOf_mem hτ g⟩ = g := by
  ext y
  change σc (σc.symm (g (σc (σc.symm y)))) = g y
  simp

lemma piBridge_comp_mk (h : (curveGaloisData K hτ).H) :
    ((piBridge (Ω := Ω) hτ hU).toMulEquiv.toMonoidHom.comp
        (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ).H
          (curveGaloisData K hτ).S))) h = arithAction Ω C hc.out (arithAut hτ h) :=
  piBridge_mk hτ hU h

/-- **[AbsTopIII] Thm 1.9 (a)/(b), the cuspidal inertia groups under the bridge**: the image in
`Π_U` (Galois model) of the inertia group `I_W ∩ H` of a place `W ⊆ K(X̄)^alg` is carried by
`piBridge` to the inertia subgroup `arithInertia (σ W)` of `arithmeticExt`. -/
theorem map_inertiaH_piBridge (W : ValuationSubring (FFClosure C.Xbar)) :
    ((inertiaH (curveGaloisData K hτ) W).map
        (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ).H
          (curveGaloisData K hτ).S))).map
        (piBridge (Ω := Ω) hτ hU).toMulEquiv.toMonoidHom =
      arithInertia Ω C hc.out
        (W.comap ((σc (Ω := Ω) (C := C)).symm :
          FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) := by
  rw [Subgroup.map_map, arithInertia]
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    change piBridge hτ hU (h : Pi (curveGaloisData K hτ)) ∈ _
    rw [piBridge_mk]
    exact Subgroup.subset_closure ⟨arithAut hτ h, (arithAut_mem_inertia_iff hτ h W).2 hh, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨⟨hOf g, hOf_mem hτ g⟩, ?_, ?_⟩
    · exact (arithAut_mem_inertia_iff (Ω := Ω) hτ ⟨hOf g, hOf_mem hτ g⟩ W).1
        (by rw [arithAut_hOf]; exact hg)
    · rw [piBridge_comp_mk, arithAut_hOf]

lemma comap_σc_comap (W : ValuationSubring (FFClosure (geomCurve Ω C))) :
    (W.comap ((σc (Ω := Ω) (C := C)) : FFClosure C.Xbar →+* FFClosure (geomCurve Ω C))).comap
      ((σc (Ω := Ω) (C := C)).symm : FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar) = W := by
  ext x
  simp [ValuationSubring.mem_comap]

/-- **The cuspidal subgroups of `arithmeticExt` in the Galois model**: every cuspidal subgroup
of `Π_U` (the input of [AbsTopIII] Thm 1.9 (a)) is the image under `piBridge` of the inertia
group `I_W ∩ H` of a place `W ⊆ K(X̄)^alg` over a cusp, and conversely. -/
theorem mem_cusps_iff_piBridge (I : Subgroup (arithmeticExt Ω C hc.out).Pi) :
    I ∈ (arithmeticExt Ω C hc.out).cusps ↔
      ∃ W : ValuationSubring (FFClosure C.Xbar),
        IsCuspPlace Ω C hc.out (W.comap ((σc (Ω := Ω) (C := C)).symm :
          FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) ∧
        I = ((inertiaH (curveGaloisData K hτ) W).map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ).H
            (curveGaloisData K hτ).S))).map (piBridge (Ω := Ω) hτ hU).toMulEquiv.toMonoidHom := by
  constructor
  · intro hI
    obtain ⟨W', hW', rfl⟩ := exists_isCuspPlace_eq_arithInertia Ω C hc.out hI
    refine ⟨W'.comap ((σc (Ω := Ω) (C := C)) : FFClosure C.Xbar →+* FFClosure (geomCurve Ω C)),
      ?_, ?_⟩
    · rwa [comap_σc_comap]
    · rw [map_inertiaH_piBridge, comap_σc_comap]
  · rintro ⟨W, hW, rfl⟩
    rw [map_inertiaH_piBridge]
    refine ⟨_, ⟨_, hW.1, fun h => hW.2 ((isCentredOn_geomOpen_iff Ω C hc.out _).1 h).2, rfl⟩,
      1, ?_⟩
    rw [← arithInertia_eq_map_geom Ω C hc.out hW.1]
    ext x
    simp

end Bridge

end Iut.Reconstruction.Thm19
