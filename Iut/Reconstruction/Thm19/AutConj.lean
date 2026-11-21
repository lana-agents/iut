/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFJInvariant
import Iut.Reconstruction.Thm19.NFCanon
import CurvesJacobian.CuspChar.FinalW

/-!
# Automorphisms of `Π_{E ∖ {O}}` act on `G_K` by conjugation by `σ` with `σ(j) = j` (MR9)

[AbsTopIII] Thm 1.9 (`Topics in Absolute Anabelian Geometry III.txt` l.2109–2199), functorial
form (session v/w, `Thm19/NFConstEquiv.lean`, `Thm19/NFJInvariant.lean`): an automorphism `Φ` of
the arithmetic fundamental group of `X = E ∖ {O}` induces a field automorphism `σ` of
`k̄ = ℚ̄` with `ψ = conj σ` on `G_K` and `σ(j(E)) = j(E)`. This file packages it for an automorphism
of the Galois model `Π_X = H_L ⧸ ⟨⟨S⟩⟩` (`Pi (curveGaloisData K hτ)`) preserving the geometric
subgroup:

* generic: `autG` (the automorphism of `G_K` induced by an automorphism of `Π_U` preserving
  `Δ_U`; continuous since `Π_U ↠ G_K` is a quotient map of compact groups), **`isoOfAut`** (the
  isomorphism of cuspidal extensions, [AbsTopI] Lemma 4.5 (v), curves-jacobian
  `arithmeticExtIso'`) and **`gkIso_isoOfAut`** (`gkIso` is the induced map on `Gal(k̄ / K)`);
* **`exists_conj_of_aut`**: for `X = E ∖ {O}` (`hypCurveE E`), every continuous automorphism of
  `Π_X` preserving `Δ_X` acts on `Gal(k̄ / K)` as conjugation by a field automorphism `σ` of `k̄`
  with `σ(j(E)) = j(E)`. Inputs: `BelyiCuspSpec` (MR8), `RelIsomDGC.Exists K` (MR7), a `K`-rational
  point `σ₀` of `Ē`.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian Topology

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

/-! ### The induced automorphism of `G_K` -/

section AutG

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

/-- The kernel of `Π_U ↠ G_K` is mapped onto itself by `a`. -/
lemma map_ker_pr (a : (arithmeticExt Ω C hc).Pi ≃ₜ* (arithmeticExt Ω C hc).Pi)
    (ha : ∀ x, (arithmeticExt Ω C hc).pr (a x) = 1 ↔ (arithmeticExt Ω C hc).pr x = 1) :
    ((arithmeticExt Ω C hc).pr : (arithmeticExt Ω C hc).Pi →* (arithmeticExt Ω C hc).G).ker.map
        (a.toMulEquiv : (arithmeticExt Ω C hc).Pi →* (arithmeticExt Ω C hc).Pi) =
      ((arithmeticExt Ω C hc).pr : (arithmeticExt Ω C hc).Pi →* (arithmeticExt Ω C hc).G).ker := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (ha x).2 hx
  · intro hy
    refine ⟨a.symm y, (ha _).1 ?_, a.apply_symm_apply y⟩
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact hy

/-- The automorphism of `G_K` induced by `a`, as a group isomorphism. -/
def autGMul (a : (arithmeticExt Ω C hc).Pi ≃ₜ* (arithmeticExt Ω C hc).Pi)
    (ha : ∀ x, (arithmeticExt Ω C hc).pr (a x) = 1 ↔ (arithmeticExt Ω C hc).pr x = 1) :
    (arithmeticExt Ω C hc).G ≃* (arithmeticExt Ω C hc).G :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (arithmeticExt Ω C hc).pr_surjective).symm.trans
    ((QuotientGroup.congr _ _ a.toMulEquiv (map_ker_pr hc a ha)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (arithmeticExt Ω C hc).pr_surjective))

lemma autGMul_pr (a : (arithmeticExt Ω C hc).Pi ≃ₜ* (arithmeticExt Ω C hc).Pi)
    (ha : ∀ x, (arithmeticExt Ω C hc).pr (a x) = 1 ↔ (arithmeticExt Ω C hc).pr x = 1)
    (x : (arithmeticExt Ω C hc).Pi) :
    autGMul hc a ha ((arithmeticExt Ω C hc).pr x) = (arithmeticExt Ω C hc).pr (a x) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective _
      (arithmeticExt Ω C hc).pr_surjective).symm ((arithmeticExt Ω C hc).pr x) =
      (x : _ ⧸ ((arithmeticExt Ω C hc).pr :
        (arithmeticExt Ω C hc).Pi →* (arithmeticExt Ω C hc).G).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [autGMul, MulEquiv.trans_apply, h1]
  rfl

/-- `Π_U ↠ G_K` is a quotient map (compact to Hausdorff). -/
lemma isQuotientMap_pr : IsQuotientMap (arithmeticExt Ω C hc).pr :=
  IsClosedMap.isQuotientMap (arithmeticExt Ω C hc).pr.continuous.isClosedMap
    (arithmeticExt Ω C hc).pr.continuous (arithmeticExt Ω C hc).pr_surjective

/-- **The automorphism of `G_K` induced by `a`** (`a` preserves `Δ_U`). -/
def autG (a : (arithmeticExt Ω C hc).Pi ≃ₜ* (arithmeticExt Ω C hc).Pi)
    (ha : ∀ x, (arithmeticExt Ω C hc).pr (a x) = 1 ↔ (arithmeticExt Ω C hc).pr x = 1) :
    (arithmeticExt Ω C hc).G ≃ₜ* (arithmeticExt Ω C hc).G where
  toMulEquiv := autGMul hc a ha
  continuous_toFun := by
    refine (isQuotientMap_pr hc).continuous_iff.2 ?_
    have e : (autGMul hc a ha) ∘ (arithmeticExt Ω C hc).pr =
        (arithmeticExt Ω C hc).pr ∘ a := funext (autGMul_pr hc a ha)
    change Continuous ((autGMul hc a ha) ∘ (arithmeticExt Ω C hc).pr)
    rw [e]
    exact (arithmeticExt Ω C hc).pr.continuous.comp a.continuous
  continuous_invFun := by
    refine (isQuotientMap_pr hc).continuous_iff.2 ?_
    have e : (autGMul hc a ha).symm ∘ (arithmeticExt Ω C hc).pr =
        (arithmeticExt Ω C hc).pr ∘ a.symm := funext fun x => by
      rw [Function.comp_apply, MulEquiv.symm_apply_eq, Function.comp_apply, autGMul_pr,
        ContinuousMulEquiv.apply_symm_apply]
    change Continuous ((autGMul hc a ha).symm ∘ (arithmeticExt Ω C hc).pr)
    rw [e]
    exact (arithmeticExt Ω C hc).pr.continuous.comp a.symm.continuous

lemma autG_pr (a : (arithmeticExt Ω C hc).Pi ≃ₜ* (arithmeticExt Ω C hc).Pi)
    (ha : ∀ x, (arithmeticExt Ω C hc).pr (a x) = 1 ↔ (arithmeticExt Ω C hc).pr x = 1)
    (x : (arithmeticExt Ω C hc).Pi) :
    autG hc a ha ((arithmeticExt Ω C hc).pr x) = (arithmeticExt Ω C hc).pr (a x) :=
  autGMul_pr hc a ha x

/-- **The isomorphism of cuspidal extensions defined by `a`** ([AbsTopI] Lemma 4.5 (v):
cuspidal inertia is preserved, curves-jacobian `arithmeticExtIso'`). -/
def isoOfAut (a : (arithmeticExt Ω C hc).Pi ≃ₜ* (arithmeticExt Ω C hc).Pi)
    (ha : ∀ x, (arithmeticExt Ω C hc).pr (a x) = 1 ↔ (arithmeticExt Ω C hc).pr x = 1) :
    (arithmeticExt Ω C hc).Iso (arithmeticExt Ω C hc) :=
  CuspChar.arithmeticExtIso' a (autG hc a ha) fun x => (autG_pr hc a ha x).symm

lemma isoOfAut_g (a : (arithmeticExt Ω C hc).Pi ≃ₜ* (arithmeticExt Ω C hc).Pi)
    (ha : ∀ x, (arithmeticExt Ω C hc).pr (a x) = 1 ↔ (arithmeticExt Ω C hc).pr x = 1) :
    (isoOfAut hc a ha).g = autG hc a ha :=
  rfl

end AutG

/-! ### Automorphisms of the Galois model -/

section Bridge

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)

/-- An automorphism `αX` of the Galois model `Π_U`, transported along `piBridge`. -/
def bridgeAut (αX : Pi (curveGaloisData K hτ) ≃ₜ* Pi (curveGaloisData K hτ)) :
    (arithmeticExt Ω C hc.out).Pi ≃ₜ* (arithmeticExt Ω C hc.out).Pi :=
  (piBridge (Ω := Ω) hτ hU).symm.trans (αX.trans (piBridge (Ω := Ω) hτ hU))

lemma bridgeAut_piBridge (αX : Pi (curveGaloisData K hτ) ≃ₜ* Pi (curveGaloisData K hτ))
    (p : Pi (curveGaloisData K hτ)) :
    bridgeAut hτ hU αX (piBridge (Ω := Ω) hτ hU p) = piBridge (Ω := Ω) hτ hU (αX p) := by
  rw [bridgeAut, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.symm_apply_apply]

lemma bridgeAut_ker (αX : Pi (curveGaloisData K hτ) ≃ₜ* Pi (curveGaloisData K hτ))
    (hαX : ∀ p, piToGk (curveGaloisData K hτ) (αX p) = 1 ↔ piToGk (curveGaloisData K hτ) p = 1)
    (x : (arithmeticExt Ω C hc.out).Pi) :
    (arithmeticExt Ω C hc.out).pr (bridgeAut hτ hU αX x) = 1 ↔
      (arithmeticExt Ω C hc.out).pr x = 1 := by
  obtain ⟨p, rfl⟩ := (piBridge (Ω := Ω) hτ hU).surjective x
  rw [bridgeAut_piBridge]
  change projGk Ω C hc.out (piBridge hτ hU (αX p)) = 1 ↔ projGk Ω C hc.out (piBridge hτ hU p) = 1
  rw [projGk_piBridge_eq_one_iff, projGk_piBridge_eq_one_iff]
  exact hαX p

/-- **The isomorphism of cuspidal extensions defined by an automorphism `αX` of the Galois model**
preserving `Δ_U`. -/
def isoOfAutX (αX : Pi (curveGaloisData K hτ) ≃ₜ* Pi (curveGaloisData K hτ))
    (hαX : ∀ p, piToGk (curveGaloisData K hτ) (αX p) = 1 ↔ piToGk (curveGaloisData K hτ) p = 1) :
    (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω C hc.out) :=
  isoOfAut hc.out (bridgeAut hτ hU αX) (bridgeAut_ker hτ hU αX hαX)

/-- **`gkIso` of `isoOfAutX αX` is the map induced by `αX` on `Gal(k̄ / K)`.** -/
theorem gkIso_isoOfAutX (αX : Pi (curveGaloisData K hτ) ≃ₜ* Pi (curveGaloisData K hτ))
    (hαX : ∀ p, piToGk (curveGaloisData K hτ) (αX p) = 1 ↔ piToGk (curveGaloisData K hτ) p = 1)
    (p : Pi (curveGaloisData K hτ)) :
    gkIso hτ hU hτ hU (isoOfAutX (Ω := Ω) hτ hU αX hαX) (piToGk (curveGaloisData K hτ) p) =
      piToGk (curveGaloisData K hτ) (αX p) := by
  apply (gkBridge (Ω := Ω) hτ hU).injective
  have h : ∀ g, gkBridge (Ω := Ω) hτ hU
      (gkIso hτ hU hτ hU (isoOfAutX (Ω := Ω) hτ hU αX hαX) g) =
      (isoOfAutX (Ω := Ω) hτ hU αX hαX).g (gkBridge (Ω := Ω) hτ hU g) := fun g =>
    (gkBridge (Ω := Ω) hτ hU).apply_symm_apply _
  rw [h, gkBridge_piToGk, gkBridge_piToGk, isoOfAutX, isoOfAut_g]
  change autG hc.out _ _ ((arithmeticExt Ω C hc.out).pr (piBridge hτ hU p)) =
    (arithmeticExt Ω C hc.out).pr (piBridge hτ hU (αX p))
  rw [autG_pr, bridgeAut_piBridge]

end Bridge

/-! ### `X = E ∖ {O}`: conjugation by `σ` with `σ(j) = j` -/

section J

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  [hc : Fact ((hypCurveE E).U : Set (hypCurveE E).Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic
  Thm19.isAlgClosed_algebraicClosure Thm19.isFunctionField_fnf

variable (Ω) in
/-- `isoOfAutX` for `X = E ∖ {O}`. -/
abbrev isoE (αX : Pi (curveGaloisData K (transcendental_xN E)) ≃ₜ*
      Pi (curveGaloisData K (transcendental_xN E)))
    (hαX : ∀ p, piToGk (curveGaloisData K (transcendental_xN E)) (αX p) = 1 ↔
      piToGk (curveGaloisData K (transcendental_xN E)) p = 1) :
    (arithmeticExt Ω (hypCurveE E) hc.out).Iso (arithmeticExt Ω (hypCurveE E) hc.out) :=
  @isoOfAutX K _ _ Ω _ _ _ _ _ (hypCurveE E) hc (xN E) (transcendental_xN E) _
    (XE_eq_chartOne E) αX hαX

set_option maxRecDepth 20000 in
-- matching `gkIso` of `isoE` with that of the let-bound `Φ` unfolds deep instance terms
/-- **Automorphisms of `Π_{E ∖ {O}}` act on `G_K` by conjugation by `σ` with `σ(j) = j`**
([AbsTopIII] Thm 1.9, functoriality; `gkIso_eq_conj`, `nfConstEquiv_fix_j`). -/
theorem exists_conj_of_aut (hS : BelyiCuspSpec Ω (hypCurveE E) hc.out)
    (σ₀ : Spec (CommRingCat.of K) ⟶ (hypCurveE E).Xbar)
    (hσ₀ : σ₀ ≫ ((hypCurveE E).Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
    (hDGC : RelIsomDGC.Exists K)
    (αX : Pi (curveGaloisData K (transcendental_xN E)) ≃ₜ*
      Pi (curveGaloisData K (transcendental_xN E)))
    (hαX : ∀ p, piToGk (curveGaloisData K (transcendental_xN E)) (αX p) = 1 ↔
      piToGk (curveGaloisData K (transcendental_xN E)) p = 1) :
    ∃ σ : kbar K (FFClosure (curveE E)) ≃+* kbar K (FFClosure (curveE E)),
      σ (algebraMap K (kbar K (FFClosure (curveE E))) E.j) =
        algebraMap K (kbar K (FFClosure (curveE E))) E.j ∧
      ∀ (p : Pi (curveGaloisData K (transcendental_xN E))) (z : kbar K (FFClosure (curveE E))),
        piToGk (curveGaloisData K (transcendental_xN E)) (αX p) z =
          σ (piToGk (curveGaloisData K (transcendental_xN E)) p (σ.symm z)) := by
  let Φ := isoE E Ω αX hαX
  let N := nfModelNF (curveGaloisData K (transcendental_xN E))
  refine ⟨sigmaE E Φ hS σ₀ hσ₀ hDGC N, nfConstEquiv_fix_j E hS σ₀ hσ₀ hDGC N, fun p z => ?_⟩
  have h1 := @gkIso_isoOfAutX K _ _ Ω _ _ _ _ _ (hypCurveE E) hc (xN E) (transcendental_xN E) _
    (XE_eq_chartOne E) αX hαX p
  have h2 := @gkIso_eq_conj K _ _ Ω _ _ _ _ _ (hypCurveE E) hc K _ _ Ω _ _ _ _ _ (hypCurveE E) hc
    (xN E) (transcendental_xN E) _ (XE_eq_chartOne E) (xN E) (transcendental_xN E) _
    (XE_eq_chartOne E) Φ _ _ _ _ hS hS σ₀ hσ₀ (curveGenus_hypCurveE_ne E) σ₀ hσ₀
    (curveGenus_hypCurveE_ne E) hDGC hDGC N N (piToGk (curveGaloisData K (transcendental_xN E)) p)
    z
  exact (DFunLike.congr_fun h1 z).symm.trans h2

end J

end Iut.Reconstruction.Thm19
