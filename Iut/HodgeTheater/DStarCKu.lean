/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.DStarConj
import Iut.HodgeTheater.ExtendAut
import Iut.Multiradial.Theater.CuspGalConst

/-!
# Semi-absolute conjugacy for `π₁(C̲_K)` (MR9 session z)

`HodgeTheater/DStarConj.lean` proves `CKSemiAbsConj` for the `K`-core `C_K`: an automorphism of
`π₁(C_K)` preserving `Δ_{C_K}` acts on the image in `Gal(F̄/F_mod)` by conjugation by an element
of `Gal(F̄/F_mod)` ([AbsTopIII] Thm 1.9 for `X_K = E_K ∖ {O}`). This file proves the same for
`π₁(C̲_K)` (IUT I, Def. 3.1 (d): `C̲_K → C_K` the finite étale cover of type `(1, ℓ-tors)^±`), with
no new input, by **extending** semi-absolute automorphisms of the open subgroup
`π₁(C̲_K) ⊆ π₁(C_K)` to `π₁(C_K)` (`ExtendAut.exists_extend`, from the self-commensuration
`piCmod_selfComm` of `π₁(C_{F_mod})`, i.e. the coricity of `C_K`, IUT I Rem. 3.1.7 (i), [CanLift]
Prop. 2.7):

* `genuinePi1EqEquiv_cover`, **`exists_genuinePi1Cover_eq_mkC`**: the image of the genuine `π₁`
  of a `±`-model orbicurve covering `C = (E ∖ {O})/±1` meets every class of `Gal(Ω / k(x))` modulo
  automorphisms fixing `k̄` (`Multiradial/Theater/CuspGalConst.lean`);
* `piCKuCmod` (`π₁(C̲_K) ↪ π₁(C_K) ↪ π₁(C_{F_mod})`), **`exists_piCKu_resK`**,
  **`exists_piCKu_pr`**: `π₁(C̲_K)` and `π₁(C_K)` have the same image in `Gal(F̄/F_mod)`;
* `CKuStrictSemiAbs` (named statement: [AbsTopI] Cor. 2.8 (ii) for `C̲_K`), `CKuSemiAbsConj`;
* **`ckuSemiAbsConj`**: `CKuSemiAbsConj D` from the inputs of `ckSemiAbsConj` (`BelyiCuspSpec`,
  `RelIsomDGC.Exists`) and of `piCmod_selfComm` (`RelIsomDGC.Exists` for all number fields, the
  `j`-condition `hj`);
* **`hAbsCKu_of_strict`**, **`piCKu_aut_eq_conj`**: under `CKuStrictSemiAbs`, every continuous
  automorphism of `π₁(C̲_K)` is the restriction (along `piCKuCmod`) of conjugation by a unique
  element of `π₁(C_{F_mod})` (which then normalises the image of `π₁(C̲_K)`).
-/

noncomputable section

namespace Iut

namespace HodgeTheater

open CategoryTheory NumberField Frobenioid CurvesJacobian CurvesJacobian.Cusp
  Iut.Reconstruction Iut.Reconstruction.HemiGenuine Iut.Reconstruction.HemiPiXChar
  Iut.Reconstruction.Thm19
  Iut.Anabelian AlgebraicGeometry Belyi Belyi.Anabelian Topology KummerTheory KummerTheory.Curve
  Pi1 Pi1.Orbifold WeilCurves.FunctionField CurvesJacobian.Kummer
  CurvesJacobian.LocAn Pi1.Profinite

attribute [local instance low] Classical.propDecidable

set_option linter.unusedSectionVars false

/-! ### The genuine `π₁` of a cover of `C = (E ∖ {O}) / ±1` -/

section Cover

variable {k : Type} [Field k] [CharZero k]

/-- Transport of the map induced by a cover along an equality of targets. -/
lemma genuinePi1EqEquiv_cover {X Y Y' : Orbicurve k} (h : Y = Y') (c : Orbicurve.Cover X Y)
    (x : X.genuinePi1) : genuinePi1EqEquiv h (genuinePi1Cover c x) = genuinePi1Cover (h ▸ c) x := by
  subst h
  rfl

/-- **The image of `π₁(X)` for a `±`-model orbicurve `X` covering `C = (E ∖ {O}) / ±1`**: for every
`σ ∈ Gal(Ω / k(x))` some `δ` fixing every element algebraic over `k` has `mkC (δσ)` in the image
(`exists_fixAlg_mul_mem_Hgp`). -/
theorem exists_genuinePi1Cover_eq_mkC {E : WeierstrassCurve k} [E.IsElliptic] {X : Orbicurve k}
    (c : Orbicurve.Cover X (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)))
    (hpm : X.pm = true) (hℓ : X.level ≠ 0) (hcard : Nat.card X.torsion = X.level ^ 2)
    (σ : Genuine.Gal E) :
    ∃ (x : X.genuinePi1) (δ : Genuine.Gal E), (∀ z, IsAlgebraic k z → δ z = z) ∧
      genuinePi1Cover c x = mkC E (δ * σ) := by
  rcases X with @⟨E', hE', ℓ, M, pm⟩
  rcases c with ⟨hE, n, hn, hmul, hM, hpm'⟩
  change E' = E at hE
  subst hE
  change pm = true at hpm
  subst hpm
  change ℓ ≠ 0 at hℓ
  change n * 1 = ℓ at hmul
  obtain ⟨δ, hδ, hmem⟩ := Multiradial.Theater.exists_fixAlg_mul_mem_Hgp E' hℓ hcard M σ
  refine ⟨(QuotientGroup.mk ⟨δ * σ, hmem⟩ :
    Genuine.Hgp E' ℓ M true ⧸ GaloisPi1.kernel (Genuine.Hgp E' ℓ M true) (Genuine.SgenC E' ℓ M)),
    δ, hδ, ?_⟩
  have hM' : ∀ P ∈ M, n • P ∈ (⊥ : AddSubgroup E'.toAffine.Point) := hM
  have hc := Genuine.compatible_divSys_of_charZero E'
  have hle : Genuine.Hgp E' ℓ M true ≤ Genuine.Hgp E' 1 ⊥ true :=
    Genuine.Hgp_le E' hc hn hmul hM' fun h => h
  have hS : Genuine.SgenC E' ℓ M ⊆ Genuine.SgenC E' 1 ⊥ := by
    rw [Genuine.SgenC_of_charZero, Genuine.SgenC_of_charZero]
    exact Genuine.Sgen_subset E' hc hn hmul hM'
  change Genuine.pi1MapC E' _ = _
  rw [Genuine.pi1MapC, dif_pos ⟨hle, hS⟩]
  rfl

end Cover

variable (D : InitialThetaData.{0})

/-! ### `π₁(C̲_K)` and `π₁(C_K)` have the same image in `Gal(F̄/F_mod)` -/

/-- `π₁(C̲_K) ↪ π₁(C_K) ↪ π₁(C_{F_mod})`. -/
def piCKuCmod : D.orb.CKu.genuinePi1 →ₜ* piCmod D := (piCKToCmod D).comp (piCKuToCK D)

lemma piCKuCmod_apply (x : D.orb.CKu.genuinePi1) :
    piCKuCmod D x = piCKToCmod D (piCKuToCK D x) := rfl

lemma isOpenEmbedding_piCKuCmod : IsOpenEmbedding (piCKuCmod D) := by
  have e : ⇑(piCKuCmod D) = piCKToCmod D ∘ piCKuToCK D := rfl
  rw [e]
  exact (isOpenEmbedding_piCKToCmod D).comp D.orb.pi1CKu_to_CK_isOpenEmbedding

/-- Equal restrictions to `k̄` give equal images in `Gal(F̄/F_mod)` (`iotaK_resK`). -/
lemma piCmodPr_eq_of_resK_eq {x y : piCK D} (h : resK D x = resK D y) :
    piCmodPr D (piCKToCmod D x) = piCmodPr D (piCKToCmod D y) := by
  refine AlgEquiv.ext fun w => ?_
  obtain ⟨v, rfl⟩ := (iotaK D).surjective w
  rw [← iotaK_resK, ← iotaK_resK, h]

omit D in
/-- A ring homomorphism commuting with the structure maps preserves algebraic elements. -/
lemma isAlgebraic_ringHom {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →+* B) (hf : ∀ c : R, f (algebraMap R A c) = algebraMap R B c) {a : A}
    (ha : IsAlgebraic R a) : IsAlgebraic R (f a) :=
  ha.algHom ({ f with commutes' := hf } : A →ₐ[R] B)

/-- **`π₁(C̲_K) ↠ Gal(k̄/K)`**: every element of `π₁(C_K)` has the restriction to `k̄` of an element
of `π₁(C̲_K)`. -/
theorem exists_piCKu_resK (ρ : piCK D) :
    ∃ x : D.orb.CKu.genuinePi1, resK D (piCKuToCK D x) = resK D ρ := by
  obtain ⟨y, rfl⟩ := (genuinePi1EqEquiv (CK_eq D)).symm.surjective ρ
  obtain ⟨σ, rfl⟩ := mkC_surjective (EK D) y
  obtain ⟨hprime, hlev, hpm, -, -, hcard⟩ := D.orb.CKu_type
  have hℓ : D.orb.CKu.level ≠ 0 := by
    rw [hlev]
    exact hprime.ne_zero
  have hcard' : Nat.card D.orb.CKu.torsion = D.orb.CKu.level ^ 2 := by
    rw [hcard, hlev]
  obtain ⟨x, δ, hδ, hx⟩ :=
    exists_genuinePi1Cover_eq_mkC ((CK_eq D) ▸ D.orb.CKu_to_CK) hpm hℓ hcard' σ
  refine ⟨x, ?_⟩
  have e : piCKuToCK D x = (genuinePi1EqEquiv (CK_eq D)).symm (mkC (EK D) (δ * σ)) := by
    rw [← hx, ← genuinePi1EqEquiv_cover, ContinuousMulEquiv.symm_apply_apply]
    rfl
  rw [e]
  refine AlgEquiv.ext fun w => Subtype.ext ?_
  rw [resK_mkC, resK_mkC, AlgEquiv.mul_apply]
  congr 1
  apply hδ
  have hw : IsAlgebraic D.Kt ((w : kbar D.Kt (FFClosure (curveE (EK D)))) :
      FFClosure (curveE (EK D))) := mem_algebraicClosure_iff.1 w.2
  have hw' : IsAlgebraic D.Kt ((hemiOmegaEquiv (EK D)).symm
      ((w : kbar D.Kt (FFClosure (curveE (EK D)))) : FFClosure (curveE (EK D)))) :=
    isAlgebraic_ringHom (hemiOmegaEquiv (EK D)).symm.toRingHom (fun c => by
      change (hemiOmegaEquiv (EK D)).symm _ = _
      rw [RingEquiv.symm_apply_eq, hemiOmegaEquiv_algebraMap_K]) hw
  exact hw'.algHom (Genuine.σk (EK D) σ)

/-- **`π₁(C̲_K)` and `π₁(C_K)` have the same image in `Gal(F̄/F_mod)`.** -/
theorem exists_piCKu_pr (ρ : piCK D) :
    ∃ x : D.orb.CKu.genuinePi1,
      piCmodPr D (piCKToCmod D (piCKuToCK D x)) = piCmodPr D (piCKToCmod D ρ) := by
  obtain ⟨x, hx⟩ := exists_piCKu_resK D ρ
  exact ⟨x, piCmodPr_eq_of_resK_eq D hx⟩

/-! ### The named statements for `C̲_K` -/

/-- **Strict semi-absoluteness of the automorphisms of `π₁(C̲_K)`** ([AbsTopI] Cor. 2.8 (ii),
`Topics in Absolute Anabelian Geometry I.txt` l.1348–1379, applied to the hyperbolic orbicurve
`C̲_K` over the number field `K`; the same literature input as `CKStrictSemiAbs`), as a **named
statement**: every continuous automorphism of `π₁(C̲_K)` maps
`Δ_{C̲_K} = ker(π₁(C̲_K) → Gal(F̄/F_mod))` into itself. -/
def CKuStrictSemiAbs : Prop :=
  ∀ α : D.orb.CKu.genuinePi1 ≃ₜ* D.orb.CKu.genuinePi1, ∀ x,
    piCmodPr D (piCKuCmod D x) = 1 → piCmodPr D (piCKuCmod D (α x)) = 1

/-- **Semi-absolute conjugacy for `π₁(C̲_K)`**: every continuous automorphism of `π₁(C̲_K)`
preserving `Δ_{C̲_K}` acts on the image of `π₁(C̲_K)` in `Gal(F̄/F_mod)` by conjugation by an
element of `Gal(F̄/F_mod)` (the analogue of `CKSemiAbsConj`; proved in `ckuSemiAbsConj`). -/
def CKuSemiAbsConj : Prop :=
  ∀ α : D.orb.CKu.genuinePi1 ≃ₜ* D.orb.CKu.genuinePi1,
    (∀ x, piCmodPr D (piCKuCmod D (α x)) = 1 ↔ piCmodPr D (piCKuCmod D x) = 1) →
      ∃ g : GalG (Fmod D) D.Fbar, ∀ x,
        piCmodPr D (piCKuCmod D (α x)) = g * piCmodPr D (piCKuCmod D x) * g⁻¹

/-! ### The extension to `π₁(C_K)` -/

/-- An open embedding `Q ↪ P` of topological groups, as `Q ≃ₜ* image`. -/
def equivRange {Q P : Type*} [Group Q] [Group P] [TopologicalSpace Q] [TopologicalSpace P]
    (κ : Q →ₜ* P) (hκ : IsEmbedding κ) : Q ≃ₜ* (κ : Q →* P).range where
  toMulEquiv := MonoidHom.ofInjective hκ.injective
  continuous_toFun := κ.continuous.subtype_mk _
  continuous_invFun := by
    refine hκ.isInducing.continuous_iff.2 ?_
    have e : (κ ∘ (MonoidHom.ofInjective hκ.injective).symm) =
        fun y : (κ : Q →* P).range => (y : P) :=
      funext fun y => MonoidHom.apply_ofInjective_symm hκ.injective y
    change Continuous (κ ∘ (MonoidHom.ofInjective hκ.injective).symm)
    rw [e]
    exact continuous_subtype_val

lemma coe_equivRange {Q P : Type*} [Group Q] [Group P] [TopologicalSpace Q] [TopologicalSpace P]
    (κ : Q →ₜ* P) (hκ : IsEmbedding κ) (x : Q) : (equivRange κ hκ x : P) = κ x := rfl

/-- The projection `π₁(C_{F_mod}) → Gal(F̄/F_mod)` as a continuous homomorphism. -/
def piCmodPrC : piCmod D →ₜ* GalG (Fmod D) D.Fbar := ⟨piCmodPr D, continuous_piCmodPr D⟩

set_option maxHeartbeats 1000000 in
-- `π₁(C̲_K)`, `π₁(C_K)` and `Gal(F̄/F_mod)` are compared at heavy instance terms
/-- **`CKuSemiAbsConj`**: a semi-absolute automorphism `α` of `π₁(C̲_K)` extends to an automorphism
`β` of `π₁(C_K)` preserving `Δ_{C_K}` (`ExtendAut.exists_extend`: the self-commensuration
`piCmod_selfComm` and `π₁(C̲_K) ↠ G_K`, `exists_piCKu_pr`), and `ckSemiAbsConj` applies to `β`.
Inputs: those of `ckSemiAbsConj` (`BelyiCuspSpec` (MR8), `RelIsomDGC.Exists` (MR7)) and of
`piCmod_selfComm` (`RelIsomDGC.Exists` for all number fields, `hj`). -/
theorem ckuSemiAbsConj
    (hS : BelyiCuspSpec (AlgebraicClosure D.Kt) (hypCurveE (EK D)) (factEK D).out)
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F)) : CKuSemiAbsConj D := by
  intro α hα
  have hκ : IsOpenEmbedding (piCKuToCK D) := D.orb.pi1CKu_to_CK_isOpenEmbedding
  let eH := equivRange (piCKuToCK D) hκ.isEmbedding
  let a := eH.symm.trans (α.trans eH)
  have haH : ∀ x, (a (eH x) : piCK D) = piCKuToCK D (α x) := fun x => by
    change ((eH (α (eH.symm (eH x)))) : piCK D) = _
    rw [ContinuousMulEquiv.symm_apply_apply]
    rfl
  have ha : ∀ h, piCmodPrC D (piCKToCmod D (a h)) = 1 ↔ piCmodPrC D (piCKToCmod D h) = 1 :=
    fun h => by
      obtain ⟨x, rfl⟩ := eH.surjective h
      rw [haH]
      exact hα x
  have hB : ∀ (y : piCmod D) (ρ : piCK D), piCmodPrC D y = piCmodPrC D (piCKToCmod D ρ) →
      y ∈ Set.range (piCKToCmod D) := fun y ρ h =>
    (mem_range_piCKToCmod_iff D y).2 ⟨piCKToCmod D ρ, ⟨ρ, rfl⟩, h.symm⟩
  have hsurj : ∀ ρ : piCK D, ∃ x : (piCKuToCK D : D.orb.CKu.genuinePi1 →* piCK D).range,
      piCmodPrC D (piCKToCmod D x) = piCmodPrC D (piCKToCmod D ρ) := fun ρ => by
    obtain ⟨x, hx⟩ := exists_piCKu_pr D ρ
    exact ⟨eH x, hx⟩
  have hSC : ExtendAut.SelfComm (piCmodPrC D) :=
    fun R _ _ _ _ f₁ f₂ hi₁ ho₁ hi₂ ho₂ g hg =>
      piCmod_selfComm D hDGC hj R f₁ f₂ hi₁ ho₁ hi₂ ho₂ g hg
  obtain ⟨β, hβH, hβ⟩ := ExtendAut.exists_extend (isOpenEmbedding_piCKToCmod D)
    (isSlim_piCmod D) (isSlim_galoisGroup_numberField (Fmod D) D.Fbar) (piCmodPr_surjective D)
    hB hκ.isOpen_range hsurj hSC a ha
  obtain ⟨g, hg⟩ := ckSemiAbsConj D hS (hDGC D.Kt) β hβ
  refine ⟨g, fun x => ?_⟩
  have e := hg (piCKuToCK D x)
  have e2 : β (piCKuToCK D x) = piCKuToCK D (α x) := by
    rw [← haH]
    exact hβH (eH x)
  rw [e2] at e
  exact e

/-! ### Every automorphism of `π₁(C̲_K)` is a conjugation in `π₁(C_{F_mod})` -/

/-- **The absolute form for `π₁(C̲_K)`** (analogue of `hAbs_of_strict`): every continuous
automorphism of `π₁(C̲_K)` acts on its image in `Gal(F̄/F_mod)` by conjugation by an element of
`Gal(F̄/F_mod)`. Named inputs: `CKuStrictSemiAbs` (literature, [AbsTopI] Cor. 2.8 (ii)),
`BelyiCuspSpec` (MR8), `RelIsomDGC.Exists` (MR7), `hj`. -/
theorem hAbsCKu_of_strict (hStrict : CKuStrictSemiAbs D)
    (hS : BelyiCuspSpec (AlgebraicClosure D.Kt) (hypCurveE (EK D)) (factEK D).out)
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F))
    (α : D.orb.CKu.genuinePi1 ≃ₜ* D.orb.CKu.genuinePi1) :
    ∃ g : GalG (Fmod D) D.Fbar, ∀ x,
      piCmodPr D (piCKuCmod D (α x)) = g * piCmodPr D (piCKuCmod D x) * g⁻¹ :=
  ckuSemiAbsConj D hS hDGC hj α fun x => ⟨fun hx => by
    have h := hStrict α.symm (α x) hx
    rwa [ContinuousMulEquiv.symm_apply_apply] at h, hStrict α x⟩

set_option maxHeartbeats 1000000 in
-- `piCmod_selfComm` at `π₁(C̲_K)` unfolds heavy instance terms
/-- **Every continuous automorphism of `π₁(C̲_K)` is conjugation by a unique element of
`π₁(C_{F_mod})`** along `piCKuCmod` (the surjectivity half of `Aut(C̲_K) ≅ Out(π₁(C̲_K))` in
IUT I, Ex. 4.3 (i), with `Aut(C̲_K) = N_{π₁(C_{F_mod})}(π₁(C̲_K)) / π₁(C̲_K)`): the
self-commensuration `piCmod_selfComm` applied to `piCKuCmod` and `piCKuCmod ∘ α`
(`hAbsCKu_of_strict`), uniqueness by slimness (`isSlim_piCmod`). Named inputs as in
`hAbsCKu_of_strict`. -/
theorem piCKu_aut_eq_conj (hStrict : CKuStrictSemiAbs D)
    (hS : BelyiCuspSpec (AlgebraicClosure D.Kt) (hypCurveE (EK D)) (factEK D).out)
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F))
    (α : D.orb.CKu.genuinePi1 ≃ₜ* D.orb.CKu.genuinePi1) :
    ∃! γ : piCmod D, ∀ x, piCKuCmod D (α x) = γ * piCKuCmod D x * γ⁻¹ := by
  have hι := isOpenEmbedding_piCKuCmod D
  obtain ⟨g, hg⟩ := hAbsCKu_of_strict D hStrict hS hDGC hj α
  let f₂ : D.orb.CKu.genuinePi1 →ₜ* piCmod D :=
    (piCKuCmod D).comp (ContinuousMonoidHom.toContinuousMonoidHom α)
  have hf₂ : ⇑f₂ = piCKuCmod D ∘ α := rfl
  have hf₂o : IsOpenEmbedding f₂ := by
    rw [hf₂]
    exact hι.comp α.toHomeomorph.isOpenEmbedding
  have hf₂x : ∀ x, f₂ x = piCKuCmod D (α x) := fun _ => rfl
  have hg' : ∀ x, piCmodPr D (f₂ x) = g * piCmodPr D (piCKuCmod D x) * g⁻¹ := fun x => by
    rw [hf₂x]
    exact hg x
  obtain ⟨γ, hγ⟩ := piCmod_selfComm D hDGC hj D.orb.CKu.genuinePi1 (piCKuCmod D) f₂ hι.injective
    hι.isOpen_range hf₂o.injective hf₂o.isOpen_range g hg'
  refine ⟨γ, fun x => (hf₂x x).symm.trans (hγ x), fun δ hδ => ?_⟩
  have h1 : δ⁻¹ * γ = 1 := eq_one_of_commute_open₄ (isSlim_piCmod D) (piCKuCmod D)
    hι.isOpen_range (U := ⊤) isOpen_univ fun x _ => by
      have e : δ * piCKuCmod D x * δ⁻¹ = γ * piCKuCmod D x * γ⁻¹ :=
        (hδ x).symm.trans ((hf₂x x).symm.trans (hγ x))
      calc δ⁻¹ * γ * piCKuCmod D x
          = δ⁻¹ * (γ * piCKuCmod D x * γ⁻¹) * γ := by group
        _ = δ⁻¹ * (δ * piCKuCmod D x * δ⁻¹) * γ := by rw [e]
        _ = piCKuCmod D x * (δ⁻¹ * γ) := by group
  calc δ = δ * (δ⁻¹ * γ) := by rw [h1, mul_one]
    _ = γ := by group

end HodgeTheater

end Iut
