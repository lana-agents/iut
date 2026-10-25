/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Anabelian.CanLift
import Pi1.Orbicurve.Morphisms
import Pi1.FundamentalGroup.Galois
import CurvesJacobian.Cusp.EllipticPunctured
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral
import Mathlib.RingTheory.Unramified.Dedekind

/-!
# The core property of `C = (E ∖ O)/±1`, in ring form

Let `E` be an elliptic curve over a field `K` of characteristic `0` (in `Type`) with
`j(E) ∉ excJ`, let `X = E ∖ O = Spec K[E]`, and let `Y = Spec B → X` be a connected finite étale
cover (`B` a domain). By [CanLift], Proposition 2.7 (`Iut.Anabelian.canLift27`) the punctured
hemi-elliptic orbicurve `C = X/±1` is the `K`-core of `X`: every object of
`\overline{Loc}_K(X)` has **exactly one** finite étale morphism to `C`. Hence any two finite étale
morphisms `Y → X` agree after composing with the quotient map `X → C`, whose coarse map is the
`x`-coordinate `X → A¹`:

* `hemiCore_apply_x`: for `K`-algebra maps `a, b : K[E] → B`, each making `B` finite étale over
  `K[E]`, `a x = b x`;
* `hemiCore_eq_or_eq_neg`: `b = a` or `b = a ∘ [-1]`, where `negCoordAlgEquiv E` is the
  `[-1]`-automorphism `x ↦ x, y ↦ -y - a₁x - a₃` of `K[E]` (`y` and its conjugate are the two
  roots of the Weierstrass equation over `K[x]`, and `B` is a domain);
* `hemiCore_apply_x_sections`, `hemiCore_eq_or_eq_neg_sections`: the same for `K`-algebra maps
  `Γ(E ∖ O) → B` with `Spec B → Spec Γ(E ∖ O)` finite étale (`IsFiniteEtale`), through
  `sectionsXEAlgEquiv E : Γ(E ∖ O) ≃ₐ[K] K[E]`.

Ingredients: a domain finite étale over the coordinate ring of an affine curve (with trivial
stabilizers) is again an affine curve (`ofFiniteEtale₃`, Dedekind by
`isDedekindDomain.of_formallyUnramified`) with finite étale morphisms (ramification index `1`,
`Ideal.ramificationIdx_eq_one`) to it (`homOfFiniteEtale₃`); `K[E]` is the coordinate ring
`puncturedRing E` of pi1's `AffOrbicurve.punctured E` (`coordPuncturedEquiv`, since `K[E]` is
integrally closed, `WeierstrassCurve.Affine.CoordinateRing.instIsIntegrallyClosed`); and the
quotient map `hemiHom₃ : punctured E → hemi E` (the `x`-coordinate; after
`OrbicurveCores.Genuine.hemiHom` of `orbicurve-cores`).
-/

universe u

open Polynomial AffOrbicurve

namespace Iut.Reconstruction.HemiCore

/-! ### Finite étale covers of affine orbicurves with trivial stabilizers -/

section Generic

variable {k : Type u} [Field k]

/-- An étale ring map from a domain to a nonzero ring is injective (étale maps are flat). -/
lemma injective_of_etale₃ {R B : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    (f : R →+* B) (he : f.Etale) : Function.Injective f := by
  letI := f.toAlgebra
  haveI : Module.Flat R B := (RingHom.Etale.iff_flat_and_formallyUnramified.mp he).1
  exact FaithfulSMul.algebraMap_injective R B

/-- A domain finite étale over the coordinate ring of an affine orbicurve is a Dedekind domain. -/
lemma isDedekindDomain_of_finiteEtale₃ (A : AffOrbicurve k) {B : Type u} [CommRing B]
    [IsDomain B] (f : A.A →+* B) (hf : f.Finite) (he : f.Etale) : IsDedekindDomain B := by
  letI := f.toAlgebra
  haveI : Module.Finite A.A B := hf
  haveI : Algebra.FormallyUnramified A.A B :=
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp he).2.1
  exact isDedekindDomain.of_formallyUnramified A.A B

/-- A `k`-algebra finite over the coordinate ring of an affine orbicurve is of finite type. -/
lemma finiteType_of_finite₃ (A : AffOrbicurve k) {B : Type u} [CommRing B] [Algebra k B]
    (f : A.A →ₐ[k] B) (hf : f.toRingHom.Finite) : Algebra.FiniteType k B := by
  letI := f.toRingHom.toAlgebra
  haveI : Module.Finite A.A B := hf
  haveI : IsScalarTower k A.A B := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  exact Algebra.FiniteType.trans (S := A.A) inferInstance inferInstance

/-- A domain finite étale over the coordinate ring of an affine orbicurve is not a field. -/
lemma not_isField_of_finiteEtale₃ (A : AffOrbicurve k) {B : Type u} [CommRing B] [IsDomain B]
    (f : A.A →+* B) (hf : f.Finite) (he : f.Etale) : ¬ IsField B := by
  intro hB
  letI := f.toAlgebra
  haveI : Module.Finite A.A B := hf
  exact A.not_isField (isField_of_isIntegral_of_isField (injective_of_etale₃ f he) hB)

/-- **The affine curve `Spec B`** of a domain `B` finite étale over the coordinate ring of an
affine orbicurve `A` (via `f`), with trivial stabilizers. -/
noncomputable def ofFiniteEtale₃ (A : AffOrbicurve k) (B : Type u) [CommRing B] [IsDomain B]
    [Algebra k B] (f : A.A →ₐ[k] B) (hf : f.toRingHom.Finite) (he : f.toRingHom.Etale) :
    AffOrbicurve k :=
  letI := isDedekindDomain_of_finiteEtale₃ A f.toRingHom hf he
  letI := finiteType_of_finite₃ A f hf
  { A := B
    not_isField := not_isField_of_finiteEtale₃ A f.toRingHom hf he
    mult := fun _ => 1
    mult_pos := fun _ _ => Nat.one_pos
    finite_mult := by simp }

/-- Ramification indices of a finite étale map are `1`. -/
lemma ramificationIdx_eq_one_of_etale₃ {R B : Type*} [CommRing R] [CommRing B] (f : R →+* B)
    (hf : f.Finite) (he : f.Etale) (w : Ideal B) [hw : w.IsPrime] :
    (letI := f.toAlgebra; w.ramificationIdx R) = 1 := by
  letI := f.toAlgebra
  haveI : Module.Finite R B := hf
  haveI : Algebra.FormallyUnramified R B :=
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp he).2.1
  haveI : Algebra.IsUnramifiedAt R w :=
    Algebra.formallyUnramified_iff_forall.mp inferInstance ⟨w, hw⟩
  exact Ideal.ramificationIdx_eq_one w R

/-- The contraction of a maximal ideal along a finite ring map is maximal. -/
lemma comap_isMaximal_of_finite₃ {R B : Type*} [CommRing R] [CommRing B] (f : R →+* B)
    (hf : f.Finite) (w : Ideal B) (hw : w.IsMaximal) : (w.comap f).IsMaximal := by
  letI := f.toAlgebra
  haveI : Module.Finite R B := hf
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal w

/-- **A finite étale map `A.A → B` is a finite étale morphism `Spec B → A`** of affine
orbicurves, when `A` has trivial stabilizers (ramification indices of étale maps are `1`). -/
noncomputable def homOfFiniteEtale₃ (A : AffOrbicurve k) (hA : ∀ v, v.IsMaximal → A.mult v = 1)
    {B : Type u} [CommRing B] [IsDomain B] [Algebra k B] (f₀ : A.A →ₐ[k] B)
    (hf₀ : f₀.toRingHom.Finite) (he₀ : f₀.toRingHom.Etale) (f : A.A →ₐ[k] B)
    (hf : f.toRingHom.Finite) (he : f.toRingHom.Etale) :
    Hom (ofFiniteEtale₃ A B f₀ hf₀ he₀) A where
  f := f
  injective := injective_of_etale₃ f.toRingHom he
  isIntegral := RingHom.IsIntegral.of_finite hf
  etale w hw := by
    have h1 := ramificationIdx_eq_one_of_etale₃ f.toRingHom hf he (show Ideal B from w)
      (hw := hw.isPrime)
    have h2 := comap_isMaximal_of_finite₃ f.toRingHom hf (show Ideal B from w) hw
    have h3 : A.mult (w.comap f) = 1 := hA _ h2
    change _ * 1 = _
    rw [mul_one]
    exact h1.trans h3.symm

/-- **Uniqueness of morphisms to a core**: two finite étale morphisms `Y → X` agree after
composing with any finite étale morphism `X → C` to the core `C` of `X`. -/
theorem f_comp_eq_of_isCoreOf₃ {X C Y : AffOrbicurve k} (hC : IsCoreOf X C) (h : Hom X C)
    (g₁ g₂ : Hom Y X) : g₁.f.comp h.f = g₂.f.comp h.f := by
  obtain ⟨-, hs⟩ := hC.2 Y (LocBar.of_hom g₁)
  exact congrArg Hom.f (hs.elim (g₁.comp h) (g₂.comp h))

/-- Finiteness is preserved by precomposing with a ring isomorphism. -/
lemma finite_comp_equiv₃ {R S B : Type*} [CommRing R] [CommRing S] [CommRing B] (a : S →+* B)
    (e : R ≃+* S) (ha : a.Finite) : (a.comp e.toRingHom).Finite :=
  ha.comp (RingHom.Finite.of_surjective _ e.surjective)

/-- Étaleness is preserved by precomposing with a ring isomorphism. -/
lemma etale_comp_equiv₃ {R S B : Type*} [CommRing R] [CommRing S] [CommRing B] (a : S →+* B)
    (e : R ≃+* S) (ha : a.Etale) : (a.comp e.toRingHom).Etale := by
  letI := e.toRingHom.toAlgebra
  letI := a.toAlgebra
  letI := (a.comp e.toRingHom).toAlgebra
  haveI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.Etale R S := RingHom.Etale.of_bijective e.bijective
  haveI : Algebra.Etale S B := ha
  exact Algebra.Etale.comp R S B

end Generic

/-! ### The once-punctured elliptic curve and its `±1`-quotient -/

section Hemi

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

attribute [local instance] FractionRing.liftAlgebra

/-- **`K[E]` is the coordinate ring of `E ∖ {0}`** of pi1 (the integral closure of `k[x]` in
`k(E)`): `K[E]` is integrally closed and integral over `k[x]`. -/
noncomputable def coordPuncturedEquiv :
    E.toAffine.CoordinateRing ≃ₐ[k[X]] puncturedRing E :=
  IsIntegralClosure.equiv k[X] E.toAffine.CoordinateRing E.toAffine.FunctionField
    (puncturedRing E)

local instance : IsLocalization
    (Algebra.algebraMapSubmonoid E.toAffine.CoordinateRing (nonZeroDivisors k[X]))
    E.toAffine.FunctionField :=
  isLocalization_algebraMapSubmonoid_of_isAlgebraic k[X] E.toAffine.CoordinateRing
    E.toAffine.FunctionField

omit [CharZero k] [E.IsElliptic] in
/-- `[k(E) : k(x)] = 2`. -/
lemma finrank_functionField₃ :
    Module.finrank (FractionRing k[X]) E.toAffine.FunctionField = 2 := by
  have b := (WeierstrassCurve.Affine.CoordinateRing.basis E.toAffine).localizationLocalization
    (FractionRing k[X]) (nonZeroDivisors k[X]) E.toAffine.FunctionField
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

local instance : Algebra.IsQuadraticExtension (FractionRing k[X]) E.toAffine.FunctionField :=
  ⟨finrank_functionField₃ E⟩

local instance : SMulCommClass
    (E.toAffine.FunctionField ≃ₐ[FractionRing k[X]] E.toAffine.FunctionField) k[X]
    E.toAffine.FunctionField where
  smul_comm g a b := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul',
      IsScalarTower.algebraMap_apply k[X] (FractionRing k[X]) E.toAffine.FunctionField,
      AlgEquiv.smul_def, AlgEquiv.commutes]

local instance : IsFractionRing (puncturedRing E) E.toAffine.FunctionField :=
  integralClosure.isFractionRing_of_finite_extension (FractionRing k[X]) E.toAffine.FunctionField

local instance : IsGaloisGroup
    (E.toAffine.FunctionField ≃ₐ[FractionRing k[X]] E.toAffine.FunctionField) k[X]
    (puncturedRing E) :=
  IsGaloisGroup.of_isFractionRing _ k[X] (puncturedRing E) (FractionRing k[X])
    E.toAffine.FunctionField

/-- The `x`-coordinate, as a map of coordinate rings `k[x] → k[E ∖ 0]`. -/
noncomputable def hemiMap₃ : (hemi E).A →ₐ[k] (punctured E).A :=
  IsScalarTower.toAlgHom k k[X] (puncturedRing E)

omit [E.IsElliptic] in
lemma ramIdx_hemiMap₃ (w : Ideal (punctured E).A) :
    (letI := (hemiMap₃ E).toRingHom.toAlgebra
     w.ramificationIdx (hemi E).A) =
      (show Ideal (puncturedRing E) from w).ramificationIdx k[X] := by
  have h : (hemiMap₃ E).toRingHom.toAlgebra =
      (inferInstance : Algebra k[X] (puncturedRing E)) :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  rw [h]
  rfl

/-- **The quotient map `E ∖ {0} → (E ∖ {0}) / ±1`** (the `x`-coordinate) is a finite étale
morphism of affine orbicurves: all primes over a given prime of `k[x]` are conjugate under the
Galois group of `k(E)/k(x)`, so they have the same ramification index. (After
`OrbicurveCores.Genuine.hemiHom`.) -/
noncomputable def hemiHom₃ : Hom (punctured E) (hemi E) where
  f := hemiMap₃ E
  injective := FaithfulSMul.algebraMap_injective k[X] (puncturedRing E)
  isIntegral := Algebra.IsIntegral.isIntegral (R := k[X]) (A := puncturedRing E)
  etale w hw := by
    rw [ramIdx_hemiMap₃]
    obtain ⟨w', rfl⟩ : ∃ w' : Ideal (puncturedRing E), w' = w := ⟨w, rfl⟩
    have : w'.IsPrime := hw.isPrime
    change w'.ramificationIdx k[X] * 1 = (w'.under k[X]).ramificationIdxIn (puncturedRing E)
    rw [mul_one]
    exact (Ideal.ramificationIdxIn_eq_ramificationIdx (w'.under k[X]) w'
      (E.toAffine.FunctionField ≃ₐ[FractionRing k[X]] E.toAffine.FunctionField)).symm

omit [E.IsElliptic] in
lemma hemiHom₃_f_X : (hemiHom₃ E).f X = algebraMap k[X] (puncturedRing E) X := rfl

end Hemi

/-! ### The core property -/

section Core

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- `K[E] ≅ puncturedRing E` as `K`-algebras. -/
noncomputable def coordPuncturedEquivK :
    E.toAffine.CoordinateRing ≃ₐ[K] puncturedRing E :=
  (coordPuncturedEquiv E).restrictScalars K

/-- **The core property of `(E ∖ O)/±1`** ([CanLift], Proposition 2.7): if `a, b : K[E] → B`
are `K`-algebra maps into a domain `B`, each finite étale, then `a x = b x`. -/
theorem hemiCore_apply_x (hj : ∀ c ∈ excJ, E.j ≠ (c : K)) {B : Type} [CommRing B] [IsDomain B]
    [Algebra K B] (a b : E.toAffine.CoordinateRing →ₐ[K] B) (haf : a.toRingHom.Finite)
    (hae : a.toRingHom.Etale) (hbf : b.toRingHom.Finite) (hbe : b.toRingHom.Etale) :
    a (algebraMap K[X] E.toAffine.CoordinateRing X) =
      b (algebraMap K[X] E.toAffine.CoordinateRing X) := by
  have haf' : (a.comp (coordPuncturedEquivK E).symm.toAlgHom).toRingHom.Finite :=
    finite_comp_equiv₃ a.toRingHom (coordPuncturedEquivK E).symm.toRingEquiv haf
  have hae' : (a.comp (coordPuncturedEquivK E).symm.toAlgHom).toRingHom.Etale :=
    etale_comp_equiv₃ a.toRingHom (coordPuncturedEquivK E).symm.toRingEquiv hae
  have hbf' : (b.comp (coordPuncturedEquivK E).symm.toAlgHom).toRingHom.Finite :=
    finite_comp_equiv₃ b.toRingHom (coordPuncturedEquivK E).symm.toRingEquiv hbf
  have hbe' : (b.comp (coordPuncturedEquivK E).symm.toAlgHom).toRingHom.Etale :=
    etale_comp_equiv₃ b.toRingHom (coordPuncturedEquivK E).symm.toRingEquiv hbe
  have hcore := f_comp_eq_of_isCoreOf₃ (Iut.Anabelian.canLift27 K E hj) (hemiHom₃ E)
    (homOfFiniteEtale₃ (punctured E) (fun _ _ => rfl) _ haf' hae' _ haf' hae')
    (homOfFiniteEtale₃ (punctured E) (fun _ _ => rfl) _ haf' hae' _ hbf' hbe')
  have h1 := DFunLike.congr_fun hcore X
  have h2 : (coordPuncturedEquivK E).symm (algebraMap K[X] (puncturedRing E) X) =
      algebraMap K[X] E.toAffine.CoordinateRing X :=
    (coordPuncturedEquiv E).symm.commutes X
  have h3 : a ((coordPuncturedEquivK E).symm (algebraMap K[X] (puncturedRing E) X)) =
      b ((coordPuncturedEquivK E).symm (algebraMap K[X] (puncturedRing E) X)) := h1
  rwa [h2] at h3

end Core

/-! ### The `[-1]`-automorphism of `K[E]` and the dichotomy -/

section Neg

open scoped Polynomial.Bivariate

variable {K : Type u} [Field K] (E : WeierstrassCurve K)

/-- The class of `x` in `K[E]`. -/
noncomputable abbrev xCoord₃ : E.toAffine.CoordinateRing :=
  algebraMap K[X] E.toAffine.CoordinateRing X

/-- The class of `y` in `K[E]`. -/
noncomputable abbrev yCoord₃ : E.toAffine.CoordinateRing :=
  AdjoinRoot.root E.toAffine.polynomial

lemma polynomial_comp_negPolynomial₃ :
    E.toAffine.polynomial.comp E.toAffine.negPolynomial = E.toAffine.polynomial := by
  simp only [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.Affine.negPolynomial, sub_comp,
    add_comp, mul_comp, pow_comp, X_comp, C_comp]
  ring1

lemma negPolynomial_comp_negPolynomial₃ :
    E.toAffine.negPolynomial.comp E.toAffine.negPolynomial = (Y : K[X][Y]) := by
  simp only [WeierstrassCurve.Affine.negPolynomial, sub_comp, neg_comp, X_comp, C_comp]
  ring1

lemma eval₂_of_mk₃ (q r : K[X][Y]) :
    q.eval₂ (AdjoinRoot.of E.toAffine.polynomial) (AdjoinRoot.mk E.toAffine.polynomial r) =
      AdjoinRoot.mk E.toAffine.polynomial (q.comp r) := by
  rw [Polynomial.comp, Polynomial.hom_eval₂]
  rfl

lemma eval₂_negPolynomial₃ :
    E.toAffine.polynomial.eval₂ (Algebra.ofId K[X] E.toAffine.CoordinateRing)
      (AdjoinRoot.mk E.toAffine.polynomial E.toAffine.negPolynomial) = 0 := by
  rw [show ((Algebra.ofId K[X] E.toAffine.CoordinateRing : K[X] →+* E.toAffine.CoordinateRing))
        = AdjoinRoot.of E.toAffine.polynomial from rfl,
    eval₂_of_mk₃, polynomial_comp_negPolynomial₃, AdjoinRoot.mk_self]

/-- The `[-1]`-map of `K[E]` over `K[x]`: `y ↦ -y - a₁x - a₃`. -/
noncomputable def negCoordHom₃ :
    E.toAffine.CoordinateRing →ₐ[K[X]] E.toAffine.CoordinateRing :=
  AdjoinRoot.liftAlgHom E.toAffine.polynomial (Algebra.ofId K[X] E.toAffine.CoordinateRing)
    (AdjoinRoot.mk E.toAffine.polynomial E.toAffine.negPolynomial) (eval₂_negPolynomial₃ E)

lemma negCoordHom₃_mk (q : K[X][Y]) :
    negCoordHom₃ E (AdjoinRoot.mk E.toAffine.polynomial q) =
      AdjoinRoot.mk E.toAffine.polynomial (q.comp E.toAffine.negPolynomial) := by
  rw [negCoordHom₃, AdjoinRoot.liftAlgHom_mk]
  exact eval₂_of_mk₃ E q E.toAffine.negPolynomial

lemma negCoordHom₃_root :
    negCoordHom₃ E (yCoord₃ E) = AdjoinRoot.mk E.toAffine.polynomial E.toAffine.negPolynomial := by
  rw [yCoord₃, ← AdjoinRoot.mk_X, negCoordHom₃_mk, X_comp]

lemma negCoordHom₃_comp :
    (negCoordHom₃ E).comp (negCoordHom₃ E) = AlgHom.id K[X] E.toAffine.CoordinateRing :=
  AdjoinRoot.algHom_ext <| by
    rw [AlgHom.comp_apply, negCoordHom₃_root, negCoordHom₃_mk,
      negPolynomial_comp_negPolynomial₃, AdjoinRoot.mk_X, AlgHom.coe_id, id_eq]

/-- **The `[-1]`-automorphism `ν` of `K[E]`**: `x ↦ x`, `y ↦ -y - a₁x - a₃`. -/
noncomputable def negCoordAlgEquiv : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing :=
  (AlgEquiv.ofAlgHom (negCoordHom₃ E) (negCoordHom₃ E) (negCoordHom₃_comp E)
    (negCoordHom₃_comp E)).restrictScalars K

lemma negCoordAlgEquiv_x : negCoordAlgEquiv E (xCoord₃ E) = xCoord₃ E :=
  (negCoordHom₃ E).commutes X

lemma negCoordAlgEquiv_y : negCoordAlgEquiv E (yCoord₃ E) =
    -yCoord₃ E - (algebraMap K _ E.a₁ * xCoord₃ E + algebraMap K _ E.a₃) := by
  change negCoordHom₃ E (yCoord₃ E) = _
  rw [negCoordHom₃_root, WeierstrassCurve.Affine.negPolynomial]
  simp only [map_sub, map_neg, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  rfl

/-- The Weierstrass equation in `K[E]`. -/
lemma weierstrass_rel₃ : yCoord₃ E ^ 2 + (algebraMap K _ E.a₁ * xCoord₃ E +
    algebraMap K _ E.a₃) * yCoord₃ E = xCoord₃ E ^ 3 + algebraMap K _ E.a₂ * xCoord₃ E ^ 2 +
      algebraMap K _ E.a₄ * xCoord₃ E + algebraMap K _ E.a₆ := by
  have h : AdjoinRoot.mk E.toAffine.polynomial (Y ^ 2 + C (C E.a₁ * X + C E.a₃) * Y -
      C (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)) = 0 := AdjoinRoot.mk_self
  have hC : ∀ c : K, AdjoinRoot.mk E.toAffine.polynomial (C (C c)) =
      algebraMap K E.toAffine.CoordinateRing c := fun _ => rfl
  have hx : AdjoinRoot.mk E.toAffine.polynomial (C X) = xCoord₃ E := rfl
  have hy : AdjoinRoot.mk E.toAffine.polynomial Y = yCoord₃ E := AdjoinRoot.mk_X
  simp only [map_add, map_sub, map_mul, map_pow, hC, hx, hy] at h
  linear_combination h

/-- The Weierstrass equation, transported along a `K`-algebra map. -/
lemma weierstrass_rel_map₃ {B : Type*} [CommRing B] [Algebra K B]
    (c : E.toAffine.CoordinateRing →ₐ[K] B) :
    c (yCoord₃ E) ^ 2 + (algebraMap K B E.a₁ * c (xCoord₃ E) + algebraMap K B E.a₃) *
      c (yCoord₃ E) = c (xCoord₃ E) ^ 3 + algebraMap K B E.a₂ * c (xCoord₃ E) ^ 2 +
        algebraMap K B E.a₄ * c (xCoord₃ E) + algebraMap K B E.a₆ := by
  have h := congrArg c (weierstrass_rel₃ E)
  simpa only [map_add, map_mul, map_pow, AlgHom.commutes] using h

/-- `K`-algebra maps out of `K[E]` are determined by the images of `x` and `y`. -/
lemma algHom_ext₃ {B : Type*} [CommRing B] [Algebra K B]
    {f g : E.toAffine.CoordinateRing →ₐ[K] B} (hx : f (xCoord₃ E) = g (xCoord₃ E))
    (hy : f (yCoord₃ E) = g (yCoord₃ E)) : f = g := by
  have hpoly : f.comp (IsScalarTower.toAlgHom K K[X] E.toAffine.CoordinateRing) =
      g.comp (IsScalarTower.toAlgHom K K[X] E.toAffine.CoordinateRing) :=
    Polynomial.algHom_ext hx
  have hring : f.toRingHom.comp (algebraMap K[X] E.toAffine.CoordinateRing) =
      g.toRingHom.comp (algebraMap K[X] E.toAffine.CoordinateRing) :=
    RingHom.ext fun p => DFunLike.congr_fun hpoly p
  refine AlgHom.ext fun r => ?_
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
  change f.toRingHom _ = g.toRingHom _
  rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂, hring]
  rw [show f.toRingHom (AdjoinRoot.root E.toAffine.polynomial) =
    g.toRingHom (AdjoinRoot.root E.toAffine.polynomial) from hy]

/-- **Two `K`-algebra maps `K[E] → B` into a domain agreeing on `x` agree up to `[-1]`**:
`b = a` or `b = a ∘ ν` (`y` and `ν y` are the two roots of the Weierstrass equation over
`K[x]`). -/
theorem eq_or_eq_neg_of_apply_x {B : Type*} [CommRing B] [IsDomain B] [Algebra K B]
    (a b : E.toAffine.CoordinateRing →ₐ[K] B) (hx : a (xCoord₃ E) = b (xCoord₃ E)) :
    b = a ∨ b = a.comp (negCoordAlgEquiv E).toAlgHom := by
  have ha := weierstrass_rel_map₃ E a
  have hb := weierstrass_rel_map₃ E b
  have hν : a (negCoordAlgEquiv E (yCoord₃ E)) =
      -a (yCoord₃ E) - (algebraMap K B E.a₁ * a (xCoord₃ E) + algebraMap K B E.a₃) := by
    rw [negCoordAlgEquiv_y]
    simp only [map_sub, map_neg, map_add, map_mul, AlgHom.commutes]
  rw [← hx] at hb
  have hprod : (b (yCoord₃ E) - a (yCoord₃ E)) *
      (b (yCoord₃ E) - a (negCoordAlgEquiv E (yCoord₃ E))) = 0 := by
    rw [hν]
    linear_combination hb - ha
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inl (algHom_ext₃ E hx.symm (sub_eq_zero.mp h))
  · refine Or.inr (algHom_ext₃ E ?_ (sub_eq_zero.mp h))
    change b (xCoord₃ E) = a (negCoordAlgEquiv E (xCoord₃ E))
    rw [negCoordAlgEquiv_x, hx]

end Neg

/-! ### Main statements -/

section Main

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- **The core property of `(E ∖ O)/±1`, dichotomy form**: for `K`-algebra maps
`a, b : K[E] → B` into a domain, each finite étale, `b = a` or `b = a ∘ [-1]`. -/
theorem hemiCore_eq_or_eq_neg (hj : ∀ c ∈ excJ, E.j ≠ (c : K)) {B : Type} [CommRing B]
    [IsDomain B] [Algebra K B] (a b : E.toAffine.CoordinateRing →ₐ[K] B)
    (haf : a.toRingHom.Finite) (hae : a.toRingHom.Etale) (hbf : b.toRingHom.Finite)
    (hbe : b.toRingHom.Etale) :
    b = a ∨ b = a.comp (negCoordAlgEquiv E).toAlgHom :=
  eq_or_eq_neg_of_apply_x E a b (hemiCore_apply_x E hj a b haf hae hbf hbe)

open AlgebraicGeometry CurvesJacobian.Cusp

/-- Ring-level finite étaleness from `IsFiniteEtale (Spec.map _)`, after composing with
`Γ(E ∖ O) ≅ K[E]`. -/
lemma finite_etale_of_sections₃ {B : Type} [CommRing B] [Algebra K B]
    (a : Γ(curveE E, XE E) →ₐ[K] B)
    (ha : IsFiniteEtale (Spec.map (CommRingCat.ofHom a.toRingHom))) :
    (a.comp (sectionsXEAlgEquiv E).symm.toAlgHom).toRingHom.Finite ∧
      (a.comp (sectionsXEAlgEquiv E).symm.toAlgHom).toRingHom.Etale := by
  rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom,
    RingHom.FiniteEtale.iff_finite_and_etale] at ha
  exact ⟨finite_comp_equiv₃ a.toRingHom (sectionsXEAlgEquiv E).symm.toRingEquiv ha.2,
    etale_comp_equiv₃ a.toRingHom (sectionsXEAlgEquiv E).symm.toRingEquiv ha.1⟩

/-- **The core property, scheme form**: for `K`-algebra maps `a, b : Γ(E ∖ O) → B` into a
domain with `Spec B → Spec Γ(E ∖ O)` finite étale, `a` and `b` agree on `x`. -/
theorem hemiCore_apply_x_sections (hj : ∀ c ∈ excJ, E.j ≠ (c : K)) {B : Type} [CommRing B]
    [IsDomain B] [Algebra K B] (a b : Γ(curveE E, XE E) →ₐ[K] B)
    (ha : IsFiniteEtale (Spec.map (CommRingCat.ofHom a.toRingHom)))
    (hb : IsFiniteEtale (Spec.map (CommRingCat.ofHom b.toRingHom))) :
    a ((sectionsXEAlgEquiv E).symm (algebraMap K[X] E.toAffine.CoordinateRing X)) =
      b ((sectionsXEAlgEquiv E).symm (algebraMap K[X] E.toAffine.CoordinateRing X)) := by
  obtain ⟨haf, hae⟩ := finite_etale_of_sections₃ E a ha
  obtain ⟨hbf, hbe⟩ := finite_etale_of_sections₃ E b hb
  exact hemiCore_apply_x E hj _ _ haf hae hbf hbe

/-- **The core property, scheme form, dichotomy**: `b = a` or `b = a ∘ [-1]` on `Γ(E ∖ O)`,
with `[-1]` transported along `sectionsXEAlgEquiv E`. -/
theorem hemiCore_eq_or_eq_neg_sections (hj : ∀ c ∈ excJ, E.j ≠ (c : K)) {B : Type}
    [CommRing B] [IsDomain B] [Algebra K B] (a b : Γ(curveE E, XE E) →ₐ[K] B)
    (ha : IsFiniteEtale (Spec.map (CommRingCat.ofHom a.toRingHom)))
    (hb : IsFiniteEtale (Spec.map (CommRingCat.ofHom b.toRingHom))) :
    b = a ∨ b = a.comp ((sectionsXEAlgEquiv E).trans
      ((negCoordAlgEquiv E).trans (sectionsXEAlgEquiv E).symm)).toAlgHom := by
  obtain ⟨haf, hae⟩ := finite_etale_of_sections₃ E a ha
  obtain ⟨hbf, hbe⟩ := finite_etale_of_sections₃ E b hb
  rcases hemiCore_eq_or_eq_neg E hj _ _ haf hae hbf hbe with h | h
  · left
    ext s
    have := DFunLike.congr_fun h (sectionsXEAlgEquiv E s)
    simpa using this
  · right
    ext s
    have := DFunLike.congr_fun h (sectionsXEAlgEquiv E s)
    simpa using this

end Main

end Iut.Reconstruction.HemiCore
