/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.HemiGenuine
import CurvesJacobian.Cusp.HemiTwistArith

/-!
# `Π_{C_F} ↪ Π_{C_{F_mod}}` for iut's genuine orbicurves (MR8, IUT I Def. 3.1 (b))

IUT's `C_{F_mod}` is the `F_mod`-model of the hemi-elliptic orbicurve `C_F = X_F / ±1`: its coarse
space is the `x`-line, which does not see quadratic twists. Let `K = F_mod` be a number field,
`E'` an elliptic curve over `K` (e.g. `WeierstrassCurve.ofJ j`) with `j(E') ∉ {0, 1728}`,
`M ⊆ K̄` finite Galois over `K` (IUT's `F`) and `E` an elliptic curve over `M` with
`j(E) = j(E')`. This file shows that iut's genuine `π₁` of `C_M = (E ∖ {O}) / ±1` is an open
normal subgroup of index `[M : K]` of the genuine `π₁` of `C_K = (E' ∖ {O}) / ±1`
(`genuine_CM_emb`), through curves-jacobian's twist (`hemiTwData`, `hemiTw_constExt`):

* generic: `galConjHom φ`, `σ ↦ φ σ φ⁻¹`, for `φ : Ω₁ ≃+* Ω₂` with `φ⁻¹(P₂) ⊆ P₁` (an injective
  continuous homomorphism `Gal(Ω₁ / P₁) → Gal(Ω₂ / P₂)`), and `pi1CongrEmb`: the transport of
  `H ⧸ ⟨⟨S⟩⟩` along such an embedding when it maps `H₁` onto `H₂` and matches `S₁`, `S₂`;
* `genuinePi1CongrEmb`: iut's genuine `π₁(C)` transported along `φ : k(E)^alg ≃ Ω₂` onto the
  group `H ⧸ ⟨⟨S⟩⟩` of pi1's Galois data `D` when conjugation by `φ` maps `Gal(k(E)^alg / k(x))`
  onto `D.H`;
* `twOmegaEquiv : k(E)^alg ≃+* K(Ē')^alg` extending curves-jacobian's embedding
  `twRho : M[E] → K(Ē')^alg` (`x_E ↦ xTw = u2⁻¹ (x' − r)`, `y_E ↦ yTw`);
* **`genuinePi1TwEquiv`**: `(pmQuotient (oncePunctured E)).genuinePi1 ≃ₜ* Π_{C_M}` of
  `hemiTwData E' M E u2 r`;
* **`genuine_CM_emb`**: the open embedding of genuine groups, normal, of index `[M : K]`.
-/

open CategoryTheory AlgebraicGeometry CurvesJacobian CurvesJacobian.Cusp Belyi Belyi.Anabelian
  Pi1.Orbifold AffOrbicurve Topology Polynomial

noncomputable section

namespace Iut.Reconstruction.HemiGenuine

universe u

/-! ### Conjugation into a Galois group over a smaller field -/

section GalConjHom

variable {P₁ P₂ Ω₁ Ω₂ : Type u} [Field P₁] [Field P₂] [Field Ω₁] [Field Ω₂] [Algebra P₁ Ω₁]
  [Algebra P₂ Ω₂] (φ : Ω₁ ≃+* Ω₂)
  (hφ : ∀ y ∈ (algebraMap P₂ Ω₂).range, φ.symm y ∈ (algebraMap P₁ Ω₁).range)

/-- `σ ↦ φ σ φ⁻¹`, for `φ⁻¹(P₂) ⊆ P₁`. -/
def galConjFun' (σ : Ω₁ ≃ₐ[P₁] Ω₁) : Ω₂ ≃ₐ[P₂] Ω₂ :=
  AlgEquiv.ofRingEquiv (f := (φ.symm.trans σ.toRingEquiv).trans φ) fun c => by
    obtain ⟨c', hc'⟩ := hφ (algebraMap P₂ Ω₂ c) ⟨c, rfl⟩
    change φ (σ (φ.symm (algebraMap P₂ Ω₂ c))) = _
    rw [← hc', AlgEquiv.commutes, hc', RingEquiv.apply_symm_apply]

/-- **Conjugation by `φ`**, `Gal(Ω₁ / P₁) → Gal(Ω₂ / P₂)`. -/
def galConjHom : (Ω₁ ≃ₐ[P₁] Ω₁) →* (Ω₂ ≃ₐ[P₂] Ω₂) where
  toFun := galConjFun' φ hφ
  map_one' := AlgEquiv.ext fun y => by
    change φ (φ.symm y) = y
    rw [RingEquiv.apply_symm_apply]
  map_mul' σ τ := AlgEquiv.ext fun y => by
    change φ ((σ * τ) (φ.symm y)) = φ (σ (φ.symm (φ (τ (φ.symm y)))))
    rw [RingEquiv.symm_apply_apply, AlgEquiv.mul_apply]

lemma galConjHom_apply (σ : Ω₁ ≃ₐ[P₁] Ω₁) (y : Ω₂) :
    galConjHom φ hφ σ y = φ (σ (φ.symm y)) := rfl

lemma galConjHom_apply' (σ : Ω₁ ≃ₐ[P₁] Ω₁) (x : Ω₁) :
    galConjHom φ hφ σ (φ x) = φ (σ x) := by
  rw [galConjHom_apply, RingEquiv.symm_apply_apply]

lemma galConjHom_injective : Function.Injective (galConjHom φ hφ) := fun σ τ h =>
  AlgEquiv.ext fun x => φ.injective (by
    rw [← galConjHom_apply' φ hφ σ x, ← galConjHom_apply' φ hφ τ x, h])

lemma continuous_galConjHom [Algebra.IsAlgebraic P₁ Ω₁] : Continuous (galConjHom φ hφ) := by
  refine continuous_of_continuousAt_one (galConjHom φ hφ) ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff P₂ Ω₂ U).1 hU
  rw [Filter.mem_map]
  let b := Module.finBasis P₂ E
  let s : Set Ω₁ := Set.range fun i => φ.symm (b i : Ω₂)
  haveI : Finite s := Set.finite_range _ |>.to_subtype
  haveI : FiniteDimensional P₁ (IntermediateField.adjoin P₁ s) :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic (R := P₁) x).isIntegral
  refine (krullTopology_mem_nhds_one_iff P₁ Ω₁ _).2
    ⟨IntermediateField.adjoin P₁ s, inferInstance, fun σ hσ => hEU ?_⟩
  rw [SetLike.mem_coe] at hσ ⊢
  refine mem_fixingSubgroup_of_basis b fun i => ?_
  have h := (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ (φ.symm (b i : Ω₂))
    (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  change φ (σ (φ.symm (b i : Ω₂))) = _
  rw [h, RingEquiv.apply_symm_apply]

/-- `φ` maps the inertia group of `W` into that of `φ(W)`, and conversely. -/
lemma galConjHom_mem_inertia_iff (σ : Ω₁ ≃ₐ[P₁] Ω₁) (W : ValuationSubring Ω₁) :
    galConjHom φ hφ σ ∈ GaloisPi1.inertia (W.comap φ.symm.toRingHom) ↔
      σ ∈ GaloisPi1.inertia W := by
  simp only [GaloisPi1.inertia, Set.mem_setOf_eq]
  have key : ∀ a : Ω₁, (W.comap φ.symm.toRingHom).valuation (φ a) < 1 ↔ W.valuation a < 1 := by
    intro a
    rw [valuation_lt_one_iff_mem', valuation_lt_one_iff_mem']
    simp only [ValuationSubring.mem_comap, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply, map_inv₀, map_eq_zero_iff _ φ.injective]
  constructor
  · intro h a ha
    have := h (φ a) (by simpa [ValuationSubring.mem_comap] using ha)
    rw [galConjHom_apply', ← map_sub, key] at this
    exact this
  · intro h b hb
    obtain ⟨a, rfl⟩ := φ.surjective b
    have ha : a ∈ W := by simpa [ValuationSubring.mem_comap] using hb
    rw [galConjHom_apply', ← map_sub, key]
    exact h a ha

end GalConjHom

/-! ### Transport of `H ⧸ ⟨⟨S⟩⟩` along an embedding of Galois groups -/

section Pi1CongrEmb

variable {P₁ P₂ Ω₁ Ω₂ : Type u} [Field P₁] [Field P₂] [Field Ω₁] [Field Ω₂] [Algebra P₁ Ω₁]
  [Algebra P₂ Ω₂] [IsGalois P₁ Ω₁] [IsGalois P₂ Ω₂]
  (e : (Ω₁ ≃ₐ[P₁] Ω₁) →* (Ω₂ ≃ₐ[P₂] Ω₂)) (he : Continuous e) (hinj : Function.Injective e)
  {H₁ : Subgroup (Ω₁ ≃ₐ[P₁] Ω₁)} {S₁ : Set (Ω₁ ≃ₐ[P₁] Ω₁)}
  (hH₁ : IsClosed (H₁ : Set (Ω₁ ≃ₐ[P₁] Ω₁)))
  {H₂ : Subgroup (Ω₂ ≃ₐ[P₂] Ω₂)} {S₂ : Set (Ω₂ ≃ₐ[P₂] Ω₂)}
  (hH₂ : IsClosed (H₂ : Set (Ω₂ ≃ₐ[P₂] Ω₂)))
  (hH : ∀ σ, σ ∈ H₁ → e σ ∈ H₂) (hsurj : ∀ τ ∈ H₂, ∃ σ ∈ H₁, e σ = τ)
  (hS : ∀ σ, σ ∈ S₁ ↔ e σ ∈ S₂) (hS₂ : S₂ ⊆ H₂)

include he hinj hH hsurj hS hS₂ in
lemma map_ambientKernel_emb :
    (GaloisPi1.ambientKernel H₁ S₁).map e = GaloisPi1.ambientKernel H₂ S₂ := by
  have hconj : (Subgroup.closure (GaloisPi1.conjSet H₁ S₁)).map e =
      Subgroup.closure (GaloisPi1.conjSet H₂ S₂) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_image, GaloisPi1.conjSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, ⟨h, hh, s, hs, rfl⟩, rfl⟩
      exact ⟨e h, hH h hh, e s, (hS s).1 hs, by simp [map_mul, map_inv]⟩
    · rintro ⟨h, hh, s, hs, rfl⟩
      obtain ⟨h', hh', rfl⟩ := hsurj h hh
      obtain ⟨s', -, rfl⟩ := hsurj s (hS₂ hs)
      exact ⟨h' * s' * h'⁻¹, ⟨h', hh', s', (hS s').2 hs, rfl⟩, by simp [map_mul, map_inv]⟩
  have hce : IsClosedEmbedding e := he.isClosedEmbedding hinj
  unfold GaloisPi1.ambientKernel
  rw [← hconj]
  apply SetLike.coe_injective
  rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe,
    Subgroup.coe_map]
  exact (hce.closure_image_eq _).symm

/-- The restriction `H₁ → H₂` of `e`. -/
def restrictHEmbHom : H₁ →* H₂ :=
  (e.restrict H₁).codRestrict H₂ fun σ => hH σ.1 σ.2

omit [IsGalois P₁ Ω₁] [IsGalois P₂ Ω₂] in
include hinj hsurj in
lemma restrictHEmbHom_bijective : Function.Bijective (restrictHEmbHom e hH) := by
  refine ⟨fun x y h => Subtype.ext (hinj (congrArg Subtype.val h)), fun y => ?_⟩
  obtain ⟨σ, hσ, h⟩ := hsurj y.1 y.2
  exact ⟨⟨σ, hσ⟩, Subtype.ext h⟩

/-- `e` restricted to a topological isomorphism `H₁ ≃ₜ* H₂` (compact to Hausdorff). -/
def restrictHEmb : H₁ ≃ₜ* H₂ :=
  haveI : CompactSpace H₁ := isCompact_iff_compactSpace.mp hH₁.isCompact
  let f := MulEquiv.ofBijective _ (restrictHEmbHom_bijective e hinj hH hsurj)
  have hf : Continuous f := (he.comp continuous_subtype_val).subtype_mk _
  { f with
    continuous_toFun := hf
    continuous_invFun := hf.continuous_symm_of_equiv_compact_to_t2 (f := f.toEquiv) }

lemma restrictHEmb_apply (x : H₁) :
    ((restrictHEmb e he hinj hH₁ hH hsurj x : H₂) : Ω₂ ≃ₐ[P₂] Ω₂) = e x := rfl

include hS hS₂ in
lemma map_kernel_emb : (GaloisPi1.kernel H₁ S₁).map
      ((restrictHEmb e he hinj hH₁ hH hsurj).toMulEquiv : H₁ →* H₂) =
    GaloisPi1.kernel H₂ S₂ := by
  have hamb : ∀ σ, σ ∈ GaloisPi1.ambientKernel H₁ S₁ ↔ e σ ∈ GaloisPi1.ambientKernel H₂ S₂ :=
    fun σ => by
      rw [← map_ambientKernel_emb e he hinj hH hsurj hS hS₂]
      exact (Subgroup.mem_map_iff_mem hinj).symm
  ext y
  obtain ⟨x, rfl⟩ := (restrictHEmb e he hinj hH₁ hH hsurj).surjective y
  constructor
  · rintro ⟨x', hx', h⟩
    obtain rfl : x' = x := (restrictHEmb e he hinj hH₁ hH hsurj).injective h
    exact (hamb x'.1).1 hx'
  · intro h
    exact ⟨x, (hamb x.1).2 h, rfl⟩

/-- **Transport of `H ⧸ ⟨⟨S⟩⟩` along an embedding** of Galois groups mapping `H₁` onto `H₂` and
matching `S₁`, `S₂`. -/
def pi1CongrEmb : GaloisPi1.pi1 H₁ S₁ hH₁ ≃ₜ* GaloisPi1.pi1 H₂ S₂ hH₂ where
  toMulEquiv := QuotientGroup.congr _ _ (restrictHEmb e he hinj hH₁ hH hsurj).toMulEquiv
    (map_kernel_emb e he hinj hH₁ hH hsurj hS hS₂)
  continuous_toFun := by
    change Continuous (QuotientGroup.congr (GaloisPi1.kernel H₁ S₁) (GaloisPi1.kernel H₂ S₂)
      (restrictHEmb e he hinj hH₁ hH hsurj).toMulEquiv
      (map_kernel_emb e he hinj hH₁ hH hsurj hS hS₂))
    rw [(QuotientGroup.isQuotientMap_mk (GaloisPi1.kernel H₁ S₁)).continuous_iff]
    exact QuotientGroup.continuous_mk.comp (restrictHEmb e he hinj hH₁ hH hsurj).continuous
  continuous_invFun := by
    change Continuous (QuotientGroup.congr (GaloisPi1.kernel H₁ S₁) (GaloisPi1.kernel H₂ S₂)
      (restrictHEmb e he hinj hH₁ hH hsurj).toMulEquiv
      (map_kernel_emb e he hinj hH₁ hH hsurj hS hS₂)).symm
    rw [QuotientGroup.congr_symm,
      (QuotientGroup.isQuotientMap_mk (GaloisPi1.kernel H₂ S₂)).continuous_iff]
    exact QuotientGroup.continuous_mk.comp (restrictHEmb e he hinj hH₁ hH hsurj).symm.continuous

end Pi1CongrEmb

/-! ### The genuine `π₁` of `C` transported along an embedding of Galois groups -/

section GenuineEmb

open Iut.Anabelian Iut.Anabelian.Genuine WeierstrassCurve

attribute [local instance low] Classical.propDecidable

variable {L : Type u} [Field L] [CharZero L] (E : WeierstrassCurve L) [E.IsElliptic]
  -- the instances on the target side are those of `D`, unified rather than synthesized
  {k Ω₂ : Type u} {_ : Field k} {_ : Field Ω₂} {_ : Algebra k Ω₂} {t : Ω₂}
  [IsGalois (K₀ k t) Ω₂] (D : GaloisData k t) (φ : Genuine.Ω E ≃+* Ω₂)
  (hφ : ∀ y ∈ (algebraMap (K₀ k t) Ω₂).range,
    φ.symm y ∈ (algebraMap (Genuine.baseField E) (Genuine.Ω E)).range)

/-- **iut's genuine `π₁` of `C = (E ∖ {O}) / ±1`, transported along `φ : k(E)^alg ≃ Ω₂`** onto the
group `H ⧸ ⟨⟨S⟩⟩` of Galois data `D` (with `φ⁻¹(k(t)) ⊆ k(x)`), when conjugation by `φ` maps
`Gal(k(E)^alg / k(x))` onto `D.H` and matches the inertia elements. -/
def genuinePi1CongrEmb (hH : ∀ σ : Gal E, galConjHom φ hφ σ ∈ D.H)
    (hsurj : ∀ τ ∈ D.H, ∃ σ : Gal E, galConjHom φ hφ σ = τ)
    (hS : ∀ σ : Gal E, σ ∈ SgenC E 1 ⊥ ↔ galConjHom φ hφ σ ∈ D.S) :
    (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).genuinePi1 ≃ₜ*
      GaloisPi1.pi1 D.H D.S D.isClosed_H :=
  pi1CongrEmb (galConjHom φ hφ) (continuous_galConjHom φ hφ) (galConjHom_injective φ hφ)
    (isClosed_Hgp E 1 ⊥ true) D.isClosed_H (fun σ _ => hH σ)
    (fun τ hτ => (hsurj τ hτ).elim fun σ h => ⟨σ, mem_Hgp_one_bot_true E σ, h⟩) hS
    (fun _ h => D.le h.1)

end GenuineEmb

/-! ### The twisted curve inside `K(Ē')^alg` -/

section Twist

open Iut.Anabelian Iut.Anabelian.Genuine WeierstrassCurve

-- the decidability instances of `Iut.Anabelian.Genuine` (classical, also for `↥M`)
attribute [local instance low] Classical.propDecidable


variable {K : Type u} [Field K] [NumberField K] (E' : WeierstrassCurve K) [E'.IsElliptic]
  (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E'))))
  (E : WeierstrassCurve M) (u2 r : M) (hu2 : u2 ≠ 0)

omit [NumberField K] [E'.IsElliptic] in
/-- The classical decidable equality of `M` used by `Iut.Anabelian.Genuine` and
`Iut.Anabelian.Orbicurve` (where it is found for a generic field). Without it, the instance found
for `↥M` goes through `Subtype` and differs from the one inside `oncePunctured E`. -/
abbrev decEqM : DecidableEq M := fun a b => Classical.propDecidable (a = b)

attribute [local instance high] decEqM

/-- `ρ : M[E] → K(Ē')^alg` (curves-jacobian's `twRho`), injective. -/
abbrev twRho' : E.toAffine.CoordinateRing →+* FFClosure (curveE E') :=
  twRho (coordT (xN E')) M E u2 r

include hu2 in
lemma twRho'_injective : Function.Injective (twRho' E' M E u2 r) :=
  twRho_injective _ M E r (hemiData E').transcendental hu2

/-- `ρ` on the function field `M(E) → K(Ē')^alg`. -/
def twRhoF : E.toAffine.FunctionField →+* FFClosure (curveE E') :=
  IsFractionRing.lift (twRho'_injective E' M E u2 r hu2)

lemma twRhoF_algebraMap (a : E.toAffine.CoordinateRing) :
    twRhoF E' M E u2 r hu2 (algebraMap _ E.toAffine.FunctionField a) = twRho' E' M E u2 r a :=
  IsFractionRing.lift_algebraMap _ _

lemma algebraMap_K_eq_constι₃ (c : K) :
    algebraMap K (FFClosure (curveE E')) c = constι₃ M (algebraMap K M c) := rfl

lemma twRhoF_C (m : M) :
    twRhoF E' M E u2 r hu2 (algebraMap M E.toAffine.FunctionField m) = constι₃ M m := by
  rw [IsScalarTower.algebraMap_apply M E.toAffine.CoordinateRing E.toAffine.FunctionField,
    twRhoF_algebraMap]
  change twRho _ M E u2 r (AdjoinRoot.of _ (C m)) = _
  rw [twRho_of, eval₂_C]

lemma twRhoF_xF : twRhoF E' M E u2 r hu2 (xF E) = xTw (coordT (xN E')) M u2 r := by
  rw [xF, twRhoF_algebraMap]
  change twRho _ M E u2 r (AdjoinRoot.of _ X) = _
  rw [twRho_of, eval₂_X]

lemma twRhoF_yF : twRhoF E' M E u2 r hu2 (yF E) = yTw (coordT (xN E')) M E u2 r := by
  rw [yF, twRhoF_algebraMap]
  exact twRho_root _ M E u2 r

/-- The image `M(E) ⊆ K(Ē')^alg` of `ρ`, as an intermediate field over `K`. -/
def twLK : IntermediateField K (FFClosure (curveE E')) :=
  (Subfield.map (twRhoF E' M E u2 r hu2) ⊤).toIntermediateField fun c =>
    ⟨algebraMap M E.toAffine.FunctionField (algebraMap K M c), trivial, by
      rw [twRhoF_C]; rfl⟩

lemma t_eq_twRhoF : coordT (xN E') =
    twRhoF E' M E u2 r hu2 (algebraMap M _ u2 * xF E + algebraMap M _ r) := by
  rw [map_add, map_mul, twRhoF_C, twRhoF_C, twRhoF_xF]
  exact (constι₃_mul_xTw _ M hu2 r).symm

lemma le_twLK : K₀ K (coordT (xN E')) ≤ twLK E' M E u2 r hu2 := by
  rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact ⟨_, trivial, (t_eq_twRhoF E' M E u2 r hu2).symm⟩

/-- `M(E)` as an intermediate field of `K(Ē')^alg / K(x')`. -/
abbrev twL : IntermediateField (K₀ K (coordT (xN E'))) (FFClosure (curveE E')) :=
  IntermediateField.extendScalars (le_twLK E' M E u2 r hu2)

/-- `M(E) ≃ twL`. -/
def twFFEquiv : E.toAffine.FunctionField ≃+* twL E' M E u2 r hu2 :=
  RingEquiv.ofBijective
    ((twRhoF E' M E u2 r hu2).codRestrict (twL E' M E u2 r hu2).toSubalgebra fun f =>
      ⟨f, trivial, rfl⟩)
    ⟨fun a b h => (twRhoF E' M E u2 r hu2).injective (congrArg Subtype.val h), fun y => by
      obtain ⟨f, -, hf⟩ := y.2
      exact ⟨f, Subtype.ext hf⟩⟩

lemma coe_twFFEquiv (f : E.toAffine.FunctionField) :
    ((twFFEquiv E' M E u2 r hu2 f : twL E' M E u2 r hu2) : FFClosure (curveE E')) =
      twRhoF E' M E u2 r hu2 f := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- the instance searches through `M(E)` for `M ⊆ K̄ ⊆ K(Ē')^alg` exceed the default budget
instance isAlgClosure_twL : IsAlgClosure (twL E' M E u2 r hu2) (FFClosure (curveE E')) :=
  ⟨inferInstance, inferInstance⟩

set_option synthInstance.maxHeartbeats 200000 in
-- the instance searches through `M(E)` for `M ⊆ K̄ ⊆ K(Ē')^alg` exceed the default budget
/-- **`k(E)^alg ≃ K(Ē')^alg`** extending `ρ : M(E) → K(Ē')^alg`. -/
def twOmegaEquiv : Genuine.Ω E ≃+* FFClosure (curveE E') :=
  IsAlgClosure.equivOfEquiv (Genuine.Ω E) (FFClosure (curveE E')) (twFFEquiv E' M E u2 r hu2)

set_option synthInstance.maxHeartbeats 200000 in
-- the instance searches and unifications over `M ⊆ K̄ ⊆ K(Ē')^alg` exceed the default budget
lemma twOmegaEquiv_algebraMap (f : E.toAffine.FunctionField) :
    twOmegaEquiv E' M E u2 r hu2 (algebraMap _ (Genuine.Ω E) f) = twRhoF E' M E u2 r hu2 f :=
  IsAlgClosure.equivOfEquiv_algebraMap _ _ _ f

set_option synthInstance.maxHeartbeats 200000 in
-- the instance searches and unifications over `M ⊆ K̄ ⊆ K(Ē')^alg` exceed the default budget
lemma twOmegaEquiv_C (m : M) :
    twOmegaEquiv E' M E u2 r hu2 (algebraMap M (Genuine.Ω E) m) = constι₃ M m := by
  rw [IsScalarTower.algebraMap_apply M E.toAffine.FunctionField (Genuine.Ω E),
    twOmegaEquiv_algebraMap, twRhoF_C]

lemma twOmegaEquiv_xG : twOmegaEquiv E' M E u2 r hu2 (xG E) = xTw (coordT (xN E')) M u2 r := by
  rw [xG, twOmegaEquiv_algebraMap, twRhoF_xF]

lemma twOmegaEquiv_yG : twOmegaEquiv E' M E u2 r hu2 (yG E) = yTw (coordT (xN E')) M E u2 r := by
  rw [yG, twOmegaEquiv_algebraMap, twRhoF_yF]

lemma twOmegaEquiv_symm_t : (twOmegaEquiv E' M E u2 r hu2).symm (coordT (xN E')) =
    algebraMap M (Genuine.Ω E) u2 * xG E + algebraMap M (Genuine.Ω E) r := by
  apply (twOmegaEquiv E' M E u2 r hu2).injective
  rw [RingEquiv.apply_symm_apply, map_add, map_mul, twOmegaEquiv_C, twOmegaEquiv_C,
    twOmegaEquiv_xG]
  exact (constι₃_mul_xTw _ M hu2 r).symm

lemma twOmegaEquiv_symm_C (m : M) :
    (twOmegaEquiv E' M E u2 r hu2).symm (constι₃ M m) = algebraMap M (Genuine.Ω E) m := by
  rw [← twOmegaEquiv_C E' M E u2 r hu2, RingEquiv.symm_apply_apply]

/-- `φ⁻¹(K(x')) ⊆ M(x_E)`. -/
lemma twOmegaEquiv_symm_mem_range :
    ∀ y ∈ (algebraMap (K₀ K (coordT (xN E'))) (FFClosure (curveE E'))).range,
      (twOmegaEquiv E' M E u2 r hu2).symm y ∈
        (algebraMap (Genuine.baseField E) (Genuine.Ω E)).range := by
  let Z : IntermediateField K (FFClosure (curveE E')) :=
    ((Genuine.baseField E).toSubfield.comap
      (twOmegaEquiv E' M E u2 r hu2).symm.toRingHom).toIntermediateField fun c => by
        rw [Subfield.mem_comap, algebraMap_K_eq_constι₃ E' M]
        change (twOmegaEquiv E' M E u2 r hu2).symm (constι₃ M _) ∈ Genuine.baseField E
        rw [twOmegaEquiv_symm_C]
        exact (Genuine.baseField E).algebraMap_mem _
  have hle : K₀ K (coordT (xN E')) ≤ Z := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    change (twOmegaEquiv E' M E u2 r hu2).symm (coordT (xN E')) ∈ Genuine.baseField E
    rw [twOmegaEquiv_symm_t]
    exact add_mem (mul_mem ((Genuine.baseField E).algebraMap_mem _) (xG_mem_baseField E))
      ((Genuine.baseField E).algebraMap_mem _)
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨_, hle c.2⟩, rfl⟩

/-- `Gal(k(E)^alg / M(x_E)) → Gal(K(Ē')^alg / K(x'))`, conjugation by `φ`. -/
abbrev twGalHom :
    Genuine.Gal E →* (FFClosure (curveE E') ≃ₐ[K₀ K (coordT (xN E'))] FFClosure (curveE E')) :=
  galConjHom (twOmegaEquiv E' M E u2 r hu2) (twOmegaEquiv_symm_mem_range E' M E u2 r hu2)

lemma twGalHom_apply' (σ : Genuine.Gal E) (z : Genuine.Ω E) :
    twGalHom E' M E u2 r hu2 σ (twOmegaEquiv E' M E u2 r hu2 z) =
      twOmegaEquiv E' M E u2 r hu2 (σ z) :=
  galConjHom_apply' _ _ σ z

lemma twGalHom_fix_C (σ : Genuine.Gal E) (m : M) :
    twGalHom E' M E u2 r hu2 σ (constι₃ M m) = constι₃ M m := by
  rw [← twOmegaEquiv_C E' M E u2 r hu2, twGalHom_apply']
  congr 1
  exact σ.commutes ⟨_, (Genuine.baseField E).algebraMap_mem m⟩

variable [FiniteDimensional K M] [IsGalois K M]

/-- **The image is `H = Gal(Ω / K(x')(M))`.** -/
lemma twGalHom_mem_H (σ : Genuine.Gal E) :
    twGalHom E' M E u2 r hu2 σ ∈ (hemiTwData E' M E u2 r).H := by
  change _ ∈ constFixer₃ (coordT (xN E')) M
  rw [← fixingSubgroup_adjoin_constSet₃, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  refine (IntermediateField.forall_mem_adjoin_smul_eq_self_iff (F := K₀ K (coordT (xN E')))
    (S := constSet₃ M) (twGalHom E' M E u2 r hu2 σ)).2 ?_ x hx
  rintro _ ⟨m, rfl⟩
  exact twGalHom_fix_C E' M E u2 r hu2 σ m

set_option maxHeartbeats 1000000 in
-- the instance searches and unifications over `M ⊆ K̄ ⊆ K(Ē')^alg` exceed the default budget
lemma twGalHom_surj (τ) (hτ : τ ∈ (hemiTwData E' M E u2 r).H) :
    ∃ σ : Genuine.Gal E, σ ∈ (⊤ : Subgroup (Genuine.Gal E)) ∧ twGalHom E' M E u2 r hu2 σ = τ := by
  set φ := twOmegaEquiv E' M E u2 r hu2
  have hτ' : τ ∈ constFixer₃ (coordT (xN E')) M := hτ
  let σM : Genuine.Ω E ≃ₐ[M] Genuine.Ω E :=
    AlgEquiv.ofRingEquiv (f := (φ.trans τ.toRingEquiv).trans φ.symm) fun m => by
      change φ.symm (τ (φ (algebraMap M (Genuine.Ω E) m))) = _
      rw [twOmegaEquiv_C, fix_constι₃_tw _ M hτ', twOmegaEquiv_symm_C]
  have hfix : ∀ z ∈ K₀ M (xG E), σM z = z := by
    intro z hz
    refine (IntermediateField.forall_mem_adjoin_smul_eq_self_iff (F := M) (S := {xG E}) σM).2
      ?_ z hz
    rintro _ rfl
    change φ.symm (τ (φ (xG E))) = xG E
    rw [twOmegaEquiv_xG, fix_xTw _ M u2 r hτ', ← twOmegaEquiv_xG E' M E u2 r hu2,
      RingEquiv.symm_apply_apply]
  let σ : Genuine.Gal E := AlgEquiv.ofRingEquiv (f := σM.toRingEquiv) fun c => by
    have hc : (c : Genuine.Ω E) ∈ K₀ M (xG E) := by rw [← hbase E]; exact c.2
    exact hfix _ hc
  refine ⟨σ, Subgroup.mem_top _, AlgEquiv.ext fun y => ?_⟩
  change φ (φ.symm (τ (φ (φ.symm y)))) = τ y
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

variable [E.IsElliptic]

set_option synthInstance.maxHeartbeats 200000 in
-- the instance searches and unifications over `M ⊆ K̄ ⊆ K(Ē')^alg` exceed the default budget
set_option maxHeartbeats 1000000 in
-- the instance searches and unifications over `M ⊆ K̄ ⊆ K(Ē')^alg` exceed the default budget
omit [FiniteDimensional K M] [IsGalois K M] in
lemma hgp_false_iff (σ : Genuine.Gal E) : σ ∈ Hgp E 1 ⊥ false ↔ σ (yG E) = yG E := by
  rw [mem_Hgp_false, Qpt_one E, Mbar_one_bot E, sub_eq_zero, act_genericPoint E σ,
    Genuine.genericPoint, Affine.Point.some.injEq]
  exact ⟨fun h => h.2, fun h =>
    ⟨gal_fix_xLine E σ (IntermediateField.mem_adjoin_simple_self M _), h⟩⟩

omit [E.IsElliptic] [FiniteDimensional K M] [IsGalois K M] in
lemma twGalHom_yTw_iff (σ : Genuine.Gal E) :
    twGalHom E' M E u2 r hu2 σ (yTw (coordT (xN E')) M E u2 r) =
      yTw (coordT (xN E')) M E u2 r ↔ σ (yG E) = yG E := by
  rw [← twOmegaEquiv_yG E' M E u2 r hu2, twGalHom_apply' E' M E u2 r hu2 σ (yG E)]
  exact (twOmegaEquiv E' M E u2 r hu2).injective.eq_iff

omit [E.IsElliptic] in
lemma twGalHom_HL_iff (σ : Genuine.Gal E) :
    twGalHom E' M E u2 r hu2 σ ∈ (hemiTwData E' M E u2 r).HL ↔ σ (yG E) = yG E :=
  ⟨fun h => (twGalHom_yTw_iff E' M E u2 r hu2 σ).1
      ((mem_fixingSubgroup_adjoin_singleton_tw _ _ _).1 h.2),
    fun h => ⟨twGalHom_mem_H E' M E u2 r hu2 σ,
      (mem_fixingSubgroup_adjoin_singleton_tw _ _ _).2 ((twGalHom_yTw_iff E' M E u2 r hu2 σ).2 h)⟩⟩

lemma twGalHom_mem_HL (σ : Genuine.Gal E) :
    σ ∈ Hgp E 1 ⊥ false ↔ twGalHom E' M E u2 r hu2 σ ∈ (hemiTwData E' M E u2 r).HL :=
  (hgp_false_iff E' M E σ).trans (twGalHom_HL_iff E' M E u2 r hu2 σ).symm

set_option maxHeartbeats 4000000 in
-- the statements involve `M ⊆ K̄ ⊆ K(Ē')^alg`, whose types are large
lemma twGalHom_mem_S (σ : Genuine.Gal E) :
    σ ∈ SgenC E 1 ⊥ ↔ twGalHom E' M E u2 r hu2 σ ∈ (hemiTwData E' M E u2 r).S := by
  rw [SgenC_of_charZero E, Sgen_eq_S0 E]
  have hHL := twGalHom_mem_HL E' M E u2 r hu2 σ
  rw [mem_Hgp_false, Qpt_one E, Mbar_one_bot E, sub_eq_zero] at hHL
  change (act E σ (Genuine.genericPoint E) = Genuine.genericPoint E ∧ _) ↔
    (twGalHom E' M E u2 r hu2 σ ∈ (hemiTwData E' M E u2 r).HL ∧ _)
  rw [hHL]
  set φ := twOmegaEquiv E' M E u2 r hu2
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨W, hk, hx, hσ⟩
    refine ⟨W.comap φ.symm.toRingHom, fun c => ?_, ?_, ?_⟩
    · rw [ValuationSubring.mem_comap, algebraMap_K_eq_constι₃ E' M]
      simpa [twOmegaEquiv_symm_C, φ] using hk (algebraMap K M c)
    · rw [ValuationSubring.mem_comap]
      have : φ.symm (coordT (xN E')) ∈ W := by
        rw [twOmegaEquiv_symm_t]
        exact add_mem (mul_mem (hk u2) hx) (hk r)
      simpa using this
    · exact (galConjHom_mem_inertia_iff _ _ σ W).2 hσ
  · rintro ⟨W', hk, ht, hσ⟩
    let W := W'.comap φ.toRingHom
    have hW : W.comap φ.symm.toRingHom = W' := by
      ext z
      simp [W, ValuationSubring.mem_comap]
    have hC : ∀ m : M, constι₃ M m ∈ W' := fun m =>
      Pi1.Orbifold.mem_of_isIntegral hk ht (isIntegral_constι₃ _ M m)
    refine ⟨W, fun m => ?_, ?_, ?_⟩
    · change φ _ ∈ W'
      rw [twOmegaEquiv_C]
      exact hC m
    · change φ _ ∈ W'
      rw [twOmegaEquiv_xG, xTw]
      exact mul_mem (hC _) (sub_mem ht (hC r))
    · rw [← galConjHom_mem_inertia_iff φ (twOmegaEquiv_symm_mem_range E' M E u2 r hu2) σ W]
      change twGalHom E' M E u2 r hu2 σ ∈ _
      rw [hW]
      exact hσ

include hu2 in
/-- **iut's genuine `π₁` of `C_M = (E ∖ {O}) / ±1` is curves-jacobian's `Π_{C_M}` of the twist**
(`hemiTwData E' M E u2 r`, inside `K(Ē')^alg`). -/
def genuinePi1TwEquiv :
    (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).genuinePi1 ≃ₜ*
      GaloisPi1.pi1 (hemiTwData E' M E u2 r).H (hemiTwData E' M E u2 r).S
        (hemiTwData E' M E u2 r).isClosed_H :=
  genuinePi1CongrEmb E (hemiTwData E' M E u2 r) (twOmegaEquiv E' M E u2 r hu2)
    (twOmegaEquiv_symm_mem_range E' M E u2 r hu2) (twGalHom_mem_H E' M E u2 r hu2)
    (fun τ hτ => (twGalHom_surj E' M E u2 r hu2 τ hτ).elim fun σ h => ⟨σ, h.2⟩)
    (twGalHom_mem_S E' M E u2 r hu2)

end Twist

/-! ### `Π_{C_M} ↪ Π_{C_K}` -/

section Emb

open Iut.Anabelian

attribute [local instance low] Classical.propDecidable

variable {K : Type u} [Field K] [NumberField K] (E' : WeierstrassCurve K) [E'.IsElliptic]
  (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E')))) [FiniteDimensional K M]
  [IsGalois K M] (E : WeierstrassCurve M) [E.IsElliptic]

attribute [local instance high] decEqM

omit [E.IsElliptic] in
/-- **Galois compatibility of `Π_{C_M} ↪ Π_{C_K}`**: the image of curves-jacobian's `twInclC` is
the preimage of `Gal(K̄ / M)` under the restriction to the field of constants
`Π_{C_K} ↠ Gal(K̄ / K)` (`H(hemiTwData) = constFixer₃ M`, the preimage of `Gal(K̄ / M)` in
`Gal(K(Ē')^alg / K(x'))`). -/
lemma mem_range_twInclC_iff {u2 r : M} (hS : (hemiTwData E' M E u2 r).S = (hemiData E').S)
    (y : GaloisPi1.pi1 (hemiData E').H (hemiData E').S (hemiData E').isClosed_H) :
    y ∈ (twInclC (hemiTwData E' M E u2 r) (hemiData E') le_top hS).toMonoidHom.range ↔
      piConstC (hemiData E') y ∈ M.fixingSubgroup := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective z
    exact τ.2
  · intro hy
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk (⟨(σ : FFClosure (curveE E') ≃ₐ[K₀ K (coordT (xN E'))]
      FFClosure (curveE E')), hy⟩ : (hemiTwData E' M E u2 r).H), rfl⟩

/-- **`Π_{C_F} ↪ Π_{C_{F_mod}}` for iut's genuine orbicurves** (IUT I, Def. 3.1 (b)): for an
elliptic curve `E'` over the number field `K = F_mod` with `j(E') ∉ {0, 1728}`, `M ⊆ K̄` finite
Galois over `K` and `E` over `M` with `j(E) = j(E')`, the genuine `π₁` of
`C_M = (E ∖ {O}) / ±1` is an open normal subgroup of index `[M : K]` of the genuine `π₁` of
`C_K = (E' ∖ {O}) / ±1` (`C` does not see quadratic twists; through curves-jacobian's
`hemiTw_constExt`). -/
theorem genuine_CM_emb (hj : E.j = algebraMap K M E'.j) (h0 : E'.j ≠ 0)
    (h1728 : E'.j ≠ 1728) :
    ∃ f : (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).genuinePi1 →ₜ*
        (Orbicurve.pmQuotient (Orbicurve.oncePunctured E')).genuinePi1,
      IsOpenEmbedding f ∧ f.toMonoidHom.range.Normal ∧
        f.toMonoidHom.range.index = Module.finrank K M ∧
        ∀ y, y ∈ f.toMonoidHom.range ↔
          piConstC (hemiData E') (genuinePi1HemiEquiv E' y) ∈ M.fixingSubgroup := by
  have hj' : E.j = (E'.baseChange M).j := by
    rw [hj]
    change _ = (E'.map (algebraMap K M)).j
    rw [WeierstrassCurve.map_j]
  have hE0 : E.j ≠ 0 := by
    rw [hj]; exact (_root_.map_ne_zero _).2 h0
  have hE1728 : E.j ≠ 1728 := by
    rw [hj]; intro h
    exact h1728 ((algebraMap K M).injective (by rw [h, map_ofNat]))
  obtain ⟨u2, r, hu2, hΨ⟩ := exists_Ψ₂Sq_comp_xrat₃ E (E'.baseChange M) hj' hE0 hE1728
  obtain ⟨ho, hn, hi, -⟩ := hemiTw_constExt E' M E r hu2 hΨ
  let ι := twInclC (hemiTwData E' M E u2 r) (hemiData E') le_top (hemiTwData_S E' M E r hu2 hΨ)
  let e₁ := genuinePi1TwEquiv E' M E u2 r hu2
  let e₂ := (genuinePi1HemiEquiv E').symm
  let f := ((ContinuousMonoidHom.toContinuousMonoidHom e₂).comp ι).comp
    (ContinuousMonoidHom.toContinuousMonoidHom e₁)
  have hrange : f.toMonoidHom.range = ι.toMonoidHom.range.map (e₂.toMulEquiv : _ →* _) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨ι (e₁ y), ⟨e₁ y, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine ⟨e₁.symm z, ?_⟩
      change e₂ (ι (e₁ (e₁.symm z))) = e₂ (ι z)
      rw [ContinuousMulEquiv.apply_symm_apply]
  refine ⟨f, e₂.toHomeomorph.isOpenEmbedding.comp (ho.comp e₁.toHomeomorph.isOpenEmbedding),
    ?_, ?_, fun y => ?_⟩
  · rw [hrange]
    exact hn.map _ e₂.toMulEquiv.surjective
  · rw [hrange, Subgroup.index_map_equiv]
    exact hi
  · rw [hrange]
    exact Subgroup.mem_map_equiv.trans (mem_range_twInclC_iff E' M E _ _)

end Emb

end Iut.Reconstruction.HemiGenuine
