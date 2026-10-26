/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.HemiPi1
import CurvesJacobian.Cusp.EllipticMulByN
import Pi1.Orbicurve.EtaleInertia
import Pi1.Orbicurve.BaseChange
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral

/-!
# The cover `[m] : E ∖ E[m] → E ∖ {O}` inside `Ω = K(E)^alg` (MR14, G1 step 2)

Let `E` be an elliptic curve over a field `K` of characteristic `0`, `Ω = K(Ē)^alg`, `τ = x` the
Weierstrass coordinate, and `hemiData E` the Galois data of `curves-jacobian` whose function field
`L_X = (hemiData E).L` is `K(E) ⊆ Ω` (embedded by `embE`), with coordinate ring `K[E]`. We embed
the source of `[m]` into `Ω`:

* `mulByNEmb E m : K(E) →ₐ[K] Ω` with `mulByNEmb ([m]^* f) = embE f` (`mulByNEmb_mulByNHom`):
  `K(E)` is algebraic over `[m]^* K(E)` and `Ω` is algebraically closed;
* `mulByNField E m`: its image `L_m`, an intermediate field of `Ω / K(τ)` containing `L_X`
  (`hemiL_le_mulByNField`), whose coordinate ring (the integral closure of `K[τ]`) is the image of
  `K[E][1/ψ_m]` (`mem_coordRing_mulByNField_iff`);
* **`etale_mulByNField`**: `coordRing L_X → coordRing L_m` is étale — the finite étale map
  `[m]^* : K[E] → K[E][1/ψ_m]` of `curves-jacobian` (`isFiniteEtale_spec_mulByNHom`);
* **`etale_of_le_mulByNField`**: hence, by `pi1`'s inertia criterion
  (`AffOrbicurve.etale_iff_inertia`), every intermediate field `L_X ≤ L' ≤ L_m` gives an étale
  `coordRing L_X → coordRing L'`. This is how the level `Ÿ'_N` of the étale theta function
  (`L' = ψ^*K(E_Q)` with `m = 2N`) is shown to be étale over `X = E ∖ {O}`.
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open IntermediateField AffOrbicurve

noncomputable section

universe u

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

local notation "CR" => E.toAffine.CoordinateRing
local notation "FF" => E.toAffine.FunctionField
local notation "Ω" => FFClosure (curveE E)
local notation "τ" => coordT (xN E)

/-- `K[E] ⊆ K(E) ↪ Ω`. -/
def rhoA : CR →+* Ω := (embE E).toRingHom.comp (algebraMap CR FF)

lemma rhoA_injective : Function.Injective (rhoA E) :=
  (embE E).toRingHom.injective.comp (IsFractionRing.injective CR FF)

lemma mem_hemiL_iff (z : Ω) : z ∈ (hemiData E).L ↔ ∃ f : FF, embE E f = z := by
  constructor
  · intro hz
    refine ⟨funFieldEquivE E ((hemiEquivL E).symm ⟨z, hz⟩), ?_⟩
    change algebraMap _ _ ((funFieldEquivE E).symm (funFieldEquivE E _)) = z
    rw [RingEquiv.symm_apply_apply, ← hemiEquivL_apply, RingEquiv.apply_symm_apply]
  · rintro ⟨f, rfl⟩
    change algebraMap _ _ ((funFieldEquivE E).symm f) ∈ (hemiData E).L
    rw [← hemiEquivL_apply]
    exact SetLike.coe_mem _

variable (m : ℕ) [NeZero m]

section Emb

/-- The embedding of `K[E][1/ψ_m]` (the source of `[m]`) into `Ω` over `K[E]`. -/
def mulByNEmbB : MulByNB E m →+* Ω :=
  letI : Algebra CR Ω := (rhoA E).toAlgebra
  haveI : Module.IsTorsionFree CR Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (rhoA_injective E)
  haveI : Module.IsTorsionFree CR (MulByNB E m) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (mulByNHom_injective E m)
  (IsAlgClosed.lift (R := CR) (S := MulByNB E m) (M := Ω)).toRingHom

lemma mulByNEmbB_mulByNHom (a : CR) :
    mulByNEmbB E m (toMulByNB E m (mulByNHom E m a)) = rhoA E a := by
  letI : Algebra CR Ω := (rhoA E).toAlgebra
  haveI : Module.IsTorsionFree CR Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (rhoA_injective E)
  haveI : Module.IsTorsionFree CR (MulByNB E m) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (mulByNHom_injective E m)
  exact (IsAlgClosed.lift (R := CR) (S := MulByNB E m) (M := Ω)).commutes a

lemma mulByNEmbB_injective : Function.Injective (mulByNEmbB E m) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  have hker : RingHom.ker (mulByNEmbB E m) = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := CR) ?_
    refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_mulByNB, mulByNEmbB_mulByNHom] at ha
    exact rhoA_injective E (ha.trans (map_zero _).symm)
  have : b ∈ RingHom.ker (mulByNEmbB E m) := hb
  rwa [hker, Ideal.mem_bot] at this

/-- The source of `[m]` in `Ω`, as a ring map. -/
def mulByNEmbR : FF →+* Ω :=
  IsFractionRing.lift (K := FF)
    (g := (mulByNEmbB E m).comp (toMulByNB E m).toRingEquiv.toRingHom)
    ((mulByNEmbB_injective E m).comp (toMulByNB E m).injective)

lemma mulByNEmbR_algebraMap (b : coverRingN E m) :
    mulByNEmbR E m (algebraMap (coverRingN E m) FF b) = mulByNEmbB E m (toMulByNB E m b) :=
  IsFractionRing.lift_algebraMap _ _

lemma mulByNEmbR_mulByNHom (a : CR) :
    mulByNEmbR E m (algebraMap (coverRingN E m) FF (mulByNHom E m a)) =
      embE E (algebraMap CR FF a) := by
  rw [mulByNEmbR_algebraMap, mulByNEmbB_mulByNHom]; rfl

/-- **The source of `[m]` in `Ω`**: `K(E) ↪ Ω` with `[m]^* f ↦ embE f`. -/
def mulByNEmb : FF →ₐ[K] Ω where
  toRingHom := mulByNEmbR E m
  commutes' c := by
    have h := mulByNEmbR_mulByNHom E m (algebraMap K CR c)
    rw [mulByNHom_algebraMap, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply] at h
    exact h.trans ((embE E).commutes c)

lemma mulByNEmb_algebraMap (b : coverRingN E m) :
    mulByNEmb E m (algebraMap (coverRingN E m) FF b) = mulByNEmbB E m (toMulByNB E m b) :=
  mulByNEmbR_algebraMap E m b

/-- `mulByNEmb ∘ [m]^* = embE` on `K[E]`. -/
lemma mulByNEmb_mulByNHom (a : CR) :
    mulByNEmb E m (algebraMap (coverRingN E m) FF (mulByNHom E m a)) =
      embE E (algebraMap CR FF a) :=
  mulByNEmbR_mulByNHom E m a

end Emb

/-- `K[E] ≅ R` of `hemiData E` is compatible with `embE`. -/
lemma algebraMap_hemiREquiv' (a : CR) :
    algebraMap (hemiData E).R Ω (hemiREquiv E a) = embE E (algebraMap CR FF a) := by
  change algebraMap (hemiData E).R Ω
    (sectionsXEHemiAlgEquiv E ((sectionsXEAlgEquiv E).symm a)) = _
  rw [algebraMap_sectionsXEHemiAlgEquiv]
  have h := funFieldEquivE_germ E ((sectionsXEAlgEquiv E).symm a)
  rw [AlgEquiv.apply_symm_apply] at h
  change _ = algebraMap _ _ ((funFieldEquivE E).symm (algebraMap CR FF a))
  rw [← h, RingEquiv.symm_apply_apply]

/-! ### The intermediate field `L_m = mulByNEmb(K(E))` -/

section Galois

local notation "φ" => mulByNEmb E m
local notation "ι" => algebraMap (coverRingN E m) FF

lemma transcendental_tau : Transcendental K τ := (hemiData E).transcendental

lemma tau_eq : φ (ι (mulByNHom E m (xE E))) = τ := by
  rw [mulByNEmb_mulByNHom, ← embE_genX]; rfl

lemma K₀_le_fieldRange : K₀ K τ ≤ (mulByNEmb E m).fieldRange := by
  rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact ⟨_, tau_eq E m⟩

/-- **`L_m`**: the image of the source `K(E)` of `[m]` in `Ω`, over `K(τ)`. -/
def mulByNField : IntermediateField (K₀ K τ) Ω :=
  (mulByNEmb E m).fieldRange.toSubfield.toIntermediateField fun x =>
    K₀_le_fieldRange E m x.2

lemma mem_mulByNField_iff (z : Ω) : z ∈ mulByNField E m ↔ ∃ f : FF, φ f = z := Iff.rfl

lemma hemiL_le_mulByNField : (hemiData E).L ≤ mulByNField E m := by
  intro z hz
  obtain ⟨f, rfl⟩ := (mem_hemiL_iff E z).mp hz
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := CR) f
  refine ⟨ι (mulByNHom E m a) / ι (mulByNHom E m b), ?_⟩
  change φ _ = _
  rw [map_div₀, map_div₀, mulByNEmb_mulByNHom, mulByNEmb_mulByNHom]

/-- `K[τ] ≅ K[X] → K[E][1/ψ_m]`, `τ ↦ [m]^*x`. -/
def liftA₀ : A₀ K τ →ₐ[K] coverRingN E m :=
  (aeval (mulByNHom E m (xE E))).comp
    (Polynomial.algEquivOfTranscendental K τ (transcendental_tau E)).symm.toAlgHom

lemma liftA₀_spec (c : A₀ K τ) : φ (ι (liftA₀ E m c)) = c := by
  obtain ⟨p, rfl⟩ := (Polynomial.algEquivOfTranscendental K τ (transcendental_tau E)).surjective c
  have e : liftA₀ E m (Polynomial.algEquivOfTranscendental K τ (transcendental_tau E) p) =
      aeval (mulByNHom E m (xE E)) p := by
    simp [liftA₀]
  rw [e, coe_algEquivOfTranscendental (transcendental_tau E) p, ← tau_eq E m]
  exact (Polynomial.aeval_algHom_apply
    ((mulByNEmb E m).comp (IsScalarTower.toAlgHom K (coverRingN E m) FF)) _ p).symm

lemma isIntegral_rhoA (a : CR) : IsIntegral (A₀ K τ) (rhoA E a) := by
  have := CoordRing.isIntegral_algebraMap (hemiREquiv E a)
  rwa [algebraMap_hemiREquiv'] at this

lemma isIntegral_mulByNEmb (b : coverRingN E m) : IsIntegral (A₀ K τ) (φ (ι b)) := by
  rw [mulByNEmb_algebraMap]
  obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := CR) (toMulByNB E m b)
  let T := integralClosure (A₀ K τ) Ω
  have hT : ∀ a : CR, rhoA E a ∈ T := isIntegral_rhoA E
  let r : CR →+* T := (rhoA E).codRestrict T.toSubring hT
  have hrr : (algebraMap T Ω).comp r = (mulByNEmbB E m).comp (algebraMap CR (MulByNB E m)) := by
    refine RingHom.ext fun a => ?_
    change rhoA E a = mulByNEmbB E m (toMulByNB E m (mulByNHom E m a))
    rw [mulByNEmbB_mulByNHom]
  have hint : IsIntegral T (mulByNEmbB E m (toMulByNB E m b)) := by
    refine ⟨p.map r, hp.map r, ?_⟩
    rw [eval₂_map, hrr, ← Polynomial.hom_eval₂, hpb, map_zero]
  exact isIntegral_trans _ hint

lemma exists_of_isIntegral {f : FF} (hf : IsIntegral (A₀ K τ) (φ f)) :
    ∃ b : coverRingN E m, ι b = f := by
  haveI : IsIntegrallyClosed (coverRingN E m) :=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (psiN E m))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (psiN_ne_zero_of_neZero E m))
  obtain ⟨p, hp, hpf⟩ := hf
  have hint : IsIntegral (coverRingN E m) f := by
    refine ⟨p.map (liftA₀ E m).toRingHom, hp.map _, ?_⟩
    apply (mulByNEmb E m).toRingHom.injective
    rw [map_zero, Polynomial.hom_eval₂, eval₂_map, ← hpf]
    congr 1
    ext c
    exact liftA₀_spec E m c
  exact IsIntegrallyClosed.isIntegral_iff.mp hint

/-- **The coordinate ring of `L_m` is `K[E][1/ψ_m]`.** -/
lemma mem_coordRing_mulByNField_iff (z : Ω) :
    (z ∈ mulByNField E m ∧ IsIntegral (A₀ K τ) z) ↔ ∃ b : coverRingN E m, φ (ι b) = z := by
  constructor
  · rintro ⟨⟨f, rfl⟩, hz⟩
    obtain ⟨b, rfl⟩ := exists_of_isIntegral E m hz
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨⟨_, rfl⟩, isIntegral_mulByNEmb E m b⟩

lemma mulByNField_eq_adjoin :
    mulByNField E m = IntermediateField.adjoin (K₀ K τ)
      {φ (algebraMap CR FF (xE E)), φ (algebraMap CR FF (yE E))} := by
  refine le_antisymm ?_ (IntermediateField.adjoin_le_iff.mpr ?_)
  · rintro z ⟨f, rfl⟩
    set S := IntermediateField.adjoin (K₀ K τ)
      ({φ (algebraMap CR FF (xE E)), φ (algebraMap CR FF (yE E))} : Set Ω)
    have hx : φ (algebraMap CR FF (xE E)) ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
    have hy : φ (algebraMap CR FF (yE E)) ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
    have hK : ∀ c : K, algebraMap K Ω c ∈ S := fun c => by
      have := S.algebraMap_mem (algebraMap K (K₀ K τ) c)
      rwa [← IsScalarTower.algebraMap_apply] at this
    have hpoly : ∀ p : K[X], φ (algebraMap CR FF (aeval (xE E) p)) ∈ S := fun p => by
      induction p using Polynomial.induction_on with
      | C c => rw [aeval_C, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]; exact hK c
      | add p q hp hq => rw [map_add, map_add, map_add]; exact add_mem hp hq
      | monomial n c _ =>
        rw [map_mul, map_pow, aeval_C, aeval_X, map_mul, map_mul, map_pow, map_pow,
          ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
        exact mul_mem (hK c) (pow_mem hx _)
    have hA : ∀ a : CR, φ (algebraMap CR FF a) ∈ S := fun a => by
      obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
      rw [Algebra.smul_def, Algebra.smul_def, mul_one, algebraMap_polynomial_eq_aeval_xE,
        algebraMap_polynomial_eq_aeval_xE, map_add, map_add, map_mul, map_mul]
      exact add_mem (hpoly p) (mul_mem (hpoly q) hy)
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := CR) f
    rw [map_div₀]
    exact div_mem (hA a) (hA b)
  · rintro z (rfl | rfl)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

instance finiteDimensional_mulByNField : FiniteDimensional (K₀ K τ) (mulByNField E m) := by
  rw [mulByNField_eq_adjoin]
  refine IntermediateField.finiteDimensional_adjoin fun z hz => ?_
  have hz' : ∃ a : CR, z = φ (ι (algebraMap CR (coverRingN E m) a)) := by
    rcases hz with rfl | rfl
    · exact ⟨xE E, by rw [← IsScalarTower.algebraMap_apply]⟩
    · exact ⟨yE E, by rw [← IsScalarTower.algebraMap_apply]⟩
  obtain ⟨a, rfl⟩ := hz'
  exact (isIntegral_mulByNEmb E m _).tower_top

/-- `K[E][1/ψ_m] ≅ coordRing L_m`. -/
def coverToCoordRing : coverRingN E m →+* coordRing K τ (mulByNField E m) where
  toFun b := ⟨⟨φ (ι b), ⟨_, rfl⟩⟩,
    (CoordRing.isIntegral_coe_iff (F := mulByNField E m) _).1 (isIntegral_mulByNEmb E m b)⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

lemma coe_coverToCoordRing (b : coverRingN E m) :
    ((coverToCoordRing E m b : mulByNField E m) : Ω) = φ (ι b) := rfl

def coverEquivCoordRing : coverRingN E m ≃+* coordRing K τ (mulByNField E m) :=
  RingEquiv.ofBijective (coverToCoordRing E m)
    ⟨fun b b' h => by
      have h' := congrArg (fun z : coordRing K τ (mulByNField E m) => ((z : mulByNField E m) : Ω)) h
      exact IsFractionRing.injective (coverRingN E m) FF ((mulByNEmb E m).injective h'),
     fun z => by
      obtain ⟨b, hb⟩ := (mem_coordRing_mulByNField_iff E m _).mp
        ⟨(z : mulByNField E m).2, (CoordRing.isIntegral_coe_iff (F := mulByNField E m) _).2 z.2⟩
      exact ⟨b, Subtype.ext (Subtype.ext hb)⟩⟩

lemma coe_coverEquivCoordRing (b : coverRingN E m) :
    ((coverEquivCoordRing E m b : mulByNField E m) : Ω) = φ (ι b) := rfl

/-- **`coordRing L_X → coordRing L_m` is étale**: it is `[m]^* : K[E] → K[E][1/ψ_m]`. -/
theorem etale_mulByNField :
    (ringMap τ (hemiL_le_mulByNField E m)).toRingHom.Etale := by
  have hcomp : (ringMap τ (hemiL_le_mulByNField E m)).toRingHom =
      ((coverEquivCoordRing E m).toRingHom.comp (mulByNHom E m)).comp
        (hemiREquiv E).symm.toRingEquiv.toRingHom := by
    ext z
    change ((z : (hemiData E).L) : Ω) = φ (ι (mulByNHom E m ((hemiREquiv E).symm z)))
    rw [mulByNEmb_mulByNHom, ← algebraMap_hemiREquiv', AlgEquiv.apply_symm_apply]
    rfl
  rw [hcomp]
  refine RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (hemiREquiv E).symm.bijective)
    (RingHom.Etale.stableUnderComposition _ _ ?_
      (RingHom.Etale.of_bijective (coverEquivCoordRing E m).bijective))
  exact (inferInstance : Algebra.Etale CR (MulByNB E m))

/-- **Intermediate levels are étale over `X`**: for `L_X ≤ L' ≤ L_m`,
`coordRing L_X → coordRing L'` is étale (`pi1`'s inertia criterion). -/
theorem etale_of_le_mulByNField {L' : IntermediateField (K₀ K τ) Ω} (h₁ : (hemiData E).L ≤ L')
    (h₂ : L' ≤ mulByNField E m) : (ringMap τ h₁).toRingHom.Etale := by
  haveI : FiniteDimensional (K₀ K τ) L' :=
    FiniteDimensional.of_injective (IntermediateField.inclusion h₂).toLinearMap
      (IntermediateField.inclusion h₂).injective
  have hm := (etale_iff_inertia (transcendental_tau E) (hemiL_le_mulByNField E m)).mp
    (etale_mulByNField E m)
  exact (etale_iff_inertia (transcendental_tau E) h₁).mpr fun W hW σ hσ =>
    IntermediateField.fixingSubgroup_antitone h₂ (hm W hW hσ)

/-! ### Levels between `X` and `[m]` given by generators -/

lemma mem_adjoin_image {S : Set FF} {g : FF} (hg : g ∈ IntermediateField.adjoin K S) :
    φ g ∈ IntermediateField.adjoin (K₀ K τ) (φ '' S) := by
  have h1 : φ g ∈ (IntermediateField.adjoin K S).map (mulByNEmb E m) := ⟨g, hg, rfl⟩
  rw [IntermediateField.adjoin_map] at h1
  have h2 : IntermediateField.adjoin K (φ '' S) ≤
      (IntermediateField.adjoin (K₀ K τ) (φ '' S)).restrictScalars K :=
    IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin (K₀ K τ) (φ '' S))
  exact h2 h1

/-- A level generated by `S ⊆ K(E)` containing `[m]^*K[E]` lies over `L_X`. -/
lemma hemiL_le_adjoin {S : Set FF}
    (hS : ∀ a : CR, ι (mulByNHom E m a) ∈ IntermediateField.adjoin K S) :
    (hemiData E).L ≤ IntermediateField.adjoin (K₀ K τ) (φ '' S) := by
  intro z hz
  obtain ⟨f, rfl⟩ := (mem_hemiL_iff E z).mp hz
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := CR) f
  rw [map_div₀, ← mulByNEmb_mulByNHom E m, ← mulByNEmb_mulByNHom E m]
  exact div_mem (mem_adjoin_image E m (hS a)) (mem_adjoin_image E m (hS b))

lemma adjoin_image_le_mulByNField (S : Set FF) :
    IntermediateField.adjoin (K₀ K τ) (φ '' S) ≤ mulByNField E m := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨g, -, rfl⟩
  exact ⟨g, rfl⟩

/-- **Étaleness of a level given by generators**: if `S ⊆ K(E)` generates a subfield containing
`[m]^* K[E]`, then `L' = K(τ)(φ(S))` satisfies `L_X ≤ L' ≤ L_m`, it is finite over `K(τ)`, and
`coordRing L_X → coordRing L'` is étale. -/
theorem etale_adjoin_image {S : Set FF}
    (hS : ∀ a : CR, ι (mulByNHom E m a) ∈ IntermediateField.adjoin K S) :
    (ringMap τ (hemiL_le_adjoin E m hS)).toRingHom.Etale :=
  etale_of_le_mulByNField E m _ (adjoin_image_le_mulByNField E m S)

instance finiteDimensional_adjoin_image (S : Set FF) :
    FiniteDimensional (K₀ K τ) (IntermediateField.adjoin (K₀ K τ) (φ '' S)) :=
  FiniteDimensional.of_injective
    (IntermediateField.inclusion (adjoin_image_le_mulByNField E m S)).toLinearMap
    (IntermediateField.inclusion (adjoin_image_le_mulByNField E m S)).injective

end Galois


end CurvesJacobian.Cusp
