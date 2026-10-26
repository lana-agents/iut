/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.MulByNGalois
import EllipticCurves.FunctionField.MulByNXCoordRatFunc

/-!
# Lifting `[-1]^*` to an automorphism of `Ω` (MR14, [EtTh] Prop. 1.5(iii), inversion part)

Let `E` be an elliptic curve over a field `K` of characteristic `0`, `Ω = K(Ē)^alg`, `τ = x`, and
`φ_m = mulByNEmb E m : K(E) ↪ Ω` the source of `[m]` (`MulByNGalois.lean`). The inversion
`[-1]^* = negYAlgEquiv` of `K(E)` commutes with `[m]^*` (`negE_comp_pb`: through the generic point,
`m • (-𝒫) = -(m • 𝒫)`), so it fixes `[m]^*x`, whose image in `Ω` is `τ`. Hence:

* `negLift E m : L_m →ₐ[K(τ)] Ω`, `φ_m(g) ↦ φ_m([-1]^* g)`, is `K(τ)`-linear;
* **`exists_negAut`**: there is `σ ∈ Gal(Ω / K(τ))` with `σ ∘ φ_m = φ_m ∘ [-1]^*`
  (`AlgHom.liftNormal`, `Ω / K(τ)` being Galois); in particular `σ` lies over `[-1]` on
  `X = E ∖ {O}` (`σ ∘ embE = embE ∘ [-1]^*`).
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open IntermediateField AffOrbicurve

noncomputable section

universe u

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

local notation "FF" => E.toAffine.FunctionField
local notation "Ω" => FFClosure (curveE E)
local notation "τ" => coordT (xN E)

/-- `[-1]^*` on `K(E)`. -/
abbrev negE : FF ≃ₐ[K] FF := WeierstrassCurve.Affine.CoordinateRing.negYAlgEquiv E.toAffine

/-- **`[-1]^*` commutes with `[m]^*`.** -/
lemma negE_comp_pb (m : ℕ) [NeZero m] :
    (negE E : FF →ₐ[K] FF).comp (pb E m) = (pb E m).comp (negE E : FF →ₐ[K] FF) := by
  refine WeierstrassCurve.Affine.CoordinateRing.algHom_ext_of_genPointHom ?_
  rw [← WeierstrassCurve.Affine.CoordinateRing.genPointHom_comp,
    ← WeierstrassCurve.Affine.CoordinateRing.genPointHom_comp, genPointHom_pb, map_nsmul,
    WeierstrassCurve.Affine.CoordinateRing.genPointHom_negYAlgEquiv_genericPoint, map_neg,
    genPointHom_pb, smul_neg]

lemma negE_pb (m : ℕ) [NeZero m] (g : FF) : negE E (pb E m g) = pb E m (negE E g) :=
  congrArg (fun f : FF →ₐ[K] FF => f g) (negE_comp_pb E m)

variable (m : ℕ) [NeZero m]

local notation "φ" => mulByNEmb E m

/-- The preimage under `φ_m` of an element of `L_m`. -/
def preImg (x : mulByNField E m) : FF := ((mem_mulByNField_iff E m x).1 x.2).choose

lemma mulByNEmb_preImg (x : mulByNField E m) : φ (preImg E m x) = x :=
  ((mem_mulByNField_iff E m x).1 x.2).choose_spec

lemma preImg_eq {x : mulByNField E m} {f : FF} (h : φ f = x) : preImg E m x = f :=
  (mulByNEmb E m).injective (by change φ (preImg E m x) = φ f; rw [mulByNEmb_preImg, h])

/-- `φ_m(g) ↦ φ_m([-1]^* g)` on `L_m`, as a ring map. -/
def negLiftRing : mulByNField E m →+* Ω where
  toFun x := φ (negE E (preImg E m x))
  map_one' := by rw [preImg_eq E m (f := 1) (by simp)]; simp
  map_mul' x y := by
    rw [preImg_eq E m (f := preImg E m x * preImg E m y)
      (by rw [map_mul, mulByNEmb_preImg, mulByNEmb_preImg]; rfl)]
    simp
  map_zero' := by rw [preImg_eq E m (f := 0) (by simp)]; simp
  map_add' x y := by
    rw [preImg_eq E m (f := preImg E m x + preImg E m y)
      (by rw [map_add, mulByNEmb_preImg, mulByNEmb_preImg]; rfl)]
    simp

lemma negLiftRing_apply (f : FF) (hf : φ f ∈ mulByNField E m) :
    negLiftRing E m ⟨φ f, hf⟩ = φ (negE E f) := by
  change φ (negE E (preImg E m ⟨φ f, hf⟩)) = _
  rw [preImg_eq E m rfl]

/-- The restriction of `negLiftRing` to `K(τ)`, as a `K`-algebra map. -/
def negLiftK₀ : K₀ K τ →ₐ[K] Ω where
  toRingHom := (negLiftRing E m).comp (algebraMap (K₀ K τ) (mulByNField E m))
  commutes' c := by
    change negLiftRing E m ⟨algebraMap K Ω c, _⟩ = algebraMap K Ω c
    have h : algebraMap K Ω c = φ (algebraMap K FF c) := ((mulByNEmb E m).commutes c).symm
    simp only [h]
    rw [negLiftRing_apply, AlgEquiv.commutes, AlgHom.commutes]

lemma negLiftK₀_eq : negLiftK₀ E m = (K₀ K τ).val := by
  refine IntermediateField.adjoin_algHom_ext K fun x hx => ?_
  rw [Set.mem_singleton_iff] at hx
  subst hx
  change negLiftRing E m ⟨coordT (xN E), _⟩ = coordT (xN E)
  have hτ : φ (pb E m (WeierstrassCurve.Affine.CoordinateRing.genX E.toAffine)) = τ := by
    rw [← AlgHom.comp_apply, mulByNEmb_comp_pb, embE_genX]
  simp only [← hτ]
  rw [negLiftRing_apply, negE_pb, WeierstrassCurve.Affine.CoordinateRing.negYAlgEquiv_genX]

/-- **`[-1]^*` on `L_m`**, a `K(τ)`-algebra map `L_m → Ω`. -/
def negLift : mulByNField E m →ₐ[K₀ K τ] Ω where
  toRingHom := negLiftRing E m
  commutes' c := congrArg (fun f : K₀ K τ →ₐ[K] Ω => f c) (negLiftK₀_eq E m)

/-- **The lift of `[-1]^*`**: an automorphism `σ` of `Ω` over `K(τ)` with
`σ ∘ φ_m = φ_m ∘ [-1]^*`. -/
theorem exists_negAut :
    ∃ σ : Ω ≃ₐ[K₀ K τ] Ω, ∀ g : FF, σ (φ g) = φ (negE E g) := by
  let σ' : Ω →ₐ[K₀ K τ] Ω := (negLift E m).liftNormal Ω
  have hσ' : ∀ g : FF, σ' (φ g) = φ (negE E g) := fun g => by
    have := AlgHom.liftNormal_commutes (E := Ω) (negLift E m) ⟨φ g, ⟨g, rfl⟩⟩
    exact this.trans (negLiftRing_apply E m g _)
  exact ⟨AlgEquiv.ofBijective σ' (Algebra.IsAlgebraic.algHom_bijective σ'), hσ'⟩

end CurvesJacobian.Cusp
