/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.MulByNGalois
import EllipticCurves.Torsion.XSupport

/-!
# Commutators of `Gal(Ω / L_X · K^alg)` fix the source `L_m` of `[m]` (MR14, run 15, F1)

Let `E` be an elliptic curve over a field `K` of characteristic `0`, `Ω = K(Ē)^alg`, `L_X = K(E)`
embedded in `Ω` by `embE`, and `L_m = mulByNEmb(K(E))` the source of `[m] : E → E` in `Ω`
(`Iut.EtaleTheta.MulByNGalois`). We show that the commutator `⁅σ, ρ⁆` of two automorphisms of
`Ω / K(τ)` fixing `L_X` and every element of `Ω` algebraic over `K` acts trivially on `L_m`
(`commutator_fix_mulByNField`): the geometric part of `Gal(L_m / L_X)` is the abelian group
`E[m]`.

## The argument

* `P := (mulByNEmb x, mulByNEmb y) ∈ E(Ω)` is the image of the generic point of `K(E)`, and
  `m • P = P_X := (embE x, embE y)` (`nsmul_ptM`), since `mulByNEmb ∘ [m]^* = embE`.
* An automorphism `σ` of `Ω` acts on `E(Ω)` additively (`Point.map`). If `σ` fixes `L_X` it fixes
  `P_X` (`act_ptX`), so `c(σ) := σP − P` is `m`-torsion (`nsmul_cocycle`).
* `m`-torsion points of `E(Ω)` have coordinates algebraic over `K` (`isIntegral_of_torsion`):
  `x` is a root of the nonzero polynomial `ΨSq_m ∈ K[X]`, and `(2y + a₁x + a₃)² = 4(x³ + a₂x² +
  a₄x + a₆) + (a₁x + a₃)²`. So, if `σ` also fixes all elements algebraic over `K`, it fixes all
  `m`-torsion points (`act_torsion`).
* On the subgroup of such `σ` the map `c` is therefore a homomorphism to the commutative group
  `E(Ω)` (`cocycle_mul`), so `c(⁅σ, ρ⁆) = 0`, i.e. `⁅σ, ρ⁆` fixes `P`. It thus fixes the
  generators `mulByNEmb x`, `mulByNEmb y` of `L_m` and hence `L_m`.
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open IntermediateField AffOrbicurve
open scoped commutatorElement

noncomputable section

universe u

namespace CurvesJacobian.Cusp

/-- **The `y`-coordinate of a point is integral when `x` and the coefficients are.** From the
Weierstrass equation, `(2y + a₁x + a₃)² = 4(x³ + a₂x² + a₄x + a₆) + (a₁x + a₃)²`. -/
lemma isIntegral_y_of_equation {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    {W : WeierstrassCurve.Affine L} (h₁ : IsIntegral K W.a₁) (h₂ : IsIntegral K W.a₂)
    (h₃ : IsIntegral K W.a₃) (h₄ : IsIntegral K W.a₄) (h₆ : IsIntegral K W.a₆) {x y : L}
    (heq : W.Equation x y) (hx : IsIntegral K x) : IsIntegral K y := by
  have e := (WeierstrassCurve.Affine.equation_iff x y).mp heq
  have hw : (2 * y + W.a₁ * x + W.a₃) ^ 2 =
      4 * (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) + (W.a₁ * x + W.a₃) ^ 2 := by
    linear_combination 4 * e
  have h4 : IsIntegral K (4 : L) := by
    have := isIntegral_algebraMap (R := K) (A := L) (x := 4)
    rwa [map_ofNat] at this
  have hw' : IsIntegral K (2 * y + W.a₁ * x + W.a₃) := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hw]
    exact (h4.mul ((((hx.pow 3).add (h₂.mul (hx.pow 2))).add (h₄.mul hx)).add h₆)).add
      ((h₁.mul hx).add h₃ |>.pow 2)
  have h2 : (2 : L) ≠ 0 := by
    have := (map_ne_zero (algebraMap K L)).mpr (two_ne_zero : (2 : K) ≠ 0)
    rwa [map_ofNat] at this
  have hy : y = (2 * y + W.a₁ * x + W.a₃ - W.a₁ * x - W.a₃) * algebraMap K L 2⁻¹ := by
    rw [map_inv₀, map_ofNat]
    field_simp
    ring
  rw [hy]
  exact ((hw'.sub (h₁.mul hx)).sub h₃).mul isIntegral_algebraMap

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

local notation "FF" => E.toAffine.FunctionField
local notation "Ω" => FFClosure (curveE E)
local notation "τ" => coordT (xN E)
local notation "Pt" => WeierstrassCurve.Affine.Point (E.toAffine.baseChange Ω)

/-- Classical decidable equality on `Ω`, for the group law of `E(Ω)`. -/
abbrev decEqΩ : DecidableEq Ω := Classical.decEq _

attribute [local instance] decEqΩ

/-! ### Extensionality of embeddings of `K(E)` through the generators -/

omit [CharZero K] [E.IsElliptic] in
/-- **Generator extensionality for `K`-algebra maps out of `K(E)`**: two of them agreeing on
`x` and `y` are equal (`elliptic-curves`' `algHom_ext_gen`, for an arbitrary target field). -/
theorem algHom_ext_genXY {L : Type*} [Field L] [Algebra K L] {φ ψ : FF →ₐ[K] L}
    (hx : φ (WeierstrassCurve.Affine.CoordinateRing.genX E.toAffine) =
      ψ (WeierstrassCurve.Affine.CoordinateRing.genX E.toAffine))
    (hy : φ (WeierstrassCurve.Affine.CoordinateRing.genY E.toAffine) =
      ψ (WeierstrassCurve.Affine.CoordinateRing.genY E.toAffine)) : φ = ψ := by
  have hcr : (φ : FF →+* L).comp (WeierstrassCurve.Affine.CoordinateRing.genPsi E.toAffine)
      = (ψ : FF →+* L).comp (WeierstrassCurve.Affine.CoordinateRing.genPsi E.toAffine) := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · have hofC : AdjoinRoot.of E.toAffine.polynomial (C c) =
          algebraMap K E.toAffine.CoordinateRing c := by
        rw [IsScalarTower.algebraMap_apply K K[X] E.toAffine.CoordinateRing,
          AdjoinRoot.algebraMap_eq, ← Polynomial.C_eq_algebraMap]
      simp only [RingHom.comp_apply, hofC, WeierstrassCurve.Affine.CoordinateRing.genPsi,
        ← IsScalarTower.algebraMap_apply, AlgHom.coe_toRingHom, AlgHom.commutes]
    · exact hx
    · exact hy
  refine AlgHom.coe_ringHom_injective ?_
  refine IsFractionRing.ringHom_ext (A := E.toAffine.CoordinateRing) (fun a => ?_)
  exact congr($hcr a)

/-! ### The action of `Aut(Ω / K(τ))` on `E(Ω)` -/

/-- An automorphism of `Ω / K(τ)`, as a `K`-algebra map `Ω → Ω`. -/
abbrev resK (σ : Ω ≃ₐ[K₀ K τ] Ω) : Ω →ₐ[K] Ω :=
  (σ : Ω →ₐ[K₀ K τ] Ω).restrictScalars K

/-- **The action of `σ` on `E(Ω)`**, an additive map (`Point.map`). -/
def act (σ : Ω ≃ₐ[K₀ K τ] Ω) : Pt →+ Pt :=
  WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (resK E σ)

lemma act_map (σ : Ω ≃ₐ[K₀ K τ] Ω) (f : FF →ₐ[K] Ω)
    (Q : WeierstrassCurve.Affine.Point (E.toAffine.baseChange FF)) :
    act E σ (WeierstrassCurve.Affine.Point.map (W' := E.toAffine) f Q) =
      WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ((resK E σ).comp f) Q :=
  WeierstrassCurve.Affine.Point.map_map _ _ Q

lemma act_mul (σ ρ : Ω ≃ₐ[K₀ K τ] Ω) (Q : Pt) : act E (σ * ρ) Q = act E σ (act E ρ Q) := by
  have h : resK E (σ * ρ) = (resK E σ).comp (resK E ρ) := AlgHom.ext fun _ => rfl
  change WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (resK E (σ * ρ)) Q =
    WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (resK E σ)
      (WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (resK E ρ) Q)
  rw [WeierstrassCurve.Affine.Point.map_map, h]

lemma act_one (Q : Pt) : act E 1 Q = Q := by
  rcases Q with _ | ⟨x, y, h⟩ <;> rfl

/-! ### Torsion points have algebraic coordinates -/

lemma two_ne_zero_Ω : (2 : Ω) ≠ 0 := by
  have := (map_ne_zero (algebraMap K Ω)).mpr (two_ne_zero : (2 : K) ≠ 0)
  rwa [map_ofNat] at this

/-- **The coordinates of an `m`-torsion point of `E(Ω)` are integral over `K`**: `x` is a root of
the nonzero `ΨSq_m ∈ K[X]`, and then so is `y` (`isIntegral_y_of_equation`). -/
lemma isIntegral_of_torsion (m : ℕ) [NeZero m] {x y : Ω}
    {h : (E.toAffine.baseChange Ω).Nonsingular x y}
    (hP : m • (WeierstrassCurve.Affine.Point.some x y h : Pt) = 0) :
    IsIntegral K x ∧ IsIntegral K y := by
  have hmem : (WeierstrassCurve.Affine.Point.some x y h : Pt) ∈
      (E.toAffine.baseChange Ω).torsion m :=
    WeierstrassCurve.Affine.mem_torsion_iff.mpr hP
  have hx := WeierstrassCurve.Affine.mem_torsionXSupport_of_mem_torsion (two_ne_zero_Ω E) hmem
  change ((E.map (algebraMap K Ω)).ΨSq (m : ℤ)).IsRoot x at hx
  rw [WeierstrassCurve.map_ΨSq] at hx
  have hne : E.ΨSq (m : ℤ) ≠ 0 := E.ΨSq_ne_zero (by
    rw [Int.cast_natCast]
    exact Nat.cast_ne_zero.mpr (NeZero.ne m))
  have hxi : IsIntegral K x := by
    refine (IsAlgebraic.isIntegral ⟨E.ΨSq (m : ℤ), hne, ?_⟩)
    rw [aeval_def, eval₂_eq_eval_map]
    exact hx
  refine ⟨hxi, isIntegral_y_of_equation (W := E.toAffine.baseChange Ω)
    (isIntegral_algebraMap (x := E.a₁)) (isIntegral_algebraMap (x := E.a₂))
    (isIntegral_algebraMap (x := E.a₃)) (isIntegral_algebraMap (x := E.a₄))
    (isIntegral_algebraMap (x := E.a₆)) h.1 hxi⟩

/-- **Automorphisms fixing the elements algebraic over `K` fix the `m`-torsion of `E(Ω)`.** -/
lemma act_torsion (m : ℕ) [NeZero m] {σ : Ω ≃ₐ[K₀ K τ] Ω}
    (hσa : ∀ z : Ω, IsAlgebraic K z → σ z = z) {Q : Pt} (hQ : m • Q = 0) : act E σ Q = Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨hx, hy⟩ := isIntegral_of_torsion E m hQ
    change WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (resK E σ) _ = _
    rw [WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hσa x hx.isAlgebraic, hσa y hy.isAlgebraic⟩

/-! ### The generic points `P_X` and `P` -/

/-- The generic point `(x, y)` of `K(E)`, as a point of `E(K(E))`. -/
def genPt : WeierstrassCurve.Affine.Point (E.toAffine.baseChange FF) :=
  WeierstrassCurve.Affine.CoordinateRing.genericPoint

lemma nsmul_genPt (m : ℕ) [NeZero m] :
    m • genPt E = WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (pb E m) (genPt E) :=
  (genPointHom_pb E m).symm

lemma map_genPt (f : FF →ₐ[K] Ω) :
    ∃ h, WeierstrassCurve.Affine.Point.map (W' := E.toAffine) f (genPt E) =
      WeierstrassCurve.Affine.Point.some
        (f (WeierstrassCurve.Affine.CoordinateRing.genX E.toAffine))
        (f (WeierstrassCurve.Affine.CoordinateRing.genY E.toAffine)) h :=
  ⟨_, rfl⟩

/-- `P_X = (embE x, embE y) ∈ E(Ω)`, the generic point of `L_X`. -/
def ptX : Pt :=
  WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (embE E) (genPt E)

/-- `P = (mulByNEmb x, mulByNEmb y) ∈ E(Ω)`, the generic point of the source `L_m` of `[m]`. -/
def ptM (m : ℕ) [NeZero m] : Pt :=
  WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (mulByNEmb E m) (genPt E)

/-- `m • P = P_X`, from `mulByNEmb ∘ [m]^* = embE`. -/
lemma nsmul_ptM (m : ℕ) [NeZero m] : m • ptM E m = ptX E := by
  rw [ptM, ← map_nsmul, nsmul_genPt, WeierstrassCurve.Affine.Point.map_map, mulByNEmb_comp_pb]
  rfl

/-- An automorphism fixing `L_X` fixes `P_X`. -/
lemma act_ptX {σ : Ω ≃ₐ[K₀ K τ] Ω} (hσL : ∀ z ∈ (hemiData E).L, σ z = z) :
    act E σ (ptX E) = ptX E := by
  have h : (resK E σ).comp (embE E) = embE E :=
    AlgHom.ext fun f => hσL _ ((mem_hemiL_iff E _).mpr ⟨f, rfl⟩)
  rw [ptX, act_map, h]

/-! ### The cocycle `σ ↦ σP − P` -/

/-- The automorphisms of `Ω / K(τ)` fixing `L_X` and all elements algebraic over `K`. -/
def fixSubgroup : Subgroup (Ω ≃ₐ[K₀ K τ] Ω) where
  carrier := {σ | (∀ z ∈ (hemiData E).L, σ z = z) ∧ ∀ z : Ω, IsAlgebraic K z → σ z = z}
  mul_mem' {σ ρ} hσ hρ :=
    ⟨fun z hz => by rw [AlgEquiv.mul_apply, hρ.1 z hz, hσ.1 z hz],
     fun z hz => by rw [AlgEquiv.mul_apply, hρ.2 z hz, hσ.2 z hz]⟩
  one_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  inv_mem' {σ} hσ :=
    ⟨fun z hz => σ.injective (by
        rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, hσ.1 z hz]),
     fun z hz => σ.injective (by
        rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, hσ.2 z hz])⟩

/-- The cocycle `c(σ) = σP − P`. -/
def cocycle (m : ℕ) [NeZero m] (σ : Ω ≃ₐ[K₀ K τ] Ω) : Pt := act E σ (ptM E m) - ptM E m

lemma nsmul_cocycle (m : ℕ) [NeZero m] {σ : Ω ≃ₐ[K₀ K τ] Ω} (hσ : σ ∈ fixSubgroup E) :
    m • cocycle E m σ = 0 := by
  rw [cocycle, smul_sub, ← map_nsmul, nsmul_ptM, act_ptX E hσ.1, sub_self]

/-- **`c` is a homomorphism on `fixSubgroup`**: `c(σρ) = c(σ) + σ c(ρ) = c(σ) + c(ρ)`. -/
lemma cocycle_mul (m : ℕ) [NeZero m] {σ ρ : Ω ≃ₐ[K₀ K τ] Ω} (hσ : σ ∈ fixSubgroup E)
    (hρ : ρ ∈ fixSubgroup E) : cocycle E m (σ * ρ) = cocycle E m σ + cocycle E m ρ := by
  have h : act E ρ (ptM E m) = ptM E m + cocycle E m ρ := by
    rw [cocycle]; abel
  have h' : act E σ (cocycle E m ρ) = cocycle E m ρ := act_torsion E m hσ.2 (nsmul_cocycle E m hρ)
  change act E (σ * ρ) (ptM E m) - ptM E m = (act E σ (ptM E m) - ptM E m) + cocycle E m ρ
  rw [act_mul, h, map_add, h']
  abel

lemma cocycle_one (m : ℕ) [NeZero m] : cocycle E m 1 = 0 := by
  rw [cocycle, act_one, sub_self]

lemma cocycle_inv (m : ℕ) [NeZero m] {σ : Ω ≃ₐ[K₀ K τ] Ω} (hσ : σ ∈ fixSubgroup E) :
    cocycle E m σ⁻¹ = -cocycle E m σ := by
  have h := cocycle_mul E m (inv_mem hσ) hσ
  rw [inv_mul_cancel, cocycle_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

lemma cocycle_commutator (m : ℕ) [NeZero m] {σ ρ : Ω ≃ₐ[K₀ K τ] Ω} (hσ : σ ∈ fixSubgroup E)
    (hρ : ρ ∈ fixSubgroup E) : cocycle E m ⁅σ, ρ⁆ = 0 := by
  have hσρ := mul_mem hσ hρ
  have hσρσ := mul_mem hσρ (inv_mem hσ)
  rw [commutatorElement_def, cocycle_mul E m hσρσ (inv_mem hρ), cocycle_mul E m hσρ (inv_mem hσ),
    cocycle_mul E m hσ hρ, cocycle_inv E m hσ, cocycle_inv E m hρ]
  abel

/-- **A commutator in `fixSubgroup` fixes `P`.** -/
lemma act_commutator_ptM (m : ℕ) [NeZero m] {σ ρ : Ω ≃ₐ[K₀ K τ] Ω} (hσ : σ ∈ fixSubgroup E)
    (hρ : ρ ∈ fixSubgroup E) : act E ⁅σ, ρ⁆ (ptM E m) = ptM E m :=
  sub_eq_zero.mp (cocycle_commutator E m hσ hρ)

/-- An automorphism fixing `P` fixes `L_m` pointwise, through `x` and `y`. -/
lemma resK_comp_mulByNEmb (m : ℕ) [NeZero m] {g : Ω ≃ₐ[K₀ K τ] Ω}
    (hg : act E g (ptM E m) = ptM E m) : (resK E g).comp (mulByNEmb E m) = mulByNEmb E m := by
  obtain ⟨h₁, e₁⟩ := map_genPt E ((resK E g).comp (mulByNEmb E m))
  obtain ⟨h₂, e₂⟩ := map_genPt E (mulByNEmb E m)
  rw [ptM, act_map, e₁, e₂, WeierstrassCurve.Affine.Point.some.injEq] at hg
  exact algHom_ext_genXY E hg.1 hg.2

/-- **Commutators of automorphisms fixing `L_X` and `K^alg` fix the source `L_m` of `[m]`.**
The cocycle `σ ↦ σP − P` of the generic point `P` of `L_m` takes values in `E[m]`, which such
automorphisms fix, so it is a homomorphism to the commutative group `E(Ω)` and kills `⁅σ, ρ⁆`. -/
theorem commutator_fix_mulByNField (m : ℕ) [NeZero m] {σ ρ : Ω ≃ₐ[K₀ K τ] Ω}
    (hσL : ∀ z ∈ (hemiData E).L, σ z = z) (hρL : ∀ z ∈ (hemiData E).L, ρ z = z)
    (hσa : ∀ z : Ω, IsAlgebraic K z → σ z = z) (hρa : ∀ z : Ω, IsAlgebraic K z → ρ z = z) :
    ∀ z ∈ mulByNField E m, ⁅σ, ρ⁆ z = z := by
  intro z hz
  obtain ⟨f, rfl⟩ := (mem_mulByNField_iff E m z).mp hz
  have h := resK_comp_mulByNEmb E m (act_commutator_ptM E m ⟨hσL, hσa⟩ ⟨hρL, hρa⟩)
  exact congr($h f)

end CurvesJacobian.Cusp
