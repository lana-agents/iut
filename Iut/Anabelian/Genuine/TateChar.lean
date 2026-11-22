/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Anabelian.Tempered
import Iut.Anabelian.Genuine.Homs

/-!
# The Tate characters on the tempered group of a model orbicurve (MR18 run 17)

In characteristic `0` the tempered fundamental group `Orbicurve.temperedPi1 X` of a model
orbicurve `X = (E, ℓ, M, ±)` is, by definition, the tempered group of its **Galois presentation**
`Genuine.orbifold E ℓ M ±` (`Orbicurve.temperedPresentation_of_charZero`). The tempered group of
this presentation is lana-agents/tempered-fundamental-groups' `Kummer.TempPi (galoisData E ℓ M ±)`,
the group on which MR18's Tate data (`Iut.Frobenioid.BAn.tateGalDeckK`, `tateFrobK`) are stated.
So no comparison of the geometric and the Galois presentation is needed for the Tate data; this
file supplies the remaining pieces:

* `Orbicurve.temperedPi1EquivGalois`: `Π^tp_X ≃ₜ* Π^tp` of `Genuine.orbifold` (a cast).
* `Genuine.subsingleton_A_false`: for `± = false` (curves, e.g. `X̲_v` of type `(1, ℓ-tors)`)
  the finite group `A = H ⧸ H_L` of the presentation is trivial, as tfg's Tate objects require.
* **Change of Weierstrass model.** For a change of variables `C`, the generic point in the
  coordinates of `C • E` (`xMod`, `yMod`, Mathlib's convention `x = u²x' + r`,
  `y = u³y' + u²sx' + t`) satisfies the equation of `C • E` (`equation_xMod_yMod`), is fixed by
  `H_L` and integral over `k[x]`, hence lies in the coordinate ring `R` of the presentation
  (`xR`, `yR`). If `C • E` is in Tate normal form `y² + xy = x³ + π²b₄x + π²b₆`, this gives
  tfg's `TateObject.Data` on `R` (`tateData`), hence the graph character
  `TateObject.character : Π^tp_X → ℤ` of the tempered group of `X` itself.
* **The `ℤ/2`-character of the `2`-isogeny** (`sqrtSign`, `sqrtSignPi`, `tempSign`). tfg's
  `TateObject.DoubleData` needs `x − e` to be a unit of `R` (`R[t]/(t² − c)` étale), which fails
  for `E ∖ {0}` and for `X̲_v`. Instead, for `c ∈ R` with `a c + b g = 1` and `h² = c g` in `R`
  (for `c = x − e`, `e` the `x`-coordinate of a rational `2`-torsion point:
  `(y + x/2)² = (x − e) g(x)` with `g(e) ≠ 0`), the inertia at every place centered on `Spec R`
  fixes `√c` (`fix_sqrt_of_mem_S`: at each place `c` or `g` is a unit, and then `√c` resp.
  `√g = h/√c` is fixed by ckt's `eq_of_mem_inertia`). So `σ ↦ σ(√c)/√c` descends to
  `Π_U = H ⧸ ⟨⟨S⟩⟩` and, through `tempToPi`, to `Π^tp`: the character of the étale double cover
  `√c` of `Spec R` ([EtTh] §1: `X'` with `Ÿ = Y ×_X X'`), with the expected values on Galois
  elements (`tempSign_galoisToTempered`).
-/

namespace Iut.Anabelian

universe u

open TemperedFundamentalGroups Pi1.Orbifold WeierstrassCurve AffOrbicurve Polynomial

noncomputable section

attribute [local instance low] Classical.propDecidable

/-! ### The presentation -/

/-- Equal affine orbifolds have isomorphic tempered fundamental groups. -/
def canonicalTemperedPi1EquivOfEq {k : Type u} [Field k] {Y Y' : AffineOrbifold k}
    (h : Y = Y') : Y.canonicalTemperedPi1 ≃ₜ* Y'.canonicalTemperedPi1 := by
  subst h
  exact ContinuousMulEquiv.refl _

/-- **In characteristic `0`, `Π^tp_X` is the tempered group of the Galois presentation**
`Genuine.orbifold E ℓ M ±` (by definition of `Orbicurve.temperedPresentation`). -/
def Orbicurve.temperedPi1EquivGalois {k : Type u} [Field k] [CharZero k] (X : Orbicurve k)
    {pm : Bool} (hpm : X.pm = pm) :
    X.temperedPi1 ≃ₜ* (Genuine.orbifold X.E X.level X.M pm).canonicalTemperedPi1 :=
  canonicalTemperedPi1EquivOfEq ((congrArg Sigma.fst X.temperedPresentation_of_charZero).trans
    (congrArg (Genuine.orbifold X.E X.level X.M) hpm))

namespace Genuine

section Presentation

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]
  (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool)

/-- The valuation subring of `Ω` of the tempered group of the Galois presentation. -/
abbrev tempV : ValuationSubring (Ω E) := (orbifold E ℓ M pm).V (canonicalValuationSubring k)

lemma tempV_comap :
    (tempV E ℓ M pm).comap (algebraMap k (Ω E)) = canonicalValuationSubring k :=
  (orbifold E ℓ M pm).V_comap _

/-- The tempered group of the Galois presentation is `Kummer.TempPi` of `galoisData`. -/
lemma canonicalTemperedPi1_eq :
    (orbifold E ℓ M pm).canonicalTemperedPi1 =
      Kummer.TempPi (galoisData E ℓ M pm) (canonicalValuationSubring k) (tempV E ℓ M pm)
        (tempV_comap E ℓ M pm) := rfl

/-- **For curves (`± = false`) the group `A = H ⧸ H_L` of the presentation is trivial.** -/
instance subsingleton_A_false : Subsingleton (galoisData E ℓ M false).A := by
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  exact (x⁻¹ * y).2

variable {E ℓ M pm}

/-- `H_L = Aut(Ω / L_X)` fixes the generic point. -/
lemma fix_generic_of_mem_HL {σ : Ω E ≃ₐ[K₀ k (xG E)] Ω E}
    (hσ : σ ∈ (galoisData E ℓ M pm).HL) : σ (xG E) = xG E ∧ σ (yG E) = yG E := by
  have h : act E (Genuine.galHom E σ) (genericPoint E) = genericPoint E :=
    act_generic_of_mem_geom E hσ
  have h' : act E (Genuine.galHom E σ) (genericPoint E) =
      Affine.Point.some (Genuine.galHom E σ (xG E)) (Genuine.galHom E σ (yG E))
        ((Affine.baseChange_nonsingular (W := E)
        (f := σk E (Genuine.galHom E σ)) (σk E (Genuine.galHom E σ)).toRingHom.injective _ _).mpr
        (nonsingular_generic E)) := rfl
  rw [h'] at h
  have h1 := (Affine.Point.some.inj h).1
  have h2 := (Affine.Point.some.inj h).2
  exact ⟨by simpa using h1, by simpa using h2⟩

omit [CharZero k] [E.IsElliptic] in
lemma fix_algebraMap (σ : Ω E ≃ₐ[K₀ k (xG E)] Ω E) (a : k) :
    σ (algebraMap k (Ω E) a) = algebraMap k (Ω E) a := by
  rw [IsScalarTower.algebraMap_apply k (K₀ k (xG E)) (Ω E), σ.commutes]

omit [CharZero k] [E.IsElliptic] in
lemma fix_xG (σ : Ω E ≃ₐ[K₀ k (xG E)] Ω E) : σ (xG E) = xG E :=
  σ.commutes ⟨xG E, IntermediateField.subset_adjoin k _ (Set.mem_singleton _)⟩

/-! ### The generic point in another Weierstrass model -/

variable (E) in
/-- The `x`-coordinate of the generic point in the model `C • E`: `x' = (x − r)/u²`. -/
def xMod (C : VariableChange k) : Ω E :=
  (xG E - algebraMap k (Ω E) C.r) / algebraMap k (Ω E) (C.u : k) ^ 2

variable (E) in
/-- The `y`-coordinate of the generic point in the model `C • E`:
`y' = (y − t − s(x − r))/u³`. -/
def yMod (C : VariableChange k) : Ω E :=
  (yG E - algebraMap k (Ω E) C.t - algebraMap k (Ω E) C.s * (xG E - algebraMap k (Ω E) C.r)) /
    algebraMap k (Ω E) (C.u : k) ^ 3

omit [CharZero k] in
/-- The Weierstrass equation of the generic point, in `Ω`. -/
lemma equation_generic :
    yG E ^ 2 + algebraMap k (Ω E) E.a₁ * xG E * yG E + algebraMap k (Ω E) E.a₃ * yG E =
      xG E ^ 3 + algebraMap k (Ω E) E.a₂ * xG E ^ 2 + algebraMap k (Ω E) E.a₄ * xG E +
        algebraMap k (Ω E) E.a₆ := by
  have h := (nonsingular_generic E).1
  rw [Affine.equation_iff] at h
  simpa [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] using h

omit [CharZero k] [E.IsElliptic] in
/-- **Change of Weierstrass model for points**: if `(x, y)` (in a field `F` over `k` via `φ`)
satisfies the equation of `E`, then `x' = (x − r)/u²`, `y' = (y − t − s(x − r))/u³` satisfy the
equation of `C • E`. -/
lemma equation_variableChange {F : Type*} [Field F] (φ : k →+* F) (C : VariableChange k)
    {x y : F} (h : y ^ 2 + φ E.a₁ * x * y + φ E.a₃ * y =
      x ^ 3 + φ E.a₂ * x ^ 2 + φ E.a₄ * x + φ E.a₆) :
    ((y - φ C.t - φ C.s * (x - φ C.r)) / φ (C.u : k) ^ 3) ^ 2 +
        φ (C • E).a₁ * ((x - φ C.r) / φ (C.u : k) ^ 2) *
          ((y - φ C.t - φ C.s * (x - φ C.r)) / φ (C.u : k) ^ 3) +
        φ (C • E).a₃ * ((y - φ C.t - φ C.s * (x - φ C.r)) / φ (C.u : k) ^ 3) =
      ((x - φ C.r) / φ (C.u : k) ^ 2) ^ 3 + φ (C • E).a₂ * ((x - φ C.r) / φ (C.u : k) ^ 2) ^ 2 +
        φ (C • E).a₄ * ((x - φ C.r) / φ (C.u : k) ^ 2) + φ (C • E).a₆ := by
  have hu : φ (C.u : k) ≠ 0 := (_root_.map_ne_zero _).2 C.u.ne_zero
  have hui : φ ((C.u⁻¹ : kˣ) : k) = (φ (C.u : k))⁻¹ := by
    rw [← map_inv₀, Units.val_inv_eq_inv_val]
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆, map_mul, map_add, map_sub, map_pow, map_ofNat, hui]
  field_simp
  linear_combination h

omit [CharZero k] in
/-- **The generic point satisfies the equation of `C • E` in the coordinates `xMod`, `yMod`.** -/
lemma equation_xMod_yMod (C : VariableChange k) :
    yMod E C ^ 2 + algebraMap k (Ω E) (C • E).a₁ * xMod E C * yMod E C +
        algebraMap k (Ω E) (C • E).a₃ * yMod E C =
      xMod E C ^ 3 + algebraMap k (Ω E) (C • E).a₂ * xMod E C ^ 2 +
        algebraMap k (Ω E) (C • E).a₄ * xMod E C + algebraMap k (Ω E) (C • E).a₆ :=
  equation_variableChange (algebraMap k (Ω E)) C equation_generic

/-- **A rational point `(e, f)` of `C • E` in Tate normal form with `2f + e = 0`** (a `2`-torsion
point) satisfies `f² + ef = e³ + a₄e + a₆` and `3e² + e/2 + a₄ ≠ 0` (nonsingularity). -/
lemma two_torsion_data {C : VariableChange k} (h₁ : (C • E).a₁ = 1) (h₂ : (C • E).a₂ = 0)
    (h₃ : (C • E).a₃ = 0) {e f : k} (he : (C • E).toAffine.Equation e f) (hf : 2 * f + e = 0) :
    f ^ 2 + e * f = e ^ 3 + (C • E).a₄ * e + (C • E).a₆ ∧ 3 * e ^ 2 + e / 2 + (C • E).a₄ ≠ 0 := by
  have hns := (Affine.equation_iff_nonsingular (W := (C • E).toAffine)).1 he
  rw [Affine.nonsingular_iff'] at hns
  rw [Affine.equation_iff] at he
  rw [h₁, h₂, h₃] at he hns
  refine ⟨by linear_combination he, fun hd => ?_⟩
  have hd' : 3 * e ^ 2 + e / 2 + (C • E).toAffine.a₄ = 0 := hd
  rcases hns.2 with h | h
  · exact h (by linear_combination -hd' + (1 / 2 : k) * hf)
  · exact h (by linear_combination hf)

omit [CharZero k] [E.IsElliptic] in
lemma algebraMap_mem_A₀ (a : k) : algebraMap k (Ω E) a ∈ A₀ k (xG E) :=
  Subalgebra.algebraMap_mem _ a

omit [CharZero k] [E.IsElliptic] in
lemma xG_mem_A₀ : xG E ∈ A₀ k (xG E) := Algebra.subset_adjoin (Set.mem_singleton _)

omit [CharZero k] [E.IsElliptic] in
lemma isIntegral_of_mem_A₀ {z : Ω E} (hz : z ∈ A₀ k (xG E)) : IsIntegral (A₀ k (xG E)) z := by
  have : z = algebraMap (A₀ k (xG E)) (Ω E) ⟨z, hz⟩ := rfl
  rw [this]
  exact isIntegral_algebraMap

omit [CharZero k] in
/-- `y` is integral over `k[x]`. -/
lemma isIntegral_yG_A₀ : IsIntegral (A₀ k (xG E)) (yG E) := by
  have h := equation_generic (E := E)
  let xx : A₀ k (xG E) := ⟨xG E, xG_mem_A₀⟩
  let b : A₀ k (xG E) := algebraMap k (A₀ k (xG E)) E.a₁ * xx + algebraMap k (A₀ k (xG E)) E.a₃
  let c : A₀ k (xG E) := xx ^ 3 + algebraMap k (A₀ k (xG E)) E.a₂ * xx ^ 2 +
    algebraMap k (A₀ k (xG E)) E.a₄ * xx + algebraMap k (A₀ k (xG E)) E.a₆
  refine ⟨X ^ 2 + (C b * X - C c), monic_X_pow_add ?_, ?_⟩
  · refine (degree_sub_le _ _).trans_lt ?_
    refine max_lt ((degree_C_mul_X_le _).trans_lt (by norm_num)) ?_
    exact degree_C_le.trans_lt (by norm_num)
  · simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X, b, c, xx]
    change yG E ^ 2 + ((algebraMap k (Ω E) E.a₁ * xG E + algebraMap k (Ω E) E.a₃) *
      yG E - (xG E ^ 3 + algebraMap k (Ω E) E.a₂ * xG E ^ 2 +
      algebraMap k (Ω E) E.a₄ * xG E + algebraMap k (Ω E) E.a₆)) = 0
    linear_combination h

omit [CharZero k] [E.IsElliptic] in
lemma isIntegral_xMod (C : VariableChange k) : IsIntegral (A₀ k (xG E)) (xMod E C) := by
  have hu : algebraMap k (Ω E) (C.u : k) ≠ 0 := (_root_.map_ne_zero _).2 C.u.ne_zero
  have : xMod E C = algebraMap k (Ω E) ((C.u : k)⁻¹ ^ 2) * (xG E - algebraMap k (Ω E) C.r) := by
    rw [xMod, map_pow, map_inv₀]
    field_simp
  rw [this]
  exact isIntegral_of_mem_A₀ (Subalgebra.mul_mem _ (algebraMap_mem_A₀ _)
    (Subalgebra.sub_mem _ xG_mem_A₀ (algebraMap_mem_A₀ _)))

omit [CharZero k] in
lemma isIntegral_yMod (C : VariableChange k) : IsIntegral (A₀ k (xG E)) (yMod E C) := by
  have hu : algebraMap k (Ω E) (C.u : k) ≠ 0 := (_root_.map_ne_zero _).2 C.u.ne_zero
  have : yMod E C = algebraMap k (Ω E) ((C.u : k)⁻¹ ^ 3) * yG E -
      algebraMap k (Ω E) ((C.u : k)⁻¹ ^ 3) *
        (algebraMap k (Ω E) C.t + algebraMap k (Ω E) C.s * (xG E - algebraMap k (Ω E) C.r)) := by
    rw [yMod, map_pow, map_inv₀]
    field_simp
    ring
  rw [this]
  refine IsIntegral.sub (IsIntegral.mul (isIntegral_of_mem_A₀ (algebraMap_mem_A₀ _))
    isIntegral_yG_A₀) (isIntegral_of_mem_A₀ ?_)
  exact Subalgebra.mul_mem _ (algebraMap_mem_A₀ _) (Subalgebra.add_mem _ (algebraMap_mem_A₀ _)
    (Subalgebra.mul_mem _ (algebraMap_mem_A₀ _)
      (Subalgebra.sub_mem _ xG_mem_A₀ (algebraMap_mem_A₀ _))))

lemma xMod_mem_L (C : VariableChange k) : xMod E C ∈ (galoisData E ℓ M pm).L := by
  refine (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => ?_
  rw [xMod, map_div₀, map_pow, map_sub, fix_xG, fix_algebraMap, fix_algebraMap]

lemma yMod_mem_L (C : VariableChange k) : yMod E C ∈ (galoisData E ℓ M pm).L := by
  refine (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => ?_
  rw [yMod, map_div₀, map_pow, map_sub, map_sub, map_mul, map_sub, fix_xG,
    (fix_generic_of_mem_HL hσ).2]
  simp only [fix_algebraMap]

variable (ℓ M pm) in
/-- `x'` as an element of the coordinate ring `R` of the Galois presentation. -/
def xR (C : VariableChange k) : (galoisData E ℓ M pm).R :=
  CoordRing.mk (xMod E C) (xMod_mem_L C) (isIntegral_xMod C)

variable (ℓ M pm) in
/-- `y'` as an element of the coordinate ring `R` of the Galois presentation. -/
def yR (C : VariableChange k) : (galoisData E ℓ M pm).R :=
  CoordRing.mk (yMod E C) (yMod_mem_L C) (isIntegral_yMod C)

@[simp] lemma algebraMap_xR (C : VariableChange k) :
    algebraMap (galoisData E ℓ M pm).R (Ω E) (xR ℓ M pm C) = xMod E C := rfl

@[simp] lemma algebraMap_yR (C : VariableChange k) :
    algebraMap (galoisData E ℓ M pm).R (Ω E) (yR ℓ M pm C) = yMod E C := rfl

lemma algebraMap_R_k (a : k) :
    algebraMap (galoisData E ℓ M pm).R (Ω E) (algebraMap k (galoisData E ℓ M pm).R a) =
      algebraMap k (Ω E) a :=
  (IsScalarTower.algebraMap_apply k (galoisData E ℓ M pm).R (Ω E) a).symm

variable (ℓ M pm) in
/-- **The Tate data of `X` in the coordinates of a Weierstrass model in Tate normal form**:
if `C • E` is `y² + xy = x³ + π²b₄x + π²b₆` (`π ∈ O` a nonzero non-unit, `b₄, b₆ ∈ O`), the
generic point in the coordinates of `C • E` is a point of tfg's `TateObject.Data` on the
coordinate ring `R` of the Galois presentation. -/
def tateData {O : ValuationSubring k} (C : VariableChange k) (π b₄ b₆ : O) (hπ0 : π ≠ 0)
    (hπ : π ∈ IsLocalRing.maximalIdeal O) (h₁ : (C • E).a₁ = 1) (h₂ : (C • E).a₂ = 0)
    (h₃ : (C • E).a₃ = 0) (h₄ : (C • E).a₄ = (π : k) ^ 2 * b₄)
    (h₆ : (C • E).a₆ = (π : k) ^ 2 * b₆) : TateObject.Data O (galoisData E ℓ M pm).R where
  π := π
  b₄ := b₄
  b₆ := b₆
  π_ne_zero := hπ0
  π_mem := hπ
  x := xR ℓ M pm C
  y := yR ℓ M pm C
  equation := by
    apply CoordRing.algebraMap_injective
    have h := equation_xMod_yMod (E := E) C
    rw [h₁, h₂, h₃, h₄, h₆, map_one, map_zero, one_mul, zero_mul, add_zero, zero_mul,
      add_zero] at h
    simp only [map_mul, map_pow] at h
    simp only [map_add, map_mul, map_pow, algebraMap_xR, algebraMap_yR, algebraMap_R_k]
    linear_combination h

/-! ### The Kummer data of a rational `2`-torsion point in Tate normal form -/

variable (ℓ M pm) in
/-- `c = x' − e`, the Kummer parameter of the `2`-isogeny attached to `(e, ·)`. -/
def cR (C : VariableChange k) (e : k) : (galoisData E ℓ M pm).R :=
  xR ℓ M pm C - algebraMap k _ e

variable (ℓ M pm) in
/-- `g = x'² + (e + 1/4) x' + (e² + e/4 + a₄)`, the cofactor: `(x' − e) g = x'³ + x'²/4 + a₄x' + a₆`
when `(e, −e/2)` is a point of `C • E` in Tate normal form. -/
def gR (C : VariableChange k) (e : k) : (galoisData E ℓ M pm).R :=
  xR ℓ M pm C ^ 2 + algebraMap k _ (e + 1 / 4) * xR ℓ M pm C +
    algebraMap k _ (e ^ 2 + e / 4 + (C • E).a₄)

variable (ℓ M pm) in
/-- `h = y' + x'/2`, with `h² = c g`. -/
def hR (C : VariableChange k) : (galoisData E ℓ M pm).R :=
  yR ℓ M pm C + algebraMap k _ (1 / 2) * xR ℓ M pm C

variable (ℓ M pm) in
/-- `a = −(x' + 2e + 1/4)/d`, `d = 3e² + e/2 + a₄`, so that `a c + g/d = 1`. -/
def aR (C : VariableChange k) (e : k) : (galoisData E ℓ M pm).R :=
  algebraMap k _ (-(3 * e ^ 2 + e / 2 + (C • E).a₄)⁻¹) *
    (xR ℓ M pm C + algebraMap k _ (2 * e + 1 / 4))

variable (ℓ M pm) in
/-- `b = 1/d`. -/
def bR (C : VariableChange k) (e : k) : (galoisData E ℓ M pm).R :=
  algebraMap k _ (3 * e ^ 2 + e / 2 + (C • E).a₄)⁻¹

/-- **`h² = c g`** for a point `(e, f)` of `C • E` (Tate normal form) with `2f + e = 0`. -/
theorem hR_sq {C : VariableChange k} (h₁ : (C • E).a₁ = 1) (h₂ : (C • E).a₂ = 0)
    (h₃ : (C • E).a₃ = 0) {e f : k}
    (he : f ^ 2 + e * f = e ^ 3 + (C • E).a₄ * e + (C • E).a₆) (hf : 2 * f + e = 0) :
    hR ℓ M pm C ^ 2 = cR ℓ M pm C e * gR ℓ M pm C e := by
  apply CoordRing.algebraMap_injective
  have h := equation_xMod_yMod (E := E) C
  rw [h₁, h₂, h₃, map_one, map_zero, one_mul, zero_mul, add_zero, zero_mul, add_zero] at h
  have he' : (C • E).a₆ + e ^ 3 + e ^ 2 / 4 + (C • E).a₄ * e = 0 := by
    linear_combination -he + (2 * f + e) / 4 * hf
  have he'' := congrArg (algebraMap k (Ω E)) he'
  simp only [map_add, map_mul, map_pow, map_div₀, map_ofNat, map_zero] at he''
  simp only [hR, cR, gR, map_add, map_mul, map_pow, map_sub, algebraMap_xR, algebraMap_yR,
    algebraMap_R_k, map_div₀, map_one, map_ofNat]
  linear_combination h + he''

/-- **`a c + b g = 1`** when `d = 3e² + e/2 + a₄ ≠ 0`. -/
theorem aR_mul_add {C : VariableChange k} {e : k} (hd : 3 * e ^ 2 + e / 2 + (C • E).a₄ ≠ 0) :
    aR ℓ M pm C e * cR ℓ M pm C e + bR ℓ M pm C e * gR ℓ M pm C e = 1 := by
  apply CoordRing.algebraMap_injective
  have hd' : algebraMap k (Ω E) (3 * e ^ 2 + e / 2 + (C • E).a₄) ≠ 0 := (_root_.map_ne_zero _).2 hd
  simp only [map_add, map_mul, map_pow, map_div₀, map_ofNat] at hd'
  have hinv := inv_mul_cancel₀ hd'
  simp only [aR, bR, cR, gR, map_add, map_mul, map_pow, map_sub, map_neg, map_inv₀,
    algebraMap_xR, algebraMap_R_k, map_div₀, map_one, map_ofNat]
  linear_combination hinv

lemma xMod_ne (C : VariableChange k) (e : k) : xMod E C ≠ algebraMap k (Ω E) e := by
  intro h
  have hu : algebraMap k (Ω E) (C.u : k) ≠ 0 := (_root_.map_ne_zero _).2 C.u.ne_zero
  have hx : xG E = algebraMap k (Ω E) ((C.u : k) ^ 2 * e + C.r) := by
    rw [xMod, div_eq_iff (pow_ne_zero 2 hu)] at h
    rw [map_add, map_mul, map_pow]
    linear_combination h
  exact transcendental_xG E (hx ▸ isAlgebraic_algebraMap _)

/-- `c = x' − e ≠ 0`. -/
lemma cR_ne_zero (C : VariableChange k) (e : k) : cR ℓ M pm C e ≠ 0 := by
  intro h
  have := congrArg (algebraMap (galoisData E ℓ M pm).R (Ω E)) h
  rw [cR, map_sub, algebraMap_xR, algebraMap_R_k, map_zero, sub_eq_zero] at this
  exact xMod_ne C e this

end Presentation

end Genuine

/-! ### The `ℤ/2`-character of an étale double cover `√c` -/

namespace TateChar

section Kummer

variable {k Ω : Type u} [Field k] [CharZero k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : GaloisData k t)

omit [CharZero k] in
/-- Elements of the coordinate ring are fixed by `H_L`. -/
lemma fix_R_of_mem_HL {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ D.HL) (x : D.R) :
    σ (algebraMap D.R Ω x) = algebraMap D.R Ω x :=
  (IntermediateField.mem_fixedField_iff _ _).1 (CoordRing.algebraMap_mem x) σ hσ

omit [Algebra k Ω] in
lemma ne_neg_self [CharZero Ω] {γ : Ω} (hγ : γ ≠ 0) : γ ≠ -γ := by
  intro h
  have : (2 : Ω) * γ = 0 := by linear_combination h
  exact hγ ((mul_eq_zero.1 this).resolve_left two_ne_zero)

omit [CharZero k] in
lemma eq_or_eq_neg_of_sq_eq {σ : Ω ≃ₐ[K₀ k t] Ω} {γ : Ω} (h : σ (γ ^ 2) = γ ^ 2) :
    σ γ = γ ∨ σ γ = -γ := by
  rw [map_pow] at h
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

/-- An element `x` of `W` of valuation `1` with `σ x = ±x`, `σ` in the inertia group of `W`, is
fixed by `σ`. -/
lemma fix_of_sign {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ GaloisPi1.inertia W) {x : Ω} (hx : x ∈ W)
    (hvx : W.valuation x = 1) (h : σ x = x ∨ σ x = -x) : σ x = x := by
  rcases h with h | h
  · exact h
  · exact KummerTheory.Curve.eq_of_mem_inertia (k := k) hk hσ hx hvx two_pos (ζ := -1)
      (by norm_num) (by rw [h]; ring)

/-- A square root of a `W`-unit is a `W`-unit. -/
lemma valuation_eq_one_of_sq {W : ValuationSubring Ω} {x : Ω} (hx : x ∈ W)
    (h : W.valuation (x ^ 2) = 1) : W.valuation x = 1 := by
  have h1 := (W.valuation_le_one_iff x).mpr hx
  refine le_antisymm h1 ?_
  by_contra hlt
  have := mul_lt_one_of_lt_of_le (not_le.mp hlt) h1
  rw [← map_mul, ← sq, h] at this
  exact lt_irrefl _ this

/-- **Inertia at the places centered on `Spec R` fixes `√c`**, for `c ∈ R` with `a c + b g = 1`
and `h² = c g` in `R` (`c ≠ 0`): at each such place `c` or `g` is a unit, and `√c` resp.
`√g = h/√c` is a root of a unit. -/
theorem fix_sqrt_of_mem_S {c g h a b : D.R} (hab : a * c + b * g = 1) (hh : h ^ 2 = c * g)
    (hc : c ≠ 0) {γ : Ω} (hγ : γ ^ 2 = algebraMap D.R Ω c) {σ : Ω ≃ₐ[K₀ k t] Ω}
    (hσ : σ ∈ D.S) : σ γ = γ := by
  obtain ⟨hσL, W, hk, htW, hin⟩ := hσ
  have hW : IsCentered k t W := ⟨hk, htW⟩
  have mem : ∀ x : D.R, algebraMap D.R Ω x ∈ W := fun x => toΩ_mem hW D.L x
  have fix := fix_R_of_mem_HL D hσL
  have hc0 : algebraMap D.R Ω c ≠ 0 := fun h0 => hc (CoordRing.algebraMap_injective
    (h0.trans (map_zero _).symm))
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hγ]; ring)
  have hγW : γ ∈ W := KummerTheory.Curve.mem_of_pow_mem two_pos (hγ ▸ mem c)
  have hσγ : σ γ = γ ∨ σ γ = -γ := eq_or_eq_neg_of_sq_eq (by rw [hγ, fix])
  have key : W.valuation (algebraMap D.R Ω c) = 1 ∨ W.valuation (algebraMap D.R Ω g) = 1 := by
    by_contra hne
    push Not at hne
    have hc1 := lt_of_le_of_ne ((W.valuation_le_one_iff _).mpr (mem c)) hne.1
    have hg1 := lt_of_le_of_ne ((W.valuation_le_one_iff _).mpr (mem g)) hne.2
    have h1 : algebraMap D.R Ω a * algebraMap D.R Ω c + algebraMap D.R Ω b * algebraMap D.R Ω g =
        1 := by rw [← map_mul, ← map_mul, ← map_add, hab, map_one]
    have ha := (W.valuation_le_one_iff _).mpr (mem a)
    have hb := (W.valuation_le_one_iff _).mpr (mem b)
    have hlt : W.valuation (algebraMap D.R Ω a * algebraMap D.R Ω c +
        algebraMap D.R Ω b * algebraMap D.R Ω g) < 1 := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul]; exact (mul_le_of_le_one_left' ha).trans_lt hc1
      · rw [map_mul]; exact (mul_le_of_le_one_left' hb).trans_lt hg1
    rw [h1, map_one] at hlt
    exact lt_irrefl _ hlt
  rcases key with hc1 | hg1
  · exact fix_of_sign hk hin hγW (valuation_eq_one_of_sq hγW (by rw [hγ, hc1])) hσγ
  · -- `δ = h/γ` is a square root of `g`
    set δ := algebraMap D.R Ω h / γ with hδ
    have hδ2 : δ ^ 2 = algebraMap D.R Ω g := by
      rw [hδ, div_pow, hγ, ← map_pow, hh, map_mul, mul_div_cancel_left₀ _ hc0]
    have hδW : δ ∈ W := KummerTheory.Curve.mem_of_pow_mem two_pos (hδ2 ▸ mem g)
    have hσδ : σ δ = δ ∨ σ δ = -δ := eq_or_eq_neg_of_sq_eq (by rw [hδ2, fix])
    have hδfix := fix_of_sign hk hin hδW (valuation_eq_one_of_sq hδW (by rw [hδ2, hg1])) hσδ
    have hh0 : algebraMap D.R Ω h ≠ 0 := by
      intro h0
      have : algebraMap D.R Ω c * algebraMap D.R Ω g = 0 := by
        rw [← map_mul, ← hh, map_pow, h0]; ring
      rcases mul_eq_zero.1 this with h' | h'
      · exact hc0 h'
      · rw [h', map_zero] at hg1; exact zero_ne_one hg1
    rw [hδ, map_div₀, fix] at hδfix
    rcases hσγ with h' | h'
    · exact h'
    · exfalso
      haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
      rw [h', div_neg] at hδfix
      have h0 : algebraMap D.R Ω h / γ = 0 := by linear_combination -hδfix / 2
      exact hh0 ((div_eq_zero_iff.1 h0).resolve_right hγ0)

end Kummer

section Sign

variable {k Ω : Type u} [Field k] [CharZero k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : GaloisData k t) {γ : Ω} (hγ0 : γ ≠ 0)
  (hfix : ∀ σ ∈ D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) (γ ^ 2) = γ ^ 2)

/-- **The sign character** `σ ↦ σ(γ)/γ ∈ {±1}` of `H`, for `γ ≠ 0` with `γ²` fixed by `H`. -/
def sqrtSign : D.H →* Multiplicative (ZMod 2) where
  toFun σ := if (σ : Ω ≃ₐ[K₀ k t] Ω) γ = γ then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' σ τ := by
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
    have hne := ne_neg_self hγ0
    have hne' : -γ ≠ γ := fun h => hne h.symm
    have h11 : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
    rcases eq_or_eq_neg_of_sq_eq (hfix σ σ.2) with hσ | hσ <;>
    rcases eq_or_eq_neg_of_sq_eq (hfix τ τ.2) with hτ | hτ <;>
    simp [Subgroup.coe_mul, AlgEquiv.mul_apply, hσ, hτ, map_neg, hne', h11]

lemma sqrtSign_apply (σ : D.H) :
    sqrtSign D hγ0 hfix σ =
      if (σ : Ω ≃ₐ[K₀ k t] Ω) γ = γ then 1 else Multiplicative.ofAdd 1 := rfl

lemma sqrtSign_eq_one_iff (σ : D.H) :
    sqrtSign D hγ0 hfix σ = 1 ↔ (σ : Ω ≃ₐ[K₀ k t] Ω) γ = γ := by
  rw [sqrtSign_apply]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

variable [IsGalois (K₀ k t) Ω]

/-- **The closed normal subgroup generated by the inertia set `S` lies in the kernel of the sign
character**, if every element of `S` fixes `γ`. -/
theorem kernel_le_ker_sqrtSign (hS : ∀ σ ∈ D.S, σ γ = γ) :
    GaloisPi1.kernel D.H D.S ≤ (sqrtSign D hγ0 hfix).ker := by
  let St := MulAction.stabilizer (Ω ≃ₐ[K₀ k t] Ω) γ
  have hcl : IsClosed (St : Set (Ω ≃ₐ[K₀ k t] Ω)) :=
    Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral γ)
  have hle : GaloisPi1.ambientKernel D.H D.S ≤ St := by
    refine Subgroup.topologicalClosure_minimal _ ?_ hcl
    rw [Subgroup.closure_le]
    rintro _ ⟨h, hh, s, hs, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    have hsq : h⁻¹ (γ ^ 2) = γ ^ 2 := hfix _ (D.H.inv_mem hh)
    have hs' : s (h⁻¹ γ) = h⁻¹ γ := by
      rcases eq_or_eq_neg_of_sq_eq hsq with e | e
      · rw [e, hS s hs]
      · rw [e, map_neg, hS s hs]
    simp only [AlgEquiv.mul_apply, hs']
    exact AlgEquiv.apply_symm_apply h γ
  intro σ hσ
  rw [MonoidHom.mem_ker, sqrtSign_eq_one_iff]
  exact hle hσ

/-- The sign character on `Π_U = H ⧸ ⟨⟨S⟩⟩`. -/
def sqrtSignPi (hS : ∀ σ ∈ D.S, σ γ = γ) :
    KummerTheory.Curve.Pi D →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift _ (sqrtSign D hγ0 hfix) (kernel_le_ker_sqrtSign D hγ0 hfix hS)

variable (O : ValuationSubring k) (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)

/-- **The sign character on the tempered group**: `Π^tp → Π_U → ℤ/2`, the character of the
étale double cover `√(γ²)` of `Spec R`. -/
def tempSign (hS : ∀ σ ∈ D.S, σ γ = γ) : Kummer.TempPi D O V hV →* Multiplicative (ZMod 2) :=
  (sqrtSignPi D hγ0 hfix hS).comp (Kummer.tempToPi D O V hV)

/-- **On Galois elements the sign character is the Galois action on `γ`.** -/
theorem tempSign_galoisToTempered (hS : ∀ σ ∈ D.S, σ γ = γ)
    (σ : decompositionGroup D.R V) :
    tempSign D hγ0 hfix O V hV hS (galoisToTempered O D.R D.A hV σ) =
      if (σ : Ω ≃ₐ[D.R] Ω) γ = γ then 1 else Multiplicative.ofAdd 1 := by
  rw [tempSign, MonoidHom.comp_apply, Kummer.tempToPi_galoisToTempered]
  rfl

/-- **The kernel of the sign character is open.** -/
theorem isOpen_ker_tempSign (hS : ∀ σ ∈ D.S, σ γ = γ) :
    IsOpen ((tempSign D hγ0 hfix O V hV hS).ker : Set (Kummer.TempPi D O V hV)) := by
  have hH : IsOpen ((sqrtSign D hγ0 hfix).ker : Set D.H) := by
    have e : ((sqrtSign D hγ0 hfix).ker : Set D.H) =
        Subtype.val ⁻¹' (MulAction.stabilizer (Ω ≃ₐ[K₀ k t] Ω) γ : Set (Ω ≃ₐ[K₀ k t] Ω)) := by
      ext σ
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, sqrtSign_eq_one_iff, Set.mem_preimage,
        MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    rw [e]
    exact (stabilizer_isOpen_of_isIntegral γ).preimage continuous_subtype_val
  have hPi : IsOpen ((sqrtSignPi D hγ0 hfix hS).ker : Set (KummerTheory.Curve.Pi D)) := by
    have e : ((sqrtSignPi D hγ0 hfix hS).ker : Set (KummerTheory.Curve.Pi D)) =
        (QuotientGroup.mk : D.H → KummerTheory.Curve.Pi D) '' (sqrtSign D hγ0 hfix).ker := by
      ext x
      obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
      constructor
      · intro h
        exact ⟨σ, h, rfl⟩
      · rintro ⟨τ, hτ, e⟩
        rw [← e]
        exact hτ
    rw [e]
    exact QuotientGroup.isOpenMap_coe _ hH
  exact hPi.preimage (Kummer.continuous_tempToPi D O V hV)

end Sign

end TateChar

end

end Iut.Anabelian
