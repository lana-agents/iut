/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Pi1.Orbicurve.GaloisPi1
import Iut.Cor312.ThetaData.PointMap
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The generic point of an elliptic curve and the absolute Galois group of its function field

Let `E / k` be an elliptic curve over an arbitrary field `k`, with function field
`k(E) = k(x, y)` (`E.toAffine.FunctionField`). This file fixes the ambient data in which the
étale fundamental groups of the model orbicurves attached to `E` are computed:

* `Ω = Ω(E)`: an algebraic closure of `k(E)`;
* `genericPoint E ∈ E(Ω)`: the generic point `G = (x, y)` of `E`;
* `baseField E ⊆ Ω`: the perfect closure `P` of `k(x)` in `Ω` (so `Ω / P` is Galois: `P` is
  perfect and `Ω` is algebraically closed and algebraic over `P`); in characteristic `0`,
  `P = k(x)`. Every automorphism of `Ω` over a subfield containing `k(x)` fixes `P`;
* `Gal E = Gal(Ω / P)`, a profinite group, and its action `act σ : E(Ω) → E(Ω)` on points.

The subfields `k(x) ⊆ k(E) ⊆ Ω` are the function fields of `(E ∖ {0}) / {±1} = A¹_x` and of
`E ∖ {0}`; the automorphism groups `Aut(Ω / L)` of the function fields `L ⊇ k(x)` of the model
orbicurves are subgroups of `Gal E` (`Iut.Anabelian.Genuine.Pi1`).
-/

namespace Iut.Anabelian.Genuine

universe u

open WeierstrassCurve Polynomial
open scoped Classical

noncomputable section

variable {k : Type u} [Field k] (E : WeierstrassCurve k)

/-- **An algebraic closure `Ω` of the function field `k(E)`**. -/
abbrev Ω : Type u := AlgebraicClosure E.toAffine.FunctionField

/-- The class of `x` in the function field `k(E)`. -/
def xF : E.toAffine.FunctionField :=
  algebraMap E.toAffine.CoordinateRing _ (Affine.CoordinateRing.mk E.toAffine (C X))

/-- The class of `y` in the function field `k(E)`. -/
def yF : E.toAffine.FunctionField :=
  algebraMap E.toAffine.CoordinateRing _ (Affine.CoordinateRing.mk E.toAffine X)

lemma equation_xF_yF : (E⁄E.toAffine.FunctionField).toAffine.Equation (xF E) (yF E) := by
  rw [Affine.equation_iff]
  have h : Affine.CoordinateRing.mk E.toAffine (X ^ 2 + C (C E.a₁ * X + C E.a₃) * X -
      C (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)) = 0 := AdjoinRoot.mk_self
  have hC : ∀ a : k, Affine.CoordinateRing.mk E.toAffine (C (C a)) =
      algebraMap k E.toAffine.CoordinateRing a := fun _ => rfl
  simp only [map_add, map_sub, map_mul, map_pow, hC] at h
  have := congrArg (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField) h
  simp only [map_add, map_sub, map_mul, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply] at this
  simp only [xF, yF, baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  linear_combination this

instance [E.IsElliptic] : (E⁄(Ω E)).IsElliptic := inferInstanceAs (E.map _).IsElliptic

/-- The `x`-coordinate of the generic point, in `Ω`. -/
def xG : Ω E := algebraMap E.toAffine.FunctionField (Ω E) (xF E)

/-- The `y`-coordinate of the generic point, in `Ω`. -/
def yG : Ω E := algebraMap E.toAffine.FunctionField (Ω E) (yF E)

lemma nonsingular_generic [E.IsElliptic] : (E⁄(Ω E)).toAffine.Nonsingular (xG E) (yG E) := by
  rw [← Affine.equation_iff_nonsingular]
  exact (equation_xF_yF E).baseChange (IsScalarTower.toAlgHom k E.toAffine.FunctionField (Ω E))

/-- **The generic point** `G = (x, y) ∈ E(Ω)`. -/
def genericPoint [E.IsElliptic] : (E⁄(Ω E)).toAffine.Point :=
  Affine.Point.some (xG E) (yG E) (nonsingular_generic E)

/-- The subfield `k(x) ⊆ Ω`: the function field of the `x`-line. -/
def xLine : IntermediateField k (Ω E) := IntermediateField.adjoin k {xG E}

/-- **The base field** `P`: the perfect closure of `k(x)` in `Ω` (equal to `k(x)` in
characteristic `0`). -/
def baseField : IntermediateField k (Ω E) :=
  (perfectClosure (xLine E) (Ω E)).restrictScalars k

instance : PerfectField (baseField E) :=
  inferInstanceAs (PerfectField (perfectClosure (xLine E) (Ω E)))


/-- The embedding `k(E) → Ω`. -/
abbrev ιF : E.toAffine.FunctionField →ₐ[k] Ω E := IsScalarTower.toAlgHom k _ _

lemma xG_eq : xG E = ιF E (xF E) := rfl

lemma yG_eq : yG E = ιF E (yF E) := rfl

/-- The subfield `k(x, y) = k(E) ⊆ Ω`, over `k(x)`. -/
def fnField : IntermediateField (xLine E) (Ω E) := IntermediateField.adjoin (xLine E) {yG E}

lemma xG_mem_xLine : xG E ∈ xLine E := IntermediateField.subset_adjoin k _ (Set.mem_singleton _)

lemma xG_mem_fnField : xG E ∈ fnField E :=
  (fnField E).algebraMap_mem ⟨xG E, xG_mem_xLine E⟩

lemma yG_mem_fnField : yG E ∈ fnField E :=
  IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)

lemma algebraMap_mem_fnField (c : k) : algebraMap k (Ω E) c ∈ fnField E := by
  have : algebraMap k (Ω E) c ∈ xLine E := (xLine E).algebraMap_mem c
  exact (fnField E).algebraMap_mem ⟨_, this⟩

lemma coordRing_mem_fnField (a : E.toAffine.CoordinateRing) :
    ιF E (algebraMap _ E.toAffine.FunctionField a) ∈ fnField E := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  induction p using Polynomial.induction_on with
  | C q =>
    induction q using Polynomial.induction_on with
    | C c =>
      have : ιF E (algebraMap _ E.toAffine.FunctionField
          (AdjoinRoot.mk E.toAffine.polynomial (C (C c)))) = algebraMap k (Ω E) c := by
        change ιF E (algebraMap _ _ (algebraMap k E.toAffine.CoordinateRing c)) = _
        rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
      rw [this]; exact algebraMap_mem_fnField E c
    | add q r hq hr => simpa only [C_add, map_add] using add_mem hq hr
    | monomial n c hc =>
      rw [pow_succ, ← mul_assoc, C_mul, map_mul, map_mul, map_mul]
      exact mul_mem hc (xG_mem_fnField E)
  | add p q hp hq => simpa only [map_add] using add_mem hp hq
  | monomial n q hq =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul, map_mul]
    exact mul_mem hq (yG_mem_fnField E)

lemma ιF_mem_fnField (f : E.toAffine.FunctionField) : ιF E f ∈ fnField E := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := E.toAffine.CoordinateRing) f
  rw [map_div₀]
  exact div_mem (coordRing_mem_fnField E a) (coordRing_mem_fnField E b)

lemma isIntegral_yG : IsIntegral (xLine E) (yG E) := by
  have h := equation_xF_yF E
  rw [Affine.equation_iff] at h
  have h' := congrArg (ιF E) h
  simp only [map_add, map_mul, map_pow, baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    AlgHom.commutes] at h'
  let xx : xLine E := ⟨xG E, xG_mem_xLine E⟩
  let b : xLine E := algebraMap k (xLine E) E.a₁ * xx + algebraMap k (xLine E) E.a₃
  let c : xLine E := xx ^ 3 + algebraMap k (xLine E) E.a₂ * xx ^ 2 +
    algebraMap k (xLine E) E.a₄ * xx + algebraMap k (xLine E) E.a₆
  refine ⟨X ^ 2 + (C b * X - C c), monic_X_pow_add ?_, ?_⟩
  · refine (degree_sub_le _ _).trans_lt ?_
    refine max_lt ((degree_C_mul_X_le _).trans_lt (by norm_num)) ?_
    exact degree_C_le.trans_lt (by norm_num)
  · simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X, b, c, xx]
    change ιF E (yF E) ^ 2 + ((algebraMap k (Ω E) E.a₁ * ιF E (xF E) + algebraMap k (Ω E) E.a₃) *
      ιF E (yF E) - (ιF E (xF E) ^ 3 + algebraMap k (Ω E) E.a₂ * ιF E (xF E) ^ 2 +
      algebraMap k (Ω E) E.a₄ * ιF E (xF E) + algebraMap k (Ω E) E.a₆)) = 0
    linear_combination h'

lemma xG_mem_baseField : xG E ∈ baseField E := by
  change xG E ∈ perfectClosure (xLine E) (Ω E)
  exact (perfectClosure (xLine E) (Ω E)).algebraMap_mem
    ⟨xG E, IntermediateField.subset_adjoin k _ (Set.mem_singleton _)⟩


instance isAlgebraic_xLine : Algebra.IsAlgebraic (xLine E) (Ω E) := by
  haveI : Algebra.IsAlgebraic (xLine E) (fnField E) :=
    IntermediateField.isAlgebraic_adjoin_simple (isIntegral_yG E)
  letI : Algebra E.toAffine.FunctionField (fnField E) :=
    (RingHom.codRestrict (ιF E).toRingHom (fnField E) (ιF_mem_fnField E)).toAlgebra
  haveI : IsScalarTower E.toAffine.FunctionField (fnField E) (Ω E) :=
    .of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsAlgebraic (fnField E) (Ω E) := ⟨fun z =>
    (Algebra.IsAlgebraic.isAlgebraic (R := E.toAffine.FunctionField) z).extendScalars
      (fun a b h => (ιF E).injective (congrArg Subtype.val h))⟩
  exact Algebra.IsAlgebraic.trans (xLine E) (fnField E) (Ω E)

instance : Algebra.IsAlgebraic (baseField E) (Ω E) :=
  inferInstanceAs (Algebra.IsAlgebraic (perfectClosure (xLine E) (Ω E)) (Ω E))

instance : IsAlgClosure (baseField E) (Ω E) := ⟨inferInstance, inferInstance⟩

instance : IsGalois (baseField E) (Ω E) where
  to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField
  to_normal := inferInstance

/-- **The Galois group** `Gal(Ω / P)`: `P` is the perfect closure of `k(x)`, so `Gal(Ω / P)` is
the group of automorphisms of `Ω` over `k(x)`. -/
abbrev Gal : Type u := Ω E ≃ₐ[baseField E] Ω E

/-- An automorphism in `Gal(Ω / P)`, as a `k`-algebra map. -/
def σk (σ : Gal E) : Ω E →ₐ[k] Ω E := σ.toAlgHom.restrictScalars k

@[simp] lemma σk_apply (σ : Gal E) (a : Ω E) : σk E σ a = σ a := rfl

/-- The action of `Gal(Ω / P)` on the points `E(Ω)`. -/
def act (σ : Gal E) : (E⁄(Ω E)).toAffine.Point →+ (E⁄(Ω E)).toAffine.Point :=
  Affine.Point.map (W' := E) (S := k) (σk E σ)

lemma act_some (σ : Gal E) {x y : Ω E} (h : (E⁄(Ω E)).toAffine.Nonsingular x y)
    (h' : (E⁄(Ω E)).toAffine.Nonsingular (σ x) (σ y)) :
    act E σ (Affine.Point.some x y h) = Affine.Point.some (σ x) (σ y) h' := rfl

lemma act_mul (σ τ : Gal E) (Q : (E⁄(Ω E)).toAffine.Point) :
    act E (σ * τ) Q = act E σ (act E τ Q) := by
  cases Q <;> rfl

lemma act_one (Q : (E⁄(Ω E)).toAffine.Point) : act E 1 Q = Q := by
  cases Q <;> rfl

/-- A `k`-rational point of `E`, as a point of `E(Ω)`. -/
abbrev base : E.toAffine.Point →+ (E⁄(Ω E)).toAffine.Point := pointMap E (algebraMap k (Ω E))

lemma act_base (σ : Gal E) (T : E.toAffine.Point) : act E σ (base E T) = base E T := by
  rcases T with _ | ⟨x, y, h⟩
  · rfl
  · change Affine.Point.some _ _ _ = Affine.Point.some _ _ _
    congr 1
    · exact σ.commutes' ⟨_, (baseField E).algebraMap_mem x⟩
    · exact σ.commutes' ⟨_, (baseField E).algebraMap_mem y⟩

end

end Iut.Anabelian.Genuine
