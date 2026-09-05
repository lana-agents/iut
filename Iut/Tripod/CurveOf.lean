/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.Basic
import Iut.Tripod.Legendre
import Iut.Concrete.Existence

/-!
# The elliptic curve of a point of the tripod

To a point `λ ∈ ℚ̄ ∖ {0, 1}` of the tripod we attach the Legendre curve
`E_λ : y² = x(x − 1)(x − λ)` over its field of definition

  `F_λ := ℚ(λ, √−1, √λ, √(1 − λ), E_λ[3], E_λ[5]) ⊆ ℚ̄`

(`Iut.Tripod.fieldOf'`; the field `F = F_tpd(√−1, E[3·5])` of (E3) in the proof of IUT IV,
Theorem 1.10 and of [GenEll], Theorem 2.1, with `F_tpd = ℚ(λ)`, enlarged by `√λ`,
`√(1 − λ)` so as to be Galois over `ℚ(j)`; see the docstring of `fieldOf'`), generated over
`ℚ` by `λ`, chosen square roots of `−1`, `λ`, `1 − λ`, and the coordinates of the `3`- and
`5`-torsion points of `E_λ(ℚ̄)` (`Iut.Tripod.torsionCoords`). Under the hypothesis that the
`3`- and `5`-torsion of `E_λ(ℚ̄)` is finite (`Iut.Tripod.TorsionFinite`; it follows from
`E_λ[n](ℚ̄) ≅ (ℤ/n)²`, the hypothesis consumed by `Iut.EllipticCurveData.modEllRepData`),
`F_λ` is a number field, and `Iut.Tripod.curveOf` packages `E_λ/F_λ` with the algebraic
closure `ℚ̄` as an `Iut.EllipticCurveData`.
-/

namespace Iut.Tripod

open WeierstrassCurve NumberField

open scoped IntermediateField

/-! ### A square root of `−1` -/

/-- A chosen square root of `−1` in `ℚ̄`. -/
noncomputable def sqrtNegOne : Qbar :=
  (IsAlgClosed.exists_pow_nat_eq (-1 : Qbar) two_pos).choose

theorem sqrtNegOne_sq : sqrtNegOne ^ 2 = -1 :=
  (IsAlgClosed.exists_pow_nat_eq (-1 : Qbar) two_pos).choose_spec

/-- A chosen square root of `λ` in `ℚ̄`. -/
noncomputable def sqrtLam (l : Qbar) : Qbar := (IsAlgClosed.exists_pow_nat_eq l two_pos).choose

theorem sqrtLam_sq (l : Qbar) : sqrtLam l ^ 2 = l :=
  (IsAlgClosed.exists_pow_nat_eq l two_pos).choose_spec

/-- A chosen square root of `1 − λ` in `ℚ̄`. -/
noncomputable def sqrtOneSubLam (l : Qbar) : Qbar :=
  (IsAlgClosed.exists_pow_nat_eq (1 - l) two_pos).choose

theorem sqrtOneSubLam_sq (l : Qbar) : sqrtOneSubLam l ^ 2 = 1 - l :=
  (IsAlgClosed.exists_pow_nat_eq (1 - l) two_pos).choose_spec

/-! ### The torsion coordinates -/

/-- The set of affine coordinates of a point of `E_λ(ℚ̄)`: `∅` for the origin, `{x, y}` for an
affine point `(x, y)`. -/
def coords {l : Qbar} : (legendre l).toAffine.Point → Set Qbar
  | 0 => ∅
  | Affine.Point.some x y _ => {x, y}

@[simp] theorem coords_zero (l : Qbar) : coords (0 : (legendre l).toAffine.Point) = ∅ := rfl

@[simp] theorem coords_some {l x y : Qbar} (h : (legendre l).toAffine.Nonsingular x y) :
    coords (Affine.Point.some x y h) = {x, y} := rfl

open scoped Classical in
/-- The `n`-torsion points of `E_λ(ℚ̄)`. -/
def torsionSet (l : Qbar) (n : ℕ) : Set (legendre l).toAffine.Point := {P | n • P = 0}

/-- **Finiteness of the `n`-torsion** of `E_λ(ℚ̄)`: the hypothesis of the construction of
the field of definition. It follows from `E_λ[n](ℚ̄) ≅ (ℤ/n)²` (the hypothesis
`Nonempty (torsionBy … ≃+ (Fin 2 → ZMod n))` of `Iut.EllipticCurveData.modEllRepData`). -/
def TorsionFinite (l : Qbar) (n : ℕ) : Prop := (torsionSet l n).Finite

open scoped Classical in
/-- **`TorsionFinite l n` from a basis `E_λ[n](ℚ̄) ≅ (ℤ/n)²`**: the hypothesis of
`Iut.EllipticCurveData.modEllRepData` (for the curve `curveOf x h3 h5`, whose points over
`ℚ̄` are definitionally those of `E_λ` over `ℚ̄`) implies the finiteness of the
`n`-torsion. -/
theorem torsionFinite_of_equiv {l : Qbar} {n : ℕ} [NeZero n]
    (h : Nonempty (AddSubgroup.torsionBy (legendre l).toAffine.Point n ≃+ (Fin 2 → ZMod n))) :
    TorsionFinite l n := by
  have hset : torsionSet l n =
      (AddSubgroup.torsionBy (legendre l).toAffine.Point n : Set (legendre l).toAffine.Point) := by
    ext P
    simp only [torsionSet, Set.mem_setOf_eq, SetLike.mem_coe]
    rw [AddSubgroup.torsionBy, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff,
      natCast_zsmul]
  rw [TorsionFinite, hset]
  haveI : Finite (AddSubgroup.torsionBy (legendre l).toAffine.Point n) :=
    Finite.of_equiv _ h.some.symm.toEquiv
  exact Set.toFinite _

/-- The coordinates of the `n`-torsion points of `E_λ(ℚ̄)`. -/
def torsionCoords (l : Qbar) (n : ℕ) : Set Qbar := ⋃ P ∈ torsionSet l n, coords P

theorem torsionCoords_finite {l : Qbar} {n : ℕ} (h : TorsionFinite l n) :
    (torsionCoords l n).Finite :=
  h.biUnion fun P _ ↦ by
    cases P with
    | zero => exact Set.finite_empty
    | some x y _ => exact (Set.finite_singleton y).insert x

open scoped Classical in
theorem mem_torsionCoords {l : Qbar} {n : ℕ} {P : (legendre l).toAffine.Point}
    (hP : n • P = 0) {c : Qbar} (hc : c ∈ coords P) : c ∈ torsionCoords l n :=
  Set.mem_biUnion (x := P) hP hc

/-! ### The field of definition -/

/-- **The field of definition** `F_λ = ℚ(λ, √−1, √λ, √(1 − λ), E_λ[3], E_λ[5]) ⊆ ℚ̄` of the
Legendre curve of `λ`.

The square roots `√λ`, `√(1 − λ)` are adjoined so that `F_λ` is (plausibly) Galois over the
field of moduli `ℚ(j)`, as required by `Iut.IsGaloisOfDegreePrimeTo`: over `ℚ(j)` the
conjugates of `λ` are the six values `λ, 1 − λ, 1/λ, 1/(1 − λ), λ/(λ − 1), (λ − 1)/λ`;
`E_{1−λ} ≅ E_λ` over `ℚ(λ)`, while `E_{1/λ}` and `E_{1/(1−λ)}` are the quadratic twists of
`E_λ` by `λ` and by `1 − λ`, so `ℚ(λ, √−1, √λ, √(1 − λ), E_λ[15])` contains the `15`-torsion
fields of all the conjugate curves and is Galois over `ℚ(j)`. -/
noncomputable def fieldOf' (l : Qbar) : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ
    ({l, sqrtNegOne, sqrtLam l, sqrtOneSubLam l} ∪ torsionCoords l 3 ∪ torsionCoords l 5)

theorem mem_fieldOf'_self (l : Qbar) : l ∈ fieldOf' l :=
  IntermediateField.subset_adjoin _ _ (Or.inl (Or.inl (by simp)))

theorem sqrtNegOne_mem_fieldOf' (l : Qbar) : sqrtNegOne ∈ fieldOf' l :=
  IntermediateField.subset_adjoin _ _ (Or.inl (Or.inl (by simp)))

theorem sqrtLam_mem_fieldOf' (l : Qbar) : sqrtLam l ∈ fieldOf' l :=
  IntermediateField.subset_adjoin _ _ (Or.inl (Or.inl (by simp)))

theorem sqrtOneSubLam_mem_fieldOf' (l : Qbar) : sqrtOneSubLam l ∈ fieldOf' l :=
  IntermediateField.subset_adjoin _ _ (Or.inl (Or.inl (by simp)))

theorem torsionCoords_three_subset_fieldOf' (l : Qbar) :
    torsionCoords l 3 ⊆ fieldOf' l :=
  fun _ hc ↦ IntermediateField.subset_adjoin _ _ (Or.inl (Or.inr hc))

theorem torsionCoords_five_subset_fieldOf' (l : Qbar) :
    torsionCoords l 5 ⊆ fieldOf' l :=
  fun _ hc ↦ IntermediateField.subset_adjoin _ _ (Or.inr hc)

/-- `ℚ(λ) ⊆ F_λ`. -/
theorem fieldOf_le_fieldOf' (l : Qbar) : fieldOf l ≤ fieldOf' l :=
  IntermediateField.adjoin_simple_le_iff.mpr (mem_fieldOf'_self l)

/-- `F_λ` is a finite extension of `ℚ` when the `3`- and `5`-torsion of `E_λ(ℚ̄)` are
finite. -/
theorem finiteDimensional_fieldOf' {l : Qbar} (h3 : TorsionFinite l 3) (h5 : TorsionFinite l 5) :
    FiniteDimensional ℚ (fieldOf' l) := by
  have hfin : ({l, sqrtNegOne, sqrtLam l, sqrtOneSubLam l} ∪ torsionCoords l 3 ∪
      torsionCoords l 5).Finite :=
    ((Set.toFinite _).union (torsionCoords_finite h3)).union (torsionCoords_finite h5)
  haveI := hfin.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ ↦ isIntegral x

/-- The element `λ` of `F_λ`. -/
noncomputable def gen' (l : Qbar) : fieldOf' l := ⟨l, mem_fieldOf'_self l⟩

@[simp] theorem coe_gen' (l : Qbar) : (gen' l : Qbar) = l := rfl

/-- `√−1` as an element of `F_λ`. -/
noncomputable def sqrtNegOne' (l : Qbar) : fieldOf' l := ⟨sqrtNegOne, sqrtNegOne_mem_fieldOf' l⟩

theorem sqrtNegOne'_sq (l : Qbar) : sqrtNegOne' l ^ 2 = -1 := by
  apply Subtype.ext
  simpa [sqrtNegOne'] using sqrtNegOne_sq

/-- `√λ` as an element of `F_λ`. -/
noncomputable def sqrtLam' (l : Qbar) : fieldOf' l := ⟨sqrtLam l, sqrtLam_mem_fieldOf' l⟩

theorem sqrtLam'_sq (l : Qbar) : sqrtLam' l ^ 2 = gen' l := by
  apply Subtype.ext
  simpa [sqrtLam'] using sqrtLam_sq l

/-- `√(1 − λ)` as an element of `F_λ`. -/
noncomputable def sqrtOneSubLam' (l : Qbar) : fieldOf' l :=
  ⟨sqrtOneSubLam l, sqrtOneSubLam_mem_fieldOf' l⟩

theorem sqrtOneSubLam'_sq (l : Qbar) : sqrtOneSubLam' l ^ 2 = 1 - gen' l := by
  apply Subtype.ext
  simpa [sqrtOneSubLam'] using sqrtOneSubLam_sq l

theorem gen'_ne_zero {l : Qbar} (hl : l ≠ 0) : gen' l ≠ 0 := by
  intro h
  exact hl (congrArg Subtype.val h)

theorem gen'_ne_one {l : Qbar} (hl : l ≠ 1) : gen' l ≠ 1 := by
  intro h
  exact hl (congrArg Subtype.val h)

/-- `ℚ̄` is torsion-free over every intermediate field `F ⊆ ℚ̄` (an explicit instance, since
the generic search times out). -/
instance (F : IntermediateField ℚ Qbar) : Module.IsTorsionFree F Qbar :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap F Qbar).injective

/-- `ℚ̄` is an algebraic closure of every intermediate field `F ⊆ ℚ̄`. -/
instance (F : IntermediateField ℚ Qbar) : IsAlgClosure F Qbar := by
  haveI : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  exact (isAlgClosure_iff F Qbar).mpr ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩

/-- The Legendre curve of `λ` over `F_λ` is elliptic. -/
theorem legendre_gen'_isElliptic (x : Pt) : (legendre (gen' x.1)).IsElliptic :=
  legendre_isElliptic (gen'_ne_zero x.2.1) (gen'_ne_one x.2.2)

/-! ### The curve of a point -/

/-- **The elliptic curve of a point `λ` of the tripod**: the Legendre curve `E_λ` over its
field of definition `F_λ = ℚ(λ, √−1, √λ, √(1 − λ), E_λ[3], E_λ[5])`, with the algebraic
closure `ℚ̄`. -/
noncomputable def curveOf (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    EllipticCurveData :=
  letI := finiteDimensional_fieldOf' h3 h5
  { F := fieldOf' x.1
    Fbar := Qbar
    E := legendre (gen' x.1)
    isElliptic := legendre_gen'_isElliptic x }

variable (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)

theorem curveOf_F : (curveOf x h3 h5).F = fieldOf' x.1 := rfl
theorem curveOf_Fbar : (curveOf x h3 h5).Fbar = Qbar := rfl
theorem curveOf_E : (curveOf x h3 h5).E = legendre (gen' x.1) := rfl

/-- The base change of the curve of `x` to `ℚ̄` is the Legendre curve of `λ` over `ℚ̄`
(definitionally). -/
theorem curveOf_E_baseChange :
    Affine.baseChange (curveOf x h3 h5).E (curveOf x h3 h5).Fbar = legendre x.1 := rfl

end Iut.Tripod
