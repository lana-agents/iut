/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.Existence
import Iut.Concrete.CurveArithmeticProved

/-!
# The ℓ-torsion field of a mod-`ℓ` representation and its Tate family

For an elliptic curve `E/F` (`Iut.EllipticCurveData`) with mod-`ℓ` representation data
`R : C.ModEllRepData ℓ` (a basis of `E(F̄)[ℓ]` and the representation `ρ` computing the Galois
action in it), the torsion field `K = F̄^{ker ρ}` (`ModEllRepData.torsionField`) has:

* `E(K)[ℓ] ≃ E(F̄)[ℓ]` (`ModEllRepData.torsionEquivR`): the ℓ-torsion is rational over `K`, so
  `E(K)[ℓ]` has `ℓ²` elements (`card_TKR`);
* `K/F` is Galois (`ModEllRepData.isGalois_torsionField`), and the restriction
  `Gal(F̄/F) → Gal(K/F)` (`restrictKR`) is surjective and intertwines the actions on `E(F̄)` and
  `E(K)` (`bcKR_galK`);
* **the action of `Gal(K/F)` on `E(K)[ℓ]` is faithful** (`eq_one_of_forall_galK_eq`): an
  automorphism fixing the ℓ-torsion pointwise lies in the image of `ker ρ`, hence is trivial.

This is the analogue, for the representation data of a curve, of `Iut.AdmissiblePrimeData`'s
torsion theory (`Iut.Anabelian.Torsion`), which assumes in addition that the image of `ρ`
contains `SL₂(𝔽_ℓ)` — an assumption that fails exactly in the situation of [GenEll], Lemma 3.5
(an `ℓ`-cyclic subgroup), for which this file is written.

The file also records the Tate family of `E` over `K` at the places of `K` over the set
`EllipticCurveData.VBadOdd` of places of `F_mod` of **odd** residue characteristic over which
`E` has multiplicative reduction (`ModEllRepData.tateFamilyOdd`, from
`Iut.tateFamilyOfTorsion`), and that every multiplicative place of `F` of odd residue
characteristic lies over a place of `VBadOdd` (`exists_mem_VBadOdd`).
-/

namespace Iut.EllipticCurveData

open WeierstrassCurve NumberField Iut
open scoped Classical

universe u

noncomputable section

variable (C : EllipticCurveData.{u})

/-! ### The odd multiplicative places -/

/-- The places of `F_mod` of odd residue characteristic over which `E` has multiplicative
reduction (at every place of `F` above, and there is one): `VBadOf ℓ` without the condition
`p ≠ ℓ`. -/
def VBadOdd : Set (FinitePlace ↥(fieldOfModuli C.F C.E)) :=
  {v | residueChar v ≠ 2 ∧ (∃ w : FinitePlace C.F, FinitePlace.LiesOver w v) ∧
    ∀ w : FinitePlace C.F, FinitePlace.LiesOver w v → HasMultiplicativeReductionAt C.E w}

/-- Every multiplicative place of `F` of odd residue characteristic lies over a place of
`VBadOdd`. -/
lemma exists_mem_VBadOdd (CA : C.CurveArithmetic) {w : FinitePlace C.F} (hw : w ∈ C.badAll)
    (h2 : residueChar w ≠ 2) : ∃ v ∈ C.VBadOdd, FinitePlace.LiesOver w v := by
  obtain ⟨v, hwv⟩ := CA.exists_liesOver w
  have hv2 : residueChar v ≠ 2 := by rwa [← CA.residueChar_liesOver v w hwv]
  exact ⟨v, ⟨hv2, ⟨w, hwv⟩, fun w' hw' => CA.mult_invariant v hv2 w w' hwv hw' hw⟩, hwv⟩

/-- The place of `F` below a place of `K` over `VBadOdd` is multiplicative. -/
lemma placeUnder_mem_badAll_of_isBadPlace {Fbar : Type u} [Field Fbar] [Algebra C.F Fbar]
    [IsAlgClosure C.F Fbar] (K : IntermediateField C.F Fbar) [NumberField ↥K]
    {w : FinitePlace ↥K} (hw : IsBadPlace C.E K C.VBadOdd w) :
    (placeUnder w : FinitePlace C.F) ∈ C.badAll :=
  mult_placeUnder C.E K (fun _ hv w hwv => hv.2.2 w hwv) hw

/-- The place of `F` below a place of `K` lies over the place of `F_mod` below. -/
lemma placeUnder_liesOver_of_liesOver {Fbar : Type u} [Field Fbar] [Algebra C.F Fbar]
    (K : IntermediateField C.F Fbar) [NumberField ↥K] {w : FinitePlace ↥K}
    {v : FinitePlace ↥(fieldOfModuli C.F C.E)} (hwv : FinitePlace.LiesOver w v) :
    FinitePlace.LiesOver (placeUnder w : FinitePlace C.F) v := by
  refine ⟨?_⟩
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  rw [hwv.over, placeUnder_maximalIdeal, Ideal.under_def, Ideal.under_def, Ideal.comap_comap,
    ← IsScalarTower.algebraMap_eq]

/-- The place of `F` below a place of `K` over `VBadOdd` has odd residue characteristic. -/
lemma residueChar_placeUnder_ne_two_of_isBadPlace {Fbar : Type u} [Field Fbar]
    [Algebra C.F Fbar] (K : IntermediateField C.F Fbar) [NumberField ↥K]
    {w : FinitePlace ↥K} (hw : IsBadPlace C.E K C.VBadOdd w) :
    residueChar (placeUnder w : FinitePlace C.F) ≠ 2 := by
  obtain ⟨v, hv, hwv⟩ := hw
  rw [residueChar_eq_of_liesOver_place (C.placeUnder_liesOver_of_liesOver K hwv)]
  exact hv.1

namespace ModEllRepData

variable {C} {ℓ : ℕ} (R : C.ModEllRepData ℓ)

/-- The classical decidable equality on `K`, as used by the Tate families. -/
local instance (priority := 1100) instDecidableEqTorsionFieldR : DecidableEq ↥R.torsionField :=
  fun a b => Classical.propDecidable (a = b)

/-! ### The ℓ-torsion over the torsion field -/

/-- The base change of points `E(K) → E(F̄)`. -/
noncomputable def bcKR : (curveK C.E R.torsionField).toAffine.Point →+
    Affine.Point (Affine.baseChange C.E C.Fbar) :=
  Affine.Point.map (W' := C.E) (S := C.F) (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar)

lemma bcKR_injective : Function.Injective R.bcKR :=
  Affine.Point.map_injective (W' := C.E) (S := C.F)
    (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar)

/-- The ℓ-torsion of `E(K)`. -/
abbrev TKR : AddSubgroup (curveK C.E R.torsionField).toAffine.Point :=
  AddSubgroup.torsionBy (curveK C.E R.torsionField).toAffine.Point ℓ

/-- The ℓ-torsion of `E(F̄)` (with the representation data as an argument, for field
notation). -/
abbrev TFbarR (_R : C.ModEllRepData ℓ) :
    AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar)) :=
  AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ

/-- Elements of the kernel of the mod-ℓ representation fix the ℓ-torsion. -/
lemma galPointMap_eq_of_mem_ker {σ : C.Fbar ≃ₐ[C.F] C.Fbar} (hσ : σ ∈ R.rep.ker)
    (Q : ↥R.TFbarR) : galPointMap C.F C.E C.Fbar σ Q.1 = Q.1 := by
  have h := R.rep_spec σ Q
  rw [MonoidHom.mem_ker.mp hσ] at h
  simp only [Units.val_one, Matrix.one_mulVec] at h
  exact congrArg Subtype.val (R.torsionBasis.injective h)

/-- Every ℓ-torsion point of `E(F̄)` comes from `E(K)`. -/
lemma exists_bcKR_eq (Q : Affine.Point (Affine.baseChange C.E C.Fbar)) (hQ : Q ∈ R.TFbarR) :
    ∃ P : (curveK C.E R.torsionField).toAffine.Point, R.bcKR P = Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  · have hfix : ∀ σ ∈ R.rep.ker, σ x = x ∧ σ y = y := by
      intro σ hσ
      have h' := R.galPointMap_eq_of_mem_ker hσ ⟨_, hQ⟩
      simp only [galPointMap, Affine.Point.map_some] at h'
      exact Affine.Point.some.inj h'
    have hx : x ∈ R.torsionField := by
      rw [ModEllRepData.torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).1
    have hy : y ∈ R.torsionField := by
      rw [ModEllRepData.torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).2
    have hns : (Affine.baseChange C.E ↥R.torsionField).Nonsingular
        (⟨x, hx⟩ : ↥R.torsionField) ⟨y, hy⟩ :=
      (Affine.baseChange_nonsingular (W := C.E)
        (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar).injective _ _).mp h
    exact ⟨.some _ _ hns, rfl⟩

lemma bcKR_mem_TFbarR {P : (curveK C.E R.torsionField).toAffine.Point} (hP : P ∈ R.TKR) :
    R.bcKR P ∈ R.TFbarR := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

lemma mem_TKR_of_bcKR {P : (curveK C.E R.torsionField).toAffine.Point}
    (hP : R.bcKR P ∈ R.TFbarR) : P ∈ R.TKR := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul] at hP
  exact R.bcKR_injective (hP.trans (map_zero _).symm)

/-- **The ℓ-torsion is rational over `K`**: `E(K)[ℓ] ≃ E(F̄)[ℓ]`. -/
noncomputable def torsionEquivR : ↥R.TKR ≃+ ↥R.TFbarR :=
  AddEquiv.ofBijective (R.bcKR.restrict R.TKR |>.codRestrict _ fun P => R.bcKR_mem_TFbarR P.2)
    ⟨fun P P' h => Subtype.ext (R.bcKR_injective (congrArg Subtype.val h)),
     fun Q => by
      obtain ⟨P, hP⟩ := R.exists_bcKR_eq Q.1 Q.2
      exact ⟨⟨P, R.mem_TKR_of_bcKR (hP ▸ Q.2)⟩, Subtype.ext hP⟩⟩

@[simp] lemma coe_torsionEquivR (P : ↥R.TKR) :
    (R.torsionEquivR P : Affine.Point _) = R.bcKR P := rfl

/-- `E(K)[ℓ]` has `ℓ²` elements. -/
lemma card_TKR : Nat.card R.TKR = ℓ ^ 2 := by
  rw [Nat.card_congr (R.torsionEquivR.trans R.torsionBasis).toEquiv, Nat.card_pi, Nat.card_zmod]
  simp

/-! ### The Galois action on `E(K)` -/

/-- `K/F` is Galois (the fixed field of the normal subgroup `ker ρ`). -/
instance isGalois_torsionField : IsGalois C.F ↥R.torsionField :=
  IsGalois.of_fixedField_normal_subgroup R.rep.ker

/-- The restriction of `σ ∈ Gal(F̄/F)` to `K`. -/
noncomputable def restrictKR (σ : C.Fbar ≃ₐ[C.F] C.Fbar) :
    ↥R.torsionField ≃ₐ[C.F] ↥R.torsionField :=
  AlgEquiv.restrictNormalHom R.torsionField σ

lemma restrictKR_surjective : Function.Surjective R.restrictKR :=
  AlgEquiv.restrictNormalHom_surjective (F := C.F) (K₁ := ↥R.torsionField) C.Fbar

lemma map_map_restrictKR (σ : C.Fbar ≃ₐ[C.F] C.Fbar)
    (P : (Affine.baseChange C.E ↥R.torsionField).Point) :
    Affine.Point.map (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar)
      (Affine.Point.map (W' := C.E) (S := C.F)
        (R.restrictKR σ : ↥R.torsionField →ₐ[C.F] ↥R.torsionField) P) =
      Affine.Point.map (W' := C.E) (S := C.F) σ.toAlgHom
        (Affine.Point.map (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar) P) := by
  rw [Affine.Point.map_map, Affine.Point.map_map]
  have h : (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar).comp
      (R.restrictKR σ : ↥R.torsionField →ₐ[C.F] ↥R.torsionField) =
      σ.toAlgHom.comp (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar) := by
    ext x
    exact AlgEquiv.restrictNormalHom_apply R.torsionField σ x
  rw [h]

/-- Base change to `F̄` intertwines the restricted action with the action of `σ`. -/
lemma bcKR_galK (σ : C.Fbar ≃ₐ[C.F] C.Fbar) (P : (curveK C.E R.torsionField).toAffine.Point) :
    R.bcKR (galK C.E R.torsionField (R.restrictKR σ) P) =
      galPointMap C.F C.E C.Fbar σ (R.bcKR P) :=
  R.map_map_restrictKR σ P

lemma galK_mem_TKR (σ : ↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)
    {P : (curveK C.E R.torsionField).toAffine.Point} (hP : P ∈ R.TKR) :
    galK C.E R.torsionField σ P ∈ R.TKR := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

/-- **The action of `Gal(K/F)` on `E(K)[ℓ]` is faithful**: an automorphism of `K/F` fixing
the ℓ-torsion pointwise is trivial (it is the restriction of an element of `ker ρ`, which
fixes `K = F̄^{ker ρ}`). -/
theorem eq_one_of_forall_galK_eq (σ : ↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)
    (h : ∀ P ∈ R.TKR, galK C.E R.torsionField σ P = P) : σ = 1 := by
  obtain ⟨τ, rfl⟩ := R.restrictKR_surjective σ
  have hfix : ∀ Q : ↥R.TFbarR, galPointMap C.F C.E C.Fbar τ Q.1 = Q.1 := by
    intro Q
    obtain ⟨P, hP⟩ := R.exists_bcKR_eq Q.1 Q.2
    rw [← hP, ← R.bcKR_galK, h P (R.mem_TKR_of_bcKR (hP ▸ Q.2))]
  have hrep : R.rep τ = 1 := by
    apply Units.ext
    rw [Units.val_one]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    obtain ⟨Q, rfl⟩ := R.torsionBasis.surjective v
    rw [Matrix.toLin'_apply, ← R.rep_spec τ Q, Matrix.toLin'_one, LinearMap.id_apply]
    congr 1
    exact Subtype.ext (hfix Q)
  refine AlgEquiv.ext fun x => ?_
  rw [AlgEquiv.one_apply]
  apply Subtype.ext
  rw [restrictKR, AlgEquiv.restrictNormalHom_apply]
  have hx : (x : C.Fbar) ∈ IntermediateField.fixedField R.rep.ker := x.2
  rw [IntermediateField.mem_fixedField_iff] at hx
  exact hx τ (MonoidHom.mem_ker.mpr hrep)

/-! ### The Tate family at the odd multiplicative places -/

/-- **The Tate family of `E` over `K` at the places over `VBadOdd`** (Tate's theorem at the
odd multiplicative places, from the rationality of the ℓ-torsion over `K`,
`Iut.tateFamilyOfTorsion`). -/
noncomputable def tateFamilyOdd (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) :
    TateFamily C.E R.torsionField ℓ C.VBadOdd :=
  tateFamilyOfTorsion C.E R.torsionField ℓ (fun _ hv => hv.1) (fun _ hv w hwv => hv.2.2 w hwv)
    hℓ hodd R.TKR le_rfl (by rw [R.card_TKR, sq])

end ModEllRepData

end

end Iut.EllipticCurveData
