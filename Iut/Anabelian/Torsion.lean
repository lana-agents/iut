/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Model
import Iut.Cor312.ThetaData.LocalConditions

/-!
# The ℓ-torsion over the torsion field

For admissible prime data `P` (IUT I, Definition 3.1(b)–(c)) with torsion field
`K = F̄^{ker ρ}`, the ℓ-torsion of `E(F̄)` is rational over `K`: the base change
`E(K)[ℓ] → E(F̄)[ℓ]` is a bijection (`Iut.Anabelian.AdmissiblePrimeData.torsionEquiv`), so
that `E(K)[ℓ] ≃ 𝔽_ℓ²` through the chosen basis (`basisK`), `E(K)[ℓ]` has order `ℓ²`, and
the mod-ℓ representation computes the action of `Gal(K/F)` on `E(K)[ℓ]`
(`basisK_galK`).
-/

namespace Iut.AdmissiblePrimeData

universe u

open WeierstrassCurve NumberField Iut Iut.Anabelian
open scoped Classical

noncomputable section

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable (P : Iut.AdmissiblePrimeData F E Fbar VBad)

/-- The classical decidable equality on `K`, as used by the model orbicurves. -/
local instance (priority := high) instDecidableEqK : DecidableEq ↥P.torsionField :=
  fun a b => Classical.propDecidable (a = b)

/-- The curve `E` over the torsion field `K`. -/
abbrev EK : WeierstrassCurve ↥P.torsionField := E.map (algebraMap F ↥P.torsionField)

/-- The base change of points `E(K) → E(F̄)`. -/
def bcK : P.EK.toAffine.Point →+ Affine.Point (Affine.baseChange E Fbar) :=
  Affine.Point.map (W' := E) (S := F) (IsScalarTower.toAlgHom F ↥P.torsionField Fbar)

lemma bcK_injective : Function.Injective P.bcK :=
  Affine.Point.map_injective (W' := E) (S := F) (IsScalarTower.toAlgHom F ↥P.torsionField Fbar)

/-- The ℓ-torsion of `E(K)`. -/
abbrev TK : AddSubgroup P.EK.toAffine.Point := AddSubgroup.torsionBy P.EK.toAffine.Point P.ℓ

/-- The ℓ-torsion of `E(F̄)`. -/
abbrev TFbar : AddSubgroup (Affine.Point (Affine.baseChange E Fbar)) :=
  AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) P.ℓ

/-- Elements of the kernel of the mod-ℓ representation fix the ℓ-torsion. -/
lemma galPointMap_eq_of_mem_ker {σ : Fbar ≃ₐ[F] Fbar} (hσ : σ ∈ P.rep.ker) (Q : ↥P.TFbar) :
    galPointMap F E Fbar σ Q.1 = Q.1 := by
  have h := P.rep_spec σ Q
  rw [MonoidHom.mem_ker.mp hσ] at h
  simp only [Units.val_one, Matrix.one_mulVec] at h
  exact congrArg Subtype.val (P.torsionBasis.injective h)

/-- Every ℓ-torsion point of `E(F̄)` comes from `E(K)`. -/
lemma exists_bcK_eq (Q : Affine.Point (Affine.baseChange E Fbar)) (hQ : Q ∈ P.TFbar) :
    ∃ R : P.EK.toAffine.Point, P.bcK R = Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  · have hfix : ∀ σ ∈ P.rep.ker, σ x = x ∧ σ y = y := by
      intro σ hσ
      have h' := P.galPointMap_eq_of_mem_ker hσ ⟨_, hQ⟩
      simp only [galPointMap, Affine.Point.map_some] at h'
      exact Affine.Point.some.inj h'
    have hx : x ∈ P.torsionField := by
      rw [Iut.AdmissiblePrimeData.torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).1
    have hy : y ∈ P.torsionField := by
      rw [Iut.AdmissiblePrimeData.torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).2
    have hns : (Affine.baseChange E ↥P.torsionField).Nonsingular
        (⟨x, hx⟩ : ↥P.torsionField) ⟨y, hy⟩ :=
      (Affine.baseChange_nonsingular (W := E)
        (IsScalarTower.toAlgHom F ↥P.torsionField Fbar).injective _ _).mp h
    exact ⟨.some _ _ hns, rfl⟩

lemma bcK_mem_TFbar {R : P.EK.toAffine.Point} (hR : R ∈ P.TK) : P.bcK R ∈ P.TFbar := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hR ⊢
  rw [← map_nsmul, hR, map_zero]

lemma mem_TK_of_bcK {R : P.EK.toAffine.Point} (hR : P.bcK R ∈ P.TFbar) : R ∈ P.TK := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hR ⊢
  rw [← map_nsmul] at hR
  exact P.bcK_injective (hR.trans (map_zero _).symm)

/-- **The ℓ-torsion is rational over `K`**: `E(K)[ℓ] ≃ E(F̄)[ℓ]`. -/
def torsionEquiv : ↥P.TK ≃+ ↥P.TFbar :=
  AddEquiv.ofBijective (P.bcK.restrict P.TK |>.codRestrict _ fun R => P.bcK_mem_TFbar R.2)
    ⟨fun R R' h => Subtype.ext (P.bcK_injective (congrArg Subtype.val h)),
     fun Q => by
      obtain ⟨R, hR⟩ := P.exists_bcK_eq Q.1 Q.2
      exact ⟨⟨R, P.mem_TK_of_bcK (hR ▸ Q.2)⟩, Subtype.ext hR⟩⟩

@[simp] lemma coe_torsionEquiv (R : ↥P.TK) : (P.torsionEquiv R : Affine.Point _) = P.bcK R := rfl

/-- The chosen basis of `E(K)[ℓ] ≅ 𝔽_ℓ²`. -/
def basisK : ↥P.TK ≃+ (Fin 2 → ZMod P.ℓ) := P.torsionEquiv.trans P.torsionBasis

lemma card_TK : Nat.card P.TK = P.ℓ ^ 2 := by
  rw [Nat.card_congr P.basisK.toEquiv, Nat.card_pi, Nat.card_zmod]
  simp

/-! ### The Galois action on `E(K)` -/

/-- `K/F` is Galois (the fixed field of the normal subgroup `ker ρ`). -/
instance isGalois_torsionField : IsGalois F ↥P.torsionField :=
  IsGalois.of_fixedField_normal_subgroup P.rep.ker

/-- The action of `σ ∈ Gal(K/F)` on `E(K)`. -/
def galK (σ : ↥P.torsionField ≃ₐ[F] ↥P.torsionField) :
    P.EK.toAffine.Point →+ P.EK.toAffine.Point :=
  Affine.Point.map (W' := E) (S := F) (σ : ↥P.torsionField →ₐ[F] ↥P.torsionField)

/-- The restriction of `σ ∈ Gal(F̄/F)` to `K`. -/
def restrictK (σ : Fbar ≃ₐ[F] Fbar) : ↥P.torsionField ≃ₐ[F] ↥P.torsionField :=
  AlgEquiv.restrictNormalHom P.torsionField σ

lemma map_map_restrictK (σ : Fbar ≃ₐ[F] Fbar)
    (R : (Affine.baseChange E ↥P.torsionField).Point) :
    Affine.Point.map (IsScalarTower.toAlgHom F ↥P.torsionField Fbar)
      (Affine.Point.map (W' := E) (S := F)
        (P.restrictK σ : ↥P.torsionField →ₐ[F] ↥P.torsionField) R) =
      Affine.Point.map (W' := E) (S := F) σ.toAlgHom
        (Affine.Point.map (IsScalarTower.toAlgHom F ↥P.torsionField Fbar) R) := by
  rw [Affine.Point.map_map, Affine.Point.map_map]
  have h : (IsScalarTower.toAlgHom F ↥P.torsionField Fbar).comp
      (P.restrictK σ : ↥P.torsionField →ₐ[F] ↥P.torsionField) =
      σ.toAlgHom.comp (IsScalarTower.toAlgHom F ↥P.torsionField Fbar) := by
    ext x
    exact AlgEquiv.restrictNormalHom_apply P.torsionField σ x
  rw [h]

/-- Base change to `F̄` intertwines the restricted action with the action of `σ`. -/
lemma bcK_galK (σ : Fbar ≃ₐ[F] Fbar) (R : P.EK.toAffine.Point) :
    P.bcK (P.galK (P.restrictK σ) R) = galPointMap F E Fbar σ (P.bcK R) :=
  P.map_map_restrictK σ R

lemma galK_mem_TK (σ : ↥P.torsionField ≃ₐ[F] ↥P.torsionField) {R : P.EK.toAffine.Point}
    (hR : R ∈ P.TK) : P.galK σ R ∈ P.TK := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hR ⊢
  rw [← map_nsmul, hR, map_zero]

/-- The action of `Gal(K/F)` on the ℓ-torsion. -/
def galTK (σ : ↥P.torsionField ≃ₐ[F] ↥P.torsionField) : ↥P.TK →+ ↥P.TK :=
  (P.galK σ).restrict P.TK |>.codRestrict _ fun R => P.galK_mem_TK σ R.2

@[simp] lemma coe_galTK (σ : ↥P.torsionField ≃ₐ[F] ↥P.torsionField) (R : ↥P.TK) :
    (P.galTK σ R : P.EK.toAffine.Point) = P.galK σ R := rfl

/-- **The mod-ℓ representation computes the Galois action on `E(K)[ℓ]`** in the chosen
basis. -/
lemma basisK_galTK (σ : Fbar ≃ₐ[F] Fbar) (R : ↥P.TK) :
    P.basisK (P.galTK (P.restrictK σ) R) =
      (P.rep σ : Matrix (Fin 2) (Fin 2) (ZMod P.ℓ)).mulVec (P.basisK R) := by
  have h := P.rep_spec σ (P.torsionEquiv R)
  unfold basisK
  simp only [AddEquiv.trans_apply]
  rw [← h]
  congr 1
  ext
  simp only [coe_torsionEquiv, coe_galTK]
  exact P.bcK_galK σ R

end

end Iut.AdmissiblePrimeData
