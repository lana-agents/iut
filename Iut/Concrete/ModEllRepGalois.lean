/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.CyclicSubgroup

/-!
# The torsion field and the image of a mod-`ℓ` representation

For mod-`ℓ` representation data `R : C.ModEllRepData ℓ` of an elliptic curve `E/F` over a
number field (`Iut.EllipticCurveData`), with torsion field `K = F̄^{ker ρ}`:

* the `ℓ`-torsion of `E(F̄)` is rational over `K` (`ModEllRepData.torsionEquiv`), so that
  `E(K)[ℓ]` has order `ℓ²` (`ModEllRepData.card_torsionBy_EK`) — the argument of
  `Iut.AdmissiblePrimeData.torsionEquiv` for the data without the `SL₂` condition;
* `K/F` is Galois with group `Gal(K/F) ≅ ρ(Gal(F̄/F))` (`ModEllRepData.rangeEquivGal`), in
  particular `|ρ(Gal(F̄/F))| = |Gal(K/F)|` (`ModEllRepData.card_range`);
* a line of `𝔽_ℓ²` stable under the image of `ρ` is an `ℓ`-cyclic subgroup scheme
  (`ModEllRepData.hasCyclicSubgroup_of_stable_line`): its preimage under the chosen basis is a
  `Gal(F̄/F)`-stable subgroup of `E(F̄)` of order `ℓ`.
-/

namespace Iut.EllipticCurveData.ModEllRepData

universe u

open WeierstrassCurve NumberField Iut Matrix
open scoped Classical

noncomputable section

variable {C : EllipticCurveData.{u}} {ℓ : ℕ} (R : C.ModEllRepData ℓ)

/-- The classical decidable equality on `K`, as used by the model orbicurves. -/
local instance (priority := 1100) instDecidableEqTorsionField : DecidableEq ↥R.torsionField :=
  fun a b => Classical.propDecidable (a = b)

/-! ### The `ℓ`-torsion is rational over the torsion field -/

/-- The curve `E` over the torsion field `K`. -/
abbrev EK : WeierstrassCurve ↥R.torsionField := C.E.map (algebraMap C.F ↥R.torsionField)

/-- The base change of points `E(K) → E(F̄)`. -/
def bcK : R.EK.toAffine.Point →+ Affine.Point (Affine.baseChange C.E C.Fbar) :=
  Affine.Point.map (W' := C.E) (S := C.F) (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar)

lemma bcK_injective : Function.Injective R.bcK :=
  Affine.Point.map_injective (W' := C.E) (S := C.F)
    (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar)

/-- The `ℓ`-torsion of `E(K)`. -/
abbrev TK : AddSubgroup R.EK.toAffine.Point := AddSubgroup.torsionBy R.EK.toAffine.Point ℓ

/-- The `ℓ`-torsion of `E(F̄)`. -/
abbrev TFbar (C : EllipticCurveData.{u}) (ℓ : ℕ) :
    AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar)) :=
  AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ

/-- Elements of the kernel of the mod-`ℓ` representation fix the `ℓ`-torsion. -/
lemma galPointMap_eq_of_mem_ker {σ : C.Fbar ≃ₐ[C.F] C.Fbar} (hσ : σ ∈ R.rep.ker)
    (Q : ↥(TFbar C ℓ)) : galPointMap C.F C.E C.Fbar σ Q.1 = Q.1 := by
  have h := R.rep_spec σ Q
  rw [MonoidHom.mem_ker.mp hσ] at h
  simp only [Units.val_one, Matrix.one_mulVec] at h
  exact congrArg Subtype.val (R.torsionBasis.injective h)

/-- Every `ℓ`-torsion point of `E(F̄)` comes from `E(K)`. -/
lemma exists_bcK_eq (Q : Affine.Point (Affine.baseChange C.E C.Fbar)) (hQ : Q ∈ TFbar C ℓ) :
    ∃ P : R.EK.toAffine.Point, R.bcK P = Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  · have hfix : ∀ σ ∈ R.rep.ker, σ x = x ∧ σ y = y := by
      intro σ hσ
      have h' := R.galPointMap_eq_of_mem_ker hσ ⟨_, hQ⟩
      rw [galPointMap, Affine.Point.map_some] at h'
      exact Affine.Point.some.inj h'
    have hx : x ∈ R.torsionField := by
      rw [torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).1
    have hy : y ∈ R.torsionField := by
      rw [torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).2
    have hns : (Affine.baseChange C.E ↥R.torsionField).Nonsingular
        (⟨x, hx⟩ : ↥R.torsionField) ⟨y, hy⟩ :=
      (Affine.baseChange_nonsingular (W := C.E)
        (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar).injective _ _).mp h
    exact ⟨.some _ _ hns, rfl⟩

lemma bcK_mem_TFbar {P : R.EK.toAffine.Point} (hP : P ∈ R.TK) : R.bcK P ∈ TFbar C ℓ := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

lemma mem_TK_of_bcK {P : R.EK.toAffine.Point} (hP : R.bcK P ∈ TFbar C ℓ) : P ∈ R.TK := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul] at hP
  exact R.bcK_injective (hP.trans (map_zero _).symm)

/-- **The `ℓ`-torsion is rational over `K`**: `E(K)[ℓ] ≃ E(F̄)[ℓ]`. -/
def torsionEquiv : ↥R.TK ≃+ ↥(TFbar C ℓ) :=
  AddEquiv.ofBijective (R.bcK.restrict R.TK |>.codRestrict _ fun P => R.bcK_mem_TFbar P.2)
    ⟨fun P P' h => Subtype.ext (R.bcK_injective (congrArg Subtype.val h)),
     fun Q => by
      obtain ⟨P, hP⟩ := R.exists_bcK_eq Q.1 Q.2
      exact ⟨⟨P, R.mem_TK_of_bcK (hP ▸ Q.2)⟩, Subtype.ext hP⟩⟩

/-- `E(K)[ℓ]` has order `ℓ²`. -/
lemma card_torsionBy_EK : Nat.card R.TK = ℓ ^ 2 := by
  rw [Nat.card_congr (R.torsionEquiv.trans R.torsionBasis).toEquiv, Nat.card_pi, Nat.card_zmod]
  simp

/-! ### The Galois group of the torsion field -/

/-- `K/F` is Galois (the fixed field of the normal subgroup `ker ρ`). -/
instance isGalois_torsionField : IsGalois C.F ↥R.torsionField :=
  IsGalois.of_fixedField_normal_subgroup R.rep.ker

/-- The fixing subgroup of the torsion field is the kernel of `ρ` (which is open, hence
closed). -/
lemma fixingSubgroup_torsionField : R.torsionField.fixingSubgroup = R.rep.ker :=
  InfiniteGalois.fixingSubgroup_fixedField (k := C.F) (K := C.Fbar)
    ⟨R.rep.ker, Subgroup.isClosed_of_isOpen _ R.ker_isOpen⟩

/-- The kernel of the restriction `Gal(F̄/F) → Gal(K/F)` is the kernel of `ρ`. -/
lemma restrictNormalHom_ker_eq :
    (AlgEquiv.restrictNormalHom R.torsionField :
      (C.Fbar ≃ₐ[C.F] C.Fbar) →* (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)).ker = R.rep.ker := by
  rw [IntermediateField.restrictNormalHom_ker, fixingSubgroup_torsionField]

/-- **`Gal(K/F) ≅ ρ(Gal(F̄/F))`**: both are the quotient of `Gal(F̄/F)` by `ker ρ`. -/
def rangeEquivGal : R.rep.range ≃* (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField) :=
  (QuotientGroup.quotientKerEquivRange R.rep).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq R.restrictNormalHom_ker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (AlgEquiv.restrictNormalHom_surjective (F := C.F) (K₁ := ↥R.torsionField)
          (E := C.Fbar))))

/-- `|ρ(Gal(F̄/F))| = |Gal(K/F)|`. -/
lemma card_range : Nat.card R.rep.range = Nat.card (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField) :=
  Nat.card_congr R.rangeEquivGal.toEquiv

/-! ### Stable lines and cyclic subgroups -/

/-- **A line of `𝔽_ℓ²` stable under the image of `ρ` gives an `ℓ`-cyclic subgroup scheme**:
the preimage under the basis of the line `𝔽_ℓ·v` is a `Gal(F̄/F)`-stable subgroup of `E(F̄)`
of order `ℓ`. -/
lemma hasCyclicSubgroup_of_stable_line [Fact ℓ.Prime] (v : Fin 2 → ZMod ℓ) (hv : v ≠ 0)
    (hstab : ∀ σ : C.Fbar ≃ₐ[C.F] C.Fbar, ∃ c : ZMod ℓ,
      (R.rep σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ v = c • v) :
    C.HasCyclicSubgroup ℓ := by
  let f : (Fin 2 → ZMod ℓ) →+ Affine.Point (Affine.baseChange C.E C.Fbar) :=
    (AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ).subtype.comp
      R.torsionBasis.symm.toAddMonoidHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp R.torsionBasis.symm.injective
  have hfσ : ∀ (σ : C.Fbar ≃ₐ[C.F] C.Fbar) (x : Fin 2 → ZMod ℓ),
      galPointMap C.F C.E C.Fbar σ (f x) =
        f ((R.rep σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ x) := by
    intro σ x
    have h := R.rep_spec σ (R.torsionBasis.symm x)
    rw [AddEquiv.apply_symm_apply] at h
    have h' := congrArg R.torsionBasis.symm h
    rw [AddEquiv.symm_apply_apply] at h'
    exact congrArg Subtype.val h'
  refine ⟨(AddSubgroup.zmultiples v).map f, ?_, ?_⟩
  · rw [← Nat.card_congr (AddSubgroup.equivMapOfInjective _ f hf).toEquiv, Nat.card_zmultiples,
      addOrderOf_eq_prime (p := ℓ) _ hv]
    ext i
    simp
  · intro σ P hP
    rw [AddSubgroup.mem_map] at hP ⊢
    obtain ⟨x, hx, rfl⟩ := hP
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    obtain ⟨c, hc⟩ := hstab σ
    refine ⟨(n * c.val) • v, AddSubgroup.mem_zmultiples_iff.mpr ⟨n * c.val, rfl⟩, ?_⟩
    have hcv : c • v = (c.val : ℤ) • v := by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_smul_eq_nsmul, natCast_zsmul]
    rw [hfσ, Matrix.mulVec_smul, hc, hcv, smul_smul]

/-- If `E/F` has no `ℓ`-cyclic subgroup scheme, no line of `𝔽_ℓ²` is stable under the image
of `ρ`. -/
lemma exists_mulVec_ne_smul_of_not_hasCyclicSubgroup [Fact ℓ.Prime]
    (h : ¬ C.HasCyclicSubgroup ℓ) (v : Fin 2 → ZMod ℓ) (hv : v ≠ 0) :
    ∃ g ∈ R.rep.range, ∀ c : ZMod ℓ, (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ v ≠ c • v := by
  by_contra hcon
  apply h
  refine R.hasCyclicSubgroup_of_stable_line v hv fun σ => ?_
  by_contra hσ
  exact hcon ⟨R.rep σ, ⟨σ, rfl⟩, fun c hc => hσ ⟨c, hc⟩⟩

end

end Iut.EllipticCurveData.ModEllRepData
