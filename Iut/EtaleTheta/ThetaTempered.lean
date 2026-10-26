/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaClassSystem
import TemperedFundamentalGroups.Tempered.Kummer
import TemperedFundamentalGroups.Andre.TateObjectIsogeny

/-!
# Tempered theta classes: naturality under a change of level (MR14, run 7)

For intermediate fields `L ≤ L'` of `Ω / k(t)` with open fixing groups, the Galois data
`D = fieldData L`, `D' = fieldData L'` (trivial groups `A`, `A'`) give the affine curves
`U = Spec R`, `U' = Spec R'` (`R`, `R'` the integral closures of `k[t]` in `L`, `L'`) and the
map of orbifolds `U' → U` (`levelOrbMap`, the inclusion `R ⊆ R'`). This file proves that the
comparison maps `Π^tp → Π` of `tempered-fundamental-groups` commute with the change of level:

* `etalePi1Map_toEtalePi1`: `π₁ᵉᵗ(U') → π₁ᵉᵗ(U)` maps the action of `σ ∈ Gal(Ω/L')` on the
  fibre functor of `U'` to the action of `σ` on the fibre functor of `U`;
* `etaleToPi_etalePi1Map`: `etaleToPi D ∘ etalePi1Map = piRes ∘ etaleToPi D'`;
* `tempToPi_temperedPi1Map`: `tempToPi D ∘ temperedPi1Map = piRes ∘ tempToPi D'`;
* **`map_kummerMapTempered_level`**: the pull-back of the tempered Kummer class `κ^tp_n(v)` of a
  unit `v` of `U` along `Π^tp_{U'} → Π^tp_U` is `κ^tp_n(v')`, `v'` the image of `v` in `U'`
  (from `resPi_kummerMap`, the étale naturality).

With `exists_etaleThetaSystem` this makes the tempered theta classes
`κ^tp_n(η_j) ∈ H¹(Π^tp_{Ÿ'_{N_j}}, μ_n)` a projective system in `j`.
-/

open CategoryTheory Pi1.Orbifold AffOrbicurve KummerTheory KummerTheory.Curve
open CurvesJacobian.Cusp TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta

section Level

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (ht : Transcendental k t)

/-- For `fieldData`, `A = H ⧸ H` is trivial. -/
instance subsingleton_fieldData_A (L : IntermediateField (K₀ k t) Ω)
    (hL : IsOpen (L.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))) :
    Subsingleton (fieldData ht L hL).A := by
  refine ⟨fun a b => ?_⟩
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact (x⁻¹ * y).2

variable {L L' : IntermediateField (K₀ k t) Ω}
  (hL : IsOpen (L.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
  (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))) (hle : L ≤ L')

include hle in
theorem fieldData_L_le : (fieldData ht L hL).L ≤ (fieldData ht L' hL').L :=
  IntermediateField.fixedField_antitone (IntermediateField.fixingSubgroup_antitone hle)

/-- The inclusion `R ⊆ R'` of coordinate rings for a change of level `L ≤ L'`. -/
def levelHom : (fieldData ht L hL).R →+* (fieldData ht L' hL').R :=
  (AffOrbicurve.ringMap t (fieldData_L_le ht hL hL' hle)).toRingHom

/-- `R'` as an `R`-algebra. -/
abbrev levelAlgebra : Algebra (fieldData ht L hL).R (fieldData ht L' hL').R :=
  (levelHom ht hL hL' hle).toAlgebra

end Level

/-! ### The étale and tempered comparison maps commute with a change of level -/

section Naturality

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (ht : Transcendental k t)
  {L L' : IntermediateField (K₀ k t) Ω}
  (hL : IsOpen (L.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
  (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))) (hle : L ≤ L')
  [Algebra (fieldData ht L hL).R (fieldData ht L' hL').R]
  [IsScalarTower k (fieldData ht L hL).R (fieldData ht L' hL').R]
  [IsScalarTower (fieldData ht L hL).R (fieldData ht L' hL').R Ω]

/-- **The map of orbifolds** `U' → U` of a change of level (trivial groups). -/
def levelOrbMap : OrbMap (fieldData ht L hL).R (fieldData ht L hL).A (fieldData ht L' hL').R
    (fieldData ht L' hL').A where
  α := 1
  map_smul a' r := by
    rw [Subsingleton.elim a' 1, one_smul, MonoidHom.one_apply, one_smul]
  injective := by
    intro a b hab
    apply CoordRing.algebraMap_injective
    rw [IsScalarTower.algebraMap_apply (fieldData ht L hL).R (fieldData ht L' hL').R Ω a,
      IsScalarTower.algebraMap_apply (fieldData ht L hL).R (fieldData ht L' hL').R Ω b, hab]

omit [IsScalarTower k (fieldData ht L hL).R (fieldData ht L' hL').R] in
/-- `π₁ᵉᵗ(U') → π₁ᵉᵗ(U)` maps the action of `σ ∈ Gal(Ω/L')` on the fibre functor of `U'` to
the action of `σ` on the fibre functor of `U`. -/
theorem etalePi1Map_toEtalePi1 (h : (fieldData ht L' hL').H) :
    etalePi1Map (levelOrbMap ht hL hL') Ω ((fieldData ht L' hL').toEtalePi1 h) =
      (fieldData ht L hL).toEtalePi1
        (Subgroup.inclusion (fieldData_H_antitone ht hL hL' hle) h) := by
  apply FibreAut.ext
  intro X f
  rw [etalePi1Map, FibreAut.restrict_app]
  change X.level.bcRes (levelOrbMap ht hL hL') ((fieldData ht L' hL').fibreSmul h
    (EquivEtaleBC.bcEt (levelOrbMap ht hL hL') X) (X.level.bcExt (levelOrbMap ht hL hL') f)) =
      (fieldData ht L hL).fibreSmul _ X f
  ext y
  rw [FiniteLevel.bcRes_apply]
  refine (GaloisData.fibreSmul_of_mem (fieldData ht L' hL') h.2 _ _ _).trans ?_
  refine Eq.trans ?_ (GaloisData.fibreSmul_of_mem (fieldData ht L hL)
    (Subgroup.inclusion (fieldData_H_antitone ht hL hL' hle) h).2 _ _ _).symm
  congr 1
  exact congrArg (fun g : X.level.B →ₐ[(fieldData ht L hL).R] Ω => g y)
    (FiniteLevel.bcRes_bcExt (levelOrbMap ht hL hL') X.level f)

variable [IsGalois (K₀ k t) Ω] [CharZero k]

omit [IsScalarTower k (fieldData ht L hL).R (fieldData ht L' hL').R] in
/-- **`etaleToPi` commutes with the change of level**: `π₁ᵉᵗ(U') → π₁ᵉᵗ(U) ≅ Π_U` is
`π₁ᵉᵗ(U') ≅ Π_{U'} → Π_U`. -/
theorem etaleToPi_etalePi1Map (γ : etalePi1 (fieldData ht L' hL').R (fieldData ht L' hL').A Ω) :
    etaleToPi (fieldData ht L hL) (etalePi1Map (levelOrbMap ht hL hL') Ω γ) =
      piRes (fieldData_H_antitone ht hL hL' hle) (fieldData_S_antitone ht hL hL' hle)
        (etaleToPi (fieldData ht L' hL') γ) := by
  obtain ⟨x, rfl⟩ := (fieldData ht L' hL').equivPi1.symm.surjective γ
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  · have e : (fieldData ht L' hL').equivPi1.symm (h : Pi (fieldData ht L' hL')) =
        (fieldData ht L' hL').toEtalePi1 h := by
      apply FibreAut.ext
      intro X f
      rw [GaloisData.equivPi1_symm_mk_app]
      rfl
    rw [e, etalePi1Map_toEtalePi1 ht hL hL' hle, etaleToPi_toEtalePi1, etaleToPi_toEtalePi1]
    rfl

variable (O : ValuationSubring k) (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)

/-- **`tempToPi` commutes with the change of level**. -/
theorem tempToPi_temperedPi1Map (γ : TempPi (fieldData ht L' hL') O V hV) :
    tempToPi (fieldData ht L hL) O V hV (temperedPi1Map (levelOrbMap ht hL hL') V hV γ) =
      piRes (fieldData_H_antitone ht hL hL' hle) (fieldData_S_antitone ht hL hL' hle)
        (tempToPi (fieldData ht L' hL') O V hV γ) := by
  rw [← MonoidHom.comp_apply, ← tempToPi'_eq, tempToPi', MonoidHom.comp_apply,
    MonoidHom.comp_apply, etaleToPi_etalePi1Map ht hL hL' hle]
  rfl

variable [IsSepClosed Ω]

omit [IsSepClosed Ω] in
include hle in
/-- The action of `Π^tp_{U'}` on `μ_n` through `Π^tp_U` is its own action. -/
theorem tempToPi_smul_level (n : ℕ) [NeZero n] (γ : TempPi (fieldData ht L' hL') O V hV)
    (x : Mu n Ω) :
    tempToPi (fieldData ht L hL) O V hV (temperedPi1Map (levelOrbMap ht hL hL') V hV γ) • x =
      tempToPi (fieldData ht L' hL') O V hV γ • x := by
  rw [tempToPi_temperedPi1Map ht hL hL' hle]
  induction tempToPi (fieldData ht L' hL') O V hV γ using QuotientGroup.induction_on
  rfl

include hle in
/-- **The tempered pull-back commutes with the change of level**: pulling a class of `Π_U`
back to `Π^tp_U` and then to `Π^tp_{U'}` is restricting it to `Π_{U'}` and pulling back. -/
theorem map_toTempMu_level (n : ℕ) [NeZero n] (x : ContH1 (Pi (fieldData ht L hL)) (Mu n Ω)) :
    ContH1.map (temperedPi1Map (levelOrbMap ht hL hL') V hV)
        (continuous_temperedPi1Map (levelOrbMap ht hL hL') V hV) (MonoidHom.id _) continuous_id
        (fun γ y => (tempToPi_smul_level ht hL hL' hle O V hV n γ y).trans rfl)
        (toTempMu (fieldData ht L hL) O V hV n x) =
      toTempMu (fieldData ht L' hL') O V hV n
        (resPi (fieldData_H_antitone ht hL hL' hle) (fieldData_S_antitone ht hL hL' hle) n x) := by
  induction x using ContH1.induction_on with
  | h c =>
    simp only [resPi, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext γ
    simp only [ContH1.cocyclesMap_apply, MonoidHom.id_apply]
    rw [tempToPi_temperedPi1Map ht hL hL' hle]

/-- **Naturality of the tempered Kummer classes under a change of level**: the pull-back of
`κ^tp_n(v)` along `Π^tp_{U'} → Π^tp_U` is `κ^tp_n(v')` for the image `v'` of `v`. -/
theorem map_kummerMapTempered_level (n : ℕ) [NeZero n] (v : units (fieldData ht L hL))
    (v' : units (fieldData ht L' hL'))
    (hv : ((((v : (F (fieldData ht L hL))ˣ) : F (fieldData ht L hL)) : Ω)) =
      ((((v' : (F (fieldData ht L' hL'))ˣ) : F (fieldData ht L' hL')) : Ω))) :
    ContH1.map (temperedPi1Map (levelOrbMap ht hL hL') V hV)
        (continuous_temperedPi1Map (levelOrbMap ht hL hL') V hV) (MonoidHom.id _) continuous_id
        (fun γ y => (tempToPi_smul_level ht hL hL' hle O V hV n γ y).trans rfl)
        (kummerMapTempered (fieldData ht L hL) O V hV n v) =
      kummerMapTempered (fieldData ht L' hL') O V hV n v' := by
  rw [kummerMapTempered, kummerMapTempered, MonoidHom.comp_apply, MonoidHom.comp_apply,
    map_toTempMu_level ht hL hL' hle, resPi_kummerMap _ _ n v v' hv]

end Naturality

end Iut.EtaleTheta
