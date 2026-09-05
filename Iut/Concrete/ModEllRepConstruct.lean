/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.Existence
import Iut.Cor312.ThetaData.PlacesOver

/-!
# Construction of the mod-`ℓ` Galois representation data

Given an elliptic curve `E/F` over a number field (`Iut.EllipticCurveData`) and a prime
`ℓ` such that the `ℓ`-torsion `E(F̄)[ℓ]` admits an `𝔽_ℓ`-basis — i.e. an additive
isomorphism `E(F̄)[ℓ] ≃+ 𝔽_ℓ²` (`hbasis`) — this module constructs the data
`EllipticCurveData.ModEllRepData ℓ` (taxis #277):

* the representation `ρ : Gal(F̄/F) → GL₂(𝔽_ℓ)` sends `σ` to the matrix of the
  `𝔽_ℓ`-linear automorphism `b ∘ σ ∘ b⁻¹` of `𝔽_ℓ²` (`EllipticCurveData.repOf`); any
  additive endomorphism of `𝔽_ℓ²` is `𝔽_ℓ`-linear (`AddMonoidHom.toZModLinearMap`);
* `ρ σ` computes the Galois action in the basis (`EllipticCurveData.repOf_spec`);
* the kernel of `ρ` is open in the Krull topology (`EllipticCurveData.repOf_ker_isOpen`):
  it contains the pointwise stabilizer of the finitely many coordinates of the finitely
  many `ℓ`-torsion points, a finite intersection of open sets
  (`Iut.isOpen_eval_eq`).

The result is `EllipticCurveData.modEllRepData C ℓ hbasis`.
-/

namespace Iut

open NumberField WeierstrassCurve
open scoped Classical

/-! ## The Galois action on the torsion as a homomorphism -/

section GaloisTorsion

variable (F : Type*) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type*) [Field Fbar] [Algebra F Fbar]

omit [NumberField F] [E.IsElliptic] in
lemma galPointMap_one (P : Affine.Point (Affine.baseChange E Fbar)) :
    galPointMap F E Fbar 1 P = P := by
  cases P <;> rfl

omit [NumberField F] [E.IsElliptic] in
lemma galPointMap_mul (σ τ : Fbar ≃ₐ[F] Fbar) (P : Affine.Point (Affine.baseChange E Fbar)) :
    galPointMap F E Fbar (σ * τ) P = galPointMap F E Fbar σ (galPointMap F E Fbar τ P) := by
  cases P <;> rfl

/-- The action of `σ ∈ Gal(F̄/F)` on the `n`-torsion `E(F̄)[n]`, as an additive
endomorphism of the torsion subgroup. -/
noncomputable def galTorsionHom (n : ℕ) (σ : Fbar ≃ₐ[F] Fbar) :
    AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) n →+
      AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) n :=
  ((galPointMap F E Fbar σ).restrict
    (AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) n)).codRestrict
    (AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) n)
    (fun P => galPointMap_torsionBy F E Fbar σ P.2)

omit [NumberField F] [E.IsElliptic] in
@[simp]
lemma galTorsionHom_apply (n : ℕ) (σ : Fbar ≃ₐ[F] Fbar)
    (P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) n) :
    galTorsionHom F E Fbar n σ P = ⟨galPointMap F E Fbar σ P.1, galPointMap_torsionBy F E Fbar σ P.2⟩ :=
  rfl

end GaloisTorsion

/-! ## The representation in a chosen basis -/

namespace EllipticCurveData

variable (C : EllipticCurveData.{u}) (ℓ : ℕ)
variable (b : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ ≃+
  (Fin 2 → ZMod ℓ))

/-- The `𝔽_ℓ`-linear endomorphism `b ∘ σ ∘ b⁻¹` of `𝔽_ℓ²` induced by `σ ∈ Gal(F̄/F)` through
the basis `b`. -/
noncomputable def repLin (σ : C.Fbar ≃ₐ[C.F] C.Fbar) :
    Module.End (ZMod ℓ) (Fin 2 → ZMod ℓ) :=
  (b.toAddMonoidHom.comp
    ((galTorsionHom C.F C.E C.Fbar ℓ σ).comp b.symm.toAddMonoidHom)).toZModLinearMap ℓ

lemma repLin_apply (σ : C.Fbar ≃ₐ[C.F] C.Fbar) (v : Fin 2 → ZMod ℓ) :
    repLin C ℓ b σ v = b (galTorsionHom C.F C.E C.Fbar ℓ σ (b.symm v)) :=
  rfl

/-- `σ ↦ b ∘ σ ∘ b⁻¹` as a monoid homomorphism to the endomorphisms of `𝔽_ℓ²`. -/
noncomputable def repEnd : (C.Fbar ≃ₐ[C.F] C.Fbar) →* Module.End (ZMod ℓ) (Fin 2 → ZMod ℓ) where
  toFun := repLin C ℓ b
  map_one' := by
    refine LinearMap.ext fun v => ?_
    rw [repLin_apply, Module.End.one_apply]
    have h : galTorsionHom C.F C.E C.Fbar ℓ 1 (b.symm v) = b.symm v :=
      Subtype.ext (galPointMap_one C.F C.E C.Fbar _)
    rw [h, b.apply_symm_apply]
  map_mul' σ τ := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, repLin_apply, repLin_apply, repLin_apply, b.symm_apply_apply]
    congr 1
    exact Subtype.ext (galPointMap_mul C.F C.E C.Fbar σ τ _)

/-- **The mod-`ℓ` representation** `ρ : Gal(F̄/F) → GL₂(𝔽_ℓ)` in the basis `b`: `ρ σ` is the
matrix of `b ∘ σ ∘ b⁻¹`. -/
noncomputable def repOf : (C.Fbar ≃ₐ[C.F] C.Fbar) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod ℓ) :=
  (Units.mapEquiv (LinearMap.toMatrixAlgEquiv' :
    Module.End (ZMod ℓ) (Fin 2 → ZMod ℓ) ≃ₐ[ZMod ℓ] Matrix (Fin 2) (Fin 2) (ZMod ℓ)).toMulEquiv
    ).toMonoidHom.comp (repEnd C ℓ b).toHomUnits

lemma coe_repOf (σ : C.Fbar ≃ₐ[C.F] C.Fbar) :
    (repOf C ℓ b σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = LinearMap.toMatrix' (repEnd C ℓ b σ) :=
  rfl

/-- `ρ σ` computes the Galois action in the basis `b`. -/
lemma repOf_spec (σ : C.Fbar ≃ₐ[C.F] C.Fbar)
    (P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ) :
    b ⟨galPointMap C.F C.E C.Fbar σ P.1, galPointMap_torsionBy C.F C.E C.Fbar σ P.2⟩ =
      (repOf C ℓ b σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).mulVec (b P) := by
  rw [coe_repOf, LinearMap.toMatrix'_mulVec]
  show _ = repLin C ℓ b σ (b P)
  rw [repLin_apply, b.symm_apply_apply, galTorsionHom_apply]

/-- An automorphism fixing the `ℓ`-torsion pointwise lies in the kernel of `ρ`. -/
lemma mem_repOf_ker_of_fixed (σ : C.Fbar ≃ₐ[C.F] C.Fbar)
    (hσ : ∀ P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ,
      galPointMap C.F C.E C.Fbar σ P.1 = P.1) :
    σ ∈ (repOf C ℓ b).ker := by
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [coe_repOf, Units.val_one, ← LinearMap.toMatrix'_one]
  congr 1
  refine LinearMap.ext fun v => ?_
  change repLin C ℓ b σ v = v
  rw [repLin_apply]
  have h : galTorsionHom C.F C.E C.Fbar ℓ σ (b.symm v) = b.symm v := Subtype.ext (hσ _)
  rw [h, b.apply_symm_apply]

/-- The set of automorphisms fixing a given point of `E(F̄)` is open. -/
lemma isOpen_galPointMap_eq (P : Affine.Point (Affine.baseChange C.E C.Fbar)) :
    IsOpen {σ : C.Fbar ≃ₐ[C.F] C.Fbar | galPointMap C.F C.E C.Fbar σ P = P} := by
  rcases P with _ | ⟨x, y, h⟩
  · have : {σ : C.Fbar ≃ₐ[C.F] C.Fbar | galPointMap C.F C.E C.Fbar σ .zero = .zero} =
        Set.univ :=
      Set.eq_univ_of_forall fun _ => rfl
    rw [this]
    exact isOpen_univ
  · have : {σ : C.Fbar ≃ₐ[C.F] C.Fbar | galPointMap C.F C.E C.Fbar σ (.some x y h) = .some x y h} =
        {σ | σ x = x} ∩ {σ | σ y = y} := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, galPointMap, Affine.Point.map_some,
        Affine.Point.some.injEq, AlgEquiv.coe_toAlgHom]
    rw [this]
    exact (isOpen_eval_eq C.F C.Fbar x x).inter (isOpen_eval_eq C.F C.Fbar y y)

/-- **The kernel of `ρ` is open**: it contains the pointwise stabilizer of the finitely many
`ℓ`-torsion points, a finite intersection of open sets. -/
lemma repOf_ker_isOpen [NeZero ℓ] : IsOpen ((repOf C ℓ b).ker : Set (C.Fbar ≃ₐ[C.F] C.Fbar)) := by
  haveI : Finite (AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ) :=
    Finite.of_equiv _ b.symm.toEquiv
  have hS : IsOpen (⋂ P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ,
      {σ : C.Fbar ≃ₐ[C.F] C.Fbar | galPointMap C.F C.E C.Fbar σ P.1 = P.1}) :=
    isOpen_iInter_of_finite fun P => isOpen_galPointMap_eq C P.1
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hS.mem_nhds ?_) ?_)
  · simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact fun P => galPointMap_one C.F C.E C.Fbar P.1
  · intro σ hσ
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hσ
    exact mem_repOf_ker_of_fixed C ℓ b σ hσ

/-- **The mod-`ℓ` representation data** of `E/F` from a basis of the `ℓ`-torsion
(taxis #277). -/
noncomputable def modEllRepData [NeZero ℓ]
    (hbasis : Nonempty (AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ ≃+
      (Fin 2 → ZMod ℓ))) : C.ModEllRepData ℓ where
  torsionBasis := hbasis.some
  rep := repOf C ℓ hbasis.some
  rep_spec := repOf_spec C ℓ hbasis.some
  ker_isOpen := repOf_ker_isOpen C ℓ hbasis.some

end EllipticCurveData

end Iut
