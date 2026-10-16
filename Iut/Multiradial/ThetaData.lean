/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Anabelian.CoreOfJ
import Iut.Anabelian.Existence
import Iut.Concrete.Existence

/-!
# Genuine decomposition groups in initial Θ-data (multiradial roadmap, MR1)

IUT I, Definition 3.1(e) uses, at every place `v` of the valuation section, "the decomposition
group `G_v ⊆ G_K` determined, up to `G_K`-conjugacy, by `v`". In `Iut.LocalThetaData` this group is
the **definition** `LocalThetaData.decomp v := Iut.decompGroup v` (the stabilizer of the chosen
prime of the integral closure of `𝓞_K` in `F̄` over `𝔓_v`), no longer a datum (shells #6, #38;
before MR1 it was an arbitrary closed subgroup given as a structure field). This file

* defines what it means for a subgroup to be **a decomposition group** of a finite place `w` of
  `K`: the stabilizer of *some* prime of the integral closure of `𝓞_K` in `F̄` over `𝔓_w`
  (`Iut.IsDecompositionGroup`); every such subgroup is closed (`IsDecompositionGroup.isClosed`);
* proves that the groups `G_v` of local and initial Θ-data are decomposition groups in this
  sense (`LocalThetaData.isDecompositionGroup_decomp`,
  `InitialThetaData.isDecompositionGroup_decomp`) and records
  `InitialThetaData.decomp_eq : D.localData.decomp v = decompGroup D.Kt D.Fbar v`.

The core condition of Definition 3.1(d) is derived from [CanLift], Proposition 2.7 in
`Iut.Anabelian.CoreOfJ`; `EllipticCurveData.thetaDataOfJ` is the existence construction with that
derivation built in.
-/

namespace Iut

open NumberField

universe u

/-! ### Decomposition groups -/

section Stabilizer

variable (K : Type*) [Field K] (Fbar : Type*) [Field Fbar] [Algebra K Fbar]

/-- The **setwise stabilizer** in `Gal(F̄/K)` of a subset of `F̄`. -/
def setStabilizer (S : Set Fbar) : Subgroup (Fbar ≃ₐ[K] Fbar) where
  carrier := {σ | ∀ x, x ∈ S ↔ σ x ∈ S}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {σ τ} hσ hτ x => by
    simp only [Set.mem_setOf_eq] at hσ hτ ⊢
    rw [AlgEquiv.mul_apply, ← hσ, ← hτ]
  inv_mem' := fun {σ} hσ x => by
    simp only [Set.mem_setOf_eq] at hσ ⊢
    have h := hσ (σ⁻¹ x)
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h
    exact h.symm

lemma mem_setStabilizer {S : Set Fbar} {σ : Fbar ≃ₐ[K] Fbar} :
    σ ∈ setStabilizer K Fbar S ↔ ∀ x, x ∈ S ↔ σ x ∈ S := Iff.rfl

/-- **Setwise stabilizers are closed** in the Krull topology. -/
theorem setStabilizer_isClosed [NumberField K] [Algebra.IsIntegral K Fbar] (S : Set Fbar) :
    IsClosed ((setStabilizer K Fbar S : Subgroup _) : Set (Fbar ≃ₐ[K] Fbar)) := by
  have : ((setStabilizer K Fbar S : Subgroup _) : Set (Fbar ≃ₐ[K] Fbar)) =
      ⋂ x, {σ | x ∈ S ↔ σ x ∈ S} := by
    ext σ; simp [setStabilizer]
  rw [this]
  refine isClosed_iInter fun x => ?_
  by_cases hx : x ∈ S
  · have : {σ : Fbar ≃ₐ[K] Fbar | x ∈ S ↔ σ x ∈ S} = ({σ | σ x ∈ Sᶜ})ᶜ := by
      ext σ; simp [hx]
    rw [this, isClosed_compl_iff]
    exact isOpen_eval_mem K Fbar x _
  · have : {σ : Fbar ≃ₐ[K] Fbar | x ∈ S ↔ σ x ∈ S} = ({σ | σ x ∈ S})ᶜ := by
      ext σ; simp [hx]
    rw [this, isClosed_compl_iff]
    exact isOpen_eval_mem K Fbar x _

variable [NumberField K]

/-- An ideal of the integral closure of `𝓞_K` in `F̄`, as a subset of `F̄`. -/
def idealSet (Q : Ideal (intClosure K Fbar)) : Set Fbar :=
  {x | ∃ hx : x ∈ intClosure K Fbar, (⟨x, hx⟩ : intClosure K Fbar) ∈ Q}

/-- **`H` is a decomposition group of the finite place `w` of `K`** in `Gal(F̄/K)`: the
stabilizer of some prime `Q` of the integral closure of `𝓞_K` in `F̄` lying over `𝔓_w` (IUT I,
Definition 3.1(e): "a decomposition group", well defined up to conjugacy). -/
def IsDecompositionGroup (w : FinitePlace K) (H : Subgroup (Fbar ≃ₐ[K] Fbar)) : Prop :=
  ∃ Q : Ideal (intClosure K Fbar), Q.IsPrime ∧
    Q.comap (algebraMap (𝓞 K) (intClosure K Fbar)) = w.maximalIdeal.asIdeal ∧
    H = setStabilizer K Fbar (idealSet K Fbar Q)

/-- `Iut.decompGroup w` (the stabilizer of the chosen prime over `𝔓_w`) is the stabilizer of
that prime. -/
lemma decompGroup_eq_setStabilizer (w : FinitePlace K) :
    decompGroup K Fbar w = setStabilizer K Fbar (idealSet K Fbar (primeOver K Fbar w)) :=
  Subgroup.ext fun _ => Iff.rfl

/-- **`Iut.decompGroup w` is a decomposition group of `w`.** -/
theorem isDecompositionGroup_decompGroup (w : FinitePlace K) :
    IsDecompositionGroup K Fbar w (decompGroup K Fbar w) :=
  ⟨primeOver K Fbar w, primeOver_isPrime K Fbar w, primeOver_comap K Fbar w,
    decompGroup_eq_setStabilizer K Fbar w⟩

/-- **Decomposition groups are closed** in the Krull topology. -/
theorem IsDecompositionGroup.isClosed [Algebra.IsIntegral K Fbar] {w : FinitePlace K}
    {H : Subgroup (Fbar ≃ₐ[K] Fbar)} (h : IsDecompositionGroup K Fbar w H) :
    IsClosed (H : Set (Fbar ≃ₐ[K] Fbar)) := by
  obtain ⟨Q, -, -, rfl⟩ := h
  exact setStabilizer_isClosed K Fbar _

end Stabilizer

/-! ### The groups `G_v` of Θ-data are decomposition groups -/

namespace LocalThetaData

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
  {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
  {VBad : Set (FinitePlace ↥(fieldOfModuli F E))} {P : AdmissiblePrimeData F E Fbar VBad}
  [NumberField ↥P.torsionField] {O : OrbicurveDataSection.OrbicurveData F E Fbar VBad P}

/-- **The groups `G_v` of local Θ-data are decomposition groups** of the places `v` (IUT I,
Definition 3.1(e)). -/
theorem isDecompositionGroup_decomp (L : LocalThetaData F E Fbar VBad P O)
    (v : FinitePlace ↥P.torsionField) :
    IsDecompositionGroup (↥P.torsionField) Fbar v (L.decomp v) :=
  isDecompositionGroup_decompGroup _ Fbar v

end LocalThetaData

namespace InitialThetaData

/-- **The groups `G_v` of initial Θ-data are the decomposition groups** `Iut.decompGroup v`
(roadmap MR1, `decomp_eq`; no hypothesis beyond `D`). -/
theorem decomp_eq (D : InitialThetaData.{u}) (v : FinitePlace D.Kt) :
    D.localData.decomp v = decompGroup D.Kt D.Fbar v := rfl

/-- **The groups `G_v` of initial Θ-data are decomposition groups** of the places `v`. -/
theorem isDecompositionGroup_decomp (D : InitialThetaData.{u}) (v : FinitePlace D.Kt) :
    IsDecompositionGroup D.Kt D.Fbar v (D.localData.decomp v) :=
  isDecompositionGroup_decompGroup _ _ v

end InitialThetaData

/-! ### The existence construction for elliptic curves -/

namespace EllipticCurveData

variable (C : EllipticCurveData.{0}) (CA : C.CurveArithmetic) (TI : C.TateInputs) {ℓ : ℕ}
  (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) (R : C.ModEllRepData ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ R.rep.range)
  (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
  (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)

/-- **The initial Θ-data attached to `(E/F, ℓ)` with the core condition derived** from
[CanLift], Proposition 2.7 (`Iut.Anabelian.hasCoreUniversally_of_j`): the only input beyond the
arithmetic of `E` is that `j(E)` is not exceptional. -/
noncomputable def thetaDataOfJ (hj : ∀ c ∈ AffOrbicurve.excJ, C.E.j ≠ (c : C.F)) :
    InitialThetaData.{0} :=
  C.thetaData CA TI hℓ h7 R hsl hP2 hP5 (Anabelian.hasCoreUniversally_of_j C.E hj)

end EllipticCurveData

end Iut
