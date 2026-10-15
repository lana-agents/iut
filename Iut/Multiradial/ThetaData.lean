/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Anabelian.CoreOfJ
import Iut.Anabelian.Existence
import Iut.Concrete.Existence
import Iut.Concrete.ThetaRegion

/-!
# Genuine decomposition groups in initial Θ-data (multiradial roadmap, MR1)

IUT I, Definition 3.1(e) fixes, at every place of the valuation section, a decomposition group
`G_v ⊆ Gal(F̄/K)`. The structure `Iut.LocalThetaData` records it as a field `decomp` that is only
required to be a closed subgroup (ROADMAP §5, shells #6, #38). That structure lies in the trusted
import closure of the comparator challenge (`Comparator/Challenge.lean` imports
`Iut.Concrete.ThetaRegion`, which imports `Iut.Cor312.ThetaData.Basic`), so it is not changed here.
Instead this file

* defines what it means for a subgroup to be **a decomposition group** of a finite place `w` of
  `K`: the stabilizer of a prime of the integral closure of `𝓞_K` in `F̄` over `𝔓_w`
  (`Iut.IsDecompositionGroup`); every such subgroup is closed (`IsDecompositionGroup.isClosed`), so
  the field `decomp_isClosed` is a consequence of genuineness;
* defines **genuine** local Θ-data and initial Θ-data (`LocalThetaData.HasGenuineDecomp`,
  `InitialThetaData.HasGenuineDecomp`) and the **genuinization** `D.withGenuineDecomp`, which
  replaces `decomp` by the decomposition groups `Iut.decompGroup` and keeps all other data, with
  `InitialThetaData.decomp_eq : D.withGenuineDecomp.localData.decomp v = decompGroup D.Kt D.Fbar v`;
* proves that the **existence construction** already produces genuine data
  (`AdmissiblePrimeData.localThetaData_hasGenuineDecomp`,
  `EllipticCurveData.thetaData_hasGenuineDecomp`);
* proves that the **comparator hypothesis is unchanged** by the restriction to genuine Θ-data
  (`Iut.cor312VariantHolds_iff_genuine`, `Iut.cor312LiteralHolds_iff_genuine`): the concrete
  Corollary 3.12 data do not read `decomp`.

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

/-! ### Genuine local and initial Θ-data -/

namespace LocalThetaData

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
  {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
  {VBad : Set (FinitePlace ↥(fieldOfModuli F E))} {P : AdmissiblePrimeData F E Fbar VBad}
  [NumberField ↥P.torsionField] {O : OrbicurveDataSection.OrbicurveData F E Fbar VBad P}

/-- **Genuine local Θ-data**: every chosen group `G_v` is a decomposition group of `v` (IUT I,
Definition 3.1(e)). -/
def HasGenuineDecomp (L : LocalThetaData F E Fbar VBad P O) : Prop :=
  ∀ v, IsDecompositionGroup (↥P.torsionField) Fbar v (L.decomp v)

/-- The closedness of the chosen groups is a consequence of genuineness. -/
theorem HasGenuineDecomp.decomp_isClosed {L : LocalThetaData F E Fbar VBad P O}
    (h : L.HasGenuineDecomp) (v : FinitePlace ↥P.torsionField) :
    IsClosed ((L.decomp v : Subgroup _) : Set (Fbar ≃ₐ[↥P.torsionField] Fbar)) :=
  (h v).isClosed

/-- **The genuinization** of local Θ-data: the groups `G_v` replaced by the decomposition groups
`Iut.decompGroup v`, all other data unchanged. -/
noncomputable def withGenuineDecomp (L : LocalThetaData F E Fbar VBad P O) :
    LocalThetaData F E Fbar VBad P O :=
  { L with
    decomp := fun w => decompGroup ↥P.torsionField Fbar w
    decomp_isClosed := fun w => decompGroup_isClosed ↥P.torsionField Fbar w }

@[simp]
theorem withGenuineDecomp_decomp (L : LocalThetaData F E Fbar VBad P O)
    (v : FinitePlace ↥P.torsionField) :
    L.withGenuineDecomp.decomp v = decompGroup ↥P.torsionField Fbar v := rfl

@[simp]
theorem withGenuineDecomp_sect (L : LocalThetaData F E Fbar VBad P O) :
    L.withGenuineDecomp.sect = L.sect := rfl

theorem hasGenuineDecomp_withGenuineDecomp (L : LocalThetaData F E Fbar VBad P O) :
    L.withGenuineDecomp.HasGenuineDecomp :=
  fun v => isDecompositionGroup_decompGroup _ Fbar v

end LocalThetaData

namespace InitialThetaData

/-- **Genuine initial Θ-data**: the groups `G_v` of the local data are decomposition groups. -/
def HasGenuineDecomp (D : InitialThetaData.{u}) : Prop := D.localData.HasGenuineDecomp

/-- **The genuinization** of initial Θ-data (`LocalThetaData.withGenuineDecomp`). -/
noncomputable def withGenuineDecomp (D : InitialThetaData.{u}) : InitialThetaData.{u} :=
  { D with localData := D.localData.withGenuineDecomp }

/-- **The groups `G_v` of the genuinized data are the decomposition groups** (roadmap MR1,
`decomp_eq`). -/
theorem decomp_eq (D : InitialThetaData.{u}) (v : FinitePlace D.Kt) :
    D.withGenuineDecomp.localData.decomp v = decompGroup D.Kt D.Fbar v := rfl

theorem hasGenuineDecomp_withGenuineDecomp (D : InitialThetaData.{u}) :
    D.withGenuineDecomp.HasGenuineDecomp :=
  D.localData.hasGenuineDecomp_withGenuineDecomp

end InitialThetaData

/-! ### The existence construction is genuine -/

namespace AdmissiblePrimeData

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
  {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
  {VBad : Set (FinitePlace ↥(fieldOfModuli F E))} (P : AdmissiblePrimeData F E Fbar VBad)
  [NumberField ↥P.torsionField] (TF : TateFamily E P.torsionField P.ℓ VBad)

/-- **The constructed local Θ-data use the decomposition groups.** -/
theorem localThetaData_hasGenuineDecomp (hcore : OrbicurveDataSection.HasCoreUniversally F E) :
    (P.localThetaData TF hcore).HasGenuineDecomp :=
  fun v => isDecompositionGroup_decompGroup _ Fbar v

end AdmissiblePrimeData

/-! ### The comparator hypothesis does not see `decomp` -/

open Lean Elab Tactic Meta in
/-- Close a goal `a = b` by `Eq.refl a`, leaving the definitional check to the kernel (the
elaborator's unifier does not finish on the concrete right-hand side; the kernel checks the
declaration as usual). -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let some (_, a, _) := (← g.getType').eq? | throwError "kernel_rfl: not an equality"
  g.assign (← mkEqRefl a)

/-- The `q`-pilot side does not read the groups `G_v`. -/
theorem lhs_withGenuineDecomp (D : InitialThetaData.{u}) :
    D.withGenuineDecomp.qPilot.lhs = D.qPilot.lhs := by
  kernel_rfl

/-- The right-hand side (IUT IV's reading) does not read the groups `G_v`. -/
theorem rhs_withGenuineDecomp (D : InitialThetaData.{u}) :
    D.withGenuineDecomp.rhsData.rhs = D.rhsData.rhs := by
  kernel_rfl

/-- The right-hand side (literal reading) does not read the groups `G_v`. -/
theorem rhsLit_withGenuineDecomp (D : InitialThetaData.{u}) :
    D.withGenuineDecomp.rhsDataLit.rhs = D.rhsDataLit.rhs := by
  kernel_rfl

/-- The concrete Corollary 3.12 variant of initial Θ-data and of their genuinization agree. -/
theorem corollary312Variant_withGenuineDecomp_iff (D : InitialThetaData.{u}) :
    Corollary312Variant (concreteVariantData D.withGenuineDecomp) ↔
      Corollary312Variant (concreteVariantData D) := by
  change D.withGenuineDecomp.qPilot.lhs ≤ D.withGenuineDecomp.rhsData.rhs ↔
    D.qPilot.lhs ≤ D.rhsData.rhs
  rw [lhs_withGenuineDecomp, rhs_withGenuineDecomp]

/-- As `corollary312Variant_withGenuineDecomp_iff`, literal reading. -/
theorem corollary312VariantLit_withGenuineDecomp_iff (D : InitialThetaData.{u}) :
    Corollary312Variant (concreteVariantDataLit D.withGenuineDecomp) ↔
      Corollary312Variant (concreteVariantDataLit D) := by
  change D.withGenuineDecomp.qPilot.lhs ≤ D.withGenuineDecomp.rhsDataLit.rhs ↔
    D.qPilot.lhs ≤ D.rhsDataLit.rhs
  rw [lhs_withGenuineDecomp, rhsLit_withGenuineDecomp]

/-- **The hypothesis of the comparator challenge, restricted to genuine Θ-data**: the Corollary
3.12 variant for all initial Θ-data is equivalent to the variant for all initial Θ-data whose
groups `G_v` are genuine decomposition groups. -/
theorem cor312VariantHolds_iff_genuine :
    Cor312VariantHolds ↔
      ∀ D : InitialThetaData.{0}, D.HasGenuineDecomp →
        Corollary312Variant (concreteVariantData D) :=
  ⟨fun h D _ => h D, fun h D =>
    (corollary312Variant_withGenuineDecomp_iff D).1
      (h D.withGenuineDecomp D.hasGenuineDecomp_withGenuineDecomp)⟩

/-- As `cor312VariantHolds_iff_genuine`, literal reading. -/
theorem cor312LiteralHolds_iff_genuine :
    Cor312LiteralHolds ↔
      ∀ D : InitialThetaData.{0}, D.HasGenuineDecomp →
        Corollary312Variant (concreteVariantDataLit D) :=
  ⟨fun h D _ => h D, fun h D =>
    (corollary312VariantLit_withGenuineDecomp_iff D).1
      (h D.withGenuineDecomp D.hasGenuineDecomp_withGenuineDecomp)⟩

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

/-- **The constructed initial Θ-data are genuine**: their groups `G_v` are the decomposition
groups. -/
theorem thetaData_hasGenuineDecomp (hcore : OrbicurveDataSection.HasCoreUniversally C.F C.E) :
    (C.thetaData CA TI hℓ h7 R hsl hP2 hP5 hcore).HasGenuineDecomp :=
  fun v => isDecompositionGroup_decompGroup _ _ v

end EllipticCurveData

end Iut
