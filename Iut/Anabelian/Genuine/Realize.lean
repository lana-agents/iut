/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Anabelian.Genuine.Cover
import Iut.Anabelian.Genuine.Orbifold
import Pi1.Orbicurve.SubfieldRamified
import Pi1.Orbicurve.Elliptic

/-!
# The model orbicurves as affine orbicurves (characteristic `0`)

Over a field `k` of characteristic `0`, the base field `P` of `Iut.Anabelian.Genuine.Basic` is
`k(x)` itself, and `Gal E = Gal(Ω / k(x))`. The function fields of the model orbicurve
`X = (E, ℓ, M, ±)` are the fixed fields

* `geomField E ℓ M = L_X = Ω^{Aut(Ω / L_X)}` (the function field of `X_M`),
* `coarseField E ℓ M pm = F_X` (the function field of the coarse space of `X_M / {±1}`),

as intermediate fields of `Ω / k(x)`, finite over `k(x)`. The affine orbicurve `realize E ℓ M pm`
(`AffOrbicurve`, `Pi1.Orbicurve.Core`) is

* without `±`: the normalization of the `x`-line in `L_X` (all stabilizers trivial), i.e. `X_M`
  (`X_M → E ∖ {0} → A¹_x` is finite and `X_M` is normal);
* with `±`: the normalization of the `x`-line in `F_X`, with stabilizer order at a closed point
  `v` the ramification index of the double cover `X_M → X_M / {±1}` over `v` (the order of the
  stabilizer of `{±1}` at a point over `v`): the quotient stack `[X_M / {±1}]`.
-/

namespace Iut.Anabelian.Genuine

universe u

open WeierstrassCurve Polynomial AffOrbicurve IntermediateField
open IntermediateField.algebraAdjoinAdjoin


noncomputable section

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-! ### The base field in characteristic `0` -/

open scoped Classical in
omit [E.IsElliptic] in
@[simp] lemma galHom_apply (σ : Ω E ≃ₐ[xLine E] Ω E) (a : Ω E) : galHom E σ a = σ a :=
  galEquiv_symm_apply E σ a

/-! ### The function fields of the model orbicurves -/

open scoped Classical in
/-- `Aut(Ω / F_X)` for `X = (E, ℓ, M, ±)`, as a subgroup of `Gal(Ω / k(x))`. -/
def fullSub (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Subgroup (Ω E ≃ₐ[xLine E] Ω E) :=
  (Hgp E ℓ M pm).comap (galHom E)

open scoped Classical in
/-- **The function field `F_X` of the coarse space of `(E, ℓ, M, ±)`** (for `pm = false`: the
function field `L_X` of `X_M`). -/
def coarseField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    IntermediateField (xLine E) (Ω E) :=
  fixedField (fullSub E ℓ M pm)

open scoped Classical in
/-- **The function field `L_X` of `X_M = (E/M) ∖ (E[ℓ]/M)`**. -/
abbrev geomField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) : IntermediateField (xLine E) (Ω E) :=
  coarseField E ℓ M false

open scoped Classical in
/-- The field generated over `k(x)` by the coordinates of `Q_ℓ`. -/
def QFieldX (ℓ : ℕ) : IntermediateField (xLine E) (Ω E) :=
  IntermediateField.adjoin (xLine E) {ptX (Qpt E ℓ), ptY (Qpt E ℓ)}

open scoped Classical in
instance (ℓ : ℕ) : FiniteDimensional (xLine E) (QFieldX E ℓ) :=
  IntermediateField.finiteDimensional_adjoin (fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic (R := xLine E) x).isIntegral)

open scoped Classical in
lemma QFieldX_fixing_le (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    (QFieldX E ℓ).fixingSubgroup ≤ fullSub E ℓ M pm := by
  intro σ hσ
  have hfix : ∀ a ∈ ({ptX (Qpt E ℓ), ptY (Qpt E ℓ)} : Set (Ω E)), σ a = a := fun a ha =>
    (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ a
      (IntermediateField.subset_adjoin _ _ ha)
  refine ⟨1, Or.inl rfl, ?_⟩
  change act E (galHom E σ) (Qpt E ℓ) - (1 : ℤ) • Qpt E ℓ ∈ _
  have h1 : galHom E σ (ptX (Qpt E ℓ)) = ptX (Qpt E ℓ) := by
    rw [galHom_apply]; exact hfix _ (by simp)
  have h2 : galHom E σ (ptY (Qpt E ℓ)) = ptY (Qpt E ℓ) := by
    rw [galHom_apply]; exact hfix _ (by simp)
  rw [act_eq_self_of_fix E (galHom E σ) _ h1 h2, one_smul,
    sub_self]
  exact zero_mem _

open scoped Classical in
lemma isOpen_fullSub (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    IsOpen (fullSub E ℓ M pm : Set (Ω E ≃ₐ[xLine E] Ω E)) :=
  Subgroup.isOpen_mono (QFieldX_fixing_le E ℓ M pm) (QFieldX E ℓ).fixingSubgroup_isOpen

open scoped Classical in
instance finiteDimensional_coarseField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    FiniteDimensional (xLine E) (coarseField E ℓ M pm) := by
  have hc : IsClosed (fullSub E ℓ M pm : Set (Ω E ≃ₐ[xLine E] Ω E)) :=
    Subgroup.isClosed_of_isOpen _ (isOpen_fullSub E ℓ M pm)
  have h := InfiniteGalois.fixingSubgroup_fixedField ⟨fullSub E ℓ M pm, hc⟩
  rw [← InfiniteGalois.isOpen_iff_finite]
  change IsOpen (((fixedField (fullSub E ℓ M pm)).fixingSubgroup :
    Subgroup (Ω E ≃ₐ[xLine E] Ω E)) : Set (Ω E ≃ₐ[xLine E] Ω E))
  rw [h]
  exact isOpen_fullSub E ℓ M pm

open scoped Classical in
instance (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Algebra.IsSeparable (xLine E) (coarseField E ℓ M pm) := by
  haveI : CharZero (xLine E) := charZero_of_injective_algebraMap (algebraMap k (xLine E)).injective
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

open scoped Classical in
lemma fullSub_mono {ℓ : ℕ} {M : AddSubgroup E.toAffine.Point} {pm pm' : Bool}
    (h : pm = true → pm' = true) : fullSub E ℓ M pm ≤ fullSub E ℓ M pm' := by
  rintro σ ⟨ε, hε, hT⟩
  refine ⟨ε, ?_, hT⟩
  rcases hε with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h h2, h3⟩

open scoped Classical in
lemma coarseField_le_geomField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    coarseField E ℓ M pm ≤ geomField E ℓ M :=
  IntermediateField.fixedField_antitone (fullSub_mono E (by simp))


/-! ### The realizations -/

open scoped Classical in
/-- The coordinate ring of the coarse space `X_M / {±1}` over that of `X_M`. -/
abbrev pmAlg (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Algebra (coordRing k (xG E) (coarseField E ℓ M true)) (coordRing k (xG E) (geomField E ℓ M)) :=
  algRing (xG E) (coarseField_le_geomField E ℓ M true)

open scoped Classical in
/-- **The stabilizer orders of `[X_M / {±1}]`**: the ramification index of `X_M → X_M / {±1}`
over a closed point of the coarse space. -/
def pmMult (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point)
    (v : Ideal (coordRing k (xG E) (coarseField E ℓ M true))) : ℕ :=
  letI := pmAlg E ℓ M
  v.ramificationIdxIn (coordRing k (xG E) (geomField E ℓ M))

open scoped Classical in
lemma pmMult_pos (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point)
    (v : Ideal (coordRing k (xG E) (coarseField E ℓ M true))) (hv : v.IsMaximal) :
    0 < pmMult E ℓ M v := by
  letI iR := pmAlg E ℓ M
  letI : SMul (coordRing k (xG E) (coarseField E ℓ M true))
    (coordRing k (xG E) (geomField E ℓ M)) := iR.toSMul
  letI : Module (coordRing k (xG E) (coarseField E ℓ M true))
    (coordRing k (xG E) (geomField E ℓ M)) := iR.toModule
  haveI := module_finite_ringMap (xG E) (transcendental_xG E) (coarseField_le_geomField E ℓ M true)
  haveI : Algebra.IsIntegral (coordRing k (xG E) (coarseField E ℓ M true))
    (coordRing k (xG E) (geomField E ℓ M)) := ⟨ringMap_isIntegral _ _⟩
  haveI : FaithfulSMul (coordRing k (xG E) (coarseField E ℓ M true))
      (coordRing k (xG E) (geomField E ℓ M)) := by
    rw [faithfulSMul_iff_algebraMap_injective]; exact ringMap_injective _ _
  obtain ⟨P, hP, hPl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := coordRing k (xG E) (geomField E ℓ M)) v
  have hex : ∃ P : Ideal (coordRing k (xG E) (geomField E ℓ M)), P.IsPrime ∧ P.LiesOver v :=
    ⟨P, hP.isPrime, hPl⟩
  unfold pmMult
  rw [Ideal.ramificationIdxIn, dif_pos hex]
  have := hex.choose_spec.1
  exact Ideal.ramificationIdx_pos _ _

open scoped Classical in
lemma pmMult_finite (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    {v : Ideal (coordRing k (xG E) (coarseField E ℓ M true)) |
      v.IsMaximal ∧ pmMult E ℓ M v ≠ 1}.Finite :=
  finite_ramified (xG E) (transcendental_xG E) (coarseField_le_geomField E ℓ M true)

open scoped Classical in
/-- **The genuine model orbicurve `(E, ℓ, M, ±)`** as an affine orbicurve over `k`
(characteristic `0`): `X_M` (the normalization of the `x`-line in `L_X`) without `±`; the quotient
stack `[X_M / {±1}]` (coarse space the normalization of the `x`-line in `F_X`, stabilizer orders
the ramification indices of `X_M → X_M / {±1}`) with `±`. -/
def realize (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) : Bool → AffOrbicurve k
  | false => ofSubfieldScheme (xG E) (transcendental_xG E) (geomField E ℓ M)
  | true => ofSubfield (xG E) (transcendental_xG E) (coarseField E ℓ M true) (pmMult E ℓ M)
      (pmMult_pos E ℓ M) (pmMult_finite E ℓ M)

end

end Iut.Anabelian.Genuine
