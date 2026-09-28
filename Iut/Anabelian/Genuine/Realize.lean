/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Genuine.Cover
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

open WeierstrassCurve Polynomial AffOrbicurve IntermediateField IntermediateField.algebraAdjoinAdjoin

open scoped Classical

noncomputable section

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-! ### The base field in characteristic `0` -/

omit [E.IsElliptic] in
lemma mem_baseField_iff (a : Ω E) : a ∈ baseField E ↔ a ∈ xLine E := by
  change a ∈ perfectClosure (xLine E) (Ω E) ↔ _
  haveI : CharZero (xLine E) := charZero_of_injective_algebraMap (algebraMap k (xLine E)).injective
  haveI : Algebra.IsSeparable (xLine E) (Ω E) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [perfectClosure.eq_bot_of_isSeparable, IntermediateField.mem_bot]
  constructor
  · rintro ⟨b, rfl⟩; exact b.2
  · intro h; exact ⟨⟨a, h⟩, rfl⟩

instance : IsGalois (xLine E) (Ω E) := by
  haveI : CharZero (xLine E) := charZero_of_injective_algebraMap (algebraMap k (xLine E)).injective
  haveI : Module.IsTorsionFree (xLine E) (Ω E) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact (algebraMap (xLine E) (Ω E)).injective
  haveI : IsAlgClosure (xLine E) (Ω E) := ⟨AlgebraicClosure.isAlgClosed _, isAlgebraic_xLine E⟩
  exact IsAlgClosure.isGalois _ _

/-- In characteristic `0`, `Gal(Ω / k(x)) = Gal(Ω / P)`. -/
def galEquiv : (Ω E ≃ₐ[xLine E] Ω E) ≃* Gal E where
  toFun σ := { σ.toRingEquiv with
    commutes' := fun p => σ.commutes ⟨p, (mem_baseField_iff E p).mp p.2⟩ }
  invFun σ := { σ.toRingEquiv with
    commutes' := fun p => σ.commutes ⟨p, (mem_baseField_iff E p).mpr p.2⟩ }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [E.IsElliptic] in
@[simp] lemma galEquiv_apply (σ : Ω E ≃ₐ[xLine E] Ω E) (a : Ω E) : galEquiv E σ a = σ a := rfl

omit [CharZero k] [E.IsElliptic] in
/-- The `x`-coordinate of the generic point is transcendental over `k`. -/
lemma transcendental_xG : Transcendental k (xG E) := by
  have h1 : Transcendental k (X : k[X]) := Polynomial.transcendental_X k
  have h2 : Transcendental k (algebraMap k[X] E.toAffine.CoordinateRing X) :=
    (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective _ _)).mpr h1
  have h3 : Transcendental k (xF E) :=
    (transcendental_algebraMap_iff (IsFractionRing.injective _ E.toAffine.FunctionField)).mpr h2
  exact (transcendental_algebraMap_iff (algebraMap E.toAffine.FunctionField (Ω E)).injective).mpr h3


/-! ### The function fields of the model orbicurves -/

/-- `Aut(Ω / F_X)` for `X = (E, ℓ, M, ±)`, as a subgroup of `Gal(Ω / k(x))`. -/
def fullSub (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Subgroup (Ω E ≃ₐ[xLine E] Ω E) :=
  (Hgp E ℓ M pm).comap (galEquiv E).toMonoidHom

/-- **The function field `F_X` of the coarse space of `(E, ℓ, M, ±)`** (for `pm = false`: the
function field `L_X` of `X_M`). -/
def coarseField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    IntermediateField (xLine E) (Ω E) :=
  fixedField (fullSub E ℓ M pm)

/-- **The function field `L_X` of `X_M = (E/M) ∖ (E[ℓ]/M)`**. -/
abbrev geomField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) : IntermediateField (xLine E) (Ω E) :=
  coarseField E ℓ M false

/-- The field generated over `k(x)` by the coordinates of `Q_ℓ`. -/
def QFieldX (ℓ : ℕ) : IntermediateField (xLine E) (Ω E) :=
  IntermediateField.adjoin (xLine E) {ptX (Qpt E ℓ), ptY (Qpt E ℓ)}

instance (ℓ : ℕ) : FiniteDimensional (xLine E) (QFieldX E ℓ) :=
  IntermediateField.finiteDimensional_adjoin (fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic (R := xLine E) x).isIntegral)

lemma QFieldX_fixing_le (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    (QFieldX E ℓ).fixingSubgroup ≤ fullSub E ℓ M pm := by
  intro σ hσ
  have hfix : ∀ a ∈ ({ptX (Qpt E ℓ), ptY (Qpt E ℓ)} : Set (Ω E)), σ a = a := fun a ha =>
    (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ a
      (IntermediateField.subset_adjoin _ _ ha)
  refine ⟨1, Or.inl rfl, ?_⟩
  change act E (galEquiv E σ) (Qpt E ℓ) - (1 : ℤ) • Qpt E ℓ ∈ _
  rw [act_eq_self_of_fix E (galEquiv E σ) _ (hfix _ (by simp)) (hfix _ (by simp)), one_smul,
    sub_self]
  exact zero_mem _

lemma isOpen_fullSub (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    IsOpen (fullSub E ℓ M pm : Set (Ω E ≃ₐ[xLine E] Ω E)) :=
  Subgroup.isOpen_mono (QFieldX_fixing_le E ℓ M pm) (QFieldX E ℓ).fixingSubgroup_isOpen

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

instance (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Algebra.IsSeparable (xLine E) (coarseField E ℓ M pm) := by
  haveI : CharZero (xLine E) := charZero_of_injective_algebraMap (algebraMap k (xLine E)).injective
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

lemma fullSub_mono {ℓ : ℕ} {M : AddSubgroup E.toAffine.Point} {pm pm' : Bool}
    (h : pm = true → pm' = true) : fullSub E ℓ M pm ≤ fullSub E ℓ M pm' := by
  rintro σ ⟨ε, hε, hT⟩
  refine ⟨ε, ?_, hT⟩
  rcases hε with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h h2, h3⟩

lemma coarseField_le_geomField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    coarseField E ℓ M pm ≤ geomField E ℓ M :=
  IntermediateField.fixedField_antitone (fullSub_mono E (by simp))


/-! ### The realizations -/

/-- The coordinate ring of the coarse space `X_M / {±1}` over that of `X_M`. -/
abbrev pmAlg (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Algebra (coordRing k (xG E) (coarseField E ℓ M true)) (coordRing k (xG E) (geomField E ℓ M)) :=
  algRing (xG E) (coarseField_le_geomField E ℓ M true)

/-- **The stabilizer orders of `[X_M / {±1}]`**: the ramification index of `X_M → X_M / {±1}`
over a closed point of the coarse space. -/
def pmMult (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point)
    (v : Ideal (coordRing k (xG E) (coarseField E ℓ M true))) : ℕ :=
  letI := pmAlg E ℓ M
  v.ramificationIdxIn (coordRing k (xG E) (geomField E ℓ M))

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

lemma pmMult_finite (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    {v : Ideal (coordRing k (xG E) (coarseField E ℓ M true)) |
      v.IsMaximal ∧ pmMult E ℓ M v ≠ 1}.Finite :=
  finite_ramified (xG E) (transcendental_xG E) (coarseField_le_geomField E ℓ M true)

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
