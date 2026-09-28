/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Genuine.Core
import Pi1.Orbicurve.Iso
import Pi1.Orbicurve.Elliptic

/-!
# The once-punctured elliptic curve and its `±1`-quotient

Over a field `k` of characteristic `0`, the realizations of the model orbicurves
`E ∖ {0} = (E, 1, 0)` and `(E ∖ {0}) / {±1} = (E, 1, 0, ±)` are isomorphic to the affine
orbicurves `AffOrbicurve.punctured E` and `AffOrbicurve.hemi E` of `Pi1.Orbicurve.Elliptic`
(`isoPunctured`, `isoHemi`), on which [CanLift], Proposition 2.7 (`AffOrbicurve.CanLift27`) is
stated:

* the function field `L_X` of `E ∖ {0}` is `k(x, y) = ιF(k(E))` (`geomField_one_bot`), so the
  coordinate rings (integral closures of `k[x]`) correspond (`AffOrbicurve.integralClosureEquiv`);
* the function field `F_X` of `(E ∖ {0}) / {±1}` is `k(x)` (`coarseField_one_bot`), with
  coordinate ring `k[x]`, and the stabilizer orders are the ramification indices of
  `E ∖ {0} → A¹_x` on both sides (`AffOrbicurve.ramificationIdx_congr`).
-/

namespace Iut.Anabelian.Genuine

universe u

open WeierstrassCurve AffOrbicurve IntermediateField Polynomial
open IntermediateField.algebraAdjoinAdjoin

noncomputable section

attribute [local instance 2000] Classical.propDecidable

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

lemma Qpt_one : Qpt E 1 = genericPoint E := by
  have h := (compatible_divSys_of_charZero E).1
  unfold Qpt effLevel
  simpa using h

/-- **The function field of `E ∖ {0}`** is `k(x, y)`. -/
lemma geomField_one_bot : geomField E 1 ⊥ = fnField E := by
  apply le_antisymm
  · refine (geomField_le_QFieldX E 1 ⊥).trans ?_
    rw [QFieldX, Qpt_one, IntermediateField.adjoin_le_iff]
    rintro z (rfl | rfl)
    · exact xG_mem_fnField E
    · exact yG_mem_fnField E
  · rw [fnField, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact (xG_yG_mem_geomField E 1 ⊥).2

omit [CharZero k] [E.IsElliptic] in
lemma fnField_le_range (z : Ω E) (hz : z ∈ fnField E) : ∃ f, ιF E f = z := by
  let S : IntermediateField (xLine E) (Ω E) :=
    (ιF E).fieldRange.toSubfield.toIntermediateField (fun x => by
      have hx : ∀ y ∈ xLine E, y ∈ (ιF E).fieldRange := by
        intro y hy
        have : xLine E ≤ (ιF E).fieldRange := by
          rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
          exact ⟨xF E, rfl⟩
        exact this hy
      exact hx _ x.2)
  have : fnField E ≤ S := by
    rw [fnField, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨yF E, rfl⟩
  exact this hz

/-- **`k(E) ≅ L_X`** for `X = E ∖ {0}`, induced by `ιF : k(E) → Ω`. -/
def funFieldEquiv : E.toAffine.FunctionField ≃+* geomField E 1 ⊥ :=
  RingEquiv.ofBijective ((ιF E).toRingHom.codRestrict (geomField E 1 ⊥) fun f => by
      rw [geomField_one_bot]; exact ιF_mem_fnField E f)
    ⟨fun a b h => (ιF E).injective (congrArg Subtype.val h), fun z => by
      have hz : (z : Ω E) ∈ fnField E := by rw [← geomField_one_bot]; exact z.2
      obtain ⟨f, hf⟩ := fnField_le_range E z hz
      exact ⟨f, Subtype.ext hf⟩⟩

@[simp] lemma coe_funFieldEquiv (f : E.toAffine.FunctionField) :
    ((funFieldEquiv E f : geomField E 1 ⊥) : Ω E) = ιF E f := rfl

/-- `k[x] ≅ k[xG]`. -/
def polyEquiv : k[X] ≃ₐ[k] A₀ k (xG E) :=
  Polynomial.algEquivOfTranscendental k (xG E) (transcendental_xG E)

lemma coe_polyEquiv (p : k[X]) : ((polyEquiv E p : A₀ k (xG E)) : Ω E) = aeval (xG E) p := by
  change ((aeval (⟨xG E, Algebra.self_mem_adjoin_singleton k (xG E)⟩ : A₀ k (xG E)) p :
    A₀ k (xG E)) : Ω E) = _
  rw [← Subalgebra.aeval_coe]

omit [CharZero k] [E.IsElliptic] in
lemma ιF_algebraMap_poly (p : k[X]) :
    ιF E (algebraMap k[X] E.toAffine.FunctionField p) = aeval (xG E) p := by
  have h : ((ιF E).comp (IsScalarTower.toAlgHom k k[X] E.toAffine.FunctionField)) =
      aeval (xG E) := by
    apply Polynomial.algHom_ext
    rw [aeval_X]
    change ιF E (algebraMap k[X] E.toAffine.FunctionField X) = xG E
    rw [IsScalarTower.algebraMap_apply k[X] E.toAffine.CoordinateRing E.toAffine.FunctionField]
    rfl
  exact congrArg (fun φ : k[X] →ₐ[k] Ω E => φ p) h

lemma funFieldEquiv_algebraMap (p : k[X]) :
    funFieldEquiv E (algebraMap k[X] E.toAffine.FunctionField p) =
      algebraMap (A₀ k (xG E)) (geomField E 1 ⊥) (polyEquiv E p) := by
  apply Subtype.ext
  rw [coe_funFieldEquiv, ιF_algebraMap_poly]
  exact (coe_polyEquiv E p).symm

/-- The coordinate rings of `E ∖ {0}`: `puncturedRing E ≅ coordRing (L_X)`. -/
def puncturedRingEquiv :
    puncturedRing E ≃+* coordRing k (xG E) (geomField E 1 ⊥) :=
  integralClosureEquiv (polyEquiv E).toRingEquiv (funFieldEquiv E) (funFieldEquiv_algebraMap E)

@[simp] lemma coe_puncturedRingEquiv (a : puncturedRing E) :
    (((puncturedRingEquiv E a : coordRing k (xG E) (geomField E 1 ⊥)) : geomField E 1 ⊥) : Ω E) =
      ιF E (a : E.toAffine.FunctionField) := rfl

/-- **`E ∖ {0}`**: the realization of the model orbicurve `(E, 1, 0)` is `punctured E`. -/
def isoPunctured : AffOrbicurve.Iso (realize E 1 ⊥ false) (punctured E) :=
  AffOrbicurve.Iso.ofAlgEquiv
    (AlgEquiv.ofRingEquiv (f := (puncturedRingEquiv E).symm) fun c => by
      refine ((puncturedRingEquiv E).symm_apply_eq).mpr ?_
      apply Subtype.ext; apply Subtype.ext
      rw [coe_puncturedRingEquiv]
      change algebraMap k (Ω E) c = ιF E (algebraMap k E.toAffine.FunctionField c)
      rw [AlgHom.commutes])
    (fun _ _ => rfl)

/-! ### `(E ∖ {0}) / {±1}` -/

/-- Every automorphism maps the generic point to `±` itself. -/
lemma act_generic_eq_or_neg (σ : Gal E) :
    act E σ (genericPoint E) = genericPoint E ∨ act E σ (genericPoint E) = -genericPoint E := by
  have hx : σ (xG E) = xG E := σ.commutes ⟨_, xG_mem_baseField E⟩
  obtain ⟨h', hact⟩ : ∃ h', act E σ (genericPoint E) = Affine.Point.some (σ (xG E)) (σ (yG E)) h' :=
    ⟨_, rfl⟩
  rcases Affine.Y_eq_of_X_eq h'.1 (nonsingular_generic E).1 hx with hy | hy
  · left
    rw [hact, genericPoint]
    congr 1
  · right
    rw [hact, genericPoint, Affine.Point.neg_some]
    congr 1

lemma Hgp_one_bot_true : Hgp E 1 ⊥ true = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  rcases act_generic_eq_or_neg E σ with h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [Qpt_one, h, one_smul, sub_self]; exact zero_mem _
  · refine ⟨-1, Or.inr ⟨rfl, rfl⟩, ?_⟩
    rw [Qpt_one, h, neg_one_smul, sub_neg_eq_add, neg_add_cancel]; exact zero_mem _

/-- **The function field of `(E ∖ {0}) / {±1}`** is `k(x)`. -/
lemma coarseField_one_bot : coarseField E 1 ⊥ true = ⊥ := by
  have hfull : fullSub E 1 ⊥ true = ⊤ := by
    rw [fullSub, Hgp_one_bot_true, Subgroup.comap_top]
  rw [coarseField, hfull, ← IntermediateField.fixingSubgroup_bot,
    InfiniteGalois.fixedField_fixingSubgroup]

set_option maxHeartbeats 1000000 in
/-- The coordinate ring of `(E ∖ {0}) / {±1}` is `k[xG]`. -/
lemma bijective_algebraMap_coarse :
    Function.Bijective
      (algebraMap (A₀ k (xG E)) (coordRing k (xG E) (coarseField E 1 ⊥ true))) := by
  refine ⟨fun a b h => Subtype.ext (congrArg (fun c : coordRing k (xG E)
    (coarseField E 1 ⊥ true) => ((c : coarseField E 1 ⊥ true) : Ω E)) h), fun b => ?_⟩
  have hb : ((b : coarseField E 1 ⊥ true) : Ω E) ∈ (⊥ : IntermediateField (K₀ k (xG E)) (Ω E)) := by
    rw [← coarseField_one_bot E]; exact (b : coarseField E 1 ⊥ true).2
  obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp hb
  haveI := isPrincipalIdealRing_A₀ (transcendental_xG E)
  have hzint : IsIntegral (A₀ k (xG E)) z := by
    have h1 := isIntegral_of_mem_coordRing (xG E) b
    rw [← hz] at h1
    haveI : IsScalarTower (A₀ k (xG E)) (K₀ k (xG E)) (Ω E) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact (isIntegral_algebraMap_iff (algebraMap (K₀ k (xG E)) (Ω E)).injective).mp h1
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A₀ k (xG E))
    (K := K₀ k (xG E))).mp hzint
  refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
  rw [← hz, ← ha]
  rfl

/-- `k[x] ≅` the coordinate ring of the coarse space of `(E ∖ {0}) / {±1}`. -/
def coarseRingEquiv : k[X] ≃+* coordRing k (xG E) (coarseField E 1 ⊥ true) :=
  (polyEquiv E).toRingEquiv.trans (RingEquiv.ofBijective _ (bijective_algebraMap_coarse E))

lemma coe_coarseRingEquiv (p : k[X]) :
    (((coarseRingEquiv E p : coordRing k (xG E) (coarseField E 1 ⊥ true)) :
      coarseField E 1 ⊥ true) : Ω E) = aeval (xG E) p :=
  coe_polyEquiv E p

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The stabilizer orders of `(E ∖ {0}) / {±1}` on both sides agree. -/
lemma ramificationIdxIn_punctured_eq (w : Ideal k[X]) [hw : w.IsMaximal] :
    w.ramificationIdxIn (puncturedRing E) =
      pmMult E 1 ⊥ (w.comap (coarseRingEquiv E).symm.toRingHom) := by
  have hFL := coarseField_le_geomField E 1 ⊥ true
  haveI : IsDedekindDomain (puncturedRing E) := (punctured E).isDedekindDomain
  haveI := isDedekindDomain_ring (xG E) (transcendental_xG E) (coarseField E 1 ⊥ true)
  haveI := isDedekindDomain_ring (xG E) (transcendental_xG E) (geomField E 1 ⊥)
  have hex : ∃ P : Ideal (puncturedRing E), P.IsPrime ∧ P.LiesOver w := by
    obtain ⟨P, hP, hPl⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := puncturedRing E) w
    exact ⟨P, hP.isPrime, hPl⟩
  rw [Ideal.ramificationIdxIn, dif_pos hex]
  obtain ⟨hP, hPl⟩ := hex.choose_spec
  set P := hex.choose
  haveI := hP
  haveI := hPl
  haveI hPm : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P w
  have hcompat : ∀ r : k[X], puncturedRingEquiv E (algebraMap k[X] (puncturedRing E) r) =
      (ringMap (xG E) hFL).toRingHom (coarseRingEquiv E r) := by
    intro r
    apply Subtype.ext; apply Subtype.ext
    rw [coe_puncturedRingEquiv]
    change ιF E (algebraMap k[X] E.toAffine.FunctionField r) = _
    rw [ιF_algebraMap_poly, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_ringMap,
      coe_coarseRingEquiv]
  have hcongr := ramificationIdx_congr (algebraMap k[X] (puncturedRing E))
    (ringMap (xG E) hFL).toRingHom (coarseRingEquiv E) (puncturedRingEquiv E) hcompat
    (ringMap_injective _ hFL) P
  have halg : (algebraMap k[X] (puncturedRing E)).toAlgebra =
      (inferInstance : Algebra k[X] (puncturedRing E)) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  rw [halg] at hcongr
  rw [hcongr]
  set ŵ := P.comap (puncturedRingEquiv E).symm.toRingHom
  haveI : ŵ.IsMaximal := Ideal.comap_isMaximal_of_surjective _ (RingEquiv.surjective _)
  have hpm := pmMult_eq E 1 ⊥ ŵ
  refine hpm.trans (congrArg _ ?_)
  ext x
  obtain ⟨r, rfl⟩ := (coarseRingEquiv E).surjective x
  simp only [Ideal.mem_comap]
  change (puncturedRingEquiv E).symm ((ringMap (xG E) hFL).toRingHom (coarseRingEquiv E r)) ∈ P ↔
    (coarseRingEquiv E).symm (coarseRingEquiv E r) ∈ w
  rw [← hcompat, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply, hPl.over]
  rfl

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **`(E ∖ {0}) / {±1}`**: the realization of the model orbicurve `(E, 1, 0, ±)` is
`hemi E`. -/
def isoHemi : AffOrbicurve.Iso (realize E 1 ⊥ true) (hemi E) :=
  AffOrbicurve.Iso.ofAlgEquiv
    (AlgEquiv.ofRingEquiv (f := (coarseRingEquiv E).symm) fun c => by
      refine ((coarseRingEquiv E).symm_apply_eq).mpr ?_
      apply Subtype.ext; apply Subtype.ext
      rw [coe_coarseRingEquiv]
      change algebraMap k (Ω E) c = aeval (xG E) (algebraMap k k[X] c)
      exact ((aeval (xG E)).commutes c).symm)
    (fun w hw => @ramificationIdxIn_punctured_eq k _ _ E _ w hw)

/-- **[CanLift], Proposition 2.7 for the realizations**: if `j(E)` is not exceptional, the
`k`-core of `E ∖ {0}` is `(E ∖ {0}) / {±1}`. -/
theorem isCoreOf_realize_oncePunctured (h27 : CanLift27.{u}) (hj : ∀ c ∈ excJ, E.j ≠ (c : k)) :
    IsCoreOf (realize E 1 ⊥ false) (realize E 1 ⊥ true) :=
  ((h27 k E hj).congr_left (isoPunctured E).symm).congr_right (isoHemi E).symm

end

end Iut.Anabelian.Genuine
