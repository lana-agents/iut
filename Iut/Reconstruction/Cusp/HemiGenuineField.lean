/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.HemiGenuineTwist
import Iut.Cor312.ThetaData.Basic
import Iut.Cor312.ThetaData.PlaceUnder
import Iut.Cor312.ThetaData.PlacesOver

/-!
# `Π_{C_F} ↪ Π_{C_{F_mod}}` for an abstract number field `F ⊇ F_mod` (MR8, IUT I Def. 3.1 (b))

`Iut.Reconstruction.HemiGenuine.genuine_CM_emb` embeds the genuine `π₁` of `C_M` into that of
`C_{F_mod}` for `M ⊆ F̄_mod` an intermediate field of curves-jacobian's algebraic closure. IUT's
`F` (`InitialThetaData.F`) is an abstract number field containing `F_mod = ℚ(j)`. This file
transports the genuine `π₁` along field isomorphisms and realises `F` inside `F̄_mod`:

* `mapOmegaEquiv e E : k(E)^alg ≃+* k'(E')^alg` for a field isomorphism `e : k ≃+* k'` and
  `E' = E.map e` (from the isomorphism of coordinate rings `mapCoordEquiv`);
* **`genuinePi1MapEquiv e E`**: the genuine `π₁` of `C = (E ∖ {O}) / ±1` is invariant under
  `E ↦ E.map e`;
* **`genuine_CF_emb`**: for number fields `K ⊆ F` with `F/K` Galois, `E` over `F` and `E'` over
  `K` with `j(E) = j(E') ∉ {0, 1728}`, the genuine `π₁` of `C_F` is an open normal subgroup of
  index `[F : K]` of the genuine `π₁` of `C_K`;
* **`genuine_CF_emb_Fmod`**: the same with `K = F_mod = ℚ(j(E))` and `E' = WeierstrassCurve.ofJ j`
  (IUT's `C_{F_mod}`), for `F/F_mod` Galois and `j(E) ∉ {0, 1728}`.
-/

open CategoryTheory AlgebraicGeometry CurvesJacobian CurvesJacobian.Cusp Belyi Belyi.Anabelian
  Pi1.Orbifold AffOrbicurve Topology Polynomial

noncomputable section

namespace Iut.Reconstruction.HemiGenuine

universe u

open Iut.Anabelian Iut.Anabelian.Genuine WeierstrassCurve

/-! ### Transport along a field isomorphism -/

section Map

attribute [local instance low] Classical.propDecidable

variable {k k' : Type u} [Field k] [Field k'] (e : k ≃+* k') (E : WeierstrassCurve k)

/-- `E.map e` for a field isomorphism `e`. -/
abbrev mapE : WeierstrassCurve k' := E.map (e : k →+* k')

/-- `k[E] ≃ k'[E.map e]`. -/
def mapCoordEquiv : E.toAffine.CoordinateRing ≃+* (mapE e E).toAffine.CoordinateRing :=
  RingEquiv.ofBijective (Affine.CoordinateRing.map E.toAffine (e : k →+* k'))
    ⟨Affine.CoordinateRing.map_injective e.injective, fun y => by
      obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
      refine ⟨Affine.CoordinateRing.mk E.toAffine
        (q.map (mapRingHom (e.symm : k' →+* k))), ?_⟩
      rw [Affine.CoordinateRing.map_mk, Polynomial.map_map, Polynomial.mapRingHom_comp,
        RingEquiv.comp_symm, Polynomial.mapRingHom_id, Polynomial.map_id]⟩

lemma mapCoordEquiv_mk (q : k[X][X]) :
    mapCoordEquiv e E (Affine.CoordinateRing.mk E.toAffine q) =
      Affine.CoordinateRing.mk (mapE e E).toAffine (q.map (mapRingHom (e : k →+* k'))) :=
  Affine.CoordinateRing.map_mk _ _

/-- `k(E) ≃ k'(mapE e E)`. -/
def mapFFEquiv : E.toAffine.FunctionField ≃+* (mapE e E).toAffine.FunctionField :=
  IsFractionRing.ringEquivOfRingEquiv (mapCoordEquiv e E)

lemma mapFFEquiv_algebraMap (a : E.toAffine.CoordinateRing) :
    mapFFEquiv e E (algebraMap _ E.toAffine.FunctionField a) =
      algebraMap _ (mapE e E).toAffine.FunctionField (mapCoordEquiv e E a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

/-- **`k(E)^alg ≃ k'(mapE e E)^alg`**, extending `mapFFEquiv`. -/
def mapOmegaEquiv : Genuine.Ω E ≃+* Genuine.Ω (mapE e E) :=
  IsAlgClosure.equivOfEquiv (Genuine.Ω E) (Genuine.Ω (mapE e E)) (mapFFEquiv e E)

lemma mapOmegaEquiv_algebraMapF (f : E.toAffine.FunctionField) :
    mapOmegaEquiv e E (algebraMap _ (Genuine.Ω E) f) =
      algebraMap _ (Genuine.Ω (mapE e E)) (mapFFEquiv e E f) :=
  IsAlgClosure.equivOfEquiv_algebraMap _ _ _ f

lemma mapOmegaEquiv_algebraMapR (a : E.toAffine.CoordinateRing) :
    mapOmegaEquiv e E (algebraMap _ (Genuine.Ω E) a) =
      algebraMap _ (Genuine.Ω (mapE e E)) (mapCoordEquiv e E a) := by
  rw [IsScalarTower.algebraMap_apply _ E.toAffine.FunctionField (Genuine.Ω E),
    mapOmegaEquiv_algebraMapF, mapFFEquiv_algebraMap, ← IsScalarTower.algebraMap_apply]

lemma mapOmegaEquiv_algebraMap (c : k) :
    mapOmegaEquiv e E (algebraMap k (Genuine.Ω E) c) =
      algebraMap k' (Genuine.Ω (mapE e E)) (e c) := by
  rw [IsScalarTower.algebraMap_apply k E.toAffine.CoordinateRing (Genuine.Ω E),
    mapOmegaEquiv_algebraMapR, IsScalarTower.algebraMap_apply k' (mapE e E).toAffine.CoordinateRing]
  congr 1
  change mapCoordEquiv e E (Affine.CoordinateRing.mk E.toAffine (C (C c))) =
    Affine.CoordinateRing.mk (mapE e E).toAffine (C (C (e c)))
  rw [mapCoordEquiv_mk, Polynomial.map_C, coe_mapRingHom, Polynomial.map_C]
  rfl

lemma mapOmegaEquiv_xG : mapOmegaEquiv e E (xG E) = xG (mapE e E) := by
  rw [xG, xF, mapOmegaEquiv_algebraMapF, mapFFEquiv_algebraMap, mapCoordEquiv_mk,
    Polynomial.map_C, coe_mapRingHom, Polynomial.map_X]
  rfl

lemma mapOmegaEquiv_yG : mapOmegaEquiv e E (yG E) = yG (mapE e E) := by
  rw [yG, yF, mapOmegaEquiv_algebraMapF, mapFFEquiv_algebraMap, mapCoordEquiv_mk,
    Polynomial.map_X]
  rfl

lemma mapOmegaEquiv_symm_algebraMap (c : k') :
    (mapOmegaEquiv e E).symm (algebraMap k' (Genuine.Ω (mapE e E)) c) =
      algebraMap k (Genuine.Ω E) (e.symm c) := by
  rw [RingEquiv.symm_apply_eq, mapOmegaEquiv_algebraMap, RingEquiv.apply_symm_apply]

lemma mapOmegaEquiv_symm_xG : (mapOmegaEquiv e E).symm (xG (mapE e E)) = xG E := by
  rw [RingEquiv.symm_apply_eq, mapOmegaEquiv_xG]

/-- `φ(k(x)) = k'(x')`. -/
lemma map_K₀_mapOmegaEquiv : (K₀ k (xG E)).toSubfield.map (mapOmegaEquiv e E).toRingHom =
    (K₀ k' (xG (mapE e E))).toSubfield := by
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield,
    RingHom.map_field_closure]
  congr 1
  ext y
  simp only [Set.image_union, Set.image_singleton, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_image, Set.mem_range]
  constructor
  · rintro (⟨_, ⟨c, rfl⟩, rfl⟩ | rfl)
    · exact Or.inl ⟨e c, (mapOmegaEquiv_algebraMap e E c).symm⟩
    · exact Or.inr (mapOmegaEquiv_xG e E)
  · rintro (⟨c, rfl⟩ | rfl)
    · exact Or.inl ⟨_, ⟨e.symm c, rfl⟩, by
        rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, mapOmegaEquiv_algebraMap,
          RingEquiv.apply_symm_apply]⟩
    · exact Or.inr (mapOmegaEquiv_xG e E).symm

variable [CharZero k] [CharZero k']

/-- `φ` maps `k(x)` onto `k'(x')`. -/
lemma mapOmegaEquiv_mem_range (z : Genuine.Ω E) :
    z ∈ (algebraMap (baseField E) (Genuine.Ω E)).range ↔
      mapOmegaEquiv e E z ∈ (algebraMap (baseField (mapE e E)) (Genuine.Ω (mapE e E))).range := by
  have h1 : ∀ {k : Type u} [Field k] (E : WeierstrassCurve k) (z : Genuine.Ω E),
      z ∈ (algebraMap (baseField E) (Genuine.Ω E)).range ↔ z ∈ baseField E :=
    fun _ z => ⟨by rintro ⟨c, rfl⟩; exact c.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩
  rw [h1, h1, hbase E, hbase (mapE e E), ← IntermediateField.mem_toSubfield,
    ← IntermediateField.mem_toSubfield, ← map_K₀_mapOmegaEquiv, Subfield.mem_map]
  constructor
  · intro h; exact ⟨z, h, rfl⟩
  · rintro ⟨y, hy, hyz⟩
    rwa [(mapOmegaEquiv e E).injective hyz] at hy

/-- **`Gal(k(E)^alg / k(x)) ≃ₜ* Gal(k'(E')^alg / k'(x'))`**, conjugation by `mapOmegaEquiv`. -/
def mapGalEquiv : Gal E ≃ₜ* Gal (mapE e E) :=
  galConj (mapOmegaEquiv e E) (mapOmegaEquiv_mem_range e E)

lemma mapGalEquiv_apply' (σ : Gal E) (z : Genuine.Ω E) :
    mapGalEquiv e E σ (mapOmegaEquiv e E z) = mapOmegaEquiv e E (σ z) :=
  galConj_apply' _ _ σ z

variable [E.IsElliptic]

omit [CharZero k'] in
/-- `σ` fixes the generic point iff it fixes `y`. -/
lemma act_generic_eq_iff_yG (σ : Gal E) :
    act E σ (Genuine.genericPoint E) = Genuine.genericPoint E ↔ σ (yG E) = yG E := by
  rw [act_genericPoint E σ, Genuine.genericPoint, Affine.Point.some.injEq]
  exact ⟨fun h => h.2, fun h =>
    ⟨gal_fix_xLine E σ (IntermediateField.mem_adjoin_simple_self k _), h⟩⟩

/-- **The inertia elements correspond.** -/
lemma mem_SgenC_map_iff (σ : Gal E) :
    σ ∈ SgenC E 1 ⊥ ↔ mapGalEquiv e E σ ∈ SgenC (mapE e E) 1 ⊥ := by
  rw [SgenC_of_charZero, Sgen_eq_S0, SgenC_of_charZero, Sgen_eq_S0]
  change (act E σ (Genuine.genericPoint E) = Genuine.genericPoint E ∧ _) ↔
    (act (mapE e E) _ (Genuine.genericPoint (mapE e E)) = Genuine.genericPoint (mapE e E) ∧ _)
  rw [act_generic_eq_iff_yG, act_generic_eq_iff_yG]
  have hy : mapGalEquiv e E σ (yG (mapE e E)) = yG (mapE e E) ↔ σ (yG E) = yG E := by
    rw [← mapOmegaEquiv_yG e E, mapGalEquiv_apply']
    exact (mapOmegaEquiv e E).injective.eq_iff
  rw [hy]
  set φ := mapOmegaEquiv e E
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨W, hk, hx, hσ⟩
    refine ⟨W.comap φ.symm.toRingHom, fun c => ?_, ?_, ?_⟩
    · rw [ValuationSubring.mem_comap]
      simpa [φ, mapOmegaEquiv_symm_algebraMap] using hk (e.symm c)
    · rw [ValuationSubring.mem_comap]
      simpa [φ, mapOmegaEquiv_symm_xG] using hx
    · exact (galConj_mem_inertia_iff _ _ σ W).2 hσ
  · rintro ⟨W', hk, hx, hσ⟩
    let W := W'.comap φ.toRingHom
    have hW : W.comap φ.symm.toRingHom = W' := by
      ext z
      simp [W, ValuationSubring.mem_comap]
    refine ⟨W, fun c => ?_, ?_, ?_⟩
    · simpa [W, φ, ValuationSubring.mem_comap, mapOmegaEquiv_algebraMap] using hk (e c)
    · simpa [W, φ, ValuationSubring.mem_comap, mapOmegaEquiv_xG] using hx
    · rw [← galConj_mem_inertia_iff φ (mapOmegaEquiv_mem_range e E) σ W]
      change mapGalEquiv e E σ ∈ _
      rw [hW]
      exact hσ

/-- **The genuine `π₁` of `C = (E ∖ {O}) / ±1` is invariant under a field isomorphism**
`e : k ≃+* k'` (`E ↦ E.map e`). -/
def genuinePi1MapEquiv :
    (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).genuinePi1 ≃ₜ*
      (Orbicurve.pmQuotient (Orbicurve.oncePunctured (mapE e E))).genuinePi1 :=
  pi1Congr (mapGalEquiv e E) (isClosed_Hgp E 1 ⊥ true) (isClosed_Hgp (mapE e E) 1 ⊥ true)
    (fun σ => iff_of_true (mem_Hgp_one_bot_true E σ) (mem_Hgp_one_bot_true (mapE e E) _))
    (mem_SgenC_map_iff e E)

end Map


/-! ### `Π_{C_F} ↪ Π_{C_K}` for number fields `K ⊆ F` -/

section NF

attribute [local instance low] Classical.propDecidable

variable {K F : Type u} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F] (E' : WeierstrassCurve K) [E'.IsElliptic] (E : WeierstrassCurve F) [E.IsElliptic]

/-- A `K`-embedding of `F` into the algebraic closure `K̄ ⊆ K(Ē')^alg` of curves-jacobian. -/
def embConst : F →ₐ[K] ConstField₂ K (FFClosure (curveE E')) := IsAlgClosed.lift

/-- `F` realised as `M ⊆ K̄`. -/
abbrev fieldM : IntermediateField K (ConstField₂ K (FFClosure (curveE E'))) :=
  (embConst E' (F := F)).fieldRange

/-- `F ≃ M`. -/
def equivM : F ≃ₐ[K] fieldM E' (F := F) :=
  AlgEquiv.ofBijective
    ((embConst E').codRestrict (fieldM E' (F := F)).toSubalgebra fun x => ⟨x, rfl⟩)
    ⟨fun a b h => (embConst E').injective (congrArg Subtype.val h), fun y => by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x, Subtype.ext hx⟩⟩

instance : FiniteDimensional K F := Module.Finite.of_restrictScalars_finite ℚ K F

instance : FiniteDimensional K (fieldM E' (F := F)) :=
  LinearEquiv.finiteDimensional (equivM E' (F := F)).toLinearEquiv

instance : IsGalois K (fieldM E' (F := F)) := IsGalois.of_algEquiv (equivM E' (F := F))

/-- **`Π_{C_F} ↪ Π_{C_K}` for iut's genuine orbicurves** (IUT I, Def. 3.1 (b)): for number fields
`K ⊆ F` with `F/K` Galois, an elliptic curve `E` over `F` and `E'` over `K` with
`j(E) = j(E') ∉ {0, 1728}`, the genuine `π₁` of `C_F = (E ∖ {O}) / ±1` is an open normal subgroup
of index `[F : K]` of the genuine `π₁` of `C_K = (E' ∖ {O}) / ±1` (`F` is realised inside
`K̄ ⊆ K(Ē')^alg`, `genuinePi1MapEquiv`, then `genuine_CM_emb`). -/
theorem genuine_CF_emb (hj : E.j = algebraMap K F E'.j) (h0 : E'.j ≠ 0) (h1728 : E'.j ≠ 1728) :
    ∃ f : (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).genuinePi1 →ₜ*
        (Orbicurve.pmQuotient (Orbicurve.oncePunctured E')).genuinePi1,
      IsOpenEmbedding f ∧ f.toMonoidHom.range.Normal ∧
        f.toMonoidHom.range.index = Module.finrank K F := by
  set e := (equivM E' (F := F)).toRingEquiv
  have hjM : (mapE e E).j = algebraMap K (fieldM E' (F := F)) E'.j := by
    rw [map_j, hj]
    exact (equivM E' (F := F)).commutes _
  obtain ⟨g, hg, hn, hi⟩ := genuine_CM_emb E' (fieldM E' (F := F)) (mapE e E) hjM h0 h1728
  let t := genuinePi1MapEquiv e E
  let f := g.comp (ContinuousMonoidHom.toContinuousMonoidHom t)
  have hrange : f.toMonoidHom.range = g.toMonoidHom.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨t y, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨t.symm y, ?_⟩
      change g (t (t.symm y)) = g y
      rw [ContinuousMulEquiv.apply_symm_apply]
  refine ⟨f, ?_, ?_, ?_⟩
  · have hf : (f : _ → _) = g ∘ t := rfl
    rw [hf]
    exact hg.comp t.toHomeomorph.isOpenEmbedding
  · rw [hrange]; exact hn
  · rw [hrange, hi]
    exact (equivM E' (F := F)).toLinearEquiv.finrank_eq.symm

end NF

/-! ### IUT's `C_{F_mod}` -/

section Fmod

attribute [local instance low] Classical.propDecidable

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]

/-- `j(E) ∈ F_mod = ℚ(j(E))`. -/
def jMod : fieldOfModuli F E := ⟨E.j, IntermediateField.mem_adjoin_simple_self ℚ E.j⟩

/-- **IUT's `C_{F_mod}`**: the hemi-elliptic orbicurve `(E_mod ∖ {O}) / ±1` of the `F_mod`-model
`E_mod = WeierstrassCurve.ofJ j` (`j = j(E)`; `C` does not depend on the model). -/
abbrev curveMod : WeierstrassCurve (fieldOfModuli F E) := WeierstrassCurve.ofJ (jMod E)

/-- **`Π_{C_F} ↪ Π_{C_{F_mod}}`** (IUT I, Def. 3.1 (b); Ex. 5.1 (i) "a profinite group
corresponding to `C_{F_mod}` […] which contains `π₁(†D^⊚)` as an open subgroup"): for `F/F_mod`
Galois and `j(E) ∉ {0, 1728}`, the genuine `π₁` of `C_F` is an open normal subgroup of index
`[F : F_mod]` of the genuine `π₁` of `C_{F_mod}` (`curveMod E`). -/
theorem genuine_CF_emb_Fmod [IsGalois (fieldOfModuli F E) F] (h0 : E.j ≠ 0) (h1728 : E.j ≠ 1728) :
    ∃ f : (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).genuinePi1 →ₜ*
        (Orbicurve.pmQuotient (Orbicurve.oncePunctured (curveMod E))).genuinePi1,
      IsOpenEmbedding f ∧ f.toMonoidHom.range.Normal ∧
        f.toMonoidHom.range.index = Module.finrank (fieldOfModuli F E) F := by
  have hj : (curveMod E).j = jMod E := by
    classical
    exact WeierstrassCurve.ofJ_j _
  refine genuine_CF_emb (curveMod E) E ?_ ?_ ?_
  · rw [hj]; rfl
  · rw [hj]; exact fun h => h0 (congrArg Subtype.val h)
  · rw [hj]; intro h
    have h' := congrArg (algebraMap (fieldOfModuli F E) F) h
    rw [map_ofNat] at h'
    exact h1728 h'

/-- At a place of multiplicative reduction, `j(E) ∉ {0, 1728}`. -/
lemma j_ne_of_mult {w : NumberField.FinitePlace F} (hw : HasMultiplicativeReductionAt E w) :
    E.j ≠ 0 ∧ E.j ≠ 1728 := by
  have h := one_lt_valuation_j_of_mult E w hw
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · rw [h0, map_zero] at h
    exact not_lt.2 zero_le h
  · rw [h1] at h
    have h' : w.maximalIdeal.valuation F (1728 : F) ≤ 1 := by
      have := w.maximalIdeal.valuation_le_one (K := F) (1728 : NumberField.RingOfIntegers F)
      exact_mod_cast this
    exact not_lt.2 h' h

end Fmod

open scoped Classical in
/-- **`Π_{C_F} ↪ Π_{C_{F_mod}}` for initial Θ-data** (IUT I, Def. 3.1 (b), Ex. 5.1 (i)): the genuine
`π₁` of `C_F` is an open normal subgroup of index `[F : F_mod]` of the genuine `π₁` of
`C_{F_mod}` (`F/F_mod` is Galois by Def. 3.1 (b); `j(E_F) ∉ {0, 1728}` since `E_F` has
multiplicative reduction at the places over `V_mod^bad ≠ ∅`). -/
theorem genuine_CF_emb_Fmod_theta (D : InitialThetaData.{u}) :
    ∃ f : (OrbicurveDataSection.CF D.F D.E).genuinePi1 →ₜ*
        (Orbicurve.pmQuotient (Orbicurve.oncePunctured (curveMod D.E))).genuinePi1,
      IsOpenEmbedding f ∧ f.toMonoidHom.range.Normal ∧
        f.toMonoidHom.range.index = Module.finrank (fieldOfModuli D.F D.E) D.F := by
  haveI := D.prime.galois_deg_prime.1
  obtain ⟨v, hv⟩ := D.global.bad_nonempty
  obtain ⟨w, hw⟩ := FinitePlace.exists_liesOver (K := D.F) v
  obtain ⟨h0, h1728⟩ := j_ne_of_mult D.E (D.global.bad_multiplicative v hv w hw)
  exact genuine_CF_emb_Fmod D.E h0 h1728

end Iut.Reconstruction.HemiGenuine
