/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.HemiPi1
import Iut.Cor312.ThetaData.Orbicurve
import Iut.Reconstruction.Cusp.GaloisConj

/-!
# The hemi-elliptic orbicurve: curves-jacobian's `Π_C` is iut's genuine `π₁(C_F)` (MR8)

iut's model orbicurves (`Iut.Anabelian.Orbicurve`) have **genuine** étale fundamental groups
`Orbicurve.genuinePi1 = Genuine.pi1C`: for `X = (E, ℓ, M, ±)` over a field `k` of
characteristic `0`, the group `Aut(Ω / F_X) ⧸ ⟨⟨inertia over X_M⟩⟩` inside
`Ω = k(E)^alg` (`Iut.Anabelian.Genuine`). curves-jacobian's hemi-elliptic orbicurve
`C = [(E ∖ {O}) / ±1]` (`CurvesJacobian.Cusp.hemiData E`, on which MR8's results on
[AbsTopII] Cor. 3.3 are stated) is the same Galois-theoretic construction inside another
algebraic closure `K(Ē)^alg` of the function field. This file identifies the two:

* generic: an isomorphism `φ : Ω₁ ≃+* Ω₂` mapping the image of `P₁` onto that of `P₂` induces a
  topological isomorphism of Galois groups `galConj` (Krull topologies), mapping the inertia
  group of a valuation subring `W` onto that of `φ(W)` (`galConj_mem_inertia_iff`); the
  Galois-theoretic fundamental groups `H ⧸ ⟨⟨S⟩⟩` are transported along such isomorphisms
  (`pi1Congr`);
* `hemiOmegaEquiv E : k(E)^alg ≃+* K(Ē)^alg`, extending `K(E) ≃ K(Ē)` (`funFieldEquivE`);
* **`genuinePi1HemiEquiv`**: `(pmQuotient (oncePunctured E)).genuinePi1 ≃ₜ* Π_C` — in particular
  for `C_F = OrbicurveData.CF F E` (`genuinePi1CFEquiv`);
* **`genuinePi1HemiXEquiv`**: `(oncePunctured E).genuinePi1 ≃ₜ* Π_X` (`X = E ∖ {O}`, the curve data
  `H_L ⧸ ⟨⟨S⟩⟩` of `hemiData E`);
* **`genuinePi1Cover_hemi`**: under these identifications, the map `genuinePi1Cover` of the cover
  `X → C` is curves-jacobian's `orbiIncl (hemiData E)` (open embedding with normal image of
  index `2`, `hemi_orbiIncl`).
-/

open CategoryTheory AlgebraicGeometry CurvesJacobian CurvesJacobian.Cusp Belyi Belyi.Anabelian
  Pi1.Orbifold AffOrbicurve Topology Polynomial

noncomputable section

namespace Iut.Reconstruction.HemiGenuine

universe u


/-! ### The two algebraic closures of the function field -/

section Hemi

open Iut.Anabelian Iut.Anabelian.Genuine WeierstrassCurve

attribute [local instance low] Classical.propDecidable

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- **`k(E)^alg ≃ K(Ē)^alg`**: iut's algebraic closure `Ω E` of the function field `K(E)` and
curves-jacobian's `FFClosure (curveE E)`, extending `K(E) ≃ K(Ē)` (`funFieldEquivE`). -/
def hemiOmegaEquiv : Genuine.Ω E ≃+* FFClosure (curveE E) :=
  IsAlgClosure.equivOfEquiv (Genuine.Ω E) (FFClosure (curveE E)) (funFieldEquivE E).symm

lemma hemiOmegaEquiv_algebraMap (f : E.toAffine.FunctionField) :
    hemiOmegaEquiv E (algebraMap E.toAffine.FunctionField (Genuine.Ω E) f) =
      algebraMap (curveE E).functionField (FFClosure (curveE E)) ((funFieldEquivE E).symm f) :=
  IsAlgClosure.equivOfEquiv_algebraMap _ _ _ f

lemma hemiOmegaEquiv_symm_algebraMap (r : (curveE E).functionField) :
    (hemiOmegaEquiv E).symm (algebraMap (curveE E).functionField (FFClosure (curveE E)) r) =
      algebraMap E.toAffine.FunctionField (Genuine.Ω E) (funFieldEquivE E r) := by
  rw [hemiOmegaEquiv, IsAlgClosure.equivOfEquiv_symm_algebraMap, RingEquiv.symm_symm]

lemma hemiOmegaEquiv_algebraMap_K (c : K) :
    hemiOmegaEquiv E (algebraMap K (Genuine.Ω E) c) = algebraMap K (FFClosure (curveE E)) c := by
  rw [IsScalarTower.algebraMap_apply K E.toAffine.FunctionField (Genuine.Ω E),
    hemiOmegaEquiv_algebraMap, ← funFieldEquivE_algebraMap E c, RingEquiv.symm_apply_apply,
    ← IsScalarTower.algebraMap_apply]

/-- `hemiOmegaEquiv` as a `K`-algebra isomorphism. -/
def hemiOmegaAlgEquiv : Genuine.Ω E ≃ₐ[K] FFClosure (curveE E) :=
  AlgEquiv.ofRingEquiv (f := hemiOmegaEquiv E) (hemiOmegaEquiv_algebraMap_K E)

omit [CharZero K] [E.IsElliptic] in
lemma xF_eq_genX : xF E = WeierstrassCurve.Affine.CoordinateRing.genX E.toAffine := rfl

lemma hemiOmegaEquiv_xG : hemiOmegaEquiv E (xG E) = coordT (xN E) := by
  rw [xG, hemiOmegaEquiv_algebraMap, xF_eq_genX, ← funFieldEquivE_xN, RingEquiv.symm_apply_apply]

lemma hemiOmegaEquiv_symm_coordT : (hemiOmegaEquiv E).symm (coordT (xN E)) = xG E := by
  rw [← hemiOmegaEquiv_xG, RingEquiv.symm_apply_apply]

/-- `φ` maps `k(x) ⊆ k(E)^alg` onto `K(x) ⊆ K(Ē)^alg`. -/
lemma hemiOmegaEquiv_mem_range (z : Genuine.Ω E) :
    z ∈ (algebraMap (baseField E) (Genuine.Ω E)).range ↔
      hemiOmegaEquiv E z ∈ (algebraMap (K₀ K (coordT (xN E))) (FFClosure (curveE E))).range := by
  have h1 : ∀ z, z ∈ (algebraMap (baseField E) (Genuine.Ω E)).range ↔ z ∈ baseField E :=
    fun z => ⟨by rintro ⟨c, rfl⟩; exact c.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩
  have h2 : ∀ z, z ∈ (algebraMap (K₀ K (coordT (xN E))) (FFClosure (curveE E))).range ↔
      z ∈ K₀ K (coordT (xN E)) :=
    fun z => ⟨by rintro ⟨c, rfl⟩; exact c.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩
  have hmap : (K₀ K (xG E)).map (hemiOmegaAlgEquiv E).toAlgHom = K₀ K (coordT (xN E)) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    exact congrArg (fun t => IntermediateField.adjoin K {t}) (hemiOmegaEquiv_xG E)
  rw [h1, h2, hbase E, ← hmap, IntermediateField.mem_map]
  constructor
  · intro h; exact ⟨z, h, rfl⟩
  · rintro ⟨y, hy, hyz⟩
    rwa [(hemiOmegaEquiv E).injective hyz] at hy

/-- **`Gal(k(E)^alg / k(x)) ≃ₜ* Gal(K(Ē)^alg / K(x))`**, conjugation by `hemiOmegaEquiv`. -/
def hemiGalEquiv : Gal E ≃ₜ* (FFClosure (curveE E) ≃ₐ[K₀ K (coordT (xN E))] FFClosure (curveE E)) :=
  galConj (hemiOmegaEquiv E) (hemiOmegaEquiv_mem_range E)

lemma hemiGalEquiv_apply' (σ : Gal E) (z : Genuine.Ω E) :
    hemiGalEquiv E σ (hemiOmegaEquiv E z) = hemiOmegaEquiv E (σ z) :=
  galConj_apply' _ _ σ z

omit [E.IsElliptic] in
/-- The elements of `Gal E` fix `k(x)`. -/
lemma gal_fix_xLine (σ : Gal E) {z : Genuine.Ω E} (hz : z ∈ xLine E) : σ z = z := by
  have hz' : z ∈ baseField E := by rw [hbase E]; exact hz
  exact σ.commutes ⟨z, hz'⟩

omit [CharZero K] in
/-- The image of the generic point under `σ` is a point. -/
lemma nonsingular_gal (σ : Gal E) :
    (E⁄(Genuine.Ω E)).toAffine.Nonsingular (σ (xG E)) (σ (yG E)) :=
  (Affine.baseChange_nonsingular (W := E.toAffine) (σk E σ).injective (xG E) (yG E)).mpr
    (nonsingular_generic E)

omit [CharZero K] in
lemma act_genericPoint (σ : Gal E) :
    act E σ (Genuine.genericPoint E) = Affine.Point.some _ _ (nonsingular_gal E σ) :=
  act_some E σ _ _

/-- `σ` fixes `K(E)` iff it fixes the generic point. -/
lemma act_generic_eq_iff (σ : Gal E) :
    act E σ (Genuine.genericPoint E) = Genuine.genericPoint E ↔
      ∀ f : E.toAffine.FunctionField, σ (algebraMap _ (Genuine.Ω E) f) = algebraMap _ _ f := by
  rw [act_genericPoint, Genuine.genericPoint, Affine.Point.some.injEq]
  constructor
  · rintro ⟨-, hy⟩
    -- `σ` fixes `k(x)(y) ∋ f`
    let σ' : Genuine.Ω E ≃ₐ[xLine E] Genuine.Ω E :=
      AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun c => gal_fix_xLine E σ c.2
    have hle : (fnField E).toSubalgebra ≤ AlgHom.equalizer σ'.toAlgHom (AlgHom.id _ _) := by
      rw [fnField, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
          (isIntegral_yG E).isAlgebraic,
        Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact hy
    intro f
    exact hle (ιF_mem_fnField E f)
  · intro h
    exact ⟨h (xF E), h (yF E)⟩

/-- **`H_L` corresponds**: `σ` fixes the generic point iff `φ σ φ⁻¹` fixes `K(Ē)`. -/
lemma act_generic_eq_iff_mem_HL (σ : Gal E) :
    act E σ (Genuine.genericPoint E) = Genuine.genericPoint E ↔
      hemiGalEquiv E σ ∈ (hemiData E).HL := by
  rw [act_generic_eq_iff]
  change _ ↔ hemiGalEquiv E σ ∈ (imageL (k := K) (xN E)).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h z hz
    obtain ⟨r, rfl⟩ := hz
    change hemiGalEquiv E σ (algebraMap (curveE E).functionField (FFClosure (curveE E)) r) =
      algebraMap (curveE E).functionField (FFClosure (curveE E)) r
    have e1 : algebraMap (curveE E).functionField (FFClosure (curveE E)) r =
        hemiOmegaEquiv E (algebraMap E.toAffine.FunctionField (Genuine.Ω E)
          (funFieldEquivE E r)) := by
      rw [← hemiOmegaEquiv_symm_algebraMap, RingEquiv.apply_symm_apply]
    rw [e1, hemiGalEquiv_apply', h]
  · intro h f
    apply (hemiOmegaEquiv E).injective
    rw [← hemiGalEquiv_apply', hemiOmegaEquiv_algebraMap]
    exact h _ ⟨_, rfl⟩

/-- In characteristic `0` the chosen division point of level `1` is the generic point. -/
lemma Qpt_one : Qpt E 1 = Genuine.genericPoint E := by
  have h : effLevel 1 = 1 := if_neg one_ne_zero
  rw [Qpt, h]
  exact (compatible_divSys_of_charZero E).1

omit [CharZero K] [E.IsElliptic] in
lemma Mbar_one_bot {T : Pt E} : T ∈ Mbar E 1 ⊥ ↔ T = 0 := by
  constructor
  · rintro ⟨T₀, ⟨hT₀, -⟩, rfl⟩
    obtain rfl : T₀ = 0 := hT₀
    exact map_zero _
  · rintro rfl; exact zero_mem _

/-- **`H = Gal(Ω / k(x))`** for the `±1`-quotient of `E ∖ {O}`: every `σ` maps the generic point
to `±` itself. -/
lemma mem_Hgp_one_bot_true (σ : Gal E) : σ ∈ Hgp E 1 ⊥ true := by
  have hx : σ (xG E) = xG E := gal_fix_xLine E σ (IntermediateField.mem_adjoin_simple_self K _)
  have h' := nonsingular_gal E σ
  rcases Affine.Y_eq_of_X_eq h'.1 (nonsingular_generic E).1 hx with hy | hy
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [Qpt_one, Mbar_one_bot, one_smul, sub_eq_zero, act_genericPoint, Genuine.genericPoint,
      Affine.Point.some.injEq]
    exact ⟨hx, hy⟩
  · refine ⟨-1, Or.inr ⟨rfl, rfl⟩, ?_⟩
    rw [Qpt_one, Mbar_one_bot, neg_one_smul, sub_neg_eq_add, ← eq_neg_iff_add_eq_zero,
      act_genericPoint, Genuine.genericPoint, Affine.Point.neg_some, Affine.Point.some.injEq]
    exact ⟨hx, hy⟩

end Hemi

/-! ### The genuine fundamental groups of `E ∖ {O}` and `[(E ∖ {O}) / ±1]` -/

section HemiPi1

open Iut.Anabelian Iut.Anabelian.Genuine WeierstrassCurve

attribute [local instance low] Classical.propDecidable

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- **The inertia elements correspond.** -/
lemma mem_SgenC_iff (σ : Gal E) : σ ∈ SgenC E 1 ⊥ ↔ hemiGalEquiv E σ ∈ (hemiData E).S := by
  rw [SgenC_of_charZero, Sgen_eq_S0]
  change (act E σ (Genuine.genericPoint E) = Genuine.genericPoint E ∧ _) ↔
    (hemiGalEquiv E σ ∈ (hemiData E).HL ∧ _)
  rw [act_generic_eq_iff_mem_HL]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨W, hk, hx, hσ⟩
    refine ⟨W.comap (hemiOmegaEquiv E).symm.toRingHom, fun c => ?_, ?_, ?_⟩
    · rw [ValuationSubring.mem_comap]
      have : (hemiOmegaEquiv E).symm (algebraMap K (FFClosure (curveE E)) c) =
          algebraMap K (Genuine.Ω E) c := by
        rw [← hemiOmegaEquiv_algebraMap_K, RingEquiv.symm_apply_apply]
      simpa [this] using hk c
    · rw [ValuationSubring.mem_comap]
      simpa [hemiOmegaEquiv_symm_coordT] using hx
    · exact (galConj_mem_inertia_iff _ _ σ W).2 hσ
  · rintro ⟨W', hk, hx, hσ⟩
    let W := W'.comap (hemiOmegaEquiv E).toRingHom
    have hW : W.comap (hemiOmegaEquiv E).symm.toRingHom = W' := by
      ext z
      simp [W, ValuationSubring.mem_comap]
    refine ⟨W, fun c => ?_, ?_, ?_⟩
    · simpa [W, ValuationSubring.mem_comap, hemiOmegaEquiv_algebraMap_K] using hk c
    · simpa [W, ValuationSubring.mem_comap, hemiOmegaEquiv_xG] using hx
    · rw [← galConj_mem_inertia_iff (hemiOmegaEquiv E) (hemiOmegaEquiv_mem_range E) σ W]
      change hemiGalEquiv E σ ∈ _
      rw [hW]
      exact hσ

lemma mem_Hgp_true_iff (σ : Gal E) : σ ∈ Hgp E 1 ⊥ true ↔ hemiGalEquiv E σ ∈ (hemiData E).H :=
  ⟨fun _ => Subgroup.mem_top _, fun _ => mem_Hgp_one_bot_true E σ⟩

lemma mem_Hgp_false_iff (σ : Gal E) :
    σ ∈ Hgp E 1 ⊥ false ↔ hemiGalEquiv E σ ∈ (hemiData E).HL := by
  rw [mem_Hgp_false, Qpt_one, Mbar_one_bot, sub_eq_zero, act_generic_eq_iff_mem_HL]

/-- **iut's genuine `π₁` of `[(E ∖ {O}) / ±1]` is curves-jacobian's `Π_C`** (`hemiData E`). -/
def genuinePi1HemiEquiv :
    (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).genuinePi1 ≃ₜ*
      GaloisPi1.pi1 (hemiData E).H (hemiData E).S (hemiData E).isClosed_H :=
  pi1Congr (hemiGalEquiv E) (isClosed_Hgp E 1 ⊥ true) (hemiData E).isClosed_H
    (mem_Hgp_true_iff E) (mem_SgenC_iff E)

/-- **iut's genuine `π₁` of `E ∖ {O}` is curves-jacobian's `Π_X`** (the curve part `H_L ⧸ ⟨⟨S⟩⟩`
of `hemiData E`). -/
def genuinePi1HemiXEquiv :
    (Orbicurve.oncePunctured E).genuinePi1 ≃ₜ*
      GaloisPi1.pi1 (hemiData E).HL (hemiData E).S (hemiData E).isClosed_HL :=
  pi1Congr (hemiGalEquiv E) (isClosed_Hgp E 1 ⊥ false) (hemiData E).isClosed_HL
    (mem_Hgp_false_iff E) (mem_SgenC_iff E)

/-- The cover `X = E ∖ {O} → C = [X / ±1]` of model orbicurves. -/
def hemiCover : Orbicurve.Cover (Orbicurve.oncePunctured E)
    (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)) where
  E_eq := rfl
  n := 1
  n_pos := one_pos
  mul := one_mul _
  M_le P hP := by
    obtain rfl : P = 0 := hP
    rw [smul_zero]
    exact zero_mem _
  pm_le _ := rfl

/-- **`genuinePi1Cover` of `X → C` is curves-jacobian's `orbiIncl`**: the square formed by the
two identifications commutes. -/
theorem genuinePi1Cover_hemi (x : (Orbicurve.oncePunctured E).genuinePi1) :
    genuinePi1HemiEquiv E (genuinePi1Cover (hemiCover E) x) =
      orbiIncl (hemiData E) (genuinePi1HemiXEquiv E x) := by
  have hle : Hgp E 1 ⊥ false ≤ Hgp E 1 ⊥ true ∧ SgenC E 1 ⊥ ⊆ SgenC E 1 ⊥ :=
    ⟨fun σ _ => mem_Hgp_one_bot_true E σ, subset_refl _⟩
  have hc : genuinePi1Cover (hemiCover E) =
      GaloisPi1.pi1Map (isClosed_Hgp E 1 ⊥ false) (isClosed_Hgp E 1 ⊥ true) hle.1 hle.2 := by
    change pi1MapC E = _
    unfold pi1MapC
    split_ifs with h
    · rfl
    · exact absurd hle h
  rw [hc]
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

/-- `C_F = X_F / ±1` of IUT I, Def. 3.1 (a) (`OrbicurveData.CF`): its genuine `π₁` is `Π_C`. -/
def genuinePi1CFEquiv {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F)
    [E.IsElliptic] :
    (OrbicurveDataSection.CF F E).genuinePi1 ≃ₜ*
      GaloisPi1.pi1 (hemiData E).H (hemiData E).S (hemiData E).isClosed_H :=
  genuinePi1HemiEquiv E

/-- iut's genuine `π₁(C)` is the étale fundamental group of curves-jacobian's orbifold
`[Spec R / A]` of `hemiData E` (SGA 1 V.8.2, `GaloisData.equivPi1`), the group on which
`hemiCoreChain` and the `Π_C`-statements of MR8 are formulated. -/
def genuinePi1HemiEtaleEquiv :
    (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).genuinePi1 ≃ₜ*
      etalePi1 (hemiData E).R (hemiData E).A (FFClosure (curveE E)) :=
  (genuinePi1HemiEquiv E).trans (hemiData E).equivPi1.symm

end HemiPi1

end Iut.Reconstruction.HemiGenuine
