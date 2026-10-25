/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFColimit
import CurvesJacobian.Galois.NewCoordinate

/-!
# [AbsTopIII] Thm 1.9 (d): the transition maps of the colimit over `V`

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178) takes
`lim→_V H¹(Π_V, μ_Ẑ(Π_U))`, `V` running over the open subschemes obtained by removing finite sets
of NF-points (and over finite extensions `k′`, `Thm19/NFColimit.lean`). In the Galois model an open
`V ⊆ U` is given by a new coordinate `t′ ∈ L` (curves-jacobian `newData`: the coordinate ring of
`V` is the integral closure of `k[t′]` in `L`), and `V ⊆ U` means that `t` is regular on `V`
(`htV : t ∈ chartRing k t′`). Here:

* `mem_of_mem_V`, `fromNew_mem_S`: places centred on `V` are centred on `U`, so the inertia
  elements of `V` are inertia elements of `U` (under `H ≅ H′`, `fromNew`);
* **`piV : Π_V → Π_U`** (`kernel_le_comap_fromNew`), continuous;
* `fV`: the function fields of `U` and `V` agree; `zV`: `Ẑ(1)_{F_U} → Ẑ(1)_{F_V}`;
* **`resV : H¹(Π_U, Ẑ(1)) → H¹(Π_V, Ẑ(1))`**, the transition map of the colimit;
* `unitsV`: units of `U` are units of `V` (integrality over `k[t]` implies integrality over
  `k[t′]`);
* **`resV_kummerMapZHat`**: `resV (κ_U(u)) = κ_V(u)`, the Kummer maps are compatible with the
  transition maps.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer
open IntermediateField.algebraAdjoinAdjoin

universe u

namespace Iut.Reconstruction.Thm19

section Shrink

open CurvesJacobian

set_option linter.unusedSectionVars false

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t t' : Ω}
  (D : Pi1.Orbifold.GaloisData k t) (ht' : t' ∈ D.L) (htr' : Transcendental k t')

include D ht' htr' in
/-- `Ω` is Galois over `k(t')`. -/
lemma isGalois_K₀_V [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] :
    IsGalois (K₀ k t') Ω :=
  isGalois_K₀_of_mem (E := D.L) D.transcendental ht' htr'

variable [IsGalois (K₀ k t) Ω] [IsGalois (K₀ k t') Ω] (hH : D.H ≤ D.HL)
  (htV : t ∈ chartRing k t')

/-- The Galois model of the open `V ⊆ U` whose coordinate ring is the integral closure of
`k[t']` (`t ∈ chartRing k t'`: `t` is regular on `V`). -/
noncomputable abbrev VData : Pi1.Orbifold.GaloisData k t' := newData D ht' htr'

include htV in
/-- Places centred on `V` are centred on `U`. -/
lemma mem_of_mem_V {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : t' ∈ W) :
    t ∈ W :=
  mem_of_mem_chartRing W hk hW htV

include hH htV in
/-- **Inertia elements of `V` are inertia elements of `U`.** -/
lemma fromNew_mem_S {σ : (VData D ht' htr').H}
    (hσ : (σ : Ω ≃ₐ[K₀ k t'] Ω) ∈ (VData D ht' htr').S) :
    ((fromNew D ht' htr' σ : D.H) : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S := by
  obtain ⟨-, W, hk, hW, hI⟩ := hσ
  exact ⟨hH (fromNew D ht' htr' σ).2, W, hk, mem_of_mem_V htV hk hW, fun a ha => hI a ha⟩

include hH htV in
lemma kernel_le_comap_fromNew :
    GaloisPi1.kernel (VData D ht' htr').H (VData D ht' htr').S ≤
      (GaloisPi1.kernel D.H D.S).comap (fromNew D ht' htr') := by
  have hS' : (VData D ht' htr').S ⊆ (VData D ht' htr').H := fun _ h => (VData D ht' htr').le h.1
  have hS : D.S ⊆ D.H := fun _ h => D.le h.1
  rw [GaloisPi1.kernel_eq_topologicalClosure _ (VData D ht' htr').isClosed_H _ hS']
  haveI : (GaloisPi1.kernel D.H D.S).Normal := inferInstance
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
    ((GaloisPi1.isClosed_kernel D.H D.S).preimage (continuous_fromNew D ht' htr'))
  intro s hs
  change fromNew D ht' htr' s ∈ GaloisPi1.kernel D.H D.S
  rw [GaloisPi1.kernel_eq_topologicalClosure _ D.isClosed_H _ hS]
  exact Subgroup.le_topologicalClosure _
    (Subgroup.subset_normalClosure (fromNew_mem_S D ht' htr' hH htV hs))

/-- **`Π_V ↠ Π_U`** (induced by `H ≅ H'`). -/
noncomputable def piV : Pi (VData D ht' htr') →* Pi D :=
  QuotientGroup.map _ _ (fromNew D ht' htr') (kernel_le_comap_fromNew D ht' htr' hH htV)

@[simp]
lemma piV_mk (σ : (VData D ht' htr').H) :
    piV D ht' htr' hH htV (σ : Pi (VData D ht' htr')) = (fromNew D ht' htr' σ : Pi D) := rfl

lemma continuous_piV : Continuous (piV D ht' htr' hH htV) := by
  change Continuous (QuotientGroup.map _ _ (fromNew D ht' htr')
    (kernel_le_comap_fromNew D ht' htr' hH htV))
  rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
  exact QuotientGroup.continuous_mk.comp (continuous_fromNew D ht' htr')

lemma mem_F_V {x : Ω} (hx : x ∈ F D) : x ∈ F (VData D ht' htr') := by
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro σ hσ
  exact hx _ (fromNew D ht' htr' ⟨σ, hσ⟩).2

/-- The identification `F_U = F_V` (same function field), as a ring map. -/
noncomputable def fV : F D →+* F (VData D ht' htr') where
  toFun x := ⟨x, mem_F_V D ht' htr' x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `F_V` as an `F_U`-algebra (local instance). -/
@[reducible] noncomputable def algebraFV : Algebra (F D) (F (VData D ht' htr')) :=
  (fV D ht' htr').toAlgebra

attribute [local instance] algebraFV

instance isScalarTower_fV : IsScalarTower (F D) (F (VData D ht' htr')) Ω :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma algebraMap_fV (x : F D) :
    algebraMap (F D) (F (VData D ht' htr')) x = ⟨x, mem_F_V D ht' htr' x.2⟩ := rfl

-- `Subtype.coe_mk` instead of `rfl`: the kernel would compare the predicates of `F_V` and `F_U`
@[simp]
lemma coe_algebraMap_fV (x : F D) :
    ((algebraMap (F D) (F (VData D ht' htr')) x : F (VData D ht' htr')) : Ω) = x := by
  rw [algebraMap_fV, Subtype.coe_mk]

variable [CharZero k]

/-- The coefficients `Ẑ(1)_{F_U} → Ẑ(1)_{F_V}` (the identity at every level). -/
noncomputable abbrev zV : ZHatOne (F D) Ω →* ZHatOne (F (VData D ht' htr')) Ω :=
  zHatRes (F D) (F (VData D ht' htr')) Ω Ω

lemma zV_fromNew_smul (σ : (VData D ht' htr').H) (x : ZHatOne (F D) Ω) :
    zV D ht' htr' (fromNew D ht' htr' σ • x) = σ • zV D ht' htr' x := by
  apply Subtype.ext
  funext i
  change muMap i.n Ω Ω ((fromNew D ht' htr' σ : Ω ≃ₐ[K₀ k t] Ω) •
      (x : ∀ j, Mu j.n Ω) (reindex (k := F D) i)) =
    (σ : Ω ≃ₐ[K₀ k t'] Ω) • muMap i.n Ω Ω ((x : ∀ j, Mu j.n Ω) (reindex (k := F D) i))
  apply Mu.ext
  apply Units.ext
  simp [AlgEquiv.smul_units_def]
  rfl

lemma zV_piV_smul (p : Pi (VData D ht' htr')) (x : ZHatOne (F D) Ω) :
    zV D ht' htr' (piV D ht' htr' hH htV p • x) = p • zV D ht' htr' x := by
  induction p using QuotientGroup.induction_on with
  | H σ => exact zV_fromNew_smul D ht' htr' σ x

/-- **Restriction `H¹(Π_U, Ẑ(1)) → H¹(Π_V, Ẑ(1))`** to the smaller open `V`. -/
noncomputable def resV :
    ContH1 (Pi D) (ZHatOne (F D) Ω) →*
      ContH1 (Pi (VData D ht' htr')) (ZHatOne (F (VData D ht' htr')) Ω) :=
  ContH1.map (piV D ht' htr' hH htV) (continuous_piV D ht' htr' hH htV) (zV D ht' htr')
    (continuous_zHatRes (F D) (F (VData D ht' htr')) Ω Ω) (zV_piV_smul D ht' htr' hH htV)

include htV in
lemma isIntegral_A₀_V {x : F D} (hx : IsIntegral (A₀ k t) x) :
    IsIntegral (A₀ k t') (algebraMap (F D) (F (VData D ht' htr')) x) := by
  haveI : IsScalarTower (A₀ k t) (F D) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (A₀ k t') (F (VData D ht' htr')) Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : IsIntegral (A₀ k t) (x : Ω) := hx.map (IsScalarTower.toAlgHom (A₀ k t) (F D) Ω)
  have h2 : (x : Ω) ∈ (chartRing k t').toSubring :=
    chartRing_le (S := (chartRing k t').toSubring) (fun c => algebraMap_mem_chartRing t' c)
      htV h1
  have h3 : IsIntegral (A₀ k t') (x : Ω) := h2
  rw [← coe_algebraMap_fV D ht' htr' x] at h3
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (A₀ k t') (F (VData D ht' htr')) Ω)
    (algebraMap (F (VData D ht' htr')) Ω).injective).1 h3

include htV in
/-- **Units of `U` are units of `V`.** -/
noncomputable def unitsV : units D →* units (VData D ht' htr') where
  toFun u := ⟨Units.map (algebraMap (F D) (F (VData D ht' htr')) :
      F D →* F (VData D ht' htr')) u,
    isIntegral_A₀_V D ht' htr' htV u.2.1, by
      rw [← map_inv]
      exact isIntegral_A₀_V D ht' htr' htV u.2.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

lemma val_unitsV (u : units D) :
    ((unitsV D ht' htr' htV u : units (VData D ht' htr')) : (F (VData D ht' htr'))ˣ) =
      Units.map (algebraMap (F D) (F (VData D ht' htr')) : F D →* F (VData D ht' htr'))
        (u : (F D)ˣ) :=
  rfl

lemma toGalF_fromNew (σ : (VData D ht' htr').H) :
    toGalF D (fromNew D ht' htr' σ) =
      galRestrict (F D) (F (VData D ht' htr')) Ω Ω (toGalF (VData D ht' htr') σ) := by
  ext x
  have := KummerTheory.algebraMap_galRestrict_apply (K := F D) (L := F (VData D ht' htr'))
    (ΩK := Ω) (ΩL := Ω) (toGalF (VData D ht' htr') σ) x
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
  rw [this]
  rfl

/-- Restriction `H¹(H, Ẑ(1)) → H¹(H', Ẑ(1))` along `fromNew`. -/
noncomputable def resHV :
    ContH1 D.H (ZHatOne (F D) Ω) →*
      ContH1 (VData D ht' htr').H (ZHatOne (F (VData D ht' htr')) Ω) :=
  ContH1.map (fromNew D ht' htr') (continuous_fromNew D ht' htr') (zV D ht' htr')
    (continuous_zHatRes (F D) (F (VData D ht' htr')) Ω Ω) (zV_fromNew_smul D ht' htr')

lemma inflZHat_resV (x : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    inflZHat (VData D ht' htr') (F (VData D ht' htr')) (resV D ht' htr' hH htV x) =
      resHV D ht' htr' (inflZHat D (F D) x) := by
  induction x using ContH1.induction_on with
  | h c => rfl

lemma resHV_resZHat (X : ContH1 (Ω ≃ₐ[F D] Ω) (ZHatOne (F D) Ω)) :
    resHV D ht' htr' (resZHat D (F D) X) =
      resZHat (VData D ht' htr') (F (VData D ht' htr'))
        (restrictZHat (F D) (F (VData D ht' htr')) Ω Ω X) := by
  induction X using ContH1.induction_on with
  | h c =>
    simp only [resHV, resZHat, Curve.res, restrictZHat, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext σ
    simp only [ContH1.cocyclesMap_apply, toGalF_fromNew, MonoidHom.id_apply]

variable [IsSepClosed Ω]

set_option maxHeartbeats 1600000 in
-- the action instances of `inflation_injective` and of `inflZHat` are unified slowly
/-- **The restriction of `κ_U(u)` to `Π_V` is `κ_V(u)`.** -/
theorem resV_kummerMapZHat (u : units D) :
    resV D ht' htr' hH htV (kummerMapZHat D u) =
      kummerMapZHat (VData D ht' htr') (unitsV D ht' htr' htV u) := by
  apply ContH1.inflation_injective
    (N := GaloisPi1.kernel (VData D ht' htr').H (VData D ht' htr').S) (fun _ _ => rfl)
  rw [inflation_kummerMapZHat, inflZHat_resV, inflation_kummerMapZHat]
  simp only [val_unitsV, kummerZHat_restrict (ΩK := Ω) (ΩL := Ω)]
  exact resHV_resZHat D ht' htr' _

end Shrink

end Iut.Reconstruction.Thm19
