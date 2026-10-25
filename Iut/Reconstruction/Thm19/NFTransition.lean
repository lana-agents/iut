/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFShrink

/-!
# [AbsTopIII] Thm 1.9 (d): transition maps between arbitrary stages of the colimit

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178) takes
`lim→_V H¹(Π_V, μ_Ẑ(Π_U))`, `V` running over the opens of `Z ×_{k_Z} k′` for finite extensions
`k′` and finite sets of removed NF-points. `Thm19/NFColimit.lean` treats `U_{k′} → U` and
`Thm19/NFShrink.lean` treats `V → U`. Here both are instances of one generic transition map,
between two Galois models `D₁ : GaloisData k₁ t₁` (the curve `U₁`) and `D₂ : GaloisData k₂ t₂`
(the curve `U₂`) inside the same `Ω`, given

* `hF`: the function field of `U₁` is contained in that of `U₂` (`F D₁ ⊆ F D₂`);
* `hW`: every place of `Ω` centred on `U₂` (containing `k₂` and `t₂`) is centred on `U₁`
  (contains `k₁` and `t₁`): `U₂` maps to `U₁`;
* `hH₁`: `H₁ = H_{L,1}` (no orbifold structure on `U₁`).

Then:

* **`piT : Π_{U₂} → Π_{U₁}`** (`σ ↦ σ`), continuous; `piT_piT`: transitivity;
* **`resT : H¹(Π_{U₁}, Ẑ(1)) → H¹(Π_{U₂}, Ẑ(1))`** and **`resT_resT`**: the transition maps
  compose, so the stages form a direct system;
* `unitsT`: units of `U₁` are units of `U₂`; `unitsT_unitsT`;
* **`resT_kummerMapZHat`**: `resT (κ_{U₁}(u)) = κ_{U₂}(u)`;
* `resKH1_eq_resT`, `resV_eq_resT`: the maps of `NFColimit` and `NFShrink` are transition maps.

The **stages** (`stage K t′ = newData (constExt K D) t′`: base change to an algebraic extension
`K` of `k`, then the open of a coordinate `t′`) with their order (`K ⊆ K′`, `t′` regular on the
open of `t″`) are in the second half: `F_stage`, `le_F_stage`, `F_stage_mono`, the transitions
`U → stage`, `U_K → stage` and `stage → stage`, and **directedness** (`exists_stage_ge`: two
stages over the same `K` have a common refinement, the coordinate `t₁ + c t₂`).
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer
open IntermediateField.algebraAdjoinAdjoin

universe u

namespace Iut.Reconstruction.Thm19

section Transition

open CurvesJacobian

set_option linter.unusedSectionVars false

variable {k₁ k₂ Ω : Type u} [Field k₁] [Field k₂] [Field Ω] [Algebra k₁ Ω] [Algebra k₂ Ω]
  {t₁ t₂ : Ω} (D₁ : Pi1.Orbifold.GaloisData k₁ t₁) (D₂ : Pi1.Orbifold.GaloisData k₂ t₂)
  (hF : ∀ x ∈ F D₁, x ∈ F D₂)

include hF in
lemma fixes_of_le_F (σ : D₂.H) {x : Ω} (hx : x ∈ F D₁) : (σ : Ω ≃ₐ[K₀ k₂ t₂] Ω) x = x :=
  fixes_of_mem_F σ.2 ⟨x, hF x hx⟩

/-- An element of `H₂` as an automorphism of `Ω` over `k₁(t₁)`. -/
noncomputable def galT : D₂.H →* (Ω ≃ₐ[K₀ k₁ t₁] Ω) where
  toFun σ := AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[K₀ k₂ t₂] Ω).toRingEquiv)
    fun c => fixes_of_le_F D₁ D₂ hF σ ((F D₁).algebraMap_mem c)
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

@[simp]
lemma galT_apply (σ : D₂.H) (x : Ω) :
    galT D₁ D₂ hF σ x = (σ : Ω ≃ₐ[K₀ k₂ t₂] Ω) x := rfl

variable [IsGalois (K₀ k₁ t₁) Ω]

lemma galT_mem (σ : D₂.H) : galT D₁ D₂ hF σ ∈ D₁.H := by
  have e : (IntermediateField.fixedField D₁.H).fixingSubgroup = D₁.H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨D₁.H, D₁.isClosed_H⟩
  rw [← e]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
    fixes_of_le_F D₁ D₂ hF σ hx

/-- **`H₂ → H₁`** (`σ ↦ σ`). -/
noncomputable def hT : D₂.H →* D₁.H :=
  (galT D₁ D₂ hF).codRestrict D₁.H (galT_mem D₁ D₂ hF)

@[simp]
lemma hT_apply (σ : D₂.H) (x : Ω) :
    ((hT D₁ D₂ hF σ : D₁.H) : Ω ≃ₐ[K₀ k₁ t₁] Ω) x = (σ : Ω ≃ₐ[K₀ k₂ t₂] Ω) x := rfl

variable [IsGalois (K₀ k₂ t₂) Ω]

lemma continuous_hT : Continuous (hT D₁ D₂ hF) :=
  (continuous_of_isOpen_setOf_apply_eq (D₁.H.subtype.comp (hT D₁ D₂ hF)) fun x =>
      (Pi1.Orbifold.isOpen_setOf_apply_eq (t := t₂) x).preimage continuous_subtype_val).subtype_mk _

variable (hW : ∀ W : ValuationSubring Ω, (∀ c : k₂, algebraMap k₂ Ω c ∈ W) → t₂ ∈ W →
    (∀ c : k₁, algebraMap k₁ Ω c ∈ W) ∧ t₁ ∈ W) (hH₁ : D₁.H ≤ D₁.HL)

include hW hH₁ in
/-- **Inertia elements of `U₂` are inertia elements of `U₁`.** -/
lemma hT_mem_S {σ : D₂.H} (hσ : (σ : Ω ≃ₐ[K₀ k₂ t₂] Ω) ∈ D₂.S) :
    ((hT D₁ D₂ hF σ : D₁.H) : Ω ≃ₐ[K₀ k₁ t₁] Ω) ∈ D₁.S := by
  obtain ⟨-, W, hk, htW, hI⟩ := hσ
  obtain ⟨hk₁, ht₁⟩ := hW W hk htW
  exact ⟨hH₁ (hT D₁ D₂ hF σ).2, W, hk₁, ht₁, fun a ha => hI a ha⟩

include hW hH₁ in
lemma kernel_le_comap_hT :
    GaloisPi1.kernel D₂.H D₂.S ≤ (GaloisPi1.kernel D₁.H D₁.S).comap (hT D₁ D₂ hF) := by
  have hS₂ : D₂.S ⊆ D₂.H := fun _ h => D₂.le h.1
  have hS₁ : D₁.S ⊆ D₁.H := fun _ h => D₁.le h.1
  rw [GaloisPi1.kernel_eq_topologicalClosure _ D₂.isClosed_H _ hS₂]
  haveI : (GaloisPi1.kernel D₁.H D₁.S).Normal := inferInstance
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
    ((GaloisPi1.isClosed_kernel D₁.H D₁.S).preimage (continuous_hT D₁ D₂ hF))
  intro s hs
  change hT D₁ D₂ hF s ∈ GaloisPi1.kernel D₁.H D₁.S
  rw [GaloisPi1.kernel_eq_topologicalClosure _ D₁.isClosed_H _ hS₁]
  exact Subgroup.le_topologicalClosure _
    (Subgroup.subset_normalClosure (hT_mem_S D₁ D₂ hF hW hH₁ hs))

/-- **The transition map `Π_{U₂} → Π_{U₁}`.** -/
noncomputable def piT : Pi D₂ →* Pi D₁ :=
  QuotientGroup.map _ _ (hT D₁ D₂ hF) (kernel_le_comap_hT D₁ D₂ hF hW hH₁)

@[simp]
lemma piT_mk (σ : D₂.H) : piT D₁ D₂ hF hW hH₁ (σ : Pi D₂) = (hT D₁ D₂ hF σ : Pi D₁) := rfl

lemma continuous_piT : Continuous (piT D₁ D₂ hF hW hH₁) := by
  change Continuous (QuotientGroup.map _ _ (hT D₁ D₂ hF) (kernel_le_comap_hT D₁ D₂ hF hW hH₁))
  rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
  exact QuotientGroup.continuous_mk.comp (continuous_hT D₁ D₂ hF)

/-- The inclusion `F₁ ⊆ F₂` of function fields. -/
noncomputable def fT : F D₁ →+* F D₂ where
  toFun x := ⟨x, hF x x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `F₂` as an `F₁`-algebra (not an instance: it depends on `hF`). -/
@[reducible] noncomputable def algebraFT : Algebra (F D₁) (F D₂) := (fT D₁ D₂ hF).toAlgebra

lemma isScalarTower_fT :
    letI := algebraFT D₁ D₂ hF
    IsScalarTower (F D₁) (F D₂) Ω :=
  letI := algebraFT D₁ D₂ hF
  IsScalarTower.of_algebraMap_eq fun _ => rfl

-- `Subtype.coe_mk` instead of `rfl`: the kernel would compare the predicates of `F₂` and `F₁`
@[simp]
lemma coe_fT (x : F D₁) : ((fT D₁ D₂ hF x : F D₂) : Ω) = x := by
  change ((⟨(x : Ω), hF x x.2⟩ : F D₂) : Ω) = x
  rw [Subtype.coe_mk]

variable [CharZero k₁] [CharZero k₂]

/-- The coefficients `Ẑ(1)_{F₁} → Ẑ(1)_{F₂}` (the identity at every level). -/
noncomputable abbrev zT : ZHatOne (F D₁) Ω →* ZHatOne (F D₂) Ω :=
  zHatRes (F D₁) (F D₂) Ω Ω

lemma zT_hT_smul (σ : D₂.H) (x : ZHatOne (F D₁) Ω) :
    zT D₁ D₂ (hT D₁ D₂ hF σ • x) = σ • zT D₁ D₂ x := by
  apply Subtype.ext
  funext i
  change muMap i.n Ω Ω ((hT D₁ D₂ hF σ : Ω ≃ₐ[K₀ k₁ t₁] Ω) •
      (x : ∀ j, Mu j.n Ω) (reindex (k := F D₁) i)) =
    (σ : Ω ≃ₐ[K₀ k₂ t₂] Ω) • muMap i.n Ω Ω ((x : ∀ j, Mu j.n Ω) (reindex (k := F D₁) i))
  apply Mu.ext
  apply Units.ext
  simp [AlgEquiv.smul_units_def]
  rfl

lemma zT_piT_smul (p : Pi D₂) (x : ZHatOne (F D₁) Ω) :
    zT D₁ D₂ (piT D₁ D₂ hF hW hH₁ p • x) = p • zT D₁ D₂ x := by
  induction p using QuotientGroup.induction_on with
  | H σ => exact zT_hT_smul D₁ D₂ hF σ x

/-- **The transition map `H¹(Π_{U₁}, Ẑ(1)) → H¹(Π_{U₂}, Ẑ(1))`.** -/
noncomputable def resT :
    ContH1 (Pi D₁) (ZHatOne (F D₁) Ω) →* ContH1 (Pi D₂) (ZHatOne (F D₂) Ω) :=
  ContH1.map (piT D₁ D₂ hF hW hH₁) (continuous_piT D₁ D₂ hF hW hH₁) (zT D₁ D₂)
    (continuous_zHatRes (F D₁) (F D₂) Ω Ω) (zT_piT_smul D₁ D₂ hF hW hH₁)

include hW in
lemma mem_chartRing_of_isIntegral {x : Ω} (hx : IsIntegral (A₀ k₁ t₁) x) :
    IsIntegral (A₀ k₂ t₂) x :=
  mem_chartRing_of_forall fun W hk ht =>
    Pi1.Orbifold.mem_of_isIntegral (hW W hk ht).1 (hW W hk ht).2 hx

include hW in
lemma isIntegral_fT {x : F D₁} (hx : IsIntegral (A₀ k₁ t₁) x) :
    IsIntegral (A₀ k₂ t₂) (fT D₁ D₂ hF x) := by
  haveI : IsScalarTower (A₀ k₁ t₁) (F D₁) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (A₀ k₂ t₂) (F D₂) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : IsIntegral (A₀ k₁ t₁) (x : Ω) :=
    hx.map (IsScalarTower.toAlgHom (A₀ k₁ t₁) (F D₁) Ω)
  have h2 : IsIntegral (A₀ k₂ t₂) (x : Ω) := mem_chartRing_of_isIntegral hW h1
  rw [← coe_fT D₁ D₂ hF x] at h2
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (A₀ k₂ t₂) (F D₂) Ω)
    (algebraMap (F D₂) Ω).injective).1 h2

/-- **Units of `U₁` are units of `U₂`.** -/
noncomputable def unitsT : units D₁ →* units D₂ where
  toFun u := ⟨Units.map (fT D₁ D₂ hF : F D₁ →* F D₂) u,
    isIntegral_fT D₁ D₂ hF hW u.2.1, by
      rw [← map_inv]
      exact isIntegral_fT D₁ D₂ hF hW u.2.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[simp]
lemma coe_unitsT (u : units D₁) :
    ((((unitsT D₁ D₂ hF hW u : units D₂) : (F D₂)ˣ) : F D₂) : Ω) =
      (((u : (F D₁)ˣ) : F D₁) : Ω) := by
  change ((fT D₁ D₂ hF ((u : (F D₁)ˣ) : F D₁) : F D₂) : Ω) = _
  exact coe_fT D₁ D₂ hF _

lemma toGalF_hT (σ : D₂.H) :
    letI := algebraFT D₁ D₂ hF
    haveI := isScalarTower_fT D₁ D₂ hF
    toGalF D₁ (hT D₁ D₂ hF σ) = galRestrict (F D₁) (F D₂) Ω Ω (toGalF D₂ σ) := by
  letI := algebraFT D₁ D₂ hF
  haveI := isScalarTower_fT D₁ D₂ hF
  ext x
  have := KummerTheory.algebraMap_galRestrict_apply (K := F D₁) (L := F D₂)
    (ΩK := Ω) (ΩL := Ω) (toGalF D₂ σ) x
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
  rw [this]
  rfl

/-- Restriction `H¹(H₁, Ẑ(1)) → H¹(H₂, Ẑ(1))` along `hT`. -/
noncomputable def resHT :
    ContH1 D₁.H (ZHatOne (F D₁) Ω) →* ContH1 D₂.H (ZHatOne (F D₂) Ω) :=
  ContH1.map (hT D₁ D₂ hF) (continuous_hT D₁ D₂ hF) (zT D₁ D₂)
    (continuous_zHatRes (F D₁) (F D₂) Ω Ω) (zT_hT_smul D₁ D₂ hF)

lemma inflZHat_resT (x : ContH1 (Pi D₁) (ZHatOne (F D₁) Ω)) :
    inflZHat D₂ (F D₂) (resT D₁ D₂ hF hW hH₁ x) = resHT D₁ D₂ hF (inflZHat D₁ (F D₁) x) := by
  induction x using ContH1.induction_on with
  | h c => rfl

lemma resHT_resZHat (X : ContH1 (Ω ≃ₐ[F D₁] Ω) (ZHatOne (F D₁) Ω)) :
    letI := algebraFT D₁ D₂ hF
    haveI := isScalarTower_fT D₁ D₂ hF
    resHT D₁ D₂ hF (resZHat D₁ (F D₁) X) =
      resZHat D₂ (F D₂) (restrictZHat (F D₁) (F D₂) Ω Ω X) := by
  letI := algebraFT D₁ D₂ hF
  haveI := isScalarTower_fT D₁ D₂ hF
  induction X using ContH1.induction_on with
  | h c =>
    simp only [resHT, resZHat, Curve.res, restrictZHat, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext σ
    simp only [ContH1.cocyclesMap_apply, toGalF_hT, MonoidHom.id_apply]

variable [IsSepClosed Ω]

set_option maxHeartbeats 1600000 in
-- the action instances of `inflation_injective` and of `inflZHat` are unified slowly
/-- **The transition maps are compatible with the Kummer maps**: `resT (κ_{U₁}(u)) = κ_{U₂}(u)`. -/
theorem resT_kummerMapZHat (u : units D₁) :
    resT D₁ D₂ hF hW hH₁ (kummerMapZHat D₁ u) = kummerMapZHat D₂ (unitsT D₁ D₂ hF hW u) := by
  letI := algebraFT D₁ D₂ hF
  haveI := isScalarTower_fT D₁ D₂ hF
  apply ContH1.inflation_injective (N := GaloisPi1.kernel D₂.H D₂.S) (fun _ _ => rfl)
  rw [inflation_kummerMapZHat, inflZHat_resT, inflation_kummerMapZHat]
  have hu : ((unitsT D₁ D₂ hF hW u : units D₂) : (F D₂)ˣ) =
      Units.map (algebraMap (F D₁) (F D₂) : F D₁ →* F D₂) (u : (F D₁)ˣ) := rfl
  simp only [hu,
    kummerZHat_restrict (ΩK := Ω) (ΩL := Ω)]
  exact resHT_resZHat D₁ D₂ hF _

end Transition

/-! ### The transition maps compose -/

section Compose

open CurvesJacobian

set_option linter.unusedSectionVars false

variable {k₁ k₂ k₃ Ω : Type u} [Field k₁] [Field k₂] [Field k₃] [Field Ω] [Algebra k₁ Ω]
  [Algebra k₂ Ω] [Algebra k₃ Ω] {t₁ t₂ t₃ : Ω} {D₁ : Pi1.Orbifold.GaloisData k₁ t₁}
  {D₂ : Pi1.Orbifold.GaloisData k₂ t₂} {D₃ : Pi1.Orbifold.GaloisData k₃ t₃}
  [IsGalois (K₀ k₁ t₁) Ω] [IsGalois (K₀ k₂ t₂) Ω] [IsGalois (K₀ k₃ t₃) Ω]
  {hF₁₂ : ∀ x ∈ F D₁, x ∈ F D₂} {hF₂₃ : ∀ x ∈ F D₂, x ∈ F D₃} {hF₁₃ : ∀ x ∈ F D₁, x ∈ F D₃}
  {hW₁₂ : ∀ W : ValuationSubring Ω, (∀ c : k₂, algebraMap k₂ Ω c ∈ W) → t₂ ∈ W →
    (∀ c : k₁, algebraMap k₁ Ω c ∈ W) ∧ t₁ ∈ W}
  {hW₂₃ : ∀ W : ValuationSubring Ω, (∀ c : k₃, algebraMap k₃ Ω c ∈ W) → t₃ ∈ W →
    (∀ c : k₂, algebraMap k₂ Ω c ∈ W) ∧ t₂ ∈ W}
  {hW₁₃ : ∀ W : ValuationSubring Ω, (∀ c : k₃, algebraMap k₃ Ω c ∈ W) → t₃ ∈ W →
    (∀ c : k₁, algebraMap k₁ Ω c ∈ W) ∧ t₁ ∈ W}
  {hH₁ : D₁.H ≤ D₁.HL} {hH₂ : D₂.H ≤ D₂.HL}

lemma hT_hT (σ : D₃.H) : hT D₁ D₂ hF₁₂ (hT D₂ D₃ hF₂₃ σ) = hT D₁ D₃ hF₁₃ σ :=
  Subtype.ext (AlgEquiv.ext fun _ => rfl)

lemma piT_piT (p : Pi D₃) :
    piT D₁ D₂ hF₁₂ hW₁₂ hH₁ (piT D₂ D₃ hF₂₃ hW₂₃ hH₂ p) = piT D₁ D₃ hF₁₃ hW₁₃ hH₁ p := by
  induction p using QuotientGroup.induction_on with
  | H σ => exact congrArg (fun h : D₁.H => (h : Pi D₁)) (hT_hT σ)

variable [CharZero k₁] [CharZero k₂] [CharZero k₃]

lemma zT_zT (x : ZHatOne (F D₁) Ω) : zT D₂ D₃ (zT D₁ D₂ x) = zT D₁ D₃ x := by
  apply Subtype.ext
  funext i
  apply Mu.ext
  apply Units.ext
  rfl

/-- **The transition maps compose**: the stages form a direct system. -/
theorem resT_resT (x : ContH1 (Pi D₁) (ZHatOne (F D₁) Ω)) :
    resT D₂ D₃ hF₂₃ hW₂₃ hH₂ (resT D₁ D₂ hF₁₂ hW₁₂ hH₁ x) = resT D₁ D₃ hF₁₃ hW₁₃ hH₁ x := by
  induction x using ContH1.induction_on with
  | h c =>
    simp only [resT, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext σ
    simp only [ContH1.cocyclesMap_apply]
    rw [piT_piT (hF₁₃ := hF₁₃) (hW₁₃ := hW₁₃), zT_zT]

lemma unitsT_unitsT (u : units D₁) :
    unitsT D₂ D₃ hF₂₃ hW₂₃ (unitsT D₁ D₂ hF₁₂ hW₁₂ u) = unitsT D₁ D₃ hF₁₃ hW₁₃ u := by
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  rw [coe_unitsT, coe_unitsT, coe_unitsT]

end Compose

/-! ### The maps of `NFColimit` and `NFShrink` are transition maps -/

section Compare

open CurvesJacobian

set_option linter.unusedSectionVars false

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] (hH : D.H ≤ D.HL)

section ConstExt

variable (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K]

/-- Places of `Ω` centred on `U_K` are centred on `U`. -/
lemma hW_constExt (W : ValuationSubring Ω) (hK : ∀ c : K, algebraMap K Ω c ∈ W) (ht : t ∈ W) :
    (∀ c : k, algebraMap k Ω c ∈ W) ∧ t ∈ W :=
  ⟨fun c => by rw [IsScalarTower.algebraMap_apply k K Ω]; exact hK _, ht⟩

variable [IsAlgClosed Ω]

lemma piRes_eq_piT (p : Pi (constExt K D)) :
    piRes K D p = piT D (constExt K D) (fun _ hx => le_F_constExt D hx) (hW_constExt K) hH p := by
  induction p using QuotientGroup.induction_on with
  | H σ => exact congrArg (fun h : D.H => (h : Pi D)) (Subtype.ext (AlgEquiv.ext fun _ => rfl))

/-- `resKH1` (`Thm19/NFColimit.lean`) is the transition map `U → U_K`. -/
theorem resKH1_eq_resT (x : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    resKH1 K D x =
      resT D (constExt K D) (fun _ hx => le_F_constExt D hx) (hW_constExt K) hH x := by
  induction x using ContH1.induction_on with
  | h c =>
    simp only [resKH1, resT, ContH1.map_mk]
    congr 1

lemma unitsRes_eq_unitsT (u : units D) :
    unitsRes K D u =
      unitsT D (constExt K D) (fun _ hx => le_F_constExt D hx) (hW_constExt K) u := by
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  rw [coe_unitsRes, coe_unitsT]

end ConstExt

section Shrink

variable {t' : Ω} (ht' : t' ∈ D.L) (htr' : Transcendental k t') [IsGalois (K₀ k t') Ω]
  (htV : t ∈ chartRing k t')

include htV in
/-- Places of `Ω` centred on `V` are centred on `U`. -/
lemma hW_V (W : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : t' ∈ W) :
    (∀ c : k, algebraMap k Ω c ∈ W) ∧ t ∈ W :=
  ⟨hk, mem_of_mem_V htV hk hW⟩

lemma piV_eq_piT (p : Pi (VData D ht' htr')) :
    piV D ht' htr' hH htV p =
      piT D (VData D ht' htr') (fun _ hx => mem_F_V D ht' htr' hx) (hW_V htV) hH p := by
  induction p using QuotientGroup.induction_on with
  | H σ => exact congrArg (fun h : D.H => (h : Pi D)) (Subtype.ext (AlgEquiv.ext fun _ => rfl))

/-- `resV` (`Thm19/NFShrink.lean`) is the transition map `U → V`. -/
theorem resV_eq_resT (x : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    resV D ht' htr' hH htV x =
      resT D (VData D ht' htr') (fun _ hx => mem_F_V D ht' htr' hx) (hW_V htV) hH x := by
  induction x using ContH1.induction_on with
  | h c =>
    simp only [resV, resT, ContH1.map_mk]
    congr 1

end Shrink

end Compare

/-! ### The stages of the colimit: `V ⊆ U_K` for algebraic `K` and coordinates `t′` -/

section Stage

open CurvesJacobian

set_option linter.unusedSectionVars false

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- The function field `L_K` of `U_K`, read off from `D`: the elements fixed by every element of
`H_L` fixing `K`. -/
lemma mem_L_constExt_iff (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K] {x : Ω} :
    x ∈ (constExt K D).L ↔ ∀ σ : Ω ≃ₐ[K₀ k t] Ω, σ ∈ D.HL →
      (∀ c : K, σ (algebraMap K Ω c) = algebraMap K Ω c) → σ x = x := by
  rw [Pi1.Orbifold.GaloisData.L, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h σ hσ hK
    obtain ⟨σ', rfl⟩ := exists_resK_eq hK
    exact h σ' ((mem_constExt_HL D).2 hσ)
  · intro h σ' hσ'
    exact h (resK k K t σ') ((mem_constExt_HL D).1 hσ') (resK_fix σ')

lemma L_constExt_mono {K K' : IntermediateField k Ω} [Algebra.IsAlgebraic k K]
    [Algebra.IsAlgebraic k K'] (hKK' : K ≤ K') {x : Ω} (hx : x ∈ (constExt K D).L) :
    x ∈ (constExt K' D).L := by
  rw [mem_L_constExt_iff] at hx ⊢
  exact fun σ hσ hK' => hx σ hσ fun c => hK' ⟨c, hKK' c.2⟩

lemma le_L_constExt (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K] {x : Ω}
    (hx : x ∈ F D) : x ∈ (constExt K D).L := by
  rw [mem_L_constExt_iff]
  exact fun σ hσ _ => (IntermediateField.mem_fixedField_iff _ _).1 hx σ (D.le hσ)

lemma F_constExt_le_L (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K] {x : Ω}
    (hx : x ∈ F (constExt K D)) : x ∈ (constExt K D).L := by
  rw [Pi1.Orbifold.GaloisData.L, IntermediateField.mem_fixedField_iff]
  exact fun σ hσ => (IntermediateField.mem_fixedField_iff _ _).1 hx σ ((constExt K D).le hσ)

lemma constExt_H_le (hH : D.H ≤ D.HL) (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K] :
    (constExt K D).H ≤ (constExt K D).HL :=
  fun _ hσ => (mem_constExt_HL D).2 (hH ((mem_constExt_H D).1 hσ))

lemma t_mem_L_constExt (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K] :
    t ∈ (constExt K D).L :=
  (constExt K D).L.algebraMap_mem ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩

variable (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K] {t' : Ω}
  (ht' : t' ∈ (constExt K D).L) (htr' : Transcendental K t')

/-- **A stage of the colimit**: the open `V` of the coordinate `t′` of the base change `U_K`
(the coordinate ring of `V` is the integral closure of `K[t′]` in `L_K`). -/
noncomputable abbrev stage : Pi1.Orbifold.GaloisData K t' := newData (constExt K D) ht' htr'

include D ht' htr' in
lemma isGalois_stage : IsGalois (K₀ K t') Ω := isGalois_K₀_V (constExt K D) ht' htr'

lemma stage_H_le : (stage D K ht' htr').H ≤ (stage D K ht' htr').HL := le_rfl

lemma mem_F_stage_iff [IsGalois (K₀ K t') Ω] {x : Ω} :
    x ∈ F (stage D K ht' htr') ↔ x ∈ (constExt K D).L :=
  mem_newData_L (constExt K D) ht' htr' x

/-- `F_U ⊆ F_V`. -/
lemma le_F_stage [IsGalois (K₀ K t') Ω] {x : Ω} (hx : x ∈ F D) : x ∈ F (stage D K ht' htr') :=
  (mem_F_stage_iff D K ht' htr').2 (le_L_constExt D K hx)

/-- `F_{U_K} ⊆ F_V`. -/
lemma le_F_stage_of_constExt [IsGalois (K₀ K t') Ω] {x : Ω} (hx : x ∈ F (constExt K D)) :
    x ∈ F (stage D K ht' htr') :=
  (mem_F_stage_iff D K ht' htr').2 (F_constExt_le_L D K hx)

variable {D K ht' htr'}

/-- Places centred on the stage `V ⊆ U_K` are centred on `U` (if `t` is regular on `V`). -/
lemma hW_stage (htV : t ∈ chartRing K t') (W : ValuationSubring Ω)
    (hK : ∀ c : K, algebraMap K Ω c ∈ W) (hW : t' ∈ W) :
    (∀ c : k, algebraMap k Ω c ∈ W) ∧ t ∈ W :=
  hW_constExt K W hK (mem_of_mem_chartRing W hK hW htV)

/-- Places centred on `V` are centred on `U_K`. -/
lemma hW_stage_constExt (htV : t ∈ chartRing K t') (W : ValuationSubring Ω)
    (hK : ∀ c : K, algebraMap K Ω c ∈ W) (hW : t' ∈ W) :
    (∀ c : K, algebraMap K Ω c ∈ W) ∧ t ∈ W :=
  ⟨hK, mem_of_mem_chartRing W hK hW htV⟩

/-- Places centred on the stage `(K′, t″)` are centred on the stage `(K, t′)` if `K ⊆ K′` and
`t′` is regular on the open of `t″`. -/
lemma hW_stage_mono {K' : IntermediateField k Ω} (hKK' : K ≤ K') {t'' : Ω}
    (ht'' : t' ∈ chartRing K' t'') (W : ValuationSubring Ω)
    (hK' : ∀ c : K', algebraMap K' Ω c ∈ W) (hW : t'' ∈ W) :
    (∀ c : K, algebraMap K Ω c ∈ W) ∧ t' ∈ W :=
  ⟨fun c => hK' ⟨c, hKK' c.2⟩, mem_of_mem_chartRing W hK' hW ht''⟩

variable (D) in
/-- `F_V ⊆ F_{V′}` for stages `(K, t′) ≤ (K′, t″)`. -/
lemma F_stage_mono {K' : IntermediateField k Ω} [Algebra.IsAlgebraic k K'] (hKK' : K ≤ K')
    {t'' : Ω} (ht''L : t'' ∈ (constExt K' D).L) (htr'' : Transcendental K' t'')
    [IsGalois (K₀ K t') Ω] [IsGalois (K₀ K' t'') Ω] {x : Ω}
    (hx : x ∈ F (stage D K ht' htr')) : x ∈ F (stage D K' ht''L htr'') :=
  (mem_F_stage_iff D K' ht''L htr'').2
    (L_constExt_mono D hKK' ((mem_F_stage_iff D K ht' htr').1 hx))

variable (D K) in
/-- **Directedness**: two coordinates `t₁, t₂ ∈ L_K` are regular on the open of a third
coordinate `t₃ = t₁ + c t₂` (`c ∈ K`). -/
theorem exists_stage_ge (hH : D.H ≤ D.HL) {t₁ t₂ : Ω} (ht₁ : t₁ ∈ (constExt K D).L)
    (htr₁ : Transcendental K t₁) (ht₂ : t₂ ∈ (constExt K D).L) :
    ∃ t₃ : Ω, t₃ ∈ (constExt K D).L ∧ Transcendental K t₃ ∧ t₁ ∈ chartRing K t₃ ∧
      t₂ ∈ chartRing K t₃ := by
  have hH' := constExt_H_le D hH K
  have hLF : ∀ {x : Ω}, x ∈ (constExt K D).L → x ∈ F (constExt K D) := fun {x} hx => by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun σ hσ => (IntermediateField.mem_fixedField_iff _ _).1 hx σ (hH' hσ)
  obtain ⟨c, hc⟩ := exists_smul_add_mem_imp (constExt K D) ⟨t₁, hLF ht₁⟩ ⟨t₂, hLF ht₂⟩
  set z : F (constExt K D) := ⟨t₁, hLF ht₁⟩ + algebraMap K (F (constExt K D)) c * ⟨t₂, hLF ht₂⟩
  have htr : Transcendental K (z : Ω) := by
    intro halg
    apply htr₁
    have hall : ∀ W : ValuationSubring Ω, (∀ c : K, algebraMap K Ω c ∈ W) → t₁ ∈ W :=
      fun W hk => (hc W hk (KummerTheory.Curve.mem_of_isIntegral hk halg.isIntegral)).1
    have hmem : t₁ ∈ (integralClosure K Ω).toSubring := by
      rw [Subring.eq_iInf_of_isIntegrallyClosedIn (R := (integralClosure K Ω).toSubring),
        Subring.mem_iInf]
      intro V
      exact hall V.1 fun c => V.2 (Subalgebra.algebraMap_mem _ c)
    exact ((mem_integralClosure_iff K Ω).1 hmem).isAlgebraic
  refine ⟨z, mem_L_of_mem_F_shrink (constExt K D) z.2, htr, ?_, ?_⟩
  · exact mem_chartRing_of_forall fun W hk hW => (hc W hk hW).1
  · exact mem_chartRing_of_forall fun W hk hW => (hc W hk hW).2

variable (D K) in
/-- **Cofinality of the stages**: every unit `f` of the function field of `U_K` is a unit on a
stage `V ⊆ U_K` (with `t` regular on `V`). -/
theorem exists_stage_units (f : (F (constExt K D))ˣ) :
    ∃ (t' : Ω) (ht' : t' ∈ (constExt K D).L) (htr' : Transcendental K t'),
      t ∈ chartRing K t' ∧ ∃ v : units (stage D K ht' htr'),
        (((v : (F (stage D K ht' htr'))ˣ) : F (stage D K ht' htr')) : Ω) =
          ((f : F (constExt K D)) : Ω) := by
  obtain ⟨t', ht', htr', htV, hf, hf'⟩ := exists_coordinate_V (constExt K D) f
  exact ⟨t', ht', htr', htV, exists_units_V ht' htr' f hf hf'⟩

end Stage

/-! ### Injectivity in the colimit -/

section Injective

open CurvesJacobian

set_option linter.unusedSectionVars false

variable {k₁ k₂ Ω : Type u} [Field k₁] [Field k₂] [Field Ω] [Algebra k₁ Ω] [Algebra k₂ Ω]
  {t₁ t₂ : Ω} {D₁ : Pi1.Orbifold.GaloisData k₁ t₁} {D₂ : Pi1.Orbifold.GaloisData k₂ t₂}
  [IsGalois (K₀ k₁ t₁) Ω] [IsGalois (K₀ k₂ t₂) Ω] [CharZero k₁] [CharZero k₂] [IsSepClosed Ω]
  {hF : ∀ x ∈ F D₁, x ∈ F D₂}
  {hW : ∀ W : ValuationSubring Ω, (∀ c : k₂, algebraMap k₂ Ω c ∈ W) → t₂ ∈ W →
    (∀ c : k₁, algebraMap k₁ Ω c ∈ W) ∧ t₁ ∈ W} {hH₁ : D₁.H ≤ D₁.HL}

lemma unitsT_injective : Function.Injective (unitsT D₁ D₂ hF hW) := by
  intro u v huv
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  rw [← coe_unitsT D₁ D₂ hF hW u, ← coe_unitsT D₁ D₂ hF hW v, huv]

/-- **A unit whose Kummer class dies at a later stage is trivial** (Prop 1.6 (i) at the later
stage: `k₂` Kummer-faithful and algebraically closed in the function field of `U₂`). -/
theorem eq_one_of_resT_kummerMapZHat_eq_one
    (hk₂ : ∀ x : F D₂, IsAlgebraic k₂ x → x ∈ Set.range (algebraMap k₂ (F D₂)))
    (hkf₂ : IsKummerFaithfulGm k₂) {u : units D₁}
    (hu : resT D₁ D₂ hF hW hH₁ (kummerMapZHat D₁ u) = 1) : u = 1 := by
  rw [resT_kummerMapZHat] at hu
  apply unitsT_injective (hF := hF) (hW := hW)
  rw [map_one]
  exact kummerMapZHat_injective hk₂ hkf₂ (hu.trans (map_one _).symm)

end Injective

section StageInjective

open CurvesJacobian

set_option linter.unusedSectionVars false

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [Algebra.IsAlgebraic k K] {t' : Ω}
  {ht' : t' ∈ (constExt K D).L} {htr' : Transcendental K t'} [IsGalois (K₀ K t') Ω]

/-- **`K` is algebraically closed in the function field of a stage** `V ⊆ U_K` if `k` is
algebraically closed in that of `U` (geometric connectedness is stable under base change). -/
theorem mem_range_of_isAlgebraic_stage (hH : D.H ≤ D.HL)
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (x : F (stage D K ht' htr')) (hx : IsAlgebraic K x) :
    x ∈ Set.range (algebraMap K (F (stage D K ht' htr'))) := by
  have hxL : (x : Ω) ∈ (constExt K D).L := (mem_F_stage_iff D K ht' htr').1 x.2
  have hyK : IsAlgebraic K (x : Ω) := by
    haveI : IsScalarTower K (F (stage D K ht' htr')) Ω :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact hx.algHom (IsScalarTower.toAlgHom K (F (stage D K ht' htr')) Ω)
  have hyk : IsAlgebraic k (x : Ω) := hyK.restrictScalars k
  obtain ⟨c, hc⟩ := exists_eq_of_forall_fix_constExt (K := K)
    ⟨(x : Ω), mem_algebraicClosure_iff.2 hyk⟩ fun g hg => by
      obtain ⟨h, rfl⟩ := hToGk_surjective D hkF g
      have hfixK : ∀ c : K, (h : Ω ≃ₐ[K₀ k t] Ω) (algebraMap K Ω c) = algebraMap K Ω c := by
        intro c
        rw [← algebraMap_hToGk_apply D h ⟨_, algebraMap_mem_kbar c⟩, hg c]
        rfl
      apply Subtype.ext
      change algebraMap (kbar k Ω) Ω (hToGk D h ⟨(x : Ω), _⟩) = (x : Ω)
      rw [algebraMap_hToGk_apply]
      exact (mem_L_constExt_iff D K).1 hxL h (hH h.2) hfixK
  exact ⟨c, Subtype.ext hc⟩

/-- **[AbsTopIII] Prop 1.6 (i) at every stage over a number field**: for `k` a number field and
`K / k` finite, the Kummer map of every stage `V ⊆ U_K` is injective. -/
theorem kummerMapZHat_stage_injective_numberField [NumberField k] [FiniteDimensional k K]
    (hH : D.H ≤ D.HL)
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D))) :
    Function.Injective (kummerMapZHat (stage D K ht' htr')) := by
  haveI : NumberField K := NumberField.of_module_finite k K
  exact kummerMapZHat_injective_of_numberField (mem_range_of_isAlgebraic_stage hH hkF)

end StageInjective

/-! ### Thm 1.9 (d) in the double colimit -/

section Main

open CurvesJacobian

set_option linter.unusedSectionVars false

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

set_option maxHeartbeats 4000000 in
-- `ContH1` and unit terms over the stages unify slowly
/-- **[AbsTopIII] Thm 1.9 (d) in the colimit over the stages**: if `η ∈ P_U` and
`η^M = κ_U(w)` with `M > 0`, there is a finite extension `k ⊆ K ⊆ Ω` such that the image of `η`
at the stage `(K, t)` (`U_K` itself, as a stage) is the Kummer class `κ(v)` of an `M`-th root
`v` of `w`; by `resT_resT` and `resT_kummerMapZHat` the same then holds at every later stage. -/
theorem exists_stage_resT_eq_kummerMapZHat (hH : D.H ≤ D.HL) (hJ : IsKummerFaithfulJac D)
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    {η : ContH1 (Pi D) (ZHatOne (F D) Ω)} (hη : η ∈ PU D) {M : ℕ} (hM : 0 < M)
    {w : units D} (hw : η ^ M = kummerMapZHat D w) :
    ∃ (K : IntermediateField k Ω) (_ : FiniteDimensional k K)
      (v : units (stage D K (t_mem_L_constExt D K) (transcendental_K D))),
      resT D (stage D K (t_mem_L_constExt D K) (transcendental_K D))
          (fun _ hx => le_F_stage D K _ _ hx) (hW_stage (self_mem_chartRing K t)) hH η =
        kummerMapZHat (stage D K (t_mem_L_constExt D K) (transcendental_K D)) v ∧
      v ^ M = unitsT D (stage D K (t_mem_L_constExt D K) (transcendental_K D))
        (fun _ hx => le_F_stage D K _ _ hx) (hW_stage (self_mem_chartRing K t)) w := by
  obtain ⟨K, hfin, v, hv, hvM⟩ := exists_finite_resKH1_eq_kummerMapZHat hJ hkF hη hM hw
  refine ⟨K, hfin, unitsT (constExt K D) (stage D K (t_mem_L_constExt D K) (transcendental_K D))
    (fun _ hx => le_F_stage_of_constExt D K _ _ hx)
    (hW_stage_constExt (self_mem_chartRing K t)) v, ?_, ?_⟩
  · rw [← resT_resT (D₂ := constExt K D) (hF₁₂ := fun _ hx => le_F_constExt D hx)
      (hW₁₂ := hW_constExt K) (hF₂₃ := fun _ hx => le_F_stage_of_constExt D K _ _ hx)
      (hW₂₃ := hW_stage_constExt (self_mem_chartRing K t)) (hH₂ := constExt_H_le D hH K),
      ← resKH1_eq_resT D hH K, hv, resT_kummerMapZHat]
  · rw [← map_pow, hvM, unitsRes_eq_unitsT, unitsT_unitsT]

end Main

end Iut.Reconstruction.Thm19
