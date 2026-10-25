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
  transition maps;
* **cofinality**: `exists_smul_add_mem_imp` (for `a, b ∈ F` some `a + c b`, `c ∈ k`, has a pole
  wherever `a` or `b` has one: at each place at most one `c` fails, and only finitely many places
  matter, weil-curves `Place.finite_setOf_notMem`), hence **`exists_coordinate_V`**: every unit `f`
  of the function field is regular and invertible on the open `V` of a coordinate
  `t′ = t + c₂ (f + c₁ f⁻¹)` with `t` regular on `V`, and **`exists_units_V`**: `f` is then a unit
  of `V`. So the Kummer classes `κ_V(f)` of all `f ∈ F^×` live in the colimit over `V`.
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

section Cofinal

open CurvesJacobian

set_option linter.unusedSectionVars false

/-- An element lying in every valuation subring of `Ω` containing `k` and `t'` lies in the
integral closure of `k[t']`. -/
lemma mem_chartRing_of_forall {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {t' y : Ω}
    (h : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → t' ∈ W → y ∈ W) :
    y ∈ chartRing k t' := by
  change y ∈ (chartRing k t').toSubring
  rw [Subring.eq_iInf_of_isIntegrallyClosedIn (R := (chartRing k t').toSubring), Subring.mem_iInf]
  intro V
  exact h V.1 (fun c => V.2 (algebraMap_mem_chartRing t' c)) (V.2 (self_mem_chartRing k t'))

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

/-- **Choosing a coordinate with prescribed poles**: for `a, b ∈ F` there is `λ ∈ k` such that
every place `W ⊇ k` of `Ω` containing `a + λ b` contains `a` and `b` (at each place of `F` with a
pole of `a` or `b` at most one `λ` fails, and there are finitely many such places). -/
theorem exists_smul_add_mem_imp (a b : F D) :
    ∃ c : k, ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) →
      (((a + algebraMap k (F D) c * b : F D) : Ω) ∈ W) → (a : Ω) ∈ W ∧ (b : Ω) ∈ W := by
  classical
  set bad : Set k := {c | ∃ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) ∧
    ((a + algebraMap k (F D) c * b : F D) : Ω) ∈ W ∧ ¬ ((a : Ω) ∈ W ∧ (b : Ω) ∈ W)}
  -- the place of `F` under the chosen `W`
  have hplace : ∀ c ∈ bad, ∃ P : Place k (F D), ((a + algebraMap k (F D) c * b : F D) ∈ P.1) ∧
      ¬ (a ∈ P.1 ∧ b ∈ P.1) := by
    rintro c ⟨W, hk, hW, hab⟩
    refine ⟨⟨W.comap (algebraMap (F D) Ω), ?_, fun c' => ?_⟩, hW, hab⟩
    · intro htop
      apply hab
      constructor
      · exact (show a ∈ W.comap (algebraMap (F D) Ω) by rw [htop]; trivial)
      · exact (show b ∈ W.comap (algebraMap (F D) Ω) by rw [htop]; trivial)
    · change algebraMap (F D) Ω (algebraMap k (F D) c') ∈ W
      rw [← IsScalarTower.algebraMap_apply]
      exact hk c'
  choose! P hP using hplace
  have hinj : Set.InjOn P bad := by
    intro c hc c' hc' hcc
    by_contra hne
    have h1 := (hP c hc).1
    have h2 := (hP c' hc').1
    rw [hcc] at h1
    have hsub : algebraMap k (F D) (c - c') * b ∈ (P c').1 := by
      have := (P c').1.sub_mem h1 h2
      rwa [add_sub_add_left_eq_sub, ← sub_mul, ← map_sub] at this
    have hunit : (algebraMap k (F D) (c - c'))⁻¹ ∈ (P c').1 := by
      rw [← map_inv₀]
      exact (P c').2.2 _
    have hb : b ∈ (P c').1 := by
      have := mul_mem hunit hsub
      rwa [← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).2 (sub_ne_zero.2 hne)), one_mul]
        at this
    have ha : a ∈ (P c').1 := by
      have := (P c').1.sub_mem h2 (mul_mem ((P c').2.2 c') hb)
      rwa [add_sub_cancel_right] at this
    exact (hP c' hc').2 ⟨ha, hb⟩
  have hfin : bad.Finite := by
    refine Set.Finite.of_finite_image ?_ hinj
    refine ((Place.finite_setOf_notMem (k := k) a).union
      (Place.finite_setOf_notMem (k := k) b)).subset ?_
    rintro _ ⟨c, hc, rfl⟩
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact (hP c hc).2 h
  obtain ⟨c, hc⟩ := hfin.infinite_compl.nonempty
  exact ⟨c, fun W hk hW => of_not_not fun hab => hc ⟨W, hk, hW, hab⟩⟩

lemma mem_L_of_mem_F_shrink {x : Ω} (hx : x ∈ F D) : x ∈ D.L := by
  rw [Pi1.Orbifold.GaloisData.L, IntermediateField.mem_fixedField_iff]
  rw [IntermediateField.mem_fixedField_iff] at hx
  exact fun σ hσ => hx σ (D.le hσ)

/-- **Cofinality of the opens `V`**: for every unit `f` of the function field there is a
coordinate `t′ ∈ L`, transcendental over `k`, such that `t`, `f` and `f⁻¹` are regular on the
open `V` of `t′` (integral over `k[t′]`): `f` is a unit on some open `V ⊆ U`. -/
theorem exists_coordinate_V (f : (F D)ˣ) :
    ∃ t' : Ω, t' ∈ D.L ∧ Transcendental k t' ∧ t ∈ chartRing k t' ∧
      ((f : F D) : Ω) ∈ chartRing k t' ∧ (((f⁻¹ : (F D)ˣ) : F D) : Ω) ∈ chartRing k t' := by
  obtain ⟨c₁, h₁⟩ := exists_smul_add_mem_imp D (f : F D) ((f⁻¹ : (F D)ˣ) : F D)
  obtain ⟨c₂, h₂⟩ := exists_smul_add_mem_imp D (tF D)
    ((f : F D) + algebraMap k (F D) c₁ * ((f⁻¹ : (F D)ˣ) : F D))
  set z : F D := tF D + algebraMap k (F D) c₂ *
    ((f : F D) + algebraMap k (F D) c₁ * ((f⁻¹ : (F D)ˣ) : F D)) with hz
  have key : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → (z : Ω) ∈ W →
      t ∈ W ∧ ((f : F D) : Ω) ∈ W ∧ (((f⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W := by
    intro W hk hW
    obtain ⟨ht, hz₁⟩ := h₂ W hk hW
    obtain ⟨hf, hf'⟩ := h₁ W hk hz₁
    exact ⟨ht, hf, hf'⟩
  have htr' : Transcendental k (z : Ω) := by
    intro halg
    apply D.transcendental
    have hall : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → t ∈ W :=
      fun W hk => (key W hk (KummerTheory.Curve.mem_of_isIntegral hk halg.isIntegral)).1
    have hmem : t ∈ (integralClosure k Ω).toSubring := by
      rw [Subring.eq_iInf_of_isIntegrallyClosedIn (R := (integralClosure k Ω).toSubring),
        Subring.mem_iInf]
      intro V
      exact hall V.1 fun c => V.2 (Subalgebra.algebraMap_mem _ c)
    exact ((mem_integralClosure_iff k Ω).1 hmem).isAlgebraic
  refine ⟨z, mem_L_of_mem_F_shrink D z.2, htr', ?_, ?_, ?_⟩
  · exact mem_chartRing_of_forall fun W hk hW => (key W hk hW).1
  · exact mem_chartRing_of_forall fun W hk hW => (key W hk hW).2.1
  · exact mem_chartRing_of_forall fun W hk hW => (key W hk hW).2.2

variable {D} {t' : Ω} (ht' : t' ∈ D.L) (htr' : Transcendental k t')

attribute [local instance] algebraFV

lemma isIntegral_fV_of_mem_chartRing (x : F D) (hx : (x : Ω) ∈ chartRing k t') :
    haveI := isGalois_K₀_V D ht' htr'
    IsIntegral (A₀ k t') (algebraMap (F D) (F (VData D ht' htr')) x) := by
  haveI := isGalois_K₀_V D ht' htr'
  haveI : IsScalarTower (A₀ k t') (F (VData D ht' htr')) Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h3 : IsIntegral (A₀ k t') (x : Ω) := hx
  rw [← coe_algebraMap_fV D ht' htr' x] at h3
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (A₀ k t') (F (VData D ht' htr')) Ω)
    (algebraMap (F (VData D ht' htr')) Ω).injective).1 h3

/-- **`f` is a unit on `V`** once `f` and `f⁻¹` are regular on `V`. -/
theorem exists_units_V (f : (F D)ˣ) (hf : ((f : F D) : Ω) ∈ chartRing k t')
    (hf' : (((f⁻¹ : (F D)ˣ) : F D) : Ω) ∈ chartRing k t') :
    ∃ v : units (VData D ht' htr'),
      (((v : (F (VData D ht' htr'))ˣ) : F (VData D ht' htr')) : Ω) = ((f : F D) : Ω) := by
  haveI := isGalois_K₀_V D ht' htr'
  refine ⟨⟨Units.map (algebraMap (F D) (F (VData D ht' htr')) :
      F D →* F (VData D ht' htr')) f, isIntegral_fV_of_mem_chartRing ht' htr' _ hf, ?_⟩, ?_⟩
  · rw [← map_inv]
    exact isIntegral_fV_of_mem_chartRing ht' htr' _ hf'
  · change ((algebraMap (F D) (F (VData D ht' htr')) (f : F D) : F (VData D ht' htr')) : Ω) = _
    exact coe_algebraMap_fV D ht' htr' _

end Cofinal

end Iut.Reconstruction.Thm19
