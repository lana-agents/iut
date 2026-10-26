/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.StageNF
import CurvesJacobian.Kummer.JacobianLocalField

/-!
# [AbsTopIII] Thm 1.9 (d): Kummer-faithfulness of the Jacobian at the stages

[AbsTopIII] Prop 1.8 (i) ("if") uses Prop 1.6 (iii), i.e. `⋂_N N · J(k′) = 0` for the field of
constants `k′` of the curve to which it is applied. Thm 1.9 (d) applies it to the stages
`V ⊆ Z ×_{k_Z} k′` for finite extensions `k′` ("a finite extension of a sub-`p`-adic field is
sub-`p`-adic", [AbsTopIII] Rem 1.5.4 (i), T3 l.1909–1919). In the Galois model the stage
`s.data` (`Thm19/NFDirectLimit.lean`) has its own `Pic(F K̄)` with its own action; here:

* **semilinear transport of divisor class groups**: a ring isomorphism `e : K ≃+* K′` of function
  fields mapping the field of constants `κ` onto `κ′` induces `placeMapS`, `ord_placeMapS`
  (orders are preserved) and **`picEquivS : Pic(K) ≃+ Pic(K′)`**, compatible with the actions
  of semilinear automorphisms (`picEquivS_picMap`);
* `fStageEquiv s : F K̄ (stage) ≃+* F k̄ (U)` (the identity of `Ω`, `mem_F_baseChange_stage_iff`),
  and **`picStageEquiv s`**; an element `h ∈ H` fixing `K` lifts to the stage
  (`exists_stage_lift`), so `picStageEquiv` maps `Pic^{G_K}` of the stage into the classes fixed
  by `H_K = {h ∈ H | h fixes K}` (`picStageEquiv_mem_inv`);
* **`isKummerFaithfulJac_stage`**: if `⋂_N N · Pic(F k̄)^{H_K} = 0` (`IsDivFreeOver D K`), then
  `IsKummerFaithfulJac s.data` for every stage `s` over `K`;
* for a curve `X` over `k` with a rational point `σ` (Galois model `curveGaloisData k hτ`):
  `JacDivFree.of_ext'` (descent of `⋂_N N · J = 0` along `J(K) ↪ J(L)` for `k ⊆ K ⊆ L`),
  `jacDivFree_numberField'` (`⋂_N N · J(K) = 0` for every number field `K ⊇ k`, through a local
  field containing `K`, curves-jacobian `jacDivFree_of_properSpace`), **`isDivFreeOver_curve`**
  (`J(K) ≅ J(k̄)^{G_K}`, curves-jacobian `jacPointsEquivInv`, and the `G_k`-equivariant bridge
  `picPsi`), and **`isKummerFaithfulJac_stage_curve_numberField`**: every stage of the Galois
  model of a curve over a number field is Kummer-faithful for its Jacobian.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

open CurvesJacobian StageIdx

set_option linter.unusedSectionVars false

/-! ### Semilinear transport of places, divisors and `Pic` -/

section Semilinear

variable {κ κ' K K' : Type*} [Field κ] [Field κ'] [Field K] [Field K'] [Algebra κ K]
  [Algebra κ' K'] (e : K ≃+* K')

/-- `e` maps the field of constants `κ` into `κ′`. -/
def MapsConst (e : K ≃+* K') (κ κ' : Type*) [Field κ] [Field κ'] [Algebra κ K]
    [Algebra κ' K'] : Prop :=
  ∀ c : κ, ∃ c' : κ', e (algebraMap κ K c) = algebraMap κ' K' c'

variable {e}

/-- The place `e(P)` of `K′` (valuation ring `e(O_P)`), for `e⁻¹` mapping `κ′` into `κ`. -/
def placeMapS (he : MapsConst e.symm κ' κ) (P : Place κ K) : Place κ' K' :=
  ⟨P.1.comap e.symm.toRingHom, fun h ↦ P.ne_top (eq_top_iff.2 fun x _ ↦ by
      have : e x ∈ P.1.comap e.symm.toRingHom := h ▸ ValuationSubring.mem_top _
      simpa using this),
    fun c ↦ by
      change e.symm (algebraMap κ' K' c) ∈ P.1
      obtain ⟨c', hc'⟩ := he c
      rw [hc']
      exact P.algebraMap_mem c'⟩

lemma mem_placeMapS (he : MapsConst e.symm κ' κ) (P : Place κ K) (y : K') :
    y ∈ (placeMapS he P).1 ↔ e.symm y ∈ P.1 := Iff.rfl

lemma mem_placeMapS_apply (he : MapsConst e.symm κ' κ) (P : Place κ K) (x : K) :
    e x ∈ (placeMapS he P).1 ↔ x ∈ P.1 := by
  rw [mem_placeMapS, RingEquiv.symm_apply_apply]

variable [PerfectField κ] [IsFunctionField κ K] [PerfectField κ'] [IsFunctionField κ' K']

/-- Units at `P` map to units at `e(P)`. -/
lemma ord_placeMapS_of_ord_eq_zero (he : MapsConst e.symm κ' κ) (P : Place κ K) {u : K}
    (hu : u ≠ 0) (h : P.ord u = 0) : (placeMapS he P).ord (e u) = 0 := by
  obtain ⟨h1, h2⟩ := (P.ord_eq_zero_iff hu).1 h
  refine ((placeMapS he P).ord_eq_zero_iff (by simpa using hu)).2
    ⟨(mem_placeMapS_apply he P u).2 h1, ?_⟩
  rw [← map_inv₀]
  exact (mem_placeMapS_apply he P _).2 h2

/-- Uniformisers map to uniformisers. -/
lemma ord_placeMapS_uniformizer (he : MapsConst e.symm κ' κ) (P : Place κ K) {π : K}
    (hπ : P.ord π = 1) : (placeMapS he P).ord (e π) = 1 := by
  set P' := placeMapS he P
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  have hπmem : π ∈ P.1 := P.mem_of_ord_nonneg (by rw [hπ]; norm_num)
  have hπinv : π⁻¹ ∉ P.1 := fun h ↦ by
    have := P.ord_nonneg_of_mem h
    rw [P.ord_inv, hπ] at this
    norm_num at this
  have heπ0 : e π ≠ 0 := by simpa using hπ0
  have ha : 0 < P'.ord (e π) := ord_pos_of_mem_of_inv_notMem P' heπ0
    ((mem_placeMapS_apply he P π).2 hπmem)
    (by rw [← map_inv₀, mem_placeMapS_apply]; exact hπinv)
  obtain ⟨π', hπ'⟩ := P'.exists_ord_eq_one
  have hπ'0 : π' ≠ 0 := by rintro rfl; simp at hπ'
  set y := e.symm π'
  have hy0 : y ≠ 0 := by simpa [y] using hπ'0
  have hymem : y ∈ P.1 :=
    (mem_placeMapS he P π').1 (P'.mem_of_ord_nonneg (by rw [hπ']; norm_num))
  have hyinv : y⁻¹ ∉ P.1 := fun h ↦ by
    have h' : π'⁻¹ ∈ P'.1 := by
      rw [mem_placeMapS, map_inv₀]
      exact h
    have := P'.ord_nonneg_of_mem h'
    rw [P'.ord_inv, hπ'] at this
    norm_num at this
  have hb : 0 < P.ord y := ord_pos_of_mem_of_inv_notMem P hy0 hymem hyinv
  obtain ⟨w, hw0, hw, hyw⟩ := eq_zpow_mul_unit P hπ hy0
  have hπ'eq : π' = e π ^ P.ord y * e w := by
    have h' : π' = e (π ^ P.ord y * w) := by rw [← hyw]; simp [y]
    rw [h', map_mul, map_zpow₀]
  have h1 : P'.ord π' = P.ord y * P'.ord (e π) := by
    rw [hπ'eq, P'.ord_mul (zpow_ne_zero _ heπ0) (by simpa using hw0), P'.ord_zpow,
      ord_placeMapS_of_ord_eq_zero he P hw0 hw, add_zero]
  rw [hπ'] at h1
  nlinarith

/-- **Orders are invariant**: `ord_{e P}(e f) = ord_P f`. -/
theorem ord_placeMapS (he : MapsConst e.symm κ' κ) (P : Place κ K) (f : K) :
    (placeMapS he P).ord (e f) = P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨π, hπ⟩ := P.exists_ord_eq_one
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  obtain ⟨u, hu0, hu, hfu⟩ := eq_zpow_mul_unit P hπ hf
  conv_lhs => rw [hfu, map_mul, map_zpow₀]
  rw [(placeMapS he P).ord_mul (zpow_ne_zero _ (by simpa using hπ0)) (by simpa using hu0),
    (placeMapS he P).ord_zpow, ord_placeMapS_uniformizer he P hπ,
    ord_placeMapS_of_ord_eq_zero he P hu0 hu]
  ring

variable (he : MapsConst e κ κ') (he' : MapsConst e.symm κ' κ)

/-- Places of function fields isomorphic by `e` (mapping the constants onto each other). -/
def placeEquivS : Place κ K ≃ Place κ' K' where
  toFun := placeMapS he'
  invFun := placeMapS (e := e.symm) he
  left_inv P := Place.ext (by ext x; simp [mem_placeMapS])
  right_inv Q := Place.ext (by ext x; simp [mem_placeMapS])

/-- Divisors of function fields isomorphic by `e`. -/
def divisorEquivS : Divisor κ K ≃+ Divisor κ' K' :=
  Finsupp.domCongr (placeEquivS he he')

lemma div_ringEquivS (f : K) :
    Divisor.div κ' (e f) = divisorEquivS he he' (Divisor.div κ f) := by
  ext Q
  change Q.ord (e f) = Divisor.div κ f ((placeEquivS he he').symm Q)
  rw [Divisor.div_apply]
  conv_lhs => rw [← (placeEquivS he he').apply_symm_apply Q]
  exact ord_placeMapS he' _ f

lemma map_principalS :
    (principal κ K).map (divisorEquivS he he').toAddMonoidHom = principal κ' K' := by
  ext D'
  simp only [AddSubgroup.mem_map, mem_principal]
  constructor
  · rintro ⟨D, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨e f, by simpa using hf, div_ringEquivS he he' f⟩
  · rintro ⟨f', hf', rfl⟩
    refine ⟨Divisor.div κ (e.symm f'), ⟨_, by simpa using hf', rfl⟩, ?_⟩
    change divisorEquivS he he' _ = _
    rw [← div_ringEquivS, RingEquiv.apply_symm_apply]

/-- **`Pic(K) ≃ Pic(K′)`** for function fields isomorphic by `e` (mapping the constants onto
each other). -/
def picEquivS : Pic κ K ≃+ Pic κ' K' :=
  QuotientAddGroup.congr _ _ (divisorEquivS he he') (map_principalS he he')

lemma picEquivS_mk (E : Divisor κ K) :
    picEquivS he he' (E : Pic κ K) = (divisorEquivS he he' E : Pic κ' K') := rfl

/-- **`picEquivS` is equivariant**: if `e ∘ τ = τ′ ∘ e` for semilinear automorphisms `τ`, `τ′`,
then `picEquivS ∘ picMap τ = picMap τ′ ∘ picEquivS`. -/
theorem picEquivS_picMap (τ : constAut κ K) (τ' : constAut κ' K')
    (hτ : ∀ x : K, e ((τ : K ≃+* K) x) = (τ' : K' ≃+* K') (e x)) (x : Pic κ K) :
    picEquivS he he' (Kummer.picMap τ x) = Kummer.picMap τ' (picEquivS he he' x) := by
  induction x using QuotientAddGroup.induction_on with
  | H E =>
    rw [Kummer.picMap_mk, picEquivS_mk, picEquivS_mk, Kummer.picMap_mk]
    congr 1
    have hτ' : ∀ y : K', (τ : K ≃+* K).symm (e.symm y) =
        e.symm ((τ' : K' ≃+* K').symm y) := by
      intro y
      apply e.injective
      apply (τ' : K' ≃+* K').injective
      rw [← hτ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
        RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    have key : ∀ P : Place κ K, placeEquivS he he' (Kummer.placeMap τ P) =
        Kummer.placeMap τ' (placeEquivS he he' P) := by
      intro P
      apply Place.ext
      ext y
      change e.symm y ∈ (Kummer.placeMap τ P).1 ↔ (τ' : K' ≃+* K').symm y ∈ (placeMapS he' P).1
      rw [Kummer.mem_placeMap, mem_placeMapS, hτ']
    induction E using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
    | single P n =>
      change Finsupp.equivMapDomain _ (Finsupp.equivMapDomain _ (Finsupp.single P n)) =
        Finsupp.equivMapDomain _ (Finsupp.equivMapDomain _ (Finsupp.single P n))
      rw [Finsupp.equivMapDomain_single, Finsupp.equivMapDomain_single,
        Finsupp.equivMapDomain_single, Finsupp.equivMapDomain_single]
      change Finsupp.single (placeEquivS he he' (Kummer.placeMap τ P)) n =
        Finsupp.single (Kummer.placeMap τ' (placeEquivS he he' P)) n
      rw [key]

end Semilinear

/-! ### The stages -/

section Stage

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [CharZero Ω] [hH : Fact (D.H ≤ D.HL)]

attribute [local instance] CurvesJacobian.isFunctionField_F

/-- **`F K̄` of a stage is `F k̄` of `U`** (the identity of `Ω`). -/
def fStageEquiv (s : StageIdx D) : F (baseChange s.data) ≃+* F (baseChange D) where
  toFun x := ⟨x, (mem_F_baseChange_stage_iff s).1 x.2⟩
  invFun y := ⟨y, (mem_F_baseChange_stage_iff s).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[simp] lemma coe_fStageEquiv (s : StageIdx D) (x : F (baseChange s.data)) :
    ((fStageEquiv s x : F (baseChange D)) : Ω) = x :=
  Subtype.coe_mk _ _

lemma mapsConst_fStageEquiv (s : StageIdx D) :
    MapsConst (fStageEquiv s) (kbar s.K Ω) (kbar k Ω) := fun c =>
  ⟨⟨c, (mem_kbar_stage_iff s.K).1 c.2⟩, rfl⟩

lemma mapsConst_fStageEquiv_symm (s : StageIdx D) :
    MapsConst (fStageEquiv s).symm (kbar k Ω) (kbar s.K Ω) := fun c =>
  ⟨⟨c, (mem_kbar_stage_iff s.K).2 c.2⟩, rfl⟩

/-- **`Pic(F K̄)` of a stage is `Pic(F k̄)` of `U`.** -/
def picStageEquiv (s : StageIdx D) :
    Pic (kbar s.K Ω) (F (baseChange s.data)) ≃+ Pic (kbar k Ω) (F (baseChange D)) :=
  picEquivS (mapsConst_fStageEquiv s) (mapsConst_fStageEquiv_symm s)

/-- **Lifting `h ∈ H` fixing `K` to the stage**: an element of `H` fixing `K` pointwise is
(as an automorphism of `Ω`) an element of the group `H_V` of the stage `V ⊆ U_K`. -/
theorem exists_stage_lift (s : StageIdx D) (h : D.H)
    (hK : ∀ c : s.K, (h : Ω ≃ₐ[K₀ k t] Ω) (algebraMap s.K Ω c) = algebraMap s.K Ω c) :
    ∃ g : s.data.H, ∀ x, (g : Ω ≃ₐ[K₀ s.K s.t'] Ω) x = (h : Ω ≃ₐ[K₀ k t] Ω) x := by
  have hfixL : ∀ y ∈ (constExt s.K D).L, (h : Ω ≃ₐ[K₀ k t] Ω) y = y := fun y hy =>
    (mem_L_constExt_iff D s.K).1 hy _ (hH.out h.2) hK
  obtain ⟨g, hg⟩ := exists_algEquiv_K₀ (E := s.K) (t' := s.t')
    (h : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv hK (hfixL _ s.ht')
  have hmem : g ∈ s.data.H := by
    change g ∈ (extendK₀ (constExt s.K D).L s.ht').fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    rw [hg]
    exact hfixL y hy
  exact ⟨⟨g, hmem⟩, hg⟩

/-- **`H_K`-invariance**: the classes of `Pic(F k̄)` fixed by every `h ∈ H` fixing `K`. -/
def picInvOver (D : Pi1.Orbifold.GaloisData k t) (K : IntermediateField k Ω) :
    AddSubgroup (Pic (kbar k Ω) (F (baseChange D))) where
  carrier := {x | ∀ h : D.H,
    (∀ c : K, (h : Ω ≃ₐ[K₀ k t] Ω) (algebraMap K Ω c) = algebraMap K Ω c) → picAct D h x = x}
  zero_mem' _ _ := map_zero _
  add_mem' ha hb h hh := by rw [map_add, ha h hh, hb h hh]
  neg_mem' ha h hh := by rw [map_neg, ha h hh]

/-- **`⋂_N N · Pic(F k̄)^{H_K} = 0`** (`⋂_N N · J(K) = 0` for the Jacobian of `U`). -/
def IsDivFreeOver (D : Pi1.Orbifold.GaloisData k t) (K : IntermediateField k Ω) : Prop :=
  ∀ x : Pic (kbar k Ω) (F (baseChange D)),
    (∀ N : ℕ, 0 < N → ∃ y ∈ picInvOver D K, N • y = x) → x = 0

/-- `picStageEquiv` maps `Pic^{G_K}` of the stage into the `H_K`-invariant classes. -/
theorem picStageEquiv_mem_inv (s : StageIdx D) {y : Pic (kbar s.K Ω) (F (baseChange s.data))}
    (hy : y ∈ Kummer.picInv s.data) : picStageEquiv s y ∈ picInvOver D s.K := by
  intro h hK
  obtain ⟨g, hg⟩ := exists_stage_lift s h hK
  have e := picEquivS_picMap (mapsConst_fStageEquiv s) (mapsConst_fStageEquiv_symm s)
    (autF s.data g) (autF D h) (fun x => Subtype.ext (by
      simp only [coe_fStageEquiv, coe_autF_apply]
      exact hg x)) y
  change picStageEquiv s (picAct s.data g y) = picAct D h (picStageEquiv s y) at e
  rw [← e, hy g]

/-- **[AbsTopIII] Prop 1.6 (iii) input at a stage**: `IsKummerFaithfulJac` for the stage `s` over
`K` follows from `⋂_N N · Pic(F k̄)^{H_K} = 0`. -/
theorem isKummerFaithfulJac_stage (s : StageIdx D) (hJ : IsDivFreeOver D s.K) :
    IsKummerFaithfulJac s.data := by
  intro x hx
  apply (picStageEquiv s).injective
  rw [map_zero]
  refine hJ _ fun N hN => ?_
  obtain ⟨y, hy, hyx⟩ := hx N hN
  exact ⟨picStageEquiv s y, picStageEquiv_mem_inv s hy, by rw [← map_nsmul, hyx]⟩

end Stage

/-! ### Curves: `⋂_N N · J(K) = 0` for number fields `K ⊇ k` -/

section Curve

open CategoryTheory AlgebraicGeometry Belyi CurvesJacobian.Cusp

section Ext

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] {σ : Spec (CommRingCat.of k) ⟶ X}
  {hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k))}

/-- **`⋂_N N · J = 0` descends along `J(K) ↪ J(L)`** for `k ⊆ K ⊆ L`. -/
theorem JacDivFree.of_ext' (K L : Type u) [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] (hL : JacDivFree X σ hσ L) : JacDivFree X σ hσ K := by
  intro z hz hdiv
  apply picRes_injective X σ hσ K L
  rw [map_zero]
  refine hL _ (picRes_mem_jacPoints X σ hσ K L hz) fun N hN ↦ ?_
  obtain ⟨y, hy, hyz⟩ := hdiv N hN
  exact ⟨_, picRes_mem_jacPoints X σ hσ K L hy, by rw [← map_nsmul, hyz]⟩

variable (X σ hσ) in
/-- **`⋂_N N · J(K) = 0` for every number field `K ⊇ k`** (through a local field containing
`K`: [AbsTopIII] Rem 1.5.4 (i) for the Jacobian). -/
theorem jacDivFree_numberField' (K : Type u) [Field K] [NumberField K] [Algebra k K] :
    JacDivFree X σ hσ K := by
  obtain ⟨L, _, _, _, ⟨f⟩⟩ := NumberField.exists_localField K
  letI : Algebra K L := f.toAlgebra
  letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact JacDivFree.of_ext' K L (jacDivFree_of_properSpace X σ hσ L)

end Ext

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  (σ : Spec (CommRingCat.of k) ⟶ X)
  (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

instance fact_curveGaloisData_H_le :
    Fact ((curveGaloisData k hτ).H ≤ (curveGaloisData k hτ).HL) := ⟨le_of_eq rfl⟩

attribute [local instance] CurvesJacobian.isFunctionField_F

section Over

variable [IsAlgClosed (FFClosure X)] (K : IntermediateField k (FFClosure X))
  [Algebra.IsAlgebraic k K]

lemma le_kbar : K ≤ kbar k (FFClosure X) := fun x hx =>
  mem_algebraicClosure_iff.2
    ((Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : K)).algHom K.val)

/-- `K ⊆ k̄` (local instance). -/
@[reducible] def algebraKKbar : Algebra K (kbar k (FFClosure X)) :=
  (IntermediateField.inclusion (le_kbar k K)).toRingHom.toAlgebra

attribute [local instance] algebraKKbar

instance : IsScalarTower k K (kbar k (FFClosure X)) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    ((IntermediateField.inclusion (le_kbar k K)).commutes x).symm

set_option synthInstance.maxHeartbeats 400000 in
-- `Module.IsTorsionFree K k̄` is found slowly
instance : Algebra.IsAlgebraic K (kbar k (FFClosure X)) :=
  ⟨fun x =>
    ((Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral.tower_top (A := K)).isAlgebraic⟩

set_option synthInstance.maxHeartbeats 400000 in
-- `IsAlgClosure K k̄` is found slowly
set_option maxHeartbeats 1000000 in
-- the separability of `k̄ / K` is found slowly
instance : IsGalois K (kbar k (FFClosure X)) := by
  haveI : IsAlgClosure K (kbar k (FFClosure X)) := ⟨isAlgClosed_kbar, inferInstance⟩
  exact IsAlgClosure.isGalois K (kbar k (FFClosure X))

set_option maxHeartbeats 3200000 in
-- the `Pic` and `J` terms over `k̄ = kbar k Ω` as a `K`-algebra unify slowly
/-- **`⋂_N N · Pic(F k̄)^{H_K} = 0`** for a curve with a rational point over `k`, from
`⋂_N N · J(K) = 0`: an `H_K`-invariant class of degree `0` maps to `J(k̄)^{G_K} ≅ J(K)`. -/
theorem isDivFreeOver_curve (hJ : JacDivFree X σ hσ K) :
    IsDivFreeOver (curveGaloisData k hτ) K := by
  have hinv : ∀ {y}, y ∈ picInvOver (curveGaloisData k hτ) K → Pic.deg _ _ y = 0 →
      picPsi k hτ σ hσ y ∈ (jacPoints X σ hσ (kbar k (FFClosure X)) ⊓
        CurvesJacobian.picInv X σ hσ K (kbar k (FFClosure X))) := by
    intro y hy hy0
    refine AddSubgroup.mem_inf.mpr ⟨(picPsi_mem_jacPoints_iff k hτ σ hσ y).2 hy0, fun g ↦ ?_⟩
    obtain ⟨h, hh⟩ := hToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ) (g.restrictScalars k)
    have hK : ∀ c : K, ((h : (curveGaloisData k hτ).H) : FFClosure X ≃ₐ[K₀ k (coordT τ)]
        FFClosure X) (algebraMap K (FFClosure X) c) = algebraMap K (FFClosure X) c := by
      intro c
      have h1 : algebraMap (kbar k (FFClosure X)) (FFClosure X)
          (hToGk (curveGaloisData k hτ) h (algebraMap K (kbar k (FFClosure X)) c)) =
          ((h : (curveGaloisData k hτ).H) : FFClosure X ≃ₐ[K₀ k (coordT τ)] FFClosure X)
            (algebraMap K (FFClosure X) c) :=
        algebraMap_hToGk_apply (curveGaloisData k hτ) h (algebraMap K _ c)
      rw [← h1, hh, AlgEquiv.restrictScalars_apply, g.commutes]
      rfl
    have e := picPsi_picAct k hτ σ hσ h y
    rw [hy h hK, hh] at e
    exact e.symm
  intro x hx
  have hdeg0 : Pic.deg _ _ x = 0 := deg_eq_zero_of_forall_nsmul k hτ fun N hN ↦
    (hx N hN).imp fun _ h ↦ h.2
  have hxinv : x ∈ picInvOver (curveGaloisData k hτ) K := by
    obtain ⟨y, hy, hyx⟩ := hx 1 one_pos
    rw [one_smul] at hyx
    exact hyx ▸ hy
  have hdesc : ∀ {y}, y ∈ picInvOver (curveGaloisData k hτ) K → Pic.deg _ _ y = 0 →
      ∃ z ∈ jacPoints X σ hσ K, picRes X σ hσ K (kbar k (FFClosure X)) z = picPsi k hτ σ hσ y := by
    intro y hy hy0
    set w := (jacPointsEquivInv X σ hσ K (kbar k (FFClosure X))).symm ⟨_, hinv hy hy0⟩
    refine ⟨w, w.2, ?_⟩
    rw [← coe_jacPointsEquivInv, AddEquiv.apply_symm_apply]
  obtain ⟨z, hz, hzx⟩ := hdesc hxinv hdeg0
  have hz0 : z = 0 := hJ z hz fun N hN ↦ by
    obtain ⟨y, hy, hyx⟩ := hx N hN
    have hy0 : Pic.deg _ _ y = 0 := by
      have h := congrArg (Pic.deg _ _) hyx
      rw [map_nsmul, hdeg0, nsmul_eq_mul, mul_eq_zero] at h
      exact h.resolve_left (by exact_mod_cast hN.ne')
    obtain ⟨w, hw, hwy⟩ := hdesc hy hy0
    refine ⟨w, hw, picRes_injective X σ hσ K (kbar k (FFClosure X)) ?_⟩
    rw [map_nsmul, hwy, hzx, ← map_nsmul, hyx]
  apply picPsi_injective k hτ σ hσ
  rw [map_zero, ← hzx, hz0, map_zero]

end Over

include σ hσ in
/-- **Every stage of the Galois model of a curve over a number field is Kummer-faithful for its
Jacobian** (`⋂_N N · J(K) = 0` over the number field `K` of the stage). -/
theorem isKummerFaithfulJac_stage_curve_numberField [NumberField k]
    [IsAlgClosed (FFClosure X)] [CharZero (FFClosure X)] (s : StageIdx (curveGaloisData k hτ)) :
    IsKummerFaithfulJac s.data := by
  haveI : NumberField s.K := NumberField.of_module_finite k s.K
  exact isKummerFaithfulJac_stage s
    (isDivFreeOver_curve k hτ σ hσ s.K (jacDivFree_numberField' X σ hσ s.K))

end Curve

end Iut.Reconstruction.Thm19
