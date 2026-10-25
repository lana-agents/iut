/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Elliptic.EllModel
import Iut.AutHolomorphic.Elliptic.LieTransport

/-!
# `A_p` for an abstract once-punctured elliptic curve ([AbsTopIII] Cor 2.7 (e), Def 4.1 (i))

Let `(E, A)` be an Aut-holomorphic space isomorphic to some `E_Λ = T_Λ ∖ {0}` (`IsEllModel A`,
the output of [AbsTopIII] Corollary 2.7 (a)). From `(E, A)` alone:

* `onePointStr A`: the Aut-holomorphic structure on `OnePoint E` given by `A` on the opens not
  containing `∞` (only the germs at points `p ≠ ∞` enter `A_p`);
* `EllSpace A`: `OnePoint E` with the group law of Corollary 2.7 (c) (`ellAddCommGroup`, whose
  addition is the model-implicit `recAdd A`), a topological group
  (`ellSpace_isTopologicalAddGroup`);
* `EllField A p = A_p ∪ {0}` for `p ∈ E`: the set `fieldSet` of `LinearHol.lean` (endomorphisms of
  the tangent space `Lie (OnePoint E)` holomorphic at `p`, squares, and `0`); its addition is
  addition of endomorphisms (`add_val`) and its multiplication is composition (`mul_val`).

For every isomorphism `ψ : (E, A) ≅ (E_Λ, ellStr L)`:

* `ellHomeo hψ : OnePoint E ≃ₜ T_Λ` is additive (`ellHomeo_add`) and an isomorphism of
  Aut-holomorphic spaces away from `∞` (`isIsoNear_ellHomeo`);
* `mem_ellFieldSet_iff`: **`A_p ∪ {0}` consists of the conjugates of the maps `c ↦ b c` of
  `Lie T_Λ ≅ ℂ`**, and `mem_ellApSet_iff`: `A_p` of those with `b ≠ 0`;
* `ellEquiv hψ p : EllField A p ≃+* ℂ`, a homeomorphism (`continuous_ellEquiv`,
  `continuous_ellEquiv_symm`): **`A_p ∪ {0}` is a topological field isomorphic to `ℂ`**, the CAF
  `A_{X_ell}` of [AbsTopIII] Definition 4.1 (i);
* `ellEquiv_trans_eq`: two isomorphisms `ψ, ψ'` give identifications with `ℂ` that differ by the
  identity or complex conjugation (the archimedean Kummer indeterminacy `Gal(ℂ/ℝ)`);
* `fieldSet_eq`: the sets `A_p ∪ {0}` for `p, p' ∈ E` coincide inside `End_ℝ (Lie (OnePoint E))`,
  so the "compatible isomorphisms `A_p ≅ A_{p'}`" of Corollary 2.7 (e) are identities.
-/

namespace Iut

namespace AutHol

namespace Ell

open Set Topology TopologicalSpace OnePoint Torus

variable {E : Type*} [TopologicalSpace E] {A : AutHolStr E}

/-! ### The Aut-holomorphic structure on `OnePoint E` away from `∞` -/

/-- The open subset `U ∩ E` of `E`. -/
def preOpen (V : Opens (OnePoint E)) : Opens E :=
  ⟨((↑) : E → OnePoint E) ⁻¹' (V : Set (OnePoint E)), V.2.preimage continuous_coe⟩

theorem range_coe_preOpen {V : Opens (OnePoint E)} (h : ∞ ∉ V) :
    range (((↑) : E → OnePoint E) ∘ (Subtype.val : preOpen V → E)) = (V : Set (OnePoint E)) := by
  ext y
  induction y using OnePoint.rec with
  | infty =>
    simp only [mem_range, Function.comp_apply, coe_ne_infty, exists_false, SetLike.mem_coe,
      false_iff]
    exact h
  | coe x =>
    constructor
    · rintro ⟨z, hz⟩
      rw [Function.comp_apply] at hz
      rw [← coe_injective hz]
      exact z.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩

/-- For `∞ ∉ V`, the inclusion `E → OnePoint E` maps `V ∩ E` homeomorphically onto `V`. -/
noncomputable def preHomeo (V : Opens (OnePoint E)) (h : ∞ ∉ V) : preOpen V ≃ₜ V :=
  (isOpenEmbedding_coe.isEmbedding.comp IsEmbedding.subtypeVal).toHomeomorph.trans
    (Homeomorph.setCongr (range_coe_preOpen h))

@[simp]
theorem preHomeo_apply (V : Opens (OnePoint E)) (h : ∞ ∉ V) (x : preOpen V) :
    (preHomeo V h x : OnePoint E) = ((x : E) : OnePoint E) := rfl

open Classical in
/-- **The Aut-holomorphic structure of `OnePoint E` away from `∞`**: `A(V) = A_E(V)` for
`∞ ∉ V`; on opens containing `∞` it is (arbitrarily) the full group. -/
noncomputable def onePointStr (A : AutHolStr E) : AutHolStr (OnePoint E) where
  aut V := if h : ∞ ∈ V then ⊤ else (A.aut (preOpen V)).map (conj (preHomeo V h)).toMonoidHom

theorem onePointStr_aut {V : Opens (OnePoint E)} (h : ∞ ∉ V) :
    (onePointStr A).aut V = (A.aut (preOpen V)).map (conj (preHomeo V h)).toMonoidHom := by
  simp only [onePointStr, dif_neg h]

/-- **`compEquiv ψ : OnePoint E ≃ₜ T_Λ` is an isomorphism of Aut-holomorphic spaces away from
`∞`**. -/
theorem isIsoNear_compEquiv {L : PeriodPair} {ψ : E ≃ₜ punct L} (hψ : IsIso A (ellStr L) ψ) :
    IsIsoNear (onePointStr A) (torusStr L) (compEquiv ψ) (range ((↑) : E → OnePoint E)) := by
  intro U hUO hU V e he
  have hinf : ∞ ∉ U := fun h => by
    obtain ⟨x, hx⟩ := hUO h
    exact coe_ne_infty x hx
  rw [onePointStr_aut hinf, map_conj_trans]
  have hφ : IsMorphism A (torusStr L) ((Subtype.val : punct L → Torus L) ∘ ψ) :=
    (AutHolStr.isMorphism_val (torusStr L) (punct L)).comp hψ
  exact hφ.2 (preOpen U) (isConnected_of_homeomorph (preHomeo U hinf).symm hU) V
    (isConnected_of_homeomorph e hU) ((preHomeo U hinf).trans e) fun x => by
      rw [Homeomorph.trans_apply, he]
      rfl

/-! ### The group `OnePoint E` -/

/-- `OnePoint E` with the group law of [AbsTopIII] Corollary 2.7 (c) (for `IsEllModel A`). -/
def EllSpace (_A : AutHolStr E) : Type _ := OnePoint E

instance : TopologicalSpace (EllSpace A) := inferInstanceAs (TopologicalSpace (OnePoint E))

/-- The point `p ∈ E` of `EllSpace A`. -/
def ellPt (A : AutHolStr E) (p : E) : EllSpace A := (p : OnePoint E)

/-- `onePointStr A` on `EllSpace A`. -/
noncomputable def ellPtStr (A : AutHolStr E) : AutHolStr (EllSpace A) := onePointStr A

/-- `compEquiv ψ` as a map out of `EllSpace A`. -/
noncomputable def ellHomeo {L : PeriodPair} {ψ : E ≃ₜ punct L} (_hψ : IsIso A (ellStr L) ψ) :
    EllSpace A ≃ₜ Torus L :=
  compEquiv ψ

theorem ellHomeo_ellPt {L : PeriodPair} {ψ : E ≃ₜ punct L} (hψ : IsIso A (ellStr L) ψ) (p : E) :
    ellHomeo hψ (ellPt A p) = ((ψ p : punct L) : Torus L) := rfl

theorem isIsoNear_ellHomeo {L : PeriodPair} {ψ : E ≃ₜ punct L} (hψ : IsIso A (ellStr L) ψ) :
    IsIsoNear (ellPtStr A) (torusStr L) (ellHomeo hψ) (range (ellPt A)) :=
  isIsoNear_compEquiv hψ

theorem range_ellPt_mem_nhds (p : E) : range (ellPt A) ∈ 𝓝 (ellPt A p) :=
  (isOpen_range_coe (X := E)).mem_nhds ⟨p, rfl⟩

variable [hA : Fact (IsEllModel A)]

/-- **The group structure** of [AbsTopIII] Corollary 2.7 (c) on `OnePoint E`. -/
noncomputable instance : AddCommGroup (EllSpace A) := ellAddCommGroup hA.out

theorem ellSpace_add (x y : EllSpace A) :
    x + y = recAdd A (x : OnePoint E) (y : OnePoint E) :=
  ellAddCommGroup_add hA.out x y

theorem ellHomeo_add {L : PeriodPair} {ψ : E ≃ₜ punct L} (hψ : IsIso A (ellStr L) ψ)
    (x y : EllSpace A) : ellHomeo hψ (x + y) = ellHomeo hψ x + ellHomeo hψ y := by
  rw [ellSpace_add]
  exact recAdd_of_isIso hψ x y

/-- The chosen model `L` of `(E, A)`. -/
noncomputable def chosenL (A : AutHolStr E) [hA : Fact (IsEllModel A)] : PeriodPair :=
  hA.out.choose

/-- The chosen isomorphism `(E, A) ≅ E_Λ`. -/
noncomputable def chosenIso (A : AutHolStr E) [hA : Fact (IsEllModel A)] :
    E ≃ₜ punct (chosenL A) :=
  hA.out.choose_spec.choose

theorem chosenIso_spec : IsIso A (ellStr (chosenL A)) (chosenIso A) :=
  hA.out.choose_spec.choose_spec

/-- `OnePoint E` is a **topological group** for the law of [AbsTopIII] Corollary 2.7 (c). -/
instance ellSpace_isTopologicalAddGroup : IsTopologicalAddGroup (EllSpace A) := by
  let Θ := ellHomeo (chosenIso_spec (A := A))
  have hΘ : ∀ x y, Θ (x + y) = Θ x + Θ y := ellHomeo_add chosenIso_spec
  let φ : EllSpace A →+ Torus (chosenL A) := AddMonoidHom.mk' Θ hΘ
  have hadd : ∀ x y : EllSpace A, x + y = Θ.symm (Θ x + Θ y) := fun x y => by
    rw [← hΘ, Homeomorph.symm_apply_apply]
  have hneg : ∀ x : EllSpace A, -x = Θ.symm (-Θ x) := fun x => by
    rw [← Θ.symm_apply_apply (-x)]
    congr 1
    exact map_neg φ x
  exact
    { continuous_add := by
        simp only [hadd]
        fun_prop
      continuous_neg := by
        simp only [hneg]
        fun_prop }

/-! ### `A_p ∪ {0}` -/

/-- **`A_p ∪ {0}`** ([AbsTopIII] Corollary 2.7 (e)) for `p ∈ E`, built from `(E, A)` alone. -/
noncomputable def EllField (A : AutHolStr E) [Fact (IsEllModel A)] (p : E) : Type _ :=
  fieldSet (ellPtStr A) (ellPt A p)

/-- The topology of pointwise convergence on the tangent space. -/
noncomputable instance (p : E) : TopologicalSpace (EllField A p) :=
  TopologicalSpace.induced
    (fun M : EllField A p => (M.1 : Lie (EllSpace A) → Lie (EllSpace A))) inferInstance

section Model

variable {L : PeriodPair} {ψ : E ≃ₜ punct L} (hψ : IsIso A (ellStr L) ψ)

/-- **`A_p ∪ {0}` in the model**: the conjugates by `ψ` of the maps `c ↦ b c`. -/
theorem mem_ellFieldSet_iff (p : E) (M : Lie (EllSpace A) →ₗ[ℝ] Lie (EllSpace A)) :
    M ∈ fieldSet (ellPtStr A) (ellPt A p) ↔
      ∃ b, lieConj (ellHomeo hψ) (ellHomeo_add hψ) M = mulMap b := by
  rw [mem_fieldSet_transport (ellHomeo_add hψ) (range_ellPt_mem_nhds p) (isIsoNear_ellHomeo hψ)
    continuous_linearMap_lie, mem_fieldSet_iff']

/-- **`A_p` in the model** ([AbsTopIII] Proposition 2.6 (a), Corollary 2.7 (e): `A_p ≅ ℂ^×`). -/
theorem mem_ellApSet_iff (p : E) (M : Lie (EllSpace A) →ₗ[ℝ] Lie (EllSpace A)) :
    M ∈ apSet (ellPtStr A) (ellPt A p) ↔
      ∃ b, b ≠ 0 ∧ lieConj (ellHomeo hψ) (ellHomeo_add hψ) M = mulMap b := by
  rw [mem_apSet_transport (ellHomeo_add hψ) (range_ellPt_mem_nhds p) (isIsoNear_ellHomeo hψ)
    continuous_linearMap_lie, mem_apSet_iff']

/-- **The sets `A_p ∪ {0}`, `p ∈ E`, coincide**: the isomorphisms `A_p ≅ A_{p'}` of [AbsTopIII]
Corollary 2.7 (e) are identities. -/
theorem fieldSet_eq (p p' : E) :
    fieldSet (ellPtStr A) (ellPt A p) = fieldSet (ellPtStr A) (ellPt A p') := by
  ext M
  rw [mem_ellFieldSet_iff chosenIso_spec, mem_ellFieldSet_iff chosenIso_spec]

/-- The coefficient of `M ∈ A_p ∪ {0}` read through `ψ`. -/
noncomputable def coeff (M : Lie (EllSpace A) →ₗ[ℝ] Lie (EllSpace A)) : ℂ :=
  lieEquiv.symm (lieConj (ellHomeo hψ) (ellHomeo_add hψ) M (line 1))

theorem coeff_mulMap (b : ℂ) :
    lieEquiv.symm (mulMap (L := L) b (line 1)) = b := by
  rw [mulMap_line, mul_one, ← lieEquiv_apply, LinearEquiv.symm_apply_apply]

/-- The coefficient equivalence `A_p ∪ {0} ≃ ℂ` through `ψ`. -/
noncomputable def coeffEquiv (p : E) : EllField A p ≃ ℂ where
  toFun M := coeff hψ M.1
  invFun b := ⟨lieConj (ellHomeo hψ).symm (symm_add _ (ellHomeo_add hψ)) (mulMap b),
    (mem_ellFieldSet_iff hψ p _).2 ⟨b, lieConj_lieConj_symm _ _ _⟩⟩
  left_inv M := by
    obtain ⟨b, hb⟩ := (mem_ellFieldSet_iff hψ p M.1).1 M.2
    apply Subtype.ext
    change lieConj _ _ (mulMap (coeff hψ M.1)) = M.1
    rw [coeff, hb, coeff_mulMap, ← hb, lieConj_symm_lieConj]
  right_inv b := by
    change coeff hψ (lieConj _ _ (mulMap b)) = b
    rw [coeff, lieConj_lieConj_symm, coeff_mulMap]

theorem lieConj_val (p : E) (M : EllField A p) :
    lieConj (ellHomeo hψ) (ellHomeo_add hψ) M.1 = mulMap (coeffEquiv hψ p M) := by
  obtain ⟨b, hb⟩ := (mem_ellFieldSet_iff hψ p M.1).1 M.2
  change _ = mulMap (coeff hψ M.1)
  rw [coeff, hb, coeff_mulMap]

theorem val_eq (p : E) (M : EllField A p) :
    M.1 = lieConj (ellHomeo hψ).symm (symm_add _ (ellHomeo_add hψ))
      (mulMap (coeffEquiv hψ p M)) := by
  rw [← lieConj_val, lieConj_symm_lieConj]

end Model

/-- **The field structure on `A_p ∪ {0}`** (transported from `ℂ` along a chosen model; by
`add_val` and `mul_val` it is addition and composition of endomorphisms, hence model-free). -/
noncomputable instance (p : E) : Field (EllField A p) := (coeffEquiv chosenIso_spec p).field

namespace EllField

variable {p : E}

/-- The underlying endomorphism of the tangent space. -/
def val (M : EllField A p) : Lie (EllSpace A) →ₗ[ℝ] Lie (EllSpace A) := M.1

theorem val_injective : Function.Injective (val : EllField A p → _) := Subtype.val_injective

theorem coeffEquiv_symm_val {L : PeriodPair} {ψ : E ≃ₜ punct L} (hψ : IsIso A (ellStr L) ψ)
    (b : ℂ) : ((coeffEquiv hψ p).symm b).val =
      lieConj (ellHomeo hψ).symm (symm_add _ (ellHomeo_add hψ)) (mulMap b) := rfl

/-- **Addition in `A_p ∪ {0}` is addition of endomorphisms of the tangent space.** -/
theorem add_val (M M' : EllField A p) : (M + M').val = M.val + M'.val := by
  change ((coeffEquiv chosenIso_spec p).symm
    (coeffEquiv chosenIso_spec p M + coeffEquiv chosenIso_spec p M')).val = _
  rw [coeffEquiv_symm_val, TorusField.mulMap_add, lieConj_add, val, val, val_eq chosenIso_spec p M,
    val_eq chosenIso_spec p M']

/-- **Multiplication in `A_p ∪ {0}` is composition.** -/
theorem mul_val (M M' : EllField A p) : (M * M').val = M.val * M'.val := by
  change ((coeffEquiv chosenIso_spec p).symm
    (coeffEquiv chosenIso_spec p M * coeffEquiv chosenIso_spec p M')).val = _
  rw [coeffEquiv_symm_val, TorusField.mulMap_mul, lieConj_mul, val, val, val_eq chosenIso_spec p M,
    val_eq chosenIso_spec p M']

theorem zero_val : (0 : EllField A p).val = 0 := by
  change ((coeffEquiv chosenIso_spec p).symm 0).val = _
  rw [coeffEquiv_symm_val, ← lieConj_eq_zero_iff (ellHomeo chosenIso_spec)
    (ellHomeo_add chosenIso_spec), lieConj_lieConj_symm]
  exact linearMap_ext_line fun c => by simp [mulMap_line, line_zero]

theorem one_val : (1 : EllField A p).val = 1 := by
  change ((coeffEquiv chosenIso_spec p).symm 1).val = _
  rw [coeffEquiv_symm_val]
  apply lieConj_injective (ellHomeo chosenIso_spec) (ellHomeo_add chosenIso_spec)
  rw [lieConj_lieConj_symm]
  refine LinearMap.ext fun f => ?_
  obtain ⟨c, rfl⟩ := exists_line f
  simp [mulMap_line, lieConj_apply]

end EllField

section Model

variable {L : PeriodPair} {ψ : E ≃ₜ punct L} (hψ : IsIso A (ellStr L) ψ)

theorem coeffEquiv_add (p : E) (M M' : EllField A p) :
    coeffEquiv hψ p (M + M') = coeffEquiv hψ p M + coeffEquiv hψ p M' := by
  change lieEquiv.symm (lieConj _ _ (M + M').val (line 1)) = _
  rw [EllField.add_val, lieConj_add, LinearMap.add_apply, map_add]
  rfl

theorem coeffEquiv_mul (p : E) (M M' : EllField A p) :
    coeffEquiv hψ p (M * M') = coeffEquiv hψ p M * coeffEquiv hψ p M' := by
  change lieEquiv.symm (lieConj _ _ (M * M').val (line 1)) = _
  rw [EllField.mul_val, lieConj_mul, EllField.val, EllField.val, lieConj_val, lieConj_val,
    Module.End.mul_apply, mulMap_line, mul_one, mulMap_line, ← lieEquiv_apply,
    LinearEquiv.symm_apply_apply]

/-- **`A_p ∪ {0} ≅ ℂ` as fields**, through any isomorphism `ψ : (E, A) ≅ E_Λ`. -/
noncomputable def ellEquiv (p : E) : EllField A p ≃+* ℂ where
  toEquiv := coeffEquiv hψ p
  map_add' := coeffEquiv_add hψ p
  map_mul' := coeffEquiv_mul hψ p

theorem ellEquiv_apply (p : E) (M : EllField A p) :
    ellEquiv hψ p M = lieEquiv.symm (lieConj (ellHomeo hψ) (ellHomeo_add hψ) M.1 (line 1)) := rfl

theorem continuous_ellEquiv (p : E) : Continuous (ellEquiv hψ p) := by
  have h1 : Continuous fun M : EllField A p =>
      M.1 ((lieMap (ellHomeo hψ) (ellHomeo_add hψ)).symm (line 1)) :=
    (continuous_apply _).comp continuous_induced_dom
  exact continuous_lieEquiv_symm.comp
    ((continuous_lieMap (ellHomeo hψ) (ellHomeo_add hψ)).comp h1)

theorem continuous_ellEquiv_symm (p : E) : Continuous (ellEquiv hψ p).symm := by
  refine continuous_induced_rng.2 (continuous_pi fun f => ?_)
  obtain ⟨c, hc⟩ := exists_line (lieMap (ellHomeo hψ) (ellHomeo_add hψ) f)
  change Continuous fun b : ℂ => lieConj (ellHomeo hψ).symm (symm_add _ (ellHomeo_add hψ))
    (mulMap b) f
  have h : ∀ b : ℂ, lieConj (ellHomeo hψ).symm (symm_add _ (ellHomeo_add hψ)) (mulMap b) f =
      lieMap (ellHomeo hψ).symm (symm_add _ (ellHomeo_add hψ)) (line (b * c)) := fun b => by
    rw [lieConj_apply, lieMap_symm_symm_eq _ (ellHomeo_add hψ), ← hc, mulMap_line]
  simp only [h]
  exact (continuous_lieMap (ellHomeo hψ).symm (symm_add _ (ellHomeo_add hψ))).comp
    (continuous_line.comp (continuous_id.mul continuous_const))

/-- **`A_p ∪ {0}` is a topological field homeomorphic to `ℂ`.** -/
noncomputable def ellHomeoField (p : E) : EllField A p ≃ₜ ℂ where
  toEquiv := (ellEquiv hψ p).toEquiv
  continuous_toFun := continuous_ellEquiv hψ p
  continuous_invFun := continuous_ellEquiv_symm hψ p

/-- **The Galois indeterminacy**: two isomorphisms `ψ, ψ'` of `(E, A)` with once-punctured tori
identify `A_p ∪ {0}` with `ℂ` up to the identity or complex conjugation. -/
theorem ellEquiv_trans_eq (p : E) {L' : PeriodPair} {ψ' : E ≃ₜ punct L'}
    (hψ' : IsIso A (ellStr L') ψ') :
    (((ellEquiv hψ p).symm.trans (ellEquiv hψ' p)) : ℂ →+* ℂ) = RingHom.id ℂ ∨
    (((ellEquiv hψ p).symm.trans (ellEquiv hψ' p)) : ℂ →+* ℂ) = starRingEnd ℂ := by
  apply Complex.ringHom_eq_id_or_conj_of_continuous
  exact (continuous_ellEquiv hψ' p).comp (continuous_ellEquiv_symm hψ p)

end Model

end Ell

end AutHol

end Iut
