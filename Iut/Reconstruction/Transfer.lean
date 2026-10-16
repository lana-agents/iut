/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The transfer: products over sections, transitivity (roadmap MR11)

General facts about Mathlib's transfer `MonoidHom.transfer` (the Verlagerung), not specific to
IUT, used for the reconstruction of `𝒪^×_{k̄}(G)` from `G` as a colimit along the transfer
([AbsTopIII], Proposition 5.8 (i), (ii)).

* `MonoidHom.transfer_eq_prod_section`: for any section `s : G ⧸ H → G` of the quotient map,
  `transfer ϕ g = ∏_{q ∈ G/H} ϕ(s(q)⁻¹ · g · s(g⁻¹ q))`;
* **`MonoidHom.transfer_transfer`** (transitivity): for `K ≤ H ≤ G` of finite index and
  `ϕ : K →* A`, `transfer_{G/H} (transfer_{H/K} ϕ) = transfer_{G/K} ϕ`;
* `MonoidHom.transfer_top`: the transfer to `G` itself is `ϕ`.
-/

open Subgroup

namespace MonoidHom

variable {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A]

theorem section_inv_mul_mem (s : G ⧸ H → G) (hs : ∀ q, (s q : G ⧸ H) = q) (g : G) (q : G ⧸ H) :
    (s q)⁻¹ * g * s (g⁻¹ • q) ∈ H := by
  have h1 : ((g * s (g⁻¹ • q) : G) : G ⧸ H) = (s q : G ⧸ H) := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, hs, hs, smul_inv_smul]
  rw [mul_assoc]
  exact QuotientGroup.leftRel_apply.mp (Quotient.exact' h1.symm)

/-- **The transfer as a product over an arbitrary section**:
`transfer ϕ g = ∏_q ϕ(s(q)⁻¹ g s(g⁻¹ q))`. -/
theorem transfer_eq_prod_section [H.FiniteIndex] [Fintype (G ⧸ H)] (ϕ : H →* A)
    (s : G ⧸ H → G) (hs : ∀ q, (s q : G ⧸ H) = q) (g : G) :
    ϕ.transfer g = ∏ q : G ⧸ H, ϕ ⟨(s q)⁻¹ * g * s (g⁻¹ • q), section_inv_mul_mem s hs g q⟩ := by
  classical
  let T : H.LeftTransversal := ⟨Set.range s, isComplement_range_left hs⟩
  rw [transfer_def ϕ T g, leftTransversals.diff]
  refine Finset.prod_congr (by congr; exact Subsingleton.elim _ _) fun c _ => congrArg ϕ ?_
  apply Subtype.ext
  have h1 := IsComplement.leftQuotientEquiv_apply (H := H) hs
  simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_assoc]
  change (T.2.leftQuotientEquiv c : G)⁻¹ * (g * (T.2.leftQuotientEquiv (g⁻¹ • c) : G)) = _
  rw [h1, h1]

/-- The transfer to `G` itself is the identity. -/
theorem transfer_top (ϕ : (⊤ : Subgroup G) →* A) (g : G) :
    ϕ.transfer g = ϕ ⟨g, Subgroup.mem_top g⟩ := by
  classical
  letI : Fintype (G ⧸ (⊤ : Subgroup G)) := Fintype.ofFinite _
  haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  have hs : ∀ q : G ⧸ (⊤ : Subgroup G), ((1 : G) : G ⧸ (⊤ : Subgroup G)) = q := fun q =>
    Subsingleton.elim _ _
  rw [transfer_eq_prod_section ϕ (fun _ => 1) hs g]
  haveI : Unique (G ⧸ (⊤ : Subgroup G)) := ⟨⟨(1 : G)⟩, fun q => Subsingleton.elim _ _⟩
  rw [Fintype.prod_unique]
  congr 1
  apply Subtype.ext
  simp



/-- The transfer commutes with post-composition by homomorphisms of commutative groups. -/
theorem transfer_comp_hom {B : Type*} [CommGroup B] [H.FiniteIndex] (f : A →* B) (ϕ : H →* A)
    (g : G) : (f.comp ϕ).transfer g = f (ϕ.transfer g) := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  rw [transfer_eq_prod_section _ Quotient.out Quotient.out_eq',
    transfer_eq_prod_section _ Quotient.out Quotient.out_eq', map_prod]
  rfl

section Topological

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A] [IsTopologicalGroup A]

/-- **The transfer to an open subgroup of finite index is continuous** (for continuous `ϕ`). -/
theorem continuous_transfer (hH : IsOpen (H : Set G)) [H.FiniteIndex] (ϕ : H →* A)
    (hϕ : Continuous ϕ) : Continuous ϕ.transfer := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set s : G ⧸ H → G := Quotient.out
  have hs : ∀ q, (s q : G ⧸ H) = q := Quotient.out_eq'
  set V : Set G := ⋂ q : G ⧸ H, (fun g => (s q)⁻¹ * g * s q) ⁻¹' (H : Set G)
  have hVo : IsOpen V := isOpen_iInter_of_finite fun q =>
    hH.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hV1 : (1 : G) ∈ V := by
    simp only [V, Set.mem_iInter, Set.mem_preimage, mul_one, inv_mul_cancel, SetLike.mem_coe]
    exact fun _ => H.one_mem
  have hmem : ∀ v ∈ V, ∀ q, (s q)⁻¹ * v * s q ∈ H := fun v hv q => Set.mem_iInter.1 hv q
  have hfix : ∀ v ∈ V, ∀ q : G ⧸ H, v⁻¹ • q = q := by
    intro v hv q
    conv_lhs => rw [← hs q]
    conv_rhs => rw [← hs q]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    have : (v⁻¹ * s q)⁻¹ * s q = (s q)⁻¹ * v * s q := by group
    rw [this]
    exact hmem v hv q
  have heq : ∀ v : V, ϕ.transfer v = ∏ q, ϕ ⟨(s q)⁻¹ * v * s q, hmem v v.2 q⟩ := by
    intro v
    rw [transfer_eq_prod_section ϕ s hs]
    refine Finset.prod_congr rfl fun q _ => congrArg ϕ (Subtype.ext ?_)
    simp only [hfix v v.2 q]
  refine continuous_of_continuousAt_one ϕ.transfer ?_
  refine (continuousOn_iff_continuous_restrict.2 ?_).continuousAt (hVo.mem_nhds hV1)
  have : V.restrict ϕ.transfer = fun v : V => ∏ q, ϕ ⟨(s q)⁻¹ * v * s q, hmem v v.2 q⟩ :=
    funext heq
  rw [this]
  refine continuous_finsetProd _ fun q _ => hϕ.comp ?_
  exact Continuous.subtype_mk (((continuous_const.mul continuous_subtype_val).mul
    continuous_const)) _

end Topological

section Equiv

variable {G' : Type*} [Group G'] (e : G ≃* G') {H' : Subgroup G'} (hHH' : H.map e.toMonoidHom = H')
include hHH'

theorem mem_iff_of_map_eq (g : G) : e g ∈ H' ↔ g ∈ H := by
  rw [← hHH', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

/-- The isomorphism `G ⧸ H ≃ G' ⧸ H'` induced by `e`. -/
def quotientEquivOfMapEq : G ⧸ H ≃ G' ⧸ H' :=
  Quotient.congr e.toEquiv fun a b => by
    change QuotientGroup.leftRel H a b ↔ QuotientGroup.leftRel H' (e a) (e b)
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← map_inv, ← map_mul,
      mem_iff_of_map_eq e hHH']

theorem quotientEquivOfMapEq_mk (g : G) :
    quotientEquivOfMapEq e hHH' (g : G ⧸ H) = (e g : G' ⧸ H') := rfl

/-- `e` restricted to `H → H'`. -/
def restrictEquiv : H →* H' :=
  (e.toMonoidHom.restrict H).codRestrict H' fun x => (mem_iff_of_map_eq e hHH' x).2 x.2

theorem coe_restrictEquiv (x : H) : (restrictEquiv e hHH' x : G') = e x := rfl

/-- **Naturality of the transfer under isomorphisms.** -/
theorem transfer_map_equiv [H.FiniteIndex] [H'.FiniteIndex] (ϕ' : H' →* A) (g : G) :
    ϕ'.transfer (e g) = (ϕ'.comp (restrictEquiv e hHH')).transfer g := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  letI : Fintype (G' ⧸ H') := Fintype.ofFinite _
  set eq := quotientEquivOfMapEq e hHH'
  set s : G ⧸ H → G := Quotient.out
  have hs : ∀ q, (s q : G ⧸ H) = q := Quotient.out_eq'
  set s' : G' ⧸ H' → G' := fun q' => e (s (eq.symm q'))
  have hs' : ∀ q', (s' q' : G' ⧸ H') = q' := by
    intro q'
    change (e (s (eq.symm q')) : G' ⧸ H') = q'
    rw [← quotientEquivOfMapEq_mk e hHH', hs, Equiv.apply_symm_apply]
  have hsmul : ∀ (x : G) (q : G ⧸ H), eq (x • q) = e x • eq q := by
    intro x q
    induction q using QuotientGroup.induction_on with | H y => ?_
    rw [MulAction.Quotient.smul_mk, quotientEquivOfMapEq_mk, quotientEquivOfMapEq_mk,
      MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul, map_mul]
  rw [transfer_eq_prod_section ϕ' s' hs', transfer_eq_prod_section _ s hs]
  refine (Fintype.prod_equiv eq _ _ fun q => ?_).symm
  have h1 : eq.symm ((e g)⁻¹ • eq q) = g⁻¹ • q := by
    rw [← map_inv, ← hsmul, Equiv.symm_apply_apply]
  simp only [MonoidHom.comp_apply, s', Equiv.symm_apply_apply, h1]
  congr 1
  apply Subtype.ext
  simp [coe_restrictEquiv, map_mul, map_inv]

end Equiv

section Trans

variable {K : Subgroup G} (hKH : K ≤ H)

/-- `ϕ : K →* A` as a homomorphism on `K` viewed inside `H`. -/
noncomputable def restrictSub (ϕ : K →* A) : K.subgroupOf H →* A :=
  ϕ.comp (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom

theorem restrictSub_apply (ϕ : K →* A) (x : K.subgroupOf H) :
    restrictSub hKH ϕ x = ϕ ⟨((x : H) : G), x.2⟩ := rfl

/-- **Transitivity of the transfer**: `Ver_{G/H} ∘ Ver_{H/K} = Ver_{G/K}`. -/
theorem transfer_transfer [H.FiniteIndex] [(K.subgroupOf H).FiniteIndex] [K.FiniteIndex]
    (ϕ : K →* A) (g : G) : (restrictSub hKH ϕ).transfer.transfer g = ϕ.transfer g := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  letI : Fintype (H ⧸ K.subgroupOf H) := Fintype.ofFinite _
  letI : Fintype (G ⧸ K) := Fintype.ofFinite _
  set s : G ⧸ H → G := Quotient.out
  have hs : ∀ q, (s q : G ⧸ H) = q := Quotient.out_eq'
  set t : H ⧸ K.subgroupOf H → H := Quotient.out
  have ht : ∀ q, (t q : H ⧸ K.subgroupOf H) = q := Quotient.out_eq'
  set e := quotientEquivProdOfLE' hKH s hs
  set u : G ⧸ K → G := fun q => s (e q).1 * t (e q).2
  have he_symm : ∀ a b, e.symm (a, b) = ((s a * t b : G) : G ⧸ K) := by
    intro a b
    conv_lhs => rw [← ht b]
    rfl
  have hu : ∀ q, (u q : G ⧸ K) = q := by
    intro q
    simp only [u]
    rw [← he_symm, Prod.mk.eta, Equiv.symm_apply_apply]
  have he_mk : ∀ w : G, e (w : G ⧸ K) = ((w : G ⧸ H),
      ((⟨(s (w : G ⧸ H))⁻¹ * w, QuotientGroup.leftRel_apply.mp
        (Quotient.exact' (hs (w : G ⧸ H)))⟩ : H) : H ⧸ K.subgroupOf H)) := fun w => rfl
  -- the action of `g⁻¹` in the product decomposition
  have he_smul : ∀ (a : G ⧸ H) (b : H ⧸ K.subgroupOf H),
      e (g⁻¹ • e.symm (a, b)) =
        (g⁻¹ • a, (⟨(s a)⁻¹ * g * s (g⁻¹ • a), section_inv_mul_mem s hs g a⟩ : H)⁻¹ • b) := by
    intro a b
    rw [he_symm, MulAction.Quotient.smul_mk, he_mk]
    have h1 : ((g⁻¹ * (s a * (t b : G)) : G) : G ⧸ H) = g⁻¹ • a := by
      conv_rhs => rw [← hs a]
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      have : (g⁻¹ * (s a * (t b : G)))⁻¹ * (g⁻¹ * s a) = ((t b : H) : G)⁻¹ := by group
      rw [this]
      exact inv_mem (t b).2
    ext1
    · exact h1
    · change ((_ : H) : H ⧸ K.subgroupOf H) = _
      conv_rhs => rw [← ht b, MulAction.Quotient.smul_mk]
      congr 1
      apply Subtype.ext
      simp only [smul_eq_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [h1]
      group
  rw [transfer_eq_prod_section ϕ u hu g, transfer_eq_prod_section _ s hs g]
  simp_rw [transfer_eq_prod_section _ t ht, restrictSub_apply]
  rw [← Fintype.prod_prod_type']
  refine (Fintype.prod_equiv e _ _ fun q => ?_).symm
  obtain ⟨⟨a, b⟩, rfl⟩ := e.symm.surjective q
  rw [Equiv.apply_symm_apply]
  congr 1
  apply Subtype.ext
  have hgq := he_smul a b
  simp only [u, hgq, Equiv.apply_symm_apply, Subgroup.coe_mul, InvMemClass.coe_inv]
  group

end Trans

end MonoidHom

/-! ### The transfer on topological abelianizations -/

namespace Iut.Reconstruction

open MonoidHom

instance isClosed_commutator_closure (X : Type*) [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] : IsClosed ((commutator X).topologicalClosure : Set X) :=
  Subgroup.isClosed_topologicalClosure _

/-- The quotient map `X → X^ab`. -/
abbrev abMk (X : Type*) [Group X] [TopologicalSpace X] [IsTopologicalGroup X] :
    X →* TopologicalAbelianization X :=
  QuotientGroup.mk' _

theorem continuous_abMk (X : Type*) [Group X] [TopologicalSpace X] [IsTopologicalGroup X] :
    Continuous (abMk X) :=
  continuous_quot_mk

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H K L : Subgroup G}

/-- `K.subgroupOf H → K → K^ab`. -/
noncomputable def abMkOf (hKH : K ≤ H) : K.subgroupOf H →* TopologicalAbelianization K :=
  (abMk K).comp (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom

theorem abMkOf_apply (hKH : K ≤ H) (x : K.subgroupOf H) :
    abMkOf hKH x = abMk K ⟨((x : H) : G), x.2⟩ := rfl

theorem continuous_abMkOf (hKH : K ≤ H) : Continuous (abMkOf hKH) :=
  (continuous_abMk K).comp
    (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)

omit [IsTopologicalGroup G] in
theorem isOpen_subgroupOf (hK : IsOpen (K : Set G)) :
    IsOpen ((K.subgroupOf H : Subgroup H) : Set H) := by
  rw [Subgroup.coe_subgroupOf]
  exact hK.preimage continuous_subtype_val

/-- **The transfer `Ver : H^ab → K^ab`** on topological abelianizations, for an open subgroup
`K ≤ H` of finite index ([AbsTopIII], Proposition 5.8 (i): the contravariant functoriality of
`G ↦ G^ab`). -/
noncomputable def verAb (hKH : K ≤ H) (hK : IsOpen (K : Set G)) [K.FiniteIndex] :
    TopologicalAbelianization H →* TopologicalAbelianization K :=
  QuotientGroup.lift _ (abMkOf hKH).transfer (by
    have hc := continuous_transfer (isOpen_subgroupOf (H := H) hK) (abMkOf hKH)
      (continuous_abMkOf hKH)
    refine Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _) ?_
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hc)

theorem verAb_mk (hKH : K ≤ H) (hK : IsOpen (K : Set G)) [K.FiniteIndex] (h : H) :
    verAb hKH hK (abMk H h) = (abMkOf hKH).transfer h := rfl

/-- **Transitivity**: `Ver_{K/L} ∘ Ver_{H/K} = Ver_{H/L}`. -/
theorem verAb_verAb (hLK : L ≤ K) (hKH : K ≤ H) (hL : IsOpen (L : Set G))
    (hK : IsOpen (K : Set G)) [L.FiniteIndex] [K.FiniteIndex]
    (x : TopologicalAbelianization H) :
    verAb hLK hL (verAb hKH hK x) = verAb (hLK.trans hKH) hL x := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ x
  change verAb hLK hL (verAb hKH hK (abMk H h)) = verAb (hLK.trans hKH) hL (abMk H h)
  rw [verAb_mk, verAb_mk, ← transfer_comp_hom]
  -- `Ver_{K/L} ∘ abMkOf hKH = (abMkOf hLK).transfer ∘ e`, `e : K.subgroupOf H ≃* K`
  set e := Subgroup.subgroupOfEquivOfLe hKH
  have hmap : ((L.subgroupOf H).subgroupOf (K.subgroupOf H)).map e.toMonoidHom =
      L.subgroupOf K := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, hx, by simp⟩
  have h1 : (verAb hLK hL).comp (abMkOf hKH) =
      ((abMkOf hLK).comp (MonoidHom.restrictEquiv e hmap)).transfer := by
    ext y
    change (abMkOf hLK).transfer (e y) = _
    rw [MonoidHom.transfer_map_equiv e hmap]
  rw [h1]
  have hLK' : L.subgroupOf H ≤ K.subgroupOf H := Subgroup.subgroupOf_mono H hLK
  have h2 : (abMkOf hLK).comp (MonoidHom.restrictEquiv e hmap) =
      MonoidHom.restrictSub hLK' (abMkOf (hLK.trans hKH)) := by
    ext y
    rfl
  rw [h2, MonoidHom.transfer_transfer]

/-- **`Ver` to a subgroup equal to `H` is the identity** (up to the identification). -/
theorem verAb_of_ge (hKH : K ≤ H) (hHK : H ≤ K) (hK : IsOpen (K : Set G)) [K.FiniteIndex]
    (h : H) : verAb hKH hK (abMk H h) = abMk K ⟨h, hHK h.2⟩ := by
  classical
  rw [verAb_mk]
  letI : Fintype (H ⧸ K.subgroupOf H) := Fintype.ofFinite _
  have hall : ∀ x : H, x ∈ K.subgroupOf H := fun x => Subgroup.mem_subgroupOf.2 (hHK x.2)
  have hs : ∀ q : H ⧸ K.subgroupOf H, ((1 : H) : H ⧸ K.subgroupOf H) = q := by
    intro q
    induction q using QuotientGroup.induction_on with | H x => ?_
    rw [QuotientGroup.eq]
    simpa using hall x
  rw [MonoidHom.transfer_eq_prod_section _ (fun _ => 1) hs]
  haveI : Unique (H ⧸ K.subgroupOf H) :=
    ⟨⟨((1 : H) : H ⧸ K.subgroupOf H)⟩, fun q => (hs q).symm⟩
  rw [Fintype.prod_unique, abMkOf_apply]
  congr 1
  apply Subtype.ext
  simp

theorem verAb_self (hH : IsOpen (H : Set G)) [H.FiniteIndex] (x : TopologicalAbelianization H) :
    verAb le_rfl hH x = x := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ x
  exact verAb_of_ge le_rfl le_rfl hH h

end Iut.Reconstruction
