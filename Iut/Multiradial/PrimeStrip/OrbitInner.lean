/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Transport
import Iut.Frobenioid.Tempered.BaseRecon

/-!
# Isomorphic functors `B(G₁)⁰ ⥤ B(G₂)⁰` of isomorphisms differ by an inner automorphism

For isomorphisms of topological groups `σ, σ' : G₁ ≃ₜ* G₂` the functors
`G₁/H ↦ G₂/σ(H)` and `G₁/H ↦ G₂/σ'(H)` (`OrbitObj.isoFunctor`) are isomorphic iff
`σ' = g⁻¹ σ(−) g` for some `g ∈ G₂`, provided `G₂` is Hausdorff, has a basis of open normal
subgroups and is complete for them (`IsONSComplete`; e.g. profinite groups,
`isONSComplete_of_compact`, or the tempered `Π_v`, `PiTpONS.lean`). This is the uniqueness half
of [Mzk2], Proposition 3.2 / [SemiAnbd], Proposition 3.2 in functorial form
(`OrbitIsoRecon.lean` gives the existence half): the components of a natural isomorphism give
cosets `y_N σ'(N)` (`N` open normal in `G₁`) forming a directed family of closed sets, a common
point `g` of which conjugates `σ` into `σ'` modulo every `σ'(N)`.

The converse is `OrbitObj.mapFunctorConjIso`.
-/

noncomputable section

namespace Iut

namespace Frobenioid

open CategoryTheory

universe u u'

section Compact

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **Compact groups are complete for their open normal subgroups.** -/
theorem isONSComplete_of_compact [CompactSpace G] : IsONSComplete G := by
  intro S hS hd hcl _
  have hne : ∀ s ∈ S, s.Nonempty := fun s hs => (hcl s hs).1
  rw [Set.sInter_eq_iInter]
  haveI : Nonempty S := hS.to_subtype
  exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed (fun s : S => (s : Set G))
    (fun a b => by
      obtain ⟨c, hc, hca, hcb⟩ := hd a a.2 b b.2
      exact ⟨⟨c, hc⟩, hca, hcb⟩)
    (fun s => hne s s.2) (fun s => (hcl s s.2).2.isCompact) (fun s => (hcl s s.2).2)

end Compact

namespace OrbitObj

section Inner

variable {G₁ : Type u} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  {G₂ : Type u'} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  (σ σ' : G₁ ≃ₜ* G₂) (β : OrbitObj.isoFunctor σ ⟶ OrbitObj.isoFunctor σ')

/-- The image `σ(N)` of an open normal subgroup, as an open normal subgroup of `G₂`. -/
def onsMap (N : OpenNormalSubgroup G₁) : OpenNormalSubgroup G₂ where
  toSubgroup := N.toSubgroup.map (σ' : G₁ →* G₂)
  isOpen' := isOpen_map_of_continuousMulEquiv σ' _ N.isOpen
  isNormal' := N.isNormal'.map _ σ'.surjective

/-- The preimage `σ⁻¹(N')` of an open normal subgroup. -/
def onsComap (N : OpenNormalSubgroup G₂) : OpenNormalSubgroup G₁ where
  toSubgroup := N.toSubgroup.comap (σ' : G₁ →* G₂)
  isOpen' := N.isOpen.preimage σ'.continuous
  isNormal' := N.isNormal'.comap _

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
lemma onsMap_onsComap (N : OpenNormalSubgroup G₂) :
    ((onsMap σ' (onsComap σ' N)).toSubgroup : Subgroup G₂) = N.toSubgroup :=
  Subgroup.map_comap_eq_self_of_surjective σ'.surjective _

omit [IsTopologicalGroup G₁] in
lemma conjCond (N : OpenNormalSubgroup G₁) (h : G₁) :
    ∀ a ∈ (ofONS N).H, h⁻¹ * a * h ∈ (ofONS N).H := fun a ha => by
  simpa using N.isNormal'.conj_mem a ha h⁻¹

/-- The representative `y_N` of the component of `β` at `G₁/N`. -/
abbrev yN (N : OpenNormalSubgroup G₁) : G₂ := OrbitHom.rep (β.app (ofONS N))

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
/-- `y_N⁻¹ σ(N) y_N ⊆ σ'(N)`. -/
lemma conj_yN_mem (N : OpenNormalSubgroup G₁) {n : G₁} (hn : n ∈ N) :
    (yN σ σ' β N)⁻¹ * (σ n * yN σ σ' β N) ∈ (onsMap σ' N).toSubgroup :=
  OrbitHom.conj_mem (β.app (ofONS N)) (Subgroup.mem_map_of_mem _ hn)

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
/-- **Naturality for `xN ↦ xhN`**: `σ'(r) ≡ y_N⁻¹ σ(r) y_N` modulo `σ'(N)` for the
representative `r` of right multiplication by `h`. -/
lemma natural_rightMul (N : OpenNormalSubgroup G₁) (h : G₁) :
    let r := OrbitHom.rep (OrbitHom.ofRightMul (ofONS N) (ofONS N) h
      (conjCond N h))
    (yN σ σ' β N)⁻¹ * (σ r)⁻¹ * yN σ σ' β N * σ' r ∈ (onsMap σ' N).toSubgroup := by
  intro r
  set f := OrbitHom.ofRightMul (ofONS N) (ofONS N) h
      (conjCond N h)
  have hnat := congrArg (fun φ => OrbitHom.toFun φ (QuotientGroup.mk 1)) (β.naturality f)
  have lhs : ((isoFunctor σ).map f ≫ β.app (ofONS N)).toFun (QuotientGroup.mk 1) =
      QuotientGroup.mk (σ r * yN σ σ' β N) := by
    change (β.app (ofONS N)).toFun (QuotientGroup.mk (1 * σ r)) = _
    rw [one_mul]
    exact OrbitHom.apply_mk_of_eq _ (OrbitHom.mk_rep _).symm _
  have rhs : (β.app (ofONS N) ≫ (isoFunctor σ').map f).toFun (QuotientGroup.mk 1) =
      QuotientGroup.mk (yN σ σ' β N * σ' r) := by
    change ((isoFunctor σ').map f).toFun ((β.app (ofONS N)).toFun (QuotientGroup.mk 1)) = _
    rw [← OrbitHom.mk_rep (β.app (ofONS N))]
    rfl
  have := QuotientGroup.eq.1 (lhs.symm.trans (hnat.trans rhs))
  change (σ r * yN σ σ' β N)⁻¹ * (yN σ σ' β N * σ' r) ∈ (onsMap σ' N).toSubgroup at this
  convert this using 1
  group

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
/-- **Naturality for `G₁/N₁ → G₁/N₂`**: `y_{N₁} ≡ y_{N₂}` modulo `σ'(N₂)`. -/
lemma yN_proj {N₁ N₂ : OpenNormalSubgroup G₁} (hle : N₁ ≤ N₂) :
    (yN σ σ' β N₂)⁻¹ * yN σ σ' β N₁ ∈ (onsMap σ' N₂).toSubgroup := by
  set f := OrbitHom.ofRightMul (ofONS N₁) (ofONS N₂) 1 
    (fun a ha => by rw [inv_one, one_mul, mul_one]; exact hle ha)
  have hr : OrbitHom.rep f ∈ N₂ := by
    have := OrbitHom.mk_rep f
    rw [OrbitHom.ofRightMul_mk, mul_one] at this
    exact QuotientGroup.eq_one_iff _ |>.1 this
  have hnat := congrArg (fun φ => OrbitHom.toFun φ (QuotientGroup.mk 1)) (β.naturality f)
  have h1 : (QuotientGroup.mk (1 * σ (OrbitHom.rep f)) :
      G₂ ⧸ ((isoFunctor σ).obj (ofONS N₂)).H) = QuotientGroup.mk 1 :=
    QuotientGroup.eq.2 (by
      rw [one_mul, mul_one]
      exact Subgroup.inv_mem _ (Subgroup.mem_map_of_mem (σ : G₁ →* G₂) hr))
  have lhs : ((isoFunctor σ).map f ≫ β.app (ofONS N₂)).toFun (QuotientGroup.mk 1) =
      QuotientGroup.mk (yN σ σ' β N₂) := by
    change (β.app (ofONS N₂)).toFun (QuotientGroup.mk (1 * σ (OrbitHom.rep f))) = _
    rw [h1]
    exact (OrbitHom.mk_rep _).symm
  have rhs : (β.app (ofONS N₁) ≫ (isoFunctor σ').map f).toFun (QuotientGroup.mk 1) =
      QuotientGroup.mk (yN σ σ' β N₁ * σ' (OrbitHom.rep f)) := by
    change ((isoFunctor σ').map f).toFun ((β.app (ofONS N₁)).toFun (QuotientGroup.mk 1)) = _
    rw [← OrbitHom.mk_rep (β.app (ofONS N₁))]
    rfl
  have hnat := lhs.symm.trans (hnat.trans rhs)
  have := QuotientGroup.eq.1 hnat
  have hs : σ' (OrbitHom.rep f) ∈ (onsMap σ' N₂).toSubgroup := Subgroup.mem_map_of_mem _ hr
  have e : (yN σ σ' β N₂)⁻¹ * yN σ σ' β N₁ =
      ((yN σ σ' β N₂)⁻¹ * (yN σ σ' β N₁ * σ' (OrbitHom.rep f))) * (σ' (OrbitHom.rep f))⁻¹ := by
    group
  rw [e]
  exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ hs)

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] in
lemma quot_aux {Q : Type*} [Group Q] {y g sx sr s'x s'r : Q} (h1 : y⁻¹ * sr⁻¹ * y * s'r = 1)
    (h2 : y⁻¹ * g = 1) (h3 : s'x⁻¹ * s'r = 1) (h4 : y⁻¹ * (sx⁻¹ * sr * y) = 1) :
    g⁻¹ * sx⁻¹ * g * s'x = 1 := by
  rw [inv_mul_eq_one] at h2 h3 h4
  subst h2 h3
  have h5 : sx⁻¹ * sr = 1 := mul_right_cancel ((h4.symm.trans (one_mul y).symm))
  rw [inv_mul_eq_one] at h5
  subst h5
  exact h1

variable [T2Space G₂] (hb : HasONSBasis G₂) (hc : IsONSComplete G₂)

omit [IsTopologicalGroup G₁] in
include β hb hc in
/-- **Isomorphic functors of isomorphisms differ by an inner automorphism**: a natural
transformation `G₁/H ↦ G₂/σ(H)` ⟶ `G₁/H ↦ G₂/σ'(H)` forces `σ' = g⁻¹ σ(−) g`. -/
theorem exists_conj_of_natTrans : ∃ g : G₂, ∀ x, σ' x = g⁻¹ * σ x * g := by
  let S : Set (Set G₂) := Set.range fun N : OpenNormalSubgroup G₁ =>
    {z | (yN σ σ' β N)⁻¹ * z ∈ (onsMap σ' N).toSubgroup}
  have hmemS : ∀ (N : OpenNormalSubgroup G₁) z,
      z ∈ {z | (yN σ σ' β N)⁻¹ * z ∈ (onsMap σ' N).toSubgroup} ↔
        (yN σ σ' β N)⁻¹ * z ∈ (onsMap σ' N).toSubgroup := fun _ _ => Iff.rfl
  have hsub : ∀ {N₁ N₂ : OpenNormalSubgroup G₁}, N₁ ≤ N₂ →
      {z | (yN σ σ' β N₁)⁻¹ * z ∈ (onsMap σ' N₁).toSubgroup} ⊆
        {z | (yN σ σ' β N₂)⁻¹ * z ∈ (onsMap σ' N₂).toSubgroup} := fun {N₁ N₂} hle z hz => by
    have h1 : (yN σ σ' β N₁)⁻¹ * z ∈ (onsMap σ' N₂).toSubgroup :=
      Subgroup.map_mono hle hz
    have e : (yN σ σ' β N₂)⁻¹ * z =
        ((yN σ σ' β N₂)⁻¹ * yN σ σ' β N₁) * ((yN σ σ' β N₁)⁻¹ * z) := by group
    rw [hmemS, e]
    exact Subgroup.mul_mem _ (yN_proj σ σ' β hle) h1
  obtain ⟨g, hg⟩ : (⋂₀ S).Nonempty := by
    haveI : Nonempty (OpenNormalSubgroup G₁) :=
      ⟨{ toOpenSubgroup := ⊤, isNormal' := inferInstanceAs (⊤ : Subgroup G₁).Normal }⟩
    refine hc S (Set.range_nonempty _) ?_ ?_ ?_
    · rintro _ ⟨N₁, rfl⟩ _ ⟨N₂, rfl⟩
      exact ⟨_, ⟨N₁ ⊓ N₂, rfl⟩, hsub inf_le_left, hsub inf_le_right⟩
    · rintro _ ⟨N, rfl⟩
      refine ⟨⟨yN σ σ' β N, by simp⟩, ?_⟩
      change IsClosed ((fun z => (yN σ σ' β N)⁻¹ * z) ⁻¹' ((onsMap σ' N).toSubgroup : Set G₂))
      exact ((onsMap σ' N).toSubgroup.isClosed_of_isOpen (onsMap σ' N).isOpen).preimage
        (continuous_const.mul continuous_id)
    · intro N'
      refine ⟨_, ⟨onsComap σ' N', rfl⟩, fun x hx y hy => ?_⟩
      change (yN σ σ' β (onsComap σ' N'))⁻¹ * x ∈ (onsMap σ' (onsComap σ' N')).toSubgroup at hx
      change (yN σ σ' β (onsComap σ' N'))⁻¹ * y ∈ (onsMap σ' (onsComap σ' N')).toSubgroup at hy
      have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy
      rw [onsMap_onsComap] at h
      have e : x⁻¹ * y = ((yN σ σ' β (onsComap σ' N'))⁻¹ * x)⁻¹ *
          ((yN σ σ' β (onsComap σ' N'))⁻¹ * y) := by group
      rw [e]
      exact h
  have hgN : ∀ N : OpenNormalSubgroup G₁, (yN σ σ' β N)⁻¹ * g ∈ (onsMap σ' N).toSubgroup :=
    fun N => hg _ ⟨N, rfl⟩
  refine ⟨g, fun x => ?_⟩
  have key : ∀ N : OpenNormalSubgroup G₂, (g⁻¹ * σ x * g)⁻¹ * σ' x ∈ N := fun N' => by
    set N := onsComap σ' N'
    haveI : (onsMap σ' N).toSubgroup.Normal := (onsMap σ' N).isNormal'
    set r := OrbitHom.rep (OrbitHom.ofRightMul (ofONS N) (ofONS N) x
      (conjCond N x)) with hr_def
    have hr : x⁻¹ * r ∈ N := by
      have := OrbitHom.mk_rep (OrbitHom.ofRightMul (ofONS N) (ofONS N) x
        (conjCond N x))
      rw [OrbitHom.ofRightMul_mk, one_mul] at this
      exact QuotientGroup.eq.1 this.symm
    -- work in `G₂ ⧸ σ'(N)`
    let q : G₂ →* G₂ ⧸ (onsMap σ' N).toSubgroup := QuotientGroup.mk' _
    have hq : ∀ z, q z = 1 ↔ z ∈ (onsMap σ' N).toSubgroup := fun z => QuotientGroup.eq_one_iff z
    set y := yN σ σ' β N
    have h1 : q (y⁻¹ * (σ r)⁻¹ * y * σ' r) = 1 := (hq _).2 (natural_rightMul σ σ' β N x)
    have h2 : q (y⁻¹ * g) = 1 := (hq _).2 (hgN N)
    have h3 : q (σ' (x⁻¹ * r)) = 1 := (hq _).2 (Subgroup.mem_map_of_mem _ hr)
    have h4 : q (y⁻¹ * (σ (x⁻¹ * r) * y)) = 1 := (hq _).2 (conj_yN_mem σ σ' β N hr)
    simp only [map_mul, map_inv] at h1 h2 h3 h4
    have e : q ((g⁻¹ * σ x * g)⁻¹ * σ' x) = 1 := by
      rw [show (g⁻¹ * σ x * g)⁻¹ * σ' x = g⁻¹ * (σ x)⁻¹ * g * σ' x by group]
      simp only [map_mul, map_inv]
      exact quot_aux h1 h2 h3 h4
    have hmem := (hq _).1 e
    rw [onsMap_onsComap] at hmem
    exact hmem
  have := eq_one_of_forall_mem_ons hb key
  calc σ' x = (g⁻¹ * σ x * g) * ((g⁻¹ * σ x * g)⁻¹ * σ' x) := by group
    _ = g⁻¹ * σ x * g := by rw [this, mul_one]

end Inner

end OrbitObj

end Frobenioid

end Iut
