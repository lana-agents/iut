/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GaloisRecon

/-!
# Tempered groups from their base categories `B^temp(Π)⁰` ([SemiAnbd], Proposition 3.2)

[EtTh], proof of Theorem 5.6, passes from a self-equivalence of a tempered Frobenioid to an
outer automorphism of the tempered fundamental group `Π^tp` through the "Grothendieck Conjecture
for connected temperoids", [SemiAnbd], Proposition 3.2: for tempered groups `Π₁`, `Π₂`, the
isomorphism classes of morphisms `B^temp(Π₁) → B^temp(Π₂)` correspond to continuous outer
homomorphisms `Π₁ → Π₂` (the proof there is "formally entirely similar" to the anabelioid case,
Galois objects being preserved). `Iut/Frobenioid/GaloisRecon.lean` proves the profinite case for
the categories of connected objects `OrbitObj G = B(G)⁰`, using compactness three times
(compatible base points, the common point of a nested family of cosets, closedness of the image).
Here compactness is replaced by the properties of tempered groups ([SemiAnbd], Definition 3.1,
Remarks 3.1.1, 3.1.2: inverse limits of countable discrete groups, with a basis of open normal
subgroups):

* `HasONSBasis G`: the open normal subgroups form a basis of neighbourhoods of `1`;
* `HasONSChain G`: a countable decreasing cofinal chain of open normal subgroups (countably
  indexed inverse systems, [SemiAnbd], Remark 3.1.1);
* `IsONSComplete G`: completeness for the uniformity of open normal subgroups, in the form "a
  directed family of nonempty closed sets which is eventually contained in a coset of every open
  normal subgroup has a common point" (`G = lim G/N`).

**Theorem** (`OrbitObj.exists_continuousMulEquiv_temp`). For Hausdorff topological groups
`G₁`, `G₂` with these properties (`HasONSChain` for `G₁` only) and an equivalence
`F : B(G₁)⁰ ≌ B(G₂)⁰`, there are an isomorphism of topological groups `α : G₁ ≅ G₂` and
compatible base points `x_N ∈ F(G₁/N)` with `F(G₁/N) = G₂/α(N)` and
`F(rmul g)(x_N) = α(g)·x_N` (as in the profinite case).

**Theorem** (`OrbitObj.isSlim_temp`). `B(G)⁰` is slim for a slim group `G` with `HasONSBasis`
and `IsONSComplete` (the tempered analogue of `OrbitObj.isSlim`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe u u'

section TempGroup

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The open normal subgroups form a basis of neighbourhoods of `1`. -/
def HasONSBasis : Prop :=
  ∀ ⦃U : Set G⦄, IsOpen U → (1 : G) ∈ U → ∃ N : OpenNormalSubgroup G, (N : Set G) ⊆ U

/-- A countable decreasing chain of open normal subgroups, cofinal among all of them. -/
def HasONSChain : Prop :=
  ∃ s : ℕ → OpenNormalSubgroup G, Antitone s ∧ ∀ N : OpenNormalSubgroup G, ∃ k, s k ≤ N

/-- **Completeness** for the uniformity of open normal subgroups: a nonempty directed family of
nonempty closed sets which, for every open normal subgroup `N`, contains a member inside a left
coset of `N`, has a common point. -/
def IsONSComplete : Prop :=
  ∀ S : Set (Set G), S.Nonempty → DirectedOn (· ⊇ ·) S → (∀ s ∈ S, s.Nonempty ∧ IsClosed s) →
    (∀ N : OpenNormalSubgroup G, ∃ s ∈ S, ∀ x ∈ s, ∀ y ∈ s, x⁻¹ * y ∈ N) → (⋂₀ S).Nonempty

variable {G}

/-- In a Hausdorff group with a basis of open normal subgroups, these intersect in `1`. -/
lemma eq_one_of_forall_mem_ons [T2Space G] (hb : HasONSBasis G) {k : G}
    (h : ∀ N : OpenNormalSubgroup G, k ∈ N) : k = 1 := by
  by_contra hk
  obtain ⟨N, hN⟩ := hb (isOpen_compl_singleton (x := k)) (by simpa [eq_comm] using hk)
  exact hN (h N) rfl

/-- A profinite group has a basis of open normal subgroups. -/
lemma hasONSBasis_of_profinite [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] : HasONSBasis G :=
  fun _ hU h1 => OrbitObj.exists_ons_le hU h1

end TempGroup

namespace OrbitObj

section Recon

variable {G₁ : Type u} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
variable {G₂ : Type u'} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
variable (F : OrbitObj G₁ ⥤ OrbitObj G₂) [F.IsEquivalence]

/-- The image `H'_N` of `G₁/N` (with `F(G₁/N) = G₂/H'_N`). -/
abbrev tHc (N : OpenNormalSubgroup G₁) : Subgroup G₂ := (F.obj (ofONS N)).H

instance normal_tHc (N : OpenNormalSubgroup G₁) : (tHc F N).Normal :=
  (isGaloisObj_iff _).mp (((isGaloisObj_iff (ofONS N)).mpr N.isNormal').map F)

/-! #### Compatible base points along a countable chain -/

section Points

variable (s : ℕ → OpenNormalSubgroup G₁) (hs : Antitone s)

/-- Base points `x_k ∈ F(G₁/s_k)` along the chain, chosen successively (the transition maps are
surjective). -/
noncomputable def chainPt : (k : ℕ) → G₂ ⧸ tHc F (s k)
  | 0 => QuotientGroup.mk 1
  | k + 1 => (OrbitHom.surjective (F.map (projN (hs (Nat.le_succ k))))
      (chainPt k)).choose

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [F.IsEquivalence] in
lemma chainPt_succ (k : ℕ) :
    (F.map (projN (hs (Nat.le_succ k)))).toFun (chainPt F s hs (k + 1)) = chainPt F s hs k :=
  (OrbitHom.surjective (F.map (projN (hs (Nat.le_succ k)))) (chainPt F s hs k)).choose_spec

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [F.IsEquivalence] in
lemma chainPt_compat {k k' : ℕ} (h : k ≤ k') :
    (F.map (projN (hs h))).toFun (chainPt F s hs k') = chainPt F s hs k := by
  induction k', h using Nat.le_induction with
  | base => rw [projN_refl, F.map_id]; rfl
  | succ k' hkk' ih =>
    rw [← projN_comp (hs (Nat.le_succ k')) (hs hkk'), F.map_comp]
    change (F.map (projN (hs hkk'))).toFun
      ((F.map (projN (hs (Nat.le_succ k')))).toFun (chainPt F s hs (k' + 1))) = _
    rw [chainPt_succ, ih]

variable (hcof : ∀ N : OpenNormalSubgroup G₁, ∃ k, s k ≤ N)

/-- **Compatible base points** `x_N ∈ F(G₁/N)` for all open normal `N`. -/
noncomputable def tpt (N : OpenNormalSubgroup G₁) : G₂ ⧸ tHc F N :=
  (F.map (projN (hcof N).choose_spec)).toFun (chainPt F s hs (hcof N).choose)

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [F.IsEquivalence] in
lemma tpt_eq (N : OpenNormalSubgroup G₁) {k : ℕ} (h : s k ≤ N) :
    tpt F s hs hcof N = (F.map (projN h)).toFun (chainPt F s hs k) := by
  have key : ∀ (j m : ℕ) (hj : s j ≤ N) (hjm : j ≤ m),
      (F.map (projN hj)).toFun (chainPt F s hs j) =
        (F.map (projN ((hs hjm).trans hj))).toFun (chainPt F s hs m) := by
    intro j m hj hjm
    rw [← chainPt_compat F s hs hjm, ← projN_comp (hs hjm) hj, F.map_comp]
    rfl
  unfold tpt
  rw [key _ (max k (hcof N).choose) _ (le_max_right _ _), key k (max k (hcof N).choose) h
    (le_max_left _ _)]

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [F.IsEquivalence] in
lemma tpt_compat {N M : OpenNormalSubgroup G₁} (h : N ≤ M) :
    (F.map (projN h)).toFun (tpt F s hs hcof N) = tpt F s hs hcof M := by
  rw [tpt_eq F s hs hcof N (hcof N).choose_spec,
    tpt_eq F s hs hcof M ((hcof N).choose_spec.trans h), ← projN_comp (hcof N).choose_spec h,
    F.map_comp]
  rfl

end Points

/-! #### The homomorphism -/

variable (s : ℕ → OpenNormalSubgroup G₁) (hs : Antitone s)
  (hcof : ∀ N : OpenNormalSubgroup G₁, ∃ k, s k ≤ N)

/-- The coset `{h : h·x_N = F(rmul g)(x_N)}`. -/
def tcoset (g : G₁) (N : OpenNormalSubgroup G₁) : Set G₂ :=
  {h | h • tpt F s hs hcof N = (F.map (rmul N g)).toFun (tpt F s hs hcof N)}

lemma tsmul_eq_smul_iff {N : OpenNormalSubgroup G₁} (h h' : G₂) (x : G₂ ⧸ tHc F N) :
    h • x = h' • x ↔ h⁻¹ * h' ∈ tHc F N := by
  rw [← SetLike.ext_iff.mp (stabilizer_eq_of_normal (H := tHc F N) x),
    MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, eq_comm]

omit [IsTopologicalGroup G₁] [F.IsEquivalence] in
lemma isClosed_tcoset (g : G₁) (N : OpenNormalSubgroup G₁) :
    IsClosed (tcoset F s hs hcof g N) := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (tpt F s hs hcof N)
  obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective ((F.map (rmul N g)).toFun (tpt F s hs hcof N))
  have : tcoset F s hs hcof g N = (fun h => (h * c)⁻¹ * d) ⁻¹' (tHc F N : Set G₂) := by
    ext h
    simp only [tcoset, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    rw [← hd, ← hc, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  rw [this]
  exact (Subgroup.isClosed_of_isOpen _ (F.obj (ofONS N)).isOpen).preimage (by fun_prop)

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [F.IsEquivalence] in
lemma tcoset_nonempty (g : G₁) (N : OpenNormalSubgroup G₁) :
    (tcoset F s hs hcof g N).Nonempty := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (tpt F s hs hcof N)
  obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective ((F.map (rmul N g)).toFun (tpt F s hs hcof N))
  refine ⟨d * c⁻¹, ?_⟩
  simp only [tcoset, Set.mem_setOf_eq]
  rw [← hd, ← hc, MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel_right]

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [F.IsEquivalence] in
lemma tcoset_mono (g : G₁) {N M : OpenNormalSubgroup G₁} (hNM : N ≤ M) :
    tcoset F s hs hcof g N ⊆ tcoset F s hs hcof g M := by
  intro h hh
  simp only [tcoset, Set.mem_setOf_eq] at hh ⊢
  have := congrArg (F.map (projN hNM)).toFun hh
  rw [OrbitHom.map_smul, tpt_compat] at this
  rw [this]
  change ((F.map (rmul N g)) ≫ F.map (projN hNM)).toFun (tpt F s hs hcof N) = _
  rw [← F.map_comp, rmul_projN, F.map_comp]
  change (F.map (rmul M g)).toFun ((F.map (projN hNM)).toFun (tpt F s hs hcof N)) = _
  rw [tpt_compat]

/-- Cofinality: every open normal subgroup of `G₂` contains some `H'_N`. -/
lemma exists_tHc_le (h₁b : HasONSBasis G₁) (K : OpenNormalSubgroup G₂) :
    ∃ N : OpenNormalSubgroup G₁, tHc F N ≤ K.toSubgroup := by
  let B := F.objPreimage (ofONS K)
  let e : F.obj B ≅ ofONS K := F.objObjPreimageIso (ofONS K)
  obtain ⟨N, hN⟩ := h₁b B.isOpen B.H.one_mem
  refine ⟨N, ?_⟩
  let f : F.obj (ofONS N) ⟶ ofONS K := F.map (proj B (fun _ hx => hN hx)) ≫ e.hom
  have := stabilizer_le_map f (QuotientGroup.mk 1)
  rwa [stabilizer_eq_of_normal, stabilizer_eq_of_normal (H := K.toSubgroup)] at this

lemma eq_of_mem_tcoset [T2Space G₂] (h₁b : HasONSBasis G₁) (h₂b : HasONSBasis G₂) {g : G₁}
    {h h' : G₂}
    (hh : ∀ N, h ∈ tcoset F s hs hcof g N) (hh' : ∀ N, h' ∈ tcoset F s hs hcof g N) :
    h = h' := by
  have hk : ∀ N, h⁻¹ * h' ∈ tHc F N := fun N =>
    (tsmul_eq_smul_iff F h h' (tpt F s hs hcof N)).mp ((hh N).trans (hh' N).symm)
  have : h⁻¹ * h' = 1 := eq_one_of_forall_mem_ons h₂b fun K => by
    obtain ⟨N, hN⟩ := exists_tHc_le F h₁b K
    exact hN (hk N)
  exact inv_mul_eq_one.mp this

lemma exists_mem_tcoset (h₁b : HasONSBasis G₁) (h₂c : IsONSComplete G₂) (g : G₁) :
    ∃ h : G₂, ∀ N, h ∈ tcoset F s hs hcof g N := by
  obtain ⟨h, hh⟩ := h₂c (Set.range (tcoset F s hs hcof g)) ⟨_, s 0, rfl⟩
    (by
      rintro _ ⟨N, rfl⟩ _ ⟨M, rfl⟩
      exact ⟨_, ⟨N ⊓ M, rfl⟩, tcoset_mono F s hs hcof g inf_le_left,
        tcoset_mono F s hs hcof g inf_le_right⟩)
    (by
      rintro _ ⟨N, rfl⟩
      exact ⟨tcoset_nonempty F s hs hcof g N, isClosed_tcoset F s hs hcof g N⟩)
    (by
      intro K
      obtain ⟨N, hN⟩ := exists_tHc_le F h₁b K
      refine ⟨_, ⟨N, rfl⟩, fun x hx y hy => hN ?_⟩
      exact (tsmul_eq_smul_iff F x y (tpt F s hs hcof N)).mp (hx.trans hy.symm))
  exact ⟨h, fun N => hh _ ⟨N, rfl⟩⟩

variable [T2Space G₂] (h₁b : HasONSBasis G₁) (h₂b : HasONSBasis G₂) (h₂c : IsONSComplete G₂)

/-- The map `φ : G₁ → G₂`. -/
noncomputable def tphi₀ (g : G₁) : G₂ := (exists_mem_tcoset F s hs hcof h₁b h₂c g).choose

omit [T2Space G₂] in
lemma tphi₀_smul (g : G₁) (N : OpenNormalSubgroup G₁) :
    tphi₀ F s hs hcof h₁b h₂c g • tpt F s hs hcof N =
      (F.map (rmul N g)).toFun (tpt F s hs hcof N) :=
  (exists_mem_tcoset F s hs hcof h₁b h₂c g).choose_spec N

/-- `φ` as a homomorphism. -/
noncomputable def tphi : G₁ →* G₂ where
  toFun := tphi₀ F s hs hcof h₁b h₂c
  map_one' := eq_of_mem_tcoset F s hs hcof h₁b h₂b
    (tphi₀_smul F s hs hcof h₁b h₂c 1) fun N => by
      simp only [tcoset, Set.mem_setOf_eq, one_smul]
      rw [(rmul_eq_id_iff N 1).mpr N.toSubgroup.one_mem, F.map_id]
      rfl
  map_mul' g₁ g₂ := eq_of_mem_tcoset F s hs hcof h₁b h₂b
    (tphi₀_smul F s hs hcof h₁b h₂c (g₁ * g₂)) fun N => by
      simp only [tcoset, Set.mem_setOf_eq]
      rw [mul_smul, tphi₀_smul, ← OrbitHom.map_smul, tphi₀_smul, ← rmul_mul, F.map_comp]
      rfl

lemma tphi_smul (g : G₁) (N : OpenNormalSubgroup G₁) :
    tphi F s hs hcof h₁b h₂b h₂c g • tpt F s hs hcof N =
      (F.map (rmul N g)).toFun (tpt F s hs hcof N) := tphi₀_smul F s hs hcof h₁b h₂c g N

lemma tphi_mem_tHc_iff (g : G₁) (N : OpenNormalSubgroup G₁) :
    tphi F s hs hcof h₁b h₂b h₂c g ∈ tHc F N ↔ g ∈ N := by
  rw [← rmul_eq_id_iff]
  constructor
  · intro h
    have hfix : (F.map (rmul N g)).toFun (tpt F s hs hcof N) = tpt F s hs hcof N := by
      rw [← tphi_smul]
      exact (tsmul_eq_smul_iff F (tphi F s hs hcof h₁b h₂b h₂c g) 1 _).mpr (by simpa using h)
        |>.trans (one_smul _ _)
    apply F.map_injective
    rw [F.map_id]
    exact eq_id_of_fix _ hfix
  · intro h
    have := tphi_smul F s hs hcof h₁b h₂b h₂c g N
    rw [h, F.map_id] at this
    have h1 : tphi F s hs hcof h₁b h₂b h₂c g • tpt F s hs hcof N =
        (1 : G₂) • tpt F s hs hcof N := this.trans (one_smul _ _).symm
    simpa using (tsmul_eq_smul_iff F _ _ _).mp h1

lemma continuous_tphi : Continuous (tphi F s hs hcof h₁b h₂b h₂c) := by
  refine continuous_of_continuousAt_one _ ?_
  intro U hU
  rw [map_one] at hU
  obtain ⟨V, hVU, hV, h1⟩ := mem_nhds_iff.mp hU
  obtain ⟨K, hK⟩ := h₂b hV h1
  obtain ⟨N, hN⟩ := exists_tHc_le F h₁b K
  refine Filter.mem_map.mpr (Filter.mem_of_superset (N.isOpen.mem_nhds N.toSubgroup.one_mem)
    fun g hg => ?_)
  exact hVU (hK (hN ((tphi_mem_tHc_iff F s hs hcof h₁b h₂b h₂c g N).mpr hg)))

lemma tphi_injective [T2Space G₁] : Function.Injective (tphi F s hs hcof h₁b h₂b h₂c) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  exact eq_one_of_forall_mem_ons h₁b fun N =>
    (tphi_mem_tHc_iff F s hs hcof h₁b h₂b h₂c g N).mp (by rw [hg]; exact one_mem _)

/-- **Surjectivity** (completeness of `G₁`): for `h ∈ G₂`, the cosets
`{g : F(rmul g)(x_N) = h·x_N}` of the `N` have a common point. -/
lemma tphi_surjective (h₁c : IsONSComplete G₁) :
    Function.Surjective (tphi F s hs hcof h₁b h₂b h₂c) := by
  intro h
  set φ := tphi F s hs hcof h₁b h₂b h₂c
  set x := tpt F s hs hcof
  let T : OpenNormalSubgroup G₁ → Set G₁ := fun N => {g | φ g • x N = h • x N}
  have hTmem : ∀ N g g', g ∈ T N → (g' ∈ T N ↔ g⁻¹ * g' ∈ N) := by
    intro N g g' hg
    change φ g • x N = h • x N at hg
    change φ g' • x N = h • x N ↔ _
    rw [← hg, eq_comm, tsmul_eq_smul_iff, ← map_inv, ← map_mul, tphi_mem_tHc_iff]
  have hTne : ∀ N, (T N).Nonempty := by
    intro N
    obtain ⟨ψ, hψ⟩ := exists_endo (A := F.obj (ofONS N)) (x N) (h • x N)
    obtain ⟨g, hg⟩ := exists_rmul_eq N (F.preimage ψ)
    refine ⟨g, ?_⟩
    change φ g • x N = h • x N
    rw [tphi_smul, ← hg, F.map_preimage, hψ]
  have hTmono : ∀ {N M : OpenNormalSubgroup G₁}, N ≤ M → T N ⊆ T M := by
    intro N M hNM g hg
    change φ g • x N = h • x N at hg
    change φ g • x M = h • x M
    have := congrArg (F.map (projN hNM)).toFun hg
    rwa [OrbitHom.map_smul, OrbitHom.map_smul, tpt_compat] at this
  have hTcl : ∀ N, IsClosed (T N) := by
    intro N
    obtain ⟨g, hg⟩ := hTne N
    have : T N = (fun g' => g⁻¹ * g') ⁻¹' (N.toSubgroup : Set G₁) := by
      ext g'
      exact hTmem N g g' hg
    rw [this]
    exact (Subgroup.isClosed_of_isOpen _ N.isOpen).preimage (by fun_prop)
  obtain ⟨g, hg⟩ := h₁c (Set.range T) ⟨_, s 0, rfl⟩
    (by
      rintro _ ⟨N, rfl⟩ _ ⟨M, rfl⟩
      exact ⟨_, ⟨N ⊓ M, rfl⟩, hTmono inf_le_left, hTmono inf_le_right⟩)
    (by rintro _ ⟨N, rfl⟩; exact ⟨hTne N, hTcl N⟩)
    (fun K => ⟨_, ⟨K, rfl⟩, fun a ha b hb => by
      have h₁ := (hTmem K a a ha).1 ha
      have h₂ := (hTmem K a b ha).1 hb
      exact h₂⟩)
  refine ⟨g, ?_⟩
  have hgN : ∀ N, φ g • x N = h • x N := fun N => hg _ ⟨N, rfl⟩
  have : (φ g)⁻¹ * h = 1 := eq_one_of_forall_mem_ons h₂b fun K => by
    obtain ⟨N, hN⟩ := exists_tHc_le F h₁b K
    exact hN ((tsmul_eq_smul_iff F _ _ _).mp (hgN N))
  exact inv_mul_eq_one.mp this

lemma tHc_eq_map (h₁c : IsONSComplete G₁) (N : OpenNormalSubgroup G₁) :
    tHc F N = N.toSubgroup.map (tphi F s hs hcof h₁b h₂b h₂c) := by
  ext h
  constructor
  · intro hh
    obtain ⟨g, rfl⟩ := tphi_surjective F s hs hcof h₁b h₂b h₂c h₁c h
    exact ⟨g, (tphi_mem_tHc_iff F s hs hcof h₁b h₂b h₂c g N).mp hh, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact (tphi_mem_tHc_iff F s hs hcof h₁b h₂b h₂c g N).mpr hg

lemma isOpenMap_tphi (h₁c : IsONSComplete G₁) : IsOpenMap (tphi F s hs hcof h₁b h₂b h₂c) := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨N, hN⟩ := h₁b (hU.preimage (continuous_const_mul g)) (by simpa using hg)
  refine ⟨(tphi F s hs hcof h₁b h₂b h₂c g * ·) '' (tHc F N : Set G₂), ?_, ?_, ⟨1, one_mem _,
    mul_one _⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    rw [tHc_eq_map F s hs hcof h₁b h₂b h₂c h₁c] at hk
    obtain ⟨n, hn, rfl⟩ := hk
    exact ⟨g * n, hN hn, by rw [map_mul]⟩
  · exact (isOpenMap_mul_left _) _ (F.obj (ofONS N)).isOpen

/-- The isomorphism of topological groups `G₁ ≅ G₂` induced by `F`. -/
noncomputable def tphiEquiv [T2Space G₁] (h₁c : IsONSComplete G₁) : G₁ ≃ₜ* G₂ :=
  let e : G₁ ≃* G₂ := MulEquiv.ofBijective (tphi F s hs hcof h₁b h₂b h₂c)
    ⟨tphi_injective F s hs hcof h₁b h₂b h₂c, tphi_surjective F s hs hcof h₁b h₂b h₂c h₁c⟩
  let t : G₁ ≃ₜ G₂ := e.toEquiv.toHomeomorphOfContinuousOpen
    (continuous_tphi F s hs hcof h₁b h₂b h₂c) (isOpenMap_tphi F s hs hcof h₁b h₂b h₂c h₁c)
  { e with
    continuous_toFun := by exact t.continuous
    continuous_invFun := by exact t.symm.continuous }

end Recon

/-- **[SemiAnbd], Proposition 3.2 for the categories of connected objects**: an equivalence
`F : B^temp(G₁)⁰ ≌ B^temp(G₂)⁰` of Hausdorff groups with bases of open normal subgroups,
complete for them, `G₁` with a countable cofinal chain, induces an isomorphism of topological
groups `α : G₁ ≅ G₂` and compatible base points `x_N ∈ F(G₁/N)` with `F(G₁/N) = G₂/α(N)` and
`F(rmul g)(x_N) = α(g)·x_N`. -/
theorem exists_continuousMulEquiv_temp {G₁ : Type u} [Group G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [T2Space G₁] {G₂ : Type u'} [Group G₂] [TopologicalSpace G₂]
    [IsTopologicalGroup G₂] [T2Space G₂] (h₁b : HasONSBasis G₁) (h₁s : HasONSChain G₁)
    (h₁c : IsONSComplete G₁) (h₂b : HasONSBasis G₂) (h₂c : IsONSComplete G₂)
    (F : OrbitObj G₁ ⥤ OrbitObj G₂) [F.IsEquivalence] :
    ∃ (α : G₁ ≃ₜ* G₂) (x : ∀ N, G₂ ⧸ (F.obj (ofONS N)).H),
      (∀ N, (F.obj (ofONS N)).H = N.toSubgroup.map (α : G₁ →* G₂)) ∧
      (∀ {N M : OpenNormalSubgroup G₁} (h : N ≤ M),
        (F.map (proj (ofONS M) (fun _ hx => h hx))).toFun (x N) = x M) ∧
      ∀ N g, (F.map (rmul N g)).toFun (x N) = α g • x N := by
  obtain ⟨s, hs, hcof⟩ := h₁s
  exact ⟨tphiEquiv F s hs hcof h₁b h₂b h₂c h₁c, tpt F s hs hcof,
    tHc_eq_map F s hs hcof h₁b h₂b h₂c h₁c, fun h => tpt_compat F s hs hcof h,
    fun N g => (tphi_smul F s hs hcof h₁b h₂b h₂c g N).symm⟩

/-! ### Slimness of `B^temp(G)⁰` -/

section SlimTemp

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable (A : OrbitObj G) (η : Over.forget A ≅ Over.forget A)

omit [T2Space G] in
/-- **A common point `m` of all cosets `m_N N`** (completeness replacing compactness). -/
lemma exists_common_temp (hb : HasONSBasis G) (hc : IsONSComplete G) :
    ∃ m : G, ∀ i : Idx A, m ∈ coset A η i := by
  obtain ⟨N₀, hN₀⟩ := hb A.isOpen A.H.one_mem
  obtain ⟨m, hm⟩ := hc (Set.range (coset A η)) ⟨_, ⟨N₀, hN₀⟩, rfl⟩
    (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      obtain ⟨N, hN⟩ := hb ((i.1.isOpen).inter (j.1.isOpen))
        ⟨i.1.toSubgroup.one_mem, j.1.toSubgroup.one_mem⟩
      have hNi : (N.toSubgroup : Subgroup G) ≤ i.1.toSubgroup := fun x hx => (hN hx).1
      have hNj : (N.toSubgroup : Subgroup G) ≤ j.1.toSubgroup := fun x hx => (hN hx).2
      refine ⟨_, ⟨⟨N, hNi.trans i.2⟩, rfl⟩, fun m hm => ?_, fun m hm => ?_⟩
      · simp only [coset, Set.mem_setOf_eq] at hm ⊢
        rw [← mN_compat A η i.2 (hNi.trans i.2) hNi]
        exact QuotientGroup.eq.2 (hNi (QuotientGroup.eq.1 hm))
      · simp only [coset, Set.mem_setOf_eq] at hm ⊢
        rw [← mN_compat A η j.2 (hNi.trans i.2) hNj]
        exact QuotientGroup.eq.2 (hNj (QuotientGroup.eq.1 hm)))
    (by
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨mN A η i.1 i.2, rfl⟩, isClosed_coset A η i⟩)
    (by
      intro K
      obtain ⟨N, hN⟩ := hb (K.isOpen.inter A.isOpen) ⟨K.toSubgroup.one_mem, A.H.one_mem⟩
      have hNH : (N.toSubgroup : Subgroup G) ≤ A.H := fun y hy => (hN hy).2
      refine ⟨_, ⟨⟨N, hNH⟩, rfl⟩, fun x hx y hy => (hN ?_).1⟩
      simp only [coset, Set.mem_setOf_eq] at hx hy
      exact QuotientGroup.eq.1 (hx.trans hy.symm))
  exact ⟨m, fun i => hm _ ⟨i, rfl⟩⟩

omit [IsTopologicalGroup G] in
/-- The common point commutes with `H`. -/
lemma common_comm_temp (hb : HasONSBasis G) {m : G} (hm : ∀ i : Idx A, m ∈ coset A η i) {x : G}
    (hx : x ∈ A.H) : m * x = x * m := by
  by_contra hne
  have hg : (x * m)⁻¹ * (m * x) ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
  have hU : IsOpen ({(x * m)⁻¹ * (m * x)}ᶜ ∩ (A.H : Set G)) :=
    (isOpen_compl_singleton).inter A.isOpen
  obtain ⟨N, hN⟩ := hb hU ⟨fun h => hg (Set.mem_singleton_iff.mp h).symm, A.H.one_mem⟩
  have hNH : (N.toSubgroup : Subgroup G) ≤ A.H := fun y hy => (hN hy).2
  have hmN : (QuotientGroup.mk m : G ⧸ N.toSubgroup) = QuotientGroup.mk (mN A η N hNH) :=
    hm ⟨N, hNH⟩
  have hc := mN_comm A η N hNH hx
  have h₁ : (QuotientGroup.mk (x * m) : G ⧸ N.toSubgroup) =
      QuotientGroup.mk (x * mN A η N hNH) := by
    rw [QuotientGroup.eq] at hmN ⊢
    simpa [mul_assoc] using hmN
  have h₂ : (QuotientGroup.mk (mN A η N hNH * x) : G ⧸ N.toSubgroup) =
      QuotientGroup.mk (m * x) := by
    rw [QuotientGroup.eq] at hmN ⊢
    have := N.isNormal'.conj_mem' _ (N.toSubgroup.inv_mem hmN) x
    simpa [mul_assoc] using this
  have h₃ := (h₁.trans hc).trans h₂
  rw [QuotientGroup.eq] at h₃
  exact (hN h₃).1 rfl

include η in
lemma app_overN_eq_temp (hb : HasONSBasis G) (hc : IsONSComplete G) (hG : IsSlimGroup G)
    (N : OpenNormalSubgroup G) (hN : (N.toSubgroup : Subgroup G) ≤ A.H) :
    η.hom.app (overN A N hN) = 𝟙 _ := by
  obtain ⟨m, hm⟩ := exists_common_temp A η hb hc
  have h1 : m = 1 := hG A.H A.isOpen m (fun x hx => common_comm_temp A η hb hm hx)
  have hmN : (QuotientGroup.mk (mN A η N hN) : G ⧸ N.toSubgroup) = QuotientGroup.mk 1 := by
    rw [← h1]; exact (hm ⟨N, hN⟩).symm
  have h2 : (mN A η N hN)⁻¹ ∈ (N.toSubgroup : Subgroup G) := by
    simpa using QuotientGroup.eq.1 hmN
  ext y
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [app_mk]
    change _ = QuotientGroup.mk g
    exact QuotientGroup.eq.2 (show (g * mN A η N hN)⁻¹ * g ∈ (N.toSubgroup : Subgroup G) by
      simpa using h2)

/-- **`B^temp(G)⁰` is slim** for a slim Hausdorff group `G` with a basis of open normal subgroups
for which it is complete (the tempered analogue of `OrbitObj.isSlim`). -/
theorem isSlim_temp (hb : HasONSBasis G) (hc : IsONSComplete G) (hG : IsSlimGroup G) :
    IsSlim (OrbitObj G) := by
  intro A η
  refine Iso.ext (NatTrans.ext (funext fun T => ?_))
  change η.hom.app T = 𝟙 _
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (T.hom.toFun (QuotientGroup.mk 1))
  obtain ⟨N, hN⟩ := hb (A.isOpen.inter T.left.isOpen) ⟨A.H.one_mem, T.left.H.one_mem⟩
  have hNH : (N.toSubgroup : Subgroup G) ≤ A.H := fun y hy => (hN hy).1
  have hNK : (N.toSubgroup : Subgroup G) ≤ T.left.H := fun y hy => (hN hy).2
  let f₀ : ofONS N ⟶ T.left := pointHom (ofONS N) T.left (QuotientGroup.mk a⁻¹) (by
    intro n hn
    rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    have : (n * a⁻¹)⁻¹ * a⁻¹ = a * n⁻¹ * a⁻¹ := by group
    rw [this]
    exact hNK (N.isNormal'.conj_mem _ (N.toSubgroup.inv_mem hn) a))
  have hf₀ : f₀ ≫ T.hom = proj A hNH := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H g =>
      change T.hom.toFun (g • (QuotientGroup.mk a⁻¹ : G ⧸ T.left.H)) =
        (proj A hNH).toFun (QuotientGroup.mk g)
      rw [proj_mk]
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, OrbitHom.apply_mk_of_eq _ ha.symm,
        inv_mul_cancel_right]
  let f : overN A N hNH ⟶ T := Over.homMk f₀ hf₀
  have hnat := η.hom.naturality f
  rw [app_overN_eq_temp A η hb hc hG N hNH] at hnat
  simp only [Over.forget_map, Over.homMk_left, f] at hnat
  exact (cancel_epi f₀).mp (hnat.trans (Category.comp_id f₀).symm)

end SlimTemp

end OrbitObj

end Frobenioid

end Iut
