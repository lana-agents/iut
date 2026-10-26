/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.BaseRecon
import TemperedFundamentalGroups.Andre.OrbStageLimit

/-!
# The tempered fundamental group is a tempered group (open normal subgroups)

`Iut/Frobenioid/Tempered/BaseRecon.lean` proves [SemiAnbd], Proposition 3.2 for Hausdorff groups
`G` with `HasONSBasis G`, `IsONSComplete G` and (for the source) `HasONSChain G`. Here these
properties are proved for the tempered fundamental group `temperedPi1` of tfg, through its
description as the inverse limit of the discrete stage groups (`temperedPi1HomeoLim`,
`temperedPi1HomeoLimO`):

* `hasONSBasis_pi`, `isONSComplete_pi`: a subgroup (resp. closed subgroup) of a product of
  discrete groups has a basis of open normal subgroups (resp. is complete for them);
* `hasONSBasis_of_equiv`, `isONSComplete_of_equiv`, `hasONSChain_of_equiv`: the properties are
  invariant under isomorphisms of topological groups;
* `GaloisLimit.hasONSChain_limGroup`: the inverse limit of the stage groups has a countable cofinal
  chain of open normal subgroups as soon as some sequence of pointed Galois objects dominates all
  of them;
* `temperedPi1_hasONSBasis`, `temperedPi1_isONSComplete`, `temperedPi1_t2Space` (scheme case),
  `temperedPi1_hasONSBasisO`, `temperedPi1_isONSCompleteO`, `temperedPi1_t2SpaceO` (orbifold case),
  and `temperedPi1_hasONSChainO` from a dominating sequence of pointed Galois objects.

The countability hypothesis of the last item is part of the definition of tempered groups in
[SemiAnbd], Definition 3.1 (countable discrete quotients, countably indexed systems). For the
tempered fundamental group of a curve over a finite extension of `ℚ_p` it holds because there are
only countably many finite étale coverings up to isomorphism; it is not proved here and enters as
the explicit argument `hctbl` (recorded in `MR18-plan.md`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe u v w

section General

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The kernel of a continuous homomorphism to a discrete group, as an open normal subgroup. -/
def onsOfKer {D : Type v} [Group D] [TopologicalSpace D] [DiscreteTopology D] (f : G →* D)
    (hf : Continuous f) : OpenNormalSubgroup G where
  toSubgroup := f.ker
  isOpen' := by
    have : (f.ker : Set G) = f ⁻¹' {1} := by ext; simp
    change IsOpen (f.ker : Set G)
    rw [this]
    exact (isOpen_discrete _).preimage hf
  isNormal' := f.normal_ker

@[simp]
lemma mem_onsOfKer {D : Type v} [Group D] [TopologicalSpace D] [DiscreteTopology D] (f : G →* D)
    (hf : Continuous f) {g : G} : g ∈ onsOfKer f hf ↔ f g = 1 := MonoidHom.mem_ker

/-- A sequence of open normal subgroups cofinal among all of them gives a decreasing one. -/
lemma hasONSChain_of_seq (t : ℕ → OpenNormalSubgroup G)
    (ht : ∀ N : OpenNormalSubgroup G, ∃ n, t n ≤ N) : HasONSChain G := by
  let s : ℕ → OpenNormalSubgroup G := fun k => Nat.rec (t 0) (fun k sk => sk ⊓ t (k + 1)) k
  refine ⟨s, antitone_nat_of_succ_le fun k => inf_le_left, fun N => ?_⟩
  obtain ⟨n, hn⟩ := ht N
  refine ⟨n, le_trans ?_ hn⟩
  cases n with
  | zero => exact le_rfl
  | succ n => exact inf_le_right

variable {H : Type w} [Group H] [TopologicalSpace H] (e : G ≃ₜ* H)

/-- The preimage of an open normal subgroup under an isomorphism of topological groups. -/
def onsComap (N : OpenNormalSubgroup H) : OpenNormalSubgroup G where
  toSubgroup := N.toSubgroup.comap (e : G →* H)
  isOpen' := N.isOpen.preimage e.continuous
  isNormal' := N.isNormal'.comap _

@[simp]
lemma mem_onsComap (N : OpenNormalSubgroup H) {g : G} : g ∈ onsComap e N ↔ e g ∈ N := Iff.rfl

include e in
lemma hasONSBasis_of_equiv (h : HasONSBasis H) : HasONSBasis G := by
  intro U hU h1
  obtain ⟨N, hN⟩ := h (e.toHomeomorph.isOpenMap U hU) ⟨1, h1, map_one e⟩
  refine ⟨onsComap e N, fun g hg => ?_⟩
  obtain ⟨g', hg', he⟩ := hN hg
  rwa [← e.injective he]

include e in
lemma isONSComplete_of_equiv (h : IsONSComplete H) : IsONSComplete G := by
  intro S hS hdir hcl hfine
  obtain ⟨y, hy⟩ := h ((fun s => e '' s) '' S) (hS.image _)
    (by
      rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
      obtain ⟨r, hr, hrs, hrt⟩ := hdir s hs t ht
      exact ⟨_, ⟨r, hr, rfl⟩, Set.image_mono hrs, Set.image_mono hrt⟩)
    (by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨(hcl s hs).1.image _, e.toHomeomorph.isClosedMap _ (hcl s hs).2⟩)
    (by
      intro N
      obtain ⟨s, hs, hN⟩ := hfine (onsComap e N)
      refine ⟨_, ⟨s, hs, rfl⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have := hN x hx y hy
      rwa [mem_onsComap, map_mul, map_inv] at this)
  refine ⟨e.symm y, fun s hs => ?_⟩
  obtain ⟨x, hx, hxy⟩ := hy _ ⟨s, hs, rfl⟩
  rwa [← hxy, ContinuousMulEquiv.symm_apply_apply]

include e in
lemma hasONSChain_of_equiv (h : HasONSChain H) : HasONSChain G := by
  obtain ⟨s, hs, hcof⟩ := h
  refine ⟨fun k => onsComap e (s k), fun i j hij g hg => hs hij hg, fun N => ?_⟩
  obtain ⟨k, hk⟩ := hcof (onsComap e.symm N)
  refine ⟨k, fun g hg => ?_⟩
  have := hk hg
  simpa using this

end General

section Pi

variable {ι : Type u} {D : ι → Type v} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  [∀ i, DiscreteTopology (D i)] (L : Subgroup (∀ i, D i))

/-- Restriction of a subgroup of the product to the coordinates in a finite set. -/
def piRes (I : Finset ι) : L →* ∀ i : I, D i :=
  MonoidHom.pi fun i => (Pi.evalMonoidHom D i.1).comp L.subtype

omit [∀ i, DiscreteTopology (D i)] in
lemma continuous_piRes (I : Finset ι) : Continuous (piRes L I) :=
  continuous_pi fun i => (continuous_apply i.1).comp continuous_subtype_val

/-- The open normal subgroup of elements of `L` trivial at the coordinates in `I`. -/
def piKer (I : Finset ι) : OpenNormalSubgroup L := onsOfKer (piRes L I) (continuous_piRes L I)

lemma mem_piKer {I : Finset ι} {x : L} : x ∈ piKer L I ↔ ∀ i ∈ I, x.1 i = 1 := by
  rw [piKer, mem_onsOfKer]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.1 i.2

/-- Every neighbourhood of `1` in `L` contains some `piKer L I`. -/
lemma exists_piKer_subset {U : Set L} (hU : IsOpen U) (h1 : (1 : L) ∈ U) :
    ∃ I : Finset ι, ((piKer L I : Set L)) ⊆ U := by
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hV 1 h1
  refine ⟨I, fun x hx => hIu fun i hi => ?_⟩
  rw [SetLike.mem_coe, mem_piKer] at hx
  have := (hu i hi).2
  rw [hx i hi]
  exact this

/-- **A subgroup of a product of discrete groups has a basis of open normal subgroups.** -/
lemma hasONSBasis_pi : HasONSBasis L := fun _ hU h1 =>
  let ⟨I, hI⟩ := exists_piKer_subset L hU h1
  ⟨piKer L I, hI⟩

lemma piKer_le_of_ons (N : OpenNormalSubgroup L) : ∃ I : Finset ι, piKer L I ≤ N :=
  exists_piKer_subset L N.isOpen N.one_mem

/-- **A closed subgroup of a product of discrete groups is complete** for its open normal
subgroups: the coordinates of the common point are read off from members of the family inside
cosets of the kernels of the coordinate projections. -/
lemma isONSComplete_pi (hL : IsClosed (L : Set (∀ i, D i))) : IsONSComplete L := by
  classical
  intro S hS hdir hcl hfine
  -- a member of `S` inside a coset of `piKer L I`, and a point in it
  choose s hsS hs using fun I : Finset ι => hfine (piKer L I)
  have hne : ∀ I, (s I).Nonempty := fun I => (hcl _ (hsS I)).1
  let z : ∀ I : Finset ι, L := fun I => (hne I).some
  have hz : ∀ I, z I ∈ s I := fun I => (hne I).some_mem
  have hcoord : ∀ {I : Finset ι} {y y' : L}, y ∈ s I → y' ∈ s I → ∀ i ∈ I, y.1 i = y'.1 i := by
    intro I y y' hy hy' i hi
    have := (mem_piKer L).mp (hs I y hy y' hy') i hi
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply] at this
    exact (inv_mul_eq_one.mp this)
  let x : ∀ i, D i := fun i => (z {i}).1 i
  -- every member of `S` contains a point agreeing with `x` on any finite set of coordinates
  have hagree : ∀ t ∈ S, ∀ I : Finset ι, ∃ y ∈ t, ∀ i ∈ I, y.1 i = x i := by
    intro t ht I
    obtain ⟨t', ht', ht't, ht'I⟩ := hdir t ht (s I) (hsS I)
    obtain ⟨y, hy⟩ := (hcl t' ht').1
    refine ⟨y, ht't hy, fun i hi => ?_⟩
    obtain ⟨r, hr, hrt', hri⟩ := hdir t' ht' (s {i}) (hsS {i})
    obtain ⟨w, hw⟩ := (hcl r hr).1
    rw [hcoord (ht'I hy) (ht'I (hrt' hw)) i hi]
    exact hcoord (hri hw) (hz {i}) i (Finset.mem_singleton_self i)
  have hmem : ∀ t ∈ S, x ∈ Subtype.val '' t := by
    intro t ht
    have hclosed : IsClosed (Subtype.val '' t) :=
      hL.isClosedEmbedding_subtypeVal.isClosedMap _ (hcl t ht).2
    refine hclosed.closure_subset (mem_closure_iff.mpr fun o ho hxo => ?_)
    obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp ho x hxo
    obtain ⟨y, hyt, hy⟩ := hagree t ht I
    refine ⟨y.1, hIu fun i hi => ?_, y, hyt, rfl⟩
    rw [hy i hi]
    exact (hu i hi).2
  obtain ⟨t₀, ht₀⟩ := hS
  obtain ⟨y₀, hy₀, hy₀x⟩ := hmem t₀ ht₀
  refine ⟨y₀, fun t ht => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hmem t ht
  rwa [Subtype.ext (hyx.trans hy₀x.symm)] at hy

end Pi

namespace GaloisLimit

open TemperedFundamentalGroups TemperedFundamentalGroups.GaloisLimit

variable {C : Type u} [Category.{v} C] {Φ : C ⥤ Type w} {𝒢 : ObjectProperty C}
  (hgal : IsGaloisClass Φ 𝒢) (hrig : IsRigid Φ 𝒢)

/-- The inverse limit of the stage groups is closed in the product. -/
lemma isClosed_limGroup :
    IsClosed (limGroup Φ 𝒢 hgal hrig : Set (∀ p : PtGal Φ 𝒢, stageGroup Φ p.G)) := by
  have : (limGroup Φ 𝒢 hgal hrig : Set (∀ p : PtGal Φ 𝒢, stageGroup Φ p.G)) =
      ⋂ (p : PtGal Φ 𝒢) (q : PtGal Φ 𝒢) (f : p ⟶ q),
        {γ | transition hgal hrig f (γ p) = γ q} := by
    ext γ
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h p q f ↦ h f, fun h p q f ↦ h p q f⟩
  rw [this]
  refine isClosed_iInter fun p ↦ isClosed_iInter fun q ↦ isClosed_iInter fun f ↦ ?_
  have hc : Continuous fun γ : ∀ p : PtGal Φ 𝒢, stageGroup Φ p.G ↦ (γ p, γ q) :=
    (continuous_apply p).prodMk (continuous_apply q)
  exact (isClosed_discrete {x : stageGroup Φ p.G × stageGroup Φ q.G |
    transition hgal hrig f x.1 = x.2}).preimage hc

lemma hasONSBasis_limGroup : HasONSBasis (limGroup Φ 𝒢 hgal hrig) := hasONSBasis_pi _

lemma isONSComplete_limGroup : IsONSComplete (limGroup Φ 𝒢 hgal hrig) :=
  isONSComplete_pi _ (isClosed_limGroup hgal hrig)

/-- An element of the limit trivial at `p` is trivial at every `q` dominated by `p`. -/
lemma eq_one_of_hom {p q : PtGal Φ 𝒢} (f : p ⟶ q) {γ : limGroup Φ 𝒢 hgal hrig}
    (hγ : γ.1 p = 1) : γ.1 q = 1 := by
  rw [← γ.2 f, hγ, map_one]

/-- **A countable dominating family of pointed Galois objects gives a countable cofinal chain of
open normal subgroups** of the inverse limit of the stage groups. -/
lemma hasONSChain_limGroup (hdom : IsDominating Φ 𝒢) (p : ℕ → PtGal Φ 𝒢)
    (hp : ∀ q, ∃ n, Nonempty (p n ⟶ q)) : HasONSChain (limGroup Φ 𝒢 hgal hrig) := by
  classical
  refine hasONSChain_of_seq (fun n => piKer _ {p n}) fun N => ?_
  obtain ⟨I, hI⟩ := piKer_le_of_ons _ N
  set l := I.toList
  obtain ⟨G, hG, g, f, hf⟩ := hdom l.length fun k => ⟨(l.get k).G, (l.get k).g⟩
  let r : PtGal Φ 𝒢 := ⟨G, hG, g⟩
  have hr : ∀ q ∈ I, Nonempty (r ⟶ q) := by
    intro q hq
    obtain ⟨k, hk⟩ := List.mem_iff_get.1 (Finset.mem_toList.2 hq)
    subst hk
    exact ⟨⟨Φ.map (f k), ⟨f k, rfl⟩, hf k⟩⟩
  obtain ⟨n, ⟨fn⟩⟩ := hp r
  refine ⟨n, fun γ hγ => hI ?_⟩
  rw [mem_piKer] at hγ ⊢
  have hγr : γ.1 r = 1 := eq_one_of_hom hgal hrig fn (hγ _ (Finset.mem_singleton_self _))
  intro q hq
  obtain ⟨fq⟩ := hr q hq
  exact eq_one_of_hom hgal hrig fq hγr

end GaloisLimit

section TemperedPi1

open TemperedFundamentalGroups TemperedFundamentalGroups.GaloisLimit

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

section Scheme

variable {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]

include hp hR in
/-- **The tempered fundamental group has a basis of open normal subgroups** (scheme case). -/
theorem temperedPi1_hasONSBasis : HasONSBasis (temperedPi1 O R A V hV) :=
  hasONSBasis_of_equiv (temperedPi1HomeoLim V hV hp hR) (GaloisLimit.hasONSBasis_limGroup _ _)

include hp hR in
/-- **The tempered fundamental group is complete for its open normal subgroups** (scheme case). -/
theorem temperedPi1_isONSComplete : IsONSComplete (temperedPi1 O R A V hV) :=
  isONSComplete_of_equiv (temperedPi1HomeoLim V hV hp hR)
    (GaloisLimit.isONSComplete_limGroup _ _)

include hp hR in
/-- The tempered fundamental group is Hausdorff (scheme case). -/
theorem temperedPi1_t2Space : T2Space (temperedPi1 O R A V hV) :=
  (temperedPi1HomeoLim V hV hp hR).toHomeomorph.isEmbedding.t2Space

end Scheme

section Orbifold

variable {A : Type u} [Group A] [MulSemiringAction A R] [SMulCommClass A K R] [Finite A]

include hp hR in
/-- **The tempered fundamental group of the orbifold `[Spec R / A]` has a basis of open normal
subgroups.** -/
theorem temperedPi1_hasONSBasisO : HasONSBasis (temperedPi1 O R A V hV) :=
  hasONSBasis_of_equiv (temperedPi1HomeoLimO V hV hp hR) (GaloisLimit.hasONSBasis_limGroup _ _)

include hp hR in
/-- **The tempered fundamental group of the orbifold `[Spec R / A]` is complete for its open
normal subgroups.** -/
theorem temperedPi1_isONSCompleteO : IsONSComplete (temperedPi1 O R A V hV) :=
  isONSComplete_of_equiv (temperedPi1HomeoLimO V hV hp hR)
    (GaloisLimit.isONSComplete_limGroup _ _)

include hp hR in
/-- The tempered fundamental group of the orbifold `[Spec R / A]` is Hausdorff. -/
theorem temperedPi1_t2SpaceO : T2Space (temperedPi1 O R A V hV) :=
  (temperedPi1HomeoLimO V hV hp hR).toHomeomorph.isEmbedding.t2Space

include hp hR in
/-- **A countable cofinal chain of open normal subgroups** of the tempered fundamental group of
the orbifold `[Spec R / A]`, from a sequence of pointed orbifold Galois objects dominating all of
them ([SemiAnbd], Definition 3.1: countability of tempered groups). The hypothesis `hctbl` holds
for curves over finite extensions of `ℚ_p` (countably many finite étale coverings); it is not
proved here. -/
theorem temperedPi1_hasONSChainO
    (hctbl : ∃ p : ℕ → PtGal (tempFibre O R A V hV) (galO O R A Ω),
      ∀ q, ∃ n, Nonempty (p n ⟶ q)) :
    HasONSChain (temperedPi1 O R A V hV) := by
  obtain ⟨s, hs⟩ := hctbl
  exact hasONSChain_of_equiv (temperedPi1HomeoLimO V hV hp hR)
    (GaloisLimit.hasONSChain_limGroup _ _ (galoisLimitData_galO V hV hp hR).2.1 s hs)

end Orbifold

end TemperedPi1

end Frobenioid

end Iut
