/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GaloisBase
import Iut.Frobenioid.Thm34Base
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Slimness of the Galois base categories `B(G)⁰`

[FrdI] §0 (p. 14–15) recalls ([Mzk7], Corollary 1.1.6) that for a profinite group `G`, `G` is
slim if and only if the category `B(G)` is slim. We prove the direction used for [FrdI], Theorem
3.4(v), for the category `B(G)⁰ = OrbitObj G` of connected objects:

**Theorem** (`OrbitObj.isSlim`). Let `G` be a profinite group (compact, Hausdorff, totally
disconnected topological group) which is **slim**: the centralizer of every open subgroup is
trivial (`IsSlimGroup`). Then `B(G)⁰` is slim: for every object `A = G/H`, the forgetful
functor `B(G)⁰_A → B(G)⁰` has no nontrivial automorphisms.

*Proof.* Let `η` be an automorphism of the forgetful functor. For an open normal subgroup
`N ⊆ H`, the component of `η` at `G/N → G/H` is right multiplication by some `m_N`. Naturality
along the projections `G/N' → G/N` shows that the `m_N` are compatible; naturality along the
right multiplications by `x ∈ H` (which lie over `G/H`) shows `m_N x ≡ x m_N (mod N)`. By
compactness the cosets `m_N N` have a common point `m`, which then commutes with `H` modulo every
open normal subgroup, hence commutes with `H`; so `m = 1`. Finally every object `G/K → G/H` of
`B(G)⁰_{G/H}` receives an epimorphism over `G/H` from some `G/N`, on which `η` is trivial.

As a consequence (`Model.thm34_galois_preservesBase`), [FrdI], Theorem 3.4(v) holds for
model Frobenioids over `B(G₁)⁰`, `B(G₂)⁰` with `G₂` slim profinite and rational functions with
torsion of every order.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe u u'

/-- **Slim topological groups** ([FrdI] §0; [Mzk7]): the centralizer of every open subgroup is
trivial. -/
def IsSlimGroup (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : Subgroup G, IsOpen (U : Set G) → ∀ m : G, (∀ x ∈ U, m * x = x * m) → m = 1

namespace OrbitObj

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The object `G/N` for an open normal subgroup `N`. -/
abbrev ofONS (N : OpenNormalSubgroup G) : OrbitObj G := ⟨N.toSubgroup, N.isOpen⟩

omit [IsTopologicalGroup G] in
lemma stabilizer_mk_of_normal (N : OpenNormalSubgroup G) (x : G) :
    (N.toSubgroup : Subgroup G) ≤
      MulAction.stabilizer G (QuotientGroup.mk x : G ⧸ N.toSubgroup) := by
  intro n hn
  rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  have : (n * x)⁻¹ * x = x⁻¹ * n⁻¹ * x := by group
  rw [this]
  exact N.isNormal'.conj_mem' n⁻¹ (N.toSubgroup.inv_mem hn) x

/-- Right multiplication by `x` on `G/N` (`N` normal). -/
noncomputable def rmul (N : OpenNormalSubgroup G) (x : G) : ofONS N ⟶ ofONS N :=
  pointHom (ofONS N) (ofONS N) (QuotientGroup.mk x) (stabilizer_mk_of_normal N x)

omit [IsTopologicalGroup G] in
lemma rmul_mk (N : OpenNormalSubgroup G) (x g : G) :
    (rmul N x).toFun (QuotientGroup.mk g) = QuotientGroup.mk (g * x) := by
  rw [rmul, pointHom_mk, MulAction.Quotient.smul_mk, smul_eq_mul]

/-- The projection `G/N → G/K` for `N ≤ K`. -/
noncomputable def proj {N : OpenNormalSubgroup G} (K : OrbitObj G)
    (h : (N.toSubgroup : Subgroup G) ≤ K.H) : ofONS N ⟶ K :=
  pointHom (ofONS N) K (QuotientGroup.mk 1) (by
    intro n hn
    rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
      QuotientGroup.eq, mul_one]
    exact K.H.inv_mem (h hn))

omit [IsTopologicalGroup G] in
lemma proj_mk {N : OpenNormalSubgroup G} (K : OrbitObj G)
    (h : (N.toSubgroup : Subgroup G) ≤ K.H) (g : G) :
    (proj K h).toFun (QuotientGroup.mk g) = QuotientGroup.mk g := by
  rw [proj, pointHom_mk, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

section Slim

variable [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space G]

omit [T2Space G] in
/-- In a profinite group, every open set containing `1` contains an open normal subgroup. -/
lemma exists_ons_le {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    ∃ N : OpenNormalSubgroup G, (N : Set G) ⊆ U :=
  ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1

variable (A : OrbitObj G) (η : Over.forget A ≅ Over.forget A)

/-- `N ≤ H` as an object of `B(G)⁰_{G/H}` via the projection. -/
noncomputable def overN (N : OpenNormalSubgroup G) (hN : (N.toSubgroup : Subgroup G) ≤ A.H) :
    Over A :=
  Over.mk (proj A hN)

/-- The element `m_N` with `η_{G/N}(N) = m_N N`. -/
noncomputable def mN (N : OpenNormalSubgroup G) (hN : (N.toSubgroup : Subgroup G) ≤ A.H) : G :=
  ((η.hom.app (overN A N hN)).toFun (QuotientGroup.mk 1)).out

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space G] in
lemma app_mk (N : OpenNormalSubgroup G) (hN : (N.toSubgroup : Subgroup G) ≤ A.H) (g : G) :
    (η.hom.app (overN A N hN)).toFun (QuotientGroup.mk g) =
      QuotientGroup.mk (g * mN A η N hN) :=
  OrbitHom.apply_mk_of_eq _ (QuotientGroup.out_eq' _).symm g

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space G] in
/-- Compatibility of the `m_N` along projections. -/
lemma mN_compat {N N' : OpenNormalSubgroup G} (hN : (N.toSubgroup : Subgroup G) ≤ A.H)
    (hN' : (N'.toSubgroup : Subgroup G) ≤ A.H) (hle : (N'.toSubgroup : Subgroup G) ≤ N) :
    (QuotientGroup.mk (mN A η N' hN') : G ⧸ N.toSubgroup) = QuotientGroup.mk (mN A η N hN) := by
  let f : overN A N' hN' ⟶ overN A N hN := Over.homMk (proj (ofONS N) hle) (by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change (proj A hN).toFun ((proj (ofONS N) hle).toFun (QuotientGroup.mk g)) =
        (proj A hN').toFun (QuotientGroup.mk g)
      rw [proj_mk, proj_mk, proj_mk])
  have := congrArg (fun φ => φ.toFun (QuotientGroup.mk 1)) (η.hom.naturality f)
  change (η.hom.app (overN A N hN)).toFun ((proj (ofONS N) hle).toFun (QuotientGroup.mk 1)) =
    (proj (ofONS N) hle).toFun ((η.hom.app (overN A N' hN')).toFun (QuotientGroup.mk 1)) at this
  rw [proj_mk] at this
  erw [app_mk, app_mk, proj_mk] at this
  rw [one_mul, one_mul] at this
  exact this.symm

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space G] in
/-- The `m_N` commute with `H` modulo `N`. -/
lemma mN_comm (N : OpenNormalSubgroup G) (hN : (N.toSubgroup : Subgroup G) ≤ A.H) {x : G}
    (hx : x ∈ A.H) :
    (QuotientGroup.mk (x * mN A η N hN) : G ⧸ N.toSubgroup) =
      QuotientGroup.mk (mN A η N hN * x) := by
  let f : overN A N hN ⟶ overN A N hN := Over.homMk (rmul N x) (by
    ext y
    induction y using QuotientGroup.induction_on with
    | H g =>
      change (proj A hN).toFun ((rmul N x).toFun (QuotientGroup.mk g)) =
        (proj A hN).toFun (QuotientGroup.mk g)
      rw [rmul_mk, proj_mk, proj_mk, QuotientGroup.eq]
      have : (g * x)⁻¹ * g = x⁻¹ := by group
      rw [this]
      exact A.H.inv_mem hx)
  have := congrArg (fun φ => φ.toFun (QuotientGroup.mk 1)) (η.hom.naturality f)
  change (η.hom.app (overN A N hN)).toFun ((rmul N x).toFun (QuotientGroup.mk 1)) =
    (rmul N x).toFun ((η.hom.app (overN A N hN)).toFun (QuotientGroup.mk 1)) at this
  rw [rmul_mk] at this
  erw [app_mk, app_mk, rmul_mk] at this
  rw [one_mul, one_mul] at this
  exact this

/-- The open normal subgroups contained in `H`. -/
abbrev Idx : Type u := {N : OpenNormalSubgroup G // (N.toSubgroup : Subgroup G) ≤ A.H}

/-- The coset `m_N N` as a subset of `G`. -/
def coset (i : Idx A) : Set G :=
  {m | (QuotientGroup.mk m : G ⧸ i.1.toSubgroup) = QuotientGroup.mk (mN A η i.1 i.2)}

omit [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space G] in
lemma isClosed_coset (i : Idx A) : IsClosed (coset A η i) := by
  have hc : IsClosed ((i.1.toSubgroup : Subgroup G) : Set G) :=
    Subgroup.isClosed_of_isOpen _ i.1.isOpen
  have : coset A η i = (fun m => (mN A η i.1 i.2)⁻¹ * m) ⁻¹' (i.1.toSubgroup : Set G) := by
    ext m
    simp only [coset, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    rw [eq_comm, QuotientGroup.eq]
  rw [this]
  exact hc.preimage (by fun_prop)

omit [T2Space G] in
/-- **A common point `m` of all cosets `m_N N`** (compactness). -/
lemma exists_common : ∃ m : G, ∀ i : Idx A, m ∈ coset A η i := by
  haveI : Nonempty (Idx A) := by
    obtain ⟨N, hN⟩ := exists_ons_le A.isOpen A.H.one_mem
    exact ⟨⟨N, hN⟩⟩
  have hdir : Directed (· ⊇ ·) (coset A η) := by
    intro i j
    obtain ⟨N, hN⟩ := exists_ons_le ((i.1.isOpen).inter (j.1.isOpen))
      ⟨i.1.toSubgroup.one_mem, j.1.toSubgroup.one_mem⟩
    have hNi : (N.toSubgroup : Subgroup G) ≤ i.1.toSubgroup := fun x hx => (hN hx).1
    have hNj : (N.toSubgroup : Subgroup G) ≤ j.1.toSubgroup := fun x hx => (hN hx).2
    refine ⟨⟨N, hNi.trans i.2⟩, fun m hm => ?_, fun m hm => ?_⟩
    · simp only [coset, Set.mem_setOf_eq] at hm ⊢
      rw [← mN_compat A η i.2 (hNi.trans i.2) hNi]
      exact QuotientGroup.eq.2 (hNi (QuotientGroup.eq.1 hm))
    · simp only [coset, Set.mem_setOf_eq] at hm ⊢
      rw [← mN_compat A η j.2 (hNi.trans i.2) hNj]
      exact QuotientGroup.eq.2 (hNj (QuotientGroup.eq.1 hm))
  obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (coset A η) hdir (fun i => ⟨mN A η i.1 i.2, rfl⟩)
    (fun i => (isClosed_coset A η i).isCompact) (fun i => isClosed_coset A η i)
  exact ⟨m, Set.mem_iInter.mp hm⟩

/-- The common point commutes with `H`. -/
lemma common_comm {m : G} (hm : ∀ i : Idx A, m ∈ coset A η i) {x : G} (hx : x ∈ A.H) :
    m * x = x * m := by
  by_contra hne
  have hg : (x * m)⁻¹ * (m * x) ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
  have hU : IsOpen ({(x * m)⁻¹ * (m * x)}ᶜ ∩ (A.H : Set G)) :=
    (isOpen_compl_singleton).inter A.isOpen
  obtain ⟨N, hN⟩ := exists_ons_le hU ⟨fun h => hg (Set.mem_singleton_iff.mp h).symm,
    A.H.one_mem⟩
  have hNH : (N.toSubgroup : Subgroup G) ≤ A.H := fun y hy => (hN hy).2
  have hmN : (QuotientGroup.mk m : G ⧸ N.toSubgroup) = QuotientGroup.mk (mN A η N hNH) :=
    hm ⟨N, hNH⟩
  have hc := mN_comm A η N hNH hx
  -- `x m ≡ x m_N ≡ m_N x ≡ m x (mod N)`
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
/-- At the objects `G/N → G/H`, the components of `η` are identities. -/
lemma app_overN_eq (hG : IsSlimGroup G) (N : OpenNormalSubgroup G)
    (hN : (N.toSubgroup : Subgroup G) ≤ A.H) : η.hom.app (overN A N hN) = 𝟙 _ := by
  obtain ⟨m, hm⟩ := exists_common A η
  have h1 : m = 1 := hG A.H A.isOpen m (fun x hx => common_comm A η hm hx)
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

/-- **`B(G)⁰` is slim** for a slim profinite group `G` ([FrdI] §0; [Mzk7], Corollary 1.1.6). -/
theorem isSlim (hG : IsSlimGroup G) : IsSlim (OrbitObj G) := by
  intro A η
  refine Iso.ext (NatTrans.ext (funext fun T => ?_))
  change η.hom.app T = 𝟙 _
  -- `T = (G/K, t)` with `t(K) = a H`
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (T.hom.toFun (QuotientGroup.mk 1))
  obtain ⟨N, hN⟩ := exists_ons_le (A.isOpen.inter T.left.isOpen) ⟨A.H.one_mem, T.left.H.one_mem⟩
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
  rw [app_overN_eq A η hG N hNH] at hnat
  simp only [Over.forget_map, Over.homMk_left, f] at hnat
  exact (cancel_epi f₀).mp (hnat.trans (Category.comp_id f₀).symm)

end Slim

end OrbitObj

namespace Model

variable {G₁ : Type u} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [CompactSpace G₁]
variable {G₂ : Type u'} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  [CompactSpace G₂] [TotallyDisconnectedSpace G₂] [T2Space G₂]
variable {Φ₁ : DivMonoid (OrbitObj G₁)} {B₁ : GrpOn (OrbitObj G₁)}
  {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {Φ₂ : DivMonoid (OrbitObj G₂)} {B₂ : GrpOn (OrbitObj G₂)}
  {divB₂ : DivHom B₂ Φ₂.toGrpOn}

/-- **[FrdI], Theorem 3.4(v) over the Galois base categories**: for compact `G₁`, a slim
profinite `G₂`, and model Frobenioids over `B(G₁)⁰`, `B(G₂)⁰` whose rational functions have
torsion of every order, every equivalence lies over a functor `B(G₁)⁰ → B(G₂)⁰`. -/
theorem thm34_galois_preservesBase (hG₂ : IsSlimGroup G₂) (hB₁ : HasAllTorsion B₁)
    (hB₂ : HasAllTorsion B₂) (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] :
    PreservesBase (toElem Φ₁ B₁ divB₁) (toElem Φ₂ B₂ divB₂) F :=
  thm34_preservesBase F OrbitObj.baseHyp hB₁ OrbitObj.baseHyp hB₂ (OrbitObj.isSlim hG₂)

end Model

end Frobenioid

end Iut
