/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Theta sections of cyclotomic envelopes and mono-theta environments ([EtTh], §2)

For a group `Π` acting on a cyclotome `μ` (in [EtTh]: `μ_N`, with `Π` acting through the
cyclotomic character), the **cyclotomic envelope** is `Π[μ] = μ ⋊ Π` ([EtTh], Def. 2.10). A
`1`-cocycle `δ : Π → μ` (in [EtTh]: a cocycle of the étale theta class reduced mod `N`) gives
the section `s_δ(g) = (δ(g), g)` of `Π[μ] ↠ Π`; the trivial cocycle gives the tautological
(*algebraic*) section, a cocycle of the étale theta class the **theta section**
([EtTh], Def. 2.13(i)).

## Main results

* `isHom_iff`: `g ↦ (δ(g), g)` is a homomorphism iff `δ` is a `1`-cocycle; every homomorphic
  section of `Π[μ] ↠ Π` is of this form (`eq_sectionOf`).
* `conj_sectionOf`, `conj_sectionOf_iff`: conjugating `s_δ` by `ζ ∈ μ` gives `s_{δ'}` with
  `δ' = δ·∂ζ`; two sections are `μ`-conjugate iff the cocycles are cohomologous ("conjugation by
  an element of `μ_N` corresponds precisely to modifying a cocycle by a coboundary", [EtTh],
  discussion before Def. 2.13).
* `range_conj_iff`: the images of `s_δ`, `s_{δ'}` are `μ`-conjugate subgroups iff `δ` and `δ'` are
  cohomologous. Hence the `μ`-conjugacy class of the image of the theta section — datum (c) of a
  model mono-theta environment — is exactly the cohomology class (`thetaClassSubgroups`,
  `thetaClassSubgroups_eq_iff`).
* `sectionOf_mul_inr_inv`: the difference of the theta section and the algebraic section is the
  cocycle: `s_δ(g)·s^alg(g)⁻¹ = δ(g) ∈ μ` (the isomorphism of cyclotomes of [EtTh],
  Cor. 2.19(i), obtained "by forming the difference of these two splittings").
* `MonoThetaEnv`, `MonoThetaEnv.Iso` ([EtTh], Def. 2.13(ii)): mono-theta environments and their
  isomorphisms, which form a groupoid (`Iso.refl`, `Iso.symm`, `Iso.trans`).
-/

namespace Iut.EtaleTheta

open SemidirectProduct

variable {μ : Type*} [CommGroup μ] {P : Type*} [Group P] (φ : P →* MulAut μ)

/-- The `1`-cocycle condition for `δ : Π → μ`, `δ(gh) = δ(g)·(g·δ(h))`. -/
def IsCocycle (δ : P → μ) : Prop := ∀ g h, δ (g * h) = δ g * φ g (δ h)

/-- Two cocycles are cohomologous: `δ'(g) = ζ·δ(g)·(g·ζ)⁻¹`. -/
def Cohomologous (δ δ' : P → μ) : Prop := ∃ ζ : μ, ∀ g, δ' g = ζ * δ g * (φ g ζ)⁻¹

variable {φ}

/-- The section `g ↦ (δ(g), g)` of the cyclotomic envelope `μ ⋊ Π ↠ Π` of a cocycle `δ`. -/
def sectionOf (δ : P → μ) (hδ : IsCocycle φ δ) : P →* μ ⋊[φ] P where
  toFun g := ⟨δ g, g⟩
  map_one' := by
    have h := hδ 1 1
    simp only [mul_one, map_one, MulAut.one_apply] at h
    ext
    · exact (left_eq_mul.1 h).symm ▸ rfl
    · rfl
  map_mul' g h := by
    ext
    · exact hδ g h
    · rfl

@[simp] lemma sectionOf_left (δ : P → μ) (hδ : IsCocycle φ δ) (g : P) :
    (sectionOf δ hδ g).left = δ g := rfl

@[simp] lemma sectionOf_right (δ : P → μ) (hδ : IsCocycle φ δ) (g : P) :
    (sectionOf δ hδ g).right = g := rfl

/-- **Homomorphic sections are cocycles**: `g ↦ (δ(g), g)` is multiplicative iff `δ` is a
`1`-cocycle. -/
theorem isHom_iff (δ : P → μ) :
    (∀ g h, (⟨δ (g * h), g * h⟩ : μ ⋊[φ] P) = ⟨δ g, g⟩ * ⟨δ h, h⟩) ↔ IsCocycle φ δ := by
  constructor
  · intro H g h
    exact congrArg SemidirectProduct.left (H g h)
  · intro hδ g h
    exact (sectionOf δ hδ).map_mul g h

/-- Every homomorphic section of `μ ⋊ Π ↠ Π` is `sectionOf` of its cocycle. -/
theorem eq_sectionOf (s : P →* μ ⋊[φ] P) (hs : ∀ g, (s g).right = g) :
    ∃ hδ : IsCocycle φ (fun g => (s g).left), s = sectionOf _ hδ := by
  have hδ : IsCocycle φ (fun g => (s g).left) := by
    intro g h
    have := congrArg SemidirectProduct.left (s.map_mul g h)
    rw [mul_left, hs g] at this
    exact this
  refine ⟨hδ, ?_⟩
  ext g
  · rfl
  · exact hs g

/-- The trivial cocycle. -/
lemma isCocycle_one : IsCocycle φ (fun _ => (1 : μ)) := fun g _ => by simp

/-- The **algebraic (tautological) section** is the section of the trivial cocycle. -/
theorem sectionOf_one : sectionOf (fun _ => (1 : μ)) isCocycle_one = (inr : P →* μ ⋊[φ] P) :=
  by ext g <;> rfl

/-- **The difference of the theta and algebraic sections is the cocycle** ([EtTh],
Cor. 2.19(i)): `s_δ(g)·s^alg(g)⁻¹ = δ(g)`. -/
theorem sectionOf_mul_inr_inv (δ : P → μ) (hδ : IsCocycle φ δ) (g : P) :
    sectionOf δ hδ g * (inr g)⁻¹ = inl (δ g) := by
  ext
  · simp [mul_left, inv_left]
  · simp

/-- **Conjugation by `ζ ∈ μ` changes the cocycle by a coboundary**:
`ζ·s_δ(g)·ζ⁻¹ = (ζ·δ(g)·(g·ζ)⁻¹, g)`. -/
theorem conj_sectionOf (δ : P → μ) (hδ : IsCocycle φ δ) (ζ : μ) (g : P) :
    inl ζ * sectionOf δ hδ g * (inl ζ)⁻¹ = (⟨ζ * δ g * (φ g ζ)⁻¹, g⟩ : μ ⋊[φ] P) := by
  ext
  · simp [mul_left, inv_left, map_inv]
  · simp

/-- **`μ`-conjugate sections ↔ cohomologous cocycles.** -/
theorem conj_sectionOf_iff (δ δ' : P → μ) (hδ : IsCocycle φ δ) (hδ' : IsCocycle φ δ') :
    (∃ ζ : μ, ∀ g, inl ζ * sectionOf δ hδ g * (inl ζ)⁻¹ = sectionOf δ' hδ' g) ↔
      Cohomologous φ δ δ' := by
  constructor
  · rintro ⟨ζ, hζ⟩
    refine ⟨ζ, fun g => ?_⟩
    have := congrArg SemidirectProduct.left (hζ g)
    rw [conj_sectionOf] at this
    exact this.symm
  · rintro ⟨ζ, hζ⟩
    refine ⟨ζ, fun g => ?_⟩
    rw [conj_sectionOf]
    ext
    · exact (hζ g).symm
    · rfl

/-- The image of a section, conjugated by `ζ ∈ μ`. -/
def conjRange (δ : P → μ) (hδ : IsCocycle φ δ) (ζ : μ) : Subgroup (μ ⋊[φ] P) :=
  (sectionOf δ hδ).range.map (MulAut.conj (inl ζ : μ ⋊[φ] P)).toMonoidHom

lemma mem_conjRange (δ : P → μ) (hδ : IsCocycle φ δ) (ζ : μ) (x : μ ⋊[φ] P) :
    x ∈ conjRange δ hδ ζ ↔ x = (⟨ζ * δ x.right * (φ x.right ζ)⁻¹, x.right⟩ : μ ⋊[φ] P) := by
  constructor
  · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_sectionOf]
  · intro hx
    refine ⟨sectionOf δ hδ x.right, ⟨x.right, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_sectionOf, ← hx]

/-- **The images of two theta sections are `μ`-conjugate iff the cocycles are cohomologous.** -/
theorem range_conj_iff (δ δ' : P → μ) (hδ : IsCocycle φ δ) (hδ' : IsCocycle φ δ') :
    (∃ ζ : μ, conjRange δ hδ ζ = (sectionOf δ' hδ').range) ↔ Cohomologous φ δ δ' := by
  constructor
  · rintro ⟨ζ, hζ⟩
    refine ⟨ζ, fun g => ?_⟩
    have hmem : sectionOf δ' hδ' g ∈ conjRange δ hδ ζ := hζ ▸ ⟨g, rfl⟩
    rw [mem_conjRange] at hmem
    exact congrArg SemidirectProduct.left hmem
  · rintro ⟨ζ, hζ⟩
    refine ⟨ζ, le_antisymm ?_ ?_⟩
    · intro x hx
      rw [mem_conjRange] at hx
      refine ⟨x.right, ?_⟩
      rw [hx]
      ext
      · exact hζ _
      · rfl
    · rintro x ⟨g, rfl⟩
      rw [mem_conjRange]
      ext
      · exact hζ g
      · rfl

/-- Datum (c) of a model mono-theta environment ([EtTh], Def. 2.13(ii)(c)): the `μ`-conjugacy
class of the image of the theta section. -/
def thetaClassSubgroups (δ : P → μ) (hδ : IsCocycle φ δ) : Set (Subgroup (μ ⋊[φ] P)) :=
  Set.range (conjRange δ hδ)

/-- **Datum (c) is the cohomology class**: the `μ`-conjugacy classes of the images of two theta
sections coincide iff the cocycles are cohomologous. In particular datum (c) depends only on
the étale theta class, not on the cocycle representing it. -/
theorem thetaClassSubgroups_eq_iff (δ δ' : P → μ) (hδ : IsCocycle φ δ)
    (hδ' : IsCocycle φ δ') :
    thetaClassSubgroups δ hδ = thetaClassSubgroups δ' hδ' ↔ Cohomologous φ δ δ' := by
  constructor
  · intro h
    have : (sectionOf δ' hδ').range ∈ thetaClassSubgroups δ hδ := by
      rw [h]
      refine ⟨1, ?_⟩
      ext x
      rw [mem_conjRange]
      constructor
      · intro hx; exact ⟨x.right, by rw [hx]; ext <;> simp⟩
      · rintro ⟨g, rfl⟩; ext <;> simp
    obtain ⟨ζ, hζ⟩ := this
    exact (range_conj_iff δ δ' hδ hδ').1 ⟨ζ, hζ⟩
  · rintro ⟨ζ, hζ⟩
    -- both sets are the `μ`-conjugates of one subgroup
    have key : ∀ ξ : μ, conjRange δ' hδ' ξ = conjRange δ hδ (ξ * ζ) := by
      intro ξ
      ext x
      rw [mem_conjRange, mem_conjRange, hζ x.right]
      constructor <;> intro hx <;> rw [hx] <;> ext <;>
        simp [map_mul, mul_comm, mul_left_comm, mul_assoc]
    ext H
    constructor
    · rintro ⟨ξ, rfl⟩
      exact ⟨ξ * ζ⁻¹, by rw [key, inv_mul_cancel_right]⟩
    · rintro ⟨ξ, rfl⟩
      exact ⟨ξ * ζ, (key ξ).symm⟩

/-! ### Mono-theta environments -/

universe u

/-- A **mono-theta environment** ([EtTh], Def. 2.13(ii)) in the abstract: a topological group
`G` (`≅ Π^tp_Y[μ_N]` for an actual environment), a subgroup `D` of its automorphisms containing
the inner ones (the preimage of `D_Y ⊆ Out(G)`), and a collection of subgroups (the
`μ_N`-conjugacy class of the image of the theta section). -/
structure MonoThetaEnv where
  /-- The topological group. -/
  G : Type u
  [group : Group G]
  [top : TopologicalSpace G]
  [topGroup : IsTopologicalGroup G]
  /-- The subgroup of automorphisms (preimage of `D_Π ⊆ Out(Π)`). -/
  D : Subgroup (MulAut G)
  inner_le : (MulAut.conj : G →* MulAut G).range ≤ D
  /-- The theta subgroups. -/
  thetaSubgroups : Set (Subgroup G)

attribute [instance] MonoThetaEnv.group MonoThetaEnv.top MonoThetaEnv.topGroup

namespace MonoThetaEnv

/-- Transport of an automorphism along a group isomorphism. -/
def conjAut {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') : MulAut G →* MulAut G' where
  toFun α := (e.symm.trans α).trans e
  map_one' := by ext; simp
  map_mul' α β := by ext; simp [MulAut.mul_apply]

/-- An **isomorphism of mono-theta environments** ([EtTh], Def. 2.13(ii)): an isomorphism of
topological groups mapping `D` to `D'` and the theta subgroups to the theta subgroups. -/
structure Iso (M M' : MonoThetaEnv.{u}) where
  /-- The isomorphism of topological groups. -/
  e : M.G ≃ₜ* M'.G
  map_D : M.D.map (conjAut e.toMulEquiv) = M'.D
  map_theta : Subgroup.map e.toMulEquiv.toMonoidHom '' M.thetaSubgroups = M'.thetaSubgroups

lemma conjAut_refl {G : Type*} [Group G] (α : MulAut G) : conjAut (MulEquiv.refl G) α = α := by
  ext; simp [conjAut]

lemma conjAut_trans {G G' G'' : Type*} [Group G] [Group G'] [Group G''] (e : G ≃* G')
    (e' : G' ≃* G'') (α : MulAut G) : conjAut (e.trans e') α = conjAut e' (conjAut e α) := by
  ext; simp [conjAut]

lemma conjAut_symm_conjAut {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (α : MulAut G) :
    conjAut e.symm (conjAut e α) = α := by
  ext; simp [conjAut]

/-- The identity isomorphism. -/
def Iso.refl (M : MonoThetaEnv.{u}) : Iso M M where
  e := ContinuousMulEquiv.refl M.G
  map_D := by
    ext α
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨β, hβ, rfl⟩
      convert hβ
      exact conjAut_refl β
    · intro hα
      exact ⟨α, hα, conjAut_refl α⟩
  map_theta := by
    ext H
    constructor
    · rintro ⟨K, hK, rfl⟩
      convert hK
      ext
      simp only [Subgroup.mem_map]
      exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨_, hx, rfl⟩⟩
    · intro hH
      refine ⟨H, hH, ?_⟩
      ext
      simp only [Subgroup.mem_map]
      exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨_, hx, rfl⟩⟩

/-- Composition of isomorphisms. -/
def Iso.trans {M M' M'' : MonoThetaEnv.{u}} (f : Iso M M') (g : Iso M' M'') : Iso M M'' where
  e := f.e.trans g.e
  map_D := by
    rw [← g.map_D, ← f.map_D, Subgroup.map_map]
    congr 1
  map_theta := by
    rw [← g.map_theta, ← f.map_theta, Set.image_image]
    refine Set.image_congr fun H _ => ?_
    rw [Subgroup.map_map]
    rfl

/-- The inverse isomorphism. -/
def Iso.symm {M M' : MonoThetaEnv.{u}} (f : Iso M M') : Iso M' M where
  e := f.e.symm
  map_D := by
    rw [← f.map_D, Subgroup.map_map]
    ext α
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨β, hβ, rfl⟩
      convert hβ
      exact conjAut_symm_conjAut f.e.toMulEquiv β
    · intro hα
      exact ⟨α, hα, conjAut_symm_conjAut f.e.toMulEquiv α⟩
  map_theta := by
    rw [← f.map_theta, Set.image_image]
    convert Set.image_id M.thetaSubgroups using 2 with H
    ext x
    simp only [Subgroup.mem_map, id]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      convert hz
      exact f.e.symm_apply_apply z
    · intro hx
      exact ⟨f.e x, ⟨x, hx, rfl⟩, f.e.symm_apply_apply x⟩

end MonoThetaEnv

end Iut.EtaleTheta
