/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EtLocTerminal

/-!
# Extending semi-absolute automorphisms of an open subgroup by self-commensuration

Let `ι : P ↪ M` be an open embedding of compact groups with `M` slim, `pr : M → G` a continuous
surjection onto a slim group `G` such that `ι(P) = pr⁻¹(pr(ι(P)))`, and suppose `M` is
*self-commensurating over `G`* (`hSC`): two open injections `f₁, f₂ : R → M` of a compact group
with `pr ∘ f₂ = g (pr ∘ f₁) g⁻¹` for some `g ∈ G` differ by an inner automorphism of `M`. (For
`M = π₁(C_{F_mod})`, `P = π₁(C_K)` this is `HodgeTheater.piCmod_selfComm`, the coricity of `C_K`.)

Then every continuous automorphism `a` of an open subgroup `H ⊆ P` whose image in `G` is that of
`P` (`hsurj`) and which preserves `H ∩ ker(pr ∘ ι)` (`ha`, semi-absoluteness) **extends to a
continuous automorphism of `P`** preserving `ker(pr ∘ ι)` (`exists_extend`). Construction: for
`ρ ∈ P`, conjugation by `ρ` on the normal core `N` of `H`, transported by `a`, is an open
injection `N → M` lying over `G` up to conjugation by `pr(ι(a(x)))` (`x ∈ H` with the image of
`ρ` in `G`); `hSC` gives `γ_ρ ∈ M`, which lies in `ι(P)` and is unique by slimness. `ρ ↦ γ_ρ` is
the extension; the same construction for `a⁻¹` gives its inverse.

This is the group-theoretic form of "a semi-absolute automorphism of `π₁` of a finite étale cover
of the `K`-core `C_K` comes from an automorphism of `π₁(C_K)`", used in
`HodgeTheater/DStarCKu.lean` for `C̲_K → C_K` (IUT I, Def. 3.1 (d)).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.HodgeTheater.ExtendAut

open Topology Pi1.Profinite CurvesJacobian.Cusp

variable {P M G : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [CompactSpace M] [T2Space M]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-! ### The normal core of an open subgroup -/

lemma isOpen_normalCore {H : Subgroup P} (hH : IsOpen (H : Set P)) :
    IsOpen (H.normalCore : Set P) := by
  haveI : Finite (P ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
    (H.normalCore_isClosed ((⟨H, hH⟩ : OpenSubgroup P).isClosed))

lemma conj_mem_normalCore {H : Subgroup P} (ρ : P) {n : P} (hn : n ∈ H.normalCore) :
    ρ * n * ρ⁻¹ ∈ H.normalCore :=
  (Subgroup.normalCore_normal H).conj_mem n hn ρ

lemma mem_of_mem_normalCore {H : Subgroup P} {n : P} (hn : n ∈ H.normalCore) : n ∈ H :=
  H.normalCore_le hn

/-! ### The relation defining the extension -/

variable {H : Subgroup P}

/-- `b ∈ P` **extends `a` at `ρ`**: `a(ρ n ρ⁻¹) = b a(n) b⁻¹` for all `n` in the normal core of
`H`. -/
def Rel (a : H ≃ₜ* H) (ρ b : P) : Prop :=
  ∀ (n : P) (hn : n ∈ H.normalCore),
    ((a ⟨ρ * n * ρ⁻¹, mem_of_mem_normalCore (conj_mem_normalCore ρ hn)⟩ : H) : P) =
      b * (a ⟨n, mem_of_mem_normalCore hn⟩ : P) * b⁻¹

/-- The image under `a` (inside `P`) of an open subgroup `V ⊆ H`. -/
def imageSub (a : H ≃ₜ* H) (V : Subgroup P) : Subgroup P :=
  ((V.subgroupOf H).map (a : H →* H)).map H.subtype

lemma mem_imageSub (a : H ≃ₜ* H) {V : Subgroup P} {n : P} (hn : n ∈ V) (hnH : n ∈ H) :
    ((a ⟨n, hnH⟩ : H) : P) ∈ imageSub a V :=
  ⟨a ⟨n, hnH⟩, ⟨⟨n, hnH⟩, hn, rfl⟩, rfl⟩

lemma isOpen_imageSub (a : H ≃ₜ* H) (hH : IsOpen (H : Set P)) {V : Subgroup P}
    (hV : IsOpen (V : Set P)) : IsOpen (imageSub a V : Set P) := by
  have h1 : IsOpen (((V.subgroupOf H : Subgroup H)) : Set H) :=
    hV.preimage continuous_subtype_val
  have h2 : IsOpen ((V.subgroupOf H).map (a : H →* H) : Set H) := by
    rw [Subgroup.coe_map]
    exact a.toHomeomorph.isOpenMap _ h1
  rw [imageSub, Subgroup.coe_map]
  exact hH.isOpenMap_subtype_val _ h2

/-- **Uniqueness**: an element is determined by its conjugation action on `a(V)`, `V ⊆ H` open
(`P` embeds openly into the slim `M`). -/
lemma eq_of_conj_eq (ι : P →ₜ* M) (hι : IsOpenEmbedding ι) (hM : IsSlim M) (a : H ≃ₜ* H)
    (hH : IsOpen (H : Set P)) {V : Subgroup P} (hV : IsOpen (V : Set P)) (hVH : V ≤ H) {b b' : P}
    (h : ∀ (n : P) (hn : n ∈ V), b * (a ⟨n, hVH hn⟩ : P) * b⁻¹ = b' * (a ⟨n, hVH hn⟩ : P) * b'⁻¹) :
    b = b' := by
  have h1 : ι (b'⁻¹ * b) = 1 := eq_one_of_commute_open₄ hM ι hι.isOpen_range
    (isOpen_imageSub a hH hV) fun u hu => by
      obtain ⟨_, ⟨⟨n, hnH⟩, hn, rfl⟩, rfl⟩ := hu
      have e := h n hn
      rw [← map_mul, ← map_mul]
      congr 1
      change b'⁻¹ * b * (a ⟨n, hnH⟩ : P) = (a ⟨n, hnH⟩ : P) * (b'⁻¹ * b)
      calc b'⁻¹ * b * (a ⟨n, hnH⟩ : P)
          = b'⁻¹ * (b * (a ⟨n, hVH hn⟩ : P) * b⁻¹) * b := by group
        _ = b'⁻¹ * (b' * (a ⟨n, hVH hn⟩ : P) * b'⁻¹) * b := by rw [e]
        _ = (a ⟨n, hnH⟩ : P) * (b'⁻¹ * b) := by group
  have h2 : b'⁻¹ * b = 1 := hι.injective (h1.trans (map_one ι).symm)
  calc b = b' * (b'⁻¹ * b) := by group
    _ = b' := by rw [h2, mul_one]

/-- Two extensions of `a` at `ρ` agree. -/
lemma Rel.unique (ι : P →ₜ* M) (hι : IsOpenEmbedding ι) (hM : IsSlim M) {a : H ≃ₜ* H}
    (hH : IsOpen (H : Set P)) {ρ b b' : P} (h : Rel a ρ b) (h' : Rel a ρ b') : b = b' :=
  eq_of_conj_eq ι hι hM a hH (isOpen_normalCore hH) H.normalCore_le fun n hn =>
    (h n hn).symm.trans (h' n hn)

/-- `a(h)` extends `a` at `h ∈ H`. -/
lemma rel_self (a : H ≃ₜ* H) (h : H) : Rel a (h : P) (a h : P) := by
  intro n hn
  have e : (⟨(h : P) * n * (h : P)⁻¹, mem_of_mem_normalCore (conj_mem_normalCore (h : P) hn)⟩ :
      H) = h * ⟨n, mem_of_mem_normalCore hn⟩ * h⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  rfl

/-- Extensions at `ρ₁`, `ρ₂` multiply to an extension at `ρ₁ ρ₂`. -/
lemma Rel.mul {a : H ≃ₜ* H} {ρ₁ ρ₂ b₁ b₂ : P} (h₁ : Rel a ρ₁ b₁) (h₂ : Rel a ρ₂ b₂) :
    Rel a (ρ₁ * ρ₂) (b₁ * b₂) := by
  intro n hn
  have hn₂ := conj_mem_normalCore ρ₂ hn
  have e : (⟨ρ₁ * ρ₂ * n * (ρ₁ * ρ₂)⁻¹,
      mem_of_mem_normalCore (conj_mem_normalCore (ρ₁ * ρ₂) hn)⟩ : H) =
      ⟨ρ₁ * (ρ₂ * n * ρ₂⁻¹) * ρ₁⁻¹, mem_of_mem_normalCore (conj_mem_normalCore ρ₁ hn₂)⟩ :=
    Subtype.ext (by group)
  rw [e, h₁ _ hn₂, h₂ n hn]
  group

/-- **Inverse relation**: if `b'` extends `a⁻¹` at `ρ'`, then `ρ'` extends `a` at `b'` on the open
subgroup of `n` in the normal core with `a(n)` in the normal core. -/
lemma rel_symm_conj {a : H ≃ₜ* H} {ρ' b' : P} (h : Rel a.symm ρ' b') (n : P)
    (hn : n ∈ H.normalCore) (han : ((a ⟨n, mem_of_mem_normalCore hn⟩ : H) : P) ∈ H.normalCore) :
    ((a ⟨b' * n * b'⁻¹, mem_of_mem_normalCore (conj_mem_normalCore b' hn)⟩ : H) : P) =
      ρ' * (a ⟨n, mem_of_mem_normalCore hn⟩ : P) * ρ'⁻¹ := by
  have e := h _ han
  have e2 : (⟨((a ⟨n, mem_of_mem_normalCore hn⟩ : H) : P), mem_of_mem_normalCore han⟩ : H) =
      a ⟨n, mem_of_mem_normalCore hn⟩ := rfl
  rw [e2, ContinuousMulEquiv.symm_apply_apply] at e
  have e3 : (⟨b' * n * b'⁻¹, mem_of_mem_normalCore (conj_mem_normalCore b' hn)⟩ : H) =
      a.symm ⟨ρ' * (a ⟨n, mem_of_mem_normalCore hn⟩ : P) * ρ'⁻¹,
        mem_of_mem_normalCore (conj_mem_normalCore ρ' han)⟩ :=
    Subtype.ext e.symm
  rw [e3, ContinuousMulEquiv.apply_symm_apply]

/-! ### Existence -/

section Exist

variable (pr : M →ₜ* G)

/-- **Self-commensuration of `M` over `G`** (the hypothesis `hSC`; `piCmod_selfComm`). -/
def SelfComm : Prop :=
  ∀ (R : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [CompactSpace R]
    (f₁ f₂ : R →ₜ* M), Function.Injective f₁ → IsOpen (Set.range f₁) →
      Function.Injective f₂ → IsOpen (Set.range f₂) → ∀ g : G,
        (∀ x, pr (f₂ x) = g * pr (f₁ x) * g⁻¹) → ∃ γ : M, ∀ x, f₂ x = γ * f₁ x * γ⁻¹

variable {pr} {ι : P →ₜ* M}

/-- Semi-absoluteness of `a` in the form used below. -/
lemma pr_eq_of_pr_eq {a : H ≃ₜ* H} (ha : ∀ h : H, pr (ι (a h)) = 1 ↔ pr (ι h) = 1) {h₁ h₂ : H}
    (e : pr (ι h₁) = pr (ι h₂)) : pr (ι (a h₁)) = pr (ι (a h₂)) := by
  have h0 : pr (ι ((h₁⁻¹ * h₂ : H) : P)) = 1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, map_inv, e,
      inv_mul_cancel]
  have h1 := (ha _).2 h0
  rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv,
    map_inv] at h1
  exact (inv_mul_eq_one.1 h1)

/-- **Existence of the extension at `ρ`** (self-commensuration applied to conjugation by `ρ` on
the normal core of `H`, transported by `a`), with the image of the extension in `G`. -/
theorem exists_rel (hι : IsOpenEmbedding ι) (hG : IsSlim G) (hpr : Function.Surjective pr)
    (hB : ∀ (y : M) (ρ : P), pr y = pr (ι ρ) → y ∈ Set.range ι) (hH : IsOpen (H : Set P))
    (hsurj : ∀ ρ : P, ∃ x : H, pr (ι x) = pr (ι ρ)) (hSC : SelfComm pr) (a : H ≃ₜ* H)
    (ha : ∀ h : H, pr (ι (a h)) = 1 ↔ pr (ι h) = 1) (ρ : P) :
    ∃ b : P, Rel a ρ b ∧ ∃ x : H, pr (ι x) = pr (ι ρ) ∧ pr (ι b) = pr (ι (a x)) := by
  have hNo : IsOpen (H.normalCore : Set P) := isOpen_normalCore hH
  haveI : CompactSpace H.normalCore :=
    isCompact_iff_compactSpace.1 (⟨H.normalCore, hNo⟩ : OpenSubgroup P).isClosed.isCompact
  have hNH : H.normalCore ≤ H := H.normalCore_le
  let incl : H.normalCore →ₜ* H := ⟨Subgroup.inclusion hNH, continuous_inclusion hNH⟩
  let sub : H →ₜ* P := ⟨H.subtype, continuous_subtype_val⟩
  let f₁ : H.normalCore →ₜ* M :=
    ι.comp (sub.comp ((ContinuousMonoidHom.toContinuousMonoidHom a).comp incl))
  let c : H.normalCore →ₜ* H.normalCore :=
    { toFun := fun n => ⟨ρ * n * ρ⁻¹, conj_mem_normalCore ρ n.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group)
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact (continuous_const.mul continuous_subtype_val).mul continuous_const }
  let f₂ : H.normalCore →ₜ* M := f₁.comp c
  have hf₁ : ∀ n : H.normalCore, f₁ n = ι (a ⟨n, hNH n.2⟩ : P) := fun n => rfl
  have hf₂ : ∀ n : H.normalCore,
      f₂ n = ι (a ⟨ρ * n * ρ⁻¹, hNH (conj_mem_normalCore ρ n.2)⟩ : P) := fun n => rfl
  have hi₁ : Function.Injective f₁ := fun x y hxy => by
    rw [hf₁, hf₁] at hxy
    have h1 := a.injective (Subtype.ext (hι.injective hxy))
    have h2 : (x : P) = y := congrArg (Subtype.val : H → P) h1
    exact Subtype.ext h2
  have hcs : Function.Surjective c := fun n =>
    ⟨⟨ρ⁻¹ * n * ρ, by simpa using conj_mem_normalCore ρ⁻¹ n.2⟩, Subtype.ext (by
      change ρ * (ρ⁻¹ * (n : P) * ρ) * ρ⁻¹ = n
      group)⟩
  have hci : Function.Injective c := fun x y hxy => by
    have := congrArg Subtype.val hxy
    change ρ * (x : P) * ρ⁻¹ = ρ * y * ρ⁻¹ at this
    exact Subtype.ext (by simpa using this)
  have hr₁ : Set.range f₁ = ι '' (imageSub a H.normalCore : Set P) := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨_, mem_imageSub a n.2 (hNH n.2), rfl⟩
    · rintro ⟨_, ⟨_, ⟨⟨n, hnH⟩, hn, rfl⟩, rfl⟩, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  have ho₁ : IsOpen (Set.range f₁) := by
    rw [hr₁]
    exact hι.isOpenMap _ (isOpen_imageSub a hH hNo)
  have hr₂ : Set.range f₂ = Set.range f₁ := by
    change Set.range (f₁ ∘ c) = _
    rw [Set.range_comp, hcs.range_eq, Set.image_univ]
  obtain ⟨x, hx⟩ := hsurj ρ
  let g : G := pr (ι (a x))
  have hg : ∀ n, pr (f₂ n) = g * pr (f₁ n) * g⁻¹ := fun n => by
    rw [hf₂, hf₁]
    have e : pr (ι ((⟨ρ * n * ρ⁻¹, hNH (conj_mem_normalCore ρ n.2)⟩ : H) : P)) =
        pr (ι ((x * ⟨n, hNH n.2⟩ * x⁻¹ : H) : P)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hx]
    rw [pr_eq_of_pr_eq ha e, map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rfl
  obtain ⟨γ, hγ⟩ := hSC H.normalCore f₁ f₂ hi₁ ho₁ (hi₁.comp hci) (hr₂ ▸ ho₁) g hg
  have hprγ : pr γ = g := by
    have hp : IsOpen (Set.range pr) := by
      rw [hpr.range_eq]
      exact isOpen_univ
    have h1 : g⁻¹ * pr γ = 1 := eq_one_of_commute_open₄ hG pr hp
      (U := (f₁ : H.normalCore →* M).range) ho₁ fun u hu => by
        obtain ⟨n, rfl⟩ := hu
        have e : g * pr (f₁ n) * g⁻¹ = pr γ * pr (f₁ n) * (pr γ)⁻¹ := by
          rw [← hg n, hγ n, map_mul, map_mul, map_inv]
        change g⁻¹ * pr γ * pr (f₁ n) = pr (f₁ n) * (g⁻¹ * pr γ)
        calc g⁻¹ * pr γ * pr (f₁ n)
            = g⁻¹ * (pr γ * pr (f₁ n) * (pr γ)⁻¹) * pr γ := by group
          _ = g⁻¹ * (g * pr (f₁ n) * g⁻¹) * pr γ := by rw [e]
          _ = pr (f₁ n) * (g⁻¹ * pr γ) := by group
    calc pr γ = g * (g⁻¹ * pr γ) := by group
      _ = g := by rw [h1, mul_one]
  obtain ⟨b, hb⟩ := hB γ (a x) hprγ
  refine ⟨b, fun n hn => hι.injective ?_, x, hx, by rw [hb, hprγ]⟩
  have e := hγ ⟨n, hn⟩
  rw [hf₂, hf₁, ← hb] at e
  rw [e, map_mul, map_mul, map_inv]

end Exist

/-! ### The extension -/

section Extend

variable {ι : P →ₜ* M}

/-- An extension function is a homomorphism. -/
lemma ext_mul (hι : IsOpenEmbedding ι) (hM : IsSlim M) {a : H ≃ₜ* H} (hH : IsOpen (H : Set P))
    {β : P → P} (hβ : ∀ ρ, Rel a ρ (β ρ)) (ρ₁ ρ₂ : P) : β (ρ₁ * ρ₂) = β ρ₁ * β ρ₂ :=
  Rel.unique ι hι hM hH (hβ _) ((hβ ρ₁).mul (hβ ρ₂))

/-- An extension function extends `a`. -/
lemma ext_of_mem (hι : IsOpenEmbedding ι) (hM : IsSlim M) {a : H ≃ₜ* H} (hH : IsOpen (H : Set P))
    {β : P → P} (hβ : ∀ ρ, Rel a ρ (β ρ)) (h : H) : β h = a h :=
  Rel.unique ι hι hM hH (hβ _) (rel_self a h)

/-- The open subgroup of `n ∈ N` with `a(n) ∈ N` (`N` the normal core of `H`). -/
def coreSub (a : H ≃ₜ* H) : Subgroup P :=
  ((H.normalCore.subgroupOf H) ⊓ (H.normalCore.subgroupOf H).comap (a : H →* H)).map H.subtype

lemma isOpen_coreSub (a : H ≃ₜ* H) (hH : IsOpen (H : Set P)) :
    IsOpen (coreSub a : Set P) := by
  have hN : IsOpen ((H.normalCore.subgroupOf H : Subgroup H) : Set H) :=
    (isOpen_normalCore hH).preimage continuous_subtype_val
  have h2 : IsOpen (((H.normalCore.subgroupOf H) ⊓
      (H.normalCore.subgroupOf H).comap (a : H →* H) : Subgroup H) : Set H) :=
    hN.inter (hN.preimage a.continuous)
  rw [coreSub, Subgroup.coe_map]
  exact hH.isOpenMap_subtype_val _ h2

lemma coreSub_le (a : H ≃ₜ* H) : coreSub a ≤ H := by
  rintro _ ⟨h, -, rfl⟩
  exact h.2

/-- Extension functions of `a` and `a⁻¹` are mutually inverse. -/
lemma ext_symm (hι : IsOpenEmbedding ι) (hM : IsSlim M) {a : H ≃ₜ* H} (hH : IsOpen (H : Set P))
    {β β' : P → P} (hβ : ∀ ρ, Rel a ρ (β ρ)) (hβ' : ∀ ρ, Rel a.symm ρ (β' ρ)) (b' : P) :
    β (β' b') = b' := by
  refine eq_of_conj_eq ι hι hM a hH (isOpen_coreSub a hH) (coreSub_le a) fun n hn => ?_
  obtain ⟨⟨n, hnH⟩, ⟨hnN, hanN⟩, rfl⟩ := hn
  have e1 := hβ (β' b') n hnN
  have e2 := rel_symm_conj (hβ' b') n hnN hanN
  exact e1.symm.trans e2

/-- **Semi-absolute automorphisms of an open subgroup extend** (module docstring). -/
theorem exists_extend {pr : M →ₜ* G} (hι : IsOpenEmbedding ι) (hM : IsSlim M) (hG : IsSlim G)
    (hpr : Function.Surjective pr)
    (hB : ∀ (y : M) (ρ : P), pr y = pr (ι ρ) → y ∈ Set.range ι) (hH : IsOpen (H : Set P))
    (hsurj : ∀ ρ : P, ∃ x : H, pr (ι x) = pr (ι ρ)) (hSC : SelfComm pr) (a : H ≃ₜ* H)
    (ha : ∀ h : H, pr (ι (a h)) = 1 ↔ pr (ι h) = 1) :
    ∃ β : P ≃ₜ* P, (∀ h : H, β h = a h) ∧ ∀ ρ, pr (ι (β ρ)) = 1 ↔ pr (ι ρ) = 1 := by
  have ha' : ∀ h : H, pr (ι (a.symm h)) = 1 ↔ pr (ι h) = 1 := fun h => by
    have := ha (a.symm h)
    rw [ContinuousMulEquiv.apply_symm_apply] at this
    exact this.symm
  choose β hβ using exists_rel hι hG hpr hB hH hsurj hSC a ha
  choose β' hβ' using exists_rel hι hG hpr hB hH hsurj hSC a.symm ha'
  have hR : ∀ ρ, Rel a ρ (β ρ) := fun ρ => (hβ ρ).1
  have hR' : ∀ ρ, Rel a.symm ρ (β' ρ) := fun ρ => (hβ' ρ).1
  have hR'' : ∀ ρ, Rel a.symm.symm ρ (β ρ) := hR
  have hcont : ∀ (a : H ≃ₜ* H) (β : P → P), (∀ ρ, Rel a ρ (β ρ)) → Continuous β := by
    intro a β hβ
    let m : P →* P :=
      { toFun := β
        map_one' := by
          have := ext_of_mem hι hM hH hβ 1
          rw [map_one] at this
          exact this
        map_mul' := ext_mul hι hM hH hβ }
    change Continuous m
    refine continuous_of_continuousAt_one m ?_
    have hon : ContinuousOn β (H : Set P) := by
      rw [continuousOn_iff_continuous_restrict]
      have e : (H : Set P).restrict β = fun h : H => (a h : P) :=
        funext fun h => ext_of_mem hι hM hH hβ h
      rw [e]
      exact continuous_subtype_val.comp a.continuous
    exact hon.continuousAt (hH.mem_nhds H.one_mem)
  let m : P ≃* P :=
    { toFun := β
      invFun := β'
      left_inv := ext_symm hι hM hH hR' hR''
      right_inv := ext_symm hι hM hH hR hR'
      map_mul' := ext_mul hι hM hH hR }
  refine ⟨⟨m, hcont a β hR, hcont a.symm β' hR'⟩, fun h => ext_of_mem hι hM hH hR h,
    fun ρ => ?_⟩
  obtain ⟨-, x, hx, hb⟩ := hβ ρ
  change pr (ι (β ρ)) = 1 ↔ _
  rw [hb, ← hx]
  exact ha x

end Extend

end Iut.HodgeTheater.ExtendAut
