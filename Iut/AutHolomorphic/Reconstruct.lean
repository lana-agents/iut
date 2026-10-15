/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Basic

/-!
# The model-implicit reconstruction of the local linear structure (generic part)

Let `G ⊆ Aut(X^top)` be a group of self-homeomorphisms of a topological space `X` (for an
Aut-holomorphic space, `G = A_X(X)`), and `p ∈ X`. The following data are defined from `(X, G, p)`
alone, with no reference to a model of `ℂ` ([AbsTopIII], Remark 2.7.4: "model-implicit"):

* `IsTransl G g`: `g ∈ G` is a **translation**: `g = 1` or `g` has no fixed point;
* `transl G p a`: a translation sending `p` to `a` (unique in the cases of interest);
* `addAt G p a b = transl G p a b`, `negAt G p a`: the **local additive structure at `p`** (the
  sum `a +_p b` relative to the origin `p`, [AbsTopIII], Proposition 2.5(e));
* `Kset G p ⊆ (X → X)`: the elements of the stabiliser `A_p = Stab_G(p)` together with the constant
  map `p` ("`A_p ∪ {0}`", [AbsTopIII], Proposition 2.6(a), Corollary 2.7(e));
* the operations on `X → X`: `kAdd` (pointwise `+_p`), `kNeg`, `kMul` (composition), `kInv`
  (inverse in `G`), `kZero` (the constant `p`), `kOne` (the identity).

For the Aut-holomorphic plane these make `Kset G p` a topological field isomorphic to `ℂ`
(`Iut/AutHolomorphic/PlaneField.lean`).

**Functoriality** (`transportFun`, `kAdd_transport`, …): a homeomorphism `φ : X ≃ₜ Y` with
`G_Y = φ G_X φ⁻¹` (e.g. an isomorphism of connected Aut-holomorphic spaces, `IsIso.global_eq`)
carries all these data for `(X, G_X, p)` to those for `(Y, G_Y, φ p)` via `f ↦ φ ∘ f ∘ φ⁻¹`,
provided the translations act simply transitively (`TranslSimplyTransitive`).
-/

namespace Iut

namespace AutHol

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Translations and the local additive structure -/

/-- **Translations**: the elements of `G` without fixed points, and the identity. -/
def IsTransl (G : Subgroup (X ≃ₜ X)) (g : X ≃ₜ X) : Prop := g ∈ G ∧ (g = 1 ∨ ∀ x, g x ≠ x)

/-- **The translations act simply transitively.** -/
def TranslSimplyTransitive (G : Subgroup (X ≃ₜ X)) : Prop :=
  ∀ p a : X, ∃! g, IsTransl G g ∧ g p = a

open Classical in
/-- **The translation sending `p` to `a`** (the identity if there is none). -/
noncomputable def transl (G : Subgroup (X ≃ₜ X)) (p a : X) : X ≃ₜ X :=
  if h : ∃ g, IsTransl G g ∧ g p = a then h.choose else 1

theorem transl_spec {G : Subgroup (X ≃ₜ X)} (hG : TranslSimplyTransitive G) (p a : X) :
    IsTransl G (transl G p a) ∧ transl G p a p = a := by
  have h : ∃ g, IsTransl G g ∧ g p = a := (hG p a).exists
  rw [transl, dif_pos h]
  exact h.choose_spec

theorem transl_eq {G : Subgroup (X ≃ₜ X)} (hG : TranslSimplyTransitive G) {p a : X}
    {g : X ≃ₜ X} (hg : IsTransl G g) (hga : g p = a) : transl G p a = g :=
  (hG p a).unique (transl_spec hG p a) ⟨hg, hga⟩

/-- **The local additive structure at `p`**: `a +_p b`. -/
noncomputable def addAt (G : Subgroup (X ≃ₜ X)) (p a b : X) : X := transl G p a b

/-- The additive inverse `−_p a` relative to the origin `p`. -/
noncomputable def negAt (G : Subgroup (X ≃ₜ X)) (p a : X) : X := (transl G p a).symm p

/-! ### The set `A_p ∪ {0}` and its operations -/

/-- **`A_p ∪ {0}`**: the maps underlying elements of `G` fixing `p`, and the constant map `p`. -/
def Kset (G : Subgroup (X ≃ₜ X)) (p : X) : Set (X → X) :=
  {f | (∃ g ∈ G, g p = p ∧ ⇑g = f) ∨ f = fun _ => p}

/-- Addition: pointwise `+_p`. -/
noncomputable def kAdd (G : Subgroup (X ≃ₜ X)) (p : X) (f f' : X → X) : X → X :=
  fun x => addAt G p (f x) (f' x)

/-- Negation: pointwise `−_p`. -/
noncomputable def kNeg (G : Subgroup (X ≃ₜ X)) (p : X) (f : X → X) : X → X :=
  fun x => negAt G p (f x)

/-- Multiplication: composition. -/
def kMul (f f' : X → X) : X → X := f ∘ f'

/-- Zero: the constant map `p`. -/
def kZero (p : X) : X → X := fun _ => p

/-- One: the identity. -/
def kOne : X → X := id

open Classical in
/-- Inversion: the inverse in `G` (the constant map is sent to itself). -/
noncomputable def kInv (G : Subgroup (X ≃ₜ X)) (p : X) (f : X → X) : X → X :=
  if h : ∃ g ∈ G, g p = p ∧ ⇑g = f then ⇑(h.choose.symm) else f

theorem kInv_of_mem {G : Subgroup (X ≃ₜ X)} {p : X} {g : X ≃ₜ X} (hg : g ∈ G) (hgp : g p = p) :
    kInv G p g = ⇑g.symm := by
  have h : ∃ g' ∈ G, g' p = p ∧ ⇑g' = ⇑g := ⟨g, hg, hgp, rfl⟩
  rw [kInv, dif_pos h]
  have : h.choose = g := DFunLike.coe_injective h.choose_spec.2.2
  rw [this]

theorem kInv_zero (G : Subgroup (X ≃ₜ X)) {p : X} (hX : ∃ x : X, x ≠ p) :
    kInv G p (kZero p) = kZero p := by
  rw [kInv, dif_neg]
  rintro ⟨g, -, -, hg⟩
  obtain ⟨x, hx⟩ := hX
  apply hx
  have h1 := congrFun hg x
  have h2 := congrFun hg (g.symm x)
  simp only [Homeomorph.apply_symm_apply, kZero] at h1 h2
  exact h2

/-! ### Functoriality -/

/-- Transport of a map `X → X` along `φ : X ≃ₜ Y`: `f ↦ φ ∘ f ∘ φ⁻¹`. -/
def transportFun (φ : X ≃ₜ Y) (f : X → X) : Y → Y := fun y => φ (f (φ.symm y))

theorem transportFun_coe (φ : X ≃ₜ Y) (g : X ≃ₜ X) : transportFun φ g = ⇑(conj φ g) := rfl

theorem transportFun_injective (φ : X ≃ₜ Y) : Function.Injective (transportFun φ) := by
  intro f f' h
  ext x
  have := congrFun h (φ x)
  simp only [transportFun, Homeomorph.symm_apply_apply] at this
  exact φ.injective this

section Transport

variable {GX : Subgroup (X ≃ₜ X)} {GY : Subgroup (Y ≃ₜ Y)} {φ : X ≃ₜ Y}

theorem mem_of_map_conj (hG : GY = GX.map (conj φ).toMonoidHom) {g : X ≃ₜ X} :
    conj φ g ∈ GY ↔ g ∈ GX := by
  rw [hG, mem_map_conj]
  have : conj φ.symm (conj φ g) = g := by ext x; simp
  rw [this]

theorem isTransl_conj (hG : GY = GX.map (conj φ).toMonoidHom) {g : X ≃ₜ X} :
    IsTransl GY (conj φ g) ↔ IsTransl GX g := by
  unfold IsTransl
  rw [mem_of_map_conj hG]
  refine and_congr Iff.rfl (or_congr ?_ ?_)
  · rw [map_eq_one_iff _ (conj φ).injective]
  · constructor
    · intro h x hx
      apply h (φ x)
      simp [hx]
    · intro h y hy
      apply h (φ.symm y)
      have := congrArg φ.symm hy
      simpa using this

theorem translSimplyTransitive_of_conj (hG : GY = GX.map (conj φ).toMonoidHom)
    (hY : TranslSimplyTransitive GY) : TranslSimplyTransitive GX := by
  intro p a
  obtain ⟨g, ⟨hg, hgp⟩, huniq⟩ := hY (φ p) (φ a)
  refine ⟨conj φ.symm g, ⟨?_, ?_⟩, ?_⟩
  · rw [← isTransl_conj hG]
    have : conj φ (conj φ.symm g) = g := by ext; simp
    rwa [this]
  · simp [hgp]
  · rintro g' ⟨hg', hg'p⟩
    have : conj φ g' = g := huniq _ ⟨(isTransl_conj hG).2 hg', by simp [hg'p]⟩
    rw [← this]
    ext
    simp

theorem transl_conj (hG : GY = GX.map (conj φ).toMonoidHom) (hY : TranslSimplyTransitive GY)
    (p a : X) : transl GY (φ p) (φ a) = conj φ (transl GX p a) := by
  have hX := translSimplyTransitive_of_conj hG hY
  obtain ⟨h1, h2⟩ := transl_spec hX p a
  exact transl_eq hY ((isTransl_conj hG).2 h1) (by simp [h2])

theorem addAt_conj (hG : GY = GX.map (conj φ).toMonoidHom) (hY : TranslSimplyTransitive GY)
    (p a b : X) : addAt GY (φ p) (φ a) (φ b) = φ (addAt GX p a b) := by
  rw [addAt, addAt, transl_conj hG hY]
  simp

theorem negAt_conj (hG : GY = GX.map (conj φ).toMonoidHom) (hY : TranslSimplyTransitive GY)
    (p a : X) : negAt GY (φ p) (φ a) = φ (negAt GX p a) := by
  rw [negAt, negAt, transl_conj hG hY]
  simp [conj]

theorem mem_Kset_transport (hG : GY = GX.map (conj φ).toMonoidHom) {p : X} {f : X → X} :
    transportFun φ f ∈ Kset GY (φ p) ↔ f ∈ Kset GX p := by
  constructor
  · rintro (⟨g, hg, hgp, hgf⟩ | h)
    · left
      refine ⟨conj φ.symm g, ?_, ?_, ?_⟩
      · rw [← mem_of_map_conj hG]
        have : conj φ (conj φ.symm g) = g := by ext; simp
        rwa [this]
      · simp [hgp]
      · ext x
        have := congrFun hgf (φ x)
        simp only [transportFun, Homeomorph.symm_apply_apply] at this
        simp [this]
    · right
      ext x
      have := congrFun h (φ x)
      simp only [transportFun, Homeomorph.symm_apply_apply] at this
      exact φ.injective this
  · rintro (⟨g, hg, hgp, rfl⟩ | rfl)
    · exact Or.inl ⟨conj φ g, (mem_of_map_conj hG).2 hg, by simp [hgp], rfl⟩
    · exact Or.inr rfl

theorem kAdd_transport (hG : GY = GX.map (conj φ).toMonoidHom) (hY : TranslSimplyTransitive GY)
    (p : X) (f f' : X → X) :
    kAdd GY (φ p) (transportFun φ f) (transportFun φ f') = transportFun φ (kAdd GX p f f') := by
  ext y
  simp only [kAdd, transportFun]
  rw [addAt_conj hG hY]

theorem kNeg_transport (hG : GY = GX.map (conj φ).toMonoidHom) (hY : TranslSimplyTransitive GY)
    (p : X) (f : X → X) :
    kNeg GY (φ p) (transportFun φ f) = transportFun φ (kNeg GX p f) := by
  ext y
  simp only [kNeg, transportFun]
  rw [negAt_conj hG hY]

theorem kMul_transport (f f' : X → X) :
    kMul (transportFun φ f) (transportFun φ f') = transportFun φ (kMul f f') := by
  ext y
  simp [kMul, transportFun]

theorem kZero_transport (p : X) : kZero (φ p) = transportFun φ (kZero p) := rfl

theorem kOne_transport : (kOne : Y → Y) = transportFun φ kOne := by
  ext y
  simp [kOne, transportFun]

theorem kInv_transport (hG : GY = GX.map (conj φ).toMonoidHom) {p : X} (hX : ∃ x : X, x ≠ p)
    {f : X → X} (hf : f ∈ Kset GX p) :
    kInv GY (φ p) (transportFun φ f) = transportFun φ (kInv GX p f) := by
  rcases hf with ⟨g, hg, hgp, rfl⟩ | rfl
  · rw [transportFun_coe, kInv_of_mem ((mem_of_map_conj hG).2 hg) (by simp [hgp]),
      kInv_of_mem hg hgp]
    ext y
    simp [transportFun, conj]
  · have hY : ∃ y : Y, y ≠ φ p := by
      obtain ⟨x, hx⟩ := hX
      exact ⟨φ x, fun h => hx (φ.injective h)⟩
    change kInv GY (φ p) (transportFun φ (kZero p)) = transportFun φ (kInv GX p (kZero p))
    rw [← kZero_transport, kInv_zero GY hY, kInv_zero GX hX, kZero_transport]

end Transport

end AutHol

end Iut
