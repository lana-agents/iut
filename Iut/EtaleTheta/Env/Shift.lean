/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Env.Model

/-!
# Shifting automorphisms ([EtTh], Proposition 2.14(ii))

In the abstract theta setting of `Env/Model.lean`, let `tΘ` be the theta section of a second
cocycle `η'` on `PYdd` (in [EtTh]: a conjugate of `s^Θ` under the actions of `K^×` and `l·ℤ`),
and let `δ = tΘ − sΘ`. [EtTh], Prop. 2.14(ii): the "shift by `δ`" extends to an automorphism
`α_δ` of `Π_Y[μ]` which is the identity on the quotient `Π_Y[μ] ↠ Π_Y` and on its kernel `μ`,
conjugation by `α_δ` maps `sΘ` to `tΘ`, and `α_δ` normalises `D_Y`.

In [EtTh] two facts about the genuine objects enter the proof, and here they are explicit,
named hypotheses (Layer-B obligations, MR15 plan):

* **the extension of `δ`** to a cocycle `δY` on all of `PY` ([EtTh]: `δ` lies in the span of
  the Kummer classes of `K^×` and of `Ü²`, which descends to `Y̲` — Prop. 1.5(ii),(iii)): the
  argument `δY` with `hδY : IsCocycle … δY` and the restriction identity `hres`;
* **`hShiftConj`**: the `PX`-conjugates of `δY` differ from `δY` by a Kummer cocycle and a
  coboundary ([EtTh]: an element of `Gal(Y̲/X̲)` maps `Ü²` to a `K^×`-multiple of `Ü²`).

## Main results

* `shift`: the shift `(m, h) ↦ (δY(h)·m, h)` of `Π_Y[μ]`; `shift_right`, `shift_inlY`: it is the
  identity on the quotient and on the kernel;
* `shift_thetaSection`: it maps the theta section of `η` to the theta section of `η·δ⁻¹`
  (i.e. `tΘ = sΘ + δ`);
* `shift_conj_mem_DY` (**normalises `D_Y`**): under `hShiftConj`, `α_δ ∘ γ ∘ α_δ⁻¹ ∈ D_Y` for all
  `γ ∈ D_Y`;
* `shiftIso` (**[EtTh], Prop. 2.14(ii)**): `α_δ` is an isomorphism of model mono-theta
  environments `modelEnv η ≅ modelEnv (η·δ⁻¹)`, inducing the identity on `Π_Y` (`shiftIso_right`).
  This is the uniqueness "up to isomorphisms lying over the identity of `Π_Y̲`" of
  [EtTh], Cor. 2.18(ii).
-/

namespace Iut.EtaleTheta.Env

open SemidirectProduct

universe u

variable {PX G μ : Type u} [Group PX] [Group G] [CommGroup μ] (aug : PX →* G)
  (ψ : G →* MulAut μ)

/-- The action of `PY` on `μ`. -/
abbrev actY (PY : Subgroup PX) : PY →* MulAut μ := (act aug ψ).comp PY.subtype

section Shift

variable {PY : Subgroup PX}

/-- The element of `PY` underlying an element of `Π_Y[μ]`. -/
def rightY (z : envY aug ψ PY) : PY := ⟨(z : EnvX aug ψ).right, z.2⟩

/-- **The shifting automorphism** `α_δ : (m, h) ↦ (δY(h)·m, h)` of `Π_Y[μ]` ([EtTh],
Prop. 2.14(ii)). -/
def shift (δY : PY → μ) (hδY : IsCocycle (actY aug ψ PY) δY) : MulAut (envY aug ψ PY) where
  toFun z := ⟨⟨δY (rightY aug ψ z) * (z : EnvX aug ψ).left, (z : EnvX aug ψ).right⟩, z.2⟩
  invFun z := ⟨⟨(δY (rightY aug ψ z))⁻¹ * (z : EnvX aug ψ).left, (z : EnvX aug ψ).right⟩, z.2⟩
  left_inv z := Subtype.ext (SemidirectProduct.ext (by simp [rightY]) rfl)
  right_inv z := Subtype.ext (SemidirectProduct.ext (by simp [rightY]) rfl)
  map_mul' z z' := by
    apply Subtype.ext
    refine SemidirectProduct.ext ?_ rfl
    have h : δY (rightY aug ψ (z * z')) = δY (rightY aug ψ z) *
        ψ (aug (z : EnvX aug ψ).right) (δY (rightY aug ψ z')) := by
      rw [show rightY aug ψ (z * z') = rightY aug ψ z * rightY aug ψ z' from rfl]
      exact hδY _ _
    change δY (rightY aug ψ (z * z')) * ((z : EnvX aug ψ) * z').left =
      (δY (rightY aug ψ z) * (z : EnvX aug ψ).left) *
        ψ (aug (z : EnvX aug ψ).right) (δY (rightY aug ψ z') * (z' : EnvX aug ψ).left)
    rw [h, mul_left, map_mul]
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    simp only [mul_assoc, mul_left_comm, mul_comm]

variable {δY : PY → μ} (hδY : IsCocycle (actY aug ψ PY) δY)

@[simp] lemma coe_shift (z : envY aug ψ PY) :
    (shift aug ψ δY hδY z : EnvX aug ψ) = inl (δY (rightY aug ψ z)) * (z : EnvX aug ψ) := by
  change (⟨δY (rightY aug ψ z) * (z : EnvX aug ψ).left, (z : EnvX aug ψ).right⟩ : EnvX aug ψ) = _
  refine SemidirectProduct.ext ?_ ?_ <;> simp [mul_left]

@[simp] lemma coe_shift_inv (z : envY aug ψ PY) :
    ((shift aug ψ δY hδY)⁻¹ z : EnvX aug ψ) =
      inl (δY (rightY aug ψ z))⁻¹ * (z : EnvX aug ψ) := by
  change (⟨(δY (rightY aug ψ z))⁻¹ * (z : EnvX aug ψ).left, (z : EnvX aug ψ).right⟩ :
    EnvX aug ψ) = _
  refine SemidirectProduct.ext ?_ ?_ <;> simp [mul_left]

/-- The shift is the identity on the quotient `Π_Y[μ] ↠ Π_Y`. -/
@[simp] lemma shift_right (z : envY aug ψ PY) :
    (shift aug ψ δY hδY z : EnvX aug ψ).right = (z : EnvX aug ψ).right := rfl

lemma map_one_of_isCocycle {P : Type*} [Group P] {φ : P →* MulAut μ} {δ : P → μ}
    (hδ : IsCocycle φ δ) : δ 1 = 1 := by
  have := hδ 1 1
  simp only [mul_one, map_one, MulAut.one_apply] at this
  exact left_eq_mul.1 this

/-- The shift is the identity on the kernel `μ`. -/
@[simp] lemma shift_inlY (m : μ) : shift aug ψ δY hδY (inlY aug ψ PY m) = inlY aug ψ PY m := by
  apply Subtype.ext
  rw [coe_shift]
  have : rightY aug ψ (inlY aug ψ PY m) = 1 := rfl
  rw [this, map_one_of_isCocycle hδY, map_one, one_mul]

variable {PYdd : Subgroup PX} (hle : PYdd ≤ PY)

/-- The restriction of a cocycle on `PY` to `PYdd`. -/
def resDD (δY : PY → μ) : PYdd → μ := fun g => δY ⟨g, hle g.2⟩

/-- **Conjugation by `α_δ` maps the theta section of `η` to that of `η·δ⁻¹`**, i.e.
`α_δ ∘ s^Θ = t^Θ` with `t^Θ − s^Θ = δ`. -/
theorem shift_thetaSection {η : PYdd → μ} (hη : IsCocycle (actDD aug ψ PYdd) η)
    (hη' : IsCocycle (actDD aug ψ PYdd) (fun g => η g * (resDD hle δY g)⁻¹)) (g : PYdd) :
    shift aug ψ δY hδY (thetaSection aug ψ hle hη g) = thetaSection aug ψ hle hη' g := by
  apply Subtype.ext
  refine SemidirectProduct.ext ?_ rfl
  simp only [shift, MulEquiv.coe_mk, Equiv.coe_fn_mk, coe_thetaSection, mul_inv, inv_inv,
    resDD, rightY]
  exact mul_comm _ _

include hδY in
lemma isCocycle_resDD : IsCocycle (actDD aug ψ PYdd) (resDD hle δY) :=
  fun g h => hδY ⟨g, hle g.2⟩ ⟨h, hle h.2⟩

include hδY in
lemma isCocycle_mul_inv_resDD {η : PYdd → μ} (hη : IsCocycle (actDD aug ψ PYdd) η) :
    IsCocycle (actDD aug ψ PYdd) (fun g => η g * (resDD hle δY g)⁻¹) := by
  intro g h
  have h1 := hη g h
  have h2 := isCocycle_resDD aug ψ hδY hle g h
  change η (g * h) * (resDD hle δY (g * h))⁻¹ =
    (η g * (resDD hle δY g)⁻¹) * actDD aug ψ PYdd g (η h * (resDD hle δY h)⁻¹)
  rw [h1, h2, map_mul, map_inv, mul_inv]
  simp only [mul_assoc, mul_left_comm]

/-- The shift maps datum (c) of `η` onto datum (c) of `η·δ⁻¹`. -/
theorem image_thetaSubgroups_shift {η : PYdd → μ} (hη : IsCocycle (actDD aug ψ PYdd) η) :
    Subgroup.map (shift aug ψ δY hδY).toMonoidHom '' thetaSubgroups aug ψ hle hη =
      thetaSubgroups aug ψ hle (isCocycle_mul_inv_resDD aug ψ hδY hle hη) := by
  refine image_thetaSubgroups aug ψ hle hη _ _ (Equiv.refl μ) (fun ζ => shift_inlY aug ψ hδY ζ) ?_
  ext z
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, (shift_thetaSection aug ψ hδY hle hη _ g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, ⟨g, rfl⟩, shift_thetaSection aug ψ hδY hle hη _ g⟩

end Shift

/-! ### The shift normalises `D_Y` -/

section Normalises

variable {PY : Subgroup PX} [PY.Normal] (Kum : Subgroup (G → μ))
  (hKum : ∀ κ ∈ Kum, IsCocycle ψ κ)
  {δY : PY → μ} (hδY : IsCocycle (actY aug ψ PY) δY)

/-- `a·h·a⁻¹ ∈ PY` for `h ∈ PY`. -/
def conjPY (a : PX) (h : PY) : PY := ⟨a * h * a⁻¹, Subgroup.Normal.conj_mem inferInstance _ h.2 a⟩

/-- **Layer-B hypothesis of [EtTh], Prop. 2.14(ii)**: the `PX`-conjugates of the extended
difference cocycle `δY` differ from `δY` by a Kummer cocycle and a coboundary ([EtTh]: an element
of `Gal(Y̲/X̲)` maps `Ü²` to a `K^×`-multiple of `Ü²`). -/
def ShiftConj (Kum : Subgroup (G → μ)) (δY : PY → μ) : Prop :=
  ∀ a : PX, ∃ κ ∈ Kum, ∃ ζ : μ, ∀ h : PY,
    δY (conjPY a h) * (ψ (aug a) (δY h))⁻¹ =
      κ (aug (a * h * a⁻¹)) * cob (ψ := ψ) ζ (aug (a * h * a⁻¹))

/-- Elements of `DX` act on `μ` through `ψ`. -/
lemma DX_apply_inl {β : MulAut (EnvX aug ψ)} (hβ : β ∈ DX aug ψ Kum hKum) :
    ∃ s : G, ∀ m : μ, β (inl m) = inl (ψ s m) := by
  obtain ⟨κ, hκ, x, rfl⟩ := hβ
  refine ⟨aug x.right, fun m => ?_⟩
  rw [MulAut.mul_apply, MulAut.conj_apply]
  have : x * inl m * x⁻¹ = inl (ψ (aug x.right) m) := by
    refine SemidirectProduct.ext ?_ ?_
    · simp [mul_left, inv_left, mul_comm]
    · simp
  rw [this, twist_inl]

include hδY in
/-- **The shift normalises `D_Y`** ([EtTh], Prop. 2.14(ii)), under `ShiftConj`. -/
theorem shift_conj_mem_DY (hconj : ShiftConj aug ψ Kum δY) {γ : MulAut (envY aug ψ PY)}
    (hγ : γ ∈ DY aug ψ Kum PY hKum) :
    shift aug ψ δY hδY * γ * (shift aug ψ δY hδY)⁻¹ ∈ DY aug ψ Kum PY hKum := by
  obtain ⟨β, hβ, hγβ⟩ := hγ
  obtain ⟨κ0, hκ0, x, hβx⟩ := id hβ
  obtain ⟨κ, hκ, ζ, hζ⟩ := hconj x.right
  have hβinl : ∀ m : μ, β (inl m) = inl (ψ (aug x.right) m) := by
    intro m
    rw [hβx, MulAut.mul_apply, MulAut.conj_apply]
    have : x * inl m * x⁻¹ = inl (ψ (aug x.right) m) := by
      refine SemidirectProduct.ext ?_ ?_
      · simp [mul_left, inv_left, mul_comm]
      · simp
    rw [this, twist_inl]
  have hβr : ∀ y : EnvX aug ψ, (β y).right = x.right * y.right * x.right⁻¹ := by
    intro y
    simp [hβx, MulAut.mul_apply, MulAut.conj_apply]
  have hcob : twist (aug := aug) (cob ζ) (isCocycle_cob ζ) ∈ DX aug ψ Kum hKum := by
    rw [twist_cob]
    exact conj_mem_DX aug ψ Kum hKum _
  refine ⟨twist κ (hKum κ hκ) * twist (cob ζ) (isCocycle_cob ζ) * β,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (twist_mem_DX aug ψ Kum hKum hκ) hcob) hβ,
    fun z => ?_⟩
  have hr : rightY aug ψ (γ ((shift aug ψ δY hδY)⁻¹ z)) = conjPY x.right (rightY aug ψ z) := by
    apply Subtype.ext
    change ((γ ((shift aug ψ δY hδY)⁻¹ z) : envY aug ψ PY) : EnvX aug ψ).right = _
    rw [hγβ, coe_shift_inv, map_mul, hβinl, mul_right, right_inl, one_mul, hβr]
    rfl
  have hz := hζ (rightY aug ψ z)
  have hcoe : ((rightY aug ψ z : PY) : PX) = (z : EnvX aug ψ).right := rfl
  rw [hcoe] at hz
  simp only [MulAut.mul_apply]
  rw [coe_shift, hr, hγβ, coe_shift_inv, map_mul, hβinl, ← mul_assoc, ← map_mul, map_inv, hz,
    twist_apply_eq, twist_apply_eq, mul_right, right_inl, one_mul, hβr, ← mul_assoc, ← map_mul]

lemma shiftConj_inv (hconj : ShiftConj aug ψ Kum δY) : ShiftConj aug ψ Kum δY⁻¹ := by
  intro a
  obtain ⟨κ, hκ, ζ, hζ⟩ := hconj a
  refine ⟨κ⁻¹, Kum.inv_mem hκ, ζ⁻¹, fun h => ?_⟩
  have e1 : δY⁻¹ (conjPY a h) * (ψ (aug a) (δY⁻¹ h))⁻¹ =
      (δY (conjPY a h) * (ψ (aug a) (δY h))⁻¹)⁻¹ := by
    simp only [Pi.inv_apply, map_inv, mul_inv, inv_inv]
  have e2 : κ⁻¹ (aug (a * h * a⁻¹)) * cob (ψ := ψ) ζ⁻¹ (aug (a * h * a⁻¹)) =
      (κ (aug (a * h * a⁻¹)) * cob (ψ := ψ) ζ (aug (a * h * a⁻¹)))⁻¹ := by
    simp only [Pi.inv_apply, cob, map_inv, mul_inv, inv_inv]
  rw [e1, hζ h, e2]

omit [PY.Normal] in
include hδY in
lemma isCocycle_inv_Y : IsCocycle (actY aug ψ PY) δY⁻¹ := by
  intro g h
  simp only [Pi.inv_apply, hδY g h, mul_inv, map_inv]

omit [PY.Normal] in
include hδY in
lemma shift_inv_eq : (shift aug ψ δY hδY)⁻¹ = shift aug ψ δY⁻¹ (isCocycle_inv_Y aug ψ hδY) := by
  refine MulEquiv.ext fun z => Subtype.ext ?_
  rw [coe_shift_inv, coe_shift]
  rfl

/-- `MonoThetaEnv.conjAut α` is conjugation by `α`. -/
lemma conjAut_eq' {H : Type*} [Group H] (α : H ≃* H) (β : MulAut H) :
    MonoThetaEnv.conjAut α β = α * β * α⁻¹ := by
  ext; rfl

include hδY in
/-- **Conjugation by the shift maps `D_Y` onto `D_Y`** ([EtTh], Prop. 2.14(ii)). -/
theorem map_conjAut_shift (hconj : ShiftConj aug ψ Kum δY) :
    (DY aug ψ Kum PY hKum).map (MonoThetaEnv.conjAut (shift aug ψ δY hδY)) =
      DY aug ψ Kum PY hKum := by
  ext γ
  simp only [Subgroup.mem_map, conjAut_eq']
  constructor
  · rintro ⟨γ', hγ', rfl⟩
    exact shift_conj_mem_DY aug ψ Kum hKum hδY hconj hγ'
  · intro hγ
    refine ⟨(shift aug ψ δY hδY)⁻¹ * γ * shift aug ψ δY hδY, ?_, by simp [mul_assoc]⟩
    have := shift_conj_mem_DY aug ψ Kum hKum (isCocycle_inv_Y aug ψ hδY)
      (shiftConj_inv aug ψ Kum hconj) hγ
    rw [← shift_inv_eq, inv_inv] at this
    exact this

end Normalises

/-! ### The shift as an isomorphism of model environments -/

section Iso

variable [TopologicalSpace PX] [IsTopologicalGroup PX] [TopologicalSpace μ] [DiscreteTopology μ]
  (Kum : Subgroup (G → μ)) {PY PYdd : Subgroup PX} [PY.Normal] (hle : PYdd ≤ PY)
  (hψ : IsOpen ((act aug ψ).ker : Set PX)) (hKum : ∀ κ ∈ Kum, IsCocycle ψ κ)
  {δY : PY → μ} (hδY : IsCocycle (actY aug ψ PY) δY)

open scoped Envelope

omit [IsTopologicalGroup PX] [DiscreteTopology μ] [PY.Normal] in
lemma continuous_rightY : Continuous (rightY aug ψ (PY := PY)) :=
  (Envelope.continuous_right.comp continuous_subtype_val).subtype_mk _

omit [IsTopologicalGroup PX] [PY.Normal] in
/-- The shift as an automorphism of topological groups, for a continuous `δY`. -/
def shiftT (hδc : Continuous δY) : envY aug ψ PY ≃ₜ* envY aug ψ PY where
  toMulEquiv := shift aug ψ δY hδY
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Envelope.continuous_mk ?_ (Envelope.continuous_right.comp continuous_subtype_val)
    exact (continuous_of_discreteTopology (f := fun q : μ × μ => q.1 * q.2)).comp
      ((hδc.comp (continuous_rightY aug ψ)).prodMk
        (Envelope.continuous_left.comp continuous_subtype_val))
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine Envelope.continuous_mk ?_ (Envelope.continuous_right.comp continuous_subtype_val)
    exact (continuous_of_discreteTopology (f := fun q : μ × μ => q.1⁻¹ * q.2)).comp
      ((hδc.comp (continuous_rightY aug ψ)).prodMk
        (Envelope.continuous_left.comp continuous_subtype_val))

/-- **[EtTh], Proposition 2.14(ii)**: for a continuous cocycle `δY` on `PY` satisfying the
Layer-B hypothesis `ShiftConj`, the shifting automorphism `α_δ` is an isomorphism of model
mono-theta environments from the environment of `η` to the environment of `η·δ⁻¹`
(`δ = δY|_{PYdd}`; i.e. it maps `s^Θ` to `t^Θ = s^Θ + δ` and preserves `D_Y`). -/
def shiftIso (hδc : Continuous δY) (hconj : ShiftConj aug ψ Kum δY) {η : PYdd → μ}
    (hη : IsCocycle (actDD aug ψ PYdd) η) :
    MonoThetaEnv.Iso (modelEnv aug ψ Kum hle hψ hKum hη)
      (modelEnv aug ψ Kum hle hψ hKum (isCocycle_mul_inv_resDD aug ψ hδY hle hη)) where
  e := shiftT aug ψ hδY hδc
  map_D := map_conjAut_shift aug ψ Kum hKum hδY hconj
  map_theta := image_thetaSubgroups_shift aug ψ hδY hle hη

lemma shiftIso_e (hδc : Continuous δY) (hconj : ShiftConj aug ψ Kum δY) {η : PYdd → μ}
    (hη : IsCocycle (actDD aug ψ PYdd) η) :
    (shiftIso aug ψ Kum hle hψ hKum hδY hδc hconj hη).e = shiftT aug ψ hδY hδc := rfl

omit [IsTopologicalGroup PX] [PY.Normal] in
/-- The shifting isomorphism lies over the identity of `Π_Y` and is the identity on `μ`
([EtTh], Cor. 2.18(ii): uniqueness up to isomorphisms over the identity of `Π_Y̲`). -/
theorem shiftT_right (hδc : Continuous δY) (z : envY aug ψ PY) :
    (shiftT aug ψ hδY hδc z : EnvX aug ψ).right = (z : EnvX aug ψ).right := rfl

theorem shiftIso_inlY (hδc : Continuous δY) (hconj : ShiftConj aug ψ Kum δY) {η : PYdd → μ}
    (hη : IsCocycle (actDD aug ψ PYdd) η) (m : μ) :
    (shiftIso aug ψ Kum hle hψ hKum hδY hδc hconj hη).e (inlY aug ψ PY m) = inlY aug ψ PY m :=
  shift_inlY aug ψ hδY m

end Iso

end Iut.EtaleTheta.Env
