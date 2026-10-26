/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Env.Model

/-!
# Recovering `Π_X̲` from a mono-theta environment ([EtTh], Corollary 2.18(iii))

[EtTh], Cor. 2.18(iii): from a mono-theta environment `M = (Π, D, s^Θ)` one recovers the quotient
`Π ↠ Π_Y̲` (its kernel `μ_N` is group-theoretic, Prop. 2.11(ii)) and then

`Π_X̲ = Aut(Π_Y̲) ×_{Out(Π_Y̲)} Im(D)`,

the automorphisms of `Π_Y̲` whose outer class is induced by `D`. Since `D` contains the inner
automorphisms of `Π`, which induce all inner automorphisms of `Π_Y̲`, this is the group of
automorphisms of `Π_Y̲ = Π/μ` induced by the elements of `D` (`piX`).

* `piX M N hN`: for a normal subgroup `N` of `M.G` preserved by `D` (in [EtTh]: `N = μ_N`), the
  group of automorphisms of `M.G ⧸ N` induced by `D`; `piXMap`: an isomorphism of environments
  mapping `N` onto `N'` induces an isomorphism `piX M ≃* piX M'` (functoriality).
* For the model environment of the abstract theta setting (`Env/Model.lean`) with `N` the kernel
  of `Π_Y[μ] ↠ Π_Y`: `piXModelEquiv`: **`PX ≃* piX (modelEnv …)`** provided `PY` has trivial
  centralizer in `PX` (temp-slimness of `Π_X̲` in [EtTh]; a Layer-B obligation): `a ∈ PX` acts
  on `Π_Y = Π_Y[μ]/μ` by conjugation, Kummer twists act trivially on `Π_Y`.
-/

namespace Iut.EtaleTheta.Env

open SemidirectProduct

universe u

/-! ### The abstract construction -/

section Abstract

variable (M : MonoThetaEnv.{u}) (N : Subgroup M.G) [N.Normal]
  (hN : ∀ γ ∈ M.D, N.map (γ : M.G →* M.G) = N)

/-- The automorphism of `M.G ⧸ N` induced by `γ ∈ D`. -/
def barAut {γ : MulAut M.G} (hγ : γ ∈ M.D) : MulAut (M.G ⧸ N) :=
  QuotientGroup.congr N N γ (hN γ hγ)

lemma barAut_mk {γ : MulAut M.G} (hγ : γ ∈ M.D) (x : M.G) :
    barAut M N hN hγ (x : M.G ⧸ N) = ((γ x : M.G) : M.G ⧸ N) :=
  QuotientGroup.congr_mk _ _ _ _ x

/-- **[EtTh], Cor. 2.18(iii)**: `Π_X(M) = Aut(Π_Y) ×_{Out(Π_Y)} Im(D)`, the automorphisms of
`Π_Y = M.G ⧸ N` induced by `D`. -/
def piX : Subgroup (MulAut (M.G ⧸ N)) where
  carrier := {α | ∃ γ, ∃ hγ : γ ∈ M.D, α = barAut M N hN hγ}
  one_mem' := ⟨1, M.D.one_mem, MulEquiv.ext fun x => by
    induction x using QuotientGroup.induction_on with
    | H x => rw [barAut_mk]; rfl⟩
  mul_mem' := by
    rintro _ _ ⟨γ, hγ, rfl⟩ ⟨γ', hγ', rfl⟩
    refine ⟨γ * γ', M.D.mul_mem hγ hγ', MulEquiv.ext fun x => ?_⟩
    induction x using QuotientGroup.induction_on with
    | H x => rw [MulAut.mul_apply, barAut_mk, barAut_mk, barAut_mk]; rfl
  inv_mem' := by
    rintro _ ⟨γ, hγ, rfl⟩
    refine ⟨γ⁻¹, M.D.inv_mem hγ, MulEquiv.ext fun x => ?_⟩
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, barAut_mk, barAut_mk, MulAut.inv_apply,
        MulEquiv.apply_symm_apply]

variable {M N hN} {M' : MonoThetaEnv.{u}} {N' : Subgroup M'.G} [N'.Normal]
  {hN' : ∀ γ ∈ M'.D, N'.map (γ : M'.G →* M'.G) = N'}

/-- An isomorphism of environments mapping `N` onto `N'` induces `M.G ⧸ N ≃* M'.G ⧸ N'`. -/
def quotMap (f : MonoThetaEnv.Iso M M') (hf : N.map f.e.toMulEquiv.toMonoidHom = N') :
    M.G ⧸ N ≃* M'.G ⧸ N' :=
  QuotientGroup.congr N N' f.e.toMulEquiv hf

/-- **Functoriality of `Π_X`** ([EtTh], Cor. 2.18(iii)): conjugation by the induced isomorphism
of quotients maps `Π_X(M)` onto `Π_X(M')`. -/
theorem piX_map (f : MonoThetaEnv.Iso M M') (hf : N.map f.e.toMulEquiv.toMonoidHom = N') :
    (piX M N hN).map (MonoThetaEnv.conjAut (quotMap f hf)) = piX M' N' hN' := by
  have key : ∀ γ (hγ : γ ∈ M.D) (hγ' : MonoThetaEnv.conjAut f.e.toMulEquiv γ ∈ M'.D),
      MonoThetaEnv.conjAut (quotMap f hf) (barAut M N hN hγ) = barAut M' N' hN' hγ' := by
    intro γ hγ hγ'
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H x =>
      change quotMap f hf (barAut M N hN hγ ((quotMap f hf).symm x)) = _
      have hs : (quotMap f hf).symm (x : M'.G ⧸ N') = ((f.e.symm x : M.G) : M.G ⧸ N) := by
        rw [MulEquiv.symm_apply_eq, quotMap, QuotientGroup.congr_mk]
        congr 1
        exact (f.e.apply_symm_apply x).symm
      rw [hs, barAut_mk, quotMap, QuotientGroup.congr_mk, barAut_mk]
      rfl
  ext α
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    have hγ' : MonoThetaEnv.conjAut f.e.toMulEquiv γ ∈ M'.D := by
      rw [← f.map_D]; exact ⟨γ, hγ, rfl⟩
    exact ⟨_, hγ', key γ hγ hγ'⟩
  · rintro ⟨γ', hγ', rfl⟩
    have hmem : γ' ∈ M.D.map (MonoThetaEnv.conjAut f.e.toMulEquiv) := by rw [f.map_D]; exact hγ'
    obtain ⟨γ, hγ, rfl⟩ := hmem
    exact ⟨_, ⟨γ, hγ, rfl⟩, key γ hγ hγ'⟩

end Abstract

/-! ### The model: `Π_X(modelEnv) ≅ PX` -/

section Model

variable {PX G μ : Type u} [Group PX] [Group G] [CommGroup μ] (aug : PX →* G)
  (ψ : G →* MulAut μ) (PY : Subgroup PX)

/-- The projection `Π_Y[μ] ↠ Π_Y`. -/
def rightPY : envY aug ψ PY →* PY where
  toFun z := ⟨(z : EnvX aug ψ).right, z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma coe_rightPY (z : envY aug ψ PY) :
    (rightPY aug ψ PY z : PX) = (z : EnvX aug ψ).right := rfl

/-- The kernel `μ` of `Π_Y[μ] ↠ Π_Y`. -/
abbrev muY : Subgroup (envY aug ψ PY) := (rightPY aug ψ PY).ker

instance muY_normal : (muY aug ψ PY).Normal := MonoidHom.normal_ker _

lemma muY_eq_range : muY aug ψ PY = (inlY aug ψ PY).range := by
  ext z
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro h
    refine ⟨(z : EnvX aug ψ).left, Subtype.ext (SemidirectProduct.ext rfl ?_)⟩
    exact (congrArg Subtype.val h).symm
  · rintro ⟨m, rfl⟩
    rfl

variable (Kum : Subgroup (G → μ)) (hKum : ∀ κ ∈ Kum, IsCocycle ψ κ)

/-- Every `γ ∈ D_Y` acts on `Π_Y` as conjugation by some `a ∈ PX`. -/
lemma DY_right {γ : MulAut (envY aug ψ PY)} (hγ : γ ∈ DY aug ψ Kum PY hKum) :
    ∃ a : PX, ∀ z, ((γ z : envY aug ψ PY) : EnvX aug ψ).right =
      a * (z : EnvX aug ψ).right * a⁻¹ := by
  obtain ⟨β, ⟨κ, hκ, x, rfl⟩, hγβ⟩ := hγ
  exact ⟨x.right, fun z => by rw [hγβ]; simp [MulAut.mul_apply, MulAut.conj_apply]⟩

lemma DY_map_muY {γ : MulAut (envY aug ψ PY)} (hγ : γ ∈ DY aug ψ Kum PY hKum) :
    (muY aug ψ PY).map (γ : envY aug ψ PY →* envY aug ψ PY) = muY aug ψ PY := by
  obtain ⟨a, ha⟩ := DY_right aug ψ PY Kum hKum hγ
  have key : ∀ z, γ z ∈ muY aug ψ PY ↔ z ∈ muY aug ψ PY := by
    intro z
    simp only [MonoidHom.mem_ker]
    rw [← Subtype.coe_inj, ← Subtype.coe_inj, coe_rightPY, coe_rightPY, ha]
    constructor
    · intro h
      have : (z : EnvX aug ψ).right = a⁻¹ * (a * (z : EnvX aug ψ).right * a⁻¹) * a := by
        simp [mul_assoc]
      rw [this, h]; simp
    · intro h
      rw [h]; simp
  ext z
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (key y).2 hy
  · intro hz
    exact ⟨γ.symm z, (key _).1 (by simpa using hz), by simp⟩

/-- `Π_Y[μ]/μ ≅ Π_Y`. -/
noncomputable def quotPY : envY aug ψ PY ⧸ muY aug ψ PY ≃* PY :=
  QuotientGroup.quotientKerEquivOfSurjective _ fun h =>
    ⟨salg aug ψ PY h, Subtype.ext rfl⟩

@[simp] lemma quotPY_mk (z : envY aug ψ PY) :
    quotPY aug ψ PY (z : envY aug ψ PY ⧸ muY aug ψ PY) = rightPY aug ψ PY z := rfl

lemma bar_eq_iff {α β : MulAut (envY aug ψ PY ⧸ muY aug ψ PY)} :
    α = β ↔ ∀ z : envY aug ψ PY,
      quotPY aug ψ PY (α (z : envY aug ψ PY ⧸ muY aug ψ PY)) =
        quotPY aug ψ PY (β (z : envY aug ψ PY ⧸ muY aug ψ PY)) := by
  constructor
  · rintro rfl _; rfl
  · intro h
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H z => exact (quotPY aug ψ PY).injective (h z)

/-- Conjugation by `inr a` restricted to `Π_Y[μ]`. -/
def conjY [PY.Normal] (a : PX) : MulAut (envY aug ψ PY) :=
  restrictAut aug ψ PY (MulAut.conj (inr a)) (conj_mem_envY_iff aug ψ PY _)

lemma conjY_mem [PY.Normal] (a : PX) : conjY aug ψ PY a ∈ DY aug ψ Kum PY hKum :=
  restrictAut_mem_DY aug ψ Kum PY hKum _ _ (conj_mem_DX aug ψ Kum hKum _)

@[simp] lemma coe_conjY_right [PY.Normal] (a : PX) (z : envY aug ψ PY) :
    ((conjY aug ψ PY a z : envY aug ψ PY) : EnvX aug ψ).right =
      a * (z : EnvX aug ψ).right * a⁻¹ := by
  simp [conjY, MulAut.conj_apply]

variable [TopologicalSpace PX] [IsTopologicalGroup PX] [TopologicalSpace μ] [DiscreteTopology μ]
  {PYdd : Subgroup PX} (hle : PYdd ≤ PY) (hψ : IsOpen ((act aug ψ).ker : Set PX))
  {η : PYdd → μ} (hη : IsCocycle (actDD aug ψ PYdd) η)

/-- `Π_X` of the model environment. -/
abbrev piXModel : Subgroup (MulAut (envY aug ψ PY ⧸ muY aug ψ PY)) :=
  @piX (modelEnv aug ψ Kum hle hψ hKum hη) (muY aug ψ PY) (muY_normal aug ψ PY)
    (fun _ hγ => DY_map_muY aug ψ PY Kum hKum hγ)

variable [PY.Normal]

/-- The map `PX → Π_X(model)`: `a` acts on `Π_Y` by conjugation. -/
def toPiX (a : PX) : piXModel aug ψ PY Kum hKum hle hψ hη :=
  ⟨@barAut (modelEnv aug ψ Kum hle hψ hKum hη) (muY aug ψ PY) (muY_normal aug ψ PY)
    (fun _ hγ => DY_map_muY aug ψ PY Kum hKum hγ) _ (conjY_mem aug ψ PY Kum hKum a),
    _, conjY_mem aug ψ PY Kum hKum a, rfl⟩

lemma toPiX_mk (a : PX) (z : envY aug ψ PY) :
    (toPiX aug ψ PY Kum hKum hle hψ hη a : MulAut _) (z : envY aug ψ PY ⧸ muY aug ψ PY) =
      ((conjY aug ψ PY a z : envY aug ψ PY) : envY aug ψ PY ⧸ muY aug ψ PY) :=
  rfl

/-- `a ↦ (conjugation by a on Π_Y)` as a homomorphism `PX →* Π_X(model)`. -/
def toPiXHom : PX →* piXModel aug ψ PY Kum hKum hle hψ hη where
  toFun := toPiX aug ψ PY Kum hKum hle hψ hη
  map_one' := by
    apply Subtype.ext
    rw [bar_eq_iff]
    intro z
    apply Subtype.ext
    simp [toPiX_mk]
  map_mul' a b := by
    apply Subtype.ext
    rw [bar_eq_iff]
    intro z
    apply Subtype.ext
    simp only [Subgroup.coe_mul, MulAut.mul_apply, toPiX_mk, quotPY_mk, coe_rightPY,
      coe_conjY_right, mul_inv_rev, mul_assoc]

/-- **[EtTh], Cor. 2.18(iii) for the model**: if `PY` has trivial centralizer in `PX`
(a consequence of temp-slimness; Layer-B obligation `hcent`), then
`PX ≃* Aut(Π_Y) ×_{Out(Π_Y)} Im(D_Y)`, `a ↦ (conjugation by a on Π_Y)`. -/
noncomputable def piXModelEquiv (hcent : ∀ a : PX, (∀ h ∈ PY, a * h = h * a) → a = 1) :
    PX ≃* piXModel aug ψ PY Kum hKum hle hψ hη := by
  refine MulEquiv.ofBijective (toPiXHom aug ψ PY Kum hKum hle hψ hη) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro a ha
    refine hcent a fun h hh => ?_
    have := congrArg (fun α : piXModel aug ψ PY Kum hKum hle hψ hη =>
      (quotPY aug ψ PY ((α : MulAut _) ((salg aug ψ PY ⟨h, hh⟩ : envY aug ψ PY) :
        envY aug ψ PY ⧸ muY aug ψ PY)) : PX)) ha
    simp only [toPiXHom, MonoidHom.coe_mk, OneHom.coe_mk, toPiX_mk, quotPY_mk, coe_rightPY,
      coe_conjY_right, coe_salg, right_inr, OneMemClass.coe_one, MulAut.one_apply] at this
    calc a * h = a * h * a⁻¹ * a := by rw [inv_mul_cancel_right]
      _ = h * a := by rw [this]
  · rintro ⟨α, γ, hγ, rfl⟩
    obtain ⟨a, ha⟩ := DY_right aug ψ PY Kum hKum hγ
    refine ⟨a, Subtype.ext ?_⟩
    rw [bar_eq_iff]
    intro z
    apply Subtype.ext
    simp only [toPiXHom, MonoidHom.coe_mk, OneHom.coe_mk, toPiX_mk, quotPY_mk, coe_rightPY,
      coe_conjY_right]
    change a * (z : EnvX aug ψ).right * a⁻¹ =
      ((quotPY aug ψ PY (QuotientGroup.mk (s := muY aug ψ PY) (γ z))) : PX)
    rw [quotPY_mk, coe_rightPY]
    exact (ha z).symm

/-- Under `piXModelEquiv`, `a` acts on `Π_Y` by conjugation. -/
theorem piXModelEquiv_apply (hcent : ∀ a : PX, (∀ h ∈ PY, a * h = h * a) → a = 1) (a : PX)
    (z : envY aug ψ PY) :
    (quotPY aug ψ PY (((piXModelEquiv aug ψ PY Kum hKum hle hψ hη hcent a :
      piXModel aug ψ PY Kum hKum hle hψ hη) : MulAut _) (z : envY aug ψ PY ⧸ muY aug ψ PY)) :
        PX) = a * (z : EnvX aug ψ).right * a⁻¹ := by
  simp [piXModelEquiv, toPiXHom, toPiX_mk]

end Model

end Iut.EtaleTheta.Env
