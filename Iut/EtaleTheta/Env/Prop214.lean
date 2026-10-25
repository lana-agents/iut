/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Env.Model
import Iut.EtaleTheta.ArithEnv
import Iut.Frobenioid.PAdicSlim

/-!
# The algebraic splitting: [EtTh], Proposition 2.14(i)

[EtTh], Prop. 2.14(i): inside the cyclotomic envelope of the theta quotient, the elements
`γ(β)·β⁻¹`, for `β` geometric and `γ ∈ Aut(Π_Y̲[μ_N])` whose class lies in `D_Y̲` and which induces
the identity on `Π_Y̲[μ_N] ↠ G_K`, lie in the image of the **tautological section**. Mochizuki's
proof: the automorphisms arising from `K^×` are trivial on the geometric part, and since `G_K` is
center-free ([Mzk2], Thm 1.1.1(ii)) the conjugating element is geometric; the resulting
commutators are then tautological.

Here this is proved for the abstract theta setting of `Env/Model.lean`, before passing to the
theta quotient, as an exact description (`prop214Set_eq`): if `G` is center-free and `PY` maps
onto `G`, the set of [EtTh], Prop. 2.14(i) is exactly the tautological image of the commutators
`[a, b]`, `a ∈ Δ_X = Ker(PX ↠ G)`, `b ∈ Δ_Y = PY ∩ Δ_X`. Projected to the theta quotient these
commutators are `l·Δ_Θ` by Prop. 2.12(i) (`ThetaGroup.commutator_eq_theta` for the model,
`ThetaQuotient.commutator_eq_zpowers` in general).

The center-freeness hypothesis is **discharged for `G = G_K`**, `K` a finite extension of `ℚ_p`:
`G_K` is slim (`PAdicGalois.isSlimGroup`, via local class field theory), hence center-free
(`IsSlimGroup.center_free`). This gives `prop214Set_eq_padic`, and for the arithmetic model of
`ArithEnv.lean` the unconditional `prop214_padic`, `prop214_inter_padic` (the hypothesis `hG`
of `prop214` is gone).
-/

namespace Iut.EtaleTheta

/-- A slim group is center-free. -/
theorem _root_.Iut.Frobenioid.IsSlimGroup.center_free {G : Type*} [Group G] [TopologicalSpace G]
    (h : Iut.Frobenioid.IsSlimGroup G) (τ : G) (hτ : ∀ σ, τ * σ = σ * τ) : τ = 1 :=
  h ⊤ isOpen_univ τ fun x _ => hτ x

/-- **`G_K` is center-free** for every finite extension `K/ℚ_p` ([Mzk2], Thm 1.1.1(ii); here from
the slimness of `G_K`, `PAdicGalois.isSlimGroup`). -/
theorem gK_center_free {p : ℕ} [Fact p.Prime]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    (τ : Iut.Frobenioid.PAdicGalois.GK p E)
    (hτ : ∀ σ, τ * σ = σ * τ) : τ = 1 :=
  Iut.Frobenioid.PAdicGalois.isSlimGroup.center_free τ hτ

/-- **[EtTh], Prop. 2.14(i)** in the arithmetic model, for `G = G_K` (`K/ℚ_p` finite), without
hypotheses. -/
theorem prop214_padic {p : ℕ} [Fact p.Prime]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    (M : Type) [AddCommGroup M] (l : ℤ) (μ : Type) [AddCommGroup μ]
    (χ : Iut.Frobenioid.PAdicGalois.GK p E →* ℤˣ) :
    prop214Set (M := M) (μ := μ) (χ := χ) l = Set.range (tautArith l) :=
  prop214 l gK_center_free

/-- **[EtTh], Prop. 2.14(i)**, in the form of the statement, for `G = G_K`. -/
theorem prop214_inter_padic {p : ℕ} [Fact p.Prime]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    (M : Type) [AddCommGroup M] (l : ℤ) (μ : Type) [AddCommGroup μ]
    (χ : Iut.Frobenioid.PAdicGalois.GK p E →* ℤˣ) :
    lArith (M := M) (μ := μ) (χ := χ) l ∩ prop214Set l = Set.range (tautArith l) :=
  prop214_inter l gK_center_free

namespace Env

open SemidirectProduct
open scoped commutatorElement

universe u

variable {PX G μ : Type u} [Group PX] [Group G] [CommGroup μ] (aug : PX →* G)
  (ψ : G →* MulAut μ) (Kum : Subgroup (G → μ)) (hKum : ∀ κ ∈ Kum, IsCocycle ψ κ)
  (PY : Subgroup PX)

/-- **The set of [EtTh], Prop. 2.14(i)**: the `γ(β)·β⁻¹` for `β ∈ Δ_Y[μ]` (geometric) and
`γ ∈ D_Y` inducing the identity on `Π_Y[μ] ↠ G`. -/
def prop214Set : Set (envY aug ψ PY) :=
  {w | ∃ γ ∈ DY aug ψ Kum PY hKum,
    (∀ z : envY aug ψ PY, aug ((γ z : envY aug ψ PY) : EnvX aug ψ).right =
      aug (z : EnvX aug ψ).right) ∧
    ∃ β : envY aug ψ PY, aug (β : EnvX aug ψ).right = 1 ∧ w = γ β * β⁻¹}

/-- The tautological images `s^alg([a, b])` of the commutators `a ∈ Δ_X`, `b ∈ Δ_Y`. -/
def geomCommutators : Set (envY aug ψ PY) :=
  {w | ∃ a b : PX, aug a = 1 ∧ b ∈ PY ∧ aug b = 1 ∧ (w : EnvX aug ψ) = inr ⁅a, b⁆}

/-- In `Π_X[μ]`, the commutator of two geometric elements is tautological. -/
lemma geom_commutator (x y : EnvX aug ψ) (hx : aug x.right = 1) (hy : aug y.right = 1) :
    x * y * x⁻¹ * y⁻¹ = inr ⁅x.right, y.right⁆ := by
  refine SemidirectProduct.ext ?_ ?_
  · simp only [mul_left, inv_left, mul_right, inv_right, left_inr, MonoidHom.coe_comp,
      Function.comp_apply, map_mul, map_inv, hx, hy, inv_one, mul_one, map_one, MulAut.one_apply]
    rw [mul_comm x.left y.left, mul_inv_cancel_right, mul_inv_cancel]
  · simp [commutatorElement_def]

/-- **[EtTh], Proposition 2.14(i)** for the abstract theta setting: if `G` is center-free and
`PY ↠ G` is surjective, the set of `γ(β)·β⁻¹` (`β` geometric, `γ ∈ D_Y` inducing the identity on
`G`) is exactly the tautological image of the commutators `[a, b]`, `a ∈ Δ_X`, `b ∈ Δ_Y`. In
particular every such element lies in the image of the tautological section. -/
theorem prop214Set_eq [PY.Normal] (hG : ∀ τ : G, (∀ σ, τ * σ = σ * τ) → τ = 1)
    (hsurj : ∀ σ : G, ∃ h ∈ PY, aug h = σ) :
    prop214Set aug ψ Kum hKum PY = geomCommutators aug ψ PY := by
  ext w
  constructor
  · rintro ⟨γ, ⟨β0, ⟨κ, hκ, x, rfl⟩, hγβ⟩, hid, β, hβ, rfl⟩
    -- the conjugating element is geometric
    have hx : aug x.right = 1 := by
      refine hG _ fun σ => ?_
      obtain ⟨h, hh, rfl⟩ := hsurj σ
      have := hid (salg aug ψ PY ⟨h, hh⟩)
      rw [hγβ] at this
      simp only [coe_salg, MulAut.mul_apply, twist_right, MulAut.conj_apply, mul_right,
        right_inr, inv_right, map_mul, map_inv] at this
      calc aug x.right * aug h = aug x.right * aug h * (aug x.right)⁻¹ * aug x.right := by
            rw [inv_mul_cancel_right]
        _ = aug h * aug x.right := by rw [this]
    refine ⟨x.right, (β : EnvX aug ψ).right, hx, β.2, hβ, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hγβ, MulAut.mul_apply, MulAut.conj_apply,
      twist_apply_eq]
    have hr : aug (x * (β : EnvX aug ψ) * x⁻¹).right = 1 := by
      simp [hx, hβ]
    have h1 : κ 1 = 1 := by
      have := hKum κ hκ 1 1
      simp only [mul_one, map_one, MulAut.one_apply] at this
      exact left_eq_mul.1 this
    rw [hr, h1, map_one, one_mul]
    exact geom_commutator aug ψ x β hx hβ
  · rintro ⟨a, b, ha, hb, hb1, hw⟩
    refine ⟨restrictAut aug ψ PY (MulAut.conj (inr a)) (conj_mem_envY_iff aug ψ PY _),
      restrictAut_mem_DY aug ψ Kum PY hKum _ _ (conj_mem_DX aug ψ Kum hKum _), fun z => ?_,
      salg aug ψ PY ⟨b, hb⟩, hb1, ?_⟩
    · simp [MulAut.conj_apply, ha]
    · apply Subtype.ext
      rw [hw, Subgroup.coe_mul, Subgroup.coe_inv, coe_restrictAut, coe_salg, MulAut.conj_apply,
        commutatorElement_def]
      simp only [map_mul, map_inv, mul_assoc]

/-- **[EtTh], Proposition 2.14(i)** for the abstract theta setting over `G = G_K`, `K/ℚ_p`
finite: the center-freeness of `G_K` is proved (`gK_center_free`). -/
theorem prop214Set_eq_padic {p : ℕ} [Fact p.Prime]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    {PX μ : Type} [Group PX] [CommGroup μ] (aug : PX →* Iut.Frobenioid.PAdicGalois.GK p E)
    (ψ : Iut.Frobenioid.PAdicGalois.GK p E →* MulAut μ)
    (Kum : Subgroup (Iut.Frobenioid.PAdicGalois.GK p E → μ)) (hKum : ∀ κ ∈ Kum, IsCocycle ψ κ)
    (PY : Subgroup PX) [PY.Normal]
    (hsurj : ∀ σ, ∃ h ∈ PY, aug h = σ) :
    prop214Set aug ψ Kum hKum PY = geomCommutators aug ψ PY :=
  prop214Set_eq aug ψ Kum hKum PY gK_center_free hsurj

/-- Every element of the set of [EtTh], Prop. 2.14(i) lies in the image of the tautological
section (its `μ`-component is trivial). -/
theorem prop214Set_subset_salg [PY.Normal] (hG : ∀ τ : G, (∀ σ, τ * σ = σ * τ) → τ = 1)
    (hsurj : ∀ σ : G, ∃ h ∈ PY, aug h = σ) {w : envY aug ψ PY}
    (hw : w ∈ prop214Set aug ψ Kum hKum PY) : w ∈ Set.range (salg aug ψ PY) := by
  rw [prop214Set_eq aug ψ Kum hKum PY hG hsurj] at hw
  obtain ⟨a, b, -, hb, -, hw⟩ := hw
  have hmem : ⁅a, b⁆ ∈ PY := by
    rw [commutatorElement_def]
    exact PY.mul_mem (Subgroup.Normal.conj_mem inferInstance _ hb a) (PY.inv_mem hb)
  exact ⟨⟨_, hmem⟩, Subtype.ext hw.symm⟩

end Env

end Iut.EtaleTheta
