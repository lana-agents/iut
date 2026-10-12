/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.CyclotomicRigidity
import ContinuousKummerTheory.ContH1.Basic

/-!
# The model étale theta class in `H¹` ([EtTh], Prop. 1.3, 1.5(iii); step 2, milestone (11))

On the discrete model `(Π^tp_Ÿ)^Θ = Δ_Θ × 2·(Δ_Y)^ell` of the geometric theta quotient of
`Π^tp_Ÿ` (coordinates `(c, a')`, `a = 2a'`), acting trivially on the cyclotome `μ` (the
geometric part of the action), the **model étale theta class** is the class

`η(c, a') = red c + ρ a'`

of the continuous cocycle `ηCocycle` in `ContH1` (`thetaClass`): `red : Δ_Θ → μ` is the natural
reduction `Δ_Θ ⊗ ℤ/N ≅ μ_N` (the restriction of the étale theta class to `Δ_Θ`, [EtTh], Prop.
1.3) and `ρ` the Kummer class of `Ü` on `(Δ_Ÿ)^ell`.

## Results

* `thetaSection_eq`: **the theta section of the model environment is the tautological section
  minus the theta class**, `s^Θ = s^taut − η` (`CyclotomicRigidity.thetaSection`); this is the
  defining relation of [EtTh], Def. 2.13(ii) / Prop. 1.4.
* `thetaClass_eq_one_iff`: for the trivial action `H¹ = Hom`, and the class is trivial iff
  `red = 0` and `ρ = 0`; `thetaClass_ne_one`: it is nontrivial as soon as `red ≠ 0`.
* `thetaClass_restrict`: the restriction of the class to `Δ_Θ` is `red`, and
  `model_isCyc_eq_neg_thetaClass`: the isomorphism of cyclotomes reconstructed by the
  cyclotomic rigidity algorithm (`model_isCyc`) is minus the restriction of the theta class to
  `l·Δ_Θ`.
* **The `Gal(Y/X)`-conjugates** (the geometric shadow of [EtTh], Prop. 1.5(iii)):
  `conj_sub_thetaCocycle`: pulling the class back along the conjugation `γ_k` by the `k`-th power
  of the generator (`(c, a') ↦ (c + 2kl·a', a')`) changes it by `2kl·red(a')`, i.e. by the
  `2kl`-th multiple of the class of `(Δ_Ÿ)^ell → μ`, `a' ↦ red a'`; `gammaK_thetaSection`: this
  conjugation is `γ_k` of the model environment on the image of the theta section.

The genuine class `η^Θ ∈ H¹(Π^tp_Ÿ, Δ_Θ)` on the tempered group remains research-level
(`README.md`, scope decision S2').
-/

namespace Iut.EtaleTheta

open ContH1

universe u

variable {M : Type u} [AddCommGroup M] {μ : Type u} [AddCommGroup μ]

section Action

variable (G A : Type*) [Monoid G] [Monoid A]

/-- The trivial action of `G` on `A` (the geometric part `(Δ_Ÿ)^Θ` acts trivially on `μ`). -/
abbrev trivialMulDistribMulAction : MulDistribMulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

end Action

section Model

variable [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace μ] [IsTopologicalAddGroup μ]

/-- `(Π^tp_Ÿ)^Θ` in the model: `Δ_Θ × 2·(Δ_Y)^ell`, coordinates `(c, a')`, written
multiplicatively. -/
abbrev PiYddot (M : Type u) [AddCommGroup M] : Type u := Multiplicative (M × M)

attribute [local instance] trivialMulDistribMulAction

/-- The model theta cocycle `(c, a') ↦ red c + ρ a'`. -/
def thetaFun (red ρ : M →+ μ) (x : PiYddot M) : Multiplicative μ :=
  Multiplicative.ofAdd (red (Multiplicative.toAdd x).1 + ρ (Multiplicative.toAdd x).2)

omit [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace μ] [IsTopologicalAddGroup μ] in
theorem isMulCocycle₁_thetaFun (red ρ : M →+ μ) :
    groupCohomology.IsMulCocycle₁ (G := PiYddot M) (thetaFun red ρ) := by
  intro g h
  change Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
  rw [← ofAdd_add]
  congr 1
  simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, map_add]
  abel

/-- **The model étale theta cocycle.** -/
def thetaCocycle (red ρ : M →+ μ) : cocycles (PiYddot M) (Multiplicative μ) :=
  mkCocycle (thetaFun red ρ) continuous_of_discreteTopology (isMulCocycle₁_thetaFun red ρ)

/-- **The model étale theta class** in `H¹((Π^tp_Ÿ)^Θ, μ)`. -/
def thetaClass (red ρ : M →+ μ) : ContH1 (PiYddot M) (Multiplicative μ) :=
  mk (thetaCocycle red ρ)

omit [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace μ] [IsTopologicalAddGroup μ] in
/-- For the trivial action every coboundary is trivial. -/
theorem eq_one_of_isMulCoboundary₁ {f : PiYddot M → Multiplicative μ}
    (h : groupCohomology.IsMulCoboundary₁ f) (g : PiYddot M) : f g = 1 := by
  obtain ⟨x, hx⟩ := h
  rw [← hx g]
  exact div_self' x

/-- **The class is trivial iff `red = 0` and `ρ = 0`** (for the trivial action `H¹ = Hom`). -/
theorem thetaClass_eq_one_iff (red ρ : M →+ μ) :
    thetaClass red ρ = 1 ↔ red = 0 ∧ ρ = 0 := by
  rw [thetaClass, mk_eq_one_iff]
  constructor
  · intro h
    have h' := eq_one_of_isMulCoboundary₁ h
    refine ⟨AddMonoidHom.ext fun c => ?_, AddMonoidHom.ext fun a => ?_⟩
    · have := h' (Multiplicative.ofAdd (c, 0))
      simpa [thetaCocycle, mkCocycle, thetaFun] using this
    · have := h' (Multiplicative.ofAdd (0, a))
      simpa [thetaCocycle, mkCocycle, thetaFun] using this
  · rintro ⟨rfl, rfl⟩
    refine ⟨1, fun g => ?_⟩
    simp [thetaCocycle, mkCocycle, thetaFun]

theorem thetaClass_ne_one {red : M →+ μ} (ρ : M →+ μ) (h : red ≠ 0) : thetaClass red ρ ≠ 1 :=
  fun h' => h ((thetaClass_eq_one_iff red ρ).1 h').1

/-- The restriction of the theta class to `Δ_Θ` (`a' = 0`) is `red`. -/
theorem thetaClass_restrict (red ρ : M →+ μ) (c : M) :
    Multiplicative.toAdd ((thetaCocycle red ρ : PiYddot M → Multiplicative μ)
      (Multiplicative.ofAdd (c, 0))) = red c := by
  simp [thetaCocycle, mkCocycle, thetaFun]

/-- **The theta section is the tautological section minus the theta class**:
`s^Θ(c, a') = (−η(c, a'), c, 2a')`. -/
theorem thetaSection_eq (red ρ : M →+ μ) (x : M × M) :
    thetaSection M μ red ρ x =
      (-Multiplicative.toAdd ((thetaCocycle red ρ : PiYddot M → Multiplicative μ)
        (Multiplicative.ofAdd x)), x.1, 2 • x.2) := by
  simp only [thetaSection, AddMonoidHom.coe_mk, ZeroHom.coe_mk, thetaCocycle, mkCocycle,
    thetaFun, toAdd_ofAdd, neg_add, sub_eq_add_neg]

/-- **The reconstructed isomorphism of cyclotomes is minus the restriction of the theta class**
to `l·Δ_Θ`. -/
theorem model_isCyc_eq_neg_thetaClass [IsAddTorsionFree M] (hμ : AddMonoid.IsTorsion μ)
    (l : ℤ) (red ρ : M →+ μ) (t m : μ × M × M) :
    (model M l μ red ρ).IsCyc t m ↔ ∃ y : M, t = (0, l • y, 0) ∧
      m = (-Multiplicative.toAdd ((thetaCocycle red ρ : PiYddot M → Multiplicative μ)
        (Multiplicative.ofAdd (l • y, 0))), 0, 0) := by
  rw [model_isCyc hμ]
  simp only [thetaClass_restrict]

/-- The conjugation by the `k`-th power of the generator of `Gal(Y/X)` on `(Π^tp_Ÿ)^Θ`:
`(c, a') ↦ (c + 2kl·a', a')` (`γ_k` on `a = 2a'`). -/
def conjK (l k : ℤ) : PiYddot M →* PiYddot M where
  toFun x := Multiplicative.ofAdd
    ((Multiplicative.toAdd x).1 + (2 * k * l) • (Multiplicative.toAdd x).2,
      (Multiplicative.toAdd x).2)
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, smul_add, ← ofAdd_add]
    congr 1
    ext
    · simp only [Prod.fst_add]
      abel
    · simp only [Prod.snd_add]

omit [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace μ] [IsTopologicalAddGroup μ] in
/-- `conjK` is `γ_k` on the second coordinate `a = 2a'`. -/
theorem gammaK_thetaSection (l k : ℤ) (red ρ : M →+ μ) (x : M × M) :
    gammaK M l μ k (thetaSection M μ red ρ x) =
      (-red x.1 - ρ x.2, (Multiplicative.toAdd (conjK l k (Multiplicative.ofAdd x))).1,
        2 • x.2) := by
  simp only [gammaK, thetaSection, conjK, AddEquiv.coe_mk, Equiv.coe_fn_mk, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, Prod.mk.injEq, true_and,
    and_true]
  rw [two_nsmul, smul_add, ← add_zsmul]
  congr 2
  ring

/-- **The `Gal(Y/X)`-conjugates of the theta class** (the geometric shadow of [EtTh],
Prop. 1.5(iii)): `η ∘ γ_k − η = 2kl·red(a')`. -/
theorem conj_sub_thetaCocycle (l k : ℤ) (red ρ : M →+ μ) (x : PiYddot M) :
    Multiplicative.toAdd ((thetaCocycle red ρ : PiYddot M → Multiplicative μ) (conjK l k x)) -
      Multiplicative.toAdd ((thetaCocycle red ρ : PiYddot M → Multiplicative μ) x) =
        (2 * k * l) • red (Multiplicative.toAdd x).2 := by
  simp only [thetaCocycle, mkCocycle, thetaFun, conjK, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd, map_add, map_zsmul]
  abel

end Model

end Iut.EtaleTheta
