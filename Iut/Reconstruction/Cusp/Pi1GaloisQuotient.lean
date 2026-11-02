/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.CategoryTheory.Galois.Prorepresentability
import Pi1.FundamentalGroup.Galois
import Pi1.FundamentalGroup.Functoriality
import Pi1.Profinite.ProSigma
import CurvesJacobian.Cusp.LineS

/-!
# Finite Galois quotients of `π₁ᵉᵗ` from covers with enough automorphisms

Let `C` be a Galois category with fibre functor `F`, and let `X` be a connected object of `C`
on which a group `G` acts faithfully (`ρ : G →* Aut X` injective) with
`|F X| ≤ |G|` (e.g. `|G|` = the degree of `X`). Then:

* `isGalois_of_card_le`: `X` is a Galois object (the evaluation `g ↦ ρ g • x` is an injection
  `G → F X` with `|F X| ≤ |G|`, hence a bijection, so `Aut X` acts transitively on `F X`,
  `isGalois_iff_pretransitive`);
* `bijective_of_card_le`: `ρ : G ≅ Aut X`; `finite_of_card_le`: `G` is finite;
* `galoisQuotientHom F X ρ hρ hcard x : Aut F →* G` (for a point `x ∈ F X`) is a **continuous
  surjection** (`galoisQuotientHom_surjective`, `continuous_galoisQuotientHom`), characterised by
  `ρ (galoisQuotientHom … t) • (t • x) = x` (`galoisQuotientHom_spec`). It is
  `t ↦ ρ⁻¹ (σ_t⁻¹)`, where `σ_t ∈ Aut X` is the unique automorphism with `σ_t • x = t • x`
  (`autFiber`; `t ↦ σ_t` is an anti-homomorphism, `autFiber_mul`, so `autFiberHom` uses `σ_t⁻¹`);
* `sigmaQuotientHom`: if `|G|` is a `Σ`-number (`Pi1.Profinite.IsSigmaNat P`), the surjection
  factors through the maximal pro-`Σ` quotient `Pi1.Profinite.MaxProSigma P (Aut F)`.

Applied to the étale fundamental group `π₁ᵉᵗ(ξ) = Aut (fiber ξ)` of pi1 (`FiniteEtale X` for a
connected scheme `X` and a geometric point `ξ`), and in particular to
`X = ℙ¹ ∖ (S ∪ {∞}) = Spec (lineRingS S)` with the geometric generic point `lineGenS S ht` of
curves-jacobian (`line_isGalois_of_card`, `line_exists_galoisQuotient`,
`line_exists_sigmaQuotient`).
-/

open CategoryTheory PreGaloisCategory

universe u₁ u₂ w u

noncomputable section

namespace Iut.Reconstruction.Pi1GaloisQuotient

section Generic

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w})
  [FiberFunctor F]

section Card

variable {G : Type*} [Group G] (X : C) [PreGaloisCategory.IsConnected X] (ρ : G →* Aut X)

lemma surjective_eval_of_card_le (hρ : Function.Injective ρ)
    (hcard : Nat.card (F.obj X) ≤ Nat.card G) (x : F.obj X) :
    Function.Surjective (fun g : G ↦ ρ g • x) :=
  (((evaluation_aut_injective_of_isConnected F X x).comp hρ :
    Function.Injective (fun g : G ↦ ρ g • x)).bijective_of_nat_card_le hcard).2

/-- **A connected object with a faithful action of a group of order `≥` its degree is Galois.** -/
theorem isGalois_of_card_le (hρ : Function.Injective ρ)
    (hcard : Nat.card (F.obj X) ≤ Nat.card G) : IsGalois X := by
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected F X
  have hsurj := surjective_eval_of_card_le F X ρ hρ hcard x
  rw [isGalois_iff_pretransitive F X]
  refine ⟨fun y z ↦ ?_⟩
  obtain ⟨g, hg⟩ := hsurj y
  obtain ⟨h, hh⟩ := hsurj z
  refine ⟨ρ h * (ρ g)⁻¹, ?_⟩
  change ρ g • x = y at hg
  change ρ h • x = z at hh
  rw [← hg, ← hh, smul_smul, inv_mul_cancel_right]

/-- Under the hypotheses of `isGalois_of_card_le`, `ρ : G → Aut X` is bijective. -/
theorem bijective_of_card_le (hρ : Function.Injective ρ)
    (hcard : Nat.card (F.obj X) ≤ Nat.card G) : Function.Bijective ρ := by
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected F X
  refine ⟨hρ, fun σ ↦ ?_⟩
  obtain ⟨g, hg⟩ := surjective_eval_of_card_le F X ρ hρ hcard x (σ • x)
  exact ⟨g, evaluation_aut_injective_of_isConnected F X x hg⟩

include F in
/-- Under the hypotheses of `isGalois_of_card_le`, `G` is finite. -/
theorem finite_of_card_le (hρ : Function.Injective ρ) : Finite G := by
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected F X
  exact Finite.of_injective _ ((evaluation_aut_injective_of_isConnected F X x).comp hρ)

end Card

section AutFiber

variable (X : C) [IsGalois X] (x : F.obj X)

/-- For `t ∈ Aut F`, the unique `σ_t ∈ Aut X` with `σ_t • x = t • x`. -/
def autFiber (t : Aut F) : Aut X :=
  (evaluationEquivOfIsGalois F X x).symm (t • x)

lemma autFiber_smul (t : Aut F) : autFiber F X x t • x = t • x :=
  evaluationEquivOfIsGalois_symm_fiber F X x (t • x)

lemma autFiber_eq_of_smul (t : Aut F) (σ : Aut X) (h : σ • x = t • x) :
    autFiber F X x t = σ :=
  evaluation_aut_injective_of_isConnected F X x ((autFiber_smul F X x t).trans h.symm)

lemma autFiber_mul (s t : Aut F) :
    autFiber F X x (s * t) = autFiber F X x t * autFiber F X x s := by
  refine autFiber_eq_of_smul F X x _ _ ?_
  rw [mul_smul, mul_smul, autFiber_smul F X x s]
  change F.map (autFiber F X x t).hom (s • x) = s • t • x
  rw [← mulAction_naturality]
  exact congrArg (s • ·) (autFiber_smul F X x t)

/-- The homomorphism `Aut F → Aut X`, `t ↦ σ_t⁻¹` (for a Galois object `X` and `x ∈ F X`). -/
def autFiberHom : Aut F →* Aut X where
  toFun t := (autFiber F X x t)⁻¹
  map_one' := by
    rw [autFiber_eq_of_smul F X x 1 1 (by rw [one_smul, one_smul]), inv_one]
  map_mul' s t := by
    simp only [autFiber_mul, mul_inv_rev]

lemma autFiberHom_apply (t : Aut F) : autFiberHom F X x t = (autFiber F X x t)⁻¹ := rfl

lemma autFiberHom_smul (t : Aut F) : autFiberHom F X x t • t • x = x := by
  rw [autFiberHom_apply, ← autFiber_smul F X x t, inv_smul_smul]

lemma autFiberHom_surjective : Function.Surjective (autFiberHom F X x) := by
  intro σ
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq (Aut F) x (σ⁻¹ • x)
  refine ⟨t, ?_⟩
  rw [autFiberHom_apply, autFiber_eq_of_smul F X x t σ⁻¹ ht.symm, inv_inv]

end AutFiber

section Quotient

variable {G : Type*} [Group G] (X : C) [PreGaloisCategory.IsConnected X] (ρ : G →* Aut X)
  (hρ : Function.Injective ρ) (hcard : Nat.card (F.obj X) ≤ Nat.card G) (x : F.obj X)

/-- **The finite quotient `π₁ ↠ G`** defined by a connected object `X` with a faithful action
`ρ` of `G`, `|F X| ≤ |G|`, and a point `x ∈ F X`. -/
def galoisQuotientHom : Aut F →* G :=
  haveI := isGalois_of_card_le F X ρ hρ hcard
  (MulEquiv.ofBijective ρ (bijective_of_card_le F X ρ hρ hcard)).symm.toMonoidHom.comp
    (autFiberHom F X x)

lemma ρ_galoisQuotientHom (t : Aut F) :
    haveI := isGalois_of_card_le F X ρ hρ hcard
    ρ (galoisQuotientHom F X ρ hρ hcard x t) = autFiberHom F X x t :=
  MulEquiv.ofBijective_apply_symm_apply ρ (bijective_of_card_le F X ρ hρ hcard)

/-- **Characterisation of `galoisQuotientHom`**: `ρ (galoisQuotientHom … t)` maps `t • x` to
`x`. -/
theorem galoisQuotientHom_spec (t : Aut F) :
    F.map (ρ (galoisQuotientHom F X ρ hρ hcard x t)).hom (t.hom.app X x) = x := by
  haveI := isGalois_of_card_le F X ρ hρ hcard
  change ρ (galoisQuotientHom F X ρ hρ hcard x t) • t • x = x
  rw [ρ_galoisQuotientHom]
  exact autFiberHom_smul F X x t

theorem galoisQuotientHom_surjective :
    Function.Surjective (galoisQuotientHom F X ρ hρ hcard x) := by
  haveI := isGalois_of_card_le F X ρ hρ hcard
  intro g
  obtain ⟨t, ht⟩ := autFiberHom_surjective F X x (ρ g)
  exact ⟨t, hρ ((ρ_galoisQuotientHom F X ρ hρ hcard x t).trans ht)⟩

theorem continuous_galoisQuotientHom [TopologicalSpace G] [DiscreteTopology G] :
    Continuous (galoisQuotientHom F X ρ hρ hcard x) := by
  haveI := isGalois_of_card_le F X ρ hρ hcard
  have h : (galoisQuotientHom F X ρ hρ hcard x : Aut F → G) =
      (fun y : F.obj X ↦ (MulEquiv.ofBijective ρ (bijective_of_card_le F X ρ hρ hcard)).symm
        ((evaluationEquivOfIsGalois F X x).symm y)⁻¹) ∘ (fun t : Aut F ↦ t • x) := rfl
  rw [h]
  exact continuous_of_discreteTopology.comp (continuous_id.smul continuous_const)

/-- **Factorisation through the maximal pro-`Σ` quotient** when `|G|` is a `Σ`-number. -/
def sigmaQuotientHom (P : ℕ → Prop) [TopologicalSpace G] [DiscreteTopology G]
    (hG : Pi1.Profinite.IsSigmaNat P (Nat.card G)) :
    Pi1.Profinite.MaxProSigma P (Aut F) →* G :=
  haveI := finite_of_card_le F X ρ hρ
  Pi1.Profinite.MaxProSigma.liftFinite (galoisQuotientHom F X ρ hρ hcard x)
    (continuous_galoisQuotientHom F X ρ hρ hcard x) hG

variable (P : ℕ → Prop) [TopologicalSpace G] [DiscreteTopology G]
  (hG : Pi1.Profinite.IsSigmaNat P (Nat.card G))

theorem sigmaQuotientHom_mk (t : Aut F) :
    sigmaQuotientHom F X ρ hρ hcard x P hG (Pi1.Profinite.MaxProSigma.mk t) =
      galoisQuotientHom F X ρ hρ hcard x t :=
  rfl

theorem sigmaQuotientHom_surjective :
    Function.Surjective (sigmaQuotientHom F X ρ hρ hcard x P hG) := by
  intro g
  obtain ⟨t, ht⟩ := galoisQuotientHom_surjective F X ρ hρ hcard x g
  exact ⟨Pi1.Profinite.MaxProSigma.mk t, ht⟩

theorem continuous_sigmaQuotientHom :
    Continuous (sigmaQuotientHom F X ρ hρ hcard x P hG) :=
  haveI := finite_of_card_le F X ρ hρ
  Pi1.Profinite.MaxProSigma.continuous_liftFinite _ _ hG

end Quotient

end Generic

/-! ### The line `ℙ¹ ∖ (S ∪ {∞})` with its geometric generic point -/

section Line

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale CurvesJacobian.Cusp

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω}
  (S : Finset k) (ht : Transcendental k t) {G : Type*} [Group G]
  (Y : FiniteEtale (Spec (.of (lineRingS S)))) (ρ : G →* Aut Y)

/-- A connected finite étale cover `Y` of `ℙ¹ ∖ (S ∪ {∞})` with a faithful action of a group
`G` whose order is the degree of `Y` is Galois. -/
theorem line_isGalois_of_card [ConnectedSpace Y.left] (hρ : Function.Injective ρ)
    (hcard : Nat.card G = Nat.card ((fiber (lineGenS S ht)).obj Y)) : IsGalois Y :=
  haveI := (isConnected_iff_connectedSpace Y).2 inferInstance
  isGalois_of_card_le (fiber (lineGenS S ht)) Y ρ hρ hcard.ge

/-- **The continuous surjection `π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞}), η) ↠ G`** attached to a connected finite
étale cover `Y` with a faithful action of `G`, `|G| = deg Y`, and a point `y` of its fibre:
`ρ (f t)` maps `t • y` to `y`. -/
theorem line_exists_galoisQuotient [ConnectedSpace Y.left] (hρ : Function.Injective ρ)
    (hcard : Nat.card G = Nat.card ((fiber (lineGenS S ht)).obj Y))
    (y : (fiber (lineGenS S ht)).obj Y) [TopologicalSpace G] [DiscreteTopology G] :
    ∃ f : π₁ᵉᵗ(lineGenS S ht) →* G, Function.Surjective f ∧ Continuous f ∧
      ∀ τ, (fiber (lineGenS S ht)).map (ρ (f τ)).hom (τ.hom.app Y y) = y := by
  haveI := (isConnected_iff_connectedSpace Y).2 inferInstance
  exact ⟨galoisQuotientHom _ Y ρ hρ hcard.ge y, galoisQuotientHom_surjective _ Y ρ hρ hcard.ge y,
    continuous_galoisQuotientHom _ Y ρ hρ hcard.ge y, galoisQuotientHom_spec _ Y ρ hρ hcard.ge y⟩

/-- **The `Σ`-version**: if `|G|` is a `Σ`-number, the surjection of
`line_exists_galoisQuotient` factors through `MaxProSigma P π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞}), η)`. -/
theorem line_exists_sigmaQuotient [ConnectedSpace Y.left] (hρ : Function.Injective ρ)
    (hcard : Nat.card G = Nat.card ((fiber (lineGenS S ht)).obj Y))
    (y : (fiber (lineGenS S ht)).obj Y) [TopologicalSpace G] [DiscreteTopology G]
    (P : ℕ → Prop) (hG : Pi1.Profinite.IsSigmaNat P (Nat.card G)) :
    ∃ (f : π₁ᵉᵗ(lineGenS S ht) →* G) (f' : Pi1.Profinite.MaxProSigma P π₁ᵉᵗ(lineGenS S ht) →* G),
      Function.Surjective f ∧ Continuous f ∧ Function.Surjective f' ∧ Continuous f' ∧
      (∀ τ, f' (Pi1.Profinite.MaxProSigma.mk τ) = f τ) ∧
      ∀ τ, (fiber (lineGenS S ht)).map (ρ (f τ)).hom (τ.hom.app Y y) = y := by
  haveI := (isConnected_iff_connectedSpace Y).2 inferInstance
  exact ⟨galoisQuotientHom _ Y ρ hρ hcard.ge y, sigmaQuotientHom _ Y ρ hρ hcard.ge y P hG,
    galoisQuotientHom_surjective _ Y ρ hρ hcard.ge y,
    continuous_galoisQuotientHom _ Y ρ hρ hcard.ge y,
    sigmaQuotientHom_surjective _ Y ρ hρ hcard.ge y P hG,
    continuous_sigmaQuotientHom _ Y ρ hρ hcard.ge y P hG,
    sigmaQuotientHom_mk _ Y ρ hρ hcard.ge y P hG,
    galoisQuotientHom_spec _ Y ρ hρ hcard.ge y⟩

end Line

end Iut.Reconstruction.Pi1GaloisQuotient
