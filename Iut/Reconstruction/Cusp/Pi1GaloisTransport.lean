/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.Pi1GaloisPoint

/-!
# Galois quotients of `π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞}))` from covers of a ring isomorphic to `lineRingS S`

* **`Pi1GaloisTransport.card_ringHom_le_finrank`**: for a finite `T`-algebra `C` and a field `K'`
  through which `g : T → Ω` factors, the points `φ : C → Ω` over `g` number at most
  `[K' ⊗_T C : K']`;
* **`Pi1GaloisTransport.line_exists_galoisQuotient_point_of_equiv`**: the statement of
  `Pi1GaloisPoint.line_exists_galoisQuotient_point` for a connected finite étale algebra `C` over a
  ring `T` with a ring isomorphism `e : T ≃ lineRingS S` (e.g. `T = K̄ ⊗_O R1`, the base change of
  the chart `V₁` of MR13's `ℙ¹_O` with three cusps, `e` from tfg's `P1Three.tensorLineEquiv`):
  a continuous surjection `f : π₁ᵉᵗ ↠ G` and a point `φ : C → Ω` over `lineToΩS ∘ e` with
  `σ ∘ φ = φ ∘ ρ (f (lineGaloisS σ))`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale TensorProduct

universe u

noncomputable section

namespace Iut.Reconstruction.Pi1GaloisTransport

open CurvesJacobian.Cusp Pi1GaloisQuotient Pi1GaloisAlgebra Pi1GaloisPoint PreGaloisCategory
  AffOrbicurve

section Card

variable {T C Ω : Type*} [CommRing T] [CommRing C] [Field Ω] [Algebra T C] [Module.Finite T C]

/-- **Points over `g : T → Ω` are at most `[K' ⊗_T C : K']`** for a field `K'` through which `g`
factors. -/
theorem card_ringHom_le_finrank (g : T →+* Ω) (K' : Type*) [Field K'] [Algebra T K']
    [Algebra K' Ω] (hK' : (algebraMap K' Ω).comp (algebraMap T K') = g) :
    Nat.card {φ : C →+* Ω // φ.comp (algebraMap T C) = g} ≤ Module.finrank K' (K' ⊗[T] C) := by
  letI : Algebra T Ω := g.toAlgebra
  haveI : IsScalarTower T K' Ω := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.congr_fun hK' x).symm
  let ι : {φ : C →+* Ω // φ.comp (algebraMap T C) = g} → (K' ⊗[T] C →ₐ[K'] Ω) := fun φ ↦
    Algebra.TensorProduct.lift (Algebra.ofId K' Ω)
      { φ.1 with commutes' := fun x ↦ RingHom.congr_fun φ.2 x } fun _ _ ↦ Commute.all _ _
  have hι : Function.Injective ι := fun φ ψ h ↦ Subtype.ext <| RingHom.ext fun c ↦ by
    have := AlgHom.congr_fun h (1 ⊗ₜ c)
    simpa [ι] using this
  exact (Nat.card_le_card_of_injective ι hι).trans (card_algHom_le_finrank K' (K' ⊗[T] C) Ω)

end Card

section Line

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω}
  [IsGalois (K₀ k t) Ω] (S : Finset k) (ht : Transcendental k t)

/-- **Galois quotients from a cover of a ring isomorphic to `lineRingS S`**: for a connected
finite étale `T`-algebra `C`, a ring isomorphism `e : T ≃ lineRingS S`, a faithful action `ρ` of
`G` by `T`-algebra automorphisms and `[K' ⊗_T C : K'] ≤ |G|` (`K'` a field through which
`lineToΩS ∘ e` factors), there are a continuous surjection `f : π₁ᵉᵗ ↠ G` and a point
`φ : C → Ω` over `lineToΩS ∘ e` with `σ ∘ φ = φ ∘ ρ (f (lineGaloisS σ))`. -/
theorem line_exists_galoisQuotient_point_of_equiv {T C : Type u} [CommRing T] [CommRing C]
    [Algebra T C] [Algebra.FiniteEtale T C] [Nontrivial C]
    (hconn : ∀ c : C, IsIdempotentElem c → c = 0 ∨ c = 1) (e : T ≃+* lineRingS S)
    {G : Type*} [Group G] (ρ : G →* (C ≃ₐ[T] C)) (hρ : Function.Injective ρ)
    (K' : Type*) [Field K'] [Algebra T K'] [Algebra K' Ω]
    (hK' : (algebraMap K' Ω).comp (algebraMap T K') =
      (lineToΩS S ht : lineRingS S →+* Ω).comp e.toRingHom)
    (hdeg : Module.finrank K' (K' ⊗[T] C) ≤ Nat.card G)
    [TopologicalSpace G] [DiscreteTopology G] :
    ∃ (f : π₁ᵉᵗ(lineGenS S ht) →* G) (φ : C →+* Ω),
      Function.Surjective f ∧ Continuous f ∧
      φ.comp (algebraMap T C) = (lineToΩS S ht : lineRingS S →+* Ω).comp e.toRingHom ∧
      ∀ σ : Ω ≃ₐ[K₀ k t] Ω,
        (σ : Ω →+* Ω).comp φ = φ.comp (ρ (f (lineGaloisS S ht σ)) : C →+* C) := by
  letI : Algebra (lineRingS S) T := e.symm.toRingHom.toAlgebra
  letI : Algebra (lineRingS S) C := ((algebraMap T C).comp e.symm.toRingHom).toAlgebra
  haveI : IsScalarTower (lineRingS S) T C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let e' : lineRingS S ≃ₐ[lineRingS S] T :=
    AlgEquiv.ofRingEquiv (f := e.symm) fun _ ↦ rfl
  haveI : Algebra.FiniteEtale (lineRingS S) T := Algebra.FiniteEtale.of_equiv e'
  haveI : Algebra.Etale (lineRingS S) C := Algebra.Etale.comp (lineRingS S) T C
  haveI : Module.Finite (lineRingS S) C := Module.Finite.trans T C
  haveI : Algebra.FiniteEtale (lineRingS S) C := ⟨⟩
  let ρ' : G →* (C ≃ₐ[lineRingS S] C) :=
    { toFun := fun g ↦ (ρ g).restrictScalars (lineRingS S)
      map_one' := by ext; simp
      map_mul' := fun g h ↦ by ext; simp }
  have hρ' : Function.Injective ρ' := fun g h hgh ↦ hρ (AlgEquiv.ext fun c ↦
    AlgEquiv.congr_fun hgh c)
  have hinv : ∀ φ : {φ : C →+* Ω // φ.comp (algebraMap T C) =
      (lineToΩS S ht : lineRingS S →+* Ω).comp e.toRingHom}, ∀ y : lineRingS S,
      φ.1 (algebraMap T C (e.symm y)) = lineToΩS S ht y := fun φ y ↦ by
    have h := RingHom.congr_fun φ.2 (e.symm y)
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h
    exact h
  have hle : Nat.card ((fiber (lineGenS S ht)).obj (ofAlgebra (lineRingS S) C)) ≤ Nat.card G := by
    letI : Algebra (lineRingS S) Ω := (lineToΩS S ht : lineRingS S →+* Ω).toAlgebra
    have hfwd : ∀ φ : C →ₐ[lineRingS S] Ω, ∀ x : T,
        φ (algebraMap T C x) = lineToΩS S ht (e x) := fun φ x ↦ by
      have h := φ.commutes (e x)
      change φ (algebraMap T C (e.symm (e x))) = lineToΩS S ht (e x) at h
      rw [RingEquiv.symm_apply_apply] at h
      exact h
    have h1 : Nat.card ((fiber (lineGenS S ht)).obj (ofAlgebra (lineRingS S) C)) =
        Nat.card (C →ₐ[lineRingS S] Ω) := by
      rw [lineGenS_eq]
      exact Nat.card_congr (fiberEquivAlgHom Ω)
    let E : (C →ₐ[lineRingS S] Ω) ≃
        {φ : C →+* Ω // φ.comp (algebraMap T C) =
          (lineToΩS S ht : lineRingS S →+* Ω).comp e.toRingHom} :=
      { toFun := fun φ ↦ ⟨φ.toRingHom, RingHom.ext (hfwd φ)⟩
        invFun := fun φ ↦ { φ.1 with commutes' := hinv φ }
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [h1, Nat.card_congr E]
    exact (card_ringHom_le_finrank _ K' hK').trans hdeg
  obtain ⟨f, φ, hfs, hfc, hφ, hσ⟩ :=
    line_exists_galoisQuotient_point_of_card S ht C hconn ρ' hρ' hle
  refine ⟨f, φ, hfs, hfc, RingHom.ext fun x ↦ ?_, hσ⟩
  have h := RingHom.congr_fun hφ (e x)
  change φ (algebraMap T C (e.symm (e x))) = lineToΩS S ht (e x) at h
  rw [RingEquiv.symm_apply_apply] at h
  exact h

end Line

end Iut.Reconstruction.Pi1GaloisTransport
