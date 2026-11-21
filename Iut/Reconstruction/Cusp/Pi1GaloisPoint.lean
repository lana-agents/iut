/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.Pi1GaloisAlgebra
import CurvesJacobian.Cusp.LineS

/-!
# Galois quotients of `π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞}))` with their geometric point

**`Pi1GaloisPoint.line_exists_galoisQuotient_point`**: the Galois quotient `f : π₁ᵉᵗ ↠ G` of
`Pi1GaloisAlgebra.line_exists_sigmaQuotient_ofAlgebra` together with the geometric point
`φ : C → Ω` of the cover over the geometric generic point (`φ ∘ (T → C) = lineToΩS`), such that
the Galois action of `Ω / k(t)` on `φ` is the action of `G` on the cover:

  `σ ∘ φ = φ ∘ ρ (f (lineGaloisS σ))` for all `σ ∈ Gal(Ω / k(t))`.

(The Galois action on fibres is precomposition with `Spec σ`,
`FiniteEtale.galoisAction_hom_app_left`; `coverAut ρ g = Spec (ρ g⁻¹)`;
`galoisQuotientHom_spec`.)
This is the bridge used by MR13's B4′: an inertia element `σ` of a place `W` over a cusp acts on
`φ` through `ρ (f σ)`, so `f σ` stabilises the special point under `φ` ("A2⁻", tfg
`P1Three.Datum.exists_fixed_special_point`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale TensorProduct

universe u

noncomputable section

namespace Iut.Reconstruction.Pi1GaloisPoint

open CurvesJacobian.Cusp Pi1GaloisQuotient Pi1GaloisAlgebra PreGaloisCategory AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω}
  [IsGalois (K₀ k t) Ω] (S : Finset k) (ht : Transcendental k t) (C : Type u) [CommRing C]
  [Algebra (lineRingS S) C] [Algebra.FiniteEtale (lineRingS S) C]

/-- **Galois quotients of `π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞}))` with the geometric point**: for a connected finite
étale `lineRingS S`-algebra `C` with a faithful action `ρ` of `G` and `[K' ⊗ C : K'] ≤ |G|`, there
are a continuous surjection `f : π₁ᵉᵗ ↠ G` and a point `φ : C → Ω` over `lineToΩS` with
`σ ∘ φ = φ ∘ ρ (f (lineGaloisS σ))` for every `σ ∈ Gal(Ω / k(t))`. -/
theorem line_exists_galoisQuotient_point [Nontrivial C]
    (hconn : ∀ e : C, IsIdempotentElem e → e = 0 ∨ e = 1) {G : Type*} [Group G]
    (ρ : G →* (C ≃ₐ[lineRingS S] C)) (hρ : Function.Injective ρ)
    (K' : Type*) [Field K'] [Algebra (lineRingS S) K'] [Algebra K' Ω]
    (hK' : (algebraMap K' Ω).comp (algebraMap (lineRingS S) K') =
      (lineToΩS S ht : lineRingS S →+* Ω))
    (hdeg : Module.finrank K' (K' ⊗[lineRingS S] C) ≤ Nat.card G)
    [TopologicalSpace G] [DiscreteTopology G] :
    ∃ (f : π₁ᵉᵗ(lineGenS S ht) →* G) (φ : C →+* Ω),
      Function.Surjective f ∧ Continuous f ∧
      φ.comp (algebraMap (lineRingS S) C) = (lineToΩS S ht : lineRingS S →+* Ω) ∧
      ∀ σ : Ω ≃ₐ[K₀ k t] Ω,
        (σ : Ω →+* Ω).comp φ = φ.comp (ρ (f (lineGaloisS S ht σ)) : C →+* C) := by
  haveI := connectedSpace_of_idempotent (T := lineRingS S) hconn
  haveI := (isConnected_iff_connectedSpace (ofAlgebra (lineRingS S) C)).2 inferInstance
  have hle := (line_card_fiber_le S ht C K' hK').trans hdeg
  obtain ⟨y⟩ := nonempty_fiber_of_isConnected (fiber (lineGenS S ht)) (ofAlgebra (lineRingS S) C)
  have hρ' := coverAut_injective ρ hρ
  let f := galoisQuotientHom _ _ (coverAut ρ) hρ' hle y
  let L : Spec (.of Ω) ⟶ Spec (.of C) := (fiberObjEquivHom (lineGenS S ht) _ y).left
  let φ : C →+* Ω := (Spec.preimage L).hom
  have hL : Spec.map (CommRingCat.ofHom φ) = L := by
    simp only [φ, CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨f, φ, galoisQuotientHom_surjective _ _ (coverAut ρ) hρ' hle y,
    continuous_galoisQuotientHom _ _ (coverAut ρ) hρ' hle y, ?_, fun σ ↦ ?_⟩
  · have h : L ≫ Spec.map (CommRingCat.ofHom (algebraMap (lineRingS S) C)) = lineGenS S ht :=
      Over.w (fiberObjEquivHom (lineGenS S ht) _ y)
    rw [lineGenS_eq, ← hL, ← Spec.map_comp] at h
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    exact h2
  · have hspec := galoisQuotientHom_spec _ _ (coverAut ρ) hρ' hle y (lineGaloisS S ht σ)
    have h1 := congrArg (fun z ↦ (fiberObjEquivHom (lineGenS S ht) _ z).left) hspec
    simp only at h1
    rw [← fiberObjEquivHom_naturality] at h1
    change (fiberObjEquivHom (lineGenS S ht) _ ((lineGaloisS S ht σ).hom.app _ y)).left ≫
      (coverAut ρ (f (lineGaloisS S ht σ))).hom.left = L at h1
    rw [lineGaloisS, galoisAction_hom_app_left, coverAut, MonoidHom.coe_mk, OneHom.coe_mk,
      specAut_hom_left] at h1
    change (Spec.map _ ≫ L) ≫ _ = L at h1
    rw [← hL, ← Spec.map_comp, ← Spec.map_comp] at h1
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    ext c
    have h3 := RingHom.congr_fun h2 (ρ (f (lineGaloisS S ht σ)) c)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h3
    have hc : ∀ g : G, (ρ g⁻¹) (ρ g c) = c := fun g ↦ by
      rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]
    exact (congrArg (fun z ↦ (σ : Ω →+* Ω) (φ z)) (hc (f (lineGaloisS S ht σ)))).symm.trans h3

end Iut.Reconstruction.Pi1GaloisPoint
