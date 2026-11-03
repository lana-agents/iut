/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.Pi1GaloisQuotient
import Pi1.FundamentalGroup.BaseChangeInjective
import Pi1.FundamentalGroup.Point

/-!
# Galois quotients of `π₁ᵉᵗ` from finite étale algebras with a group action

For a finite étale `T`-algebra `C` (`FiniteEtale.ofAlgebra T C`, the cover `Spec C → Spec T`):

* **`Pi1GaloisAlgebra.specAut`**, **`coverAut : G →* Aut (ofAlgebra T C)`** (`g ↦ Spec (ρ g⁻¹)`) for
  an action `ρ : G →* (C ≃ₐ[T] C)`, faithful if `ρ` is (**`coverAut_injective`**);
* **`connectedSpace_of_idempotent`**: `Spec C` is connected if `C` is nontrivial with only the
  idempotents `0`, `1`;
* **`fiberEquivAlgHom`**: the fibre over `Spec Ω → Spec T` is `C →ₐ[T] Ω`, and
  **`card_fiber_le_finrank`**: its cardinality is at most `[K' ⊗_T C : K']` for every field `K'`
  through which `T → Ω` factors;
* **`line_exists_sigmaQuotient_ofAlgebra`**: for `T = lineRingS S` (`ℙ¹ ∖ (S ∪ {∞})`) and its
  geometric generic point, a connected finite étale `C` with a faithful action of `G` and
  `[K' ⊗ C : K'] ≤ |G|` gives continuous surjections `π₁ᵉᵗ ↠ G` and
  `MaxProSigma P π₁ᵉᵗ ↠ G` (`Pi1GaloisQuotient.line_exists_sigmaQuotient`).

This is the iut side of MR13's (f) step 4 bridge: the lift of a tame `G`-cover of
`ℙ¹_k ∖ {0, 1, ā}` (tfg `P1Three.Datum.ring1AlgAct`, `BaseChangeAct.act`,
`P1Three.connected_lift_algebraic`) gives such a `C` over `K̄`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale TensorProduct

universe u

noncomputable section

namespace Iut.Reconstruction.Pi1GaloisAlgebra

variable {T C : Type u} [CommRing T] [CommRing C] [Algebra T C] [Algebra.FiniteEtale T C]

/-- **The automorphism `Spec σ` of the cover `Spec C → Spec T`** for `σ : C ≃ₐ[T] C`. -/
def specAut (σ : C ≃ₐ[T] C) : Aut (ofAlgebra T C) :=
  MorphismProperty.Over.isoMk
    { hom := Spec.map (CommRingCat.ofHom (σ : C →+* C))
      inv := Spec.map (CommRingCat.ofHom (σ.symm : C →+* C))
      hom_inv_id := by
        change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of C))
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
        ext x
        simp
      inv_hom_id := by
        change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of C))
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
        ext x
        simp }
    (by
      change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap T C)) =
        Spec.map (CommRingCat.ofHom (algebraMap T C))
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact σ.commutes x)

lemma specAut_hom_left (σ : C ≃ₐ[T] C) :
    (specAut σ).hom.left = Spec.map (CommRingCat.ofHom (σ : C →+* C)) :=
  rfl

variable {G : Type*} [Group G] (ρ : G →* (C ≃ₐ[T] C))

/-- **The action of `G` on the cover**: `g ↦ Spec (ρ g⁻¹)` (`Spec` is contravariant). -/
def coverAut : G →* Aut (ofAlgebra T C) where
  toFun g := specAut (ρ g⁻¹)
  map_one' := Iso.ext <| MorphismProperty.Over.Hom.ext <| by
    change Spec.map _ = 𝟙 _
    rw [← Spec.map_id]
    congr 1
    ext x
    simp
  map_mul' g g' := Iso.ext <| MorphismProperty.Over.Hom.ext <| by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp [mul_inv_rev, map_mul, AlgEquiv.mul_apply]

/-- **The action on the cover is faithful** if `ρ` is. -/
theorem coverAut_injective (hρ : Function.Injective ρ) : Function.Injective (coverAut ρ) := by
  refine (injective_iff_map_eq_one _).mpr fun g hg ↦ ?_
  have h1 : Spec.map (CommRingCat.ofHom (ρ g⁻¹ : C →+* C)) = 𝟙 _ :=
    congrArg (fun e : Aut (ofAlgebra T C) ↦ e.hom.left) hg
  have h2 := Spec.map_injective (h1.trans (Spec.map_id _).symm)
  have h3 : ρ g⁻¹ = 1 := AlgEquiv.ext fun x ↦
    congrArg (fun f : CommRingCat.of C ⟶ CommRingCat.of C ↦ f.hom x) h2
  rw [← map_one ρ] at h3
  simpa using hρ h3

/-- **`Spec C` is connected** if `C` is nontrivial with only the trivial idempotents. -/
theorem connectedSpace_of_idempotent [Nontrivial C]
    (h : ∀ e : C, IsIdempotentElem e → e = 0 ∨ e = 1) : ConnectedSpace (ofAlgebra T C).left := by
  change ConnectedSpace (PrimeSpectrum C)
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, fun s hs ↦ ?_⟩
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hs
  rcases h e he with rfl | rfl
  · left; simp
  · right; simp

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra T Ω]

/-- **Geometric points of the cover over `Spec Ω → Spec T` are `T`-algebra maps `C → Ω`.** -/
def overHomEquivAlgHom :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T Ω))) ⟶ (ofAlgebra T C).toComma) ≃
      (C →ₐ[T] Ω) where
  toFun x :=
    { toRingHom := (Spec.preimage x.left).hom
      commutes' := fun c ↦ by
        have h : x.left ≫ Spec.map (CommRingCat.ofHom (algebraMap T C)) =
            Spec.map (CommRingCat.ofHom (algebraMap T Ω)) := Over.w x
        have h2 : Spec.map (CommRingCat.ofHom (algebraMap T C) ≫ Spec.preimage x.left) =
            Spec.map (CommRingCat.ofHom (algebraMap T Ω)) := by
          rw [Spec.map_comp, Spec.map_preimage]
          exact h
        exact congrArg (fun f : CommRingCat.of T ⟶ CommRingCat.of Ω ↦ f.hom c)
          (Spec.map_injective h2) }
  invFun φ := Over.homMk (Spec.map (CommRingCat.ofHom (φ : C →+* Ω))) (by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
    rfl)
  left_inv x := by
    ext1
    change Spec.map (CommRingCat.ofHom (Spec.preimage x.left).hom) = x.left
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  right_inv φ := by
    ext c
    change (Spec.preimage (Spec.map (CommRingCat.ofHom (φ : C →+* Ω)))).hom c = φ c
    rw [Spec.preimage_map]
    rfl

/-- **The fibre of the cover over `Spec Ω → Spec T` is `C →ₐ[T] Ω`.** -/
def fiberEquivAlgHom :
    (fiber (Spec.map (CommRingCat.ofHom (algebraMap T Ω)))).obj (ofAlgebra T C) ≃ (C →ₐ[T] Ω) :=
  (fiberObjEquivHom _ _).trans (overHomEquivAlgHom Ω)

/-- **The fibre has at most `[K' ⊗_T C : K']` points** for a field `K'` through which `T → Ω`
factors. -/
theorem card_fiber_le_finrank (K' : Type*) [Field K'] [Algebra T K'] [Algebra K' Ω]
    [IsScalarTower T K' Ω] :
    Nat.card ((fiber (Spec.map (CommRingCat.ofHom (algebraMap T Ω)))).obj (ofAlgebra T C)) ≤
      Module.finrank K' (K' ⊗[T] C) := by
  rw [Nat.card_congr (fiberEquivAlgHom Ω)]
  let ι : (C →ₐ[T] Ω) → (K' ⊗[T] C →ₐ[K'] Ω) := fun φ ↦
    Algebra.TensorProduct.lift (Algebra.ofId K' Ω) φ fun _ _ ↦ Commute.all _ _
  have hι : Function.Injective ι := fun φ ψ h ↦ AlgHom.ext fun c ↦ by
    have := AlgHom.congr_fun h (1 ⊗ₜ c)
    simpa [ι] using this
  exact (Nat.card_le_card_of_injective ι hι).trans
    (card_algHom_le_finrank K' (K' ⊗[T] C) Ω)

/-! ### The line `ℙ¹ ∖ (S ∪ {∞})` -/

section Line

open CurvesJacobian.Cusp Pi1GaloisQuotient PreGaloisCategory

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω}
  (S : Finset k) (ht : Transcendental k t) (C : Type u) [CommRing C] [Algebra (lineRingS S) C]
  [Algebra.FiniteEtale (lineRingS S) C]

/-- **The fibre of `Spec C` over the geometric generic point of `ℙ¹ ∖ (S ∪ {∞})` has at most
`[K' ⊗ C : K']` points** for a field `K'` through which `lineRingS S → Ω` factors. -/
theorem line_card_fiber_le (K' : Type*) [Field K'] [Algebra (lineRingS S) K'] [Algebra K' Ω]
    (hK' : (algebraMap K' Ω).comp (algebraMap (lineRingS S) K') =
      (lineToΩS S ht : lineRingS S →+* Ω)) :
    Nat.card ((fiber (lineGenS S ht)).obj (ofAlgebra (lineRingS S) C)) ≤
      Module.finrank K' (K' ⊗[lineRingS S] C) := by
  letI : Algebra (lineRingS S) Ω := (lineToΩS S ht : lineRingS S →+* Ω).toAlgebra
  haveI : IsScalarTower (lineRingS S) K' Ω := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.congr_fun hK' x).symm
  rw [lineGenS_eq]
  exact card_fiber_le_finrank Ω K'

/-- **Galois quotients of `π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞}))` from a finite étale algebra**: a connected
(nontrivial, only trivial idempotents) finite étale `lineRingS S`-algebra `C` with a faithful
action of `G` by algebra automorphisms and `[K' ⊗ C : K'] ≤ |G|` gives continuous surjections
`π₁ᵉᵗ ↠ G` and, for `|G|` a `Σ`-number, `MaxProSigma P π₁ᵉᵗ ↠ G`, compatible with
`MaxProSigma.mk`. -/
theorem line_exists_sigmaQuotient_ofAlgebra [Nontrivial C]
    (hconn : ∀ e : C, IsIdempotentElem e → e = 0 ∨ e = 1) {G : Type*} [Group G]
    (ρ : G →* (C ≃ₐ[lineRingS S] C)) (hρ : Function.Injective ρ)
    (K' : Type*) [Field K'] [Algebra (lineRingS S) K'] [Algebra K' Ω]
    (hK' : (algebraMap K' Ω).comp (algebraMap (lineRingS S) K') =
      (lineToΩS S ht : lineRingS S →+* Ω))
    (hdeg : Module.finrank K' (K' ⊗[lineRingS S] C) ≤ Nat.card G)
    [TopologicalSpace G] [DiscreteTopology G] (P : ℕ → Prop)
    (hG : Pi1.Profinite.IsSigmaNat P (Nat.card G)) :
    ∃ (f : π₁ᵉᵗ(lineGenS S ht) →* G) (f' : Pi1.Profinite.MaxProSigma P π₁ᵉᵗ(lineGenS S ht) →* G),
      Function.Surjective f ∧ Continuous f ∧ Function.Surjective f' ∧ Continuous f' ∧
      ∀ τ, f' (Pi1.Profinite.MaxProSigma.mk τ) = f τ := by
  haveI := connectedSpace_of_idempotent (T := lineRingS S) hconn
  haveI := (isConnected_iff_connectedSpace (ofAlgebra (lineRingS S) C)).2 inferInstance
  have hle := (line_card_fiber_le S ht C K' hK').trans hdeg
  obtain ⟨y⟩ := nonempty_fiber_of_isConnected (fiber (lineGenS S ht)) (ofAlgebra (lineRingS S) C)
  have hρ' := coverAut_injective ρ hρ
  exact ⟨galoisQuotientHom _ _ (coverAut ρ) hρ' hle y,
    sigmaQuotientHom _ _ (coverAut ρ) hρ' hle y P hG,
    galoisQuotientHom_surjective _ _ (coverAut ρ) hρ' hle y,
    continuous_galoisQuotientHom _ _ (coverAut ρ) hρ' hle y,
    sigmaQuotientHom_surjective _ _ (coverAut ρ) hρ' hle y P hG,
    continuous_sigmaQuotientHom _ _ (coverAut ρ) hρ' hle y P hG,
    sigmaQuotientHom_mk _ _ (coverAut ρ) hρ' hle y P hG⟩

end Line

end Iut.Reconstruction.Pi1GaloisAlgebra
