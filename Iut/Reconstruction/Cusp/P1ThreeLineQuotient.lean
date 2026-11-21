/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.Pi1GaloisTransport
import CurvesJacobian.Cusp.HemiInvolutionGen
import TemperedFundamentalGroups.SemistableReduction.P1ThreeBaseChange

/-!
# Galois quotients of `π₁ᵉᵗ(ℙ¹_{K̄} ∖ {0, 1, ā})` from tame special covers (MR13 (f), steps 5–6)

Ingredients for the Galois quotient of `π₁ᵉᵗ(ℙ¹_{K̄} ∖ {0, 1, ā})` attached to a tame special cover
(tfg's `P1Three.Datum`, `O` a complete discrete valuation ring with algebraically closed residue
field `k`, `K = Frac O`, `K̄` an algebraic closure):

* **`P1ThreeLineQuotient.lineS a K̄ = {1, ā⁻¹}`**, `pS_eq_polyS`, **`awayEquiv`**:
  tfg's `Localization.Away (pS ā)` is curves-jacobian's `lineRingS {1, ā⁻¹}` (the chart `V₁` of
  `ℙ¹_{K̄}` in the coordinate `s = 1/t`; the cusps `t = 1, a, 0` are `s = 1, ā⁻¹, ∞`);
* **`P1ThreeLineQuotient.baseEquiv`**: `K̄ ⊗_O R1 ≃ lineRingS {1, ā⁻¹}` (tfg `tensorLineEquiv`);
* **`P1ThreeLineQuotient.exists_point_of_tensor`** (generic): for an `R`-algebra `B` with a
  faithful `G`-action, finite of rank `|G|`, such that `K̄ ⊗_O B` is a connected étale
  `K̄ ⊗_O R`-algebra and `K̄ ⊗_O R ≃ lineRingS S`, there are a continuous surjection
  `f : π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞})) ↠ G` and a point `u : B → Ω` over the generic point with
  `σ ∘ u = u ∘ (f σ)` for `σ ∈ Gal(Ω / K̄(t))` (via `Pi1GaloisTransport`).

It is applied to the lift `B₁` of a tame special cover in `P1ThreeCuspStab`.
-/

open Polynomial TensorProduct

universe u

noncomputable section

namespace Iut.Reconstruction.P1ThreeLineQuotient

open SemistableReduction SemistableReduction.P1Three TateLevel AdmissibleLift EtaleTower
  ProjectiveLine CurvesJacobian.Cusp AffOrbicurve Pi1GaloisTransport

/-! ### The base: `Localization.Away (pS ā) = lineRingS {1, ā⁻¹}` -/

section Base

variable {K : Type u} [Field K] (a : K)

open scoped Classical in
/-- The finite set `{1, a⁻¹}` (the cusps `s = 1, a⁻¹` of `V₁`; `s = ∞` is the third). -/
def lineSK (a : K) : Finset K := {1, a⁻¹}

lemma one_ne_inv (ha1 : a ≠ 1) : (1 : K) ≠ a⁻¹ :=
  fun h ↦ ha1 (by rw [← inv_inv a, ← h, inv_one])

open scoped Classical in
/-- **`pS a = polyS {1, a⁻¹}`.** -/
lemma pS_eq_polyS (ha1 : a ≠ 1) : P1Three.pS a = polyS (lineSK a) := by
  rw [polyS, lineSK, Finset.prod_pair (one_ne_inv a ha1), P1Three.pS, map_one]

/-- **`Localization.Away (pS a) ≃ lineRingS {1, a⁻¹}`** over `K[X]`. -/
def awayEquiv (ha1 : a ≠ 1) :
    Localization.Away (P1Three.pS a) ≃ₐ[K[X]] lineRingS (lineSK a) :=
  haveI : IsLocalization.Away (P1Three.pS a) (lineRingS (lineSK a)) := by
    rw [pS_eq_polyS a ha1]
    infer_instance
  IsLocalization.algEquiv (Submonoid.powers (P1Three.pS a)) _ _

lemma awayEquiv_X (ha1 : a ≠ 1) :
    awayEquiv a ha1 (algebraMap K[X] (Localization.Away (P1Three.pS a)) X) = lineTS (lineSK a) :=
  (awayEquiv a ha1).commutes X

lemma awayEquiv_algebraMap (ha1 : a ≠ 1) (c : K) :
    awayEquiv a ha1 (algebraMap K (Localization.Away (P1Three.pS a)) c) =
      algebraMap K (lineRingS (lineSK a)) c := by
  rw [IsScalarTower.algebraMap_apply K K[X] (Localization.Away (P1Three.pS a)),
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

end Base

/-! ### The Galois quotient with its point -/

/-- `O → K̄` is injective (`K = Frac O`). -/
lemma injective_algebraMap_O (O K Kb : Type*) [CommRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [Field Kb] [Algebra K Kb] [Algebra O Kb] [IsScalarTower O K Kb] :
    Function.Injective (algebraMap O Kb) := by
  rw [IsScalarTower.algebraMap_eq O K Kb]
  exact (algebraMap K Kb).injective.comp (IsFractionRing.injective O K)

section Quotient

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k} {a : O}
  (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (Kb : Type u) [Field Kb] [Algebra O Kb]

/-- The cusps `{1, ā⁻¹}` of `V₁ ⊗ K̄` in the coordinate `s` (`ā` the image of `a` in `K̄`). -/
abbrev lineS (a : O) : Finset Kb := lineSK (algebraMap O Kb a)

include hO ha0 in
lemma algebraMap_a_ne_zero : algebraMap O Kb a ≠ 0 := fun h ↦ by
  have hu := (hO a ha0).map (algebraMap O Kb)
  rw [h] at hu
  exact not_isUnit_zero hu

include hO ha1 in
lemma algebraMap_a_ne_one : algebraMap O Kb a ≠ 1 := fun h ↦ by
  have h1 : θ (a - 1) ≠ 0 := by rw [map_sub, map_one]; exact sub_ne_zero.2 ha1
  have hu := (hO _ h1).map (algebraMap O Kb)
  rw [map_sub, h, map_one, sub_self] at hu
  exact not_isUnit_zero hu

include hO ha0 ha1 in
/-- **The base isomorphism** `K̄ ⊗_O R1 ≃ lineRingS {1, ā⁻¹}` (tfg `tensorLineEquiv` and
`awayEquiv`). -/
def baseEquiv : Kb ⊗[O] R1 O a ≃+* lineRingS (lineS Kb a) :=
  ((tensorLineEquiv a Kb (algebraMap_a_ne_zero ha0 hO Kb)).trans
    ((awayEquiv _ (algebraMap_a_ne_one ha1 hO Kb)).restrictScalars Kb)).toRingEquiv

lemma baseEquiv_s1 :
    baseEquiv ha0 ha1 hO Kb ((1 : Kb) ⊗ₜ[O] s1 O a) = lineTS (lineS Kb a) := by
  change awayEquiv _ (algebraMap_a_ne_one ha1 hO Kb)
    (tensorLineEquiv a Kb (algebraMap_a_ne_zero ha0 hO Kb) _) = _
  rw [tensorLineEquiv_s1, awayEquiv_X]

lemma baseEquiv_tmul_one (c : Kb) :
    baseEquiv ha0 ha1 hO Kb (c ⊗ₜ[O] (1 : R1 O a)) =
      algebraMap Kb (lineRingS (lineS Kb a)) c := by
  change awayEquiv _ (algebraMap_a_ne_one ha1 hO Kb)
    (tensorLineEquiv a Kb (algebraMap_a_ne_zero ha0 hO Kb) (algebraMap Kb (Kb ⊗[O] R1 O a) c)) = _
  rw [AlgEquiv.commutes, awayEquiv_algebraMap]

end Quotient

section Generic

variable {O R B : Type u} [CommRing O] [CommRing R] [CommRing B] [Algebra O R] [Algebra R B]
  [Algebra O B] [IsScalarTower O R B] (Kb : Type u) [Field Kb] [Algebra O Kb]
  [Algebra (Kb ⊗[O] R) (Kb ⊗[O] B)]
  {Ω : Type u} [Field Ω] [Algebra Kb Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ Kb t) Ω]
  (ht : Transcendental Kb t)

/-- **Galois quotients from the base change of a cover (generic form)**: for an `R`-algebra `B`
(`R`, `B` flat over `O`, `B` finite of rank `|G|` over `R` with a faithful action `ρ0` of `G` by
`R`-algebra automorphisms) such that `K̄ ⊗_O B` is a connected étale `K̄ ⊗_O R`-algebra and
`K̄ ⊗_O R ≃ lineRingS S`, there are a continuous surjection `f : π₁ᵉᵗ ↠ G` and `u : B → Ω` over
`lineToΩS ∘ e` with `σ ∘ u = u ∘ ρ0 (f σ)`. -/
theorem exists_point_of_tensor [Module.Flat O B] [Module.Flat O R] [Nontrivial B]
    (hOK : Function.Injective (algebraMap O Kb))
    (h₃ : algebraMap (Kb ⊗[O] R) (Kb ⊗[O] B) = (tensorMap O R B Kb).toRingHom)
    [Module.Finite R B] [Algebra.Etale (Kb ⊗[O] R) (Kb ⊗[O] B)]
    (hconn : ∀ c : Kb ⊗[O] B, IsIdempotentElem c → c = 0 ∨ c = 1)
    (S : Finset Kb) (e : Kb ⊗[O] R ≃+* lineRingS S)
    {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (ρ0 : G →* (B ≃ₐ[R] B)) (hρ0 : Function.Injective ρ0)
    (hdeg : Module.finrank R B = Nat.card G) :
    ∃ (f : π₁ᵉᵗ(lineGenS S ht) →* G) (u : B →+* Ω),
      Function.Surjective f ∧ Continuous f ∧
      (∀ r : R, u (algebraMap R B r) = lineToΩS S ht (e ((1 : Kb) ⊗ₜ r))) ∧
      (∀ o : O, u (algebraMap O B o) = lineToΩS S ht (e (algebraMap O Kb o ⊗ₜ (1 : R)))) ∧
      ∀ (σ : Ω ≃ₐ[K₀ Kb t] Ω) (b : B), σ (u b) = u (ρ0 (f (lineGaloisS S ht σ)) b) := by
  haveI : Module.Finite (Kb ⊗[O] R) (Kb ⊗[O] B) := finite_tensor h₃
  haveI : Algebra.FiniteEtale (Kb ⊗[O] R) (Kb ⊗[O] B) := ⟨⟩
  have hinc := BaseChangeAct.injective_includeRight O Kb (B := B) hOK
  haveI : Nontrivial (Kb ⊗[O] B) := hinc.nontrivial
  let ρ := tensorAct Kb h₃ ρ0
  have hρ : Function.Injective ρ := fun g h hgh ↦
    BaseChangeAct.act_injective (R := R) (B := B) O Kb ρ0 hρ0 hinc
      (AlgEquiv.ext fun x ↦ AlgEquiv.congr_fun hgh x)
  letI : Algebra (Kb ⊗[O] R) Ω :=
    ((lineToΩS S ht : lineRingS S →+* Ω).comp e.toRingHom).toAlgebra
  have hincR := BaseChangeAct.injective_includeRight O Kb (B := R) hOK
  have hinj : Function.Injective ((algebraMap (Kb ⊗[O] R) Ω).comp
      (Algebra.TensorProduct.includeRight : R →ₐ[O] Kb ⊗[O] R).toRingHom) :=
    (lineToΩS_injective₂ S ht).comp (e.injective.comp hincR)
  have hfin : Module.finrank Ω (Ω ⊗[Kb ⊗[O] R] (Kb ⊗[O] B)) = Nat.card G := by
    rw [finrank_tensor h₃ Ω hinj, hdeg]
  obtain ⟨f, φ, hfs, hfc, hφ, hσ⟩ := line_exists_galoisQuotient_point_of_equiv S ht
    hconn e ρ hρ Ω (by rw [Algebra.algebraMap_self, RingHom.id_comp]; rfl) hfin.le
  have hφ' : ∀ x, φ (algebraMap (Kb ⊗[O] R) (Kb ⊗[O] B) x) = lineToΩS S ht (e x) :=
    fun x ↦ RingHom.congr_fun hφ x
  refine ⟨f, φ.comp (Algebra.TensorProduct.includeRight : B →ₐ[O] Kb ⊗[O] B).toRingHom,
    hfs, hfc, fun r ↦ ?_, fun o ↦ ?_, fun σ b ↦ ?_⟩
  · have h1 : (Algebra.TensorProduct.includeRight : B →ₐ[O] Kb ⊗[O] B) (algebraMap R B r) =
        algebraMap (Kb ⊗[O] R) (Kb ⊗[O] B) ((1 : Kb) ⊗ₜ r) := by
      rw [h₃]
      rfl
    change φ ((Algebra.TensorProduct.includeRight : B →ₐ[O] Kb ⊗[O] B) (algebraMap R B r)) = _
    rw [h1, hφ']
  · have h1 : (Algebra.TensorProduct.includeRight : B →ₐ[O] Kb ⊗[O] B) (algebraMap O B o) =
        algebraMap (Kb ⊗[O] R) (Kb ⊗[O] B) (algebraMap O Kb o ⊗ₜ (1 : R)) := by
      rw [h₃]
      change (1 : Kb) ⊗ₜ[O] algebraMap O B o = algebraMap O Kb o ⊗ₜ[O] algebraMap R B 1
      rw [map_one, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    change φ ((Algebra.TensorProduct.includeRight : B →ₐ[O] Kb ⊗[O] B) (algebraMap O B o)) = _
    rw [h1, hφ']
  · exact RingHom.congr_fun (hσ σ) ((1 : Kb) ⊗ₜ b)

end Generic

end Iut.Reconstruction.P1ThreeLineQuotient
