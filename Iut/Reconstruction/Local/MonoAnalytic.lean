/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Abelianization
import Iut.Reconstruction.Local.LogShell
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The mono-analytic log-shell `𝓘(G)` (roadmap P17, M3b)

[AbsTopIII], Proposition 5.8 (ii): from the topological group `G = G_K` alone one reconstructs
`𝒪^×(G) := image of the inertia subgroup in G^ab` (`≅ 𝒪_Kˣ` by local class field theory,
`Iut.Reconstruction.unitsAbEquiv`), the ℚ-vector space `𝒪^×(G) ⊗ ℚ`, and the **mono-analytic
log-shell**

`𝓘(G) := (p*)⁻¹ · image(𝒪^×(G) → 𝒪^×(G) ⊗ ℚ)`,   `p* = p` (`p` odd), `p* = 4` (`p = 2`),

with `p = recPrime G`. For `G = G_K` the logarithm identifies `𝒪_Kˣ ⊗ ℚ` with `K` (the kernel
of `𝒪_Kˣ → 𝒪_Kˣ ⊗ ℚ` is the torsion `μ(K)`, which is also the kernel of `log` on `𝒪_Kˣ`), and
`𝓘(G_K)` with the log-shell `(p*)⁻¹ log 𝒪_Kˣ` of IUT III, Definition 1.1 (whose normalised
log-volume is `Iut.Reconstruction.logShellConst`, M3).

## Main definitions and results

* `Iut.Reconstruction.unitsQ G = ℚ ⊗[ℤ] 𝒪^×(G)` and `Iut.Reconstruction.monoLogShell G`;
* `Iut.Reconstruction.map_monoLogShell`: `𝓘(G)` is group-theoretic (transported by every
  isomorphism of topological groups);
* `Iut.Reconstruction.unitsQGalEquiv`, `Iut.Reconstruction.image_monoLogShell_gal`: for
  `G = Gal(Ω/K)`, under `ℚ ⊗ 𝒪_Kˣ ≅ ℚ ⊗ 𝒪^×(G)` the log-shell `𝓘(G)` is
  `{(p*)⁻¹ ⊗ u | u ∈ 𝒪_Kˣ}`.

The identification of `ℚ ⊗ 𝒪_Kˣ` with `K` through the `p`-adic logarithm, i.e. with
`Iut.logShell` (which lives in the valued-field framework of `Iut/Concrete`), is not formalised
here.
-/

open scoped TensorProduct

set_option linter.unusedSectionVars false

namespace Iut.Reconstruction

section GroupTheoretic

variable {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

/-- `𝒪^×(G) ⊗ ℚ`, as `ℚ ⊗[ℤ] 𝒪^×(G)` (with `𝒪^×(G)` written additively). -/
abbrev unitsQ (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Type _ :=
  ℚ ⊗[ℤ] Additive (abUnits G)

/-- `p*` reconstructed from `G`. -/
noncomputable def recPStar (G : Type*) [Group G] [TopologicalSpace G] : ℕ :=
  pStar (recPrime G)

/-- **The mono-analytic log-shell** `𝓘(G) = (p*)⁻¹ · 𝒪^×(G) ⊆ 𝒪^×(G) ⊗ ℚ`. -/
def monoLogShell (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Set (unitsQ G) :=
  {x | ∃ u : abUnits G, x = ((recPStar G : ℚ)⁻¹) ⊗ₜ Additive.ofMul u}

/-- The isomorphism `𝒪^×(G) ≃* 𝒪^×(G')` induced by an isomorphism of topological groups. -/
noncomputable def abUnitsEquiv (ψ : G ≃ₜ* G') : abUnits G ≃* abUnits G' :=
  ((abEquiv ψ).subgroupMap _).trans (MulEquiv.subgroupCongr (map_abUnits ψ))

/-- The induced `ℚ`-linear isomorphism `𝒪^×(G) ⊗ ℚ ≃ 𝒪^×(G') ⊗ ℚ`. -/
noncomputable def unitsQEquiv (ψ : G ≃ₜ* G') : unitsQ G ≃ₗ[ℤ] unitsQ G' :=
  TensorProduct.congr (LinearEquiv.refl ℤ ℚ)
    (abUnitsEquiv ψ).toAdditive.toIntLinearEquiv

theorem unitsQEquiv_tmul (ψ : G ≃ₜ* G') (c : ℚ) (u : abUnits G) :
    unitsQEquiv ψ (c ⊗ₜ Additive.ofMul u) = c ⊗ₜ Additive.ofMul (abUnitsEquiv ψ u) :=
  rfl

theorem unitsQEquiv_smul (ψ : G ≃ₜ* G') (c : ℚ) (x : unitsQ G) :
    unitsQEquiv ψ (c • x) = c • unitsQEquiv ψ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
    simp only [unitsQEquiv, TensorProduct.smul_tmul', TensorProduct.congr_tmul, smul_eq_mul,
      LinearEquiv.refl_apply]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **The mono-analytic log-shell is group-theoretic.** -/
theorem map_monoLogShell (ψ : G ≃ₜ* G') :
    unitsQEquiv ψ '' monoLogShell G = monoLogShell G' := by
  have hp : recPStar G = recPStar G' := by
    simp only [recPStar, recPrime, charCountFun_congr ψ]
  ext x
  constructor
  · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
    exact ⟨abUnitsEquiv ψ u, by rw [unitsQEquiv_tmul, hp]⟩
  · rintro ⟨u, rfl⟩
    refine ⟨((recPStar G : ℚ)⁻¹) ⊗ₜ Additive.ofMul ((abUnitsEquiv ψ).symm u),
      ⟨_, rfl⟩, ?_⟩
    rw [unitsQEquiv_tmul, MulEquiv.apply_symm_apply, hp]

end GroupTheoretic

section Galois

open PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

variable (p K Ω) in
/-- `ℚ ⊗ 𝒪_Kˣ ≃ ℚ ⊗ 𝒪^×(G_K)`, induced by the Artin map. -/
noncomputable def unitsQGalEquiv :
    ℚ ⊗[ℤ] Additive (unitGroup p K) ≃ₗ[ℤ] unitsQ (Ω ≃ₐ[K] Ω) :=
  TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (unitsAbEquiv p K Ω).toAdditive.toIntLinearEquiv

variable (p) in
theorem recPStar_gal : recPStar (Ω ≃ₐ[K] Ω) = pStar p := by
  rw [recPStar, recPrime_gal p]

variable (p K Ω) in
/-- **`𝓘(G_K)` is `(p*)⁻¹ · 𝒪_Kˣ`**: under `ℚ ⊗ 𝒪_Kˣ ≅ ℚ ⊗ 𝒪^×(G_K)` the mono-analytic
log-shell of `G_K` is the set of `(p*)⁻¹ ⊗ u`, `u ∈ 𝒪_Kˣ`. -/
theorem image_monoLogShell_gal :
    unitsQGalEquiv p K Ω '' {x | ∃ u : unitGroup p K, x = ((pStar p : ℚ)⁻¹) ⊗ₜ
      Additive.ofMul u} = monoLogShell (Ω ≃ₐ[K] Ω) := by
  ext x
  constructor
  · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
    exact ⟨unitsAbEquiv p K Ω u, by rw [recPStar_gal p]; rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨((pStar p : ℚ)⁻¹) ⊗ₜ Additive.ofMul ((unitsAbEquiv p K Ω).symm u), ⟨_, rfl⟩, ?_⟩
    rw [recPStar_gal p]
    change ((pStar p : ℚ)⁻¹) ⊗ₜ Additive.ofMul
      (unitsAbEquiv p K Ω ((unitsAbEquiv p K Ω).symm u)) = _
    rw [MulEquiv.apply_symm_apply]

end Galois

end Iut.Reconstruction
