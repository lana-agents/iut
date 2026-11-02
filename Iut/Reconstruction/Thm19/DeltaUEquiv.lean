/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.DeltaXEquiv
import CurvesJacobian.Kummer.SyncBaseChange

/-!
# `Δ_U = Π_{U_{k̄}}` in the Galois model (MR9 item 4 (b-i), step Ξ1)

[AbsTopIII] Prop 1.4 (`Topics in Absolute Anabelian Geometry III.txt` l.1752–1806) works with the
geometric fundamental groups `Δ_U`, `Δ_{U_x}`, `Δ_X` of curves over `k̄`. In the Galois model
`Π_U = H ⧸ ⟨⟨S⟩⟩` of a curve over `k`, the geometric subgroup `Δ_U = ker(Π_U ↠ G_k)` is the
fundamental group `Π_{U_{k̄}}` of the base change (curves-jacobian `baseChange`), as
curves-jacobian `deltaXEquivPiBc` shows for `X` (all inertia elements `SAll`). Here the same for
the inertia elements `S` at the places over `U`:

* `conj_mem_S`, `exists_S_baseChange`, `ambientKernel_S_le_map_baseChange`,
  `bcToDeltaTilde_mem_kernel_S`;
* `DeltaU D = ker(piToGk D)`, **`bcToDeltaU : H_{k̄} →* Δ_U`** (`σ ↦ [σ|_{k(t)}]`), surjective, with
  kernel `⟨⟨S_{k̄}⟩⟩` (`ker_bcToDeltaU`);
* **`deltaUEquivPiBc : Δ_U ≃ₜ* Π_{U_{k̄}}`**.
-/

open Pi1.Orbifold Pi1 AffOrbicurve KummerTheory KummerTheory.Curve CurvesJacobian
  CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

lemma mem_baseChange_HL {σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω} :
    σ ∈ (baseChange D).HL ↔ resK₀ k t σ ∈ D.HL := by
  unfold baseChange
  exact Subgroup.mem_comap

/-- `H` permutes the inertia elements at the places over `U`. -/
theorem conj_mem_S {g : Ω ≃ₐ[K₀ k t] Ω} (hg : g ∈ D.H) {s : Ω ≃ₐ[K₀ k t] Ω}
    (hs : s ∈ D.S) : g * s * g⁻¹ ∈ D.S := by
  obtain ⟨hsHL, W, hkW, htW, hsW⟩ := hs
  refine ⟨D.conj_mem g hg s hsHL,
    W.comap ((g⁻¹ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv : Ω →+* Ω), fun c => ?_, ?_, ?_⟩
  · rw [ValuationSubring.mem_comap]
    have : (g⁻¹ : Ω ≃ₐ[K₀ k t] Ω) (algebraMap k Ω c) = algebraMap k Ω c := by
      rw [IsScalarTower.algebraMap_apply k (K₀ k t) Ω, AlgEquiv.commutes]
    change (g⁻¹ : Ω ≃ₐ[K₀ k t] Ω) (algebraMap k Ω c) ∈ W
    rw [this]
    exact hkW c
  · rw [ValuationSubring.mem_comap]
    have : (g⁻¹ : Ω ≃ₐ[K₀ k t] Ω) t = t :=
      (g⁻¹ : Ω ≃ₐ[K₀ k t] Ω).commutes ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩
    change (g⁻¹ : Ω ≃ₐ[K₀ k t] Ω) t ∈ W
    rw [this]
    exact htW
  · refine ChernClass.mem_inertia_comap (g⁻¹ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (fun x => ?_) hsW
    change (g⁻¹ : Ω ≃ₐ[K₀ k t] Ω) ((g * s * g⁻¹) x) = s ((g⁻¹ : Ω ≃ₐ[K₀ k t] Ω) x)
    simp [AlgEquiv.mul_apply]

/-- **Inertia elements at the places over `U` come from `H_{k̄}`.** -/
theorem exists_S_baseChange {s : Ω ≃ₐ[K₀ k t] Ω} (hs : s ∈ D.S) :
    ∃ σ ∈ (baseChange D).S, resK₀ k t σ = s := by
  obtain ⟨hsHL, W, hkW, htW, hsW⟩ := hs
  have hfix : ∀ x ∈ kbar k Ω, s x = x := fun x hx =>
    inertia_fix_algebraic hkW hsW (mem_algebraicClosure_iff.mp hx)
  obtain ⟨σ, rfl⟩ := exists_resK₀_eq hfix
  exact ⟨σ, ⟨(mem_baseChange_HL D).2 hsHL, W, fun c => kbar_mem W hkW c, htW,
    fun a ha => hsW a ha⟩, rfl⟩

/-- **`⟨⟨S⟩⟩_H ⊆ res(⟨⟨S_{k̄}⟩⟩_{H_{k̄}})`.** -/
theorem ambientKernel_S_le_map_baseChange :
    GaloisPi1.ambientKernel D.H D.S ≤
      (GaloisPi1.ambientKernel (baseChange D).H (baseChange D).S).map (resK₀ k t) := by
  refine Subgroup.topologicalClosure_minimal _ ?_
    ((continuous_resK₀ (k := k) (t := t)).isClosedMap _ (GaloisPi1.isClosed_ambientKernel _ _))
  rw [Subgroup.closure_le]
  rintro _ ⟨h, hh, s, hs, rfl⟩
  obtain ⟨σ, hσ, he⟩ := exists_S_baseChange D (conj_mem_S D hh hs)
  refine ⟨σ, Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ?_), he⟩
  exact ⟨1, (baseChange D).H.one_mem, σ, hσ, by simp⟩

/-- `ι : H_{k̄} → Δ̃` maps `⟨⟨S_{k̄}⟩⟩` into `⟨⟨S⟩⟩`. -/
lemma bcToDeltaTilde_mem_kernel_S {σ : (baseChange D).H}
    (hσ : σ ∈ GaloisPi1.kernel (baseChange D).H (baseChange D).S) :
    ((bcToDeltaTilde D σ : deltaTilde D) : D.H) ∈ GaloisPi1.kernel D.H D.S := by
  let L : Subgroup (Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) :=
    (GaloisPi1.ambientKernel D.H D.S).comap (resK₀ k t)
  have hL : IsClosed (L : Set (Ω ≃ₐ[K₀ (kbar k Ω) t] Ω)) :=
    (GaloisPi1.isClosed_ambientKernel D.H D.S).preimage (continuous_resK₀ (k := k) (t := t))
  have hconj : GaloisPi1.conjSet (baseChange D).H (baseChange D).S ⊆ L := by
    rintro _ ⟨h, hh, x, ⟨hxHL, W, hk, ht, hW⟩, rfl⟩
    refine Subgroup.le_topologicalClosure _ (Subgroup.subset_closure
      ⟨resK₀ k t h, (mem_baseChange_H D).1 hh, resK₀ k t x,
        ⟨(mem_baseChange_HL D).1 hxHL, W, fun c => hk (algebraMap k (kbar k Ω) c), ht, hW⟩, ?_⟩)
    rw [map_mul, map_mul, map_inv]
  have hle : GaloisPi1.ambientKernel (baseChange D).H (baseChange D).S ≤ L :=
    Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le L).2 hconj) hL
  exact Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hσ))

/-- **The geometric subgroup `Δ_U = ker(Π_U ↠ G_k)`.** -/
abbrev DeltaU : Subgroup (Pi D) := (piToGk D).ker

/-- `H_{k̄} → Δ_U`, `σ ↦ [σ|_{k(t)}]`. -/
def bcToDeltaU : (baseChange D).H →* DeltaU D :=
  ((QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)).comp
    ((deltaTilde D).subtype.comp (bcToDeltaTilde D))).codRestrict (DeltaU D) fun σ =>
    (hToGk_eq_one_iff D _).2 fun x hx =>
      (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω).commutes ⟨x, (K₀ (kbar k Ω) t).algebraMap_mem ⟨x, hx⟩⟩

@[simp]
lemma coe_bcToDeltaU (σ : (baseChange D).H) :
    (bcToDeltaU D σ : Pi D) =
      (QuotientGroup.mk ((bcToDeltaTilde D σ : deltaTilde D) : D.H) : Pi D) := rfl

lemma continuous_bcToDeltaU : Continuous (bcToDeltaU D) :=
  ((QuotientGroup.continuous_mk.comp continuous_subtype_val).comp
    (continuous_bcToDeltaTilde (D := D))).subtype_mk _

lemma bcToDeltaU_surjective : Function.Surjective (bcToDeltaU D) := by
  intro δ
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (δ : Pi D)
  have hfix : ∀ x ∈ kbar k Ω, (h : Ω ≃ₐ[K₀ k t] Ω) x = x := by
    refine (hToGk_eq_one_iff D h).1 ?_
    have h1 : piToGk D (δ : Pi D) = 1 := δ.2
    rw [← hh] at h1
    exact h1
  obtain ⟨σ, hσ⟩ := exists_resK₀_eq hfix
  have hσH : σ ∈ (baseChange D).H := by
    rw [mem_baseChange_H, hσ]
    exact h.2
  refine ⟨⟨σ, hσH⟩, Subtype.ext ?_⟩
  rw [coe_bcToDeltaU, ← hh]
  exact congrArg QuotientGroup.mk (Subtype.ext hσ)

/-- **The kernel of `H_{k̄} ↠ Δ_U` is `⟨⟨S_{k̄}⟩⟩`.** -/
theorem ker_bcToDeltaU :
    (bcToDeltaU D).ker = GaloisPi1.kernel (baseChange D).H (baseChange D).S := by
  ext σ
  constructor
  · intro hσ
    have h1 : ((bcToDeltaTilde D σ : deltaTilde D) : D.H) ∈ GaloisPi1.kernel D.H D.S := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hσ)
      rw [coe_bcToDeltaU] at this
      exact (QuotientGroup.eq_one_iff _).1 this
    have h2 : resK₀ k t (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) ∈
        GaloisPi1.ambientKernel D.H D.S := Subgroup.mem_subgroupOf.1 h1
    obtain ⟨σ', hσ', he⟩ := ambientKernel_S_le_map_baseChange D h2
    rw [resK₀_injective he] at hσ'
    exact Subgroup.mem_subgroupOf.2 hσ'
  · intro hσ
    refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
    rw [coe_bcToDeltaU]
    exact (QuotientGroup.eq_one_iff _).2 (bcToDeltaTilde_mem_kernel_S D hσ)

instance t2Space_pi : T2Space (Pi D) := by
  haveI : IsClosed (GaloisPi1.kernel D.H D.S : Set D.H) := GaloisPi1.isClosed_kernel _ _
  infer_instance

/-- **`Δ_U ≃ₜ* Π_{U_{k̄}}`**: the geometric subgroup of `Π_U` is the fundamental group of the
base change `baseChange D`. -/
def deltaUEquivPiBc : DeltaU D ≃ₜ* Pi (baseChange D) :=
  GaloisPi1.equivOfSurjective (baseChange D).H (baseChange D).isClosed_H (baseChange D).S
    (bcToDeltaU D) (continuous_bcToDeltaU D) (bcToDeltaU_surjective D) (ker_bcToDeltaU D)

theorem deltaUEquivPiBc_symm_mk (σ : (baseChange D).H) :
    (deltaUEquivPiBc D).symm (QuotientGroup.mk σ : Pi (baseChange D)) = bcToDeltaU D σ :=
  rfl

/-! ### `Δ_U = π₁ᵉᵗ(U_{k̄})` for a curve -/

section Curve

open CategoryTheory AlgebraicGeometry Belyi CurvesJacobian.Cusp

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

/-- **`U_{k̄}`**: the chart of the coordinate `τ` on `X_{k̄}`. -/
abbrev chartBar (τ : X.functionField) : (baseChangeKbar k X).Opens :=
  chartOne (kbar k (FFClosure X)) (baseChangeKbar k X) (ffMap k X τ)

include hτ in
lemma transcendental_ffMap : Transcendental (kbar k (FFClosure X)) (ffMap k X τ) :=
  transcendental_of_embK (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ)
    (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ)

/-- The places centred on `U_{k̄}` are those of the Galois model `barData`. -/
lemma SU_chartBar :
    SU (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (chartBar k τ) = (barData k hτ).S :=
  (SU_chartOne (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barEquivL_algebraMap k hτ)
    (barData_H_le k hτ) (transcendental_ffMap k hτ)).trans (by rw [barEquivL_tau k hτ]; rfl)

/-- The Galois action `H_{k̄} → π₁ᵉᵗ(U_{k̄})` at the generic point. -/
abbrev rhoBarU : (barData k hτ).H →* DeltaBar k hτ (chartBar k τ) :=
  (barData k hτ).chartHom (barData_H_le k hτ)
    (genericL (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (chartBar k τ))

lemma rhoBarU_spec :
    (rhoBarU k hτ).ker = GaloisPi1.kernel (barData k hτ).H (barData k hτ).S ∧
      Function.Surjective (rhoBarU k hτ) := by
  obtain ⟨h1, h2⟩ := genericL_chartOne_spec (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ)
    (barEquivL_algebraMap k hτ) (barData_H_le k hτ) (transcendental_ffMap k hτ)
  exact ⟨h1.trans (by rw [SU_chartBar k hτ]), h2⟩

/-- **`π₁ᵉᵗ(U_{k̄}) ≃ₜ* Π_{U_{k̄}}`** (Galois model `barData`). -/
def deltaBarUEquiv : DeltaBar k hτ (chartBar k τ) ≃ₜ* Pi (barData k hτ) :=
  GaloisPi1.equivOfSurjective (barData k hτ).H (barData k hτ).isClosed_H (barData k hτ).S
    (rhoBarU k hτ) ((barData k hτ).continuous_chartHom _ _) (rhoBarU_spec k hτ).2
    (rhoBarU_spec k hτ).1

lemma deltaBarUEquiv_symm_mk (σ : (barData k hτ).H) :
    (deltaBarUEquiv k hτ).symm (QuotientGroup.mk σ : Pi (barData k hτ)) = rhoBarU k hτ σ :=
  rfl

/-- **`Δ_U ≃ₜ* π₁ᵉᵗ(U_{k̄})`**: the geometric subgroup of the Galois model `Π_U` of the curve
is the étale fundamental group of `U_{k̄}` (curves-jacobian's `DeltaBar`, where the
synchronization of [AbsTopIII] Prop 1.4 (ii) lives). -/
def deltaUEquivBar : DeltaU (curveGaloisData k hτ) ≃ₜ* DeltaBar k hτ (chartBar k τ) :=
  (deltaUEquivPiBc (curveGaloisData k hτ)).trans (deltaBarUEquiv k hτ).symm

lemma deltaUEquivBar_symm_rhoBarU (σ : (barData k hτ).H) :
    (deltaUEquivBar k hτ).symm (rhoBarU k hτ σ) = bcToDeltaU (curveGaloisData k hτ) σ := by
  rw [← deltaBarUEquiv_symm_mk]
  change (deltaUEquivPiBc (curveGaloisData k hτ)).symm
    ((deltaBarUEquiv k hτ) ((deltaBarUEquiv k hτ).symm (QuotientGroup.mk σ))) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  rfl

end Curve

end Iut.Reconstruction.Thm19
