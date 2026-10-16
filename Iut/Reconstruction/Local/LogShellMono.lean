/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Galois
import Iut.Reconstruction.Local.LogVolumeCompletion
import Iut.Reconstruction.Local.UnitBall

/-!
# The mono-analytic log-shell of an MLF-Galois group and its log-volume (roadmap MR11)

[AbsTopIII], Proposition 5.8 (ii), (iii): from a topological group `G` isomorphic to the absolute
Galois group `G_k` of a finite extension `k/ℚ_p` one constructs, group-theoretically, the
`ℚ`-vector space `k∼(G)^G = 𝒪^×(G) ⊗ ℚ` (`Iut.Reconstruction.unitsQ`), the log-shell
`𝓘(G) = (p*)⁻¹ · 𝒪^×(G)` (`Iut.Reconstruction.monoLogShell`) and its log-volume, normalised by

`μ^log(G)(𝓘(G)) = {−1 − m_G/f_G + e_G · log(p*_G)/log(p_G)} · F(G)`,

`F(G) ↔ f_G · log p_G`. Here we package the identification of these group-theoretic objects with
the log-shell `Iut.logShell k p` of IUT III, Definition 1.1, for an arbitrary isomorphism
`ψ : G ≃ₜ* Gal(Ω/k)` — the only input — with no further hypothesis: the unit balls of the
valuation of `k` and of the spectral norm agree automatically (`hball_auto`, shell #36 of the
multiradial ROADMAP).

## Main definitions and results

* `monoLogEquiv ψ : unitsQ G ≃+ k`: `ℚ ⊗ 𝒪^×(G) ≅ ℚ ⊗ 𝒪_kˣ ≅ k` (`ψ`, local class field theory,
  then the `p`-adic logarithm);
* **`monoLogShellEquiv ψ : monoLogShell G ≃ logShell k p`** (`image_monoLogEquiv`);
* **`monoLogEquiv_unitsQEquiv`** (equivariance): an automorphism `φ` of `G` acts on `unitsQ G`
  through `unitsQEquiv φ` and on `k` through the identification `galLogEquiv` induced by
  `ψ ∘ φ ∘ ψ⁻¹`; `monoLogShellEquiv_unitsQEquiv` for the log-shells;
* `monoLogVol G := recLogShellConst G · log p_G / e_G` (group-theoretic,
  `monoLogVol_congr`) and **`logVol_monoLogShell`**: it is the normalised Haar log-volume
  `log(μ(𝓘_k)/μ(𝒪_k)) / [k : ℚ_p]` of the log-shell, for every Haar measure `μ` on `k`;
* hypothesis-free versions of the results of `LogVolumeLCFT.lean`, `LogShellIdent.lean`:
  `measure_logShell_eq_auto`, `logVolume_logShell_eq_auto`, `image_logTensor_monoLogShell_auto`.
-/

namespace Iut.Reconstruction

open MeasureTheory PadicField Iut.LogLink
open scoped TensorProduct Valued

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Functoriality of `unitsQEquiv` -/

section Functorial

variable {G G' G'' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  [Group G''] [TopologicalSpace G''] [IsTopologicalGroup G'']

theorem abEquiv_mk (ψ : G ≃ₜ* G') (g : G) :
    abEquiv ψ (QuotientGroup.mk g : TopologicalAbelianization G) = QuotientGroup.mk (ψ g) := rfl

theorem abEquiv_trans (ψ : G ≃ₜ* G') (χ : G' ≃ₜ* G'') (x : TopologicalAbelianization G) :
    abEquiv (ψ.trans χ) x = abEquiv χ (abEquiv ψ x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem abEquiv_refl (x : TopologicalAbelianization G) :
    abEquiv (ContinuousMulEquiv.refl G) x = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem abUnitsEquiv_trans (ψ : G ≃ₜ* G') (χ : G' ≃ₜ* G'') (u : abUnits G) :
    abUnitsEquiv (ψ.trans χ) u = abUnitsEquiv χ (abUnitsEquiv ψ u) :=
  Subtype.ext (abEquiv_trans ψ χ u)

theorem abUnitsEquiv_refl (u : abUnits G) : abUnitsEquiv (ContinuousMulEquiv.refl G) u = u :=
  Subtype.ext (abEquiv_refl (u : TopologicalAbelianization G))

theorem unitsQEquiv_trans (ψ : G ≃ₜ* G') (χ : G' ≃ₜ* G'') (x : unitsQ G) :
    unitsQEquiv (ψ.trans χ) x = unitsQEquiv χ (unitsQEquiv ψ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
    change a ⊗ₜ Additive.ofMul (abUnitsEquiv (ψ.trans χ) u.toMul) =
      a ⊗ₜ Additive.ofMul (abUnitsEquiv χ (abUnitsEquiv ψ u.toMul))
    rw [abUnitsEquiv_trans]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem unitsQEquiv_symm_apply (ψ : G ≃ₜ* G') (x : unitsQ G') :
    unitsQEquiv ψ (unitsQEquiv ψ.symm x) = x := by
  rw [← unitsQEquiv_trans]
  have : ψ.symm.trans ψ = ContinuousMulEquiv.refl G' := by ext; simp
  rw [this]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
    change a ⊗ₜ Additive.ofMul (abUnitsEquiv (ContinuousMulEquiv.refl G') u.toMul) = _
    rw [abUnitsEquiv_refl]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

end Functorial

/-! ### Hypothesis-free versions (shell #36 removed) -/

section Auto

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type*} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k] [CompleteSpace k] [CharZero k]

/-- **[AbsTopIII], Proposition 5.8 (iii): the volume of the log-shell**, for every `p`-adic field
`k` (no compatibility hypothesis between the valuation and the `ℚ_p`-structure):
`p^{f+m} · μ(𝓘_k) = (p*)^d · μ(𝒪_k)`. -/
theorem measure_logShell_eq_auto [ProperSpace k] [MeasurableSpace k] [BorelSpace k]
    (μ : Measure k) [μ.IsAddLeftInvariant] :
    (p : ENNReal) ^ (f p ℚ_[p] k + mExp p k) * μ (logShell k p) =
      (pStar p : ENNReal) ^ Module.finrank ℚ_[p] k * μ (Metric.closedBall 0 1) :=
  measure_logShell_eq hball_auto μ

/-- **The normalised log-volume of `Iut.logShell` is given by `logShellConst`**, for every
`p`-adic field `k`. -/
theorem logVolume_logShell_eq_auto [ProperSpace k] [MeasurableSpace k] [BorelSpace k]
    (μ : Measure k) [μ.IsAddLeftInvariant]
    (h0 : μ (Metric.closedBall 0 1) ≠ 0) (hfin : μ (Metric.closedBall 0 1) ≠ ⊤) :
    Real.log ((μ (logShell k p)).toReal / (μ (Metric.closedBall 0 1)).toReal) /
        Module.finrank ℚ_[p] k =
      logShellConst p (f p ℚ_[p] k) (e p ℚ_[p] k) (mExp p k) * Real.log p / e p ℚ_[p] k :=
  logVolume_logShell_eq hball_auto μ h0 hfin

variable {Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

variable (Ω) in
/-- **[AbsTopIII], Proposition 5.8 (ii)**, for every `p`-adic field `k`: the logarithm
`ℚ ⊗ 𝒪^×(G_k) ≅ ℚ ⊗ 𝒪_kˣ → k` maps `𝓘(G_k)` onto `Iut.logShell k p`. -/
theorem image_logTensor_monoLogShell_auto :
    (fun x => logTensor hball_auto ((unitsQGalEquiv p k Ω).symm x)) ''
        monoLogShell (Ω ≃ₐ[k] Ω) = logShell k p :=
  image_logTensor_monoLogShell hball_auto Ω

end Auto

/-! ### The log-shell of an abstract MLF-Galois group -/

section Mono

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type*} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k] [CompleteSpace k] [CharZero k]
variable {Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **`ℚ ⊗ 𝒪^×(G) ≅ k`** for `ψ : G ≃ₜ* G_k`: `ψ`, the Artin map, and the `p`-adic
logarithm `ℚ ⊗ 𝒪_kˣ ≅ k`. -/
def monoLogEquiv (ψ : G ≃ₜ* (Ω ≃ₐ[k] Ω)) : unitsQ G ≃+ k :=
  (unitsQEquiv ψ).toAddEquiv.trans
    ((unitsQGalEquiv p k Ω).symm.toAddEquiv.trans (logEquiv hball_auto))

theorem monoLogEquiv_apply (ψ : G ≃ₜ* (Ω ≃ₐ[k] Ω)) (x : unitsQ G) :
    monoLogEquiv (p := p) ψ x =
      logTensor hball_auto ((unitsQGalEquiv p k Ω).symm (unitsQEquiv ψ x)) := rfl

/-- **The image of the group-theoretic log-shell `𝓘(G)` is `Iut.logShell k p`.** -/
theorem image_monoLogEquiv (ψ : G ≃ₜ* (Ω ≃ₐ[k] Ω)) :
    monoLogEquiv (p := p) ψ '' monoLogShell G = logShell k p := by
  rw [← image_logTensor_monoLogShell_auto (p := p) Ω, ← map_monoLogShell ψ, Set.image_image]
  rfl

/-- **`𝓘(G) ≃ 𝓘_k`** ([AbsTopIII], Proposition 5.8 (ii); IUT III, Proposition 1.2 (vi)). -/
def monoLogShellEquiv (ψ : G ≃ₜ* (Ω ≃ₐ[k] Ω)) : monoLogShell G ≃ logShell k p :=
  ((monoLogEquiv (p := p) ψ).toEquiv.image (monoLogShell G)).trans
    (Equiv.setCongr (image_monoLogEquiv ψ))

theorem coe_monoLogShellEquiv (ψ : G ≃ₜ* (Ω ≃ₐ[k] Ω)) (x : monoLogShell G) :
    (monoLogShellEquiv (p := p) ψ x : k) = monoLogEquiv (p := p) ψ x := rfl

/-- **Equivariance**: an automorphism `φ` of `G` acts on `ℚ ⊗ 𝒪^×(G)` by `unitsQEquiv φ`, and on
`k` by the unit-induced identification `galLogEquiv` of `ψ φ ψ⁻¹`. -/
theorem monoLogEquiv_unitsQEquiv (ψ : G ≃ₜ* (Ω ≃ₐ[k] Ω)) (φ : G ≃ₜ* G) (x : unitsQ G) :
    monoLogEquiv (p := p) ψ (unitsQEquiv φ x) =
      galLogEquiv (hball_auto (p := p)) ((ψ.symm.trans φ).trans ψ) (monoLogEquiv (p := p) ψ x) := by
  rw [monoLogEquiv_apply, monoLogEquiv_apply, galLogEquiv_transport]
  congr 2
  rw [← unitsQEquiv_trans, ← unitsQEquiv_trans]
  have h : φ.trans ψ = ψ.trans ((ψ.symm.trans φ).trans ψ) := by
    refine ContinuousMulEquiv.ext fun g => ?_
    change ψ (φ g) = ψ (φ (ψ.symm (ψ g)))
    rw [ContinuousMulEquiv.symm_apply_apply]
  rw [h]

/-- **The equivalence of log-shells is equivariant.** -/
theorem monoLogShellEquiv_unitsQEquiv (ψ : G ≃ₜ* (Ω ≃ₐ[k] Ω)) (φ : G ≃ₜ* G)
    (x : monoLogShell G) (hx : unitsQEquiv φ (x : unitsQ G) ∈ monoLogShell G) :
    (monoLogShellEquiv (p := p) ψ ⟨_, hx⟩ : k) =
      galLogEquiv (hball_auto (p := p)) ((ψ.symm.trans φ).trans ψ) (monoLogShellEquiv (p := p) ψ x) :=
  monoLogEquiv_unitsQEquiv ψ φ x

theorem unitsQEquiv_mem_monoLogShell (φ : G ≃ₜ* G) {x : unitsQ G} (hx : x ∈ monoLogShell G) :
    unitsQEquiv φ x ∈ monoLogShell G := by
  rw [← map_monoLogShell φ]
  exact ⟨x, hx, rfl⟩

/-! ### Log-volumes -/

variable (G) in
/-- **The group-theoretic log-volume of `𝓘(G)`**, `{−1 − m/f + e · log(p*)/log p} · log p / e`
(i.e. `μ^log(G)(𝓘(G)) / [k : ℚ_p]` with `F(G) ↔ f log p`, [AbsTopIII], Proposition 5.8 (iii)). -/
def monoLogVol : ℝ := recLogShellConst G * Real.log (recPrime G) / recE G

/-- `monoLogVol` is group-theoretic. -/
theorem monoLogVol_congr {G' : Type*} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    (φ : G ≃ₜ* G') : monoLogVol G = monoLogVol G' := by
  simp only [monoLogVol, recLogShellConst, recMExp, recMuPInf, recMu, recF, recE, recDeg,
    recPrime, charCountFun_congr φ]

theorem monoLogVol_gal :
    monoLogVol (Ω ≃ₐ[k] Ω) =
      logShellConst p (f p ℚ_[p] k) (e p ℚ_[p] k) (mExp p k) * Real.log p / e p ℚ_[p] k := by
  rw [monoLogVol, recLogShellConst_gal p, recPrime_gal p, recE_gal p]

/-- **[AbsTopIII], Proposition 5.8 (iii)**: the group-theoretic log-volume `monoLogVol G` is the
normalised Haar log-volume of the log-shell `Iut.logShell k p = monoLogEquiv ψ '' 𝓘(G)`, for every
isomorphism `ψ : G ≃ₜ* G_k` and every Haar measure on `k`. -/
theorem logVol_monoLogShell [ProperSpace k] [MeasurableSpace k] [BorelSpace k]
    (ψ : G ≃ₜ* (Ω ≃ₐ[k] Ω)) (μ : Measure k) [μ.IsAddLeftInvariant]
    (h0 : μ (Metric.closedBall 0 1) ≠ 0) (hfin : μ (Metric.closedBall 0 1) ≠ ⊤) :
    Real.log ((μ (monoLogEquiv (p := p) ψ '' monoLogShell G)).toReal /
        (μ (Metric.closedBall 0 1)).toReal) / Module.finrank ℚ_[p] k = monoLogVol G := by
  rw [image_monoLogEquiv, logVolume_logShell_eq_auto μ h0 hfin, monoLogVol_congr ψ,
    monoLogVol_gal (p := p)]

end Mono

end

end Iut.Reconstruction
