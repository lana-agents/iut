/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.Unramified
import Iut.Tower.InertiaBound

/-!
# Inertia acts unipotently on the prime-to-`p` torsion of a Legendre curve at a bad place

For a Legendre curve `E_μ` over a number field `k`, a Galois extension `K/k` and a place `v` of
`K` of odd residue characteristic at which `μ` is not a unit or `μ − 1` is not a unit, an element
`σ` of the inertia group of `v` satisfies `σ^n Q = Q` for every `n`-torsion point `Q ∈ E_μ(K)`
(`n` odd, prime to the residue characteristic), provided `σ` fixes square roots `√−1` and `√μ`
in `K` (`Iut.iterate_map_eq_self_of_inertia`): the Legendre model of `μ`, `1 − μ` or `1/μ` is a
model with multiplicative reduction at `v`, related to `E_μ` by the changes of variables
`⟨√−1, 1, 0, 0⟩`, `⟨√μ, 0, 0, 0⟩`, and `Iut.MultKernel.iterate_map_eq_self` applies.
-/

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WeierstrassCurve
  WeierstrassCurve.Affine Iut.Tripod

open scoped Classical

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The Legendre coefficients of `E_μ` base changed to `K`. -/
lemma legendreCoeffs_baseChange (μ₀ : k) :
    (Affine.baseChange (legendre μ₀) K).a₁ = 0 ∧
    (Affine.baseChange (legendre μ₀) K).a₂ = -(1 + algebraMap k K μ₀) ∧
    (Affine.baseChange (legendre μ₀) K).a₃ = 0 ∧
    (Affine.baseChange (legendre μ₀) K).a₄ = algebraMap k K μ₀ ∧
    (Affine.baseChange (legendre μ₀) K).a₆ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change algebraMap k K (legendre μ₀).a₁ = 0
    simp [legendre]
  · change algebraMap k K (legendre μ₀).a₂ = _
    simp [legendre]
  · change algebraMap k K (legendre μ₀).a₃ = 0
    simp [legendre]
  · change algebraMap k K (legendre μ₀).a₄ = _
    simp [legendre]
  · change algebraMap k K (legendre μ₀).a₆ = 0
    simp [legendre]

set_option maxHeartbeats 1000000 in
/-- **Inertia acts unipotently on the prime-to-`p` torsion at a bad place**: for `σ` in the
inertia group of `v` (odd residue characteristic), fixing `√−1` and `√μ`, and an `n`-torsion
point `Q` of `E_μ(K)` (`n` odd, `v(n) = 1`), `σ^n Q = Q` when `v(μ) ≠ 1` or `v(μ − 1) ≠ 1`. -/
theorem iterate_map_eq_self_of_inertia (μ₀ : k) (v : FinitePlace K) (h2 : residueChar v ≠ 2)
    {n : ℕ} (hodd : Odd n) (hn : v.maximalIdeal.valuation K (n : K) = 1)
    (hbad : v.maximalIdeal.valuation K (algebraMap k K μ₀) ≠ 1 ∨
      v.maximalIdeal.valuation K (algebraMap k K μ₀ - 1) ≠ 1)
    (σ : K ≃ₐ[k] K) (hσ : σ ∈ v.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K))
    {i u : K} (hi : i ^ 2 = -1) (hu : u ^ 2 = algebraMap k K μ₀) (hσi : σ i = i) (hσu : σ u = u)
    (Q : (Affine.baseChange (legendre μ₀) K).Point) (hQ : n • Q = 0) :
    (⇑(Point.map (W' := legendre μ₀) (S := k) (σ : K →ₐ[k] K)))^[n] Q = Q := by
  set vK := v.maximalIdeal.valuation K with hvK
  set μ : K := algebraMap k K μ₀ with hμ_def
  have h2' : vK 2 = 1 := valuation_two_eq_one v h2
  have hσ' : ∀ z : K, vK z ≤ 1 → vK (σ z - z) < 1 := fun z hz =>
    valuation_sub_lt_one_of_mem_inertia hσ hz
  have hvσ : ∀ z : K, vK (σ z) = vK z := fun z => valuation_map_eq_of_mem_inertia hσ z
  obtain ⟨hE₁, hE₂, hE₃, hE₄, hE₆⟩ := legendreCoeffs_baseChange (K := K) μ₀
  have hφ : ∀ (a b : K) (h : (Affine.baseChange (legendre μ₀) K).Nonsingular a b),
      ∃ h' : (Affine.baseChange (legendre μ₀) K).Nonsingular (σ a) (σ b),
        Point.map (W' := legendre μ₀) (S := k) (σ : K →ₐ[k] K) (Point.some a b h) =
          Point.some (σ a) (σ b) h' :=
    fun a b h => ⟨_, Point.map_some _ h⟩
  have hψ : ReductionKernel.DivPolyHyp (Affine.baseChange (legendre μ₀) K) := by
    rw [eq_legendre_of_coeffs hE₁ hE₂ hE₃ hE₄ hE₆]
    exact divPolyLegendreHyp _ _
  rcases lt_trichotomy (vK μ) 1 with hμ | hμ | hμ
  · -- `v(μ) < 1`: the Legendre model itself
    exact MultKernel.iterate_map_eq_self vK hE₁ hE₂ hE₃ hE₄ hE₆ (σ : K →+* K) hμ h2'
      (σ.commutes _) hσ' hvσ hψ hodd hn _ hφ Q hQ
  · -- `v(μ) = 1`, so `v(μ − 1) < 1`: the model `E_{1−μ} = ⟨√−1, 1, 0, 0⟩ • E_μ`
    have hμ1 : vK (1 - μ) < 1 := by
      have hne : vK (μ - 1) ≠ 1 := by
        rcases hbad with hb | hb
        · exact absurd hμ hb
        · exact hb
      have hle : vK (μ - 1) ≤ 1 :=
        (Valuation.map_sub _ _ _).trans (max_le hμ.le (by rw [map_one]))
      rw [Valuation.map_sub_swap]
      exact lt_of_le_of_ne hle hne
    have hi0 : i ≠ 0 := fun h0 => by
      rw [h0, zero_pow two_ne_zero, eq_comm, neg_eq_zero] at hi
      exact one_ne_zero hi
    set C : VariableChange K := ⟨Units.mk0 i hi0, 1, 0, 0⟩ with hC
    obtain ⟨hC₁, hC₂, hC₃, hC₄, hC₆⟩ := legendreCoeffs_vc_one_sub hE₁ hE₂ hE₃ hE₄ hE₆ hi hi0
    set e := Anabelian.vcEquiv C (Affine.baseChange (legendre μ₀) K) with he
    set φ' := e.toAddMonoidHom.comp
      ((Point.map (W' := legendre μ₀) (S := k) (σ : K →ₐ[k] K)).comp e.symm.toAddMonoidHom)
      with hφ'
    have hφ'' := exists_vcEquiv_map_eq C (Affine.baseChange (legendre μ₀) K) (σ : K →+* K)
      (by rw [hC]; exact hσi) (by rw [hC]; exact map_one _) (by rw [hC]; exact map_zero _)
      (by rw [hC]; exact map_zero _) _ hφ
    have hψ' : ReductionKernel.DivPolyHyp (C • Affine.baseChange (legendre μ₀) K) := by
      rw [eq_legendre_of_coeffs hC₁ hC₂ hC₃ hC₄ hC₆]
      exact divPolyLegendreHyp _ _
    have hQ' : n • e Q = 0 := by rw [← map_nsmul, hQ, map_zero]
    have := MultKernel.iterate_map_eq_self vK hC₁ hC₂ hC₃ hC₄ hC₆ (σ : K →+* K) hμ1 h2'
      (by change σ (1 - μ) = 1 - μ; rw [map_sub, map_one, hμ_def, σ.commutes]) hσ' hvσ hψ' hodd
      hn φ' hφ'' (e Q) hQ'
    rw [hφ', iterate_conj] at this
    exact e.injective this
  · -- `v(μ) > 1`: the model `E_{1/μ} = ⟨√μ, 0, 0, 0⟩ • E_μ`
    have hμ0 : μ ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hμ
      exact absurd hμ (not_lt.mpr zero_le_one)
    have hμ1 : vK μ⁻¹ < 1 := by
      rw [map_inv₀, inv_lt_one₀ (lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr
        hμ0)))]
      exact hμ
    have hu0 : u ≠ 0 := fun h0 => hμ0 (by rw [← hu, h0, zero_pow two_ne_zero])
    set C : VariableChange K := ⟨Units.mk0 u hu0, 0, 0, 0⟩ with hC
    obtain ⟨hC₁, hC₂, hC₃, hC₄, hC₆⟩ := legendreCoeffs_vc_inv hE₁ hE₂ hE₃ hE₄ hE₆ hu hu0
    set e := Anabelian.vcEquiv C (Affine.baseChange (legendre μ₀) K) with he
    set φ' := e.toAddMonoidHom.comp
      ((Point.map (W' := legendre μ₀) (S := k) (σ : K →ₐ[k] K)).comp e.symm.toAddMonoidHom)
      with hφ'
    have hφ'' := exists_vcEquiv_map_eq C (Affine.baseChange (legendre μ₀) K) (σ : K →+* K)
      (by rw [hC]; exact hσu) (by rw [hC]; exact map_zero _) (by rw [hC]; exact map_zero _)
      (by rw [hC]; exact map_zero _) _ hφ
    have hψ' : ReductionKernel.DivPolyHyp (C • Affine.baseChange (legendre μ₀) K) := by
      rw [eq_legendre_of_coeffs hC₁ hC₂ hC₃ hC₄ hC₆]
      exact divPolyLegendreHyp _ _
    have hQ' : n • e Q = 0 := by rw [← map_nsmul, hQ, map_zero]
    have := MultKernel.iterate_map_eq_self vK hC₁ hC₂ hC₃ hC₄ hC₆ (σ : K →+* K) hμ1 h2'
      (by change σ μ⁻¹ = μ⁻¹; rw [map_inv₀, hμ_def, σ.commutes]) hσ' hvσ hψ' hodd hn φ' hφ''
      (e Q) hQ'
    rw [hφ', iterate_conj] at this
    exact e.injective this

end Iut
