/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.ThetaLocalConstruct.Ordp

/-!
# Conjugate places have equal local invariants

For number fields `k ⊆ K` with `K/k` Galois, the Galois group `Gal(K/k)` acts transitively on
the places of `K` over a given finite place `w` of `k`. Conjugate places therefore have the same
local invariants over `ℚ`:

* `Iut.ramIdx_eq_of_liesOver`, `Iut.inertDeg_eq_of_liesOver`: the ramification index `e_v` and
  the residue degree `f_v` over the rational prime;
* `Iut.ordDifferent_eq_of_liesOver`, `Iut.differentExponent_eq_of_liesOver`: the exponent
  `ord_v(𝔡_{K/ℚ})` of the different and the different exponent `d_v = ord_v(𝔡_{K/ℚ})/e_v`,
  since the different ideal `𝔡_{K/ℚ}` is stable under every automorphism of `K`
  (`Iut.smul_differentIdeal`: the trace form is invariant).

This is the input of the averaging over the section `V ⊆ V(K)` (IUT III, Remark 3.1.1(ii)):
for `K/F_mod` Galois (IUT I, Remark 3.1.5), the local different `d_v` of IUT IV, Proposition 1.3
at the place `v ∈ V` over `w ∈ V_mod` is the common value at all the places of `K` over `w`.
-/

namespace Iut

open NumberField IsDedekindDomain
open scoped Pointwise nonZeroDivisors

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-! ### Invariance of the different ideal -/

section Different

/-- The membership predicate of the inverse of the dual of `𝓞_K`, i.e. of the different
`𝔡_{K/ℚ}` (`coeIdeal_differentIdeal`), is preserved by the automorphisms of `K`. -/
lemma mem_inv_dual_one_map (τ : K ≃ₐ[ℚ] K) {z : K}
    (hz : z ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))⁻¹) :
    τ z ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := one_ne_zero
  have hd : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ h1
  -- the automorphisms preserve `𝓞_K`
  have hint : ∀ (τ : K ≃ₐ[ℚ] K) (a : K), a ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) →
      τ a ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro τ a ha
    obtain ⟨b, rfl⟩ := FractionalIdeal.mem_one_iff _ |>.mp ha
    refine FractionalIdeal.mem_one_iff _ |>.mpr ⟨⟨τ b, ?_⟩, rfl⟩
    exact (b.2.map (τ.toAlgHom.restrictScalars ℤ))
  -- the automorphisms preserve the dual
  have hdual : ∀ (τ : K ≃ₐ[ℚ] K) (y : K),
      y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) →
      τ y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro τ y hy
    rw [FractionalIdeal.mem_dual h1] at hy ⊢
    intro a ha
    have := hy (τ.symm a) (hint τ.symm a ha)
    rw [Algebra.traceForm_apply] at this ⊢
    rwa [← Algebra.trace_eq_of_algEquiv τ, map_mul, AlgEquiv.apply_symm_apply] at this
  rw [FractionalIdeal.mem_inv_iff hd] at hz ⊢
  intro y hy
  have := hint τ _ (hz (τ.symm y) (hdual τ.symm y hy))
  rwa [map_mul, AlgEquiv.apply_symm_apply] at this

/-- **The different `𝔡_{K/ℚ}` is Galois-stable**: `σ·𝔡 = 𝔡` for `σ ∈ Gal(K/k)`. -/
theorem smul_differentIdeal [IsGalois k K] (σ : K ≃ₐ[k] K) :
    σ • differentIdeal ℤ (𝓞 K) = differentIdeal ℤ (𝓞 K) := by
  have key : ∀ σ : K ≃ₐ[k] K, ∀ x ∈ differentIdeal ℤ (𝓞 K),
      σ • x ∈ differentIdeal ℤ (𝓞 K) := by
    intro σ x hx
    have hx' : (x : K) ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
      rw [← coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)]
      exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨x, hx, rfl⟩
    have := mem_inv_dual_one_map (σ.restrictScalars ℚ) hx'
    rw [← coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)] at this
    obtain ⟨y, hy, hyx⟩ := (FractionalIdeal.mem_coeIdeal _).mp this
    have : y = σ • x := Subtype.ext hyx
    rwa [← this]
  have hle : ∀ σ : K ≃ₐ[k] K, σ • differentIdeal ℤ (𝓞 K) ≤ differentIdeal ℤ (𝓞 K) := by
    intro σ
    rw [Ideal.pointwise_smul_def, Ideal.map_le_iff_le_comap]
    exact fun x hx => key σ x hx
  refine le_antisymm (hle σ) ?_
  calc differentIdeal ℤ (𝓞 K) = σ • σ⁻¹ • differentIdeal ℤ (𝓞 K) := by rw [smul_inv_smul]
    _ ≤ σ • differentIdeal ℤ (𝓞 K) := smul_mono_right σ (hle σ⁻¹)

end Different

/-! ### Conjugate places -/

section Conjugate

variable [IsGalois k K]

/-- The Galois group acts transitively on the places over `w`: the prime of `v'` is
`σ·𝔭_v` for some `σ ∈ Gal(K/k)`. -/
theorem exists_smul_maximalIdeal_eq {w : FinitePlace k} {v v' : FinitePlace K}
    (hv : FinitePlace.LiesOver v w) (hv' : FinitePlace.LiesOver v' w) :
    ∃ σ : K ≃ₐ[k] K, σ • v.maximalIdeal.asIdeal = v'.maximalIdeal.asIdeal := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hv
  haveI : v'.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hv'
  exact Ideal.exists_smul_eq_of_isGaloisGroup w.maximalIdeal.asIdeal _ _ (K ≃ₐ[k] K)

/-- **Conjugate places have the same different exponent `ord_v(𝔡_{K/ℚ})`**. -/
theorem ordDifferent_eq_of_liesOver {w : FinitePlace k} {v v' : FinitePlace K}
    (hv : FinitePlace.LiesOver v w) (hv' : FinitePlace.LiesOver v' w) :
    ordDifferent K v = ordDifferent K v' := by
  obtain ⟨σ, hσ⟩ := exists_smul_maximalIdeal_eq hv hv'
  have hd : differentIdeal ℤ (𝓞 K) ≠ 0 := differentIdeal_ne_bot
  have hcount : ∀ u : FinitePlace K, ordDifferent K u =
      multiplicity u.maximalIdeal.asIdeal (differentIdeal ℤ (𝓞 K)) := by
    intro u
    unfold ordDifferent
    rw [UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime u.maximalIdeal.ne_bot u.maximalIdeal.isPrime).irreducible hd,
      normalize_eq]
  rw [hcount, hcount, ← hσ, ← multiplicity_map_eq
    (MulSemiringAction.toRingEquiv (K ≃ₐ[k] K) (Ideal (𝓞 K)) σ)]
  change multiplicity (σ • v.maximalIdeal.asIdeal) (σ • differentIdeal ℤ (𝓞 K)) = _
  rw [smul_differentIdeal]

/-- **Conjugate places have the same ramification index** `e_v` over `ℚ`. -/
theorem ramIdx_eq_of_liesOver {w : FinitePlace k} {v v' : FinitePlace K}
    (hv : FinitePlace.LiesOver v w) (hv' : FinitePlace.LiesOver v' w) :
    ramIdx K v = ramIdx K v' := by
  obtain ⟨σ, hσ⟩ := exists_smul_maximalIdeal_eq hv hv'
  unfold ramIdx
  rw [← hσ, Ideal.ramificationIdx_smul]

/-- **Conjugate places have the same residue degree** `f_v` over `ℚ`. -/
theorem inertDeg_eq_of_liesOver {w : FinitePlace k} {v v' : FinitePlace K}
    (hv : FinitePlace.LiesOver v w) (hv' : FinitePlace.LiesOver v' w) :
    inertDeg K v = inertDeg K v' := by
  obtain ⟨σ, hσ⟩ := exists_smul_maximalIdeal_eq hv hv'
  unfold inertDeg
  rw [← hσ, Ideal.inertiaDeg_smul]

/-- **Conjugate places have the same different exponent** `d_v = ord_v(𝔡_{K/ℚ})/e_v`
(IUT IV, Proposition 1.3). -/
theorem differentExponent_eq_of_liesOver {w : FinitePlace k} {v v' : FinitePlace K}
    (hv : FinitePlace.LiesOver v w) (hv' : FinitePlace.LiesOver v' w) :
    differentExponent K v = differentExponent K v' := by
  unfold differentExponent
  rw [ordDifferent_eq_of_liesOver hv hv', ramIdx_eq_of_liesOver hv hv']

end Conjugate

end Iut
