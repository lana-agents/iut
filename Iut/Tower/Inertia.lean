/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.Basic

/-!
# The inertia criterion for `e(v/u) = 1`

For a Galois extension `K/k` of number fields and a place `v` of `K` over `u` of `k`, the
ramification index `e(v/u)` is the order of the inertia group
`I_v = {σ ∈ Gal(K/k) | σ x ≡ x mod 𝔓_v for all x ∈ 𝓞_K}` (Mathlib's
`Ideal.card_inertia_eq_ramificationIdxIn`). Hence `e(v/u) = 1` as soon as every `σ ∈ I_v` is
the identity (`Iut.relRamIdx_eq_one_of_inertia_trivial`).

The inertia condition is transported from `𝓞_K` to the `v`-integral elements of `K`
(`Iut.valuation_sub_lt_one_of_mem_inertia`): `x = n/d` with `d ∉ 𝔓_v`.
-/

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The action of `σ ∈ Gal(K/k)` on `𝓞_K`, on coordinates. -/
lemma coe_galSmul (σ : K ≃ₐ[k] K) (x : 𝓞 K) : ((σ • x : 𝓞 K) : K) = σ (x : K) := rfl

/-- **The inertia condition on `v`-integral elements**: if `σ x − x ∈ 𝔓_v` for all
`x ∈ 𝓞_K`, then `v(σ x − x) < 1` for every `x ∈ K` with `v(x) ≤ 1`. -/
lemma valuation_sub_lt_one_of_mem_inertia (v : FinitePlace K) (σ : K ≃ₐ[k] K)
    (hσ : σ ∈ v.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K)) (x : K)
    (hx : v.maximalIdeal.valuation K x ≤ 1) :
    v.maximalIdeal.valuation K (σ x - x) < 1 := by
  set w := v.maximalIdeal
  obtain ⟨n, d, hnd⟩ := exists_primeCompl_mul_eq_of_integer w x hx
  have hd0 : (d : 𝓞 K) ≠ 0 := fun h => d.2 (by rw [h]; exact w.asIdeal.zero_mem)
  have hd0' : (algebraMap (𝓞 K) K d) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  have hmem : ∀ y : 𝓞 K, w.valuation K (σ (y : K) - y) < 1 := by
    intro y
    have h := hσ y
    rw [Submodule.mem_toAddSubgroup] at h
    have : (σ (y : K) - y) = algebraMap (𝓞 K) K (σ • y - y) := by
      rw [map_sub]; rfl
    rw [this, valuation_lt_one_iff_mem]
    exact h
  have hdval : w.valuation K (algebraMap (𝓞 K) K d) = 1 :=
    (valuation_eq_one_iff_notMem w).mpr d.2
  have hσd : w.valuation K (σ (algebraMap (𝓞 K) K d)) = 1 := by
    have h1 := hmem d
    have : σ (algebraMap (𝓞 K) K d) = (σ (algebraMap (𝓞 K) K d) - algebraMap (𝓞 K) K d) +
      algebraMap (𝓞 K) K d := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ (by rw [hdval]; exact h1), hdval]
  have hσd0 : σ (algebraMap (𝓞 K) K d) ≠ 0 := by
    intro h; rw [h, map_zero] at hσd; exact zero_ne_one hσd
  have hx' : x = algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K d := by
    rw [eq_div_iff hd0']; exact hnd
  have key : σ x - x = ((σ (algebraMap (𝓞 K) K n) - algebraMap (𝓞 K) K n) *
      algebraMap (𝓞 K) K d - algebraMap (𝓞 K) K n *
      (σ (algebraMap (𝓞 K) K d) - algebraMap (𝓞 K) K d)) /
      (σ (algebraMap (𝓞 K) K d) * algebraMap (𝓞 K) K d) := by
    rw [hx', map_div₀]
    field_simp
    ring
  rw [key, map_div₀, map_mul, hσd, hdval, one_mul, div_one]
  refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
  · rw [map_mul, hdval, mul_one]; exact hmem n
  · rw [map_mul]
    calc w.valuation K (algebraMap (𝓞 K) K n) * w.valuation K
          (σ (algebraMap (𝓞 K) K d) - algebraMap (𝓞 K) K d)
        ≤ 1 * w.valuation K (σ (algebraMap (𝓞 K) K d) - algebraMap (𝓞 K) K d) :=
          mul_le_mul_left (valuation_le_one w n) _
      _ < 1 := by rw [one_mul]; exact hmem d

variable [IsGalois k K]

/-- **The inertia criterion**: `e(v/u) = 1` if every `σ ∈ Gal(K/k)` with `v(σ x − x) < 1` for
all `v`-integral `x` is the identity. -/
theorem relRamIdx_eq_one_of_inertia_trivial {v : FinitePlace K} {u : FinitePlace k}
    (hvu : FinitePlace.LiesOver v u)
    (hfix : ∀ σ : K ≃ₐ[k] K, (∀ x : K, v.maximalIdeal.valuation K x ≤ 1 →
      v.maximalIdeal.valuation K (σ x - x) < 1) → σ = 1) :
    relRamIdx v u = 1 := by
  haveI : v.maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal := hvu
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[k] K)
    u.maximalIdeal.asIdeal v.maximalIdeal.asIdeal
  have h2 := Ideal.ramificationIdxIn_eq_ramificationIdx u.maximalIdeal.asIdeal
    v.maximalIdeal.asIdeal (K ≃ₐ[k] K)
  have hpS : u.maximalIdeal.asIdeal.map (algebraMap (𝓞 k) (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective algebraMap_ringOfIntegers_injective]
    exact u.maximalIdeal.ne_bot
  have h3 := Ideal.ramificationIdx'_eq_ramificationIdx' u.maximalIdeal.asIdeal
    v.maximalIdeal.asIdeal hpS
  have h4 : v.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K) = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    exact hfix σ (valuation_sub_lt_one_of_mem_inertia v σ hσ)
  change u.maximalIdeal.asIdeal.ramificationIdx' v.maximalIdeal.asIdeal = 1
  rw [h3, ← h2, ← h1, Subgroup.card_eq_one, h4]

end Iut
