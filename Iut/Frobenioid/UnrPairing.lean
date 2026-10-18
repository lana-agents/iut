/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.InvCompat
import Iut.Reconstruction.Local.Valuation

/-!
# The unramified pairing value under isomorphisms of Galois pairs ([FrdII], Theorem 2.4(ii))

[FrdII], Theorem 2.4(ii) (proof): "the isomorphism `G₁ ≅ G₂` is automatically compatible with the
quotients `G_i ↠ G_i^unr`, as well as with the Frobenius elements ∈ `G_i^unr` [cf., e.g., [Mzk1],
Proposition 1.2.1, (ii), (iv)]". Here this is used through the pairing of `InvCompat.lean`:

* `unrChar_apply_of_mem_absInertia`, `unrChar_apply_of_frob`: the unramified character
  `PadicField.unrChar n c` kills the inertia subgroup and sends lifts of the Frobenius to `c`;
* **`artinChar_charPair_unrChar`**: for every isomorphism of topological groups
  `ψ : Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` the transported character `unrChar 1 ∘ ψ⁻¹` takes the value `1` on
  `artin(y)` for every `y ∈ K'^×` with `v(y) = 1` (inertia and Frobenius lifts are preserved by `ψ`:
  `Iut.Reconstruction.galEquiv_inertia`, `galEquiv_arithFrob`);
* `h1PairMap_kummer`: `Φ₁` maps the Kummer class of `a` to that of `a'` as soon as the Kummer
  cocycles of `n`-th roots correspond pointwise;
* **`pairing_unrChar_kummer`**: hence if `Φ₁(κ(π)) = κ(π')` with `v(π) = v(π') = 1`, the pairing
  value `⟨unrChar 1, κ(π)⟩ = 1` is preserved and is a unit — the hypotheses `hpair`, `hunit` of
  `PairCompat.h2MuEquiv_h2PairMap`.
-/

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.PairCompat

open PadicField Iut.Reconstruction Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]
variable {K' : Type*} [Field K'] [Algebra ℚ_[p] K'] [FiniteDimensional ℚ_[p] K']
variable {Ω' : Type*} [Field Ω'] [Algebra K' Ω'] [Algebra ℚ_[p] Ω'] [IsScalarTower ℚ_[p] K' Ω']
  [IsAlgClosed Ω'] [IsGalois K' Ω'] [Algebra.IsAlgebraic ℚ_[p] Ω']
variable (n : ℕ) [NeZero n]

/-- The unramified character kills the inertia subgroup. -/
theorem unrChar_apply_of_mem_absInertia (c : ZMod n) {τ : Ω ≃ₐ[K] Ω}
    (hτ : τ ∈ absInertia p K Ω) : (unrChar (p := p) (K := K) (Ω := Ω) n c).1 τ = 1 := by
  rw [unrChar_apply]
  have h1 : AlgEquiv.restrictNormalHom (unramifiedOfDegree p K Ω n) τ = 1 := by
    ext y
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.one_apply]
    rw [absInertia_eq] at hτ
    exact hτ ⟨(y : Ω), unramifiedOfDegree_le_maxUnramified p K Ω n y.2⟩
  rw [h1, map_one]

/-- The unramified character `unrChar c` sends every lift of the Frobenius to `c`. -/
theorem unrChar_apply_of_frob (c : ZMod n) {φ : Ω ≃ₐ[K] Ω}
    (hφ : (QuotientGroup.mk φ : (Ω ≃ₐ[K] Ω) ⧸ absInertia p K Ω) = arithFrob p K Ω) :
    (unrChar (p := p) (K := K) (Ω := Ω) n c).1 φ = Multiplicative.ofAdd c := by
  obtain ⟨π, hπ⟩ := exists_uniformizer (p := p) (K := K)
  have hπ0 : π ≠ 0 := hπ.ne_zero
  obtain ⟨φ₀, τ₀, hφ₀, hτ₀, hres⟩ := exists_restrict_eq_artin (p := p) (Ω := Ω) (Units.mk0 π hπ0)
  have hv : v p ((Units.mk0 π hπ0 : Kˣ) : K) = 1 := hπ
  rw [hv, zpow_one] at hres
  have h1 := artinChar_eq (p := p) n (unrChar (p := p) (K := K) (Ω := Ω) n c) _ _ hres
  rw [artinChar_unrChar n hv] at h1
  have h2 : (unrChar (p := p) (K := K) (Ω := Ω) n c).1 (φ₀ * τ₀) = Multiplicative.ofAdd c := by
    conv_rhs => rw [h1]
    rw [ofAdd_toAdd]
  rw [map_mul, unrChar_apply_of_mem_absInertia n c hτ₀, mul_one] at h2
  have h3 : φ₀⁻¹ * φ ∈ absInertia p K Ω := by
    rw [← QuotientGroup.eq, hφ, hφ₀]
  have h4 : φ = φ₀ * (φ₀⁻¹ * φ) := by group
  rw [h4, map_mul, h2, unrChar_apply_of_mem_absInertia n c h3, mul_one]

/-- **The transported unramified character on a uniformiser**: for every isomorphism of
topological groups `ψ : Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` and `y ∈ K'^×` with `v(y) = 1`,
`(unrChar 1 ∘ ψ⁻¹)(artin y) = 1`. -/
theorem artinChar_charPair_unrChar (ψ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) {y : K'ˣ}
    (hy : v p (y : K') = 1) :
    artinChar (p := p) n (charPair n ψ (unrChar (p := p) (K := K) (Ω := Ω) n 1)) y = 1 := by
  obtain ⟨φ', τ', hφ', hτ', hres⟩ := exists_restrict_eq_artin (p := p) (Ω := Ω') y
  rw [hy, zpow_one] at hres
  rw [artinChar_eq (p := p) n _ y _ hres]
  change Multiplicative.toAdd ((unrChar (p := p) (K := K) (Ω := Ω) n 1).1 (ψ.symm (φ' * τ'))) = 1
  have hφ : (QuotientGroup.mk (ψ.symm φ') : (Ω ≃ₐ[K] Ω) ⧸ absInertia p K Ω) =
      arithFrob p K Ω := by
    rw [← galEquiv_arithFrob p p ψ (ψ.symm φ'), ContinuousMulEquiv.apply_symm_apply]
    exact hφ'
  have hτ : ψ.symm τ' ∈ absInertia p K Ω := by
    rw [← galEquiv_inertia (p := p) (p' := p) ψ] at hτ'
    obtain ⟨t, ht, e⟩ := hτ'
    have e' : ψ.symm τ' = t := by
      rw [← e]
      exact ψ.symm_apply_apply t
    rw [e']
    exact ht
  rw [map_mul, map_mul, unrChar_apply_of_frob n 1 hφ, unrChar_apply_of_mem_absInertia n 1 hτ,
    mul_one, toAdd_ofAdd]

variable (ψ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω'))
  (β : KummerTheory.Mu n Ω →* KummerTheory.Mu n Ω')
  (hβ : ∀ (σ : Ω ≃ₐ[K] Ω) (ζ : KummerTheory.Mu n Ω), β (σ • ζ) = ψ σ • β ζ)

/-- `Φ₁` maps Kummer classes to Kummer classes when the Kummer cocycles of chosen `n`-th roots
correspond. -/
theorem h1PairMap_kummer [KummerTheory.HasKummerRoots n K Ω]
    [KummerTheory.HasKummerRoots n K' Ω'] {a : Kˣ} {a' : K'ˣ} (g : Ωˣ)
    (hg : g ^ n = Units.map (algebraMap K Ω : K →* Ω) a) (g' : Ω'ˣ)
    (hg' : g' ^ n = Units.map (algebraMap K' Ω' : K' →* Ω') a')
    (h : ∀ σ : Ω ≃ₐ[K] Ω, β (KummerTheory.kummerFun g (KummerTheory.smul_pow_of_pow_eq hg) σ) =
      KummerTheory.kummerFun g' (KummerTheory.smul_pow_of_pow_eq hg') (ψ σ)) :
    h1PairMap n ψ β hβ (KummerTheory.kummer n K Ω a) = KummerTheory.kummer n K' Ω' a' := by
  rw [KummerTheory.kummer_eq a g hg, KummerTheory.kummer_eq a' g' hg', h1PairMap,
    ContH1.map_mk]
  congr 1
  refine Subtype.ext (funext fun σ' => ?_)
  rw [ContH1.cocyclesMap_apply, KummerTheory.kummerCocycle_apply,
    KummerTheory.kummerCocycle_apply]
  have := h (ψ.symm σ')
  rw [ContinuousMulEquiv.apply_symm_apply] at this
  exact this

/-- **The pairing hypotheses of `h2MuEquiv_h2PairMap` from uniformisers**: if
`Φ₁(κ(π)) = κ(π')` with `v(π) = v(π') = 1`, then `⟨unrChar 1, κ(π)⟩` is a unit and is
preserved by `(ψ, β)`. -/
theorem pairing_unrChar_kummer [KummerTheory.HasKummerRoots n K Ω] {π : Kˣ}
    (hπ : v p (π : K) = 1) {π' : K'ˣ} (hπ' : v p (π' : K') = 1)
    (hk : h1PairMap n ψ β hβ (KummerTheory.kummer n K Ω π) =
      @KummerTheory.kummer n K' Ω' _ _ _ (hasKummerRoots (K := K') (Ω := Ω') n) _ π') :
    pairingH1 (p := p) n (charPair n ψ (unrChar (p := p) (K := K) (Ω := Ω) n 1))
        (h1PairMap n ψ β hβ (KummerTheory.kummer n K Ω π)) =
      pairingH1 (p := p) n (unrChar (p := p) (K := K) (Ω := Ω) n 1)
        (KummerTheory.kummer n K Ω π) ∧
    IsUnit (pairingH1 (p := p) n (unrChar (p := p) (K := K) (Ω := Ω) n 1)
      (KummerTheory.kummer n K Ω π)) := by
  have e1 : pairingH1 (p := p) n (unrChar (p := p) (K := K) (Ω := Ω) n 1)
      (KummerTheory.kummer n K Ω π) = 1 := by
    rw [pairingH1_kummer, artinChar_unrChar n hπ]
  refine ⟨?_, by rw [e1]; exact isUnit_one⟩
  rw [e1, hk, pairingH1_kummer, artinChar_charPair_unrChar n ψ hπ']

end Iut.Frobenioid.PairCompat
