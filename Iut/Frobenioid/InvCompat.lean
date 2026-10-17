/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.CupGeneric
import Iut.Frobenioid.SaturationTransport

/-!
# Compatibility of `H²(K, μ_n) ≅ ℤ/n` with isomorphisms of Galois pairs ([FrdII], Theorem 2.4(ii))

[FrdII], Theorem 2.4(ii) (proof): the natural isomorphisms `H²(G_i, μ(K̄_i^×)) ≅ ℚ/ℤ` "are
compatible with the isomorphism `H²(G₁, μ(K̄₁^×)) ≅ H²(G₂, μ(K̄₂^×))` induced by `Ψ`" — Mochizuki
argues via the Brauer group and the unramified quotient ([Mzk1], Proposition 1.2.1(vii)). Here we
isolate a cup-product criterion which reduces this compatibility to reciprocity:

**`PairCompat.h2MuEquiv_mapEquiv2`**: let `α : Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` and let
`β : μ_n(Ω) ≃* μ_n(Ω')` be `α`-equivariant (`K, K'` finite over `ℚ_p`), inducing
`Φ₁ : H¹(K, μ_n) ≅ H¹(K', μ_n)` and `Φ₂ : H²(K, μ_n) ≅ H²(K', μ_n)`. If for one character `χ`
and one class `ζ` the pairing value `⟨χ, ζ⟩ ∈ ℤ/n` is a unit and is preserved,
`⟨χ ∘ α⁻¹, Φ₁ ζ⟩ = ⟨χ, ζ⟩`, then `Φ₂` is compatible with the canonical isomorphisms
`PadicField.h2MuEquiv : H²(−, μ_n) ≅ ℤ/n`. (Proof: `Φ₂(χ ∪ ζ) = (χ ∘ α⁻¹) ∪ Φ₁ ζ` by naturality of
the cup product, `CupAux.map_cupH1G`, and `χ ∪ ζ` generates the cyclic group `H²(K, μ_n)`.)

For Kummer classes `ζ = κ(x)` the pairing is `χ(artin x)` (`PadicField.pairingH1_kummer`); with
`χ` unramified of order `n` and `x` a uniformiser this is a unit, so Theorem 2.4(ii) reduces to
`Φ₁(κ(x)) = κ(x')` with `v(x') = v(x)` and the preservation of unramified characters and Frobenius
under `α` (`Iut.Reconstruction.galEquiv_unrZHat`).
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

namespace CupAux

/-- Two homomorphisms to `ℤ/n`, the second bijective, agreeing on an element mapped to a unit,
are equal. -/
theorem eq_of_eq_on_unit {A : Type*} [Group A] {n : ℕ} [NeZero n]
    (f g : A →* Multiplicative (ZMod n)) (hg : Function.Injective g) (a₀ : A)
    (hu : IsUnit (Multiplicative.toAdd (g a₀))) (h : f a₀ = g a₀) (a : A) : f a = g a := by
  obtain ⟨u, hu⟩ := hu
  set k : ℕ := (Multiplicative.toAdd (g a) * (u⁻¹ : (ZMod n)ˣ)).val
  have hk : a = a₀ ^ k := by
    apply hg
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul, ← hu, ZMod.natCast_zmod_val, mul_assoc, Units.inv_mul,
      mul_one]
  rw [hk, map_pow, map_pow, h]

end CupAux

end Frobenioid

end Iut

namespace Iut.Frobenioid.PairCompat

open PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
variable {K' : Type*} [Field K'] [Algebra ℚ_[p] K'] [FiniteDimensional ℚ_[p] K']
variable {Ω' : Type*} [Field Ω'] [Algebra K' Ω'] [Algebra ℚ_[p] Ω'] [IsScalarTower ℚ_[p] K' Ω']
  [IsAlgClosed Ω'] [IsGalois K' Ω']
variable (n : ℕ) [NeZero n] (α : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω'))
  (β : KummerTheory.Mu n Ω ≃* KummerTheory.Mu n Ω')
  (hβ : ∀ (σ : Ω ≃ₐ[K] Ω) (ζ : KummerTheory.Mu n Ω), β (σ • ζ) = α σ • β ζ)

include hβ in
lemma smul_compat_symm (g : Ω' ≃ₐ[K'] Ω') (ζ : KummerTheory.Mu n Ω) :
    β (α.symm g • ζ) = g • β ζ := by
  rw [hβ, ContinuousMulEquiv.apply_symm_apply]

/-- `Φ₁ : H¹(K, μ_n) ≅ H¹(K', μ_n)` induced by `(α, β)`. -/
noncomputable def h1PairEquiv :
    ContH1 (Ω ≃ₐ[K] Ω) (KummerTheory.Mu n Ω) ≃* ContH1 (Ω' ≃ₐ[K'] Ω') (KummerTheory.Mu n Ω') :=
  ContH1Aux.mapEquiv α.symm β continuous_of_discreteTopology continuous_of_discreteTopology
    (smul_compat_symm n α β hβ)

/-- `Φ₂ : H²(K, μ_n) ≅ H²(K', μ_n)` induced by `(α, β)`. -/
noncomputable def h2PairEquiv : Brauer.H2Mu K Ω n ≃* Brauer.H2Mu K' Ω' n :=
  ContH2Aux.mapEquiv2 α.symm β (smul_compat_symm n α β hβ)

/-- A character of `Gal(Ω/K)` transported along `α`. -/
noncomputable def charPair (χ : Brauer.LocChar K Ω n) : Brauer.LocChar K' Ω' n :=
  ⟨χ.1.comp (α.symm : (Ω' ≃ₐ[K'] Ω') →* (Ω ≃ₐ[K] Ω)), χ.2.comp_continuous α.symm.continuous⟩

/-- **Naturality of the cup product** under `(α, β)`: `Φ₂(χ ∪ ζ) = (χ ∘ α⁻¹) ∪ Φ₁ ζ`. -/
theorem h2PairEquiv_cupH1 (χ : Brauer.LocChar K Ω n)
    (ζ : ContH1 (Ω ≃ₐ[K] Ω) (KummerTheory.Mu n Ω)) :
    h2PairEquiv n α β hβ (Brauer.cupH1 n χ ζ) =
      Brauer.cupH1 n (charPair n α χ) (h1PairEquiv n α β hβ ζ) := by
  rw [CupAux.cupH1_eq_cupH1G, CupAux.cupH1_eq_cupH1G]
  exact CupAux.map_cupH1G n _ _ _ _ χ.1 _ _ _ _ continuous_of_discreteTopology _ ζ

/-- **Compatibility of `H²(−, μ_n) ≅ ℤ/n` with `(α, β)`** (the reduction of [FrdII],
Theorem 2.4(ii), to reciprocity): if `⟨χ ∘ α⁻¹, Φ₁ ζ⟩ = ⟨χ, ζ⟩` for one pair `(χ, ζ)` with
`⟨χ, ζ⟩ ∈ (ℤ/n)^×`, then `h2MuEquiv ∘ Φ₂ = h2MuEquiv`. -/
theorem h2MuEquiv_mapEquiv2 (χ : Brauer.LocChar K Ω n)
    (ζ : ContH1 (Ω ≃ₐ[K] Ω) (KummerTheory.Mu n Ω))
    (hpair : pairingH1 (p := p) n (charPair n α χ) (h1PairEquiv n α β hβ ζ) =
      pairingH1 (p := p) n χ ζ)
    (hunit : IsUnit (pairingH1 (p := p) n χ ζ)) (c : Brauer.H2Mu K Ω n) :
    h2MuEquiv p K' Ω' (Nat.pos_of_ne_zero (NeZero.ne n)) (h2PairEquiv n α β hβ c) =
      h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n)) c := by
  refine CupAux.eq_of_eq_on_unit
    ((h2MuEquiv p K' Ω' (Nat.pos_of_ne_zero (NeZero.ne n))).toMonoidHom.comp
      (h2PairEquiv n α β hβ).toMonoidHom)
    (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n))).toMonoidHom
    (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n))).injective (Brauer.cupH1 n χ ζ) hunit ?_ c
  change h2MuEquiv p K' Ω' _ (h2PairEquiv n α β hβ (Brauer.cupH1 n χ ζ)) = _
  rw [h2PairEquiv_cupH1]
  apply Multiplicative.toAdd.injective
  exact hpair

end Iut.Frobenioid.PairCompat
