/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.KummerH2

/-!
# Cyclotomic rigidity for `p`-adic fields (roadmap P17, M2)

[AbsTopIII], Proposition 3.2 (i) and Corollary 1.10 (i), (c): the natural isomorphism
`H²(G_K, μ_n) ≃ ℤ/n` (of roadmap P9, `PadicField.h2MuEquiv`) **rigidifies the cyclotome**: the
automorphisms of the `G_K`-module `μ_n` are the power maps `ζ ↦ ζ^a` (`a ∈ (ℤ/n)ˣ`), they act on
`H²(G_K, μ_n) ≃ ℤ/n` by multiplication by `a`, and therefore the identity is the only
automorphism of `μ_n` compatible with the isomorphism `H²(G_K, μ_n) ≃ ℤ/n`. This is the
"cyclotomic rigidity" that allows IUT to identify the cyclotome of a Frobenioid with the
cyclotome of the Galois group ([AbsTopIII], Remark 3.2.1; IUT I, Remark 1.9.2).

## Main results

* `Iut.Reconstruction.coeffMap α`: the map on `H²(G_K, μ_n)` induced by an endomorphism `α` of
  `μ_n` (every endomorphism of the cyclic group `μ_n` is `G_K`-equivariant,
  `Iut.Reconstruction.exists_pow_eq`);
* `Iut.Reconstruction.coeffMap_pow`: `(ζ ↦ ζ^a)_* = (·)^a`;
* `Iut.Reconstruction.h2MuEquiv_coeffMap`: `inv(α_* β) = a · inv(β)` for `α = (·)^a`;
* `Iut.Reconstruction.cyclotomic_rigidity`: an endomorphism `α` of `μ_n` with
  `inv ∘ α_* = inv` is the identity.
-/

open Brauer ContH2 KummerTheory PadicField

namespace Iut.Reconstruction

section Coefficients

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {n : ℕ} [NeZero n]

instance isCyclic_mu : IsCyclic (Mu n Ω) := inferInstanceAs (IsCyclic (rootsOfUnity n Ω))

/-- Every endomorphism of `μ_n` is a power map. -/
theorem exists_pow_eq (α : Mu n Ω →* Mu n Ω) : ∃ a : ℤ, ∀ ζ, α ζ = ζ ^ a :=
  MonoidHom.map_cyclic α

/-- Every endomorphism of `μ_n` is `Gal(Ω/K)`-equivariant. -/
theorem map_smul_mu (α : Mu n Ω →* Mu n Ω) (g : Ω ≃ₐ[K] Ω) (ζ : Mu n Ω) :
    α (g • ζ) = g • α ζ := by
  obtain ⟨a, ha⟩ := exists_pow_eq α
  rw [ha, ha, smul_zpow']

/-- The map `α_*` on `H²(Gal(Ω/K), μ_n)` induced by an endomorphism `α` of `μ_n`. -/
noncomputable def coeffMap (α : Mu n Ω →* Mu n Ω) : H2Mu K Ω n →* H2Mu K Ω n :=
  ContH2.map (MonoidHom.id _) continuous_id α (fun g ζ => map_smul_mu α g ζ)

theorem coeffMap_zpow (a : ℤ) (α : Mu n Ω →* Mu n Ω) (ha : ∀ ζ, α ζ = ζ ^ a)
    (β : H2Mu K Ω n) : coeffMap α β = β ^ a := by
  induction β using ContH2.induction_on with
  | h c =>
    rw [coeffMap, map_mk, ← map_zpow]
    congr 1
    refine cocycles_ext fun x y => ?_
    rw [cocyclesMap_apply, ha]
    rfl

theorem coeffMap_id (β : H2Mu K Ω n) : coeffMap (MonoidHom.id (Mu n Ω)) β = β := by
  rw [coeffMap_zpow 1 _ (fun ζ => by simp), zpow_one]

end Coefficients

section Rigidity

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
variable {n : ℕ} [NeZero n] (hn : 0 < n)

/-- **The cyclotome acts on `H² ≃ ℤ/n` through multiplication**: for `α = (ζ ↦ ζ^a)`,
`inv(α_* β) = a · inv(β)`. -/
theorem h2MuEquiv_coeffMap (a : ℤ) (α : Mu n Ω →* Mu n Ω) (ha : ∀ ζ, α ζ = ζ ^ a)
    (β : H2Mu K Ω n) :
    Multiplicative.toAdd (h2MuEquiv p K Ω hn (coeffMap α β)) =
      (a : ZMod n) * Multiplicative.toAdd (h2MuEquiv p K Ω hn β) := by
  rw [coeffMap_zpow a α ha, map_zpow, toAdd_zpow, zsmul_eq_mul]

/-- **Cyclotomic rigidity** ([AbsTopIII], Proposition 3.2 (i); Corollary 1.10 (c)): an
endomorphism of the cyclotome `μ_n` compatible with the natural isomorphism
`H²(G_K, μ_n) ≃ ℤ/n` is the identity. -/
theorem cyclotomic_rigidity (α : Mu n Ω →* Mu n Ω)
    (h : ∀ β : H2Mu K Ω n, h2MuEquiv p K Ω hn (coeffMap α β) = h2MuEquiv p K Ω hn β) :
    α = MonoidHom.id _ := by
  obtain ⟨a, ha⟩ := exists_pow_eq α
  obtain ⟨β, hβ⟩ := (h2MuEquiv p K Ω hn).surjective (Multiplicative.ofAdd 1)
  have h1 := h2MuEquiv_coeffMap (p := p) hn a α ha β
  rw [h β, hβ, toAdd_ofAdd, mul_one] at h1
  -- `a ≡ 1 mod n`, so `α = id` on `μ_n`
  have ha1 : ((a - 1 : ℤ) : ZMod n) = 0 := by push_cast; rw [← h1]; ring
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 ha1
  ext ζ : 1
  rw [ha, MonoidHom.id_apply]
  have hζ : ζ ^ (n : ℤ) = 1 := by
    rw [zpow_natCast]
    exact Mu.ext (by rw [map_pow, Mu.val_pow_n, map_one])
  calc ζ ^ a = ζ ^ ((a - 1) + 1) := by rw [sub_add_cancel]
    _ = (ζ ^ (n : ℤ)) ^ c * ζ := by rw [hc, zpow_add, zpow_mul, zpow_one]
    _ = ζ := by rw [hζ, one_zpow, one_mul]

end Rigidity

end Iut.Reconstruction
