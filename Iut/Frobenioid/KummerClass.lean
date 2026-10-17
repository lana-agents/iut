/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.ContH1.Basic

/-!
# Kummer classes of a commutative normal subgroup ([FrdII], Definition 2.1(ii))

[FrdII], Definition 2.1(ii): for an object `A` of a Frobenioid, a subgroup `H_A` acting on
`O^▷(A)`, an element `f` fixed by `H_A` and an `N`-th root `g` (`g^N = f`), "`H_A` stabilizes the
subset `μ_N(A)·g` …, hence determines a cohomology class `κ_f ∈ H¹(H_A, μ_N(A))` which is easily
verified to be independent of the choice of `g`". This file carries this out group-theoretically
for a commutative normal subgroup `U` of a group `G` (for a Frobenioid: `U = O^×(A)` inside
`G = Aut_C(A)`, acting by conjugation; `KummerClassFrob.lean`), with `G` discrete:

* `KummerClass.mu U n`: `μ_n(U) = {u ∈ U : u^n = 1}`, with the conjugation action of `G`;
* `KummerClass.kummerClass U H n g hg ∈ ContH1 H (μ_n(U))`: the class of the cocycle
  `h ↦ (h g h⁻¹) g⁻¹`, for `g ∈ U` with `g^n` fixed by `H`;
* `kummerClass_eq_of_pow_eq`: **independence of the root** `g`;
* `map_kummerClass`: **naturality**: an isomorphism `φ : G ≅ G'` with `φ(U) ⊆ U'`, `φ(H) = H'`
  maps Kummer classes to Kummer classes (the "compatibility with the Kummer maps" of
  [FrdII], Theorem 2.4(i));
* `kfun_eq_of_mul_mem`: the cocycle only depends on `h` modulo the kernel of the action, so the
  class comes from the image `H_A` of `H` in `Aut(U)`.

`ContH1` is the continuous `H¹` of `continuous-kummer-theory` (for discrete `G` every cochain is
continuous), the same model as used by `local-class-field-theory` for local duality.
-/

namespace Iut

namespace Frobenioid

open scoped IsMulCommutative

/-- A type synonym carrying the discrete topology. -/
def WithDisc (α : Type*) : Type _ := α

namespace WithDisc

instance {α : Type*} [Group α] : Group (WithDisc α) := inferInstanceAs (Group α)
instance {α : Type*} : TopologicalSpace (WithDisc α) := ⊥
instance {α : Type*} : DiscreteTopology (WithDisc α) := ⟨rfl⟩

end WithDisc

namespace KummerClass

variable {G : Type*} [Group G]
variable (U : Subgroup G) [hUn : U.Normal] [IsMulCommutative U]

/-- `μ_n(U) = {u ∈ U : u^n = 1}`. -/
def mu (n : ℕ) : Subgroup U := (powMonoidHom n : U →* U).ker

omit hUn in
variable {U} in
lemma mem_mu {n : ℕ} {u : U} : u ∈ mu U n ↔ u ^ n = 1 := Iff.rfl

/-- Conjugation `u ↦ g u g⁻¹` on `U`. -/
def conjU (g : G) (u : U) : U := ⟨g * u * g⁻¹, hUn.conj_mem _ u.2 g⟩

omit [IsMulCommutative U] in
@[simp] lemma coe_conjU (g : G) (u : U) : (conjU U g u : G) = g * u * g⁻¹ := rfl

omit [IsMulCommutative U] in
lemma conjU_pow (g : G) (u : U) (n : ℕ) : conjU U g u ^ n = conjU U g (u ^ n) :=
  Subtype.ext (by simp [conj_pow])

omit [IsMulCommutative U] in
lemma conjU_div (g : G) (u v : U) : conjU U g (u / v) = conjU U g u / conjU U g v :=
  Subtype.ext (by simp only [coe_conjU, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]; group)

/-- The conjugation action of `G` on `μ_n(U)`. -/
instance (n : ℕ) : MulDistribMulAction G (mu U n) where
  smul g u := ⟨conjU U g u, by
    rw [mem_mu, conjU_pow, (mem_mu.mp u.2)]
    exact Subtype.ext (by simp)⟩
  one_smul u := Subtype.ext (Subtype.ext (by simp [HSMul.hSMul]))
  mul_smul g h u := Subtype.ext (Subtype.ext (by simp [HSMul.hSMul, mul_assoc]))
  smul_mul g u v := Subtype.ext (Subtype.ext (by simp [HSMul.hSMul, mul_assoc]))
  smul_one g := Subtype.ext (Subtype.ext (by simp [HSMul.hSMul]))

@[simp] lemma coe_smul_mu {n : ℕ} (g : G) (u : mu U n) :
    (((g • u : mu U n) : U) : G) = g * u * g⁻¹ := rfl

variable (H : Subgroup G) (n : ℕ)

/-- The Kummer cocycle `h ↦ (h g h⁻¹) g⁻¹ ∈ μ_n(U)` of `g ∈ U` with `g^n` fixed by `H`. -/
def kfun (g : U) (hg : ∀ h ∈ H, conjU U h (g ^ n) = g ^ n) (h : H) : mu U n :=
  ⟨conjU U h g / g, by
    rw [mem_mu, div_pow, conjU_pow, hg h h.2, div_self']⟩

@[simp] lemma coe_kfun (g : U) (hg : ∀ h ∈ H, conjU U h (g ^ n) = g ^ n) (h : H) :
    ((kfun U H n g hg h : U) : G) = h * g * h⁻¹ * (g : G)⁻¹ := by
  simp [kfun, div_eq_mul_inv]

lemma isMulCocycle₁_kfun (g : U) (hg : ∀ h ∈ H, conjU U h (g ^ n) = g ^ n) :
    groupCohomology.IsMulCocycle₁ (kfun U H n g hg) := fun a b => by
  apply Subtype.ext; apply Subtype.ext
  change (((kfun U H n g hg (a * b)) : U) : G) =
    (((a : G) • kfun U H n g hg b : mu U n) : U) * ((kfun U H n g hg a : U) : G)
  simp only [coe_kfun, coe_smul_mu, Subgroup.coe_mul, mul_inv_rev]
  group

variable [TopologicalSpace G] [DiscreteTopology G]

/-- **The Kummer class** `κ ∈ H¹(H, μ_n(U))` of `g` ([FrdII], Definition 2.1(ii)). -/
noncomputable def kummerClass (g : U) (hg : ∀ h ∈ H, conjU U h (g ^ n) = g ^ n) :
    ContH1 H (mu U n) :=
  ContH1.mk ⟨kfun U H n g hg, continuous_of_discreteTopology, isMulCocycle₁_kfun U H n g hg⟩

/-- **Independence of the root**: `N`-th roots with the same `N`-th power have the same Kummer
class. -/
theorem kummerClass_eq_of_pow_eq (g g' : U) (hg : ∀ h ∈ H, conjU U h (g ^ n) = g ^ n)
    (hg' : ∀ h ∈ H, conjU U h (g' ^ n) = g' ^ n) (hpow : g ^ n = g' ^ n) :
    kummerClass U H n g hg = kummerClass U H n g' hg' := by
  rw [kummerClass, kummerClass, ContH1.mk_eq_mk_iff]
  refine ⟨⟨g / g', by rw [mem_mu, div_pow, hpow, div_self']⟩, fun h => ?_⟩
  apply Subtype.ext
  change conjU U h (g / g') / (g / g') = conjU U h g / g / (conjU U h g' / g')
  rw [conjU_div, div_div_div_comm]

omit [TopologicalSpace G] [DiscreteTopology G] in
/-- The cocycle only depends on the class of `h` modulo the kernel of the conjugation action. -/
lemma kfun_eq_of_mul_mem (g : U) (hg : ∀ h ∈ H, conjU U h (g ^ n) = g ^ n) {h h' : H}
    (hk : ∀ u : U, conjU U ((h : G)⁻¹ * h') u = u) : kfun U H n g hg h = kfun U H n g hg h' := by
  have e : conjU U h' g = conjU U h g := by
    have := congrArg (conjU U (h : G)) (hk g)
    apply Subtype.ext
    have h2 := congrArg Subtype.val this
    simp only [coe_conjU] at h2 ⊢
    rw [← h2]
    group
  apply Subtype.ext
  change conjU U h g / g = conjU U h' g / g
  rw [e]

section Naturality

variable {G' : Type*} [Group G'] [TopologicalSpace G'] [DiscreteTopology G']
variable {U' : Subgroup G'} [U'.Normal] [IsMulCommutative U'] {H' : Subgroup G'}

/-- The map `μ_n(U) → μ_n(U')` induced by `φ` with `φ(U) ⊆ U'`. -/
def muMap (φ : G ≃* G') (hU : ∀ u ∈ U, φ u ∈ U') : mu U n →* mu U' n where
  toFun u := ⟨⟨φ u, hU _ u.1.2⟩, by
    rw [mem_mu]
    apply Subtype.ext
    have := congrArg (fun x : U => φ x) (mem_mu.mp u.2)
    simpa using this⟩
  map_one' := Subtype.ext (Subtype.ext (map_one φ))
  map_mul' a b := Subtype.ext (Subtype.ext (map_mul φ _ _))

/-- The map `H' → H` induced by `φ⁻¹` when `φ(H) = H'`. -/
def subMap (φ : G ≃* G') (hH : H.map (φ : G →* G') = H') : H' →* H where
  toFun h := ⟨φ.symm h, by
    obtain ⟨x, hx, e⟩ := (hH ▸ h.2 : (h : G') ∈ H.map (φ : G →* G'))
    rw [← e]
    simpa using hx⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

omit [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace G'] [DiscreteTopology G']
  [IsMulCommutative U] [IsMulCommutative U'] in
/-- The hypothesis of `kummerClass` is transported by `φ`. -/
lemma fixed_map (φ : G ≃* G') (hU : ∀ u ∈ U, φ u ∈ U') (hH : H.map (φ : G →* G') = H') (g : U)
    (hg : ∀ h ∈ H, conjU U h (g ^ n) = g ^ n) :
    ∀ h ∈ H', conjU U' h (⟨φ g, hU _ g.2⟩ ^ n) = ⟨φ g, hU _ g.2⟩ ^ n := by
  intro h hh
  obtain ⟨x, hx, rfl⟩ := (hH ▸ hh : h ∈ H.map (φ : G →* G'))
  have := congrArg (fun u : U => φ u) (hg x hx)
  apply Subtype.ext
  simpa [map_pow] using this

omit [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace G'] [DiscreteTopology G'] in
lemma muMap_smul (φ : G ≃* G') (hU : ∀ u ∈ U, φ u ∈ U') (hH : H.map (φ : G →* G') = H')
    (h : H') (m : mu U n) : muMap U n φ hU (subMap H φ hH h • m) = h • muMap U n φ hU m := by
  apply Subtype.ext; apply Subtype.ext
  change φ ((φ.symm h : G) * m * (φ.symm h : G)⁻¹) = (h : G') * φ m * (h : G')⁻¹
  simp

/-- The map `H¹(H, μ_n(U)) → H¹(H', μ_n(U'))` induced by `φ`. -/
noncomputable def kummerMap (φ : G ≃* G') (hU : ∀ u ∈ U, φ u ∈ U')
    (hH : H.map (φ : G →* G') = H') : ContH1 H (mu U n) →* ContH1 H' (mu U' n) :=
  ContH1.map (subMap H φ hH) continuous_of_discreteTopology (muMap U n φ hU)
    continuous_of_discreteTopology (muMap_smul U H n φ hU hH)

/-- **Naturality of Kummer classes** under `φ : G ≅ G'` with `φ(U) ⊆ U'` and `φ(H) = H'`. -/
theorem map_kummerClass (φ : G ≃* G') (hU : ∀ u ∈ U, φ u ∈ U')
    (hH : H.map (φ : G →* G') = H') (g : U) (hg : ∀ h ∈ H, conjU U h (g ^ n) = g ^ n)
    (hg' : ∀ h ∈ H', conjU U' h (⟨φ g, hU _ g.2⟩ ^ n) = ⟨φ g, hU _ g.2⟩ ^ n) :
    kummerMap U H n φ hU hH (kummerClass U H n g hg) =
      kummerClass U' H' n ⟨φ g, hU _ g.2⟩ hg' := by
  rw [kummerMap, kummerClass, ContH1.map_mk]
  congr 1
  apply Subtype.ext
  funext h
  apply Subtype.ext; apply Subtype.ext
  change φ (((kfun U H n g hg (subMap H φ hH h)) : U) : G) = _
  rw [coe_kfun, coe_kfun]
  change φ ((φ.symm h) * g * (φ.symm h)⁻¹ * (g : G)⁻¹) = _
  simp

end Naturality

end KummerClass

end Frobenioid

end Iut
