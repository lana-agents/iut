/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.SaturationTransport

/-!
# The `G_A / H_A`-actions of [FrdII], Theorem 2.4(i), group-theoretically

[FrdII], Definition 2.2 / Remark 2.2.1: the cup-product isomorphism
`H¹(H_A, μ_N(A)) ≅ H_A^ab ⊗ F_N(A)` is "compatible with the natural actions of `G_A/H_A` on its
domain and codomain"; Theorem 2.4(i): the isomorphisms induced by `Ψ` are compatible "with the
various natural actions of `(G₁)_{A₁}/(H₁)_{A₁}`, `(G₂)_{A₂}/(H₂)_{A₂}`".

In the group-theoretic setting of `KummerClass.lean` (`G` discrete, `U ⊴ G` commutative,
`H ≤ G`), an element `g ∈ G` normalising `H` acts on `H¹(H, μ_n(U))` and `H²(H, μ_n(U))` by
`(g·c)(h) = g · c(g⁻¹ h g)` (`KummerClass.conjH1`, `conjH2`). Here:

* **`KummerClass.kummerClass_conjU`**: the Kummer map is equivariant,
  `κ(g u g⁻¹) = g · κ(u)`;
* **`KummerClass.conjH1_of_mem`**: elements of `H` act trivially on `H¹(H, μ_n(U))`, so the action
  of the normaliser factors through its quotient by `H` (for `H = H_A`, `g ∈ G_A`: an action of
  `G_A / H_A`);
* **`KummerClass.kummerMap_conjH1`**: the transport `kummerMap` along `φ : G ≅ G'` is
  equivariant (`g ↦ φ g`);
* **`Saturation.h1Equiv_conjH1`**, **`Saturation.h2Equiv_conjH2`**: the isomorphisms
  `H^i(H_A, μ_n(U)) ≅ H^i(H'_{A'}, μ_n(U'))` of `SaturationTransport.lean` (those of
  Theorem 2.4(i)) are equivariant.
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

open scoped IsMulCommutative

namespace KummerClass

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (U : Subgroup G) [U.Normal] [IsMulCommutative U] (H : Subgroup G) (n : ℕ)

/-- `h ↦ g⁻¹ h g` on `H`, for `g` normalising `H`. -/
def conjSub (g : G) (hg : ∀ h ∈ H, g⁻¹ * h * g ∈ H) : H →* H where
  toFun h := ⟨g⁻¹ * h * g, hg h h.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[simp] lemma coe_conjSub (g : G) (hg : ∀ h ∈ H, g⁻¹ * h * g ∈ H) (h : H) :
    (conjSub H g hg h : G) = g⁻¹ * h * g := rfl

/-- `m ↦ g · m` on `μ_n(U)`. -/
def smulMu (g : G) : mu U n →* mu U n := MulDistribMulAction.toMonoidHom (mu U n) g

@[simp] lemma coe_smulMu (g : G) (m : mu U n) : ((smulMu U n g m : U) : G) = g * m * g⁻¹ := rfl

lemma smulMu_conjSub (g : G) (hg : ∀ h ∈ H, g⁻¹ * h * g ∈ H) (h : H) (m : mu U n) :
    smulMu U n g (conjSub H g hg h • m) = h • smulMu U n g m := by
  apply Subtype.ext; apply Subtype.ext
  change g * ((g⁻¹ * h * g) * m * (g⁻¹ * h * g)⁻¹) * g⁻¹ = (h : G) * (g * m * g⁻¹) * (h : G)⁻¹
  group

/-- **The action of `g` (normalising `H`) on `H¹(H, μ_n(U))`**: `(g·c)(h) = g · c(g⁻¹ h g)`. -/
noncomputable def conjH1 (g : G) (hg : ∀ h ∈ H, g⁻¹ * h * g ∈ H) :
    ContH1 H (mu U n) →* ContH1 H (mu U n) :=
  ContH1.map (conjSub H g hg) continuous_of_discreteTopology (smulMu U n g)
    continuous_of_discreteTopology (smulMu_conjSub U H n g hg)

/-- **The action of `g` (normalising `H`) on `H²(H, μ_n(U))`**. -/
noncomputable def conjH2 (g : G) (hg : ∀ h ∈ H, g⁻¹ * h * g ∈ H) :
    ContH2 H (mu U n) →* ContH2 H (mu U n) :=
  ContH2.map (conjSub H g hg) continuous_of_discreteTopology (smulMu U n g)
    (smulMu_conjSub U H n g hg)

omit [TopologicalSpace G] [DiscreteTopology G] [IsMulCommutative U] in
/-- The hypothesis of `kummerClass` for `g u g⁻¹`. -/
lemma fixed_conjU (g : G) (hg : ∀ h ∈ H, g⁻¹ * h * g ∈ H) (u : U)
    (hu : ∀ h ∈ H, conjU U h (u ^ n) = u ^ n) :
    ∀ h ∈ H, conjU U h (conjU U g u ^ n) = conjU U g u ^ n := by
  intro h hh
  have e : g * ((conjU U (g⁻¹ * h * g) (u ^ n) : U) : G) * g⁻¹ = g * ((u ^ n : U) : G) * g⁻¹ :=
    congrArg (fun v : U => g * (v : G) * g⁻¹) (hu _ (hg h hh))
  apply Subtype.ext
  rw [conjU_pow, coe_conjU, coe_conjU]
  rw [coe_conjU] at e
  calc h * (g * ((u ^ n : U) : G) * g⁻¹) * h⁻¹
      = g * ((g⁻¹ * h * g) * ((u ^ n : U) : G) * (g⁻¹ * h * g)⁻¹) * g⁻¹ := by group
    _ = _ := e

/-- **The Kummer map is equivariant**: `κ(g u g⁻¹) = g · κ(u)` for `g` normalising `H`. -/
theorem kummerClass_conjU (g : G) (hg : ∀ h ∈ H, g⁻¹ * h * g ∈ H) (u : U)
    (hu : ∀ h ∈ H, conjU U h (u ^ n) = u ^ n) :
    kummerClass U H n (conjU U g u) (fixed_conjU U H n g hg u hu) =
      conjH1 U H n g hg (kummerClass U H n u hu) := by
  rw [conjH1, kummerClass, kummerClass, ContH1.map_mk]
  congr 1
  refine Subtype.ext (funext fun h => ?_)
  apply Subtype.ext; apply Subtype.ext
  change ((kfun U H n (conjU U g u) (fixed_conjU U H n g hg u hu) h : U) : G) =
    g * ((kfun U H n u hu (conjSub H g hg h) : U) : G) * g⁻¹
  simp only [coe_kfun, Subgroup.coe_inv, coe_conjSub, coe_conjU]
  group

omit [TopologicalSpace G] [DiscreteTopology G] [U.Normal] [IsMulCommutative U] in
/-- Elements of `H` normalise `H`. -/
lemma normalises_self (g : H) : ∀ h ∈ H, (g : G)⁻¹ * h * g ∈ H :=
  fun _ hh => H.mul_mem (H.mul_mem (H.inv_mem g.2) hh) g.2

/-- **Elements of `H` act trivially on `H¹(H, μ_n(U))`**: `(h₀·c)(h) = c(h) · (h·c(h₀))/c(h₀)`. -/
theorem conjH1_of_mem (g : H) (c : ContH1 H (mu U n)) :
    conjH1 U H n g (normalises_self H g) c = c := by
  induction c using ContH1.induction_on with | h c => ?_
  rw [conjH1, ContH1.map_mk, ContH1.mk_eq_mk_iff]
  refine ⟨c g, fun h => ?_⟩
  have hc := ContH1.isMulCocycle₁ c
  have e1 : (conjSub H g (normalises_self H g) h : H) = g⁻¹ * (h * g) :=
    Subtype.ext (by simp [mul_assoc])
  have e2 : c (g⁻¹ * (h * g)) = g⁻¹ • (h • c g * c h) * c g⁻¹ := by
    rw [hc, hc]
  have e3 : g • c g⁻¹ * c g = 1 := by
    rw [← hc, mul_inv_cancel, ContH1.map_one_eq]
  have e4 : g • c g⁻¹ = (c g)⁻¹ := eq_inv_of_mul_eq_one_left e3
  have e5 : (g : G) • (g⁻¹ • (h • c g * c h)) = h • c g * c h := by
    change (g : G) • (((g⁻¹ : H) : G) • (h • c g * c h)) = _
    rw [← mul_smul]
    rw [show ((g : G) * ((g⁻¹ : H) : G)) = 1 by simp, one_smul]
  change h • c g / c g = (g : G) • (c (conjSub H g (normalises_self H g) h)) / c h
  rw [e1, e2, smul_mul', e5, show (g : G) • c g⁻¹ = g • c g⁻¹ from rfl, e4,
    mul_right_comm (h • c g) (c h), mul_div_cancel_right, div_eq_mul_inv]

section Naturality

variable {G' : Type*} [Group G'] [TopologicalSpace G'] [DiscreteTopology G']
variable {U' : Subgroup G'} [U'.Normal] [IsMulCommutative U'] {H' : Subgroup G'}

omit [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace G'] [DiscreteTopology G']
  [IsMulCommutative U] [IsMulCommutative U'] [U.Normal] [U'.Normal] in
/-- `φ g` normalises `H' = φ(H)`. -/
lemma normalises_map (φ : G ≃* G') (hH : H.map (φ : G →* G') = H') (g : G)
    (hg : ∀ h ∈ H, g⁻¹ * h * g ∈ H) : ∀ h ∈ H', (φ g)⁻¹ * h * φ g ∈ H' := by
  intro h hh
  obtain ⟨x, hx, rfl⟩ := (hH ▸ hh : h ∈ H.map (φ : G →* G'))
  rw [← hH]
  exact ⟨g⁻¹ * x * g, hg x hx, by simp⟩

/-- **The transport `kummerMap` along `φ` is equivariant.** -/
theorem kummerMap_conjH1 (φ : G ≃* G') (hU : ∀ u ∈ U, φ u ∈ U')
    (hH : H.map (φ : G →* G') = H') (g : G) (hg : ∀ h ∈ H, g⁻¹ * h * g ∈ H)
    (c : ContH1 H (mu U n)) :
    kummerMap U H n φ hU hH (conjH1 U H n g hg c) =
      conjH1 U' H' n (φ g) (normalises_map H φ hH g hg) (kummerMap U H n φ hU hH c) := by
  induction c using ContH1.induction_on with | h c => ?_
  simp only [conjH1, kummerMap, ContH1.map_mk]
  congr 1
  refine Subtype.ext (funext fun h => ?_)
  have e : (conjSub H g hg (subMap H φ hH h)) =
      subMap H φ hH (conjSub H' (φ g) (normalises_map H φ hH g hg) h) :=
    Subtype.ext (by
      change g⁻¹ * φ.symm h * g = φ.symm ((φ g)⁻¹ * h * φ g)
      simp)
  apply Subtype.ext; apply Subtype.ext
  change φ (g * ((c (conjSub H g hg (subMap H φ hH h)) : U) : G) * g⁻¹) =
    φ g * φ ((c (subMap H φ hH (conjSub H' (φ g) _ h)) : U) : G) * (φ g)⁻¹
  rw [e]
  simp

end Naturality

end KummerClass

namespace Saturation

open KummerClass

section Transport

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] {U : Subgroup G}
  [U.Normal] [IsMulCommutative U] {K : Type*} [Group K] [TopologicalSpace K] {j : K →* G}
  (H : Subgroup K) (n : ℕ)
variable {G' : Type*} [Group G'] [TopologicalSpace G'] [DiscreteTopology G'] {U' : Subgroup G'}
  [U'.Normal] [IsMulCommutative U'] {K' : Type*} [Group K'] [TopologicalSpace K'] {j' : K' →* G'}
variable (φ : G ≃* G') (hU : ∀ u, u ∈ U ↔ φ u ∈ U') (α : K ≃ₜ* K')
  (hjα : ∀ k, j' (α k) = φ (j k))

include hjα in
/-- `φ g` normalises `H'_{A'}` if `g` normalises `H_A`. -/
lemma normalises_subAG (g : G) (hg : ∀ h ∈ subAG j H, g⁻¹ * h * g ∈ subAG j H) :
    ∀ h ∈ subAG j' (H.map (α : K →* K')), (φ g)⁻¹ * h * φ g ∈ subAG j' (H.map (α : K →* K')) :=
  normalises_map (subAG j H) φ (map_subAG H φ α hjα) g hg

lemma subAEquiv_symm_conjSub (g : G) (hg : ∀ h ∈ subAG j H, g⁻¹ * h * g ∈ subAG j H)
    (x : subAG j' (H.map (α : K →* K'))) :
    (subAEquiv H φ α hjα).symm (conjSub _ (φ g) (normalises_subAG H φ α hjα g hg) x) =
      conjSub _ g hg ((subAEquiv H φ α hjα).symm x) := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [coe_subAEquiv, coe_conjSub, coe_conjSub, map_mul, map_mul, map_inv, ← coe_subAEquiv H φ α hjα,
    MulEquiv.apply_symm_apply]

/-- **`H¹(H_A, μ_n(U)) ≅ H¹(H'_{A'}, μ_n(U'))` is equivariant** ([FrdII], Theorem 2.4(i):
compatibility with the actions of `G_A / H_A`). -/
theorem h1Equiv_conjH1 (g : G) (hg : ∀ h ∈ subAG j H, g⁻¹ * h * g ∈ subAG j H)
    (c : ContH1 (subAG j H) (mu U n)) :
    h1Equiv H n φ hU α hjα (conjH1 U (subAG j H) n g hg c) =
      conjH1 U' (subAG j' (H.map (α : K →* K'))) n (φ g) (normalises_subAG H φ α hjα g hg)
        (h1Equiv H n φ hU α hjα c) := by
  induction c using ContH1.induction_on with | h c => ?_
  change ContH1.mk _ = ContH1.mk _
  congr 1
  refine Subtype.ext (funext fun x => ?_)
  apply Subtype.ext; apply Subtype.ext
  change φ (g * ((c (conjSub _ g hg ((subAEquiv H φ α hjα).symm x)) : U) : G) * g⁻¹) =
    φ g * φ ((c ((subAEquiv H φ α hjα).symm (conjSub _ (φ g) _ x)) : U) : G) * (φ g)⁻¹
  rw [subAEquiv_symm_conjSub H φ α hjα g hg]
  simp

/-- **`H²(H_A, μ_n(U)) ≅ H²(H'_{A'}, μ_n(U'))` is equivariant.** -/
theorem h2Equiv_conjH2 (g : G) (hg : ∀ h ∈ subAG j H, g⁻¹ * h * g ∈ subAG j H)
    (c : ContH2 (subAG j H) (mu U n)) :
    h2Equiv H n φ hU α hjα (conjH2 U (subAG j H) n g hg c) =
      conjH2 U' (subAG j' (H.map (α : K →* K'))) n (φ g) (normalises_subAG H φ α hjα g hg)
        (h2Equiv H n φ hU α hjα c) := by
  induction c using ContH2.induction_on with | h c => ?_
  change ContH2.mk _ = ContH2.mk _
  congr 1
  refine ContH2.cocycles_ext fun x y => ?_
  apply Subtype.ext; apply Subtype.ext
  change φ (g * ((c (conjSub _ g hg ((subAEquiv H φ α hjα).symm x),
      conjSub _ g hg ((subAEquiv H φ α hjα).symm y)) : U) : G) * g⁻¹) =
    φ g * φ ((c ((subAEquiv H φ α hjα).symm (conjSub _ (φ g) _ x),
      (subAEquiv H φ α hjα).symm (conjSub _ (φ g) _ y)) : U) : G) * (φ g)⁻¹
  rw [subAEquiv_symm_conjSub H φ α hjα g hg, subAEquiv_symm_conjSub H φ α hjα g hg]
  simp

end Transport

end Saturation

end Frobenioid

end Iut
