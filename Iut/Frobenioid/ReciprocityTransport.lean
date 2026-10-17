/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.CupGeneric
import Iut.Frobenioid.Thm24Saturated

/-!
# Reciprocity maps under `Ψ` ([FrdII], Theorem 2.4(i))

[FrdII], Theorem 2.4(i): `Ψ` induces isomorphisms `H¹((H₁)_{A₁}, μ_N(A₁)) ≅ H¹((H₂)_{A₂}, μ_N(A₂))`,
`F_N(A₁) ≅ F_N(A₂)` "compatible with the respective Kummer and reciprocity maps"; the proof
appeals to the "manifestly group- or category-theoretic" construction of the reciprocity map
(Remark 2.2.1: the cup product `H¹(H_A, μ_N(A)) ≅ H_A^ab ⊗ F_N(A)`).

* `Saturation.recipG`: the group-theoretic reciprocity map for a datum `(U, j, H)`:
  `η(κ)(χ) = [χ ∪ κ] ∈ F_N`, with the generic cup product `CupAux.cupH1G` over `H_A`;
* **`Saturation.fngEquiv_recipG`**: the transport isomorphisms `F_N ≅ F_N'`, `H¹ ≅ H¹'`,
  `H_A ≅ H'_{A'}` of `SaturationTransport.lean` are compatible with `recipG`;
* **`PAdicGalois.recip_eq_recipG`**: for `C^⊢(E)`, the reciprocity map `recip` of
  `Reciprocity.lean` (cup product over `L = K̄^H` in local class field theory) *is* the
  group-theoretic `recipG` (naturality of the cup product, `CupAux.map_cupH1G`,
  `CupAux.cupH1_eq_cupH1G`);
* **`PAdicGalois.thm24_recip`**: for `Ψ : C^⊢(E) ≌ C^⊢(E')` and any `α : G_E ≃ₜ* G_{E'}` (e.g. the
  one of `thm24`), the isomorphism
  `F_N(X) ≅ F_N(Ψ X)` of `thm24` carries `recip κ χ` to
  `recipG (h1Equiv κ) (χ ∘ (H_A ≅ H'_{A'})⁻¹)`.
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

namespace Saturation

section RecipGen

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] (U : Subgroup G)
  [U.Normal] [IsMulCommutative U] {K : Type*} [Group K] [TopologicalSpace K] (j : K →* G)
  (hj : Continuous j) (H : Subgroup K) (n : ℕ) [NeZero n]

lemma mu_pow_eq_one (m : KummerClass.mu U n) : m ^ n = 1 :=
  Subtype.ext m.2

/-- The cup product `H¹(H_A, μ_n(U)) → H²(H_A, μ_n(U))`, `κ ↦ χ ∪ κ`. -/
noncomputable abbrev cupA (χ : subAG j H →* Multiplicative (ZMod n)) :
    ContH1 (subAG j H) (KummerClass.mu U n) →* ContH2 (subAG j H) (KummerClass.mu U n) :=
  CupAux.cupH1G n (mu_pow_eq_one U n) (fun _ => continuous_of_discreteTopology) χ
    continuous_of_discreteTopology

/-- **The reciprocity map** for the datum `(U, j, H)` ([FrdII], Remark 2.2.1): `κ ↦ η(κ)`,
`η(κ) ∈ H_A^ab ⊗ F_N ≅ Hom(H¹(H_A, ℤ/N), F_N)` given by `χ ↦ [χ ∪ κ]`. -/
noncomputable def recipG (κ : ContH1 (subAG j H) (KummerClass.mu U n))
    (χ : subAG j H →* Multiplicative (ZMod n)) : FNG U j hj H n :=
  QuotientGroup.mk (cupA U j H n χ κ)

end RecipGen

section RecipTransport

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] {U : Subgroup G}
  [U.Normal] [IsMulCommutative U] {K : Type*} [Group K] [TopologicalSpace K] {j : K →* G}
  (hj : Continuous j) (H : Subgroup K) (n : ℕ) [NeZero n]
variable {G' : Type*} [Group G'] [TopologicalSpace G'] [DiscreteTopology G'] {U' : Subgroup G'}
  [U'.Normal] [IsMulCommutative U'] {K' : Type*} [Group K'] [TopologicalSpace K'] {j' : K' →* G'}
  (hj' : Continuous j')
variable (φ : G ≃* G') (hU : ∀ u, u ∈ U ↔ φ u ∈ U') (α : K ≃ₜ* K')
  (hjα : ∀ k, j' (α k) = φ (j k))

lemma h2Equiv_cupA (χ : subAG j H →* Multiplicative (ZMod n))
    (κ : ContH1 (subAG j H) (KummerClass.mu U n)) :
    h2Equiv H n φ hU α hjα (cupA U j H n χ κ) =
      cupA U' j' (H.map (α : K →* K')) n
        (χ.comp ((subATEquiv H φ α hjα).symm : subAG j' (H.map (α : K →* K')) →* subAG j H))
        (h1Equiv H n φ hU α hjα κ) :=
  CupAux.map_cupH1G n _ _ _ _ χ _ _ _ _ continuous_of_discreteTopology _ κ

/-- **Compatibility with the reciprocity maps** ([FrdII], Theorem 2.4(i)): `F_N ≅ F_N'` maps
`η(κ)(χ)` to `η'(κ')(χ')` for `κ' = h1Equiv κ` and `χ' = χ ∘ (H_A ≅ H'_{A'})⁻¹`. -/
theorem fngEquiv_recipG (κ : ContH1 (subAG j H) (KummerClass.mu U n))
    (χ : subAG j H →* Multiplicative (ZMod n)) :
    fngEquiv hj H n hj' φ hU α hjα (recipG U j hj H n κ χ) =
      recipG U' j' hj' (H.map (α : K →* K')) n (h1Equiv H n φ hU α hjα κ)
        (χ.comp ((subATEquiv H φ α hjα).symm : subAG j' (H.map (α : K →* K')) →* subAG j H)) := by
  unfold recipG fngEquiv
  rw [QuotientGroup.congr_mk, h2Equiv_cupA]

end RecipTransport

end Saturation

namespace PAdicGalois

open Saturation CategoryTheory IntermediateField

variable {p : ℕ} [hp : Fact p.Prime] {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable {Γ : AddSubgroup ℝ}
variable (N : OpenNormalSubgroup (GK p E)) (a : Γ) (H : Subgroup (GK p E))
  (hH : IsOpen (H : Set (GK p E)))

/-- `F_N(X) ≅ H²(L, μ_N)` on classes: the composite of the maps along `Gal(K̄/L) ≅ H ↠ H_A` and
`μ_N(X) ≅ μ_N(K̄)`. -/
lemma fnEquivH2L_mk (n : ℕ) [NeZero n] (hs : IsSaturated N a H n)
    (y : ContH2 (subA N a H) (muX N a n)) :
    fnEquivH2L N a H hH n hs (QuotientGroup.mk y) =
      ContH2.map (galLA N a H hH) (continuous_galLA N a H hH) (uMu N a n)
        (uMu_smul_L N a H hH n) y := by
  induction y using ContH2.induction_on with | h c => ?_
  rfl

/-- **The reciprocity map of `Reciprocity.lean` (cup product over `L` in local class field
theory) is the group-theoretic one** (`Saturation.recipG`, cup product over `H_A`). -/
theorem recip_eq_recipG (n : ℕ) [NeZero n] (hs : IsSaturated N a H n)
    (κ : ContH1 (subA N a H) (muX N a n)) (χ : subA N a H →* Multiplicative (ZMod n)) :
    recip N a H hH n hs κ χ =
      recipG (Model.ouAut (XN N a)) (galHom N a) (continuous_galHom N a) H n κ χ := by
  refine ((fnEquivH2L N a H hH n hs).symm_apply_eq).mpr ?_
  refine (CupAux.cupH1_eq_cupH1G n _ _).trans ?_
  refine Eq.trans ?_ (fnEquivH2L_mk N a H hH n hs _).symm
  exact (CupAux.map_cupH1G n _ _ _ _ χ continuous_of_discreteTopology _ _ _
    continuous_of_discreteTopology _ κ).symm

variable {E' : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- **[FrdII], Theorem 2.4(i), reciprocity maps, for `C^⊢`**: for `Ψ : C^⊢(E) ≌ C^⊢(E')` and
`α : G_E ≃ₜ* G_{E'}` (with the Galois structure `jΨ = Ψ ∘ galHom ∘ α⁻¹` on `Ψ X`; `thm24` provides
the `α` induced by `Ψ`), the isomorphism `F_N(X) ≅ F_N(Ψ X)` maps the reciprocity class
`η(κ)(χ)` of `X` (cup product over `L = K̄^H`) to the reciprocity class of `Ψ X` for the transported
class `h1Equiv κ` and character `χ ∘ (H_A ≅ α(H)_{Ψ X})⁻¹`. -/
theorem thm24_recip [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']
    (F : GFrob p E Γ ⥤ GFrob p E' Γ) [F.IsEquivalence] (α : GK p E ≃ₜ* GK p E') (n : ℕ) [NeZero n]
    (hs : IsSaturated N a H n) (κ : ContH1 (subA N a H) (muX N a n))
    (χ : subA N a H →* Multiplicative (ZMod n)) :
    fngEquiv (continuous_galHom N a) H n (continuous_jPsi F N a α) (Model.autEquiv F (XN N a))
        (mem_ouAut_iff F (XN N a)) α (jPsi_apply F N a α) (recip N a H hH n hs κ χ) =
      recipG (Model.ouAut (F.obj (XN N a))) (jPsi F N a α) (continuous_jPsi F N a α)
        (H.map (α : GK p E →* GK p E')) n
        (h1Equiv H n (Model.autEquiv F (XN N a)) (mem_ouAut_iff F (XN N a)) α
          (jPsi_apply F N a α) κ)
        (χ.comp ((subATEquiv H (Model.autEquiv F (XN N a)) α (jPsi_apply F N a α)).symm :
          subAG (jPsi F N a α) (H.map (α : GK p E →* GK p E')) →* subA N a H)) :=
  (congrArg _ (recip_eq_recipG N a H hH n hs κ χ)).trans
    (fngEquiv_recipG (continuous_galHom N a) H n (continuous_jPsi F N a α)
      (Model.autEquiv F (XN N a)) (mem_ouAut_iff F (XN N a)) α (jPsi_apply F N a α) κ χ)

end PAdicGalois

end Frobenioid

end Iut
