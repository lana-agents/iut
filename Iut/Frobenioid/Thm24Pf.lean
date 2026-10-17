/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.ReciprocityTransport
import Iut.Frobenioid.KummerTransportGalois
import Iut.Frobenioid.SaturationExists

/-!
# [FrdII], Theorem 2.4(i) for the perfected `p`-adic Frobenioid `C_v`

The files `KummerGalois.lean` … `KummerTransportGalois.lean` are stated for the Galois-model
Frobenioid `GFrob p E Γ` with an arbitrary divisor group `Γ ⊆ ℝ`; `Frob p E` (`C^⊢_v`, `Γ = ℤ`)
and `FrobPf p E` (`C_v`, `Γ = ℚ`, IUT I, Example 3.3(i)) are the cases `Γ = gammaZ`, `gammaQ`.
This file records the `C_v` versions of the main statements explicitly:

* `exists_isSaturatedPf`: `(n, H)`-saturated objects of `C_v` exist ([FrdII], Remark 2.2.1);
* **`thm24Pf`**: `Ψ : C_v(E) ≌ C_v(E')` maps `(n, H)`-saturated objects to `(n, α(H))`-saturated
  ones, with `F_N(X) ≅ F_N(Ψ X)`;
* `thm24Pf_recip`: compatibility with the reciprocity maps (`thm24_kummer_galois`, for the
  Galois-side Kummer classes, applies verbatim with `Γ = ℚ`).
-/

namespace Iut

namespace Frobenioid

namespace PAdicGalois

open Saturation CategoryTheory

variable {p : ℕ} [hp : Fact p.Prime] {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- **Existence of `(n, H)`-saturated objects of `C_v`** ([FrdII], Remark 2.2.1). -/
theorem exists_isSaturatedPf [FiniteDimensional ℚ_[p] E] (H : Subgroup (GK p E))
    (hH : IsOpen (H : Set (GK p E))) (n : ℕ) [NeZero n] :
    ∃ N₀ : OpenNormalSubgroup (GK p E), ∀ N : OpenNormalSubgroup (GK p E), N ≤ N₀ →
      ∀ a : gammaQ, IsSaturated N a H n :=
  exists_isSaturated H hH n

variable [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']

/-- **[FrdII], Theorem 2.4(i), for `C_v`**: for `Ψ : C_v(E) ≌ C_v(E')` there is
`α : G_E ≃ₜ* G_{E'}` such that for every `X = (G_E/N, a)`, the Galois structure
`jΨ = Ψ ∘ galHom ∘ α⁻¹` of `Ψ X` acts on rational functions of units through a conjugate of the
identity, and `(n, H)`-saturation of `X` implies `(n, α(H))`-saturation of `Ψ X`, with
`F_N(X) ≅ F_N(Ψ X)`. -/
theorem thm24Pf (F : FrobPf p E ⥤ FrobPf p E') [F.IsEquivalence] :
    ∃ α : GK p E ≃ₜ* GK p E', ∀ (N : OpenNormalSubgroup (GK p E)) (a : gammaQ),
      (∃ τ : GK p E', ∀ (σ' : GK p E') (v : Model.ouAut (F.obj (XN N a))),
        ratFunY (KummerClass.conjU (Model.ouAut (F.obj (XN N a))) (jPsi F N a α σ') v) =
          (τ * σ' * τ⁻¹) • ratFunY v) ∧
      ∀ (H : Subgroup (GK p E)) (n : ℕ), IsSaturated N a H n →
        IsSat (Model.ouAut (F.obj (XN N a))) (jPsi F N a α) (continuous_jPsi F N a α)
            (H.map (α : GK p E →* GK p E')) n ∧
          Nonempty (FN N a H n ≃* FNG (Model.ouAut (F.obj (XN N a))) (jPsi F N a α)
            (continuous_jPsi F N a α) (H.map (α : GK p E →* GK p E')) n) :=
  thm24 F

/-- **[FrdII], Theorem 2.4(i), reciprocity maps, for `C_v`** (`thm24_recip` with `Γ = ℚ`). -/
theorem thm24Pf_recip (F : FrobPf p E ⥤ FrobPf p E') [F.IsEquivalence]
    (α : GK p E ≃ₜ* GK p E') (N : OpenNormalSubgroup (GK p E)) (a : gammaQ)
    (H : Subgroup (GK p E)) (hH : IsOpen (H : Set (GK p E))) (n : ℕ) [NeZero n]
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
  thm24_recip N a H hH F α n hs κ χ

end PAdicGalois

end Frobenioid

end Iut
