/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.SaturationTransport
import Iut.Frobenioid.GalHomCompat

/-!
# [FrdII], Theorem 2.4(i) for `C^⊢`: saturation, `H_A`, `F_N` under `Ψ`

[FrdII], Theorem 2.4(i): "`Ψ` maps `(N, H₁)`-saturated objects to `(N, H₂)`-saturated objects and
induces isomorphisms of monoids/modules […] `(H₁)_{A₁} ≅ (H₂)_{A₂}`; […]
`H¹((H₁)_{A₁}, μ_N(A₁)) ≅ H¹((H₂)_{A₂}, μ_N(A₂))`; `F_N(A₁) ≅ F_N(A₂)` […] compatible with the
respective Kummer and reciprocity maps […] as well as with the various natural actions".

For `Ψ : C^⊢(E) ≌ C^⊢(E')`, `α : G_E ≃ₜ* G_{E'}` from `exists_galHom_compat`, `X = (G_E/N, a)`:
the Galois structure of `Ψ(X)` is `jΨ = Ψ ∘ galHom ∘ α⁻¹ : G_{E'} → Aut(Ψ X)`, which acts on the
rational functions of the units of `Ψ X` by `σ' ↦ τ σ' τ⁻¹` (`exists_galHom_compat`). **`thm24`**:
if `X` is `(n, H)`-saturated, then `Ψ X` is `(n, α(H))`-saturated for `jΨ`, with
`F_N(X) ≅ F_N(Ψ X)` (`Saturation.fngEquiv`) and `H¹(H_A, μ_N(X)) ≅ H¹(α(H)_{Ψ X}, μ_N(Ψ X))`
(`Saturation.h1Equiv`), the latter mapping Kummer classes to Kummer classes
(`KummerClass.map_kummerClass`).
-/

namespace Iut

namespace Frobenioid

namespace PAdicGalois

open Saturation CategoryTheory

variable {p : ℕ} [hp : Fact p.Prime] {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- `IsSaturated` is the generic `Saturation.IsSat` for `(O^×(X), galHom, H)`. -/
lemma isSaturated_isSat (N : OpenNormalSubgroup (GK p E)) (a : gammaZ) (H : Subgroup (GK p E))
    (n : ℕ) (hs : IsSaturated N a H n) :
    IsSat (Model.ouAut (XN N a)) (galHom N a) (continuous_galHom N a) H n :=
  ⟨hs.muSat, hs.h1Mu, hs.h1Z, hs.h2Mu⟩

/-- `F_N(X)` is the generic `Saturation.FNG` for `(O^×(X), galHom, H)`. -/
noncomputable def fnEquivFNG (N : OpenNormalSubgroup (GK p E)) (a : gammaZ)
    (H : Subgroup (GK p E)) (n : ℕ) :
    FN N a H n ≃* FNG (Model.ouAut (XN N a)) (galHom N a) (continuous_galHom N a) H n :=
  MulEquiv.refl _

/-- The Galois structure `Ψ ∘ galHom ∘ α⁻¹ : G_{E'} → Aut(Ψ X)` of `Ψ X`. -/
noncomputable def jPsi (F : Frob p E ⥤ Frob p E') [F.IsEquivalence]
    (N : OpenNormalSubgroup (GK p E)) (a : gammaZ) (α : GK p E ≃ₜ* GK p E') :
    GK p E' →* WithDisc (Aut (F.obj (XN N a))) :=
  (Model.autEquiv F (XN N a)).toMonoidHom.comp ((galHom N a).comp (α.symm : GK p E' →* GK p E))

lemma continuous_jPsi (F : Frob p E ⥤ Frob p E') [F.IsEquivalence]
    (N : OpenNormalSubgroup (GK p E)) (a : gammaZ) (α : GK p E ≃ₜ* GK p E') :
    Continuous (jPsi F N a α) :=
  Continuous.comp (g := ⇑(Model.autEquiv F (XN N a))) continuous_of_discreteTopology
    ((continuous_galHom N a).comp α.symm.continuous)

lemma jPsi_apply (F : Frob p E ⥤ Frob p E') [F.IsEquivalence]
    (N : OpenNormalSubgroup (GK p E)) (a : gammaZ) (α : GK p E ≃ₜ* GK p E') (σ : GK p E) :
    jPsi F N a α (α σ) = Model.autEquiv F (XN N a) (galHom N a σ) := by
  simp [jPsi]

variable [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']

/-- `Ψ` restricts to `O^×(X) ≅ O^×(Ψ X)`. -/
lemma mem_ouAut_iff (F : Frob p E ⥤ Frob p E') [F.IsEquivalence] (X : Frob p E)
    (u : WithDisc (Aut X)) :
    u ∈ Model.ouAut X ↔ Model.autEquiv F X u ∈ Model.ouAut (F.obj X) :=
  Model.mem_ounits_iff F OrbitObj.baseHyp (GaloisModel.hasAllTorsion (torsion p E))
    OrbitObj.baseHyp (GaloisModel.hasAllTorsion (torsion p E')) (OrbitObj.isSlim isSlimGroup)
    (OrbitObj.isSlim isSlimGroup) (show Aut X from u).hom

/-- **[FrdII], Theorem 2.4(i), for `C^⊢`**: for `Ψ : C^⊢(E) ≌ C^⊢(E')` there is
`α : G_E ≃ₜ* G_{E'}` such that for every `X = (G_E/N, a)`: (1) the Galois structure
`jΨ = Ψ ∘ galHom ∘ α⁻¹` of `Ψ X` acts on rational functions of units by `σ' ↦ τ σ' τ⁻¹` for some
`τ`; (2) if `X` is `(n, H)`-saturated, then `Ψ X` is `(n, α(H))`-saturated for `jΨ`, and
`F_N(X) ≅ F_N(Ψ X)`. -/
theorem thm24 (F : Frob p E ⥤ Frob p E') [F.IsEquivalence] :
    ∃ α : GK p E ≃ₜ* GK p E', ∀ (N : OpenNormalSubgroup (GK p E)) (a : gammaZ),
      (∃ τ : GK p E', ∀ (σ' : GK p E') (v : Model.ouAut (F.obj (XN N a))),
        ratFunY (KummerClass.conjU (Model.ouAut (F.obj (XN N a))) (jPsi F N a α σ') v) =
          (τ * σ' * τ⁻¹) • ratFunY v) ∧
      ∀ (H : Subgroup (GK p E)) (n : ℕ), IsSaturated N a H n →
        IsSat (Model.ouAut (F.obj (XN N a))) (jPsi F N a α) (continuous_jPsi F N a α)
            (H.map (α : GK p E →* GK p E')) n ∧
          Nonempty (FN N a H n ≃* FNG (Model.ouAut (F.obj (XN N a))) (jPsi F N a α)
            (continuous_jPsi F N a α) (H.map (α : GK p E →* GK p E')) n) := by
  refine (exists_galHom_compat F).elim fun α hα => ?_
  refine ⟨α, fun N a => ⟨?_, fun H n hs => ?_⟩⟩
  · obtain ⟨τ, hτ⟩ := hα N a
    refine ⟨τ, fun σ' v => ?_⟩
    have h := hτ (α.symm σ') v
    rw [ContinuousMulEquiv.apply_symm_apply] at h
    exact h
  · have hjα : ∀ σ, jPsi F N a α (α σ) = Model.autEquiv F (XN N a) (galHom N a σ) :=
      jPsi_apply F N a α
    exact ⟨(isSaturated_isSat N a H n hs).transport (continuous_galHom N a) H n
        (continuous_jPsi F N a α) (Model.autEquiv F (XN N a)) (mem_ouAut_iff F (XN N a)) α hjα,
      ⟨(fnEquivFNG N a H n).trans (fngEquiv (continuous_galHom N a) H n
        (continuous_jPsi F N a α) (Model.autEquiv F (XN N a)) (mem_ouAut_iff F (XN N a)) α hjα)⟩⟩

end PAdicGalois

end Frobenioid

end Iut
