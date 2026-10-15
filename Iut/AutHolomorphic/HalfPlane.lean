/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Oka.Uniformization.HalfPlaneAut

/-!
# The Aut-holomorphic disc ([AbsTopIII], Proposition 2.2(ii), group part)

The upper half-plane `ℍ` (biholomorphic to the open unit disc by the Cayley map) with its
Aut-holomorphic structure `halfPlane = ofEmbedding (↑) ` is an **Aut-holomorphic disc**
([AbsTopIII], Definition 2.1(i)).

* `mem_global_halfPlane`: `A_ℍ(ℍ)` consists exactly of the Möbius maps `τ ↦ g • τ`,
  `g ∈ SL(2, ℝ)` (via `Uniformization.exists_SL2R_eq_of_holomorphic` of `oka`: Schwarz lemma);
* `mobiusHom : SL(2, ℝ) →* A_ℍ(ℍ)` is surjective with kernel `{±1}` (`mem_ker_mobiusHom`);
* `globalEquivPSL : A_ℍ(ℍ) ≃* SL(2, ℝ) ⧸ {±1}`: **`Aut^hol(X) ≅ SL₂(ℝ)/{±1}`** as abstract groups
  ([AbsTopIII], Proposition 2.2(ii); the topological statement and the commensurable terminality
  of `Aut^{RC-hol}(X)`, which use Cartan's theorem, are not formalised here).
-/

namespace Iut

namespace AutHol

open Set TopologicalSpace UpperHalfPlane
open scoped MatrixGroups

/-- **The Aut-holomorphic disc** `ℍ`. -/
noncomputable def halfPlane : AutHolStr ℍ := ofEmbedding ((↑) : ℍ → ℂ)

theorem image_coe_top : ((↑) : ℍ → ℂ) '' ((⊤ : Opens ℍ) : Set ℍ) = {z : ℂ | 0 < z.im} := by
  ext z
  simp only [Opens.coe_top, image_univ, mem_range, mem_setOf_eq]
  constructor
  · rintro ⟨τ, rfl⟩
    exact τ.im_pos
  · intro hz
    exact ⟨⟨z, hz⟩, rfl⟩

theorem holIn_top_iff_holomorphicH {g : (⊤ : Opens ℍ) → (⊤ : Opens ℍ)} :
    HolIn ((↑) : ℍ → ℂ) ((⊤ : Opens ℍ) : Set ℍ) g ↔
      Uniformization.HolomorphicH (fun τ => (g ⟨τ, by simp⟩ : ℍ)) := by
  rw [HolIn, image_coe_top]
  constructor
  · rintro ⟨F, hF, hFg⟩
    refine hF.congr fun z hz => ?_
    have h1 := hFg ⟨ofComplex z, by simp⟩
    rw [Uniformization.ofComplex_of_im_pos hz] at h1
    exact h1
  · intro h
    refine ⟨_, h, fun x => ?_⟩
    simp only
    congr 3
    ext
    rw [Uniformization.ofComplex_of_im_pos x.1.im_pos]

/-- The Möbius homeomorphism `τ ↦ g • τ`. -/
noncomputable def mobius (g : SL(2, ℝ)) : ℍ ≃ₜ ℍ := Homeomorph.smul g

@[simp]
theorem mobius_apply (g : SL(2, ℝ)) (τ : ℍ) : mobius g τ = g • τ := rfl

theorem holomorphicH_id : Uniformization.HolomorphicH id := by
  unfold Uniformization.HolomorphicH
  refine differentiableOn_id.congr fun z hz => ?_
  exact Uniformization.ofComplex_of_im_pos hz

/-- **`A_ℍ(ℍ)` consists of the Möbius maps.** -/
theorem mem_global_halfPlane {T : ℍ ≃ₜ ℍ} :
    T ∈ halfPlane.global ↔ ∃ g : SL(2, ℝ), ∀ τ, T τ = g • τ := by
  rw [AutHolStr.mem_global]
  change HolIn _ _ _ ∧ HolIn _ _ _ ↔ _
  rw [holIn_top_iff_holomorphicH, holIn_top_iff_holomorphicH]
  constructor
  · rintro ⟨h1, h2⟩
    exact Uniformization.exists_SL2R_eq_of_holomorphic h1 h2 (fun τ => by simp [conj, topHomeo])
      (fun τ => by simp [conj, topHomeo])
  · rintro ⟨g, hg⟩
    have hs : ∀ τ, T.symm τ = g⁻¹ • τ := by
      intro τ
      rw [Homeomorph.symm_apply_eq, hg, smul_inv_smul]
    constructor
    · have : (fun τ => ((conj (topHomeo ℍ).symm T) ⟨τ, by simp⟩ : ℍ)) = fun τ => g • id τ := by
        ext1 τ
        exact hg τ
      rw [this]
      exact holomorphicH_id.smul g
    · have : (fun τ => ((conj (topHomeo ℍ).symm T).symm ⟨τ, by simp⟩ : ℍ)) =
          fun τ => g⁻¹ • id τ := by
        ext1 τ
        exact hs τ
      rw [this]
      exact holomorphicH_id.smul g⁻¹

/-- **`SL(2, ℝ) → A_ℍ(ℍ)`**, `g ↦ (τ ↦ g • τ)`. -/
noncomputable def mobiusHom : SL(2, ℝ) →* halfPlane.global where
  toFun g := ⟨mobius g, mem_global_halfPlane.2 ⟨g, fun _ => rfl⟩⟩
  map_one' := by
    ext τ
    simp
  map_mul' g h := by
    ext τ
    simp [mul_smul]

theorem mobiusHom_surjective : Function.Surjective mobiusHom := by
  rintro ⟨T, hT⟩
  obtain ⟨g, hg⟩ := mem_global_halfPlane.1 hT
  exact ⟨g, Subtype.ext (Homeomorph.ext fun τ => (hg τ).symm)⟩

/-- **The kernel of `SL(2, ℝ) → A_ℍ(ℍ)` is `{±1}`.** -/
theorem mem_ker_mobiusHom (g : SL(2, ℝ)) : g ∈ mobiusHom.ker ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro hg
    have hfix : ∀ τ : ℍ, g • τ = τ := by
      intro τ
      have := congrArg (fun T : halfPlane.global => (T : ℍ ≃ₜ ℍ) τ) (MonoidHom.mem_ker.1 hg)
      simpa [mobiusHom] using this
    have key : ∀ τ : ℍ, (g 0 0 : ℂ) * τ + g 0 1 = τ * ((g 1 0 : ℂ) * τ + g 1 1) := by
      intro τ
      have h1 := congrArg ((↑) : ℍ → ℂ) (hfix τ)
      rw [Uniformization.coe_SL2R_smul] at h1
      rw [div_eq_iff (Uniformization.denom_SL2R_ne_zero g τ.im_pos)] at h1
      rw [h1]
    have hI := key I
    have h2I := key ⟨2 * Complex.I, by simp⟩
    simp only [coe_I] at hI
    have hI_re := congrArg Complex.re hI
    have hI_im := congrArg Complex.im hI
    have h2_re := congrArg Complex.re h2I
    have h2_im := congrArg Complex.im h2I
    simp [Complex.mul_re, Complex.mul_im] at hI_re hI_im h2_re h2_im
    have hdet := g.2
    rw [Matrix.det_fin_two] at hdet
    have hc : g 1 0 = 0 := by nlinarith
    have hb : g 0 1 = 0 := by nlinarith
    have had : g 0 0 = g 1 1 := by nlinarith
    have ha2 : g 0 0 * g 0 0 = 1 := by
      have : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := hdet
      rw [hb, ← had] at this
      linarith
    rcases mul_self_eq_one_iff.1 ha2 with ha | ha
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, ← had]
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, ← had, Matrix.SpecialLinearGroup.coe_neg]
  · rintro (rfl | rfl)
    · exact one_mem _
    · rw [MonoidHom.mem_ker]
      refine Subtype.ext (Homeomorph.ext fun τ => ?_)
      change (-1 : SL(2, ℝ)) • τ = τ
      apply UpperHalfPlane.ext
      rw [Uniformization.coe_SL2R_smul]
      simp [Matrix.SpecialLinearGroup.coe_neg]

/-- **`A_ℍ(ℍ) ≅ SL(2, ℝ)/{±1}`** ([AbsTopIII], Proposition 2.2(ii), as abstract groups). -/
noncomputable def globalEquivPSL : halfPlane.global ≃* SL(2, ℝ) ⧸ mobiusHom.ker :=
  (QuotientGroup.quotientKerEquivOfSurjective mobiusHom mobiusHom_surjective).symm

end AutHol

end Iut
