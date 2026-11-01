/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.StageIso

/-!
# Residues along stage isomorphisms (MR9 item 4, generic start)

[AbsTopIII] Thm 1.9 (c) (`Topics in Absolute Anabelian Geometry III.txt` l.2153–2157) constructs
`P_U ⊆ H¹(Π_U, μ_Ẑ(Π_U))` from the residues, i.e. the restrictions to the inertia groups `I_x`
of the cusps (Prop 1.6 (iii), l.2001–2012). For the functoriality of Thm 1.9 in isomorphisms the
residues must be carried along the stage isomorphisms `h1Congr e χ`. Here, generically:

* `smul_eq_self_of_h1Congr`: if `σ` acts trivially on `M`, then `e σ` acts trivially on `M'`;
* **`evalTriv_h1Congr`**: `(h1Congr e χ η)(e σ) = χ (η(σ))` for such `σ` (the residue at `e σ` of
  the transported class is the transported residue);
* **`evalTrivHom_h1Congr`**: the same for the restriction to a subgroup `I` acting trivially and
  its image `e(I)`.
-/

open KummerTheory Curve AffOrbicurve CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section Residues

variable {P P' M M' : Type*} [Group P] [TopologicalSpace P] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction P M]
  [Group P'] [TopologicalSpace P'] [CommGroup M'] [TopologicalSpace M']
  [IsTopologicalGroup M'] [MulDistribMulAction P' M']
  (e : P ≃ₜ* P') (χ : M ≃ₜ* M') (hχ : ∀ p m, χ (p • m) = e p • χ m)

include hχ in
/-- An element acting trivially on `M` is carried to one acting trivially on `M'`. -/
lemma smul_eq_self_of_h1Congr {σ : P} (hσ : ∀ m : M, σ • m = m) (m' : M') : e σ • m' = m' := by
  obtain ⟨m, rfl⟩ := χ.surjective m'
  rw [← hχ, hσ]

/-- **The residues of a transported class are the transported residues.** -/
lemma evalTriv_h1Congr {σ : P} (hσ : ∀ m : M, σ • m = m) (x : ContH1 P M) :
    ContH1.evalTriv (e σ) (smul_eq_self_of_h1Congr e χ hχ hσ) (h1Congr e χ hχ x) =
      χ (ContH1.evalTriv σ hσ x) := by
  induction x using ContH1.induction_on with
  | h c =>
    rw [h1Congr_apply, ContH1.map_mk, ContH1.evalTriv_mk, ContH1.evalTriv_mk]
    simp only [ContH1.cocyclesMap_apply]
    exact congrArg (fun p => χ (c p)) (e.symm_apply_apply σ)

include hχ in
/-- The image `e(I)` of a subgroup acting trivially acts trivially. -/
lemma map_smul_eq_self_of_h1Congr (I : Subgroup P) (hI : ∀ g ∈ I, ∀ m : M, g • m = m) :
    ∀ g ∈ I.map e.toMulEquiv.toMonoidHom, ∀ m' : M', g • m' = m' := by
  rintro _ ⟨g, hg, rfl⟩ m'
  exact smul_eq_self_of_h1Congr e χ hχ (hI g hg) m'

/-- **Restriction to `I` and to `e(I)`**: `res_{e(I)} (h1Congr η) ∘ e = χ ∘ res_I η`. -/
lemma evalTrivHom_h1Congr (I : Subgroup P) (hI : ∀ g ∈ I, ∀ m : M, g • m = m)
    (x : ContH1 P M) (g : I) :
    ContH1.evalTrivHom (I.map e.toMulEquiv.toMonoidHom) (map_smul_eq_self_of_h1Congr e χ hχ I hI)
        (h1Congr e χ hχ x) ⟨e g, g, g.2, rfl⟩ =
      χ (ContH1.evalTrivHom I hI x g) :=
  evalTriv_h1Congr e χ hχ (hI g g.2) x

end Residues

end Iut.Reconstruction.Thm19
