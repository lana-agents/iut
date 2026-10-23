/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.BelyiSpec
import CurvesJacobian.Cusp.Cor37c

/-!
# [AbsTopII] Cor 3.7 (c) for the genuine cusp data: decomposition groups of the filled points

[AbsTopII] Corollary 3.7 (c) (`Topics in Absolute Anabelian Geometry II.txt` l.4767–4769): "The
decomposition groups of the closed points of `X` lying in the complement of `U_X` may be obtained
as the images via `Π_{U_X} ↠ Π` of the cuspidal decomposition groups of `Π_{U_X}`."

This is the input of [AbsTopIII] Thm 1.9 (a) (`Topics in Absolute Anabelian Geometry III.txt`
l.2131–2143: "a "group-theoretic" construction of `Π_U` equipped with the collection of subgroups
that arise as decomposition groups of NF-points"). curves-jacobian's `cor37c` is stated for the
places `W` over the cusps of `U_X`; here it is restated for the cuspidal subgroups of the
cuspidal extension `arithmeticExt` (the cusp data `arithCuspData` of `BelyiSpec.lean`), which are
what the group-theoretic algorithm sees:

* `exists_isCuspPlace_eq_arithInertia`: every cuspidal subgroup `I` of `Π_U` is the inertia group
  `arithInertia W` of a place `W` over a cusp;
* **`cor37c_cusps`**: up to one change of base point `α₀` and one conjugation `t` (both
  independent of the cusp), for every cuspidal subgroup `I` of `Π_{U_X}` the image of its
  commensurator `Comm_{Π_{U_X}}(I)` (the cuspidal decomposition group, [AbsTopI] Lemma 4.5 (vi))
  under `Π_{U_X} ↠ Π_X` is the decomposition group `D_W ⊆ Π_X` of the place `W` with
  `I = I_W`, i.e. a decomposition group of the closed point of `X ∖ U_X` under `W`.

No hypothesis beyond those of `arithmeticExt` is needed (the filling `Π_{U_X} ↠ Π_X` here is the
geometric one; that it is the group-theoretic `belyiCusp` is `belyiCuspSpec`, debt `hDGC`).
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian.Cusp

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction

section Arith

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **Every cuspidal subgroup of `Π_U` is the inertia group of a place over a cusp.** -/
theorem exists_isCuspPlace_eq_arithInertia {I : Subgroup (arithmeticExt Ω C hc).Pi}
    (hI : I ∈ (arithmeticExt Ω C hc).cusps) :
    ∃ W : ValuationSubring (FFClosure (geomCurve Ω C)),
      IsCuspPlace Ω C hc W ∧ I = arithInertia Ω C hc W := by
  obtain ⟨I₀, ⟨W, hWk, hWU, rfl⟩, g, rfl⟩ := hI
  obtain ⟨τ, rfl⟩ := arithAction_surjective Ω C hc g
  have hW : IsCuspPlace Ω C hc W :=
    ⟨hWk, fun h => hWU ((isCentredOn_geomOpen_iff Ω C hc W).2 ⟨hWk, h⟩)⟩
  refine ⟨_, isCuspPlace_comap Ω C hc τ.symm hW, ?_⟩
  rw [arithInertia_comap, arithInertia_eq_map_geom Ω C hc hWk]

/-- **[AbsTopII] Cor 3.7 (c) for the cuspidal subgroups of `Π_{U_X}`**: for a nonempty open
`U_X ⊆ X` and a change of base point `α₀` there is `t ∈ Π_X` such that every cuspidal subgroup
`I` of `Π_{U_X}` is `I_W` for a place `W` over a cusp of `U_X`, and the image of the cuspidal
decomposition group `Comm_{Π_{U_X}}(I)` under `Π_{U_X} ↠ Π_X` is `t · α₀(D_W(X)) · t⁻¹`. -/
theorem cor37c_cusps (UX : C.Xbar.Opens) (hUX : UX ≤ C.U) (hne : (UX : Set C.Xbar).Nonempty)
    (α₀ : fiber (basePoint Ω C hc) ≅
      fiber (fillPoint Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) hUX)) :
    ∃ t, ∀ I ∈ (arithmeticExt Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc)).cusps,
      ∃ W : ValuationSubring (FFClosure (geomCurve Ω C)),
        IsCuspPlace Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) W ∧
        I = arithInertia Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) W ∧
        (Subgroup.Commensurable.commensurator I).map
            (fillMap Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) hUX).toMonoidHom =
          ((arithDecomp Ω C hc W).map (autContinuousMulEquivOfIso
            (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, C.U)) rfl rfl
              α₀)).toMulEquiv.toMonoidHom).map (MulAut.conj t).toMonoidHom := by
  obtain ⟨t, ht⟩ := cor37c Ω C hc UX hUX hne α₀
  refine ⟨t, fun I hI => ?_⟩
  obtain ⟨W, hW, rfl⟩ := exists_isCuspPlace_eq_arithInertia Ω _ _ hI
  exact ⟨W, hW, rfl, ht W hW⟩

end Arith

end Iut.Reconstruction
