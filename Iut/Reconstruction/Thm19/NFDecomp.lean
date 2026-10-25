/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ArithBridgeDecomp

/-!
# [AbsTopIII] Thm 1.9 (a) in the Galois model: decomposition groups by cuspidalization

[AbsTopIII] Thm 1.9 (a) (`Topics in Absolute Anabelian Geometry III.txt` l.2131–2143): "a
"group-theoretic" construction of `Π_U` equipped with the collection of subgroups that arise as
decomposition groups of NF-points", via Belyi cuspidalization ([AbsTopII] Cor 3.7 (a)–(c)). For
an affine hyperbolic curve `C` over a number field, every closed point of `U` is an NF-point, and
removing it gives a nonempty open `U_X ⊆ U` of which it is a cusp. [AbsTopII] Cor 3.7 (c)
(`Reconstruction/Cusp/Cor37c.lean`, `Topics in Absolute Anabelian Geometry II.txt` l.4767–4769)
says that its decomposition groups are the images of the cuspidal decomposition groups
`Comm_{Π_{U_X}}(I)` under the filling `Π_{U_X} ↠ Π_U`. Here this is carried to the Galois model
`Pi (curveGaloisData K hτ)` of the Kummer side ((b)–(e)) through `piBridge`
(`Thm19/ArithBridge.lean`, `map_decompH_piBridge`):

* **`map_decompH_eq_fillMap_commensurator`**: for a nonempty open `U_X ⊆ U` and a change of
  base point `α₀`, there is one `t ∈ Π_U` such that for every place `W` of `K(X̄)^alg` over a
  point of `U ∖ U_X`, the image of `D_W ∩ H` in `Π_U` (Galois model), carried by `piBridge`,
  `α₀` and conjugation by `t`, is `fillMap(Comm(I))` for the cuspidal subgroup
  `I = I_{σW} ∈ cusps(Π_{U_X})`.

The filling `Π_{U_X} ↠ Π_U` used here is the geometric one; that it is the group-theoretic Belyi
cuspidalization `belyiCusp` is `belyiCuspSpec` (`Reconstruction/Cusp/BelyiSpec.lean`, debt `hDGC`,
milestone MR7).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian CurvesJacobian.Cusp AffOrbicurve KummerTheory Curve

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section Decomp

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar algFF algFFL₀ isAlgClosure_of_isAlgebraic

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)

attribute [local instance] nonempty_U

/-- **[AbsTopIII] Thm 1.9 (a) in the Galois model of the Kummer side**: for a nonempty open
`U_X ⊆ U` and a change of base point `α₀`, there is `t ∈ Π_U` such that for every place `W` of
`K(X̄)^alg` over a point of `U ∖ U_X` (its transport `σW` is a cusp place of `U_X`), the
decomposition group `D_W ∩ H` (its image in `Π_U` of the Galois model), carried to the
`Π_U` of `arithmeticExt` by `piBridge` and then by `α₀` and conjugation by `t`, is the image
under the filling `Π_{U_X} ↠ Π_U` of the cuspidal decomposition group `Comm_{Π_{U_X}}(I)` of
the cuspidal subgroup `I = I_{σW}` of `Π_{U_X}` ([AbsTopII] Cor 3.7 (c)). -/
theorem map_decompH_eq_fillMap_commensurator (UX : C.Xbar.Opens) (hUX : UX ≤ C.U)
    (hne : (UX : Set C.Xbar).Nonempty)
    (α₀ : fiber (basePoint Ω C hc.out) ≅
      fiber (fillPoint Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc.out) hUX)) :
    ∃ t, ∀ W : ValuationSubring (FFClosure C.Xbar),
      IsCuspPlace Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc.out)
          (W.comap ((σc (Ω := Ω) (C := C)).symm :
            FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) →
      arithInertia Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc.out)
          (W.comap ((σc (Ω := Ω) (C := C)).symm :
            FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) ∈
        (arithmeticExt Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc.out)).cusps ∧
      (((((decompH (curveGaloisData K hτ) W).map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ).H
            (curveGaloisData K hτ).S))).map
          (piBridge (Ω := Ω) hτ hU).toMulEquiv.toMonoidHom).map
          (autContinuousMulEquivOfIso (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, C.U)) rfl rfl
            α₀)).toMulEquiv.toMonoidHom).map (MulAut.conj t).toMonoidHom =
        (Subgroup.Commensurable.commensurator (arithInertia Ω (subCurve C UX hUX hne)
            (compl_nonempty_of_le hUX hc.out)
            (W.comap ((σc (Ω := Ω) (C := C)).symm :
              FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)))).map
          (fillMap Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc.out)
            hUX).toMonoidHom) := by
  obtain ⟨t, ht⟩ := cor37c Ω C hc.out UX hUX hne α₀
  refine ⟨t, fun W hW => ⟨(mem_arithCusps_iff Ω _ _).2 ⟨_, hW, rfl⟩, ?_⟩⟩
  rw [map_decompH_piBridge hτ hU W]
  exact (ht _ hW).symm

end Decomp

end Iut.Reconstruction.Thm19
