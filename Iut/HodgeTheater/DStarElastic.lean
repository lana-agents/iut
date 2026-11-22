/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.DStarDescent
import Iut.HodgeTheater.VeryElastic

/-!
# `CKStrictSemiAbs` from the very elasticity of `Gal(F̄/F_mod)`

[AbsTopI] Cor. 2.8 (ii) (`Topics in Absolute Anabelian Geometry I.txt` l.1348–1379) gives strict
semi-absoluteness of isomorphisms of arithmetic fundamental groups over number fields; for the
semi-absoluteness of absolute homomorphisms its proof uses Prop. 2.5 (ii) (l.1046–1060): `Δ₁` is
topologically finitely generated (Prop. 2.2) and `G₂` is very elastic (Thm. 1.7 (iii), l.705–712).

Here the geometric half is proved and the arithmetic half is the only input:

* `isTopFG_ker_arith`: `Δ_X = ker(Π_X ↠ G_{F_mod})` is topologically finitely generated
  (`Δ_X ≃ₜ* Π̂_{g,r}`, curves-jacobian's `nonempty_kerProjGk_equiv`; `Π_{g,r}` is finitely
  generated and dense in its profinite completion);
* `isTopFG_ker_hemiCorePr₄`: hence so is `Δ_C` (`Δ_X = Δ_C ∩ Π_X` is open in `Δ_C`);
* **`isTopFG_ker_piCmodPr`**: `Δ_{C_{F_mod}} = ker(π₁(C_{F_mod}) ↠ Gal(F̄/F_mod))` is topologically
  finitely generated;
* **`ckStrictSemiAbs`**: `CKStrictSemiAbs D` from the single standard input
  `IsVeryElastic (GalG (Fmod D) D.Fbar)` ([AbsTopI] Thm. 1.7 (iii) for the number field `F_mod`),
  via the generic `Elastic.map_eq_one_of_isVeryElastic` (open subgroups of `π₁(C_{F_mod})` have
  topologically finitely generated geometric part by topological Schreier).
-/

noncomputable section

namespace Iut

namespace HodgeTheater

open CategoryTheory NumberField Frobenioid CurvesJacobian CurvesJacobian.Cusp
  Iut.Reconstruction.HemiGenuine Iut.Reconstruction.HemiCore Topology Pi1.Profinite Elastic

attribute [local instance low] Classical.propDecidable

variable (D : InitialThetaData.{0})

/-- `Π_{g,r}` (lifted) is finitely generated. -/
lemma fg_uliftSurfaceGroup (g r : ℕ) : Group.FG (ULift.{0} (Pi1.SurfaceGroup g r)) := by
  haveI : Finite (Pi1.SurfaceGen g r) :=
    Finite.of_equiv _ (CurvesJacobian.Cusp.surfaceGenEquiv g r).symm
  haveI : Group.FG (Pi1.SurfaceGroup g r) := Group.fg_of_surjective (PresentedGroup.mk_surjective _)
  exact Group.fg_of_surjective (f := (MulEquiv.ulift (α := Pi1.SurfaceGroup g r)).symm.toMonoidHom)
    (MulEquiv.ulift (α := Pi1.SurfaceGroup g r)).symm.surjective

/-- **`Δ_X` is topologically finitely generated** (`X = E_{F_mod} ∖ {O}`): `Δ_X ≃ₜ* Π̂_{g,r}`. -/
theorem isTopFG_ker_arith :
    IsTopFG (arithmeticExt D.Fbar (hypCurveX (curveMod D.E))
      (compl_XE_nonempty (curveMod D.E))).pr.toMonoidHom.ker := by
  obtain ⟨e⟩ := nonempty_kerProjGk_equiv D.Fbar (hypCurveX (curveMod D.E))
    (compl_XE_nonempty (curveMod D.E))
  haveI := fg_uliftSurfaceGroup (curveGenus D.Fbar (baseChange (Fmod D) D.Fbar
    (hypCurveX (curveMod D.E)).Xbar)).toNat (Nat.card ((baseChangeOpen (Fmod D) D.Fbar
      (hypCurveX (curveMod D.E)).U : Set (baseChange (Fmod D) D.Fbar
        (hypCurveX (curveMod D.E)).Xbar))ᶜ : Set _))
  refine IsTopFG.of_top_subtype ?_ (isTopFG_top_of_equiv e.symm
    (isTopFG_top_of_dense (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of _)).hom
      (ProfiniteGrp.ProfiniteCompletion.denseRange _)))
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage
    (arithmeticExt D.Fbar (hypCurveX (curveMod D.E))
      (compl_XE_nonempty (curveMod D.E))).pr.continuous

/-- **`Δ_C` is topologically finitely generated** (`C` the hemi-elliptic orbicurve over `F_mod`):
`Δ_C ∩ Π_X = Δ_X` is open in `Δ_C`. -/
theorem isTopFG_ker_hemiCorePr₄ :
    IsTopFG (hemiCorePr₄ (curveMod D.E) D.Fbar).toMonoidHom.ker := by
  set emb := hemiCoreEmb₄ (curveMod D.E) D.Fbar
  set pr := hemiCorePr₄ (curveMod D.E) D.Fbar
  have hemb := isOpenEmbedding_hemiCoreEmb₄ (curveMod D.E) D.Fbar
  have hU : IsOpen ((emb.toMonoidHom.range : Subgroup _) : Set (hemiCoreGrp₄ (curveMod D.E))) := by
    rw [MonoidHom.coe_range]
    exact hemb.isOpen_range
  have hM : IsClosed ((pr.toMonoidHom.ker : Subgroup _) : Set (hemiCoreGrp₄ (curveMod D.E))) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage pr.continuous
  have he : pr.toMonoidHom.ker ⊓ emb.toMonoidHom.range =
      (arithmeticExt D.Fbar (hypCurveX (curveMod D.E))
        (compl_XE_nonempty (curveMod D.E))).pr.toMonoidHom.ker.map emb.toMonoidHom := by
    ext y
    constructor
    · rintro ⟨hy, x, rfl⟩
      exact ⟨x, MonoidHom.mem_ker.2 ((hemiCorePr₄_hemiCoreEmb₄ (curveMod D.E) D.Fbar x).symm.trans
        (MonoidHom.mem_ker.1 hy)), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨MonoidHom.mem_ker.2 ((hemiCorePr₄_hemiCoreEmb₄ (curveMod D.E) D.Fbar x).trans
        (MonoidHom.mem_ker.1 hx)), x, rfl⟩
  refine IsTopFG.of_inf_open hM hU ?_
  rw [he]
  refine (isTopFG_ker_arith D).map _ emb.continuous ?_
  rw [Subgroup.coe_map]
  exact ((isTopFG_ker_arith D).isClosed.isCompact.image emb.continuous).isClosed

/-- **`Δ_{C_{F_mod}} = ker(π₁(C_{F_mod}) ↠ Gal(F̄/F_mod))` is topologically finitely generated.** -/
theorem isTopFG_ker_piCmodPr : IsTopFG (piCmodPr D).ker := by
  set e := piCmodCoreEquiv D
  refine IsTopFG.of_map (e : piCmod D →* hemiCoreGrp₄ (curveMod D.E))
    e.toHomeomorph.isClosedEmbedding ?_
  have h : (piCmodPr D).ker.map (e : piCmod D →* hemiCoreGrp₄ (curveMod D.E)) =
      (hemiCorePr₄ (curveMod D.E) D.Fbar).toMonoidHom.ker := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 := (piCmodPr_eq D x).symm.trans (MonoidHom.mem_ker.1 hx)
      exact MonoidHom.mem_ker.2 ((galCoreEquiv D).map_eq_one_iff.1 h1)
    · intro hy
      refine ⟨e.symm y, MonoidHom.mem_ker.2 ((piCmodPr_eq D (e.symm y)).trans ?_),
        e.apply_symm_apply y⟩
      have h2 : hemiCorePr₄ (curveMod D.E) D.Fbar (e (e.symm y)) = 1 := by
        rw [e.apply_symm_apply]
        exact MonoidHom.mem_ker.1 hy
      exact (galCoreEquiv D).map_eq_one_iff.2 h2
  rw [h]
  exact isTopFG_ker_hemiCorePr₄ D

/-- **Strict semi-absoluteness for `π₁(C_K)` (`CKStrictSemiAbs`) from the very elasticity of
`Gal(F̄/F_mod)`** ([AbsTopI] Cor. 2.8 (ii), l.1348–1379, via Prop. 2.5 (ii), l.1046–1060). The
input `hEl` is [AbsTopI] Thm. 1.7 (iii) (l.705–712: the absolute Galois group of a number field
is very elastic) for `F_mod`; the geometric half (`Δ` topologically finitely generated) is
`isTopFG_ker_piCmodPr`. -/
theorem ckStrictSemiAbs (hEl : IsVeryElastic (GalG (Fmod D) D.Fbar)) : CKStrictSemiAbs D :=
  fun α x hx => map_eq_one_of_isVeryElastic (piCKToCmod D : piCK D →* piCmod D)
    (isOpenEmbedding_piCKToCmod D) (piCmodPr D) (continuous_piCmodPr D) (piCmodPr_surjective D)
    (isTopFG_ker_piCmodPr D) hEl (α : piCK D →* piCK D) α.continuous α.surjective x hx

end HodgeTheater

end Iut
