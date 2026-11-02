/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ClosedPointDecomp
import Iut.Reconstruction.Thm19.PlaceConj
import Iut.Reconstruction.Thm19.GeomLim

/-!
# Stages with rational cusps are cofinal (MR9 item 4, step 4)

`LiftData.S_mem_PU_cycloIso` (`Thm19/SyncStageLift.lean`, [AbsTopIII] Thm 1.9 (c),
`Topics in Absolute Anabelian Geometry III.txt` l.2153–2157, along the stage isomorphisms) needs
stages whose cusps are rational. Here: after a finite extension of the field of constants every cusp
is rational.

* `transPlace_eq_toGalF_smul`;
* **`exists_ratCusps`**: for a Galois model `D` (of a curve, `F D` a function field) and a finite
  extension `K₁` of `k`, there is a finite extension `K' ⊇ K₁` such that every cusp place of
  `F_{K'}` is the place of a `K'`-rational point (finitely many cusp places of `F`, places of
  `Ω` over them, `exists_gkLiftsTo_of_ne` for each, `gkLiftsTo_smul` for the conjugate places,
  `ratPointConstExt`);
* **`GStage.exists_ge_ratCusps`**: geometric stages with rational cusps are cofinal.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer
open scoped Pointwise

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

omit [CharZero k] [IsAlgClosed Ω] in
lemma transPlace_eq_toGalF_smul (ρ : D.H) (A : ValuationSubring Ω) :
    transPlace (ρ : Ω ≃ₐ[K₀ k t] Ω) A = toGalF D ρ • A := by
  ext x
  rw [mem_transPlace, mem_smul_valuationSubring_iff]
  rfl

/-- **Rational cusps after a finite extension of the field of constants.** -/
theorem exists_ratCusps (K₁ : IntermediateField k Ω) [FiniteDimensional k K₁] :
    ∃ (K' : IntermediateField k Ω) (_ : FiniteDimensional k K'), K₁ ≤ K' ∧
      ∀ P : Place K' (F (constExt K' D)), IsCuspPlaceF P →
        ∃ x : RatPoint (constExt K' D), placeOfF x = P := by
  classical
  have hfin := Place.finite_setOf_notMem (k := k) (CurvesJacobian.tF D)
  choose A hA using fun P : Place k (F D) => CurvesJacobian.exists_valuationSubring_liesOver D P
  have hkA : ∀ (P : Place k (F D)) (c : k), algebraMap k Ω c ∈ A P := fun P c => by
    rw [IsScalarTower.algebraMap_apply k (F D) Ω]
    exact (hA P _).2 (P.2.2 c)
  have key : ∀ T : Finset (Place k (F D)), (∀ P ∈ T, CurvesJacobian.tF D ∉ P.1) →
      ∃ (K' : IntermediateField k Ω) (_ : FiniteDimensional k K'), K₁ ≤ K' ∧
        (T.Nonempty → GkStable K') ∧ ∀ P ∈ T, GkLiftsTo D K' (A P) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨K₁, inferInstance, le_rfl, fun h => absurd h Finset.not_nonempty_empty,
        fun _ h => absurd h (Finset.notMem_empty _)⟩
    | insert P T _ ih =>
      intro hT
      obtain ⟨K'', hK'', hle, -, hl⟩ := ih fun Q hQ => hT Q (Finset.mem_insert_of_mem hQ)
      obtain ⟨K, hK, hle', hst, hlift⟩ := exists_gkLiftsTo_of_ne (A P) (hkA P)
        ⟨CurvesJacobian.tF D, fun h => hT P (Finset.mem_insert_self P T) ((hA P _).1 h)⟩ K''
      refine ⟨K, hK, hle.trans hle', fun _ => hst, fun Q hQ => ?_⟩
      rcases Finset.mem_insert.1 hQ with rfl | hQ
      · exact hlift
      · exact (hl Q hQ).mono hle'
  obtain ⟨K', hK', hle, hst, hl⟩ := key hfin.toFinset fun P hP => hfin.mem_toFinset.1 hP
  refine ⟨K', hK', hle, fun P' hP' => ?_⟩
  obtain ⟨A', hA'⟩ := CurvesJacobian.exists_valuationSubring_liesOver (constExt K' D) P'
  have hkA' : ∀ c : k, algebraMap k Ω c ∈ A' := fun c => by
    rw [IsScalarTower.algebraMap_apply k K' Ω,
      IsScalarTower.algebraMap_apply K' (F (constExt K' D)) Ω]
    exact (hA' _).2 (P'.2.2 _)
  have ht' : (CurvesJacobian.tF D : Ω) ∉ A' := fun h =>
    hP' ((hA' (CurvesJacobian.tF (constExt K' D))).1 h)
  have hne : ∃ f : F D, (f : Ω) ∉ A' := ⟨CurvesJacobian.tF D, ht'⟩
  set P0 := placeBelow D A' hkA' hne
  have hP0 : P0 ∈ hfin.toFinset := hfin.mem_toFinset.2 ht'
  have hcomap : (A P0).comap (algebraMap (F D) Ω) = A'.comap (algebraMap (F D) Ω) := by
    ext y
    exact hA P0 y
  obtain ⟨ρ, hρ⟩ := exists_transPlace_eq_of_comap_eq (D := D) (A P0) A' hcomap
  have hlift : GkLiftsTo D K' A' := by
    rw [hρ, transPlace_eq_toGalF_smul]
    exact gkLiftsTo_smul K' (hst ⟨P0, hP0⟩) ρ (hl P0 hP0)
  refine ⟨ratPointConstExt K' A' hkA' (isIntegral_residueField_of_ne A' hkA' hne) hlift,
    Place.ext ?_⟩
  ext y
  exact hA' y

section GStage

open CategoryTheory AlgebraicGeometry CurvesJacobian CurvesJacobian.Cusp Belyi

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [IsFunctionField k X.functionField] {τ : X.functionField}
  {hτ : Transcendental k τ}

/-- **Geometric stages whose cusps are rational are cofinal** (enlarge the field of constants,
`exists_ratCusps`). -/
theorem GStage.exists_ge_ratCusps (g : GStage k hτ) :
    ∃ g' : GStage k hτ, g ≤ g' ∧ g'.τ₀ = g.τ₀ ∧
      ∀ P : Place g'.K (F g'.data), IsCuspPlaceF P → ∃ x : RatPoint g'.data, placeOfF x = P := by
  obtain ⟨K', hK', hle, h⟩ := exists_ratCusps (D := curveGaloisData k g.hτ₀) g.K
  exact ⟨⟨K', g.τ₀, g.hτ₀, g.htV⟩, ⟨hle, self_mem_chartRing k _⟩, rfl, h⟩

end GStage

end Iut.Reconstruction.Thm19
