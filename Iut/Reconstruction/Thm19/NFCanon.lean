/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.RecFunctionField
import Iut.Reconstruction.Thm19.StageNF

/-!
# The NF-model of a curve over a number field is canonical (MR9 item 4, step 4)

[AbsTopIII] Def 1.7 (`Topics in Absolute Anabelian Geometry III.txt`): an NF-curve is a curve
defined over `k̄_NF`. Over a number field `k` the algebraic closure `k̄` of `k` in `Ω` is `k̄_NF`,
so every NF-model `N` (curves-jacobian `NFModel`) has `F_NF = F k̄`, every stage is an NF-stage
and every point is an NF-point:

* `kbarNF_eq_bot`, **`nfModelNF`**: the canonical NF-model `F_NF = F k̄`;
* **`NFModel.mem_FNF_iff_numberField`**: every NF-model is the canonical one;
* **`StageIdx.isNF_numberField`**: every stage is an NF-stage.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

open CurvesJacobian

set_option linter.unusedSectionVars false

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] [CharZero k] [CharZero Ω]
  [NumberField k]

omit [IsGalois (K₀ k t) Ω] in
/-- Over a number field, an element of `k̄` is an algebraic number. -/
lemma isAlgebraic_of_mem_kbar {x : Ω} (hx : x ∈ kbar k Ω) : IsAlgebraic ℚ x :=
  (mem_algebraicClosure_iff.1 hx).restrictScalars ℚ

variable (k Ω) in
omit [IsGalois (K₀ k t) Ω] in
/-- Over a number field, `k̄ = k̄_NF`. -/
lemma kbarNF_eq_bot : kbarNF k Ω = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  have hxk : x ∈ kbar k Ω := hx
  exact IntermediateField.mem_bot.2
    ⟨⟨x, mem_algebraicClosure_iff.2 (isAlgebraic_of_mem_kbar hxk)⟩, rfl⟩

/-- **The canonical NF-model of a curve over a number field**: `F_NF = F k̄`. -/
def nfModelNF : NFModel D where
  FNF := (F (baseChange D)).toSubfield
  algebraic_mem x hx := kbar_le_F_baseChange D (mem_kbar_of_isAlgebraic hx)
  mem_F _ hx := hx
  isAlgebraic_of_mem_kbar _ _ hxk := isAlgebraic_of_mem_kbar hxk
  mem_closure _ hx := Subfield.subset_closure (Or.inl hx)
  cusp_nf _ _ ht := ⟨t, le_F_baseChange D ((F D).algebraMap_mem
    ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩), ht⟩
  linearDisjoint := by
    rw [kbarNF_eq_bot k Ω]
    exact IntermediateField.LinearDisjoint.bot_right _

variable {D}

/-- **Every NF-model of a curve over a number field is the canonical one**: `F k̄ ⊆ F_NF`
(`F_NF · k̄ = F k̄` and `k̄ = k̄_NF ⊆ F_NF`). -/
lemma NFModel.mem_FNF_iff_numberField (N : NFModel D) (x : Ω) :
    x ∈ N.FNF ↔ x ∈ F (baseChange D) := by
  refine ⟨N.mem_F x, fun hx => ?_⟩
  have h := N.mem_closure x hx
  refine (Subfield.closure_le.2 ?_) h
  rintro y (hy | hy)
  · exact hy
  · exact N.algebraic_mem y (isAlgebraic_of_mem_kbar hy)

/-- The coordinate of a stage lies in `F k̄`. -/
lemma StageIdx.t'_mem_F_baseChange [IsAlgClosed Ω] [Fact (D.H ≤ D.HL)] (s : StageIdx D) :
    s.t' ∈ F (baseChange D) :=
  mem_F_baseChange_of_stage s ((F s.data).algebraMap_mem
    ⟨s.t', IntermediateField.mem_adjoin_simple_self s.K s.t'⟩)

/-- **Over a number field every stage is an NF-stage.** -/
lemma StageIdx.isNF_numberField [IsAlgClosed Ω] [Fact (D.H ≤ D.HL)] (N : NFModel D)
    (s : StageIdx D) : s.IsNF N := fun _ _ ht =>
  ⟨s.t', (NFModel.mem_FNF_iff_numberField N _).2 s.t'_mem_F_baseChange, ht⟩

end Iut.Reconstruction.Thm19
