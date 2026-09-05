/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.Admissible

/-!
# Finiteness of the indeterminacy automorphisms and admissibility of theta regions (taxis #4, #278)

The class `indAut vQ c` of indeterminacy automorphisms of a packet is the image of the
finite type `∀ j, Factor' K vQ (c j) ≃ₐ Factor' K vQ (c j)` (the automorphism groups of the
factors are finite: the factors are finite field extensions of `ℚ_p`, resp. `ℝ` or `ℂ`, or the
zero ring), so it is finite (`indAut_finite`), and each of its members is continuous
(`continuous_of_mem_indAut`). Hence the union of the images of a compact set of positive
measure under the indeterminacy automorphisms is admissible (`iUnion_indAut_admissible`),
which gives `LocalTheory.theta_admissible` (`theta_admissible`) and, once the log-shells are
constructed, `LocalTheory.thetaShell_admissible`. The unconditional form of IUT IV,
Proposition 1.4(iv) for the maximal order is `prop14_iv`.
-/

namespace Iut

namespace LocalConstruct

open NumberField MeasureTheory
open scoped TensorProduct Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K]

/-! ### Finiteness of the automorphism groups of the factors -/

section Finite

variable (p : Nat.Primes) (v : Place K)

/-- For `v ∣ p`, the factor is isomorphic over `ℚ_p` to the completion `K_v` (with the
`ℚ_p`-structure `padicAlgebra`). -/
noncomputable def completionAlgEquivFactor (h : IsOver K p v) :
    letI := padicAlgebra h.residueChar_finPart
    completionAt K (finPart K v) ≃ₐ[ℚ_[p]] Factor K p v :=
  letI := padicAlgebra h.residueChar_finPart
  (AlgEquiv.quotientBot ℚ_[p] (completionAt K (finPart K v))).symm.trans
    ((Ideal.quotientEquivAlgOfEq ℚ_[p] (junkIdeal_eq_bot h).symm).trans (factorQuotAlgEquiv p v h))

/-- The automorphism group of a nonarchimedean factor is finite. -/
instance finite_algEquiv_factor : Finite (Factor K p v ≃ₐ[ℚ_[p]] Factor K p v) := by
  by_cases h : IsOver K p v
  · letI := padicAlgebra h.residueChar_finPart
    haveI := finite_padicAlgebra h.residueChar_finPart
    haveI := AlgEquiv.fintype ℚ_[p] (completionAt K (finPart K v))
    exact Finite.of_equiv _ (AlgEquiv.autCongr (completionAlgEquivFactor p v h)).toEquiv
  · haveI := subsingleton_factor p v h
    exact Finite.of_injective
      (fun σ : Factor K p v ≃ₐ[ℚ_[p]] Factor K p v => (⇑σ : Factor K p v → Factor K p v))
      DFunLike.coe_injective

/-- The automorphism group of an archimedean factor is finite. -/
instance finite_algEquiv_archFactor : Finite (ArchFactor K v ≃ₐ[ℝ] ArchFactor K v) := by
  by_cases h : (archPlace K v).IsReal
  · let e : ArchFactor K v ≃ₐ[ℝ] ℝ :=
      (ULift.algEquiv : ULift (archField K (archPlace K v)) ≃ₐ[ℝ] archField K (archPlace K v)).trans
        ((Subalgebra.equivOfEq _ _ (archField_of_isReal K h)).trans (Algebra.botEquiv ℝ ℂ))
    haveI := AlgEquiv.fintype ℝ ℝ
    exact Finite.of_equiv _ (AlgEquiv.autCongr e).symm.toEquiv
  · have h' : (archPlace K v).IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp h
    let e : ArchFactor K v ≃ₐ[ℝ] ℂ :=
      (ULift.algEquiv : ULift (archField K (archPlace K v)) ≃ₐ[ℝ] archField K (archPlace K v)).trans
        ((Subalgebra.equivOfEq _ _ (archField_of_isComplex K h')).trans Subalgebra.topEquiv)
    haveI := AlgEquiv.fintype ℝ ℂ
    exact Finite.of_equiv _ (AlgEquiv.autCongr e).symm.toEquiv

/-- The automorphism groups of the factors are finite. -/
instance finite_algEquiv_factor' (vQ : RationalPlace) :
    Finite (Factor' K vQ v ≃ₐ[baseField vQ] Factor' K vQ v) :=
  match vQ with
  | .finite p => finite_algEquiv_factor p v
  | .infinite => finite_algEquiv_archFactor v

end Finite

variable {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K)

/-- **The class of indeterminacy automorphisms is finite.** -/
theorem indAut_finite : (indAut vQ c).Finite := by
  have : indAut vQ c = Set.range
      fun σ : ∀ j, Factor' K vQ (c j) ≃ₐ[baseField vQ] Factor' K vQ (c j) =>
        ⇑(mapAlgHom vQ c σ) := by
    ext φ
    simp only [indAut, Set.mem_setOf_eq, Set.mem_range]
    exact ⟨fun ⟨σ, h⟩ => ⟨σ, h.symm⟩, fun ⟨σ, h⟩ => ⟨σ, h.symm⟩⟩
  rw [this]
  exact Set.finite_range _

/-- The automorphisms `⊗_j σ_j` are continuous (linear maps of finite-dimensional spaces). -/
lemma continuous_mapAlgHom (σ : ∀ j, Factor' K vQ (c j) ≃ₐ[baseField vQ] Factor' K vQ (c j)) :
    Continuous (mapAlgHom vQ c σ) :=
  LinearMap.continuous_of_finiteDimensional (mapAlgHom vQ c σ).toLinearMap

/-- Indeterminacy automorphisms are continuous. -/
lemma continuous_of_mem_indAut {φ : Tensor K vQ c → Tensor K vQ c} (hφ : φ ∈ indAut vQ c) :
    Continuous φ := by
  obtain ⟨σ, rfl⟩ := hφ
  exact continuous_mapAlgHom vQ c σ

/-! ### Admissibility of unions over the indeterminacies -/

/-- **The union of the images of a compact set of positive Haar measure under the
indeterminacy automorphisms is admissible.** -/
theorem iUnion_indAut_admissible {S : Set (Tensor K vQ c)} (hS : IsCompact S)
    (hpos : 0 < haar vQ c S) : (⋃ φ ∈ indAut vQ c, φ '' S) ∈ admissible vQ c := by
  have hsub : S ⊆ ⋃ φ ∈ indAut vQ c, φ '' S := fun x hx =>
    Set.mem_iUnion₂.mpr ⟨id, id_mem_indAut vQ c, ⟨x, hx, rfl⟩⟩
  have hcpt : IsCompact (⋃ φ ∈ indAut vQ c, φ '' S) :=
    (indAut_finite vQ c).isCompact_biUnion fun φ hφ => hS.image (continuous_of_mem_indAut vQ c hφ)
  refine ⟨?_, ?_, hcpt.isClosed.measurableSet, lt_of_lt_of_le hpos (measure_mono hsub),
    hcpt.measure_lt_top⟩
  · obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
    exact ⟨x, hsub hx⟩
  · rw [hcpt.isClosed.closure_eq]
    exact hcpt

/-- **`LocalTheory.theta_admissible`**: the union of the images of a scaled integral
structure under the indeterminacy automorphisms is admissible. -/
theorem theta_admissible (s : Tensor K vQ c) (hs : IsUnit s) :
    (⋃ φ ∈ indAut vQ c, φ '' (s • integralAt vQ c)) ∈ admissible vQ c :=
  iUnion_indAut_admissible vQ c (isCompact_smul_integralAt s) (haar_smul_integralAt_pos hs)

/-- **IUT IV, Proposition 1.4(iv)** for the maximal order, at every prime
(`LocalTheory.prop14_iv`): the indeterminacy automorphisms preserve `(R_I)^∼`. -/
theorem prop14_iv (p : Nat.Primes) (c : ι → Place K) :
    ∀ φ ∈ indAut (.finite p) c,
      φ '' integralAt (.finite p) c ⊆ integralAt (.finite p) c := by
  rintro _ ⟨σ, rfl⟩
  exact mapAlgHom_image_integral_subset p c σ

end LocalConstruct

end Iut
