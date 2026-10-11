/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.Admissible

/-!
# Finiteness of the Galois automorphisms of a packet and admissibility (taxis #4, #278)

The class `galAut vQ c` of Galois automorphisms `⊗_j σ_j` of a packet is the image of the
finite type `∀ j, Factor' K vQ (c j) ≃ₐ Factor' K vQ (c j)` (the automorphism groups of the
factors are finite: the factors are finite field extensions of `ℚ_p`, resp. `ℝ` or `ℂ`, or the
zero ring), so it is finite (`galAut_finite`), and each of its members is continuous
(`continuous_of_mem_galAut`). Hence the union of the images of a compact set of positive
measure under the Galois automorphisms is admissible (`iUnion_galAut_admissible`,
`galAut_theta_admissible`), and they preserve `(R_I)^∼` (`galAut_integral_subset`). The
indeterminacy automorphisms of IUT IV, Proposition 1.2 form a much larger class
(`IndAut.lean`); the Galois automorphisms are used at the archimedean place
(`ArchLogShell.lean`, `ArchIndAut.lean`).
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

/-- **The class of Galois automorphisms is finite.** -/
theorem galAut_finite : (galAut vQ c).Finite := by
  have : galAut vQ c = Set.range
      fun σ : ∀ j, Factor' K vQ (c j) ≃ₐ[baseField vQ] Factor' K vQ (c j) =>
        ⇑(mapAlgHom vQ c σ) := by
    ext φ
    simp only [galAut, Set.mem_setOf_eq, Set.mem_range]
    exact ⟨fun ⟨σ, h⟩ => ⟨σ, h.symm⟩, fun ⟨σ, h⟩ => ⟨σ, h.symm⟩⟩
  rw [this]
  exact Set.finite_range _

/-- The automorphisms `⊗_j σ_j` are continuous (linear maps of finite-dimensional spaces). -/
lemma continuous_mapAlgHom (σ : ∀ j, Factor' K vQ (c j) ≃ₐ[baseField vQ] Factor' K vQ (c j)) :
    Continuous (mapAlgHom vQ c σ) :=
  LinearMap.continuous_of_finiteDimensional (mapAlgHom vQ c σ).toLinearMap

/-- Indeterminacy automorphisms are continuous. -/
lemma continuous_of_mem_galAut {φ : Tensor K vQ c → Tensor K vQ c} (hφ : φ ∈ galAut vQ c) :
    Continuous φ := by
  obtain ⟨σ, rfl⟩ := hφ
  exact continuous_mapAlgHom vQ c σ

/-! ### Admissibility of unions over the indeterminacies -/

/-- **The union of the images of a compact set of positive Haar measure under the
Galois automorphisms is admissible.** -/
theorem iUnion_galAut_admissible {S : Set (Tensor K vQ c)} (hS : IsCompact S)
    (hpos : 0 < haar vQ c S) : (⋃ φ ∈ galAut vQ c, φ '' S) ∈ admissible vQ c := by
  have hsub : S ⊆ ⋃ φ ∈ galAut vQ c, φ '' S := fun x hx =>
    Set.mem_iUnion₂.mpr ⟨id, id_mem_galAut vQ c, ⟨x, hx, rfl⟩⟩
  have hcpt : IsCompact (⋃ φ ∈ galAut vQ c, φ '' S) :=
    (galAut_finite vQ c).isCompact_biUnion fun φ hφ => hS.image (continuous_of_mem_galAut vQ c hφ)
  refine ⟨?_, ?_, hcpt.isClosed.measurableSet, lt_of_lt_of_le hpos (measure_mono hsub),
    hcpt.measure_lt_top⟩
  · obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
    exact ⟨x, hsub hx⟩
  · rw [hcpt.isClosed.closure_eq]
    exact hcpt

/-- **`LocalTheory.galAut_theta_admissible`**: the union of the images of a scaled integral
structure under the Galois automorphisms of the packet is admissible. -/
theorem galAut_theta_admissible (s : Tensor K vQ c) (hs : IsUnit s) :
    (⋃ φ ∈ galAut vQ c, φ '' (s • integralAt vQ c)) ∈ admissible vQ c :=
  iUnion_galAut_admissible vQ c (isCompact_smul_integralAt s) (haar_smul_integralAt_pos hs)

/-- The Galois automorphisms of the packet preserve `(R_I)^∼`, at every prime. -/
theorem galAut_integral_subset (p : Nat.Primes) (c : ι → Place K) :
    ∀ φ ∈ galAut (.finite p) c,
      φ '' integralAt (.finite p) c ⊆ integralAt (.finite p) c := by
  rintro _ ⟨σ, rfl⟩
  exact mapAlgHom_image_integral_subset p c σ

end LocalConstruct

end Iut
