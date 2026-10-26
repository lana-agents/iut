/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.RecFunctionField
import WeilCurves.ConstantExtension.ExtPlaces

/-!
# [AbsTopIII] Thm 1.9 (e): the points of the reconstructed triple are determined by `U_x`

In [AbsTopIII] Thm 1.9 (e) (`Topics in Absolute Anabelian Geometry III.txt` l.2179–2185) the
points of the triple of Prop 1.3 (l.1691–1721) are indexed by the decomposition groups of (a), and
the subgroups `U_x = {f | f(x) = 1}` are read off from the restrictions `s_x^*` of the Kummer
classes to them (`mem_U_recTriple_iff`). For the points to be recovered from these data, distinct
points must have distinct subgroups `U_x`. Here:

* `Uchida.ValEvalData.Iso.U_injective`: injectivity of `x ↦ U_x` is invariant under isomorphisms
  of triples;
* **`Uchida.ofFunctionField.exists_mem_U_notMem_U`**: for distinct places `P ≠ Q` of a function
  field `K / k` (`k` algebraically closed) there is `f` with `f(P) = 1` and `f ∉ U_Q`: take
  `g = x⁻¹` for an `x` whose only zero is `Q` (weil-curves `exists_zero_only_at`, Riemann's
  inequality), so `g` is regular at `P` with a pole at `Q`, and `f = 1 + g − g(P)`;
* **`recTriple_U_injective`**: in the reconstructed triple of the NF-portion, distinct points have
  distinct `U_x`; with `mem_U_recTriple_iff`, an NF-point is determined by which Kummer classes
  restrict trivially to its decomposition group.
-/

open WeilCurves.FunctionField

universe u

noncomputable section

namespace Iut.Reconstruction

namespace Uchida

namespace ValEvalData.Iso

variable {D D' : ValEvalData.{u}}

/-- **Injectivity of `x ↦ U_x` is transported by isomorphisms of triples.** -/
theorem U_injective (e : D.Iso D') (h : Function.Injective D.U) : Function.Injective D'.U := by
  intro y₁ y₂ hy
  have hx : D.U (e.σ.symm y₁) = D.U (e.σ.symm y₂) := by
    ext f
    rw [← e.mem_U_iff, ← e.mem_U_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hy]
  have := h hx
  rwa [e.σ.symm.injective.eq_iff] at this

end ValEvalData.Iso

namespace ofFunctionField

variable {k : Type*} {K : Type u} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  [IsFunctionField k K]

/-- **Distinct places are separated by the subgroups `U_x`**: for `P ≠ Q` there is `f ∈ Kˣ` with
`f(P) = 1` and `f ∉ U_Q`. -/
theorem exists_mem_U_notMem_U {P Q : Place k K} (h : P ≠ Q) :
    ∃ f : Kˣ, f ∈ (ofFunctionField k K).U P ∧ f ∉ (ofFunctionField k K).U Q := by
  obtain ⟨x, hxt, hxQ, hx⟩ := exists_zero_only_at Q
  have hgt : Transcendental k x⁻¹ := transcendental_inv hxt
  have hgP : 0 ≤ P.ord x⁻¹ := by
    rw [Place.ord_inv]
    have := hx P h
    omega
  have hgQ : Q.ord x⁻¹ < 0 := by
    rw [Place.ord_inv]
    omega
  have hv : P.IsValue x⁻¹ (P.value x⁻¹) := P.isValue_value (P.mem_of_ord_nonneg hgP)
  have hu : P.IsValue (x⁻¹ - algebraMap k K (P.value x⁻¹)) 0 := by
    simpa using hv.sub (Place.isValue_algebraMap (P := P) (P.value x⁻¹))
  set f₀ : K := 1 + (x⁻¹ - algebraMap k K (P.value x⁻¹)) with hf₀
  have hf₀0 : f₀ ≠ 0 := by
    intro h0
    apply hgt
    have e : x⁻¹ = algebraMap k K (P.value x⁻¹ - 1) := by
      rw [map_sub, map_one]
      linear_combination h0
    rw [e]
    exact isAlgebraic_algebraMap _
  have hsub : (Units.mk0 f₀ hf₀0 : K) - 1 = x⁻¹ - algebraMap k K (P.value x⁻¹) := by
    simp [hf₀]
  refine ⟨Units.mk0 f₀ hf₀0, ?_, ?_⟩
  · rw [mem_U_iff, hsub]
    exact (Place.isValue_zero_iff (P := P)).mp hu
  · rw [mem_U_iff, hsub]
    intro hmem
    have hm : x⁻¹ - algebraMap k K (P.value x⁻¹) ∈ Q.1 :=
      Q.1.nonunits_subset hmem
    have hx1 : x⁻¹ ∈ Q.1 := by
      have := add_mem hm (Q.algebraMap_mem (P.value x⁻¹))
      simpa using this
    have := Q.ord_nonneg_of_mem hx1
    omega

/-- **`x ↦ U_x` is injective** for the triple of a function field. -/
theorem U_injective : Function.Injective (ofFunctionField k K).U := by
  intro P Q hPQ
  by_contra h
  obtain ⟨f, hP, hQ⟩ := exists_mem_U_notMem_U h
  exact hQ (hPQ ▸ hP)

end ofFunctionField

end Uchida

namespace Thm19

open KummerTheory Curve AffOrbicurve CurvesJacobian.Kummer IsLocalRing CurvesJacobian StageIdx

attribute [local instance] isAlgClosed_algebraicClosure isFunctionField_fnf
  CurvesJacobian.isFunctionField_F

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [CharZero Ω] [Fact (D.H ≤ D.HL)] [NumberField k] (N : NFModel D)
  (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))

/-- **Distinct points of the reconstructed triple have distinct `U_x`** ([AbsTopIII] Thm 1.9 (e)):
so the points are recovered from the subgroups `U_x`, which `mem_U_recTriple_iff` reads off from
the restrictions of the Kummer classes to the decomposition groups. -/
theorem recTriple_U_injective : Function.Injective (recTriple N hkF).U :=
  (recIso N hkF).U_injective Uchida.ofFunctionField.U_injective

end Thm19

end Iut.Reconstruction
