/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.P1ThreeLineQuotient
import Iut.Reconstruction.Cusp.LineCuspGenerators
import TemperedFundamentalGroups.SemistableReduction.P1ThreeHomAction
import TemperedFundamentalGroups.SemistableReduction.P1ThreeDegree
import TemperedFundamentalGroups.SemistableReduction.P1ThreeGeomConnectedAlg
import TemperedFundamentalGroups.SemistableReduction.P1ThreeFlatStructure
import TemperedFundamentalGroups.SemistableReduction.P1ThreeFixedPoint
import TemperedFundamentalGroups.SemistableReduction.AlgStrLift01
import TemperedFundamentalGroups.SemistableReduction.StabIdeal

/-!
# Cusp generators of a tame special cover stabilise special points (MR13's B4′, "A2⁻")

For a datum `D` of a tame Galois cover of `ℙ¹_k ∖ {0, 1, ā}` (tfg's `P1Three.Datum`) with a group
`G` acting faithfully on the covering `C1` of `V₁`, `C1` connected of generic rank `|G|` (the
special-side hypotheses, explicit arguments; MR13-plan, lead decision (ii) after run 16):

* **`P1ThreeCuspStab.cusp_one`, `cusp_inv`, `cusp_inf`**: at a place `W ⊇ K̄` of `Ω` centred at a
  cusp `s = 1, ā⁻¹, ∞` of `V₁ ⊗ K̄`, the coordinate `X = t (t − 1) (t − a) = (1 − s)(1 − ā s)/s³` of
  the base and `t − τ` (`τ = 1, a, 0`, `t = 1/s`) lie in the maximal ideal of `W`;
* **`P1ThreeCuspStab.exists_special_point`** ("A2⁻"): for a point `u : B₁ → Ω` of the generic fibre
  of the lift with `σ ∘ u = u ∘ F σ` and a place `W` over the cusp `t = τ`, there is a special
  point `𝔪` of `C0` over `t̄ = τ̄` fixed by `F σ` for every inertia element `σ` of `W`
  (residue map of `W` on the extension of `u` to `B₀`, tfg `AlgStr.lift0`,
  `P1Three.Datum.exists_fixed_special_point`);
* **`P1ThreeCuspStab.exists_cusp_stabilisers`** (**B4′**): there are `z₀, z₁, z₂ ∈ G` with
  `z₀ z₁ z₂ = 1`, any two generating `G`, and a numbering `τ` of the cusps `0, 1, a` such that each
  `z j` is conjugate to an element of `G` fixing a special point of `C0` over `t̄ = τ̄ j`.
-/

open Polynomial TensorProduct

universe u

noncomputable section

namespace Iut.Reconstruction.P1ThreeCuspStab

open SemistableReduction SemistableReduction.P1Three TateLevel AdmissibleLift EtaleTower
  ProjectiveLine CurvesJacobian.Cusp AffOrbicurve P1ThreeLineQuotient

/-! ### Valuations at the cusps -/

section Valuation

variable {Kb Ω : Type*} [Field Kb] [Field Ω] [Algebra Kb Ω] (W : ValuationSubring Ω)
  (hW : ∀ c : Kb, algebraMap Kb Ω c ∈ W) (b : Kb) {x : Ω}

include hW in
lemma valuation_algebraMap {c : Kb} (hc : c ≠ 0) : W.valuation (algebraMap Kb Ω c) = 1 := by
  have h1 : W.valuation (algebraMap Kb Ω c) ≤ 1 := (W.valuation_le_one_iff _).2 (hW c)
  have h2 : W.valuation (algebraMap Kb Ω c⁻¹) ≤ 1 := (W.valuation_le_one_iff _).2 (hW c⁻¹)
  have h3 : W.valuation (algebraMap Kb Ω c) * W.valuation (algebraMap Kb Ω c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : _) = W.valuation (algebraMap Kb Ω c) * W.valuation (algebraMap Kb Ω c⁻¹) := h3.symm
    _ ≤ W.valuation (algebraMap Kb Ω c) := mul_le_of_le_one_right' h2

include hW in
/-- **The cusp `s = 1` (`t = 1`).** -/
lemma cusp_one (hv : W.valuation (x - 1) < 1) :
    W.valuation ((1 - x) * (1 - algebraMap Kb Ω b * x) / x ^ 3) < 1 ∧
      W.valuation (x⁻¹ - algebraMap Kb Ω 1) < 1 := by
  have hx1 : W.valuation x = 1 := by
    have h := Valuation.map_eq_of_sub_lt W.valuation (x := 1) (y := x) (by rwa [map_one])
    rwa [map_one] at h
  have hx0 : x ≠ 0 := fun h ↦ by rw [h, map_zero] at hx1; exact zero_ne_one hx1
  have hxW : x ∈ W := (W.valuation_le_one_iff _).1 hx1.le
  have hm : W.valuation (1 - algebraMap Kb Ω b * x) ≤ 1 :=
    (W.valuation_le_one_iff _).2 (W.sub_mem W.one_mem (W.mul_mem _ _ (hW b) hxW))
  have h1x : W.valuation (1 - x) < 1 := by rwa [Valuation.map_sub_swap]
  refine ⟨?_, ?_⟩
  · rw [map_div₀, map_mul, map_pow, hx1, one_pow, div_one]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hm) h1x
  · have : x⁻¹ - algebraMap Kb Ω 1 = (1 - x) / x := by rw [map_one]; field_simp
    rw [this, map_div₀, hx1, div_one]
    exact h1x

include hW in
/-- **The cusp `s = b⁻¹` (`t = b`).** -/
lemma cusp_inv (hb0 : b ≠ 0) (hv : W.valuation (x - algebraMap Kb Ω b⁻¹) < 1) :
    W.valuation ((1 - x) * (1 - algebraMap Kb Ω b * x) / x ^ 3) < 1 ∧
      W.valuation (x⁻¹ - algebraMap Kb Ω b) < 1 := by
  have hbinv := valuation_algebraMap W hW (inv_ne_zero hb0)
  have hb := valuation_algebraMap W hW hb0
  have hx1 : W.valuation x = 1 :=
    (Valuation.map_eq_of_sub_lt W.valuation (by rwa [hbinv])).trans hbinv
  have hx0 : x ≠ 0 := fun h ↦ by rw [h, map_zero] at hx1; exact zero_ne_one hx1
  have hxW : x ∈ W := (W.valuation_le_one_iff _).1 hx1.le
  have hm : W.valuation (1 - x) ≤ 1 :=
    (W.valuation_le_one_iff _).2 (W.sub_mem W.one_mem hxW)
  have hkey : 1 - algebraMap Kb Ω b * x = -(algebraMap Kb Ω b * (x - algebraMap Kb Ω b⁻¹)) := by
    have hbb : algebraMap Kb Ω b * algebraMap Kb Ω b⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hb0, map_one]
    linear_combination -hbb
  have h1b : W.valuation (1 - algebraMap Kb Ω b * x) < 1 := by
    rw [hkey, Valuation.map_neg, map_mul, hb, one_mul]
    exact hv
  refine ⟨?_, ?_⟩
  · rw [map_div₀, map_mul, map_pow, hx1, one_pow, div_one]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hm) h1b
  · have : x⁻¹ - algebraMap Kb Ω b = (1 - algebraMap Kb Ω b * x) / x := by field_simp
    rw [this, map_div₀, hx1, div_one]
    exact h1b

include hW in
/-- **The cusp `s = ∞` (`t = 0`).** -/
lemma cusp_inf (hx0 : x ≠ 0) (hv : W.valuation x⁻¹ < 1) :
    W.valuation ((1 - x) * (1 - algebraMap Kb Ω b * x) / x ^ 3) < 1 ∧
      W.valuation (x⁻¹ - algebraMap Kb Ω 0) < 1 := by
  have hxW : x⁻¹ ∈ W := (W.valuation_le_one_iff _).1 hv.le
  have h1 : W.valuation (x⁻¹ - 1) ≤ 1 :=
    (W.valuation_le_one_iff _).2 (W.sub_mem hxW W.one_mem)
  have h2 : W.valuation (x⁻¹ - algebraMap Kb Ω b) ≤ 1 :=
    (W.valuation_le_one_iff _).2 (W.sub_mem hxW (hW b))
  refine ⟨?_, by rwa [map_zero, sub_zero]⟩
  have : (1 - x) * (1 - algebraMap Kb Ω b * x) / x ^ 3 =
      x⁻¹ * ((x⁻¹ - 1) * (x⁻¹ - algebraMap Kb Ω b)) := by
    field_simp
  rw [this, map_mul, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (mul_le_one' h1 h2)) hv

end Valuation

/-! ### A2⁻: inertia elements of a place over a cusp fix a special point -/

section Point

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]
  (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  [IsAdicComplete (Ideal.span {ϖ}) O] [(Ideal.span {ϖ}).IsMaximal]
  (Kb : Type u) [Field Kb] [Algebra O Kb]
  {D : Datum O θ a} {G : Type*} [Group G]
  (act : G → D.Hom D) (hone : act 1 = Datum.Hom.id D)
  (hmul : ∀ g h, act (g * h) = (act g).comp (act h))
  (L : AdicChartAlgSystem.Algebraization (Datum.systemD hϖ hker hO D))
  {ψ : ChartModule.Hom (twoChart O a).chartModule L.N} (hψ : (twoChart O a).algStr.IsHom L.B ψ)
  {Ω : Type u} [Field Ω] [Algebra Kb Ω] {P : Type u} [Field P] [Algebra P Ω] {t : Ω}

omit [IsAdicComplete (Ideal.span {ϖ}) O] [(Ideal.span {ϖ}).IsMaximal] in
/-- `y = u(Y)` satisfies `y (1 − t)(1 − ā t) = t³` (the relation `eq1` of `R1`). -/
lemma u_X1_mul (u : L.B.Ring1 →+* Ω)
    (hu1 : ∀ o : O, u (L.B.const1 o) = algebraMap Kb Ω (algebraMap O Kb o))
    (hus : u (@algebraMap (R1 O a) L.B.Ring1 _ _ (L.B.algR1 hψ) (s1 O a)) = t) :
    u L.B.X1 * ((1 - t) * (1 - algebraMap Kb Ω (algebraMap O Kb a) * t)) = t ^ 3 := by
  letI : Algebra (R1 O a) L.B.Ring1 := L.B.algR1 hψ
  have hX1 : algebraMap (R1 O a) L.B.Ring1 (y1 O a) = L.B.X1 := by
    have h := RingHom.congr_fun (algR1_comp hψ) X
    rw [RingHom.comp_apply] at h
    rw [show y1 O a = algebraMap O[X] (R1 O a) X from rfl, h]
    simp [ProjectiveLine.ChartModule.AlgStr.polyHom1]
  have hus' : u (algebraMap (R1 O a) L.B.Ring1 (s1 O a)) = t := hus
  have hc : ∀ o : O, u (algebraMap (R1 O a) L.B.Ring1 (algebraMap O (R1 O a) o)) =
      algebraMap Kb Ω (algebraMap O Kb o) := fun o ↦ by rw [algR1_const hψ, hu1]
  have h := congrArg (fun r ↦ u (algebraMap (R1 O a) L.B.Ring1 r)) (eq1 O a)
  simp only [map_sub, map_add, map_mul, map_pow, map_zero] at h
  simp only [hc, hus', hX1, map_one] at h
  linear_combination -h

include ha0 ha1 hone hmul in
/-- **A2⁻ at a place over a cusp.** Let `u : B₁ → Ω` be a point of the generic fibre of the lift
(elements of `O` mapped through `O → K̄ → Ω`, `u(s) = t ≠ 0`) and `F : Aut(Ω / P) → G` with
`σ ∘ u = u ∘ (F σ)` on `B₁`. If `W ⊇ K̄` is a place of `Ω` at which `X = (1 − t)(1 − ā t)/t³` and
`t⁻¹ − τ` lie in the maximal ideal, then there is a maximal ideal `𝔪` of `C0` (a special point)
containing the reduction of `t − τ` (in the cusp chart, `t = t0`) and fixed by `(act (F σ)).φ0` for
every inertia element `σ` of `W`. -/
theorem exists_special_point (hOK : Function.Injective (algebraMap O Kb))
    (u : L.B.Ring1 →+* Ω)
    (hu1 : ∀ o : O, u (L.B.const1 o) = algebraMap Kb Ω (algebraMap O Kb o))
    (hus : u (@algebraMap (R1 O a) L.B.Ring1 _ _ (L.B.algR1 hψ) (s1 O a)) = t) (ht0 : t ≠ 0)
    (F : (Ω ≃ₐ[P] Ω) → G)
    (hF : ∀ σ b, σ (u b) = u (Datum.ring1Act hϖ hker ha0 ha1 hO act L hone hmul (F σ) b))
    (W : ValuationSubring Ω) (hW : ∀ c : Kb, algebraMap Kb Ω c ∈ W) (τ : O)
    (hq : W.valuation ((1 - t) * (1 - algebraMap Kb Ω (algebraMap O Kb a) * t) / t ^ 3) < 1)
    (hτ : W.valuation (t⁻¹ - algebraMap Kb Ω (algebraMap O Kb τ)) < 1) :
    ∃ 𝔪 : Ideal D.S0.C0, 𝔪.IsMaximal ∧
      specialFibreEquiv0 D.Sp hϖ hker D.S0 D.om hO L.hα L.hB
        (Ideal.Quotient.mk _ (ψ.f0 (t0 O a - algebraMap O (R0 O a) τ))) ∈ 𝔪 ∧
      ∀ σ : Ω ≃ₐ[P] Ω, σ ∈ GaloisPi1.inertia (P := P) W → 𝔪.comap (act (F σ)).φ0 = 𝔪 := by
  letI i1 : Algebra (R1 O a) L.B.Ring1 := L.B.algR1 hψ
  have hrel := u_X1_mul hϖ hker hO Kb L hψ u hu1 hus
  have hy0 : u L.B.X1 ≠ 0 := fun h ↦ by
    rw [h, zero_mul] at hrel
    exact pow_ne_zero 3 ht0 hrel.symm
  have hu : IsUnit (u L.B.X1) := isUnit_iff_ne_zero.2 hy0
  set u0 := L.B.lift0 u hu with hu0
  have hu0c : ∀ o, u0 (L.B.const0 o) = algebraMap Kb Ω (algebraMap O Kb o) := fun o ↦ by
    rw [hu0, ChartModule.AlgStr.lift0_apply, L.B.r0Hom_const0, ← L.B.r1Hom_const1,
      ChartModule.AlgStr.lift01_r1Hom, hu1]
  have hu0X : u0 L.B.X0 = (1 - t) * (1 - algebraMap Kb Ω (algebraMap O Kb a) * t) / t ^ 3 := by
    have h := L.B.lift0_X0_mul u hu
    rw [← hu0] at h
    rw [eq_div_iff (pow_ne_zero 3 ht0), ← hrel, ← mul_assoc, h, one_mul]
  -- the point `t0 ↦ t⁻¹`
  have hm : (twoChart O a).ρ0 (t0 O a) * (twoChart O a).ρ1 (s1 O a) = 1 := by
    change rho0 O a (t0 O a) * so O a = 1
    rw [rho0_t0, mul_comm]
    exact so_mul_sinv O a
  have hu0t : u0 (ψ.f0 (t0 O a)) = t⁻¹ := by
    have h := L.B.lift0_mul_eq_one u hu (ChartModule.AlgStr.IsHom.r0Hom_mul_r1Hom L.B hψ hm)
    have hs : u (hψ.ringHom1 ((TwoChartRings.ring1Equiv (twoChart O a)).symm (s1 O a))) = t :=
      hus
    rw [hs] at h
    exact eq_inv_of_mul_eq_one_left h
  have hu0W : ∀ b, u0 b ∈ W := L.B.mem_of_X0 W u0 (fun o ↦ by rw [hu0c]; exact hW _)
    (by rw [hu0X]; exact (W.valuation_le_one_iff _).1 hq.le)
  -- the residue point `χ : B₀ → W/𝔪_W`
  let ι : L.B.Ring0 →+* W :=
    { toFun := fun b ↦ ⟨u0 b, hu0W b⟩
      map_one' := Subtype.ext (map_one u0)
      map_mul' := fun x y ↦ Subtype.ext (map_mul u0 x y)
      map_zero' := Subtype.ext (map_zero u0)
      map_add' := fun x y ↦ Subtype.ext (map_add u0 x y) }
  let χ : L.B.Ring0 →+* IsLocalRing.ResidueField W := (IsLocalRing.residue W).comp ι
  have hχ0 : ∀ b, χ b = 0 ↔ W.valuation (u0 b) < 1 := fun b ↦ by
    change IsLocalRing.residue W (ι b) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, W.valuation_lt_one_iff]
    rfl
  letI : Algebra O (IsLocalRing.ResidueField W) := (χ.comp L.B.const0).toAlgebra
  have hF' : Function.Injective (algebraMap O (IsLocalRing.ResidueField W)) := by
    rw [injective_iff_map_eq_zero]
    intro o ho
    have h := (hχ0 _).1 ho
    rw [hu0c] at h
    by_contra hne
    have hne' : algebraMap O Kb o ≠ 0 := fun h' ↦ hne (hOK (h'.trans (map_zero _).symm))
    rw [valuation_algebraMap W hW hne'] at h
    exact lt_irrefl _ h
  obtain ⟨𝔪, hmax, hkerχ, hfix⟩ := Datum.exists_fixed_special_point hϖ hker ha0 ha1 hO act L
    hF' χ (fun _ ↦ rfl) ((hχ0 _).2 (by rw [hu0X]; exact hq))
  refine ⟨𝔪, hmax, hkerχ _ ((hχ0 _).2 ?_), fun σ hσ ↦ hfix _ fun b ↦ ?_⟩
  · have h2 : (TwoChartRings.ring0Equiv (twoChart O a)).symm
        (algebraMap O (twoChart O a).R0 τ) = (twoChart O a).algStr.const0 τ := by
      rw [← TwoChartRings.ring0Equiv_const0, RingEquiv.symm_apply_apply]
    have e1 : (TwoChartRings.ring0Equiv (twoChart O a)).symm (t0 O a - algebraMap O (R0 O a) τ) =
        (TwoChartRings.ring0Equiv (twoChart O a)).symm (t0 O a) -
          (twoChart O a).algStr.const0 τ := by
      rw [← h2]
      exact map_sub _ _ _
    have h : ψ.f0 (t0 O a - algebraMap O (R0 O a) τ) =
        hψ.ringHom0 ((TwoChartRings.ring0Equiv (twoChart O a)).symm (t0 O a)) -
          L.B.const0 τ :=
      (congrArg hψ.ringHom0 e1).trans (by rw [map_sub, hψ.ringHom0_const0])
    rw [h, map_sub, hu0c]
    change W.valuation (u0 (ψ.f0 (t0 O a)) - _) < 1
    rw [hu0t]
    exact hτ
  · have heq := ChartModule.AlgStr.IsHom.lift0_equivariant
      (Datum.isHom_algMap hϖ hker ha0 ha1 hO (act (F σ)) L L) u hu (σ : Ω →+* Ω)
      (fun b ↦ hF σ b) b
    rw [← hu0] at heq
    rw [← sub_eq_zero, ← map_sub, hχ0, map_sub, ← heq]
    exact hσ _ (hu0W b)

end Point

/-! ### B4′ -/

section Main

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]
  (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  [IsDomain O] [IsDiscreteValuationRing O] [(Ideal.span {ϖ}).IsMaximal]
  [IsAdicComplete (Ideal.span {ϖ}) O] [IsAlgClosed k] (hϖ0 : ϖ ≠ 0) (hϖu : ¬IsUnit ϖ)
  (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
  (Kb : Type u) [Field Kb] [IsAlgClosed Kb] [CharZero Kb] [Algebra K Kb] [Algebra O Kb]
  [IsScalarTower O K Kb] [Algebra.IsAlgebraic K Kb]
  {D : Datum O θ a} {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  (act : G → D.Hom D) (hone : act 1 = Datum.Hom.id D)
  (hmul : ∀ g h, act (g * h) = (act g).comp (act h))
  {Ω : Type u} [Field Ω] [Algebra Kb Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ Kb t) Ω]
  (ht : Transcendental Kb t)

open scoped Classical in
/-- The value `τ ∈ {1, a, 0}` of `t = 1/s` at a cusp `s ∈ {1, ā⁻¹, ∞}`. -/
def cuspValue (a : O) : Option (lineS Kb a) → O
  | none => 0
  | some x => if x.1 = 1 then 1 else a

/-- **The special point over a cusp `t̄ = τ̄`**: `𝔪` contains the reduction of `t − τ` (in the
cusp chart `R0`, through the structure map `R0 → C0` of the special cover). -/
def LiesOver (D : Datum O θ a) (τ : O) (𝔪 : Ideal D.S0.C0) : Prop :=
  (letI := (overlap D.Sp hϖ hker D.S0 D.om hO).algC0' 0
   algebraMap (overlap D.Sp hϖ hker D.S0 D.om hO).B0' (overlap D.Sp hϖ hker D.S0 D.om hO).C0
     (t0 O a - algebraMap O (R0 O a) τ)) ∈ 𝔪

include hϖ0 hϖu K Kb ht ha0 ha1 hone hmul in
/-- **B4′ (Route B's generation statement, MR13-plan run 16)**: for a tame special cover with group
`G` (a datum `D` of a cover of `ℙ¹_k ∖ {0, 1, ā}` with `G` acting faithfully on `C1`, `C1`
connected of generic rank `|G|`), there are `z₀, z₁, z₂ ∈ G` with `z₀ z₁ z₂ = 1`, any two of which
generate `G`, and a numbering `τ : Fin 3 → {0, 1, a}` of the cusps (injective) such that each
`z j` is a conjugate `y x y⁻¹` of an element `x` fixing a special point `𝔪` of `C0` over
`t̄ = τ̄ j`. (Images of the cuspidal generators of `π₁ᵉᵗ(ℙ¹_{K̄} ∖ {0, 1, ā})` under the
Galois quotient of the lifted cover; "A2⁻": inertia ⊆ stabiliser of the reduction.)
The fields `K = Frac O`, an algebraic closure `K̄` and a separably closed `Ω ⊇ K̄(t)` Galois over
`K̄(t)` are auxiliary choices; the conclusion does not depend on them. -/
theorem exists_cusp_stabilisers
    (hfaith : ∀ g, (∀ c, (act g).φ1 c = c) → g = 1)
    (hconn : ∀ e : D.Sp.C1, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hdeg : Module.finrank (Ts θ (R1 O a)) D.Sp.C1 = Nat.card G) :
    ∃ (z : Fin 3 → G) (τ : Fin 3 → O), z 0 * z 1 * z 2 = 1 ∧
      (∀ i j, i ≠ j → Subgroup.closure {z i, z j} = ⊤) ∧
      (∀ j, τ j = 0 ∨ τ j = 1 ∨ τ j = a) ∧ Function.Injective τ ∧
      ∀ j, ∃ (𝔪 : Ideal D.S0.C0) (y x : G), 𝔪.IsMaximal ∧ LiesOver hϖ hker hO D (τ j) 𝔪 ∧
        z j = y * x * y⁻¹ ∧ 𝔪.comap (act x).φ0 = 𝔪 := by
  classical
  have hOK := injective_algebraMap_O O K Kb
  -- the lift, typed over `system` (no comparison with `systemD` except in `L`)
  obtain ⟨N, hN0, hN1, B, α, hα, hc, hB, -, hf1, ψ, hψ, hψα⟩ :=
    exists_flat_algebraization_structureMap D.Sp hϖ hker D.S0 D.om hO hϖ0
  haveI := hN0
  haveI := hN1
  haveI := hf1
  let L : AdicChartAlgSystem.Algebraization (Datum.systemD hϖ hker hO D) := ⟨N, B, α, hα, hc, hB⟩
  have hψα' := structure_f1 hϖ hker D.Sp D.S0 D.om hO hψα
  letI i1 : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
  letI i2 : Algebra O B.Ring1 := algO1 B
  haveI : IsScalarTower O (R1 O a) B.Ring1 := isScalarTower_algO1 hψ
  letI i3 : Algebra (Kb ⊗[O] R1 O a) (Kb ⊗[O] B.Ring1) :=
    (tensorMap O (R1 O a) B.Ring1 Kb).toRingHom.toAlgebra
  have h₃ : algebraMap (Kb ⊗[O] R1 O a) (Kb ⊗[O] B.Ring1) =
      (tensorMap O (R1 O a) B.Ring1 Kb).toRingHom := rfl
  have hϖL : IsUnit (algebraMap O Kb ϖ) :=
    isUnit_iff_ne_zero.2 fun h ↦ hϖ0 (hOK (h.trans (map_zero _).symm))
  haveI : Module.Finite (R1 O a) B.Ring1 := finite_ring1 hψ
  haveI : Algebra.Etale (Kb ⊗[O] R1 O a) (Kb ⊗[O] B.Ring1) :=
    etale_tensor_lift D.Sp hϖ hker D.S0 D.om hO hϖ0 hα hB hψ hψα Kb hϖL h₃
  letI : Algebra O[X] B.Ring1 := algX1 B
  haveI : IsScalarTower O O[X] B.Ring1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := B.flat_polyHom1
  haveI : Module.Flat O B.Ring1 := Module.Flat.trans O O[X] B.Ring1
  haveI : Module.Flat O (R1 O a) := Module.Flat.trans O O[X] (R1 O a)
  haveI hC1 : Nontrivial D.Sp.C1 := by
    haveI := isDomain_Ts_R1 a (θ := θ)
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h0 := Module.finrank_zero_of_subsingleton (R := Ts θ (R1 O a)) (M := D.Sp.C1)
    rw [hdeg] at h0
    exact (Nat.card_pos (α := G)).ne' h0
  haveI : Nontrivial B.Ring1 := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have hs : Subsingleton (B.Ring1 ⧸ Ideal.span {B.const1 ϖ}) :=
      Ideal.Quotient.mk_surjective.subsingleton
    exact not_subsingleton D.Sp.C1
      ((specialFibreEquiv1 D.Sp hϖ hker D.S0 D.om hO hα hB).symm.injective.subsingleton)
  have hconnC : ∀ c : Kb ⊗[O] B.Ring1, IsIdempotentElem c → c = 0 ∨ c = 1 := fun c hc ↦
    connected_lift_algebraic D.Sp hϖ hker D.S0 D.om hO hα hB hϖ0 K hconn Kb hc
  have hdeg' : Module.finrank (R1 O a) B.Ring1 = Nat.card G :=
    (finrank_lift D.Sp hϖ hker D.S0 D.om hO hα hB hψ hψα).trans hdeg
  obtain ⟨f, u, hfs, hfc, hR, hOu, hσ⟩ := exists_point_of_tensor Kb ht hOK h₃ hconnC
    (lineS Kb a) (baseEquiv ha0 ha1 hO Kb)
    (Datum.ring1AlgAct hϖ hker ha0 ha1 hO act L hϖu hone hmul hψ hψα')
    (Datum.ring1AlgAct_injective hϖ hker ha0 ha1 hO act L hϖu hone hmul hfaith hψ hψα') hdeg'
  have hu1 : ∀ o : O, u (L.B.const1 o) = algebraMap Kb Ω (algebraMap O Kb o) := fun o ↦ by
    have hc' : L.B.const1 o = algebraMap O B.Ring1 o := by
      simp [L, ProjectiveLine.ChartModule.AlgStr.polyHom1, RingHom.algebraMap_toAlgebra]
    rw [hc', hOu, baseEquiv_tmul_one, AlgHom.commutes]
  have hus : u (@algebraMap (R1 O a) L.B.Ring1 _ _ (L.B.algR1 hψ) (s1 O a)) = t := by
    rw [show (@algebraMap (R1 O a) L.B.Ring1 _ _ (L.B.algR1 hψ) (s1 O a)) =
      algebraMap (R1 O a) B.Ring1 (s1 O a) from rfl, hR, baseEquiv_s1, lineToΩS_lineTS]
  have ha := algebraMap_a_ne_zero ha0 hO Kb
  have ha1' := algebraMap_a_ne_one ha1 hO Kb
  have hS : (lineS Kb a).card = 2 := Finset.card_pair (one_ne_inv _ ha1')
  obtain ⟨z, e, he, hprod, hgen, hconj⟩ := LineCuspGenerators.exists_cusp_gen hS f hfc hfs
  have hbij : Function.Bijective e := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨he, by simp [hS]⟩
  let c : Fin 3 → Option (lineS Kb a) := fun j ↦ (Equiv.ofBijective e hbij).symm j
  have hec : ∀ j, e (c j) = j := fun j ↦ (Equiv.ofBijective e hbij).apply_symm_apply j
  have hc : Function.Injective c := (Equiv.ofBijective e hbij).symm.injective
  have ht0 : t ≠ 0 := fun h ↦ ht (by rw [h]; exact isAlgebraic_zero)
  -- the values of `τ`
  have hτv : ∀ x : Option (lineS Kb a), cuspValue Kb a x = 0 ∨ cuspValue Kb a x = 1 ∨
      cuspValue Kb a x = a := by
    rintro (_ | x)
    · exact Or.inl rfl
    · simp only [cuspValue]
      split_ifs <;> simp
  have hτinj : Function.Injective (cuspValue Kb a) := by
    have h0 : (0 : O) ≠ 1 := fun h ↦ ha0 (by
      have := congrArg θ h
      rw [map_zero, map_one] at this
      exact absurd this zero_ne_one)
    have ha0' : a ≠ 0 := fun h ↦ ha0 (by rw [h, map_zero])
    have ha1'' : (1 : O) ≠ a := fun h ↦ ha1 (by rw [← h, map_one])
    have hmem : ∀ x : lineS Kb a, x.1 ≠ 1 → x.1 = (algebraMap O Kb a)⁻¹ := fun x hx ↦ by
      have := x.2
      simp only [lineS, lineSK, Finset.mem_insert, Finset.mem_singleton] at this
      tauto
    rintro (_ | x) (_ | x') h <;> simp only [cuspValue] at h
    · rfl
    · split_ifs at h with h1 <;> [exact absurd h h0; exact absurd h.symm ha0']
    · split_ifs at h with h1 <;> [exact absurd h.symm h0; exact absurd h ha0']
    · congr 1
      apply Subtype.ext
      split_ifs at h with h1 h2 h2
      · rw [h1, h2]
      · exact absurd h ha1''
      · exact absurd h.symm ha1''
      · rw [hmem x h1, hmem x' h2]
  -- one cusp at a time
  have key : ∀ x : Option (lineS Kb a), ∃ (𝔪 : Ideal D.S0.C0) (y g : G), 𝔪.IsMaximal ∧
      LiesOver hϖ hker hO D (cuspValue Kb a x) 𝔪 ∧ z (e x) = y * g * y⁻¹ ∧
      𝔪.comap (act g).φ0 = 𝔪 := by
    intro x
    obtain ⟨W, hW, hv⟩ := LineCuspGenerators.exists_place_cusp ht (x.map Subtype.val)
    have hvals : W.valuation ((1 - t) * (1 - algebraMap Kb Ω (algebraMap O Kb a) * t) / t ^ 3) < 1
        ∧ W.valuation (t⁻¹ - algebraMap Kb Ω (algebraMap O Kb (cuspValue Kb a x))) < 1 := by
      rcases x with _ | x
      · simpa [cuspValue] using cusp_inf W hW (algebraMap O Kb a) ht0 (by simpa using hv)
      · by_cases h1 : x.1 = 1
        · have := cusp_one W hW (algebraMap O Kb a) (x := t) (by simpa [h1] using hv)
          simpa [cuspValue, h1] using this
        · have hx : x.1 = (algebraMap O Kb a)⁻¹ := by
            have := x.2
            simp only [lineS, lineSK, Finset.mem_insert, Finset.mem_singleton] at this
            tauto
          have := cusp_inv W hW (algebraMap O Kb a) ha (x := t) (by simpa [hx] using hv)
          simpa [cuspValue, h1] using this
    obtain ⟨𝔪, hmax, hover, hfix⟩ := exists_special_point hϖ hker ha0 ha1 hO Kb act hone hmul
      L hψ hOK u hu1 hus ht0 (fun σ ↦ f (lineGaloisS (lineS Kb a) ht σ)) (fun σ b ↦ hσ σ b) W hW
      (cuspValue Kb a x) hvals.1 hvals.2
    let φ0 : G → D.S0.C0 →+* D.S0.C0 := fun g ↦ ((act g).φ0 : D.S0.C0 →+* D.S0.C0)
    have hone' : ∀ x, φ0 1 x = x := fun x ↦ by simp [φ0, hone, Datum.Hom.id]
    have hmul' : ∀ g h x, φ0 (g * h) x = φ0 g (φ0 h x) := fun g h x ↦ by
      simp [φ0, hmul, Datum.Hom.comp]
    obtain ⟨y, g, hg, hzg⟩ := hconj x W hW hv (StabIdeal.stab φ0 hone' hmul' 𝔪)
      fun σ hσ' ↦ (StabIdeal.mem_stab φ0 hone' hmul' 𝔪 _).2 (hfix σ hσ')
    refine ⟨𝔪, y, g, hmax, ?_, hzg, (StabIdeal.mem_stab φ0 hone' hmul' 𝔪 g).1 hg⟩
    unfold LiesOver
    rw [← specialFibreEquiv0_ψ D.Sp hϖ hker D.S0 D.om hO hα hB hψα]
    exact hover
  refine ⟨z, fun j ↦ cuspValue Kb a (c j), hprod, hgen, fun j ↦ hτv _,
    hτinj.comp hc, fun j ↦ ?_⟩
  obtain ⟨𝔪, y, g, hmax, hover, hzg, hfix⟩ := key (c j)
  rw [hec] at hzg
  exact ⟨𝔪, y, g, hmax, hover, hzg, hfix⟩

end Main

end Iut.Reconstruction.P1ThreeCuspStab
