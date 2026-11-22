/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.P1ThreeCuspStab
import Iut.Reconstruction.Cusp.RouteBVertex

/-!
# Route B, step 7 (D3): the level statement from B4′

The level hypotheses of `RouteBVertex.exists_vertex_iso` at one finite level `N`, from B4′ with
cyclic stabilisers (`P1ThreeCuspStab.exists_cusp_stabilisers_cyclic`) applied to the vertex datum
`D` of the level-`N` cover with group `G = Γ_v(C_N)`:

* the vertex group `Dv ≤ Δ` maps to `G` by `ρ` (onto, `ker ρ ⊆ N`: `Dv/(Dv ∩ N) ≅ Γ_v(C_N)`,
  `RouteBVertex.sup_eq_of_transitive`);
* the **branch dictionary** (`hI₀`, `hI₁`): every element of the stabiliser of a special point
  over the node branch `t̄ = 0` (resp. `t̄ = 1`) is `ρ` of a `Dv`-conjugate of an element of the
  branch stabiliser `I` (resp. of `τ I τ⁻¹`, `τ` the loop element), and `I` maps into the
  stabiliser of one special point over `t̄ = 0` (`hIstab`).

Then **`exists_level_generators`**: `Dv ≤ N ⊔ ⟨d₀ y₀ d₀⁻¹, (d₁ τ y₁ τ⁻¹ d₁⁻¹)⁻¹⟩` for some
`d₀, d₁ ∈ Dv`, `y₀, y₁ ∈ I` (two of the three B4′ generators, at the two node branches); and
**`isCyclic_level`**: the image of `I` in `Δ/N` is cyclic (C2, `P1Three.isCyclic_stab`).
The branch dictionary and the vertex datum itself are what D1 (the vertex datum of a Galois Tate
cover, MR13 plan run 18 (2)) has to supply; they are explicit arguments here.
-/

open Polynomial TensorProduct

universe u v

noncomputable section

namespace Iut.Reconstruction.RouteBLevel

open SemistableReduction SemistableReduction.P1Three TateLevel AdmissibleLift EtaleTower
  ProjectiveLine CurvesJacobian.Cusp AffOrbicurve P1ThreeLineQuotient P1ThreeCuspStab
  RouteBVertex

/-- An injective `τ : Fin 3 → {0, 1, a}` takes the value `b` for each `b ∈ {0, 1, a}`. -/
lemma exists_eq_of_injective {O : Type*} [Zero O] [One O] {a b : O} {τ : Fin 3 → O}
    (hτ : ∀ j, τ j = 0 ∨ τ j = 1 ∨ τ j = a)
    (hinj : Function.Injective τ) (hb : b = 0 ∨ b = 1 ∨ b = a) : ∃ j, τ j = b := by
  classical
  by_contra hne
  simp only [not_exists] at hne
  -- the values of `τ` lie in the two-element set `{0, 1, a} ∖ {b}`
  obtain ⟨c₁, c₂, hc⟩ : ∃ c₁ c₂ : O, ∀ j, τ j = c₁ ∨ τ j = c₂ := by
    rcases hb with rfl | rfl | rfl
    · exact ⟨1, a, fun j ↦ (hτ j).resolve_left (hne j)⟩
    · exact ⟨0, a, fun j ↦ ((hτ j).imp_right fun h ↦ h.resolve_left (hne j))⟩
    · exact ⟨0, 1, fun j ↦ ((hτ j).imp_right fun h ↦ h.resolve_right (hne j))⟩
  let f : Fin 3 → Bool := fun j ↦ decide (τ j = c₁)
  have hf : Function.Injective f := by
    intro i j hij
    apply hinj
    by_cases hi : τ i = c₁
    · have hj : τ j = c₁ := by simpa [f, hi] using hij.symm
      rw [hi, hj]
    · have hj : τ j ≠ c₁ := by simpa [f, hi] using hij.symm
      rw [(hc i).resolve_left hi, (hc j).resolve_left hj]
  have := Fintype.card_le_of_injective f hf
  simp at this

section Level

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
  {Δ : Type v} [Group Δ] {Dv I : Subgroup Δ} {τ : Δ} {N : Subgroup Δ}
  (ρ : Dv →* G) (hρ : Function.Surjective ρ)

/-- The stabiliser in `G` of a special point `𝔪` of `C0`. -/
abbrev stabG (𝔪 : Ideal D.S0.C0) : Subgroup G :=
  StabIdeal.stab (P1Three.φ0Act D act) (P1Three.φ0Act_one act hone) (P1Three.φ0Act_mul act hmul) 𝔪

include hϖ0 hϖu K Kb ht ha0 ha1 hone hmul hρ in
/-- **D3 at one level (B4′ ⇒ generation modulo `N`).** -/
theorem exists_level_generators
    (hfaith : ∀ g, (∀ c, (act g).φ1 c = c) → g = 1)
    (hconn : ∀ e : D.Sp.C1, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hdeg : Module.finrank (Ts θ (R1 O a)) D.Sp.C1 = Nat.card G) (hG : (Nat.card G : k) ≠ 0)
    (hρN : ∀ x : Dv, ρ x = 1 → (x : Δ) ∈ N)
    (hI₀ : ∀ 𝔪 : Ideal D.S0.C0, 𝔪.IsMaximal → LiesOver hϖ hker hO D 0 𝔪 →
      ∀ x ∈ stabG act hone hmul 𝔪, ∃ w : Dv, ∃ d ∈ Dv, ∃ y ∈ I, (w : Δ) = d * y * d⁻¹ ∧ ρ w = x)
    (hI₁ : ∀ 𝔪 : Ideal D.S0.C0, 𝔪.IsMaximal → LiesOver hϖ hker hO D 1 𝔪 →
      ∀ x ∈ stabG act hone hmul 𝔪, ∃ w : Dv, ∃ d ∈ Dv, ∃ y ∈ I,
        (w : Δ) = d * (τ * y * τ⁻¹) * d⁻¹ ∧ ρ w = x) :
    ∃ d₀ ∈ Dv, ∃ d₁ ∈ Dv, ∃ y₀ ∈ I, ∃ y₁ ∈ I,
      Dv ≤ N ⊔ Subgroup.closure {d₀ * y₀ * d₀⁻¹, (d₁ * (τ * y₁ * τ⁻¹) * d₁⁻¹)⁻¹} := by
  obtain ⟨z, τc, -, hgen, hτc, hinj, hj⟩ := exists_cusp_stabilisers_cyclic hϖ hker ha0 ha1 hO
    hϖ0 hϖu K Kb act hone hmul ht hfaith hconn hdeg hG
  have h01 : (0 : O) ≠ 1 := zero_ne_one
  obtain ⟨j₀, hj₀⟩ := exists_eq_of_injective hτc hinj (Or.inl rfl)
  obtain ⟨j₁, hj₁⟩ := exists_eq_of_injective hτc hinj (Or.inr (Or.inl rfl))
  have hne : j₀ ≠ j₁ := fun h ↦ h01 (by rw [← hj₀, ← hj₁, h])
  -- branch `0`
  obtain ⟨𝔪₀, h𝔪₀, y₀', x₀, hover₀, hz₀, hx₀, -⟩ := hj j₀
  rw [hj₀] at hover₀
  obtain ⟨w₀, e₀, he₀, u₀, hu₀, hw₀, hρw₀⟩ := hI₀ 𝔪₀ h𝔪₀ hover₀ x₀ hx₀
  obtain ⟨v₀, hv₀⟩ := hρ y₀'
  -- branch `1`
  obtain ⟨𝔪₁, h𝔪₁, y₁', x₁, hover₁, hz₁, hx₁, -⟩ := hj j₁
  rw [hj₁] at hover₁
  obtain ⟨w₁, e₁, he₁, u₁, hu₁, hw₁, hρw₁⟩ := hI₁ 𝔪₁ h𝔪₁ hover₁ x₁ hx₁
  obtain ⟨v₁, hv₁⟩ := hρ y₁'
  have hgen' : Subgroup.closure {ρ (v₀ * w₀ * v₀⁻¹), ρ (v₁ * w₁ * v₁⁻¹)} = ⊤ := by
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hv₀, hv₁, hρw₀, hρw₁, ← hz₀, ← hz₁]
    exact hgen j₀ j₁ hne
  have hle := le_sup_closure_of_quot ρ hρN hgen'
  have ha : ((v₀ * w₀ * v₀⁻¹ : Dv) : Δ) = ((v₀ : Δ) * e₀) * u₀ * ((v₀ : Δ) * e₀)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hw₀]; group
  have hb : ((v₁ * w₁ * v₁⁻¹ : Dv) : Δ) =
      (((v₁ : Δ) * e₁) * (τ * u₁⁻¹ * τ⁻¹) * ((v₁ : Δ) * e₁)⁻¹)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hw₁]; group
  rw [ha, hb] at hle
  exact ⟨(v₀ : Δ) * e₀, Dv.mul_mem v₀.2 he₀, (v₁ : Δ) * e₁, Dv.mul_mem v₁.2 he₁, u₀, hu₀, u₁⁻¹,
    I.inv_mem hu₁, hle⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [(Ideal.span {ϖ}).IsMaximal]
  [IsAdicComplete (Ideal.span {ϖ}) O] [TopologicalSpace G] [DiscreteTopology G] in
include ha0 ha1 hone hmul in
/-- **C2 at one level**: the image of the branch stabiliser `I ≤ Dv` in `Δ/N` is cyclic if `ρ`
maps it into the stabiliser of a special point over a cusp. -/
theorem isCyclic_level [N.Normal] (hID : I ≤ Dv)
    (hfaith : ∀ g, (∀ c, (act g).φ1 c = c) → g = 1)
    (hconn : ∀ e : D.Sp.C1, IsIdempotentElem e → e = 0 ∨ e = 1) (hG : (Nat.card G : k) ≠ 0)
    (hρN : ∀ x : Dv, ρ x = 1 → (x : Δ) ∈ N)
    {τc : O} (hτc : τc = 0 ∨ τc = 1 ∨ τc = a)
    (hIstab : ∃ 𝔪 : Ideal D.S0.C0, 𝔪.IsMaximal ∧ LiesOver hϖ hker hO D τc 𝔪 ∧
      ∀ y (hy : y ∈ I), ρ ⟨y, hID hy⟩ ∈ stabG act hone hmul 𝔪) :
    IsCyclic (I.map (QuotientGroup.mk' N)) := by
  obtain ⟨𝔪, h𝔪, hover, hstab⟩ := hIstab
  haveI := h𝔪
  haveI := P1Three.isCyclic_stab act hone hmul ha0 ha1 hfaith hconn hG 𝔪
    (mem_of_liesOver hϖ hker hO D hτc hover)
  have hle : (I.subgroupOf Dv).map ρ ≤ stabG act hone hmul 𝔪 := by
    rintro _ ⟨y, hy, rfl⟩
    exact hstab y.1 hy
  haveI : IsCyclic ((I.subgroupOf Dv).map ρ) := Subgroup.isCyclic_of_le hle
  exact isCyclic_map_of_ker_le hID ρ hρN this

end Level

end Iut.Reconstruction.RouteBLevel
