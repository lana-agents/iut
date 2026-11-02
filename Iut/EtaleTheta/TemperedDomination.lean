/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.TemperedLevelTrans

/-!
# Reductions of the debts C1 and Z_0 to the domination of cyclic covers (TFGD, run 1)

The debts C1 (`LevelsDominated`, `Π^tp_Ÿ ≤ Π^tp_{Ÿ'_{N_j}}`) and Z_0 (`PiYIndexTwoAt … 0`,
`[Π^tp_Y : Π^tp_Ÿ] ≤ 2`) have one geometric core (`TFGD-plan.md`): the `ℤ`-covering `Y → X` of
the special fibre of the Tate model dominates the cyclic "`q`-direction" covers
`E_{q^M} → E_q`, `u ↦ u` — statement (Z_M): `Π^tp_Y ≤ Π^tp_{L_M}` for the field `L_M` of
`E_{q^M}`. This file proves the formal parts of the reduction, with no new hypotheses:

* `piY_le_range_of_hom` (generic, tempered category): (Z_M) for a finite étale `R → R'` follows
  from an object `Z` with morphisms to `X₀` (injective on fibres) and to the cover `Spec R'`,
  and a point of `Z` over both base points. The geometric input left is the construction of
  `Z` (a model of `R'` whose special fibre is the `2M`-gon over the 2-gon; `TFGD-plan.md`).
* Tempered Galois correspondence for the levels (`mem_range_muL_iff(_forall)`):
  `range_muL_antitone`, `inf_range_muL_le` (`L₃ ≤ L₁ ⊔ L₂ ⇒ Π^tp_{L₁} ∩ Π^tp_{L₂} ≤ Π^tp_{L₃}`),
  `indexTwo_of_quadratic` (a quadratic extension `L_mid ≤ L'` has "index `≤ 2`" in the form of
  `PiYIndexTwoAt`).
* **`piYIndexTwoAt_zero_of_quadratic`**: Z_0 from (Z_2) for an intermediate field `L_mid ≤ L 0`
  with `L 0 / L_mid` quadratic (`Ẍ → E_{q²}`, `Ü ↦ Ü²`).
* **`levelsDominated_of`**: C1 from (Z_{M_j}) for fields `L' j` with `L j ≤ L 0 ⊔ L' j`
  (`Ÿ'_N` is the component of `Ẍ ×_X E_{q^N}`).
* `exists_eq_ofAdd_one_of_isCoprime` (debt 13a, algebraic part): a character to `ℤ` with two
  coprime values takes the value `1`.
-/

open CategoryTheory Pi1.Orbifold AffOrbicurve KummerTheory KummerTheory.Curve
open CurvesJacobian.Cusp TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta

/-! ### The formal reduction of (Z_M) to an object over `X₀` and the cover -/

section Object

open TemperedFundamentalGroups.TateObject FibreAut

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A] [Subsingleton A]
  [MulSemiringAction A R] [SMulCommClass A K R] (T : Data O R)
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  [Algebra.Etale R R'] [Module.Finite R R']
  {A' : Type u} [Group A'] [Subsingleton A'] [MulSemiringAction A' R']
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **(Z_M) from an object dominating `X₀` and the cover.** Let `Z` be a tempered object with
morphisms `a : Z ⟶ X₀` and `b : Z ⟶ coverObj R'` and a fibre point `z₀` over the base points
of `X₀` and of the cover, such that `a` is injective on fibres. Then `Π^tp_Y ≤ Π^tp_{R'}`. -/
theorem piY_le_range_of_hom (μ : OrbMap R A R' A') {Z : TempObj O R A}
    (a : Z ⟶ X₀ (A := A) T) (b : Z ⟶ coverObj O R A R') (z₀ : (tempFibre O R A V hV).obj Z)
    (ha : (tempFibre O R A V hV).map a z₀ = basePoint T V hV)
    (hb : (tempFibre O R A V hV).map b z₀ = coverFibrePt V hV)
    (hinj : Function.Injective (fun z => (tempFibre O R A V hV).map a z)) :
    TateObject.piY (A := A) T V hV ≤ (temperedPi1Map (O := O) μ V hV).range := by
  intro γ hγ
  rw [TateObject.mem_piY_iff] at hγ
  rw [mem_range_temperedPi1Map]
  have hz : γ.app Z z₀ = z₀ := hinj (by
    change (tempFibre O R A V hV).map a (γ.app Z z₀) = (tempFibre O R A V hV).map a z₀
    rw [← app_naturality, ha, hγ])
  rw [← hb, app_naturality, hz]

end Object

/-! ### Field-side lemmas: tempered Galois correspondence for the levels -/

section Fields

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (ht : Transcendental k t)
  [IsGalois (K₀ k t) Ω] [CharZero k]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  (O : ValuationSubring k) (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)

/-- `Π^tp_{L₂} ≤ Π^tp_{L₁}` for levels `L₁ ≤ L₂`. -/
theorem range_muL_antitone {L₁ L₂ : IntermediateField (K₀ k t) Ω}
    (hL₁ : IsOpen (L₁.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
    (hL₂ : IsOpen (L₂.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
    [Fact (LX ≤ L₁)] [Fact (LX ≤ L₂)]
    [Algebra.Etale (fieldData ht LX hLX).R (fieldData ht L₁ hL₁).R]
    [Algebra.Etale (fieldData ht LX hLX).R (fieldData ht L₂ hL₂).R] (h : L₁ ≤ L₂) :
    (temperedPi1Map (muL ht hLX L₂ hL₂) V hV).range ≤
      (temperedPi1Map (muL ht hLX L₁ hL₁) V hV).range := by
  intro γ hγ
  obtain ⟨σ, hσ, hσL⟩ := (mem_range_muL_iff ht hLX L₂ hL₂ O V hV γ).1 hγ
  exact (mem_range_muL_iff ht hLX L₁ hL₁ O V hV γ).2
    ⟨σ, hσ, IntermediateField.fixingSubgroup_antitone h hσL⟩

/-- **`Π^tp_{L₁} ∩ Π^tp_{L₂} ≤ Π^tp_{L₃}` for `L₃ ≤ L₁ ⊔ L₂`.** -/
theorem inf_range_muL_le {L₁ L₂ L₃ : IntermediateField (K₀ k t) Ω}
    (hL₁ : IsOpen (L₁.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
    (hL₂ : IsOpen (L₂.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
    (hL₃ : IsOpen (L₃.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
    [Fact (LX ≤ L₁)] [Fact (LX ≤ L₂)] [Fact (LX ≤ L₃)]
    [Algebra.Etale (fieldData ht LX hLX).R (fieldData ht L₁ hL₁).R]
    [Algebra.Etale (fieldData ht LX hLX).R (fieldData ht L₂ hL₂).R]
    [Algebra.Etale (fieldData ht LX hLX).R (fieldData ht L₃ hL₃).R] (h : L₃ ≤ L₁ ⊔ L₂) :
    (temperedPi1Map (muL ht hLX L₁ hL₁) V hV).range ⊓
        (temperedPi1Map (muL ht hLX L₂ hL₂) V hV).range ≤
      (temperedPi1Map (muL ht hLX L₃ hL₃) V hV).range := by
  rintro γ ⟨h₁, h₂⟩
  obtain ⟨σ, hσ, hσL⟩ := (mem_range_muL_iff ht hLX L₁ hL₁ O V hV γ).1 h₁
  have hσ₂ := (mem_range_muL_iff_forall ht hLX L₂ hL₂ O V hV γ).1 h₂ σ hσ
  refine (mem_range_muL_iff ht hLX L₃ hL₃ O V hV γ).2 ⟨σ, hσ, ?_⟩
  refine IntermediateField.fixingSubgroup_antitone h ?_
  rw [IntermediateField.fixingSubgroup_sup]
  exact ⟨hσL, hσ₂⟩

set_option synthInstance.maxHeartbeats 200000 in
-- `DivisionMonoid (Pi _)` is slow to synthesize
/-- **A quadratic extension of levels has index `≤ 2`.** Let `L_mid ≤ L'` be levels and
`α ∈ Ω` such that every `σ` fixing `L_mid` sends `α` to `±α`, and fixes `L'` if it fixes `α`.
Then of two elements of `Π^tp_{L_mid}` one lies in `Π^tp_{L'}` or they agree modulo it. -/
theorem indexTwo_of_quadratic {Lm L' : IntermediateField (K₀ k t) Ω}
    (hLm : IsOpen (Lm.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
    (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
    [Fact (LX ≤ Lm)] [Fact (LX ≤ L')]
    [Algebra.Etale (fieldData ht LX hLX).R (fieldData ht Lm hLm).R]
    [Algebra.Etale (fieldData ht LX hLX).R (fieldData ht L' hL').R] (α : Ω)
    (hα : ∀ σ ∈ Lm.fixingSubgroup, σ α = α ∨ σ α = -α)
    (hgen : ∀ σ ∈ Lm.fixingSubgroup, σ α = α → σ ∈ L'.fixingSubgroup)
    {y₁ y₂ : TempPi (fieldData ht LX hLX) O V hV}
    (h₁ : y₁ ∈ (temperedPi1Map (muL ht hLX Lm hLm) V hV).range)
    (h₂ : y₂ ∈ (temperedPi1Map (muL ht hLX Lm hLm) V hV).range) :
    y₁ ∈ (temperedPi1Map (muL ht hLX L' hL') V hV).range ∨
      y₂ ∈ (temperedPi1Map (muL ht hLX L' hL') V hV).range ∨
      y₁ * y₂⁻¹ ∈ (temperedPi1Map (muL ht hLX L' hL') V hV).range := by
  obtain ⟨σ₁, hσ₁, hσ₁L⟩ := (mem_range_muL_iff ht hLX Lm hLm O V hV y₁).1 h₁
  obtain ⟨σ₂, hσ₂, hσ₂L⟩ := (mem_range_muL_iff ht hLX Lm hLm O V hV y₂).1 h₂
  rcases hα _ hσ₁L with e₁ | e₁
  · exact Or.inl ((mem_range_muL_iff ht hLX L' hL' O V hV y₁).2 ⟨σ₁, hσ₁, hgen _ hσ₁L e₁⟩)
  rcases hα _ hσ₂L with e₂ | e₂
  · exact Or.inr (Or.inl
      ((mem_range_muL_iff ht hLX L' hL' O V hV y₂).2 ⟨σ₂, hσ₂, hgen _ hσ₂L e₂⟩))
  refine Or.inr (Or.inr ((mem_range_muL_iff ht hLX L' hL' O V hV _).2 ⟨σ₁ * σ₂⁻¹, ?_, ?_⟩))
  · rw [map_mul, map_inv, ← hσ₁, ← hσ₂]
    rfl
  · have hm : ((σ₁ * σ₂⁻¹ : (fieldData ht LX hLX).H) : Ω ≃ₐ[K₀ k t] Ω) ∈ Lm.fixingSubgroup :=
      mul_mem hσ₁L (inv_mem hσ₂L)
    refine hgen _ hm ?_
    have hinv : ((σ₂ : Ω ≃ₐ[K₀ k t] Ω))⁻¹ α = -α := by
      rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, map_neg, e₂, neg_neg]
    change ((σ₁ : Ω ≃ₐ[K₀ k t] Ω) * ((σ₂ : Ω ≃ₐ[K₀ k t] Ω))⁻¹) α = α
    rw [AlgEquiv.mul_apply, hinv, map_neg, e₁, neg_neg]

end Fields

/-! ### C1 and Z_0 from the domination of cyclic covers -/

section Debts

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  {T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R}
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  [hX : ∀ j, Fact (LX ≤ L j)]
  [het : ∀ j, Algebra.Etale (fieldData ht LX hLX).R (fieldData ht (L j) (hL j)).R]

/-- **Z_0 from (Z_2)**: if `Π^tp_Y ≤ Π^tp_{L_mid}` for a level `L_mid` over which `L 0` is
quadratic (generated by `α` with `σ α = ±α`), then `[Π^tp_Y : Π^tp_Ÿ] ≤ 2`. -/
theorem piYIndexTwoAt_zero_of_quadratic {Lm : IntermediateField (K₀ k t) Ω}
    (hLm : IsOpen (Lm.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))) [Fact (LX ≤ Lm)]
    [Algebra.Etale (fieldData ht LX hLX).R (fieldData ht Lm hLm).R]
    (hZ2 : TateObject.piY (A := (fieldData ht LX hLX).A) T V hV ≤
      (temperedPi1Map (muL ht hLX Lm hLm) V hV).range) (α : Ω)
    (hα : ∀ σ ∈ Lm.fixingSubgroup, σ α = α ∨ σ α = -α)
    (hgen : ∀ σ ∈ Lm.fixingSubgroup, σ α = α → σ ∈ (L 0).fixingSubgroup) :
    PiYIndexTwoAt V hV T hL 0 := fun _ hy₁ _ hy₂ =>
  indexTwo_of_quadratic ht O V hV hLm (hL 0) α hα hgen (hZ2 hy₁) (hZ2 hy₂)

/-- **C1 from (Z_M)**: if `Π^tp_Y ≤ Π^tp_{L' j}` and `L j ≤ L 0 ⊔ L' j` for every `j`, then
`Π^tp_Ÿ ≤ Π^tp_{L j}` for every `j`. -/
theorem levelsDominated_of {L' : ℕ → IntermediateField (K₀ k t) Ω}
    (hL' : ∀ j, IsOpen ((L' j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
    [∀ j, Fact (LX ≤ L' j)]
    [∀ j, Algebra.Etale (fieldData ht LX hLX).R (fieldData ht (L' j) (hL' j)).R]
    (hZ : ∀ j, TateObject.piY (A := (fieldData ht LX hLX).A) T V hV ≤
      (temperedPi1Map (muL ht hLX (L' j) (hL' j)) V hV).range)
    (hsup : ∀ j, L j ≤ L 0 ⊔ L' j) :
    LevelsDominated V hV T hL := fun j _ hγ =>
  inf_range_muL_le ht O V hV (hL 0) (hL' j) (hL j) (hsup j)
    ⟨(mem_piYddotX_iff.1 hγ).2, hZ j (mem_piYddotX_iff.1 hγ).1⟩

end Debts

/-! ### 13a: the value `1` of a character from coprime values -/

section Character

/-- **13a, algebraic part**: if a character `χ : G → ℤ` takes coprime values `a`, `b`, it takes
the value `1` (`g₁^u g₂^v` for `u a + v b = 1`). With tfg's `exists_character_eq_of_loop` this
reduces 13a to loops of coprime windings (`TFGD-plan.md`). -/
theorem exists_eq_ofAdd_one_of_isCoprime {G : Type*} [Group G] (χ : G →* Multiplicative ℤ)
    {g₁ g₂ : G} {a b : ℤ} (h₁ : χ g₁ = Multiplicative.ofAdd a)
    (h₂ : χ g₂ = Multiplicative.ofAdd b) (hab : IsCoprime a b) :
    ∃ g : G, χ g = Multiplicative.ofAdd 1 := by
  obtain ⟨u, v, huv⟩ := hab
  refine ⟨g₁ ^ u * g₂ ^ v, ?_⟩
  rw [map_mul, map_zpow, map_zpow, h₁, h₂, ← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_add,
    smul_eq_mul, smul_eq_mul, huv]

end Character

end Iut.EtaleTheta
