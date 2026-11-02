/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.TemperedLevelGalois

/-!
# The translation action of `Π^tp_X` on the levels, and `[Π^tp_Y : Π^tp_Ÿ] ≤ 2` (MR14, run 18)

MR15 obligations 13b (index) and 13c(i) (tempered form), `MR15-plan.md` (phase 2 run 6).

* **Debt Z** (`PiYIndexTwoAt j`, `MR14-plan.md`, "Debts"): the image of `Π^tp_Y` in
  `Gal(L_j/L_X)` has order `≤ 2`, i.e. `[Π^tp_Y : Π^tp_Y ∩ Π^tp_{L_j}] ≤ 2`. Geometrically: the
  `ℤ`-covering `Y → X` dominates the cyclic covering `E_{q^{N}} → E_q` (`U ↦ U`; run 8's
  reduction (Z_N) of C1), and `L_j` has degree `2` over the field of `E_{q^N}` (`Ÿ'_N = E_{s^N}`,
  `E_{s^N}/⟨-1⟩ ≅ E_{q^N}`), so the image is `{1, t_{-1}}`. This needs `2N`-gon models of the levels
  in tfg (as C1) and is not provable in iut now.
* `mul_self_mem_of_indexTwo`: under Z, squares of elements of `Π^tp_Y` lie in `Π^tp_{L_j}`.
* `piYIndexTwoAt_of_levelsDominated`: Z at `j = 0` and C1 give Z at every level, so the only
  new debt is Z at `j = 0`, i.e. `[Π^tp_Y : Π^tp_Ÿ] ≤ 2` (`Π^tp_Y ≤ Π^tp_{E_{q²}}`, run 8's (Z_2)).
* **`piYddotX_index`** (13b): under Z at `j = 0`, for every `e ∈ Π^tp_Y ∖ Π^tp_Ÿ`:
  `e² ∈ Π^tp_Ÿ` and `Π^tp_Y = Π^tp_Ÿ ∪ Π^tp_Ÿ·e` (the hypotheses `he2`, `hidx` of MR15's
  `exists_cX_of_invariant`).
* **`of_mem_piXdd`** (13c(i), tempered): for a homomorphism `w : Gal(Ω/L_X) → G` that is
  trivial on `Gal(Ω/L_j)` (MR14's translation homomorphisms `w_j` of `exists_etaleThetaSystem`), a
  property `P` of `Gal(Ω/L_X)` with `w σ = (w ρ)^l·w τ`, `(w τ)² = 1 ⇒ P σ` (for `w_j`: the
  conjunct `MovesByPow … η_j … l` of `exists_etaleThetaSystem`, [EtTh] Prop. 1.5(iii) mod `l`),
  Z at `j`, and `g₁` with `χ(g₁) = 1` (MR15 13a): every lift `σ ∈ H_X` of `tempToPi γ`,
  `l ∣ χ(γ)`, satisfies `P σ`.
-/

open CategoryTheory Pi1.Orbifold AffOrbicurve KummerTheory KummerTheory.Curve
open CurvesJacobian.Cusp TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta

section Index

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  (T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R)
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
  [hX : ∀ j, Fact (LX ≤ L j)]
  [het : ∀ j, Algebra.Etale (fieldData ht LX hLX).R (fieldData ht (L j) (hL j)).R]

variable (V hV) in
/-- **Debt Z at the level `j`** (`MR14-plan.md`, "Debts"): `[Π^tp_Y : Π^tp_Y ∩ Π^tp_{L_j}] ≤ 2`,
i.e. of any two elements of `Π^tp_Y` one lies in `Π^tp_{L_j}` or they agree modulo it.
(The `ℤ`-covering `Y → X` dominates `E_{q^{N_j}} → E_q`, and `[L_j : K(E_{q^{N_j}})] = 2`.) -/
def PiYIndexTwoAt (j : ℕ) : Prop :=
  ∀ y₁ ∈ TateObject.piY (A := (fieldData ht LX hLX).A) T V hV,
    ∀ y₂ ∈ TateObject.piY (A := (fieldData ht LX hLX).A) T V hV,
      y₁ ∈ (temperedPi1Map (muL ht hLX (L j) (hL j)) V hV).range ∨
      y₂ ∈ (temperedPi1Map (muL ht hLX (L j) (hL j)) V hV).range ∨
      y₁ * y₂⁻¹ ∈ (temperedPi1Map (muL ht hLX (L j) (hL j)) V hV).range

variable {T hL}

omit [IsGalois (K₀ k t) Ω] [CharZero k] het in
/-- Under Z at `j`, squares of elements of `Π^tp_Y` lie in `Π^tp_{L_j}`. -/
theorem mul_self_mem_of_indexTwo {j : ℕ} (hZ : PiYIndexTwoAt V hV T hL j)
    {y : TempPi (fieldData ht LX hLX) O V hV}
    (hy : y ∈ TateObject.piY (A := (fieldData ht LX hLX).A) T V hV) :
    y * y ∈ (temperedPi1Map (muL ht hLX (L j) (hL j)) V hV).range := by
  rcases hZ y hy y⁻¹ (inv_mem hy) with h | h | h
  · exact mul_mem h h
  · have h' := inv_mem h
    rw [inv_inv] at h'
    exact mul_mem h' h'
  · rwa [inv_inv] at h

omit [IsGalois (K₀ k t) Ω] [CharZero k] het in
theorem mem_piYddotX_iff {γ : TempPi (fieldData ht LX hLX) O V hV} :
    γ ∈ piYddotX V hV T hL ↔ γ ∈ TateObject.piY (A := (fieldData ht LX hLX).A) T V hV ∧
      γ ∈ (temperedPi1Map (muL ht hLX (L 0) (hL 0)) V hV).range :=
  Subgroup.mem_inf

omit [IsGalois (K₀ k t) Ω] [CharZero k] het in
/-- **`[Π^tp_Y : Π^tp_Ÿ] ≤ 2`** (MR15 obligation 13b, under debt Z at `j = 0`): for
`e ∈ Π^tp_Y ∖ Π^tp_Ÿ`, `e² ∈ Π^tp_Ÿ` and every `y ∈ Π^tp_Y` lies in `Π^tp_Ÿ` or in `Π^tp_Ÿ·e`. -/
theorem piYddotX_index (hZ : PiYIndexTwoAt V hV T hL 0) {e : TempPi (fieldData ht LX hLX) O V hV}
    (heY : e ∈ TateObject.piY (A := (fieldData ht LX hLX).A) T V hV)
    (he : e ∉ piYddotX V hV T hL) :
    e * e ∈ piYddotX V hV T hL ∧
      ∀ y ∈ TateObject.piY (A := (fieldData ht LX hLX).A) T V hV,
        y ∈ piYddotX V hV T hL ∨ y * e⁻¹ ∈ piYddotX V hV T hL := by
  have heR : e ∉ (temperedPi1Map (muL ht hLX (L 0) (hL 0)) V hV).range := fun h =>
    he (mem_piYddotX_iff.2 ⟨heY, h⟩)
  refine ⟨mem_piYddotX_iff.2 ⟨mul_mem heY heY, mul_self_mem_of_indexTwo hZ heY⟩,
    fun y hy => ?_⟩
  rcases hZ y hy e heY with h | h | h
  · exact Or.inl (mem_piYddotX_iff.2 ⟨hy, h⟩)
  · exact absurd h heR
  · exact Or.inr (mem_piYddotX_iff.2 ⟨mul_mem hy (inv_mem heY), h⟩)

omit [IsGalois (K₀ k t) Ω] [CharZero k] het in
/-- **Z at every level from Z at `j = 0` and C1**: `Π^tp_Ÿ ⊆ Π^tp_Y ∩ Π^tp_{L_j}` (C1) and
`[Π^tp_Y : Π^tp_Ÿ] ≤ 2` give `[Π^tp_Y : Π^tp_Y ∩ Π^tp_{L_j}] ≤ 2`. -/
theorem piYIndexTwoAt_of_levelsDominated (hZ : PiYIndexTwoAt V hV T hL 0)
    (hC1 : LevelsDominated V hV T hL) (j : ℕ) : PiYIndexTwoAt V hV T hL j := by
  intro y₁ hy₁ y₂ hy₂
  rcases hZ y₁ hy₁ y₂ hy₂ with h | h | h
  · exact Or.inl (hC1 j (mem_piYddotX_iff.2 ⟨hy₁, h⟩))
  · exact Or.inr (Or.inl (hC1 j (mem_piYddotX_iff.2 ⟨hy₂, h⟩)))
  · exact Or.inr (Or.inr (hC1 j (mem_piYddotX_iff.2 ⟨mul_mem hy₁ (inv_mem hy₂), h⟩)))

set_option synthInstance.maxHeartbeats 200000 in
-- `DivisionMonoid (Pi _)` is slow to synthesize
/-- **The translation action of `Π^tp_X̿` on a level is by `l`-th powers** (MR15 obligation
13c(i), tempered form). Let `w : H_X → G` be trivial on `Gal(Ω/L_j)` and let `P` hold for every
`σ` with `w σ = (w ρ)^l·w τ`, `(w τ)² = 1`. Under Z at `j` and with `g₁ ∈ Π^tp_X`, `χ(g₁) = 1`
(MR15 13a), every lift `σ ∈ H_X` of the image of `γ ∈ Π^tp_X` with `χ(γ) = l·m` satisfies `P σ`.
(For MR14's `w_j` and `P σ = MovesByPow (L j) σ η_j l`: `σ η_j = (d·y)^l·η_j`, `d ∈ K`,
`y ∈ L_j`.) -/
theorem of_mem_piXdd {G : Type*} [CommGroup G] (j : ℕ) (w : (fieldData ht LX hLX).H →* G)
    (hw1 : ∀ σ : (fieldData ht LX hLX).H, (∀ z ∈ L j, (σ : Ω ≃ₐ[K₀ k t] Ω) z = z) → w σ = 1)
    (P : (fieldData ht LX hLX).H → Prop) (l : ℕ)
    (hP : ∀ σ ρ τ : (fieldData ht LX hLX).H, w σ = w ρ ^ l * w τ → w τ ^ 2 = 1 → P σ)
    (hZ : PiYIndexTwoAt V hV T hL j)
    {g₁ : TempPi (fieldData ht LX hLX) O V hV}
    (hg₁ : Iut.EtaleTheta.TateObject.charN (A := (fieldData ht LX hLX).A) T V hV
      g₁ = Multiplicative.ofAdd (1 : ℤ))
    {γ : TempPi (fieldData ht LX hLX) O V hV} {m : ℤ}
    (hγ : Iut.EtaleTheta.TateObject.charN (A := (fieldData ht LX hLX).A) T V hV
      γ = Multiplicative.ofAdd ((l : ℤ) * m))
    (σ : (fieldData ht LX hLX).H)
    (hσ : (σ : Pi (fieldData ht LX hLX)) = tempToPi (fieldData ht LX hLX) O V hV γ) :
    P σ := by
  set φ := tempToPi (fieldData ht LX hLX) O V hV
  set y := g₁ ^ (-((l : ℤ) * m)) * γ with hydef
  have hy : y ∈ TateObject.piY (A := (fieldData ht LX hLX).A) T V hV := by
    rw [← TateObject.charN_eq_one_iff, hydef, map_mul, map_zpow, hg₁, hγ, ← ofAdd_zsmul,
      ← ofAdd_add]
    simp
  have hfix : ∀ (δ : TempPi (fieldData ht LX hLX) O V hV),
      δ ∈ (temperedPi1Map (muL ht hLX (L j) (hL j)) V hV).range →
      ∀ κ : (fieldData ht LX hLX).H, (κ : Pi (fieldData ht LX hLX)) = φ δ → w κ = 1 :=
    fun δ hδ κ hκ => hw1 κ ((IntermediateField.mem_fixingSubgroup_iff _ _).1
      ((mem_range_muL_iff_forall ht hLX (L j) (hL j) O V hV δ).1 hδ κ hκ))
  obtain ⟨σ₁, hσ₁⟩ := QuotientGroup.mk_surjective (φ g₁)
  obtain ⟨σy, hσy⟩ := QuotientGroup.mk_surjective (φ y)
  -- the lift `σ' = σ₁^{lm}·σ_y` of `φ γ`
  set σ' := σ₁ ^ ((l : ℤ) * m) * σy with hσ'def
  have hσ' : (σ' : Pi (fieldData ht LX hLX)) = φ γ := by
    rw [hσ'def, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, hσ₁, hσy, hydef, map_mul,
      map_zpow, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  -- `σ = σ'·κ` with `κ` a lift of `1`
  have hκ : w (σ'⁻¹ * σ) = 1 := by
    refine hfix 1 (one_mem _) _ ?_
    rw [map_one, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hσ', hσ, inv_mul_cancel]
  have hw : w σ = w (σ₁ ^ m) ^ l * w σy := by
    have e1 : σ = σ' * (σ'⁻¹ * σ) := by group
    rw [e1, map_mul, hκ, mul_one, hσ'def, map_mul, ← map_pow, ← zpow_natCast, ← zpow_mul,
      mul_comm m (l : ℤ)]
  have hy2 : w σy ^ 2 = 1 := by
    rw [sq, ← map_mul]
    refine hfix (y * y) (mul_self_mem_of_indexTwo hZ hy) _ ?_
    rw [QuotientGroup.mk_mul, hσy]
    exact (map_mul φ y y).symm
  exact hP σ (σ₁ ^ m) σy hw hy2

end Index

end Iut.EtaleTheta
