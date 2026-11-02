/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.TemperedDomination
import EllipticCurves.FunctionField.TranslationAction
import EllipticCurves.FunctionField.TranslationMulByNCommGeneral
import Pi1.Orbifold.Smooth

/-!
# The geometric inputs (Z_{N_j}) for debts Z_0 and C1, and debt 13a (TFGD, runs 2–4)

The debts Z_0 (`PiYIndexTwoAt … 0`, `[Π^tp_Y : Π^tp_Ÿ] ≤ 2`) and C1 (`LevelsDominated`) are
restated through the single family of named geometric inputs (Z_{N_j}) (`TFGD-plan.md`, lead
decisions D-T1, D-T5, D-T7):

* **`ZM j`** (the named geometric input (Z_{N_j})): `Π^tp_Y ≤ Π^tp_{K(E_{q^{N_j}})}` for the
  level `levelQN j = K(E_{q^{N_j}})` of `ThetaLevelQuot.lean` (the cyclic cover
  `E_{q^{N_j}} → E_q`, `v ↦ v`, `N_j = 2(j+1)`);
* **`piYIndexTwoAt_zero_of_zM`**: any one (Z_{N_j}) implies Z_0 for every system of levels with
  `L 0 ≤ L_{[2]}` (`piYIndexTwoAt_zero_of_quadratic`, `exists_quadratic_levelQN`: `L_{[2]}` lies in
  the quadratic extension `K(Ÿ'_{N_j})` of `K(E_{q^{N_j}})`); Z_0 uses `ZM 0` (`K(E_{q²})`; run 2
  had a separate input `ZTwo` for the same field, unified into `ZM 0` in run 4, D-T7);
* **`levelsDominated_of_zM`**: (Z_{N_j}) for all `j` implies C1 (`LevelsDominated`) for every
  system with `L j ≤ L 0 ⊔ K(E_{q^{N_j}})`.
* **Debt 13a** (lead decision D-T2): `exists_character_ne_one_tateDataX` (Theorem B of
  `tempered-fundamental-groups` for `tateDataX`: `b₆ = a₆/q` is a unit, `Δ ≠ 0`, `x`
  transcendental; `O` a complete DVR of mixed characteristic with perfect residue field) and
  **`exists_charN_eq_one_tateDataX`**: the normalised character `χ̂ = TateObject.charN` takes
  the value `1`. MR15's `Π^tp_X̿` is `χ̂⁻¹(lℤ)` (`Env/ThetaLTors.lean`, `piXdd`).
-/

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve KummerTheory KummerTheory.Curve CurvesJacobian.Cusp
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer
open TateCurvesTheta TateParameter WeierstrassCurve.Affine.CoordinateRing

noncomputable section

universe u

namespace Iut.EtaleTheta

/-! ### The Tate curve: the geometric inputs (Z_{N_j}) -/

section Tate

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

variable (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0)

variable [t.tateCurve.IsElliptic]

variable (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) {s : Kˣ} (hs : s ^ 2 = t.q)

/-! ### Debts Z_0 and C1 as the domination statements (Z_{N_j}) (TFGD runs 3, 4) -/

instance fact_hemiL_le_levelQN (j : ℕ) : Fact ((hemiData t.tateCurve).L ≤ levelQN h2 h12 hs j) :=
  ⟨hemiL_le_levelQN h2 h12 hs j⟩

instance etale_levelQN_fieldData (j : ℕ) : Algebra.Etale (DX t).R
    (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs j)
      (isOpen_levelQN h2 h12 hs j)).R :=
  etale_fieldData (transcendental_tau t.tateCurve) (hemiL_open t) _ _ (etale_levelQN h2 h12 hs j)

/-- **The geometric input (Z_{N_j})** (named; owner TFGD/tfg, `TFGD-plan.md`, lead decision
D-T5): the `ℤ`-covering `Y → X` of the Tate model dominates the cyclic cover
`E_{q^{N_j}} → E_q`, `v ↦ v` (`N_j = 2(j+1)`), i.e. `Π^tp_Y ≤ Π^tp_{K(E_{q^{N_j}})}` for the
base point `V` (`levelQN`). Geometrically: the special fibre of `E_{q^N}` (`π = s`) is the
`2N`-gon over the `2`-gon, a quotient of the universal `ℤ`-chain (`piY_le_range_of_hom`). -/
def ZM (j : ℕ) (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) : Prop :=
  TateObject.piY (A := (DX t).A) (tateDataX O hO hs h12) V hV ≤
    (temperedPi1Map (muL (transcendental_tau t.tateCurve) (hemiL_open t) (levelQN h2 h12 hs j)
      (isOpen_levelQN h2 h12 hs j)) V hV).range

/-- **Z_0 from (Z_{N_j})** (TFGD run 4, D-T7; used with `j = 0`): for every system of levels with
`L 0 ≤ L_{[2]}`, `Π^tp_Y ≤ Π^tp_{K(E_{q^{N_j}})}` gives `[Π^tp_Y : Π^tp_Ÿ] ≤ 2`
(`PiYIndexTwoAt … 0`): `L_{[2]}` is fixed by the index-`≤ 2` subgroup of `Π_{K(E_{q^{N_j}})}`
fixing `α` (`exists_quadratic_levelQN`). -/
theorem piYIndexTwoAt_zero_of_zM {j : ℕ} {V : ValuationSubring Ω}
    {hV : V.comap (algebraMap K Ω) = O}
    (hZ : ZM h2 h12 O hO hs j V hV) {L : ℕ → IntermediateField (K₀ K τ) Ω}
    {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω))}
    [∀ j, Fact ((hemiData t.tateCurve).L ≤ L j)]
    [∀ j, Algebra.Etale (DX t).R (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R]
    (hL02 : L 0 ≤ mulByNField t.tateCurve 2) :
    PiYIndexTwoAt V hV (tateDataX O hO hs h12) hL 0 := by
  obtain ⟨α, hα, hgen⟩ := exists_quadratic_levelQN h2 h12 hs j
  exact piYIndexTwoAt_zero_of_quadratic (isOpen_levelQN h2 h12 hs j) hZ α hα
    fun σ hσ e => (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun z hz =>
      hgen σ hσ e z (hL02 hz)

/-- **C1 from (Z_{N_j})**: for every system of levels with `L j ≤ L 0 ⊔ K(E_{q^{N_j}})`
(`exists_etaleThetaSystem`, `adjoin_levelCoords_le`), the inputs (Z_{N_j}) for all `j` give
`LevelsDominated` (`levelsDominated_of`). -/
theorem levelsDominated_of_zM {V : ValuationSubring Ω} {hV : V.comap (algebraMap K Ω) = O}
    (hZ : ∀ j, ZM h2 h12 O hO hs j V hV) {L : ℕ → IntermediateField (K₀ K τ) Ω}
    {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω))}
    [∀ j, Fact ((hemiData t.tateCurve).L ≤ L j)]
    [∀ j, Algebra.Etale (DX t).R (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R]
    (hsup : ∀ j, L j ≤ L 0 ⊔ levelQN h2 h12 hs j) :
    LevelsDominated V hV (tateDataX O hO hs h12) hL :=
  levelsDominated_of (isOpen_levelQN h2 h12 hs) hZ hsup

/-! ### Theorem B for the Tate data of `X`, and debt 13a for the normalised character -/

omit [t.tateCurve.IsElliptic] [CharZero K] in
include h12 in
/-- `‖a₆(q)‖ = ‖q‖`, from `‖a₆ + q‖ ≤ ‖q‖²`. -/
theorem norm_a₆_eq : ‖t.a₆‖ = ‖(t.q : K)‖ := by
  have hq1 : ‖(t.q : K)‖ < 1 := t.norm_lt_one
  have hqpos : 0 < ‖(t.q : K)‖ := norm_pos_iff.2 t.q.ne_zero
  have ha₆q : ‖t.a₆ + t.q‖ < ‖(t.q : K)‖ :=
    (t.norm_a₆_add_q_le h12).trans_lt (by nlinarith)
  apply le_antisymm
  · calc ‖t.a₆‖ = ‖(t.a₆ + t.q) + (-(t.q : K))‖ := by ring_nf
      _ ≤ max ‖t.a₆ + t.q‖ ‖-(t.q : K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = ‖(t.q : K)‖ := by rw [norm_neg]; exact max_eq_right ha₆q.le
  · have : ‖(t.q : K)‖ ≤ max ‖t.a₆ + t.q‖ ‖-t.a₆‖ := by
      calc ‖(t.q : K)‖ = ‖(t.a₆ + t.q) + (-t.a₆)‖ := by ring_nf
        _ ≤ _ := IsUltrametricDist.norm_add_le_max _ _
    rw [norm_neg] at this
    rcases le_max_iff.1 this with h | h
    · exact absurd h (not_le.2 ha₆q)
    · exact h

/-- **Theorem B for the Tate data `tateDataX` of `X = E_q ∖ {O}`**: the character
`χ : Π^tp_X → ℤ` of `Y → X` is nontrivial (`TateObject.exists_character_ne_one'`, Theorem B of
`tempered-fundamental-groups`), for `O` a complete discrete valuation ring of mixed
characteristic `(0, p)` with perfect residue field. -/
theorem exists_character_ne_one_tateDataX [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
    (p : ℕ) (hp : p.Prime) (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) :
    ∃ α, TemperedFundamentalGroups.TateObject.character (A := (DX t).A)
      (tateDataX O hO hs h12) V hV α ≠ 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hs0 : ((s : K) ^ 2) ≠ 0 := pow_ne_zero _ s.ne_zero
  have hsq : ((s : K) ^ 2) = t.q := by rw [← Units.val_pow_eq_pow_val, hs]
  -- `Δ ≠ 0`, so the discriminant polynomial is squarefree
  have hΔ : TemperedFundamentalGroups.TateNormal.tateDisc (tateDataX O hO hs h12).π
      (tateDataX O hO hs h12).b₄ (tateDataX O hO hs h12).b₆ ≠ 0 := by
    intro h
    have hW := TemperedFundamentalGroups.TateNormal.Δ_eq_tateDisc
      (π := (tateDataX O hO hs h12).π) (b₄ := (tateDataX O hO hs h12).b₄)
      (b₆ := (tateDataX O hO hs h12).b₆) O.subtype t.tateCurve rfl rfl rfl
      (by simp [tateDataX, mul_div_cancel₀ _ hs0]) (by simp [tateDataX, mul_div_cancel₀ _ hs0])
    rw [h, map_zero] at hW
    exact t.tateCurve.isUnit_Δ.ne_zero hW
  have h2O : (2 : O) ≠ 0 := fun h => two_ne_zero (congrArg Subtype.val h : ((2 : O) : K) = 0)
  -- `b₆ = a₆/q` is a unit
  have hb₆ : ‖t.a₆ / (s : K) ^ 2‖ = 1 := by
    rw [norm_div, hsq, norm_a₆_eq h12, div_self (norm_pos_iff.2 t.q.ne_zero).ne']
  have hb₆' : ‖(t.a₆ / (s : K) ^ 2)⁻¹‖ = 1 := by rw [norm_inv, hb₆, inv_one]
  have hb₆0 : t.a₆ / (s : K) ^ 2 ≠ 0 := by
    intro h; rw [h, norm_zero] at hb₆; exact zero_ne_one hb₆
  have hunit : IsUnit (tateDataX O hO hs h12).b₆ :=
    ⟨Units.mkOfMulEqOne (tateDataX O hO hs h12).b₆
      ⟨(t.a₆ / (s : K) ^ 2)⁻¹, (hO _).2 hb₆'.le⟩ (Subtype.ext (mul_inv_cancel₀ hb₆0)), rfl⟩
  -- `x` is transcendental over `K`
  have hx : Transcendental K (tateDataX O hO hs h12).x := fun h =>
    transcendental_tau t.tateCurve (by rw [← algebraMap_xX]; exact h.algebraMap)
  exact TateObject.exists_character_ne_one' (tateDataX O hO hs h12) V hV p hp hpm
    (GaloisData.ringKrullDim_R _) ϖ hϖ
    (TemperedFundamentalGroups.TateNormal.squarefree_dpoly _ _ _ h2O hΔ) (Or.inl hunit) hx

/-- **Debt 13a for the normalised character** (TFGD run 2, lead decision D-T2): there is
`g₁ ∈ Π^tp_X` with `χ̂(g₁) = 1` (`TateObject.charN`; Theorem B and `exists_charN_eq_ofAdd_one`). -/
theorem exists_charN_eq_one_tateDataX [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
    (p : ℕ) (hp : p.Prime) (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) :
    ∃ g₁, TateObject.charN (A := (DX t).A) (tateDataX O hO hs h12) V hV g₁ =
      Multiplicative.ofAdd (1 : ℤ) :=
  TateObject.exists_charN_eq_ofAdd_one _ V hV
    (exists_character_ne_one_tateDataX h12 O hO hs p hp hpm V hV)

end Tate

end Iut.EtaleTheta
