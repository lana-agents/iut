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
# The level `L_2 = K(E_{q²})` and the debt Z_0 as the domination statement (Z_2) (TFGD, run 2)

The debt Z_0 (`PiYIndexTwoAt … 0`, `[Π^tp_Y : Π^tp_Ÿ] ≤ 2`) is restated as the single geometric
input (Z_2) `Π^tp_Y ≤ Π^tp_{L_2}` (`TFGD-plan.md`, lead decision D-T1), for the explicit level
`L_2 = K(E_{q²})` of the cyclic "`q`-direction" cover `E_{q²} → E_q`, `u ↦ u`:

* generic (an elliptic curve `E/K`, a `K`-rational point `T₀` of order `2`):
  `translateAut T₀` (translation by `T₀` on the source `K(E)` of `[2]`) fixes `[2]^*K(E)`
  (`translateAut_pb_two`) and is an involution; **`levelTwoField E T₀`** is the image in `Ω`
  (under `mulByNEmb E 2`, the source of `[2]`) of its fixed field — the function field of the
  quotient `E/⟨T₀⟩`, through which `[2]` factors. It lies between `L_X` and `L_{[2]}`, so it is an
  étale level (`etale_levelTwoField`, `isOpen_levelTwoField`).
* **`exists_quadratic_levelTwoField`**: `L_{[2]} = L_2(α)` with `α ∈ L_{[2]}` and every
  `σ` fixing `L_2` sends `α ↦ ±α` (`α = φ(z − T₀^*z)`, `α² ∈ L_2`; `K(E) = F₀ ⊕ F₀·a`).
* For the Tate curve `E_q`, `T₀ = ` the Tate point of `u = −1` (`tatePtNegOne`), and
  `E_q/⟨−1⟩ ≅ E_{q²}` (`u ↦ u²`), with `[2] : E_q → E_q` the composite with `E_{q²} → E_q`,
  `u ↦ u`; so `levelTwo t h2 h12 = K(E_{q²}) ⊆ L 0 = L_{[2]}` (numerical check in
  `TFGD-plan.md`, run 1: `L_2 = L_X(√(x − x_q(−1)))`).
* **`ZTwo`** (the named geometric input (Z_2)): `Π^tp_Y ≤ Π^tp_{L_2}` for the Tate data
  `tateDataX`; **`piYIndexTwoAt_zero_of_zTwo`**: (Z_2) implies Z_0 for every system of levels
  with `L 0 ≤ L_{[2]}` (`piYIndexTwoAt_zero_of_quadratic`).
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

/-! ### Generic: the fixed field of a translation by a `2`-torsion point -/

section Generic

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

local notation "CR" => E.toAffine.CoordinateRing
local notation "FF" => E.toAffine.FunctionField
local notation "Ω" => FFClosure (curveE E)
local notation "τ" => coordT (xN E)

variable {T₀ : E.toAffine.Point}

open Classical in
/-- Translation by a `2`-torsion point fixes `[2]^*K(E)`. -/
theorem translateAut_pb_two (h2T : T₀ + T₀ = 0) (f : FF) :
    translateAut T₀ (pb E 2 f) = pb E 2 f := by
  rcases T₀ with _ | ⟨x, y, h⟩
  · rfl
  · rw [translateAut_apply_some]
    exact translateEndo_mulByNEndo_apply_torsion_of_baseField h.left 2 (transcendental_N E 2)
      (by rw [two_nsmul]; exact h2T) f

omit [CharZero K] in
open Classical in
/-- Translation by a `2`-torsion point is an involution. -/
theorem translateAut_translateAut (h2T : T₀ + T₀ = 0) (f : FF) :
    translateAut T₀ (translateAut T₀ f) = f := by
  have h := translateAut_add T₀ T₀
  rw [h2T, translateAut_zero] at h
  rw [← AlgEquiv.mul_apply, ← h, AlgEquiv.one_apply]

variable (T₀) in
/-- **The level of `E/⟨T₀⟩`**: the image in `Ω` (source of `[2]`, `mulByNEmb E 2`) of the
fixed field of the translation by `T₀`. -/
abbrev levelTwoField : IntermediateField (K₀ K τ) Ω :=
  IntermediateField.adjoin (K₀ K τ) (mulByNEmb E 2 '' {f : FF | translateAut T₀ f = f})

open Classical in
theorem hemiL_le_levelTwoField (h2T : T₀ + T₀ = 0) :
    (hemiData E).L ≤ levelTwoField E T₀ :=
  hemiL_le_adjoin E 2 fun a => IntermediateField.subset_adjoin K _ (by
    change translateAut T₀ _ = _
    rw [algebraMap_mulByNHom_eq_pb]
    exact translateAut_pb_two E h2T _)

theorem levelTwoField_le_mulByNField : levelTwoField E T₀ ≤ mulByNField E 2 :=
  adjoin_image_le_mulByNField E 2 _

theorem isOpen_levelTwoField :
    IsOpen ((levelTwoField E T₀).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)) :=
  IntermediateField.fixingSubgroup_isOpen _

open Classical in
/-- `L_X → L_2` is étale (`L_X ≤ L_2 ≤ L_{[2]}`). -/
theorem etale_levelTwoField (h2T : T₀ + T₀ = 0) :
    (ringMap τ (hemiL_le_levelTwoField E h2T)).toRingHom.Etale :=
  etale_of_le_mulByNField E 2 _ (levelTwoField_le_mulByNField E)

open Classical in
/-- **`L_{[2]}` is quadratic over `L_2`**: for `T₀ ≠ 0` of order `2` there is `α ∈ L_{[2]}`
such that every `σ` fixing `L_2` sends `α` to `±α`, and fixes `L_{[2]}` if it fixes `α`
(`α = φ(z − T₀^*z)`; every `f ∈ K(E)` is `c₀ + c₁·(z − T₀^*z)` with `T₀^*c_i = c_i`). -/
theorem exists_quadratic_levelTwoField (h2T : T₀ + T₀ = 0) (hT0 : T₀ ≠ 0) :
    ∃ α : Ω, (∀ σ ∈ (levelTwoField E T₀).fixingSubgroup, σ α = α ∨ σ α = -α) ∧
      ∀ σ ∈ (levelTwoField E T₀).fixingSubgroup, σ α = α → ∀ z ∈ mulByNField E 2, σ z = z := by
  set ρ := translateAut (W := E.toAffine) T₀ with hρ
  set φ := mulByNEmb E 2
  have hρ1 : ρ ≠ 1 := fun h => hT0 (translateAut_eq_one_iff.1 h)
  obtain ⟨z, hz⟩ : ∃ z : FF, ρ z ≠ z := by
    by_contra! h
    exact hρ1 (AlgEquiv.ext h)
  set a := z - ρ z with ha
  have ha0 : a ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  have hρρ : ∀ f, ρ (ρ f) = f := translateAut_translateAut E h2T
  have hρa : ρ a = -a := by
    rw [ha, map_sub, hρρ]; ring
  have hfix : ∀ σ ∈ (levelTwoField E T₀).fixingSubgroup, ∀ c : FF, ρ c = c → σ (φ c) = φ c :=
    fun σ hσ c hc => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _
      (IntermediateField.subset_adjoin _ _ ⟨c, hc, rfl⟩)
  have h2 : (2 : FF) ≠ 0 := by
    have h := (algebraMap K FF).injective.ne (two_ne_zero (α := K))
    rwa [map_ofNat, map_zero] at h
  refine ⟨φ a, fun σ hσ => ?_, fun σ hσ hσa _ hw => ?_⟩
  · have hsq : σ (φ a) ^ 2 = φ a ^ 2 := by
      rw [← map_pow, ← map_pow, hfix σ hσ _ (by rw [map_pow, hρa, neg_sq])]
    exact sq_eq_sq_iff_eq_or_eq_neg.1 hsq
  · obtain ⟨f, rfl⟩ := hw
    set c₀ := (f + ρ f) / 2
    set c₁ := (f - ρ f) / (2 * a)
    have hc₀ : ρ c₀ = c₀ := by
      simp only [c₀, map_div₀, map_add, hρρ, map_ofNat]; ring
    have hc₁ : ρ c₁ = c₁ := by
      simp only [c₁, map_div₀, map_sub, map_mul, hρa, hρρ, map_ofNat]
      field_simp
      ring
    have hf : f = c₀ + c₁ * a := by
      simp only [c₀, c₁]; field_simp; ring
    change σ (φ f) = φ f
    rw [hf, map_add, map_mul, map_add, map_mul, hfix σ hσ _ hc₀, hfix σ hσ _ hc₁, hσa]

end Generic

/-! ### The Tate curve: `L_2 = K(E_{q²})` and the geometric input (Z_2) -/

section Tate

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

variable (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem neg_one_notMem_qpowers : (-1 : Kˣ) ∉ t.qpowers := by
  intro h
  obtain ⟨n, hn⟩ := (t.mem_qpowers_iff_val_eq).mp h
  have hq0 : (0 : ℝ) < ‖(t.q : K)‖ := norm_pos_iff.2 t.q.ne_zero
  have hnorm : ‖(t.q : K)‖ ^ n = 1 := by
    rw [← norm_zpow, ← hn]; simp
  have hn0 : n = 0 := (zpow_eq_one_iff_right₀ hq0.le t.norm_lt_one.ne).1 hnorm
  rw [hn0, zpow_zero, Units.val_neg, Units.val_one] at hn
  exact (by norm_num : (-1 : K) ≠ 1) hn

variable (t) in
/-- **The `2`-torsion point `u = −1`** of the Tate curve `E_q` (Tate parametrisation). -/
def tatePtNegOne : t.tateCurve.toAffine.Point :=
  t.tatePoint (fun _ hw => t.tatePoint_mem' h12 hw) ⟨h2, h12⟩ (-1)

omit [CharZero K] in
open Classical in
theorem tatePtNegOne_add_self : tatePtNegOne t h2 h12 + tatePtNegOne t h2 h12 = 0 := by
  rw [tatePtNegOne, ← t.tatePoint_mul, neg_one_mul, neg_neg, t.tatePoint_one]

theorem tatePtNegOne_ne_zero : tatePtNegOne t h2 h12 ≠ 0 := fun h =>
  neg_one_notMem_qpowers ((t.tatePoint_eq_zero_iff _ _).1 h)

variable [t.tateCurve.IsElliptic]

variable (t) in
/-- **The level `L_2 = K(E_{q²})`** of the cover `E_{q²} → E_q`, `u ↦ u`: the image in `Ω` of
the function field of `E_q/⟨−1⟩ ≅ E_{q²}` inside the source of `[2]` (`levelTwoField`). -/
def levelTwo : IntermediateField (K₀ K τ) Ω := levelTwoField t.tateCurve (tatePtNegOne t h2 h12)

theorem isOpen_levelTwo :
    IsOpen ((levelTwo t h2 h12).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)) :=
  isOpen_levelTwoField _

instance fact_hemiL_le_levelTwo : Fact ((hemiData t.tateCurve).L ≤ levelTwo t h2 h12) :=
  ⟨hemiL_le_levelTwoField _ (tatePtNegOne_add_self h2 h12)⟩

instance etale_levelTwo : Algebra.Etale (DX t).R
    (fieldData (transcendental_tau t.tateCurve) (levelTwo t h2 h12) (isOpen_levelTwo h2 h12)).R :=
  etale_fieldData (transcendental_tau t.tateCurve) (hemiL_open t) _ _
    (etale_levelTwoField _ (tatePtNegOne_add_self h2 h12))

variable (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) {s : Kˣ} (hs : s ^ 2 = t.q)

/-- **The geometric input (Z_2)** (named; owner TFGD/tfg, `TFGD-plan.md`): the `ℤ`-covering
`Y → X` of the Tate model dominates the cover `E_{q²} → E_q`, i.e. `Π^tp_Y ≤ Π^tp_{L_2}` for
the base point `V`. Geometrically: `Y` maps to the model of `L_2` (the double cover of the
2-gon by the 4-gon, étale over both components) compatibly with the base points
(`piY_le_range_of_hom`). -/
def ZTwo (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) : Prop :=
  TateObject.piY (A := (DX t).A) (tateDataX O hO hs h12) V hV ≤
    (temperedPi1Map (muL (transcendental_tau t.tateCurve) (hemiL_open t) (levelTwo t h2 h12)
      (isOpen_levelTwo h2 h12)) V hV).range

/-- **Z_0 from (Z_2)**: for every system of levels with `L 0 ≤ L_{[2]}`, (Z_2) gives
`[Π^tp_Y : Π^tp_Ÿ] ≤ 2` (`PiYIndexTwoAt … 0`). -/
theorem piYIndexTwoAt_zero_of_zTwo {V : ValuationSubring Ω} {hV : V.comap (algebraMap K Ω) = O}
    (hZ : ZTwo h2 h12 O hO hs V hV) {L : ℕ → IntermediateField (K₀ K τ) Ω}
    {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω))}
    [∀ j, Fact ((hemiData t.tateCurve).L ≤ L j)]
    [∀ j, Algebra.Etale (DX t).R (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R]
    (hL02 : L 0 ≤ mulByNField t.tateCurve 2) :
    PiYIndexTwoAt V hV (tateDataX O hO hs h12) hL 0 := by
  obtain ⟨α, hα, hgen⟩ := exists_quadratic_levelTwoField t.tateCurve
    (tatePtNegOne_add_self h2 h12) (tatePtNegOne_ne_zero h2 h12)
  exact piYIndexTwoAt_zero_of_quadratic (isOpen_levelTwo h2 h12) hZ α hα
    fun σ hσ e => (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun z hz =>
      hgen σ hσ e z (hL02 hz)

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
