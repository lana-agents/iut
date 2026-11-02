/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaLevelHeisenberg
import EllipticCurves.FunctionField.TranslationAction

/-!
# The levels `K(E_{q^N})` and `L_j ≤ L_0 ⊔ K(E_{q^{N_j}})` (TFGD, run 3)

Debt C1 (`LevelsDominated`, `Π^tp_Ÿ ≤ Π^tp_{Ÿ'_{N_j}}`) is restated through the geometric
inputs (Z_{N_j}) `Π^tp_Y ≤ Π^tp_{K(E_{q^{N_j}})}` (`TFGD-plan.md`, lead decision D-T5,
`levelsDominated_of`). This file provides the field side, for `N` even, `Q = s^N` (`s² = q`):

* `ι = φ ∘ j : K(E_Q) → Ω`, the embedding of the level `Ÿ'_N` (`j = pullbackT` of the level
  coordinates `x_Q∘ψ, y_Q∘ψ`, `ψ(u) = u^N`, `φ = mulByNEmb (2N)`);
* **`levelQuot`**: the image under `ι` of the fixed field of the translation `t_{-1}` by the
  `2`-torsion point `U = -1` of `E_Q`: the function field of `E_Q/⟨-1⟩ ≅ E_{Q²} = E_{q^N}`
  (`U ↦ U²`), i.e. the level of the cyclic cover `E_{q^N} → E_q`, `v ↦ v`, of degree `N`;
  `hemiL_le_levelQuot` (`t_{-1}` fixes `[2N]^*K[E_q]`: `transT_R_eq`, `transT_Ry_eq`),
  `levelQuot_le_mulByNField`;
* **`levelQN j`**: `levelQuot` for the level coordinates `levelCoords j` (`N = N_j = 2(j+1)`;
  the coordinates are unique, `eq_levelCoords`), so `levelQN j = K(E_{q^{N_j}}) ⊆ Ω`;
* the generic **`mem_sup_adjoin_fixed`**: for an involution `ρ` of a field `F` (`2 ≠ 0`) and
  `ι : F → Ω`, if `ι z ∈ M` for some `z` with `ρ z ≠ z`, then `ι(F) ⊆ M ⊔ ι(F^ρ)`
  (`f = c₀ + c₁(z − ρz)` with `c_i ∈ F^ρ`);
* **`adjoin_levelCoords_le`**: `L_j ≤ M ⊔ levelQN j` whenever `φ_2(x) ∈ M` (applied with
  `M = L_0 = K(E_q)` in the source of `[2]`): the element `z ∈ K(E_Q)` with values `X_q(U)`
  (`exists_poly_quotX`) has `ι z = φ_2(x)` and `t_{-1} z ≠ z` (its values at `U = 2` and `U = -2`
  differ: `X_ne_X_of_norm_one`).
-/

open Polynomial

noncomputable section

universe u

namespace Iut.EtaleTheta

open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing

/-! ### Generic: the fixed field of an involution and a quadratic decomposition -/

section Generic

/-- **`ι(F) ⊆ M ⊔ ι(F^ρ)`** for an involution `ρ` of `F` (`2 ≠ 0`) and `z` with `ρ z ≠ z`,
`ι z ∈ M`: every `f` is `c₀ + c₁·(z − ((z + ρz) − z))` with `c₀ = (f + ρf)/2`,
`c₁ = (f − ρf)/(2(z − ρz))` fixed by `ρ`. -/
theorem mem_sup_adjoin_fixed {K B Ω F : Type*} [Field K] [Field B] [Field Ω] [Field F]
    [Algebra K B] [Algebra B Ω] [Algebra K Ω] [IsScalarTower K B Ω] [Algebra K F]
    (ι : F →ₐ[K] Ω) (ρ : F ≃ₐ[K] F) (hρρ : ∀ f, ρ (ρ f) = f) (h2 : (2 : F) ≠ 0)
    {z : F} (hz : ρ z ≠ z) {M : IntermediateField B Ω} (hzM : ι z ∈ M) (f : F) :
    ι f ∈ M ⊔ IntermediateField.adjoin B (ι '' {g | ρ g = g}) := by
  set L' := IntermediateField.adjoin B (ι '' {g | ρ g = g})
  have hfix : ∀ c, ρ c = c → ι c ∈ M ⊔ L' := fun c hc =>
    (le_sup_right : L' ≤ M ⊔ L') (IntermediateField.subset_adjoin B _ ⟨c, hc, rfl⟩)
  have hzM' : ι z ∈ M ⊔ L' := (le_sup_left : M ≤ M ⊔ L') hzM
  set a := z - ρ z with ha
  have ha0 : a ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  have hρa : ρ a = -a := by rw [ha, map_sub, hρρ]; ring
  set c₀ := (f + ρ f) / 2 with hc₀def
  set c₁ := (f - ρ f) / (2 * a) with hc₁def
  have hc₀ : ρ c₀ = c₀ := by
    simp only [c₀, map_div₀, map_add, hρρ, map_ofNat]; ring
  have hc₁ : ρ c₁ = c₁ := by
    simp only [c₁, map_div₀, map_sub, map_mul, hρa, hρρ, map_ofNat]
    field_simp
    ring
  have hw : ρ (z + ρ z) = z + ρ z := by rw [map_add, hρρ, add_comm]
  have hf : f = c₀ + c₁ * (z - ((z + ρ z) - z)) := by
    have e : z - ((z + ρ z) - z) = a := by rw [ha]; ring
    rw [e]
    simp only [c₀, c₁]
    field_simp
    ring
  rw [hf, map_add, map_mul, map_sub, map_sub]
  exact add_mem (hfix _ hc₀) (mul_mem (hfix _ hc₁) (sub_mem hzM' (sub_mem (hfix _ hw) hzM')))

end Generic

/-! ### Units of norm one and the Tate coordinates -/

section NormOne

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem eq_of_norm_one_of_eq_zpow (T : TateParameter K) {u w : K} (hu : ‖u‖ = 1)
    (hw : ‖w‖ = 1) {n : ℤ} (h : u = (T.q : K) ^ n * w) : u = w := by
  have hq0 : (0 : ℝ) < ‖(T.q : K)‖ := norm_pos_iff.2 T.q.ne_zero
  have hnorm : ‖(T.q : K)‖ ^ n = 1 := by
    have := congrArg norm h
    rwa [norm_mul, norm_zpow, hu, hw, mul_one, eq_comm] at this
  have hn0 : n = 0 := (zpow_eq_one_iff_right₀ hq0.le T.norm_lt_one.ne).1 hnorm
  rw [h, hn0, zpow_zero, one_mul]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem offOrbit_of_norm_one (T : TateParameter K) {u : Kˣ} (hu : ‖(u : K)‖ = 1)
    (h1 : (u : K) ≠ 1) : OffOrbit T u := by
  intro n hn
  have hn' : (u : K) = (T.q : K) ^ (-n) * 1 := by
    rw [mul_one, zpow_neg]; exact eq_inv_of_mul_eq_one_right hn
  exact h1 (eq_of_norm_one_of_eq_zpow T hu norm_one hn')

omit [CharZero K] in
/-- On units of norm one, `X_T` separates `u` from `w` unless `u = w` or `u w = 1`. -/
theorem X_ne_X_of_norm_one (h12 : (12 : K) ≠ 0) (h2 : ‖(2 : K)‖ = 1) (T : TateParameter K)
    {u w : Kˣ} (hu : OffOrbit T u) (hw : OffOrbit T w) (hnu : ‖(u : K)‖ = 1)
    (hnw : ‖(w : K)‖ = 1) (hne : (u : K) ≠ w) (hinv : (u : K) * w ≠ 1) : T.X u ≠ T.X w := by
  intro hX
  have E1 := (WeierstrassCurve.Affine.equation_iff _ _).mp (tateEquation h12 hu)
  have E2 := (WeierstrassCurve.Affine.equation_iff _ _).mp (tateEquation h12 hw)
  simp only [tateCurve_a₁, tateCurve_a₂, tateCurve_a₃] at E1 E2
  rw [hX] at E1
  have hfac : (T.Y u - T.Y w) * (T.Y u + T.Y w + T.X w) = 0 := by
    linear_combination E1 - E2
  rcases mul_eq_zero.mp hfac with h | h
  · obtain ⟨m, hm⟩ := exists_zpow_of_coords_eq h12 h2 hu hw hX (sub_eq_zero.mp h)
    exact hne (eq_of_norm_one_of_eq_zpow T hnu hnw hm)
  · have hwi := offOrbit_inv T hw
    obtain ⟨m, hm⟩ := exists_zpow_of_coords_eq h12 h2 hu hwi (by rw [T.X_inv hw, hX])
      (by rw [T.Y_inv hw]; linear_combination h)
    have hnwi : ‖((w⁻¹ : Kˣ) : K)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, hnw, inv_one]
    have e := eq_of_norm_one_of_eq_zpow T hnu hnwi hm
    apply hinv
    rw [e, Units.val_inv_eq_inv_val, inv_mul_cancel₀ w.ne_zero]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem norm_neg_one_val : ‖((-1 : Kˣ) : K)‖ = 1 := by simp

omit [CharZero K] in
/-- **Translation by the `2`-torsion point `-1` is an involution** (`P(-1) + P(-1) = 0`). -/
theorem transT_transT_negOne (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) (T : TateParameter K)
    [T.tateCurve.IsElliptic] (f : TateField T) :
    transT h12 (offOrbit_neg_one T h2) (transT h12 (offOrbit_neg_one T h2) f) = f := by
  classical
  have hmem : ∀ w : Kˣ, (∀ n : ℤ, (T.q : K) ^ n * (w : K) ≠ 1) →
      T.tateCurve.toAffine.Equation (T.X w) (T.Y w) := fun w hw => T.tatePoint_mem' h12 hw
  have tame : TameResidueChar K := ⟨h2, h12⟩
  have hnm : (-1 : Kˣ) ∉ T.qpowers := fun h =>
    (T.mem_qpowers_iff _).mp h |>.elim fun n hn => offOrbit_neg_one T h2 n hn
  set P := T.tatePoint hmem tame (-1) with hPdef
  have hPP : P + P = 0 := by
    rw [hPdef, ← T.tatePoint_mul, neg_one_mul, neg_neg, T.tatePoint_one]
  have hP : ∀ g, translateAut P g = transT h12 (offOrbit_neg_one T h2) g := fun g => by
    rw [hPdef, T.tatePoint_of_notMem hmem tame hnm, translateAut_apply_some]
    rfl
  rw [← hP, ← hP]
  have h := translateAut_add P P
  rw [hPP, translateAut_zero] at h
  rw [← AlgEquiv.mul_apply, ← h, AlgEquiv.one_apply]

end NormOne

/-! ### The level `K(E_{q^N})` -/

section Level

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

variable (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)

/-- The value data of the level coordinates `x_Q∘ψ, y_Q∘ψ` of `Ÿ'_N` (`ψ(u) = u^N`). -/
abbrev LevelVals {N : ℕ} (hN : 0 < N) (gX gY : TateField t) : Prop :=
  ∀ (u : Kˣ) (hu : OffOrbit t u), OffOrbit t (u ^ (2 * N)) →
    HasTateValue t h12 gX hu ((sqrtPow hs N hN).X (u ^ N)) ∧
    HasTateValue t h12 gY hu ((sqrtPow hs N hN).Y (u ^ N))

include h2 in
theorem isTPoint_of_levelVals [t.tateCurve.IsElliptic] {N : ℕ} (hN : 0 < N) [NeZero (2 * N)]
    {gX gY : TateField t} (hval : LevelVals h12 hs hN gX gY) :
    IsTPoint (sqrtPow hs N hN) gX gY := by
  have hψ0 := psiN_ne_zero_of_neZero t.tateCurve (2 * N)
  have hpts : ∀ (u : Kˣ) (hu : OffOrbit t u),
      evalTate t h12 hu (psiN t.tateCurve (2 * N)) ≠ 0 → OffOrbit t (u ^ (2 * N)) :=
    fun u hu hψ => (hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu hψ).1
  exact isTPoint_of_values (h12 := h12) hψ0 (fun u => u ^ N)
    fun u hu hψ => ⟨offOrbit_sqrt_pow hs _ rfl (hpts u hu hψ), (hval u hu (hpts u hu hψ)).1,
      (hval u hu (hpts u hu hψ)).2⟩

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem transcendental_of_levelVals [t.tateCurve.IsElliptic] {N : ℕ} (hN : 0 < N)
    [NeZero (2 * N)] {gX gY : TateField t} (hpt : IsTPoint (sqrtPow hs N hN) gX gY)
    (hmul : ∀ a : TateRing t, algebraMap _ (TateField t) (mulByNHom t.tateCurve (2 * N) a) ∈
      IntermediateField.adjoin K ({gX, gY} : Set (TateField t))) :
    Transcendental K gX := by
  set Rt : TateField t := algebraMap (coverRingN t.tateCurve (2 * N)) (TateField t)
    (mulByNHom t.tateCurve (2 * N) (xE t.tateCurve)) with hRtdef
  have hRt : mulByNEmb t.tateCurve (2 * N) Rt = τ := tau_eq t.tateCurve (2 * N)
  have htrR : Transcendental K Rt := fun h =>
    transcendental_tau t.tateCurve (hRt ▸ h.algHom (mulByNEmb t.tateCurve (2 * N)))
  exact transcendental_of_mem_adjoin gX gY hpt (hmul _) htrR

/-- **The level of `E_{q^N} → E_q`** (`N` even): the image under `ι = φ ∘ j` of the fixed
field of the translation by `U = -1` on `K(E_Q)`, `Q = s^N` (`E_Q/⟨-1⟩ ≅ E_{q^N}`, `U ↦ U²`). -/
def levelQuot [t.tateCurve.IsElliptic] {N : ℕ} (hN : 0 < N) [NeZero (2 * N)]
    [(sqrtPow hs N hN).tateCurve.IsElliptic] (gX gY : TateField t)
    (hpt : IsTPoint (sqrtPow hs N hN) gX gY) (htr : Transcendental K gX) :
    IntermediateField (K₀ K τ) Ω :=
  IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) ''
    (pullbackT gX gY hpt htr '' {f | transT h12 (offOrbit_neg_one _ h2) f = f}))

theorem levelQuot_le_mulByNField [t.tateCurve.IsElliptic] {N : ℕ} (hN : 0 < N) [NeZero (2 * N)]
    [(sqrtPow hs N hN).tateCurve.IsElliptic] (gX gY : TateField t)
    (hpt : IsTPoint (sqrtPow hs N hN) gX gY) (htr : Transcendental K gX) :
    levelQuot h2 h12 hs hN gX gY hpt htr ≤ mulByNField t.tateCurve (2 * N) :=
  adjoin_image_le_mulByNField _ _ _

include h2 in
/-- **`L_X ≤ K(E_{q^N})`**: `t_{-1}` fixes `R = X_q(U²)` and `R_y = Y_q(U²)`, whose images are
`[2N]^*x`, `[2N]^*y`. -/
theorem hemiL_le_levelQuot [t.tateCurve.IsElliptic] {N : ℕ} (hN : 0 < N) (hev : Even N)
    [NeZero (2 * N)] [(sqrtPow hs N hN).tateCurve.IsElliptic] {gX gY : TateField t}
    (hval : LevelVals h12 hs hN gX gY) (hpt : IsTPoint (sqrtPow hs N hN) gX gY)
    (htr : Transcendental K gX) :
    (hemiData t.tateCurve).L ≤ levelQuot h2 h12 hs hN gX gY hpt htr := by
  set T := sqrtPow hs N hN with hTdef
  have hψ0 := psiN_ne_zero_of_neZero t.tateCurve (2 * N)
  have hpts : ∀ (u : Kˣ) (hu : OffOrbit t u),
      evalTate t h12 hu (psiN t.tateCurve (2 * N)) ≠ 0 → OffOrbit t (u ^ (2 * N)) :=
    fun u hu hψ => (hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu hψ).1
  set j := pullbackT gX gY hpt htr with hjdef
  have htrans : ∀ (u : Kˣ) (hu : OffOrbit t u) (hum : OffOrbit t (u ^ (2 * N)))
      {g : TateField T} {c : K}, HasTateValue T h12 g (offOrbit_sqrt_pow hs T rfl hum) c →
      HasTateValue t h12 (j g) hu c := fun u hu hum _ _ hg =>
    hasTateValue_pullbackT hpt htr _ (hval u hu hum).1 (hval u hu hum).2 hg
  obtain ⟨A₁, B₁, A₂, B₂, -, -, -, -, hR⟩ := exists_poly_isogenyX_deg t h12 hs hN T rfl
  obtain ⟨C₁, E₁, C₂, E₂, hRy⟩ := exists_poly_isogenyY t hs hN T rfl h12 hev
  set R := algebraMap _ (TateField T) (polyXY T A₁ B₁) /
    algebraMap _ (TateField T) (polyXY T A₂ B₂) with hRdef
  set Ry := algebraMap _ (TateField T) (polyXY T C₁ E₁) /
    algebraMap _ (TateField T) (polyXY T C₂ E₂) with hRydef
  have hjR : j R = algebraMap (coverRingN t.tateCurve (2 * N)) (TateField t)
      (mulByNHom t.tateCurve (2 * N) (xE t.tateCurve)) := by
    refine eq_of_hasTateValue (h12 := h12) hψ0 (G := fun u => t.X (u ^ (2 * N)))
      (fun u hu hψ => ?_) (fun u hu hψ => ?_)
    · have hum := hpts u hu hψ
      have e : (u ^ N) ^ 2 = u ^ (2 * N) := by rw [← pow_mul, mul_comm]
      have hum2 : OffOrbit t ((u ^ N) ^ 2) := by rw [e]; exact hum
      exact (htrans u hu hum (hasTateValue_R hR _ hum2)).congr (by rw [e])
    · obtain ⟨hum, hv⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu hψ
      exact (hv (xE t.tateCurve)).congr (by
        rw [show xE t.tateCurve = mkT t (C X) from rfl, evalTate_mk_C, eval_X])
  have hjRy : j Ry = algebraMap (coverRingN t.tateCurve (2 * N)) (TateField t)
      (mulByNHom t.tateCurve (2 * N) (yE t.tateCurve)) := by
    refine eq_of_hasTateValue (h12 := h12) hψ0 (G := fun u => t.Y (u ^ (2 * N)))
      (fun u hu hψ => ?_) (fun u hu hψ => ?_)
    · have hum := hpts u hu hψ
      have e : (u ^ N) ^ 2 = u ^ (2 * N) := by rw [← pow_mul, mul_comm]
      have hum2 : OffOrbit t ((u ^ N) ^ 2) := by rw [e]; exact hum
      exact (htrans u hu hum (hasTateValue_Ry h12 hRy _ hum2)).congr (by rw [e])
    · obtain ⟨hum, hv⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu hψ
      exact (hv (yE t.tateCurve)).congr (by
        rw [show yE t.tateCurve = mkT t Polynomial.X from rfl, evalTate_mk_Y])
  have hk : ∃ k : ℤ, ((-1 : Kˣ) : K) ^ 2 = (t.q : K) ^ k := ⟨0, by simp⟩
  have hRfix : transT h12 (offOrbit_neg_one T h2) R = R :=
    transT_R_eq hs hN rfl h2 hR (offOrbit_neg_one T h2) hk
  have hRyfix : transT h12 (offOrbit_neg_one T h2) Ry = Ry :=
    transT_Ry_eq rfl hN h12 hs hRy h2 (offOrbit_neg_one T h2) hk
  unfold levelQuot
  refine hemiL_le_adjoin t.tateCurve (2 * N) fun a => mulByNHom_mem_of_xy (2 * N) ?_ ?_ a
  · exact IntermediateField.subset_adjoin K _ ⟨R, hRfix, hjR⟩
  · exact IntermediateField.subset_adjoin K _ ⟨Ry, hRyfix, hjRy⟩

/-! ### The canonical level coordinates `levelCoords j` (`N_j = 2(j+1)`) -/

variable [t.tateCurve.IsElliptic]

include h2 in
theorem exists_levelCoords (j : ℕ) : ∃ g : TateField t × TateField t,
    (∀ a : TateRing t, algebraMap _ (TateField t) (mulByNHom t.tateCurve (2 * (2 * (j + 1))) a) ∈
      IntermediateField.adjoin K ({g.1, g.2} : Set (TateField t))) ∧
    LevelVals h12 hs (N := 2 * (j + 1)) (Nat.mul_pos two_pos j.succ_pos) g.1 g.2 := by
  obtain ⟨gX, gY, _F, _hF, hmul, _hu, hval⟩ :=
    exists_levelData (t := t) h12 h2 hs (N := 2 * (j + 1)) (Nat.mul_pos two_pos j.succ_pos)
      ⟨j + 1, by ring⟩
  exact ⟨(gX, gY), hmul, fun u hu hum => ⟨(hval u hu hum).1, (hval u hu hum).2.1⟩⟩

/-- **The level coordinates of `Ÿ'_{N_j}`** (`x_Q∘ψ, y_Q∘ψ`, `Q = s^{N_j}`, `ψ(u) = u^{N_j}`;
unique by their values, `eq_levelCoords`). -/
def levelCoords (j : ℕ) : TateField t × TateField t :=
  (exists_levelCoords h2 h12 hs j).choose

theorem levelCoords_spec (j : ℕ) :
    (∀ a : TateRing t, algebraMap _ (TateField t) (mulByNHom t.tateCurve (2 * (2 * (j + 1))) a) ∈
      IntermediateField.adjoin K ({(levelCoords h2 h12 hs j).1, (levelCoords h2 h12 hs j).2} :
        Set (TateField t))) ∧
    LevelVals h12 hs (N := 2 * (j + 1)) (Nat.mul_pos two_pos j.succ_pos) (levelCoords h2 h12 hs j).1
      (levelCoords h2 h12 hs j).2 :=
  (exists_levelCoords h2 h12 hs j).choose_spec

include h2 in
/-- **The level coordinates are unique** (identity principle on Tate values). -/
theorem eq_levelCoords (j : ℕ) {gX gY : TateField t}
    (hval : LevelVals h12 hs (N := 2 * (j + 1)) (Nat.mul_pos two_pos j.succ_pos) gX gY) :
    gX = (levelCoords h2 h12 hs j).1 ∧ gY = (levelCoords h2 h12 hs j).2 := by
  have hψ0 := psiN_ne_zero_of_neZero t.tateCurve (2 * (2 * (j + 1)))
  have hpts : ∀ (u : Kˣ) (hu : OffOrbit t u),
      evalTate t h12 hu (psiN t.tateCurve (2 * (2 * (j + 1)))) ≠ 0 →
        OffOrbit t (u ^ (2 * (2 * (j + 1)))) :=
    fun u hu hψ => (hasTateValue_mulByNHom (h12 := h12) _ h2 hu hψ).1
  have hc := (levelCoords_spec h2 h12 hs j).2
  exact ⟨eq_of_hasTateValue (h12 := h12) hψ0 (fun u hu hψ => (hval u hu (hpts u hu hψ)).1)
      (fun u hu hψ => (hc u hu (hpts u hu hψ)).1),
    eq_of_hasTateValue (h12 := h12) hψ0 (fun u hu hψ => (hval u hu (hpts u hu hψ)).2)
      (fun u hu hψ => (hc u hu (hpts u hu hψ)).2)⟩

omit [CharZero K] [t.tateCurve.IsElliptic] in
include h12 in
theorem isElliptic_sqrtPow (j : ℕ) :
    (sqrtPow hs (2 * (j + 1)) (by omega)).tateCurve.IsElliptic :=
  (sqrtPow hs (2 * (j + 1)) (by omega)).tateCurve_isElliptic h12

theorem isTPoint_levelCoords (j : ℕ) :
    IsTPoint (sqrtPow hs (2 * (j + 1)) (by omega)) (levelCoords h2 h12 hs j).1
      (levelCoords h2 h12 hs j).2 :=
  isTPoint_of_levelVals h2 h12 hs _ (levelCoords_spec h2 h12 hs j).2

theorem transcendental_levelCoords (j : ℕ) : Transcendental K (levelCoords h2 h12 hs j).1 :=
  transcendental_of_levelVals hs _ (isTPoint_levelCoords h2 h12 hs j)
    (levelCoords_spec h2 h12 hs j).1

/-- **The level `K(E_{q^{N_j}})` ⊆ `Ω`** (`N_j = 2(j+1)`): the level of the cyclic cover
`E_{q^{N_j}} → E_q`, `v ↦ v`, inside the source of `[2N_j]` (`levelQuot` of `levelCoords j`). -/
def levelQN (j : ℕ) : IntermediateField (K₀ K τ) Ω :=
  haveI := isElliptic_sqrtPow h12 hs j
  levelQuot h2 h12 hs (N := 2 * (j + 1)) (Nat.mul_pos two_pos j.succ_pos)
    (levelCoords h2 h12 hs j).1 (levelCoords h2 h12 hs j).2 (isTPoint_levelCoords h2 h12 hs j)
    (transcendental_levelCoords h2 h12 hs j)

theorem hemiL_le_levelQN (j : ℕ) : (hemiData t.tateCurve).L ≤ levelQN h2 h12 hs j :=
  haveI := isElliptic_sqrtPow h12 hs j
  hemiL_le_levelQuot h2 h12 hs _ ⟨j + 1, by ring⟩ (levelCoords_spec h2 h12 hs j).2 _ _

theorem levelQN_le_mulByNField (j : ℕ) :
    levelQN h2 h12 hs j ≤ mulByNField t.tateCurve (2 * (2 * (j + 1))) :=
  haveI := isElliptic_sqrtPow h12 hs j
  levelQuot_le_mulByNField h2 h12 hs _ _ _ _ _

instance finiteDimensional_levelQN (j : ℕ) :
    FiniteDimensional (K₀ K τ) (levelQN h2 h12 hs j) :=
  FiniteDimensional.of_injective
    (IntermediateField.inclusion (levelQN_le_mulByNField h2 h12 hs j)).toLinearMap
    (IntermediateField.inclusion (levelQN_le_mulByNField h2 h12 hs j)).injective

theorem isOpen_levelQN (j : ℕ) :
    IsOpen ((levelQN h2 h12 hs j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)) :=
  IntermediateField.fixingSubgroup_isOpen _

theorem etale_levelQN (j : ℕ) :
    (ringMap τ (hemiL_le_levelQN h2 h12 hs j)).toRingHom.Etale :=
  etale_of_le_mulByNField t.tateCurve _ _ (levelQN_le_mulByNField h2 h12 hs j)

/-! ### `L_j ≤ M ⊔ K(E_{q^{N_j}})` -/

/-- **The level `Ÿ'_{N_j}` lies in `M ⊔ K(E_{q^{N_j}})`** whenever `φ_2(x) ∈ M` (`M = L_0`, the
source of `[2]`): `z ∈ K(E_Q)` with values `X_q(U)` has `ι z = φ_2(x)` and `t_{-1} z ≠ z`. -/
theorem adjoin_levelCoords_le (j : ℕ) {M : IntermediateField (K₀ K τ) Ω}
    (hM : mulByNEmb t.tateCurve 2 (algebraMap (TateRing t) (TateField t) (xE t.tateCurve)) ∈ M) :
    IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * (2 * (j + 1))) ''
      {(levelCoords h2 h12 hs j).1, (levelCoords h2 h12 hs j).2}) ≤ M ⊔ levelQN h2 h12 hs j := by
  haveI := isElliptic_sqrtPow h12 hs j
  set N := 2 * (j + 1) with hNdef
  have hN : 0 < N := by omega
  set T := sqrtPow hs N hN with hTdef
  set gX := (levelCoords h2 h12 hs j).1
  set gY := (levelCoords h2 h12 hs j).2
  have hval := (levelCoords_spec h2 h12 hs j).2
  set hpt := isTPoint_levelCoords h2 h12 hs j
  set htr := transcendental_levelCoords h2 h12 hs j
  set jj := pullbackT gX gY hpt htr with hjjdef
  set ι : TateField T →ₐ[K] Ω := (mulByNEmb t.tateCurve (2 * N)).comp jj with hιdef
  set ρ := transT h12 (offOrbit_neg_one T h2) with hρdef
  have hTq : T.q = t.q ^ (j + 1) := by
    rw [hTdef, sqrtPow_q, ← hs, ← pow_mul]
  -- the element `z` with values `X_q(U)`
  obtain ⟨A₁, B₁, A₂, B₂, hA⟩ :=
    exists_poly_quotX (T := t) (T' := T) (M := j + 1) (by omega) hTq h12
  set z := algebraMap _ (TateField T) (polyXY T A₁ B₁) /
    algebraMap _ (TateField T) (polyXY T A₂ B₂) with hzdef
  have hzv : ∀ (v : Kˣ) (hv : OffOrbit T v), OffOrbit t v → HasTateValue T h12 z hv (t.X v) := by
    intro v hv hvt
    obtain ⟨hd, he⟩ := hA v hv
    have hθ := theta_neg_ne_zero t hvt
    refine ((HasTateValue.ofRing hv _).div (HasTateValue.ofRing hv _)
      (by rw [evalTate_polyXY]; exact hd.mpr hθ)).congr ?_
    rw [evalTate_polyXY, evalTate_polyXY, he hθ]
  -- `ι z = φ_2(x)`
  have hjz : jj z = pb t.tateCurve N (algebraMap (TateRing t) (TateField t) (xE t.tateCurve)) := by
    have hD : psiN t.tateCurve (2 * N) * psiN t.tateCurve N ≠ 0 :=
      mul_ne_zero (psiN_ne_zero_of_neZero _ _) (psiN_ne_zero_of_neZero _ _)
    refine eq_of_hasTateValue (h12 := h12) hD (G := fun u => t.X (u ^ N))
      (fun u hu h0 => ?_) (fun u hu h0 => ?_)
    · rw [map_mul] at h0
      obtain ⟨hum2, -⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu (left_ne_zero_of_mul h0)
      obtain ⟨hum, -⟩ := hasTateValue_pb (h12 := h12) h2 N hu (right_ne_zero_of_mul h0)
      exact hasTateValue_pullbackT hpt htr _ (hval u hu hum2).1 (hval u hu hum2).2
        (hzv _ (offOrbit_sqrt_pow hs T rfl hum2) hum)
    · rw [map_mul] at h0
      obtain ⟨hum, hpb⟩ := hasTateValue_pb (h12 := h12) h2 N hu (right_ne_zero_of_mul h0)
      exact hpb _ _ (HasTateValue.x hum)
  have hιz : ι z ∈ M := by
    haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
    rw [hιdef, AlgHom.comp_apply, hjz, ← AlgHom.comp_apply,
      mulByNEmb_comp_pb_eq (m := 2) (r := N) (m' := 2 * N) (by ring)]
    exact hM
  -- `t_{-1} z ≠ z`: the values at `U = 2` and `U = -2` differ
  have hρz : ρ z ≠ z := by
    intro hfix
    have hn2 : ‖((twoU h2 : Kˣ) : K)‖ = 1 := by simpa using h2
    have hn2' : ‖((twoU h2 * -1 : Kˣ) : K)‖ = 1 := by simpa using h2
    have h2T : OffOrbit T (twoU h2) := offOrbit_of_norm_one T hn2 (by norm_num)
    have h2t : OffOrbit t (twoU h2) := offOrbit_of_norm_one t hn2 (by norm_num)
    have hm2T : OffOrbit T (twoU h2 * -1) := offOrbit_of_norm_one T hn2' (by norm_num)
    have hm2t : OffOrbit t (twoU h2 * -1) := offOrbit_of_norm_one t hn2' (by norm_num)
    have hxT : T.X (twoU h2) ≠ T.X (-1) :=
      X_ne_X_of_norm_one h12 h2 T h2T (offOrbit_neg_one T h2) hn2 norm_neg_one_val
        (by norm_num) (by norm_num)
    have hv1 := hzv _ h2T h2t
    have hv2 := hasTateValue_trans h2 h2T (offOrbit_neg_one T h2) hm2T hxT z _ (hzv _ hm2T hm2t)
    rw [← hρdef, hfix] at hv2
    exact X_ne_X_of_norm_one h12 h2 t h2t hm2t hn2 hn2' (by norm_num) (by norm_num)
      (hv1.unique hv2)
  -- conclusion
  have key : ∀ f, ι f ∈ M ⊔ levelQN h2 h12 hs j := by
    intro f
    have h2F : (2 : TateField T) ≠ 0 := by
      have h := (algebraMap K (TateField T)).injective.ne (two_ne_zero (α := K))
      rwa [map_ofNat, map_zero] at h
    have h := mem_sup_adjoin_fixed (B := K₀ K τ) ι ρ (transT_transT_negOne h2 h12 T) h2F
      hρz hιz f
    have e : ι '' {g | ρ g = g} = mulByNEmb t.tateCurve (2 * N) ''
        (jj '' {f | transT h12 (offOrbit_neg_one T h2) f = f}) := by
      rw [hιdef, AlgHom.coe_comp, Set.image_comp]
    rw [e] at h
    exact h
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨g, hg, rfl⟩
  rcases hg with rfl | rfl
  · have := key (algebraMap (TateRing T) (TateField T) (mkT T (C X)))
    rwa [hιdef, AlgHom.comp_apply, hjjdef, pullbackT_genX] at this
  · have := key (algebraMap (TateRing T) (TateField T) (mkT T Polynomial.X))
    rwa [hιdef, AlgHom.comp_apply, hjjdef, pullbackT_genY] at this

end Level

end Iut.EtaleTheta
