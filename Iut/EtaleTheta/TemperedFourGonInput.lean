/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.TemperedLevelTwo
import TemperedFundamentalGroups.Andre.TateFourGonCover

/-!
# The `ℙ⁴`-model input of `E_{q²}` for (Z_2) = `ZM 0` (TFGD run 5, step 5)

Let `s² = q`, `t₂ = sqrtPow hs 4` the Tate parameter `q² = s⁴` of `E_{q²}`. This file provides
the Tate-series side of the explicit model of `E_{q²} → E_q` (`TFGD-plan.md`, run 4):

* **Vélu = series splitting** (`velu_X`, `velu_Y`): splitting the Tate series of `E_q` into
  even and odd indices gives, for every `v`,
  `X_q(v) = X_{q²}(v) + X_{q²}(v·s²) − x_T` and `Y_q(v) = Y_{q²}(v) + Y_{q²}(v·s²) + c_y`, where
  `x_T = X_{q²}(s²) = 2s₁(q) − 4s₁(q²)` (`xT_eq`) is the `x`-coordinate of the `2`-torsion
  point `T = P(q)` of `E_{q²}` and `c_y = s₁(q) − 2s₁(q²)`;
* **translation by `T`** (`addT_rels`, `tate_addT_rels`): with `C_T = 3x_T² + a₄' + x_T/2`,
  `(x₁ − x_T)(x₂ − x_T) = C_T`, `(2y₂ + x₂)(x₁ − x_T) + (2y₁ + x₁)(x₂ − x_T) = 0`,
  `(2y₁ + x₁)(2y₂ + x₂) + C_T(4(x₁ + x₂) + 4x_T + 1) = 0` for `(x₁, y₁) = P(v)`,
  `(x₂, y₂) = P(v·q)` on `E_{q²}`;
* the norm estimates of the coefficients;
* **the `Ω`-level input** (`exists_fourGonInput`): `x₁, y₁, x₂, y₂ ∈ R' = K[E_{q²}]` (the
  coordinate ring of `levelQN 0`, `x₁R` …) with the `ℙ⁴`-model relations, Vélu
  `x = x₁ + x₂ − πε`, `y = y₁ + y₂ + πκ` (`exists_fourGonInput_rels`) and the fibre property
  (`fourGon_fibre`): two `R`-algebra maps `R' → Ω` agree or swap `(x₁, y₁) ↔ (x₂, y₂)`.
  The key step is `levelQN_le_adjoinS`, `K(E_{q²}) = K(τ)(x₁, y₁, x₂, y₂)`, by Galois theory
  (`iotaQ_galois`: `Gal(Ω/L_X)` acts on `K(E_Q)` by translations `t_w`, `w ∈ {±1, ±s}`).
-/

open Polynomial

noncomputable section

universe u

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine

/-! ### Splitting sums over `ℤ` into even and odd indices -/

section Split

variable {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [T2Space M]

theorem tsum_int_even_add_odd {f : ℤ → M} (hf : Summable f) :
    ∑' n, f n = ∑' m, f (2 * m) + ∑' m, f (2 * m + 1) := by
  have he : Function.Injective (fun m : ℤ => 2 * m) := fun a b h => by
    simp only at h; omega
  have ho : Function.Injective (fun m : ℤ => 2 * m + 1) := fun a b h => by
    simp only at h; omega
  have hc : IsCompl (Set.range fun m : ℤ => 2 * m) (Set.range fun m : ℤ => 2 * m + 1) := by
    constructor
    · rw [Set.disjoint_left]
      rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
      simp only at hb
      omega
    · rw [codisjoint_iff]
      refine Set.eq_univ_of_forall fun n => ?_
      obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
      · exact Or.inl ⟨k, hk.symm⟩
      · exact Or.inr ⟨k, hk.symm⟩
  have h1 := (he.hasSum_range_iff (f := f)).2 (hf.comp_injective he).hasSum
  have h2 := (ho.hasSum_range_iff (f := f)).2 (hf.comp_injective ho).hasSum
  exact (h1.add_isCompl hc h2).tsum_eq

end Split

/-! ### Vélu for `E_{q²} → E_q`, `v ↦ v`: splitting the Tate series -/

section Velu

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K} {s : Kˣ} (hs : s ^ 2 = t.q)

/-- The Tate parameter `q² = s⁴` of `E_{q²}`. -/
abbrev tq2 : TateParameter K := sqrtPow hs 4 (by norm_num)

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem val_q_eq : (t.q : K) = (s : K) ^ 2 := by
  rw [← hs, Units.val_pow_eq_pow_val]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem val_tq2_q : ((tq2 hs).q : K) = (s : K) ^ 4 := by
  rw [sqrtPow_q, Units.val_pow_eq_pow_val]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem zpow_even (a : K) (m : ℤ) : (a ^ 2) ^ (2 * m) = (a ^ 4) ^ m := by
  rw [zpow_mul, show ((a ^ 2) ^ (2 : ℤ)) = a ^ 4 by rw [zpow_two, ← pow_two, ← pow_mul]]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem zpow_odd {a : K} (ha : a ≠ 0) (m : ℤ) (v : K) :
    (a ^ 2) ^ (2 * m + 1) * v = (a ^ 4) ^ m * (v * a ^ 2) := by
  rw [zpow_add₀ (pow_ne_zero 2 ha), zpow_even, zpow_one]; ring

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem Xterm_even (v : Kˣ) (m : ℤ) : t.Xterm v (2 * m) = (tq2 hs).Xterm v m := by
  simp only [Xterm_apply, val_q_eq hs, val_tq2_q, zpow_even]

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem Xterm_odd (v : Kˣ) (m : ℤ) :
    t.Xterm v (2 * m + 1) = (tq2 hs).Xterm (v * s ^ 2) m := by
  simp only [Xterm_apply, val_q_eq hs, val_tq2_q, Units.val_mul, Units.val_pow_eq_pow_val,
    zpow_odd s.ne_zero]

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem Yterm_even (v : Kˣ) (m : ℤ) : t.Yterm v (2 * m) = (tq2 hs).Yterm v m := by
  simp only [Yterm_apply, val_q_eq hs, val_tq2_q, zpow_even]

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem Yterm_odd (v : Kˣ) (m : ℤ) :
    t.Yterm v (2 * m + 1) = (tq2 hs).Yterm (v * s ^ 2) m := by
  simp only [Yterm_apply, val_q_eq hs, val_tq2_q, Units.val_mul, Units.val_pow_eq_pow_val,
    zpow_odd s.ne_zero]

include hs in
/-- **Vélu, `x`** (series splitting): `X_q(v) = X_{q²}(v) + X_{q²}(v·s²) + 4s₁(q²) − 2s₁(q)`. -/
theorem velu_X_aux (v : Kˣ) :
    t.X v = (tq2 hs).X v + (tq2 hs).X (v * s ^ 2) +
      (4 * (tq2 hs).eisenstein 1 - 2 * t.eisenstein 1) := by
  rw [X_apply, X_apply, X_apply, tsum_int_even_add_odd (t.Xterm_summable v)]
  simp only [Xterm_even hs, Xterm_odd hs]
  ring

include hs in
/-- **Vélu, `y`** (series splitting): `Y_q(v) = Y_{q²}(v) + Y_{q²}(v·s²) + s₁(q) − 2s₁(q²)`. -/
theorem velu_Y (v : Kˣ) :
    t.Y v = (tq2 hs).Y v + (tq2 hs).Y (v * s ^ 2) +
      (t.eisenstein 1 - 2 * (tq2 hs).eisenstein 1) := by
  rw [Y_apply, Y_apply, Y_apply, tsum_int_even_add_odd (t.Yterm_summable v)]
  simp only [Yterm_even hs, Yterm_odd hs]
  ring

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem eisP_inv (x : K) : eisP x⁻¹ = eisP x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  simp only [eisP]
  rw [show (1 - x⁻¹) = -(1 - x) / x by field_simp; ring, div_pow, neg_sq]
  rcases eq_or_ne (1 - x) 0 with h | h
  · simp [h]
  field_simp

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem Xterm_sq_eq (m : ℤ) :
    (tq2 hs).Xterm (s ^ 2) m = eisP (((s : K) ^ 2) ^ (2 * m + 1)) := by
  simp only [Xterm_apply, val_tq2_q, Units.val_pow_eq_pow_val, eisP]
  rw [zpow_add₀ (pow_ne_zero 2 s.ne_zero), zpow_even, zpow_one]

include hs in
theorem tsum_Xterm_sq :
    (∑' m : ℤ, (tq2 hs).Xterm (s ^ 2) m) =
      2 * ∑' k : ℕ, eisP ((t.q : K) ^ (2 * k + 1)) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simp only at h; omega
  have hO : Summable fun k : ℕ => eisP ((t.q : K) ^ (2 * k + 1)) :=
    t.summable_pSum_terms.comp_injective hinj
  have h1 : HasSum (fun n : ℕ => (tq2 hs).Xterm (s ^ 2) (n : ℤ))
      (∑' k : ℕ, eisP ((t.q : K) ^ (2 * k + 1))) := by
    refine hO.hasSum.congr_fun fun k => ?_
    rw [Xterm_sq_eq hs, val_q_eq hs,
      show (2 * ((k : ℕ) : ℤ) + 1) = ((2 * k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have h2 : HasSum (fun n : ℕ => (tq2 hs).Xterm (s ^ 2) (-((n : ℤ) + 1)))
      (∑' k : ℕ, eisP ((t.q : K) ^ (2 * k + 1))) := by
    refine hO.hasSum.congr_fun fun k => ?_
    rw [Xterm_sq_eq hs, val_q_eq hs,
      show (2 * (-((k : ℕ) + 1 : ℤ)) + 1) = -((2 * k + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, eisP_inv]
  rw [(h1.of_nat_of_neg_add_one h2).tsum_eq]; ring

include hs in
theorem pSum_split :
    t.pSum = (∑' k : ℕ, eisP ((t.q : K) ^ (2 * k + 1))) + (tq2 hs).pSum := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simp only at h; omega
  have hinj' : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by
    simp only at h; omega
  have hO : Summable fun k : ℕ => eisP ((t.q : K) ^ (2 * k + 1)) :=
    t.summable_pSum_terms.comp_injective hinj
  have hE : Summable fun k : ℕ => eisP ((t.q : K) ^ (2 * k + 1 + 1)) :=
    t.summable_pSum_terms.comp_injective hinj'
  have hsplit := tsum_even_add_odd (f := fun k : ℕ => eisP ((t.q : K) ^ (k + 1))) hO hE
  have hev' : (∑' k : ℕ, eisP ((t.q : K) ^ (2 * k + 1 + 1))) = (tq2 hs).pSum := by
    rw [pSum]
    refine tsum_congr fun k => ?_
    rw [val_tq2_q, val_q_eq hs, ← pow_mul,
      show 2 * (2 * k + 1 + 1) = 4 * (k + 1) by ring, pow_mul]
  rw [pSum, ← hsplit, hev']

include hs in
/-- **The `x`-coordinate of the `2`-torsion point `P(q)` of `E_{q²}`**:
`X_{q²}(s²) = 2s₁(q) − 4s₁(q²)` (Lambert form `s₁ = ∑ eisP(qᵏ)`, `pSum_eq_eisenstein_one`). -/
theorem xT_eq : (tq2 hs).X (s ^ 2) = 2 * t.eisenstein 1 - 4 * (tq2 hs).eisenstein 1 := by
  rw [X_apply, tsum_Xterm_sq hs, ← t.pSum_eq_eisenstein_one,
    ← (tq2 hs).pSum_eq_eisenstein_one, pSum_split hs]
  ring

include hs in
/-- **Vélu, `x`**: `X_q(v) = X_{q²}(v) + X_{q²}(v·s²) − x_T`, `x_T = X_{q²}(s²)`. -/
theorem velu_X (v : Kˣ) :
    t.X v = (tq2 hs).X v + (tq2 hs).X (v * s ^ 2) - (tq2 hs).X (s ^ 2) := by
  rw [velu_X_aux hs v, xT_eq hs]; ring

end Velu

/-! ### The `2`-torsion point `T = P(q)` of `E_{q²}` and the translation by `T` -/

/-- **Translation by a `2`-torsion point, algebraically**: for `(x₁, y₁)` on
`y² + xy = x³ + a₄x + a₆`, the `2`-torsion point `(e, -e/2)` and `P₂ = P₁ + T` given by the
chord slope `ℓ` (`y₁ = ℓ(x₁ − e) − e/2`), the relations of the `ℙ⁴`-model hold. -/
theorem addT_rels {F : Type*} [Field F] [CharZero F] {a₄ a₆ x₁ y₁ e x₂ y₂ ℓ : F} (hd : x₁ - e ≠ 0)
    (E₁ : y₁ ^ 2 + x₁ * y₁ = x₁ ^ 3 + a₄ * x₁ + a₆)
    (ET : (-e / 2) ^ 2 + e * (-e / 2) = e ^ 3 + a₄ * e + a₆)
    (hℓ : y₁ = ℓ * (x₁ - e) - e / 2) (hx₂ : x₂ = ℓ ^ 2 + ℓ - x₁ - e)
    (hy₂ : y₂ = -(ℓ * (x₂ - x₁) + y₁) - x₂) :
    (x₁ - e) * (x₂ - e) = 3 * e ^ 2 + a₄ + e / 2 ∧
    (2 * y₂ + x₂) * (x₁ - e) + (2 * y₁ + x₁) * (x₂ - e) = 0 ∧
    (2 * y₁ + x₁) * (2 * y₂ + x₂) + (3 * e ^ 2 + a₄ + e / 2) * (4 * (x₁ + x₂) + 4 * e + 1) = 0 := by
  subst hy₂ hx₂ hℓ
  have key : (x₁ - e) * (ℓ ^ 2 * (x₁ - e) + ℓ * (x₁ - e) -
      (x₁ ^ 2 + x₁ * e + e ^ 2 + a₄ + e / 2)) = 0 := by
    linear_combination E₁ - ET
  have k' := (mul_eq_zero.1 key).resolve_left hd
  have r2 : (x₁ - e) * (ℓ ^ 2 + ℓ - x₁ - e - e) = 3 * e ^ 2 + a₄ + e / 2 := by
    linear_combination k'
  refine ⟨r2, by ring, ?_⟩
  linear_combination (-(2 * ℓ + 1) ^ 2) * r2

section Torsion

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K} {s : Kˣ} (hs : s ^ 2 = t.q)

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
theorem norm_s_pos_lt : 0 < ‖(s : K)‖ ∧ ‖(s : K)‖ < 1 :=
  ⟨norm_pos_iff.2 s.ne_zero, norm_sqrt_lt_one hs⟩

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
/-- `s²` is off the orbit `s^{4ℤ}`. -/
theorem offOrbit_tq2_sq : OffOrbit (tq2 hs) (s ^ 2) := by
  intro n h
  have h' := congrArg norm h
  rw [norm_mul, norm_one, val_tq2_q, norm_zpow, norm_pow, Units.val_pow_eq_pow_val,
    norm_pow] at h'
  have e1 : ‖(s : K)‖ ^ (4 * n + 2) = (‖(s : K)‖ ^ 4) ^ n * ‖(s : K)‖ ^ 2 := by
    rw [zpow_add₀ (norm_pos_iff.2 s.ne_zero).ne', zpow_mul, zpow_ofNat, zpow_ofNat]
  rw [← e1] at h'
  have := (zpow_eq_one_iff_right₀ (norm_nonneg _) (norm_sqrt_lt_one hs).ne).1 h'
  omega

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
theorem sq_inv_eq : (s ^ 2)⁻¹ = (tq2 hs).q ^ (-1 : ℤ) * s ^ 2 := by
  rw [sqrtPow_q]; group

omit [CharZero K] in
include hs in
/-- **`T = P(q)` is `2`-torsion on `E_{q²}`**: `2Y(s²) + X(s²) = 0`. -/
theorem two_mul_yT_add_xT : 2 * (tq2 hs).Y (s ^ 2) + (tq2 hs).X (s ^ 2) = 0 := by
  have hY := (tq2 hs).Y_inv (offOrbit_tq2_sq hs)
  rw [sq_inv_eq hs, Y_zpow_mul] at hY
  linear_combination hY

omit [CharZero K] in
/-- The Weierstrass equation of a Tate point, in Tate form. -/
theorem tate_eq_of (h12 : (12 : K) ≠ 0) {T : TateParameter K} {w : Kˣ} (hw : OffOrbit T w) :
    T.Y w ^ 2 + T.X w * T.Y w = T.X w ^ 3 + T.a₄ * T.X w + T.a₆ := by
  have h := (equation_iff _ _).mp (tateEquation h12 hw)
  simp only [tateCurve_a₁, tateCurve_a₂, tateCurve_a₃, tateCurve_a₄, tateCurve_a₆] at h
  linear_combination h

include hs in
/-- **The relations of the `ℙ⁴`-model on Tate values** (translation by `T = P(q)` on `E_{q²}`):
for `v`, `v·s²` off the orbit and `X(v) ≠ x_T`. -/
theorem tate_addT_rels (h12 : (12 : K) ≠ 0) (h2 : ‖(2 : K)‖ = 1) {v : Kˣ}
    (hv : OffOrbit (tq2 hs) v) (hvs : OffOrbit (tq2 hs) (v * s ^ 2))
    (hx : (tq2 hs).X v ≠ (tq2 hs).X (s ^ 2)) :
    ((tq2 hs).X v - (tq2 hs).X (s ^ 2)) * ((tq2 hs).X (v * s ^ 2) - (tq2 hs).X (s ^ 2)) =
        3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2 ∧
    (2 * (tq2 hs).Y (v * s ^ 2) + (tq2 hs).X (v * s ^ 2)) *
        ((tq2 hs).X v - (tq2 hs).X (s ^ 2)) +
      (2 * (tq2 hs).Y v + (tq2 hs).X v) *
        ((tq2 hs).X (v * s ^ 2) - (tq2 hs).X (s ^ 2)) = 0 ∧
    (2 * (tq2 hs).Y v + (tq2 hs).X v) * (2 * (tq2 hs).Y (v * s ^ 2) + (tq2 hs).X (v * s ^ 2)) +
      (3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2) *
        (4 * ((tq2 hs).X v + (tq2 hs).X (v * s ^ 2)) + 4 * (tq2 hs).X (s ^ 2) + 1) = 0 := by
  have hd : (tq2 hs).X v - (tq2 hs).X (s ^ 2) ≠ 0 := sub_ne_zero.2 hx
  obtain ⟨eX, eY⟩ := tate_mul_coords h12 h2 hv (offOrbit_tq2_sq hs) hvs hx
  have hyT : (tq2 hs).Y (s ^ 2) = -(tq2 hs).X (s ^ 2) / 2 := by
    linear_combination (1 / 2 : K) * two_mul_yT_add_xT hs
  have ET := tate_eq_of h12 (offOrbit_tq2_sq hs)
  rw [hyT] at ET
  refine addT_rels hd (tate_eq_of h12 hv) ET
    (ℓ := ((tq2 hs).Y v - (tq2 hs).Y (s ^ 2)) / ((tq2 hs).X v - (tq2 hs).X (s ^ 2)))
    ?_ ?_ ?_
  · rw [div_mul_cancel₀ _ hd, hyT]; ring
  · rw [eX]; simp only [addX, tateCurve_a₁, tateCurve_a₂]; ring
  · rw [eY, eX]; simp only [addY, negY, negAddY, tateCurve_a₁, tateCurve_a₃]; ring

end Torsion

/-! ### Norms of the coefficients -/

section Norms

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K} {s : Kˣ} (hs : s ^ 2 = t.q)

omit [CompleteSpace K] in
theorem norm_eq_of_norm_sub_lt {a b : K} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by
  have e : a = b + (a - b) := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

include hs in
/-- `‖x_T − 2q‖ ≤ ‖s‖⁴`. -/
theorem norm_xT_sub_le :
    ‖(tq2 hs).X (s ^ 2) - 2 * (t.q : K)‖ ≤ ‖(s : K)‖ ^ 4 := by
  have hq : ‖(t.q : K)‖ = ‖(s : K)‖ ^ 2 := by rw [val_q_eq hs, norm_pow]
  have hq2 : ‖((tq2 hs).q : K)‖ = ‖(s : K)‖ ^ 4 := by rw [val_tq2_q, norm_pow]
  have h1 := t.norm_eisenstein_sub_q_le 1
  have h2 := (tq2 hs).norm_eisenstein_le 1
  rw [xT_eq hs, show 2 * t.eisenstein 1 - 4 * (tq2 hs).eisenstein 1 - 2 * (t.q : K) =
    2 * (t.eisenstein 1 - t.q) + (-4) * (tq2 hs).eisenstein 1 by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖(2 : K)‖ * ‖t.eisenstein 1 - t.q‖ ≤ 1 * (‖(s : K)‖ ^ 2) ^ 2 :=
          mul_le_mul (IsUltrametricDist.norm_natCast_le_one K 2 |>.trans_eq' (by norm_cast))
            (h1.trans_eq (by rw [hq])) (norm_nonneg _) zero_le_one
      _ = _ := by ring
  · rw [norm_mul]
    calc ‖(-4 : K)‖ * ‖(tq2 hs).eisenstein 1‖ ≤ 1 * ‖(s : K)‖ ^ 4 :=
          mul_le_mul (by
              rw [norm_neg]
              exact IsUltrametricDist.norm_natCast_le_one K 4 |>.trans_eq' (by norm_cast))
            (h2.trans_eq hq2) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

include hs in
/-- **`‖x_T‖ = ‖q‖ = ‖s‖²`** (`‖2‖ = 1`). -/
theorem norm_xT (h2 : ‖(2 : K)‖ = 1) : ‖(tq2 hs).X (s ^ 2)‖ = ‖(s : K)‖ ^ 2 := by
  obtain ⟨hs0, hs1⟩ := norm_s_pos_lt hs
  have h2q : ‖2 * (t.q : K)‖ = ‖(s : K)‖ ^ 2 := by rw [norm_mul, h2, one_mul, val_q_eq hs, norm_pow]
  rw [← h2q]
  refine norm_eq_of_norm_sub_lt ((norm_xT_sub_le hs).trans_lt ?_)
  rw [h2q]
  calc ‖(s : K)‖ ^ 4 = ‖(s : K)‖ ^ 2 * ‖(s : K)‖ ^ 2 := by ring
    _ < 1 * ‖(s : K)‖ ^ 2 := by gcongr; nlinarith
    _ = _ := one_mul _

end Norms

/-! ### The isogeny `E_q → E_{q²}`, `U ↦ U²`, for the `y`-coordinate (weight `4`) -/

section Isogeny

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem isogenyMult_one {t T : TateParameter K} (ht : (t.q : K) = (T.q : K) ^ 2) :
    (T.q ^ (0 : ℤ))⁻¹ * ((t.q * (-1))⁻¹ ^ 4) ^ 1 * (t.q ^ (4 * Nat.choose 1 2))⁻¹ =
      multθ T ^ (4 * 1 * 2) := by
  rw [zpow_zero, show Nat.choose 1 2 = 0 from rfl, mul_zero, pow_zero, inv_one, one_mul,
    mul_one, pow_one]
  ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, multθ]
  rw [ht, inv_pow, inv_pow]
  congr 1
  ring

/-- **`Y_{t}(v²)` is a rational function of `X_T(v)`, `Y_T(v)`** for `T.q² = t.q` (the
isogeny `v ↦ v²`, `E_T → E_t`; weight-`4` family `Y·θ⁴`, so no parity condition). -/
theorem exists_poly_isogenyY_one {t T : TateParameter K} (hlat : T.q ^ 2 = t.q ^ 1)
    (h12 : (12 : K) ≠ 0) :
    ∃ P₁ Q₁ P₂ Q₂ : K[X], ∀ v : Kˣ, OffOrbit T v → t.theta (-(v ^ 2)) ≠ 0 →
      P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v) ≠ 0 ∧
      t.Y (v ^ 2) = (P₁.eval (T.X v) + T.Y v * Q₁.eval (T.X v)) /
        (P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v)) := by
  have ht : (t.q : K) = (T.q : K) ^ 2 := by
    have := congrArg (fun u : Kˣ => (u : K)) hlat
    simp only [Units.val_pow_eq_pow_val, pow_one] at this
    exact this.symm
  have hm := isogenyMult_one ht
  have h₁ := (isWeightFamily_YThetaCube t).conv (isWeightFamily_thetaBlock (t := t) (-1))
  rw [← pow_succ] at h₁
  have h₁' := weightFamily_of_eq t h₁ (show 3 + 1 = 4 by rfl)
  have h₂ := isWeightFamily_cpow t (isWeightFamily_thetaBlock (t := t) (-1)) 4
  rw [one_mul] at h₂
  have h₂' := weightFamily_of_eq t h₂ (show 1 * 4 = 4 by rfl)
  have g₁ := isWeightFamily_pullIter (m := 2) two_pos hlat h₁' 0
  have g₂ := isWeightFamily_pullIter (m := 2) two_pos hlat h₂' 0
  rw [hm] at g₁ g₂
  obtain ⟨P₁, Q₁, e₁⟩ := exists_poly_of_isWeightFamily T h12 (by norm_num) g₁
  obtain ⟨P₂, Q₂, e₂⟩ := exists_poly_of_isWeightFamily T h12 (by norm_num) g₂
  refine ⟨P₁, Q₁, P₂, Q₂, fun v hv hθ => ?_⟩
  have f₁ := e₁ v hv
  have f₂ := e₂ v hv
  rw [(hasSum_pullCoef h₁' two_pos 0 v).tsum_eq,
    ((isWeightFamily_YThetaCube t).conv_hasSum (isWeightFamily_thetaBlock (t := t) (-1))
      (v ^ 2)).tsum_eq,
    (t.hasSum_YThetaCubeCoeff (offOrbit_of_theta_ne_zero hθ)).tsum_eq, tsum_thetaBlock,
    neg_one_mul, neg_zero, zpow_zero, one_mul] at f₁
  rw [tsum_pull_theta two_pos 4 v, neg_zero, zpow_zero, one_mul] at f₂
  have hθT : T.theta (-v) ^ (4 * 1 * 2) ≠ 0 := pow_ne_zero _ (theta_neg_ne_zero T hv)
  have hden : P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at f₂
    exact pow_ne_zero _ hθ f₂
  refine ⟨hden, ?_⟩
  rw [eq_div_iff hden]
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 4 hθ) hθT)
  linear_combination
    (T.theta (-v) ^ (4 * 1 * 2) * (P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v))) * f₁ -
    ((P₁.eval (T.X v) + T.Y v * Q₁.eval (T.X v)) * T.theta (-v) ^ (4 * 1 * 2)) * f₂

end Isogeny

/-! ### Translations of `K(E_T)` -/

section Trans

open WeierstrassCurve.Affine.CoordinateRing

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

theorem transT_eq_translateAut (h12 : (12 : K) ≠ 0) (T : TateParameter K)
    [T.tateCurve.IsElliptic]
    (hmem : ∀ v : Kˣ, (∀ n : ℤ, (T.q : K) ^ n * (v : K) ≠ 1) →
      T.tateCurve.toAffine.Equation (T.X v) (T.Y v))
    (tame : TameResidueChar K) {w : Kˣ} (hw : OffOrbit T w) (g : TateField T) :
    translateAut (T.tatePoint hmem tame w) g = transT h12 hw g := by
  classical
  have hnm : w ∉ T.qpowers := fun h => (T.mem_qpowers_iff _).mp h |>.elim fun n hn => hw n hn
  rw [T.tatePoint_of_notMem hmem tame hnm, translateAut_apply_some]
  rfl

/-- Translations commute. -/
theorem transT_comm (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) (T : TateParameter K)
    [T.tateCurve.IsElliptic] {w w' : Kˣ} (hw : OffOrbit T w) (hw' : OffOrbit T w')
    (g : TateField T) :
    transT h12 hw (transT h12 hw' g) = transT h12 hw' (transT h12 hw g) := by
  classical
  have hmem : ∀ v : Kˣ, (∀ n : ℤ, (T.q : K) ^ n * (v : K) ≠ 1) →
      T.tateCurve.toAffine.Equation (T.X v) (T.Y v) := fun v hv => T.tatePoint_mem' h12 hv
  have tame : TameResidueChar K := ⟨h2, h12⟩
  simp only [← transT_eq_translateAut h12 T hmem tame hw,
    ← transT_eq_translateAut h12 T hmem tame hw']
  rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← translateAut_add, ← translateAut_add,
    add_comm]

/-- Translation by `w` with `w² = q` is an involution. -/
theorem transT_transT_of_sq (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) (T : TateParameter K)
    [T.tateCurve.IsElliptic] {w : Kˣ} (hw : OffOrbit T w) (hsq : (w : K) ^ 2 = T.q)
    (g : TateField T) : transT h12 hw (transT h12 hw g) = g := by
  classical
  have hmem : ∀ v : Kˣ, (∀ n : ℤ, (T.q : K) ^ n * (v : K) ≠ 1) →
      T.tateCurve.toAffine.Equation (T.X v) (T.Y v) := fun v hv => T.tatePoint_mem' h12 hv
  have tame : TameResidueChar K := ⟨h2, h12⟩
  have hww : w * w ∈ T.qpowers := (T.mem_qpowers_iff _).2 ⟨-1, by
    rw [Units.val_mul, ← sq, hsq, zpow_neg_one, inv_mul_cancel₀ T.q.ne_zero]⟩
  have hPP : T.tatePoint hmem tame w + T.tatePoint hmem tame w = 0 := by
    rw [← T.tatePoint_mul, T.tatePoint_of_mem hmem tame hww]
  rw [← transT_eq_translateAut h12 T hmem tame hw, ← transT_eq_translateAut h12 T hmem tame hw,
    ← AlgEquiv.mul_apply, ← translateAut_add, hPP, translateAut_zero, AlgEquiv.one_apply]

/-- Equal `X`-coordinates: `u ≡ w^{±1}` modulo `qᶻ`. -/
theorem zpow_of_X_eq (h12 : (12 : K) ≠ 0) (h2 : ‖(2 : K)‖ = 1) {T : TateParameter K}
    {u w : Kˣ} (hu : OffOrbit T u) (hw : OffOrbit T w) (hX : T.X u = T.X w) :
    ∃ m : ℤ, (u : K) = (T.q : K) ^ m * w ∨ (u : K) = (T.q : K) ^ m * (w : K)⁻¹ := by
  have E1 := (equation_iff _ _).mp (tateEquation h12 hu)
  have E2 := (equation_iff _ _).mp (tateEquation h12 hw)
  simp only [tateCurve_a₁, tateCurve_a₂, tateCurve_a₃] at E1 E2
  rw [hX] at E1
  have hfac : (T.Y u - T.Y w) * (T.Y u + T.Y w + T.X w) = 0 := by
    linear_combination E1 - E2
  rcases mul_eq_zero.mp hfac with h | h
  · obtain ⟨m, hm⟩ := exists_zpow_of_coords_eq h12 h2 hu hw hX (sub_eq_zero.mp h)
    exact ⟨m, Or.inl hm⟩
  · have hwi := offOrbit_inv T hw
    obtain ⟨m, hm⟩ := exists_zpow_of_coords_eq h12 h2 hu hwi (by rw [T.X_inv hw, hX])
      (by rw [T.Y_inv hw]; linear_combination h)
    exact ⟨m, Or.inr (by rw [hm, Units.val_inv_eq_inv_val])⟩

end Trans

/-! ### Good points: `U` with `U² ∉ qᶻ` -/

section Good

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K} {s : Kˣ} (hs : s ^ 2 = t.q)

/-- The Tate parameter `s²` of `E_Q`, `Q = s^{N_0} = q` (as in `levelQN 0`). -/
abbrev tq1 : TateParameter K := sqrtPow hs (2 * (0 + 1)) (Nat.mul_pos two_pos (0 : ℕ).succ_pos)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem val_tq1_q : ((tq1 hs).q : K) = (s : K) ^ 2 := by
  rw [sqrtPow_q, Units.val_pow_eq_pow_val]; norm_num

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem tq1_q : (tq1 hs).q = s ^ 2 := by rw [sqrtPow_q]; norm_num

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem offOrbit_tq2_of {v : Kˣ} (hv : OffOrbit t v) : OffOrbit (tq2 hs) v := by
  intro n h
  apply hv (2 * n)
  rw [val_q_eq hs, zpow_even, ← val_tq2_q hs]
  exact h

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem offOrbit_tq2_mul_of {v : Kˣ} (hv : OffOrbit t v) : OffOrbit (tq2 hs) (v * s ^ 2) := by
  intro n h
  apply hv (2 * n + 1)
  rw [val_q_eq hs, zpow_odd s.ne_zero, ← val_tq2_q hs]
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using h

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem zpow_two_mul_add_one {a : K} (ha : a ≠ 0) (m : ℤ) :
    a ^ (-(2 * m + 1)) * ((a ^ 2) ^ m * a) = 1 := by
  have e : (a ^ 2) ^ m * a = a ^ (2 * m + 1) := by rw [zpow_add_one₀ ha, zpow_mul, zpow_ofNat]
  rw [e, ← zpow_add₀ ha, neg_add_cancel, zpow_zero]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem zpow_two_mul_sub_one {a : K} (ha : a ≠ 0) (m : ℤ) :
    a ^ (-(2 * m - 1)) * ((a ^ 2) ^ m * a⁻¹) = 1 := by
  have e : (a ^ 2) ^ m * a⁻¹ = a ^ (2 * m - 1) := by rw [zpow_sub_one₀ ha, zpow_mul, zpow_ofNat]
  rw [e, ← zpow_add₀ ha, neg_add_cancel, zpow_zero]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem sq_zpow_mul (a b : K) (m : ℤ) : (a ^ m * b) ^ 2 = (a ^ 2) ^ m * b ^ 2 := by
  rw [mul_pow, sq (a ^ m), ← mul_zpow, ← sq]

include hs in
theorem xT_ne_of (h12 : (12 : K) ≠ 0) (h2 : ‖(2 : K)‖ = 1) {v : Kˣ} (hv : OffOrbit t v) :
    (tq2 hs).X v ≠ (tq2 hs).X (s ^ 2) := by
  intro hX
  have hs2 : ((s ^ 2 : Kˣ) : K) = (s : K) ^ 2 := Units.val_pow_eq_pow_val _ _
  have ha : (s : K) ^ 2 ≠ 0 := pow_ne_zero _ s.ne_zero
  have h4 : ((tq2 hs).q : K) = ((s : K) ^ 2) ^ 2 := by rw [val_tq2_q, ← pow_mul]
  obtain ⟨m, hm | hm⟩ := zpow_of_X_eq h12 h2 (offOrbit_tq2_of hs hv) (offOrbit_tq2_sq hs) hX
  · apply hv (-(2 * m + 1))
    rw [hm, h4, hs2, val_q_eq hs]
    exact zpow_two_mul_add_one ha m
  · apply hv (-(2 * m - 1))
    rw [hm, h4, hs2, val_q_eq hs]
    exact zpow_two_mul_sub_one ha m

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem offOrbit_tq1_s : OffOrbit (tq1 hs) s := by
  intro n h
  have h' := congrArg norm h
  rw [norm_mul, norm_one, val_tq1_q, norm_zpow, norm_pow] at h'
  have e1 : ‖(s : K)‖ ^ (2 * n + 1) = (‖(s : K)‖ ^ 2) ^ n * ‖(s : K)‖ := by
    rw [zpow_add_one₀ (norm_pos_iff.2 s.ne_zero).ne', zpow_mul, zpow_ofNat]
  rw [← e1] at h'
  have := (zpow_eq_one_iff_right₀ (norm_nonneg _) (norm_sqrt_lt_one hs).ne).1 h'
  omega

include hs in
theorem X_ne_X_s (h12 : (12 : K) ≠ 0) (h2 : ‖(2 : K)‖ = 1) {U : Kˣ} (hU : OffOrbit (tq1 hs) U)
    (hU2 : OffOrbit t (U ^ 2)) : (tq1 hs).X U ≠ (tq1 hs).X s := by
  intro hX
  have ha : (s : K) ≠ 0 := s.ne_zero
  obtain ⟨m, hm | hm⟩ := zpow_of_X_eq h12 h2 hU (offOrbit_tq1_s hs) hX
  · apply hU2 (-(2 * m + 1))
    rw [Units.val_pow_eq_pow_val, hm, val_tq1_q, sq_zpow_mul, val_q_eq hs]
    exact zpow_two_mul_add_one (pow_ne_zero 2 ha) m
  · apply hU2 (-(2 * m - 1))
    rw [Units.val_pow_eq_pow_val, hm, val_tq1_q, sq_zpow_mul, inv_pow, val_q_eq hs]
    exact zpow_two_mul_sub_one (pow_ne_zero 2 ha) m

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem offOrbit_mul_s {U : Kˣ} (hx : (tq1 hs).X U ≠ (tq1 hs).X s) :
    OffOrbit (tq1 hs) (U * s) := by
  intro n hn
  apply hx
  have e : U = (tq1 hs).q ^ (-n) * s⁻¹ := by
    apply Units.ext
    push_cast at hn ⊢
    have hw0 : (s : K) ≠ 0 := s.ne_zero
    have hT0 : ((tq1 hs).q : K) ≠ 0 := (tq1 hs).q.ne_zero
    rw [zpow_neg]
    field_simp
    linear_combination hn
  rw [e, X_zpow_mul, (tq1 hs).X_inv (offOrbit_tq1_s hs)]

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem offOrbit_mul_s_sq {U : Kˣ} (hU2 : OffOrbit t (U ^ 2)) : OffOrbit t ((U * s) ^ 2) := by
  intro n hn
  apply hU2 (n + 1)
  rw [zpow_add_one₀ t.q.ne_zero, val_q_eq hs]
  rw [mul_pow, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, val_q_eq hs]
    at hn
  rw [Units.val_pow_eq_pow_val]
  linear_combination hn

end Good

/-! ### The elements `x₁, y₁, x₂, y₂ ∈ K(E_q)` (coordinate `U`, `E_q/⟨-1⟩ ≅ E_{q²}`) -/

section FieldElts

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K} (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem sq_sq_eq_tq2 : (s ^ 2) ^ 2 = (tq2 hs).q := by rw [sqrtPow_q, ← pow_mul]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem tq1_q_eq : (tq1 hs).q = (s ^ 2) ^ 1 := by rw [tq1_q, pow_one]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem tq_lat : (tq1 hs).q ^ 2 = (tq2 hs).q ^ 1 := by
  rw [tq1_q, sqrtPow_q, ← pow_mul, pow_one]

omit [CharZero K] in
/-- **The identity principle on good points** `U` (`U² ∉ qᶻ`) of `E_Q`, `Q = q`. -/
theorem eq_of_good {a b : TateField (tq1 hs)} {A : Kˣ → K}
    (ha : ∀ (U : Kˣ) (hU : OffOrbit (tq1 hs) U), OffOrbit t (U ^ 2) →
      HasTateValue (tq1 hs) h12 a hU (A U))
    (hb : ∀ (U : Kˣ) (hU : OffOrbit (tq1 hs) U), OffOrbit t (U ^ 2) →
      HasTateValue (tq1 hs) h12 b hU (A U)) : a = b := by
  have good : ∀ (U : Kˣ) (hU : OffOrbit (tq1 hs) U),
      evalTate (tq1 hs) h12 hU (mkT (tq1 hs) (C (badPoly (tq1 hs) s 2))) ≠ 0 →
      OffOrbit t (U ^ 2) := by
    intro U hU h0
    by_contra h
    exact h0 (by rw [evalTate_mk_C]; exact badPoly_eval_eq_zero hs two_pos (tq1_q hs) h)
  exact eq_of_hasTateValue (h12 := h12) (mkT_C_ne_zero h12 badPoly_ne_zero) (G := A)
    (fun U hU h0 => ha U hU (good U hU h0)) (fun U hU h0 => hb U hU (good U hU h0))

omit [CharZero K] in
/-- **The four functions on `E_Q`** (`Q = q`, coordinate `U`): `x₁, y₁` with values
`X_{q²}(U²), Y_{q²}(U²)` and `x₂ = t_s x₁`, `y₂ = t_s y₁` with values
`X_{q²}(U²s²), Y_{q²}(U²s²)`; all fixed by `t_{-1}`, and swapped by `t_s`. -/
theorem exists_fourGon_tateField [(tq1 hs).tateCurve.IsElliptic] :
    ∃ f₁ g₁ f₂ g₂ : TateField (tq1 hs),
      (transT h12 (offOrbit_neg_one (tq1 hs) h2) f₁ = f₁ ∧
        transT h12 (offOrbit_neg_one (tq1 hs) h2) g₁ = g₁ ∧
        transT h12 (offOrbit_neg_one (tq1 hs) h2) f₂ = f₂ ∧
        transT h12 (offOrbit_neg_one (tq1 hs) h2) g₂ = g₂) ∧
      (transT h12 (offOrbit_tq1_s hs) f₁ = f₂ ∧ transT h12 (offOrbit_tq1_s hs) g₁ = g₂ ∧
        transT h12 (offOrbit_tq1_s hs) f₂ = f₁ ∧ transT h12 (offOrbit_tq1_s hs) g₂ = g₁) ∧
      ∀ (U : Kˣ) (hU : OffOrbit (tq1 hs) U), OffOrbit t (U ^ 2) →
        HasTateValue (tq1 hs) h12 f₁ hU ((tq2 hs).X (U ^ 2)) ∧
        HasTateValue (tq1 hs) h12 g₁ hU ((tq2 hs).Y (U ^ 2)) ∧
        HasTateValue (tq1 hs) h12 f₂ hU ((tq2 hs).X (U ^ 2 * s ^ 2)) ∧
        HasTateValue (tq1 hs) h12 g₂ hU ((tq2 hs).Y (U ^ 2 * s ^ 2)) := by
  obtain ⟨P₁, Q₁, P₂, Q₂, hR⟩ :=
    exists_poly_isogenyX (tq2 hs) (sq_sq_eq_tq2 hs) one_pos (tq1 hs) (tq1_q_eq hs) h12
  obtain ⟨C₁, E₁, C₂, E₂, hRy⟩ := exists_poly_isogenyY_one (tq_lat hs) h12
  have hk : ∃ k : ℤ, (((-1 : Kˣ) : K)) ^ 2 = ((tq2 hs).q : K) ^ k := ⟨0, by simp⟩
  have hρf := transT_R_eq (h12 := h12) (sq_sq_eq_tq2 hs) one_pos (tq1_q_eq hs) h2 hR
    (offOrbit_neg_one (tq1 hs) h2) hk
  have hρg := transT_Ry_eq (tq1_q_eq hs) one_pos h12 (sq_sq_eq_tq2 hs) hRy h2
    (offOrbit_neg_one (tq1 hs) h2) hk
  have hsq : ((s : Kˣ) : K) ^ 2 = ((tq1 hs).q : K) := by rw [val_tq1_q]
  set f₁ := algebraMap _ (TateField (tq1 hs)) (polyXY (tq1 hs) P₁ Q₁) /
    algebraMap _ (TateField (tq1 hs)) (polyXY (tq1 hs) P₂ Q₂) with hf₁
  set g₁ := algebraMap _ (TateField (tq1 hs)) (polyXY (tq1 hs) C₁ E₁) /
    algebraMap _ (TateField (tq1 hs)) (polyXY (tq1 hs) C₂ E₂) with hg₁
  refine ⟨f₁, g₁, transT h12 (offOrbit_tq1_s hs) f₁, transT h12 (offOrbit_tq1_s hs) g₁,
    ⟨hρf, hρg, ?_, ?_⟩, ⟨rfl, rfl, transT_transT_of_sq h2 h12 _ _ hsq f₁,
      transT_transT_of_sq h2 h12 _ _ hsq g₁⟩, fun U hU hU2 => ?_⟩
  · rw [transT_comm h2 h12 (tq1 hs), hρf]
  · rw [transT_comm h2 h12 (tq1 hs), hρg]
  have hx := X_ne_X_s hs h12 h2 hU hU2
  have hUs := offOrbit_mul_s hs hx
  have hUs2 := offOrbit_mul_s_sq hs hU2
  have e : (U * s) ^ 2 = U ^ 2 * s ^ 2 := mul_pow U s 2
  refine ⟨hasTateValue_R (h12 := h12) hR hU (offOrbit_tq2_of hs hU2),
    hasTateValue_Ry h12 hRy hU (offOrbit_tq2_of hs hU2), ?_, ?_⟩
  · exact hasTateValue_trans h2 hU (offOrbit_tq1_s hs) hUs hx _ _
      ((hasTateValue_R (h12 := h12) hR hUs (offOrbit_tq2_of hs hUs2)).congr (by rw [e]))
  · exact hasTateValue_trans h2 hU (offOrbit_tq1_s hs) hUs hx _ _
      ((hasTateValue_Ry h12 hRy hUs (offOrbit_tq2_of hs hUs2)).congr (by rw [e]))

include h2 in
/-- **The relations of the `ℙ⁴`-model in `K(E_Q)`** (identity principle from
`tate_eq_of`, `tate_addT_rels`), for any four functions with the values of
`exists_fourGon_tateField`; `e = x_T = X_{q²}(s²)`, `C_T = 3e² + a₄' + e/2`. -/
theorem fourGon_rels {f₁ g₁ f₂ g₂ : TateField (tq1 hs)}
    (hval : ∀ (U : Kˣ) (hU : OffOrbit (tq1 hs) U), OffOrbit t (U ^ 2) →
        HasTateValue (tq1 hs) h12 f₁ hU ((tq2 hs).X (U ^ 2)) ∧
        HasTateValue (tq1 hs) h12 g₁ hU ((tq2 hs).Y (U ^ 2)) ∧
        HasTateValue (tq1 hs) h12 f₂ hU ((tq2 hs).X (U ^ 2 * s ^ 2)) ∧
        HasTateValue (tq1 hs) h12 g₂ hU ((tq2 hs).Y (U ^ 2 * s ^ 2))) :
    g₁ ^ 2 + f₁ * g₁ = f₁ ^ 3 + algebraMap K (TateField (tq1 hs)) (tq2 hs).a₄ * f₁ +
        algebraMap K (TateField (tq1 hs)) (tq2 hs).a₆ ∧
    g₂ ^ 2 + f₂ * g₂ = f₂ ^ 3 + algebraMap K (TateField (tq1 hs)) (tq2 hs).a₄ * f₂ +
        algebraMap K (TateField (tq1 hs)) (tq2 hs).a₆ ∧
    (f₁ - algebraMap K (TateField (tq1 hs)) ((tq2 hs).X (s ^ 2))) *
        (f₂ - algebraMap K (TateField (tq1 hs)) ((tq2 hs).X (s ^ 2))) =
      algebraMap K (TateField (tq1 hs))
        (3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2) ∧
    (2 * g₂ + f₂) * (f₁ - algebraMap K (TateField (tq1 hs)) ((tq2 hs).X (s ^ 2))) +
        (2 * g₁ + f₁) * (f₂ - algebraMap K (TateField (tq1 hs)) ((tq2 hs).X (s ^ 2))) = 0 ∧
    (2 * g₁ + f₁) * (2 * g₂ + f₂) + algebraMap K (TateField (tq1 hs))
        (3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2) *
      (4 * (f₁ + f₂) + algebraMap K (TateField (tq1 hs)) (4 * (tq2 hs).X (s ^ 2) + 1)) = 0 := by
  have H : ∀ (U : Kˣ), OffOrbit t (U ^ 2) → _ := fun U hU2 =>
    tate_addT_rels hs h12 h2 (offOrbit_tq2_of hs hU2) (offOrbit_tq2_mul_of hs hU2)
      (xT_ne_of hs h12 h2 hU2)
  have two : ∀ (U : Kˣ) (hU : OffOrbit (tq1 hs) U),
      HasTateValue (tq1 hs) h12 (2 : TateField (tq1 hs)) hU 2 := fun U hU => by
    have e : algebraMap K (TateField (tq1 hs)) 2 = 2 := map_ofNat _ 2
    exact e ▸ HasTateValue.const (h12 := h12) hU (2 : K)
  have four : ∀ (U : Kˣ) (hU : OffOrbit (tq1 hs) U),
      HasTateValue (tq1 hs) h12 (4 : TateField (tq1 hs)) hU 4 := fun U hU => by
    have e : algebraMap K (TateField (tq1 hs)) 4 = 4 := map_ofNat _ 4
    exact e ▸ HasTateValue.const (h12 := h12) hU (4 : K)
  have zero : ∀ (U : Kˣ) (hU : OffOrbit (tq1 hs) U),
      HasTateValue (tq1 hs) h12 (0 : TateField (tq1 hs)) hU 0 := fun U hU => by
    simpa using HasTateValue.const (h12 := h12) hU (0 : K)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine eq_of_good h12 hs
      (A := fun U => (tq2 hs).Y (U ^ 2) ^ 2 + (tq2 hs).X (U ^ 2) * (tq2 hs).Y (U ^ 2))
      (fun U hU hU2 => ?_) (fun U hU hU2 => ?_)
    · obtain ⟨a, b, -, -⟩ := hval U hU hU2
      exact (b.pow 2).add (a.mul b)
    · obtain ⟨a, b, -, -⟩ := hval U hU hU2
      exact (((a.pow 3).add ((HasTateValue.const hU _).mul a)).add
        (HasTateValue.const hU _)).congr (tate_eq_of h12 (offOrbit_tq2_of hs hU2)).symm
  · refine eq_of_good h12 hs
      (A := fun U => (tq2 hs).Y (U ^ 2 * s ^ 2) ^ 2 +
        (tq2 hs).X (U ^ 2 * s ^ 2) * (tq2 hs).Y (U ^ 2 * s ^ 2))
      (fun U hU hU2 => ?_) (fun U hU hU2 => ?_)
    · obtain ⟨-, -, a, b⟩ := hval U hU hU2
      exact (b.pow 2).add (a.mul b)
    · obtain ⟨-, -, a, b⟩ := hval U hU hU2
      exact (((a.pow 3).add ((HasTateValue.const hU _).mul a)).add
        (HasTateValue.const hU _)).congr (tate_eq_of h12 (offOrbit_tq2_mul_of hs hU2)).symm
  · refine eq_of_good h12 hs (fun U hU hU2 => ?_) (fun U hU hU2 => HasTateValue.const hU _)
    obtain ⟨a, -, c, -⟩ := hval U hU hU2
    exact ((a.sub (HasTateValue.const hU _)).mul (c.sub (HasTateValue.const hU _))).congr
      (H U hU2).1
  · refine eq_of_good h12 hs (fun U hU hU2 => ?_) (fun U hU hU2 => zero U hU)
    obtain ⟨a, b, c, d⟩ := hval U hU hU2
    exact ((((two U hU).mul d).add c).mul (a.sub (HasTateValue.const hU _))).add
      ((((two U hU).mul b).add a).mul (c.sub (HasTateValue.const hU _))) |>.congr (H U hU2).2.1
  · refine eq_of_good h12 hs (fun U hU hU2 => ?_) (fun U hU hU2 => zero U hU)
    obtain ⟨a, b, c, d⟩ := hval U hU hU2
    refine ((((two U hU).mul b).add a).mul (((two U hU).mul d).add c)).add
      ((HasTateValue.const hU _).mul (((four U hU).mul (a.add c)).add
        (HasTateValue.const hU _))) |>.congr ?_
    linear_combination (H U hU2).2.2

end FieldElts

/-! ### Generic algebra: integrality of roots of monic quadratics, units of `O` -/

section Generic

theorem isIntegral_of_sq_eq {R F : Type*} [CommRing R] [Field F] [Algebra R F] {x a b h : F}
    (hh : IsIntegral R h) (h2 : h * 2 = 1) (ha : IsIntegral R a) (hb : IsIntegral R b)
    (hx : x ^ 2 = a * x + b) : IsIntegral R x := by
  have hw : IsIntegral R (x + x - a) := by
    refine IsIntegral.of_pow two_pos ?_
    rw [show (x + x - a) ^ 2 = b + b + b + b + a * a by linear_combination 4 * hx]
    exact (((hb.add hb).add hb).add hb).add (ha.mul ha)
  rw [show x = h * (x + x - a + a) by linear_combination (-x) * h2]
  exact hh.mul (hw.add ha)

variable {K : Type u} [NormedField K] (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)

include hO in
theorem mem_maximalIdeal_of_norm_lt {x : O} (hx : ‖(x : K)‖ < 1) :
    x ∈ IsLocalRing.maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, rfl⟩
  have h1 : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := u.inv_mul
  have h2 := congrArg (fun z : O => ‖(z : K)‖) h1
  simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h2
  have h3 : ‖(((u⁻¹ : Oˣ) : O) : K)‖ ≤ 1 := (hO _).1 ((u⁻¹ : Oˣ) : O).2
  nlinarith [norm_nonneg (((u⁻¹ : Oˣ) : O) : K), norm_nonneg ((u : O) : K)]

include hO in
theorem isUnit_of_norm_eq_one {x : O} (hx : ‖(x : K)‖ = 1) : IsUnit x := by
  have hx0 : (x : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at hx; exact zero_ne_one hx
  exact ⟨Units.mkOfMulEqOne x ⟨(x : K)⁻¹, (hO _).2 (by rw [norm_inv, hx, inv_one])⟩
    (Subtype.ext (mul_inv_cancel₀ hx0)), rfl⟩

end Generic

/-! ### Norms of the coefficients of the model -/

section Consts

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K} {s : Kˣ} (hs : s ^ 2 = t.q)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem norm_div_s_le {a : K} {n k : ℕ} (h : ‖a‖ ≤ ‖(s : K)‖ ^ (n + k)) :
    ‖a / (s : K) ^ n‖ ≤ ‖(s : K)‖ ^ k := by
  have hs0 : 0 < ‖(s : K)‖ ^ n := pow_pos (norm_pos_iff.2 s.ne_zero) n
  rw [norm_div, norm_pow, div_le_iff₀ hs0, ← pow_add, add_comm]
  exact h

theorem norm_a₄_tq2_le : ‖(tq2 hs).a₄‖ ≤ ‖(s : K)‖ ^ (2 + 2) := by
  have := (tq2 hs).norm_a₄_le
  rwa [val_tq2_q, norm_pow] at this

theorem norm_a₆_tq2_le (h12 : (12 : K) ≠ 0) : ‖(tq2 hs).a₆‖ ≤ ‖(s : K)‖ ^ (2 + 2) := by
  have := norm_a₆_le (t := tq2 hs) h12
  rwa [val_tq2_q, norm_pow] at this

include hs in
theorem norm_cY_le :
    ‖t.eisenstein 1 - 2 * (tq2 hs).eisenstein 1‖ ≤ ‖(s : K)‖ ^ (1 + 1) := by
  obtain ⟨hs0, hs1⟩ := norm_s_pos_lt hs
  have h1 := t.norm_eisenstein_le 1
  have h2 := (tq2 hs).norm_eisenstein_le 1
  rw [val_q_eq hs, norm_pow] at h1
  rw [val_tq2_q, norm_pow] at h2
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rw [norm_neg, norm_mul]
  calc ‖(2 : K)‖ * ‖(tq2 hs).eisenstein 1‖ ≤ 1 * ‖(s : K)‖ ^ 4 :=
        mul_le_mul (IsUltrametricDist.norm_natCast_le_one K 2 |>.trans_eq' (by norm_cast))
          h2 (norm_nonneg _) zero_le_one
    _ ≤ ‖(s : K)‖ ^ (1 + 1) := by
        rw [one_mul]; exact pow_le_pow_of_le_one hs0.le hs1.le (by norm_num)

include hs in
/-- `‖C_T‖ = ‖s‖²` for `C_T = 3x_T² + a₄' + x_T/2`. -/
theorem norm_CT (h2 : ‖(2 : K)‖ = 1) :
    ‖3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2‖ = ‖(s : K)‖ ^ 2 := by
  obtain ⟨hs0, hs1⟩ := norm_s_pos_lt hs
  have he := norm_xT hs h2
  have he2 : ‖(tq2 hs).X (s ^ 2) / 2‖ = ‖(s : K)‖ ^ 2 := by rw [norm_div, he, h2, div_one]
  rw [← he2]
  refine norm_eq_of_norm_sub_lt ?_
  rw [he2, show 3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2 -
    (tq2 hs).X (s ^ 2) / 2 = 3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ by ring]
  have h4 : ‖(s : K)‖ ^ 4 < ‖(s : K)‖ ^ 2 := pow_lt_pow_right_of_lt_one₀ hs0 hs1 (by norm_num)
  refine lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) h4
  · rw [norm_mul, norm_pow, he]
    calc ‖(3 : K)‖ * (‖(s : K)‖ ^ 2) ^ 2 ≤ 1 * (‖(s : K)‖ ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (IsUltrametricDist.norm_natCast_le_one K 3 |>.trans_eq' (by norm_cast))
            (by positivity)
      _ = _ := by ring
  · exact norm_a₄_tq2_le hs

end Consts

/-! ### The Ω-level wrapper: `x₁, y₁, x₂, y₂ ∈ R' = K[E_{q²}]` -/

section Wrapper

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve KummerTheory KummerTheory.Curve CurvesJacobian.Cusp
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

variable (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)

omit [CompleteSpace K] [IsUltrametricDist K] in
instance isElliptic_tq1 : (tq1 hs).tateCurve.IsElliptic :=
  (tq1 hs).tateCurve_isElliptic (by norm_num)

/-- The properties of the four functions `x₁, y₁, x₂, y₂` on `E_Q` (`exists_fourGon_tateField`). -/
def FourGonSpec
    (f : TateField (tq1 hs) × TateField (tq1 hs) × TateField (tq1 hs) × TateField (tq1 hs)) :
    Prop :=
  (transT h12 (offOrbit_neg_one (tq1 hs) h2) f.1 = f.1 ∧
      transT h12 (offOrbit_neg_one (tq1 hs) h2) f.2.1 = f.2.1 ∧
      transT h12 (offOrbit_neg_one (tq1 hs) h2) f.2.2.1 = f.2.2.1 ∧
      transT h12 (offOrbit_neg_one (tq1 hs) h2) f.2.2.2 = f.2.2.2) ∧
    (transT h12 (offOrbit_tq1_s hs) f.1 = f.2.2.1 ∧ transT h12 (offOrbit_tq1_s hs) f.2.1 = f.2.2.2 ∧
      transT h12 (offOrbit_tq1_s hs) f.2.2.1 = f.1 ∧
      transT h12 (offOrbit_tq1_s hs) f.2.2.2 = f.2.1) ∧
    ∀ (U : Kˣ) (hU : OffOrbit (tq1 hs) U), OffOrbit t (U ^ 2) →
      HasTateValue (tq1 hs) h12 f.1 hU ((tq2 hs).X (U ^ 2)) ∧
      HasTateValue (tq1 hs) h12 f.2.1 hU ((tq2 hs).Y (U ^ 2)) ∧
      HasTateValue (tq1 hs) h12 f.2.2.1 hU ((tq2 hs).X (U ^ 2 * s ^ 2)) ∧
      HasTateValue (tq1 hs) h12 f.2.2.2 hU ((tq2 hs).Y (U ^ 2 * s ^ 2))

theorem exists_fourGonSpec : ∃ f, FourGonSpec h2 h12 hs f := by
  obtain ⟨f₁, g₁, f₂, g₂, h⟩ := exists_fourGon_tateField h2 h12 hs
  exact ⟨(f₁, g₁, f₂, g₂), h⟩

/-- The four functions `x₁, y₁, x₂, y₂ ∈ K(E_Q)`. -/
def fgT : TateField (tq1 hs) × TateField (tq1 hs) × TateField (tq1 hs) × TateField (tq1 hs) :=
  (exists_fourGonSpec h2 h12 hs).choose

theorem fgT_spec : FourGonSpec h2 h12 hs (fgT h2 h12 hs) :=
  (exists_fourGonSpec h2 h12 hs).choose_spec

variable [t.tateCurve.IsElliptic]

/-- `ι = φ₄ ∘ pullbackT : K(E_Q) → Ω` (`levelQN 0` is generated by the `ι`-image of the
`t_{-1}`-fixed field). -/
def iotaQ : TateField (tq1 hs) →ₐ[K] Ω :=
  (mulByNEmb t.tateCurve (2 * (2 * (0 + 1)))).comp
    (pullbackT (levelCoords h2 h12 hs 0).1 (levelCoords h2 h12 hs 0).2
      (isTPoint_levelCoords h2 h12 hs 0) (transcendental_levelCoords h2 h12 hs 0))

theorem iotaQ_mem {f : TateField (tq1 hs)}
    (hf : transT h12 (offOrbit_neg_one (tq1 hs) h2) f = f) :
    iotaQ h2 h12 hs f ∈ levelQN h2 h12 hs 0 :=
  IntermediateField.subset_adjoin _ _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩

theorem iotaQ_mem_L {f : TateField (tq1 hs)}
    (hf : transT h12 (offOrbit_neg_one (tq1 hs) h2) f = f) :
    iotaQ h2 h12 hs f ∈ (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
      (isOpen_levelQN h2 h12 hs 0)).L := by
  rw [fieldData_L]
  exact iotaQ_mem h2 h12 hs hf

/-- **Vélu, `x`, in `K(E_q)`**: `pullbackT (x₁ + x₂ − x_T) = [4]^*x`. -/
theorem pullbackT_velu_x :
    pullbackT (levelCoords h2 h12 hs 0).1 (levelCoords h2 h12 hs 0).2
      (isTPoint_levelCoords h2 h12 hs 0) (transcendental_levelCoords h2 h12 hs 0)
      ((fgT h2 h12 hs).1 + (fgT h2 h12 hs).2.2.1 -
        algebraMap K (TateField (tq1 hs)) ((tq2 hs).X (s ^ 2))) =
    algebraMap (coverRingN t.tateCurve (2 * (2 * (0 + 1)))) (TateField t)
      (mulByNHom t.tateCurve (2 * (2 * (0 + 1))) (xE t.tateCurve)) := by
  have hψ0 := psiN_ne_zero_of_neZero t.tateCurve (2 * (2 * (0 + 1)))
  have hc := (levelCoords_spec h2 h12 hs 0).2
  refine eq_of_hasTateValue (h12 := h12) hψ0 (G := fun u => t.X (u ^ (2 * (2 * (0 + 1)))))
    (fun u hu hψ => ?_) (fun u hu hψ => ?_)
  · obtain ⟨hum, -⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * (2 * (0 + 1))) h2 hu hψ
    have hv : OffOrbit (tq1 hs) (u ^ (2 * (0 + 1))) := offOrbit_sqrt_pow hs (tq1 hs) rfl hum
    have e : (u ^ (2 * (0 + 1))) ^ 2 = u ^ (2 * (2 * (0 + 1))) := by
      rw [← pow_mul, mul_comm]
    have hU2 : OffOrbit t ((u ^ (2 * (0 + 1))) ^ 2) := by rw [e]; exact hum
    obtain ⟨a, -, c, -⟩ := (fgT_spec h2 h12 hs).2.2 _ hv hU2
    refine (hasTateValue_pullbackT (isTPoint_levelCoords h2 h12 hs 0)
      (transcendental_levelCoords h2 h12 hs 0) hv (hc u hu hum).1 (hc u hu hum).2
      ((a.add c).sub (HasTateValue.const hv _))).congr ?_
    rw [← e, velu_X hs]
  · obtain ⟨hum, hv⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * (2 * (0 + 1))) h2 hu hψ
    exact (hv (xE t.tateCurve)).congr (by
      rw [show xE t.tateCurve = mkT t (C X) from rfl, evalTate_mk_C, eval_X])

/-- **Vélu, `y`, in `K(E_q)`**: `pullbackT (y₁ + y₂ + c_y) = [4]^*y`. -/
theorem pullbackT_velu_y :
    pullbackT (levelCoords h2 h12 hs 0).1 (levelCoords h2 h12 hs 0).2
      (isTPoint_levelCoords h2 h12 hs 0) (transcendental_levelCoords h2 h12 hs 0)
      ((fgT h2 h12 hs).2.1 + (fgT h2 h12 hs).2.2.2 +
        algebraMap K (TateField (tq1 hs)) (t.eisenstein 1 - 2 * (tq2 hs).eisenstein 1)) =
    algebraMap (coverRingN t.tateCurve (2 * (2 * (0 + 1)))) (TateField t)
      (mulByNHom t.tateCurve (2 * (2 * (0 + 1))) (yE t.tateCurve)) := by
  have hψ0 := psiN_ne_zero_of_neZero t.tateCurve (2 * (2 * (0 + 1)))
  have hc := (levelCoords_spec h2 h12 hs 0).2
  refine eq_of_hasTateValue (h12 := h12) hψ0 (G := fun u => t.Y (u ^ (2 * (2 * (0 + 1)))))
    (fun u hu hψ => ?_) (fun u hu hψ => ?_)
  · obtain ⟨hum, -⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * (2 * (0 + 1))) h2 hu hψ
    have hv : OffOrbit (tq1 hs) (u ^ (2 * (0 + 1))) := offOrbit_sqrt_pow hs (tq1 hs) rfl hum
    have e : (u ^ (2 * (0 + 1))) ^ 2 = u ^ (2 * (2 * (0 + 1))) := by
      rw [← pow_mul, mul_comm]
    have hU2 : OffOrbit t ((u ^ (2 * (0 + 1))) ^ 2) := by rw [e]; exact hum
    obtain ⟨-, b, -, d⟩ := (fgT_spec h2 h12 hs).2.2 _ hv hU2
    refine (hasTateValue_pullbackT (isTPoint_levelCoords h2 h12 hs 0)
      (transcendental_levelCoords h2 h12 hs 0) hv (hc u hu hum).1 (hc u hu hum).2
      ((b.add d).add (HasTateValue.const hv _))).congr ?_
    rw [← e, velu_Y hs]
  · obtain ⟨hum, hv⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * (2 * (0 + 1))) h2 hu hψ
    exact (hv (yE t.tateCurve)).congr (by
      rw [show yE t.tateCurve = mkT t Polynomial.X from rfl, evalTate_mk_Y])

/-- The elements `x₁, y₁, x₂, y₂ ∈ Ω`. -/
def fgx₁ : Ω := iotaQ h2 h12 hs (fgT h2 h12 hs).1
/-- See `fgx₁`. -/
def fgy₁ : Ω := iotaQ h2 h12 hs (fgT h2 h12 hs).2.1
/-- See `fgx₁`. -/
def fgx₂ : Ω := iotaQ h2 h12 hs (fgT h2 h12 hs).2.2.1
/-- See `fgx₁`. -/
def fgy₂ : Ω := iotaQ h2 h12 hs (fgT h2 h12 hs).2.2.2

/-- **Vélu, `x`, in `Ω`**: `x₁ + x₂ − x_T = τ`. -/
theorem fg_velu_x :
    fgx₁ h2 h12 hs + fgx₂ h2 h12 hs - algebraMap K Ω ((tq2 hs).X (s ^ 2)) =
      algebraMap (DX t).R Ω (xX t) := by
  have h := congrArg (mulByNEmb t.tateCurve (2 * (2 * (0 + 1)))) (pullbackT_velu_x h2 h12 hs)
  rw [tau_eq, ← AlgHom.comp_apply, ← iotaQ, map_sub, map_add, AlgHom.commutes] at h
  rw [algebraMap_xX]
  exact h

/-- **Vélu, `y`, in `Ω`**: `y₁ + y₂ + c_y = y`. -/
theorem fg_velu_y :
    fgy₁ h2 h12 hs + fgy₂ h2 h12 hs +
        algebraMap K Ω (t.eisenstein 1 - 2 * (tq2 hs).eisenstein 1) =
      algebraMap (DX t).R Ω (yX t) := by
  have h := congrArg (mulByNEmb t.tateCurve (2 * (2 * (0 + 1)))) (pullbackT_velu_y h2 h12 hs)
  rw [mulByNEmb_mulByNHom, ← AlgHom.comp_apply, ← iotaQ, map_add, map_add,
    AlgHom.commutes] at h
  rw [algebraMap_yX, hemiRho_apply, algebraMap_hemiREquiv']
  exact h

include h2 in
/-- **The relations of the `ℙ⁴`-model in `Ω`.** -/
theorem fg_rels :
    fgy₁ h2 h12 hs ^ 2 + fgx₁ h2 h12 hs * fgy₁ h2 h12 hs = fgx₁ h2 h12 hs ^ 3 +
        algebraMap K Ω (tq2 hs).a₄ * fgx₁ h2 h12 hs + algebraMap K Ω (tq2 hs).a₆ ∧
    fgy₂ h2 h12 hs ^ 2 + fgx₂ h2 h12 hs * fgy₂ h2 h12 hs = fgx₂ h2 h12 hs ^ 3 +
        algebraMap K Ω (tq2 hs).a₄ * fgx₂ h2 h12 hs + algebraMap K Ω (tq2 hs).a₆ ∧
    (fgx₁ h2 h12 hs - algebraMap K Ω ((tq2 hs).X (s ^ 2))) *
        (fgx₂ h2 h12 hs - algebraMap K Ω ((tq2 hs).X (s ^ 2))) =
      algebraMap K Ω (3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2) ∧
    (2 * fgy₂ h2 h12 hs + fgx₂ h2 h12 hs) *
        (fgx₁ h2 h12 hs - algebraMap K Ω ((tq2 hs).X (s ^ 2))) +
      (2 * fgy₁ h2 h12 hs + fgx₁ h2 h12 hs) *
        (fgx₂ h2 h12 hs - algebraMap K Ω ((tq2 hs).X (s ^ 2))) = 0 ∧
    (2 * fgy₁ h2 h12 hs + fgx₁ h2 h12 hs) * (2 * fgy₂ h2 h12 hs + fgx₂ h2 h12 hs) +
      algebraMap K Ω (3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2) *
        (4 * (fgx₁ h2 h12 hs + fgx₂ h2 h12 hs) +
          algebraMap K Ω (4 * (tq2 hs).X (s ^ 2) + 1)) = 0 := by
  obtain ⟨r1, r2, r3, r4, r5⟩ := fourGon_rels h2 h12 hs (fgT_spec h2 h12 hs).2.2
  have m : ∀ {a b : TateField (tq1 hs)}, a = b → iotaQ h2 h12 hs a = iotaQ h2 h12 hs b :=
    fun h => congrArg _ h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [fgx₁, fgy₁, fgx₂, fgy₂, map_add, map_mul, map_pow, map_sub, map_ofNat,
      map_one, map_zero, map_div₀, AlgHom.commutes] using m r1
  · simpa only [fgx₁, fgy₁, fgx₂, fgy₂, map_add, map_mul, map_pow, map_sub, map_ofNat,
      map_one, map_zero, map_div₀, AlgHom.commutes] using m r2
  · simpa only [fgx₁, fgy₁, fgx₂, fgy₂, map_add, map_mul, map_pow, map_sub, map_ofNat,
      map_one, map_zero, map_div₀, AlgHom.commutes] using m r3
  · simpa only [fgx₁, fgy₁, fgx₂, fgy₂, map_add, map_mul, map_pow, map_sub, map_ofNat,
      map_one, map_zero, map_div₀, AlgHom.commutes] using m r4
  · simpa only [fgx₁, fgy₁, fgx₂, fgy₂, map_add, map_mul, map_pow, map_sub, map_ofNat,
      map_one, map_zero, map_div₀, AlgHom.commutes] using m r5

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem isIntegral_K (c : K) : IsIntegral (A₀ K τ) (algebraMap K Ω c) := by
  rw [IsScalarTower.algebraMap_apply K (A₀ K τ) Ω]
  exact isIntegral_algebraMap

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem isIntegral_DX (r : (DX t).R) : IsIntegral (A₀ K τ) (algebraMap (DX t).R Ω r) :=
  CoordRing.isIntegral_algebraMap r

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem isIntegral_half : IsIntegral (A₀ K τ) (algebraMap K Ω 2⁻¹) := isIntegral_K _

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem half_mul_two : algebraMap K Ω 2⁻¹ * 2 = 1 := by
  have h2Ω : (2 : Ω) ≠ 0 := by
    have := (algebraMap K Ω).injective.ne (two_ne_zero (α := K))
    rwa [map_ofNat, map_zero] at this
  rw [map_inv₀, map_ofNat, inv_mul_cancel₀ h2Ω]

include h2 in
theorem isIntegral_fgx :
    IsIntegral (A₀ K τ) (fgx₁ h2 h12 hs) ∧ IsIntegral (A₀ K τ) (fgx₂ h2 h12 hs) := by
  have hv := fg_velu_x h2 h12 hs
  have r := (fg_rels h2 h12 hs).2.2.1
  set E := algebraMap K Ω ((tq2 hs).X (s ^ 2))
  set C := algebraMap K Ω (3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2)
  set T := algebraMap (DX t).R Ω (xX t)
  have hE : IsIntegral (A₀ K τ) E := isIntegral_K _
  have hC : IsIntegral (A₀ K τ) C := isIntegral_K _
  have hT : IsIntegral (A₀ K τ) T := isIntegral_DX _
  have hab : IsIntegral (A₀ K τ) (T + E) := hT.add hE
  have hb : IsIntegral (A₀ K τ) (-(E * T + C)) := ((hE.mul hT).add hC).neg
  refine ⟨isIntegral_of_sq_eq isIntegral_half half_mul_two hab hb ?_,
    isIntegral_of_sq_eq isIntegral_half half_mul_two hab hb ?_⟩
  · linear_combination (-1 : Ω) * r + (fgx₁ h2 h12 hs - E) * hv
  · linear_combination (-1 : Ω) * r + (fgx₂ h2 h12 hs - E) * hv

include h2 in
theorem isIntegral_fgy :
    IsIntegral (A₀ K τ) (fgy₁ h2 h12 hs) ∧ IsIntegral (A₀ K τ) (fgy₂ h2 h12 hs) := by
  obtain ⟨r1, r2, -⟩ := fg_rels h2 h12 hs
  obtain ⟨hx₁, hx₂⟩ := isIntegral_fgx h2 h12 hs
  have h4 := isIntegral_K (t := t) (tq2 hs).a₄
  have h6 := isIntegral_K (t := t) (tq2 hs).a₆
  refine ⟨isIntegral_of_sq_eq isIntegral_half half_mul_two hx₁.neg
      (((hx₁.pow 3).add (h4.mul hx₁)).add h6) ?_,
    isIntegral_of_sq_eq isIntegral_half half_mul_two hx₂.neg
      (((hx₂.pow 3).add (h4.mul hx₂)).add h6) ?_⟩
  · linear_combination r1
  · linear_combination r2

end Wrapper


/-! ### `x₁, y₁, x₂, y₂ ∈ R'` and the `ℙ⁴`-model relations (fields of `FourGon.Input`) -/

section Input

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve KummerTheory KummerTheory.Curve CurvesJacobian.Cusp
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

variable (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)
  [t.tateCurve.IsElliptic]

/-- `x₁ ∈ R' = K[E_{q²}]` (the coordinate ring of `levelQN 0`). -/
def x₁R : (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
    (isOpen_levelQN h2 h12 hs 0)).R :=
  CoordRing.mk (fgx₁ h2 h12 hs) (iotaQ_mem_L h2 h12 hs (fgT_spec h2 h12 hs).1.1)
    (isIntegral_fgx h2 h12 hs).1

/-- `y₁ ∈ R'`. -/
def y₁R : (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
    (isOpen_levelQN h2 h12 hs 0)).R :=
  CoordRing.mk (fgy₁ h2 h12 hs) (iotaQ_mem_L h2 h12 hs (fgT_spec h2 h12 hs).1.2.1)
    (isIntegral_fgy h2 h12 hs).1

/-- `x₂ ∈ R'`. -/
def x₂R : (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
    (isOpen_levelQN h2 h12 hs 0)).R :=
  CoordRing.mk (fgx₂ h2 h12 hs) (iotaQ_mem_L h2 h12 hs (fgT_spec h2 h12 hs).1.2.2.1)
    (isIntegral_fgx h2 h12 hs).2

/-- `y₂ ∈ R'`. -/
def y₂R : (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
    (isOpen_levelQN h2 h12 hs 0)).R :=
  CoordRing.mk (fgy₂ h2 h12 hs) (iotaQ_mem_L h2 h12 hs (fgT_spec h2 h12 hs).1.2.2.2)
    (isIntegral_fgy h2 h12 hs).2

theorem algebraMap_RQ_K (c : K) :
    algebraMap (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
      (isOpen_levelQN h2 h12 hs 0)).R Ω
        (algebraMap K (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
          (isOpen_levelQN h2 h12 hs 0)).R c) = algebraMap K Ω c :=
  (IsScalarTower.algebraMap_apply K _ Ω c).symm

theorem algebraMap_RQ_R (r : (DX t).R) :
    algebraMap (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
      (isOpen_levelQN h2 h12 hs 0)).R Ω
        (algebraMap (DX t).R (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
          (isOpen_levelQN h2 h12 hs 0)).R r) = algebraMap (DX t).R Ω r :=
  rfl

include h2 in
/-- **The relations in `R'`** with the coefficients `a₄', a₆'`, `e = x_T`, `C_T`, `c_y` of `K`. -/
theorem fg_rels_R :
    y₁R h2 h12 hs ^ 2 + x₁R h2 h12 hs * y₁R h2 h12 hs = x₁R h2 h12 hs ^ 3 +
        algebraMap K _ (tq2 hs).a₄ * x₁R h2 h12 hs + algebraMap K _ (tq2 hs).a₆ ∧
    y₂R h2 h12 hs ^ 2 + x₂R h2 h12 hs * y₂R h2 h12 hs = x₂R h2 h12 hs ^ 3 +
        algebraMap K _ (tq2 hs).a₄ * x₂R h2 h12 hs + algebraMap K _ (tq2 hs).a₆ ∧
    (x₁R h2 h12 hs - algebraMap K _ ((tq2 hs).X (s ^ 2))) *
        (x₂R h2 h12 hs - algebraMap K _ ((tq2 hs).X (s ^ 2))) =
      algebraMap K _ (3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2) ∧
    (2 * y₂R h2 h12 hs + x₂R h2 h12 hs) *
        (x₁R h2 h12 hs - algebraMap K _ ((tq2 hs).X (s ^ 2))) +
      (2 * y₁R h2 h12 hs + x₁R h2 h12 hs) *
        (x₂R h2 h12 hs - algebraMap K _ ((tq2 hs).X (s ^ 2))) = 0 ∧
    (2 * y₁R h2 h12 hs + x₁R h2 h12 hs) * (2 * y₂R h2 h12 hs + x₂R h2 h12 hs) +
      algebraMap K _ (3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2) *
        (4 * (x₁R h2 h12 hs + x₂R h2 h12 hs) +
          algebraMap K _ (4 * (tq2 hs).X (s ^ 2) + 1)) = 0 ∧
    algebraMap (DX t).R _ (xX t) =
      x₁R h2 h12 hs + x₂R h2 h12 hs - algebraMap K _ ((tq2 hs).X (s ^ 2)) ∧
    algebraMap (DX t).R _ (yX t) = y₁R h2 h12 hs + y₂R h2 h12 hs +
      algebraMap K _ (t.eisenstein 1 - 2 * (tq2 hs).eisenstein 1) := by
  obtain ⟨r1, r2, r3, r4, r5⟩ := fg_rels h2 h12 hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply CoordRing.ext <;>
    simp only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_zero, algebraMap_RQ_K,
      algebraMap_RQ_R, x₁R, y₁R, x₂R, y₂R, CoordRing.algebraMap_mk]
  · simpa only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_one, map_zero, map_div₀,
      AlgHom.commutes] using r1
  · simpa only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_one, map_zero, map_div₀,
      AlgHom.commutes] using r2
  · simpa only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_one, map_zero, map_div₀,
      AlgHom.commutes] using r3
  · simpa only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_one, map_zero, map_div₀,
      AlgHom.commutes] using r4
  · simpa only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_one, map_zero, map_div₀,
      AlgHom.commutes] using r5
  · simpa only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_one, map_zero, map_div₀,
      AlgHom.commutes] using (fg_velu_x h2 h12 hs).symm
  · simpa only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_one, map_zero, map_div₀,
      AlgHom.commutes] using (fg_velu_y h2 h12 hs).symm

include h2 in
/-- **The fields (1)–(5), (7) of `FourGon.Input`** for `E_{q²}` (`π = s`, `b₄' = a₄'/s²`,
`b₆' = a₆'/s²`, `ε = x_T/s`, `γ = C_T/s²`, `κ = c_y/s`). -/
theorem exists_fourGonInput_rels (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) :
    ∃ (b₄' b₆' ε γ κ : O),
      y₁R h2 h12 hs ^ 2 + x₁R h2 h12 hs * y₁R h2 h12 hs = x₁R h2 h12 hs ^ 3 +
          algebraMap K _ (((tateDataX O hO hs h12).π : K) ^ 2 * b₄') * x₁R h2 h12 hs +
          algebraMap K _ (((tateDataX O hO hs h12).π : K) ^ 2 * b₆') ∧
      y₂R h2 h12 hs ^ 2 + x₂R h2 h12 hs * y₂R h2 h12 hs = x₂R h2 h12 hs ^ 3 +
          algebraMap K _ (((tateDataX O hO hs h12).π : K) ^ 2 * b₄') * x₂R h2 h12 hs +
          algebraMap K _ (((tateDataX O hO hs h12).π : K) ^ 2 * b₆') ∧
      (x₁R h2 h12 hs - algebraMap K _ (((tateDataX O hO hs h12).π : K) * ε)) *
          (x₂R h2 h12 hs - algebraMap K _ (((tateDataX O hO hs h12).π : K) * ε)) =
        algebraMap K _ (((tateDataX O hO hs h12).π : K) ^ 2 * γ) ∧
      (2 * y₂R h2 h12 hs + x₂R h2 h12 hs) *
          (x₁R h2 h12 hs - algebraMap K _ (((tateDataX O hO hs h12).π : K) * ε)) +
        (2 * y₁R h2 h12 hs + x₁R h2 h12 hs) *
          (x₂R h2 h12 hs - algebraMap K _ (((tateDataX O hO hs h12).π : K) * ε)) = 0 ∧
      (2 * y₁R h2 h12 hs + x₁R h2 h12 hs) * (2 * y₂R h2 h12 hs + x₂R h2 h12 hs) +
        algebraMap K _ (((tateDataX O hO hs h12).π : K) ^ 2 * γ) *
          (4 * (x₁R h2 h12 hs + x₂R h2 h12 hs) +
            algebraMap K _ (4 * ((tateDataX O hO hs h12).π : K) * ε + 1)) = 0 ∧
      algebraMap (DX t).R _ (tateDataX O hO hs h12).x = x₁R h2 h12 hs + x₂R h2 h12 hs -
        algebraMap K _ (((tateDataX O hO hs h12).π : K) * ε) ∧
      algebraMap (DX t).R _ (tateDataX O hO hs h12).y = y₁R h2 h12 hs + y₂R h2 h12 hs +
        algebraMap K _ (((tateDataX O hO hs h12).π : K) * κ) ∧
      b₆' ∈ IsLocalRing.maximalIdeal O ∧ ε ∈ IsLocalRing.maximalIdeal O ∧ IsUnit γ := by
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  obtain ⟨hsp, hs1⟩ := norm_s_pos_lt hs
  have hπ : ((tateDataX O hO hs h12).π : K) = s := rfl
  have hle : ∀ k : ℕ, ‖(s : K)‖ ^ k ≤ 1 := fun k => pow_le_one₀ (norm_nonneg _) hs1.le
  obtain ⟨b₄', hb₄⟩ : ∃ b : O, ((tateDataX O hO hs h12).π : K) ^ 2 * b = (tq2 hs).a₄ :=
    ⟨⟨(tq2 hs).a₄ / (s : K) ^ 2, (hO _).2 ((norm_div_s_le (norm_a₄_tq2_le hs)).trans (hle 2))⟩,
      by change (s : K) ^ 2 * ((tq2 hs).a₄ / (s : K) ^ 2) = _
         exact mul_div_cancel₀ _ (pow_ne_zero 2 hs0)⟩
  obtain ⟨b₆', hb₆, hb₆m⟩ : ∃ b : O, ((tateDataX O hO hs h12).π : K) ^ 2 * b = (tq2 hs).a₆ ∧
      b ∈ IsLocalRing.maximalIdeal O := by
    have h := norm_div_s_le (norm_a₆_tq2_le hs h12)
    refine ⟨⟨(tq2 hs).a₆ / (s : K) ^ 2, (hO _).2 (h.trans (hle 2))⟩,
      by change (s : K) ^ 2 * ((tq2 hs).a₆ / (s : K) ^ 2) = _
         exact mul_div_cancel₀ _ (pow_ne_zero 2 hs0),
      mem_maximalIdeal_of_norm_lt O hO (h.trans_lt (pow_lt_one₀ (norm_nonneg _) hs1 two_ne_zero))⟩
  obtain ⟨ε, hε, hεm⟩ : ∃ b : O, ((tateDataX O hO hs h12).π : K) * b = (tq2 hs).X (s ^ 2) ∧
      b ∈ IsLocalRing.maximalIdeal O := by
    have h := norm_div_s_le (n := 1) (k := 1)
      (show ‖(tq2 hs).X (s ^ 2)‖ ≤ ‖(s : K)‖ ^ (1 + 1) by rw [norm_xT hs h2])
    refine ⟨⟨(tq2 hs).X (s ^ 2) / (s : K) ^ 1, (hO _).2 (h.trans (hle 1))⟩,
      by change (s : K) * ((tq2 hs).X (s ^ 2) / (s : K) ^ 1) = _
         rw [pow_one]; exact mul_div_cancel₀ _ hs0,
      mem_maximalIdeal_of_norm_lt O hO (h.trans_lt (by rw [pow_one]; exact hs1))⟩
  obtain ⟨γ, hγ, hγu⟩ : ∃ b : O, ((tateDataX O hO hs h12).π : K) ^ 2 * b =
      3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2 ∧ IsUnit b := by
    have h : ‖(3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2) /
        (s : K) ^ 2‖ = 1 := by
      rw [norm_div, norm_pow, norm_CT hs h2, div_self (pow_pos hsp 2).ne']
    refine ⟨⟨_, (hO _).2 h.le⟩, by
        change (s : K) ^ 2 * ((3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2) /
          (s : K) ^ 2) = _
        exact mul_div_cancel₀ _ (pow_ne_zero 2 hs0),
      isUnit_of_norm_eq_one O hO (x := ⟨_, (hO _).2 h.le⟩) h⟩
  obtain ⟨κ, hκ⟩ : ∃ b : O, ((tateDataX O hO hs h12).π : K) * b =
      t.eisenstein 1 - 2 * (tq2 hs).eisenstein 1 := by
    have h := norm_div_s_le (n := 1) (k := 1) (norm_cY_le hs)
    refine ⟨⟨_, (hO _).2 (h.trans (hle 1))⟩, ?_⟩
    change (s : K) * ((t.eisenstein 1 - 2 * (tq2 hs).eisenstein 1) / (s : K) ^ 1) = _
    rw [pow_one]; exact mul_div_cancel₀ _ hs0
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := fg_rels_R h2 h12 hs
  refine ⟨b₄', b₆', ε, γ, κ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb₆m, hεm, hγu⟩
  · rw [hb₄, hb₆]; exact r1
  · rw [hb₄, hb₆]; exact r2
  · rw [hε, hγ]; exact r3
  · rw [hε]; exact r4
  · rw [hγ, show 4 * ((tateDataX O hO hs h12).π : K) * (ε : K) = 4 * (tq2 hs).X (s ^ 2) by
      rw [mul_assoc, hε]]
    exact r5
  · rw [hε]; exact r6
  · rw [hκ]; exact r7

end Input

/-! ### The fibre of `Spec R' → X` over the generic point: `x₁, y₁, x₂, y₂` are swapped or fixed -/

/-- **The fibre lemma, generic algebra**: two solutions `(aᵢ, bᵢ)`, `(aᵢ', bᵢ')` of the
relations `a₁ + a₂ = S`, `(a₁ − e)(a₂ − e) = C`, `b₁ + b₂ = W`, relation (3), with `a₁ ≠ a₂`, are
equal or swapped. -/
theorem fibre_cases {F : Type*} [Field F] (h2F : (2 : F) ≠ 0)
    {E C S W a₁ a₂ b₁ b₂ a₁' a₂' b₁' b₂' : F}
    (hne : a₁ ≠ a₂) (hS : a₁ + a₂ = S) (hS' : a₁' + a₂' = S) (hC : (a₁ - E) * (a₂ - E) = C)
    (hC' : (a₁' - E) * (a₂' - E) = C) (hW : b₁ + b₂ = W) (hW' : b₁' + b₂' = W)
    (h3 : (2 * b₂ + a₂) * (a₁ - E) + (2 * b₁ + a₁) * (a₂ - E) = 0)
    (h3' : (2 * b₂' + a₂') * (a₁' - E) + (2 * b₁' + a₁') * (a₂' - E) = 0) :
    (a₁' = a₁ ∧ b₁' = b₁ ∧ a₂' = a₂ ∧ b₂' = b₂) ∨
      (a₁' = a₂ ∧ b₁' = b₂ ∧ a₂' = a₁ ∧ b₂' = b₁) := by
  have hq : (a₁' - a₁) * (a₁' - a₂) = 0 := by
    linear_combination hC - hC' + (a₁' - E) * hS' - (a₁' - E) * hS
  rcases mul_eq_zero.1 hq with h1 | h1
  · have e1 : a₁' = a₁ := sub_eq_zero.1 h1
    have e2 : a₂' = a₂ := by linear_combination hS' - hS - e1
    rw [e1, e2] at h3'
    have hb : (b₁' - b₁) * (2 * (a₂ - a₁)) = 0 := by
      linear_combination h3' - h3 - 2 * (a₁ - E) * hW' + 2 * (a₁ - E) * hW
    have hd : 2 * (a₂ - a₁) ≠ 0 := mul_ne_zero h2F (sub_ne_zero.2 (Ne.symm hne))
    have eb1 : b₁' = b₁ := sub_eq_zero.1 ((mul_eq_zero.1 hb).resolve_right hd)
    exact Or.inl ⟨e1, eb1, e2, by linear_combination hW' - hW - eb1⟩
  · have e1 : a₁' = a₂ := sub_eq_zero.1 h1
    have e2 : a₂' = a₁ := by linear_combination hS' - hS - e1
    rw [e1, e2] at h3'
    have hb : (b₁' - b₂) * (2 * (a₁ - a₂)) = 0 := by
      linear_combination h3' - h3 - 2 * (a₂ - E) * hW' + 2 * (a₂ - E) * hW
    have hd : 2 * (a₁ - a₂) ≠ 0 := mul_ne_zero h2F (sub_ne_zero.2 hne)
    have eb1 : b₁' = b₂ := sub_eq_zero.1 ((mul_eq_zero.1 hb).resolve_right hd)
    exact Or.inr ⟨e1, eb1, e2, by linear_combination hW' - hW - eb1⟩

/-- Distinct roots: if `a₁ + a₂ − e = T`, `(a₁ − e)(a₂ − e) = C` and `(T − e)² ≠ 4C`, then
`a₁ ≠ a₂`. -/
theorem ne_of_disc {F : Type*} [Field F] {a₁ a₂ E C T : F} (hv : a₁ + a₂ - E = T)
    (r : (a₁ - E) * (a₂ - E) = C) (hd : (T - E) ^ 2 ≠ 4 * C) : a₁ ≠ a₂ := by
  intro heq
  apply hd
  linear_combination (-(T + a₁ + a₂ - 3 * E)) * hv + (a₁ - a₂) * heq + 4 * r

section Fibre

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve KummerTheory KummerTheory.Curve CurvesJacobian.Cusp
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

variable (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)
  [t.tateCurve.IsElliptic]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- `τ` is not a root of `(X − d)² − c`. -/
theorem tau_sub_sq_ne (d c : K) :
    (algebraMap (DX t).R Ω (xX t) - algebraMap K Ω d) ^ 2 ≠ algebraMap K Ω c := by
  intro h
  rw [algebraMap_xX] at h
  apply transcendental_tau t.tateCurve
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (2 * d) * Polynomial.X + Polynomial.C (d ^ 2 - c),
    fun h0 => ?_, ?_⟩
  · have := congrArg (fun p : K[X] => p.coeff 2) h0
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at this
    norm_num at this
  · simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, aeval_X, aeval_C]
    linear_combination h

omit [CharZero K] in
/-- `t_w` for equal `w`. -/
theorem transT_congr {T : TateParameter K} {w w' : Kˣ} (h : w = w') (hw : OffOrbit T w)
    (hw' : OffOrbit T w') : transT h12 hw = transT h12 hw' := by
  subst h; rfl

omit [CharZero K] in
include h2 in
/-- `t_{ww'} = t_w ∘ t_{w'}`. -/
theorem transT_mul (T : TateParameter K) [T.tateCurve.IsElliptic] {w w' : Kˣ}
    (hw : OffOrbit T w) (hw' : OffOrbit T w') (hww : OffOrbit T (w * w')) (g : TateField T) :
    transT h12 hww g = transT h12 hw (transT h12 hw' g) := by
  classical
  have hmem : ∀ v : Kˣ, (∀ n : ℤ, (T.q : K) ^ n * (v : K) ≠ 1) →
      T.tateCurve.toAffine.Equation (T.X v) (T.Y v) := fun v hv => T.tatePoint_mem' h12 hv
  have tame : TameResidueChar K := ⟨h2, h12⟩
  rw [← transT_eq_translateAut h12 T hmem tame hww, ← transT_eq_translateAut h12 T hmem tame hw,
    ← transT_eq_translateAut h12 T hmem tame hw', ← AlgEquiv.mul_apply,
    ← WeierstrassCurve.Affine.CoordinateRing.translateAut_add, T.tatePoint_mul]

/-- **The Galois action on `K(E_Q)`** (`exists_levelEmb`): every `σ` fixing `L_X` acts on
`ι(K(E_Q))` by a translation `t_w`, `w = (-1)^e s^a`. -/
theorem iotaQ_galois (σ : Ω ≃ₐ[K₀ K τ] Ω) (hσ : ∀ z ∈ (hemiData t.tateCurve).L, σ z = z) :
    ∃ p : Fin 2 × Fin (2 * (0 + 1)),
      ((σ : Ω →ₐ[K₀ K τ] Ω).restrictScalars K).comp (iotaQ h2 h12 hs) =
        (iotaQ h2 h12 hs).comp (baseAut (rfl : (tq1 hs).q = s ^ (2 * (0 + 1)))
          (Nat.mul_pos two_pos (0 : ℕ).succ_pos) h12 p.1 p.2 :
            TateField (tq1 hs) →ₐ[K] TateField (tq1 hs)) := by
  obtain ⟨gX, gY, F, -, hmul, -, hval⟩ := exists_levelData (t := t) h12 h2 hs
    (N := 2 * (0 + 1)) (Nat.mul_pos two_pos (0 : ℕ).succ_pos) ⟨0 + 1, by ring⟩
  obtain ⟨e1, e2⟩ := eq_levelCoords h2 h12 hs 0 (gX := gX) (gY := gY)
    (fun u hu hum => ⟨(hval u hu hum).1, (hval u hu hum).2.1⟩)
  subst e1 e2
  obtain ⟨hpt, htr, -, -, -, hidx⟩ := exists_levelEmb h2 h12 hs
    (N := 2 * (0 + 1)) (Nat.mul_pos two_pos (0 : ℕ).succ_pos) ⟨0 + 1, by ring⟩ hmul hval
  exact hidx σ hσ

omit [t.tateCurve.IsElliptic] in
/-- **The translations `t_w`, `w ∈ {±1, ±s}`, of `K(E_Q)`**: `t_{±1}` fix the `t_{-1}`-fixed
field, `t_{±s}` send `x₁ ↦ x₂`. -/
theorem baseAut_cases (p : Fin 2 × Fin (2 * (0 + 1))) :
    (∀ f, transT h12 (offOrbit_neg_one (tq1 hs) h2) f = f →
        baseAut (rfl : (tq1 hs).q = s ^ (2 * (0 + 1))) (Nat.mul_pos two_pos (0 : ℕ).succ_pos)
          h12 p.1 p.2 f = f) ∨
      baseAut (rfl : (tq1 hs).q = s ^ (2 * (0 + 1))) (Nat.mul_pos two_pos (0 : ℕ).succ_pos)
        h12 p.1 p.2 (fgT h2 h12 hs).1 = (fgT h2 h12 hs).2.2.1 := by
  obtain ⟨e, a⟩ := p
  have hspec := fgT_spec h2 h12 hs
  have cm : ∀ (w : Kˣ) (hw : OffOrbit (tq1 hs) w), w = -1 → ∀ f,
      transT h12 (offOrbit_neg_one (tq1 hs) h2) f = f → transT h12 hw f = f := by
    rintro w hw rfl f hf
    exact hf
  have cs : ∀ (w : Kˣ) (hw : OffOrbit (tq1 hs) w), w = s →
      transT h12 hw (fgT h2 h12 hs).1 = (fgT h2 h12 hs).2.2.1 := by
    rintro w hw rfl
    exact hspec.2.1.1
  have cms : ∀ (w : Kˣ) (hw : OffOrbit (tq1 hs) w), w = -1 * s →
      transT h12 hw (fgT h2 h12 hs).1 = (fgT h2 h12 hs).2.2.1 := by
    rintro w hw rfl
    rw [transT_mul h2 h12 (tq1 hs) (offOrbit_neg_one (tq1 hs) h2) (offOrbit_tq1_s hs) hw,
      hspec.2.1.1, hspec.1.2.2.1]
  fin_cases e <;> fin_cases a
  · left
    intro f _
    simp [baseAut]
  · right
    simp only [baseAut]
    rw [dif_neg (by decide)]
    exact cs _ _ (by simp [cuspElt])
  · left
    intro f hf
    simp only [baseAut]
    rw [dif_neg (by decide)]
    exact cm _ _ (by simp [cuspElt]) f hf
  · right
    simp only [baseAut]
    rw [dif_neg (by decide)]
    exact cms _ _ (by simp [cuspElt])

include h2 in
/-- `L_X ≤ K(τ)(x₁, y₁, x₂, y₂)` (`[4]^*x = ι(x₁ + x₂ − e)`, `[4]^*y = ι(y₁ + y₂ + c_y)`). -/
theorem hemiL_le_adjoinS : (hemiData t.tateCurve).L ≤ IntermediateField.adjoin (K₀ K τ)
    ({fgx₁ h2 h12 hs, fgy₁ h2 h12 hs, fgx₂ h2 h12 hs, fgy₂ h2 h12 hs} : Set Ω) := by
  set j := pullbackT (levelCoords h2 h12 hs 0).1 (levelCoords h2 h12 hs 0).2
      (isTPoint_levelCoords h2 h12 hs 0) (transcendental_levelCoords h2 h12 hs 0) with hj
  set S : Set (TateField t) := {j (fgT h2 h12 hs).1, j (fgT h2 h12 hs).2.1,
    j (fgT h2 h12 hs).2.2.1, j (fgT h2 h12 hs).2.2.2} with hS
  have mem : ∀ f ∈ S, f ∈ IntermediateField.adjoin K S := fun f hf =>
    IntermediateField.subset_adjoin K S hf
  have hx : algebraMap _ (TateField t) (mulByNHom t.tateCurve (2 * (2 * (0 + 1)))
      (xE t.tateCurve)) ∈ IntermediateField.adjoin K S := by
    rw [← pullbackT_velu_x h2 h12 hs, map_sub, map_add, AlgHom.commutes]
    exact sub_mem (add_mem (mem _ (Set.mem_insert _ _))
      (mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))
      (IntermediateField.algebraMap_mem _ _)
  have hy : algebraMap _ (TateField t) (mulByNHom t.tateCurve (2 * (2 * (0 + 1)))
      (yE t.tateCurve)) ∈ IntermediateField.adjoin K S := by
    rw [← pullbackT_velu_y h2 h12 hs, map_add, map_add, AlgHom.commutes]
    exact add_mem (add_mem (mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
      (mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_singleton _))))))
      (IntermediateField.algebraMap_mem _ _)
  have h := hemiL_le_adjoin t.tateCurve (2 * (2 * (0 + 1))) (S := S)
    (fun a => mulByNHom_mem_of_xy (2 * (2 * (0 + 1))) hx hy a)
  have e : mulByNEmb t.tateCurve (2 * (2 * (0 + 1))) '' S =
      {fgx₁ h2 h12 hs, fgy₁ h2 h12 hs, fgx₂ h2 h12 hs, fgy₂ h2 h12 hs} := by
    simp only [hS, Set.image_insert_eq, Set.image_singleton]
    rfl
  rwa [e] at h

include h2 in
theorem fgx_ne : fgx₁ h2 h12 hs ≠ fgx₂ h2 h12 hs := by
  refine ne_of_disc (fg_velu_x h2 h12 hs) (fg_rels h2 h12 hs).2.2.1 ?_
  rw [← map_ofNat (algebraMap K Ω) 4, ← map_mul]
  exact tau_sub_sq_ne _ _

include h2 in
/-- **`K(E_{q²}) = K(τ)(x₁, y₁, x₂, y₂)`**, via Galois theory: `σ` fixing `x₁, y₁, x₂, y₂`
fixes `L_X`, so acts on `ι(K(E_Q))` by `t_w`, `w ∈ {±1, ±s}` (`iotaQ_galois`); `w = ±s` would
move `x₁` to `x₂ ≠ x₁`, and `t_{±1}` fix the `t_{-1}`-fixed field. -/
theorem levelQN_le_adjoinS : levelQN h2 h12 hs 0 ≤ IntermediateField.adjoin (K₀ K τ)
    ({fgx₁ h2 h12 hs, fgy₁ h2 h12 hs, fgx₂ h2 h12 hs, fgy₂ h2 h12 hs} : Set Ω) := by
  intro z hz
  rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin (K₀ K τ)
    ({fgx₁ h2 h12 hs, fgy₁ h2 h12 hs, fgx₂ h2 h12 hs, fgy₂ h2 h12 hs} : Set Ω))]
  rintro ⟨σ, hσ⟩
  change σ z = z
  have hσS := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ
  obtain ⟨p, hp⟩ := iotaQ_galois h2 h12 hs σ
    (fun w hw => hσS w (hemiL_le_adjoinS h2 h12 hs hw))
  have hι : ∀ f, σ (iotaQ h2 h12 hs f) = iotaQ h2 h12 hs
      (baseAut (rfl : (tq1 hs).q = s ^ (2 * (0 + 1))) (Nat.mul_pos two_pos (0 : ℕ).succ_pos)
        h12 p.1 p.2 f) := fun f => DFunLike.congr_fun hp f
  have hF : ∀ f, transT h12 (offOrbit_neg_one (tq1 hs) h2) f = f →
      σ (iotaQ h2 h12 hs f) = iotaQ h2 h12 hs f := by
    rcases baseAut_cases h2 h12 hs p with hc | hc
    · intro f hf
      rw [hι, hc f hf]
    · exfalso
      have h1 : σ (fgx₁ h2 h12 hs) = fgx₁ h2 h12 hs :=
        hσS _ (IntermediateField.subset_adjoin _ _ (by simp))
      rw [fgx₁, hι, hc] at h1
      exact fgx_ne h2 h12 hs h1.symm
  have hz' : z ∈ IntermediateField.adjoin (K₀ K τ)
      (mulByNEmb t.tateCurve (2 * (2 * (0 + 1))) ''
        (pullbackT (levelCoords h2 h12 hs 0).1 (levelCoords h2 h12 hs 0).2
          (isTPoint_levelCoords h2 h12 hs 0) (transcendental_levelCoords h2 h12 hs 0) ''
          {f | transT h12 (offOrbit_neg_one (tq1 hs) h2) f = f})) := hz
  clear hz
  induction hz' using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨_, ⟨f, hf, rfl⟩, rfl⟩ := hx
    exact hF f hf
  | algebraMap c => exact σ.commutes c
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem isAlgebraic_of_mem_levelQN {z : Ω} (hz : z ∈ levelQN h2 h12 hs 0) :
    IsAlgebraic (K₀ K τ) z :=
  ((Algebra.IsIntegral.isIntegral (R := K₀ K τ) (⟨z, hz⟩ : levelQN h2 h12 hs 0)).map
    (IntermediateField.val _)).isAlgebraic

include h2 in
/-- Every element of `R'` times a nonzero element of `K[τ]` lies in `R[x₁, y₁, x₂, y₂]`. -/
theorem exists_mul_mem_adjoin (r : (fieldData (transcendental_tau t.tateCurve)
    (levelQN h2 h12 hs 0) (isOpen_levelQN h2 h12 hs 0)).R) :
    ∃ d : A₀ K τ, algebraMap (A₀ K τ) Ω d ≠ 0 ∧
      algebraMap (DX t).R _ (algebraMap (A₀ K τ) (DX t).R d) * r ∈
        Algebra.adjoin (DX t).R
          ({x₁R h2 h12 hs, y₁R h2 h12 hs, x₂R h2 h12 hs, y₂R h2 h12 hs} :
            Set (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
              (isOpen_levelQN h2 h12 hs 0)).R) := by
  set B := Algebra.adjoin (DX t).R
    ({x₁R h2 h12 hs, y₁R h2 h12 hs, x₂R h2 h12 hs, y₂R h2 h12 hs} :
      Set (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
        (isOpen_levelQN h2 h12 hs 0)).R) with hB
  set S : Set Ω := {fgx₁ h2 h12 hs, fgy₁ h2 h12 hs, fgx₂ h2 h12 hs, fgy₂ h2 h12 hs} with hS
  -- `D d = d` in `R'`
  set D : A₀ K τ → (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
      (isOpen_levelQN h2 h12 hs 0)).R :=
    fun d => algebraMap (DX t).R _ (algebraMap (A₀ K τ) (DX t).R d) with hD
  have hDΩ : ∀ d, algebraMap _ Ω (D d) = algebraMap (A₀ K τ) Ω d := fun d =>
    (IsScalarTower.algebraMap_apply (A₀ K τ) (DX t).R Ω d).symm
  have hDB : ∀ d, D d ∈ B := fun d => Subalgebra.algebraMap_mem B _
  have key : ∀ z ∈ Algebra.adjoin (K₀ K τ) S, ∃ d : A₀ K τ, algebraMap (A₀ K τ) Ω d ≠ 0 ∧
      ∃ b ∈ B, algebraMap _ Ω b = algebraMap (A₀ K τ) Ω d * z := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      refine ⟨1, by simp, ?_⟩
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨x₁R h2 h12 hs, Algebra.subset_adjoin (by simp), by simp [x₁R]⟩
      · exact ⟨y₁R h2 h12 hs, Algebra.subset_adjoin (by simp), by simp [y₁R]⟩
      · exact ⟨x₂R h2 h12 hs, Algebra.subset_adjoin (by simp), by simp [x₂R]⟩
      · exact ⟨y₂R h2 h12 hs, Algebra.subset_adjoin (by simp), by simp [y₂R]⟩
    | algebraMap c =>
      obtain ⟨a, ha, b, hb, hc⟩ := IntermediateField.mem_adjoin_iff_div.mp c.2
      by_cases hb0 : b = 0
      · refine ⟨1, by simp, 0, zero_mem _, ?_⟩
        rw [map_zero, map_one, one_mul]
        change 0 = (c : Ω)
        rw [hc, hb0, div_zero]
      · refine ⟨⟨b, hb⟩, hb0, D ⟨a, ha⟩, hDB _, ?_⟩
        rw [hDΩ]
        change a = b * (c : Ω)
        rw [hc, mul_div_cancel₀ _ hb0]
    | add x y _ _ hx hy =>
      obtain ⟨d₁, hd₁, b₁, hb₁, e₁⟩ := hx
      obtain ⟨d₂, hd₂, b₂, hb₂, e₂⟩ := hy
      refine ⟨d₁ * d₂, by rw [map_mul]; exact mul_ne_zero hd₁ hd₂, D d₂ * b₁ + D d₁ * b₂,
        add_mem (mul_mem (hDB _) hb₁) (mul_mem (hDB _) hb₂), ?_⟩
      rw [map_add, map_mul, map_mul, hDΩ, hDΩ, e₁, e₂, map_mul]
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨d₁, hd₁, b₁, hb₁, e₁⟩ := hx
      obtain ⟨d₂, hd₂, b₂, hb₂, e₂⟩ := hy
      refine ⟨d₁ * d₂, by rw [map_mul]; exact mul_ne_zero hd₁ hd₂, b₁ * b₂, mul_mem hb₁ hb₂, ?_⟩
      rw [map_mul, e₁, e₂, map_mul]
      ring
  have hr : algebraMap _ Ω r ∈ Algebra.adjoin (K₀ K τ) S := by
    have h1 := (fieldData_L (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
      (isOpen_levelQN h2 h12 hs 0)).le (CoordRing.algebraMap_mem r)
    have h2' := levelQN_le_adjoinS h2 h12 hs h1
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun x hx => ?_]
    · exact h2'
    · rcases hx with rfl | rfl | rfl | rfl <;>
        exact isAlgebraic_of_mem_levelQN h2 h12 hs (iotaQ_mem h2 h12 hs (by
          first
            | exact (fgT_spec h2 h12 hs).1.1
            | exact (fgT_spec h2 h12 hs).1.2.1
            | exact (fgT_spec h2 h12 hs).1.2.2.1
            | exact (fgT_spec h2 h12 hs).1.2.2.2))
  obtain ⟨d, hd, b, hb, e⟩ := key _ hr
  refine ⟨d, hd, ?_⟩
  have : b = D d * r := CoordRing.ext (by rw [e, map_mul, hDΩ])
  rw [← this]
  exact hb

include h2 in
/-- **`R'`-algebra maps are determined by `x₁, y₁, x₂, y₂`.** -/
theorem algHom_ext_fg {φ φ' : (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
      (isOpen_levelQN h2 h12 hs 0)).R →ₐ[(DX t).R] Ω}
    (h₁ : φ' (x₁R h2 h12 hs) = φ (x₁R h2 h12 hs)) (h₂ : φ' (y₁R h2 h12 hs) = φ (y₁R h2 h12 hs))
    (h₃ : φ' (x₂R h2 h12 hs) = φ (x₂R h2 h12 hs)) (h₄ : φ' (y₂R h2 h12 hs) = φ (y₂R h2 h12 hs)) :
    φ' = φ := by
  have hB : Algebra.adjoin (DX t).R
      ({x₁R h2 h12 hs, y₁R h2 h12 hs, x₂R h2 h12 hs, y₂R h2 h12 hs} :
        Set (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
          (isOpen_levelQN h2 h12 hs 0)).R) ≤ AlgHom.equalizer φ' φ := by
    rw [Algebra.adjoin_le_iff]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
  ext r
  obtain ⟨d, hd, hmem⟩ := exists_mul_mem_adjoin h2 h12 hs r
  have h := hB hmem
  change φ' _ = φ _ at h
  rw [map_mul, map_mul, AlgHom.commutes, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply (A₀ K τ) (DX t).R Ω] at h
  exact mul_left_cancel₀ hd h

include h2 in
/-- **The fibre property (8)**: two `R`-algebra maps `R' → Ω` are equal or differ by the swap
`(x₁, y₁) ↔ (x₂, y₂)`. -/
theorem fourGon_fibre (φ φ' : (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
      (isOpen_levelQN h2 h12 hs 0)).R →ₐ[(DX t).R] Ω) :
    φ' = φ ∨ (φ' (x₁R h2 h12 hs) = φ (x₂R h2 h12 hs) ∧ φ' (y₁R h2 h12 hs) = φ (y₂R h2 h12 hs) ∧
      φ' (x₂R h2 h12 hs) = φ (x₁R h2 h12 hs) ∧ φ' (y₂R h2 h12 hs) = φ (y₁R h2 h12 hs)) := by
  obtain ⟨-, -, r3, r4, -, r6, r7⟩ := fg_rels_R h2 h12 hs
  have hK : ∀ (ψ : (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
      (isOpen_levelQN h2 h12 hs 0)).R →ₐ[(DX t).R] Ω) (c : K),
      ψ (algebraMap K _ c) = algebraMap K Ω c := fun ψ c => (ψ.restrictScalars K).commutes c
  have data : ∀ (ψ : (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
      (isOpen_levelQN h2 h12 hs 0)).R →ₐ[(DX t).R] Ω),
      ψ (x₁R h2 h12 hs) + ψ (x₂R h2 h12 hs) - algebraMap K Ω ((tq2 hs).X (s ^ 2)) =
        algebraMap (DX t).R Ω (xX t) ∧
      ψ (y₁R h2 h12 hs) + ψ (y₂R h2 h12 hs) =
        algebraMap (DX t).R Ω (yX t) - algebraMap K Ω (t.eisenstein 1 - 2 * (tq2 hs).eisenstein 1) ∧
      (ψ (x₁R h2 h12 hs) - algebraMap K Ω ((tq2 hs).X (s ^ 2))) *
          (ψ (x₂R h2 h12 hs) - algebraMap K Ω ((tq2 hs).X (s ^ 2))) =
        algebraMap K Ω (3 * (tq2 hs).X (s ^ 2) ^ 2 + (tq2 hs).a₄ + (tq2 hs).X (s ^ 2) / 2) ∧
      (2 * ψ (y₂R h2 h12 hs) + ψ (x₂R h2 h12 hs)) *
          (ψ (x₁R h2 h12 hs) - algebraMap K Ω ((tq2 hs).X (s ^ 2))) +
        (2 * ψ (y₁R h2 h12 hs) + ψ (x₁R h2 h12 hs)) *
          (ψ (x₂R h2 h12 hs) - algebraMap K Ω ((tq2 hs).X (s ^ 2))) = 0 := by
    intro ψ
    have a6 := congrArg ψ r6
    have a7 := congrArg ψ r7
    have a3 := congrArg ψ r3
    have a4 := congrArg ψ r4
    simp only [map_add, map_mul, map_sub, map_ofNat, map_zero, AlgHom.commutes, hK] at a6 a7 a3 a4
    refine ⟨a6.symm, ?_, ?_, a4⟩
    · rw [a7, map_sub, map_mul, map_ofNat]; ring
    · simpa only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_one, map_zero, map_div₀,
      AlgHom.commutes] using a3
  obtain ⟨d1, e1, c1, t1⟩ := data φ
  obtain ⟨d2, e2, c2, t2⟩ := data φ'
  have h2Ω : (2 : Ω) ≠ 0 := by
    have := (algebraMap K Ω).injective.ne (two_ne_zero (α := K))
    rwa [map_ofNat, map_zero] at this
  have hne : φ (x₁R h2 h12 hs) ≠ φ (x₂R h2 h12 hs) := by
    refine ne_of_disc d1 c1 ?_
    rw [← map_ofNat (algebraMap K Ω) 4, ← map_mul]
    exact tau_sub_sq_ne _ _
  rcases fibre_cases h2Ω hne (sub_eq_iff_eq_add.1 d1) (sub_eq_iff_eq_add.1 d2) c1 c2 e1 e2 t1 t2
    with ⟨f1, f2, f3, f4⟩ | ⟨f1, f2, f3, f4⟩
  · exact Or.inl (algHom_ext_fg h2 h12 hs f1 f2 f3 f4)
  · exact Or.inr ⟨f1, f2, f3, f4⟩


include h2 in
/-- **The input of `FourGon.Input` for `E_{q²} → E_q`** (`R' = K[E_{q²}]`, the coordinate ring
of `levelQN 0`): the `ℙ⁴`-model relations (1)–(5), the coefficients (7), and the fibre property (8)
(two `R`-algebra maps `R' → Ω` agree or differ by `(x₁, y₁) ↔ (x₂, y₂)`). -/
theorem exists_fourGonInput (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) :
    ∃ (b₄' b₆' ε γ κ : O) (x₁ y₁ x₂ y₂ : (fieldData (transcendental_tau t.tateCurve)
        (levelQN h2 h12 hs 0)
        (isOpen_levelQN h2 h12 hs 0)).R),
      y₁ ^ 2 + x₁ * y₁ = x₁ ^ 3 + algebraMap K _ (((tateDataX O hO hs h12).π : K) ^ 2 * b₄') * x₁ +
          algebraMap K _ (((tateDataX O hO hs h12).π : K) ^ 2 * b₆') ∧
      y₂ ^ 2 + x₂ * y₂ = x₂ ^ 3 + algebraMap K _ (((tateDataX O hO hs h12).π : K) ^ 2 * b₄') * x₂ +
          algebraMap K _ (((tateDataX O hO hs h12).π : K) ^ 2 * b₆') ∧
      (x₁ - algebraMap K _ (((tateDataX O hO hs h12).π : K) * ε)) *
          (x₂ - algebraMap K _ (((tateDataX O hO hs h12).π : K) * ε)) =
        algebraMap K _ (((tateDataX O hO hs h12).π : K) ^ 2 * γ) ∧
      (2 * y₂ + x₂) * (x₁ - algebraMap K _ (((tateDataX O hO hs h12).π : K) * ε)) +
        (2 * y₁ + x₁) * (x₂ - algebraMap K _ (((tateDataX O hO hs h12).π : K) * ε)) = 0 ∧
      (2 * y₁ + x₁) * (2 * y₂ + x₂) + algebraMap K _ (((tateDataX O hO hs h12).π : K) ^ 2 * γ) *
          (4 * (x₁ + x₂) + algebraMap K _ (4 * ((tateDataX O hO hs h12).π : K) * ε + 1)) = 0 ∧
      algebraMap (DX t).R _ (tateDataX O hO hs h12).x =
        x₁ + x₂ - algebraMap K _ (((tateDataX O hO hs h12).π : K) * ε) ∧
      algebraMap (DX t).R _ (tateDataX O hO hs h12).y =
        y₁ + y₂ + algebraMap K _ (((tateDataX O hO hs h12).π : K) * κ) ∧
      b₆' ∈ IsLocalRing.maximalIdeal O ∧ ε ∈ IsLocalRing.maximalIdeal O ∧ IsUnit γ ∧
      ∀ φ φ' : (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
        (isOpen_levelQN h2 h12 hs 0)).R →ₐ[(DX t).R] Ω,
        φ' = φ ∨ (φ' x₁ = φ x₂ ∧ φ' y₁ = φ y₂ ∧ φ' x₂ = φ x₁ ∧ φ' y₂ = φ y₁) := by
  obtain ⟨b₄', b₆', ε, γ, κ, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ :=
    exists_fourGonInput_rels h2 h12 hs O hO
  exact ⟨b₄', b₆', ε, γ, κ, x₁R h2 h12 hs, y₁R h2 h12 hs, x₂R h2 h12 hs, y₂R h2 h12 hs,
    e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, fun φ φ' => fourGon_fibre h2 h12 hs φ φ'⟩

/-- **(Z_2) = `ZM 0`** (TFGD run 6; formerly a named hypothesis of
`exists_thetaClassTemp_prop13`): `Π^tp_Y ≤ Π^tp_{K(E_{q²})}` for every base point `V` over `O`.
The model data (`exists_fourGonInput`) give `FourGon.Input`; the object `Z` over `X₀` and the
cover (`FourGon.exists_object`, tfg: the `4`-gon model of `E_{q²}` in `ℙ⁴_O` and its
`ℤ`-covering) gives the inclusion by `piY_le_range_of_hom`. -/
theorem zM_zero (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
    (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) :
    ZM h2 h12 O hO hs 0 V hV := by
  obtain ⟨b₄', b₆', ε, γ, κ, x₁, y₁, x₂, y₂, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, hfib⟩ :=
    exists_fourGonInput h2 h12 hs O hO
  have two_unit : IsUnit (2 : O) :=
    isUnit_of_norm_eq_one O hO (x := 2) (by
      have e : ((2 : O) : K) = 2 := map_ofNat O.subtype 2
      rw [e]; exact h2)
  let I : FourGon.Input O (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs 0)
      (isOpen_levelQN h2 h12 hs 0)).R (tateDataX O hO hs h12) :=
    ⟨b₄', b₆', ε, γ, κ, x₁, y₁, x₂, y₂, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, two_unit⟩
  obtain ⟨Z, a, b, z₀, ha, hb, hinj⟩ :=
    FourGon.exists_object (A := (DX t).A) I V hV fun φ φ' => hfib φ φ'
  exact piY_le_range_of_hom (tateDataX O hO hs h12) V hV
    (muL (transcendental_tau t.tateCurve) (hemiL_open t) (levelQN h2 h12 hs 0)
      (isOpen_levelQN h2 h12 hs 0)) a b z₀ ha hb hinj

end Fibre

end Iut.EtaleTheta
