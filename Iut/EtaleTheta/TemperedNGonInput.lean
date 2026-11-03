/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.TemperedFourGonInput
import TemperedFundamentalGroups.Andre.TateNGonCover
import TateCurvesTheta.TateCurve.SphereBounds
import Iut.EtaleTheta.TemperedGammaConst
import Iut.EtaleTheta.TemperedCoeffNorms
import Iut.EtaleTheta.TemperedBlockIntegral
import Iut.EtaleTheta.TemperedLevelAut

/-!
# The `ℙ^{2N}`-model input of `E_{q^N}` for (Z_{N_j}) = `ZM j` (TFGD run 8)

Let `s² = q`, `n = N_j = 2(j+1)`, `tB hs n` the Tate parameter `q^n = s^{2n}` of `E_{q^n}`. This
file provides the Tate-series side of the explicit `2n`-gon model of `E_{q^n} → E_q`
(`TFGD-plan.md`, runs 6–7; tfg `NGon.Input`):

* **Vélu = series splitting mod `n`** (`veluN_X`, `veluN_Y`): splitting the Tate series of `E_q`
  by residues mod `n` gives `X_q(v) = Σ_{i<n} X_{q^n}(v qⁱ) + c` and the same for `Y`;
* **translation by `D = P(q^d)`** on `E_{q^n}` (`addD_rels`, `tate_pair_rels`): three bilinear
  relations between `P` and `P + D` whose reductions are the patterns of `NGon.RedCoeffs`;
* the norm estimates of the coefficients;
* the `Ω`-level input and the fibre property, and `zM j` for every `j`.
-/

open Polynomial

noncomputable section

set_option linter.unusedSectionVars false

universe u

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine

/-! ### Splitting sums over `ℤ` by residues mod `n` -/

section Split

variable {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [T2Space M]

theorem tsum_int_split (n : ℕ) [NeZero n] {f : ℤ → M} (hf : Summable f) :
    ∑' m, f m = ∑ i : Fin n, ∑' m : ℤ, f (m * n + i) := by
  set e : Fin n × ℤ ≃ ℤ := (Equiv.prodComm (Fin n) ℤ).trans (Int.divModEquiv n).symm with he
  have hf' : Summable (fun p : Fin n × ℤ => f (e p)) := e.summable_iff.2 hf
  rw [← e.tsum_eq, hf'.tsum_prod' (fun b => hf'.prod_factor b), tsum_fintype]
  rfl

end Split

/-! ### Vélu for `E_{q^n} → E_q`, `v ↦ v`: splitting the Tate series mod `n` -/

section VeluN

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K} {s : Kˣ} (hs : s ^ 2 = t.q) (n : ℕ) [NeZero n]

/-- The Tate parameter `q^n = s^{2n}` of `E_{q^n}`. -/
abbrev tB : TateParameter K := sqrtPow hs (2 * n) (by have := NeZero.pos n; omega)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem tB_q : (tB hs n).q = s ^ (2 * n) := sqrtPow_q _ _ _

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem unit_split (m : ℤ) (i : ℕ) (v : Kˣ) :
    t.q ^ (m * n + i) * v = (tB hs n).q ^ m * (v * s ^ (2 * i)) := by
  rw [tB_q, ← hs, mul_comm v, ← mul_assoc]
  congr 1
  rw [← zpow_natCast s (2 * n), ← zpow_natCast s (2 * i), ← zpow_natCast s 2, ← zpow_mul,
    ← zpow_mul, ← zpow_add]
  congr 1
  push_cast
  ring

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem val_unit_split (m : ℤ) (i : ℕ) (v : Kˣ) :
    (t.q : K) ^ (m * n + i) * (v : K) =
      ((tB hs n).q : K) ^ m * ((v * s ^ (2 * i) : Kˣ) : K) := by
  have := congrArg (fun w : Kˣ => (w : K)) (unit_split hs n m i v)
  simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val] using this

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem Xterm_split (v : Kˣ) (m : ℤ) (i : ℕ) :
    t.Xterm v (m * n + i) = (tB hs n).Xterm (v * s ^ (2 * i)) m := by
  simp only [Xterm_apply, val_unit_split hs n]

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem Yterm_split (v : Kˣ) (m : ℤ) (i : ℕ) :
    t.Yterm v (m * n + i) = (tB hs n).Yterm (v * s ^ (2 * i)) m := by
  simp only [Yterm_apply, val_unit_split hs n]

include hs in
/-- **Vélu, `x`** (series splitting mod `n`):
`X_q(v) = Σ_{i<n} X_{q^n}(v·q^i) + (2n·s₁(q^n) − 2s₁(q))`. -/
theorem veluN_X (v : Kˣ) :
    t.X v = ∑ i : Fin n, (tB hs n).X (v * s ^ (2 * (i : ℕ))) +
      (2 * n * (tB hs n).eisenstein 1 - 2 * t.eisenstein 1) := by
  rw [X_apply, tsum_int_split n (t.Xterm_summable v)]
  simp only [Xterm_split hs n, X_apply, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

include hs in
/-- **Vélu, `y`** (series splitting mod `n`):
`Y_q(v) = Σ_{i<n} Y_{q^n}(v·q^i) + (s₁(q) − n·s₁(q^n))`. -/
theorem veluN_Y (v : Kˣ) :
    t.Y v = ∑ i : Fin n, (tB hs n).Y (v * s ^ (2 * (i : ℕ))) +
      (t.eisenstein 1 - n * (tB hs n).eisenstein 1) := by
  rw [Y_apply, tsum_int_split n (t.Yterm_summable v)]
  simp only [Yterm_split hs n, Y_apply, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end VeluN

/-! ### Translation by a point `D`: the bilinear relations between `P` and `P + D` -/

/-- **Translation by a point `D = (x_D, y_D)`, algebraically** (`2D ≠ O` not needed): for
`P = (x, y)` on `y² + xy = x³ + a₄x + a₆` with `x ≠ x_D` and `P + D = (x', y')` given by the chord
slope `ℓ`, the relations `R1`, `R2`, `R3` of `TFGD-plan.md` (run 7, A-type) hold. -/
theorem addD_rels {F : Type*} [Field F] {a₄ a₆ x y e f x' y' ℓ : F} (hd : x - e ≠ 0)
    (E₁ : y ^ 2 + x * y = x ^ 3 + a₄ * x + a₆) (ED : f ^ 2 + e * f = e ^ 3 + a₄ * e + a₆)
    (hℓ : y = ℓ * (x - e) + f) (hx' : x' = ℓ ^ 2 + ℓ - x - e)
    (hy' : y' = -(ℓ * (x' - x) + y) - x') :
    x * x' + x * y' + y * x' - (e + f) * x' - e * y' + f * x - e * y = 0 ∧
    -(a₄ ^ 2 + 5 * a₄ * e ^ 2 + a₄ * e + 6 * e ^ 4 + e ^ 3 - 6 * e ^ 2 * f - 6 * e * f ^ 2 -
        e * f - f ^ 2) + (-a₄ * e - 3 * e ^ 3 + 2 * e * f + 2 * f ^ 2) * x' +
      (-a₄ * e - 3 * e ^ 3 + 3 * e * f + 4 * f ^ 2) * x + (a₄ + 3 * e ^ 2 + e + f) * x * x' -
      e * (e + 2 * f) * y + (e + 2 * f) * y * x' = 0 ∧
    y * y' + 3 * e * x * x' + (a₄ + e + f) * x' + (e + f) * y' + (a₄ - f) * x - f * y +
      (-2 * a₄ * e - 3 * e ^ 3 + 3 * e * f + 3 * f ^ 2) = 0 := by
  subst hy' hx' hℓ
  have key : (x - e) * (-a₄ + ℓ ^ 2 * x - ℓ ^ 2 * e + ℓ * x + 2 * ℓ * f - x ^ 2 - x * e -
      e ^ 2 + f) = 0 := by
    linear_combination E₁ - ED
  have k' := (mul_eq_zero.1 key).resolve_left hd
  refine ⟨by ring, ?_, ?_⟩
  · linear_combination (a₄ + ℓ * e + 2 * ℓ * f + 3 * e ^ 2 + e + f) * k'
  · linear_combination (-ℓ ^ 2 - ℓ + 3 * e) * k'

/-- **Translation by a `2`-torsion point, the `y y'` form**: for `(x₁, y₁)`,
`(x₂, y₂) = P + T` as in `addT_rels` (`T = (e, -e/2)`),
`B_YY = y₁y₂ + t(y₁ + y₂) + C(x₁ + x₂) + 2a₄t + 24t³ + 3t² = 0` (`t = e/2`,
`C = 3e² + a₄ + e/2`), and `B2 = x₁x₂ + x₁y₂ + y₁x₂ − t(x₁ + x₂) − 2t(y₁ + y₂) = 0`. -/
theorem addT_rels' {F : Type*} [Field F] [CharZero F] {a₄ a₆ x₁ y₁ e x₂ y₂ ℓ : F}
    (hd : x₁ - e ≠ 0) (E₁ : y₁ ^ 2 + x₁ * y₁ = x₁ ^ 3 + a₄ * x₁ + a₆)
    (ET : (-e / 2) ^ 2 + e * (-e / 2) = e ^ 3 + a₄ * e + a₆)
    (hℓ : y₁ = ℓ * (x₁ - e) - e / 2) (hx₂ : x₂ = ℓ ^ 2 + ℓ - x₁ - e)
    (hy₂ : y₂ = -(ℓ * (x₂ - x₁) + y₁) - x₂) :
    (x₁ - e) * (x₂ - e) - (3 * e ^ 2 + a₄ + e / 2) = 0 ∧
    x₁ * x₂ + x₁ * y₂ + y₁ * x₂ - e / 2 * (x₁ + x₂) - 2 * (e / 2) * (y₁ + y₂) = 0 ∧
    y₁ * y₂ + e / 2 * (y₁ + y₂) + (3 * e ^ 2 + a₄ + e / 2) * (x₁ + x₂) +
      (2 * a₄ * (e / 2) + 24 * (e / 2) ^ 3 + 3 * (e / 2) ^ 2) = 0 := by
  obtain ⟨r1, r2, r3⟩ := addT_rels hd E₁ ET hℓ hx₂ hy₂
  refine ⟨by linear_combination r1, by linear_combination (1 / 2 : F) * r2, ?_⟩
  linear_combination (1 / 4 : F) * r3 - (1 / 4 : F) * r2 + (1 / 4 : F) * r1

/-! ### The coefficient matrices of the pair relations -/

section BilK

variable {F : Type*} [CommRing F]

/-- The bilinear form `Σ_{a,b} c_{ab} u_a u'_b` in `u = (1, x, y)`, `u' = (1, x', y')`. -/
def bilK (c : Fin 3 → Fin 3 → F) (x y x' y' : F) : F :=
  ∑ a, ∑ b, c a b * ![1, x, y] a * ![1, x', y'] b

lemma bilK_eq (c : Fin 3 → Fin 3 → F) (x y x' y' : F) :
    bilK c x y x' y' = c 0 0 + c 0 1 * x' + c 0 2 * y' + c 1 0 * x + c 1 1 * x * x' +
      c 1 2 * x * y' + c 2 0 * y + c 2 1 * y * x' + c 2 2 * y * y' := by
  simp only [bilK, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

lemma bilK_sub (c c' : Fin 3 → Fin 3 → F) (x y x' y' : F) :
    bilK (c - c') x y x' y' = bilK c x y x' y' - bilK c' x y x' y' := by
  simp only [bilK_eq, Pi.sub_apply]
  ring

lemma bilK_zero (x y x' y' : F) : bilK (0 : Fin 3 → Fin 3 → F) x y x' y' = 0 := by
  simp [bilK_eq]

lemma map_bilK {G : Type*} [CommRing G] (f : F →+* G) (c : Fin 3 → Fin 3 → F) (x y x' y' : F) :
    f (bilK c x y x' y') = bilK (fun a b => f (c a b)) (f x) (f y) (f x') (f y') := by
  simp only [bilK_eq, map_add, map_mul]

/-- The transposed form: `bilK c` of `(u, u')` is `bilK cᵀ` of `(u', u)`. -/
lemma bilK_swap (c : Fin 3 → Fin 3 → F) (x y x' y' : F) :
    bilK c x y x' y' = bilK (fun a b => c b a) x' y' x y := by
  simp only [bilK_eq]
  ring

end BilK


/-- **The A-type relations on values**: `R1`, `R2/δ`, `R3` between `P` and `P + D`. -/
theorem pairA_rels {F : Type*} [Field F] {a₄ a₆ x y e f x' y' ℓ : F} (hd : x - e ≠ 0)
    (hδ : e + 2 * f ≠ 0)
    (E₁ : y ^ 2 + x * y = x ^ 3 + a₄ * x + a₆) (ED : f ^ 2 + e * f = e ^ 3 + a₄ * e + a₆)
    (hℓ : y = ℓ * (x - e) + f) (hx' : x' = ℓ ^ 2 + ℓ - x - e)
    (hy' : y' = -(ℓ * (x' - x) + y) - x') :
    bilK (matR1 e f) x y x' y' = 0 ∧ bilK (matR2 a₄ e f) x y x' y' = 0 ∧
      bilK (matR3 a₄ e f) x y x' y' = 0 := by
  obtain ⟨r1, r2, r3⟩ := addD_rels hd E₁ ED hℓ hx' hy'
  refine ⟨?_, ?_, ?_⟩
  · rw [bilK_eq]
    simp only [matR1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination r1
  · have e : bilK (matR2 a₄ e f) x y x' y' =
        (-(a₄ ^ 2 + 5 * a₄ * e ^ 2 + a₄ * e + 6 * e ^ 4 + e ^ 3 - 6 * e ^ 2 * f - 6 * e * f ^ 2 -
          e * f - f ^ 2) + (-a₄ * e - 3 * e ^ 3 + 2 * e * f + 2 * f ^ 2) * x' +
        (-a₄ * e - 3 * e ^ 3 + 3 * e * f + 4 * f ^ 2) * x + (a₄ + 3 * e ^ 2 + e + f) * x * x' -
        e * (e + 2 * f) * y + (e + 2 * f) * y * x') * (e + 2 * f)⁻¹ := by
      rw [bilK_eq]
      simp only [matR2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      have : (e + 2 * f) * (e + 2 * f)⁻¹ = 1 := mul_inv_cancel₀ hδ
      linear_combination (e * y - y * x') * this
    rw [e, r2, zero_mul]
  · rw [bilK_eq]
    simp only [matR3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination r3

/-- **The B-type relations on values** (translation by a `2`-torsion point `(e, -e/2)`). -/
theorem pairB_rels {F : Type*} [Field F] [CharZero F] {a₄ a₆ x y e x' y' ℓ : F}
    (hd : x - e ≠ 0) (E₁ : y ^ 2 + x * y = x ^ 3 + a₄ * x + a₆)
    (ET : (-e / 2) ^ 2 + e * (-e / 2) = e ^ 3 + a₄ * e + a₆)
    (hℓ : y = ℓ * (x - e) - e / 2) (hx' : x' = ℓ ^ 2 + ℓ - x - e)
    (hy' : y' = -(ℓ * (x' - x) + y) - x') :
    bilK (matB1 a₄ e) x y x' y' = 0 ∧ bilK (matB2 e) x y x' y' = 0 ∧
      bilK (matBY a₄ e) x y x' y' = 0 := by
  obtain ⟨r1, r2, r3⟩ := addT_rels' hd E₁ ET hℓ hx' hy'
  refine ⟨?_, ?_, ?_⟩
  · rw [bilK_eq]
    simp only [matB1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination r1
  · rw [bilK_eq]
    simp only [matB2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination r2
  · rw [bilK_eq]
    simp only [matBY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination r3

/-! ### The block functions `x_k, y_k ∈ K(E_Q)`, `Q = s^n` (coordinate `U`) -/

section LevelFns

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K} (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)
  (n : ℕ) [NeZero n]

/-- The Tate parameter `s^n` of the level curve `E_Q`, `Q = s^n` (`levelQN`, `n = N_j`). -/
abbrev tL : TateParameter K := sqrtPow hs n (NeZero.pos n)

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem tL_q : (tL hs n).q = s ^ n := sqrtPow_q _ _ _

omit [CompleteSpace K] [IsUltrametricDist K] in
instance isElliptic_tL : (tL hs n).tateCurve.IsElliptic :=
  (tL hs n).tateCurve_isElliptic (by norm_num)

omit [CompleteSpace K] [IsUltrametricDist K] in
instance isElliptic_tB : (tB hs n).tateCurve.IsElliptic :=
  (tB hs n).tateCurve_isElliptic (by norm_num)

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
theorem tL_q_sq : (tL hs n).q ^ 2 = t.q ^ n := by
  rw [tL_q, ← hs, ← pow_mul, ← pow_mul, mul_comm]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
theorem tB_q_eq : (tB hs n).q = t.q ^ n := by
  rw [tB_q, ← hs, ← pow_mul]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
/-- An orbit relation of `T` with `T.q² = q^k` gives one of `t` for the square. -/
theorem offOrbit_of_sq {T : TateParameter K} {k : ℕ} (hT : T.q ^ 2 = t.q ^ k) {U : Kˣ}
    (hU2 : OffOrbit t (U ^ 2)) : OffOrbit T U := by
  intro m h
  apply hU2 (k * m)
  have h' := congrArg (· ^ 2) h
  simp only [one_pow, mul_pow] at h'
  have e : ((T.q : K) ^ m) ^ 2 = (t.q : K) ^ ((k : ℤ) * m) := by
    have := congrArg (fun w : Kˣ => (w : K)) hT
    simp only [Units.val_pow_eq_pow_val] at this
    rw [← zpow_natCast _ 2, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, this,
      ← zpow_natCast _ k, ← zpow_mul]
  rw [← e, Units.val_pow_eq_pow_val]
  exact h'

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
theorem offOrbit_tB_of {v : Kˣ} (hv : OffOrbit t v) : OffOrbit (tB hs n) v := by
  intro m h
  apply hv (n * m)
  rw [tB_q_eq hs n, Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul] at h
  exact h

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
/-- `U² q^k` stays off the `q`-orbit. -/
theorem offOrbit_sq_mul {U w : Kˣ} (hU2 : OffOrbit t (U ^ 2))
    (hw : ∃ k : ℤ, (w : K) ^ 2 = (t.q : K) ^ k) : OffOrbit t ((U * w) ^ 2) := by
  obtain ⟨k, hk⟩ := hw
  intro m h
  apply hU2 (m + k)
  rw [zpow_add₀ t.q.ne_zero, ← hk]
  rw [mul_pow, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h
  rw [Units.val_pow_eq_pow_val]
  linear_combination h

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem cuspElt_sq_val (e : Fin 2) (a : ℕ) :
    ((cuspElt s e a : Kˣ) : K) ^ 2 = (s : K) ^ (2 * a) := by
  simp only [cuspElt, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    mul_pow, ← pow_mul]
  rw [mul_comm (e : ℕ) 2, pow_mul, neg_one_sq, one_pow, one_mul, mul_comm]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
theorem cuspElt_sq_q (e : Fin 2) (a : ℕ) :
    ∃ k : ℤ, ((cuspElt s e a : Kˣ) : K) ^ 2 = (t.q : K) ^ k :=
  ⟨a, by rw [cuspElt_sq_val, val_q_eq hs, zpow_natCast, ← pow_mul]⟩

include hs h2 h12 in
/-- `X_Q(U) ≠ X_Q(w)` for `U² ∉ qᶻ` and `w² ∈ qᶻ`. -/
theorem tL_X_ne {U w : Kˣ} (hU : OffOrbit (tL hs n) U) (hw : OffOrbit (tL hs n) w)
    (hU2 : OffOrbit t (U ^ 2)) (hw2 : ∃ k : ℤ, (w : K) ^ 2 = (t.q : K) ^ k) :
    (tL hs n).X U ≠ (tL hs n).X w := by
  intro hX
  obtain ⟨k, hk⟩ := hw2
  have hQ : ((tL hs n).q : K) ^ 2 = (t.q : K) ^ n := by
    have := congrArg (fun w : Kˣ => (w : K)) (tL_q_sq hs n)
    simpa only [Units.val_pow_eq_pow_val] using this
  have hQm : ∀ m : ℤ, (((tL hs n).q : K) ^ m) ^ 2 = (t.q : K) ^ ((n : ℤ) * m) := fun m => by
    rw [← zpow_natCast _ 2, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hQ, ← zpow_natCast _ n,
      ← zpow_mul]
  have hw0 : (w : K) ≠ 0 := w.ne_zero
  have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
  obtain ⟨m, hm | hm⟩ := zpow_of_X_eq h12 h2 hU hw hX
  · apply hU2 (-((n : ℤ) * m + k))
    rw [Units.val_pow_eq_pow_val, hm, mul_pow, hQm, hk, ← zpow_add₀ hq0, ← zpow_add₀ hq0]
    ring_nf
    exact zpow_zero _
  · apply hU2 (-((n : ℤ) * m - k))
    rw [Units.val_pow_eq_pow_val, hm, mul_pow, hQm, inv_pow, hk, ← zpow_neg, ← zpow_add₀ hq0,
      ← zpow_add₀ hq0]
    ring_nf
    exact zpow_zero _

theorem hasTateValue_of_eq {T : TateParameter K} {g : TateField T} {u u' : Kˣ} (h : u = u')
    {hu : OffOrbit T u} {hu' : OffOrbit T u'} {v : K} (hv : HasTateValue T h12 g hu v) :
    HasTateValue T h12 g hu' v := by
  subst h
  exact hv

omit [CharZero K] in
/-- **The identity principle on good points** `U` (`U² ∉ qᶻ`) of `E_Q`, `Q = s^n`. -/
theorem eq_of_goodN {a b : TateField (tL hs n)} {A : Kˣ → K}
    (ha : ∀ (U : Kˣ) (hU : OffOrbit (tL hs n) U), OffOrbit t (U ^ 2) →
      HasTateValue (tL hs n) h12 a hU (A U))
    (hb : ∀ (U : Kˣ) (hU : OffOrbit (tL hs n) U), OffOrbit t (U ^ 2) →
      HasTateValue (tL hs n) h12 b hU (A U)) : a = b := by
  have good : ∀ (U : Kˣ) (hU : OffOrbit (tL hs n) U),
      evalTate (tL hs n) h12 hU (mkT (tL hs n) (C (badPoly (tL hs n) s n))) ≠ 0 →
      OffOrbit t (U ^ 2) := by
    intro U hU h0
    by_contra h
    exact h0 (by
      rw [evalTate_mk_C]
      exact badPoly_eval_eq_zero hs (NeZero.pos n) (tL_q hs n) h)
  exact eq_of_hasTateValue (h12 := h12) (mkT_C_ne_zero h12 badPoly_ne_zero) (G := A)
    (fun U hU h0 => ha U hU (good U hU h0)) (fun U hU h0 => hb U hU (good U hU h0))

include h2 hs in
/-- **Values of `baseAut`**: the value of `t_w g` (`w = (-1)^e s^a`) at `U` is the value of `g`
at `U·w`. -/
theorem hasTateValue_baseAut {g : TateField (tL hs n)} (e : Fin 2) (a : Fin n) {U : Kˣ}
    (hU : OffOrbit (tL hs n) U) (hU2 : OffOrbit t (U ^ 2)) {v : K}
    (hg : ∀ hUc : OffOrbit (tL hs n) (U * cuspElt s e a), HasTateValue (tL hs n) h12 g hUc v) :
    HasTateValue (tL hs n) h12
      (baseAut (rfl : (tL hs n).q = s ^ n) (NeZero.pos n) h12 e a g) hU v := by
  have hUc2 := offOrbit_sq_mul hU2 (cuspElt_sq_q hs e a)
  have hUc : OffOrbit (tL hs n) (U * cuspElt s e a) := offOrbit_of_sq (tL_q_sq hs n) hUc2
  unfold baseAut
  split_ifs with h
  · obtain ⟨he, ha⟩ := Prod.mk.inj h
    have e1 : U * cuspElt s e a = U := by
      simp only [cuspElt, he, ha, Fin.val_zero, pow_zero, mul_one]
    exact hasTateValue_of_eq h12 e1 (hg hUc)
  · have hw := offOrbit_cuspElt (rfl : (tL hs n).q = s ^ n) (NeZero.pos n) a.2 h
    exact hasTateValue_trans h2 hU hw hUc
      (tL_X_ne h2 h12 hs n hU hw hU2 (cuspElt_sq_q hs e a)) g v (hg hUc)

/-- **The shifted functions** `t_{s^k} g` (`k ∈ ℤ/n`). -/
def shiftN (g : TateField (tL hs n)) (k : ZMod n) : TateField (tL hs n) :=
  baseAut (rfl : (tL hs n).q = s ^ n) (NeZero.pos n) h12 0 ⟨k.val, k.val_lt⟩ g

include h2 in
theorem hasTateValue_shiftN {g : TateField (tL hs n)} {Φ : Kˣ → K}
    (hg : ∀ (U : Kˣ) (hU : OffOrbit (tL hs n) U), OffOrbit t (U ^ 2) →
      HasTateValue (tL hs n) h12 g hU (Φ (U ^ 2)))
    (k : ZMod n) (U : Kˣ) (hU : OffOrbit (tL hs n) U) (hU2 : OffOrbit t (U ^ 2)) :
    HasTateValue (tL hs n) h12 (shiftN h12 hs n g k) hU (Φ (U ^ 2 * s ^ (2 * k.val))) :=
  hasTateValue_baseAut h2 h12 hs n 0 ⟨k.val, k.val_lt⟩ hU hU2 fun hUc =>
    (hg _ hUc (offOrbit_sq_mul hU2 (cuspElt_sq_q hs 0 k.val))).congr (by
      congr 1
      apply Units.ext
      rw [mul_pow, Units.val_mul]
      simp only [Units.val_pow_eq_pow_val]
      rw [cuspElt_sq_val]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val])

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
/-- `s^{2i}` and `s^{2j}` differ by a power of `q^n` when `i ≡ j mod n`. -/
theorem spow_period (V : Kˣ) {i j : ℕ} (h : i % n = j % n) :
    V * s ^ (2 * i) = (tB hs n).q ^ (((i : ℤ) - j) / n) * (V * s ^ (2 * j)) := by
  have hd : (n : ℤ) ∣ (i : ℤ) - j := Nat.modEq_iff_dvd.1 h.symm
  obtain ⟨c, hc⟩ := hd
  have hn0 : (n : ℤ) ≠ 0 := by have := NeZero.ne n; exact_mod_cast this
  rw [hc, Int.mul_ediv_cancel_left _ hn0, tB_q, mul_comm V, mul_comm V, ← mul_assoc]
  congr 1
  rw [← zpow_natCast s (2 * n), ← zpow_natCast s (2 * i), ← zpow_natCast s (2 * j), ← zpow_mul,
    ← zpow_add]
  congr 1
  push_cast
  linear_combination 2 * hc

include h2 in
/-- **Translations of the shifted functions**: `t_w (t_{s^k} g) = t_{s^{k+a}} g` for
`w = (-1)^e s^a`, if `g` has the `q^n`-periodic values `Φ(U²)`. -/
theorem baseAut_shiftN {g : TateField (tL hs n)} {Φ : Kˣ → K}
    (hΦ : ∀ (m : ℤ) (V : Kˣ), Φ ((tB hs n).q ^ m * V) = Φ V)
    (hg : ∀ (U : Kˣ) (hU : OffOrbit (tL hs n) U), OffOrbit t (U ^ 2) →
      HasTateValue (tL hs n) h12 g hU (Φ (U ^ 2)))
    (e : Fin 2) (a : Fin n) (k : ZMod n) :
    baseAut (rfl : (tL hs n).q = s ^ n) (NeZero.pos n) h12 e a (shiftN h12 hs n g k) =
      shiftN h12 hs n g (k + (a : ℕ)) := by
  have hper : ∀ (V : Kˣ) {i j : ℕ}, i % n = j % n →
      Φ (V * s ^ (2 * i)) = Φ (V * s ^ (2 * j)) := fun V i j h => by
    rw [spow_period hs n V h, hΦ]
  refine eq_of_goodN h12 hs n (A := fun U => Φ (U ^ 2 * s ^ (2 * (k + (a : ℕ) : ZMod n).val)))
    (fun U hU hU2 => ?_) (fun U hU hU2 => hasTateValue_shiftN h2 h12 hs n hg _ U hU hU2)
  refine hasTateValue_baseAut h2 h12 hs n e a hU hU2 fun hUc => ?_
  refine (hasTateValue_shiftN h2 h12 hs n hg k _ hUc
    (offOrbit_sq_mul hU2 (cuspElt_sq_q hs e a))).congr ?_
  have e1 : (U * cuspElt s e a) ^ 2 * s ^ (2 * k.val) = U ^ 2 * s ^ (2 * (k.val + a.val)) := by
    apply Units.ext
    rw [mul_pow, Units.val_mul, Units.val_mul, Units.val_mul]
    simp only [Units.val_pow_eq_pow_val]
    rw [cuspElt_sq_val]
    ring
  rw [e1]
  refine hper _ ?_
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, Nat.mod_mod]

end LevelFns

/-! ### The pair relations on Tate values of `E_{q^n}` -/

section TatePairs

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0)

omit [CharZero K] in
include h2 h12 in
/-- **The A-type relations on Tate values**: `R1`, `R2/δ`, `R3` between `P(u)` and
`P(u·w) = P(u) + P(w)`. -/
theorem tate_pairA (T : TateParameter K) {u w : Kˣ} (hu : OffOrbit T u) (hw : OffOrbit T w)
    (huw : OffOrbit T (u * w)) (hx : T.X u ≠ T.X w) (hδ : T.X w + 2 * T.Y w ≠ 0) :
    bilK (matR1 (T.X w) (T.Y w)) (T.X u) (T.Y u) (T.X (u * w)) (T.Y (u * w)) = 0 ∧
    bilK (matR2 T.a₄ (T.X w) (T.Y w)) (T.X u) (T.Y u) (T.X (u * w)) (T.Y (u * w)) = 0 ∧
    bilK (matR3 T.a₄ (T.X w) (T.Y w)) (T.X u) (T.Y u) (T.X (u * w)) (T.Y (u * w)) = 0 := by
  have hd : T.X u - T.X w ≠ 0 := sub_ne_zero.2 hx
  obtain ⟨eX, eY⟩ := tate_mul_coords h12 h2 hu hw huw hx
  refine pairA_rels hd hδ (tate_eq_of h12 hu) (tate_eq_of h12 hw)
    (ℓ := (T.Y u - T.Y w) / (T.X u - T.X w)) ?_ ?_ ?_
  · rw [div_mul_cancel₀ _ hd]; ring
  · rw [eX]; simp only [addX, tateCurve_a₁, tateCurve_a₂]; ring
  · rw [eY, eX]; simp only [addY, negY, negAddY, tateCurve_a₁, tateCurve_a₃]; ring

omit [CharZero K] in
/-- A point `w` with `w² = Q` is `2`-torsion: `2Y(w) + X(w) = 0`. -/
theorem two_mul_Y_add_X (T : TateParameter K) {w : Kˣ} (hw : OffOrbit T w)
    (hw2 : w * w = T.q) : 2 * T.Y w + T.X w = 0 := by
  have hY := T.Y_inv hw
  have e : w⁻¹ = T.q ^ (-1 : ℤ) * w := by
    rw [← hw2, zpow_neg_one, mul_inv, mul_assoc, inv_mul_cancel, mul_one]
  rw [e, Y_zpow_mul] at hY
  linear_combination hY

include h2 h12 in
/-- **The B-type relations on Tate values** (translation by a `2`-torsion point `P(w)`). -/
theorem tate_pairB (T : TateParameter K) {u w : Kˣ} (hu : OffOrbit T u) (hw : OffOrbit T w)
    (huw : OffOrbit T (u * w)) (hx : T.X u ≠ T.X w) (hw2 : w * w = T.q) :
    bilK (matB1 T.a₄ (T.X w)) (T.X u) (T.Y u) (T.X (u * w)) (T.Y (u * w)) = 0 ∧
    bilK (matB2 (T.X w)) (T.X u) (T.Y u) (T.X (u * w)) (T.Y (u * w)) = 0 ∧
    bilK (matBY T.a₄ (T.X w)) (T.X u) (T.Y u) (T.X (u * w)) (T.Y (u * w)) = 0 := by
  have hd : T.X u - T.X w ≠ 0 := sub_ne_zero.2 hx
  obtain ⟨eX, eY⟩ := tate_mul_coords h12 h2 hu hw huw hx
  have hyT : T.Y w = -T.X w / 2 := by
    linear_combination (1 / 2 : K) * two_mul_Y_add_X T hw hw2
  have ET := tate_eq_of h12 hw
  rw [hyT] at ET
  refine pairB_rels hd (tate_eq_of h12 hu) ET
    (ℓ := (T.Y u - T.Y w) / (T.X u - T.X w)) ?_ ?_ ?_
  · rw [div_mul_cancel₀ _ hd, hyT]; ring
  · rw [eX]; simp only [addX, tateCurve_a₁, tateCurve_a₂]; ring
  · rw [eY, eX]; simp only [addY, negY, negAddY, tateCurve_a₁, tateCurve_a₃]; ring

end TatePairs

/-! ### The block functions and their relations in `K(E_Q)` -/

section Blocks

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K} (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)
  (n : ℕ) [NeZero n]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem zpow_q_eq_one {k : ℤ} (h : (t.q : K) ^ k = 1) : k = 0 := by
  have h' := congrArg norm h
  rw [norm_zpow, norm_one] at h'
  exact (zpow_eq_one_iff_right₀ (norm_nonneg _) t.norm_lt_one.ne).1 h'

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
theorem val_spow (k : ℕ) : ((s ^ (2 * k) : Kˣ) : K) = (t.q : K) ^ (k : ℤ) := by
  rw [Units.val_pow_eq_pow_val, val_q_eq hs, zpow_natCast, pow_mul]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem offOrbit_mul_q {v : Kˣ} (hv : OffOrbit t v) {w : Kˣ} {k : ℤ}
    (hw : (w : K) = (t.q : K) ^ k) : OffOrbit t (v * w) := by
  intro m h
  apply hv (m + k)
  rw [zpow_add₀ t.q.ne_zero, ← hw]
  rw [Units.val_mul] at h
  linear_combination h

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
theorem val_tB_zpow (m : ℤ) : ((tB hs n).q : K) ^ m = (t.q : K) ^ ((n : ℤ) * m) := by
  rw [tB_q_eq hs n, Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
/-- `q^d` (`0 < d < n`) is off the orbit `q^{nℤ}`. -/
theorem offOrbit_tB_spow {d : ℕ} (hd0 : 0 < d) (hdn : d < n) :
    OffOrbit (tB hs n) (s ^ (2 * d)) := by
  intro m h
  rw [val_tB_zpow hs n, val_spow hs, ← zpow_add₀ t.q.ne_zero] at h
  have := zpow_q_eq_one h
  have : (n : ℤ) * m = -d := by linarith
  rcases lt_trichotomy m 0 with hm | hm | hm
  · nlinarith
  · subst hm; simp at this; omega
  · nlinarith

include h2 h12 hs in
/-- `X_{q^n}(v) ≠ X_{q^n}(q^d)` for `v ∉ qᶻ`, `0 < d < n`. -/
theorem tB_X_ne {v : Kˣ} (hv : OffOrbit t v) {d : ℕ} (hd0 : 0 < d) (hdn : d < n) :
    (tB hs n).X v ≠ (tB hs n).X (s ^ (2 * d)) := by
  intro hX
  have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
  obtain ⟨m, hm | hm⟩ := zpow_of_X_eq h12 h2 (offOrbit_tB_of hs n hv)
    (offOrbit_tB_spow hs n hd0 hdn) hX
  · apply hv (-((n : ℤ) * m + d))
    rw [hm, val_tB_zpow hs n, val_spow hs, ← mul_assoc, ← zpow_add₀ hq0, ← zpow_add₀ hq0]
    ring_nf
    exact zpow_zero _
  · apply hv (-((n : ℤ) * m - d))
    rw [hm, val_tB_zpow hs n, val_spow hs, ← zpow_neg, ← mul_assoc, ← zpow_add₀ hq0,
      ← zpow_add₀ hq0]
    ring_nf
    exact zpow_zero _

omit [CharZero K] in
include hs in
/-- **The functions `x_0, y_0` on `E_Q`** with values `X_{q^n}(U²)`, `Y_{q^n}(U²)` (the isogeny
`E_Q → E_{q^n}`, `U ↦ U²`). -/
theorem exists_xy0 : ∃ f g : TateField (tL hs n), ∀ (U : Kˣ) (hU : OffOrbit (tL hs n) U),
    OffOrbit t (U ^ 2) → HasTateValue (tL hs n) h12 f hU ((tB hs n).X (U ^ 2)) ∧
      HasTateValue (tL hs n) h12 g hU ((tB hs n).Y (U ^ 2)) := by
  have e1 : (s ^ n) ^ 2 = (tB hs n).q := by rw [tB_q, ← pow_mul, mul_comm]
  have e2 : (tL hs n).q = (s ^ n) ^ 1 := by rw [tL_q, pow_one]
  have e3 : (tL hs n).q ^ 2 = (tB hs n).q ^ 1 := by rw [tL_q, tB_q, pow_one, ← pow_mul, mul_comm]
  obtain ⟨P₁, Q₁, P₂, Q₂, hR⟩ := exists_poly_isogenyX (tB hs n) e1 one_pos (tL hs n) e2 h12
  obtain ⟨C₁, E₁, C₂, E₂, hRy⟩ := exists_poly_isogenyY_one e3 h12
  exact ⟨_, _, fun U hU hU2 => ⟨hasTateValue_R (h12 := h12) hR hU (offOrbit_tB_of hs n hU2),
    hasTateValue_Ry h12 hRy hU (offOrbit_tB_of hs n hU2)⟩⟩

/-- `x_0` (see `exists_xy0`). -/
def x0N : TateField (tL hs n) := (exists_xy0 h12 hs n).choose

/-- `y_0` (see `exists_xy0`). -/
def y0N : TateField (tL hs n) := (exists_xy0 h12 hs n).choose_spec.choose

/-- **The block functions** `x_k = t_{s^k} x_0` (values `X_{q^n}(U² q^k)`). -/
def blkX (k : ZMod n) : TateField (tL hs n) := shiftN h12 hs n (x0N h12 hs n) k

/-- `y_k = t_{s^k} y_0` (values `Y_{q^n}(U² q^k)`). -/
def blkY (k : ZMod n) : TateField (tL hs n) := shiftN h12 hs n (y0N h12 hs n) k

include h2 in
theorem hasTateValue_xN (k : ZMod n) (U : Kˣ) (hU : OffOrbit (tL hs n) U)
    (hU2 : OffOrbit t (U ^ 2)) :
    HasTateValue (tL hs n) h12 (blkX h12 hs n k) hU ((tB hs n).X (U ^ 2 * s ^ (2 * k.val))) :=
  hasTateValue_shiftN h2 h12 hs n
    (fun U hU hU2 => ((exists_xy0 h12 hs n).choose_spec.choose_spec U hU hU2).1) k U hU hU2

include h2 in
theorem hasTateValue_yN (k : ZMod n) (U : Kˣ) (hU : OffOrbit (tL hs n) U)
    (hU2 : OffOrbit t (U ^ 2)) :
    HasTateValue (tL hs n) h12 (blkY h12 hs n k) hU ((tB hs n).Y (U ^ 2 * s ^ (2 * k.val))) :=
  hasTateValue_shiftN h2 h12 hs n
    (fun U hU hU2 => ((exists_xy0 h12 hs n).choose_spec.choose_spec U hU hU2).2) k U hU hU2

include h2 in
/-- **Translations of the blocks**: `t_w x_k = x_{k+a}`, `t_w y_k = y_{k+a}` (`w = ±s^a`). -/
theorem baseAut_xN (e : Fin 2) (a : Fin n) (k : ZMod n) :
    baseAut (rfl : (tL hs n).q = s ^ n) (NeZero.pos n) h12 e a (blkX h12 hs n k) =
        blkX h12 hs n (k + (a : ℕ)) ∧
      baseAut (rfl : (tL hs n).q = s ^ n) (NeZero.pos n) h12 e a (blkY h12 hs n k) =
        blkY h12 hs n (k + (a : ℕ)) :=
  ⟨baseAut_shiftN h2 h12 hs n (fun m V => X_zpow_mul _ m V)
      (fun U hU hU2 => ((exists_xy0 h12 hs n).choose_spec.choose_spec U hU hU2).1) e a k,
    baseAut_shiftN h2 h12 hs n (fun m V => Y_zpow_mul _ m V)
      (fun U hU hU2 => ((exists_xy0 h12 hs n).choose_spec.choose_spec U hU hU2).2) e a k⟩

omit [CharZero K] in
theorem HasTateValue.finsetSum {T : TateParameter K} {ι : Type*} (S : Finset ι)
    {g : ι → TateField T} {u : Kˣ} {hu : OffOrbit T u} {v : ι → K}
    (h : ∀ i ∈ S, HasTateValue T h12 (g i) hu (v i)) :
    HasTateValue T h12 (∑ i ∈ S, g i) hu (∑ i ∈ S, v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using HasTateValue.const (h12 := h12) hu (0 : K)
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [CharZero K] in
theorem HasTateValue.bilK {T : TateParameter K} (c : Fin 3 → Fin 3 → K)
    {a b a' b' : TateField T} {u : Kˣ} {hu : OffOrbit T u} {X Y X' Y' : K}
    (ha : HasTateValue T h12 a hu X) (hb : HasTateValue T h12 b hu Y)
    (ha' : HasTateValue T h12 a' hu X') (hb' : HasTateValue T h12 b' hu Y') :
    HasTateValue T h12 (bilK (fun i j => algebraMap K (TateField T) (c i j)) a b a' b') hu
      (bilK c X Y X' Y') := by
  rw [bilK_eq, bilK_eq]
  have C : ∀ i j, HasTateValue T h12 (algebraMap K (TateField T) (c i j)) hu (c i j) :=
    fun i j => HasTateValue.const (h12 := h12) hu (c i j)
  have h1 := (C 0 0).add ((C 0 1).mul ha')
  have h2 := (h1.add ((C 0 2).mul hb')).add ((C 1 0).mul ha)
  have h3 := (h2.add (((C 1 1).mul ha).mul ha')).add (((C 1 2).mul ha).mul hb')
  have h4 := (h3.add ((C 2 0).mul hb)).add (((C 2 1).mul hb).mul ha')
  exact h4.add (((C 2 2).mul hb).mul hb')

include h2 in
/-- **Pair relations in `K(E_Q)` from relations on values**: a bilinear relation between
`P(v)` and `P(v·q^d)` on `E_{q^n}` (for all `v ∉ qᶻ`) holds between the blocks `k` and `k + d`. -/
theorem bilK_xN_eq_zero {c : Fin 3 → Fin 3 → K} (k d : ZMod n)
    (hval : ∀ v : Kˣ, OffOrbit t v →
      bilK c ((tB hs n).X v) ((tB hs n).Y v) ((tB hs n).X (v * s ^ (2 * d.val)))
        ((tB hs n).Y (v * s ^ (2 * d.val))) = 0) :
    bilK (fun i j => algebraMap K (TateField (tL hs n)) (c i j)) (blkX h12 hs n k)
      (blkY h12 hs n k) (blkX h12 hs n (k + d)) (blkY h12 hs n (k + d)) = 0 := by
  refine eq_of_goodN h12 hs n (A := fun _ => 0) (fun U hU hU2 => ?_) (fun U hU _ => by
    have := HasTateValue.const (h12 := h12) hU (0 : K)
    rwa [map_zero] at this)
  have hv : OffOrbit t (U ^ 2 * s ^ (2 * k.val)) := offOrbit_mul_q hU2 (val_spow hs k.val)
  obtain ⟨m, e1⟩ : ∃ m : ℤ, U ^ 2 * s ^ (2 * (k + d).val) =
      (tB hs n).q ^ m * (U ^ 2 * s ^ (2 * k.val) * s ^ (2 * d.val)) :=
    ⟨_, by rw [spow_period hs n (U ^ 2) (i := (k + d).val) (j := k.val + d.val)
      (by rw [ZMod.val_add, Nat.mod_mod]), mul_add, pow_add, mul_assoc]⟩
  refine (HasTateValue.bilK h12 c (hasTateValue_xN h2 h12 hs n k U hU hU2)
    (hasTateValue_yN h2 h12 hs n k U hU hU2) (hasTateValue_xN h2 h12 hs n (k + d) U hU hU2)
    (hasTateValue_yN h2 h12 hs n (k + d) U hU hU2)).congr ?_
  rw [e1, X_zpow_mul, Y_zpow_mul]
  exact hval _ hv

end Blocks

/-! ### Norm estimates for the Tate coordinates of `E_{q^n}` at `±q^k` -/

section Estimates

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

omit [CompleteSpace K] in
theorem norm_one_sub_of_lt {w : K} (hw : ‖w‖ < 1) : ‖1 - w‖ = 1 := by
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by
    rw [norm_one, norm_neg]; exact hw.ne'), norm_one, norm_neg, max_eq_left hw.le]

omit [CompleteSpace K] in
/-- `‖u/(1-u)² - u‖ ≤ ‖u‖²` for `‖u‖ < 1`. -/
theorem norm_Xterm_zero_sub_le (T : TateParameter K) {u : Kˣ} (hhi : ‖(u : K)‖ < 1) :
    ‖T.Xterm u 0 - u‖ ≤ ‖(u : K)‖ ^ 2 := by
  rw [Xterm_zero_apply]
  have h1 : ‖1 - (u : K)‖ = 1 := norm_one_sub_of_lt hhi
  have h0 : (1 - (u : K)) ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  rw [show (u : K) / (1 - (u : K)) ^ 2 - u = (u : K) * ((u : K) * (2 - u)) / (1 - (u : K)) ^ 2 by
    field_simp; ring, norm_div, norm_pow, h1, one_pow, div_one, norm_mul, norm_mul, sq]
  refine mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) ?_) (norm_nonneg _)
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact IsUltrametricDist.norm_natCast_le_one K 2 |>.trans_eq' (by norm_cast)
  · rw [norm_neg]; exact hhi.le

/-- **Annulus bound for `X`**: `‖X(u)‖ ≤ max ‖u‖ (‖q‖/‖u‖)` for `‖q‖ < ‖u‖ < 1`. -/
theorem norm_X_le_annulus (T : TateParameter K) {u : Kˣ} (hlo : ‖(T.q : K)‖ < ‖(u : K)‖)
    (hhi : ‖(u : K)‖ < 1) : ‖T.X u‖ ≤ max ‖(u : K)‖ (‖(T.q : K)‖ / ‖(u : K)‖) := by
  have hu0 : 0 < ‖(u : K)‖ := norm_pos_iff.2 u.ne_zero
  have hq : ‖(T.q : K)‖ ≤ ‖(T.q : K)‖ / ‖(u : K)‖ := le_div_self (norm_nonneg _) hu0 hhi.le
  rw [show T.X u = (T.X u - T.Xterm u 0 - T.Xterm u (-1)) + T.Xterm u 0 + T.Xterm u (-1) by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max
    _ _).trans (max_le ?_ ?_)) ?_)
  · exact ((T.norm_X_sub_annulus_le hlo hhi).trans hq).trans (le_max_right _ _)
  · rw [T.norm_Xterm_zero hhi]; exact le_max_left _ _
  · rw [T.norm_Xterm_neg_one hlo]; exact le_max_right _ _

/-- **Annulus bound for `X - u`**: `‖X(u) - u‖ ≤ max ‖u‖² (‖q‖/‖u‖)`. -/
theorem norm_X_sub_le_annulus (T : TateParameter K) {u : Kˣ} (hlo : ‖(T.q : K)‖ < ‖(u : K)‖)
    (hhi : ‖(u : K)‖ < 1) : ‖T.X u - u‖ ≤ max (‖(u : K)‖ ^ 2) (‖(T.q : K)‖ / ‖(u : K)‖) := by
  have hu0 : 0 < ‖(u : K)‖ := norm_pos_iff.2 u.ne_zero
  have hq : ‖(T.q : K)‖ ≤ ‖(T.q : K)‖ / ‖(u : K)‖ := le_div_self (norm_nonneg _) hu0 hhi.le
  rw [show T.X u - u = (T.X u - T.Xterm u 0 - T.Xterm u (-1)) + (T.Xterm u 0 - u) +
    T.Xterm u (-1) by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max
    _ _).trans (max_le ?_ ?_)) ?_)
  · exact ((T.norm_X_sub_annulus_le hlo hhi).trans hq).trans (le_max_right _ _)
  · exact (norm_Xterm_zero_sub_le T hhi).trans (le_max_left _ _)
  · rw [T.norm_Xterm_neg_one hlo]; exact le_max_right _ _

/-- **Annulus bound for `Y`**: `‖Y(u)‖ ≤ max ‖u‖² (‖q‖/‖u‖)`. -/
theorem norm_Y_le_annulus (T : TateParameter K) {u : Kˣ} (hlo : ‖(T.q : K)‖ < ‖(u : K)‖)
    (hhi : ‖(u : K)‖ < 1) : ‖T.Y u‖ ≤ max (‖(u : K)‖ ^ 2) (‖(T.q : K)‖ / ‖(u : K)‖) := by
  have hu0 : 0 < ‖(u : K)‖ := norm_pos_iff.2 u.ne_zero
  have hq : ‖(T.q : K)‖ ≤ ‖(T.q : K)‖ / ‖(u : K)‖ := le_div_self (norm_nonneg _) hu0 hhi.le
  rw [show T.Y u = (T.Y u - T.Yterm u 0 - T.Yterm u (-1)) + T.Yterm u 0 + T.Yterm u (-1) by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max
    _ _).trans (max_le ?_ ?_)) ?_)
  · exact ((T.norm_Y_sub_annulus_le hlo hhi).trans hq).trans (le_max_right _ _)
  · rw [T.norm_Yterm_zero hhi]; exact le_max_left _ _
  · rw [T.norm_Yterm_neg_one hlo]; exact le_max_right _ _

variable {t : TateParameter K} {s : Kˣ} (hs : s ^ 2 = t.q) (n : ℕ) [NeZero n]

omit [CompleteSpace K] in
include hs in
theorem norm_spow (k : ℕ) : ‖((s ^ (2 * k) : Kˣ) : K)‖ = ‖(t.q : K)‖ ^ k := by
  rw [val_spow hs, norm_zpow, zpow_natCast]

omit [CompleteSpace K] in
include hs in
theorem norm_neg_spow (k : ℕ) : ‖((-(s ^ (2 * k)) : Kˣ) : K)‖ = ‖(t.q : K)‖ ^ k := by
  rw [Units.val_neg, norm_neg, norm_spow hs]

omit [CompleteSpace K] in
include hs in
theorem norm_tB_q : ‖((tB hs n).q : K)‖ = ‖(t.q : K)‖ ^ n := by
  rw [tB_q_eq hs n, Units.val_pow_eq_pow_val, norm_pow]

omit [CompleteSpace K] in
include hs in
/-- The annulus `‖q^n‖ < ‖w‖ < 1` for `‖w‖ = ‖q‖^k`, `0 < k < n`. -/
theorem annulus_of_norm {w : Kˣ} {k : ℕ} (hw : ‖(w : K)‖ = ‖(t.q : K)‖ ^ k) (hk0 : 0 < k)
    (hkn : k < n) : ‖((tB hs n).q : K)‖ < ‖(w : K)‖ ∧ ‖(w : K)‖ < 1 := by
  have hq0 := t.norm_q_pos
  have hq1 := t.norm_lt_one
  rw [norm_tB_q hs n, hw]
  exact ⟨pow_lt_pow_right_of_lt_one₀ hq0 hq1 hkn, pow_lt_one₀ hq0.le hq1 hk0.ne'⟩

omit [CompleteSpace K] in
include hs in
theorem tB_q_div {w : Kˣ} {k : ℕ} (hw : ‖(w : K)‖ = ‖(t.q : K)‖ ^ k) (hkn : k ≤ n) :
    ‖((tB hs n).q : K)‖ / ‖(w : K)‖ = ‖(t.q : K)‖ ^ (n - k) := by
  have hq0 := t.norm_q_pos
  rw [norm_tB_q hs n, hw, div_eq_iff (pow_pos hq0 k).ne', ← pow_add, Nat.sub_add_cancel hkn]

include hs in
/-- `‖X_{q^n}(w)‖ ≤ ‖q‖` and `‖Y_{q^n}(w)‖ ≤ ‖q‖` for `‖w‖ = ‖q‖^k`, `0 < k < n`. -/
theorem norm_XY_le_q {w : Kˣ} {k : ℕ} (hw : ‖(w : K)‖ = ‖(t.q : K)‖ ^ k) (hk0 : 0 < k)
    (hkn : k < n) : ‖(tB hs n).X w‖ ≤ ‖(t.q : K)‖ ∧ ‖(tB hs n).Y w‖ ≤ ‖(t.q : K)‖ := by
  have hq0 := t.norm_q_pos
  have hq1 := t.norm_lt_one
  obtain ⟨hlo, hhi⟩ := annulus_of_norm hs n hw hk0 hkn
  have hdiv := tB_q_div hs n hw hkn.le
  have p1 : ‖(t.q : K)‖ ^ k ≤ ‖(t.q : K)‖ := pow_le_of_le_one hq0.le hq1.le hk0.ne'
  have p2 : ‖(t.q : K)‖ ^ (n - k) ≤ ‖(t.q : K)‖ := pow_le_of_le_one hq0.le hq1.le (by omega)
  have p3 : (‖(t.q : K)‖ ^ k) ^ 2 ≤ ‖(t.q : K)‖ :=
    (pow_le_of_le_one (by positivity) (pow_le_one₀ hq0.le hq1.le) two_ne_zero).trans p1
  refine ⟨(norm_X_le_annulus _ hlo hhi).trans ?_, (norm_Y_le_annulus _ hlo hhi).trans ?_⟩
  · rw [hdiv, hw]; exact max_le p1 p2
  · rw [hdiv, hw]; exact max_le p3 p2

include hs in
/-- For `2k < n`: `‖X_{q^n}(w) - w‖ ≤ ‖q‖^{k+1}` and `‖Y_{q^n}(w)‖ ≤ ‖q‖^{k+1}`
(`‖w‖ = ‖q‖^k`, `k ≥ 1`). -/
theorem norm_X_sub_le_q {w : Kˣ} {k : ℕ} (hw : ‖(w : K)‖ = ‖(t.q : K)‖ ^ k) (hk0 : 0 < k)
    (hkn : 2 * k < n) :
    ‖(tB hs n).X w - w‖ ≤ ‖(t.q : K)‖ ^ (k + 1) ∧ ‖(tB hs n).Y w‖ ≤ ‖(t.q : K)‖ ^ (k + 1) := by
  have hq0 := t.norm_q_pos
  have hq1 := t.norm_lt_one
  obtain ⟨hlo, hhi⟩ := annulus_of_norm hs n hw hk0 (by omega)
  have hdiv := tB_q_div hs n hw (by omega)
  have p1 : (‖(t.q : K)‖ ^ k) ^ 2 ≤ ‖(t.q : K)‖ ^ (k + 1) := by
    rw [← pow_mul]; exact pow_le_pow_of_le_one hq0.le hq1.le (by omega)
  have p2 : ‖(t.q : K)‖ ^ (n - k) ≤ ‖(t.q : K)‖ ^ (k + 1) :=
    pow_le_pow_of_le_one hq0.le hq1.le (by omega)
  refine ⟨(norm_X_sub_le_annulus _ hlo hhi).trans ?_, (norm_Y_le_annulus _ hlo hhi).trans ?_⟩
  · rw [hdiv, hw]; exact max_le p1 p2
  · rw [hdiv, hw]; exact max_le p1 p2

include hs in
/-- For `2k = n`: `‖X_{q^n}(w)‖ ≤ ‖q‖^k`. -/
theorem norm_X_le_half {w : Kˣ} {k : ℕ} (hw : ‖(w : K)‖ = ‖(t.q : K)‖ ^ k) (hk0 : 0 < k)
    (hkn : 2 * k = n) : ‖(tB hs n).X w‖ ≤ ‖(t.q : K)‖ ^ k := by
  obtain ⟨hlo, hhi⟩ := annulus_of_norm hs n hw hk0 (by omega)
  have hdiv := tB_q_div hs n hw (by omega)
  refine (norm_X_le_annulus _ hlo hhi).trans ?_
  rw [hdiv, hw, show n - k = k by omega, max_self]

include hs in
/-- `‖X_{q^n}(-1)‖ = 1` (`‖2‖ = 1`). -/
theorem norm_X_neg_one (h2 : ‖(2 : K)‖ = 1) : ‖(tB hs n).X (-1)‖ = 1 := by
  have h := (tB hs n).norm_X_sub_node_le (u := -1) (by simp)
  have e : (((-1 : Kˣ) : K)) / (1 - ((-1 : Kˣ) : K)) ^ 2 = -(1 / 4) := by
    norm_num
    ring
  rw [e] at h
  have h4 : ‖(-(1 / 4) : K)‖ = 1 := by
    rw [norm_neg, norm_div, norm_one, show (4 : K) = 2 * 2 by norm_num, norm_mul, h2, mul_one,
      div_one]
  have hlt : ‖(tB hs n).X (-1) - -(1 / 4)‖ < ‖(-(1 / 4) : K)‖ := by
    rw [h4]; exact h.trans_lt (tB hs n).norm_lt_one
  rw [← h4]
  exact norm_eq_of_norm_sub_lt hlt

end Estimates

/-! ### The `Ω`-level elements `x_k, y_k` (`n = N_j = 2(j+1)`) -/

theorem sum_zmod_val {M : Type*} [AddCommMonoid M] (n : ℕ) [NeZero n] (f : ℕ → M) :
    ∑ k : ZMod n, f k.val = ∑ i : Fin n, f i :=
  Fintype.sum_bijective (fun k : ZMod n => (⟨k.val, k.val_lt⟩ : Fin n))
    ⟨fun _ _ h => ZMod.val_injective n (Fin.mk.inj_iff.1 h),
      fun i => ⟨(i : ℕ), Fin.ext (ZMod.val_natCast_of_lt i.2)⟩⟩ _ _ fun _ => rfl

section WrapperN

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve KummerTheory KummerTheory.Curve CurvesJacobian.Cusp
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

variable (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)
  [t.tateCurve.IsElliptic] (j : ℕ)

/-- `ι = φ_{2N}∘pullbackT : K(E_Q) → Ω` (`Q = s^N`, `N = N_j`; `levelQN j` is generated by the
`ι`-image of the `t_{-1}`-fixed field). -/
def iotaQN : TateField (tL hs (2 * (j + 1))) →ₐ[K] Ω :=
  (mulByNEmb t.tateCurve (2 * (2 * (j + 1)))).comp
    (pullbackT (levelCoords h2 h12 hs j).1 (levelCoords h2 h12 hs j).2
      (isTPoint_levelCoords h2 h12 hs j) (transcendental_levelCoords h2 h12 hs j))

theorem iotaQN_mem {f : TateField (tL hs (2 * (j + 1)))}
    (hf : transT h12 (offOrbit_neg_one (tL hs (2 * (j + 1))) h2) f = f) :
    iotaQN h2 h12 hs j f ∈ levelQN h2 h12 hs j :=
  IntermediateField.subset_adjoin _ _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩

/-- The blocks are fixed by `t_{-1}`. -/
theorem transT_neg_one_xN (k : ZMod (2 * (j + 1))) :
    transT h12 (offOrbit_neg_one (tL hs (2 * (j + 1))) h2) (blkX h12 hs (2 * (j + 1)) k) =
        blkX h12 hs (2 * (j + 1)) k ∧
      transT h12 (offOrbit_neg_one (tL hs (2 * (j + 1))) h2) (blkY h12 hs (2 * (j + 1)) k) =
        blkY h12 hs (2 * (j + 1)) k := by
  obtain ⟨h1, h1'⟩ := baseAut_xN h2 h12 hs (2 * (j + 1)) 1 0 k
  have hne : ((1 : Fin 2), ((0 : Fin (2 * (j + 1))) : ℕ)) ≠ (0, 0) := fun h =>
    one_ne_zero (congrArg Prod.fst h)
  have e : ∀ g, baseAut (rfl : (tL hs (2 * (j + 1))).q = s ^ (2 * (j + 1))) (NeZero.pos _) h12 1 0 g
      = transT h12 (offOrbit_neg_one (tL hs (2 * (j + 1))) h2) g := by
    intro g
    simp only [baseAut]
    rw [dif_neg hne]
    exact congrFun (congrArg DFunLike.coe (transT_congr h12 (by simp [cuspElt]) _ _)) g
  rw [← e, ← e, h1, h1']
  simp

/-- `x_k ∈ Ω`. -/
def xΩ (k : ZMod (2 * (j + 1))) : Ω := iotaQN h2 h12 hs j (blkX h12 hs (2 * (j + 1)) k)

/-- `y_k ∈ Ω`. -/
def yΩ (k : ZMod (2 * (j + 1))) : Ω := iotaQN h2 h12 hs j (blkY h12 hs (2 * (j + 1)) k)

theorem xΩ_mem (k : ZMod (2 * (j + 1))) : xΩ h2 h12 hs j k ∈ levelQN h2 h12 hs j :=
  iotaQN_mem h2 h12 hs j (transT_neg_one_xN h2 h12 hs j k).1

theorem yΩ_mem (k : ZMod (2 * (j + 1))) : yΩ h2 h12 hs j k ∈ levelQN h2 h12 hs j :=
  iotaQN_mem h2 h12 hs j (transT_neg_one_xN h2 h12 hs j k).2

/-- The Vélu shift of `x`: `Σ_k x_k = x + c_x`. -/
abbrev cxN : K := 2 * t.eisenstein 1 - 2 * (2 * (j + 1) : ℕ) * (tB hs (2 * (j + 1))).eisenstein 1

/-- The Vélu shift of `y`: `y = Σ_k y_k + c_y`. -/
abbrev cyN : K := t.eisenstein 1 - (2 * (j + 1) : ℕ) * (tB hs (2 * (j + 1))).eisenstein 1

/-- **Vélu, `x`, in `K(E_q)`**: `pullbackT (Σ_k x_k − c_x) = [2N]^*x`. -/
theorem pullbackT_veluN_x :
    pullbackT (levelCoords h2 h12 hs j).1 (levelCoords h2 h12 hs j).2
      (isTPoint_levelCoords h2 h12 hs j) (transcendental_levelCoords h2 h12 hs j)
      (∑ k, blkX h12 hs (2 * (j + 1)) k - algebraMap K _ (cxN hs j)) =
    algebraMap (coverRingN t.tateCurve (2 * (2 * (j + 1)))) (TateField t)
      (mulByNHom t.tateCurve (2 * (2 * (j + 1))) (xE t.tateCurve)) := by
  have hψ0 := psiN_ne_zero_of_neZero t.tateCurve (2 * (2 * (j + 1)))
  have hc := (levelCoords_spec h2 h12 hs j).2
  refine eq_of_hasTateValue (h12 := h12) hψ0 (G := fun u => t.X (u ^ (2 * (2 * (j + 1)))))
    (fun u hu hψ => ?_) (fun u hu hψ => ?_)
  · obtain ⟨hum, -⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * (2 * (j + 1))) h2 hu hψ
    have hv : OffOrbit (tL hs (2 * (j + 1))) (u ^ (2 * (j + 1))) :=
      offOrbit_sqrt_pow hs (tL hs (2 * (j + 1))) rfl hum
    have e : (u ^ (2 * (j + 1))) ^ 2 = u ^ (2 * (2 * (j + 1))) := by
      rw [← pow_mul, mul_comm]
    have hU2 : OffOrbit t ((u ^ (2 * (j + 1))) ^ 2) := by rw [e]; exact hum
    refine (hasTateValue_pullbackT (isTPoint_levelCoords h2 h12 hs j)
      (transcendental_levelCoords h2 h12 hs j) hv (hc u hu hum).1 (hc u hu hum).2
      ((HasTateValue.finsetSum h12 Finset.univ fun k _ =>
        hasTateValue_xN h2 h12 hs (2 * (j + 1)) k _ hv hU2).sub
        (HasTateValue.const hv _))).congr ?_
    have hsum : ∑ k : ZMod (2 * (j + 1)),
        (tB hs (2 * (j + 1))).X ((u ^ (2 * (j + 1))) ^ 2 * s ^ (2 * k.val)) =
        ∑ i : Fin (2 * (j + 1)),
          (tB hs (2 * (j + 1))).X ((u ^ (2 * (j + 1))) ^ 2 * s ^ (2 * (i : ℕ))) :=
      sum_zmod_val (2 * (j + 1))
        (fun i => (tB hs (2 * (j + 1))).X ((u ^ (2 * (j + 1))) ^ 2 * s ^ (2 * i)))
    rw [← e, veluN_X hs (2 * (j + 1)), hsum]
    ring
  · obtain ⟨hum, hv⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * (2 * (j + 1))) h2 hu hψ
    exact (hv (xE t.tateCurve)).congr (by
      rw [show xE t.tateCurve = mkT t (C X) from rfl, evalTate_mk_C, eval_X])

/-- **Vélu, `y`, in `K(E_q)`**: `pullbackT (Σ_k y_k + c_y) = [2N]^*y`. -/
theorem pullbackT_veluN_y :
    pullbackT (levelCoords h2 h12 hs j).1 (levelCoords h2 h12 hs j).2
      (isTPoint_levelCoords h2 h12 hs j) (transcendental_levelCoords h2 h12 hs j)
      (∑ k, blkY h12 hs (2 * (j + 1)) k + algebraMap K _ (cyN hs j)) =
    algebraMap (coverRingN t.tateCurve (2 * (2 * (j + 1)))) (TateField t)
      (mulByNHom t.tateCurve (2 * (2 * (j + 1))) (yE t.tateCurve)) := by
  have hψ0 := psiN_ne_zero_of_neZero t.tateCurve (2 * (2 * (j + 1)))
  have hc := (levelCoords_spec h2 h12 hs j).2
  refine eq_of_hasTateValue (h12 := h12) hψ0 (G := fun u => t.Y (u ^ (2 * (2 * (j + 1)))))
    (fun u hu hψ => ?_) (fun u hu hψ => ?_)
  · obtain ⟨hum, -⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * (2 * (j + 1))) h2 hu hψ
    have hv : OffOrbit (tL hs (2 * (j + 1))) (u ^ (2 * (j + 1))) :=
      offOrbit_sqrt_pow hs (tL hs (2 * (j + 1))) rfl hum
    have e : (u ^ (2 * (j + 1))) ^ 2 = u ^ (2 * (2 * (j + 1))) := by
      rw [← pow_mul, mul_comm]
    have hU2 : OffOrbit t ((u ^ (2 * (j + 1))) ^ 2) := by rw [e]; exact hum
    refine (hasTateValue_pullbackT (isTPoint_levelCoords h2 h12 hs j)
      (transcendental_levelCoords h2 h12 hs j) hv (hc u hu hum).1 (hc u hu hum).2
      ((HasTateValue.finsetSum h12 Finset.univ fun k _ =>
        hasTateValue_yN h2 h12 hs (2 * (j + 1)) k _ hv hU2).add
        (HasTateValue.const hv _))).congr ?_
    have hsum : ∑ k : ZMod (2 * (j + 1)),
        (tB hs (2 * (j + 1))).Y ((u ^ (2 * (j + 1))) ^ 2 * s ^ (2 * k.val)) =
        ∑ i : Fin (2 * (j + 1)),
          (tB hs (2 * (j + 1))).Y ((u ^ (2 * (j + 1))) ^ 2 * s ^ (2 * (i : ℕ))) :=
      sum_zmod_val (2 * (j + 1))
        (fun i => (tB hs (2 * (j + 1))).Y ((u ^ (2 * (j + 1))) ^ 2 * s ^ (2 * i)))
    rw [← e, veluN_Y hs (2 * (j + 1)), hsum]
  · obtain ⟨hum, hv⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * (2 * (j + 1))) h2 hu hψ
    exact (hv (yE t.tateCurve)).congr (by
      rw [show yE t.tateCurve = mkT t Polynomial.X from rfl, evalTate_mk_Y])

/-- **Vélu, `x`, in `Ω`**: `Σ_k x_k − c_x = τ`. -/
theorem xΩ_velu :
    ∑ k, xΩ h2 h12 hs j k - algebraMap K Ω (cxN hs j) = algebraMap (DX t).R Ω (xX t) := by
  have h := congrArg (mulByNEmb t.tateCurve (2 * (2 * (j + 1)))) (pullbackT_veluN_x h2 h12 hs j)
  rw [tau_eq, ← AlgHom.comp_apply, ← iotaQN, map_sub, map_sum, AlgHom.commutes] at h
  rw [algebraMap_xX]
  exact h

/-- **Vélu, `y`, in `Ω`**: `Σ_k y_k + c_y = y`. -/
theorem yΩ_velu :
    ∑ k, yΩ h2 h12 hs j k + algebraMap K Ω (cyN hs j) = algebraMap (DX t).R Ω (yX t) := by
  have h := congrArg (mulByNEmb t.tateCurve (2 * (2 * (j + 1)))) (pullbackT_veluN_y h2 h12 hs j)
  rw [mulByNEmb_mulByNHom, ← AlgHom.comp_apply, ← iotaQN, map_add, map_sum,
    AlgHom.commutes] at h
  rw [algebraMap_yX, hemiRho_apply, algebraMap_hemiREquiv']
  exact h

end WrapperN

/-! ### The coefficient matrices `cA i d` of the pair relations and their relations in `K(E_Q)` -/

section PairCoeffs

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K} (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)
  (n : ℕ) [NeZero n]

/-- `x_D = X_{q^n}(q^d)`. -/
abbrev xD (d : ZMod n) : K := (tB hs n).X (s ^ (2 * d.val))

/-- `y_D = Y_{q^n}(q^d)`. -/
abbrev yD (d : ZMod n) : K := (tB hs n).Y (s ^ (2 * d.val))

/-- **The affine coefficient matrices of the pair relations** between the blocks `k` and
`k + d`: A-type `(R2/δ, R1 − R2/δ, R3)` for `2d < n`, B-type `(B1, B2, B_YY)` for `2d = n`,
and `0` for `2d > n` (those pairs are covered by `n − d`). -/
def cA (i : Fin 3) (d : ZMod n) : Fin 3 → Fin 3 → K :=
  if d = 0 then 0 else if 2 * d.val < n then
    ![matR2 (tB hs n).a₄ (xD hs n d) (yD hs n d),
      matR1 (xD hs n d) (yD hs n d) - matR2 (tB hs n).a₄ (xD hs n d) (yD hs n d),
      matR3 (tB hs n).a₄ (xD hs n d) (yD hs n d)] i
  else if 2 * d.val = n then
    ![matB1 (tB hs n).a₄ (xD hs n d), matB2 (xD hs n d), matBY (tB hs n).a₄ (xD hs n d)] i
  else 0

include h2 h12 in
/-- **The pair relations on values** for the matrices `cA i d`. -/
theorem cA_val (hδ : ∀ d : ZMod n, 0 < d.val → 2 * d.val < n → xD hs n d + 2 * yD hs n d ≠ 0)
    (i : Fin 3) {d : ZMod n} (hd : d ≠ 0) {v : Kˣ} (hv : OffOrbit t v) :
    bilK (cA hs n i d) ((tB hs n).X v) ((tB hs n).Y v) ((tB hs n).X (v * s ^ (2 * d.val)))
      ((tB hs n).Y (v * s ^ (2 * d.val))) = 0 := by
  have hd0 : 0 < d.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero d).2 hd)
  have hdn : d.val < n := d.val_lt
  have hu := offOrbit_tB_of hs n hv
  have hw := offOrbit_tB_spow hs n hd0 hdn
  have huw := offOrbit_tB_of hs n (offOrbit_mul_q hv (val_spow hs d.val))
  have hx := tB_X_ne h2 h12 hs n hv hd0 hdn
  unfold cA
  rw [if_neg hd]
  split_ifs with h1 h3
  · obtain ⟨r1, r2, r3⟩ := tate_pairA h2 h12 (tB hs n) hu hw huw hx (hδ d hd0 h1)
    fin_cases i
    · exact r2
    · change bilK (matR1 _ _ - matR2 _ _ _) _ _ _ _ = 0
      rw [bilK_sub, r1, r2, sub_zero]
    · exact r3
  · have hw2 : s ^ (2 * d.val) * s ^ (2 * d.val) = (tB hs n).q := by
      rw [← pow_add, tB_q]; congr 1; omega
    obtain ⟨r1, r2, r3⟩ := tate_pairB h2 h12 (tB hs n) hu hw huw hx hw2
    fin_cases i
    · exact r1
    · exact r2
    · exact r3
  · exact bilK_zero _ _ _ _

include h2 in
/-- **The pair relations in `K(E_Q)`** between the blocks `k` and `k + d`, `d ≠ 0`. -/
theorem cA_rel (hδ : ∀ d : ZMod n, 0 < d.val → 2 * d.val < n → xD hs n d + 2 * yD hs n d ≠ 0)
    (i : Fin 3) {d : ZMod n} (hd : d ≠ 0) (k : ZMod n) :
    bilK (fun a b => algebraMap K (TateField (tL hs n)) (cA hs n i d a b)) (blkX h12 hs n k)
      (blkY h12 hs n k) (blkX h12 hs n (k + d)) (blkY h12 hs n (k + d)) = 0 :=
  bilK_xN_eq_zero h2 h12 hs n k d fun _ hv => cA_val h2 h12 hs n hδ i hd hv

end PairCoeffs

/-! ### The cyclic quadrics `Γ_d` in `K(E_Q)` -/

section Gamma

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K} (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)
  (n : ℕ) [NeZero n]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
theorem spow_eq_qpow (k : ℕ) : s ^ (2 * k) = t.q ^ k := by rw [pow_mul, hs]

/-- The value `K_d = Γ_d(-1)` of the cyclic quadric (`exists_gammaQuadric_eq`). -/
def gamK (d : ZMod n) : K :=
  ∑ k ∈ Finset.range n, ((tB hs n).X (-1 * t.q ^ k) - (tB hs n).X (t.q ^ d.val)) *
    ((tB hs n).X (-1 * t.q ^ (k + d.val)) - (tB hs n).X (t.q ^ d.val))

include h2 in
/-- **`Γ_d` in `K(E_Q)`**: `Σ_k (x_k − x_D)(x_{k+d} − x_D) = K_d` (`d ≠ 0`). -/
theorem gam_rel {d : ZMod n} (hd : d ≠ 0) :
    ∑ k, (blkX h12 hs n k - algebraMap K _ (xD hs n d)) *
        (blkX h12 hs n (k + d) - algebraMap K _ (xD hs n d)) =
      algebraMap K (TateField (tL hs n)) (gamK hs n d) := by
  have hd0 : 0 < d.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero d).2 hd)
  refine eq_of_goodN h12 hs n (A := fun _ => gamK hs n d) (fun U hU hU2 => ?_)
    (fun U hU hU2 => HasTateValue.const hU _)
  refine (HasTateValue.finsetSum h12 Finset.univ fun k _ =>
    ((hasTateValue_xN h2 h12 hs n k U hU hU2).sub (HasTateValue.const hU _)).mul
      ((hasTateValue_xN h2 h12 hs n (k + d) U hU hU2).sub (HasTateValue.const hU _))).congr ?_
  have hT : (tB hs n).q = t.q ^ n := tB_q_eq hs n
  unfold gamK
  rw [← gammaQuadric_eq_neg_one t (tB hs n) two_ne_zero hT hd0 d.val_lt hU2]
  have hterm : ∀ k : ZMod n,
      ((tB hs n).X (U ^ 2 * s ^ (2 * k.val)) - xD hs n d) *
          ((tB hs n).X (U ^ 2 * s ^ (2 * (k + d).val)) - xD hs n d) =
        ((tB hs n).X (U ^ 2 * t.q ^ k.val) - (tB hs n).X (t.q ^ d.val)) *
          ((tB hs n).X (U ^ 2 * t.q ^ (k.val + d.val)) - (tB hs n).X (t.q ^ d.val)) := by
    intro k
    dsimp only [xD]
    rw [spow_period hs n (U ^ 2) (i := (k + d).val) (j := k.val + d.val)
      (by rw [ZMod.val_add, Nat.mod_mod]), X_zpow_mul, spow_eq_qpow hs, spow_eq_qpow hs,
      spow_eq_qpow hs]
  rw [Finset.sum_congr rfl fun k _ => hterm k, sum_zmod_val n
    (fun i => ((tB hs n).X (U ^ 2 * t.q ^ i) - (tB hs n).X (t.q ^ d.val)) *
      ((tB hs n).X (U ^ 2 * t.q ^ (i + d.val)) - (tB hs n).X (t.q ^ d.val))),
    Fin.sum_univ_eq_sum_range
    (fun i => ((tB hs n).X (U ^ 2 * t.q ^ i) - (tB hs n).X (t.q ^ d.val)) *
      ((tB hs n).X (U ^ 2 * t.q ^ (i + d.val)) - (tB hs n).X (t.q ^ d.val)))]

end Gamma

/-! ### The Galois action on the blocks -/

section GaloisN

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve KummerTheory KummerTheory.Curve CurvesJacobian.Cusp
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

variable (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)
  [t.tateCurve.IsElliptic] (j : ℕ)

/-- **The Galois action on `K(E_Q)`** (`exists_levelEmb`): every `σ` fixing `L_X` acts on
`ι(K(E_Q))` by a translation `t_w`, `w = (-1)^e s^a`. -/
theorem iotaQN_galois (σ : Ω ≃ₐ[K₀ K τ] Ω) (hσ : ∀ z ∈ (hemiData t.tateCurve).L, σ z = z) :
    ∃ p : Fin 2 × Fin (2 * (j + 1)),
      ((σ : Ω →ₐ[K₀ K τ] Ω).restrictScalars K).comp (iotaQN h2 h12 hs j) =
        (iotaQN h2 h12 hs j).comp (baseAut (rfl : (tL hs (2 * (j + 1))).q = s ^ (2 * (j + 1)))
          (NeZero.pos _) h12 p.1 p.2 :
            TateField (tL hs (2 * (j + 1))) →ₐ[K] TateField (tL hs (2 * (j + 1)))) := by
  haveI := isElliptic_sqrtPow h12 hs j
  obtain ⟨gX, gY, F, -, hmul, -, hval⟩ := exists_levelData (t := t) h12 h2 hs
    (N := 2 * (j + 1)) (Nat.mul_pos two_pos j.succ_pos) ⟨j + 1, by ring⟩
  obtain ⟨e1, e2⟩ := eq_levelCoords h2 h12 hs j (gX := gX) (gY := gY)
    (fun u hu hum => ⟨(hval u hu hum).1, (hval u hu hum).2.1⟩)
  subst e1 e2
  obtain ⟨hpt, htr, -, -, -, hidx⟩ := exists_levelEmb h2 h12 hs
    (N := 2 * (j + 1)) (Nat.mul_pos two_pos j.succ_pos) ⟨j + 1, by ring⟩ hmul hval
  exact hidx σ hσ

/-- `σ` fixing `L_X` shifts the blocks: `σ(x_k) = x_{k+a}`, `σ(y_k) = y_{k+a}`. -/
theorem galois_xΩ {σ : Ω ≃ₐ[K₀ K τ] Ω} {p : Fin 2 × Fin (2 * (j + 1))}
    (hp : ((σ : Ω →ₐ[K₀ K τ] Ω).restrictScalars K).comp (iotaQN h2 h12 hs j) =
      (iotaQN h2 h12 hs j).comp (baseAut (rfl : (tL hs (2 * (j + 1))).q = s ^ (2 * (j + 1)))
        (NeZero.pos _) h12 p.1 p.2 :
          TateField (tL hs (2 * (j + 1))) →ₐ[K] TateField (tL hs (2 * (j + 1))))) (k) :
    σ (xΩ h2 h12 hs j k) = xΩ h2 h12 hs j (k + (p.2 : ℕ)) ∧
      σ (yΩ h2 h12 hs j k) = yΩ h2 h12 hs j (k + (p.2 : ℕ)) := by
  refine ⟨?_, ?_⟩
  · have h := DFunLike.congr_fun hp (blkX h12 hs (2 * (j + 1)) k)
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom] at h
    simp only [xΩ]
    rw [h, (baseAut_xN h2 h12 hs (2 * (j + 1)) p.1 p.2 k).1]
  · have h := DFunLike.congr_fun hp (blkY h12 hs (2 * (j + 1)) k)
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom] at h
    simp only [yΩ]
    rw [h, (baseAut_xN h2 h12 hs (2 * (j + 1)) p.1 p.2 k).2]

omit [t.tateCurve.IsElliptic] in
include h2 in
/-- On the `t_{-1}`-fixed field, `t_{-s^a}` and `t_{s^a}` agree. -/
theorem baseAut_eq_of_fixed (e : Fin 2) (a : Fin (2 * (j + 1)))
    {f : TateField (tL hs (2 * (j + 1)))}
    (hf : transT h12 (offOrbit_neg_one (tL hs (2 * (j + 1))) h2) f = f) :
    baseAut (rfl : (tL hs (2 * (j + 1))).q = s ^ (2 * (j + 1))) (NeZero.pos _) h12 e a f =
      baseAut (rfl : (tL hs (2 * (j + 1))).q = s ^ (2 * (j + 1))) (NeZero.pos _) h12 0 a f := by
  fin_cases e
  · rfl
  · by_cases ha : (a : ℕ) = 0
    · have h0 : ((0 : Fin 2), (a : ℕ)) = (0, 0) := by rw [ha]
      have h1 : ((1 : Fin 2), (a : ℕ)) ≠ (0, 0) := fun h => one_ne_zero (congrArg Prod.fst h)
      simp only [Fin.mk_one, baseAut]
      rw [dif_pos h0, dif_neg h1]
      refine ((congrFun (congrArg DFunLike.coe (transT_congr h12 (T := tL hs (2 * (j + 1)))
        (w := cuspElt s 1 a) (w' := -1) (by simp [cuspElt, ha]) _
        (offOrbit_neg_one _ h2))) f)).trans hf
    · have h0 : ((0 : Fin 2), (a : ℕ)) ≠ (0, 0) := fun h => ha (congrArg Prod.snd h)
      have h1 : ((1 : Fin 2), (a : ℕ)) ≠ (0, 0) := fun h => one_ne_zero (congrArg Prod.fst h)
      simp only [Fin.mk_one, baseAut]
      rw [dif_neg h0, dif_neg h1]
      have hw' := offOrbit_cuspElt (rfl : (tL hs (2 * (j + 1))).q = s ^ (2 * (j + 1)))
        (NeZero.pos _) a.2 h0
      have hww := offOrbit_cuspElt (rfl : (tL hs (2 * (j + 1))).q = s ^ (2 * (j + 1)))
        (NeZero.pos _) a.2 h1
      have hm1 := offOrbit_neg_one (tL hs (2 * (j + 1))) h2
      have e1 : cuspElt s 1 a = -1 * cuspElt s 0 a := by simp [cuspElt]
      rw [congrFun (congrArg DFunLike.coe (transT_congr h12 e1 hww
          (by rw [← e1]; exact hww))) f,
        transT_mul h2 h12 _ hm1 hw' _ f, transT_comm h2 h12 _ hm1 hw' f, hf]

/-- Two automorphisms fixing `L_X` with the same shift agree on `K(E_{q^N})`. -/
theorem eqOn_levelQN {σ₁ σ₂ : Ω ≃ₐ[K₀ K τ] Ω} {p₁ p₂ : Fin 2 × Fin (2 * (j + 1))}
    (hp₁ : ((σ₁ : Ω →ₐ[K₀ K τ] Ω).restrictScalars K).comp (iotaQN h2 h12 hs j) =
      (iotaQN h2 h12 hs j).comp (baseAut (rfl : (tL hs (2 * (j + 1))).q = s ^ (2 * (j + 1)))
        (NeZero.pos _) h12 p₁.1 p₁.2 :
          TateField (tL hs (2 * (j + 1))) →ₐ[K] TateField (tL hs (2 * (j + 1)))))
    (hp₂ : ((σ₂ : Ω →ₐ[K₀ K τ] Ω).restrictScalars K).comp (iotaQN h2 h12 hs j) =
      (iotaQN h2 h12 hs j).comp (baseAut (rfl : (tL hs (2 * (j + 1))).q = s ^ (2 * (j + 1)))
        (NeZero.pos _) h12 p₂.1 p₂.2 :
          TateField (tL hs (2 * (j + 1))) →ₐ[K] TateField (tL hs (2 * (j + 1)))))
    (he : p₁.2 = p₂.2) {z : Ω} (hz : z ∈ levelQN h2 h12 hs j) : σ₁ z = σ₂ z := by
  haveI := isElliptic_sqrtPow h12 hs j
  have hF : ∀ f, transT h12 (offOrbit_neg_one (tL hs (2 * (j + 1))) h2) f = f →
      σ₁ (iotaQN h2 h12 hs j f) = σ₂ (iotaQN h2 h12 hs j f) := by
    intro f hf
    have h1 := DFunLike.congr_fun hp₁ f
    have h2' := DFunLike.congr_fun hp₂ f
    have hb : baseAut (rfl : (tL hs (2 * (j + 1))).q = s ^ (2 * (j + 1))) (NeZero.pos _) h12
        p₁.1 p₁.2 f = baseAut (rfl : (tL hs (2 * (j + 1))).q = s ^ (2 * (j + 1))) (NeZero.pos _)
        h12 p₂.1 p₂.2 f := by
      rw [baseAut_eq_of_fixed h2 h12 hs j p₁.1 p₁.2 hf,
        baseAut_eq_of_fixed h2 h12 hs j p₂.1 p₂.2 hf, he]
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom] at h1 h2'
    rw [h1, h2', hb]
  have hz' : z ∈ IntermediateField.adjoin (K₀ K τ)
      (mulByNEmb t.tateCurve (2 * (2 * (j + 1))) ''
        (pullbackT (levelCoords h2 h12 hs j).1 (levelCoords h2 h12 hs j).2
          (isTPoint_levelCoords h2 h12 hs j) (transcendental_levelCoords h2 h12 hs j) ''
          {f | transT h12 (offOrbit_neg_one (tL hs (2 * (j + 1))) h2) f = f})) := hz
  clear hz
  induction hz' using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨_, ⟨f, hf, rfl⟩, rfl⟩ := hx
    exact hF f hf
  | algebraMap c => rw [σ₁.commutes, σ₂.commutes]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

end GaloisN

/-! ### Norms of `K_d = Γ_d(-1)` -/

theorem norm_sub_le_max' {K : Type*} [NormedField K] [IsUltrametricDist K] (a b : K) :
    ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg, ← norm_neg b]
  exact IsUltrametricDist.norm_add_le_max _ _

section KdNorms

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K} {s : Kˣ} (hs : s ^ 2 = t.q) (n : ℕ) [NeZero n] (h2 : ‖(2 : K)‖ = 1)

omit [CompleteSpace K] in
theorem norm_neg_qpow (k : ℕ) : ‖((-1 * t.q ^ k : Kˣ) : K)‖ = ‖(t.q : K)‖ ^ k := by
  simp [Units.val_pow_eq_pow_val]

omit [CompleteSpace K] in
theorem norm_qpow (k : ℕ) : ‖((t.q ^ k : Kˣ) : K)‖ = ‖(t.q : K)‖ ^ k := by
  simp [Units.val_pow_eq_pow_val]

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem negq_period (k : ℕ) :
    (-1 * t.q ^ (k + n) : Kˣ) = (tB hs n).q ^ (1 : ℤ) * (-1 * t.q ^ k) := by
  rw [tB_q_eq hs n, zpow_one, pow_add, mul_comm (t.q ^ k), ← mul_assoc, ← mul_assoc,
    mul_comm (-1 : Kˣ)]

include hs in
theorem X_negq_period (k : ℕ) :
    (tB hs n).X (-1 * t.q ^ (k + n)) = (tB hs n).X (-1 * t.q ^ k) := by
  rw [negq_period hs n, X_zpow_mul]

omit [CompleteSpace K] in
include h2 in
theorem offOrbit_negq (k : ℕ) : OffOrbit t (-1 * t.q ^ k) :=
  offOrbit_mul_q (offOrbit_neg_one t h2) (k := k) (by rw [Units.val_pow_eq_pow_val, zpow_natCast])

include hs h2 in
/-- `X(-q^{n-d}) = X(-q^d)`. -/
theorem X_negq_sub {d : ℕ} (hdn : d ≤ n) :
    (tB hs n).X (-1 * t.q ^ (n - d)) = (tB hs n).X (-1 * t.q ^ d) := by
  have hu : OffOrbit (tB hs n) (-1 * t.q ^ d) := offOrbit_tB_of hs n (offOrbit_negq h2 d)
  have e : (-1 * t.q ^ (n - d) : Kˣ) = (tB hs n).q ^ (1 : ℤ) * (-1 * t.q ^ d)⁻¹ := by
    rw [tB_q_eq hs n, zpow_one, mul_inv, inv_neg_one, mul_left_comm, ← pow_sub _ hdn]
  rw [e, X_zpow_mul, (tB hs n).X_inv hu]

include hs in
theorem norm_xD_le {d : ℕ} (hd0 : 0 < d) (hdn : d < n) :
    ‖(tB hs n).X (t.q ^ d)‖ ≤ ‖(t.q : K)‖ :=
  (norm_XY_le_q hs n (norm_qpow d) hd0 hdn).1

include hs h2 in
/-- `‖X(-q^k) - x_D‖ ≤ ‖q‖` for `0 < k < n`, and `‖X(-1) - x_D‖ = 1`. -/
theorem norm_a_le {d k : ℕ} (hd0 : 0 < d) (hdn : d < n) (hk0 : 0 < k) (hkn : k < n) :
    ‖(tB hs n).X (-1 * t.q ^ k) - (tB hs n).X (t.q ^ d)‖ ≤ ‖(t.q : K)‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    (norm_XY_le_q hs n (norm_neg_qpow k) hk0 hkn).1
    (by rw [norm_neg]; exact norm_xD_le hs n hd0 hdn))

include hs h2 in
theorem norm_a0 {d : ℕ} (hd0 : 0 < d) (hdn : d < n) :
    ‖(tB hs n).X (-1 * t.q ^ 0) - (tB hs n).X (t.q ^ d)‖ = 1 := by
  have h1 : ‖(tB hs n).X (-1 * t.q ^ 0)‖ = 1 := by
    rw [pow_zero, mul_one]; exact norm_X_neg_one hs n h2
  rw [← h1]
  refine norm_eq_of_norm_sub_lt ?_
  rw [h1, sub_sub_cancel_left, norm_neg]
  exact (norm_xD_le hs n hd0 hdn).trans_lt t.norm_lt_one

include hs h2 in
/-- For `2d < n`: `‖X(-q^d) - x_D‖ ≤ ‖q‖^d`, with equality `= ‖q‖` for `d = 1`... (upper bound). -/
theorem norm_ad_le {d : ℕ} (hd0 : 0 < d) (hdn : 2 * d < n) :
    ‖(tB hs n).X (-1 * t.q ^ d) - (tB hs n).X (t.q ^ d)‖ ≤ ‖(t.q : K)‖ ^ d := by
  have h1 := (norm_X_sub_le_q hs n (norm_neg_qpow d) hd0 hdn).1
  have h3 := (norm_X_sub_le_q hs n (norm_qpow d) hd0 hdn).1
  have hq0 := t.norm_q_pos
  have hq1 := t.norm_lt_one
  have hle : ‖(t.q : K)‖ ^ (d + 1) ≤ ‖(t.q : K)‖ ^ d :=
    pow_le_pow_of_le_one hq0.le hq1.le (by omega)
  rw [show (tB hs n).X (-1 * t.q ^ d) - (tB hs n).X (t.q ^ d) =
    ((tB hs n).X (-1 * t.q ^ d) - ((-1 * t.q ^ d : Kˣ) : K)) -
      ((tB hs n).X (t.q ^ d) - ((t.q ^ d : Kˣ) : K)) - 2 * ((t.q ^ d : Kˣ) : K) by
    push_cast; ring]
  refine (norm_sub_le_max' _ _).trans (max_le
    ((norm_sub_le_max' _ _).trans (max_le (h1.trans hle) (h3.trans hle))) ?_)
  rw [norm_mul, h2, one_mul, norm_qpow]

include hs h2 in
/-- For `d = 1 < n/2`: `‖X(-q) - X(q)‖ = ‖q‖`. -/
theorem norm_a1 (hn : 2 < n) :
    ‖(tB hs n).X (-1 * t.q ^ 1) - (tB hs n).X (t.q ^ 1)‖ = ‖(t.q : K)‖ := by
  have h1 := (norm_X_sub_le_q hs n (norm_neg_qpow 1) one_pos hn).1
  have h3 := (norm_X_sub_le_q hs n (norm_qpow 1) one_pos hn).1
  have hq0 := t.norm_q_pos
  have hq1 := t.norm_lt_one
  have h22 : ‖-2 * ((t.q ^ 1 : Kˣ) : K)‖ = ‖(t.q : K)‖ := by
    rw [norm_mul, norm_neg, h2, one_mul, norm_qpow, pow_one]
  rw [← h22]
  refine norm_eq_of_norm_sub_lt ?_
  rw [h22, show (tB hs n).X (-1 * t.q ^ 1) - (tB hs n).X (t.q ^ 1) - -2 * ((t.q ^ 1 : Kˣ) : K) =
    ((tB hs n).X (-1 * t.q ^ 1) - ((-1 * t.q ^ 1 : Kˣ) : K)) -
      ((tB hs n).X (t.q ^ 1) - ((t.q ^ 1 : Kˣ) : K)) by push_cast; ring]
  refine lt_of_le_of_lt ((norm_sub_le_max' _ _).trans (max_le h1 h3)) ?_
  rw [pow_succ, pow_one]
  exact mul_lt_of_lt_one_right hq0 hq1

end KdNorms

/-! ### `‖K_d‖` -/

section KdBounds

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K} {s : Kˣ} (hs : s ^ 2 = t.q) (n : ℕ) [NeZero n] (h2 : ‖(2 : K)‖ = 1)

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs in
theorem negq_mod (m : ℕ) :
    (-1 * t.q ^ m : Kˣ) = (tB hs n).q ^ ((m / n : ℕ) : ℤ) * (-1 * t.q ^ (m % n)) := by
  rw [tB_q_eq hs n, zpow_natCast, ← pow_mul, mul_left_comm, ← pow_add, Nat.div_add_mod]

/-- `a_m = X(-q^m) - x_D` (the factors of `K_d`). -/
abbrev aK (d m : ℕ) : K := (tB hs n).X (-1 * t.q ^ m) - (tB hs n).X (t.q ^ d)

include hs in
theorem aK_mod (d m : ℕ) : aK hs n d m = aK hs n d (m % n) := by
  simp only [aK]; rw [negq_mod hs n m, X_zpow_mul]

include hs h2 in
theorem norm_aK_le {d m : ℕ} (hd0 : 0 < d) (hdn : d < n) (hm : m % n ≠ 0) :
    ‖aK hs n d m‖ ≤ ‖(t.q : K)‖ := by
  rw [aK_mod]
  exact norm_a_le hs n h2 hd0 hdn (Nat.pos_of_ne_zero hm) (Nat.mod_lt _ (NeZero.pos n))

include hs h2 in
theorem norm_aK_le_one {d m : ℕ} (hd0 : 0 < d) (hdn : d < n) : ‖aK hs n d m‖ ≤ 1 := by
  by_cases hm : m % n = 0
  · rw [aK_mod, hm]; exact (norm_a0 hs n h2 hd0 hdn).le
  · exact (norm_aK_le hs n h2 hd0 hdn hm).trans t.norm_lt_one.le

theorem gamK_eq (d : ZMod n) :
    gamK hs n d = ∑ k ∈ Finset.range n, aK hs n d.val k * aK hs n d.val (k + d.val) := rfl

include hs h2 in
/-- `‖K_d‖ ≤ ‖q‖` (`d ≠ 0`). -/
theorem norm_gamK_le {d : ZMod n} (hd : d ≠ 0) : ‖gamK hs n d‖ ≤ ‖(t.q : K)‖ := by
  have hd0 : 0 < d.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero d).2 hd)
  have hdn := d.val_lt
  rw [gamK_eq]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [norm_mul]
  by_cases hk0 : k = 0
  · subst hk0
    rw [zero_add]
    calc ‖aK hs n d.val 0‖ * ‖aK hs n d.val d.val‖ ≤ 1 * ‖(t.q : K)‖ :=
          mul_le_mul (norm_aK_le_one hs n h2 hd0 hdn)
            (norm_aK_le hs n h2 hd0 hdn (by rw [Nat.mod_eq_of_lt hdn]; omega))
            (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · calc ‖aK hs n d.val k‖ * ‖aK hs n d.val (k + d.val)‖ ≤ ‖(t.q : K)‖ * 1 :=
          mul_le_mul (norm_aK_le hs n h2 hd0 hdn (by rw [Nat.mod_eq_of_lt hk]; exact hk0))
            (norm_aK_le_one hs n h2 hd0 hdn) (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_one _

include hs h2 in
/-- `‖K_d‖ ≤ ‖q‖²` for `2 ≤ d`, `2d < n`. -/
theorem norm_gamK_le_sq {d : ZMod n} (hd2 : 2 ≤ d.val) (hdn2 : 2 * d.val < n) :
    ‖gamK hs n d‖ ≤ ‖(t.q : K)‖ ^ 2 := by
  have hd0 : 0 < d.val := by omega
  have hdn := d.val_lt
  have hq0 := t.norm_q_pos
  have hq1 := t.norm_lt_one
  have hρd : ‖(t.q : K)‖ ^ d.val ≤ ‖(t.q : K)‖ ^ 2 := pow_le_pow_of_le_one hq0.le hq1.le hd2
  rw [gamK_eq]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [norm_mul]
  by_cases hk0 : k = 0
  · subst hk0
    rw [zero_add]
    calc ‖aK hs n d.val 0‖ * ‖aK hs n d.val d.val‖ ≤ 1 * ‖(t.q : K)‖ ^ d.val :=
          mul_le_mul (norm_aK_le_one hs n h2 hd0 hdn) (norm_ad_le hs n h2 hd0 hdn2)
            (norm_nonneg _) zero_le_one
      _ ≤ _ := by rw [one_mul]; exact hρd
  · by_cases hkd : k + d.val = n
    · have e : k = n - d.val := by omega
      have ha : aK hs n d.val k = aK hs n d.val d.val := by
        simp only [aK]; rw [e, X_negq_sub hs n h2 hdn.le]
      rw [ha]
      calc ‖aK hs n d.val d.val‖ * ‖aK hs n d.val (k + d.val)‖ ≤ ‖(t.q : K)‖ ^ d.val * 1 :=
            mul_le_mul (norm_ad_le hs n h2 hd0 hdn2) (norm_aK_le_one hs n h2 hd0 hdn)
              (norm_nonneg _) (by positivity)
        _ ≤ _ := by rw [mul_one]; exact hρd
    · have hm : (k + d.val) % n ≠ 0 := by
        rcases lt_or_gt_of_ne hkd with h | h
        · rw [Nat.mod_eq_of_lt h]; omega
        · rw [Nat.mod_eq_sub_mod h.le, Nat.mod_eq_of_lt (by omega)]; omega
      calc ‖aK hs n d.val k‖ * ‖aK hs n d.val (k + d.val)‖ ≤ ‖(t.q : K)‖ * ‖(t.q : K)‖ :=
            mul_le_mul (norm_aK_le hs n h2 hd0 hdn (by rw [Nat.mod_eq_of_lt hk]; exact hk0))
              (norm_aK_le hs n h2 hd0 hdn hm) (norm_nonneg _) (norm_nonneg _)
        _ = _ := (sq _).symm

include hs h2 in
/-- `‖K_1‖ = ‖q‖` (`n > 2`, `d.val = 1`). -/
theorem norm_gamK_one {d : ZMod n} (hd1 : d.val = 1) (hn : 2 < n) :
    ‖gamK hs n d‖ = ‖(t.q : K)‖ := by
  have hq0 := t.norm_q_pos
  have hq1 := t.norm_lt_one
  have hn1 : (1 : ℕ) < n := by omega
  rw [gamK_eq, hd1]
  set S := Finset.range n
  have h0 : 0 ∈ S := Finset.mem_range.2 (by omega)
  have hl : n - 1 ∈ S.erase 0 := Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 (by omega)⟩
  rw [← Finset.add_sum_erase S _ h0, ← Finset.add_sum_erase (S.erase 0) _ hl]
  have hlast : aK hs n 1 (n - 1) * aK hs n 1 (n - 1 + 1) = aK hs n 1 0 * aK hs n 1 1 := by
    have e1 : aK hs n 1 (n - 1) = aK hs n 1 1 := by
      simp only [aK]; rw [X_negq_sub hs n h2 hn1.le]
    have e2 : aK hs n 1 (n - 1 + 1) = aK hs n 1 0 := by
      rw [aK_mod, show n - 1 + 1 = n by omega, Nat.mod_self]
    rw [e1, e2, mul_comm]
  rw [hlast, zero_add]
  have hmain : ‖aK hs n 1 0 * aK hs n 1 1 + aK hs n 1 0 * aK hs n 1 1‖ = ‖(t.q : K)‖ := by
    rw [← two_mul, norm_mul, h2, one_mul, norm_mul, norm_a0 hs n h2 one_pos hn1, one_mul]
    exact norm_a1 hs n h2 hn
  have hrest : ‖∑ k ∈ (S.erase 0).erase (n - 1), aK hs n 1 k * aK hs n 1 (k + 1)‖ ≤
      ‖(t.q : K)‖ ^ 2 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k hk => ?_
    obtain ⟨hk1, hk0, hkS⟩ : k ≠ n - 1 ∧ k ≠ 0 ∧ k < n := by
      simp only [Finset.mem_erase, Finset.mem_range, S] at hk; omega
    rw [norm_mul, sq]
    exact mul_le_mul (norm_aK_le hs n h2 one_pos hn1 (by rw [Nat.mod_eq_of_lt hkS]; exact hk0))
      (norm_aK_le hs n h2 one_pos hn1 (by rw [Nat.mod_eq_of_lt (by omega)]; omega))
      (norm_nonneg _) (norm_nonneg _)
  rw [← add_assoc, ← hmain]
  refine norm_eq_of_norm_sub_lt ?_
  rw [add_sub_cancel_left, hmain]
  exact hrest.trans_lt (by rw [sq]; exact mul_lt_of_lt_one_right hq0 hq1)

end KdBounds

/-! ### The cubics, `δ ≠ 0`, and the relations in `Ω` -/

section CubDelta

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K} (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)
  (n : ℕ) [NeZero n]

include h2 in
/-- **The block cubics in `K(E_Q)`**: `y_k² + x_k y_k = x_k³ + a₄' x_k + a₆'`. -/
theorem cub_rel (k : ZMod n) :
    blkY h12 hs n k ^ 2 + blkX h12 hs n k * blkY h12 hs n k = blkX h12 hs n k ^ 3 +
      algebraMap K _ (tB hs n).a₄ * blkX h12 hs n k + algebraMap K _ (tB hs n).a₆ := by
  refine eq_of_goodN h12 hs n (A := fun U => (tB hs n).Y (U ^ 2 * s ^ (2 * k.val)) ^ 2 +
      (tB hs n).X (U ^ 2 * s ^ (2 * k.val)) * (tB hs n).Y (U ^ 2 * s ^ (2 * k.val)))
    (fun U hU hU2 => ?_) (fun U hU hU2 => ?_)
  · have a := hasTateValue_xN h2 h12 hs n k U hU hU2
    have b := hasTateValue_yN h2 h12 hs n k U hU hU2
    exact (b.pow 2).add (a.mul b)
  · have a := hasTateValue_xN h2 h12 hs n k U hU hU2
    have hv : OffOrbit (tB hs n) (U ^ 2 * s ^ (2 * k.val)) :=
      offOrbit_tB_of hs n (offOrbit_mul_q hU2 (val_spow hs k.val))
    exact (((a.pow 3).add ((HasTateValue.const hU _).mul a)).add
      (HasTateValue.const hU _)).congr (tate_eq_of h12 hv).symm

omit [CharZero K] in
include hs h2 in
/-- `δ = x_D + 2y_D ≠ 0` for `0 < 2d < n` (`‖δ‖ = ‖q‖^d`). -/
theorem xD_add_ne {d : ZMod n} (hd0 : 0 < d.val) (hdn : 2 * d.val < n) :
    xD hs n d + 2 * yD hs n d ≠ 0 := by
  obtain ⟨hX, hY⟩ := norm_X_sub_le_q hs n (norm_spow hs d.val) hd0 hdn
  have hq0 := t.norm_q_pos
  have hq1 := t.norm_lt_one
  have hw := norm_spow (K := K) hs d.val
  have hlt : ‖(t.q : K)‖ ^ (d.val + 1) < ‖(t.q : K)‖ ^ d.val :=
    pow_lt_pow_right_of_lt_one₀ hq0 hq1 (by omega)
  have key : ‖xD hs n d + 2 * yD hs n d - ((s ^ (2 * d.val) : Kˣ) : K)‖ <
      ‖((s ^ (2 * d.val) : Kˣ) : K)‖ := by
    rw [hw, show xD hs n d + 2 * yD hs n d - ((s ^ (2 * d.val) : Kˣ) : K) =
      ((tB hs n).X (s ^ (2 * d.val)) - ((s ^ (2 * d.val) : Kˣ) : K)) +
        2 * (tB hs n).Y (s ^ (2 * d.val)) by ring]
    refine lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hX ?_)) hlt
    rw [norm_mul, h2, one_mul]; exact hY
  intro h0
  rw [h0, zero_sub, norm_neg] at key
  exact lt_irrefl _ key

end CubDelta

/-! ### The coefficients of the model in `O` -/

section CoeffsO

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K} (h2 : ‖(2 : K)‖ = 1) {s : Kˣ} (hs : s ^ 2 = t.q)
  (n : ℕ) [NeZero n]

/-- The homogenised coefficients `cA i d a b / s^{w_a + w_b}` (`W = s`). -/
def cPK (i : Fin 3) (d : ZMod n) (a b : Fin 3) : K :=
  cA hs n i d a b / (s : K) ^ (coeffWt a + coeffWt b)

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
theorem norm_q_eq_s_sq : ‖(t.q : K)‖ = ‖(s : K)‖ ^ 2 := by rw [val_q_eq hs, norm_pow]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
theorem norm_s_pos_lt' : 0 < ‖(s : K)‖ ∧ ‖(s : K)‖ < 1 :=
  ⟨norm_pos_iff.2 s.ne_zero, norm_sqrt_lt_one hs⟩

omit [CharZero K] in
include hs in
theorem norm_a₄B_le : ‖(tB hs n).a₄‖ ≤ ‖(s : K)‖ ^ (2 * n) := by
  have h := (tB hs n).norm_a₄_le
  rwa [norm_tB_q hs n, norm_q_eq_s_sq hs, ← pow_mul] at h

omit [CharZero K] in
include hs in
theorem pow_q_eq (k : ℕ) : ‖(t.q : K)‖ ^ k = ‖(s : K)‖ ^ (2 * k) := by
  rw [norm_q_eq_s_sq hs, ← pow_mul]

include hs h2 in
/-- **A-type reductions**: `cPK 0, 1, 2` are `‖s‖`-close to `pA0, pA1, pY`. -/
theorem cPK_A {d : ZMod n} (hd0 : 0 < d.val) (hdn : 2 * d.val < n) (a b : Fin 3) :
    ‖cPK hs n 0 d a b - patA0 a b‖ ≤ ‖(s : K)‖ ∧ ‖cPK hs n 1 d a b - patA1 a b‖ ≤ ‖(s : K)‖ ∧
      ‖cPK hs n 2 d a b - patY a b‖ ≤ ‖(s : K)‖ := by
  have hd : d ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hd0; exact lt_irrefl 0 hd0
  obtain ⟨hs0, hs1⟩ := norm_s_pos_lt' hs
  obtain ⟨hX, hY⟩ := norm_X_sub_le_q hs n (norm_spow hs d.val) hd0 hdn
  have hw : ‖((s ^ (2 * d.val) : Kˣ) : K)‖ = ‖(s : K)‖ ^ (2 * d.val) := by
    rw [norm_spow hs, pow_q_eq hs]
  rw [pow_q_eq hs, mul_add, mul_one] at hX hY
  have ha := norm_a₄B_le hs n
  simp only [cPK, cA, if_neg hd, if_pos hdn]
  exact ⟨caseA_matR2 h2 hs0 hs1 hd0 hdn hw hX hY ha a b,
    caseA_matR1_sub_matR2 h2 hs0 hs1 hd0 hdn hw hX hY ha a b,
    caseA_matR3 h2 hs0 hs1 hd0 hdn hw hX hY ha a b⟩

include hs h2 in
/-- **B-type reductions**: `cPK 0, 1, 2` are `‖s‖`-close to `pB0, pB1, pY`. -/
theorem cPK_B (hn4 : 4 ≤ n) {d : ZMod n} (hdn : 2 * d.val = n) (a b : Fin 3) :
    ‖cPK hs n 0 d a b - patB0 a b‖ ≤ ‖(s : K)‖ ∧ ‖cPK hs n 1 d a b - patB1 a b‖ ≤ ‖(s : K)‖ ∧
      ‖cPK hs n 2 d a b - patY a b‖ ≤ ‖(s : K)‖ := by
  have hd0 : 0 < d.val := by omega
  have hd : d ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hd0; exact lt_irrefl 0 hd0
  obtain ⟨hs0, hs1⟩ := norm_s_pos_lt' hs
  have he := norm_X_le_half hs n (norm_spow hs d.val) hd0 hdn
  rw [pow_q_eq hs] at he
  have ha := norm_a₄B_le hs n
  have hlt : ¬ 2 * d.val < n := by omega
  simp only [cPK, cA, if_neg hd, if_neg hlt, if_pos hdn]
  exact ⟨caseB_matB1 h2 hs0 hs1 (by omega) hdn he ha a b,
    caseB_matB2 h2 hs0 hs1 (by omega) hdn he ha a b,
    caseB_matBY h2 hs0 hs1 (by omega) hdn he ha a b⟩

omit [CompleteSpace K] in
theorem norm_le_one_of_close {x p : K} {r : ℝ} (hp : ‖p‖ ≤ 1) (hr : r ≤ 1) (h : ‖x - p‖ ≤ r) :
    ‖x‖ ≤ 1 := by
  rw [show x = (x - p) + p by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans hr) hp)

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem norm_pat_le {P : Fin 3 → Fin 3 → K} (hP : ∀ a b, P a b = 0 ∨ P a b = 1) (a b : Fin 3) :
    ‖P a b‖ ≤ 1 := by
  rcases hP a b with h | h <;> simp [h]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem pat01 : (∀ a b, patA0 (K := K) a b = 0 ∨ patA0 (K := K) a b = 1) ∧
    (∀ a b, patA1 (K := K) a b = 0 ∨ patA1 (K := K) a b = 1) ∧
    (∀ a b, patY (K := K) a b = 0 ∨ patY (K := K) a b = 1) ∧
    (∀ a b, patB0 (K := K) a b = 0 ∨ patB0 (K := K) a b = 1) ∧
    (∀ a b, patB1 (K := K) a b = 0 ∨ patB1 (K := K) a b = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro a b <;> fin_cases a <;> fin_cases b <;>
    simp [patA0, patA1, patY, patB0, patB1]

include hs h2 in
theorem norm_cPK_le (hn4 : 4 ≤ n) (i : Fin 3) (d : ZMod n) (a b : Fin 3) :
    ‖cPK hs n i d a b‖ ≤ 1 := by
  obtain ⟨hs0, hs1⟩ := norm_s_pos_lt' hs
  obtain ⟨pa0, pa1, py, pb0, pb1⟩ := pat01 (K := K)
  by_cases hd : d = 0
  · simp [cPK, cA, hd]
  by_cases hA : 2 * d.val < n
  · have hd0 : 0 < d.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero d).2 hd)
    obtain ⟨r0, r1, r2⟩ := cPK_A h2 hs n hd0 hA a b
    fin_cases i
    · exact norm_le_one_of_close (norm_pat_le pa0 a b) hs1.le r0
    · exact norm_le_one_of_close (norm_pat_le pa1 a b) hs1.le r1
    · exact norm_le_one_of_close (norm_pat_le py a b) hs1.le r2
  by_cases hB : 2 * d.val = n
  · obtain ⟨r0, r1, r2⟩ := cPK_B h2 hs n hn4 hB a b
    fin_cases i
    · exact norm_le_one_of_close (norm_pat_le pb0 a b) hs1.le r0
    · exact norm_le_one_of_close (norm_pat_le pb1 a b) hs1.le r1
    · exact norm_le_one_of_close (norm_pat_le py a b) hs1.le r2
  · simp [cPK, cA, hd, hA, hB]

end CoeffsO

/-! ### `x_k, y_k ∈ R' = K[E_{q^N}]` and the fields of `NGon.Input` (`N = N_j`, `j ≥ 1`) -/

section InputN

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve KummerTheory KummerTheory.Curve CurvesJacobian.Cusp
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

variable (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)
  [t.tateCurve.IsElliptic] (j : ℕ)

/-- The coordinate ring `R' = K[E_{q^{N_j}}]` of `levelQN j`. -/
abbrev RQN : Type u :=
  (fieldData (transcendental_tau t.tateCurve) (levelQN h2 h12 hs j) (isOpen_levelQN h2 h12 hs j)).R

theorem xΩ_cub (k : ZMod (2 * (j + 1))) :
    yΩ h2 h12 hs j k ^ 2 + xΩ h2 h12 hs j k * yΩ h2 h12 hs j k = xΩ h2 h12 hs j k ^ 3 +
      algebraMap K Ω (tB hs (2 * (j + 1))).a₄ * xΩ h2 h12 hs j k +
        algebraMap K Ω (tB hs (2 * (j + 1))).a₆ := by
  have h := congrArg (iotaQN h2 h12 hs j) (cub_rel h2 h12 hs (2 * (j + 1)) k)
  simpa only [xΩ, yΩ, map_add, map_mul, map_pow, AlgHom.commutes] using h

theorem xΩ_pair (i : Fin 3) {d : ZMod (2 * (j + 1))} (hd : d ≠ 0) (k : ZMod (2 * (j + 1))) :
    bilK (fun a b => algebraMap K Ω (cA hs (2 * (j + 1)) i d a b)) (xΩ h2 h12 hs j k)
      (yΩ h2 h12 hs j k) (xΩ h2 h12 hs j (k + d)) (yΩ h2 h12 hs j (k + d)) = 0 := by
  have h := congrArg (iotaQN h2 h12 hs j).toRingHom
    (cA_rel h2 h12 hs (2 * (j + 1)) (fun _ hd0 hdn => xD_add_ne h2 hs _ hd0 hdn) i hd k)
  rw [map_bilK, map_zero] at h
  simpa only [xΩ, yΩ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes] using h

theorem xΩ_gam {d : ZMod (2 * (j + 1))} (hd : d ≠ 0) :
    ∑ k, (xΩ h2 h12 hs j k - algebraMap K Ω (xD hs (2 * (j + 1)) d)) *
        (xΩ h2 h12 hs j (k + d) - algebraMap K Ω (xD hs (2 * (j + 1)) d)) =
      algebraMap K Ω (gamK hs (2 * (j + 1)) d) := by
  have h := congrArg (iotaQN h2 h12 hs j) (gam_rel h2 h12 hs (2 * (j + 1)) hd)
  simpa only [xΩ, map_sum, map_mul, map_sub, AlgHom.commutes] using h

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem cA_22 {n : ℕ} [NeZero n] {d : ZMod n} (hd : d ≠ 0) (h : 2 * d.val ≤ n) :
    cA hs n 2 d 2 2 = 1 := by
  unfold cA
  rw [if_neg hd]
  split_ifs with h1 h3
  · simp [matR3]
  · simp [matBY]
  · omega

theorem algebraMap_A₀_K (c : K) :
    algebraMap (A₀ K τ) Ω (algebraMap K (A₀ K τ) c) = algebraMap K Ω c :=
  (IsScalarTower.algebraMap_apply K (A₀ K τ) Ω c).symm

/-- **Integrality of the blocks** over `K[τ]` (`isIntegral_blocks`). -/
theorem isIntegral_xyΩ (k : ZMod (2 * (j + 1))) :
    IsIntegral (A₀ K τ) (xΩ h2 h12 hs j k) ∧ IsIntegral (A₀ K τ) (yΩ h2 h12 hs j k) := by
  refine isIntegral_blocks (A := A₀ K τ) (xΩ h2 h12 hs j) (yΩ h2 h12 hs j)
    (algebraMap K _ (tB hs (2 * (j + 1))).a₄) (algebraMap K _ (tB hs (2 * (j + 1))).a₆)
    (fun k => by rw [algebraMap_A₀_K, algebraMap_A₀_K]; exact xΩ_cub h2 h12 hs j k) ?_ ?_ k
  · have hv := xΩ_velu h2 h12 hs j
    rw [sub_eq_iff_eq_add] at hv
    rw [hv]
    exact (isIntegral_DX _).add (isIntegral_K _)
  · intro k k' hkk
    set d : ZMod (2 * (j + 1)) := k' - k with hdd
    have hd : d ≠ 0 := sub_ne_zero.2 (Ne.symm hkk)
    by_cases h : 2 * d.val ≤ 2 * (j + 1)
    · refine ⟨fun a b => algebraMap K _ (cA hs (2 * (j + 1)) 2 d a b), by
        beta_reduce; rw [cA_22 hs hd h, map_one], ?_⟩
      have r := xΩ_pair h2 h12 hs j 2 hd k
      rw [show k + d = k' by rw [hdd]; ring] at r
      simpa only [bilK, algebraMap_A₀_K] using r
    · have hd' : -d ≠ 0 := neg_ne_zero.2 hd
      have hv : (-d).val = 2 * (j + 1) - d.val := by rw [ZMod.neg_val, if_neg hd]
      have h' : 2 * (-d).val ≤ 2 * (j + 1) := by rw [hv]; omega
      refine ⟨fun a b => algebraMap K _ (cA hs (2 * (j + 1)) 2 (-d) b a), by
        beta_reduce; rw [cA_22 hs hd' h', map_one], ?_⟩
      have r := xΩ_pair h2 h12 hs j 2 hd' k'
      rw [show k' + -d = k by rw [hdd]; ring, bilK_swap] at r
      simpa only [bilK, algebraMap_A₀_K] using r

/-- `x_k ∈ R'`. -/
def xR (k : ZMod (2 * (j + 1))) : RQN h2 h12 hs j :=
  CoordRing.mk (xΩ h2 h12 hs j k) (by rw [fieldData_L]; exact xΩ_mem h2 h12 hs j k)
    (isIntegral_xyΩ h2 h12 hs j k).1

/-- `y_k ∈ R'`. -/
def yR (k : ZMod (2 * (j + 1))) : RQN h2 h12 hs j :=
  CoordRing.mk (yΩ h2 h12 hs j k) (by rw [fieldData_L]; exact yΩ_mem h2 h12 hs j k)
    (isIntegral_xyΩ h2 h12 hs j k).2

theorem algebraMap_xR (k : ZMod (2 * (j + 1))) :
    algebraMap (RQN h2 h12 hs j) Ω (xR h2 h12 hs j k) = xΩ h2 h12 hs j k :=
  CoordRing.algebraMap_mk _ _ _

theorem algebraMap_yR (k : ZMod (2 * (j + 1))) :
    algebraMap (RQN h2 h12 hs j) Ω (yR h2 h12 hs j k) = yΩ h2 h12 hs j k :=
  CoordRing.algebraMap_mk _ _ _

theorem algebraMap_RQN_K (c : K) :
    algebraMap (RQN h2 h12 hs j) Ω (algebraMap K (RQN h2 h12 hs j) c) = algebraMap K Ω c :=
  (IsScalarTower.algebraMap_apply K _ Ω c).symm

/-- **The fibre property**: two `R`-algebra maps `R' → Ω` agree or differ by a nonzero cyclic shift
of the blocks. -/
theorem fibreN (φ φ' : RQN h2 h12 hs j →ₐ[(DX t).R] Ω) :
    φ' = φ ∨ ∃ m : ZMod (2 * (j + 1)), m ≠ 0 ∧ ∀ k, φ' (xR h2 h12 hs j k) =
      φ (xR h2 h12 hs j (k + m)) ∧ φ' (yR h2 h12 hs j k) = φ (yR h2 h12 hs j (k + m)) := by
  obtain ⟨σ₁, hσ₁, e₁⟩ := exists_aut_of_algHom _ _ _ _ φ
  obtain ⟨σ₂, hσ₂, e₂⟩ := exists_aut_of_algHom _ _ _ _ φ'
  obtain ⟨p₁, hp₁⟩ := iotaQN_galois h2 h12 hs j σ₁ hσ₁
  obtain ⟨p₂, hp₂⟩ := iotaQN_galois h2 h12 hs j σ₂ hσ₂
  by_cases he : p₁.2 = p₂.2
  · left
    ext r
    rw [e₁, e₂]
    have hr : algebraMap (RQN h2 h12 hs j) Ω r ∈ levelQN h2 h12 hs j :=
      (fieldData_L (transcendental_tau t.tateCurve) (levelQN h2 h12 hs j)
        (isOpen_levelQN h2 h12 hs j)).le (CoordRing.algebraMap_mem r)
    exact (eqOn_levelQN h2 h12 hs j hp₁ hp₂ he hr).symm
  · right
    refine ⟨((p₂.2 : ℕ) : ZMod (2 * (j + 1))) - ((p₁.2 : ℕ) : ZMod (2 * (j + 1))), ?_,
      fun k => ?_⟩
    · intro h0
      apply he
      have := congrArg ZMod.val (sub_eq_zero.1 h0)
      rw [ZMod.val_natCast_of_lt p₂.2.2, ZMod.val_natCast_of_lt p₁.2.2] at this
      exact Fin.ext this.symm
    · obtain ⟨a₁, b₁⟩ := galois_xΩ h2 h12 hs j hp₁
        (k + (((p₂.2 : ℕ) : ZMod (2 * (j + 1))) - ((p₁.2 : ℕ) : ZMod (2 * (j + 1)))))
      obtain ⟨a₂, b₂⟩ := galois_xΩ h2 h12 hs j hp₂ k
      have hk : k + (((p₂.2 : ℕ) : ZMod (2 * (j + 1))) - ((p₁.2 : ℕ) : ZMod (2 * (j + 1)))) +
          ((p₁.2 : ℕ) : ZMod (2 * (j + 1))) = k + ((p₂.2 : ℕ) : ZMod (2 * (j + 1))) := by ring
      rw [e₁, e₂, e₁, e₂, algebraMap_xR, algebraMap_xR, algebraMap_yR, algebraMap_yR, a₁, a₂, b₁,
        b₂, hk]
      exact ⟨rfl, rfl⟩

end InputN

/-! ### Homogenisation and the patterns of `NGon.RedCoeffs` -/

theorem homog_bilK {K L : Type*} [Field K] [CommRing L] [Algebra K L] (c : Fin 3 → Fin 3 → K)
    {π : K} (hπ : π ≠ 0) (x y x' y' : L) :
    ∑ a, ∑ b, algebraMap K L (c a b / π ^ (coeffWt a + coeffWt b)) *
        ![algebraMap K L π, x, y] a * ![algebraMap K L π, x', y'] b =
      bilK (fun a b => algebraMap K L (c a b)) x y x' y' := by
  have h : algebraMap K L π * algebraMap K L π⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hπ, map_one]
  rw [bilK_eq]
  simp only [Fin.sum_univ_three, coeffWt, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, div_eq_mul_inv, ← inv_pow, map_mul,
    map_pow]
  linear_combination (algebraMap K L (c 0 1) * x' + algebraMap K L (c 0 2) * y' +
    algebraMap K L (c 1 0) * x + algebraMap K L (c 2 0) * y +
    algebraMap K L (c 0 0) * (algebraMap K L π * algebraMap K L π⁻¹ + 1)) * h

section Pats

open TemperedFundamentalGroups.NGon in
theorem coe_pats {K : Type*} [Field K] {O : ValuationSubring K} (a b : Fin 3) :
    ((pA0 (O := O) a b : O) : K) = patA0 a b ∧ ((pA1 (O := O) a b : O) : K) = patA1 a b ∧
      ((pY (O := O) a b : O) : K) = patY a b ∧ ((pB0 (O := O) a b : O) : K) = patB0 a b ∧
      ((pB1 (O := O) a b : O) : K) = patB1 a b := by
  fin_cases a <;> fin_cases b <;> simp [pA0, pA1, pY, pB0, pB1, patA0, patA1, patY, patB0, patB1]

end Pats

/-! ### `NGon.Input` for `E_{q^{N_j}}` and (Z_{N_j}) = `ZM j` -/

section ZMN

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve KummerTheory KummerTheory.Curve CurvesJacobian.Cusp
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

variable (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)
  [t.tateCurve.IsElliptic] (j : ℕ)

omit [CharZero K] in
include hs in
theorem norm_cxN_le : ‖cxN hs j‖ ≤ ‖(t.q : K)‖ ∧ ‖cyN hs j‖ ≤ ‖(t.q : K)‖ := by
  have h1 := t.norm_eisenstein_le 1
  have h3 := (tB hs (2 * (j + 1))).norm_eisenstein_le 1
  have hq : ‖((tB hs (2 * (j + 1))).q : K)‖ ≤ ‖(t.q : K)‖ := by
    rw [norm_tB_q]; exact pow_le_of_le_one t.norm_q_pos.le t.norm_lt_one.le (by omega)
  have hn : ∀ m : ℕ, ‖(m : K)‖ ≤ 1 := fun m => IsUltrametricDist.norm_natCast_le_one K m
  have h2' : ‖(2 : K)‖ ≤ 1 := by exact_mod_cast hn 2
  refine ⟨norm_sub_le_max' _ _ |>.trans (max_le ?_ ?_), norm_sub_le_max' _ _ |>.trans
    (max_le h1 ?_)⟩
  · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) h2').trans h1
  · rw [norm_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ h2' (norm_nonneg _) (hn _))).trans
      (h3.trans hq)
  · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (hn _)).trans (h3.trans hq)

/-- **The input of `NGon.exists_object`** for `E_{q^{N_j}} → E_q` (`j ≥ 1`). -/
theorem exists_NGonInput (hj : 1 ≤ j) (O : ValuationSubring K)
    (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) :
    ∃ I : NGon.Input O (RQN h2 h12 hs j) (2 * (j + 1)) (tateDataX O hO hs h12),
      I.x = xR h2 h12 hs j ∧ I.y = yR h2 h12 hs j := by
  have hn4 : 4 ≤ 2 * (j + 1) := by omega
  obtain ⟨hs0, hs1⟩ := norm_s_pos_lt' hs
  have hsK : ((tateDataX O hO hs h12).π : K) = s := rfl
  have hs0' : (s : K) ≠ 0 := s.ne_zero
  have hq : ‖((tB hs (2 * (j + 1))).q : K)‖ ≤ ‖(t.q : K)‖ := by
    rw [norm_tB_q]; exact pow_le_of_le_one t.norm_q_pos.le t.norm_lt_one.le (by omega)
  have hsq : ‖(t.q : K)‖ = ‖(s : K)‖ ^ 2 := norm_q_eq_s_sq hs
  -- `x/s ∈ O` (and in `𝔪`) for `‖x‖ ≤ ‖q‖`
  have hdiv : ∀ {x : K}, ‖x‖ ≤ ‖(t.q : K)‖ → ‖x / (s : K)‖ ≤ ‖(s : K)‖ := fun {x} hx => by
    rw [norm_div, div_le_iff₀ hs0, ← sq, ← hsq]; exact hx
  obtain ⟨b₄', hb₄⟩ : ∃ b : O, (s : K) ^ 2 * b = (tB hs (2 * (j + 1))).a₄ :=
    ⟨⟨_, mem_O_div O hO hs ((tB hs (2 * (j + 1))).norm_a₄_le.trans hq)⟩,
      mul_div_cancel₀ _ (pow_ne_zero 2 hs0')⟩
  obtain ⟨b₆', hb₆⟩ : ∃ b : O, (s : K) ^ 2 * b = (tB hs (2 * (j + 1))).a₆ :=
    ⟨⟨_, mem_O_div O hO hs ((norm_a₆_le (t := tB hs (2 * (j + 1))) h12).trans hq)⟩,
      mul_div_cancel₀ _ (pow_ne_zero 2 hs0')⟩
  have hxD : ∀ d : ZMod (2 * (j + 1)), d ≠ 0 → ‖xD hs (2 * (j + 1)) d‖ ≤ ‖(t.q : K)‖ :=
    fun d hd => (norm_XY_le_q hs _ (norm_spow hs d.val)
      (Nat.pos_of_ne_zero ((ZMod.val_ne_zero d).2 hd)) d.val_lt).1
  let cP : Fin 3 → ZMod (2 * (j + 1)) → Fin 3 → Fin 3 → O := fun i d a b =>
    ⟨cPK hs _ i d a b, (hO _).2 (norm_cPK_le h2 hs _ hn4 i d a b)⟩
  let e : ZMod (2 * (j + 1)) → O := fun d => if hd : d = 0 then 0 else
    ⟨xD hs _ d / s, (hO _).2 ((hdiv (hxD d hd)).trans hs1.le)⟩
  let g : ZMod (2 * (j + 1)) → O := fun d => if hd : d = 0 then 0 else
    ⟨gamK hs _ d / (s : K) ^ 2, mem_O_div O hO hs (norm_gamK_le hs _ h2 hd)⟩
  let ε : O := ⟨cxN hs j / s, (hO _).2 ((hdiv (norm_cxN_le hs j).1).trans hs1.le)⟩
  let κ : O := ⟨cyN hs j / s, (hO _).2 ((hdiv (norm_cxN_le hs j).2).trans hs1.le)⟩
  have he : ∀ d, d ≠ 0 → (s : K) * (e d : K) = xD hs _ d := fun d hd => by
    simp only [e, dif_neg hd]; field_simp
  have hg : ∀ d, d ≠ 0 → (s : K) ^ 2 * (g d : K) = gamK hs _ d := fun d hd => by
    simp only [g, dif_neg hd]; field_simp
  have hmem : ∀ {x : O}, ‖(x : K)‖ ≤ ‖(s : K)‖ → x ∈ IsLocalRing.maximalIdeal O :=
    fun hx => mem_maximalIdeal_of_norm_lt O hO (hx.trans_lt hs1)
  refine ⟨⟨b₄', b₆', cP, e, g, ε, κ, xR h2 h12 hs j, yR h2 h12 hs j, fun k => ?_,
    fun i d k hd => ?_, fun d hd => ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · -- the block cubics
    rw [hsK, hb₄, hb₆]
    apply CoordRing.ext
    simp only [map_add, map_mul, map_pow, algebraMap_RQN_K, algebraMap_xR, algebraMap_yR]
    exact xΩ_cub h2 h12 hs j k
  · -- the pair relations
    rw [hsK]
    simp only [cP, cPK]
    rw [homog_bilK _ hs0']
    apply CoordRing.ext
    rw [map_zero, map_bilK]
    simpa only [algebraMap_RQN_K, algebraMap_xR, algebraMap_yR] using xΩ_pair h2 h12 hs j i hd k
  · -- the cyclic quadrics
    rw [hsK, he d hd, hg d hd]
    apply CoordRing.ext
    simp only [map_sum, map_mul, map_sub, algebraMap_RQN_K, algebraMap_xR]
    exact xΩ_gam h2 h12 hs j hd
  · -- Vélu, `x`
    rw [hsK, show (s : K) * (ε : K) = cxN hs j from by simp only [ε]; field_simp]
    apply CoordRing.ext
    rw [map_sub, map_sum, algebraMap_RQN_K]
    simp only [algebraMap_xR]
    rw [← IsScalarTower.algebraMap_apply]
    exact (xΩ_velu h2 h12 hs j).symm
  · -- Vélu, `y`
    rw [hsK, show (s : K) * (κ : K) = cyN hs j from by simp only [κ]; field_simp]
    apply CoordRing.ext
    rw [map_add, map_sum, algebraMap_RQN_K]
    simp only [algebraMap_yR]
    rw [← IsScalarTower.algebraMap_apply]
    exact (yΩ_velu h2 h12 hs j).symm
  · -- `Good`
    refine ⟨⟨fun d hd0 hdn a b => ?_, fun d hdn a b => ?_, fun d => ?_, fun d hd2 hdn => ?_⟩,
      by omega, ?_, ?_⟩
    · obtain ⟨r0, r1, r2⟩ := cPK_A h2 hs _ hd0 hdn a b
      obtain ⟨c0, c1, c2, -, -⟩ := coe_pats (O := O) a b
      exact ⟨hmem (by push_cast; rw [c0]; exact r0), hmem (by push_cast; rw [c1]; exact r1),
        hmem (by push_cast; rw [c2]; exact r2)⟩
    · obtain ⟨r0, r1, r2⟩ := cPK_B h2 hs _ hn4 hdn a b
      obtain ⟨-, -, c2, c3, c4⟩ := coe_pats (O := O) a b
      exact ⟨hmem (by push_cast; rw [c3]; exact r0), hmem (by push_cast; rw [c4]; exact r1),
        hmem (by push_cast; rw [c2]; exact r2)⟩
    · by_cases hd : d = 0
      · simp only [e, dif_pos hd]; exact Ideal.zero_mem _
      · exact hmem (by simp only [e, dif_neg hd]; exact hdiv (hxD d hd))
    · have hd : d ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hd2; omega
      refine hmem ?_
      simp only [g, dif_neg hd]
      rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
      have := norm_gamK_le_sq hs _ h2 hd2 hdn
      rw [hsq] at this
      calc ‖gamK hs _ d‖ ≤ (‖(s : K)‖ ^ 2) ^ 2 := this
        _ ≤ ‖(s : K)‖ * ‖(s : K)‖ ^ 2 := by
          rw [← pow_mul, ← pow_succ']; exact pow_le_pow_of_le_one hs0.le hs1.le (by norm_num)
    · -- `g_1` is a unit
      have hv1 : (1 : ZMod (2 * (j + 1))).val = 1 := by
        simpa using ZMod.val_natCast_of_lt (n := 2 * (j + 1)) (a := 1) (by omega)
      have h1 : (1 : ZMod (2 * (j + 1))) ≠ 0 := fun h => by
        rw [h, ZMod.val_zero] at hv1; exact zero_ne_one hv1
      refine isUnit_of_norm_eq_one O hO ?_
      simp only [g, dif_neg h1]
      rw [norm_div, norm_pow, norm_gamK_one hs _ h2 hv1 (by omega), hsq, div_self (by positivity)]
    · -- `𝔪 = √(π)`
      intro c hc
      have hc1 : ‖(c : K)‖ < 1 := by
        by_contra h
        have h1 : ‖(c : K)‖ = 1 := le_antisymm ((hO _).1 c.2) (not_lt.1 h)
        exact (IsLocalRing.mem_maximalIdeal _).1 hc (isUnit_of_norm_eq_one O hO h1)
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hs0 hc1
      refine ⟨m, ⟨⟨(c : K) ^ m / s, (hO _).2 ?_⟩, Subtype.ext ?_⟩⟩
      · rw [norm_div, norm_pow, div_le_one hs0]; exact hm.le
      · change (c : K) ^ m = (s : K) * ((c : K) ^ m / s)
        field_simp

/-- **(Z_{N_j}) = `ZM j`** for `j ≥ 1` (TFGD run 8; with `zM_zero` for every `j`):
`Π^tp_Y ≤ Π^tp_{K(E_{q^{N_j}})}`. The `2N`-gon model data (`exists_NGonInput`) and the object of
`NGon.exists_object` (tfg) give the inclusion by `piY_le_range_of_hom`. -/
theorem zM_succ (hj : 1 ≤ j) (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
    (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) :
    ZM h2 h12 O hO hs j V hV := by
  obtain ⟨I, hx, hy⟩ := exists_NGonInput h2 h12 hs j hj O hO
  obtain ⟨Z, a, b, z₀, ha, hb, hinj⟩ :=
    NGon.exists_object (A := (DX t).A) I V hV fun φ φ' => by
      rw [hx, hy]; exact fibreN h2 h12 hs j φ φ'
  exact piY_le_range_of_hom (tateDataX O hO hs h12) V hV
    (muL (transcendental_tau t.tateCurve) (hemiL_open t) (levelQN h2 h12 hs j)
      (isOpen_levelQN h2 h12 hs j)) a b z₀ ha hb hinj

/-- **(Z_{N_j}) for every `j`**: `zM_zero` (the `4`-gon model) and `zM_succ`. -/
theorem zM (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
    (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) (j : ℕ) :
    ZM h2 h12 O hO hs j V hV := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact zM_zero h2 h12 hs O hO V hV
  · exact zM_succ h2 h12 hs j hj O hO V hV

end ZMN

end Iut.EtaleTheta
