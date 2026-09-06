/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Torsion.Identities
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# The division polynomials evaluated at a point: multiples of a point

Let `W : y² = x³ + a₂x² + a₄x + a₆` be a Weierstrass curve with `a₁ = a₃ = 0` over a field `F`
of characteristic `≠ 2`, and `P = (x, y)` a nonsingular point. Mathlib's division polynomials
`ψₙ ∈ F[X][Y]` are the normalised elliptic divisibility sequence `normEDS ψ₂ Ψ₃ preΨ₄`; their
values at `P` form the sequence `eₙ := ψₙ(x, y) = normEDS (2y) (Ψ₃(x)) (preΨ₄(x)) n`
(`Iut.Torsion.eds`), with the `2`-complement `cₙ := complEDS₂ (2y) (Ψ₃(x)) (preΨ₄(x)) n`,
`eₙ cₙ = e₂ₙ`.

The main theorem `Iut.Torsion.good` proves, for every `n`, the classical description of `nP`:

* `eₙ = 0 → nP = 0`;
* `eₙ ≠ 0 → nP = (Xₙ, Yₙ)` is affine with `Xₙ eₙ² = x eₙ² − eₙ₊₁ eₙ₋₁` (i.e. `Xₙ = Φₙ(x)/ψₙ(P)²`)
  and `2Yₙ eₙ³ = cₙ` (i.e. `ψ₂(nP) ψₙ(P)⁴ = ψ₂ₙ(P)`).

The proof is a strong induction on `n` following the doubling recursions of the sequence: for
`n = 2m` one computes `2·(mP)` and for `n = 2m + 1` one computes `mP + (m+1)P`, and the
recursions reduce the claims to the fixed identities of `Iut.Torsion.Ident` for the points
`mP`, `mP ± P`, `(m+1)P + P`; the degenerate cases (`mP = 0`, `mP = ±P`, …) are handled
separately. The `2`-torsion points (`y = 0`) are treated first (`good_of_y_eq_zero`).
-/

namespace Iut.Torsion

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

open scoped Classical

variable {F : Type*} [Field F] {W : Affine F}

/-! ### The sequence `ψₙ(P)` -/

/-- The value `ψₙ(x, y)` of the `n`-division polynomial at `(x, y)`, as the normalised EDS with
initial values `2y`, `Ψ₃(x)`, `preΨ₄(x)` (for `a₁ = a₃ = 0`). -/
noncomputable def eds (W : Affine F) (x y : F) (n : ℤ) : F :=
  normEDS (2 * y) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n

/-- The `2`-complement `cₙ` of the sequence `ψₙ(x, y)`: `ψₙ(P) cₙ = ψ₂ₙ(P)`. -/
noncomputable def edsC (W : Affine F) (x y : F) (n : ℤ) : F :=
  complEDS₂ (2 * y) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n

section eds

variable (W : Affine F) (x y : F)

@[simp] theorem eds_zero : eds W x y 0 = 0 := normEDS_zero ..
@[simp] theorem eds_one : eds W x y 1 = 1 := normEDS_one ..
@[simp] theorem eds_two : eds W x y 2 = 2 * y := normEDS_two ..
@[simp] theorem eds_three : eds W x y 3 = W.Ψ₃.eval x := normEDS_three ..
@[simp] theorem eds_four : eds W x y 4 = W.preΨ₄.eval x * (2 * y) := normEDS_four ..
@[simp] theorem eds_neg (n : ℤ) : eds W x y (-n) = -eds W x y n := normEDS_neg ..

theorem eds_even (m : ℤ) : eds W x y (2 * m) * (2 * y) =
    eds W x y (m - 1) ^ 2 * eds W x y m * eds W x y (m + 2) -
      eds W x y (m - 2) * eds W x y m * eds W x y (m + 1) ^ 2 :=
  normEDS_even ..

theorem eds_odd (m : ℤ) : eds W x y (2 * m + 1) =
    eds W x y (m + 2) * eds W x y m ^ 3 - eds W x y (m - 1) * eds W x y (m + 1) ^ 3 :=
  normEDS_odd ..

theorem eds_mul_edsC (k : ℤ) : eds W x y k * edsC W x y k = eds W x y (2 * k) :=
  normEDS_mul_complEDS₂ ..

theorem edsC_mul (k : ℤ) : edsC W x y k * (2 * y) =
    eds W x y (k - 1) ^ 2 * eds W x y (k + 2) - eds W x y (k - 2) * eds W x y (k + 1) ^ 2 :=
  complEDS₂_mul_b ..

@[simp] theorem edsC_one : edsC W x y 1 = 2 * y := complEDS₂_one ..
@[simp] theorem edsC_two : edsC W x y 2 = W.preΨ₄.eval x := complEDS₂_two ..

/-- `eₙ` is the value of Mathlib's `ψₙ` at `(x, y)`. -/
theorem eds_eq_evalEval (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (n : ℤ) :
    eds W x y n = (W.ψ n).evalEval x y := by
  rw [eds, WeierstrassCurve.ψ, ← coe_evalEvalRingHom, map_normEDS, coe_evalEvalRingHom,
    evalEval_C, evalEval_C, ψ₂, evalEval_polynomialY, ha₁, ha₃]
  ring_nf

/-- `eds 5 = preΨ₄(x)(2y)⁴ − Ψ₃(x)³`. -/
theorem eds_five : eds W x y 5 = W.preΨ₄.eval x * (2 * y) ^ 4 - (W.Ψ₃.eval x) ^ 3 := by
  have := eds_odd W x y 2
  norm_num at this
  linear_combination this

/-- `c₃ · 2y = (2y)²·e₅ − e₄²`. -/
theorem edsC_three_mul :
    edsC W x y 3 * (2 * y) =
      (2 * y) ^ 2 * (W.preΨ₄.eval x * (2 * y) ^ 4 - (W.Ψ₃.eval x) ^ 3) -
        (W.preΨ₄.eval x * (2 * y)) ^ 2 := by
  have := edsC_mul W x y 3
  norm_num at this
  rw [this, eds_five]

/-! ### The recursions in canonical index form -/

theorem eds_two_mul_sub_one (m : ℤ) : eds W x y (2 * m - 1) =
    eds W x y (m + 1) * eds W x y (m - 1) ^ 3 - eds W x y (m - 2) * eds W x y m ^ 3 := by
  have := eds_odd W x y (m - 1)
  rw [show 2 * (m - 1) + 1 = 2 * m - 1 by ring, show m - 1 + 2 = m + 1 by ring,
    show m - 1 - 1 = m - 2 by ring, show m - 1 + 1 = m by ring] at this
  exact this

theorem eds_two_mul_add_two (m : ℤ) :
    eds W x y (2 * m + 2) = eds W x y (m + 1) * edsC W x y (m + 1) := by
  rw [eds_mul_edsC, show 2 * (m + 1) = 2 * m + 2 by ring]

theorem eds_two_mul_sub_two (m : ℤ) :
    eds W x y (2 * m - 2) = eds W x y (m - 1) * edsC W x y (m - 1) := by
  rw [eds_mul_edsC, show 2 * (m - 1) = 2 * m - 2 by ring]

theorem edsC_two_mul (m : ℤ) : edsC W x y (2 * m) * (2 * y) =
    eds W x y (2 * m - 1) ^ 2 * eds W x y (2 * m + 2) -
      eds W x y (2 * m - 2) * eds W x y (2 * m + 1) ^ 2 :=
  edsC_mul W x y (2 * m)

theorem edsC_two_mul_add_one (m : ℤ) : edsC W x y (2 * m + 1) * (2 * y) =
    eds W x y (2 * m) ^ 2 * eds W x y (2 * m + 3) -
      eds W x y (2 * m - 1) * eds W x y (2 * m + 2) ^ 2 := by
  have := edsC_mul W x y (2 * m + 1)
  rw [show 2 * m + 1 - 1 = 2 * m by ring, show 2 * m + 1 + 2 = 2 * m + 3 by ring,
    show 2 * m + 1 - 2 = 2 * m - 1 by ring, show 2 * m + 1 + 1 = 2 * m + 2 by ring] at this
  exact this

theorem eds_two_mul_add_three (m : ℤ) : eds W x y (2 * m + 3) =
    eds W x y (m + 3) * eds W x y (m + 1) ^ 3 - eds W x y m * eds W x y (m + 2) ^ 3 := by
  have := eds_odd W x y (m + 1)
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, show m + 1 + 2 = m + 3 by ring,
    show m + 1 - 1 = m by ring, show m + 1 + 1 = m + 2 by ring] at this
  exact this

end eds

/-! ### The curve `y² = x³ + a₂x² + a₄x + a₆` -/

section curve

variable [NeZero (2 : F)] (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
include ha₁ ha₃

omit [NeZero (2 : F)] in
theorem negY_eq (x y : F) : W.negY x y = -y := by
  simp [negY, ha₁, ha₃]

omit [NeZero (2 : F)] in
theorem equation_iff₀ (x y : F) :
    W.Equation x y ↔ y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  rw [equation_iff, ha₁, ha₃]; simp

omit [NeZero (2 : F)] in
theorem addX_eq (x₁ x₂ ℓ : F) : W.addX x₁ x₂ ℓ = ℓ ^ 2 - W.a₂ - x₁ - x₂ := by
  simp [addX, ha₁]

omit [NeZero (2 : F)] in
theorem addY_eq (x₁ x₂ y₁ ℓ : F) :
    W.addY x₁ x₂ y₁ ℓ = -(ℓ * ((ℓ ^ 2 - W.a₂ - x₁ - x₂) - x₁) + y₁) := by
  simp [addY, negY, negAddY, addX, ha₁, ha₃]

omit [NeZero (2 : F)] in
theorem slope_mul_of_X_ne {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ ≠ x₂) :
    W.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
  rw [slope_of_X_ne hx, div_mul_cancel₀ _ (sub_ne_zero.mpr hx)]

theorem slope_mul_of_Y_ne {x₁ y₁ : F} (hy : y₁ ≠ 0) :
    W.slope x₁ x₁ y₁ y₁ * (2 * y₁) = 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ := by
  have hy' : y₁ ≠ W.negY x₁ y₁ := by
    rw [negY_eq ha₁ ha₃]
    intro h
    apply hy
    have : (2 : F) * y₁ = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left (NeZero.ne 2)
  rw [slope_of_Y_ne rfl hy', negY_eq ha₁ ha₃, ha₁]
  have h2 : y₁ - -y₁ = 2 * y₁ := by ring
  rw [h2, div_mul_cancel₀ _ (mul_ne_zero (NeZero.ne 2) hy)]
  ring

omit [NeZero (2 : F)] in
theorem Ψ₃_eval (x : F) : W.Ψ₃.eval x = Ident.Ψ₃v W.a₂ W.a₄ W.a₆ x := by
  simp only [WeierstrassCurve.Ψ₃, b₂, b₄, b₆, b₈, ha₁, ha₃, Ident.Ψ₃v]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]
  ring

omit [NeZero (2 : F)] in
theorem preΨ₄_eval (x : F) : W.preΨ₄.eval x = Ident.preΨ₄v W.a₂ W.a₄ W.a₆ x := by
  simp only [WeierstrassCurve.preΨ₄, b₂, b₄, b₆, b₈, ha₁, ha₃, Ident.preΨ₄v]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]
  ring

/-- `y ≠ 0` is the condition `y ≠ −y` for a point not to be `2`-torsion. -/
theorem ne_negY_iff (x y : F) : y ≠ W.negY x y ↔ y ≠ 0 := by
  rw [negY_eq ha₁ ha₃]
  constructor
  · intro h hy; exact h (by rw [hy, neg_zero])
  · intro hy h
    apply hy
    have : (2 : F) * y = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left (NeZero.ne 2)

end curve

/-! ### The claims about `n • P` -/

section main

variable [NeZero (2 : F)] (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x y : F} (h : W.Nonsingular x y)

/-- The description of `n • P` by the division polynomials at `P = (x, y)`: `eₙ = 0 → nP = 0`,
and if `eₙ ≠ 0` then `nP = (Xₙ, Yₙ)` with `Xₙ eₙ² = x eₙ² − eₙ₊₁ eₙ₋₁` and `2Yₙ eₙ³ = cₙ`. -/
def Good (n : ℕ) : Prop :=
  (eds W x y n = 0 → n • Point.some x y h = 0) ∧
  (eds W x y n ≠ 0 → ∃ (X Y : F) (hXY : W.Nonsingular X Y),
    n • Point.some x y h = Point.some X Y hXY ∧
    X * eds W x y n ^ 2 = x * eds W x y n ^ 2 - eds W x y (n + 1) * eds W x y (n - 1) ∧
    2 * Y * eds W x y n ^ 3 = edsC W x y n)

variable {h}

theorem Good.smul_eq_zero_iff {n : ℕ} (hg : Good h n) :
    n • Point.some x y h = 0 ↔ eds W x y n = 0 := by
  refine ⟨fun h0 => ?_, hg.1⟩
  by_contra hne
  obtain ⟨X, Y, hXY, hn, -, -⟩ := hg.2 hne
  rw [hn] at h0
  exact Point.some_ne_zero hXY h0

theorem Good.eds_ne_zero {n : ℕ} (hg : Good h n) (hn : n • Point.some x y h ≠ 0) :
    eds W x y n ≠ 0 :=
  fun h0 => hn (hg.1 h0)

theorem Good.eds_eq_zero {n : ℕ} (hg : Good h n) (hn : n • Point.some x y h = 0) :
    eds W x y n = 0 :=
  hg.smul_eq_zero_iff.mp hn

variable (h)

theorem good_zero : Good h 0 := by
  refine ⟨fun _ => zero_smul ℕ _, fun h0 => absurd (by simp) h0⟩

theorem good_one : Good h 1 := by
  refine ⟨fun h0 => absurd h0 (by simp), fun _ => ⟨x, y, h, one_smul ℕ _, by simp, by simp⟩⟩

include ha₁ ha₃

theorem hQ_of (hXY : W.Nonsingular x y) :
    y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
  (equation_iff₀ ha₁ ha₃ x y).mp hXY.1

/-- `2P` for `y ≠ 0`, with its coordinates. -/
theorem two_smul_eq (hy : y ≠ 0) :
    2 • Point.some x y h =
      Point.some (W.addX x x (W.slope x x y y)) (W.addY x x y (W.slope x x y y))
        (nonsingular_add h h fun hxy => ((ne_negY_iff ha₁ ha₃ x y).mpr hy) hxy.2) := by
  rw [two_nsmul, Point.add_self_of_Y_ne ((ne_negY_iff ha₁ ha₃ x y).mpr hy)]

theorem good_two (hy : y ≠ 0) : Good h 2 := by
  have hb : (2 : F) * y ≠ 0 := mul_ne_zero (NeZero.ne 2) hy
  refine ⟨fun h0 => absurd h0 (by simpa using hb), fun _ => ?_⟩
  have hμ := slope_mul_of_Y_ne ha₁ ha₃ (x₁ := x) hy
  have hI2 := Ident.double_X (hQ_of ha₁ ha₃ h) hμ hy
  have hI3 := Ident.double_Y (hQ_of ha₁ ha₃ h) hμ hy
  refine ⟨_, _, _, two_smul_eq ha₁ ha₃ h hy, ?_, ?_⟩
  · rw [addX_eq ha₁ ha₃]
    simp only [Nat.cast_ofNat, eds_two, Int.reduceAdd, eds_three, Int.reduceSub, eds_one,
      Ψ₃_eval ha₁ ha₃]
    linear_combination hI2
  · rw [addY_eq ha₁ ha₃]
    simp only [Nat.cast_ofNat, eds_two, edsC_two, preΨ₄_eval ha₁ ha₃]
    linear_combination hI3

include h in
/-- The `x`-coordinate of `2P`: `x(2P)·(2y)² = x·(2y)² − Ψ₃(x)`. -/
theorem two_smul_X (hy : y ≠ 0) :
    W.addX x x (W.slope x x y y) * (2 * y) ^ 2 = x * (2 * y) ^ 2 - W.Ψ₃.eval x := by
  have hμ := slope_mul_of_Y_ne ha₁ ha₃ (x₁ := x) hy
  have hI2 := Ident.double_X (hQ_of ha₁ ha₃ h) hμ hy
  rw [addX_eq ha₁ ha₃, Ψ₃_eval ha₁ ha₃]
  linear_combination hI2

include h in
/-- The `y`-coordinate of `2P`: `2y(2P)·(2y)³ = preΨ₄(x)`. -/
theorem two_smul_Y (hy : y ≠ 0) :
    2 * W.addY x x y (W.slope x x y y) * (2 * y) ^ 3 = W.preΨ₄.eval x := by
  have hμ := slope_mul_of_Y_ne ha₁ ha₃ (x₁ := x) hy
  have hI3 := Ident.double_Y (hQ_of ha₁ ha₃ h) hμ hy
  rw [addY_eq ha₁ ha₃, preΨ₄_eval ha₁ ha₃]
  linear_combination hI3

theorem good_three (hy : y ≠ 0) : Good h 3 := by
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have hb : (2 : F) * y ≠ 0 := mul_ne_zero h2 hy
  have hμ := slope_mul_of_Y_ne ha₁ ha₃ (x₁ := x) hy
  have h2P := two_smul_eq ha₁ ha₃ h hy
  have hX₂ := two_smul_X ha₁ ha₃ h hy
  have hY₂ := two_smul_Y ha₁ ha₃ h hy
  set μ := W.slope x x y y with hμdef
  set X₂ := W.addX x x μ with hX₂def
  set Y₂ := W.addY x x y μ with hY₂def
  obtain ⟨h₂, h2P⟩ : ∃ h₂ : W.Nonsingular X₂ Y₂, 2 • Point.some x y h = Point.some X₂ Y₂ h₂ :=
    ⟨_, h2P⟩
  have h3 : (3 : ℕ) • Point.some x y h = 2 • Point.some x y h + Point.some x y h := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul]
  have hc : (x - X₂) * (2 * y) ^ 2 = W.Ψ₃.eval x := by linear_combination -hX₂
  constructor
  · intro h0
    rw [Nat.cast_ofNat, eds_three] at h0
    have hX : X₂ = x := by
      have : (X₂ - x) * (2 * y) ^ 2 = 0 := by linear_combination -hc - h0
      rcases mul_eq_zero.mp this with h' | h'
      · exact sub_eq_zero.mp h'
      · exact absurd h' (pow_ne_zero _ hb)
    rcases (Point.X_eq_iff (h₁ := h₂) (h₂ := h)).mp hX with h1 | h1
    · exfalso
      have : 2 • Point.some x y h = Point.some x y h := by rw [h2P, h1]
      rw [two_nsmul, add_eq_right] at this
      exact Point.some_ne_zero h this
    · rw [h3, h2P, h1, neg_add_cancel]
  · intro hne
    rw [Nat.cast_ofNat, eds_three] at hne
    have hXx : X₂ ≠ x := by
      intro hX
      apply hne
      rw [← hc, hX, sub_self, zero_mul]
    have hp : W.slope X₂ x Y₂ y * (X₂ - x) = Y₂ - y := slope_mul_of_X_ne ha₁ ha₃ Y₂ y hXx
    have h3P : (3 : ℕ) • Point.some x y h =
        Point.some (W.addX X₂ x (W.slope X₂ x Y₂ y)) (W.addY X₂ x Y₂ (W.slope X₂ x Y₂ y))
          (nonsingular_add h₂ h fun hxy => hXx hxy.1) := by
      rw [h3, h2P, Point.add_of_X_ne hXx]
    -- `2P − P = P` gives the `x`-coordinate of `2P − P`
    have hm : W.slope X₂ x Y₂ (W.negY x y) * (X₂ - x) = Y₂ + y := by
      rw [slope_of_X_ne hXx, negY_eq ha₁ ha₃, div_mul_cancel₀ _ (sub_ne_zero.mpr hXx)]
      ring
    have hsub : Point.some X₂ Y₂ h₂ + -Point.some x y h = Point.some x y h := by
      rw [← h2P, two_nsmul, add_neg_cancel_right]
    rw [Point.neg_some, Point.add_of_X_ne hXx] at hsub
    have hsubX : W.addX X₂ x (W.slope X₂ x Y₂ (W.negY x y)) = x := (Point.some.inj hsub).1
    rw [addX_eq ha₁ ha₃] at hsubX
    have hD := Ident.chord_diff (a₂ := W.a₂) hXx hp hm
    rw [hsubX] at hD
    set lp := W.slope X₂ x Y₂ y with hlp
    refine ⟨_, _, _, h3P, ?_, ?_⟩
    · -- the `x`-coordinate
      have e4 : eds W x y (3 + 1) = W.preΨ₄.eval x * (2 * y) := by norm_num
      have e2 : eds W x y (3 - 1) = 2 * y := by norm_num
      rw [Nat.cast_ofNat, eds_three, e4, e2, addX_eq ha₁ ha₃, ← hc, ← hY₂]
      linear_combination (-16 * y ^ 4) * hD
    · -- the `y`-coordinate
      have hQ₂ := hQ_of ha₁ ha₃ h₂
      have hT : Y₂ * (2 * y) = -2 * y ^ 2 - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) * (X₂ - x) := by
        rw [hY₂def, hX₂def, addY_eq ha₁ ha₃, addX_eq ha₁ ha₃]
        linear_combination (-(μ ^ 2 - W.a₂ - x - x - x)) * hμ
      have hD2 : X₂ * (4 * y ^ 2) =
          (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 - 4 * y ^ 2 * (W.a₂ + 2 * x) := by
        rw [hX₂def, addX_eq ha₁ ha₃]
        linear_combination (μ * (2 * y) + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) * hμ
      have hG3 := Ident.three_Y (hQ_of ha₁ ha₃ h) hQ₂ hT hD2 hp hy
      have hc3 : edsC W x y 3 = (2 * y) * (W.preΨ₄.eval x * (2 * y) ^ 4 - (W.Ψ₃.eval x) ^ 3) -
          (W.preΨ₄.eval x) ^ 2 * (2 * y) := by
        have := edsC_three_mul W x y
        have h' : (edsC W x y 3 - ((2 * y) * (W.preΨ₄.eval x * (2 * y) ^ 4 - (W.Ψ₃.eval x) ^ 3) -
            (W.preΨ₄.eval x) ^ 2 * (2 * y))) * (2 * y) = 0 := by linear_combination this
        rcases mul_eq_zero.mp h' with h' | h'
        · exact sub_eq_zero.mp h'
        · exact absurd h' hb
      rw [Nat.cast_ofNat, eds_three, hc3, addY_eq ha₁ ha₃, ← hc, ← hY₂]
      linear_combination (2 * y) ^ 6 * hG3

/-! ### The even step -/

omit ha₁ ha₃ in
/-- `Good n` when `eₙ = 0` and `n • P = 0`. -/
theorem good_of_eq_zero {n : ℕ} (h0 : eds W x y n = 0) (hn : n • Point.some x y h = 0) :
    Good h n :=
  ⟨fun _ => hn, fun hne => absurd h0 hne⟩

omit ha₁ ha₃ in
theorem smul_succ (k : ℕ) : (k + 1) • Point.some x y h = k • Point.some x y h + Point.some x y h :=
  succ_nsmul _ _

omit ha₁ ha₃ in
theorem smul_pred {k : ℕ} (hk : 1 ≤ k) :
    (k - 1) • Point.some x y h = k • Point.some x y h - Point.some x y h := by
  conv_rhs => rw [← Nat.sub_add_cancel hk, succ_nsmul, add_sub_cancel_right]

/-- Coordinates of `Q + P` for `X ≠ x`. -/
theorem add_eq_of_X_ne {X Y : F} (hQ : W.Nonsingular X Y) (hX : X ≠ x) :
    Point.some X Y hQ + Point.some x y h =
      Point.some (W.addX X x (W.slope X x Y y)) (W.addY X x Y (W.slope X x Y y))
        (nonsingular_add hQ h fun hxy => hX hxy.1) :=
  Point.add_of_X_ne hX

/-- Coordinates of `Q − P` for `X ≠ x`. -/
theorem sub_eq_of_X_ne {X Y : F} (hQ : W.Nonsingular X Y) (hX : X ≠ x) :
    Point.some X Y hQ - Point.some x y h =
      Point.some (W.addX X x (W.slope X x Y (W.negY x y)))
        (W.addY X x Y (W.slope X x Y (W.negY x y)))
        (nonsingular_add hQ ((nonsingular_neg ..).mpr h) fun hxy => hX hxy.1) := by
  rw [sub_eq_add_neg, Point.neg_some, Point.add_of_X_ne hX]

/-- The slope of the chord through `Q` and `−P`. -/
theorem slope_neg_mul {X Y : F} (hX : X ≠ x) :
    W.slope X x Y (W.negY x y) * (X - x) = Y + y := by
  rw [slope_of_X_ne hX, negY_eq ha₁ ha₃, div_mul_cancel₀ _ (sub_ne_zero.mpr hX)]
  ring

/-- If `Q = m • P = (X, Y)` with `(m − 1) • P ≠ 0` and `(m + 1) • P ≠ 0`, then `X ≠ x`. -/
theorem X_ne_of_smul {m : ℕ} (hm : 1 ≤ m) {X Y : F} {hQ : W.Nonsingular X Y}
    (hmP : m • Point.some x y h = Point.some X Y hQ)
    (h₁ : (m - 1) • Point.some x y h ≠ 0) (h₂ : (m + 1) • Point.some x y h ≠ 0) : X ≠ x := by
  intro hX
  rcases (Point.X_eq_iff (h₁ := hQ) (h₂ := h)).mp hX with h' | h'
  · apply h₁
    rw [smul_pred h hm, hmP, h', sub_self]
  · apply h₂
    rw [smul_succ h, hmP, h', neg_add_cancel]

/-- Coordinates of `−(2 • P)` for `y ≠ 0`. -/
theorem neg_two_smul_eq (hy : y ≠ 0) :
    -(2 • Point.some x y h) =
      Point.some (W.addX x x (W.slope x x y y))
        (W.negY (W.addX x x (W.slope x x y y)) (W.addY x x y (W.slope x x y y)))
        ((nonsingular_neg ..).mpr
          (nonsingular_add h h fun hxy => ((ne_negY_iff ha₁ ha₃ x y).mpr hy) hxy.2)) := by
  rw [two_smul_eq ha₁ ha₃ h hy, Point.neg_some]

/-- The even step of the induction: `Good (2m)` from `Good (m − 1)`, `Good m`, `Good (m + 1)`,
for `m ≥ 2`. -/
theorem good_even (hy : y ≠ 0) (m : ℕ) (hm : 2 ≤ m)
    (g₁ : Good h (m - 1)) (g₂ : Good h m) (g₃ : Good h (m + 1)) : Good h (2 * m) := by
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have hb : (2 : F) * y ≠ 0 := mul_ne_zero h2 hy
  have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  have hm1' : ((m - 1 : ℕ) : ℤ) + 1 = (m : ℤ) := by omega
  have hm1'' : ((m - 1 : ℕ) : ℤ) - 1 = (m : ℤ) - 2 := by omega
  have hm2 : ((m + 1 : ℕ) : ℤ) + 1 = (m : ℤ) + 2 := by push_cast; ring
  have hm2' : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
  have hsmul : (2 * m) • Point.some x y h = 2 • (m • Point.some x y h) := mul_nsmul' _ _ _
  have hcast : ((2 * m : ℕ) : ℤ) = 2 * (m : ℤ) := by push_cast; ring
  -- the induction hypotheses in canonical index form
  unfold Good at g₁ g₃
  push_cast [Nat.cast_sub (show 1 ≤ m by omega)] at g₁ g₃
  rw [show (m : ℤ) + 1 + 1 = m + 2 by ring, show (m : ℤ) + 1 - 1 = m by ring] at g₃
  rw [show (m : ℤ) - 1 + 1 = m by ring, show (m : ℤ) - 1 - 1 = m - 2 by ring] at g₁
  -- the recursions
  have r_c : eds W x y m * edsC W x y m = eds W x y (2 * m) := eds_mul_edsC W x y m
  have r_odd1 := eds_odd W x y m
  have r_odd2 := eds_two_mul_sub_one W x y m
  have r_C := edsC_two_mul W x y m
  have r_p2 := eds_two_mul_add_two W x y m
  have r_m2 := eds_two_mul_sub_two W x y m
  have r_cm := edsC_mul W x y m
  have r_cp := edsC_mul W x y (m + 1)
  have r_cmm := edsC_mul W x y (m - 1)
  rw [show (m : ℤ) + 1 + 2 = m + 3 by ring, show (m : ℤ) + 1 - 1 = m by ring,
    show (m : ℤ) + 1 - 2 = m - 1 by ring, show (m : ℤ) + 1 + 1 = m + 2 by ring] at r_cp
  rw [show (m : ℤ) - 1 - 1 = m - 2 by ring, show (m : ℤ) - 1 + 2 = m + 1 by ring,
    show (m : ℤ) - 1 - 2 = m - 3 by ring, show (m : ℤ) - 1 + 1 = m by ring] at r_cmm
  -- the `2`-multiples
  have h2P := two_smul_eq ha₁ ha₃ h hy
  have hX₂ := two_smul_X ha₁ ha₃ h hy
  have hY₂ := two_smul_Y ha₁ ha₃ h hy
  have hn2P := neg_two_smul_eq ha₁ ha₃ h hy
  set x₂ := W.addX x x (W.slope x x y y) with hx₂def
  set y₂ := W.addY x x y (W.slope x x y y) with hy₂def
  obtain ⟨h₂, h2P⟩ : ∃ h₂ : W.Nonsingular x₂ y₂, 2 • Point.some x y h = Point.some x₂ y₂ h₂ :=
    ⟨_, h2P⟩
  obtain ⟨h₂', hn2P⟩ : ∃ h₂' : W.Nonsingular x₂ (W.negY x₂ y₂),
      -(2 • Point.some x y h) = Point.some x₂ (W.negY x₂ y₂) h₂' := ⟨_, hn2P⟩
  have hny₂ : W.negY x₂ y₂ = -y₂ := negY_eq ha₁ ha₃ _ _
  have h2P0 : 2 • Point.some x y h ≠ 0 := by rw [h2P]; exact Point.some_ne_zero _
  -- case `eₘ = 0`
  by_cases hem : eds W x y m = 0
  · refine good_of_eq_zero h ?_ ?_
    · rw [hcast, ← r_c, hem, zero_mul]
    · rw [hsmul, g₂.1 hem, smul_zero]
  obtain ⟨X, Y, hQ, hmP, hX, hY⟩ := g₂.2 hem
  have hmP0 : m • Point.some x y h ≠ 0 := by rw [hmP]; exact Point.some_ne_zero _
  -- `e₂ₘ = 2Y eₘ⁴`
  have h3 : eds W x y (2 * m) = 2 * Y * eds W x y m ^ 4 := by
    linear_combination -r_c - eds W x y m * hY
  -- case `Y = 0`: `2Q = 0`
  by_cases hY0 : Y = 0
  · refine good_of_eq_zero h ?_ ?_
    · rw [hcast, h3, hY0]; ring
    · rw [hsmul, hmP, two_nsmul, Point.add_self_of_Y_eq]
      rw [negY_eq ha₁ ha₃, hY0, neg_zero]
  have hQY : Y ≠ W.negY X Y := (ne_negY_iff ha₁ ha₃ X Y).mpr hY0
  have he2m : eds W x y (2 * m) ≠ 0 := by
    rw [h3]; exact mul_ne_zero (mul_ne_zero h2 hY0) (pow_ne_zero _ hem)
  have hμ := slope_mul_of_Y_ne ha₁ ha₃ (x₁ := X) hY0
  have h2Q : (2 * m) • Point.some x y h =
      Point.some (W.addX X X (W.slope X X Y Y)) (W.addY X X Y (W.slope X X Y Y))
        (nonsingular_add hQ hQ fun hxy => hQY hxy.2) := by
    rw [hsmul, hmP, two_nsmul, Point.add_self_of_Y_ne hQY]
  set μ := W.slope X X Y Y with hμdef
  -- the coordinates of `2Q` in terms of `Q ± P`
  have hI2 := Ident.double_X (hQ_of ha₁ ha₃ hQ) hμ hY0
  suffices key : (μ ^ 2 - W.a₂ - X - X) * eds W x y (2 * m) ^ 2 =
      x * eds W x y (2 * m) ^ 2 - eds W x y (2 * m + 1) * eds W x y (2 * m - 1) ∧
      2 * (-(μ * ((μ ^ 2 - W.a₂ - X - X) - X) + Y)) * eds W x y (2 * m) ^ 3 =
        edsC W x y (2 * m) by
    refine ⟨fun h0 => absurd h0 (by rwa [hcast]), fun _ => ⟨_, _, _, h2Q, ?_, ?_⟩⟩
    · rw [hcast, addX_eq ha₁ ha₃]; exact key.1
    · rw [hcast, addY_eq ha₁ ha₃]; exact key.2
  have hc : (x - x₂) * (2 * y) ^ 2 = W.Ψ₃.eval x := by linear_combination -hX₂
  -- abbreviations
  set E1 := eds W x y m with hE1
  set E2 := eds W x y (m + 1) with hE2
  set E0 := eds W x y (m - 1) with hE0
  set E3 := eds W x y (m + 2) with hE3
  set Em1 := eds W x y (m - 2) with hEm1
  set Em := eds W x y (2 * m) with hEm
  set Ep := eds W x y (2 * m + 1) with hEp
  set Emm := eds W x y (2 * m - 1) with hEmm
  set Ep2 := eds W x y (2 * m + 2) with hEp2
  set Em2 := eds W x y (2 * m - 2) with hEm2
  set C1 := edsC W x y m with hC1
  set C2 := edsC W x y (m + 1) with hC2
  set C0 := edsC W x y (m - 1) with hC0
  set Cm := edsC W x y (2 * m) with hCm
  by_cases hep : E2 = 0
  · -- `(m + 1) • P = 0`: `Q = −P`, `2Q = −2P`
    have hm1P : (m + 1) • Point.some x y h = 0 := g₃.1 hep
    have hQP0 : Point.some X Y hQ = -Point.some x y h := by
      rw [← hmP]; exact eq_neg_of_add_eq_zero_left (by rw [← smul_succ h]; exact hm1P)
    have hQP := hQP0
    rw [Point.neg_some] at hQP
    obtain ⟨hXx, hYy⟩ := Point.some.inj hQP
    rw [negY_eq ha₁ ha₃] at hYy
    have hmm : (m - 1) • Point.some x y h = -(2 • Point.some x y h) := by
      rw [smul_pred h (by omega), hmP, hQP0, two_nsmul, neg_add, sub_eq_add_neg]
    have hmm0 : (m - 1) • Point.some x y h ≠ 0 := by rw [hmm, neg_ne_zero]; exact h2P0
    have hem1 : E0 ≠ 0 := by
      intro h0; apply hmm0; apply g₁.1; exact h0
    obtain ⟨Xm, Ym, hQm, hmmP, hXm, hYm⟩ := g₁.2 hem1
    rw [hmmP, hn2P] at hmm
    obtain ⟨hXm', hYm'⟩ := Point.some.inj hmm
    -- the coordinates of `2Q`
    have h2Q' : (2 * m) • Point.some x y h = Point.some x₂ (W.negY x₂ y₂) h₂' := by
      rw [hsmul, hmP, hQP0, smul_neg, hn2P]
    rw [h2Q] at h2Q'
    obtain ⟨hxq, hyq⟩ := Point.some.inj h2Q'
    rw [addX_eq ha₁ ha₃] at hxq
    rw [addY_eq ha₁ ha₃] at hyq
    rw [hyq, hxq, hny₂]
    -- the sequence
    rw [hep] at r_odd1 r_odd2 r_cm
    rw [hYy] at hY h3
    rw [hXm'] at hXm
    rw [hYm', hny₂] at hYm
    have hE3' : E0 ^ 2 * E3 = -(2 * y) ^ 2 * E1 ^ 3 := by
      linear_combination -r_cm - (2 * y) * hY
    have hEm1' : E1 * Em1 * (2 * y) ^ 2 = W.Ψ₃.eval x * E0 ^ 2 := by
      linear_combination (2 * y) ^ 2 * hXm + E0 ^ 2 * hc
    have hE : E3 * Em1 = -W.Ψ₃.eval x * E1 ^ 2 := by
      have hne : E1 * E0 ^ 2 * (2 * y) ^ 2 ≠ 0 :=
        mul_ne_zero (mul_ne_zero hem (pow_ne_zero _ hem1)) (pow_ne_zero _ hb)
      have : (E3 * Em1 - -W.Ψ₃.eval x * E1 ^ 2) * (E1 * E0 ^ 2 * (2 * y) ^ 2) = 0 := by
        linear_combination E1 * Em1 * (2 * y) ^ 2 * hE3' + E1 ^ 3 * (-(2 * y) ^ 2) * hEm1'
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
    constructor
    · rw [h3, r_odd1, r_odd2]
      linear_combination (-E1 ^ 8) * hc - E1 ^ 6 * hE
    · have hEp2' : Ep2 = 0 := by rw [r_p2, hep, zero_mul]
      have hEm2' : Em2 = -(2 * y₂) * E0 ^ 4 := by linear_combination r_m2 - E0 * hYm
      rw [hEp2', hEm2', r_odd1, r_odd2] at r_C
      have : (2 * -y₂ * Em ^ 3 - Cm) * (2 * y) = 0 := by
        rw [h3]
        linear_combination -r_C + 2 * y₂ * E1 ^ 6 * ((2 * y) ^ 2 * E1 ^ 3 - E0 ^ 2 * E3) * hE3'
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hb)
  by_cases hem1 : E0 = 0
  · -- `(m − 1) • P = 0`: `Q = P`, `2Q = 2P`
    have hm1P : (m - 1) • Point.some x y h = 0 := g₁.1 hem1
    have hQP : Point.some X Y hQ = Point.some x y h := by
      rw [← hmP]
      have := hm1P
      rw [smul_pred h (by omega)] at this
      exact sub_eq_zero.mp this
    obtain ⟨hXx, hYy⟩ := Point.some.inj hQP
    have hpp : (m + 1) • Point.some x y h = 2 • Point.some x y h := by
      rw [smul_succ h, hmP, hQP, two_nsmul]
    obtain ⟨Xp, Yp, hQp, hpP, hXp, hYp⟩ := g₃.2 hep
    rw [hpP, h2P] at hpp
    obtain ⟨hXp', hYp'⟩ := Point.some.inj hpp
    have h2Q' : (2 * m) • Point.some x y h = Point.some x₂ y₂ h₂ := by
      rw [hsmul, hmP, hQP, h2P]
    rw [h2Q] at h2Q'
    obtain ⟨hxq, hyq⟩ := Point.some.inj h2Q'
    rw [addX_eq ha₁ ha₃] at hxq
    rw [addY_eq ha₁ ha₃] at hyq
    rw [hyq, hxq]
    rw [hem1] at r_odd1 r_odd2 r_cm
    rw [hYy] at hY h3
    rw [hXp'] at hXp
    rw [hYp'] at hYp
    have hEm1' : Em1 * E2 ^ 2 = -(2 * y) ^ 2 * E1 ^ 3 := by
      linear_combination r_cm + (2 * y) * hY
    have hE3' : E3 * E1 * (2 * y) ^ 2 = W.Ψ₃.eval x * E2 ^ 2 := by
      linear_combination (2 * y) ^ 2 * hXp + E2 ^ 2 * hc
    have hE : E3 * Em1 = -W.Ψ₃.eval x * E1 ^ 2 := by
      have hne : E1 * E2 ^ 2 * (2 * y) ^ 2 ≠ 0 :=
        mul_ne_zero (mul_ne_zero hem (pow_ne_zero _ hep)) (pow_ne_zero _ hb)
      have : (E3 * Em1 - -W.Ψ₃.eval x * E1 ^ 2) * (E1 * E2 ^ 2 * (2 * y) ^ 2) = 0 := by
        linear_combination E3 * E1 * (2 * y) ^ 2 * hEm1' + E1 ^ 3 * (-(2 * y) ^ 2) * hE3'
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
    constructor
    · rw [h3, r_odd1, r_odd2]
      linear_combination (-E1 ^ 8) * hc - E1 ^ 6 * hE
    · have hEm2' : Em2 = 0 := by rw [r_m2, hem1, zero_mul]
      have hEp2' : Ep2 = 2 * y₂ * E2 ^ 4 := by linear_combination r_p2 - E2 * hYp
      rw [hEp2', hEm2', r_odd1, r_odd2] at r_C
      have : (2 * y₂ * Em ^ 3 - Cm) * (2 * y) = 0 := by
        rw [h3]
        linear_combination -r_C + 2 * y₂ * E1 ^ 6 * ((2 * y) ^ 2 * E1 ^ 3 - Em1 * E2 ^ 2) * hEm1'
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hb)
  -- the generic case: `Q ≠ ±P`
  have hmm0 : (m - 1) • Point.some x y h ≠ 0 := by
    intro h0
    obtain ⟨X', Y', h', hh, -, -⟩ := g₁.2 hem1
    rw [hh] at h0
    exact Point.some_ne_zero h' h0
  have hpp0 : (m + 1) • Point.some x y h ≠ 0 := by
    intro h0
    obtain ⟨X', Y', h', hh, -, -⟩ := g₃.2 hep
    rw [hh] at h0
    exact Point.some_ne_zero h' h0
  have hXx : X ≠ x := X_ne_of_smul ha₁ ha₃ h (by omega) hmP hmm0 hpp0
  obtain ⟨Xp, Yp, hQp, hpP, hXp, hYp⟩ := g₃.2 hep
  obtain ⟨Xm, Ym, hQm, hmmP, hXm, hYm⟩ := g₁.2 hem1
  have hpP' := hpP
  rw [smul_succ h, hmP, add_eq_of_X_ne ha₁ ha₃ h hQ hXx] at hpP'
  obtain ⟨hXp', hYp'⟩ := Point.some.inj hpP'
  have hmmP' := hmmP
  rw [smul_pred h (by omega), hmP, sub_eq_of_X_ne ha₁ ha₃ h hQ hXx] at hmmP'
  obtain ⟨hXm', hYm'⟩ := Point.some.inj hmmP'
  rw [addX_eq ha₁ ha₃] at hXp' hXm'
  rw [addY_eq ha₁ ha₃] at hYp' hYm'
  have hp : W.slope X x Y y * (X - x) = Y - y := slope_mul_of_X_ne ha₁ ha₃ Y y hXx
  have hmn : W.slope X x Y (W.negY x y) * (X - x) = Y + y := slope_neg_mul ha₁ ha₃ hXx
  have hI5 := Ident.double_X_sub (hQ_of ha₁ ha₃ hQ) (hQ_of ha₁ ha₃ h) hXx hp hmn hμ hY0
  have hI6 := Ident.double_Y_mul (hQ_of ha₁ ha₃ hQ) (hQ_of ha₁ ha₃ h) hXx hp hmn hμ hY0
  rw [hYp', hYm', hXp', hXm'] at hI6
  rw [hXp', hXm'] at hI5
  have h1 : Ep = E1 ^ 2 * E2 ^ 2 * (X - Xp) := by
    linear_combination r_odd1 + E1 ^ 2 * hXp - E2 ^ 2 * hX
  have h2 : Emm = E1 ^ 2 * E0 ^ 2 * (Xm - X) := by
    linear_combination r_odd2 + E0 ^ 2 * hX - E1 ^ 2 * hXm
  have h4 : Ep2 = 2 * Yp * E2 ^ 4 := by linear_combination r_p2 - E2 * hYp
  have h5 : Em2 = 2 * Ym * E0 ^ 4 := by linear_combination r_m2 - E0 * hYm
  constructor
  · rw [h1, h2, h3]
    linear_combination (-E1 ^ 8) * hI5 +
      E1 ^ 4 * (X - Xp) * (Xm - X) * (E2 * E0 + E1 ^ 2 * (x - X)) * hX
  · rw [h1, h2, h4, h5] at r_C
    have : (2 * (-(μ * ((μ ^ 2 - W.a₂ - X - X) - X) + Y)) * Em ^ 3 - Cm) * (2 * y) = 0 := by
      rw [h3]
      linear_combination E1 ^ 12 * hI6 - r_C -
        E1 ^ 4 * (E1 ^ 2 * (x - X) + E0 * E2) * ((E1 ^ 2 * (x - X)) ^ 2 + (E0 * E2) ^ 2) *
          ((Xm - X) ^ 2 * (2 * Yp) - (X - Xp) ^ 2 * (2 * Ym)) * hX
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hb)

/-- The odd step of the induction: `Good (2m + 1)` from `Good (m − 1)`, …, `Good (m + 2)`, for
`m ≥ 2`. -/
theorem good_odd (hy : y ≠ 0) (m : ℕ) (hm : 2 ≤ m) (g₁ : Good h (m - 1)) (g₂ : Good h m)
    (g₃ : Good h (m + 1)) (g₄ : Good h (m + 2)) : Good h (2 * m + 1) := by
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have hb : (2 : F) * y ≠ 0 := mul_ne_zero h2 hy
  have hsmul : (2 * m + 1) • Point.some x y h =
      m • Point.some x y h + (m + 1) • Point.some x y h := by
    rw [← add_nsmul]; congr 1; omega
  have hcast : ((2 * m + 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 1 := by push_cast; ring
  -- the induction hypotheses in canonical index form
  unfold Good at g₁ g₃ g₄ ⊢
  push_cast [Nat.cast_sub (show 1 ≤ m by omega)] at g₁ g₃ g₄
  rw [show (m : ℤ) + 1 + 1 = m + 2 by ring, show (m : ℤ) + 1 - 1 = m by ring] at g₃
  rw [show (m : ℤ) - 1 + 1 = m by ring, show (m : ℤ) - 1 - 1 = m - 2 by ring] at g₁
  rw [show (m : ℤ) + 2 + 1 = m + 3 by ring, show (m : ℤ) + 2 - 1 = m + 1 by ring] at g₄
  rw [hcast, show 2 * (m : ℤ) + 1 + 1 = 2 * m + 2 by ring, show 2 * (m : ℤ) + 1 - 1 = 2 * m by ring]
  -- the recursions
  have r_c : eds W x y m * edsC W x y m = eds W x y (2 * m) := eds_mul_edsC W x y m
  have r_odd1 := eds_odd W x y m
  have r_odd2 := eds_two_mul_sub_one W x y m
  have r_C := edsC_two_mul_add_one W x y m
  have r_3 := eds_two_mul_add_three W x y m
  have r_p2 := eds_two_mul_add_two W x y m
  have r_cm := edsC_mul W x y m
  have r_cp := edsC_mul W x y (m + 1)
  rw [show (m : ℤ) + 1 + 2 = m + 3 by ring, show (m : ℤ) + 1 - 1 = m by ring,
    show (m : ℤ) + 1 - 2 = m - 1 by ring, show (m : ℤ) + 1 + 1 = m + 2 by ring] at r_cp
  -- abbreviations
  set E1 := eds W x y m with hE1
  set E2 := eds W x y (m + 1) with hE2
  set E0 := eds W x y (m - 1) with hE0
  set E3 := eds W x y (m + 2) with hE3
  set E4 := eds W x y (m + 3) with hE4
  set Em1 := eds W x y (m - 2) with hEm1
  set Em := eds W x y (2 * m) with hEm
  set Ep := eds W x y (2 * m + 1) with hEp
  set Emm := eds W x y (2 * m - 1) with hEmm
  set Ep2 := eds W x y (2 * m + 2) with hEp2
  set E2m3 := eds W x y (2 * m + 3) with hE2m3
  set C1 := edsC W x y m with hC1
  set C2 := edsC W x y (m + 1) with hC2
  set Cp := edsC W x y (2 * m + 1) with hCp
  -- case `eₘ = 0`: `Q = 0`, `(2m+1)P = (m+1)P = P`
  by_cases hem : E1 = 0
  · have hmP : m • Point.some x y h = 0 := g₂.1 hem
    have hpP : (m + 1) • Point.some x y h = Point.some x y h := by
      rw [smul_succ h, hmP, zero_add]
    have hmm : (m - 1) • Point.some x y h = -Point.some x y h := by
      rw [smul_pred h (by omega), hmP, zero_sub]
    have hem1 : E0 ≠ 0 := by
      intro h0
      have := g₁.1 h0
      rw [hmm, neg_eq_zero] at this
      exact Point.some_ne_zero h this
    have hep : E2 ≠ 0 := by
      intro h0
      have := g₃.1 h0
      rw [hpP] at this
      exact Point.some_ne_zero h this
    obtain ⟨Xp, Yp, hQp, hpP', hXp, hYp⟩ := g₃.2 hep
    rw [hpP] at hpP'
    obtain ⟨hXp', hYp'⟩ := Point.some.inj hpP'
    rw [hem] at r_odd1 r_odd2 r_c
    rw [← hYp'] at hYp
    have hEp' : Ep = -E0 * E2 ^ 3 := by rw [r_odd1]; ring
    have hEp0 : Ep ≠ 0 := by
      rw [hEp']; exact mul_ne_zero (neg_ne_zero.mpr hem1) (pow_ne_zero _ hep)
    refine ⟨fun h0 => absurd h0 hEp0, fun _ => ⟨x, y, h, ?_, ?_, ?_⟩⟩
    · rw [hsmul, hmP, hpP, zero_add]
    · rw [← r_c]; ring
    · rw [hEp']
      have hEp2' : Ep2 = 2 * y * E2 ^ 4 := by linear_combination r_p2 - E2 * hYp
      have hEm' : Em = 0 := by rw [← r_c, zero_mul]
      rw [hEp2', hEm', r_odd2] at r_C
      have : (2 * y * (-E0 * E2 ^ 3) ^ 3 - Cp) * (2 * y) = 0 := by linear_combination -r_C
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hb)
  obtain ⟨X, Y, hQ, hmP, hX, hY⟩ := g₂.2 hem
  -- `e₂ₘ = 2Y eₘ⁴`
  have h3 : Em = 2 * Y * E1 ^ 4 := by linear_combination -r_c - E1 * hY
  -- case `eₘ₊₁ = 0`: `Q = −P`, `(2m+1)P = Q = −P`
  by_cases hep : E2 = 0
  · have hpP : (m + 1) • Point.some x y h = 0 := g₃.1 hep
    have hQP0 : Point.some X Y hQ = -Point.some x y h := by
      rw [← hmP]; exact eq_neg_of_add_eq_zero_left (by rw [← smul_succ h]; exact hpP)
    have hQP := hQP0
    rw [Point.neg_some] at hQP
    obtain ⟨hXx, hYy⟩ := Point.some.inj hQP
    rw [negY_eq ha₁ ha₃] at hYy
    have hp2 : (m + 2) • Point.some x y h = Point.some x y h := by
      rw [show m + 2 = m + 1 + 1 from rfl, smul_succ h, hpP, zero_add]
    have hep2 : E3 ≠ 0 := by
      intro h0
      have := g₄.1 h0
      rw [hp2] at this
      exact Point.some_ne_zero h this
    rw [hep] at r_odd1 r_3 r_p2
    rw [hYy] at h3
    have hEp' : Ep = E3 * E1 ^ 3 := by rw [r_odd1]; ring
    have hEp0 : Ep ≠ 0 := by rw [hEp']; exact mul_ne_zero hep2 (pow_ne_zero _ hem)
    refine ⟨fun h0 => absurd h0 hEp0, fun _ => ⟨X, Y, hQ, ?_, ?_, ?_⟩⟩
    · rw [hsmul, hmP, hpP, add_zero]
    · rw [r_p2, hXx]; ring
    · rw [hEp', hYy]
      have hE2m3 : E2m3 = -E1 * E3 ^ 3 := by rw [r_3]; ring
      have hEp2' : Ep2 = 0 := by rw [r_p2, zero_mul]
      rw [hE2m3, hEp2', h3] at r_C
      have : (2 * -y * (E3 * E1 ^ 3) ^ 3 - Cp) * (2 * y) = 0 := by linear_combination -r_C
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hb)
  obtain ⟨Xp, Yp, hQp, hpP, hXp, hYp⟩ := g₃.2 hep
  have h1 : Ep = E1 ^ 2 * E2 ^ 2 * (X - Xp) := by
    linear_combination r_odd1 + E1 ^ 2 * hXp - E2 ^ 2 * hX
  have h4 : Ep2 = 2 * Yp * E2 ^ 4 := by linear_combination r_p2 - E2 * hYp
  have hQQ : Point.some X Y hQ + Point.some Xp Yp hQp = (2 * m + 1) • Point.some x y h := by
    rw [hsmul, hmP, hpP]
  -- case `X = Xp`: `Q = −Q⁺`, `(2m+1)P = 0`
  by_cases hXX : X = Xp
  · refine ⟨fun _ => ?_, fun hne => absurd (by rw [h1, hXX, sub_self, mul_zero]) hne⟩
    rw [← hQQ]
    rcases (Point.X_eq_iff (h₁ := hQ) (h₂ := hQp)).mp hXX with h' | h'
    · exfalso
      have : Point.some x y h = 0 := by
        have := hpP
        rw [smul_succ h, hmP, h', add_eq_left] at this
        exact this
      exact Point.some_ne_zero h this
    · rw [h', neg_add_cancel]
  -- the generic case: `(2m+1)P = Q + Q⁺`
  have hEp0 : Ep ≠ 0 := by
    rw [h1]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hem) (pow_ne_zero _ hep)) (sub_ne_zero.mpr hXX)
  rw [Point.add_of_X_ne hXX] at hQQ
  -- `Q − Q⁺ = −P` and `Q⁺ − Q = P`
  have hsub : Point.some X Y hQ - Point.some Xp Yp hQp = -Point.some x y h := by
    rw [← hmP, ← hpP, smul_succ h]; abel
  rw [sub_eq_of_X_ne ha₁ ha₃ hQp hQ hXX, Point.neg_some] at hsub
  obtain ⟨hsx, -⟩ := Point.some.inj hsub
  have hsub' : Point.some Xp Yp hQp - Point.some X Y hQ = Point.some x y h := by
    rw [← hmP, ← hpP, smul_succ h]; abel
  rw [sub_eq_of_X_ne ha₁ ha₃ hQ hQp (Ne.symm hXX)] at hsub'
  obtain ⟨hsx', hsy'⟩ := Point.some.inj hsub'
  rw [addX_eq ha₁ ha₃] at hsx hsx'
  rw [addY_eq ha₁ ha₃] at hsy'
  have hl : W.slope X Xp Y Yp * (X - Xp) = Y - Yp := slope_mul_of_X_ne ha₁ ha₃ Y Yp hXX
  have hn : W.slope Xp X Yp (W.negY X Y) * (Xp - X) = Yp + Y :=
    slope_neg_mul ha₁ ha₃ (Ne.symm hXX)
  have hn' : W.slope X Xp Y (W.negY Xp Yp) * (X - Xp) = Y + Yp := slope_neg_mul ha₁ ha₃ hXX
  have hL4 := Ident.odd_Y (hQ_of ha₁ ha₃ hQ) (hQ_of ha₁ ha₃ hQp) hl hn
  rw [hsy', hsx'] at hL4
  have hD := Ident.chord_diff (a₂ := W.a₂) hXX hl hn'
  rw [hsx] at hD
  -- the auxiliary identities `E2² e₂ₘ₋₁ = E1⁶ A`, `E1² e₂ₘ₊₃ = E2⁶ B`
  have hA : E2 ^ 2 * Emm = E1 ^ 6 * (4 * Y * y + (x - X) ^ 2 * (Xp - X)) := by
    have : (E2 ^ 2 * Emm - E1 ^ 6 * (4 * Y * y + (x - X) ^ 2 * (Xp - X))) * (E1 * E2 ^ 5) = 0 := by
      linear_combination (E1 * E2 ^ 7) * r_odd2 + (-E1 ^ 4 * E2 ^ 5) * r_cm
        - (2 * E1 ^ 4 * E2 ^ 5 * y) * hY + (-E0 ^ 2 * E1 ^ 3 * E2 ^ 5) * hXp
        + (E0 ^ 2 * E1 * E2 ^ 7 - E0 * E1 ^ 3 * E2 ^ 6 * X + E0 * E1 ^ 3 * E2 ^ 6 * Xp
          + E1 ^ 5 * E2 ^ 5 * X ^ 2 - E1 ^ 5 * E2 ^ 5 * X * Xp - E1 ^ 5 * E2 ^ 5 * X * x
          + E1 ^ 5 * E2 ^ 5 * Xp * x) * hX
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right
      (mul_ne_zero hem (pow_ne_zero _ hep)))
  have hB : E1 ^ 2 * E2m3 = E2 ^ 6 * (4 * Yp * y + (x - Xp) ^ 2 * (Xp - X)) := by
    have : (E1 ^ 2 * E2m3 - E2 ^ 6 * (4 * Yp * y + (x - Xp) ^ 2 * (Xp - X))) *
        (E1 ^ 5 * E2) = 0 := by
      linear_combination (E1 ^ 7 * E2) * r_3 - (E1 ^ 5 * E2 ^ 4) * r_cp
        - (2 * E1 ^ 5 * E2 ^ 4 * y) * hYp + (E1 ^ 5 * E2 ^ 3 * E3 ^ 2) * hX
        + (-E1 ^ 7 * E2 * E3 ^ 2 - E1 ^ 6 * E2 ^ 3 * E3 * X + E1 ^ 6 * E2 ^ 3 * E3 * Xp
          + E1 ^ 5 * E2 ^ 5 * X * Xp - E1 ^ 5 * E2 ^ 5 * X * x - E1 ^ 5 * E2 ^ 5 * Xp ^ 2
          + E1 ^ 5 * E2 ^ 5 * Xp * x) * hXp
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right
      (mul_ne_zero (pow_ne_zero _ hem) hep))
  refine ⟨fun h0 => absurd h0 hEp0, fun _ => ⟨_, _, _, hQQ.symm, ?_, ?_⟩⟩
  · rw [addX_eq ha₁ ha₃, h1, h4, h3]
    linear_combination (-E1 ^ 4 * E2 ^ 4) * hD
  · rw [addY_eq ha₁ ha₃, h1]
    rw [h3, h4] at r_C
    have hne : (2 * y * (E1 ^ 2 * E2 ^ 2)) ≠ 0 :=
      mul_ne_zero hb (mul_ne_zero (pow_ne_zero _ hem) (pow_ne_zero _ hep))
    have : (2 * (-(W.slope X Xp Y Yp * ((W.slope X Xp Y Yp ^ 2 - W.a₂ - X - Xp) - X) + Y)) *
        (E1 ^ 2 * E2 ^ 2 * (X - Xp)) ^ 3 - Cp) * (2 * y * (E1 ^ 2 * E2 ^ 2)) = 0 := by
      linear_combination E1 ^ 8 * E2 ^ 8 * hL4 - E1 ^ 2 * E2 ^ 2 * r_C
        - 4 * Y ^ 2 * E1 ^ 8 * E2 ^ 2 * hB + 4 * Yp ^ 2 * E1 ^ 2 * E2 ^ 8 * hA
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)

/-! ### The `2`-torsion points and the main theorem -/

omit ha₁ ha₃ in
/-- The odd terms of the auxiliary sequence with `b = 0` are nonzero when `c ≠ 0`. -/
theorem preNormEDS'_odd_ne_zero {c d : F} (hc : c ≠ 0) (k : ℕ) :
    preNormEDS' (0 : F) c d (2 * k + 1) ≠ 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | _ | j
  · simp
  · simpa using hc
  · rw [show 2 * (j + 2) + 1 = 2 * (j + 2) + 1 from rfl, preNormEDS'_odd]
    rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
    · rw [if_pos (even_two_mul i), if_pos (even_two_mul i)]
      have h1 := ih i (by omega)
      have h2 := ih (i + 1) (by omega)
      rw [show 2 * i + 1 = 2 * i + 1 from rfl] at h1
      rw [show 2 * (i + 1) + 1 = 2 * i + 3 by ring] at h2
      rw [show 2 * i + 1 = 2 * i + 1 from rfl, show 2 * i + 3 = 2 * i + 3 from rfl]
      simp only [mul_zero, mul_one, zero_sub, neg_ne_zero]
      exact mul_ne_zero h1 (pow_ne_zero _ h2)
    · have hodd : ¬Even (2 * i + 1) := Nat.not_even_iff_odd.mpr ⟨i, rfl⟩
      rw [if_neg hodd, if_neg hodd]
      have h1 := ih (i + 1) (by omega)
      have h2 := ih (i + 2) (by omega)
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by ring] at h1
      rw [show 2 * (i + 2) + 1 = 2 * i + 1 + 4 by ring] at h2
      simp only [mul_one, mul_zero, sub_zero]
      exact mul_ne_zero h2 (pow_ne_zero _ h1)

omit [NeZero (2 : F)] ha₁ ha₃ in
/-- The even terms of `eₙ` vanish at a `2`-torsion point. -/
theorem eds_eq_zero_of_even (hy : y = 0) {n : ℤ} (hn : Even n) : eds W x y n = 0 := by
  rw [eds, normEDS, if_pos hn, hy]; ring

include h in
/-- `Ψ₃(x) ≠ 0` at a `2`-torsion point `(x, 0)`: `Ψ₃(x) = −f'(x)²` there. -/
theorem Ψ₃_ne_zero_of_y_eq_zero (hy : y = 0) : W.Ψ₃.eval x ≠ 0 := by
  have hf := hQ_of ha₁ ha₃ h
  rw [hy] at hf
  have hf' : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := by
    rcases h.2 with h' | h'
    · rw [evalEval_polynomialX, ha₁] at h'
      intro h0; apply h'; rw [h0]; ring
    · rw [evalEval_polynomialY, ha₁, ha₃, hy] at h'
      exact absurd (by ring) h'
  rw [Ψ₃_eval ha₁ ha₃]
  have : Ident.Ψ₃v W.a₂ W.a₄ W.a₆ x =
      (12 * x + 4 * W.a₂) * (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) -
        (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 := by
    unfold Ident.Ψ₃v; ring
  rw [this, ← hf, zero_pow two_ne_zero, mul_zero, zero_sub, neg_ne_zero]
  exact pow_ne_zero _ hf'

include h in
/-- The odd terms of `eₙ` do not vanish at a `2`-torsion point. -/
theorem eds_ne_zero_of_odd (hy : y = 0) (k : ℕ) : eds W x y (2 * k + 1) ≠ 0 := by
  have hc := Ψ₃_ne_zero_of_y_eq_zero ha₁ ha₃ h hy
  have hodd : ¬Even (2 * (k : ℤ) + 1) := Int.not_even_iff_odd.mpr ⟨k, rfl⟩
  rw [eds, normEDS, if_neg hodd, mul_one, hy, mul_zero,
    show (2 * (k : ℤ) + 1) = ((2 * k + 1 : ℕ) : ℤ) by push_cast; ring, preNormEDS_ofNat]
  simpa using preNormEDS'_odd_ne_zero hc k

/-- `Good n` for every `n` at a `2`-torsion point `(x, 0)`. -/
theorem good_of_y_eq_zero (hy : y = 0) (n : ℕ) : Good h n := by
  have h2P : 2 • Point.some x y h = 0 := by
    rw [two_nsmul, Point.add_self_of_Y_eq]
    rw [negY_eq ha₁ ha₃, hy, neg_zero]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · refine good_of_eq_zero h (eds_eq_zero_of_even hy ⟨k, by push_cast; ring⟩) ?_
    rw [mul_nsmul, h2P, smul_zero]
  · have hne := eds_ne_zero_of_odd ha₁ ha₃ h hy k
    refine ⟨fun h0 => absurd (by push_cast; exact h0) hne, fun _ => ⟨x, y, h, ?_, ?_, ?_⟩⟩
    · rw [succ_nsmul, mul_nsmul, h2P, smul_zero, zero_add]
    · have e1 : eds W x y (((2 * k + 1 : ℕ) : ℤ) + 1) = 0 :=
        eds_eq_zero_of_even hy ⟨k + 1, by push_cast; ring⟩
      rw [e1, zero_mul, sub_zero]
    · rw [hy, edsC, complEDS₂, if_neg (Int.not_even_iff_odd.mpr ⟨k, by push_cast; ring⟩)]; ring

/-- **The division polynomials describe the multiples of a point**: for every nonsingular point
`P = (x, y)` of `y² = x³ + a₂x² + a₄x + a₆` and every `n`, `eₙ = ψₙ(x, y) = 0` iff `nP = 0`, and
if `eₙ ≠ 0` then `nP = (Xₙ, Yₙ)` with `Xₙ eₙ² = x eₙ² − eₙ₊₁ eₙ₋₁` and `2Yₙ eₙ³ = cₙ`. -/
theorem good (n : ℕ) : Good h n := by
  by_cases hy : y = 0
  · exact good_of_y_eq_zero ha₁ ha₃ h hy n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | _ | _ | _ | n
  · exact good_zero h
  · exact good_one h
  · exact good_two ha₁ ha₃ h hy
  · exact good_three ha₁ ha₃ h hy
  · rcases Nat.even_or_odd' (n + 4) with ⟨m, hm | hm⟩
    · rw [hm]
      exact good_even ha₁ ha₃ h hy m (by omega) (ih _ (by omega)) (ih _ (by omega))
        (ih _ (by omega))
    · rw [hm]
      exact good_odd ha₁ ha₃ h hy m (by omega) (ih _ (by omega)) (ih _ (by omega))
        (ih _ (by omega)) (ih _ (by omega))

/-- `n • P = 0 ↔ ψₙ(P) = 0`. -/
theorem smul_eq_zero_iff_eds (n : ℕ) : n • Point.some x y h = 0 ↔ eds W x y n = 0 :=
  (good ha₁ ha₃ h n).smul_eq_zero_iff

end main

end Iut.Torsion
