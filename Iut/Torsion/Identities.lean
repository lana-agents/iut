/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.NeZero

/-!
# Algebraic identities for the group law of `y² = x³ + a₂x² + a₄x + a₆`

Pure field identities underlying the division-polynomial formulas for the multiples of a
point of a Weierstrass curve with `a₁ = a₃ = 0`. Throughout, `P = (x, y)` and `Q = (X, Y)`
are points of the curve `y² = f(x) = x³ + a₂x² + a₄x + a₆` with `X ≠ x`; `lp`, `lm` are the
slopes of the chords through `Q, P` and `Q, −P`, so that `Q ± P` has coordinates `(X±, Y±)`
with `X± = l±² − a₂ − X − x`, `Y± = −(l±(X± − X) + Y)`; `mu` is the slope of the tangent at
`Q`, so `2Q = (X₂, Y₂)` with `X₂ = mu² − a₂ − 2X`, `Y₂ = −(mu(X₂ − X) + Y)`. Writing
`ψ₂(R) = 2y(R)`, the identities are:

- `chord_diff`: `(x(Q−P) − x(Q+P))·(X − x)² = ψ₂(Q)ψ₂(P)`;
- `chord_sum`: `x(Q+P) + x(Q−P)` in terms of `X`, `x` (the addition-and-subtraction map);
- `double_X`: `x(2Q)·ψ₂(Q)² = X·ψ₂(Q)² − Ψ₃(X)`;
- `double_Y`: `ψ₂(2Q)·ψ₂(Q)³ = preΨ₄(X)`;
- `double_X_sub`: `(x − x(2Q))·ψ₂(Q)² = (x − X)²(X − x(Q+P))(x(Q−P) − X)`;
- `double_Y_mul`:
  `ψ₂(2Q)ψ₂(Q)³ψ₂(P) = (x−X)⁴((x(Q−P) − X)²ψ₂(Q+P) − (X − x(Q+P))²ψ₂(Q−P))`;
- `odd_Y`: the `ψ₂`-coordinate of `Q + Q'` in terms of `Q`, `Q'` and `Q' − Q`;
- `three_Y`: the `ψ₂`-coordinate of `3P = 2P + P`.

These are the identities behind the recursions of the division polynomials `ψₙ` at the values
`ψₙ(P)`, see `Iut.Torsion.EDS`. The proofs are certificates found by computer algebra: each
identity, multiplied by a power of the denominators, is an explicit combination of the curve
equations and the slope equations, verified by `linear_combination`.
-/

namespace Iut.Torsion.Ident

variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem four_ne_zero' : (4 : F) ≠ 0 := by
  have h := NeZero.ne (2 : F)
  have : (4 : F) = 2 * 2 := by norm_num
  rw [this]; exact mul_ne_zero h h

theorem eight_ne_zero' : (8 : F) ≠ 0 := by
  have h := NeZero.ne (2 : F)
  have : (8 : F) = 2 * 2 * 2 := by norm_num
  rw [this]; exact mul_ne_zero (mul_ne_zero h h) h

theorem c32_ne_zero' : (32 : F) ≠ 0 := by
  have h := NeZero.ne (2 : F)
  have : (32 : F) = 2 ^ 5 := by norm_num
  rw [this]; exact pow_ne_zero _ h

theorem c128_ne_zero' : (128 : F) ≠ 0 := by
  have h := NeZero.ne (2 : F)
  have : (128 : F) = 2 ^ 7 := by norm_num
  rw [this]; exact pow_ne_zero _ h

/-- `Ψ₃(t) = 3t⁴ + b₂t³ + 3b₄t² + 3b₆t + b₈` for `a₁ = a₃ = 0`. -/
def Ψ₃v (a₂ a₄ a₆ t : F) : F :=
  3 * t ^ 4 + 4 * a₂ * t ^ 3 + 6 * a₄ * t ^ 2 + 12 * a₆ * t + (4 * a₂ * a₆ - a₄ ^ 2)

/-- `preΨ₄(t)` for `a₁ = a₃ = 0`. -/
def preΨ₄v (a₂ a₄ a₆ t : F) : F :=
  2 * t ^ 6 + 4 * a₂ * t ^ 5 + 10 * a₄ * t ^ 4 + 40 * a₆ * t ^ 3 +
    10 * (4 * a₂ * a₆ - a₄ ^ 2) * t ^ 2 + (4 * a₂ * (4 * a₂ * a₆ - a₄ ^ 2) - 8 * a₄ * a₆) * t +
    (2 * a₄ * (4 * a₂ * a₆ - a₄ ^ 2) - 16 * a₆ ^ 2)

/-- The sum `x(Q+P) + x(Q−P)` times `(X − x)²`, a polynomial in `X`, `x`. -/
def sumv (a₂ a₄ a₆ X x : F) : F :=
  2 * (X + x) * (X * x) + 4 * a₂ * (X * x) + 2 * a₄ * (X + x) + 4 * a₆

section

variable {a₂ a₄ a₆ X Y x y lp lm mu : F}
  (hQ : Y ^ 2 = X ^ 3 + a₂ * X ^ 2 + a₄ * X + a₆) (hP : y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
  (hX : X ≠ x) (hp : lp * (X - x) = Y - y) (hm : lm * (X - x) = Y + y)
  (hmu : mu * (2 * Y) = 3 * X ^ 2 + 2 * a₂ * X + a₄)

omit [NeZero (2 : F)] in
include hX hp hm in
/-- `(x(Q−P) − x(Q+P))·(X − x)² = 2Y·2y`. -/
theorem chord_diff :
    ((lm ^ 2 - a₂ - X - x) - (lp ^ 2 - a₂ - X - x)) * (X - x) ^ 2 = 4 * Y * y := by
  have h : (X - x) ^ 4 * ((((lm ^ 2 - a₂ - X - x) - (lp ^ 2 - a₂ - X - x)) * (X - x) ^ 2) -
      4 * Y * y) = 0 := by
    linear_combination (-X^5*lp - X^4*Y + 5*X^4*lp*x + X^4*y + 4*X^3*Y*x - 10*X^3*lp*x^2 -
      4*X^3*x*y - 6*X^2*Y*x^2 +
      10*X^2*lp*x^3 + 6*X^2*x^2*y + 4*X*Y*x^3 - 5*X*lp*x^4 - 4*X*x^3*y - Y*x^4 + lp*x^5 + x^4*y) *
      hp + (X^5*lm + X^4*Y - 5*X^4*lm*x + X^4*y - 4*X^3*Y*x + 10*X^3*lm*x^2 - 4*X^3*x*y +
      6*X^2*Y*x^2 - 10*X^2*lm*x^3 + 6*X^2*x^2*y - 4*X*Y*x^3 + 5*X*lm*x^4 - 4*X*x^3*y + Y*x^4 -
      lm*x^5 + x^4*y) * hm
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (pow_ne_zero _ (sub_ne_zero.mpr hX))
  · exact sub_eq_zero.mp h

omit [NeZero (2 : F)] in
include hQ hP hX hp hm in
/-- `(x(Q+P) + x(Q−P))·(X − x)² = sumv`. -/
theorem chord_sum :
    ((lp ^ 2 - a₂ - X - x) + (lm ^ 2 - a₂ - X - x)) * (X - x) ^ 2 = sumv a₂ a₄ a₆ X x := by
  have h : (X - x) ^ 4 * ((((lp ^ 2 - a₂ - X - x) + (lm ^ 2 - a₂ - X - x)) * (X - x) ^ 2) -
      sumv a₂ a₄ a₆ X x) = 0 := by
    unfold sumv
    linear_combination (X^5*lp + X^4*Y - 5*X^4*lp*x - X^4*y - 4*X^3*Y*x + 10*X^3*lp*x^2 +
      4*X^3*x*y + 6*X^2*Y*x^2 -
      10*X^2*lp*x^3 - 6*X^2*x^2*y - 4*X*Y*x^3 + 5*X*lp*x^4 + 4*X*x^3*y + Y*x^4 - lp*x^5 - x^4*y) *
      hp + (X^5*lm + X^4*Y - 5*X^4*lm*x + X^4*y - 4*X^3*Y*x + 10*X^3*lm*x^2 - 4*X^3*x*y +
      6*X^2*Y*x^2 - 10*X^2*lm*x^3 + 6*X^2*x^2*y - 4*X*Y*x^3 + 5*X*lm*x^4 - 4*X*x^3*y + Y*x^4 -
      lm*x^5 + x^4*y) * hm + (2*X^4 - 8*X^3*x + 12*X^2*x^2 - 8*X*x^3 + 2*x^4) * hQ + (2*X^4 -
      8*X^3*x + 12*X^2*x^2 - 8*X*x^3 + 2*x^4) * hP
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (pow_ne_zero _ (sub_ne_zero.mpr hX))
  · exact sub_eq_zero.mp h

include hQ hmu in
/-- `x(2Q)·(2Y)² = X·(2Y)² − Ψ₃(X)`. -/
theorem double_X (hY : Y ≠ 0) :
    (mu ^ 2 - a₂ - 2 * X) * (4 * Y ^ 2) = X * (4 * Y ^ 2) - Ψ₃v a₂ a₄ a₆ X := by
  have h : 4 * Y ^ 2 *
      ((mu ^ 2 - a₂ - 2 * X) * (4 * Y ^ 2) - (X * (4 * Y ^ 2) - Ψ₃v a₂ a₄ a₆ X)) = 0 := by
    unfold Ψ₃v
    linear_combination (12*X^2*Y^2 + 8*X*Y^2*a₂ + 8*Y^3*mu + 4*Y^2*a₄) * hmu + (-48*X*Y^2 -
      16*Y^2*a₂) * hQ
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h four_ne_zero'
    · exact absurd h (pow_ne_zero _ hY)
  · exact sub_eq_zero.mp h

include hQ hmu in
/-- `2y(2Q)·(2Y)³ = preΨ₄(X)`. -/
theorem double_Y (hY : Y ≠ 0) :
    2 * (-(mu * ((mu ^ 2 - a₂ - 2 * X) - X) + Y)) * (8 * Y ^ 3) = preΨ₄v a₂ a₄ a₆ X := by
  have h : 8 * Y ^ 3 *
      (2 * (-(mu * ((mu ^ 2 - a₂ - 2 * X) - X) + Y)) * (8 * Y ^ 3) - preΨ₄v a₂ a₄ a₆ X) = 0 := by
    unfold preΨ₄v
    linear_combination (-144*X^4*Y^3 - 192*X^3*Y^3*a₂ - 96*X^2*Y^4*mu - 64*X^2*Y^3*a₂^2 -
      96*X^2*Y^3*a₄ + 192*X*Y^5 -
      64*X*Y^4*a₂*mu - 64*X*Y^3*a₂*a₄ + 64*Y^5*a₂ - 64*Y^5*mu^2 - 32*Y^4*a₄*mu - 16*Y^3*a₄^2) * hmu
      + (448*X^3*Y^3 + 448*X^2*Y^3*a₂ + 128*X*Y^3*a₂^2 + 64*X*Y^3*a₄ - 128*Y^5 + 64*Y^3*a₂*a₄ -
      128*Y^3*a₆) * hQ
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h eight_ne_zero'
    · exact absurd h (pow_ne_zero _ hY)
  · exact sub_eq_zero.mp h

include hQ hP hX hp hm hmu in
/-- `(x − x(2Q))·(2Y)² = (x − X)²(X − x(Q+P))(x(Q−P) − X)`. -/
theorem double_X_sub (hY : Y ≠ 0) :
    (x - (mu ^ 2 - a₂ - 2 * X)) * (4 * Y ^ 2) =
      (x - X) ^ 2 * (X - (lp ^ 2 - a₂ - X - x)) * ((lm ^ 2 - a₂ - X - x) - X) := by
  have h : 4 * Y ^ 2 * (X - x) ^ 4 * ((x - (mu ^ 2 - a₂ - 2 * X)) * (4 * Y ^ 2) -
      (x - X) ^ 2 * (X - (lp ^ 2 - a₂ - X - x)) * ((lm ^ 2 - a₂ - X - x) - X)) = 0 := by
    linear_combination (-12*X^6*Y^2 - 8*X^5*Y^2*a₂ + 48*X^5*Y^2*x - 8*X^4*Y^3*mu + 32*X^4*Y^2*a₂*x
      - 4*X^4*Y^2*a₄ -
      72*X^4*Y^2*x^2 + 32*X^3*Y^3*mu*x - 48*X^3*Y^2*a₂*x^2 + 16*X^3*Y^2*a₄*x + 48*X^3*Y^2*x^3 -
      48*X^2*Y^3*mu*x^2 + 32*X^2*Y^2*a₂*x^3 - 24*X^2*Y^2*a₄*x^2 - 12*X^2*Y^2*x^4 + 32*X*Y^3*mu*x^3 -
      8*X*Y^2*a₂*x^4 + 16*X*Y^2*a₄*x^3 - 8*Y^3*mu*x^4 - 4*Y^2*a₄*x^4) * hmu + (-8*X^6*Y^2*lp -
      8*X^5*Y^3 - 4*X^5*Y^2*a₂*lp + 4*X^5*Y^2*lm^2*lp + 36*X^5*Y^2*lp*x + 8*X^5*Y^2*y - 4*X^4*Y^3*a₂
      + 4*X^4*Y^3*lm^2 + 28*X^4*Y^3*x + 20*X^4*Y^2*a₂*lp*x + 4*X^4*Y^2*a₂*y - 20*X^4*Y^2*lm^2*lp*x -
      4*X^4*Y^2*lm^2*y - 60*X^4*Y^2*lp*x^2 - 28*X^4*Y^2*x*y + 16*X^3*Y^3*a₂*x - 16*X^3*Y^3*lm^2*x -
      32*X^3*Y^3*x^2 - 40*X^3*Y^2*a₂*lp*x^2 - 16*X^3*Y^2*a₂*x*y + 40*X^3*Y^2*lm^2*lp*x^2 +
      16*X^3*Y^2*lm^2*x*y + 40*X^3*Y^2*lp*x^3 + 32*X^3*Y^2*x^2*y - 24*X^2*Y^3*a₂*x^2 +
      24*X^2*Y^3*lm^2*x^2 + 8*X^2*Y^3*x^3 + 40*X^2*Y^2*a₂*lp*x^3 + 24*X^2*Y^2*a₂*x^2*y -
      40*X^2*Y^2*lm^2*lp*x^3 - 24*X^2*Y^2*lm^2*x^2*y - 8*X^2*Y^2*x^3*y + 16*X*Y^3*a₂*x^3 -
      16*X*Y^3*lm^2*x^3 + 8*X*Y^3*x^4 - 20*X*Y^2*a₂*lp*x^4 - 16*X*Y^2*a₂*x^3*y +
      20*X*Y^2*lm^2*lp*x^4 + 16*X*Y^2*lm^2*x^3*y - 12*X*Y^2*lp*x^5 - 8*X*Y^2*x^4*y - 4*Y^3*a₂*x^4 +
      4*Y^3*lm^2*x^4 - 4*Y^3*x^5 + 4*Y^2*a₂*lp*x^5 + 4*Y^2*a₂*x^4*y - 4*Y^2*lm^2*lp*x^5 -
      4*Y^2*lm^2*x^4*y + 4*Y^2*lp*x^6 + 4*Y^2*x^5*y) * hp + (-8*X^6*Y^2*lm - 8*X^5*Y^3 -
      4*X^5*Y^2*a₂*lm + 36*X^5*Y^2*lm*x - 8*X^5*Y^2*y - 4*X^4*Y^3*a₂ + 28*X^4*Y^3*x +
      20*X^4*Y^2*a₂*lm*x - 4*X^4*Y^2*a₂*y - 60*X^4*Y^2*lm*x^2 + 28*X^4*Y^2*x*y + 4*X^3*Y^4*lm +
      16*X^3*Y^3*a₂*x - 8*X^3*Y^3*lm*y - 32*X^3*Y^3*x^2 - 40*X^3*Y^2*a₂*lm*x^2 + 16*X^3*Y^2*a₂*x*y +
      40*X^3*Y^2*lm*x^3 + 4*X^3*Y^2*lm*y^2 - 32*X^3*Y^2*x^2*y + 4*X^2*Y^5 - 12*X^2*Y^4*lm*x -
      4*X^2*Y^4*y - 24*X^2*Y^3*a₂*x^2 + 24*X^2*Y^3*lm*x*y + 8*X^2*Y^3*x^3 - 4*X^2*Y^3*y^2 +
      40*X^2*Y^2*a₂*lm*x^3 - 24*X^2*Y^2*a₂*x^2*y - 12*X^2*Y^2*lm*x*y^2 + 8*X^2*Y^2*x^3*y +
      4*X^2*Y^2*y^3 - 8*X*Y^5*x + 12*X*Y^4*lm*x^2 + 8*X*Y^4*x*y + 16*X*Y^3*a₂*x^3 -
      24*X*Y^3*lm*x^2*y + 8*X*Y^3*x^4 + 8*X*Y^3*x*y^2 - 20*X*Y^2*a₂*lm*x^4 + 16*X*Y^2*a₂*x^3*y -
      12*X*Y^2*lm*x^5 + 12*X*Y^2*lm*x^2*y^2 + 8*X*Y^2*x^4*y - 8*X*Y^2*x*y^3 + 4*Y^5*x^2 -
      4*Y^4*lm*x^3 - 4*Y^4*x^2*y - 4*Y^3*a₂*x^4 + 8*Y^3*lm*x^3*y - 4*Y^3*x^5 - 4*Y^3*x^2*y^2 +
      4*Y^2*a₂*lm*x^5 - 4*Y^2*a₂*x^4*y + 4*Y^2*lm*x^6 - 4*Y^2*lm*x^3*y^2 - 4*Y^2*x^5*y +
      4*Y^2*x^2*y^3) * hm + (20*X^5*Y^2 + 24*X^5*a₂*x^2 + 24*X^5*a₄*x + 24*X^5*a₆ + 24*X^5*x^3 -
      24*X^5*y^2 + 12*X^4*Y^2*a₂ - 64*X^4*Y^2*x + 16*X^4*a₂^2*x^2 + 16*X^4*a₂*a₄*x + 16*X^4*a₂*a₆ -
      56*X^4*a₂*x^3 - 16*X^4*a₂*y^2 - 72*X^4*a₄*x^2 - 72*X^4*a₆*x - 72*X^4*x^4 + 72*X^4*x*y^2 -
      40*X^3*Y^2*a₂*x + 4*X^3*Y^2*a₄ + 68*X^3*Y^2*x^2 - 48*X^3*a₂^2*x^3 - 40*X^3*a₂*a₄*x^2 -
      48*X^3*a₂*a₆*x + 24*X^3*a₂*x^4 + 48*X^3*a₂*x*y^2 + 8*X^3*a₄^2*x + 8*X^3*a₄*a₆ + 80*X^3*a₄*x^3
      - 8*X^3*a₄*y^2 + 72*X^3*a₆*x^2 + 72*X^3*x^5 - 72*X^3*x^2*y^2 + 4*X^2*Y^4 + 52*X^2*Y^2*a₂*x^2 -
      8*X^2*Y^2*a₄*x + 4*X^2*Y^2*a₆ - 16*X^2*Y^2*x^3 - 8*X^2*Y^2*y^2 + 52*X^2*a₂^2*x^4 +
      32*X^2*a₂*a₄*x^3 + 56*X^2*a₂*a₆*x^2 + 32*X^2*a₂*x^5 - 56*X^2*a₂*x^2*y^2 - 20*X^2*a₄^2*x^2 -
      16*X^2*a₄*a₆*x - 40*X^2*a₄*x^4 + 16*X^2*a₄*x*y^2 + 4*X^2*a₆^2 - 16*X^2*a₆*x^3 - 8*X^2*a₆*y^2 -
      20*X^2*x^6 + 16*X^2*x^3*y^2 + 4*X^2*y^4 - 8*X*Y^4*x - 32*X*Y^2*a₂*x^3 + 4*X*Y^2*a₄*x^2 -
      8*X*Y^2*a₆*x - 16*X*Y^2*x^4 + 16*X*Y^2*x*y^2 - 24*X*a₂^2*x^5 - 8*X*a₂*a₄*x^4 - 32*X*a₂*a₆*x^3
      - 32*X*a₂*x^6 + 32*X*a₂*x^3*y^2 + 16*X*a₄^2*x^3 + 8*X*a₄*a₆*x^2 + 8*X*a₄*x^5 - 8*X*a₄*x^2*y^2
      - 8*X*a₆^2*x - 16*X*a₆*x^4 + 16*X*a₆*x*y^2 - 8*X*x^7 + 16*X*x^4*y^2 - 8*X*x*y^4 + 4*Y^4*x^2 +
      8*Y^2*a₂*x^4 + 4*Y^2*a₆*x^2 + 8*Y^2*x^5 - 8*Y^2*x^2*y^2 + 4*a₂^2*x^6 + 8*a₂*a₆*x^4 + 8*a₂*x^7
      - 8*a₂*x^4*y^2 - 4*a₄^2*x^4 + 4*a₆^2*x^2 + 8*a₆*x^5 - 8*a₆*x^2*y^2 + 4*x^8 - 8*x^5*y^2 +
      4*x^2*y^4) * hQ + (-24*X^8 - 40*X^7*a₂ + 72*X^7*x - 16*X^6*a₂^2 + 120*X^6*a₂*x - 32*X^6*a₄ -
      72*X^6*x^2 + 48*X^5*a₂^2*x - 24*X^5*a₂*a₄ - 124*X^5*a₂*x^2 + 92*X^5*a₄*x - 28*X^5*a₆ +
      20*X^5*x^3 + 4*X^5*y^2 - 52*X^4*a₂^2*x^2 + 68*X^4*a₂*a₄*x - 20*X^4*a₂*a₆ + 44*X^4*a₂*x^3 +
      4*X^4*a₂*y^2 - 8*X^4*a₄^2 - 88*X^4*a₄*x^2 + 80*X^4*a₆*x + 8*X^4*x^4 - 8*X^4*x*y^2 +
      24*X^3*a₂^2*x^3 - 68*X^3*a₂*a₄*x^2 + 56*X^3*a₂*a₆*x + 4*X^3*a₂*x^4 - 8*X^3*a₂*x*y^2 +
      20*X^3*a₄^2*x - 12*X^3*a₄*a₆ + 24*X^3*a₄*x^3 + 4*X^3*a₄*y^2 - 76*X^3*a₆*x^2 - 4*X^3*x^5 +
      4*X^3*x^2*y^2 - 4*X^2*a₂^2*x^4 + 28*X^2*a₂*a₄*x^3 - 56*X^2*a₂*a₆*x^2 - 4*X^2*a₂*x^5 +
      4*X^2*a₂*x^2*y^2 - 16*X^2*a₄^2*x^2 + 28*X^2*a₄*a₆*x + 8*X^2*a₄*x^4 - 8*X^2*a₄*x*y^2 -
      4*X^2*a₆^2 + 20*X^2*a₆*x^3 + 4*X^2*a₆*y^2 - 4*X*a₂*a₄*x^4 + 24*X*a₂*a₆*x^3 + 4*X*a₄^2*x^3 -
      20*X*a₄*a₆*x^2 - 4*X*a₄*x^5 + 4*X*a₄*x^2*y^2 + 8*X*a₆^2*x + 8*X*a₆*x^4 - 8*X*a₆*x*y^2 -
      4*a₂*a₆*x^4 + 4*a₄*a₆*x^3 - 4*a₆^2*x^2 - 4*a₆*x^5 + 4*a₆*x^2*y^2) * hP
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h four_ne_zero'
      · exact absurd h (pow_ne_zero _ hY)
    · exact absurd h (pow_ne_zero _ (sub_ne_zero.mpr hX))
  · exact sub_eq_zero.mp h

include hQ hP hX hp hm hmu in
/-- `ψ₂(2Q)ψ₂(Q)³ψ₂(P) = (x−X)⁴((x(Q−P) − X)²ψ₂(Q+P) − (X − x(Q+P))²ψ₂(Q−P))`. -/
theorem double_Y_mul (hY : Y ≠ 0) :
    2 * (-(mu * ((mu ^ 2 - a₂ - 2 * X) - X) + Y)) * (2 * Y) ^ 3 * (2 * y) =
      (x - X) ^ 4 * (((lm ^ 2 - a₂ - X - x) - X) ^ 2 * (2 * (-(lp * ((lp ^ 2 - a₂ - X - x) - X) +
        Y))) - (X - (lp ^ 2 - a₂ - X - x)) ^ 2 * (2 * (-(lm * ((lm ^ 2 - a₂ - X - x) - X) + Y)))) :=
        by
  have hD := chord_diff (a₂ := a₂) hX hp hm
  have hS := chord_sum hQ hP hX hp hm
  have hI2 := double_X hQ hmu hY
  have hI3 := double_Y hQ hmu hY
  have hI5 := double_X_sub hQ hP hX hp hm hmu hY
  have hL : (lp * ((lm ^ 2 - a₂ - X - x) - X) + lm * (X - (lp ^ 2 - a₂ - X - x))) * (X - x) = Y *
    (((lm ^ 2 - a₂ - X - x) - X) + (X - (lp ^ 2 - a₂ - X - x))) - y * (((lm ^ 2 - a₂ - X - x) - X) -
    (X - (lp ^ 2 - a₂ - X - x))) := by
    linear_combination ((lm ^ 2 - a₂ - X - x) - X) * hp + (X - (lp ^ 2 - a₂ - X - x)) * hm
  have hA : (x - (mu ^ 2 - a₂ - 2 * X)) * (4 * Y ^ 2) = (4 * (X ^ 3 + a₂ * X ^ 2 + a₄ * X + a₆) *
    (x - X) + Ψ₃v a₂ a₄ a₆ X) := by
    linear_combination (-1 : F) * hI2 + 4 * (x - X) * hQ
  have hYpm : ((lm ^ 2 - a₂ - X - x) - X) ^ 2 * (2 * (-(lp * ((lp ^ 2 - a₂ - X - x) - X) + Y))) -
    (X - (lp ^ 2 - a₂ - X - x)) ^ 2 * (2 * (-(lm * ((lm ^ 2 - a₂ - X - x) - X) + Y))) =
      2 * ((lm ^ 2 - a₂ - X - x) - X) * (X - (lp ^ 2 - a₂ - X - x)) * (lp * ((lm ^ 2 - a₂ - X - x)
        - X) + lm * (X - (lp ^ 2 - a₂ - X - x))) - 2 * Y * (((lm ^ 2 - a₂ - X - x) - X) ^ 2 - (X -
        (lp ^ 2 - a₂ - X - x)) ^ 2) := by ring
  have key : (X - x) * preΨ₄v a₂ a₄ a₆ X =
      (4 * (X ^ 3 + a₂ * X ^ 2 + a₄ * X + a₆) * (x - X) + Ψ₃v a₂ a₄ a₆ X) * (4 * (X ^ 3 + a₂ * X ^
        2 + a₄ * X + a₆) - (sumv a₂ a₄ a₆ X x - 2 * X * (X - x) ^ 2)) - 4 * (X ^ 3 + a₂ * X ^ 2 + a₄
        * X + a₆) * (sumv a₂ a₄ a₆ X x - 2 * X * (X - x) ^ 2) * (X - x) := by
    unfold preΨ₄v Ψ₃v sumv; ring
  have h : (X - x) * (2 * (-(mu * ((mu ^ 2 - a₂ - 2 * X) - X) + Y)) * (2 * Y) ^ 3 * (2 * y) -
      (x - X) ^ 4 * (((lm ^ 2 - a₂ - X - x) - X) ^ 2 * (2 * (-(lp * ((lp ^ 2 - a₂ - X - x) - X) +
        Y))) - (X - (lp ^ 2 - a₂ - X - x)) ^ 2 * (2 * (-(lm * ((lm ^ 2 - a₂ - X - x) - X) + Y))))) =
        0 := by
    linear_combination 2 * y * (X - x) * hI3 - 2 * (4 * (X ^ 3 + a₂ * X ^ 2 + a₄ * X + a₆) * (x -
      X) + Ψ₃v a₂ a₄ a₆ X) * Y * hD + 2 * (4 * (X ^ 3 + a₂ * X ^ 2 + a₄ * X + a₆) * (x - X) + Ψ₃v a₂
      a₄ a₆ X) * y * hS
      - 8 * (4 * (X ^ 3 + a₂ * X ^ 2 + a₄ * X + a₆) * (x - X) + Ψ₃v a₂ a₄ a₆ X) * y * hQ + 2 * (X
        - x) ^ 3 * (lp * ((lm ^ 2 - a₂ - X - x) - X) + lm * (X - (lp ^ 2 - a₂ - X - x))) * hI5 - 2 *
        (X - x) ^ 3 * (lp * ((lm ^ 2 - a₂ - X - x) - X) + lm * (X - (lp ^ 2 - a₂ - X - x))) * hA
      - 2 * (X - x) ^ 2 * (4 * (X ^ 3 + a₂ * X ^ 2 + a₄ * X + a₆) * (x - X) + Ψ₃v a₂ a₄ a₆ X) * hL
        + 2 * Y * (X - x) * (sumv a₂ a₄ a₆ X x - 2 * X * (X - x) ^ 2) * hD
      + 2 * Y * (X - x) ^ 3 * (((lm ^ 2 - a₂ - X - x) - X) + (X - (lp ^ 2 - a₂ - X - x))) * hS + 8
        * y * (sumv a₂ a₄ a₆ X x - 2 * X * (X - x) ^ 2) * (X - x) * hQ - (X - x) ^ 5 * hYpm
      + 2 * y * key
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (sub_ne_zero.mpr hX)
  · exact sub_eq_zero.mp h

end

section

variable {a₂ a₄ a₆ X Y x y lam nu : F}
  (hQ : Y ^ 2 = X ^ 3 + a₂ * X ^ 2 + a₄ * X + a₆) (hP : y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
  (hX : X ≠ x) (hl : lam * (X - x) = Y - y) (hn : nu * (x - X) = y + Y)

include hQ hP hl hn in
/-- The `ψ₂`-coordinate of `Q + Q'` for `Q = (X, Y)`, `Q' = (x, y)`: with `R = Q' − Q =
(xR, yR)` and `Q + Q' = (Xs, Ys)`,
`2Ys(X − x)³·2yR = (x − X)(4Y²(xR − x)² − 4y²(xR − X)²) + 16 yR Y y (Y − y)`. -/
theorem odd_Y :
    2 * (-(lam * ((lam ^ 2 - a₂ - X - x) - X) + Y)) * (X - x) ^ 3 *
        (2 * (-(nu * ((nu ^ 2 - a₂ - x - X) - x) + y))) =
      (x - X) * (4 * Y ^ 2 * ((nu ^ 2 - a₂ - x - X) - x) ^ 2 -
          4 * y ^ 2 * ((nu ^ 2 - a₂ - x - X) - X) ^ 2) +
        16 * (-(nu * ((nu ^ 2 - a₂ - x - X) - x) + y)) * Y * y * (Y - y) := by
  have h2Y : Y * 2 = (lam - nu) * (X - x) := by linear_combination (-1 : F) * hl - hn
  have h2y : y * 2 = -(lam + nu) * (X - x) := by linear_combination hl - hn
  have hg1 : (lam - nu) ^ 2 * (X - x) ^ 2 = 4 * (X ^ 3 + a₂ * X ^ 2 + a₄ * X + a₆) := by
    linear_combination 4 * hQ - (2 * Y + (lam - nu) * (X - x)) * h2Y
  have hg2 : (lam + nu) ^ 2 * (X - x) ^ 2 = 4 * (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) := by
    linear_combination 4 * hP - (2 * y - (lam + nu) * (X - x)) * h2y
  have h : (32 : F) * (2 * (-(lam * ((lam ^ 2 - a₂ - X - x) - X) + Y)) * (X - x) ^ 3 *
        (2 * (-(nu * ((nu ^ 2 - a₂ - x - X) - x) + y))) -
      ((x - X) * (4 * Y ^ 2 * ((nu ^ 2 - a₂ - x - X) - x) ^ 2 -
          4 * y ^ 2 * ((nu ^ 2 - a₂ - x - X) - X) ^ 2) +
        16 * (-(nu * ((nu ^ 2 - a₂ - x - X) - x) + y)) * Y * y * (Y - y))) = 0 := by
    linear_combination (32*X^4*lam - 96*X^4*nu + 64*X^3*Y + 64*X^3*a₂*lam - 128*X^3*a₂*nu -
      64*X^3*lam*nu^2 +
      64*X^3*lam*x + 128*X^3*nu^3 + 64*X^3*y + 128*X^2*Y*a₂ - 128*X^2*Y*nu^2 + 192*X^2*Y*x +
      32*X^2*a₂^2*lam - 32*X^2*a₂^2*nu - 64*X^2*a₂*lam*nu^2 + 64*X^2*a₂*nu^3 + 192*X^2*a₂*nu*x +
      32*X^2*lam*nu^4 - 128*X^2*lam*nu*y - 96*X^2*lam*x^2 - 32*X^2*nu^5 - 192*X^2*nu^3*x +
      128*X^2*nu^2*y + 288*X^2*nu*x^2 - 192*X^2*x*y + 64*X*Y*a₂^2 - 128*X*Y*a₂*nu^2 + 128*X*Y*a₂*x +
      64*X*Y*nu^4 - 128*X*Y*nu^2*x - 256*X*Y*nu*y - 64*X*a₂^2*lam*x + 64*X*a₂^2*nu*x +
      128*X*a₂*lam*nu^2*x - 128*X*a₂*lam*nu*y - 192*X*a₂*lam*x^2 - 128*X*a₂*nu^3*x + 128*X*a₂*nu^2*y
      - 64*X*lam*nu^4*x + 128*X*lam*nu^3*y + 192*X*lam*nu^2*x^2 - 128*X*lam*nu*x*y - 128*X*lam*x^3 +
      128*X*lam*y^2 + 64*X*nu^5*x - 128*X*nu^4*y + 128*X*nu^2*x*y - 192*X*nu*x^3 + 128*X*nu*y^2 +
      192*X*x^2*y - 64*Y*a₂^2*x + 128*Y*a₂*nu^2*x - 256*Y*a₂*nu*y - 256*Y*a₂*x^2 - 64*Y*nu^4*x +
      256*Y*nu^3*y + 256*Y*nu^2*x^2 - 512*Y*nu*x*y - 256*Y*x^3 + 256*Y*y^2 + 32*a₂^2*lam*x^2 -
      32*a₂^2*nu*x^2 - 64*a₂*lam*nu^2*x^2 + 128*a₂*lam*nu*x*y + 128*a₂*lam*x^3 + 64*a₂*nu^3*x^2 -
      128*a₂*nu^2*x*y - 64*a₂*nu*x^3 + 256*a₂*nu*y^2 + 32*lam*nu^4*x^2 - 128*lam*nu^3*x*y -
      128*lam*nu^2*x^3 + 256*lam*nu*x^2*y + 128*lam*x^4 - 128*lam*x*y^2 - 32*nu^5*x^2 + 128*nu^4*x*y
      + 64*nu^3*x^3 - 256*nu^3*y^2 - 256*nu^2*x^2*y + 640*nu*x*y^2 - 64*x^3*y - 256*y^3) * h2Y +
      (32*X^4*lam + 96*X^4*nu + 64*X^3*a₂*lam + 128*X^3*a₂*nu - 128*X^3*lam^2*nu + 64*X^3*lam*nu^2 +
      64*X^3*lam*x - 128*X^3*nu^3 - 256*X^3*y + 32*X^2*a₂^2*lam + 32*X^2*a₂^2*nu -
      128*X^2*a₂*lam^2*nu + 64*X^2*a₂*lam*nu^2 - 64*X^2*a₂*nu^3 - 192*X^2*a₂*nu*x - 256*X^2*a₂*y +
      128*X^2*lam^2*nu^3 + 128*X^2*lam^2*y - 96*X^2*lam*nu^4 - 96*X^2*lam*x^2 + 32*X^2*nu^5 +
      192*X^2*nu^3*x + 128*X^2*nu^2*y - 288*X^2*nu*x^2 - 64*X*a₂^2*lam*x - 64*X*a₂^2*nu*x -
      64*X*a₂^2*y + 256*X*a₂*lam^2*nu*x - 128*X*a₂*lam*nu^2*x + 128*X*a₂*lam*nu*y - 192*X*a₂*lam*x^2
      + 128*X*a₂*nu^3*x + 128*X*a₂*x*y - 256*X*lam^2*nu^3*x + 384*X*lam^2*nu*x^2 - 256*X*lam^2*x*y +
      192*X*lam*nu^4*x - 128*X*lam*nu^3*y - 192*X*lam*nu^2*x^2 + 384*X*lam*nu*x*y - 128*X*lam*x^3 -
      128*X*lam*y^2 - 64*X*nu^5*x + 64*X*nu^4*y - 256*X*nu^2*x*y + 192*X*nu*x^3 + 128*X*nu*y^2 +
      192*X*x^2*y + 32*a₂^2*lam*x^2 + 32*a₂^2*nu*x^2 + 64*a₂^2*x*y - 128*a₂*lam^2*nu*x^2 +
      64*a₂*lam*nu^2*x^2 - 128*a₂*lam*nu*x*y + 128*a₂*lam*x^3 - 64*a₂*nu^3*x^2 + 64*a₂*nu*x^3 +
      128*a₂*x^2*y + 128*lam^2*nu^3*x^2 - 256*lam^2*nu*x^3 + 128*lam^2*x^2*y - 96*lam*nu^4*x^2 +
      128*lam*nu^3*x*y + 128*lam*nu^2*x^3 - 384*lam*nu*x^2*y + 128*lam*x^4 + 128*lam*x*y^2 +
      32*nu^5*x^2 - 64*nu^4*x*y - 64*nu^3*x^3 + 128*nu^2*x^2*y - 128*nu*x*y^2 + 64*x^3*y) * h2y
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h c32_ne_zero'
  · exact sub_eq_zero.mp h

end

section

variable {a₂ a₄ a₆ x y X Y nu : F}
  (hP : y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) (hQ : Y ^ 2 = X ^ 3 + a₂ * X ^ 2 + a₄ * X + a₆)
  (hT : Y * (2 * y) = -2 * y ^ 2 - (3 * x ^ 2 + 2 * a₂ * x + a₄) * (X - x))
  (hD2 : X * (4 * y ^ 2) = (3 * x ^ 2 + 2 * a₂ * x + a₄) ^ 2 - 4 * y ^ 2 * (a₂ + 2 * x))
  (hn : nu * (X - x) = Y - y)

include hP hQ hT hD2 hn in
/-- The `ψ₂`-coordinate of `3P = 2P + P` for `P = (x, y)`, `2P = (X, Y)`, `3P = (x₃, y₃)`:
`2y₃(x − X)³ = 2y(4yY − (x − X)³ − 4Y²)`. The point `2P` is described by the tangent line
(`hT`) and the doubling formula for its `x`-coordinate (`hD2`). -/
theorem three_Y (hy : y ≠ 0) :
    2 * (-(nu * ((nu ^ 2 - a₂ - X - x) - X) + Y)) * (x - X) ^ 3 =
      2 * y * (4 * y * Y - (x - X) ^ 3 - 4 * Y ^ 2) := by
  have hE : (128 : F) * y ^ 7 * ((Y - y) ^ 3 - (a₂ + 2 * X + x) * (Y - y) * (X - x) ^ 2 +
      Y * (X - x) ^ 3 - y * (4 * y * Y + (X - x) ^ 3 - 4 * Y ^ 2)) = 0 := by
    linear_combination (128*Y*y^7 + 128*y^8) * hQ + (128*X*a₂*x*y^6 + 64*X*a₄*y^6 + 192*X*x^2*y^6
      - 64*a₂*x^2*y^6 +
      64*a₆*y^6 - 128*x^3*y^6 - 64*y^8) * hT + (64*X^2*y^6 - 128*X*x*y^6 - 32*a₂^2*x^3*y^4 -
      48*a₂*a₄*x^2*y^4 - 32*a₂*a₆*x*y^4 - 80*a₂*x^4*y^4 + 32*a₂*x*y^6 - 16*a₄^2*x*y^4 - 16*a₄*a₆*y^4
      - 64*a₄*x^3*y^4 + 16*a₄*y^6 - 48*a₆*x^2*y^4 - 48*x^5*y^4 + 112*x^2*y^6) * hD2 +
      (128*a₂^3*x^3*y^4 + 192*a₂^2*a₄*x^2*y^4 + 576*a₂^2*x^4*y^4 - 128*a₂^2*x*y^6 + 96*a₂*a₄^2*x*y^4
      + 576*a₂*a₄*x^3*y^4 - 64*a₂*a₄*y^6 + 864*a₂*x^5*y^4 - 576*a₂*x^2*y^6 + 16*a₄^3*y^4 +
      144*a₄^2*x^2*y^4 + 432*a₄*x^4*y^4 - 192*a₄*x*y^6 + 432*x^6*y^4 - 576*x^3*y^6) * hP
  have hE' : (Y - y) ^ 3 - (a₂ + 2 * X + x) * (Y - y) * (X - x) ^ 2 +
      Y * (X - x) ^ 3 - y * (4 * y * Y + (X - x) ^ 3 - 4 * Y ^ 2) = 0 := by
    rcases mul_eq_zero.mp hE with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h c128_ne_zero'
      · exact absurd h (pow_ne_zero _ hy)
    · exact h
  linear_combination (-4*X^3 - 2*X^2*a₂ + 2*X^2*nu^2 + 6*X^2*x + 2*X*Y*nu + 4*X*a₂*x - 4*X*nu^2*x
    - 2*X*nu*y + 2*Y^2
    - 2*Y*nu*x - 4*Y*y - 2*a₂*x^2 + 2*nu^2*x^2 + 2*nu*x*y - 2*x^3 + 2*y^2) * hn + 2 * hE'

end

end Iut.Torsion.Ident
