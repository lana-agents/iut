/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
/-
Elementary ultrametric norm bounds for the entries of the explicit `3 × 3` coefficient
matrices `matR1`, `matR2`, `matR3`, `matB1`, `matB2`, `matBY`, after dividing each entry by
the weight `s ^ (coeffWt a + coeffWt b)` of the homogenising coordinate `W = s` (slot `0`).
-/
import Mathlib

namespace Iut.EtaleTheta

section Mats

variable {F : Type*} [Field F]

/-- `R1 = xx' + xy' + yx' − (e+f)x' − ey' + fx − ey` (translation by `D = (e, f)`). -/
def matR1 (e f : F) : Fin 3 → Fin 3 → F := ![![0, -(e + f), -e], ![f, 1, 1], ![-e, 1, 0]]

/-- `R2/δ`, `δ = e + 2f`. -/
def matR2 (a₄ e f : F) : Fin 3 → Fin 3 → F :=
  ![![-(a₄ ^ 2 + 5 * a₄ * e ^ 2 + a₄ * e + 6 * e ^ 4 + e ^ 3 - 6 * e ^ 2 * f - 6 * e * f ^ 2 -
        e * f - f ^ 2) / (e + 2 * f), (-a₄ * e - 3 * e ^ 3 + 2 * e * f + 2 * f ^ 2) / (e + 2 * f),
      0],
    ![(-a₄ * e - 3 * e ^ 3 + 3 * e * f + 4 * f ^ 2) / (e + 2 * f),
      (a₄ + 3 * e ^ 2 + e + f) / (e + 2 * f), 0],
    ![-e, 1, 0]]

/-- `R3 = yy' + 3e xx' + …`. -/
def matR3 (a₄ e f : F) : Fin 3 → Fin 3 → F :=
  ![![-2 * a₄ * e - 3 * e ^ 3 + 3 * e * f + 3 * f ^ 2, a₄ + e + f, e + f],
    ![a₄ - f, 3 * e, 0], ![-f, 0, 1]]

/-- `B1 = (x − e)(x' − e) − C`, `C = 3e² + a₄ + e/2` (translation by a `2`-torsion point). -/
def matB1 (a₄ e : F) : Fin 3 → Fin 3 → F :=
  ![![e ^ 2 - (3 * e ^ 2 + a₄ + e / 2), -e, 0], ![-e, 1, 0], ![0, 0, 0]]

/-- `B2 = xx' + xy' + yx' − t(x + x') − 2t(y + y')`, `t = e/2`. -/
def matB2 (e : F) : Fin 3 → Fin 3 → F :=
  ![![0, -(e / 2), -(2 * (e / 2))], ![-(e / 2), 1, 1], ![-(2 * (e / 2)), 1, 0]]

/-- `B_YY = yy' + t(y + y') + C(x + x') + 2a₄t + 24t³ + 3t²`. -/
def matBY (a₄ e : F) : Fin 3 → Fin 3 → F :=
  ![![2 * a₄ * (e / 2) + 24 * (e / 2) ^ 3 + 3 * (e / 2) ^ 2, 3 * e ^ 2 + a₄ + e / 2, e / 2],
    ![3 * e ^ 2 + a₄ + e / 2, 0, 0], ![e / 2, 0, 1]]

end Mats

/-- Weights of the three coordinates: the homogenising coordinate `W = s` sits in slot `0`. -/
def coeffWt : Fin 3 → ℕ := ![1, 0, 0]

section Patterns

variable {K : Type*} [Field K]

/-- Reduction pattern of `R2/δ`. -/
def patA0 : Fin 3 → Fin 3 → K := ![![0, 0, 0], ![0, 1, 0], ![0, 1, 0]]

/-- Reduction pattern of `R1 − R2/δ`. -/
def patA1 : Fin 3 → Fin 3 → K := ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]

/-- Reduction pattern of `R3` and of `B_YY` (the form `yy'`). -/
def patY : Fin 3 → Fin 3 → K := ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]

/-- Reduction pattern of `B1` (the form `xx'`). -/
def patB0 : Fin 3 → Fin 3 → K := ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]]

/-- Reduction pattern of `B2` (the form `xx' + xy' + yx'`). -/
def patB1 : Fin 3 → Fin 3 → K := ![![0, 0, 0], ![0, 1, 1], ![0, 1, 0]]

end Patterns

namespace CoeffNorms

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Ultrametric bound for a sum. -/
theorem nadd {x y : K} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x + y‖ ≤ B :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

/-- Ultrametric bound for a difference. -/
theorem nsub {x y : K} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x - y‖ ≤ B := by
  rw [sub_eq_add_neg]
  exact nadd hx (by rwa [norm_neg])

omit [IsUltrametricDist K] in
/-- Bound for a negation. -/
theorem nneg {x : K} {B : ℝ} (hx : ‖x‖ ≤ B) : ‖-x‖ ≤ B := by
  rwa [norm_neg]

omit [IsUltrametricDist K] in
/-- Bound for a product, with power bounds. -/
theorem nmul {x y : K} {r : ℝ} {i j : ℕ} (hx : ‖x‖ ≤ r ^ i) (hy : ‖y‖ ≤ r ^ j) :
    ‖x * y‖ ≤ r ^ (i + j) := by
  rw [norm_mul, pow_add]
  exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)

omit [IsUltrametricDist K] in
/-- Bound for a power, with power bounds. -/
theorem npow {x : K} {r : ℝ} {i : ℕ} (hx : ‖x‖ ≤ r ^ i) (k : ℕ) : ‖x ^ k‖ ≤ r ^ (i * k) := by
  rw [norm_pow, pow_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) hx k

/-- Numerals have norm at most `1` in an ultrametric field. -/
theorem nnum (r : ℝ) (k : ℕ) [k.AtLeastTwo] : ‖(OfNat.ofNat k : K)‖ ≤ r ^ 0 := by
  have h := IsUltrametricDist.norm_natCast_le_one K (OfNat.ofNat k)
  rw [Nat.cast_ofNat] at h
  rwa [pow_zero]

omit [IsUltrametricDist K] in
/-- Zero satisfies every power bound. -/
theorem nzero {r : ℝ} (h0 : 0 ≤ r) {i : ℕ} : ‖(0 : K)‖ ≤ r ^ i := by
  rw [norm_zero]
  exact pow_nonneg h0 i

omit [IsUltrametricDist K] in
/-- Weakening a power bound (`r ≤ 1`). -/
theorem nmono {x : K} {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) {i : ℕ} (hx : ‖x‖ ≤ r ^ i) {j : ℕ}
    (hij : j ≤ i) : ‖x‖ ≤ r ^ j :=
  hx.trans (pow_le_pow_of_le_one h0 h1 hij)

omit [IsUltrametricDist K] in
/-- Bound for a quotient by an element of known norm. -/
theorem ndiv {x y : K} {r : ℝ} (hr : 0 < r) {i j : ℕ} (hx : ‖x‖ ≤ r ^ (i + j))
    (hy : ‖y‖ = r ^ j) : ‖x / y‖ ≤ r ^ i := by
  rw [norm_div, hy, div_le_iff₀ (pow_pos hr j), ← pow_add]
  exact hx

omit [IsUltrametricDist K] in
/-- The generic off-pattern entry bound: `‖x / s ^ k - 0‖ ≤ ‖s‖` from `‖x‖ ≤ ‖s‖ ^ (i + k)`,
`1 ≤ i`. -/
theorem nentry {s x : K} (hs0 : 0 < ‖s‖) (hs1 : ‖s‖ < 1) {i k : ℕ}
    (hx : ‖x‖ ≤ ‖s‖ ^ (i + k)) (hi : 1 ≤ i) : ‖x / s ^ k - 0‖ ≤ ‖s‖ := by
  rw [sub_zero]
  have h := nmono hs0.le hs1.le (ndiv hs0 hx (norm_pow s k)) hi
  rwa [pow_one] at h

/-- Isosceles principle: a small perturbation keeps the norm. -/
theorem norm_eq_of_sub {a b : K} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by
  have h' : ‖b‖ ≠ ‖a - b‖ := h.ne'
  rw [← add_sub_cancel b a, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h',
    max_eq_left h.le]

end CoeffNorms

open CoeffNorms

section CaseA

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- In case (A), `‖e‖ = ‖s‖ ^ (2d)`. -/
theorem caseA_norm_e {s e w : K} (hs0 : 0 < ‖s‖) (hs1 : ‖s‖ < 1) {d : ℕ}
    (hw : ‖w‖ = ‖s‖ ^ (2 * d)) (hew : ‖e - w‖ ≤ ‖s‖ ^ (2 * d + 2)) :
    ‖e‖ = ‖s‖ ^ (2 * d) := by
  rw [← hw]
  refine norm_eq_of_sub (hew.trans_lt ?_)
  rw [hw]
  exact pow_lt_pow_right_of_lt_one₀ hs0 hs1 (by omega)

/-- In case (A), `‖e + 2f‖ = ‖s‖ ^ (2d)`. -/
theorem caseA_norm_delta {s e f w : K} (h2 : ‖(2 : K)‖ = 1) (hs0 : 0 < ‖s‖) (hs1 : ‖s‖ < 1)
    {d : ℕ} (hw : ‖w‖ = ‖s‖ ^ (2 * d)) (hew : ‖e - w‖ ≤ ‖s‖ ^ (2 * d + 2))
    (hf : ‖f‖ ≤ ‖s‖ ^ (2 * d + 2)) : ‖e + 2 * f‖ = ‖s‖ ^ (2 * d) := by
  have he := caseA_norm_e hs0 hs1 hw hew
  rw [← he]
  refine norm_eq_of_sub ?_
  rw [add_sub_cancel_left, norm_mul, h2, one_mul, he]
  exact hf.trans_lt (pow_lt_pow_right_of_lt_one₀ hs0 hs1 (by omega))

/-- In case (A), `e + 2f ≠ 0`. -/
theorem caseA_delta_ne_zero {s e f w : K} (h2 : ‖(2 : K)‖ = 1) (hs0 : 0 < ‖s‖)
    (hs1 : ‖s‖ < 1) {d : ℕ} (hw : ‖w‖ = ‖s‖ ^ (2 * d)) (hew : ‖e - w‖ ≤ ‖s‖ ^ (2 * d + 2))
    (hf : ‖f‖ ≤ ‖s‖ ^ (2 * d + 2)) : e + 2 * f ≠ 0 := by
  rw [← norm_ne_zero_iff, caseA_norm_delta h2 hs0 hs1 hw hew hf]
  exact (pow_pos hs0 _).ne'

variable {s e f a₄ w : K} {d n : ℕ}

/-- Numerator bound shared by the entries of case (A). -/
private theorem caseA_bounds (h2 : ‖(2 : K)‖ = 1) (hs0 : 0 < ‖s‖) (hs1 : ‖s‖ < 1)
    (hd : 1 ≤ d) (hn : 2 * d < n) (hw : ‖w‖ = ‖s‖ ^ (2 * d))
    (hew : ‖e - w‖ ≤ ‖s‖ ^ (2 * d + 2)) (hf : ‖f‖ ≤ ‖s‖ ^ (2 * d + 2))
    (ha : ‖a₄‖ ≤ ‖s‖ ^ (2 * n)) :
    ‖-(a₄ ^ 2 + 5 * a₄ * e ^ 2 + a₄ * e + 6 * e ^ 4 + e ^ 3 - 6 * e ^ 2 * f - 6 * e * f ^ 2 -
        e * f - f ^ 2) / (e + 2 * f)‖ ≤ ‖s‖ ^ (2 * d + 2) ∧
    ‖(-a₄ * e - 3 * e ^ 3 + 2 * e * f + 2 * f ^ 2) / (e + 2 * f)‖ ≤ ‖s‖ ^ (2 * d + 2) ∧
    ‖(-a₄ * e - 3 * e ^ 3 + 3 * e * f + 4 * f ^ 2) / (e + 2 * f)‖ ≤ ‖s‖ ^ (2 * d + 2) ∧
    ‖(a₄ + 3 * e ^ 2 + e + f) / (e + 2 * f) - 1‖ ≤ ‖s‖ ^ 2 ∧
    ‖-2 * a₄ * e - 3 * e ^ 3 + 3 * e * f + 3 * f ^ 2‖ ≤ ‖s‖ ^ (4 * d + 2) ∧
    ‖e‖ ≤ ‖s‖ ^ (2 * d) ∧ ‖a₄‖ ≤ ‖s‖ ^ (4 * d + 2) := by
  set r := ‖s‖
  have m : ∀ {x : K} {i : ℕ}, ‖x‖ ≤ r ^ i → ∀ {j : ℕ}, j ≤ i → ‖x‖ ≤ r ^ j :=
    fun hx _ hij => nmono hs0.le hs1.le hx hij
  have hE : ‖e‖ ≤ r ^ (2 * d) := (caseA_norm_e hs0 hs1 hw hew).le
  have hδ := caseA_norm_delta h2 hs0 hs1 hw hew hf
  have hδne := caseA_delta_ne_zero h2 hs0 hs1 hw hew hf
  have hA : ‖a₄‖ ≤ r ^ (4 * d + 2) := m ha (by omega)
  have hF := hf
  refine ⟨?_, ?_, ?_, ?_, ?_, hE, hA⟩
  · refine ndiv hs0 (j := 2 * d) (m (nneg (nsub (nsub (nsub (nsub (nadd (nadd (nadd (nadd
      (m (npow hA 2) (j := 4 * d + 2) (by omega))
      (m (nmul (nmul (nnum r 5) hA) (npow hE 2)) (by omega)))
      (m (nmul hA hE) (by omega)))
      (m (nmul (nnum r 6) (npow hE 4)) (by omega)))
      (m (npow hE 3) (by omega)))
      (m (nmul (nmul (nnum r 6) (npow hE 2)) hF) (by omega)))
      (m (nmul (nmul (nnum r 6) hE) (npow hF 2)) (by omega)))
      (m (nmul hE hF) (by omega)))
      (m (npow hF 2) (by omega)))) (by omega)) hδ
  · refine ndiv hs0 (j := 2 * d) (m (nadd (nadd (nsub
      (m (nmul (nneg hA) hE) (j := 4 * d + 2) (by omega))
      (m (nmul (nnum r 3) (npow hE 3)) (by omega)))
      (m (nmul (nmul (nnum r 2) hE) hF) (by omega)))
      (m (nmul (nnum r 2) (npow hF 2)) (by omega))) (by omega)) hδ
  · refine ndiv hs0 (j := 2 * d) (m (nadd (nadd (nsub
      (m (nmul (nneg hA) hE) (j := 4 * d + 2) (by omega))
      (m (nmul (nnum r 3) (npow hE 3)) (by omega)))
      (m (nmul (nmul (nnum r 3) hE) hF) (by omega)))
      (m (nmul (nnum r 4) (npow hF 2)) (by omega))) (by omega)) hδ
  · rw [div_sub_one hδne,
      show a₄ + 3 * e ^ 2 + e + f - (e + 2 * f) = a₄ + 3 * e ^ 2 - f by ring]
    refine ndiv hs0 (j := 2 * d) (nsub (nadd
      (m hA (j := 2 + 2 * d) (by omega))
      (m (nmul (nnum r 3) (npow hE 2)) (by omega)))
      (m hF (by omega))) hδ
  · exact nadd (nadd (nsub
      (m (nmul (nmul (nneg (nnum r 2)) hA) hE) (by omega))
      (m (nmul (nnum r 3) (npow hE 3)) (by omega)))
      (m (nmul (nmul (nnum r 3) hE) hF) (by omega)))
      (m (nmul (nnum r 3) (npow hF 2)) (by omega))

/-- Case (A): entry bounds for `R2/δ` against the pattern `patA0`. -/
theorem caseA_matR2 (h2 : ‖(2 : K)‖ = 1) (hs0 : 0 < ‖s‖) (hs1 : ‖s‖ < 1)
    (hd : 1 ≤ d) (hn : 2 * d < n) (hw : ‖w‖ = ‖s‖ ^ (2 * d))
    (hew : ‖e - w‖ ≤ ‖s‖ ^ (2 * d + 2)) (hf : ‖f‖ ≤ ‖s‖ ^ (2 * d + 2))
    (ha : ‖a₄‖ ≤ ‖s‖ ^ (2 * n)) (a b : Fin 3) :
    ‖matR2 a₄ e f a b / s ^ (coeffWt a + coeffWt b) - patA0 a b‖ ≤ ‖s‖ := by
  obtain ⟨h11, h1x, hx1, hc, -, hE, -⟩ := caseA_bounds h2 hs0 hs1 hd hn hw hew hf ha
  have m : ∀ {x : K} {i : ℕ}, ‖x‖ ≤ ‖s‖ ^ i → ∀ {j : ℕ}, j ≤ i → ‖x‖ ≤ ‖s‖ ^ j :=
    fun hx _ hij => nmono hs0.le hs1.le hx hij
  fin_cases a <;> fin_cases b
  · exact nentry hs0 hs1 (k := 2) (i := 2 * d) (m h11 (by omega)) (by omega)
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d + 1) (m h1x (by omega)) (by omega)
  · simp [matR2, coeffWt, patA0]
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d + 1) (m hx1 (by omega)) (by omega)
  · change ‖(a₄ + 3 * e ^ 2 + e + f) / (e + 2 * f) / s ^ 0 - 1‖ ≤ ‖s‖
    rw [pow_zero, div_one]
    exact (m hc (j := 1) (by omega)).trans_eq (pow_one _)
  · simp [matR2, coeffWt, patA0]
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1) (m (nneg hE) (by omega)) (by omega)
  · simp [matR2, coeffWt, patA0]
  · simp [matR2, coeffWt, patA0]

/-- Case (A): entry bounds for `R1 − R2/δ` against the pattern `patA1`. -/
theorem caseA_matR1_sub_matR2 (h2 : ‖(2 : K)‖ = 1) (hs0 : 0 < ‖s‖) (hs1 : ‖s‖ < 1)
    (hd : 1 ≤ d) (hn : 2 * d < n) (hw : ‖w‖ = ‖s‖ ^ (2 * d))
    (hew : ‖e - w‖ ≤ ‖s‖ ^ (2 * d + 2)) (hf : ‖f‖ ≤ ‖s‖ ^ (2 * d + 2))
    (ha : ‖a₄‖ ≤ ‖s‖ ^ (2 * n)) (a b : Fin 3) :
    ‖(matR1 e f - matR2 a₄ e f) a b / s ^ (coeffWt a + coeffWt b) - patA1 a b‖ ≤ ‖s‖ := by
  obtain ⟨h11, h1x, hx1, hc, -, hE, -⟩ := caseA_bounds h2 hs0 hs1 hd hn hw hew hf ha
  have m : ∀ {x : K} {i : ℕ}, ‖x‖ ≤ ‖s‖ ^ i → ∀ {j : ℕ}, j ≤ i → ‖x‖ ≤ ‖s‖ ^ j :=
    fun hx _ hij => nmono hs0.le hs1.le hx hij
  fin_cases a <;> fin_cases b
  · exact nentry hs0 hs1 (k := 2) (i := 2 * d) (m (nsub (nzero hs0.le) h11) (by omega))
      (by omega)
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1)
      (m (nsub (nneg (nadd hE (m hf (by omega)))) (m h1x (by omega))) (by omega)) (by omega)
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1) (m (nsub (nneg hE) (nzero hs0.le)) (by omega))
      (by omega)
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1)
      (m (nsub (m hf (j := 2 * d) (by omega)) (m hx1 (by omega))) (by omega)) (by omega)
  · change ‖(1 - (a₄ + 3 * e ^ 2 + e + f) / (e + 2 * f)) / s ^ 0 - 0‖ ≤ ‖s‖
    rw [pow_zero, div_one, sub_zero, ← norm_neg, neg_sub]
    exact (m hc (j := 1) (by omega)).trans_eq (pow_one _)
  all_goals simp [matR1, matR2, coeffWt, patA1]

/-- Case (A): entry bounds for `R3` against the pattern `patY`. -/
theorem caseA_matR3 (h2 : ‖(2 : K)‖ = 1) (hs0 : 0 < ‖s‖) (hs1 : ‖s‖ < 1)
    (hd : 1 ≤ d) (hn : 2 * d < n) (hw : ‖w‖ = ‖s‖ ^ (2 * d))
    (hew : ‖e - w‖ ≤ ‖s‖ ^ (2 * d + 2)) (hf : ‖f‖ ≤ ‖s‖ ^ (2 * d + 2))
    (ha : ‖a₄‖ ≤ ‖s‖ ^ (2 * n)) (a b : Fin 3) :
    ‖matR3 a₄ e f a b / s ^ (coeffWt a + coeffWt b) - patY a b‖ ≤ ‖s‖ := by
  obtain ⟨-, -, -, -, h3, hE, hA⟩ := caseA_bounds h2 hs0 hs1 hd hn hw hew hf ha
  have m : ∀ {x : K} {i : ℕ}, ‖x‖ ≤ ‖s‖ ^ i → ∀ {j : ℕ}, j ≤ i → ‖x‖ ≤ ‖s‖ ^ j :=
    fun hx _ hij => nmono hs0.le hs1.le hx hij
  fin_cases a <;> fin_cases b
  · exact nentry hs0 hs1 (k := 2) (i := 4 * d) (m h3 (by omega)) (by omega)
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1)
      (m (nadd (nadd (m hA (j := 2 * d) (by omega)) hE) (m hf (by omega))) (by omega)) (by omega)
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1)
      (m (nadd hE (m hf (by omega))) (by omega)) (by omega)
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d + 1)
      (m (nsub (m hA (j := 2 * d + 2) (by omega)) hf) (by omega)) (by omega)
  · exact nentry hs0 hs1 (k := 0) (i := 2 * d) (m (nmul (nnum ‖s‖ 3) hE) (by omega)) (by omega)
  · simp [matR3, coeffWt, patY]
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d + 1) (m (nneg hf) (by omega)) (by omega)
  · simp [matR3, coeffWt, patY]
  · simp [matR3, coeffWt, patY]

end CaseA

section CaseB

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {s e a₄ : K} {d n : ℕ}

/-- Norm bounds shared by the entries of case (B). -/
private theorem caseB_bounds (h2 : ‖(2 : K)‖ = 1) (hs0 : 0 < ‖s‖) (hs1 : ‖s‖ < 1)
    (hn : 2 * d = n) (he : ‖e‖ ≤ ‖s‖ ^ (2 * d)) (ha : ‖a₄‖ ≤ ‖s‖ ^ (2 * n)) :
    ‖e / 2‖ ≤ ‖s‖ ^ (2 * d) ∧ ‖3 * e ^ 2 + a₄ + e / 2‖ ≤ ‖s‖ ^ (2 * d) ∧
    ‖2 * a₄ * (e / 2) + 24 * (e / 2) ^ 3 + 3 * (e / 2) ^ 2‖ ≤ ‖s‖ ^ (4 * d) := by
  have m : ∀ {x : K} {i : ℕ}, ‖x‖ ≤ ‖s‖ ^ i → ∀ {j : ℕ}, j ≤ i → ‖x‖ ≤ ‖s‖ ^ j :=
    fun hx _ hij => nmono hs0.le hs1.le hx hij
  have hE2 : ‖e / 2‖ ≤ ‖s‖ ^ (2 * d) := by
    rw [norm_div, h2, div_one]
    exact he
  have hA : ‖a₄‖ ≤ ‖s‖ ^ (4 * d) := m ha (by omega)
  refine ⟨hE2, nadd (nadd (m (nmul (nnum ‖s‖ 3) (npow he 2)) (by omega))
    (m hA (by omega))) hE2, ?_⟩
  exact nadd (nadd (m (nmul (nmul (nnum ‖s‖ 2) hA) hE2) (by omega))
    (m (nmul (nnum ‖s‖ 24) (npow hE2 3)) (by omega)))
    (m (nmul (nnum ‖s‖ 3) (npow hE2 2)) (by omega))

/-- Case (B): entry bounds for `B1` against the pattern `patB0`. -/
theorem caseB_matB1 (h2 : ‖(2 : K)‖ = 1) (hs0 : 0 < ‖s‖) (hs1 : ‖s‖ < 1)
    (hd : 2 ≤ d) (hn : 2 * d = n) (he : ‖e‖ ≤ ‖s‖ ^ (2 * d)) (ha : ‖a₄‖ ≤ ‖s‖ ^ (2 * n))
    (a b : Fin 3) :
    ‖matB1 a₄ e a b / s ^ (coeffWt a + coeffWt b) - patB0 a b‖ ≤ ‖s‖ := by
  obtain ⟨-, hC, -⟩ := caseB_bounds h2 hs0 hs1 hn he ha
  have m : ∀ {x : K} {i : ℕ}, ‖x‖ ≤ ‖s‖ ^ i → ∀ {j : ℕ}, j ≤ i → ‖x‖ ≤ ‖s‖ ^ j :=
    fun hx _ hij => nmono hs0.le hs1.le hx hij
  fin_cases a <;> fin_cases b
  · exact nentry hs0 hs1 (k := 2) (i := 2 * d - 2)
      (m (nsub (m (npow he 2) (j := 2 * d) (by omega)) hC) (by omega)) (by omega)
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1) (m (nneg he) (by omega)) (by omega)
  · simp [matB1, coeffWt, patB0]
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1) (m (nneg he) (by omega)) (by omega)
  all_goals simp [matB1, coeffWt, patB0]

/-- Case (B): entry bounds for `B2` against the pattern `patB1`. -/
theorem caseB_matB2 (h2 : ‖(2 : K)‖ = 1) (hs0 : 0 < ‖s‖) (hs1 : ‖s‖ < 1)
    (hd : 2 ≤ d) (hn : 2 * d = n) (he : ‖e‖ ≤ ‖s‖ ^ (2 * d)) (ha : ‖a₄‖ ≤ ‖s‖ ^ (2 * n))
    (a b : Fin 3) :
    ‖matB2 e a b / s ^ (coeffWt a + coeffWt b) - patB1 a b‖ ≤ ‖s‖ := by
  obtain ⟨hE2, -, -⟩ := caseB_bounds h2 hs0 hs1 hn he ha
  have m : ∀ {x : K} {i : ℕ}, ‖x‖ ≤ ‖s‖ ^ i → ∀ {j : ℕ}, j ≤ i → ‖x‖ ≤ ‖s‖ ^ j :=
    fun hx _ hij => nmono hs0.le hs1.le hx hij
  fin_cases a <;> fin_cases b
  · simp [matB2, coeffWt, patB1]
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1) (m (nneg hE2) (by omega)) (by omega)
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1)
      (m (nneg (nmul (nnum ‖s‖ 2) hE2)) (by omega)) (by omega)
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1) (m (nneg hE2) (by omega)) (by omega)
  · simp [matB2, coeffWt, patB1]
  · simp [matB2, coeffWt, patB1]
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1)
      (m (nneg (nmul (nnum ‖s‖ 2) hE2)) (by omega)) (by omega)
  all_goals simp [matB2, coeffWt, patB1]

/-- Case (B): entry bounds for `B_YY` against the pattern `patY`. -/
theorem caseB_matBY (h2 : ‖(2 : K)‖ = 1) (hs0 : 0 < ‖s‖) (hs1 : ‖s‖ < 1)
    (hd : 2 ≤ d) (hn : 2 * d = n) (he : ‖e‖ ≤ ‖s‖ ^ (2 * d)) (ha : ‖a₄‖ ≤ ‖s‖ ^ (2 * n))
    (a b : Fin 3) :
    ‖matBY a₄ e a b / s ^ (coeffWt a + coeffWt b) - patY a b‖ ≤ ‖s‖ := by
  obtain ⟨hE2, hC, hW⟩ := caseB_bounds h2 hs0 hs1 hn he ha
  have m : ∀ {x : K} {i : ℕ}, ‖x‖ ≤ ‖s‖ ^ i → ∀ {j : ℕ}, j ≤ i → ‖x‖ ≤ ‖s‖ ^ j :=
    fun hx _ hij => nmono hs0.le hs1.le hx hij
  fin_cases a <;> fin_cases b
  · exact nentry hs0 hs1 (k := 2) (i := 4 * d - 2) (m hW (by omega)) (by omega)
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1) (m hC (by omega)) (by omega)
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1) (m hE2 (by omega)) (by omega)
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1) (m hC (by omega)) (by omega)
  · simp [matBY, coeffWt, patY]
  · simp [matBY, coeffWt, patY]
  · exact nentry hs0 hs1 (k := 1) (i := 2 * d - 1) (m hE2 (by omega)) (by omega)
  all_goals simp [matBY, coeffWt, patY]

end CaseB

end Iut.EtaleTheta
