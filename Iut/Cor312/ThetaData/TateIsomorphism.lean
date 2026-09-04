/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Iut.Cor312.ThetaData.UltrametricSqrt
import TateCurvesTheta

/-!
# Tate's isomorphism theorem: split multiplicative curves are Tate curves

Over a complete ultrametric field `k` with `‖2‖ = 1` (residue characteristic `≠ 2`) and
`12 ≠ 0`, an
elliptic curve `W` with `‖c₄‖ = 1`, `‖Δ‖ < 1` (multiplicative reduction) whose tangent quadratic
at the node has a root modulo the maximal ideal (split reduction) is isomorphic over `k` to the
Tate curve `E_q` of the unique Tate parameter `q` with `j(E_q) = j(W)` (Silverman, *Advanced
Topics*, V.5.3). The argument:

* `‖j(W)‖ > 1`, so `q` exists (`TateCurvesTheta`, `exists_tateParameter_tateJ_eq`);
* both curves have short Weierstrass normal forms `y² = x³ + ax + b`, `y² = x³ + a'x + b'`
  (Mathlib, `exists_variableChange_isShortNF`), and equal `j` gives `a'³b² = a³b'²`, so the two
  normal forms differ by the scaling `u` with `u² = λ := a'b/(ab')`
  (`Iut.exists_scaleChange_of_j_eq`) — provided `λ` is a square;
* `λ` is, up to visible squares, the ratio `c₄c₆(W)/c₄c₆(E_q)`, and both `−c₄c₆(W)` and
  `−c₄c₆(E_q)` are units congruent to squares modulo the maximal ideal: for `W` because
  `−c₄c₆` is the discriminant of the tangent quadratic, for `E_q` because `c₄ ≡ 1`, `c₆ ≡ −1`;
  Hensel's lemma (`Iut.exists_sq_eq_of_norm_sq_sub_lt`) then makes the ratio a square.
-/

namespace Iut

open WeierstrassCurve TateCurvesTheta

noncomputable section

variable {k : Type*} [NormedField k]

/-- The scaling change of variables `(u, 0, 0, 0)`. -/
def scaleChange (u : kˣ) : VariableChange k := ⟨u, 0, 0, 0⟩

section ShortNF

variable (W₁ W₂ : WeierstrassCurve k) [W₁.IsShortNF] [W₂.IsShortNF]

/-- A scaling carries one short normal form to another when the coefficients match. -/
lemma scaleChange_smul_eq (u : kˣ) (h4 : W₂.a₄ = (u : k)⁻¹ ^ 4 * W₁.a₄)
    (h6 : W₂.a₆ = (u : k)⁻¹ ^ 6 * W₁.a₆) : scaleChange u • W₁ = W₂ := by
  ext
  · rw [variableChange_a₁, a₁_of_isShortNF, a₁_of_isShortNF]
    simp [scaleChange]
  · rw [variableChange_a₂, a₂_of_isShortNF, a₂_of_isShortNF, a₁_of_isShortNF]
    simp [scaleChange]
  · rw [variableChange_a₃, a₃_of_isShortNF, a₃_of_isShortNF, a₁_of_isShortNF]
    simp [scaleChange]
  · rw [variableChange_a₄, a₃_of_isShortNF, a₂_of_isShortNF, a₁_of_isShortNF, h4]
    simp [scaleChange]
  · rw [variableChange_a₆, a₃_of_isShortNF, a₂_of_isShortNF, a₁_of_isShortNF, h6]
    simp [scaleChange]

variable [IsUltrametricDist k] [W₁.IsElliptic] [W₂.IsElliptic]

private lemma norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : k)‖ ≤ 1 := by
  rw [← Nat.cast_ofNat]
  exact IsUltrametricDist.norm_natCast_le_one k _

/-- In a short normal form with non-integral `j`, both coefficients are nonzero. -/
lemma coeff_ne_zero_of_isShortNF (h2 : (2 : k) ≠ 0) (hj : 1 < ‖W₁.j‖) :
    W₁.a₄ ≠ 0 ∧ W₁.a₆ ≠ 0 := by
  have hΔ : W₁.Δ ≠ 0 := by rw [← coe_Δ']; exact W₁.Δ'.ne_zero
  have hD : 4 * W₁.a₄ ^ 3 + 27 * W₁.a₆ ^ 2 ≠ 0 := by
    intro h
    apply hΔ
    rw [Δ_of_isShortNF, h, mul_zero]
  have hjeq := W₁.j_of_isShortNF
  constructor
  · intro ha
    rw [hjeq, ha] at hj
    norm_num at hj
  · intro hb
    rw [hjeq, hb] at hj
    have ha : W₁.a₄ ≠ 0 := by
      intro ha
      apply hD
      rw [ha, hb]
      ring
    have h4 : (4 : k) ≠ 0 := by
      have : (4 : k) = 2 ^ 2 := by norm_num
      rw [this]
      exact pow_ne_zero _ h2
    have : (6912 * W₁.a₄ ^ 3 / (4 * W₁.a₄ ^ 3 + 27 * 0 ^ 2) : k) = 1728 := by
      field_simp
      ring
    rw [this] at hj
    exact absurd hj (not_lt.mpr (norm_ofNat_le_one 1728))

/-- **Short normal forms with equal `j`-invariant differ by a scaling** `u` with
`u² = a'b/(ab')`, provided that ratio is a square. -/
theorem exists_scaleChange_of_j_eq (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (hj1 : 1 < ‖W₁.j‖) (hj : W₁.j = W₂.j)
    (hsq : IsSquare ((W₂.a₄ * W₁.a₆) / (W₁.a₄ * W₂.a₆))) :
    ∃ u : kˣ, scaleChange u • W₁ = W₂ := by
  obtain ⟨ha, hb⟩ := coeff_ne_zero_of_isShortNF W₁ h2 hj1
  obtain ⟨ha', hb'⟩ := coeff_ne_zero_of_isShortNF W₂ h2 (hj ▸ hj1)
  have hD : 4 * W₁.a₄ ^ 3 + 27 * W₁.a₆ ^ 2 ≠ 0 := by
    intro h
    have hΔ : W₁.Δ ≠ 0 := by rw [← coe_Δ']; exact W₁.Δ'.ne_zero
    exact hΔ (by rw [Δ_of_isShortNF, h, mul_zero])
  have hD' : 4 * W₂.a₄ ^ 3 + 27 * W₂.a₆ ^ 2 ≠ 0 := by
    intro h
    have hΔ : W₂.Δ ≠ 0 := by rw [← coe_Δ']; exact W₂.Δ'.ne_zero
    exact hΔ (by rw [Δ_of_isShortNF, h, mul_zero])
  -- the key relation `a'³ b² = a³ b'²`
  have key : W₂.a₄ ^ 3 * W₁.a₆ ^ 2 = W₁.a₄ ^ 3 * W₂.a₆ ^ 2 := by
    have h := hj
    rw [W₁.j_of_isShortNF, W₂.j_of_isShortNF, div_eq_div_iff hD hD'] at h
    have hc : (6912 * 27 : k) ≠ 0 := by
      have : (6912 * 27 : k) = 2 ^ 8 * 3 ^ 6 := by norm_num
      rw [this]
      exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
    apply mul_left_cancel₀ hc
    linear_combination -h
  obtain ⟨u₀, hu₀⟩ := hsq
  set lam := (W₂.a₄ * W₁.a₆) / (W₁.a₄ * W₂.a₆) with hlam
  have hlam0 : lam ≠ 0 := by
    rw [hlam]
    exact div_ne_zero (mul_ne_zero ha' hb) (mul_ne_zero ha hb')
  have hu₀0 : u₀ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu₀
    exact hlam0 hu₀
  -- `a' λ² = a` and `b' λ³ = b`
  have h4 : W₂.a₄ * lam ^ 2 = W₁.a₄ := by
    rw [hlam, div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero _ (mul_ne_zero ha hb'))]
    linear_combination key
  have h6 : W₂.a₆ * lam ^ 3 = W₁.a₆ := by
    rw [hlam, div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero _ (mul_ne_zero ha hb'))]
    linear_combination W₁.a₆ * W₂.a₆ * key
  refine ⟨Units.mk0 u₀ hu₀0, scaleChange_smul_eq W₁ W₂ _ ?_ ?_⟩
  · rw [Units.val_mk0, show (u₀⁻¹) ^ 4 = ((u₀ * u₀)⁻¹) ^ 2 by ring, ← hu₀, ← h4]
    field_simp
  · rw [Units.val_mk0, show (u₀⁻¹) ^ 6 = ((u₀ * u₀)⁻¹) ^ 3 by ring, ← hu₀, ← h6]
    field_simp

end ShortNF

/-! ## The isomorphism theorem -/

section Main

variable [IsUltrametricDist k] [CompleteSpace k]

omit [IsUltrametricDist k] [CompleteSpace k] in
/-- `1728 Δ = c₄³ - c₆²`. -/
lemma c₄_pow_sub_c₆_sq (W : WeierstrassCurve k) : W.c₄ ^ 3 - W.c₆ ^ 2 = 1728 * W.Δ := by
  simp only [c₄, c₆, Δ, b₂, b₄, b₆, b₈]
  ring

omit [IsUltrametricDist k] [CompleteSpace k] in
/-- **The discriminant of the tangent quadratic at the node is `−c₄c₆`**: for every `r`,
`(2c₄r + a₁c₄)² = −c₄c₆ + 4c₄·f(r)` where `f(r) = c₄r² + a₁c₄r − (54b₆ − 3b₂b₄ + a₂c₄)`. -/
lemma tangent_sq_eq (W : WeierstrassCurve k) (r : k) :
    (2 * W.c₄ * r + W.a₁ * W.c₄) ^ 2 =
      -(W.c₄ * W.c₆) + 4 * W.c₄ *
        (W.c₄ * r ^ 2 + W.a₁ * W.c₄ * r - (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
  simp only [c₄, c₆, b₂, b₄, b₆]
  ring

omit [CompleteSpace k] in
private lemma norm_ofNat_le_one' (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : k)‖ ≤ 1 := by
  rw [← Nat.cast_ofNat]
  exact IsUltrametricDist.norm_natCast_le_one k _

omit [IsUltrametricDist k] [CompleteSpace k] in
private lemma norm_mul_lt_one_of_le_of_lt {a b : k} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ < 1) :
    ‖a * b‖ < 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg a, norm_nonneg b]

omit [IsUltrametricDist k] [CompleteSpace k] in
private lemma norm_mul_lt_one_of_lt_of_le {a b : k} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) :
    ‖a * b‖ < 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg a, norm_nonneg b]

omit [CompleteSpace k] in
/-- `‖x + y‖ = ‖x‖` when `‖y‖ < ‖x‖`. -/
private lemma norm_add_eq_left {x y : k} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

omit [CompleteSpace k] in
/-- `‖c₆‖ = 1` for a curve with `‖c₄‖ = 1`, `‖Δ‖ < 1`. -/
lemma norm_c₆_eq_one (W : WeierstrassCurve k) (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1) :
    ‖W.c₆‖ = 1 := by
  have h : W.c₆ ^ 2 = W.c₄ ^ 3 + -(1728 * W.Δ) := by
    have := c₄_pow_sub_c₆_sq W
    linear_combination -this
  have hn : ‖W.c₆ ^ 2‖ = 1 := by
    rw [h, norm_add_eq_left, norm_pow, hc₄, one_pow]
    rw [norm_pow, hc₄, one_pow, norm_neg]
    exact norm_mul_lt_one_of_le_of_lt (norm_ofNat_le_one' 1728) hΔ
  rw [norm_pow] at hn
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hn

omit [IsUltrametricDist k] [CompleteSpace k] in
/-- `c₆(E_q) = −1 + 72 a₄ − 864 a₆`. -/
lemma tateCurve_c₆ (t : TateParameter k) : t.tateCurve.c₆ = -1 + 72 * t.a₄ - 864 * t.a₆ := by
  simp only [c₆, t.tateCurve_b₂, t.tateCurve_b₄, t.tateCurve_b₆]
  ring

/-- `c₄c₆(E_q) ≡ −1` modulo the maximal ideal. -/
lemma norm_tateCurve_c₄_mul_c₆_add_one_lt (t : TateParameter k) (h12 : (12 : k) ≠ 0) :
    ‖t.tateCurve.c₄ * t.tateCurve.c₆ + 1‖ < 1 := by
  have h4 := t.norm_a₄_lt_one
  have h6 := t.norm_a₆_lt_one h12
  have : t.tateCurve.c₄ * t.tateCurve.c₆ + 1 =
      t.a₄ * (120 - 3456 * t.a₄ + 41472 * t.a₆) + (-864) * t.a₆ := by
    rw [t.tateCurve_c₄, tateCurve_c₆]
    ring
  rw [this]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · refine norm_mul_lt_one_of_lt_of_le h4 ?_
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_ofNat_le_one' 120) ?_)
      rw [norm_neg, norm_mul]
      exact mul_le_one₀ (norm_ofNat_le_one' 3456) (norm_nonneg _) h4.le
    · rw [norm_mul]
      exact mul_le_one₀ (norm_ofNat_le_one' 41472) (norm_nonneg _) h6.le
  · rw [norm_mul, norm_neg]
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_ofNat_le_one' 864) (norm_nonneg _) h6

/-- **The ratio `c₄c₆(W)/c₄c₆(E_q)` is a square** when the tangent quadratic of `W` at its node
has a root modulo the maximal ideal. -/
lemma isSquare_ratio (h12 : (12 : k) ≠ 0)
    (hsqrt : ∀ a x₀ : k, ‖x₀‖ = 1 → ‖x₀ ^ 2 - a‖ < 1 → ∃ x, x ^ 2 = a)
    (W : WeierstrassCurve k) (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1)
    (hroot : ∃ r : k, ‖W.c₄ * r ^ 2 + W.a₁ * W.c₄ * r
      - (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)‖ < 1)
    (t : TateParameter k) :
    IsSquare ((W.c₄ * W.c₆) / (t.tateCurve.c₄ * t.tateCurve.c₆)) := by
  obtain ⟨r, hr⟩ := hroot
  have hc₆ := norm_c₆_eq_one W hc₄ hΔ
  set s := 2 * W.c₄ * r + W.a₁ * W.c₄ with hs
  set ε₁ := 4 * W.c₄ *
    (W.c₄ * r ^ 2 + W.a₁ * W.c₄ * r - (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) with hε₁
  have hs2 : s ^ 2 = -(W.c₄ * W.c₆) + ε₁ := tangent_sq_eq W r
  have hε₁n : ‖ε₁‖ < 1 := by
    rw [hε₁, mul_assoc]
    refine norm_mul_lt_one_of_le_of_lt (norm_ofNat_le_one' 4) ?_
    exact norm_mul_lt_one_of_le_of_lt hc₄.le hr
  have hDW : ‖W.c₄ * W.c₆‖ = 1 := by rw [norm_mul, hc₄, hc₆, one_mul]
  have hsn : ‖s‖ = 1 := by
    have : ‖s ^ 2‖ = 1 := by
      rw [hs2, norm_add_eq_left, norm_neg, hDW]
      rw [norm_neg, hDW]
      exact hε₁n
    rw [norm_pow] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  set ε₂ := t.tateCurve.c₄ * t.tateCurve.c₆ + 1 with hε₂
  have hε₂n : ‖ε₂‖ < 1 := norm_tateCurve_c₄_mul_c₆_add_one_lt t h12
  have hD' : t.tateCurve.c₄ * t.tateCurve.c₆ = -1 + ε₂ := by rw [hε₂]; ring
  have hden : ‖(-1 : k) + ε₂‖ = 1 := by
    rw [norm_add_eq_left] <;> rw [norm_neg, norm_one]
    exact hε₂n
  have hden0 : (-1 : k) + ε₂ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden
    exact zero_ne_one hden
  set μ := (W.c₄ * W.c₆) / (t.tateCurve.c₄ * t.tateCurve.c₆) with hμ
  have key : s ^ 2 - μ = (-(W.c₄ * W.c₆) * ε₂ - ε₁ + ε₁ * ε₂) / (-1 + ε₂) := by
    rw [hμ, hD', hs2]
    field_simp
    ring
  have hlt : ‖s ^ 2 - μ‖ < 1 := by
    rw [key, norm_div, hden, div_one]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_mul, norm_neg, hDW, one_mul]
        exact hε₂n
      · rw [norm_neg]
        exact hε₁n
    · exact norm_mul_lt_one_of_lt_of_le hε₁n hε₂n.le
  obtain ⟨m, hm⟩ := hsqrt μ s hsn hlt
  exact ⟨m, by rw [← hm, sq]⟩

/-- **Tate's isomorphism theorem.** An elliptic curve `W` over `k` with `‖c₄‖ = 1`, `‖Δ‖ < 1` whose
tangent quadratic at the node has a root modulo the maximal ideal is, after a change of
variables, the Tate curve `E_q` of a Tate parameter `q` (with `j(E_q) = j(W)`). -/
theorem exists_variableChange_tateCurve (h2 : ‖(2 : k)‖ = 1) (h12 : (12 : k) ≠ 0)
    (W : WeierstrassCurve k) [W.IsElliptic] (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1)
    (hroot : ∃ r : k, ‖W.c₄ * r ^ 2 + W.a₁ * W.c₄ * r
      - (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)‖ < 1) :
    ∃ (t : TateParameter k) (C : VariableChange k), C • W = t.tateCurve ∧ t.tateJ = W.j := by
  have hsqrt : ∀ a x₀ : k, ‖x₀‖ = 1 → ‖x₀ ^ 2 - a‖ < 1 → ∃ x, x ^ 2 = a := fun a x₀ hx h =>
    (exists_sq_eq_of_norm_sq_sub_lt h2 hx h).imp fun x hx => hx.1
  have h12ne : (12 : k) ≠ 0 := h12
  have h2ne : (2 : k) ≠ 0 := by
    intro h
    apply h12ne
    rw [show (12 : k) = 2 * 6 by norm_num, h, zero_mul]
  have h3ne : (3 : k) ≠ 0 := by
    intro h
    apply h12ne
    rw [show (12 : k) = 3 * 4 by norm_num, h, zero_mul]
  have hΔ0 : W.Δ ≠ 0 := by rw [← coe_Δ']; exact W.Δ'.ne_zero
  have hΔpos : 0 < ‖W.Δ‖ := norm_pos_iff.mpr hΔ0
  -- `‖j(W)‖ > 1`
  have hj : 1 < ‖W.j‖ := by
    have : W.j = W.Δ⁻¹ * W.c₄ ^ 3 := by
      rw [j, Units.val_inv_eq_inv_val, coe_Δ']
    rw [this, norm_mul, norm_inv, norm_pow, hc₄, one_pow, mul_one]
    exact (one_lt_inv₀ hΔpos).mpr hΔ
  obtain ⟨t, ht⟩ := TateParameter.exists_tateParameter_tateJ_eq h12 hj
  haveI hE' : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
  have hjE' : t.tateCurve.j = W.j := by
    rw [← ht]
    exact (t.tateJ_eq_j h12).symm
  letI := invertibleOfNonzero h2ne
  letI := invertibleOfNonzero h3ne
  obtain ⟨C₁, hC₁⟩ := W.exists_variableChange_isShortNF
  obtain ⟨C₂, hC₂⟩ := t.tateCurve.exists_variableChange_isShortNF
  have hj₁ : 1 < ‖(C₁ • W).j‖ := by rw [variableChange_j]; exact hj
  have hj₁₂ : (C₁ • W).j = (C₂ • t.tateCurve).j := by
    rw [variableChange_j, variableChange_j, hjE']
  -- the ratio `a'b/(ab')` of the normal forms is a square
  have hsq : IsSquare (((C₂ • t.tateCurve).a₄ * (C₁ • W).a₆) /
      ((C₁ • W).a₄ * (C₂ • t.tateCurve).a₆)) := by
    obtain ⟨m, hm⟩ := isSquare_ratio h12ne hsqrt W hc₄ hΔ hroot t
    have hc₄' : t.tateCurve.c₄ ≠ 0 := by
      intro h
      have := t.norm_c₄_eq_one
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hc₆' : t.tateCurve.c₆ ≠ 0 := by
      intro h
      have := norm_c₆_eq_one t.tateCurve t.norm_c₄_eq_one
        (t.norm_Δ_lt_one h12ne)
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hc₄0 : W.c₄ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hc₄
      exact zero_ne_one hc₄
    have hc₆0 : W.c₆ ≠ 0 := by
      intro h
      have := norm_c₆_eq_one W hc₄ hΔ
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have h48 : (48 : k) ≠ 0 := by
      have : (48 : k) = 2 ^ 4 * 3 := by norm_num
      rw [this]
      exact mul_ne_zero (pow_ne_zero _ h2ne) h3ne
    have h864 : (864 : k) ≠ 0 := by
      have : (864 : k) = 2 ^ 5 * 3 ^ 3 := by norm_num
      rw [this]
      exact mul_ne_zero (pow_ne_zero _ h2ne) (pow_ne_zero _ h3ne)
    have e₁ : (C₁ • W).a₄ = -(C₁ • W).c₄ / 48 := by
      rw [c₄_of_isShortNF]
      field_simp
    have e₂ : (C₁ • W).a₆ = -(C₁ • W).c₆ / 864 := by
      rw [c₆_of_isShortNF]
      field_simp
    have e₃ : (C₂ • t.tateCurve).a₄ = -(C₂ • t.tateCurve).c₄ / 48 := by
      rw [c₄_of_isShortNF]
      field_simp
    have e₄ : (C₂ • t.tateCurve).a₆ = -(C₂ • t.tateCurve).c₆ / 864 := by
      rw [c₆_of_isShortNF]
      field_simp
    refine ⟨(C₂.u : k) * t.tateCurve.c₄ * m / ((C₁.u : k) * W.c₄), ?_⟩
    rw [e₁, e₂, e₃, e₄, variableChange_c₄, variableChange_c₆, variableChange_c₄,
      variableChange_c₆, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
    have hu₁ := C₁.u.ne_zero
    have hu₂ := C₂.u.ne_zero
    rw [div_eq_iff (mul_ne_zero hc₄' hc₆')] at hm
    field_simp
    linear_combination hm
  haveI := hC₁
  haveI := hC₂
  obtain ⟨u, hu⟩ := exists_scaleChange_of_j_eq (C₁ • W) (C₂ • t.tateCurve) h2ne h3ne hj₁ hj₁₂ hsq
  refine ⟨t, C₂⁻¹ * (scaleChange u * C₁), ?_, ht⟩
  rw [mul_smul, mul_smul, hu, inv_smul_smul]

end Main

end

end Iut
