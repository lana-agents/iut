/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.IntegralTorsion
import Iut.Tower.TorsionRigid

/-!
# An involution in the inertia group fixes the odd torsion of a stable model

Let `W` be a Weierstrass curve over a field `K` with a valuation `v`, with `v`-integral
coefficients, and `σ : K →+* K` an involution (`σ ∘ σ = id`) satisfying the inertia condition
`v(σ z − z) < 1` for all `v`-integral `z`, fixing the coefficients of `W`, acting on the points
of `W` coordinatewise through `φ : W(K) →+ W(K)`. Let `n` be odd with `v(n) = 1`. Assume

* either `v(a₁) = 1` and `v(2) < 1` (**a multiplicative model at residue characteristic `2`**:
  `v(c₄) = 1` forces `v(a₁) = 1`, `Iut.InertiaInvolution.valuation_a₁_eq_one_of_c₄`),
* or `v(Δ) = 1` (**a good model**, any residue characteristic).

Then `φ` fixes every `n`-torsion point (`Iut.InertiaInvolution.map_eq_self`). Indeed, if
`φ Q = −Q` for an `n`-torsion point `Q = (x, y)`, then `Q` is integral
(`Iut.IntegralTorsion.valuation_le_one_of_nsmul_eq_zero`), `σ x = x`, `σ y = −y − a₁x − a₃`,
and the tangent slope `λ = N/D` at `Q` (`N = 3x² + 2a₂x + a₄ − a₁y`, `D = 2y + a₁x + a₃`)
satisfies `σ λ = −λ − a₁`. Now `v(λ) > 1`:

* in the multiplicative case, `λ` integral would give `v(σ λ − λ) = v(2λ + a₁) = v(a₁) = 1`,
  contradicting the inertia condition;
* in the good case, `v(D) = v(y − σ y) < 1` and the reduction of `Q` is a nonsingular point of
  the reduced curve (`Iut.InertiaInvolution.nonsingular_reduction`, from Mathlib's
  `WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero` over the residue field of
  the valuation ring), so `v(N) = 1` and `v(λ) = 1/v(D) > 1`.

Hence `x(2Q) = λ² + a₁λ − a₂ − 2x` has `v(x(2Q)) = v(λ)² > 1`: `2Q` is a nonzero `n`-torsion
point of the kernel of reduction, which is impossible
(`Iut.IntegralTorsion.nsmul_ne_zero_of_one_lt`). For a general `n`-torsion point `Q`,
`φ Q − Q` is `n`-torsion with `φ(φ Q − Q) = −(φ Q − Q)`, so `φ Q = Q`.

This is the residue-characteristic-`2` replacement of the Tate uniformization: it shows that
the inertia group of a place of residue characteristic `2` of the torsion field `F(E[ℓ])` has
odd order (no element of order `2` acts nontrivially on `E[ℓ]`), i.e. `2 ∤ e(v/w)`.
-/

namespace Iut.InertiaInvolution

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

/-! ### Nonsingular reduction at a good model -/

/-- **Nonsingular reduction at a good model**: for an integral point `(x, y)` of an integral
model with `v(Δ) = 1`, one of the partial derivatives `3x² + 2a₂x + a₄ − a₁y`,
`2y + a₁x + a₃` is a unit (the reduction of `(x, y)` is a nonsingular point of the reduced
curve, which is an elliptic curve over the residue field). -/
theorem nonsingular_reduction {W : Affine K} (hW : IsIntegralModel v W) (hΔ : v W.Δ = 1)
    {x y : K} (h : W.Equation x y) (hx : v x ≤ 1) (hy : v y ≤ 1) :
    v (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) = 1 ∨ v (2 * y + W.a₁ * x + W.a₃) = 1 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  set A := v.valuationSubring
  let W₀ : WeierstrassCurve A := ⟨⟨W.a₁, h₁⟩, ⟨W.a₂, h₂⟩, ⟨W.a₃, h₃⟩, ⟨W.a₄, h₄⟩, ⟨W.a₆, h₆⟩⟩
  let x₀ : A := ⟨x, hx⟩
  let y₀ : A := ⟨y, hy⟩
  set res := IsLocalRing.residue A
  -- the equation over `A` and over the residue field
  have hEq₀ : y₀ ^ 2 + W₀.a₁ * x₀ * y₀ + W₀.a₃ * y₀ =
      x₀ ^ 3 + W₀.a₂ * x₀ ^ 2 + W₀.a₄ * x₀ + W₀.a₆ := by
    apply Subtype.ext
    push_cast
    exact (equation_iff _ _).mp h
  have hEq : (W₀.map res).toAffine.Equation (res x₀) (res y₀) := by
    rw [equation_iff]
    have := congrArg res hEq₀
    simpa only [map_add, map_mul, map_pow, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] using this
  -- the discriminant of the reduction is nonzero
  have hΔ₀ : (W₀.Δ : K) = W.Δ := by
    have : W₀.map A.subtype = W := by ext <;> rfl
    rw [← this, map_Δ]
    rfl
  have hΔres : (W₀.map res).Δ ≠ 0 := by
    rw [map_Δ, Ne, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff, hΔ₀, hΔ]
    exact lt_irrefl 1
  have hns := (nonsingular_iff' _ _).mp ((equation_iff_nonsingular_of_Δ_ne_zero hΔres).mp hEq)
  -- an element of `A` whose residue is nonzero is a unit
  have key : ∀ z : A, res z ≠ 0 → v z = 1 := fun z hz => by
    rw [Ne, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff, not_lt] at hz
    exact le_antisymm z.2 hz
  rcases hns.2 with hX | hY
  · left
    have e : (W₀.map res).a₁ * res y₀ -
        (3 * res x₀ ^ 2 + 2 * (W₀.map res).a₂ * res x₀ + (W₀.map res).a₄) =
        res (W₀.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W₀.a₂ * x₀ + W₀.a₄)) := by
      simp only [map_a₁, map_a₂, map_a₄, map_sub, map_add, map_mul, map_pow, map_ofNat]
    rw [e] at hX
    have := key _ hX
    have e2 : ((W₀.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W₀.a₂ * x₀ + W₀.a₄) : A) : K) =
        W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) := by
      push_cast
      rfl
    rw [e2] at this
    rw [Valuation.map_sub_swap]
    exact this
  · right
    have e : 2 * res y₀ + (W₀.map res).a₁ * res x₀ + (W₀.map res).a₃ =
        res (2 * y₀ + W₀.a₁ * x₀ + W₀.a₃) := by
      simp only [map_a₁, map_a₃, map_add, map_mul, map_ofNat]
    rw [e] at hY
    have := key _ hY
    have e2 : ((2 * y₀ + W₀.a₁ * x₀ + W₀.a₃ : A) : K) = 2 * y + W.a₁ * x + W.a₃ := by
      push_cast
      rfl
    rw [e2] at this
    exact this

/-! ### A multiplicative model at residue characteristic `2` has a unit `a₁` -/

/-- **`v(a₁) = 1` for a multiplicative model at residue characteristic `2`**: from
`c₄ = b₂² − 24b₄` and `b₂ = a₁² + 4a₂`. -/
theorem valuation_a₁_eq_one_of_c₄ {W : Affine K} (hW : IsIntegralModel v W) (hc₄ : v W.c₄ = 1)
    (h2 : v 2 < 1) : v W.a₁ = 1 := by
  have hb₄ := hW.b₄
  have h24 : v (24 * W.b₄) < 1 := by
    have e : (24 : K) = 2 * 12 := by norm_num
    rw [map_mul, e, map_mul]
    calc v 2 * v 12 * v W.b₄ ≤ v 2 * 1 * 1 :=
          mul_le_mul' (mul_le_mul' le_rfl (valuation_ofNat_le_one v 12)) hb₄
      _ < 1 := by rw [mul_one, mul_one]; exact h2
  have hb₂ : v (W.b₂ ^ 2) = 1 := by
    have e : W.b₂ ^ 2 = W.c₄ + 24 * W.b₄ := by rw [c₄]; ring
    rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [hc₄]; exact h24), hc₄]
  have hb₂' : v W.b₂ = 1 := valuation_eq_one_of_sq v hb₂
  have h4 : v (4 * W.a₂) < 1 := by
    have e : (4 : K) = 2 * 2 := by norm_num
    rw [map_mul, e, map_mul]
    calc v 2 * v 2 * v W.a₂ ≤ v 2 * 1 * 1 := mul_le_mul' (mul_le_mul' le_rfl h2.le) hW.2.1
      _ < 1 := by rw [mul_one, mul_one]; exact h2
  have ha₁ : v (W.a₁ ^ 2) = 1 := by
    have e : W.a₁ ^ 2 = W.b₂ - 4 * W.a₂ := by rw [b₂]; ring
    rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hb₂']; exact h4), hb₂']
  exact valuation_eq_one_of_sq v ha₁

/-! ### The involution argument -/

section Involution

variable [NeZero (2 : K)] [DecidableEq K] {W : Affine K} (hW : IsIntegralModel v W)
  (σ : K →+* K) (hσσ : ∀ z, σ (σ z) = z) (hσ : ∀ z, v z ≤ 1 → v (σ z - z) < 1)
  (hσ₁ : σ W.a₁ = W.a₁) (hσ₂ : σ W.a₂ = W.a₂) (hσ₃ : σ W.a₃ = W.a₃) (hσ₄ : σ W.a₄ = W.a₄)
  (hcase : (v W.a₁ = 1 ∧ v 2 < 1) ∨ v W.Δ = 1)
  {n : ℕ} (hodd : Odd n) (hn : v (n : K) = 1)
  (φ : W.Point →+ W.Point)
  (hφ : ∀ (x y : K) (h : W.Nonsingular x y),
    ∃ h' : W.Nonsingular (σ x) (σ y), φ (Point.some x y h) = Point.some (σ x) (σ y) h')

omit [NeZero (2 : K)] in
include hσσ hφ in
/-- `φ` is an involution on the points. -/
lemma map_map_eq_self (Q : W.Point) : φ (φ Q) = Q := by
  cases Q with
  | zero =>
    change φ (φ 0) = 0
    rw [map_zero, map_zero]
  | some x y h =>
    obtain ⟨h', hφ'⟩ := hφ x y h
    obtain ⟨h'', hφ''⟩ := hφ (σ x) (σ y) h'
    rw [hφ', hφ'']
    exact Anabelian.some_ext (hσσ x) (hσσ y)

include hW hσ hσ₁ hσ₂ hσ₃ hσ₄ hcase hodd hn hφ in
/-- **An `n`-torsion point with `φ Q = −Q` is zero.** -/
theorem eq_zero_of_map_eq_neg (Q : W.Point) (hQ : n • Q = 0) (hneg : φ Q = -Q) : Q = 0 := by
  cases Q with
  | zero => rfl
  | some x y h =>
    exfalso
    obtain ⟨h', hφ'⟩ := hφ x y h
    rw [hφ', Point.neg_some] at hneg
    obtain ⟨hσx, hσy⟩ := Point.some.inj hneg
    -- `Q` is integral
    obtain ⟨hx, hy⟩ := IntegralTorsion.valuation_le_one_of_nsmul_eq_zero v hW hodd hn h hQ
    -- `Q` is not `2`-torsion
    have hy2 : y ≠ W.negY x y := by
      intro hy2
      have h2Q : 2 • Point.some x y h = 0 := by
        rw [two_nsmul]
        exact Point.add_of_Y_eq rfl hy2
      obtain ⟨k, hk⟩ := hodd
      have : Point.some x y h = 0 := by
        have e : Point.some x y h = n • Point.some x y h - k • (2 • Point.some x y h) := by
          rw [hk, add_nsmul, one_nsmul, mul_nsmul, add_sub_cancel_left]
        rw [e, hQ, h2Q, smul_zero, sub_zero]
      exact Point.some_ne_zero h this
    -- the tangent slope `λ = N/D`
    set D := 2 * y + W.a₁ * x + W.a₃ with hD_def
    set N := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y with hN_def
    have hD : y - W.negY x y = D := by rw [negY, hD_def]; ring
    have hD0 : D ≠ 0 := by rw [← hD]; exact sub_ne_zero.mpr hy2
    set L := W.slope x x y y with hL_def
    have hL : L = N / D := by rw [hL_def, slope_of_Y_ne rfl hy2, hD]
    -- the key estimate `v(λ) > 1`
    have hLv : 1 < v L := by
      rcases hcase with ⟨ha₁, h2⟩ | hΔ
      · by_contra hle
        rw [not_lt] at hle
        have hσN : σ N = N + W.a₁ * D := by
          rw [hN_def, hD_def]
          simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, hσx, hσy, hσ₁, hσ₂, hσ₄, negY]
          ring
        have hσD : σ D = -D := by
          rw [hD_def]
          simp only [map_add, map_mul, map_ofNat, hσx, hσy, hσ₁, hσ₃, negY]
          ring
        have hσL : σ L - L = -(2 * L + W.a₁) := by
          rw [hL, map_div₀, hσN, hσD, div_neg, add_div, mul_div_cancel_right₀ _ hD0]
          ring
        have h1 := hσ L hle
        rw [hσL, Valuation.map_neg, Valuation.map_add_eq_of_lt_right _ ?_, ha₁] at h1
        · exact lt_irrefl _ h1
        · rw [ha₁, map_mul]
          calc v 2 * v L ≤ v 2 * 1 := mul_le_mul' le_rfl hle
            _ < 1 := by rw [mul_one]; exact h2
      · have hDv : v D < 1 := by
          have := hσ y hy
          rw [hσy, Valuation.map_sub_swap, hD] at this
          exact this
        rcases nonsingular_reduction v hW hΔ h.1 hx hy with hN | hD1
        · rw [hL, map_div₀, hN, one_div]
          exact (one_lt_inv₀ (lt_of_le_of_ne zero_le
            (Ne.symm ((Valuation.ne_zero_iff _).mpr hD0)))).mpr hDv
        · exact absurd hD1 hDv.ne
    -- `2Q` lies in the kernel of reduction
    have h2Q : 2 • Point.some x y h = Point.some (W.addX x x L) (W.addY x x y L)
        (nonsingular_add h h fun hxy => hy2 hxy.2) := by
      rw [two_nsmul]
      exact Point.add_self_of_Y_ne hy2
    have hx2 : 1 < v (W.addX x x L) := by
      have e : W.addX x x L = L ^ 2 + (W.a₁ * L - W.a₂ - x - x) := by rw [addX]; ring
      have hL2 : 1 < v (L ^ 2) := by rw [map_pow]; exact one_lt_pow₀ hLv two_ne_zero
      have hLL : v L < v (L ^ 2) := by
        rw [sq, map_mul]
        calc v L = 1 * v L := (one_mul _).symm
          _ < v L * v L := mul_lt_mul_of_pos_right hLv (zero_lt_one.trans hLv)
      have hrest : v (W.a₁ * L - W.a₂ - x - x) < v (L ^ 2) := by
        refine (Valuation.map_sub _ _ _).trans_lt (max_lt ((Valuation.map_sub _ _ _).trans_lt
          (max_lt ((Valuation.map_sub _ _ _).trans_lt (max_lt ?_ ?_)) ?_)) ?_)
        · rw [map_mul]
          calc v W.a₁ * v L ≤ 1 * v L := mul_le_mul' hW.1 le_rfl
            _ = v L := one_mul _
            _ < v (L ^ 2) := hLL
        · exact hW.2.1.trans_lt hL2
        · exact hx.trans_lt hL2
        · exact hx.trans_lt hL2
      rw [e, Valuation.map_add_eq_of_lt_left _ hrest]
      exact hL2
    have hn2 : n • (2 • Point.some x y h) = 0 := by rw [smul_comm, hQ, smul_zero]
    rw [h2Q] at hn2
    exact IntegralTorsion.nsmul_ne_zero_of_one_lt v hW hodd hn _ hx2 hn2

include hW hσσ hσ hσ₁ hσ₂ hσ₃ hσ₄ hcase hodd hn hφ in
/-- **An involution in the inertia group fixes the `n`-torsion** of a stable model
(`v(a₁) = 1 ∧ v(2) < 1`, or `v(Δ) = 1`). -/
theorem map_eq_self (Q : W.Point) (hQ : n • Q = 0) : φ Q = Q := by
  have h1 : n • (φ Q - Q) = 0 := by rw [nsmul_sub, ← map_nsmul, hQ, map_zero, sub_zero]
  have h2 : φ (φ Q - Q) = -(φ Q - Q) := by
    rw [map_sub, map_map_eq_self σ hσσ φ hφ, neg_sub]
  exact sub_eq_zero.mp (eq_zero_of_map_eq_neg v hW σ hσ hσ₁ hσ₂ hσ₃ hσ₄ hcase hodd hn φ hφ _ h1 h2)

end Involution

end Iut.InertiaInvolution
