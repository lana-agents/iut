/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Torsion.EDS
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Logic.Embedding.Set
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The `n`-torsion of an elliptic curve over an algebraically closed field of characteristic `0`

Let `W : y² = x³ + a₂x² + a₄x + a₆` be a Weierstrass curve with `a₁ = a₃ = 0` over a field `K`
of characteristic `0`. From the description of the multiples of a point by the division
polynomials (`Iut.Torsion.good`) we obtain:

* `Iut.Torsion.torsion_finite`: the `n`-torsion `E[n] = {P | n • P = 0}` is finite, for `n ≠ 0`
  (its affine points have `x`-coordinate a root of the polynomial `ΨSqₙ ≠ 0`);
* `Iut.Torsion.card_torsionBy_eq_sq`: if `K` is algebraically closed and `W` is an elliptic
  curve, then `|E[n]| = n²`. The proof counts the fibres of the multiplication by `n`: for a
  point `Q = (x₀, y₀)` with `y₀ ≠ 0`, the points `P` with `nP = ±Q` are the affine points
  whose `x`-coordinate is a root of `hₓ₀ := Φₙ − x₀ ΨSqₙ`, a polynomial of degree `n²`, two
  points for each root; for `x₀` outside a finite set the roots are simple, so there are
  `2n²` such points, while they form two cosets of `E[n]`;
* `Iut.Torsion.torsionBasis`: for a prime `ℓ`, `E[ℓ] ≃+ (ℤ/ℓ)²`, since `E[ℓ]` is an
  `𝔽_ℓ`-vector space with `ℓ²` elements.
-/

namespace Iut.Torsion

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {W : Affine K} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)

/-! ### The sequence `eₙ` and the univariate division polynomials -/

section univariate

include ha₁ ha₃

/-- `Ψ₂Sq(x) = 4 f(x)` for `a₁ = a₃ = 0`. -/
theorem Ψ₂Sq_eval (x : K) :
    W.Ψ₂Sq.eval x = 4 * (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  simp only [Ψ₂Sq, b₂, b₄, b₆, ha₁, ha₃, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

variable {x y : K} (h : W.Nonsingular x y)
include h

/-- `Ψ₂Sq(x) = (2y)²` at a point of the curve. -/
theorem Ψ₂Sq_eval_eq : W.Ψ₂Sq.eval x = (2 * y) ^ 2 := by
  rw [Ψ₂Sq_eval ha₁ ha₃, ← hQ_of ha₁ ha₃ h]; ring

/-- `preΨₙ(x)` is the auxiliary sequence of `eₙ`. -/
theorem preΨ_eval (n : ℤ) :
    (W.preΨ n).eval x = preNormEDS ((2 * y) ^ 4) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n := by
  rw [preΨ, ← coe_evalRingHom, map_preNormEDS, coe_evalRingHom, eval_pow, Ψ₂Sq_eval_eq ha₁ ha₃ h,
    ← pow_mul]

/-- `eₙ² = ΨSqₙ(x)`. -/
theorem eds_sq_eq (n : ℤ) : eds W x y n ^ 2 = (W.ΨSq n).eval x := by
  rw [eds, normEDS, ΨSq, eval_mul, eval_pow, preΨ_eval ha₁ ha₃ h, mul_pow, ite_pow, one_pow,
    apply_ite (eval x), eval_one, Ψ₂Sq_eval_eq ha₁ ha₃ h]

/-- `eₙ₊₁ eₙ₋₁ = preΨₙ₊₁(x) preΨₙ₋₁(x) · (Ψ₂Sq(x) if `n` is odd)`. -/
theorem eds_succ_mul_pred (n : ℤ) : eds W x y (n + 1) * eds W x y (n - 1) =
    (W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq).eval x := by
  simp only [eds, normEDS, eval_mul, preΨ_eval ha₁ ha₃ h, apply_ite (eval x), eval_one,
    Ψ₂Sq_eval_eq ha₁ ha₃ h, Int.even_add_one, Int.even_sub_one]
  split_ifs <;> ring

/-- `Φₙ(x) = x ΨSqₙ(x) − eₙ₊₁ eₙ₋₁`. -/
theorem Φ_eval (n : ℤ) :
    (W.Φ n).eval x = x * (W.ΨSq n).eval x - eds W x y (n + 1) * eds W x y (n - 1) := by
  rw [WeierstrassCurve.Φ, eval_sub, eval_mul, eval_X, eds_succ_mul_pred ha₁ ha₃ h]

/-- `n • P = 0 ↔ ΨSqₙ(x) = 0` for an affine point `P = (x, y)`. -/
theorem smul_eq_zero_iff_ΨSq (n : ℕ) :
    n • Point.some x y h = 0 ↔ (W.ΨSq n).eval x = 0 := by
  rw [smul_eq_zero_iff_eds ha₁ ha₃ h, ← eds_sq_eq ha₁ ha₃ h, pow_eq_zero_iff two_ne_zero]

/-- If `ΨSqₙ(x) ≠ 0`, then `n • P = (X, Y)` is affine with `X ΨSqₙ(x) = Φₙ(x)`. -/
theorem smul_eq_of_ΨSq_ne_zero (n : ℕ) (hne : (W.ΨSq n).eval x ≠ 0) :
    ∃ (X Y : K) (hXY : W.Nonsingular X Y), n • Point.some x y h = Point.some X Y hXY ∧
      X * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  have he : eds W x y n ≠ 0 := by
    intro h0; apply hne; rw [← eds_sq_eq ha₁ ha₃ h, h0]; ring
  obtain ⟨X, Y, hXY, hn, hX, -⟩ := (good ha₁ ha₃ h n).2 he
  refine ⟨X, Y, hXY, hn, ?_⟩
  rw [Φ_eval ha₁ ha₃ h, ← eds_sq_eq ha₁ ha₃ h, hX]

end univariate

/-! ### Finiteness of the torsion -/

section finite

include ha₁ ha₃

/-- The `n`-torsion of `W(K)` is finite for `n ≠ 0`. -/
theorem torsion_finite (n : ℕ) (hn : n ≠ 0) : {P : W.Point | n • P = 0}.Finite := by
  have hΨ : W.ΨSq n ≠ 0 := ΨSq_ne_zero W (by exact_mod_cast hn)
  -- the finite set of candidate coordinates
  let T : Set (K × K) := ⋃ r ∈ {r | (W.ΨSq n).IsRoot r},
    (fun s => (r, s)) '' {s | s ^ 2 = r ^ 3 + W.a₂ * r ^ 2 + W.a₄ * r + W.a₆}
  have hT : T.Finite := by
    refine (finite_setOf_isRoot hΨ).biUnion fun r _ => Set.Finite.image _ ?_
    have : {s | s ^ 2 = r ^ 3 + W.a₂ * r ^ 2 + W.a₄ * r + W.a₆} =
        {s | (X ^ 2 - C (r ^ 3 + W.a₂ * r ^ 2 + W.a₄ * r + W.a₆)).IsRoot s} := by
      ext s; simp [sub_eq_zero]
    rw [this]
    refine finite_setOf_isRoot ?_
    intro h0
    have := congrArg natDegree h0
    rw [natDegree_sub_C, natDegree_X_pow, natDegree_zero] at this
    exact two_ne_zero this
  let g : K × K → W.Point := fun p =>
    if hp : W.Nonsingular p.1 p.2 then Point.some p.1 p.2 hp else 0
  refine ((hT.image g).insert 0).subset ?_
  intro P hP
  simp only [Set.mem_setOf_eq] at hP
  rcases P with _ | ⟨x, y, hxy⟩
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ⟨(x, y), ?_, ?_⟩
    · refine Set.mem_iUnion₂.mpr ⟨x, ?_, y, ?_, rfl⟩
      · exact (smul_eq_zero_iff_ΨSq ha₁ ha₃ hxy n).mp hP
      · exact hQ_of ha₁ ha₃ hxy
    · simp only [g, dif_pos hxy]

end finite

/-! ### The fibres of the multiplication by `n` -/

section count

variable [IsAlgClosed K] [W.IsElliptic]
include ha₁ ha₃

/-- Every `x₁` is the `x`-coordinate of a point of `W`. -/
theorem exists_point (x₁ : K) : ∃ y₁, W.Nonsingular x₁ y₁ := by
  obtain ⟨y₁, hy₁⟩ := IsAlgClosed.exists_pow_nat_eq (x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆)
    two_pos
  exact ⟨y₁, equation_iff_nonsingular.mp ((equation_iff₀ ha₁ ha₃ x₁ y₁).mpr hy₁)⟩

/-- The polynomial `hₓ₀ = Φₙ − x₀ ΨSqₙ` whose roots are the `x`-coordinates of the points `P`
with `x(nP) = x₀`. -/
noncomputable def fibrePoly (W : Affine K) (n : ℕ) (x₀ : K) : K[X] :=
  W.Φ n - C x₀ * W.ΨSq n

omit ha₁ ha₃ in
theorem natDegree_fibrePoly (n : ℕ) (hn : n ≠ 0) (x₀ : K) :
    (fibrePoly W n x₀).natDegree = n ^ 2 := by
  have hn' : ((n : ℤ) : K) ≠ 0 := by exact_mod_cast hn
  rw [fibrePoly, natDegree_sub_eq_left_of_natDegree_lt, natDegree_Φ, Int.natAbs_natCast]
  rw [natDegree_Φ, Int.natAbs_natCast]
  refine (natDegree_C_mul_le _ _).trans_lt ?_
  rw [W.natDegree_ΨSq hn', Int.natAbs_natCast]
  have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn)
  omega

omit ha₁ ha₃ in
theorem fibrePoly_ne_zero (n : ℕ) (hn : n ≠ 0) (x₀ : K) : fibrePoly W n x₀ ≠ 0 := by
  intro h0
  have := natDegree_fibrePoly (W := W) n hn x₀
  rw [h0, natDegree_zero] at this
  exact hn (pow_eq_zero_iff two_ne_zero |>.mp this.symm)

omit ha₁ ha₃ in
theorem eval_fibrePoly (n : ℕ) (x₀ x₁ : K) :
    (fibrePoly W n x₀).eval x₁ = (W.Φ n).eval x₁ - x₀ * (W.ΨSq n).eval x₁ := by
  rw [fibrePoly, eval_sub, eval_mul, eval_C]

/-- `Φₙ` and `ΨSqₙ` have no common root: a common root `x₁` would give a point `P` with
`nP = 0` and `(n+1)P = 0` or `(n−1)P = 0`. -/
theorem ΨSq_ne_zero_of_Φ_eq_zero (n : ℕ) (hn : n ≠ 0) {x₁ : K} (hΦ : (W.Φ n).eval x₁ = 0) :
    (W.ΨSq n).eval x₁ ≠ 0 := by
  intro hΨ
  obtain ⟨y₁, h₁⟩ := exists_point ha₁ ha₃ x₁
  have hnP : n • Point.some x₁ y₁ h₁ = 0 := (smul_eq_zero_iff_ΨSq ha₁ ha₃ h₁ n).mpr hΨ
  rw [Φ_eval ha₁ ha₃ h₁, hΨ, mul_zero, zero_sub, neg_eq_zero, mul_eq_zero] at hΦ
  rcases hΦ with h0 | h0
  · have : (n + 1) • Point.some x₁ y₁ h₁ = 0 :=
      (smul_eq_zero_iff_eds ha₁ ha₃ h₁ (n + 1)).mpr (by push_cast; exact h0)
    rw [succ_nsmul, hnP, zero_add] at this
    exact Point.some_ne_zero h₁ this
  · have : (n - 1) • Point.some x₁ y₁ h₁ = 0 :=
      (smul_eq_zero_iff_eds ha₁ ha₃ h₁ (n - 1)).mpr
        (by push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn)]; exact h0)
    rw [smul_pred h₁ (Nat.one_le_iff_ne_zero.mpr hn), hnP, zero_sub, neg_eq_zero] at this
    exact Point.some_ne_zero h₁ this

/-- A root of `hₓ₀` is not a root of `ΨSqₙ`. -/
theorem ΨSq_ne_zero_of_root (n : ℕ) (hn : n ≠ 0) {x₀ x₁ : K}
    (hr : (fibrePoly W n x₀).IsRoot x₁) : (W.ΨSq n).eval x₁ ≠ 0 := by
  intro hΨ
  refine ΨSq_ne_zero_of_Φ_eq_zero ha₁ ha₃ n hn ?_ hΨ
  rw [IsRoot, eval_fibrePoly, hΨ] at hr
  linear_combination hr

/-- The points `P` with `nP = ±Q`, for `Q = (x₀, y₀)` with `y₀ ≠ 0`, are the affine points whose
`x`-coordinate is a root of `hₓ₀`. -/
theorem smul_eq_or_neg_iff (n : ℕ) (hn : n ≠ 0) {x₀ y₀ : K} (hQ : W.Nonsingular x₀ y₀)
    (hy₀ : y₀ ≠ 0) (P : W.Point) :
    (n • P = Point.some x₀ y₀ hQ ∨ n • P = -Point.some x₀ y₀ hQ) ↔
      ∃ (x₁ y₁ : K) (h₁ : W.Nonsingular x₁ y₁), P = Point.some x₁ y₁ h₁ ∧
        (fibrePoly W n x₀).IsRoot x₁ := by
  constructor
  · intro hP
    rcases P with _ | ⟨x₁, y₁, h₁⟩
    · exfalso
      rw [← Point.zero_def, smul_zero] at hP
      rcases hP with hP | hP
      · exact Point.some_ne_zero hQ hP.symm
      · rw [Point.neg_some] at hP
        exact Point.some_ne_zero _ hP.symm
    · have hne : (W.ΨSq n).eval x₁ ≠ 0 := by
        intro h0
        have := (smul_eq_zero_iff_ΨSq ha₁ ha₃ h₁ n).mpr h0
        rw [this] at hP
        rcases hP with hP | hP
        · exact Point.some_ne_zero hQ hP.symm
        · rw [Point.neg_some] at hP
          exact Point.some_ne_zero _ hP.symm
      obtain ⟨X, Y, hXY, hnP, hX⟩ := smul_eq_of_ΨSq_ne_zero ha₁ ha₃ h₁ n hne
      have hXx : X = x₀ := by
        rw [hnP] at hP
        rcases hP with hP | hP
        · exact (Point.some.inj hP).1
        · rw [Point.neg_some] at hP
          exact (Point.some.inj hP).1
      refine ⟨x₁, y₁, h₁, rfl, ?_⟩
      rw [IsRoot, eval_fibrePoly, ← hX, hXx]; ring
  · rintro ⟨x₁, y₁, h₁, rfl, hr⟩
    have hne := ΨSq_ne_zero_of_root ha₁ ha₃ n hn hr
    obtain ⟨X, Y, hXY, hnP, hX⟩ := smul_eq_of_ΨSq_ne_zero ha₁ ha₃ h₁ n hne
    have hXx : X = x₀ := by
      rw [IsRoot, eval_fibrePoly, ← hX] at hr
      have : (X - x₀) * (W.ΨSq n).eval x₁ = 0 := by linear_combination hr
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
    rw [hnP]
    exact (Point.X_eq_iff (h₁ := hXY) (h₂ := hQ)).mp hXx

/-- The `y`-coordinate of a point `P` with `nP = ±Q` is nonzero. -/
theorem y_ne_zero_of_smul_eq (n : ℕ) {x₀ y₀ : K} (hQ : W.Nonsingular x₀ y₀)
    (hy₀ : y₀ ≠ 0) {x₁ y₁ : K} (h₁ : W.Nonsingular x₁ y₁)
    (hP : n • Point.some x₁ y₁ h₁ = Point.some x₀ y₀ hQ ∨
      n • Point.some x₁ y₁ h₁ = -Point.some x₀ y₀ hQ) : y₁ ≠ 0 := by
  intro hy₁
  have h2P : 2 • Point.some x₁ y₁ h₁ = 0 := by
    rw [two_nsmul, Point.add_self_of_Y_eq]
    rw [negY_eq ha₁ ha₃, hy₁, neg_zero]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [mul_nsmul, h2P, smul_zero] at hP
    rcases hP with hP | hP
    · exact Point.some_ne_zero hQ hP.symm
    · rw [Point.neg_some] at hP
      exact Point.some_ne_zero _ hP.symm
  · rw [succ_nsmul, mul_nsmul, h2P, smul_zero, zero_add] at hP
    rcases hP with hP | hP
    · exact hy₀ ((Point.some.inj hP).2.symm.trans hy₁)
    · rw [Point.neg_some] at hP
      have := (Point.some.inj hP).2
      rw [negY_eq ha₁ ha₃, hy₁] at this
      exact hy₀ (neg_eq_zero.mp this.symm)

omit ha₁ ha₃ in
/-- A nonzero element of an algebraically closed field of characteristic `≠ 2` has exactly two
square roots. -/
theorem card_sq_eq (c : K) (hc : c ≠ 0) : Nat.card {s : K // s ^ 2 = c} = 2 := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq c two_pos
  have ht0 : t ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero] at ht; exact hc ht.symm
  have hset : {s : K | s ^ 2 = c} = {t, -t} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, ← ht,
      sq_eq_sq_iff_eq_or_eq_neg]
  change Nat.card {s : K | s ^ 2 = c} = 2
  rw [Nat.card_coe_set_eq, hset, Set.ncard_pair]
  intro h
  apply ht0
  have : (2 : K) * t = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

/-- The cubic `f(x) = x³ + a₂x² + a₄x + a₆`. -/
noncomputable abbrev cubic (W : Affine K) (t : K) : K := t ^ 3 + W.a₂ * t ^ 2 + W.a₄ * t + W.a₆

/-- The points with `nP = ±Q` are in bijection with the pairs `(x₁, y₁)` with `x₁` a root of
`hₓ₀` and `y₁² = f(x₁)`. -/
theorem card_fibre (n : ℕ) (hn : n ≠ 0) {x₀ y₀ : K} (hQ : W.Nonsingular x₀ y₀)
    (hy₀ : y₀ ≠ 0) :
    Nat.card {P : W.Point // n • P = Point.some x₀ y₀ hQ ∨ n • P = -Point.some x₀ y₀ hQ} =
      2 * (fibrePoly W n x₀).roots.toFinset.card := by
  set R := (fibrePoly W n x₀).roots.toFinset with hR
  have hmem : ∀ r, r ∈ R ↔ (fibrePoly W n x₀).IsRoot r := fun r => by
    rw [hR, Multiset.mem_toFinset, mem_roots (fibrePoly_ne_zero n hn x₀)]
  -- the map from pairs to points
  let φ : (Σ r : R, {s : K // s ^ 2 = cubic W r}) → W.Point := fun p =>
    Point.some p.1.1 p.2.1 (equation_iff_nonsingular.mp ((equation_iff₀ ha₁ ha₃ _ _).mpr p.2.2))
  have hφ : Function.Injective φ := by
    rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ ⟨⟨r', hr'⟩, ⟨s', hs'⟩⟩ heq
    obtain ⟨rfl, rfl⟩ := Point.some.inj heq
    rfl
  have hrange : Set.range φ =
      {P : W.Point | n • P = Point.some x₀ y₀ hQ ∨ n • P = -Point.some x₀ y₀ hQ} := by
    ext P
    rw [Set.mem_setOf_eq, smul_eq_or_neg_iff ha₁ ha₃ n hn hQ hy₀, Set.mem_range]
    constructor
    · rintro ⟨⟨⟨r, hr⟩, ⟨s, hs⟩⟩, rfl⟩
      exact ⟨r, s, _, rfl, (hmem r).mp hr⟩
    · rintro ⟨x₁, y₁, h₁, rfl, hr⟩
      exact ⟨⟨⟨x₁, (hmem x₁).mpr hr⟩, ⟨y₁, hQ_of ha₁ ha₃ h₁⟩⟩, rfl⟩
  have hcard : Nat.card {P : W.Point // n • P = Point.some x₀ y₀ hQ ∨
      n • P = -Point.some x₀ y₀ hQ} = Nat.card (Σ r : R, {s : K // s ^ 2 = cubic W r}) := by
    rw [Nat.card_congr (Equiv.ofInjective φ hφ), hrange]
    rfl
  rw [hcard]
  have hfin : ∀ r : R, Finite {s : K // s ^ 2 = cubic W r} := fun r =>
    Nat.finite_of_card_ne_zero (by
      rw [card_sq_eq]
      · exact two_ne_zero
      · -- `f(r) ≠ 0`: the points over `r` have nonzero `y`-coordinate
        intro h0
        obtain ⟨y₁, h₁⟩ := exists_point ha₁ ha₃ (r : K)
        have hy₁ : y₁ = 0 := by
          have := hQ_of ha₁ ha₃ h₁
          rw [show r.1 ^ 3 + W.a₂ * r.1 ^ 2 + W.a₄ * r.1 + W.a₆ = cubic W r from rfl, h0] at this
          exact pow_eq_zero_iff two_ne_zero |>.mp this
        refine y_ne_zero_of_smul_eq ha₁ ha₃ n hQ hy₀ h₁ ?_ hy₁
        exact (smul_eq_or_neg_iff ha₁ ha₃ n hn hQ hy₀ _).mpr ⟨_, _, h₁, rfl, (hmem r).mp r.2⟩)
  rw [Nat.card_sigma]
  have : ∀ r : R, Nat.card {s : K // s ^ 2 = cubic W r} = 2 := fun r => by
    rw [card_sq_eq]
    intro h0
    obtain ⟨y₁, h₁⟩ := exists_point ha₁ ha₃ (r : K)
    have hy₁ : y₁ = 0 := by
      have := hQ_of ha₁ ha₃ h₁
      rw [show r.1 ^ 3 + W.a₂ * r.1 ^ 2 + W.a₄ * r.1 + W.a₆ = cubic W r from rfl, h0] at this
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    refine y_ne_zero_of_smul_eq ha₁ ha₃ n hQ hy₀ h₁ ?_ hy₁
    exact (smul_eq_or_neg_iff ha₁ ha₃ n hn hQ hy₀ _).mpr ⟨_, _, h₁, rfl, (hmem r).mp r.2⟩
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
  ring

omit ha₁ ha₃ in
/-- A fibre of the multiplication by `n` is in bijection with the `n`-torsion. -/
theorem card_coset (n : ℕ) {Q P₀ : W.Point} (hP₀ : n • P₀ = Q) :
    Nat.card {P : W.Point // n • P = Q} = Nat.card (AddSubgroup.torsionBy W.Point n) := by
  refine Nat.card_congr
    { toFun := fun P => ⟨P.1 - P₀, ?_⟩
      invFun := fun T => ⟨P₀ + T.1, ?_⟩
      left_inv := fun P => Subtype.ext (add_sub_cancel _ _)
      right_inv := fun T => Subtype.ext (add_sub_cancel_left _ _) }
  · rw [AddSubgroup.torsionBy.nsmul_iff, smul_sub, P.2, hP₀, sub_self]
  · rw [smul_add, hP₀, AddSubgroup.torsionBy.nsmul_iff.mp T.2, add_zero]

/-- The number of points with `nP = ±Q` is twice `|E[n]|`. -/
theorem card_fibre_eq_two_mul (n : ℕ) (hn : n ≠ 0) {x₀ y₀ : K} (hQ : W.Nonsingular x₀ y₀)
    (hy₀ : y₀ ≠ 0) [Finite (AddSubgroup.torsionBy W.Point n)] :
    Nat.card {P : W.Point // n • P = Point.some x₀ y₀ hQ ∨ n • P = -Point.some x₀ y₀ hQ} =
      2 * Nat.card (AddSubgroup.torsionBy W.Point n) := by
  -- a point `P₀` with `nP₀ = Q`
  obtain ⟨x₁, hx₁⟩ := IsAlgClosed.exists_root (fibrePoly W n x₀) (by
    rw [degree_eq_natDegree (fibrePoly_ne_zero n hn x₀), natDegree_fibrePoly n hn]
    exact_mod_cast pow_ne_zero 2 hn)
  obtain ⟨y₁, h₁⟩ := exists_point ha₁ ha₃ x₁
  have hmem := (smul_eq_or_neg_iff ha₁ ha₃ n hn hQ hy₀ (Point.some x₁ y₁ h₁)).mpr
    ⟨x₁, y₁, h₁, rfl, hx₁⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : W.Point, n • P₀ = Point.some x₀ y₀ hQ := by
    rcases hmem with h' | h'
    · exact ⟨_, h'⟩
    · exact ⟨-Point.some x₁ y₁ h₁, by rw [smul_neg, h', neg_neg]⟩
  have hdisj : Disjoint (fun P : W.Point => n • P = Point.some x₀ y₀ hQ)
      (fun P => n • P = -Point.some x₀ y₀ hQ) := by
    rw [Pi.disjoint_iff]
    intro P
    rw [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩
    rw [h1, Point.neg_some] at h2
    have := (Point.some.inj h2).2
    rw [negY_eq ha₁ ha₃] at this
    apply hy₀
    have h2y : (2 : K) * y₀ = 0 := by linear_combination this
    exact (mul_eq_zero.mp h2y).resolve_left two_ne_zero
  rw [Nat.card_congr (subtypeOrEquiv _ _ hdisj)]
  have h1 := card_coset (W := W) n hP₀
  have h2 := card_coset (W := W) n (P₀ := -P₀) (Q := -Point.some x₀ y₀ hQ) (by rw [smul_neg, hP₀])
  haveI : Finite {P : W.Point // n • P = Point.some x₀ y₀ hQ} :=
    Nat.finite_of_card_ne_zero (by rw [h1]; exact Nat.card_pos.ne')
  haveI : Finite {P : W.Point // n • P = -Point.some x₀ y₀ hQ} :=
    Nat.finite_of_card_ne_zero (by rw [h2]; exact Nat.card_pos.ne')
  rw [Nat.card_sum, h1, h2]
  ring

omit ha₁ ha₃ in
/-- The polynomial `w = Φₙ' ΨSqₙ − Φₙ ΨSqₙ'` is nonzero: its coefficient of degree `2n² − 2` is
`n²`. -/
theorem wpoly_ne_zero (n : ℕ) (hn : n ≠ 0) :
    derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n) ≠ 0 := by
  have hn' : ((n : ℤ) : K) ≠ 0 := by exact_mod_cast hn
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have h1 : n = 1 := by omega
    subst h1
    simp only [Nat.cast_one, Φ_one, ΨSq_one, derivative_X, derivative_one, mul_one, mul_zero,
      sub_zero]
    exact one_ne_zero
  set N := n ^ 2 with hN
  have hN2 : 2 ≤ N := by rw [hN]; nlinarith
  have hNK : (N : K) ≠ 0 := by rw [hN]; exact_mod_cast pow_ne_zero 2 hn
  -- the leading terms
  have hΦ : (W.Φ n).natDegree = N := by rw [natDegree_Φ, Int.natAbs_natCast]
  have hΦc : (W.Φ n).coeff N = 1 := by
    have := W.coeff_Φ n
    rwa [Int.natAbs_natCast] at this
  have hΨ : (W.ΨSq n).natDegree = N - 1 := by rw [W.natDegree_ΨSq hn', Int.natAbs_natCast]
  have hΨc : (W.ΨSq n).coeff (N - 1) = N := by
    have := W.coeff_ΨSq n
    rw [Int.natAbs_natCast] at this
    rw [this, hN]; push_cast; ring
  have hΦ' : (derivative (W.Φ n)).natDegree = N - 1 := by
    refine natDegree_eq_of_le_of_coeff_ne_zero ((natDegree_derivative_le _).trans (by omega)) ?_
    rw [coeff_derivative, Nat.sub_add_cancel (by omega), hΦc, one_mul]
    push_cast [Nat.cast_sub (show 1 ≤ N by omega)]
    rw [sub_add_cancel]; exact hNK
  have hΦ'c : (derivative (W.Φ n)).leadingCoeff = N := by
    rw [leadingCoeff, hΦ', coeff_derivative, Nat.sub_add_cancel (by omega), hΦc, one_mul]
    push_cast [Nat.cast_sub (show 1 ≤ N by omega)]
    ring
  have hΨ' : (derivative (W.ΨSq n)).natDegree = N - 2 := by
    refine natDegree_eq_of_le_of_coeff_ne_zero ((natDegree_derivative_le _).trans (by omega)) ?_
    rw [coeff_derivative, show N - 2 + 1 = N - 1 by omega, hΨc]
    push_cast [Nat.cast_sub (show 2 ≤ N by omega)]
    refine mul_ne_zero hNK ?_
    rw [show (N : K) - 2 + 1 = (N - 1 : ℕ) by push_cast [Nat.cast_sub (show 1 ≤ N by omega)]; ring]
    exact_mod_cast (show N - 1 ≠ 0 by omega)
  have hΨ'c : (derivative (W.ΨSq n)).leadingCoeff = N * (N - 1 : ℕ) := by
    rw [leadingCoeff, hΨ', coeff_derivative, show N - 2 + 1 = N - 1 by omega, hΨc]
    push_cast [Nat.cast_sub (show 2 ≤ N by omega), Nat.cast_sub (show 1 ≤ N by omega)]
    ring
  intro h0
  have hc := congrArg (fun p : K[X] => p.coeff (2 * N - 2)) h0
  simp only [coeff_sub, coeff_zero] at hc
  have e1 : 2 * N - 2 = (derivative (W.Φ n)).natDegree + (W.ΨSq n).natDegree := by
    rw [hΦ', hΨ]; omega
  have e2 : 2 * N - 2 = (W.Φ n).natDegree + (derivative (W.ΨSq n)).natDegree := by
    rw [hΦ, hΨ']; omega
  rw [e1, coeff_mul_degree_add_degree, ← e1, e2, coeff_mul_degree_add_degree, hΦ'c,
    leadingCoeff, hΨ, hΨc, leadingCoeff, hΦ, hΦc, hΨ'c] at hc
  push_cast [Nat.cast_sub (show 1 ≤ N by omega)] at hc
  apply hNK
  linear_combination hc

/-- There is an `x₀` with `f(x₀) ≠ 0` such that `hₓ₀` has only simple roots. -/
theorem exists_good_x₀ (n : ℕ) (hn : n ≠ 0) :
    ∃ x₀ : K, cubic W x₀ ≠ 0 ∧ (fibrePoly W n x₀).roots.Nodup := by
  set w := derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n) with hw
  have hw0 : w ≠ 0 := wpoly_ne_zero n hn
  have hf0 : (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : K[X]) ≠ 0 := by
    intro h0
    have := congrArg natDegree h0
    rw [natDegree_zero] at this
    have h3 : (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : K[X]).natDegree = 3 := by
      compute_degree!
    omega
  -- the finite set of bad values
  let B : Set K := ((fun r => (W.Φ n).eval r / (W.ΨSq n).eval r) '' {r | w.IsRoot r}) ∪
    {r | (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : K[X]).IsRoot r}
  have hB : B.Finite := ((finite_setOf_isRoot hw0).image _).union (finite_setOf_isRoot hf0)
  obtain ⟨x₀, hx₀⟩ := Infinite.exists_notMem_finset hB.toFinset
  rw [Set.Finite.mem_toFinset] at hx₀
  refine ⟨x₀, fun h0 => hx₀ (Or.inr ?_), ?_⟩
  · simp only [Set.mem_setOf_eq, IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    exact h0
  · rw [Multiset.nodup_iff_count_le_one]
    intro x₁
    rw [count_roots]
    by_contra hlt
    push_neg at hlt
    obtain ⟨hr, hr'⟩ := (one_lt_rootMultiplicity_iff_isRoot (fibrePoly_ne_zero n hn x₀)).mp hlt
    have hΨ := ΨSq_ne_zero_of_root ha₁ ha₃ n hn hr
    apply hx₀
    refine Or.inl ⟨x₁, ?_, ?_⟩
    · -- `x₁` is a root of `w`
      simp only [Set.mem_setOf_eq, IsRoot, hw, eval_sub, eval_mul]
      rw [IsRoot, fibrePoly, derivative_sub, derivative_C_mul, eval_sub, eval_mul, eval_C] at hr'
      rw [IsRoot, eval_fibrePoly] at hr
      have hx₀' : x₀ = (W.Φ n).eval x₁ / (W.ΨSq n).eval x₁ := by
        rw [eq_div_iff hΨ]; linear_combination -hr
      rw [hx₀'] at hr'
      field_simp at hr'
      linear_combination hr'
    · rw [IsRoot, eval_fibrePoly] at hr
      show (W.Φ n).eval x₁ / (W.ΨSq n).eval x₁ = x₀
      rw [div_eq_iff hΨ]; linear_combination hr

/-- **The `n`-torsion of an elliptic curve over an algebraically closed field of
characteristic `0` has `n²` elements.** -/
theorem card_torsionBy_eq_sq (n : ℕ) (hn : n ≠ 0) :
    Nat.card (AddSubgroup.torsionBy W.Point n) = n ^ 2 := by
  obtain ⟨x₀, hf, hnodup⟩ := exists_good_x₀ ha₁ ha₃ n hn
  obtain ⟨y₀, h₀⟩ := exists_point ha₁ ha₃ x₀
  have hy₀ : y₀ ≠ 0 := by
    intro h0
    apply hf
    have := hQ_of ha₁ ha₃ h₀
    rw [h0, zero_pow two_ne_zero] at this
    exact this.symm
  haveI : Finite (AddSubgroup.torsionBy W.Point n) := by
    have := torsion_finite ha₁ ha₃ n hn
    have hset : {P : W.Point | n • P = 0} = (AddSubgroup.torsionBy W.Point n : Set W.Point) := by
      ext P
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, AddSubgroup.torsionBy.nsmul_iff]
    rw [hset] at this
    exact this.to_subtype
  have h1 := card_fibre_eq_two_mul ha₁ ha₃ n hn h₀ hy₀
  have h2 := card_fibre ha₁ ha₃ n hn h₀ hy₀
  rw [h1, Multiset.toFinset_card_of_nodup hnodup,
    ← (IsAlgClosed.splits (fibrePoly W n x₀)).natDegree_eq_card_roots,
    natDegree_fibrePoly n hn] at h2
  omega

/-- **`E[ℓ] ≅ (ℤ/ℓ)²` for a prime `ℓ`.** -/
theorem torsionBasis (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    Nonempty (AddSubgroup.torsionBy W.Point ℓ ≃+ (Fin 2 → ZMod ℓ)) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  letI : Module (ZMod ℓ) (AddSubgroup.torsionBy W.Point ℓ) := AddSubgroup.torsionBy.zmodModule
  have hcard := card_torsionBy_eq_sq ha₁ ha₃ ℓ hℓ.out.ne_zero
  haveI : Finite (AddSubgroup.torsionBy W.Point ℓ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hℓ.out.ne_zero)
  haveI : Fintype (AddSubgroup.torsionBy W.Point ℓ) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod ℓ) (AddSubgroup.torsionBy W.Point ℓ) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy W.Point ℓ) = 2 := by
    have := Module.card_eq_pow_finrank (K := ZMod ℓ) (V := AddSubgroup.torsionBy W.Point ℓ)
    rw [← Nat.card_eq_fintype_card, hcard, ZMod.card] at this
    exact (Nat.pow_right_injective hℓ.out.two_le this).symm
  exact ⟨(Module.finBasisOfFinrankEq (ZMod ℓ) _ hrank).equivFun.toAddEquiv⟩

end count

end Iut.Torsion
