/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.Legendre
import Heights.VeluProduct

/-!
# Points of order `2` and `4` of the Legendre curve, and the Vélu ratio

On the Legendre curve `E_λ : y² = x(x − 1)(x − λ)` over a field of characteristic `≠ 2`
containing `s₁ = √λ`, `s₂ = √(1 − λ)` and `i = √−1`:

* `T₁ = (0, 0)` and `T₂ = (1, 0)` have order `2`;
* `R₁ = (s₁, i s₁(s₁ − 1))` and `R₂ = (1 + s₂, s₂(1 + s₂))` satisfy `2R₁ = T₁`, `2R₂ = T₂`
  (`Iut.CyclicPoints.half₁_add_self`, `Iut.CyclicPoints.half₂_add_self`).

For a finite subgroup `H` of odd order and a pair `(T, R)` with `T` of order `2` and `2R = T`,
the **Vélu ratio** `r(T, R) = ∏_{Q ∈ H∖0} (x(T) − x(R + Q))/(x(T) − x(Q))` is nonzero and
satisfies `r(T, R) (x(T) − x(R)) = ∑_{Q ∈ H} x(T + Q) − ∑_{Q ∈ H} x(R + Q)`
(`Iut.CyclicPoints.veluRatio_mul`, from `Heights.Velu.prod_mul_sum_sub_sum`): the ratio is
multiplicative in the torsion coordinates, and additive up to the factor `x(T) − x(R)`.
-/

namespace Iut.CyclicPoints

open WeierstrassCurve WeierstrassCurve.Affine Iut.Tripod Heights.Velu

variable {L : Type*} [Field L] {W : WeierstrassCurve L} [W.IsElliptic] {l : L}

/-! ### The points -/

section Points

variable (hW : W = legendre l)
include hW

lemma equation_iff {x y : L} :
    W.toAffine.Equation x y ↔ y ^ 2 = x * (x - 1) * (x - l) := by
  subst hW
  rw [Affine.equation_iff]
  simp only [legendre_a₁, legendre_a₂, legendre_a₃, legendre_a₄, legendre_a₆]
  constructor <;> intro h <;> linear_combination h

lemma negY_eq (x y : L) : W.toAffine.negY x y = -y := by
  subst hW; exact legendre_negY l x y

/-- `T₁ = (0, 0)`. -/
noncomputable def pt₁ : W.toAffine.Point :=
  Point.mk (x := 0) (y := 0) ((equation_iff hW).mpr (by ring))

/-- `T₂ = (1, 0)`. -/
noncomputable def pt₂ : W.toAffine.Point :=
  Point.mk (x := 1) (y := 0) ((equation_iff hW).mpr (by ring))

/-- `R₁ = (s, i s (s − 1))` for `s² = λ`, `i² = −1`. -/
noncomputable def half₁ {s i : L} (hs : s ^ 2 = l) (hi : i ^ 2 = -1) : W.toAffine.Point :=
  Point.mk (x := s) (y := i * s * (s - 1)) ((equation_iff hW).mpr (by
    rw [← hs]; linear_combination (s ^ 2 * (s - 1) ^ 2) * hi))

/-- `R₂ = (1 + s, s (1 + s))` for `s² = 1 − λ`. -/
noncomputable def half₂ {s : L} (hs : s ^ 2 = 1 - l) : W.toAffine.Point :=
  Point.mk (x := 1 + s) (y := s * (1 + s)) ((equation_iff hW).mpr (by
    have hl : l = 1 - s ^ 2 := by rw [hs]; ring
    rw [hl]; ring))

@[simp] lemma xOf_pt₁ : xOf (pt₁ hW) = 0 := rfl
@[simp] lemma xOf_pt₂ : xOf (pt₂ hW) = 1 := rfl
@[simp] lemma xOf_half₁ {s i : L} (hs : s ^ 2 = l) (hi : i ^ 2 = -1) :
    xOf (half₁ hW hs hi) = s := rfl
@[simp] lemma xOf_half₂ {s : L} (hs : s ^ 2 = 1 - l) : xOf (half₂ hW hs) = 1 + s := rfl

lemma pt₁_ne_zero : pt₁ hW ≠ 0 := Point.some_ne_zero _
lemma pt₂_ne_zero : pt₂ hW ≠ 0 := Point.some_ne_zero _

variable [DecidableEq L]

lemma pt₁_add_self : pt₁ hW + pt₁ hW = 0 :=
  Point.add_self_of_Y_eq (by rw [negY_eq hW, neg_zero])

lemma pt₂_add_self : pt₂ hW + pt₂ hW = 0 :=
  Point.add_self_of_Y_eq (by rw [negY_eq hW, neg_zero])

variable [NeZero (2 : L)]

/-- `2R₁ = T₁`. -/
lemma half₁_add_self (hl0 : l ≠ 0) (hl1 : l ≠ 1) {s i : L} (hs : s ^ 2 = l)
    (hi : i ^ 2 = -1) : half₁ hW hs hi + half₁ hW hs hi = pt₁ hW := by
  have hs0 : s ≠ 0 := by rintro rfl; apply hl0; rw [← hs]; ring
  have hs1 : s - 1 ≠ 0 := by
    intro h; apply hl1; rw [← hs, sub_eq_zero.mp h]; ring
  have hi0 : i ≠ 0 := by rintro rfl; norm_num at hi
  have h2 : (2 : L) ≠ 0 := NeZero.ne 2
  have hy : i * s * (s - 1) ≠ W.toAffine.negY s (i * s * (s - 1)) := by
    rw [negY_eq hW]
    intro h
    have : 2 * (i * s * (s - 1)) = 0 := by linear_combination h
    simp [h2, hi0, hs0, hs1] at this
  have ha₁ : W.a₁ = 0 := by subst hW; rfl
  have ha₂ : W.a₂ = -(1 + l) := by subst hW; rfl
  have ha₃ : W.a₃ = 0 := by subst hW; rfl
  have ha₄ : W.a₄ = l := by subst hW; rfl
  unfold half₁ pt₁ Point.mk
  rw [Point.add_self_of_Y_ne hy, Point.some.injEq]
  have hslope : W.toAffine.slope s s (i * s * (s - 1)) (i * s * (s - 1)) = i * (s - 1) := by
    rw [slope_of_Y_ne rfl hy, negY_eq hW, ha₁, ha₂, ha₄, ← hs]
    rw [div_eq_iff (by
      intro h
      have : 2 * (i * s * (s - 1)) = 0 := by linear_combination h
      simp [h2, hi0, hs0, hs1] at this)]
    linear_combination (-(2 * s * (s - 1) ^ 2)) * hi
  have hX : W.toAffine.addX s s (i * (s - 1)) = 0 := by
    rw [addX, ha₁, ha₂, ← hs]
    linear_combination (s - 1) ^ 2 * hi
  refine ⟨?_, ?_⟩
  · rw [hslope, hX]
  · rw [hslope, addY, negAddY, hX, negY_eq hW]
    ring

/-- `2R₂ = T₂`. -/
lemma half₂_add_self (hl0 : l ≠ 0) (hl1 : l ≠ 1) {s : L} (hs : s ^ 2 = 1 - l) :
    half₂ hW hs + half₂ hW hs = pt₂ hW := by
  have hs0 : s ≠ 0 := by rintro rfl; apply hl1; linear_combination hs
  have hs1 : 1 + s ≠ 0 := by
    intro h; apply hl0
    have : s = -1 := by linear_combination h
    rw [this] at hs; linear_combination hs
  have h2 : (2 : L) ≠ 0 := NeZero.ne 2
  have hy : s * (1 + s) ≠ W.toAffine.negY (1 + s) (s * (1 + s)) := by
    rw [negY_eq hW]
    intro h
    have : 2 * (s * (1 + s)) = 0 := by linear_combination h
    simp [h2, hs0, hs1] at this
  have ha₁ : W.a₁ = 0 := by subst hW; rfl
  have ha₂ : W.a₂ = -(1 + l) := by subst hW; rfl
  have ha₃ : W.a₃ = 0 := by subst hW; rfl
  have ha₄ : W.a₄ = l := by subst hW; rfl
  have hl : l = 1 - s ^ 2 := by rw [hs]; ring
  unfold half₂ pt₂ Point.mk
  rw [Point.add_self_of_Y_ne hy, Point.some.injEq]
  have hslope : W.toAffine.slope (1 + s) (1 + s) (s * (1 + s)) (s * (1 + s)) = 1 + s := by
    rw [slope_of_Y_ne rfl hy, negY_eq hW, ha₁, ha₂, ha₄, hl]
    rw [div_eq_iff (by
      intro h
      have : 2 * (s * (1 + s)) = 0 := by linear_combination h
      simp [h2, hs0, hs1] at this)]
    ring
  have hX : W.toAffine.addX (1 + s) (1 + s) (1 + s) = 1 := by
    rw [addX, ha₁, ha₂, hl]
    ring
  refine ⟨?_, ?_⟩
  · rw [hslope, hX]
  · rw [hslope, addY, negAddY, hX, negY_eq hW]
    ring

end Points

/-! ### Subgroups of odd order and the Vélu ratio -/

section Ratio

variable [DecidableEq L]

variable (H : AddSubgroup W.toAffine.Point) [Fintype H]

omit [W.IsElliptic] in
/-- An element of a subgroup of odd order with `2Q = 0` is zero. -/
lemma eq_zero_of_add_self {Q : W.toAffine.Point} (hodd : Odd (Fintype.card H)) (hQ : Q ∈ H)
    (h2 : Q + Q = 0) : Q = 0 := by
  obtain ⟨k, hk⟩ := hodd
  have hcard : (Fintype.card H) • (⟨Q, hQ⟩ : H) = 0 := card_nsmul_eq_zero
  have hcard' : (Fintype.card H) • Q = 0 := by
    have := congrArg Subtype.val hcard
    rwa [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero] at this
  have hkQ : k • Q + k • Q = 0 := by rw [← add_nsmul, ← two_mul, mul_nsmul, two_nsmul, h2,
    nsmul_zero]
  rw [hk, add_nsmul, one_nsmul, mul_comm, mul_nsmul, two_nsmul, hkQ, zero_add] at hcard'
  exact hcard'

omit [W.IsElliptic] in
/-- A subgroup of odd order has no points of order `2`. -/
lemma neg_ne_self (hodd : Odd (Fintype.card H)) (Q : H) (hQ : Q ≠ 0) : -Q ≠ Q := by
  intro h
  apply hQ
  apply Subtype.ext
  apply eq_zero_of_add_self H hodd Q.2
  have := congrArg Subtype.val h
  simp only [AddSubgroup.coe_neg] at this
  calc (Q : W.toAffine.Point) + Q = -Q + Q := by rw [this]
    _ = 0 := neg_add_cancel _

omit [W.IsElliptic] in
/-- A point of order `2` is not in a subgroup of odd order. -/
lemma notMem_of_add_self (hodd : Odd (Fintype.card H)) {T : W.toAffine.Point} (hT0 : T ≠ 0)
    (hT2 : T + T = 0) : T ∉ H := fun hT => hT0 (eq_zero_of_add_self H hodd hT hT2)

/-- **The Vélu ratio** `∏_{Q ∈ H∖0} (x(T) − x(R + Q))/(x(T) − x(Q))`. -/
noncomputable def veluRatio (T R : W.toAffine.Point) : L :=
  ∏ Q ∈ nonzero H, (xOf T - xOf (R + (Q : W.toAffine.Point))) / (xOf T - xOf (Q : W.toAffine.Point))

variable {H}

omit [W.IsElliptic] in
/-- The Vélu ratio is nonzero for `T` of order `2` and `2R = T`. -/
lemma veluRatio_ne_zero (hodd : Odd (Fintype.card H)) {T R : W.toAffine.Point} (hT0 : T ≠ 0)
    (hT2 : T + T = 0) (hRT : R + R = T) : veluRatio H T R ≠ 0 := by
  have hT : T ∉ H := notMem_of_add_self H hodd hT0 hT2
  have hR : R ∉ H := fun hR => hT (hRT ▸ H.add_mem hR hR)
  refine Finset.prod_ne_zero_iff.mpr fun Q hQ => div_ne_zero ?_ ?_
  · rw [sub_ne_zero]
    intro hx
    have hRQ : R + (Q : W.toAffine.Point) ≠ 0 := fun h =>
      hR (by rw [eq_neg_of_add_eq_zero_left h]; exact H.neg_mem Q.2)
    have hTR : T - R = R := by rw [← hRT]; abel
    rcases eq_or_eq_neg_of_xOf_eq hT0 hRQ hx with h | h
    · apply hR
      have : (Q : W.toAffine.Point) = R := by rw [← hTR, h]; abel
      exact this ▸ Q.2
    · apply hR
      have hTT : -T = T := neg_eq_of_add_eq_zero_left hT2
      have : (Q : W.toAffine.Point) = R := by
        rw [← hTR, ← hTT, h]; abel
      exact this ▸ Q.2
  · exact sub_ne_zero.mpr (xOf_ne_of_notMem H hT Q.2 fun h =>
      (mem_nonzero H).mp hQ (Subtype.ext h))

omit [W.IsElliptic] in
/-- **The Vélu ratio, additively**:
`r(T, R)·(x(T) − x(R)) = ∑_{Q ∈ H} x(T + Q) − ∑_{Q ∈ H} x(R + Q)`
for `T` of order `2` and `2R = T`. -/
lemma veluRatio_mul (h2 : (2 : L) ≠ 0) (hodd : Odd (Fintype.card H)) {T R : W.toAffine.Point}
    (hT0 : T ≠ 0) (hT2 : T + T = 0) (hRT : R + R = T) :
    veluRatio H T R * (xOf T - xOf R) =
      ∑ Q : H, xOf (T + (Q : W.toAffine.Point)) - ∑ Q : H, xOf (R + (Q : W.toAffine.Point)) := by
  classical
  have hT : T ∉ H := notMem_of_add_self H hodd hT0 hT2
  have hR : R ∉ H := fun hR => hT (hRT ▸ H.add_mem hR hR)
  have hRR : R + R ∉ H := hRT ▸ hT
  have hprod := prod_mul_sum_sub_sum H h2 (neg_ne_self H hodd) hT hR hRR
  have hsplit : ∏ Q : H, (xOf T - xOf (R + (Q : W.toAffine.Point))) =
      (xOf T - xOf R) * ∏ Q ∈ nonzero H, (xOf T - xOf (R + (Q : W.toAffine.Point))) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : H))]
    simp only [ZeroMemClass.coe_zero, add_zero]
    congr 1
    refine Finset.prod_congr ?_ fun _ _ => rfl
    ext Q; simp [nonzero, Finset.mem_erase, and_comm]
  have hden : ∏ Q ∈ nonzero H, (xOf T - xOf (Q : W.toAffine.Point)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun Q hQ => sub_ne_zero.mpr (xOf_ne_of_notMem H hT Q.2 fun h =>
      (mem_nonzero H).mp hQ (Subtype.ext h))
  rw [hsplit] at hprod
  unfold veluRatio
  rw [Finset.prod_div_distrib]
  field_simp
  linear_combination hprod.symm

end Ratio

end Iut.CyclicPoints
