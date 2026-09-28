/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.CyclicGain
import Iut.Tripod.CyclicPoints
import Iut.Cor312.ThetaData.PointMap

/-!
# The Vélu ratio at a place with a Tate structure

Let `W` be an elliptic curve over a field `K₀`, `φ : K₀ → k` a field embedding into a complete
discretely valued field of residue characteristic `≠ 2`, and `S` a Tate structure on `W ×_φ k`.
Let `H ⊆ W(K₀)` be a subgroup of odd order `ℓ` which maps into the graph line `μ_ℓ` of `S`,
`T ∈ W(K₀)` a point of order `2` and `R` with `2R = T`. For the Vélu ratio
`r = ∏_{Q ∈ H∖0} (x(T) − x(R + Q))/(x(T) − x(Q))` (`Iut.CyclicPoints.veluRatio`), with `τ` the
Tate coordinate of `T` normalized to the annulus `‖q‖ < ‖τ‖ ≤ 1`
(`Iut.CyclicTate.ratio_bound`):

* if `τ = −1`, then `‖φ(r)‖ ≤ 1`;
* otherwise `‖τ‖² = ‖q‖` and `‖φ(r)‖⁴ ≤ ‖q‖^{ℓ − 1}`.

This is the local gain of the isogeny estimate: the point `T` reducing to the node forces
`ℓ − 1` factors of size `‖q‖^{1/4}` in `r`. Since at most one of two distinct points of order `2`
has Tate coordinate `−1`, for two such points `T₁ ≠ T₂` (with halves `R₁`, `R₂`) the product
satisfies `(‖φ(r₁)‖ ‖φ(r₂)‖)⁴ ≤ ‖q‖^{ℓ − 1}` (`Iut.CyclicTate.ratio_mul_bound`).
-/

namespace Iut.CyclicTate

open WeierstrassCurve TateCurvesTheta Iut.CyclicGain Iut.CyclicPoints Iut.Anabelian Heights.Velu
open scoped Classical Valued

universe u

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
  {K₀ : Type*} [Field K₀] (φ : K₀ →+* k) {W : WeierstrassCurve K₀}
  (S : TateStructure (W.map φ))

omit [CompleteSpace k] in
/-- `x` commutes with the point map. -/
lemma xOf_pointMap (P : W.toAffine.Point) : xOf (pointMap W φ P) = φ (xOf P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, map_zero]
    simp
  · rfl

/-- The Tate coordinate of the image of a nonzero point gives its `x`-coordinate. -/
lemma map_xOf_eq {P : W.toAffine.Point} (hP : P ≠ 0) {u : kˣ}
    (hu : S.ofUnit u = pointMap W φ P) : φ (xOf P) = (S.C.u : k) ^ 2 * S.t.X u + S.C.r := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rw [pointMap_some] at hu
    exact x_eq_of_ofUnit S _ hu

/-- A normalized Tate coordinate of the image of a point. -/
lemma exists_class (P : W.toAffine.Point) :
    ∃ u : kˣ, S.ofUnit u = pointMap W φ P ∧ ‖(S.t.q : k)‖ < ‖(u : k)‖ ∧ ‖(u : k)‖ ≤ 1 := by
  obtain ⟨u₀, hu₀⟩ := S.ofUnit_surjective (pointMap W φ P)
  obtain ⟨n, hlo, hhi⟩ := exists_zpow_mul_mem_annulus S.t u₀
  refine ⟨S.t.q ^ n * u₀, ?_, hlo, hhi⟩
  rw [← hu₀, S.ofUnit_eq_iff]
  exact ⟨-n, by rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]⟩

variable [W.IsElliptic] (H : AddSubgroup W.toAffine.Point) [Fintype H]

/-- **The Vélu ratio at a Tate place.** -/
theorem ratio_bound {ℓ : ℕ} (hℓ : Odd ℓ) (hcard : Fintype.card H = ℓ) (h2 : ‖(2 : k)‖ = 1)
    (hgraph : ∀ Q ∈ H, pointMap W φ Q ∈ S.graphLine ℓ) {T R : W.toAffine.Point}
    (hT0 : T ≠ 0) (hT2 : T + T = 0) (hRT : R + R = T) :
    ∃ τ : kˣ, S.ofUnit τ = pointMap W φ T ∧
      (((τ : k) = -1 ∧ ‖φ (veluRatio H T R)‖ ≤ 1) ∨
        (‖(τ : k)‖ ^ 2 = ‖(S.t.q : k)‖ ∧
          ‖φ (veluRatio H T R)‖ ^ 4 ≤ ‖(S.t.q : k)‖ ^ (ℓ - 1))) := by
  have hodd : Odd (Fintype.card H) := hcard ▸ hℓ
  have hT : T ∉ H := notMem_of_add_self H hodd hT0 hT2
  have hR : R ∉ H := fun hR => hT (hRT ▸ H.add_mem hR hR)
  have hpm0 : ∀ P : W.toAffine.Point, pointMap W φ P = 0 → P = 0 := fun P h =>
    pointMap_injective W φ (h.trans (map_zero _).symm)
  -- the classes of `T` and `R`
  obtain ⟨τ, hτ, hτlo, hτhi⟩ := exists_class φ S T
  obtain ⟨ρ, hρ, hρlo, hρhi⟩ := exists_class φ S R
  have hTm0 : pointMap W φ T ≠ 0 := fun h => hT0 (hpm0 T h)
  have hTm2 : pointMap W φ T + pointMap W φ T = 0 := by rw [← map_add, hT2, map_zero]
  have hRTm : pointMap W φ R + pointMap W φ R = pointMap W φ T := by rw [← map_add, hRT]
  -- the classes of the points of `H`
  have hζ : ∀ Q : H, Q ∈ nonzero H → ∃ ζ : kˣ, ζ ^ ℓ = 1 ∧ (ζ : k) ≠ 1 ∧
      S.ofUnit ζ = pointMap W φ Q := by
    intro Q hQ
    obtain ⟨ζ, hζℓ, hζQ⟩ := hgraph Q Q.2
    refine ⟨ζ, hζℓ, fun h1 => ?_, hζQ⟩
    have : ζ = 1 := Units.ext h1
    rw [this, S.ofUnit_one] at hζQ
    exact (mem_nonzero H).mp hQ (Subtype.ext (hpm0 _ hζQ.symm))
  choose! ζ hζℓ hζ1 hζQ using hζ
  -- the factors in Tate coordinates
  have hfac : ∀ Q ∈ nonzero H,
      ‖φ ((xOf T - xOf (R + (Q : W.toAffine.Point))) / (xOf T - xOf (Q : W.toAffine.Point)))‖ =
        ‖S.t.X τ - S.t.X (ρ * ζ Q)‖ / ‖S.t.X τ - S.t.X (ζ Q)‖ := by
    intro Q hQ
    have hQ0 : (Q : W.toAffine.Point) ≠ 0 := fun h => (mem_nonzero H).mp hQ (Subtype.ext h)
    have hRQ0 : R + (Q : W.toAffine.Point) ≠ 0 := fun h =>
      hR (by rw [eq_neg_of_add_eq_zero_left h]; exact H.neg_mem Q.2)
    have hRQ : S.ofUnit (ρ * ζ Q) = pointMap W φ (R + Q) := by
      rw [S.ofUnit_mul, hρ, hζQ Q hQ, map_add]
    have hu0 : (S.C.u : k) ≠ 0 := Units.ne_zero _
    rw [map_div₀, map_sub, map_sub, map_xOf_eq φ S hT0 hτ, map_xOf_eq φ S hRQ0 hRQ,
      map_xOf_eq φ S hQ0 (hζQ Q hQ), norm_div]
    rw [show (S.C.u : k) ^ 2 * S.t.X τ + S.C.r - ((S.C.u : k) ^ 2 * S.t.X (ρ * ζ Q) + S.C.r) =
      (S.C.u : k) ^ 2 * (S.t.X τ - S.t.X (ρ * ζ Q)) by ring,
      show (S.C.u : k) ^ 2 * S.t.X τ + S.C.r - ((S.C.u : k) ^ 2 * S.t.X (ζ Q) + S.C.r) =
      (S.C.u : k) ^ 2 * (S.t.X τ - S.t.X (ζ Q)) by ring, norm_mul, norm_mul]
    have hu : 0 < ‖(S.C.u : k) ^ 2‖ := norm_pos_iff.mpr (pow_ne_zero _ hu0)
    rw [mul_div_mul_left _ _ hu.ne']
  have hr : ‖φ (veluRatio H T R)‖ = ∏ Q ∈ nonzero H,
      ‖S.t.X τ - S.t.X (ρ * ζ Q)‖ / ‖S.t.X τ - S.t.X (ζ Q)‖ := by
    unfold veluRatio
    rw [map_prod, norm_prod]
    exact Finset.prod_congr rfl hfac
  have hcardnz : (nonzero H).card = ℓ - 1 := by
    have h : nonzero H = Finset.univ.erase 0 := by ext Q; simp [nonzero]
    rw [h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
  refine ⟨τ, hτ, ?_⟩
  rcases two_torsion_class S hTm0 hTm2 hτ hτlo hτhi with hτ1 | hτn
  · -- `τ = −1`: every factor has norm `≤ 1`
    left
    refine ⟨hτ1, ?_⟩
    have hτ' : τ = -1 := Units.ext (by rw [hτ1]; simp)
    have hρ' := half_class_minus_one S hRTm (hτ' ▸ hτ) hρ hρlo hρhi
    rw [hr]
    refine Finset.prod_le_one (fun _ _ => by positivity) fun Q hQ => ?_
    obtain ⟨hnum, hden⟩ := minus_one_bounds S.t h2 hρ' hℓ (hζℓ Q hQ) (hζ1 Q hQ)
    rw [hτ']
    exact div_le_one_of_le₀ (hnum.trans hden) (norm_nonneg _)
  · -- `‖τ‖² = ‖q‖`: every factor has fourth power `≤ ‖q‖`
    right
    refine ⟨hτn, ?_⟩
    have hρ' := half_class_node S hRTm hτ hρ hτn hρlo hρhi
    have hℓ0 : ℓ ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hℓ
    rw [hr, ← Finset.prod_pow, ← hcardnz, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun Q hQ => ?_
    have hζn : ‖((ζ Q : kˣ) : k)‖ = 1 := by
      have h := congrArg (fun u : kˣ => ‖(u : k)‖) (hζℓ Q hQ)
      simp only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hℓ0).mp h
    obtain ⟨hnum, hden⟩ := node_bounds S.t hτn hρ' hζn (hζ1 Q hQ)
    calc (‖S.t.X τ - S.t.X (ρ * ζ Q)‖ / ‖S.t.X τ - S.t.X (ζ Q)‖) ^ 4
        ≤ ‖S.t.X τ - S.t.X (ρ * ζ Q)‖ ^ 4 := by
          gcongr
          exact div_le_self (norm_nonneg _) hden
      _ ≤ ‖(S.t.q : k)‖ := hnum

/-- **The gain at a Tate place for two points of order `2`**: for distinct points `T₁ ≠ T₂` of
order `2` with halves `R₁`, `R₂`, `(‖φ(r₁)‖ ‖φ(r₂)‖)⁴ ≤ ‖q‖^{ℓ − 1}`. -/
theorem ratio_mul_bound {ℓ : ℕ} (hℓ : Odd ℓ) (hcard : Fintype.card H = ℓ) (h2 : ‖(2 : k)‖ = 1)
    (hgraph : ∀ Q ∈ H, pointMap W φ Q ∈ S.graphLine ℓ) {T₁ R₁ T₂ R₂ : W.toAffine.Point}
    (hT₁0 : T₁ ≠ 0) (hT₁2 : T₁ + T₁ = 0) (hRT₁ : R₁ + R₁ = T₁)
    (hT₂0 : T₂ ≠ 0) (hT₂2 : T₂ + T₂ = 0) (hRT₂ : R₂ + R₂ = T₂) (hT : T₁ ≠ T₂) :
    (‖φ (veluRatio H T₁ R₁)‖ * ‖φ (veluRatio H T₂ R₂)‖) ^ 4 ≤ ‖(S.t.q : k)‖ ^ (ℓ - 1) := by
  have hq0 := S.t.norm_q_pos
  have hq1 := S.t.norm_lt_one
  have hqℓ : ‖(S.t.q : k)‖ ^ (ℓ - 1) ≤ 1 := pow_le_one₀ hq0.le hq1.le
  obtain ⟨τ₁, hτ₁, h₁⟩ := ratio_bound φ S H hℓ hcard h2 hgraph hT₁0 hT₁2 hRT₁
  obtain ⟨τ₂, hτ₂, h₂⟩ := ratio_bound φ S H hℓ hcard h2 hgraph hT₂0 hT₂2 hRT₂
  have hn₁ := norm_nonneg (φ (veluRatio H T₁ R₁))
  have hn₂ := norm_nonneg (φ (veluRatio H T₂ R₂))
  rw [mul_pow]
  rcases h₁ with ⟨hτ₁', h₁⟩ | ⟨-, h₁⟩ <;> rcases h₂ with ⟨hτ₂', h₂⟩ | ⟨-, h₂⟩
  · exfalso
    apply hT
    apply pointMap_injective W φ
    rw [← hτ₁, ← hτ₂, show τ₁ = τ₂ from Units.ext (hτ₁'.trans hτ₂'.symm)]
  · calc ‖φ (veluRatio H T₁ R₁)‖ ^ 4 * ‖φ (veluRatio H T₂ R₂)‖ ^ 4
        ≤ 1 * ‖(S.t.q : k)‖ ^ (ℓ - 1) := by
          gcongr
          exact pow_le_one₀ hn₁ h₁
      _ = _ := one_mul _
  · calc ‖φ (veluRatio H T₁ R₁)‖ ^ 4 * ‖φ (veluRatio H T₂ R₂)‖ ^ 4
        ≤ ‖(S.t.q : k)‖ ^ (ℓ - 1) * 1 := by
          gcongr
          exact pow_le_one₀ hn₂ h₂
      _ = _ := mul_one _
  · calc ‖φ (veluRatio H T₁ R₁)‖ ^ 4 * ‖φ (veluRatio H T₂ R₂)‖ ^ 4
        ≤ ‖(S.t.q : k)‖ ^ (ℓ - 1) * 1 := by
          gcongr
          exact h₂.trans hqℓ
      _ = _ := mul_one _

end Iut.CyclicTate
