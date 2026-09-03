/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.PointMap
import TateCurvesTheta
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Tate structures on elliptic curves over local fields

A **Tate structure** on an elliptic curve `E` over a complete rank-one valued field `k`
(`Iut.TateStructure E`) is a Tate uniformization of `E`: a Tate parameter `q` with
`‖q‖ < 1`, a change of variables `C` with `C • E = E_q` (the Tate curve of
`lana-agents/tate-curves-theta`), and a group isomorphism `k^×/q^ℤ ≃ E(k)`, **pinned** by
the requirement that the point attached to a unit `u ∉ q^ℤ` has, in the model `E_q`, the
coordinates `(X(u), Y(u))` of the Tate parametrization (`TateParameter.X`, `TateParameter.Y`).
The pinning determines the isomorphism uniquely; by Tate's theorem (Silverman, *Advanced
Topics*, V.3.1, V.5.3) a Tate structure exists exactly when `E` has split multiplicative
reduction.

From a Tate structure one reads off the objects of *The Étale Theta Function*,
Definitions 2.3–2.5, at the level of ℓ-torsion:

* the **graph line** `μ_ℓ ⊆ E(k)[ℓ]` (`TateStructure.graphLine`), the image of the ℓ-th
  roots of unity — the kernel of the graph quotient `E[ℓ] → E[ℓ]/μ_ℓ ≅ ℤ/ℓℤ`;
* the **canonical generators** `±q^{1/ℓ}` of the graph quotient
  (`TateStructure.IsCanonical`): the images of the units `u` with `u^ℓ ∈ q^{±1}·q^{ℓℤ}`.
-/

namespace Iut

open WeierstrassCurve TateCurvesTheta
open scoped Classical Valued

universe u

noncomputable section

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

/-- The `x`-coordinate of a point in the model `C • E` (Mathlib's convention
`(X, Y) ↦ (u²X' + r, u³Y' + u²sX' + t)`: the new coordinate is `X' = (X - r)/u²`); `0` at
the point at infinity. -/
def xCoord (C : VariableChange k) : {E : WeierstrassCurve k} → E.toAffine.Point → k
  | _, Affine.Point.zero => 0
  | _, Affine.Point.some x _ _ => (x - C.r) / (C.u : k) ^ 2

/-- The `y`-coordinate of a point in the model `C • E`: `Y' = (Y - t - s(X - r))/u³`; `0`
at the point at infinity. -/
def yCoord (C : VariableChange k) : {E : WeierstrassCurve k} → E.toAffine.Point → k
  | _, Affine.Point.zero => 0
  | _, Affine.Point.some x y _ => (y - C.t - C.s * (x - C.r)) / (C.u : k) ^ 3

/-- **A Tate structure** on `E`: a Tate uniformization `k^×/q^ℤ ≃ E(k)`, pinned by the
coordinates of the Tate parametrization in the model `C • E = E_q`. -/
structure TateStructure (E : WeierstrassCurve k) : Type u where
  /-- The Tate parameter `q`. -/
  t : TateParameter k
  /-- The change of variables to the Tate curve. -/
  C : VariableChange k
  /-- `C • E` is the Tate curve `E_q`. -/
  hC : C • E = t.tateCurve
  /-- The uniformization `k^×/q^ℤ ≃ E(k)`. -/
  iso : Additive (kˣ ⧸ Subgroup.zpowers t.q) ≃+ E.toAffine.Point
  /-- The point of a unit `u ∉ q^ℤ` has `x`-coordinate `X(u)` in the model `E_q`. -/
  iso_x : ∀ u : kˣ, (∀ n : ℤ, (t.q : k) ^ n * u ≠ 1) →
    xCoord C (iso (Additive.ofMul (QuotientGroup.mk u))) = t.X u
  /-- The point of a unit `u ∉ q^ℤ` has `y`-coordinate `Y(u)` in the model `E_q`. -/
  iso_y : ∀ u : kˣ, (∀ n : ℤ, (t.q : k) ^ n * u ≠ 1) →
    yCoord C (iso (Additive.ofMul (QuotientGroup.mk u))) = t.Y u

namespace TateStructure

variable {E : WeierstrassCurve k} (S : TateStructure E)

/-- The point of `E(k)` attached to a unit. -/
def ofUnit (u : kˣ) : E.toAffine.Point := S.iso (Additive.ofMul (QuotientGroup.mk u))

lemma ofUnit_mul (u v : kˣ) : S.ofUnit (u * v) = S.ofUnit u + S.ofUnit v := by
  unfold ofUnit
  rw [← map_add]
  rfl

lemma ofUnit_one : S.ofUnit 1 = 0 := by
  unfold ofUnit
  rw [← map_zero S.iso]
  rfl

lemma ofUnit_eq_iff (u v : kˣ) : S.ofUnit u = S.ofUnit v ↔ ∃ n : ℤ, v = S.t.q ^ n * u := by
  unfold ofUnit
  rw [S.iso.injective.eq_iff, Additive.ofMul.injective.eq_iff, QuotientGroup.eq]
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, mul_comm, mul_inv_cancel_left]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, mul_comm (S.t.q ^ n) u, inv_mul_cancel_left]⟩

lemma ofUnit_surjective : Function.Surjective S.ofUnit := fun P => by
  obtain ⟨a, ha⟩ := S.iso.surjective P
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  exact ⟨u, by unfold ofUnit; rw [hu]; simpa using ha⟩

lemma ofUnit_inv (u : kˣ) : S.ofUnit u⁻¹ = -S.ofUnit u := by
  rw [eq_neg_iff_add_eq_zero, ← ofUnit_mul, inv_mul_cancel, ofUnit_one]

/-- **The graph line** `μ_ℓ ⊆ E(k)[ℓ]`: the points of the ℓ-th roots of unity. -/
def graphLine (ℓ : ℕ) : AddSubgroup E.toAffine.Point where
  carrier := {P | ∃ u : kˣ, u ^ ℓ = 1 ∧ S.ofUnit u = P}
  zero_mem' := ⟨1, one_pow ℓ, S.ofUnit_one⟩
  add_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u * v, by rw [mul_pow, hu, hv, one_mul], S.ofUnit_mul u v⟩
  neg_mem' := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, by rw [inv_pow, hu, inv_one], S.ofUnit_inv u⟩

lemma mem_graphLine_iff (ℓ : ℕ) (P : E.toAffine.Point) :
    P ∈ S.graphLine ℓ ↔ ∃ u : kˣ, u ^ ℓ = 1 ∧ S.ofUnit u = P := Iff.rfl

/-- **Canonical generators of the graph quotient**: the points of the units `u` with
`u^ℓ ∈ q^{±1}·q^{ℓℤ}` — the ℓ-th roots `q^{±1/ℓ}` of the Tate parameter modulo `μ_ℓ`. -/
def IsCanonical (ℓ : ℕ) (P : E.toAffine.Point) : Prop :=
  ∃ u : kˣ, S.ofUnit u = P ∧
    ∃ m : ℤ, u ^ ℓ = S.t.q ^ (1 + ℓ * m) ∨ u ^ ℓ = S.t.q ^ (-1 + ℓ * m)

end TateStructure

end

end Iut
