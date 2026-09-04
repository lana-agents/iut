/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.TateStructureOfIso
import Iut.Cor312.ThetaData.TateIsomorphism

/-!
# Uniqueness of Tate structures

Two Tate structures on the same elliptic curve `E` over `k` have the same Tate parameter
(`j(E_q) = j(E)` determines `q`, `TateParameter.tateJ_injective`) and point maps that agree
up to a global sign: the changes of variables `C`, `C'` with `C • E = C' • E = E_q` differ by
an automorphism of `E_q`, and the only automorphisms of `E_q` are `1` and the negation
`(u, r, s, t) = (-1, 0, -1, 0)` (`Iut.eq_one_or_negChange_of_smul_tateCurve`), which acts as
`P ↦ -P` on points. Consequently the graph line and the canonical generators do not depend
on the Tate structure (`Iut.TateStructure.graphLine_eq`, `isCanonical_congr`).
-/

namespace Iut

open WeierstrassCurve TateCurvesTheta Iut.Anabelian
open scoped Classical Valued

universe u

noncomputable section

section Composition

variable {k : Type*} [Field k]

lemma vcX_mul (D C : VariableChange k) (x : k) : vcX (D * C) x = vcX D (vcX C x) := by
  simp only [vcX, VariableChange.mul_def, Units.val_mul]
  have hu := u_ne_zero C
  have hv := u_ne_zero D
  field_simp
  ring

lemma vcY_mul (D C : VariableChange k) (x y : k) :
    vcY (D * C) x y = vcY D (vcX C x) (vcY C x y) := by
  simp only [vcX, vcY, VariableChange.mul_def, Units.val_mul]
  have hu := u_ne_zero C
  have hv := u_ne_zero D
  field_simp
  ring

variable (k) in
/-- The negation change of variables `(-1, 0, -1, 0)`. -/
def negChange : VariableChange k := ⟨-1, 0, -1, 0⟩

lemma vcX_negChange (x : k) : vcX (negChange k) x = x := by
  simp [vcX, negChange]

lemma vcY_negChange (x y : k) : vcY (negChange k) x y = -y - x := by
  simp only [vcY, negChange]
  rw [Units.val_neg, Units.val_one]
  ring

end Composition

section Coordinates

variable {k : Type u} [Field k] {E : WeierstrassCurve k}

lemma xCoord_mul (D C : VariableChange k) {P : E.toAffine.Point} (hP : P ≠ 0) :
    xCoord (D * C) P = vcX D (xCoord C P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact vcX_mul D C x

lemma yCoord_mul (D C : VariableChange k) {P : E.toAffine.Point} (hP : P ≠ 0) :
    yCoord (D * C) P = vcY D (xCoord C P) (yCoord C P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact vcY_mul D C x y

lemma xCoord_neg (C : VariableChange k) (P : E.toAffine.Point) :
    xCoord C (-P) = xCoord C P := by
  cases P <;> rfl

lemma yCoord_neg (C : VariableChange k) {P : E.toAffine.Point} (hP : P ≠ 0) :
    yCoord C (-P) = (C • E).toAffine.negY (xCoord C P) (yCoord C P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    rw [Affine.Point.neg_some]
    exact vcY_negY C E x y

/-- Nonzero points with the same coordinates in a model are equal. -/
lemma eq_of_coords (C : VariableChange k) {P Q : E.toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : xCoord C P = xCoord C Q) (hy : yCoord C P = yCoord C Q) : P = Q := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    cases Q with
    | zero => exact absurd rfl hQ
    | some x' y' h' =>
      change vcX C x = vcX C x' at hx
      change vcY C x y = vcY C x' y' at hy
      have hxx := vcX_injective C hx
      subst hxx
      rw [vcY_inj] at hy
      subst hy
      rfl

end Coordinates

section Aut

variable {k : Type u} [NormedField k] [IsUltrametricDist k] [CompleteSpace k]

lemma negChange_smul_tateCurve (t : TateParameter k) :
    negChange k • t.tateCurve = t.tateCurve := by
  ext
  · rw [variableChange_a₁, t.tateCurve_a₁]
    simp [negChange] <;> norm_num
  · rw [variableChange_a₂, t.tateCurve_a₂, t.tateCurve_a₁]
    simp [negChange] <;> norm_num
  · rw [variableChange_a₃, t.tateCurve_a₃, t.tateCurve_a₁]
    simp [negChange] <;> norm_num
  · rw [variableChange_a₄, t.tateCurve_a₄, t.tateCurve_a₃, t.tateCurve_a₂, t.tateCurve_a₁]
    simp [negChange] <;> norm_num
  · rw [variableChange_a₆, t.tateCurve_a₆, t.tateCurve_a₄, t.tateCurve_a₃, t.tateCurve_a₂,
      t.tateCurve_a₁]
    simp [negChange] <;> norm_num

/-- **The automorphisms of a Tate curve** are `1` and the negation. -/
theorem eq_one_or_negChange_of_smul_tateCurve (t : TateParameter k) (h12 : (12 : k) ≠ 0)
    {D : VariableChange k} (hD : D • t.tateCurve = t.tateCurve) : D = 1 ∨ D = negChange k := by
  have h2 : (2 : k) ≠ 0 := by
    intro h
    apply h12
    rw [show (12 : k) = 2 * 6 by norm_num, h, zero_mul]
  have h3 : (3 : k) ≠ 0 := by
    intro h
    apply h12
    rw [show (12 : k) = 3 * 4 by norm_num, h, zero_mul]
  have hc₄ : t.tateCurve.c₄ ≠ 0 := by
    intro h
    have := t.norm_c₄_eq_one
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hc₆ : t.tateCurve.c₆ ≠ 0 := by
    intro h
    have := norm_c₆_eq_one t.tateCurve t.norm_c₄_eq_one (t.norm_Δ_lt_one h12)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hu0 := D.u.ne_zero
  have hu4 : (D.u : k) ^ 4 = 1 := by
    have h := variableChange_c₄ (W := t.tateCurve) (C := D)
    rw [hD, Units.val_inv_eq_inv_val, inv_pow] at h
    have h' : t.tateCurve.c₄ * (D.u : k) ^ 4 = t.tateCurve.c₄ := by
      calc t.tateCurve.c₄ * (D.u : k) ^ 4
          = ((D.u : k) ^ 4)⁻¹ * t.tateCurve.c₄ * (D.u : k) ^ 4 := by rw [← h]
        _ = t.tateCurve.c₄ := by field_simp
    have := mul_left_cancel₀ hc₄ (h'.trans (mul_one _).symm)
    exact this
  have hu6 : (D.u : k) ^ 6 = 1 := by
    have h := variableChange_c₆ (W := t.tateCurve) (C := D)
    rw [hD, Units.val_inv_eq_inv_val, inv_pow] at h
    have h' : t.tateCurve.c₆ * (D.u : k) ^ 6 = t.tateCurve.c₆ := by
      calc t.tateCurve.c₆ * (D.u : k) ^ 6
          = ((D.u : k) ^ 6)⁻¹ * t.tateCurve.c₆ * (D.u : k) ^ 6 := by rw [← h]
        _ = t.tateCurve.c₆ := by field_simp
    exact mul_left_cancel₀ hc₆ (h'.trans (mul_one _).symm)
  have hu2 : (D.u : k) * (D.u : k) = 1 := by
    have : (D.u : k) ^ 6 = (D.u : k) ^ 4 * ((D.u : k) * (D.u : k)) := by ring
    rw [hu6, hu4, one_mul] at this
    exact this.symm
  have hu : (D.u : k) = 1 ∨ (D.u : k) = -1 := mul_self_eq_one_iff.mp hu2
  -- the coefficient equations
  have e1 : (D.u : k)⁻¹ * (1 + 2 * D.s) = 1 := by
    have h := variableChange_a₁ (W := t.tateCurve) (C := D)
    rw [hD, t.tateCurve_a₁, Units.val_inv_eq_inv_val] at h
    exact h.symm
  have e2 : (D.u : k)⁻¹ ^ 2 * (0 - D.s * 1 + 3 * D.r - D.s ^ 2) = 0 := by
    have h := variableChange_a₂ (W := t.tateCurve) (C := D)
    rw [hD, t.tateCurve_a₂, t.tateCurve_a₁, Units.val_inv_eq_inv_val] at h
    exact h.symm
  have e3 : (D.u : k)⁻¹ ^ 3 * (0 + D.r * 1 + 2 * D.t) = 0 := by
    have h := variableChange_a₃ (W := t.tateCurve) (C := D)
    rw [hD, t.tateCurve_a₃, t.tateCurve_a₁, Units.val_inv_eq_inv_val] at h
    exact h.symm
  have hu' : (D.u : k)⁻¹ = (D.u : k) := inv_eq_of_mul_eq_one_right hu2
  rw [hu'] at e1 e2 e3
  have hs : D.s = ((D.u : k) - 1) / 2 := by
    have : (D.u : k) * ((D.u : k) * (1 + 2 * D.s)) = (D.u : k) * 1 := by rw [e1]
    rw [← mul_assoc, hu2, one_mul, mul_one] at this
    field_simp
    linear_combination this
  have hr : D.r = 0 := by
    have hpow : (D.u : k) ^ 2 ≠ 0 := pow_ne_zero _ hu0
    have h := (mul_eq_zero.mp e2).resolve_left hpow
    have h3r : 3 * D.r = 0 := by
      rcases hu with hu | hu
      · have hs0 : D.s = 0 := by rw [hs, hu]; norm_num
        rw [hs0] at h
        linear_combination h
      · have hs1 : D.s = -1 := by rw [hs, hu, div_eq_iff h2]; norm_num
        rw [hs1] at h
        linear_combination h
    exact (mul_eq_zero.mp h3r).resolve_left h3
  have ht : D.t = 0 := by
    have hpow : (D.u : k) ^ 3 ≠ 0 := pow_ne_zero _ hu0
    have h := (mul_eq_zero.mp e3).resolve_left hpow
    rw [hr] at h
    have : 2 * D.t = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h2
  rcases hu with hu | hu
  · left
    have hs0 : D.s = 0 := by rw [hs, hu]; norm_num
    ext
    · rw [hu]; rfl
    · rw [hr]; rfl
    · rw [hs0]; rfl
    · rw [ht]; rfl
  · right
    have hs1 : D.s = -1 := by rw [hs, hu, div_eq_iff h2]; norm_num
    ext
    · rw [hu]; rfl
    · rw [hr]; rfl
    · rw [hs1]; rfl
    · rw [ht]; rfl

end Aut

/-! ## Uniqueness up to sign -/

section Unique

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

variable {E : WeierstrassCurve k}

/-- `j` is compatible with equality of curves. -/
lemma j_congr {W W' : WeierstrassCurve k} [W.IsElliptic] [W'.IsElliptic] (h : W = W') :
    W.j = W'.j := by
  subst h
  rfl

namespace TateStructure

variable (S : TateStructure E)

lemma notMem_zpowers_iff (u : kˣ) :
    u ∉ Subgroup.zpowers S.t.q ↔ ∀ n : ℤ, (S.t.q : k) ^ n * (u : k) ≠ 1 := by
  constructor
  · intro hu n hn
    apply hu
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨-n, ?_⟩
    have h' : S.t.q ^ n * u = 1 := Units.ext (by simpa using hn)
    rw [zpow_neg]
    exact inv_eq_of_mul_eq_one_right h'
  · intro hu hmem
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨n, hn⟩ := hmem
    apply hu (-n)
    rw [← hn, Units.val_zpow_eq_zpow_val, zpow_neg,
      inv_mul_cancel₀ (zpow_ne_zero _ S.t.q.ne_zero)]

lemma ofUnit_ne_zero {u : kˣ} (hu : u ∉ Subgroup.zpowers S.t.q) : S.ofUnit u ≠ 0 := by
  intro h
  rw [← S.ofUnit_one, S.ofUnit_eq_iff] at h
  obtain ⟨n, hn⟩ := h
  apply hu
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨-n, ?_⟩
  rw [zpow_neg]
  exact inv_eq_of_mul_eq_one_right hn.symm

lemma ofUnit_eq_zero_of_mem {u : kˣ} (hu : u ∈ Subgroup.zpowers S.t.q) : S.ofUnit u = 0 := by
  rw [Subgroup.mem_zpowers_iff] at hu
  obtain ⟨n, rfl⟩ := hu
  rw [← S.ofUnit_one, S.ofUnit_eq_iff]
  exact ⟨-n, by rw [zpow_neg, inv_mul_cancel]⟩

variable [E.IsElliptic]

/-- **Uniqueness of the Tate parameter.** -/
theorem t_eq (S S' : TateStructure E) (h12 : (12 : k) ≠ 0) : S'.t = S.t := by
  apply TateParameter.tateJ_injective _ _ h12
  haveI := S.t.tateCurve_isElliptic h12
  haveI := S'.t.tateCurve_isElliptic h12
  rw [S.t.tateJ_eq_j h12, S'.t.tateJ_eq_j h12, ← j_congr S.hC, ← j_congr S'.hC,
    variableChange_j, variableChange_j]

/-- **Uniqueness of the Tate structure up to sign**: two Tate structures on `E` have point
maps agreeing up to a global sign. -/
theorem ofUnit_eq_or_neg (S S' : TateStructure E) (h12 : (12 : k) ≠ 0) :
    (∀ u, S'.ofUnit u = S.ofUnit u) ∨ (∀ u, S'.ofUnit u = -S.ofUnit u) := by
  have ht := S.t_eq S' h12
  set D := S'.C * S.C⁻¹ with hDdef
  have hC' : S'.C = D * S.C := by rw [hDdef, inv_mul_cancel_right]
  have hD : D • S.t.tateCurve = S.t.tateCurve := by
    rw [← S.hC, hDdef, mul_smul, inv_smul_smul, S'.hC, ht, S.hC]
  have hzero : ∀ u, u ∈ Subgroup.zpowers S.t.q → S'.ofUnit u = S.ofUnit u := by
    intro u hu
    rw [S.ofUnit_eq_zero_of_mem hu, S'.ofUnit_eq_zero_of_mem (by rw [ht]; exact hu)]
  have hX : ∀ u, u ∉ Subgroup.zpowers S.t.q →
      xCoord S'.C (S'.ofUnit u) = S.t.X u ∧ yCoord S'.C (S'.ofUnit u) = S.t.Y u := by
    intro u hu
    have hu' : ∀ n : ℤ, (S'.t.q : k) ^ n * (u : k) ≠ 1 := by
      rw [ht]
      exact (S.notMem_zpowers_iff u).mp hu
    have hx := S'.iso_x u hu'
    have hy := S'.iso_y u hu'
    constructor
    · rw [← ht]
      exact hx
    · rw [← ht]
      exact hy
  have hX' : ∀ u, u ∉ Subgroup.zpowers S.t.q →
      xCoord S.C (S.ofUnit u) = S.t.X u ∧ yCoord S.C (S.ofUnit u) = S.t.Y u := fun u hu =>
    ⟨S.iso_x u ((S.notMem_zpowers_iff u).mp hu), S.iso_y u ((S.notMem_zpowers_iff u).mp hu)⟩
  rcases eq_one_or_negChange_of_smul_tateCurve S.t h12 hD with hD1 | hDn
  · left
    intro u
    by_cases hu : u ∈ Subgroup.zpowers S.t.q
    · exact hzero u hu
    · rw [hD1, one_mul] at hC'
      obtain ⟨hx, hy⟩ := hX u hu
      obtain ⟨hx', hy'⟩ := hX' u hu
      rw [hC'] at hx hy
      exact eq_of_coords S.C (S'.ofUnit_ne_zero (by rw [ht]; exact hu)) (S.ofUnit_ne_zero hu)
        (hx.trans hx'.symm) (hy.trans hy'.symm)
  · right
    intro u
    by_cases hu : u ∈ Subgroup.zpowers S.t.q
    · rw [hzero u hu, S.ofUnit_eq_zero_of_mem hu, neg_zero]
    · rw [hDn] at hC'
      obtain ⟨hx, hy⟩ := hX u hu
      obtain ⟨hx', hy'⟩ := hX' u hu
      have hne' : S'.ofUnit u ≠ 0 := S'.ofUnit_ne_zero (by rw [ht]; exact hu)
      have hne : S.ofUnit u ≠ 0 := S.ofUnit_ne_zero hu
      rw [hC', xCoord_mul _ _ hne', vcX_negChange] at hx
      rw [hC', yCoord_mul _ _ hne', vcY_negChange, hx] at hy
      refine eq_of_coords S.C hne' (neg_ne_zero.mpr hne) ?_ ?_
      · rw [xCoord_neg, hx, hx']
      · rw [yCoord_neg _ hne, hx', hy']
        have hnegY : (S.C • E).toAffine.negY (S.t.X u) (S.t.Y u) = -S.t.Y u - S.t.X u := by
          unfold Affine.negY
          rw [S.hC, S.t.tateCurve_a₁, S.t.tateCurve_a₃]
          ring
        rw [hnegY]
        linear_combination -hy

/-- The graph line does not depend on the Tate structure. -/
theorem graphLine_eq (S S' : TateStructure E) (h12 : (12 : k) ≠ 0) (ℓ : ℕ) :
    S'.graphLine ℓ = S.graphLine ℓ := by
  have ht := S.t_eq S' h12
  ext P
  simp only [mem_graphLine_iff]
  rcases S.ofUnit_eq_or_neg S' h12 with h | h
  · simp only [h]
  · constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u⁻¹, by rw [inv_pow, hu, inv_one], by rw [h, S.ofUnit_inv]⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u⁻¹, by rw [inv_pow, hu, inv_one], by rw [h, S.ofUnit_inv, neg_neg]⟩

/-- The canonical generators do not depend on the Tate structure. -/
theorem isCanonical_congr (S S' : TateStructure E) (h12 : (12 : k) ≠ 0) (ℓ : ℕ)
    (P : E.toAffine.Point) : S'.IsCanonical ℓ P ↔ S.IsCanonical ℓ P := by
  have ht := S.t_eq S' h12
  unfold IsCanonical
  rw [ht]
  have hneg : ∀ m : ℤ, -(1 + (ℓ : ℤ) * m) = -1 + ℓ * -m := fun m => by ring
  have hneg' : ∀ m : ℤ, -(-1 + (ℓ : ℤ) * m) = 1 + ℓ * -m := fun m => by ring
  rcases S.ofUnit_eq_or_neg S' h12 with h | h
  · simp only [h]
  · constructor
    · rintro ⟨u, hu, m, hm⟩
      refine ⟨u⁻¹, by rw [S.ofUnit_inv, ← h, hu], -m, ?_⟩
      rw [inv_pow]
      rcases hm with hm | hm
      · right
        rw [hm, ← zpow_neg, hneg]
      · left
        rw [hm, ← zpow_neg, hneg']
    · rintro ⟨u, hu, m, hm⟩
      refine ⟨u⁻¹, by rw [h, S.ofUnit_inv, hu, neg_neg], -m, ?_⟩
      rw [inv_pow]
      rcases hm with hm | hm
      · right
        rw [hm, ← zpow_neg, hneg]
      · left
        rw [hm, ← zpow_neg, hneg']

end TateStructure

end Unique

end

end Iut
