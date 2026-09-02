/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib

/-!
# Transitivity of `SL₂(𝔽_ℓ)` on lines with a marked generator of the quotient

The linear algebra behind the existence of the data `V` and `ε` of initial Θ-data
(IUT IV, proof of Corollary 2.2: "the crucial existence of data `V` and `ε` … follows … as
a consequence of the fact that the Galois action on ℓ-torsion points contains the full
special linear group"): for lines `L, M ⊆ 𝔽_ℓ²` and vectors `g ∉ L`, `q ∉ M`, there is
`A ∈ SL₂(𝔽_ℓ)` with `A·L = M` and `A·g ≡ q (mod M)` (`Iut.Anabelian.exists_sl2`).
-/

namespace Iut.Anabelian

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- Multiplication by a matrix, as an additive homomorphism of `𝔽_ℓ²`. -/
def mulVecHom (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) : (Fin 2 → ZMod ℓ) →+ (Fin 2 → ZMod ℓ) :=
  (Matrix.mulVecLin A).toAddMonoidHom

@[simp] lemma mulVecHom_apply (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (v : Fin 2 → ZMod ℓ) :
    mulVecHom A v = A.mulVec v := rfl

lemma nsmul_self_eq_zero (v : Fin 2 → ZMod ℓ) : ℓ • v = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul]

lemma addOrderOf_eq_of_ne_zero {v : Fin 2 → ZMod ℓ} (hv : v ≠ 0) : addOrderOf v = ℓ :=
  addOrderOf_eq_prime (nsmul_self_eq_zero v) hv

lemma card_zmultiples_of_ne_zero {v : Fin 2 → ZMod ℓ} (hv : v ≠ 0) :
    Nat.card (AddSubgroup.zmultiples v) = ℓ := by
  rw [Nat.card_zmultiples, addOrderOf_eq_of_ne_zero hv]

/-- A nonzero element of a subgroup of order `ℓ` generates it. -/
lemma eq_zmultiples_of_card {L : AddSubgroup (Fin 2 → ZMod ℓ)} (hL : Nat.card L = ℓ)
    {v : Fin 2 → ZMod ℓ} (hv : v ∈ L) (hv0 : v ≠ 0) : L = AddSubgroup.zmultiples v := by
  have hle : AddSubgroup.zmultiples v ≤ L := (AddSubgroup.zmultiples_le).mpr hv
  haveI : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; exact hℓ.out.ne_zero)
  exact (AddSubgroup.eq_of_le_of_card_ge hle (by rw [hL, card_zmultiples_of_ne_zero hv0])).symm

/-- A subgroup of order `ℓ` has a nonzero element. -/
lemma exists_ne_zero_of_card {L : AddSubgroup (Fin 2 → ZMod ℓ)} (hL : Nat.card L = ℓ) :
    ∃ v ∈ L, v ≠ 0 := by
  by_contra h
  push_neg at h
  have hbot : L = ⊥ := (AddSubgroup.eq_bot_iff_forall L).mpr h
  rw [hbot, AddSubgroup.card_bot] at hL
  exact hℓ.out.one_lt.ne hL

/-- Scalar multiples lie in the subgroup generated. -/
lemma smul_mem_zmultiples (c : ZMod ℓ) (v : Fin 2 → ZMod ℓ) :
    c • v ∈ AddSubgroup.zmultiples v := by
  rw [← ZMod.intCast_zmod_cast c, Int.cast_smul_eq_zsmul]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨_, rfl⟩

/-- Two vectors with vanishing determinant are dependent. -/
lemma mem_zmultiples_of_det_eq_zero {l g : Fin 2 → ZMod ℓ} (hl : l ≠ 0)
    (h : l 0 * g 1 - l 1 * g 0 = 0) : g ∈ AddSubgroup.zmultiples l := by
  by_cases h0 : l 0 = 0
  · have h1 : l 1 ≠ 0 := by
      intro h1
      apply hl
      ext i
      fin_cases i <;> simp [h0, h1]
    have hg0 : g 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h1
    have : g = (g 1 / l 1) • l := by
      ext i
      fin_cases i
      · simp [h0, hg0]
      · simp [div_mul_cancel₀ _ h1]
    rw [this]
    exact smul_mem_zmultiples _ _
  · have : g = (g 0 / l 0) • l := by
      ext i
      fin_cases i
      · simp [div_mul_cancel₀ _ h0]
      · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
        field_simp
        linear_combination h
    rw [this]
    exact smul_mem_zmultiples _ _

/-- **Transitivity of `SL₂(𝔽_ℓ)`**: for lines `L, M` and `g ∉ L`, `q ∉ M`, some
`A ∈ SL₂(𝔽_ℓ)` maps `L` onto `M` and `g` to `q` modulo `M`. -/
theorem exists_sl2 (L M : AddSubgroup (Fin 2 → ZMod ℓ)) (hL : Nat.card L = ℓ)
    (hM : Nat.card M = ℓ) {g q : Fin 2 → ZMod ℓ} (hg : g ∉ L) (hq : q ∉ M) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ),
      L.map (mulVecHom A) = M ∧ (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).mulVec g - q ∈ M := by
  obtain ⟨l, hlL, hl0⟩ := exists_ne_zero_of_card hL
  obtain ⟨m, hmM, hm0⟩ := exists_ne_zero_of_card hM
  have hLl : L = AddSubgroup.zmultiples l := eq_zmultiples_of_card hL hlL hl0
  have hMm : M = AddSubgroup.zmultiples m := eq_zmultiples_of_card hM hmM hm0
  have hd₁ : l 0 * g 1 - l 1 * g 0 ≠ 0 := fun h =>
    hg (hLl ▸ mem_zmultiples_of_det_eq_zero hl0 h)
  have hd₂ : m 0 * q 1 - m 1 * q 0 ≠ 0 := fun h =>
    hq (hMm ▸ mem_zmultiples_of_det_eq_zero hm0 h)
  set c : ZMod ℓ := (l 0 * g 1 - l 1 * g 0) / (m 0 * q 1 - m 1 * q 0) with hc
  have hc0 : c ≠ 0 := div_ne_zero hd₁ hd₂
  set B₁ : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := !![l 0, g 0; l 1, g 1] with hB₁
  set B₂ : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := !![c * m 0, q 0; c * m 1, q 1] with hB₂
  have hdet₁ : B₁.det = l 0 * g 1 - l 1 * g 0 := by
    rw [hB₁, Matrix.det_fin_two_of]; ring
  have hdet₂ : B₂.det = c * (m 0 * q 1 - m 1 * q 0) := by
    rw [hB₂, Matrix.det_fin_two_of]; ring
  have hunit : IsUnit B₁.det := isUnit_iff_ne_zero.mpr (hdet₁ ▸ hd₁)
  set A : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := B₂ * B₁⁻¹ with hA
  have hdet : A.det = 1 := by
    rw [hA, Matrix.det_mul, Matrix.det_nonsing_inv, hdet₂, hdet₁, Ring.inverse_eq_inv', hc]
    field_simp
  have hAB : A * B₁ = B₂ := by
    rw [hA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
  have hB₁l : B₁.mulVec (Pi.single 0 1) = l := by
    ext i; fin_cases i <;> simp [hB₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hB₁g : B₁.mulVec (Pi.single 1 1) = g := by
    ext i; fin_cases i <;> simp [hB₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hB₂m : B₂.mulVec (Pi.single 0 1) = c • m := by
    ext i; fin_cases i <;> simp [hB₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hB₂q : B₂.mulVec (Pi.single 1 1) = q := by
    ext i; fin_cases i <;> simp [hB₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hAl : A.mulVec l = c • m := by
    rw [← hB₁l, Matrix.mulVec_mulVec, hAB, hB₂m]
  have hAg : A.mulVec g = q := by
    rw [← hB₁g, Matrix.mulVec_mulVec, hAB, hB₂q]
  refine ⟨⟨A, hdet⟩, ?_, ?_⟩
  · have hcm : c • m ∈ M := hMm ▸ smul_mem_zmultiples c m
    have hcm0 : c • m ≠ 0 := smul_ne_zero hc0 hm0
    rw [hLl, AddMonoidHom.map_zmultiples, mulVecHom_apply, Matrix.SpecialLinearGroup.coe_mk,
      hAl]
    exact (eq_zmultiples_of_card hM hcm hcm0).symm
  · rw [Matrix.SpecialLinearGroup.coe_mk, hAg, sub_self]
    exact M.zero_mem

end Iut.Anabelian
