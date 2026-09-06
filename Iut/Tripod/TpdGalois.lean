/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.Residual
import Iut.Tripod.CurveFacts

/-!
# `ℚ(λ)/ℚ(j)` is Galois of degree at most `6`

For the curve `E_λ/F_λ` of a point `λ` of the tripod, the tripodal field is
`F_tpd = ℚ(λ)` (`Iut.Tripod.tripodalFieldOf_eq`) and the field of moduli is
`F_mod = ℚ(j)`, `j = 256(λ² − λ + 1)³/(λ²(λ − 1)²)`. Over `ℚ(j)`, `λ` is a root of the sextic

  `S(X) = 256(X² − X + 1)³ − j·X²(X − 1)²`,

whose roots in `F_λ` are the six values `λ, 1 − λ, 1/λ, 1/(1 − λ), λ/(λ − 1), (λ − 1)/λ`
(`Iut.Tripod.sext_map_eq`: `S = 256·∏(X − r)` over these), all in `ℚ(λ)`. Hence `ℚ(λ)` is
the splitting field of `S` over `ℚ(j)`, so `ℚ(λ)/ℚ(j)` is Galois (`Iut.Tripod.isGalois_tpd`)
of degree `≤ deg S = 6` (`Iut.Tripod.finrank_tpd_le_six`) — the two facts about
`F_tpd/F_mod` consumed by the tower arithmetic (`Iut.towerArithmetic_of_localFacts`).
-/

namespace Iut.Tripod

open NumberField Polynomial WeierstrassCurve

open scoped IntermediateField

variable (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)

/-- `F_mod = ℚ(j)` of the curve of `x`, as an intermediate field of `F_λ`. -/
noncomputable abbrev modC : IntermediateField ℚ (curveOf x h3 h5).F :=
  fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E

/-- `F_tpd = ℚ(λ)` of the curve of `x`, as an intermediate field of `F_λ`. -/
noncomputable abbrev tpdC : IntermediateField ℚ (curveOf x h3 h5).F :=
  tripodalFieldOf (curveOf x h3 h5).F (curveOf x h3 h5).E

/-- `j ∈ F_mod`. -/
theorem j_mem_modC : (curveOf x h3 h5).E.j ∈ modC x h3 h5 :=
  IntermediateField.mem_adjoin_simple_self ℚ _

/-- `j` as an element of `F_mod`. -/
noncomputable def jC : modC x h3 h5 := ⟨_, j_mem_modC x h3 h5⟩

@[simp] theorem coe_jC : (jC x h3 h5 : (curveOf x h3 h5).F) = (curveOf x h3 h5).E.j := rfl

/-- **The sextic** `S(X) = 256(X² − X + 1)³ − j·X²(X − 1)² ∈ F_mod[X]`. -/
noncomputable def sext : (modC x h3 h5)[X] :=
  C 256 * (X ^ 2 - X + 1) ^ 3 - C (jC x h3 h5) * (X ^ 2 * (X - 1) ^ 2)

theorem natDegree_sext : (sext x h3 h5).natDegree = 6 := by
  unfold sext
  compute_degree!

theorem sext_ne_zero : sext x h3 h5 ≠ 0 := by
  intro h
  have := natDegree_sext x h3 h5
  rw [h, natDegree_zero] at this
  omega

/-- `S(r) = 256(r² − r + 1)³ − j·r²(r − 1)²`. -/
theorem aeval_sext (r : (curveOf x h3 h5).F) :
    aeval r (sext x h3 h5) =
      256 * (r ^ 2 - r + 1) ^ 3 - (curveOf x h3 h5).E.j * (r ^ 2 * (r - 1) ^ 2) := by
  simp only [sext, map_sub, map_mul, map_pow, map_add, aeval_C, aeval_X, map_one]
  rw [map_ofNat, IntermediateField.algebraMap_apply, coe_jC]

section Lambda

/-- The hypotheses `λ ≠ 0`, `λ ≠ 1` on `genC`. -/
theorem genC_ne_zero : genC x h3 h5 ≠ 0 := gen'_ne_zero x.2.1

theorem genC_ne_one : genC x h3 h5 ≠ 1 := gen'_ne_one x.2.2

/-- `j = 256(λ² − λ + 1)³/(λ²(λ − 1)²)`. -/
theorem j_eq : (curveOf x h3 h5).E.j = 256 * (genC x h3 h5 ^ 2 - genC x h3 h5 + 1) ^ 3 /
    (genC x h3 h5 ^ 2 * (genC x h3 h5 - 1) ^ 2) := by
  haveI : (legendre (genC x h3 h5)).IsElliptic := (curveOf x h3 h5).isElliptic
  exact legendre_j (l := genC x h3 h5)

/-- `S(λ) = 0`. -/
theorem aeval_genC_sext : aeval (genC x h3 h5) (sext x h3 h5) = 0 := by
  have h0 := genC_ne_zero x h3 h5
  have h1 : genC x h3 h5 - 1 ≠ 0 := sub_ne_zero.mpr (genC_ne_one x h3 h5)
  rw [aeval_sext, j_eq, div_mul_cancel₀ _ (by positivity), sub_self]

/-- **The factorization of the sextic** over `F_λ`:
`S = 256·(X − λ)(X − (1 − λ))(X − λ⁻¹)(X − (1 − λ)⁻¹)(X − λ/(λ − 1))(X − (λ − 1)/λ)`. -/
theorem sext_map_eq :
    (sext x h3 h5).map (algebraMap (modC x h3 h5) (curveOf x h3 h5).F) =
      C 256 * ((X - C (genC x h3 h5)) * (X - C (1 - genC x h3 h5)) *
        (X - C (genC x h3 h5)⁻¹) * (X - C (1 - genC x h3 h5)⁻¹) *
        (X - C (genC x h3 h5 / (genC x h3 h5 - 1))) *
        (X - C ((genC x h3 h5 - 1) / genC x h3 h5))) := by
  set l := genC x h3 h5 with hl
  have h0 : l ≠ 0 := genC_ne_zero x h3 h5
  have h1 : l - 1 ≠ 0 := sub_ne_zero.mpr (genC_ne_one x h3 h5)
  have h1' : 1 - l ≠ 0 := by
    intro h
    exact h1 (by rw [← neg_sub, h, neg_zero])
  apply Polynomial.funext
  intro t
  rw [eval_map, ← aeval_def, aeval_sext, j_eq]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  rw [← hl]
  field_simp
  ring

/-- The roots of the sextic in `F_λ` lie in `ℚ(λ)`. -/
theorem mem_adjoin_of_aeval_sext_eq_zero (r : (curveOf x h3 h5).F)
    (hr : aeval r (sext x h3 h5) = 0) : r ∈ ℚ⟮genC x h3 h5⟯ := by
  set l := genC x h3 h5 with hl
  have h0 : l ≠ 0 := genC_ne_zero x h3 h5
  have h1 : l - 1 ≠ 0 := sub_ne_zero.mpr (genC_ne_one x h3 h5)
  have h1' : 1 - l ≠ 0 := by
    intro h
    exact h1 (by rw [← neg_sub, h, neg_zero])
  have hl : l ∈ ℚ⟮l⟯ := IntermediateField.mem_adjoin_simple_self ℚ l
  have h := hr
  rw [aeval_def, ← eval_map, sext_map_eq] at h
  simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at h
  rcases h with (h | ((((h | h) | h) | h) | h) | h)
  · exact absurd h (by norm_num)
  · rw [h]; exact hl
  · rw [h]; exact sub_mem (one_mem _) hl
  · rw [h]; exact inv_mem hl
  · rw [h]; exact inv_mem (sub_mem (one_mem _) hl)
  · rw [h]; exact div_mem hl (sub_mem hl (one_mem _))
  · rw [h]; exact div_mem (sub_mem hl (one_mem _)) hl

end Lambda

/-! ### The splitting field -/

section Galois

/-- `F_mod ⊆ ℚ(λ)`. -/
theorem modC_le : modC x h3 h5 ≤ ℚ⟮genC x h3 h5⟯ := fieldOfModuli_le x h3 h5

/-- `t ∈ F_mod(λ) ↔ t ∈ ℚ(λ)`. -/
theorem mem_adjoin_modC_iff (t : (curveOf x h3 h5).F) :
    t ∈ (modC x h3 h5)⟮genC x h3 h5⟯ ↔ t ∈ ℚ⟮genC x h3 h5⟯ := by
  constructor
  · intro ht
    have hle : (modC x h3 h5)⟮genC x h3 h5⟯ ≤ IntermediateField.extendScalars (modC_le x h3 h5) :=
      IntermediateField.adjoin_simple_le_iff.mpr
        ((IntermediateField.mem_extendScalars (modC_le x h3 h5)).mpr
          (IntermediateField.mem_adjoin_simple_self ℚ _))
    exact (IntermediateField.mem_extendScalars (modC_le x h3 h5)).mp (hle ht)
  · intro ht
    have hle : ℚ⟮genC x h3 h5⟯ ≤ ((modC x h3 h5)⟮genC x h3 h5⟯).restrictScalars ℚ :=
      IntermediateField.adjoin_simple_le_iff.mpr
        ((IntermediateField.mem_restrictScalars ℚ).mpr
          (IntermediateField.mem_adjoin_simple_self (modC x h3 h5) _))
    exact (IntermediateField.mem_restrictScalars ℚ).mp (hle ht)

/-- `t ∈ F_tpd ↔ t ∈ ℚ(λ)`. -/
theorem mem_tpdC_iff (t : (curveOf x h3 h5).F) :
    t ∈ tpdC x h3 h5 ↔ t ∈ ℚ⟮genC x h3 h5⟯ := by
  unfold tpdC
  rw [tripodalFieldOf_eq]

/-- **`F_tpd ≃ F_mod(λ)`** as `F_mod`-algebras. -/
noncomputable def tpdEquivAdjoinMod :
    ↥(tpdC x h3 h5) ≃ₐ[modC x h3 h5] ↥((modC x h3 h5)⟮genC x h3 h5⟯) where
  toFun t := ⟨t.1, (mem_adjoin_modC_iff x h3 h5 _).mpr ((mem_tpdC_iff x h3 h5 _).mp t.2)⟩
  invFun s := ⟨s.1, (mem_tpdC_iff x h3 h5 _).mpr ((mem_adjoin_modC_iff x h3 h5 _).mp s.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The sextic splits over `F_λ`. -/
theorem sext_map_splits :
    ((sext x h3 h5).map (algebraMap (modC x h3 h5) (curveOf x h3 h5).F)).Splits := by
  rw [sext_map_eq]
  exact (((((Splits.X_sub_C _).mul (Splits.X_sub_C _)).mul (Splits.X_sub_C _)).mul
    (Splits.X_sub_C _)).mul (Splits.X_sub_C _)).mul (Splits.X_sub_C _) |>.C_mul _

/-- `F_mod(roots of S) = F_mod(λ)`. -/
theorem adjoin_rootSet_sext_eq :
    IntermediateField.adjoin (modC x h3 h5) ((sext x h3 h5).rootSet (curveOf x h3 h5).F) =
      (modC x h3 h5)⟮genC x h3 h5⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro r hr
    rw [mem_rootSet] at hr
    exact (mem_adjoin_modC_iff x h3 h5 r).mpr (mem_adjoin_of_aeval_sext_eq_zero x h3 h5 r hr.2)
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin _ _
      (mem_rootSet.mpr ⟨sext_ne_zero x h3 h5, aeval_genC_sext x h3 h5⟩)

/-- **`ℚ(λ)/ℚ(j)` is Galois**: `F_tpd/F_mod` is the splitting field of the sextic. -/
theorem isGalois_tpd : IsGalois (modC x h3 h5) (tpdC x h3 h5) := by
  haveI : IsSplittingField (modC x h3 h5)
      (IntermediateField.adjoin (modC x h3 h5) ((sext x h3 h5).rootSet (curveOf x h3 h5).F))
      (sext x h3 h5) :=
    IntermediateField.adjoin_rootSet_isSplittingField (sext_map_splits x h3 h5)
  haveI : Normal (modC x h3 h5)
      (IntermediateField.adjoin (modC x h3 h5) ((sext x h3 h5).rootSet (curveOf x h3 h5).F)) :=
    Normal.of_isSplittingField (sext x h3 h5)
  haveI : IsGalois (modC x h3 h5)
      (IntermediateField.adjoin (modC x h3 h5) ((sext x h3 h5).rootSet (curveOf x h3 h5).F)) :=
    ⟨⟩
  rw [adjoin_rootSet_sext_eq] at this
  exact IsGalois.of_algEquiv (tpdEquivAdjoinMod x h3 h5).symm

/-- **`[ℚ(λ) : ℚ(j)] ≤ 6`**. -/
theorem finrank_tpd_le_six :
    Module.finrank (modC x h3 h5) (tpdC x h3 h5) ≤ 6 := by
  haveI : Module.Finite (modC x h3 h5) (curveOf x h3 h5).F :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  have hint : IsIntegral (modC x h3 h5) (genC x h3 h5) := IsIntegral.of_finite _ _
  rw [(tpdEquivAdjoinMod x h3 h5).toLinearEquiv.finrank_eq, IntermediateField.adjoin.finrank hint]
  exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ (aeval_genC_sext x h3 h5))
    (sext_ne_zero x h3 h5)).trans (natDegree_sext x h3 h5).le

end Galois

end Iut.Tripod
