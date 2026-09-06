/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.Residual

/-!
# The ramification bound (R4) of IUT IV, Theorem 1.10

* `Iut.finrank_torsionField_le`: `[K : F] ≤ |GL₂(𝔽_ℓ)| = (ℓ² − 1)(ℓ² − ℓ)`, from the Galois
  correspondence: `K` is the fixed field of the (open, hence closed) kernel of the mod-`ℓ`
  representation, so `[K : F]` is the index of the kernel, the order of the image.
* `Iut.ramIdx_bound_of_facts`, **(R4)**: for a finite place `v` of `K` with `e_v > p_v − 2`,
  `p_v ≤ 552960·d_mod·ℓ` and `log e_v ≤ −3 + 4·log(552960·d_mod·ℓ)`. Away from `2·3·5·ℓ`,
  `e_v = e_u·e(v/u) ≤ [F_tpd : ℚ]·30ℓ ≤ 180·d_mod·ℓ` (the ramification bound of
  `TowerLocalFacts`, `[F_tpd : F_mod] ≤ 6`); at `p ∈ {2, 3, 5, ℓ}` the first bound is
  trivial. The second uses only `e_v ≤ [K : ℚ] ≤ |GL₂(𝔽_ℓ)|·[F : ℚ]` and
  `[F : ℚ] ≤ 552960·[F_tpd : ℚ] ≤ 552960·6·d_mod`.
-/

namespace Iut

open NumberField IsDedekindDomain

universe u

section Degree

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable (Pr : AdmissiblePrimeData F E Fbar VBad)

/-- `|GL₂(𝔽_ℓ)| = (ℓ² − 1)(ℓ² − ℓ)` for `ℓ` prime. -/
lemma card_GL_two_of_prime (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod ℓ)) = (ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
  simp

/-- **`[K : F] ≤ |GL₂(𝔽_ℓ)|`**: the torsion field is the fixed field of the kernel of the
mod-`ℓ` representation, whose index is the order of the image. -/
theorem finrank_torsionField_le :
    Module.finrank F ↥Pr.torsionField ≤ (Pr.ℓ ^ 2 - 1) * (Pr.ℓ ^ 2 - Pr.ℓ) := by
  let H : ClosedSubgroup (Fbar ≃ₐ[F] Fbar) :=
    ⟨Pr.rep.ker, Subgroup.isClosed_of_isOpen _ Pr.ker_isOpen⟩
  have h1 : Module.finrank F ↥Pr.torsionField = Pr.rep.ker.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index]
    change (IntermediateField.fixedField H.1).fixingSubgroup.index = H.1.index
    rw [InfiniteGalois.fixingSubgroup_fixedField H]
  haveI : NeZero Pr.ℓ := ⟨Pr.ℓ_prime.ne_zero⟩
  rw [h1, Subgroup.index_ker, ← card_GL_two_of_prime Pr.ℓ Pr.ℓ_prime]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-- `(ℓ² − 1)(ℓ² − ℓ) ≤ ℓ⁴`. -/
lemma card_GL_two_le (ℓ : ℕ) : (ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ) ≤ ℓ ^ 4 := by
  calc (ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ) ≤ ℓ ^ 2 * ℓ ^ 2 :=
        Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    _ = ℓ ^ 4 := by ring

end Degree

/-! ### (R4) -/

section R4

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable {Pr : AdmissiblePrimeData F E Fbar VBad} [NumberField ↥Pr.torsionField]

/-- `2 ≤ log 552960`. -/
lemma two_le_log_552960 : (2 : ℝ) ≤ Real.log 552960 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h2]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

/-- `log 6 ≤ 2`. -/
lemma log_six_le_two : Real.log 6 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h2]
  nlinarith

/-- **(R4)** from the local facts and the degree bounds `[F_tpd : F_mod] ≤ 6`,
`[F : ℚ] ≤ 552960·[F_tpd : ℚ]`. -/
theorem ramIdx_bound_of_facts (H : TowerLocalFacts E VBad Pr)
    (h6 : Module.finrank ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) ≤ 6)
    (hF : Module.finrank ℚ F ≤ 552960 * Module.finrank ℚ ↥(tripodalFieldOf F E))
    (v : FinitePlace ↥Pr.torsionField) (hv : residueChar v - 2 < ramIdx (↥Pr.torsionField) v) :
    residueChar v ≤ 552960 * Module.finrank ℚ ↥(fieldOfModuli F E) * Pr.ℓ ∧
      Real.log (ramIdx (↥Pr.torsionField) v) ≤
        -3 + 4 * Real.log (((552960 * Module.finrank ℚ ↥(fieldOfModuli F E) : ℕ) : ℝ) * Pr.ℓ) := by
  set d := Module.finrank ℚ ↥(fieldOfModuli F E) with hd
  set ℓ := Pr.ℓ with hℓ
  have hd1 : 1 ≤ d := Module.finrank_pos
  have hℓ5 : 5 ≤ ℓ := Pr.five_le
  have hT : Module.finrank ℚ ↥(tripodalFieldOf F E) ≤ 6 * d := by
    rw [finrank_tripodal_eq_mul F E]
    calc d * Module.finrank ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) ≤ d * 6 :=
          Nat.mul_le_mul_left _ h6
      _ = 6 * d := mul_comm _ _
  constructor
  · by_cases hp : residueChar v ∈ ({2, 3, 5, ℓ} : Finset ℕ)
    · have : residueChar v ≤ ℓ := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        omega
      calc residueChar v ≤ ℓ := this
        _ ≤ 552960 * d * ℓ := Nat.le_mul_of_pos_left _ (by positivity)
    · have h1 := H.relRamIdx_le v hp
      have h2 := ramIdx_eq_ramIdx_placeTpd_mul (F := F) (E := E) v
      have h3 := ramIdx_le_finrank (placeTpd F E Pr.torsionField v)
      have h4 : ramIdx (↥Pr.torsionField) v ≤ 6 * d * (30 * ℓ) := by
        rw [h2]
        exact Nat.mul_le_mul (h3.trans hT) h1
      have h5 : residueChar v < ramIdx (↥Pr.torsionField) v + 2 := by omega
      nlinarith
  · have hK : Module.finrank ℚ ↥Pr.torsionField ≤ ℓ ^ 4 * (552960 * (6 * d)) := by
      rw [← Module.finrank_mul_finrank ℚ F ↥Pr.torsionField]
      calc Module.finrank ℚ F * Module.finrank F ↥Pr.torsionField
          ≤ (552960 * (6 * d)) * ℓ ^ 4 :=
            Nat.mul_le_mul (hF.trans (Nat.mul_le_mul_left _ hT))
              ((finrank_torsionField_le Pr).trans (card_GL_two_le ℓ))
        _ = ℓ ^ 4 * (552960 * (6 * d)) := mul_comm _ _
    have he : ramIdx (↥Pr.torsionField) v ≤ ℓ ^ 4 * (552960 * (6 * d)) :=
      (ramIdx_le_finrank v).trans hK
    have hepos : (0 : ℝ) < ramIdx (↥Pr.torsionField) v := by exact_mod_cast ramIdx_pos' v
    have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    have hlog1 : Real.log (ramIdx (↥Pr.torsionField) v) ≤
        4 * Real.log ℓ + (Real.log 6 + Real.log (552960 * d)) := by
      calc Real.log (ramIdx (↥Pr.torsionField) v)
          ≤ Real.log ((ℓ : ℝ) ^ 4 * (552960 * (6 * d))) := by
            apply Real.log_le_log hepos
            exact_mod_cast he
        _ = 4 * Real.log ℓ + (Real.log 6 + Real.log (552960 * d)) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
              show (552960 * (6 * d) : ℝ) = 6 * (552960 * d) by ring,
              Real.log_mul (by norm_num) (by positivity)]
            push_cast
            ring
    have hlog2 : (2 : ℝ) ≤ Real.log (552960 * d) := by
      refine two_le_log_552960.trans (Real.log_le_log (by norm_num) ?_)
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      nlinarith
    have hlog3 := log_six_le_two
    have hsplit : Real.log (((552960 * d : ℕ) : ℝ) * ℓ) = Real.log (552960 * d) + Real.log ℓ := by
      rw [Real.log_mul (by positivity) (by positivity)]
      push_cast
      ring
    rw [hsplit]
    linarith

end R4

end Iut
