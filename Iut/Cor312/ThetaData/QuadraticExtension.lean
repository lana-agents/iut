/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.PlacesOver
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Quadratic extensions `K(√d)` inside `F̄`

For a number field `K ⊆ F̄` (an intermediate field of an algebraic closure `F̄` of `F`) and
`d ∈ K`, the field `K(√d) ⊆ F̄` obtained by adjoining a chosen square root of `d` in `F̄`:

* `Iut.sqrtField K d : IntermediateField ↥K Fbar` — the field `K(√d)`, a number field
  (`Iut.instNumberFieldSqrtField`), of degree `≤ 2` over `K` (`Iut.sqrtField_finrank_le`);
* `Iut.sqrtD K d : ↥(sqrtField K d)` — the chosen square root, `Iut.sqrtD_sq`;
* `Iut.conj K d hd : K(√d) ≃ₐ[K] K(√d)` — for `d` **not a square** in `K`, the conjugation
  `√d ↦ -√d` (`Iut.conj_sqrtD`), an involution (`Iut.conj_conj`) fixing exactly `K`
  (`Iut.eq_algebraMap_of_conj_eq`);
* `Iut.exists_sq_eq_of_isSquare` — the trivial case `d` a square in `K`.
-/

namespace Iut

open NumberField Polynomial

variable {F : Type*} [Field F]
variable {Fbar : Type*} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar)

/-! ### The polynomial `X² − d` -/

/-- The polynomial `X² − d` over `K`. -/
noncomputable abbrev sqrtPoly (d : ↥K) : (↥K)[X] := X ^ 2 - C d

lemma sqrtPoly_monic (d : ↥K) : (sqrtPoly K d).Monic := monic_X_pow_sub_C d two_ne_zero

lemma sqrtPoly_natDegree (d : ↥K) : (sqrtPoly K d).natDegree = 2 := natDegree_X_pow_sub_C

lemma sqrtPoly_ne_zero (d : ↥K) : sqrtPoly K d ≠ 0 := X_pow_sub_C_ne_zero two_pos d

/-- The trivial case: if `d` is a square in `K` then it has a square root in `K`. -/
theorem exists_sq_eq_of_isSquare {d : ↥K} (hd : IsSquare d) : ∃ y : ↥K, y ^ 2 = d := by
  obtain ⟨r, hr⟩ := hd
  exact ⟨r, by rw [sq, hr]⟩

lemma ne_zero_of_not_isSquare {d : ↥K} (hd : ¬ IsSquare d) : d ≠ 0 := by
  rintro rfl
  exact hd ⟨0, by simp⟩

/-- `X² − d` is irreducible over `K` when `d` is not a square in `K`. -/
theorem sqrtPoly_irreducible {d : ↥K} (hd : ¬ IsSquare d) : Irreducible (sqrtPoly K d) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [sqrtPoly_natDegree]; decide
  · intro x hx
    apply hd
    refine ⟨x, ?_⟩
    have : x ^ 2 - d = 0 := by simpa [sqrtPoly] using hx
    rw [← sq, eq_comm, ← sub_eq_zero]
    exact this

/-! ### The chosen square root and the field `K(√d)` -/

variable [IsAlgClosure F Fbar]

/-- A chosen square root in `F̄` of `d ∈ K`. -/
noncomputable def sqrtRoot (d : ↥K) : Fbar :=
  haveI : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed F
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (algebraMap ↥K Fbar d) two_pos)

lemma sqrtRoot_sq (d : ↥K) : sqrtRoot K d ^ 2 = algebraMap ↥K Fbar d :=
  haveI : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed F
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (algebraMap ↥K Fbar d) two_pos)

lemma aeval_sqrtRoot (d : ↥K) : aeval (sqrtRoot K d) (sqrtPoly K d) = 0 := by
  simp [sqrtPoly, sqrtRoot_sq]

lemma sqrtRoot_isIntegral (d : ↥K) : IsIntegral ↥K (sqrtRoot K d) :=
  ⟨sqrtPoly K d, sqrtPoly_monic K d, by simpa [aeval_def] using aeval_sqrtRoot K d⟩

lemma minpoly_sqrtRoot_dvd (d : ↥K) : minpoly ↥K (sqrtRoot K d) ∣ sqrtPoly K d :=
  minpoly.dvd _ _ (aeval_sqrtRoot K d)

/-- The field `K(√d) ⊆ F̄`, generated over `K` by the chosen square root of `d`. -/
noncomputable def sqrtField (d : ↥K) : IntermediateField ↥K Fbar :=
  IntermediateField.adjoin ↥K {sqrtRoot K d}

instance (d : ↥K) : FiniteDimensional ↥K ↥(sqrtField K d) :=
  IntermediateField.adjoin.finiteDimensional (sqrtRoot_isIntegral K d)

/-- The chosen square root of `d`, as an element of `K(√d)`. -/
noncomputable def sqrtD (d : ↥K) : ↥(sqrtField K d) :=
  ⟨sqrtRoot K d, IntermediateField.mem_adjoin_simple_self ↥K (sqrtRoot K d)⟩

@[simp] lemma coe_sqrtD (d : ↥K) : (sqrtD K d : Fbar) = sqrtRoot K d := rfl

lemma sqrtD_eq_gen (d : ↥K) :
    sqrtD K d = IntermediateField.AdjoinSimple.gen ↥K (sqrtRoot K d) := rfl

/-- `√d ^ 2 = d` in `K(√d)`. -/
theorem sqrtD_sq (d : ↥K) : sqrtD K d ^ 2 = algebraMap ↥K ↥(sqrtField K d) d := by
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, coe_sqrtD, sqrtRoot_sq]
  rfl

/-- `[K(√d) : K] ≤ 2`. -/
theorem sqrtField_finrank_le (d : ↥K) : Module.finrank ↥K ↥(sqrtField K d) ≤ 2 := by
  rw [sqrtField, IntermediateField.adjoin.finrank (sqrtRoot_isIntegral K d)]
  calc (minpoly ↥K (sqrtRoot K d)).natDegree ≤ (sqrtPoly K d).natDegree :=
        natDegree_le_of_dvd (minpoly_sqrtRoot_dvd K d) (sqrtPoly_ne_zero K d)
    _ = 2 := sqrtPoly_natDegree K d

/-! ### The conjugation `√d ↦ -√d` when `d` is not a square -/

lemma sqrtRoot_ne_zero {d : ↥K} (hd : ¬ IsSquare d) : sqrtRoot K d ≠ 0 := by
  intro h
  have h2 := sqrtRoot_sq K d
  rw [h, zero_pow two_ne_zero, eq_comm, map_eq_zero] at h2
  exact ne_zero_of_not_isSquare K hd h2

lemma sqrtD_ne_zero {d : ↥K} (hd : ¬ IsSquare d) : sqrtD K d ≠ 0 := by
  intro h
  exact sqrtRoot_ne_zero K hd (congrArg Subtype.val h)

/-- `X² − d` is the minimal polynomial of `√d` over `K` when `d` is not a square in `K`. -/
theorem minpoly_sqrtRoot {d : ↥K} (hd : ¬ IsSquare d) :
    minpoly ↥K (sqrtRoot K d) = sqrtPoly K d :=
  (minpoly.eq_of_irreducible_of_monic (sqrtPoly_irreducible K hd) (aeval_sqrtRoot K d)
    (sqrtPoly_monic K d)).symm

/-- The power basis `{1, √d}` of `K(√d)` over `K`. -/
noncomputable def sqrtPowerBasis (d : ↥K) : PowerBasis ↥K ↥(sqrtField K d) :=
  IntermediateField.adjoin.powerBasis (sqrtRoot_isIntegral K d)

lemma sqrtPowerBasis_gen (d : ↥K) : (sqrtPowerBasis K d).gen = sqrtD K d := rfl

lemma sqrtPowerBasis_dim {d : ↥K} (hd : ¬ IsSquare d) : (sqrtPowerBasis K d).dim = 2 := by
  show (minpoly ↥K (sqrtRoot K d)).natDegree = 2
  rw [minpoly_sqrtRoot K hd, sqrtPoly_natDegree]

lemma minpoly_sqrtD {d : ↥K} (hd : ¬ IsSquare d) :
    minpoly ↥K (sqrtD K d) = sqrtPoly K d := by
  have h := IntermediateField.minpoly_gen (F := ↥K) (sqrtRoot K d)
  rw [minpoly_sqrtRoot K hd] at h
  exact h

lemma aeval_neg_sqrtD (d : ↥K) : aeval (-sqrtD K d) (sqrtPoly K d) = 0 := by
  simp [sqrtPoly, sqrtD_sq]

/-- The conjugation `√d ↦ -√d` as a `K`-algebra endomorphism of `K(√d)`. -/
noncomputable def conjHom {d : ↥K} (hd : ¬ IsSquare d) :
    ↥(sqrtField K d) →ₐ[↥K] ↥(sqrtField K d) :=
  (sqrtPowerBasis K d).lift (-sqrtD K d) (by
    rw [sqrtPowerBasis_gen, minpoly_sqrtD K hd]
    exact aeval_neg_sqrtD K d)

lemma conjHom_sqrtD {d : ↥K} (hd : ¬ IsSquare d) : conjHom K hd (sqrtD K d) = -sqrtD K d :=
  (sqrtPowerBasis K d).lift_gen _ _

lemma conjHom_comp_conjHom {d : ↥K} (hd : ¬ IsSquare d) :
    (conjHom K hd).comp (conjHom K hd) = AlgHom.id ↥K ↥(sqrtField K d) :=
  (sqrtPowerBasis K d).algHom_ext (by
    rw [sqrtPowerBasis_gen, AlgHom.comp_apply, conjHom_sqrtD, map_neg, conjHom_sqrtD, neg_neg,
      AlgHom.id_apply])

/-- **The conjugation** `√d ↦ -√d` of `K(√d)` over `K`, for `d` not a square in `K`. -/
noncomputable def conj {d : ↥K} (hd : ¬ IsSquare d) :
    ↥(sqrtField K d) ≃ₐ[↥K] ↥(sqrtField K d) :=
  AlgEquiv.ofAlgHom (conjHom K hd) (conjHom K hd) (conjHom_comp_conjHom K hd)
    (conjHom_comp_conjHom K hd)

lemma conj_apply {d : ↥K} (hd : ¬ IsSquare d) (x : ↥(sqrtField K d)) :
    conj K hd x = conjHom K hd x := rfl

/-- The conjugation sends `√d` to `-√d`. -/
@[simp] theorem conj_sqrtD {d : ↥K} (hd : ¬ IsSquare d) : conj K hd (sqrtD K d) = -sqrtD K d :=
  conjHom_sqrtD K hd

/-- The conjugation is an involution. -/
theorem conj_conj {d : ↥K} (hd : ¬ IsSquare d) (x : ↥(sqrtField K d)) :
    conj K hd (conj K hd x) = x := by
  rw [conj_apply, conj_apply, ← AlgHom.comp_apply, conjHom_comp_conjHom, AlgHom.id_apply]

/-- Every element of `K(√d)` is `a + b √d` with `a, b ∈ K`. -/
theorem exists_eq_add_mul_sqrtD {d : ↥K} (hd : ¬ IsSquare d) (x : ↥(sqrtField K d)) :
    ∃ a b : ↥K, x = algebraMap ↥K _ a + algebraMap ↥K _ b * sqrtD K d := by
  obtain ⟨f, hf, rfl⟩ := (sqrtPowerBasis K d).exists_eq_aeval x
  rw [sqrtPowerBasis_dim K hd] at hf
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [sqrtPowerBasis_gen]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (Nat.lt_succ_iff.mp hf)]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  ring

/-! ### `K(√d)` as a number field -/

variable [NumberField ↥K]

instance (d : ↥K) : NumberField ↥(sqrtField K d) :=
  NumberField.of_module_finite ↥K ↥(sqrtField K d)

/-- The conjugation moves `√d`. -/
theorem conj_sqrtD_ne {d : ↥K} (hd : ¬ IsSquare d) : conj K hd (sqrtD K d) ≠ sqrtD K d := by
  rw [conj_sqrtD]
  intro h
  have h2 : (2 : ↥(sqrtField K d)) * sqrtD K d = 0 := by
    rw [two_mul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel _
  rcases mul_eq_zero.mp h2 with h0 | h0
  · exact two_ne_zero h0
  · exact sqrtD_ne_zero K hd h0

/-- The conjugation is not the identity. -/
theorem conj_ne_one {d : ↥K} (hd : ¬ IsSquare d) : conj K hd ≠ AlgEquiv.refl := by
  intro h
  exact conj_sqrtD_ne K hd (by rw [h]; rfl)

/-- **The fixed field of the conjugation is `K`.** -/
theorem eq_algebraMap_of_conj_eq {d : ↥K} (hd : ¬ IsSquare d) {x : ↥(sqrtField K d)}
    (hx : conj K hd x = x) : ∃ y : ↥K, algebraMap ↥K _ y = x := by
  obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_sqrtD K hd x
  refine ⟨a, ?_⟩
  simp only [map_add, map_mul, AlgEquiv.commutes, conj_sqrtD, mul_neg] at hx
  have h2 : (2 : ↥(sqrtField K d)) * (algebraMap ↥K _ b * sqrtD K d) = 0 := by
    linear_combination -hx
  rcases mul_eq_zero.mp h2 with h0 | h0
  · exact absurd h0 two_ne_zero
  rcases mul_eq_zero.mp h0 with h0 | h0
  · rw [h0, zero_mul, add_zero]
  · exact absurd h0 (sqrtD_ne_zero K hd)

end Iut
