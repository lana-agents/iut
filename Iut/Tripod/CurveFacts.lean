/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.CurveOf
import Iut.Concrete.TateInputsConstruct
import Iut.Concrete.CyclicSubgroup

/-!
# The arithmetic facts about the curve of a point of the tripod

For the Legendre curve `E_λ` over `F_λ = ℚ(λ, √−1, √λ, √(1 − λ), E_λ[3], E_λ[5])` of a point
`λ` of the tripod (`Iut.Tripod.curveOf`) we prove the facts about `E_λ/F_λ` consumed by
`Iut.CurveInputs` that are elementary, and isolate the remaining ones as named `Prop`s.

## Proved

* `√−1 ∈ F_λ` (`sqrt_neg_one`), `√λ, √(1 − λ) ∈ F_λ` (`exists_sq_eq_genC`,
  `exists_sq_eq_one_sub_genC`), by construction;
* the `6`-torsion of `E_λ(ℚ̄)` is rational over `F_λ` (`six_torsion_rational`): the affine
  `2`-torsion points are `(0, 0)`, `(1, 0)`, `(λ, 0)`, the `3`-torsion points have their
  coordinates in `F_λ` by construction, and `P = 3P − 2P` with `3P ∈ E[2]`, `2P ∈ E[3]`;
* the field of moduli `F_mod = ℚ(j(E_λ))` has degree `≤ [ℚ(λ) : ℚ]` (`dmod_le`), since
  `j(E_λ) = 256(λ² − λ + 1)³/(λ²(λ − 1)²) ∈ ℚ(λ)`;
* the tripodal field `F_tpd = ℚ(j, x(E_λ[2])) = ℚ(j, 0, 1, λ)` is `ℚ(λ)`
  (`tripodalFieldOf_eq`), so that `log-diff_ℙ(λ) = log(d_{F_tpd})` (`logDiff_eq`);
* the degree bound `[F_λ : ℚ] ≤ 552960·[ℚ(λ) : ℚ]` (`deg_le`) from the tower
  `ℚ ⊆ ℚ(λ) ⊆ ℚ(λ, √−1, √λ, √(1 − λ)) ⊆ ℚ(λ, √−1, √λ, √(1 − λ), E[3]) ⊆ F_λ` of relative
  degrees `≤ 8`, `≤ 48`, `≤ 480`, the last two being the **torsion degree bound**
  `Iut.Tripod.TorsionDegreeBound` (`[K(E_λ[n]) : K] ≤ |GL₂(𝔽_n)| = (n² − 1)(n² − n)`,
  isolated as a `Prop`).

## Isolated as `Prop`s (nothing postulated)

`TorsionDegreeBound`, and, for a choice `P : CurveProviders` of the arithmetic and mod-`ℓ`
representations of the curves, `LegendreHeightHyp` (IUT IV, Corollary 2.2(i); [GenEll],
Proposition 3.4; proved in `Iut/Tripod/Height.lean`, `Iut.Tripod.legendreHeight`),
`TwoAdicBoundHyp` (the `2`-adic contribution to `log(q_∀)`; proved in `TwoAdic.lean`),
`CyclicBoundHyp` ([GenEll], Lemma 3.5), `SL2ImageHyp` ([GenEll], Lemma 3.1(iii)),
`LogCondGeHyp`, `LogCondLeHyp` (the comparison of the conductor of `F_tpd = ℚ(λ)` away from
`2ℓ` with `log-cond_{{0,1,∞}}(λ)`, from the reduction theory of the Legendre curve; proved in
`LogCond.lean`) and `CoreFiniteHyp` ([CanLift], Proposition 2.7). The unproved ones are
collected in `CurveFactsProp`, and `Iut.Tripod.curveInputs` assembles
`Iut.CurveInputs tripodTheory AG K d` from it, the proved hypotheses and `NorthcottHyp`.
-/

namespace Iut.Tripod

open WeierstrassCurve NumberField Polynomial

open scoped IntermediateField

/-! ### The invariance of the different degree -/

/-- `log(d_L)` is invariant under `ℚ`-isomorphisms of number fields. -/
theorem logDifferentDeg_eq_of_algEquiv {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] (f : K ≃ₐ[ℚ] L) : logDifferentDeg K = logDifferentDeg L := by
  unfold logDifferentDeg
  rw [absNorm_differentIdeal (K := K), absNorm_differentIdeal (K := L),
    discr_eq_discr_of_algEquiv K f, f.toLinearEquiv.finrank_eq]

/-- `log-diff_ℙ(λ) = log(d_{ℚ(λ)})`. -/
theorem logDiff_eq_logDifferentDeg (x : Pt) : logDiff x = logDifferentDeg (fieldOf x.1) := by
  rw [logDiff_eq_log_absNorm_differentIdeal, logDifferentDeg, deg_eq_finrank]

section Curve

variable (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)

/-- `λ` as an element of the field `F_λ = (curveOf x h3 h5).F` of the curve. -/
noncomputable abbrev genC : (curveOf x h3 h5).F := gen' x.1

/-- The curve of `x` is the Legendre curve of `genC`. -/
theorem curveOf_E_eq : (curveOf x h3 h5).E = legendre (genC x h3 h5) := rfl

/-! ### `√−1 ∈ F` -/

/-- `√−1 ∈ F_λ`. -/
theorem sqrt_neg_one : IsSquare (-1 : (curveOf x h3 h5).F) :=
  ⟨sqrtNegOne' x.1, by rw [← sq]; exact (sqrtNegOne'_sq x.1).symm⟩

/-- `√λ ∈ F_λ`. -/
theorem exists_sq_eq_genC : ∃ s : (curveOf x h3 h5).F, s ^ 2 = genC x h3 h5 :=
  ⟨sqrtLam' x.1, sqrtLam'_sq x.1⟩

/-- `√(1 − λ) ∈ F_λ`. -/
theorem exists_sq_eq_one_sub_genC : ∃ s : (curveOf x h3 h5).F, s ^ 2 = 1 - genC x h3 h5 :=
  ⟨sqrtOneSubLam' x.1, sqrtOneSubLam'_sq x.1⟩

/-! ### Rationality of the `6`-torsion -/

open scoped Classical in
/-- A point of `E_λ(ℚ̄)` whose coordinates lie in `F_λ` is rational over `F_λ`. -/
theorem mem_range_of_coords
    (P : Affine.Point (Affine.baseChange (curveOf x h3 h5).E (curveOf x h3 h5).Fbar))
    (hP : coords (l := x.1) P ⊆ fieldOf' x.1) :
    P ∈ (Affine.Point.baseChange (W' := (curveOf x h3 h5).E) (curveOf x h3 h5).F
      (curveOf x h3 h5).Fbar).range := by
  cases P with
  | zero => exact zero_mem _
  | some a b h =>
    have ha : a ∈ fieldOf' x.1 := hP (Set.mem_insert _ _)
    have hb : b ∈ fieldOf' x.1 := hP (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have h' : (Affine.baseChange (curveOf x h3 h5).E (curveOf x h3 h5).F).Nonsingular
        (⟨a, ha⟩ : fieldOf' x.1) ⟨b, hb⟩ :=
      (Affine.baseChange_nonsingular (curveOf x h3 h5).E
        (Algebra.ofId (curveOf x h3 h5).F (curveOf x h3 h5).Fbar).injective
        (⟨a, ha⟩ : fieldOf' x.1) ⟨b, hb⟩).mp h
    exact ⟨Affine.Point.some _ _ h', rfl⟩

open scoped Classical in
/-- The `3`-torsion points of `E_λ(ℚ̄)` are rational over `F_λ`. -/
theorem three_torsion_mem_range
    (P : Affine.Point (Affine.baseChange (curveOf x h3 h5).E (curveOf x h3 h5).Fbar))
    (hP : 3 • P = 0) :
    P ∈ (Affine.Point.baseChange (W' := (curveOf x h3 h5).E) (curveOf x h3 h5).F
      (curveOf x h3 h5).Fbar).range :=
  mem_range_of_coords x h3 h5 P fun _ hc ↦
    torsionCoords_three_subset_fieldOf' x.1 (mem_torsionCoords hP hc)

open scoped Classical in
/-- The `2`-torsion points of `E_λ(ℚ̄)` are rational over `F_λ`. -/
theorem two_torsion_mem_range
    (P : Affine.Point (Affine.baseChange (curveOf x h3 h5).E (curveOf x h3 h5).Fbar))
    (hP : 2 • P = 0) :
    P ∈ (Affine.Point.baseChange (W' := (curveOf x h3 h5).E) (curveOf x h3 h5).F
      (curveOf x h3 h5).Fbar).range := by
  rcases legendre_two_torsion x.1 hP with rfl | ⟨a, h, rfl, ha⟩
  · exact zero_mem _
  · refine mem_range_of_coords x h3 h5 _ ?_
    rw [coords_some]
    rintro c (rfl | rfl)
    · rcases ha with rfl | rfl | rfl
      · exact zero_mem _
      · exact one_mem _
      · exact mem_fieldOf'_self _
    · exact zero_mem _

open scoped Classical in
/-- **The `6`-torsion of `E_λ` is rational over `F_λ`** (IUT I, Definition 3.1(b)):
`P = 3P − 2P` with `3P ∈ E[2]` and `2P ∈ E[3]`. -/
theorem six_torsion_rational :
    SixTorsionRational (curveOf x h3 h5).F (curveOf x h3 h5).E (curveOf x h3 h5).Fbar := by
  intro P hP
  rw [AddSubgroup.torsionBy, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff] at hP
  have hP' : (6 : ℕ) • P = 0 := by rw [← natCast_zsmul]; exact hP
  have h2 : 2 • (3 • P) = 0 := by rw [smul_smul]; exact hP'
  have h3' : 3 • (2 • P) = 0 := by rw [smul_smul]; exact hP'
  have hmem := sub_mem (two_torsion_mem_range x h3 h5 _ h2)
    (three_torsion_mem_range x h3 h5 _ h3')
  rwa [succ_nsmul, add_sub_cancel_left] at hmem

/-! ### The field of moduli and the tripodal field -/

/-- `j(E_λ) ∈ ℚ(λ)`. -/
theorem j_mem_adjoin : (curveOf x h3 h5).E.j ∈ ℚ⟮genC x h3 h5⟯ := by
  have hg : genC x h3 h5 ∈ ℚ⟮genC x h3 h5⟯ := IntermediateField.mem_adjoin_simple_self ℚ _
  have h256 : (256 : (curveOf x h3 h5).F) ∈ ℚ⟮genC x h3 h5⟯ := by
    have : (256 : (curveOf x h3 h5).F) = ((256 : ℕ) : (curveOf x h3 h5).F) := by norm_num
    rw [this]
    exact IntermediateField.natCast_mem _ _
  haveI : (legendre (genC x h3 h5)).IsElliptic := (curveOf x h3 h5).isElliptic
  have hj : (curveOf x h3 h5).E.j = 256 * (genC x h3 h5 ^ 2 - genC x h3 h5 + 1) ^ 3 /
      (genC x h3 h5 ^ 2 * (genC x h3 h5 - 1) ^ 2) := legendre_j (l := genC x h3 h5)
  rw [hj]
  exact div_mem (mul_mem h256 (pow_mem (add_mem (sub_mem (pow_mem hg 2) hg) (one_mem _)) 3))
    (mul_mem (pow_mem hg 2) (pow_mem (sub_mem hg (one_mem _)) 2))

/-- `F_mod = ℚ(j) ⊆ ℚ(λ)` inside `F_λ`. -/
theorem fieldOfModuli_le :
    fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E ≤ ℚ⟮genC x h3 h5⟯ :=
  IntermediateField.adjoin_simple_le_iff.mpr (j_mem_adjoin x h3 h5)

/-- `λ ∈ F_λ` is integral over `ℚ`. -/
theorem isIntegral_genC : IsIntegral ℚ (genC x h3 h5) :=
  Algebra.IsIntegral.isIntegral _

/-- The embedding `F_λ → ℚ̄` as a `ℚ`-algebra homomorphism (for the `ℚ`-algebra structure
of `F_λ` as a number field). -/
noncomputable def embC : (curveOf x h3 h5).F →ₐ[ℚ] Qbar :=
  RingHom.toRatAlgHom ((fieldOf' x.1).val.toRingHom : (curveOf x h3 h5).F →+* Qbar)

@[simp] theorem embC_apply (a : (curveOf x h3 h5).F) :
    embC x h3 h5 a = (fieldOf' x.1).val a := rfl

/-- `ℚ(λ) ⊆ F_λ` is isomorphic to `ℚ(λ) ⊆ ℚ̄`. -/
noncomputable def adjoinGenCEquiv : ℚ⟮genC x h3 h5⟯ ≃ₐ[ℚ] fieldOf x.1 :=
  (IntermediateField.equivMap ℚ⟮genC x h3 h5⟯ (embC x h3 h5)).trans
    (IntermediateField.equivOfEq (by
      rw [IntermediateField.adjoin_map, Set.image_singleton, embC_apply]
      rfl))

/-- `[ℚ(λ) : ℚ] = deg λ` for `ℚ(λ) ⊆ F_λ`. -/
theorem finrank_adjoin_genC : Module.finrank ℚ ℚ⟮genC x h3 h5⟯ = deg x.1 := by
  rw [(adjoinGenCEquiv x h3 h5).toLinearEquiv.finrank_eq, deg_eq_finrank]

/-- `d_mod = [F_mod : ℚ] ≤ [ℚ(λ) : ℚ]`. -/
theorem dmod_le :
    Module.finrank ℚ ↥(fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E) ≤ deg x.1 := by
  haveI : FiniteDimensional ℚ ℚ⟮genC x h3 h5⟯ :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_genC x h3 h5)
  rw [← finrank_adjoin_genC x h3 h5]
  exact IntermediateField.finrank_le_of_le_right (fieldOfModuli_le x h3 h5)

open scoped Classical in
/-- The `x`-coordinates of the `F_λ`-rational `2`-torsion points of `E_λ` are `0`, `1`,
`λ`. -/
theorem twoTorsionXOf_eq :
    twoTorsionXOf (curveOf x h3 h5).F (curveOf x h3 h5).E = {0, 1, genC x h3 h5} := by
  haveI : (legendre (genC x h3 h5)).IsElliptic := (curveOf x h3 h5).isElliptic
  ext a
  simp only [twoTorsionXOf, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, h, hP⟩
    rw [AddSubgroup.torsionBy, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff] at hP
    have hP' : (2 : ℕ) • Affine.Point.some a b h = 0 := by rw [← natCast_zsmul]; exact hP
    have hb : b = 0 := (two_nsmul_some_eq_zero_iff (genC x h3 h5) h).mp hP'
    subst hb
    exact legendre_equation_y_zero _ ((Affine.nonsingular_iff _ _).mp h).1
  · intro ha
    have hE : (curveOf x h3 h5).E.toAffine.Equation a 0 := by
      rcases ha with rfl | rfl | rfl
      · exact legendre_equation_zero (genC x h3 h5)
      · exact legendre_equation_one (genC x h3 h5)
      · exact legendre_equation_self (genC x h3 h5)
    refine ⟨0, Affine.equation_iff_nonsingular.mp hE, ?_⟩
    rw [AddSubgroup.torsionBy, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]
    have := two_nsmul_some_zero (genC x h3 h5) (Affine.equation_iff_nonsingular.mp hE)
    rwa [← natCast_zsmul] at this

/-- **The tripodal field of `E_λ` is `ℚ(λ)`**: `F_tpd = ℚ(j, 0, 1, λ) = ℚ(λ)`. -/
theorem tripodalFieldOf_eq :
    tripodalFieldOf (curveOf x h3 h5).F (curveOf x h3 h5).E = ℚ⟮genC x h3 h5⟯ := by
  rw [tripodalFieldOf, twoTorsionXOf_eq]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff]
    refine ⟨j_mem_adjoin x h3 h5, ?_⟩
    rintro a (rfl | rfl | rfl)
    · exact zero_mem _
    · exact one_mem _
    · exact IntermediateField.mem_adjoin_simple_self ℚ _
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (by simp))

/-- **`log-diff_ℙ(λ)` is the different degree of the tripodal field** `F_tpd = ℚ(λ)`. -/
theorem logDiff_eq :
    logDiff x = logDifferentDeg ↥(tripodalFieldOf (curveOf x h3 h5).F (curveOf x h3 h5).E) := by
  haveI : FiniteDimensional ℚ ℚ⟮genC x h3 h5⟯ :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_genC x h3 h5)
  rw [logDiff_eq_logDifferentDeg]
  exact (logDifferentDeg_eq_of_algEquiv
    ((IntermediateField.equivOfEq (tripodalFieldOf_eq x h3 h5)).trans
      (adjoinGenCEquiv x h3 h5))).symm

end Curve

/-! ### The degree bound -/

/-- **The torsion degree bound**: for every number field `K ⊆ ℚ̄` containing `λ`, adjoining
the coordinates of the `n`-torsion of `E_λ` multiplies the degree by at most
`|GL₂(𝔽_n)| = (n² − 1)(n² − n)` (the `n`-torsion field `K(E_λ[n])` is Galois over `K` with
group embedded in `GL₂(ℤ/n)` by the action on a basis of `E_λ[n] ≅ (ℤ/n)²`). Recorded as a
`Prop`, not postulated. -/
def TorsionDegreeBound (l : Qbar) (n : ℕ) : Prop :=
  ∀ K : IntermediateField ℚ Qbar, FiniteDimensional ℚ K → l ∈ K →
    Module.finrank ℚ ↥(K ⊔ IntermediateField.adjoin ℚ (torsionCoords l n)) ≤
      (n ^ 2 - 1) * (n ^ 2 - n) * Module.finrank ℚ K

/-- `[K(s) : ℚ] ≤ 2·[K : ℚ]` for `s² ∈ K`. -/
theorem finrank_sup_adjoin_sq_le (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K]
    {s : Qbar} (hs : s ^ 2 ∈ K) :
    Module.finrank ℚ ↥(K ⊔ ℚ⟮s⟯) ≤ 2 * Module.finrank ℚ K := by
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup]
  have hint : IsIntegral K s := (isIntegral s).tower_top
  have h2 : Module.finrank K K⟮s⟯ ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hint]
    have hmin := minpoly.min K s (monic_X_pow_sub_C (⟨s ^ 2, hs⟩ : K) two_ne_zero) (by simp)
    have := natDegree_le_natDegree hmin
    rwa [natDegree_X_pow_sub_C] at this
  calc Module.finrank ℚ ↥(IntermediateField.restrictScalars ℚ K⟮s⟯)
      = Module.finrank ℚ K * Module.finrank K K⟮s⟯ :=
        (Module.finrank_mul_finrank ℚ K K⟮s⟯).symm
    _ ≤ Module.finrank ℚ K * 2 := Nat.mul_le_mul_left _ h2
    _ = 2 * Module.finrank ℚ K := mul_comm _ _

/-- `[ℚ(λ, √−1, √λ, √(1 − λ)) : ℚ] ≤ 8·[ℚ(λ) : ℚ]`. -/
theorem finrank_adjoin_gens_le (l : Qbar) :
    Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {l, sqrtNegOne, sqrtLam l, sqrtOneSubLam l}) ≤
      8 * deg l := by
  have hset : ({l, sqrtNegOne, sqrtLam l, sqrtOneSubLam l} : Set Qbar) =
      (({l} ∪ {sqrtNegOne}) ∪ {sqrtLam l}) ∪ {sqrtOneSubLam l} := by
    ext a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, or_assoc]
  rw [hset, IntermediateField.adjoin_union, IntermediateField.adjoin_union,
    IntermediateField.adjoin_union]
  haveI : FiniteDimensional ℚ ℚ⟮sqrtNegOne⟯ :=
    IntermediateField.adjoin.finiteDimensional (isIntegral _)
  haveI : FiniteDimensional ℚ ℚ⟮sqrtLam l⟯ :=
    IntermediateField.adjoin.finiteDimensional (isIntegral _)
  have hl : l ∈ ℚ⟮l⟯ := IntermediateField.mem_adjoin_simple_self ℚ l
  have h1 : Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯) ≤ 2 * deg l := by
    rw [deg_eq_finrank]
    exact finrank_sup_adjoin_sq_le _ (by rw [sqrtNegOne_sq]; exact neg_mem (one_mem _))
  have h2 : Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯ ⊔ ℚ⟮sqrtLam l⟯) ≤
      2 * Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯) :=
    finrank_sup_adjoin_sq_le _ (by rw [sqrtLam_sq]; exact le_sup_left (a := ℚ⟮l⟯) hl)
  have h3 : Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯ ⊔ ℚ⟮sqrtLam l⟯ ⊔ ℚ⟮sqrtOneSubLam l⟯) ≤
      2 * Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯ ⊔ ℚ⟮sqrtLam l⟯) :=
    finrank_sup_adjoin_sq_le _ (by
      rw [sqrtOneSubLam_sq]
      exact sub_mem (one_mem _)
        (le_sup_left (a := ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯) (le_sup_left (a := ℚ⟮l⟯) hl)))
  omega

/-- **The degree bound** `[F_λ : ℚ] ≤ 552960·[ℚ(λ) : ℚ]` ((E3)–(E5) in the proof of IUT IV,
Theorem 1.10), from the torsion degree bounds for `n = 3` and `n = 5`:
`[F_λ : ℚ] ≤ 480·48·8·[ℚ(λ) : ℚ] = 184320·[ℚ(λ) : ℚ]`. -/
theorem deg_le (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)
    (hT3 : TorsionDegreeBound x.1 3) (hT5 : TorsionDegreeBound x.1 5) :
    Module.finrank ℚ (curveOf x h3 h5).F ≤ 552960 * deg x.1 := by
  set K₁ : IntermediateField ℚ Qbar :=
    IntermediateField.adjoin ℚ {x.1, sqrtNegOne, sqrtLam x.1, sqrtOneSubLam x.1} with hK₁
  set K₂ : IntermediateField ℚ Qbar :=
    K₁ ⊔ IntermediateField.adjoin ℚ (torsionCoords x.1 3) with hK₂
  haveI hK₁fin : FiniteDimensional ℚ K₁ := by
    haveI := (Set.toFinite {x.1, sqrtNegOne, sqrtLam x.1, sqrtOneSubLam x.1}).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun y _ ↦ isIntegral y
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (torsionCoords x.1 3)) := by
    haveI := (torsionCoords_finite h3).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun y _ ↦ isIntegral y
  haveI hK₂fin : FiniteDimensional ℚ K₂ := IntermediateField.finiteDimensional_sup _ _
  have hl₁ : x.1 ∈ K₁ := IntermediateField.subset_adjoin _ _ (by simp)
  have hl₂ : x.1 ∈ K₂ := le_sup_left (a := K₁) hl₁
  have hF : fieldOf' x.1 = K₂ ⊔ IntermediateField.adjoin ℚ (torsionCoords x.1 5) := by
    rw [fieldOf', IntermediateField.adjoin_union, IntermediateField.adjoin_union]
  have h1 : Module.finrank ℚ K₁ ≤ 8 * deg x.1 := finrank_adjoin_gens_le x.1
  have h2 : Module.finrank ℚ K₂ ≤ 48 * Module.finrank ℚ K₁ := by
    have := hT3 K₁ hK₁fin hl₁
    norm_num at this
    exact this
  have h5' : Module.finrank ℚ ↥(K₂ ⊔ IntermediateField.adjoin ℚ (torsionCoords x.1 5)) ≤
      480 * Module.finrank ℚ K₂ := by
    have := hT5 K₂ hK₂fin hl₂
    norm_num at this
    exact this
  change Module.finrank ℚ (fieldOf' x.1) ≤ 552960 * deg x.1
  rw [hF]
  omega

/-! ### The providers and the isolated hypotheses -/

/-- **The providers of the curve data**: the finiteness of the `3`- and `5`-torsion of
`E_λ(ℚ̄)` for every `λ`, the arithmetic `EllipticCurveData.CurveArithmetic` of `E_λ/F_λ`
(IUT IV, Proposition 1.8: everywhere stable reduction, `F_λ/F_mod` Galois of degree prime
to `ℓ ≥ 7`, …; its fields `sqrt_neg_one` and `six_torsion_rational` are proved above and
the five general fields in `Iut.EllipticCurveData.CurveArithmetic.ofCore`), and the
mod-`ℓ` representations (`Iut.EllipticCurveData.modEllRepData` from a basis of
`E_λ[ℓ]`). -/
structure CurveProviders where
  /-- The `3`-torsion of `E_λ(ℚ̄)` is finite. -/
  torsionFinite3 : ∀ l : Qbar, TorsionFinite l 3
  /-- The `5`-torsion of `E_λ(ℚ̄)` is finite. -/
  torsionFinite5 : ∀ l : Qbar, TorsionFinite l 5
  /-- The arithmetic of `E_λ/F_λ`. -/
  arith : ∀ x : Pt, (curveOf x (torsionFinite3 x.1) (torsionFinite5 x.1)).CurveArithmetic
  /-- The mod-`ℓ` representations of `E_λ`. -/
  modRep : ∀ (x : Pt) (ℓ : ℕ), ℓ.Prime →
    (curveOf x (torsionFinite3 x.1) (torsionFinite5 x.1)).ModEllRepData ℓ

namespace CurveProviders

variable (P : CurveProviders)

/-- The curve `E_λ/F_λ` of a point. -/
noncomputable def curve (x : Pt) : EllipticCurveData :=
  curveOf x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)

/-- The Tate inputs of `E_λ` (`Iut.EllipticCurveData.tateInputs`). -/
noncomputable def tate (x : Pt) : (P.curve x).TateInputs := (P.curve x).tateInputs

/-- The local height data of `E_λ`. -/
noncomputable def localData (x : Pt) : LocalHeightData :=
  (P.curve x).localHeightData (P.arith x) (P.tate x)

/-- The height `h(λ) = log(q_∀(E_λ))`. -/
noncomputable def h (x : Pt) : ℝ := (P.localData x).height

end CurveProviders

variable (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)

/-- **IUT IV, Corollary 2.2(i)** ([GenEll], Proposition 3.4): `(1/6)·log(q_∀) ≈ ht_{𝒪(1)}`
on a compactly bounded subset. -/
def LegendreHeightHyp : Prop := ((1 / 6 : ℝ) • P.h) ≈[K.set] htCan

/-- **The `2`-adic bound**: the contribution of the places over `2` to `log(q_∀(E_λ))` is
bounded by `B` on a compactly bounded subset (the places of `F_λ` over `2` lie over the
places of `ℚ(λ)` over `2 ∈ V`, where `|log|λ|_v|`, `|log|λ − 1|_v|` are bounded, and
`ord_w(q_w) = −ord_w(j(E_λ))` with `j = 256(λ² − λ + 1)³/(λ²(λ − 1)²)`). -/
def TwoAdicBoundHyp (B : ℝ) : Prop := ∀ x ∈ K.set, (P.localData x).heightEq 2 ≤ B

/-- **[GenEll], Lemma 3.5 (with Proposition 3.4)**: if `E_λ` has an `ℓ`-cyclic subgroup
scheme then `(ℓ − 2)/24 · log(q_∀) ≤ 2 log ℓ + T_K`. -/
def CyclicBoundHyp (TK : ℝ) : Prop :=
  ∀ x ∈ K.set ∩ ptLE d, ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ →
    (∀ w ∈ (P.localData x).bad, ¬ ℓ ∣ (P.localData x).hv w) →
    (P.curve x).HasCyclicSubgroup ℓ →
    ((ℓ : ℝ) - 2) / 24 * P.h x ≤ 2 * Real.log ℓ + TK

/-- **[GenEll], Lemma 3.1(iii)**: under (P2), (P4), (P5) the image of the mod-`ℓ`
representation contains `SL₂(𝔽_ℓ)`. -/
def SL2ImageHyp : Prop :=
  ∀ (x : Pt) (ℓ : ℕ) (hℓ : ℓ.Prime), 5 ≤ ℓ →
    (∀ w ∈ (P.localData x).bad, ¬ ℓ ∣ (P.localData x).hv w) →
    ¬ (P.curve x).HasCyclicSubgroup ℓ →
    (∃ w ∈ (P.localData x).bad, (P.localData x).p w ≠ 2 ∧ (P.localData x).p w ≠ ℓ) →
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range

/-- **The conductor bound from below**: the conductor degree of `F_tpd = ℚ(λ)` away from
`2ℓ` is at most `log-cond_{{0,1,∞}}(λ)` (the odd bad places of `E_λ` are among the places
where `λ` meets `{0, 1, ∞}`, as `Δ = 16λ²(λ − 1)²`). -/
def LogCondGeHyp : Prop :=
  ∀ (x : Pt) (ℓ : ℕ), ℓ.Prime → 7 ≤ ℓ →
    logConductorDegOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ) ≤ logCond x

/-- **The conductor bound from above**: `log-cond_{{0,1,∞}}(λ)` exceeds the conductor degree
of `F_tpd = ℚ(λ)` away from `2ℓ` by at most `log(2ℓ)` (the places where `λ` meets
`{0, 1, ∞}` of residue characteristic `≠ 2, ℓ` are multiplicative for `E_λ`, since `c₄` is
a unit there; the places over `2` and `ℓ` contribute at most `log 2 + log ℓ`). -/
def LogCondLeHyp : Prop :=
  ∀ (x : Pt) (ℓ : ℕ), ℓ.Prime → 7 ≤ ℓ →
    logCond x ≤
      logConductorDegOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ) + Real.log (2 * ℓ)

/-- **[CanLift], Proposition 2.7**: only finitely many points of bounded degree in `K` have
a once-punctured elliptic curve `X_λ` that fails to have the `F_λ`-core `C_λ = X_λ/{±1}`
(the four exceptional `j`-invariants), relative to an anabelian interface `AG`. -/
def CoreFinitenessHyp (AG : AnabelianGeometry.{0}) : Prop :=
  {x | ∃ hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d,
    ¬ AG.HasCore (AG.oncePunctured (P.curve x).E)
      (OrbicurveDataSection.CF AG (P.curve x).F (P.curve x).E)}.Finite

/-- **The facts about the curves of the points that remain unproved**, collected: exactly
the fields of `Iut.CurveInputs` for `curveOf` that are not proved in this file, in
`TwoAdic.lean`, `LogCond.lean` or `Height.lean`. -/
structure CurveFactsProp (AG : AnabelianGeometry.{0}) (TK : ℝ) : Prop where
  /-- [GenEll], Lemma 3.5. -/
  cyclic : CyclicBoundHyp P K d TK
  /-- [GenEll], Lemma 3.1(iii). -/
  sl2 : SL2ImageHyp P
  /-- [CanLift], Proposition 2.7. -/
  core : CoreFinitenessHyp P K d AG

/-- **The inputs of IUT IV, Corollary 2.2 for the tripod**, from the curves `E_λ/F_λ` of the
points, the facts proved in this file, the isolated hypotheses `CurveFactsProp`, the height
comparison `LegendreHeightHyp` (proved in `Height.lean`), the `2`-adic and conductor bounds
(proved in `TwoAdic.lean`, `LogCond.lean`), and the Northcott property `NorthcottHyp`. -/
noncomputable def curveInputs {AG : AnabelianGeometry.{0}} {TK : ℝ}
    (CF : CurveFactsProp P K d AG TK) (hN : NorthcottHyp)
    (hdeg3 : ∀ l : Qbar, TorsionDegreeBound l 3) (hdeg5 : ∀ l : Qbar, TorsionDegreeBound l 5)
    (hh : LegendreHeightHyp P K) (hB : TwoAdicBoundHyp P K (max (4 * K.c) 0))
    (hge : LogCondGeHyp P) (hle : LogCondLeHyp P) :
    CurveInputs tripodTheory AG K d where
  h := P.h
  curve x _ := P.curve x
  arith x _ := P.arith x
  tate x _ := P.tate x
  modRep x _ ℓ hℓ := P.modRep x ℓ hℓ
  height_eq _ _ := rfl
  deg_le x hx := by
    refine (deg_le x _ _ (hdeg3 x.1) (hdeg5 x.1)).trans ?_
    exact Nat.mul_le_mul_left _ hx.2
  dmod_le x hx := (dmod_le x _ _).trans hx.2
  htCan_equiv := hh
  northcott := northcott_of_equiv hN K d hh
  B := max (4 * K.c) 0
  B_nonneg := le_max_right _ _
  heightEq_two_le x hx := hB x hx.1
  HasCyclicSubgroup x ℓ := (P.curve x).HasCyclicSubgroup ℓ
  TK := TK
  cyclic_bound := CF.cyclic
  sl2_of x _ ℓ hℓ := CF.sl2 x ℓ hℓ
  logDiff_eq x _ := logDiff_eq x _ _
  excCore_finite := CF.core
  logCond_ge x _ := hge x
  logCond_le x _ := hle x

end Iut.Tripod
