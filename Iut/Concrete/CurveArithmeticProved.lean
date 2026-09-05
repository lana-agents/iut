/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.Existence
import Iut.Cor312.ThetaData.PlaceUnder
import Iut.Cor312.ThetaData.ValuationTransfer

/-!
# The provable part of `EllipticCurveData.CurveArithmetic`

The structure `Iut.EllipticCurveData.CurveArithmetic` packages the arithmetic of `E/F` consumed
by the construction of initial Θ-data. Five of its fields are general facts about number fields
and semistable elliptic curves, proved here for an arbitrary `C : EllipticCurveData`:

* `exists_liesOver`: every place of `F` lies over a place of `F_mod` (`Iut.placeUnder`);
* `residueChar_liesOver`: the residue characteristic is preserved along `w ∣ v`
  (the residue field of `w` is an extension of that of `v`);
* `inertDeg_pos`: residue degrees are positive (`Ideal.inertiaDeg_pos`);
* `badAll_finite`: the multiplicative places have `‖Δ(E)‖_w < 1`, and `Δ(E) ≠ 0` has
  norm `1` at all but finitely many places (`NumberField.FinitePlace.hasFiniteMulSupport`);
* `sum_inertDeg_le`: over a rational prime `q`, the residue degrees of the bad places sum to at
  most `∑_{w ∣ q} e_w f_w = [F : ℚ]` (`Ideal.sum_ramification_inertia`);
* `mult_invariant` (from everywhere-stable reduction): at a place of stable reduction, `E` is
  multiplicative iff `‖j(E)‖_w > 1`; since `j(E) ∈ F_mod`, this condition depends only on the
  place of `F_mod` below (`Iut.valuation_algebraMap_le_one_iff`).

`CurveArithmetic.ofCore` assembles them: `CurveArithmetic` reduces to `√−1 ∈ F`, everywhere
stable reduction, rational `6`-torsion and `F/F_mod` Galois of degree prime to `ℓ ≥ 7`.
-/

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WeierstrassCurve

universe u

/-! ## Residue characteristic along places of an extension -/

section ResidueChar

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- `Iut.two_mem_maximalIdeal_iff` for an arbitrary prime `q`: `q ∈ 𝔭_v` iff the residue
characteristic of `v` is `q`. -/
lemma natCast_mem_maximalIdeal_iff (v : FinitePlace k) {q : ℕ} (hq : q.Prime) :
    (q : 𝓞 k) ∈ v.maximalIdeal.asIdeal ↔ residueChar v = q := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    CharP.cast_eq_zero_iff (𝓞 k ⧸ v.maximalIdeal.asIdeal) (ringChar _)]
  exact Nat.prime_dvd_prime_iff_eq (residueChar_prime v) hq

/-- A place of `K` over a place of `k` has the same residue characteristic: the residue field of
`w` is a (finite) extension of the residue field of `v`. -/
lemma residueChar_eq_of_liesOver {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) : residueChar w = residueChar v := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  letI : Field (𝓞 k ⧸ v.maximalIdeal.asIdeal) := Ideal.Quotient.field _
  haveI : CharP (𝓞 k ⧸ v.maximalIdeal.asIdeal) (residueChar v) := ringChar.of_eq rfl
  haveI : CharP (𝓞 K ⧸ w.maximalIdeal.asIdeal) (residueChar v) :=
    charP_of_injective_algebraMap
      (algebraMap (𝓞 k ⧸ v.maximalIdeal.asIdeal) (𝓞 K ⧸ w.maximalIdeal.asIdeal)).injective
      (residueChar v)
  exact ringChar.eq _ (residueChar v)

end ResidueChar

/-! ## The `j`-invariant at places of stable reduction -/

section Reduction

variable {F : Type*} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
  (w : FinitePlace F)

omit [NumberField F] in
lemma j_eq_inv_Δ_mul : E.j = E.Δ⁻¹ * E.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ']

/-- `v_w(j(E)) > 1` at a place of multiplicative reduction. -/
lemma one_lt_valuation_j_of_mult (hw : HasMultiplicativeReductionAt E w) :
    1 < w.maximalIdeal.valuation F E.j := by
  have hc₄ := valuation_c₄_eq_one_of_mult E w hw
  have hΔ := valuation_Δ_lt_one_of_mult E w hw
  have hΔ0 : E.Δ ≠ 0 := by rw [← coe_Δ']; exact E.Δ'.ne_zero
  have hpos : 0 < w.maximalIdeal.valuation F E.Δ := by
    rw [pos_iff_ne_zero]
    exact (Valuation.ne_zero_iff _).2 hΔ0
  rw [j_eq_inv_Δ_mul, map_mul, map_inv₀, map_pow, hc₄, one_pow, mul_one]
  exact (one_lt_inv₀ hpos).2 hΔ

/-- `v_w(j(E)) ≤ 1` at a place of good reduction (of the given model). -/
lemma valuation_j_le_one_of_good (hw : HasGoodReductionAt E w) :
    w.maximalIdeal.valuation F E.j ≤ 1 := by
  haveI : (E.baseChange (w.maximalIdeal.adicCompletion F)).HasGoodReduction
    (w.maximalIdeal.adicCompletionIntegers F) := hw
  have hΔ : ‖(E.baseChange (w.maximalIdeal.adicCompletion F)).Δ‖ = 1 :=
    (valuation_eq_one_iff w _).1 HasGoodReduction.goodReduction
  have hc₄ : ‖(E.baseChange (w.maximalIdeal.adicCompletion F)).c₄‖ ≤ 1 := norm_c₄_le_one _
  rw [baseChange_adicCompletion_eq, map_Δ] at hΔ
  rw [baseChange_adicCompletion_eq, map_c₄] at hc₄
  rw [← norm_emb_le_one_iff, j_eq_inv_Δ_mul, map_mul, map_inv₀, map_pow, norm_mul, norm_inv,
    norm_pow, hΔ, inv_one, one_mul]
  exact pow_le_one₀ (norm_nonneg _) hc₄

/-- At a place of stable reduction, `E` has multiplicative reduction iff `v_w(j(E)) > 1`. -/
lemma hasMultiplicativeReductionAt_iff_of_stable (hst : HasStableReductionAt E w) :
    HasMultiplicativeReductionAt E w ↔ ¬ w.maximalIdeal.valuation F E.j ≤ 1 := by
  constructor
  · intro hw
    exact not_le.2 (one_lt_valuation_j_of_mult E w hw)
  · intro h
    rcases hst with hg | hm
    · exact absurd (valuation_j_le_one_of_good E w hg) h
    · exact hm

end Reduction

namespace EllipticCurveData

variable (C : EllipticCurveData.{u})

/-! ## The five general fields of `CurveArithmetic` -/

/-- Every finite place of `F` lies over a finite place of `F_mod`. -/
lemma exists_liesOver (w : FinitePlace C.F) :
    ∃ v : FinitePlace ↥(fieldOfModuli C.F C.E), FinitePlace.LiesOver w v :=
  ⟨placeUnder w, liesOver_placeUnder w⟩

/-- A place of `F` over a place of `F_mod` has the same residue characteristic. -/
lemma residueChar_liesOver (v : FinitePlace ↥(fieldOfModuli C.F C.E)) (w : FinitePlace C.F)
    (hwv : FinitePlace.LiesOver w v) : residueChar w = residueChar v :=
  residueChar_eq_of_liesOver hwv

/-- Residue degrees are positive. -/
lemma inertDeg_pos (w : FinitePlace C.F) : 0 < inertDeg C.F w :=
  Ideal.inertiaDeg_pos w.maximalIdeal.asIdeal ℤ

/-- The bad locus is finite: `Δ(E) ≠ 0` has `w`-adic norm `1` at all but finitely many places,
and `‖Δ(E)‖_w < 1` at a multiplicative place. -/
lemma badAll_finite : C.badAll.Finite := by
  have hΔ : C.E.Δ ≠ 0 := by rw [← coe_Δ']; exact C.E.Δ'.ne_zero
  refine (FinitePlace.hasFiniteMulSupport hΔ).subset ?_
  intro w hw
  rw [Function.mem_mulSupport, ← FinitePlace.norm_embedding_eq]
  exact ne_of_lt ((norm_emb_lt_one_iff _).2 (valuation_Δ_lt_one_of_mult C.E w hw))

/-- Multiplicative reduction does not depend on the place of `F` over a given place of
`F_mod`, given everywhere-stable reduction: it is the condition `‖j(E)‖ > 1`, and
`j(E) ∈ F_mod`. -/
lemma mult_invariant (hst : ∀ w : FinitePlace C.F, HasStableReductionAt C.E w)
    (v : FinitePlace ↥(fieldOfModuli C.F C.E)) (w w' : FinitePlace C.F)
    (hw : FinitePlace.LiesOver w v) (hw' : FinitePlace.LiesOver w' v)
    (hm : HasMultiplicativeReductionAt C.E w) : HasMultiplicativeReductionAt C.E w' := by
  rw [hasMultiplicativeReductionAt_iff_of_stable C.E w (hst w)] at hm
  rw [hasMultiplicativeReductionAt_iff_of_stable C.E w' (hst w')]
  let j₀ : ↥(fieldOfModuli C.F C.E) := ⟨C.E.j, IntermediateField.mem_adjoin_simple_self ℚ C.E.j⟩
  have key : ∀ w : FinitePlace C.F, FinitePlace.LiesOver w v →
      (w.maximalIdeal.valuation C.F C.E.j ≤ 1 ↔ v.maximalIdeal.valuation _ j₀ ≤ 1) :=
    fun w hw => valuation_algebraMap_le_one_iff hw j₀
  exact fun h => hm ((key w hw).2 ((key w' hw').1 h))

/-- The places of residue characteristic `q` are the primes over `(q) ⊆ ℤ`. -/
lemma maximalIdeal_liesOver_of_residueChar {q : ℕ} (hq : q.Prime) (w : FinitePlace C.F)
    (hw : residueChar w = q) :
    w.maximalIdeal.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal := by
    haveI hprime : (Ideal.span {(q : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2
        (Nat.prime_iff_prime_int.1 hq)
    exact IsPrime.to_maximal_ideal (by
      rw [ne_eq, Ideal.span_singleton_eq_bot]
      exact_mod_cast hq.ne_zero)
  have hmem : (q : ℤ) ∈ w.maximalIdeal.asIdeal.comap (algebraMap ℤ (𝓞 C.F)) := by
    rw [Ideal.mem_comap, map_natCast]
    exact (natCast_mem_maximalIdeal_iff w hq).2 hw
  refine ⟨hmax.eq_of_le (Ideal.comap_ne_top _ w.maximalIdeal.isPrime.ne_top) ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact hmem

/-- Over a rational prime `q`, the residue degrees of the bad places sum to at most `[F : ℚ]`:
they are bounded by `∑_{w ∣ q} e_w f_w = [F : ℚ]`. -/
lemma sum_inertDeg_le (q : ℕ) :
    ∑ w ∈ C.badAll_finite.toFinset.filter (fun w => residueChar w = q), inertDeg C.F w ≤
      Module.finrank ℚ C.F := by
  classical
  by_cases hq : q.Prime
  · set p : Ideal ℤ := Ideal.span {(q : ℤ)} with hp
    haveI hmax : p.IsMaximal := by
      haveI hprime : p.IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2
          (Nat.prime_iff_prime_int.1 hq)
      exact IsPrime.to_maximal_ideal (by
        rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
        exact_mod_cast hq.ne_zero)
    have hp0 : p ≠ ⊥ := by
      rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
      exact_mod_cast hq.ne_zero
    have hsum := Ideal.sum_ramification_inertia (𝓞 C.F) ℚ C.F hp0 (p := p)
    set T := C.badAll_finite.toFinset.filter (fun w => residueChar w = q) with hT
    -- the summand is bounded by `e_w f_w`
    have hle : ∀ w ∈ T, inertDeg C.F w ≤
        p.ramificationIdx' w.maximalIdeal.asIdeal * p.inertiaDeg' w.maximalIdeal.asIdeal := by
      intro w hw
      rw [hT, Finset.mem_filter] at hw
      haveI := C.maximalIdeal_liesOver_of_residueChar hq w hw.2
      haveI : w.maximalIdeal.asIdeal.IsMaximal :=
        w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
      have he : 0 < p.ramificationIdx' w.maximalIdeal.asIdeal :=
        Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ hp0)
      calc inertDeg C.F w = p.inertiaDeg' w.maximalIdeal.asIdeal := by
            rw [inertDeg, Ideal.inertiaDeg'_eq_inertiaDeg p w.maximalIdeal.asIdeal]
        _ ≤ _ := Nat.le_mul_of_pos_left _ he
    have hsub : T.image (fun w : FinitePlace C.F => w.maximalIdeal.asIdeal) ⊆
        IsDedekindDomain.primesOverFinset p (𝓞 C.F) := by
      intro P hP
      rw [Finset.mem_image] at hP
      obtain ⟨w, hw, rfl⟩ := hP
      rw [hT, Finset.mem_filter] at hw
      exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 C.F)).mpr
        ⟨inferInstance, C.maximalIdeal_liesOver_of_residueChar hq w hw.2⟩
    have hinj : Set.InjOn (fun w : FinitePlace C.F => w.maximalIdeal.asIdeal) T := by
      intro w₁ _ w₂ _ h
      exact FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h)
    calc ∑ w ∈ T, inertDeg C.F w
        ≤ ∑ w ∈ T, p.ramificationIdx' w.maximalIdeal.asIdeal *
            p.inertiaDeg' w.maximalIdeal.asIdeal := Finset.sum_le_sum hle
      _ = ∑ P ∈ T.image (fun w : FinitePlace C.F => w.maximalIdeal.asIdeal),
            p.ramificationIdx' P * p.inertiaDeg' P :=
          (Finset.sum_image (f := fun P => p.ramificationIdx' P * p.inertiaDeg' P) hinj).symm
      _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 C.F),
            p.ramificationIdx' P * p.inertiaDeg' P :=
          Finset.sum_le_sum_of_subset hsub
      _ = Module.finrank ℚ C.F := hsum
  · refine le_of_eq_of_le (Finset.sum_eq_zero ?_) (Nat.zero_le _)
    intro w hw
    rw [Finset.mem_filter] at hw
    exact absurd (hw.2 ▸ residueChar_prime w) hq

/-! ## Assembly -/

/-- `CurveArithmetic` from its four curve-specific inputs: `√−1 ∈ F`, everywhere stable
reduction, rational `6`-torsion, and `F/F_mod` Galois of degree prime to every prime `ℓ ≥ 7`.
The remaining five fields are proved above for every `C`. -/
theorem CurveArithmetic.ofCore (h1 : IsSquare (-1 : C.F))
    (h2 : ∀ w : FinitePlace C.F, HasStableReductionAt C.E w)
    (h3 : SixTorsionRational C.F C.E C.Fbar)
    (h4 : ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ → IsGaloisOfDegreePrimeTo C.F C.E ℓ) :
    C.CurveArithmetic where
  sqrt_neg_one := h1
  stable_reduction := h2
  six_torsion_rational := h3
  galois_deg_prime := h4
  exists_liesOver := C.exists_liesOver
  residueChar_liesOver := C.residueChar_liesOver
  mult_invariant v _ w w' hw hw' hm := C.mult_invariant h2 v w w' hw hw' hm
  badAll_finite := C.badAll_finite
  inertDeg_pos := C.inertDeg_pos
  sum_inertDeg_le := C.sum_inertDeg_le

end EllipticCurveData

end Iut
