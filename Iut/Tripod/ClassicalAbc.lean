/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Abc.Classical
import Iut.Tripod.Main

/-!
# From the height inequality on the tripod to the classical ABC conjecture

We prove that [GenEll] Theorem 2.1(i) for the tripod, `Iut.Tripod.tripodTheory.StatementI`
(the inequality `htCan ≲ (1 + ε)(logDiff + logCond)` on the points of degree `≤ d`, with no
restriction to compactly bounded subsets), implies the classical ABC conjecture
`Iut.ClassicalABC` (`Iut/Abc/Classical.lean`):

* `Iut.Tripod.classicalABCInt_of_statementI`: the symmetric form over `ℤ`;
* `Iut.Tripod.classicalABC_of_statementI`: the form over `ℕ`.

The main theorem `Iut.classicalABC_of_variant` (`Iut/MainTheorem.lean`) combines this with
`Iut.Tripod.abc_of_variant` and `Iut.Tripod.statementI_of_statementII`.

For a solution `a + b + c = 0` in coprime nonzero integers we take the rational point
`λ = −a/c ∈ ℚ ∖ {0, 1}` of the tripod (`Iut.Tripod.ratPt`), written `λ = n/d` in lowest
terms with `d = |c|`, `|n| = |a|`, `|n − d| = |b|`. Then

* `deg λ = [ℚ(λ) : ℚ] = 1` (`Iut.Tripod.deg_ratPt`);
* `htCan λ ≥ log max(|n|, d) = log max(|a|, |c|)` (`Iut.Tripod.logHeight₁_le_htCan_ratPt`,
  from the invariance of the finite part of the height under `ℚ ⊆ ℚ(λ)`,
  `Iut.finHeight_algebraMap`, the archimedean part, and Mathlib's
  `Rat.logHeight₁_eq_log_max`);
* `logDiff λ = 0`, since `ℚ(λ) ≅ ℚ` and `disc(ℚ) = 1` (`Iut.Tripod.logDiff_ratPt`);
* `logCond λ ≤ log rad(abc)` (`Iut.Tripod.logCond_ratPt_le`): a place where `λ` or `λ − 1`
  is not a unit lies over a prime dividing `n(n − d)d`, and the places of `ℚ(λ)` over `p`
  contribute at most `log p` (`Iut.sum_log_absNorm_filter_le`).

`htCan λ ≤ (1 + ε)(logDiff λ + logCond λ) + C` then gives
`max(|a|, |c|) ≤ e^C rad(abc)^{1+ε}`, and `|b| ≤ |a| + |c|`.

## Why `StatementII` is not enough

`tripodTheory.StatementII` (the conclusion of `Iut.Tripod.abc_of_variant`) is the same
inequality on compactly bounded subsets `K_V` only, and `Iut.Tripod.CompactlyBounded.set`
bounds `|log|λ|_w|` and `|log|λ − 1|_w|` at the archimedean places. The points `λ = −a/c`
of the ABC triples with `|a| ≪ |c|` tend to `0` archimedeanly (and `p`-adically at the
primes of `V` dividing `a`), so they leave every compactly bounded subset: the argument
above does not apply to `StatementII`, and the passage `StatementII → StatementI`
([GenEll], Theorem 2.1 (ii) ⇒ (i), via Belyi maps and the compactly bounded
subsets of all hyperbolic curves) is needed; it is the theorem
`Iut.Tripod.statementI_of_statementII`.

## References

- [GenEll] S. Mochizuki, *Arithmetic elliptic curves in general position*,
  Math. J. Okayama Univ. **52** (2010), 1–28.
-/

namespace Iut.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum UniqueFactorizationMonoid
open scoped Real

/-- The rational point `λ = q ∈ ℚ ∖ {0, 1}` of the tripod. -/
noncomputable def ratPt (q : ℚ) (h0 : q ≠ 0) (h1 : q ≠ 1) : Pt :=
  ⟨algebraMap ℚ Qbar q, fun h => h0 ((algebraMap ℚ Qbar).injective (h.trans (map_zero _).symm)),
    fun h => h1 ((algebraMap ℚ Qbar).injective (h.trans (map_one _).symm))⟩

section RatPt

variable {q : ℚ} (h0 : q ≠ 0) (h1 : q ≠ 1)

theorem deg_ratPt : deg (ratPt q h0 h1).1 = 1 := by
  rw [deg, ratPt]
  dsimp only
  rw [minpoly.eq_X_sub_C]
  exact Polynomial.natDegree_X_sub_C _

theorem finrank_fieldOf_ratPt : Module.finrank ℚ (fieldOf (ratPt q h0 h1).1) = 1 := by
  rw [← deg_eq_finrank, deg_ratPt]

theorem gen_ratPt : gen (ratPt q h0 h1).1 = algebraMap ℚ (fieldOf (ratPt q h0 h1).1) q := by
  apply Subtype.ext
  rw [coe_gen]
  rfl

/-- `ℚ(λ) ≅ ℚ` for `λ ∈ ℚ`. -/
noncomputable def fieldOfRatPtEquiv : fieldOf (ratPt q h0 h1).1 ≃ₐ[ℚ] ℚ :=
  (IntermediateField.equivOfEq (IntermediateField.adjoin_simple_eq_bot_iff.mpr
    (IntermediateField.mem_bot.mpr ⟨q, rfl⟩))).trans (IntermediateField.botEquiv ℚ Qbar)

/-- The log-different of a rational point vanishes: `disc(ℚ) = 1`. -/
theorem logDiff_ratPt : logDiff (ratPt q h0 h1) = 0 := by
  rw [logDiff, discr_eq_discr_of_algEquiv _ (fieldOfRatPtEquiv h0 h1), Rat.numberField_discr]
  simp

end RatPt

/-- `|q|_w = |q|` at an infinite place `w`, for `q ∈ ℚ`. -/
theorem infinitePlace_algebraMap_rat {K : Type*} [Field K] [NumberField K] (w : InfinitePlace K)
    (q : ℚ) : w (algebraMap ℚ K q) = |(q : ℝ)| := by
  rw [← InfinitePlace.norm_embedding_eq, eq_ratCast, map_ratCast, Complex.norm_ratCast]

/-- The height of an element of `ℚ` in a number field `K` is at least its height in `ℚ`
(in fact `[K : ℚ]` times it). -/
theorem logHeight₁_rat_le {K : Type*} [Field K] [NumberField K] (q : ℚ) :
    Height.logHeight₁ q ≤ Height.logHeight₁ (algebraMap ℚ K q) := by
  rw [logHeight₁_eq_infHeight_add_finHeight, logHeight₁_eq_infHeight_add_finHeight,
    finHeight_algebraMap]
  have hinf : infHeight q ≤ log⁺ |(q : ℝ)| := by
    have := infHeight_le_of_forall (T := ℚ) (y := q) (c := log⁺ |(q : ℝ)|) fun w => by
      have h : w q = |(q : ℝ)| := infinitePlace_algebraMap_rat w q
      rw [h]
    simpa using this
  have hinfK : log⁺ |(q : ℝ)| ≤ infHeight (algebraMap ℚ K q) := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    unfold infHeight
    calc log⁺ |(q : ℝ)| ≤ (w.mult : ℝ) * log⁺ (w (algebraMap ℚ K q)) := by
          rw [infinitePlace_algebraMap_rat]
          have : (1 : ℝ) ≤ w.mult := by exact_mod_cast InfinitePlace.one_le_mult
          nlinarith [Real.posLog_nonneg (x := |q|)]
      _ ≤ _ := Finset.single_le_sum (f := fun w : InfinitePlace K =>
            (w.mult : ℝ) * log⁺ (w (algebraMap ℚ K q)))
          (fun w _ => mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg) (Finset.mem_univ w)
  have hK : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  nlinarith [finHeight_nonneg q]

/-- `|m|_v = 1` at a finite place `v` whose residue characteristic does not divide the
integer `m`. -/
theorem finitePlace_intCast_eq_one {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)
    {m : ℤ} (hm : ¬ (residueChar v : ℤ) ∣ m) : v (m : K) = 1 := by
  rw [Iut.FinitePlace.apply_eq_one_iff, ← map_intCast (algebraMap (𝓞 K) K),
    valuation_of_algebraMap, intValuation_eq_one_iff]
  intro hmem
  apply hm
  haveI : CharP (𝓞 K ⧸ v.maximalIdeal.asIdeal) (residueChar v) := ringChar.charP _
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast,
    CharP.intCast_eq_zero_iff _ (residueChar v)] at hmem
  exact hmem

/-- **The log-conductor of a rational point**: for `λ = n/d ∈ ℚ ∖ {0, 1}`, the places where
`λ` meets `{0, 1, ∞}` lie over primes dividing `n(n − d)d`, so
`log-cond(λ) ≤ log rad(n(n − d)d)`. -/
theorem logCond_ratPt_le {q : ℚ} (h0 : q ≠ 0) (h1 : q ≠ 1) {n d : ℤ} (hd : d ≠ 0)
    (hq : q = n / d) :
    logCond (ratPt q h0 h1) ≤ Real.log (radical (n * (n - d) * d).natAbs : ℕ) := by
  classical
  set x := ratPt q h0 h1 with hx
  set K := fieldOf x.1
  rw [logCond_eq_sum, deg_ratPt, Nat.cast_one, div_one]
  set S := (badPlaces_finite x.2).toFinset with hS
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hn : n ≠ 0 := by
    rintro rfl
    exact h0 (by simp [hq])
  have hnd : n - d ≠ 0 := by
    intro h
    apply h1
    rw [hq, show n = d by omega, div_self hdQ]
  have hN : (n * (n - d) * d).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact mul_ne_zero (mul_ne_zero hn hnd) hd
  have hmaps : ∀ v ∈ S, residueChar v ∈ (n * (n - d) * d).natAbs.primeFactors := by
    intro v hv
    rw [Nat.mem_primeFactors]
    refine ⟨residueChar_prime v, ?_, hN⟩
    by_contra hndvd
    have h' : ¬ (residueChar v : ℤ) ∣ n * (n - d) * d := by rwa [Int.natCast_dvd]
    have hn' : ¬ (residueChar v : ℤ) ∣ n :=
      fun h => h' (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
    have hnd' : ¬ (residueChar v : ℤ) ∣ n - d :=
      fun h => h' (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)
    have hd' : ¬ (residueChar v : ℤ) ∣ d := fun h => h' (dvd_mul_of_dvd_right h _)
    have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
    have hv' := (Set.Finite.mem_toFinset _).mp hv
    have hqK : algebraMap ℚ K q = (n : K) / d := by
      rw [congrArg (algebraMap ℚ K) hq, map_div₀, map_intCast, map_intCast]
    rw [mem_badPlaces, gen_ratPt, hqK] at hv'
    have hsub : (n : K) / d - 1 = ((n - d : ℤ) : K) / d := by
      push_cast
      field_simp
    rw [hsub, map_div₀, map_div₀, finitePlace_intCast_eq_one v hn',
      finitePlace_intCast_eq_one v hnd', finitePlace_intCast_eq_one v hd'] at hv'
    simp at hv'
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ p ∈ (n * (n - d) * d).natAbs.primeFactors,
        ∑ v ∈ S with residueChar v = p, Real.log (Ideal.absNorm v.maximalIdeal.asIdeal)
      ≤ ∑ p ∈ (n * (n - d) * d).natAbs.primeFactors, Real.log p := by
        refine Finset.sum_le_sum fun p _ => ?_
        have := Iut.sum_log_absNorm_filter_le S p
        rwa [finrank_fieldOf_ratPt, Nat.cast_one, one_mul] at this
    _ = Real.log (radical (n * (n - d) * d).natAbs : ℕ) := by
        rw [Nat.radical_eq_prod_primeFactors, Nat.cast_prod, Real.log_prod]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- The height of a rational point `λ = q` is at least `log max(|num q|, den q)`. -/
theorem logHeight₁_le_htCan_ratPt {q : ℚ} (h0 : q ≠ 0) (h1 : q ≠ 1) :
    Height.logHeight₁ q ≤ htCan (ratPt q h0 h1) := by
  rw [htCan, deg_ratPt, Nat.cast_one, div_one, gen_ratPt]
  exact logHeight₁_rat_le q

/-- A normalization of a solution of `a + b + c = 0`: `λ = n/d` with `d = |c| > 0`,
`|n| = |a|`, `|n − d| = |b|`, `n` and `d` coprime. -/
private lemma exists_normal_form {a b c : ℤ} (hc : c ≠ 0) (hab : IsCoprime a b)
    (habc : a + b + c = 0) :
    ∃ n d : ℤ, 0 < d ∧ |n| = |a| ∧ d = |c| ∧ |n - d| = |b| ∧
      (n * (n - d) * d).natAbs = (a * b * c).natAbs ∧ IsCoprime n d := by
  have hac : IsCoprime a c := by
    have := hab.neg_right.add_mul_left_right (-1)
    rwa [show -b + a * -1 = c by omega] at this
  rcases hc.lt_or_gt with hc | hc
  · refine ⟨a, -c, by omega, rfl, (abs_of_neg hc).symm, ?_, ?_, hac.neg_right⟩
    · rw [show a - -c = -b by omega, abs_neg]
    · rw [show a * (a - -c) * -c = a * b * c by
        rw [show a - -c = -b by omega]; ring]
  · refine ⟨-a, c, hc, abs_neg a, (abs_of_pos hc).symm, ?_, ?_, hac.neg_left⟩
    · rw [show -a - c = b by omega]
    · rw [show -a - c = b by omega, show -a * b * c = -(a * b * c) by ring, Int.natAbs_neg]

/-- **[GenEll] Theorem 2.1(i) for the tripod implies the classical ABC conjecture** (form
over `ℤ`). For a solution `a + b + c = 0` in nonzero integers with `a`, `b` coprime, the
rational point `λ = −a/c` (normalized to `n/d` with `d = |c|`) has degree `1`, height
`log max(|a|, |c|)`, log-different `0` (`disc(ℚ) = 1`) and log-conductor at most
`log rad(abc)`; the height inequality on `U_ℙ(ℚ̄)^{≤ 1}` gives
`max(|a|, |c|) ≤ e^C · rad(abc)^{1+ε}`, and `|b| ≤ |a| + |c|`. -/
theorem classicalABCInt_of_statementI (h : tripodTheory.StatementI) : ClassicalABCInt := by
  intro ε hε
  obtain ⟨C, hC⟩ := (statementI_iff.mp h) 1 ε hε
  refine ⟨2 * Real.exp C, fun a b c ha hb hc hab habc => ?_⟩
  obtain ⟨n, d, hd, hna, hdc, hndb, hprod, hcop⟩ := exists_normal_form hc hab habc
  have hn : n ≠ 0 := by
    intro h; rw [h, abs_zero] at hna; exact ha (abs_eq_zero.mp hna.symm)
  have hnd : n - d ≠ 0 := by
    intro h; rw [h, abs_zero] at hndb; exact hb (abs_eq_zero.mp hndb.symm)
  set q : ℚ := n / d with hqdef
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have h0 : q ≠ 0 := div_ne_zero (by exact_mod_cast hn) hdQ
  have h1 : q ≠ 1 := by
    intro h
    rw [hqdef, div_eq_one_iff_eq hdQ] at h
    exact hnd (by exact_mod_cast sub_eq_zero.mpr h)
  have hcop' : Nat.Coprime n.natAbs d.natAbs := Int.isCoprime_iff_gcd_eq_one.mp hcop
  have hnum : q.num = n := Rat.num_div_eq_of_coprime hd hcop'
  have hden : (q.den : ℤ) = d := Rat.den_div_eq_of_coprime hd hcop'
  set x := ratPt q h0 h1
  have hx1 : x ∈ ptLE 1 := by rw [mem_ptLE, deg_ratPt]
  have hineq := hC x hx1
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hineq
  rw [logDiff_ratPt, zero_add] at hineq
  have hcond := logCond_ratPt_le h0 h1 hd.ne' hqdef
  have hht := logHeight₁_le_htCan_ratPt h0 h1
  rw [Rat.logHeight₁_eq_log_max, hnum] at hht
  set R : ℕ := radical (a * b * c).natAbs with hR
  rw [hprod] at hcond
  have hRpos : (0 : ℝ) < R := by exact_mod_cast Nat.radical_pos _
  -- `M = max(|a|, |c|)`
  have hM : ((max n.natAbs q.den : ℕ) : ℝ) = max |(a : ℝ)| |(c : ℝ)| := by
    have hden' : (q.den : ℝ) = |(c : ℝ)| := by
      rw [← Int.cast_abs, ← hdc, ← hden, Int.cast_natCast]
    rw [Nat.cast_max, hden', Nat.cast_natAbs, Int.cast_abs, ← Int.cast_abs, hna, Int.cast_abs]
  rw [hM] at hht
  have hMpos : 0 < max |(a : ℝ)| |(c : ℝ)| :=
    lt_max_of_lt_left (abs_pos.mpr (by exact_mod_cast ha))
  have hlog : Real.log (max |(a : ℝ)| |(c : ℝ)|) ≤ (1 + ε) * Real.log R + C := by
    nlinarith
  have hMle : max |(a : ℝ)| |(c : ℝ)| ≤ Real.exp C * (R : ℝ) ^ (1 + ε) := by
    rw [← Real.exp_log hMpos, Real.rpow_def_of_pos hRpos, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hb' : |(b : ℝ)| ≤ |(a : ℝ)| + |(c : ℝ)| := by
    rw [show (b : ℝ) = -(a + c) by
      have : (a : ℝ) + b + c = 0 := by exact_mod_cast habc
      linarith, abs_neg]
    exact abs_add_le _ _
  have hrad : ((radical (a * b * c) : ℤ) : ℝ) = R := by
    rw [hR, ← Int.radical_natAbs_eq_radical, Int.cast_natCast]
  rw [hrad]
  push_cast
  have hE : 0 ≤ Real.exp C * (R : ℝ) ^ (1 + ε) := by positivity
  have ha' := le_max_left |(a : ℝ)| |(c : ℝ)|
  have hc' := le_max_right |(a : ℝ)| |(c : ℝ)|
  refine max_le (by nlinarith) (max_le (by nlinarith) (by nlinarith))

/-- **[GenEll] Theorem 2.1(i) for the tripod implies the classical ABC conjecture**:
`tripodTheory.StatementI → Iut.ClassicalABC` (via the form over `ℤ`,
`classicalABCInt_of_statementI`). -/
theorem classicalABC_of_statementI (h : tripodTheory.StatementI) : ClassicalABC :=
  classicalABC_of_int (classicalABCInt_of_statementI h)

end Iut.Tripod
