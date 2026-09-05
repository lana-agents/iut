/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.Providers
import Iut.Concrete.ThetaLocalConstruct.Ordp
import Iut.Cor312.ThetaData.GalCompletion

/-!
# The `2`-adic bound for the Legendre curves

We prove `Iut.Tripod.TwoAdicBoundHyp P K (max (4 * K.c) 0)`: on a compactly bounded subset
`K` of the tripod, the contribution of the places over `2` to `log(q_∀(E_λ))` is bounded.

At a place `w` of `F_λ` of multiplicative reduction, the order `h_w = ord_w(q_w)` of the Tate
parameter is `−ord_w(j(E_λ))` (`Iut.Tripod.valuation_j_eq_exp_qOrder`), and
`j(E_λ) = 256(λ² − λ + 1)³/(λ²(λ − 1)²)` gives
`h_w ≤ 2|ord_w(λ)| + 2|ord_w(λ − 1)|` (`Iut.Tripod.log_valuation_legendre_j_le`). For the
place `𝔭` of `F_tpd = ℚ(λ)` below `w`, `ord_w(λ) = e(w/𝔭)·ord_𝔭(λ)`, and the bound
`|log|λ|_𝔭| ≤ c` of the compactly bounded subset (transported to `F_tpd ⊆ F_λ` from
`ℚ(λ) ⊆ ℚ̄` along `Iut.FinitePlace.mapEquiv`) reads `|ord_𝔭(λ)|·f_𝔭·log 2 ≤ c`. Summing
`h_w f_w log 2 ≤ 4c·e(w/𝔭)f(w/𝔭) ≤ 4c·[F_w : ℚ₂]` over the places over `2` and using
`∑_{w ∣ 2} [F_w : ℚ₂] ≤ [F : ℚ]` gives the bound `4c`.

## Infrastructure

* `Iut.FinitePlace.mapEquiv e`: the bijection of finite places along an isomorphism `e` of
  number fields, with its effect on the valuations, absolute values, absolute norms and
  residue characteristics;
* `Iut.sum_localDeg_filter_le`: `∑_{w ∈ S, p_w = q} e_w f_w ≤ [K : ℚ]` for any finite set `S`
  of places;
* `Iut.log_valuation_legendre_j_le`, `Iut.one_lt_valuation_legendre_j`: the valuation of
  `j(E_λ)` in terms of those of `λ`, `λ − 1`.
-/

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero

/-! ### Finite places along an isomorphism of number fields -/

section MapEquiv

variable {k k' : Type*} [Field k] [NumberField k] [Field k'] [NumberField k']

/-- **The bijection of finite places along an isomorphism** `e : k ≃+* k'` of number fields:
the place of the prime `(e⁻¹)⁻¹(𝔭_v) = e(𝔭_v)` of `𝓞 k'`. -/
noncomputable def FinitePlace.mapEquiv (e : k ≃+* k') : FinitePlace k ≃ FinitePlace k' :=
  FinitePlace.equivHeightOneSpectrum.trans
    ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).trans
      FinitePlace.equivHeightOneSpectrum.symm)

variable (e : k ≃+* k') (v : FinitePlace k)

lemma FinitePlace.mapEquiv_maximalIdeal :
    (FinitePlace.mapEquiv e v).maximalIdeal.asIdeal =
      v.maximalIdeal.asIdeal.comap ((RingOfIntegers.mapRingEquiv e).symm : 𝓞 k' →+* 𝓞 k) := by
  simp only [FinitePlace.mapEquiv, Equiv.trans_apply, FinitePlace.equivHeightOneSpectrum_apply,
    HeightOneSpectrum.equivOfRingEquiv_apply]
  exact congrArg HeightOneSpectrum.asIdeal (FinitePlace.maximalIdeal_mk _)

/-- The valuation of the transported place is the valuation of `e⁻¹`. -/
lemma FinitePlace.mapEquiv_valuation (x : k') :
    (FinitePlace.mapEquiv e v).maximalIdeal.valuation k' x =
      v.maximalIdeal.valuation k (e.symm x) :=
  valuation_of_comap ((RingOfIntegers.mapRingEquiv e).symm : 𝓞 k' →+* 𝓞 k)
    (RingOfIntegers.mapRingEquiv e).symm.bijective (FinitePlace.mapEquiv_maximalIdeal e v)
    (e.symm : k' →+* k) (fun _ => rfl) x

/-- The absolute norm of the prime of the transported place. -/
lemma FinitePlace.mapEquiv_absNorm :
    Ideal.absNorm (FinitePlace.mapEquiv e v).maximalIdeal.asIdeal =
      Ideal.absNorm v.maximalIdeal.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  have hIJ : v.maximalIdeal.asIdeal =
      (FinitePlace.mapEquiv e v).maximalIdeal.asIdeal.map
        ((RingOfIntegers.mapRingEquiv e).symm : 𝓞 k' →+* 𝓞 k) := by
    rw [FinitePlace.mapEquiv_maximalIdeal,
      Ideal.map_comap_of_surjective (f := ((RingOfIntegers.mapRingEquiv e).symm : 𝓞 k' →+* 𝓞 k))
        (RingOfIntegers.mapRingEquiv e).symm.surjective]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv e).symm hIJ).toEquiv

/-- The absolute value of the transported place is the absolute value of `e⁻¹`. -/
lemma FinitePlace.mapEquiv_apply (x : k') :
    FinitePlace.mapEquiv e v x = v (e.symm x) := by
  rw [← FinitePlace.norm_embedding_eq, ← FinitePlace.norm_embedding_eq,
    FinitePlace.norm_embedding', FinitePlace.norm_embedding', FinitePlace.mapEquiv_valuation]
  congr 1
  refine toNNReal_congr ?_ _ _ _
  exact_mod_cast FinitePlace.mapEquiv_absNorm e v

/-- The transported place has the same residue characteristic. -/
lemma FinitePlace.mapEquiv_residueChar :
    residueChar (FinitePlace.mapEquiv e v) = residueChar v := by
  rw [← natCast_mem_maximalIdeal_iff _ (residueChar_prime v), FinitePlace.mapEquiv_maximalIdeal,
    Ideal.mem_comap, map_natCast]
  exact (natCast_mem_maximalIdeal_iff v (residueChar_prime v)).mpr rfl

end MapEquiv

/-! ### The sum of the local degrees over a rational prime -/

section LocalDeg

variable {K : Type*} [Field K] [NumberField K]

/-- `[K_w : ℚ_p] = e(𝔭_w/(p)) f(𝔭_w/(p))` for `p` the residue characteristic of `w`. -/
lemma localDeg_eq_ramificationIdx'_mul_inertiaDeg' (w : FinitePlace K) {q : ℕ}
    (hq : residueChar w = q) :
    localDeg K w = (Ideal.span {(q : ℤ)}).ramificationIdx' w.maximalIdeal.asIdeal *
      (Ideal.span {(q : ℤ)}).inertiaDeg' w.maximalIdeal.asIdeal := by
  subst hq
  rw [← under_int_eq]
  haveI : w.maximalIdeal.asIdeal.LiesOver (w.maximalIdeal.asIdeal.under ℤ) := inferInstance
  haveI : (w.maximalIdeal.asIdeal.under ℤ).IsMaximal := under_int_isMaximal w
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  unfold localDeg ramIdx inertDeg
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ w.maximalIdeal.asIdeal (under_int_ne_bot w),
    Ideal.inertiaDeg'_eq_inertiaDeg _ w.maximalIdeal.asIdeal]

/-- `∑_{w ∈ S, p_w = q} [K_w : ℚ_q] ≤ [K : ℚ]` for every finite set `S` of places of `K`
(from `∑_{w ∣ q} e_w f_w = [K : ℚ]`). -/
lemma sum_localDeg_filter_le (S : Finset (FinitePlace K)) (q : ℕ) :
    ∑ w ∈ S.filter (fun w => residueChar w = q), localDeg K w ≤ Module.finrank ℚ K := by
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
    have hsum := Ideal.sum_ramification_inertia (𝓞 K) ℚ K hp0 (p := p)
    set T := S.filter (fun w => residueChar w = q) with hT
    have hover : ∀ w ∈ T, w.maximalIdeal.asIdeal.LiesOver p := by
      intro w hw
      rw [hT, Finset.mem_filter] at hw
      rw [hp, ← hw.2]
      exact liesOver_span_residueChar w
    have hsub : T.image (fun w : FinitePlace K => w.maximalIdeal.asIdeal) ⊆
        IsDedekindDomain.primesOverFinset p (𝓞 K) := by
      intro P hP
      rw [Finset.mem_image] at hP
      obtain ⟨w, hw, rfl⟩ := hP
      exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mpr
        ⟨inferInstance, hover w hw⟩
    have hinj : Set.InjOn (fun w : FinitePlace K => w.maximalIdeal.asIdeal) T := by
      intro w₁ _ w₂ _ h
      exact FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h)
    calc ∑ w ∈ T, localDeg K w
        = ∑ w ∈ T, p.ramificationIdx' w.maximalIdeal.asIdeal *
            p.inertiaDeg' w.maximalIdeal.asIdeal := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [hT, Finset.mem_filter] at hw
          exact localDeg_eq_ramificationIdx'_mul_inertiaDeg' w hw.2
      _ = ∑ P ∈ T.image (fun w : FinitePlace K => w.maximalIdeal.asIdeal),
            p.ramificationIdx' P * p.inertiaDeg' P :=
          (Finset.sum_image (f := fun P => p.ramificationIdx' P * p.inertiaDeg' P) hinj).symm
      _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 K),
            p.ramificationIdx' P * p.inertiaDeg' P :=
          Finset.sum_le_sum_of_subset hsub
      _ = Module.finrank ℚ K := hsum
  · refine le_of_eq_of_le (Finset.sum_eq_zero ?_) (Nat.zero_le _)
    intro w hw
    rw [Finset.mem_filter] at hw
    exact absurd (hw.2 ▸ residueChar_prime w) hq

/-- `∑_{w ∈ S, p_w = q} f_w ≤ [K : ℚ]` for every finite set `S` of places of `K`. -/
lemma sum_inertDeg_filter_le (S : Finset (FinitePlace K)) (q : ℕ) :
    ∑ w ∈ S.filter (fun w => residueChar w = q), inertDeg K w ≤ Module.finrank ℚ K := by
  refine le_trans (Finset.sum_le_sum fun w _ => ?_) (sum_localDeg_filter_le S q)
  unfold localDeg
  exact Nat.le_mul_of_pos_left _ (ramIdx_pos' w)

end LocalDeg

/-! ### The valuation of `j(E_λ)` -/

section LegendreValuation

open WeierstrassCurve Iut.Tripod

variable {K : Type*} [Field K] [NeZero (2 : K)] (v : Valuation K ℤᵐ⁰) {l : K}
  [(legendre l).IsElliptic]

/-- The nonvanishing of the factors of `j(E_λ)`, from `v(j) ≠ 0`. -/
lemma valuation_legendre_ne_zero (hj : v (legendre l).j ≠ 0) :
    v 256 ≠ 0 ∧ v (l ^ 2 - l + 1) ≠ 0 ∧ v l ≠ 0 ∧ v (l - 1) ≠ 0 := by
  have hl0 : l ≠ 0 := ne_zero_of_legendre_isElliptic
  have hl1 : l - 1 ≠ 0 := sub_ne_zero.mpr ne_one_of_legendre_isElliptic
  rw [legendre_j, map_div₀, map_mul, map_pow] at hj
  have hnum := (div_ne_zero_iff.mp hj).1
  exact ⟨(mul_ne_zero_iff.mp hnum).1,
    (pow_ne_zero_iff (by norm_num)).mp (mul_ne_zero_iff.mp hnum).2,
    (Valuation.ne_zero_iff v).mpr hl0, (Valuation.ne_zero_iff v).mpr hl1⟩

/-- `log v(j) = log v(256) + 3 log v(λ² − λ + 1) − 2 log v(λ) − 2 log v(λ − 1)`. -/
lemma log_valuation_legendre_j (hj : v (legendre l).j ≠ 0) :
    log (v (legendre l).j) = log (v 256) + 3 * log (v (l ^ 2 - l + 1)) -
      (2 * log (v l) + 2 * log (v (l - 1))) := by
  obtain ⟨h256, hc, hvl, hvl1⟩ := valuation_legendre_ne_zero v hj
  rw [legendre_j, map_div₀, map_mul, map_pow, map_mul, map_pow, map_pow,
    log_div (mul_ne_zero h256 (pow_ne_zero _ hc))
      (mul_ne_zero (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1)),
    log_mul h256 (pow_ne_zero _ hc), log_pow, log_mul (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1),
    log_pow, log_pow]
  simp only [nsmul_eq_mul]
  push_cast
  ring

omit [NeZero (2 : K)] [(legendre l).IsElliptic] in
/-- `log v(λ² − λ + 1) ≤ log v(λ) + log v(λ − 1)` or `≤ 0` (ultrametric inequality for
`λ² − λ + 1 = λ(λ − 1) + 1`). -/
lemma log_valuation_sq_sub_add_one_le (hc : v (l ^ 2 - l + 1) ≠ 0) (hl : v l ≠ 0)
    (hl1 : v (l - 1) ≠ 0) :
    log (v (l ^ 2 - l + 1)) ≤ log (v l) + log (v (l - 1)) ∨ log (v (l ^ 2 - l + 1)) ≤ 0 := by
  have h : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
  rw [h] at hc ⊢
  rcases Valuation.map_add' v (l * (l - 1)) 1 with h1 | h1
  · left
    rw [map_mul] at h1
    rw [← log_mul hl hl1]
    exact (log_le_log hc (mul_ne_zero hl hl1)).mpr h1
  · right
    rw [map_one] at h1
    have := (log_le_log hc one_ne_zero).mpr h1
    simpa using this

/-- **The bound on `log v(j(E_λ))`**: if `v(256) ≤ 1` then
`log v(j) ≤ 2|log v(λ)| + 2|log v(λ − 1)|`. -/
lemma log_valuation_legendre_j_le (h256 : v 256 ≤ 1) (hj : v (legendre l).j ≠ 0) :
    log (v (legendre l).j) ≤ 2 * |log (v l)| + 2 * |log (v (l - 1))| := by
  obtain ⟨h256', hc, hvl, hvl1⟩ := valuation_legendre_ne_zero v hj
  have hd : log (v 256) ≤ 0 := by
    have := (log_le_log h256' one_ne_zero).mpr h256
    simpa using this
  rw [log_valuation_legendre_j v hj]
  have ha := le_abs_self (log (v l))
  have ha' := neg_abs_le (log (v l))
  have hb := le_abs_self (log (v (l - 1)))
  have hb' := neg_abs_le (log (v (l - 1)))
  have ha0 := abs_nonneg (log (v l))
  have hb0 := abs_nonneg (log (v (l - 1)))
  rcases log_valuation_sq_sub_add_one_le v hc hvl hvl1 with h | h
  · linarith
  · linarith

/-- **`v(j(E_λ)) > 1` at a place where `λ` meets `{0, 1, ∞}`**, for `v(2) = 1`: if
`v(λ) ≠ 1` or `v(λ − 1) ≠ 1` then `v(j) > 1`. -/
lemma one_lt_valuation_legendre_j (h2 : v 2 = 1) (h : v l ≠ 1 ∨ v (l - 1) ≠ 1) :
    1 < v (legendre l).j := by
  have h256 : v 256 = 1 := by
    have : (256 : K) = 2 ^ 8 := by norm_num
    rw [this, map_pow, h2, one_pow]
  have hl0 : l ≠ 0 := ne_zero_of_legendre_isElliptic
  have hl1 : l - 1 ≠ 0 := sub_ne_zero.mpr ne_one_of_legendre_isElliptic
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hl0
  have hvl1 : v (l - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr hl1
  have key : ∃ c : ℤᵐ⁰, v (l ^ 2 - l + 1) = c ∧ c ≠ 0 ∧
      0 < 3 * log c - (2 * log (v l) + 2 * log (v (l - 1))) := by
    rcases lt_trichotomy (v l) 1 with hlt | heq | hgt
    · -- `v(λ) < 1`: `v(λ − 1) = 1` and `v(λ² − λ + 1) = 1`
      have hb : v (l - 1) = 1 := by
        rw [Valuation.map_sub_eq_of_lt_right v (by rw [map_one]; exact hlt), map_one]
      have hc : v (l ^ 2 - l + 1) = 1 := by
        have hlt' : v (l ^ 2 - l) < v 1 := by
          rw [map_one]
          refine lt_of_le_of_lt (Valuation.map_sub v _ _) (max_lt ?_ hlt)
          rw [map_pow]
          exact pow_lt_one₀ zero_le hlt (by norm_num)
        rw [Valuation.map_add_eq_of_lt_right v hlt', map_one]
      refine ⟨1, hc, one_ne_zero, ?_⟩
      have : log (v l) < 0 := by
        rw [← log_one]
        exact (log_lt_log hvl one_ne_zero).mpr hlt
      rw [hb, log_one]
      linarith
    · -- `v(λ) = 1`, so `v(λ − 1) < 1` and `v(λ² − λ + 1) = 1`
      have hb : v (l - 1) ≠ 1 := h.resolve_left (not_not.mpr heq)
      have hb' : v (l - 1) < 1 := by
        refine lt_of_le_of_ne ?_ hb
        have := Valuation.map_sub v l 1
        rwa [heq, map_one, max_self] at this
      have hc : v (l ^ 2 - l + 1) = 1 := by
        have e : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
        have hlt' : v (l * (l - 1)) < v 1 := by
          rw [map_mul, heq, one_mul, map_one]; exact hb'
        rw [e, Valuation.map_add_eq_of_lt_right v hlt', map_one]
      refine ⟨1, hc, one_ne_zero, ?_⟩
      have : log (v (l - 1)) < 0 := by
        rw [← log_one]
        exact (log_lt_log hvl1 one_ne_zero).mpr hb'
      rw [heq, log_one]
      linarith
    · -- `v(λ) > 1`: `v(λ − 1) = v(λ)` and `v(λ² − λ + 1) = v(λ)²`
      have hb : v (l - 1) = v l :=
        Valuation.map_sub_eq_of_lt_left v (by rw [map_one]; exact hgt)
      have hc : v (l ^ 2 - l + 1) = v l ^ 2 := by
        have e : l ^ 2 - l + 1 = l ^ 2 + (1 - l) := by ring
        have hlt' : v (1 - l) < v (l ^ 2) := by
          rw [Valuation.map_sub_swap, hb, map_pow]
          exact lt_self_pow₀ hgt (by norm_num)
        rw [e, Valuation.map_add_eq_of_lt_left v hlt', map_pow]
      refine ⟨v l ^ 2, hc, pow_ne_zero _ hvl, ?_⟩
      have : 0 < log (v l) := by
        rw [← log_one]
        exact (log_lt_log one_ne_zero hvl).mpr hgt
      rw [hb, log_pow]
      simp only [nsmul_eq_mul]
      push_cast
      linarith
  obtain ⟨c, hc, hc0, hpos⟩ := key
  have hj : v (legendre l).j ≠ 0 := by
    rw [legendre_j, map_div₀, map_mul, map_pow, hc, h256, map_mul, map_pow, map_pow]
    exact div_ne_zero (mul_ne_zero one_ne_zero (pow_ne_zero _ hc0))
      (mul_ne_zero (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1))
  rw [← exp_log hj, ← exp_zero, exp_lt_exp, log_valuation_legendre_j v hj, h256, log_one, hc]
  linarith

/-- The converse: `v(j(E_λ)) > 1` forces `v(λ) ≠ 1` or `v(λ − 1) ≠ 1`, for `v(256) ≤ 1`. -/
lemma ne_one_or_ne_one_of_one_lt_valuation_legendre_j (h256 : v 256 ≤ 1)
    (h : 1 < v (legendre l).j) : v l ≠ 1 ∨ v (l - 1) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hj : v (legendre l).j ≠ 0 := ne_of_gt (zero_lt_one.trans h)
  have hle := log_valuation_legendre_j_le v h256 hj
  rw [hcon.1, hcon.2, log_one, abs_zero] at hle
  have : log (v (legendre l).j) ≤ 0 := by simpa using hle
  rw [← exp_log hj, ← exp_zero, exp_lt_exp] at h
  omega

end LegendreValuation

/-! ### The order of the Tate parameter is the order of the pole of `j` -/

namespace EllipticCurveData

open TateCurvesTheta

variable (C : EllipticCurveData) {w : FinitePlace C.F}

/-- **`v_w(j(E)) = exp(ord_w(q_w))`** at a multiplicative place: `‖j‖ = ‖q‖⁻¹` for the Tate
curve, and `j(E_{q_w}) = j(E)`. -/
lemma valuation_j_eq_exp_qOrder (hw : w ∈ C.badAll) :
    w.maximalIdeal.valuation C.F C.E.j = exp ((C.tateInputs.qOrder w hw : ℕ) : ℤ) := by
  have hq : Valued.v ((C.tateInputs.tate w hw).q : localCompletion w) =
      exp (-((C.tateInputs.qOrder w hw : ℕ) : ℤ)) :=
    valued_tateParameter_q _ (C.tateInputs.unif_isUniformizer w hw)
  have hJ : (C.tateInputs.tate w hw).tateJ = FinitePlace.embedding w.maximalIdeal C.E.j :=
    C.tateInputs.tateJ_eq w hw
  have hnorm : ‖(C.tateInputs.tate w hw).tateJ‖ =
      ‖((C.tateInputs.tate w hw).q : localCompletion w)‖⁻¹ :=
    (C.tateInputs.tate w hw).norm_tateJ (twelve_ne_zero w)
  have hq0 : ((C.tateInputs.tate w hw).q : localCompletion w) ≠ 0 :=
    (C.tateInputs.tate w hw).q.ne_zero
  have h1 : ‖(C.tateInputs.tate w hw).tateJ * ((C.tateInputs.tate w hw).q : localCompletion w)‖
      = 1 := by
    rw [norm_mul, hnorm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq0)]
  rw [norm_eq_one_iff_valued, map_mul, hJ, hq, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation', exp_neg] at h1
  rw [eq_inv_of_mul_eq_one_left h1, inv_inv]

end EllipticCurveData

end Iut

namespace Iut.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero

/-! ### The tripodal field `F_tpd = ℚ(λ) ⊆ F_λ` and its identification with `ℚ(λ) ⊆ ℚ̄` -/

variable (P : CurveProviders) (x : Pt)

/-- The tripodal field `F_tpd = ℚ(j, x(E_λ[2])) = ℚ(λ)` of the curve of `x`, as an intermediate
field of `F_λ`. -/
noncomputable abbrev tpd : IntermediateField ℚ (P.curve x).F :=
  tripodalFieldOf (P.curve x).F (P.curve x).E

/-- `λ` as an element of `F_λ = (P.curve x).F`. -/
noncomputable abbrev genC' : (P.curve x).F := genC x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)

/-- The curve of `x` is the Legendre curve of `λ`. -/
theorem curve_E_eq : (P.curve x).E = legendre (genC' P x) := rfl

instance : (legendre (genC' P x)).IsElliptic := (P.curve x).isElliptic

/-- `λ ∈ F_tpd`. -/
theorem genC_mem_tpd : genC' P x ∈ tpd P x := by
  change _ ∈ tripodalFieldOf (curveOf x _ _).F (curveOf x _ _).E
  rw [tripodalFieldOf_eq]
  exact IntermediateField.mem_adjoin_simple_self ℚ _

/-- `λ` as an element of `F_tpd`. -/
noncomputable def genT : tpd P x := ⟨_, genC_mem_tpd P x⟩

@[simp] theorem coe_genT : (genT P x : (P.curve x).F) = genC' P x := rfl

theorem algebraMap_genT : algebraMap (tpd P x) (P.curve x).F (genT P x) = genC' P x := rfl

theorem genT_ne_zero : genT P x ≠ 0 := fun h => gen'_ne_zero x.2.1 (congrArg Subtype.val h)

theorem genT_sub_one_ne_zero : genT P x - 1 ≠ 0 := by
  intro h
  exact gen'_ne_one x.2.2 (congrArg Subtype.val (sub_eq_zero.mp h))

/-- **`F_tpd ≃ ℚ(λ)`**: the tripodal field of `E_λ` inside `F_λ` is isomorphic to the minimal
field of definition `ℚ(λ) ⊆ ℚ̄` of `λ`. -/
noncomputable def tpdEquiv : tpd P x ≃ₐ[ℚ] fieldOf x.1 :=
  (IntermediateField.equivOfEq (tripodalFieldOf_eq x (P.torsionFinite3 x.1)
    (P.torsionFinite5 x.1))).trans (adjoinGenCEquiv x _ _)

theorem tpdEquiv_genT : tpdEquiv P x (genT P x) = gen x.1 := by
  apply Subtype.ext
  rfl

theorem tpdEquiv_symm_gen : (tpdEquiv P x).symm (gen x.1) = genT P x := by
  rw [← tpdEquiv_genT, AlgEquiv.symm_apply_apply]

/-- `[F_tpd : ℚ] = deg λ`. -/
theorem finrank_tpd : Module.finrank ℚ (tpd P x) = deg x.1 := by
  rw [(tpdEquiv P x).toLinearEquiv.finrank_eq, deg_eq_finrank]

/-- The place of `ℚ(λ) ⊆ ℚ̄` corresponding to a place of `F_tpd`. -/
noncomputable abbrev tpdPlace (𝔭 : FinitePlace (tpd P x)) : FinitePlace (fieldOf x.1) :=
  FinitePlace.mapEquiv (tpdEquiv P x : tpd P x ≃+* fieldOf x.1) 𝔭

theorem tpdPlace_gen (𝔭 : FinitePlace (tpd P x)) : tpdPlace P x 𝔭 (gen x.1) = 𝔭 (genT P x) := by
  rw [tpdPlace, FinitePlace.mapEquiv_apply]
  congr 1
  exact tpdEquiv_symm_gen P x

theorem tpdPlace_gen_sub_one (𝔭 : FinitePlace (tpd P x)) :
    tpdPlace P x 𝔭 (gen x.1 - 1) = 𝔭 (genT P x - 1) := by
  rw [tpdPlace, FinitePlace.mapEquiv_apply, map_sub, map_one]
  congr 2
  exact tpdEquiv_symm_gen P x

theorem residueChar_tpdPlace (𝔭 : FinitePlace (tpd P x)) :
    residueChar (tpdPlace P x 𝔭) = residueChar 𝔭 :=
  FinitePlace.mapEquiv_residueChar _ _

theorem absNorm_tpdPlace (𝔭 : FinitePlace (tpd P x)) :
    Ideal.absNorm (tpdPlace P x 𝔭).maximalIdeal.asIdeal = Ideal.absNorm 𝔭.maximalIdeal.asIdeal :=
  FinitePlace.mapEquiv_absNorm _ _

/-! ### The absolute value at a place in terms of the valuation -/

/-- `log|y|_𝔭 = log v_𝔭(y) · f_𝔭 · log p`. -/
theorem log_apply_eq {T : Type*} [Field T] [NumberField T] (𝔭 : FinitePlace T) {y : T}
    (hy : y ≠ 0) :
    Real.log (𝔭 y) = ((log (𝔭.maximalIdeal.valuation T y) : ℤ) : ℝ) *
      (inertDeg T 𝔭 * Real.log (residueChar 𝔭)) := by
  have hv : 𝔭.maximalIdeal.valuation T y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  rw [← FinitePlace.norm_embedding_eq,
    norm_eq_zpow_of_valued 𝔭 _ (log (𝔭.maximalIdeal.valuation T y)) (by
      rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation', exp_log hv]),
    Real.log_zpow, Real.log_pow]

/-- A compactly bounded subset has a nonnegative bound as soon as it is nonempty. -/
theorem CompactlyBounded.c_nonneg {K : CompactlyBounded} {x : Pt} (hx : x ∈ K.set) : 0 ≤ K.c := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace (fieldOf x.1)) := inferInstance
  exact (abs_nonneg _).trans (hx.2 w).1

/-- **The bound of a compactly bounded subset at a place of `F_tpd`**: for `𝔭` of residue
characteristic in `V`, `|ord_𝔭(λ)|·f_𝔭·log p ≤ c` and `|ord_𝔭(λ − 1)|·f_𝔭·log p ≤ c`. -/
theorem abs_log_valuation_mul_le {K : CompactlyBounded} (hx : x ∈ K.set)
    (𝔭 : FinitePlace (tpd P x)) (h𝔭 : residueChar 𝔭 ∈ K.V) :
    |((log (𝔭.maximalIdeal.valuation _ (genT P x)) : ℤ) : ℝ)| *
        (inertDeg (tpd P x) 𝔭 * Real.log (residueChar 𝔭)) ≤ K.c ∧
      |((log (𝔭.maximalIdeal.valuation _ (genT P x - 1)) : ℤ) : ℝ)| *
        (inertDeg (tpd P x) 𝔭 * Real.log (residueChar 𝔭)) ≤ K.c := by
  have hb := hx.1 (tpdPlace P x 𝔭) (by rwa [residueChar_tpdPlace])
  rw [tpdPlace_gen, tpdPlace_gen_sub_one, log_apply_eq _ (genT_ne_zero P x),
    log_apply_eq _ (genT_sub_one_ne_zero P x)] at hb
  have hpos : 0 ≤ (inertDeg (tpd P x) 𝔭 : ℝ) * Real.log (residueChar 𝔭) :=
    mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _)
  obtain ⟨h1, h2⟩ := hb
  rw [abs_mul, abs_of_nonneg hpos] at h1 h2
  exact ⟨h1, h2⟩

/-! ### The `2`-adic bound -/

/-- `v_w(256) ≤ 1` at every finite place. -/
theorem valuation_256_le_one {T : Type*} [Field T] [NumberField T] (w : FinitePlace T) :
    w.maximalIdeal.valuation T 256 ≤ 1 := by
  have : (256 : T) = algebraMap (𝓞 T) T 256 := by rw [map_ofNat]
  rw [this]
  exact valuation_le_one _ _

/-- The real-number bookkeeping of `term_le`. -/
lemma term_le_aux {N A B E Fr Fp L D c : ℝ} (hN : N ≤ 2 * E * (A + B))
    (hA : A * (Fp * L) ≤ c) (hB : B * (Fp * L) ≤ c) (hE : 0 ≤ E) (hFr : 0 ≤ Fr) (hFp : 0 ≤ Fp)
    (hL : 0 ≤ L) (hD : 1 ≤ D) (hc : 0 ≤ c) :
    N * (Fp * Fr) * L ≤ 4 * c * (D * (E * Fr)) := by
  calc N * (Fp * Fr) * L = N * (Fr * (Fp * L)) := by ring
    _ ≤ 2 * E * (A + B) * (Fr * (Fp * L)) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
    _ = 2 * E * Fr * (A * (Fp * L) + B * (Fp * L)) := by ring
    _ ≤ 2 * E * Fr * (c + c) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
    _ = 4 * c * (1 * (E * Fr)) := by ring
    _ ≤ 4 * c * (D * (E * Fr)) := by gcongr

/-- **The local bound at a place over `2`**: for `w ∣ 𝔭` with `w` multiplicative and
`p_𝔭 = 2 ∈ V`, `h_w f_w log 2 ≤ 4c·[F_w : ℚ_2]`. -/
theorem term_le {K : CompactlyBounded} (hx : x ∈ K.set) {w : FinitePlace (P.curve x).F}
    (hw : w ∈ (P.curve x).badAll) (hw2 : residueChar w = 2) :
    ((P.tate x).qOrder w hw : ℝ) * inertDeg (P.curve x).F w * Real.log (residueChar w) ≤
      4 * K.c * localDeg (P.curve x).F w := by
  set 𝔭 : FinitePlace (tpd P x) := placeUnder w with h𝔭
  have hw𝔭 : FinitePlace.LiesOver w 𝔭 := liesOver_placeUnder w
  have h𝔭2 : residueChar 𝔭 = 2 := by rw [← residueChar_eq_of_liesOver hw𝔭, hw2]
  have hc := CompactlyBounded.c_nonneg hx
  -- the order of the Tate parameter is `log v_w(j)`
  have hvj := (P.curve x).valuation_j_eq_exp_qOrder hw
  have hj0 : w.maximalIdeal.valuation _ (P.curve x).E.j ≠ 0 := by rw [hvj]; exact exp_ne_zero
  have hn : ((P.tate x).qOrder w hw : ℤ) ≤
      2 * |log (w.maximalIdeal.valuation _ (genC' P x))| +
        2 * |log (w.maximalIdeal.valuation _ (genC' P x - 1))| := by
    have this : log (w.maximalIdeal.valuation _ (P.curve x).E.j) ≤
        2 * |log (w.maximalIdeal.valuation _ (genC' P x))| +
          2 * |log (w.maximalIdeal.valuation _ (genC' P x - 1))| :=
      log_valuation_legendre_j_le (w.maximalIdeal.valuation (P.curve x).F)
        (l := genC' P x) (valuation_256_le_one w) hj0
    rwa [hvj, log_exp] at this
  -- the valuations at `w` are the `e(w/𝔭)`-th powers of those at `𝔭`
  set e : ℕ := relRamIdx w 𝔭 with he
  have ha : log (w.maximalIdeal.valuation _ (genC' P x)) =
      e * log (𝔭.maximalIdeal.valuation _ (genT P x)) := by
    rw [← algebraMap_genT, valuation_algebraMap_eq_pow hw𝔭, log_pow, nsmul_eq_mul]
  have hb : log (w.maximalIdeal.valuation _ (genC' P x - 1)) =
      e * log (𝔭.maximalIdeal.valuation _ (genT P x - 1)) := by
    rw [← algebraMap_genT, ← map_one (algebraMap (tpd P x) (P.curve x).F), ← map_sub,
      valuation_algebraMap_eq_pow hw𝔭, log_pow, nsmul_eq_mul]
  rw [ha, hb, abs_mul, abs_mul, Nat.abs_cast] at hn
  -- the bound of the compactly bounded subset at `𝔭`
  obtain ⟨hA, hB⟩ := abs_log_valuation_mul_le P x hx 𝔭 (by rw [h𝔭2]; exact K.two_mem)
  rw [h𝔭2] at hA hB
  -- the residue degrees and local degrees
  have hf : (inertDeg (P.curve x).F w : ℝ) = inertDeg (tpd P x) 𝔭 * relInertDeg w 𝔭 := by
    rw [inertDeg_eq_mul hw𝔭]; push_cast; ring
  have hd : (localDeg (P.curve x).F w : ℝ) = localDeg (tpd P x) 𝔭 * (e * relInertDeg w 𝔭) := by
    rw [localDeg_eq_mul hw𝔭]; push_cast; ring
  have hD : (1 : ℝ) ≤ localDeg (tpd P x) 𝔭 := by
    exact_mod_cast Nat.mul_pos (ramIdx_pos' 𝔭) (inertDeg_pos' 𝔭)
  have hn' : ((P.tate x).qOrder w hw : ℝ) ≤ 2 * e *
      (|((log (𝔭.maximalIdeal.valuation _ (genT P x)) : ℤ) : ℝ)| +
        |((log (𝔭.maximalIdeal.valuation _ (genT P x - 1)) : ℤ) : ℝ)|) := by
    have h := (Int.cast_le (R := ℝ)).mpr hn
    push_cast at h
    linarith
  rw [hw2, hf, hd]
  exact term_le_aux hn' hA hB (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (log_natCast_nonneg _) hD hc

/-- **The `2`-adic bound** `TwoAdicBoundHyp P K (4c)`: on a compactly bounded subset with
bound `c`, the contribution of the places over `2` to `log(q_∀(E_λ))` is at most `4c`. -/
theorem twoAdicBound' (K : CompactlyBounded) : TwoAdicBoundHyp P K (4 * K.c) := by
  intro x hx
  classical
  have hc := CompactlyBounded.c_nonneg hx
  change (∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => residueChar w = 2),
      (((if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0 : ℕ) : ℝ) *
        (inertDeg (P.curve x).F w : ℝ) * Real.log (residueChar w))) /
      (Module.finrank ℚ (P.curve x).F : ℝ) ≤ 4 * K.c
  rw [div_le_iff₀ (by exact_mod_cast Module.finrank_pos)]
  calc ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => residueChar w = 2),
        (((if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0 : ℕ) : ℝ) *
          (inertDeg (P.curve x).F w : ℝ) * Real.log (residueChar w))
      ≤ ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => residueChar w = 2),
          4 * K.c * (localDeg (P.curve x).F w : ℝ) := by
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hw
        split_ifs with h
        · exact term_le P x hx h hw.2
        · exact absurd hw.1 h
    _ = 4 * K.c * ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => residueChar w = 2),
          (localDeg (P.curve x).F w : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 4 * K.c * (Module.finrank ℚ (P.curve x).F : ℝ) := by
        gcongr
        exact_mod_cast sum_localDeg_filter_le _ 2

/-- **The `2`-adic bound** in the form `TwoAdicBoundHyp P K (max (4c) 0)`, with a nonnegative
bound. -/
theorem twoAdicBound (K : CompactlyBounded) : TwoAdicBoundHyp P K (max (4 * K.c) 0) :=
  fun x hx => (twoAdicBound' P K x hx).trans (le_max_left _ _)

end Iut.Tripod
