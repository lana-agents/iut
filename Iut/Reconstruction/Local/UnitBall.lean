/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.LogVolumeLCFT
import Mathlib.NumberTheory.Padics.Hensel

/-!
# The two unit balls of a `p`-adic field always agree (roadmap MR11, shell #36)

Let `k` be a field with a rank-one discrete valuation `Valued k ℤᵐ⁰` (the framework of
`Iut.logShell`, `Iut/Concrete`) and a finite-dimensional `ℚ_p`-algebra structure (the framework
of `local-class-field-theory`, with its norm `PadicField.nrm`). We prove that the unit balls of the
two norms coincide, **with no compatibility assumption** between the two structures
(`hball_auto`). Hence the hypothesis `hball` of `LogVolumeLCFT.lean`, `LogShellIdent.lean`,
`LogLink/Galois.lean` (shell #36 of the multiradial ROADMAP) is always satisfied; previously it was
discharged only for continuous `ℚ_p → k` (`hball_of_continuous`).

Proof. The valuation of `k` is determined by the field structure:

* every `u ∈ 1 + pℤ_p` is an `n`-th power in `ℤ_p` for every `n` prime to `p` (Hensel's lemma),
  so its valuation in `ℤ` is divisible by every `(p + 1)^j` and vanishes
  (`norm_algebraMap_eq_one_of_principal`); every `u ∈ ℤ_pˣ` has `u^{p-1} ∈ 1 + pℤ_p`, so
  `‖u‖ = 1` in `k` (`norm_algebraMap_unit`);
* `‖p‖ < 1` in `k`: `‖1 + p‖ = 1` excludes `‖p‖ > 1`, and if `‖p‖ = 1` then all of `ℚ_pˣ` has
  norm `1`, hence (`k` being algebraic over `ℚ_p`) all of `kˣ`, contradicting the nontriviality
  of a rank-one valuation (`norm_p_lt_one_auto`);
* so `‖a‖ ≤ 1` in `k` for `a ∈ ℤ_p`, and then the argument of `hball_of_continuous` applies.
-/

namespace Iut.Reconstruction

open PadicField Polynomial
open scoped Valued

set_option linter.unusedSectionVars false

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Roots in `1 + pℤ_p`**: for `n` prime to `p`, every `u ∈ ℤ_p` with `‖u − 1‖ < 1` is an
`n`-th power. -/
theorem PadicInt.exists_pow_eq_of_norm_sub_one_lt {n : ℕ} (hn : p.Coprime n) {u : ℤ_[p]}
    (hu : ‖u - 1‖ < 1) : ∃ y : ℤ_[p], y ^ n = u := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hp.out.one_lt.ne' (Nat.coprime_zero_right _ |>.1 hn)
  set F : Polynomial ℤ_[p] := X ^ n - C u
  have hF : F.aeval (1 : ℤ_[p]) = 1 - u := by simp [F]
  have hF' : F.derivative.aeval (1 : ℤ_[p]) = (n : ℤ_[p]) := by
    simp [F, derivative_X_pow]
  have hnn : ‖(n : ℤ_[p])‖ = 1 := by
    exact PadicInt.norm_natCast_eq_one_iff.2 hn
  have h : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [hF, hF', hnn, one_pow, norm_sub_rev]
    exact hu
  obtain ⟨z, hz, -⟩ := hensels_lemma h
  refine ⟨z, ?_⟩
  simpa [F, sub_eq_zero] using hz

variable {k : Type*} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [Algebra ℚ_[p] k]

theorem norm_eq_one_iff_v (x : k) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  constructor
  · intro h
    exact le_antisymm (Valued.toNormedField.norm_le_one_iff.1 h.le)
      (Valued.toNormedField.one_le_norm_iff.1 h.ge)
  · intro h
    exact le_antisymm (Valued.toNormedField.norm_le_one_iff.2 h.le)
      (Valued.toNormedField.one_le_norm_iff.2 h.ge)

/-- An element of `ℤᵐ⁰ ∖ {0}` that is an `n`-th power for every `n = (p + 1)^j` is `1`. -/
theorem eq_one_of_forall_pow {a : WithZero (Multiplicative ℤ)} (ha : a ≠ 0)
    (h : ∀ j : ℕ, ∃ b : WithZero (Multiplicative ℤ), b ^ ((p + 1) ^ j) = a) : a = 1 := by
  obtain ⟨m, rfl⟩ := WithZero.ne_zero_iff_exists.1 ha
  obtain ⟨N, hN⟩ : ∃ N, N = m.toAdd.natAbs := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ := h N
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ (Nat.succ_ne_zero _))] at hb
    exact WithZero.zero_ne_coe hb
  obtain ⟨c, rfl⟩ := WithZero.ne_zero_iff_exists.1 hb0
  rw [← WithZero.coe_pow, WithZero.coe_inj] at hb
  have hm : m.toAdd = ((p + 1) ^ N : ℕ) * c.toAdd := by
    rw [← hb, toAdd_pow, nsmul_eq_mul]
  have hlt : N < (p + 1) ^ N := Nat.lt_pow_self (by have := hp.out.one_lt; omega)
  have h0 : m.toAdd = 0 := by
    by_contra hne
    have hc : c.toAdd ≠ 0 := by
      rintro hc
      rw [hc, mul_zero] at hm
      exact hne hm
    have habs := congrArg Int.natAbs hm
    rw [Int.natAbs_mul, Int.natAbs_natCast, ← hN] at habs
    have hc1 : 1 ≤ c.toAdd.natAbs := Int.natAbs_pos.2 hc
    have : (p + 1) ^ N ≤ N :=
      calc (p + 1) ^ N ≤ (p + 1) ^ N * c.toAdd.natAbs := Nat.le_mul_of_pos_right _ hc1
        _ = N := habs.symm
    omega
  have : m = 1 := by
    rw [← ofAdd_toAdd m, h0, ofAdd_zero]
  rw [this, WithZero.coe_one]

/-- **Principal units of `ℤ_p` have norm one in `k`.** -/
theorem norm_algebraMap_eq_one_of_principal {u : ℤ_[p]} (hu : ‖u - 1‖ < 1) :
    ‖algebraMap ℚ_[p] k (u : ℚ_[p])‖ = 1 := by
  rw [norm_eq_one_iff_v]
  have hu0 : (u : ℚ_[p]) ≠ 0 := by
    intro h
    have : u = 0 := PadicInt.ext h
    rw [this, zero_sub, norm_neg, norm_one] at hu
    exact lt_irrefl _ hu
  refine eq_one_of_forall_pow (p := p) ?_ fun j => ?_
  · rw [Valuation.ne_zero_iff, _root_.map_ne_zero]
    exact hu0
  · have hcop : p.Coprime ((p + 1) ^ j) :=
      Nat.Coprime.pow_right _ (by simp [Nat.coprime_self_add_right])
    obtain ⟨y, hy⟩ := PadicInt.exists_pow_eq_of_norm_sub_one_lt hcop hu
    refine ⟨Valued.v (algebraMap ℚ_[p] k (y : ℚ_[p])), ?_⟩
    rw [← map_pow, ← map_pow, ← PadicInt.coe_pow, hy]

/-- **Units of `ℤ_p` have norm one in `k`.** -/
theorem norm_algebraMap_unit (u : ℤ_[p]ˣ) :
    ‖algebraMap ℚ_[p] k ((u : ℤ_[p]) : ℚ_[p])‖ = 1 := by
  have hres : PadicInt.toZMod ((u : ℤ_[p]) ^ (p - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, sub_eq_zero]
    have hne : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := by
      intro h0
      have := (Units.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p).toMonoidHom u).ne_zero
      exact this h0
    exact ZMod.pow_card_sub_one_eq_one hne
  have hmem : (u : ℤ_[p]) ^ (p - 1) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod]; exact hres
  have hlt : ‖(u : ℤ_[p]) ^ (p - 1) - 1‖ < 1 := PadicInt.mem_nonunits.1 hmem
  have h1 := norm_algebraMap_eq_one_of_principal (k := k) hlt
  rw [PadicInt.coe_pow, map_pow, norm_pow] at h1
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hp1).1 h1

theorem norm_p_le_one_auto : ‖(p : k)‖ ≤ 1 := by
  by_contra! h
  have hu : ‖((1 + p : ℤ_[p])) - 1‖ < 1 := by
    rw [add_sub_cancel_left, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have h1 := norm_algebraMap_eq_one_of_principal (k := k) hu
  have h2 : algebraMap ℚ_[p] k ((1 + p : ℤ_[p]) : ℚ_[p]) = 1 + (p : k) := by
    push_cast; simp
  rw [h2] at h1
  have h3 : ‖(1 : k) + p‖ = ‖(p : k)‖ := by
    rw [add_comm]
    exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne')
      |>.trans (max_eq_left (by rw [norm_one]; exact h.le))
  rw [h3] at h1
  exact h.ne' h1

/-- The norm in `k` of a nonzero `p`-adic integer is `‖p‖^{v_p(a)}`. -/
theorem norm_algebraMap_padicInt {a : ℤ_[p]} (ha : a ≠ 0) :
    ‖algebraMap ℚ_[p] k (a : ℚ_[p])‖ = ‖(p : k)‖ ^ a.valuation := by
  conv_lhs => rw [PadicInt.unitCoeff_spec ha]
  rw [PadicInt.coe_mul, map_mul, norm_mul, norm_algebraMap_unit, one_mul, PadicInt.coe_pow,
    map_pow, norm_pow]
  simp

theorem norm_algebraMap_le_one_auto {a : ℚ_[p]} (ha : ‖a‖ ≤ 1) :
    ‖algebraMap ℚ_[p] k a‖ ≤ 1 := by
  by_cases h0 : a = 0
  · simp [h0]
  set a' : ℤ_[p] := ⟨a, ha⟩
  have h0' : a' ≠ 0 := fun h => h0 (by
    have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) h
    simpa [a'] using this)
  have := norm_algebraMap_padicInt (k := k) h0'
  change ‖algebraMap ℚ_[p] k a‖ = _ at this
  rw [this]
  exact pow_le_one₀ (norm_nonneg _) norm_p_le_one_auto

variable [FiniteDimensional ℚ_[p] k]

/-- **Integrality bound**: if the coefficients of the minimal polynomial of `x` over `ℚ_p` have
norm `≤ 1` in `k`, then `‖x‖ ≤ 1`. -/
theorem norm_le_one_of_minpoly_coeff {x : k}
    (hx : ∀ i, ‖algebraMap ℚ_[p] k ((minpoly ℚ_[p] x).coeff i)‖ ≤ 1) : ‖x‖ ≤ 1 := by
  set f := minpoly ℚ_[p] x
  have hf : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hroot : Polynomial.aeval x f = 0 := minpoly.aeval _ _
  by_contra! hx1
  have hdeg : 0 < f.natDegree := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)
  have key : x ^ f.natDegree = -∑ i ∈ Finset.range f.natDegree,
      algebraMap ℚ_[p] k (f.coeff i) * x ^ i := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree,
      one_smul] at hroot
    simp only [Algebra.smul_def] at hroot
    linear_combination hroot
  have hlt : ‖∑ i ∈ Finset.range f.natDegree, algebraMap ℚ_[p] k (f.coeff i) * x ^ i‖ <
      ‖x‖ ^ f.natDegree := by
    have hpos : 0 ≤ ‖x‖ ^ (f.natDegree - 1) := pow_nonneg (norm_nonneg _) _
    refine lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hpos
      fun i hi => ?_) ?_
    · rw [norm_mul, norm_pow]
      calc ‖algebraMap ℚ_[p] k (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
            gcongr; exact hx i
        _ ≤ ‖x‖ ^ (f.natDegree - 1) := by
            rw [one_mul]
            exact pow_le_pow_right₀ hx1.le (by simp at hi; omega)
    · exact pow_lt_pow_right₀ hx1 (by omega)
  rw [← norm_pow, key, norm_neg] at hlt
  exact hlt.false

/-- **`‖p‖ < 1` in `k`.** -/
theorem norm_p_lt_one_auto : ‖(p : k)‖ < 1 := by
  refine lt_of_le_of_ne norm_p_le_one_auto fun h1 => ?_
  -- every element of `ℚ_p` has norm `≤ 1` in `k`, hence every element of `k`
  have hQ : ∀ a : ℚ_[p], ‖algebraMap ℚ_[p] k a‖ ≤ 1 := by
    intro a
    by_cases ha : ‖a‖ ≤ 1
    · exact norm_algebraMap_le_one_auto ha
    · have ha0 : a ≠ 0 := by rintro rfl; simp at ha
      -- `a = p^{-n} b` with `‖b‖ ≤ 1`
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(p : ℚ_[p]) ^ n * a‖ ≤ 1 := by
        refine ⟨(-(a.valuation)).toNat, ?_⟩
        rw [norm_mul, norm_pow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation ha0, inv_pow,
          ← zpow_natCast, ← zpow_neg]
        rw [← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]
        apply zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le)
        omega
      have hb := norm_algebraMap_le_one_auto (k := k) hn
      rw [map_mul, map_pow, norm_mul, norm_pow, map_natCast, h1, one_pow, one_mul] at hb
      exact hb
  have hall : ∀ x : k, ‖x‖ ≤ 1 := fun x => norm_le_one_of_minpoly_coeff fun i => hQ _
  obtain ⟨x, hx0, hx1⟩ :=
    Valuation.RankOne.nontrivial (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))
  have hx : x ≠ 0 := by rintro rfl; exact hx0 (map_zero _)
  apply hx1
  rw [← norm_eq_one_iff_v]
  refine le_antisymm (hall x) ?_
  have := hall x⁻¹
  rw [norm_inv] at this
  exact (inv_le_one₀ (norm_pos_iff.2 hx)).1 this

/-- `‖x‖ ≤ 1` for the elements of `k` that are integral over `ℤ_p`. -/
theorem norm_le_one_of_nrm_le_one_auto {x : k} (hx : nrm p k x ≤ 1) : ‖x‖ ≤ 1 := by
  replace hx := (nrm_le_one_iff_coeff (p := p) x).1 hx
  exact norm_le_one_of_minpoly_coeff fun i => norm_algebraMap_le_one_auto (hx i)

/-- **The unit balls of the valuation of `k` and of the spectral norm of `local-class-field-theory`
agree** — for every field `k` carrying both structures (shell #36). -/
theorem hball_auto (x : k) : ‖x‖ ≤ 1 ↔ nrm p k x ≤ 1 := by
  refine ⟨fun hx => ?_, norm_le_one_of_nrm_le_one_auto⟩
  by_contra! hx1
  have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero] at hx1; linarith
  have hy : nrm p k x⁻¹ < 1 := by
    rw [nrm_inv]; exact inv_lt_one_of_one_lt₀ hx1
  haveI : CharZero k := charZero_of_injective_algebraMap (algebraMap ℚ_[p] k).injective
  have hp0 : (0 : ℝ) < nrm p k (p : k) := nrm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hp0 hy
  have h1 : nrm p k (x⁻¹ ^ N / (p : k)) ≤ 1 := by
    rw [nrm_div, map_pow, div_le_one hp0]
    exact hN.le
  have h2 := norm_le_one_of_nrm_le_one_auto h1
  have hpk := norm_p_lt_one_auto (p := p) (k := k)
  have hp0' : (0 : ℝ) < ‖(p : k)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  rw [norm_div, norm_pow, div_le_one hp0'] at h2
  have h3 : 1 ≤ ‖x⁻¹‖ := by
    rw [norm_inv]; exact one_le_inv₀ (norm_pos_iff.2 hx0) |>.2 hx
  have := one_le_pow₀ (n := N) h3
  linarith

end

end Iut.Reconstruction
