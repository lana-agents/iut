/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# The Euler product of the Dedekind zeta function

Let `K` be a number field. For real `s > 1` we prove the Euler product of the Dedekind zeta
function `ζ_K(s) = ∑_I N(I)^{-s} = ∏_𝔭 (1 - N(𝔭)^{-s})⁻¹`, in logarithmic and in
multiplicative form, and deduce that the prime ideal zeta sum `∑_𝔭 N(𝔭)^{-s}` equals
`log (1 / (s - 1))` up to a bounded error on `(1, 2]`.

## Main results

* `NumberField.dedekindZeta_ofReal_eq_tsum`: for real `s > 1`, `ζ_K(s)` is the sum of
  `N(I)^{-s}` over all ideals `I` of `𝓞 K` (the zero ideal contributes `0`).
* `NumberField.hasSum_neg_log_one_sub_rpow_neg_absNorm`: **Euler product**, logarithmic form:
  `∑_𝔭 -log (1 - N(𝔭)^{-s}) = log ζ_K(s)`.
* `NumberField.hasProd_dedekindZeta`: **Euler product**:
  `∏_𝔭 (1 - N(𝔭)^{-s})⁻¹ = ζ_K(s)`.
* `NumberField.summable_rpow_neg_absNorm_heightOneSpectrum`: `∑_𝔭 N(𝔭)^{-s}` converges for
  `s > 1`.
* `NumberField.exists_abs_tsum_rpow_neg_absNorm_sub_log_le`: there is `C` with
  `|∑_𝔭 N(𝔭)^{-s} - log (1 / (s - 1))| ≤ C` for all `s ∈ (1, 2]`.

The sums over prime ideals are indexed by `IsDedekindDomain.HeightOneSpectrum (𝓞 K)`, as for
`NumberField.Set.primeIdealZetaSum` in Mathlib's `NumberTheory/NumberField/DirichletDensity`.

## Proof

The equality `ζ_K(s) = ∑_I N(I)^{-s}` follows by grouping ideals by their norm. The Euler
product is proved by comparing finite products of truncated geometric series with partial sums
over ideals, using unique factorisation of ideals
(`Ideal.finprod_heightOneSpectrum_factorization` and `FractionalIdeal.count_prod`). The size of
`ζ_K(s)` near `1` comes from `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`.
-/

noncomputable section

open Filter Topology IsDedekindDomain
open scoped nonZeroDivisors

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

section idealSum

variable {K}

lemma one_le_absNorm_heightOneSpectrum (P : HeightOneSpectrum (𝓞 K)) :
    1 ≤ Ideal.absNorm P.asIdeal :=
  Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)

lemma two_le_absNorm_heightOneSpectrum (P : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm P.asIdeal := by
  have h1 := one_le_absNorm_heightOneSpectrum P
  have h2 : Ideal.absNorm P.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact P.isPrime.ne_top
  omega

lemma rpow_neg_absNorm_nonneg (I : Ideal (𝓞 K)) (s : ℝ) :
    0 ≤ (Ideal.absNorm I : ℝ) ^ (-s) :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma rpow_neg_absNorm_heightOneSpectrum_le_inv (P : HeightOneSpectrum (𝓞 K)) {s : ℝ}
    (hs : 1 ≤ s) : (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
  have h1 : (1 : ℝ) ≤ Ideal.absNorm P.asIdeal := by
    exact_mod_cast one_le_absNorm_heightOneSpectrum P
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

lemma rpow_neg_absNorm_heightOneSpectrum_le_half (P : HeightOneSpectrum (𝓞 K)) {s : ℝ}
    (hs : 1 ≤ s) : (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ Ideal.absNorm P.asIdeal := by
    exact_mod_cast two_le_absNorm_heightOneSpectrum P
  refine (rpow_neg_absNorm_heightOneSpectrum_le_inv P hs).trans ?_
  rw [one_div]
  exact inv_anti₀ (by norm_num) h2

lemma rpow_neg_absNorm_antitone (I : Ideal (𝓞 K)) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    (Ideal.absNorm I : ℝ) ^ (-t) ≤ (Ideal.absNorm I : ℝ) ^ (-s) := by
  rcases eq_or_ne (Ideal.absNorm I) 0 with h | h
  · rw [h, Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
  · exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h) (by linarith)

end idealSum

/-! ### The Dedekind zeta function as a sum over ideals -/

section dedekindZeta

lemma LSeriesSummable_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s := by
  have hr : (dedekindZeta_residue K : ℂ) ≠ 0 := by
    exact_mod_cast dedekindZeta_residue_ne_zero K
  have hev := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).eventually_ne hr
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu : (1 : ℝ) < u := hu
  set s₀ : ℝ := min s.re ((1 + u) / 2)
  have hs₀ : s₀ ∈ Set.Ioo 1 u :=
    ⟨lt_min hs (by linarith), (min_le_right _ _).trans_lt (by linarith)⟩
  have hne : dedekindZeta K s₀ ≠ 0 := right_ne_zero_of_mul (hsub hs₀)
  have hsum : LSeriesSummable
      (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s₀ := by
    by_contra h
    exact hne (LSeries.eq_zero_of_not_LSeriesSummable _ _ h)
  exact hsum.of_re_le_re (by simp [s₀])

variable {K}

lemma term_dedekindZeta_ofReal {s : ℝ} (hs : s ≠ 0) (n : ℕ) :
    LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s n =
      ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow (neg_ne_zero.mpr hs)]
  · rw [LSeries.term_of_ne_zero hn, Real.rpow_neg (Nat.cast_nonneg _), ← div_eq_mul_inv]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl

lemma tsum_absNorm_fiber (s : ℝ) (n : ℕ) :
    ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, (Ideal.absNorm I.1 : ℝ) ^ (-s) =
      Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} * (n : ℝ) ^ (-s) := by
  rw [tsum_congr fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n} ↦ by rw [I.2], tsum_const,
    nsmul_eq_mul]

variable (K)

lemma summable_card_mul_rpow_neg {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ ↦
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} * (n : ℝ) ^ (-s) : ℝ) :=
  Complex.summable_ofReal.mp <| (LSeriesSummable_dedekindZeta K (s := s) (by simpa)).congr
    (term_dedekindZeta_ofReal (by linarith))

/-- For real `s > 1`, the sum `∑_I N(I)^{-s}` over all ideals of `𝓞 K` converges. -/
theorem summable_rpow_neg_absNorm {s : ℝ} (hs : 1 < s) :
    Summable fun I : Ideal (𝓞 K) ↦ (Ideal.absNorm I : ℝ) ^ (-s) := by
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ Ideal.absNorm I)).summable_iff]
  refine (summable_sigma_of_nonneg fun _ ↦ rpow_neg_absNorm_nonneg _ _).mpr ⟨fun n ↦ ?_, ?_⟩
  · have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq n).to_subtype
    exact Summable.of_finite
  · simp only [Equiv.sigmaFiberEquiv_apply]
    simp_rw [tsum_absNorm_fiber]
    exact summable_card_mul_rpow_neg K hs

/-- For real `s > 1`, the Dedekind zeta function `ζ_K(s)` is the sum of `N(I)^{-s}` over all
ideals `I` of `𝓞 K` (the zero ideal contributes `0`). -/
theorem dedekindZeta_ofReal_eq_tsum {s : ℝ} (hs : 1 < s) :
    dedekindZeta K s = ((∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s) : ℝ) : ℂ) := by
  have hsig : Summable fun c : (Σ n : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) ↦
      (Ideal.absNorm c.2.1 : ℝ) ^ (-s) :=
    (Equiv.sigmaFiberEquiv _).summable_iff.mpr (summable_rpow_neg_absNorm K hs)
  rw [dedekindZeta, LSeries, tsum_congr (term_dedekindZeta_ofReal (by linarith)),
    ← Complex.ofReal_tsum,
    ← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ Ideal.absNorm I)).tsum_eq]
  simp only [Equiv.sigmaFiberEquiv_apply]
  rw [hsig.tsum_sigma]
  simp_rw [tsum_absNorm_fiber]

lemma one_le_tsum_rpow_neg_absNorm {s : ℝ} (hs : 1 < s) :
    1 ≤ ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s) := by
  simpa using (summable_rpow_neg_absNorm K hs).le_tsum ⊤
    (fun I _ ↦ rpow_neg_absNorm_nonneg I s)

lemma tsum_rpow_neg_absNorm_le_of_le {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-t) ≤
      ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s) :=
  Summable.tsum_le_tsum (fun I ↦ rpow_neg_absNorm_antitone I (by linarith) hst)
    (summable_rpow_neg_absNorm K (hs.trans_le hst)) (summable_rpow_neg_absNorm K hs)

/-- The real form of `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`. -/
theorem tendsto_sub_one_mul_tsum_rpow_neg_absNorm :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s))
      (𝓝[>] 1) (𝓝 (dedekindZeta_residue K)) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  rw [Complex.ofReal_re] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp [dedekindZeta_ofReal_eq_tsum K hs]

/-- `log ((s - 1) ζ_K(s))` is bounded on `(1, 2]`. -/
theorem exists_abs_log_sub_one_mul_tsum_le : ∃ C : ℝ, ∀ s ∈ Set.Ioc (1 : ℝ) 2,
    |Real.log ((s - 1) * ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s))| ≤ C := by
  set Z : ℝ → ℝ := fun s ↦ ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s) with hZ
  set r := dedekindZeta_residue K
  have hr := dedekindZeta_residue_pos K
  have hev : ∀ᶠ s in 𝓝[>] (1 : ℝ), (s - 1) * Z s ∈ Set.Ioo (r / 2) (2 * r) :=
    tendsto_sub_one_mul_tsum_rpow_neg_absNorm K (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu : (1 : ℝ) < u := hu
  set s₁ := min ((1 + u) / 2) 2
  have hs₁ : 1 < s₁ := lt_min (by linarith) one_lt_two
  have hs₁u : s₁ < u := (min_le_left _ _).trans_lt (by linarith)
  set m := min (r / 2) (s₁ - 1)
  set M := max (2 * r) (Z s₁)
  have hm : 0 < m := lt_min (by linarith) (by linarith)
  refine ⟨max (-Real.log m) (Real.log M), fun s ⟨hs1, hs2⟩ ↦ ?_⟩
  have hb : m ≤ (s - 1) * Z s ∧ (s - 1) * Z s ≤ M := by
    rcases lt_or_ge s s₁ with h | h
    · have h' : (s - 1) * Z s ∈ Set.Ioo (r / 2) (2 * r) := hsub ⟨hs1, h.trans hs₁u⟩
      exact ⟨(min_le_left _ _).trans h'.1.le, h'.2.le.trans (le_max_left _ _)⟩
    · have hZ1 : 1 ≤ Z s := one_le_tsum_rpow_neg_absNorm K hs1
      have hZ2 : Z s ≤ Z s₁ := tsum_rpow_neg_absNorm_le_of_le K hs₁ h
      constructor
      · calc m ≤ s₁ - 1 := min_le_right _ _
          _ ≤ (s - 1) * 1 := by linarith
          _ ≤ (s - 1) * Z s := mul_le_mul_of_nonneg_left hZ1 (by linarith)
      · calc (s - 1) * Z s ≤ 1 * Z s₁ := mul_le_mul (by linarith) hZ2 (by linarith) zero_le_one
          _ = Z s₁ := one_mul _
          _ ≤ M := le_max_right _ _
  have hpos : 0 < (s - 1) * Z s := hm.trans_le hb.1
  have h1 := Real.log_le_log hm hb.1
  have h2 := Real.log_le_log hpos hb.2
  rw [abs_le]
  constructor
  · linarith [le_max_left (-Real.log m) (Real.log M)]
  · linarith [le_max_right (-Real.log m) (Real.log M)]

end dedekindZeta

/-! ### Unique factorisation and the Euler product -/

section EulerProduct

variable {K}

open Finset

/-- The ideal `∏_{𝔭 ∈ F} 𝔭 ^ e 𝔭`. -/
def prodPowHeightOneSpectrum (F : Finset (HeightOneSpectrum (𝓞 K))) (e : F → ℕ) :
    Ideal (𝓞 K) :=
  ∏ P : F, P.1.asIdeal ^ e P

lemma prodPowHeightOneSpectrum_injective (F : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (prodPowHeightOneSpectrum F) := by
  classical
  have key : ∀ (e : F → ℕ) (P : F), FractionalIdeal.count K P.1
      ((prodPowHeightOneSpectrum F e : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = e P := by
    intro e P
    have hcoe : ((prodPowHeightOneSpectrum F e : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
        ∏ Q : F, (Q.1.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ e Q :=
      (map_prod (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K) _ _).trans
        (Finset.prod_congr rfl fun Q _ ↦ map_pow (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K) _ _)
    rw [hcoe, FractionalIdeal.count_prod]
    · simp_rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal]
      rw [Finset.sum_eq_single P (fun Q _ hQ ↦ by simp [Subtype.coe_injective.ne hQ])
        (by simp)]
      simp
    · intro Q _
      exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr Q.1.ne_bot)
  intro e e' h
  funext P
  have := key e P
  rw [h, key e' P] at this
  exact_mod_cast this.symm

lemma rpow_neg_absNorm_prodPowHeightOneSpectrum (F : Finset (HeightOneSpectrum (𝓞 K)))
    (e : F → ℕ) (s : ℝ) :
    (Ideal.absNorm (prodPowHeightOneSpectrum F e) : ℝ) ^ (-s) =
      ∏ P : F, ((Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s)) ^ e P := by
  rw [prodPowHeightOneSpectrum, map_prod, Nat.cast_prod,
    ← Real.finsetProd_rpow _ _ (fun _ _ ↦ Nat.cast_nonneg _)]
  refine Finset.prod_congr rfl fun P _ ↦ ?_
  rw [map_pow, Nat.cast_pow, Real.rpow_pow_comm (Nat.cast_nonneg _)]

open scoped Classical in
lemma prod_sum_range_eq_sum_image (F : Finset (HeightOneSpectrum (𝓞 K))) (M : ℕ) (s : ℝ) :
    ∏ P : F, ∑ k ∈ range M, ((Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s)) ^ k =
      ∑ I ∈ (Fintype.piFinset fun _ : F ↦ range M).image (prodPowHeightOneSpectrum F),
        (Ideal.absNorm I : ℝ) ^ (-s) := by
  rw [Finset.prod_univ_sum, Finset.sum_image
    (fun e _ e' _ h ↦ prodPowHeightOneSpectrum_injective F h)]
  simp_rw [rpow_neg_absNorm_prodPowHeightOneSpectrum]

open scoped Classical in
/-- Unique factorisation: a nonzero ideal of norm at most `X` is a product of powers of prime
ideals of norm at most `X`, with exponents at most `X`. -/
lemma mem_image_prodPowHeightOneSpectrum {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) {X : ℕ}
    (hIX : Ideal.absNorm I ≤ X) (F : Finset (HeightOneSpectrum (𝓞 K)))
    (hF : ∀ P : HeightOneSpectrum (𝓞 K), Ideal.absNorm P.asIdeal ≤ X → P ∈ F) :
    I ∈ (Fintype.piFinset fun _ : F ↦ range (X + 1)).image (prodPowHeightOneSpectrum F) := by
  have hI0 : I ≠ 0 := hI
  have hN : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hI
  have hdvd : ∀ v : HeightOneSpectrum (𝓞 K), v.maxPowDividing I ∣ I := fun v ↦ by
    conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI0]
    exact finprod_mem_dvd v (Ideal.hasFiniteMulSupport hI0)
  set c : HeightOneSpectrum (𝓞 K) → ℕ :=
    fun v ↦ (Associates.mk v.asIdeal).count (Associates.mk I).factors with hc_def
  have hmax : ∀ v, v.maxPowDividing I = v.asIdeal ^ c v := fun v ↦ rfl
  have hle : ∀ v, Ideal.absNorm v.asIdeal ^ c v ≤ X := fun v ↦ by
    have h := map_dvd Ideal.absNorm (hdvd v)
    rw [hmax, map_pow] at h
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h).trans hIX
  have hc : ∀ v, c v < X + 1 := fun v ↦ by
    have h2 := Nat.pow_le_pow_left (two_le_absNorm_heightOneSpectrum v) (c v)
    have h3 : c v < 2 ^ c v := Nat.lt_two_pow_self
    have := hle v
    omega
  have hsupp : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) ↦ v.maxPowDividing I) ⊆
      (F : Set (HeightOneSpectrum (𝓞 K))) := fun v hv ↦ by
    have hcv : c v ≠ 0 := fun h ↦ hv (by simp [hmax, h])
    exact hF v ((Nat.le_self_pow hcv _).trans (hle v))
  refine Finset.mem_image.mpr ⟨fun P ↦ c P.1,
    Fintype.mem_piFinset.mpr fun P ↦ Finset.mem_range.mpr (hc P.1), ?_⟩
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI0]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, ← Finset.prod_coe_sort]
  rfl

lemma prod_inv_one_sub_eq_exp (F : Finset (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 ≤ s) :
    ∏ P ∈ F, (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))⁻¹ =
      Real.exp (∑ P ∈ F, -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun P _ ↦ ?_
  have := rpow_neg_absNorm_heightOneSpectrum_le_half P hs
  rw [Real.exp_neg, Real.exp_log (by linarith)]

variable (K) in
/-- Lower half of the Euler product: finite products of Euler factors are bounded by `ζ_K(s)`. -/
lemma prod_inv_one_sub_le_tsum (F : Finset (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    ∏ P ∈ F, (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))⁻¹ ≤
      ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s) := by
  classical
  have hx0 : ∀ P : HeightOneSpectrum (𝓞 K), 0 ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) :=
    fun P ↦ rpow_neg_absNorm_nonneg _ _
  have hx1 : ∀ P : HeightOneSpectrum (𝓞 K), (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) < 1 :=
    fun P ↦ (rpow_neg_absNorm_heightOneSpectrum_le_half P hs.le).trans_lt (by norm_num)
  have hlim : Tendsto
      (fun M ↦ ∏ P : F, ∑ k ∈ range M, ((Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s)) ^ k) atTop
      (𝓝 (∏ P : F, (1 - (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s))⁻¹)) :=
    tendsto_finsetProd _ fun P _ ↦
      (hasSum_geometric_of_lt_one (hx0 P.1) (hx1 P.1)).tendsto_sum_nat
  rw [← Finset.prod_coe_sort F]
  refine le_of_tendsto' hlim fun M ↦ ?_
  rw [prod_sum_range_eq_sum_image]
  exact (summable_rpow_neg_absNorm K hs).sum_le_tsum _ (fun I _ ↦ rpow_neg_absNorm_nonneg I s)

/-- Upper half of the Euler product: every finite partial sum of `ζ_K(s)` is bounded by a
finite product of Euler factors. -/
lemma exists_sum_le_prod_inv_one_sub (T : Finset (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    ∃ F : Finset (HeightOneSpectrum (𝓞 K)), ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) ≤
      ∏ P ∈ F, (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))⁻¹ := by
  classical
  set X := T.sup Ideal.absNorm
  have hfin : {P : HeightOneSpectrum (𝓞 K) | Ideal.absNorm P.asIdeal ≤ X}.Finite :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) X).preimage
      (fun P _ Q _ h ↦ HeightOneSpectrum.ext h)
  refine ⟨hfin.toFinset, ?_⟩
  set F := hfin.toFinset
  have hx0 : ∀ P : HeightOneSpectrum (𝓞 K), 0 ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) :=
    fun P ↦ rpow_neg_absNorm_nonneg _ _
  have hx1 : ∀ P : HeightOneSpectrum (𝓞 K), (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) < 1 :=
    fun P ↦ (rpow_neg_absNorm_heightOneSpectrum_le_half P hs.le).trans_lt (by norm_num)
  rw [← Finset.prod_coe_sort F]
  calc ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s)
      ≤ ∑ I ∈ (Fintype.piFinset fun _ : F ↦ range (X + 1)).image (prodPowHeightOneSpectrum F),
          (Ideal.absNorm I : ℝ) ^ (-s) := by
        rw [← Finset.sum_filter_ne_zero]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun I hI' ↦ ?_)
          (fun I _ _ ↦ rpow_neg_absNorm_nonneg I s)
        obtain ⟨hIT, hI⟩ := Finset.mem_filter.mp hI'
        refine mem_image_prodPowHeightOneSpectrum (fun h ↦ hI ?_) (Finset.le_sup hIT) F
          (fun P hP ↦ hfin.mem_toFinset.mpr hP)
        rw [h, Ideal.absNorm_bot, Nat.cast_zero, Real.zero_rpow (by linarith)]
    _ = ∏ P : F, ∑ k ∈ range (X + 1), ((Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s)) ^ k :=
        (prod_sum_range_eq_sum_image F _ s).symm
    _ ≤ ∏ P : F, (1 - (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s))⁻¹ :=
        Finset.prod_le_prod (fun P _ ↦ Finset.sum_nonneg fun k _ ↦ pow_nonneg (hx0 P.1) k)
          fun P _ ↦ sum_le_hasSum _ (fun k _ ↦ pow_nonneg (hx0 P.1) k)
            (hasSum_geometric_of_lt_one (hx0 P.1) (hx1 P.1))

lemma le_neg_log_one_sub {x : ℝ} (hx : x < 1) : x ≤ -Real.log (1 - x) := by
  have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - x)
  linarith

lemma neg_log_one_sub_le {x : ℝ} (h1 : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ x + 2 * x ^ 2 := by
  have hpos : 0 < 1 - x := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have h2 : (1 - x)⁻¹ ≤ 1 + x + 2 * x ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [sq_nonneg x]
  linarith

variable (K)

/-- For real `s > 1`, the sum `∑_𝔭 N(𝔭)^{-s}` over the nonzero prime ideals of `𝓞 K`
converges. -/
theorem summable_rpow_neg_absNorm_heightOneSpectrum {s : ℝ} (hs : 1 < s) :
    Summable fun P : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) :=
  (summable_rpow_neg_absNorm K hs).comp_injective fun _ _ h ↦ HeightOneSpectrum.ext h

lemma summable_neg_log_one_sub_rpow_neg_absNorm {s : ℝ} (hs : 1 < s) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) := by
  refine Summable.of_nonneg_of_le (fun P ↦ ?_) (fun P ↦ ?_)
    ((summable_rpow_neg_absNorm_heightOneSpectrum K hs).mul_left 2)
  · have := rpow_neg_absNorm_nonneg P.asIdeal s
    exact this.trans (le_neg_log_one_sub (by
      linarith [rpow_neg_absNorm_heightOneSpectrum_le_half P hs.le]))
  · have h0 := rpow_neg_absNorm_nonneg P.asIdeal s
    have h1 := rpow_neg_absNorm_heightOneSpectrum_le_half P hs.le
    have := neg_log_one_sub_le h1
    nlinarith

/-- **Euler product** for the Dedekind zeta function, logarithmic form: for real `s > 1`,
`∑_𝔭 -log (1 - N(𝔭)^{-s}) = log (∑_I N(I)^{-s})`. -/
theorem hasSum_neg_log_one_sub_rpow_neg_absNorm {s : ℝ} (hs : 1 < s) :
    HasSum (fun P : HeightOneSpectrum (𝓞 K) ↦
        -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)))
      (Real.log (∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s))) := by
  have hsum := summable_neg_log_one_sub_rpow_neg_absNorm K hs
  have hZ := one_le_tsum_rpow_neg_absNorm K hs
  have hnn : ∀ P : HeightOneSpectrum (𝓞 K),
      0 ≤ -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) := fun P ↦
    (rpow_neg_absNorm_nonneg P.asIdeal s).trans (le_neg_log_one_sub (by
      linarith [rpow_neg_absNorm_heightOneSpectrum_le_half P hs.le]))
  convert hsum.hasSum using 1
  apply le_antisymm
  · rw [Real.log_le_iff_le_exp (by linarith)]
    refine Summable.tsum_le_of_sum_le (summable_rpow_neg_absNorm K hs) fun T ↦ ?_
    obtain ⟨F, hF⟩ := exists_sum_le_prod_inv_one_sub T hs
    refine hF.trans ?_
    rw [prod_inv_one_sub_eq_exp F hs.le]
    exact Real.exp_le_exp.mpr (hsum.sum_le_tsum F fun P _ ↦ hnn P)
  · refine hsum.tsum_le_of_sum_le fun F ↦ ?_
    rw [Real.le_log_iff_exp_le (by linarith), ← prod_inv_one_sub_eq_exp F hs.le]
    exact prod_inv_one_sub_le_tsum K F hs

/-- **Euler product** for the Dedekind zeta function: for real `s > 1`,
`∏_𝔭 (1 - N(𝔭)^{-s})⁻¹ = ζ_K(s)`. -/
theorem hasProd_dedekindZeta {s : ℝ} (hs : 1 < s) :
    HasProd (fun P : HeightOneSpectrum (𝓞 K) ↦ (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))⁻¹)
      (dedekindZeta K s).re := by
  have h := (hasSum_neg_log_one_sub_rpow_neg_absNorm K hs).rexp
  rw [Real.exp_log (by linarith [one_le_tsum_rpow_neg_absNorm K hs])] at h
  rw [dedekindZeta_ofReal_eq_tsum K hs, Complex.ofReal_re]
  convert h using 1
  funext P
  have := rpow_neg_absNorm_heightOneSpectrum_le_half P hs.le
  simp only [Function.comp_apply, Real.exp_neg, Real.exp_log (by linarith : (0 : ℝ) < 1 - _)]

/-- **Euler product** for the Dedekind zeta function, logarithmic form with `dedekindZeta`. -/
theorem log_dedekindZeta_re_eq_tsum {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K s).re = ∑' P : HeightOneSpectrum (𝓞 K),
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) := by
  rw [dedekindZeta_ofReal_eq_tsum K hs, Complex.ofReal_re,
    (hasSum_neg_log_one_sub_rpow_neg_absNorm K hs).tsum_eq]

/-- **KD1**: `∑_𝔭 N(𝔭)^{-s} = log (1 / (s - 1)) + O(1)` for `s ∈ (1, 2]`. -/
theorem exists_abs_tsum_rpow_neg_absNorm_sub_log_le : ∃ C : ℝ, ∀ s ∈ Set.Ioc (1 : ℝ) 2,
    |∑' P : HeightOneSpectrum (𝓞 K), (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) -
      Real.log (1 / (s - 1))| ≤ C := by
  obtain ⟨C₀, hC₀⟩ := exists_abs_log_sub_one_mul_tsum_le K
  have hB := summable_rpow_neg_absNorm_heightOneSpectrum K one_lt_two
  set B := ∑' P : HeightOneSpectrum (𝓞 K), (Ideal.absNorm P.asIdeal : ℝ) ^ (-2 : ℝ)
  refine ⟨2 * B + C₀, fun s hs ↦ ?_⟩
  obtain ⟨hs1, hs2⟩ := hs
  set Z := ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s)
  have hZ : 0 < Z := by linarith [one_le_tsum_rpow_neg_absNorm K hs1]
  have hx := summable_rpow_neg_absNorm_heightOneSpectrum K hs1
  have hdiff := (hasSum_neg_log_one_sub_rpow_neg_absNorm K hs1).sub hx.hasSum
  have h0 : 0 ≤ Real.log Z -
      ∑' P : HeightOneSpectrum (𝓞 K), (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) :=
    hdiff.nonneg fun P ↦ sub_nonneg.mpr (le_neg_log_one_sub (by
      linarith [rpow_neg_absNorm_heightOneSpectrum_le_half P hs1.le]))
  have h1 : Real.log Z -
      ∑' P : HeightOneSpectrum (𝓞 K), (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) ≤ 2 * B := by
    refine hasSum_le (fun P ↦ ?_) hdiff (hB.hasSum.mul_left 2)
    have hx0 := rpow_neg_absNorm_nonneg P.asIdeal s
    have hx1 := rpow_neg_absNorm_heightOneSpectrum_le_half P hs1.le
    have h := neg_log_one_sub_le hx1
    have h1 : (1 : ℝ) ≤ Ideal.absNorm P.asIdeal := by
      exact_mod_cast one_le_absNorm_heightOneSpectrum P
    have hsq : ((Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) ^ 2 ≤
        (Ideal.absNorm P.asIdeal : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      exact Real.rpow_le_rpow_of_exponent_le h1 (by push_cast; linarith)
    linarith
  have h2 := hC₀ s ⟨hs1, hs2⟩
  have h3 : Real.log (1 / (s - 1)) = Real.log Z - Real.log ((s - 1) * Z) := by
    rw [Real.log_mul (by linarith) hZ.ne', one_div, Real.log_inv]
    ring
  rw [h3]
  rw [abs_le] at h2 ⊢
  constructor <;> linarith [h2.1, h2.2]

end EulerProduct

end NumberField
