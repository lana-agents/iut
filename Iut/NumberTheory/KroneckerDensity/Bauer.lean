/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib
import Iut.NumberTheory.KroneckerDensity.Basic
import Iut.NumberTheory.KroneckerDensity.Splitting

/-!
# Bauer's theorem and infinitely many completely split primes

Using only Kronecker's density theorem (the sum of `N(𝔭)^{-s}` over the primes of degree one of
a number field is `log (1 / (s - 1)) + O(1)` as `s → 1⁺`), we prove:

* `NumberField.le_of_splitsCompletely` (**Bauer's theorem**): let `L, M` be number fields in a
  common field `Ω`, with `L / ℚ` Galois. If all but finitely many rational primes `p` which have a
  prime of degree one in `M` split completely in `L`, then `L ⊆ M`.
* `NumberField.infinite_setOf_splitsCompletely`: infinitely many rational primes split
  completely in a given number field `K`.
* `NumberField.exists_ncard_primesOver_eq_finrank`: in particular there is a rational prime `p`
  with exactly `[K : ℚ]` primes of `𝓞 K` above it.

## Proof of Bauer's theorem

Let `E = L ⊔ M` and `d = [E : M]`. If a prime `𝔭` of `M` of degree one lies over `p` and `p` splits
completely in `L`, then `Gal(E/M)` acts freely on the primes of `E` above `𝔭` (it embeds into
`Gal(L/ℚ)`, whose decomposition groups at `p` are trivial), so there are exactly `d` of them, all
of degree one with norm `N 𝔭`. Hence
`d · ∑_{𝔭 ∈ P₁(M)} N(𝔭)^{-s} ≤ ∑_{𝔓 ∈ P₁(E)} N(𝔓)^{-s} + O(1)`, and Kronecker's theorem for `M`
and `E` forces `d = 1`.

The infinitude of completely split primes follows from Kronecker's theorem for the Galois
closure `N` of `K`: `N` has infinitely many primes of degree one, almost all unramified, and an
unramified prime of degree one in a Galois field lies over a completely split prime.

## References

* [J. S. Milne, *Class Field Theory* (course notes), Ch. VI, Thm. 3.4 (density of completely
  split primes, via the pole of `ζ_K` only) and Cor. 3.6 (Bauer 1916, `L`, `M` both Galois)]
* [L. Merel, *Applications et versions effectives du théorème de Chebotarev* (lecture notes,
  leçon XII), Prop. 4: the statement proved here, with `M` arbitrary; proved there via
  Chebotarev. The proof given here uses only Kronecker's density theorem.]
-/

open Ideal IsDedekindDomain Module

namespace NumberField

/-! ### Auxiliary lemmas -/

section Aux

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F]

/-- The absolute norm is invariant under ring isomorphisms of rings of integers. -/
lemma absNorm_map_ringEquiv (e : 𝓞 K ≃+* 𝓞 F) (I : Ideal (𝓞 K)) :
    absNorm (I.map e) = absNorm I := by
  rw [absNorm_apply, absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv.symm

/-- Isomorphic rings of integers have primes of the same absolute norms. -/
lemma exists_heightOneSpectrum_absNorm_eq (e : 𝓞 K ≃+* 𝓞 F) (P : HeightOneSpectrum (𝓞 K)) :
    ∃ Q : HeightOneSpectrum (𝓞 F), absNorm Q.asIdeal = absNorm P.asIdeal := by
  have := P.isPrime
  refine ⟨⟨P.asIdeal.map e, map_isPrime_of_equiv e, ?_⟩, absNorm_map_ringEquiv e _⟩
  rw [ne_eq, map_eq_bot_iff_of_injective e.injective]
  exact P.ne_bot

lemma rpow_neg_absNorm_le_one (I : Ideal (𝓞 K)) (hI : absNorm I ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    (absNorm I : ℝ) ^ (-s) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hI)
    (neg_nonpos.mpr hs)

/-- Every value `R ≥ 0` is attained by `log (1 / (s - 1))` for some `s ∈ (1, 2]`. -/
lemma exists_mem_Ioc_log_eq {R : ℝ} (hR : 0 ≤ R) :
    ∃ s ∈ Set.Ioc (1 : ℝ) 2, Real.log (1 / (s - 1)) = R := by
  refine ⟨1 + Real.exp (-R), ⟨by linarith [Real.exp_pos (-R)], ?_⟩, ?_⟩
  · linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hR)]
  · rw [add_sub_cancel_left, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]

end Aux

/-! ### Bauer's theorem -/

section Bauer

variable {E : Type*} [Field E] [NumberField E]

lemma finite_setOf_under_eq (M : IntermediateField ℚ E) (𝔭 : HeightOneSpectrum (𝓞 M)) :
    {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.under (𝓞 M) = 𝔭.asIdeal}.Finite := by
  refine (Set.Finite.preimage (fun P _ Q _ h ↦ HeightOneSpectrum.ext h)
    (Algebra.QuasiFinite.finite_primesOver 𝔭.asIdeal :
      (𝔭.asIdeal.primesOver (𝓞 E)).Finite)).subset fun P hP ↦ ?_
  exact ⟨P.isPrime, ⟨hP.symm⟩⟩

lemma ncard_setOf_under_eq (M : IntermediateField ℚ E) (𝔭 : HeightOneSpectrum (𝓞 M)) :
    {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.under (𝓞 M) = 𝔭.asIdeal}.ncard =
      (𝔭.asIdeal.primesOver (𝓞 E)).ncard := by
  rw [← Set.ncard_image_of_injective _ (fun P Q h ↦ HeightOneSpectrum.ext h)]
  congr 1
  ext Q
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P.isPrime, ⟨hP.symm⟩⟩
  · rintro ⟨hQ, hQ'⟩
    exact ⟨⟨Q, hQ, ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q⟩, hQ'.over.symm, rfl⟩

variable (L M : IntermediateField ℚ E) [IsGalois ℚ L]

/-- A prime of `E = L ⊔ M` above a prime `𝔭` of `M` of prime norm `p`, where `p` splits
completely in `L`, has the same norm `p`. -/
lemma absNorm_eq_of_under_eq (hLM : L ⊔ M = ⊤) {𝔭 : HeightOneSpectrum (𝓞 M)}
    (hp : (absNorm 𝔭.asIdeal).Prime) (hL : SplitsCompletely L (absNorm 𝔭.asIdeal))
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 M) = 𝔭.asIdeal) :
    absNorm P.asIdeal = absNorm 𝔭.asIdeal := by
  have := 𝔭.isPrime
  have h𝔭 := mem_primesOver_of_absNorm_eq hp (P := 𝔭.asIdeal) rfl
  have := h𝔭.2
  have : P.asIdeal.LiesOver 𝔭.asIdeal := ⟨hP.symm⟩
  have : P.asIdeal.LiesOver (span {((absNorm 𝔭.asIdeal : ℕ) : ℤ)}) := .trans _ 𝔭.asIdeal _
  have hf := (ncard_primesOver_eq_finrank_of_splitsCompletely L M hLM hL 𝔭.asIdeal).2
    P.asIdeal ⟨P.isPrime, inferInstance⟩
  rw [absNorm_eq_iff_inertiaDeg_eq_one hp ⟨P.isPrime, inferInstance⟩,
    inertiaDeg_tower (q := 𝔭.asIdeal), hf, mul_one]
  exact (absNorm_eq_iff_inertiaDeg_eq_one hp h𝔭).mp rfl

/-- The number of primes of `E = L ⊔ M` above a prime `𝔭` of `M` of prime norm `p`, where `p`
splits completely in `L`, is `[E : M]`. -/
lemma ncard_setOf_under_eq_finrank (hLM : L ⊔ M = ⊤) {𝔭 : HeightOneSpectrum (𝓞 M)}
    (hp : (absNorm 𝔭.asIdeal).Prime) (hL : SplitsCompletely L (absNorm 𝔭.asIdeal)) :
    {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.under (𝓞 M) = 𝔭.asIdeal}.ncard = finrank M E := by
  have := 𝔭.isPrime
  have := (mem_primesOver_of_absNorm_eq hp (P := 𝔭.asIdeal) rfl).2
  rw [ncard_setOf_under_eq]
  exact (ncard_primesOver_eq_finrank_of_splitsCompletely L M hLM hL 𝔭.asIdeal).1

/-- **Bauer's theorem**, core form inside the compositum: if `E = L ⊔ M` with `L / ℚ` Galois
and every prime of `M` of prime norm `p ∉ S` has `p` splitting completely in `L`, then
`[E : M] = 1`. -/
theorem finrank_eq_one_of_splitsCompletely (hLM : L ⊔ M = ⊤) (S : Finset ℕ)
    (h : ∀ 𝔭 : HeightOneSpectrum (𝓞 M), (absNorm 𝔭.asIdeal).Prime →
      absNorm 𝔭.asIdeal ∉ S → SplitsCompletely L (absNorm 𝔭.asIdeal)) :
    finrank M E = 1 := by
  classical
  set d := finrank M E
  obtain ⟨CM, hCM⟩ := exists_abs_tsum_degOnePrimes_sub_log_le M
  obtain ⟨CE, hCE⟩ := exists_abs_tsum_degOnePrimes_sub_log_le E
  set G : Set (HeightOneSpectrum (𝓞 M)) :=
    {𝔭 | (absNorm 𝔭.asIdeal).Prime ∧ absNorm 𝔭.asIdeal ∉ S}
  set Bad : Set (HeightOneSpectrum (𝓞 M)) := {𝔭 | absNorm 𝔭.asIdeal ∈ S}
  have hBad : Bad.Finite :=
    ((Ideal.finite_setOf_absNorm_le (S := 𝓞 M) (S.sup id)).preimage
      (fun P _ Q _ h ↦ HeightOneSpectrum.ext h)).subset fun 𝔭 h𝔭 ↦ Finset.le_sup (f := id) h𝔭
  set B : ℝ := ∑' 𝔭, Bad.indicator (fun _ ↦ (1 : ℝ)) 𝔭
  have key : ∀ s ∈ Set.Ioc (1 : ℝ) 2,
      (d : ℝ) * (Real.log (1 / (s - 1)) - CM - B) ≤ Real.log (1 / (s - 1)) + CE := by
    intro s hs
    set fM := fun 𝔭 : HeightOneSpectrum (𝓞 M) ↦ (absNorm 𝔭.asIdeal : ℝ) ^ (-s)
    set fE := fun P : HeightOneSpectrum (𝓞 E) ↦ (absNorm P.asIdeal : ℝ) ^ (-s)
    have hfM0 : ∀ 𝔭, 0 ≤ fM 𝔭 := fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hfE0 : ∀ P, 0 ≤ fE P := fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hsM := summable_rpow_neg_absNorm_heightOneSpectrum M hs.1
    have hsE := summable_rpow_neg_absNorm_heightOneSpectrum E hs.1
    have hsB : Summable (Bad.indicator fun _ ↦ (1 : ℝ)) :=
      summable_of_ne_finset_zero (s := hBad.toFinset) fun b hb ↦
        Set.indicator_of_notMem (by simpa using hb) _
    have h1 : Real.log (1 / (s - 1)) - CM ≤ ∑' 𝔭, (degOnePrimes M).indicator fM 𝔭 := by
      rw [← tsum_subtype]
      linarith [(abs_le.mp (hCM s hs)).1]
    have h2 : ∑' P, (degOnePrimes E).indicator fE P ≤ Real.log (1 / (s - 1)) + CE := by
      rw [← tsum_subtype]
      linarith [(abs_le.mp (hCE s hs)).2]
    have h3 : ∑' 𝔭, (degOnePrimes M).indicator fM 𝔭 ≤ ∑' 𝔭, G.indicator fM 𝔭 + B := by
      rw [← (hsM.indicator G).tsum_add hsB]
      refine (hsM.indicator _).tsum_le_tsum (fun 𝔭 ↦ ?_) ((hsM.indicator G).add hsB)
      by_cases h1 : 𝔭 ∈ degOnePrimes M
      · rw [Set.indicator_of_mem h1]
        by_cases h2 : absNorm 𝔭.asIdeal ∈ S
        · rw [Set.indicator_of_mem (show 𝔭 ∈ Bad from h2)]
          have := rpow_neg_absNorm_le_one 𝔭.asIdeal h1.ne_zero (by linarith [hs.1] : 0 ≤ s)
          linarith [Set.indicator_nonneg (fun 𝔭 _ ↦ hfM0 𝔭) 𝔭 (s := G)]
        · rw [Set.indicator_of_mem (show 𝔭 ∈ G from ⟨h1, h2⟩)]
          linarith [Set.indicator_nonneg (fun _ _ ↦ zero_le_one' ℝ) 𝔭 (s := Bad)]
      · rw [Set.indicator_of_notMem h1]
        exact add_nonneg (Set.indicator_nonneg (fun 𝔭 _ ↦ hfM0 𝔭) 𝔭)
          (Set.indicator_nonneg (fun _ _ ↦ zero_le_one' ℝ) 𝔭)
    have h4 : (d : ℝ) * ∑' 𝔭, G.indicator fM 𝔭 ≤ ∑' P, (degOnePrimes E).indicator fE P := by
      rw [← tsum_mul_left]
      refine Real.tsum_le_of_sum_le (fun 𝔭 ↦ mul_nonneg (Nat.cast_nonneg _)
        (Set.indicator_nonneg (fun 𝔭 _ ↦ hfM0 𝔭) 𝔭)) fun T ↦ ?_
      let fib : HeightOneSpectrum (𝓞 M) → Finset (HeightOneSpectrum (𝓞 E)) :=
        fun 𝔭 ↦ (finite_setOf_under_eq M 𝔭).toFinset
      calc ∑ 𝔭 ∈ T, (d : ℝ) * G.indicator fM 𝔭
          ≤ ∑ 𝔭 ∈ T, ∑ P ∈ fib 𝔭, (degOnePrimes E).indicator fE P := by
            refine Finset.sum_le_sum fun 𝔭 _ ↦ ?_
            by_cases h𝔭 : 𝔭 ∈ G
            · rw [Set.indicator_of_mem h𝔭]
              have hfib : ∀ P ∈ fib 𝔭, (degOnePrimes E).indicator fE P = fM 𝔭 := by
                intro P hP
                have hN := absNorm_eq_of_under_eq L M hLM h𝔭.1 (h 𝔭 h𝔭.1 h𝔭.2)
                  ((finite_setOf_under_eq M 𝔭).mem_toFinset.mp hP)
                have hP1 : P ∈ degOnePrimes E := by
                  change (absNorm P.asIdeal).Prime
                  rw [hN]
                  exact h𝔭.1
                rw [Set.indicator_of_mem hP1]
                simp only [fE, fM, hN]
              rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul,
                ← Set.ncard_eq_toFinset_card _ (finite_setOf_under_eq M 𝔭),
                ncard_setOf_under_eq_finrank L M hLM h𝔭.1 (h 𝔭 h𝔭.1 h𝔭.2)]
            · rw [Set.indicator_of_notMem h𝔭, mul_zero]
              exact Finset.sum_nonneg fun P _ ↦ Set.indicator_nonneg (fun P _ ↦ hfE0 P) P
        _ = ∑ P ∈ T.biUnion fib, (degOnePrimes E).indicator fE P := by
            refine (Finset.sum_biUnion fun 𝔭 _ 𝔭' _ hne ↦ ?_).symm
            refine Finset.disjoint_left.mpr fun P hP hP' ↦ hne (HeightOneSpectrum.ext ?_)
            exact ((finite_setOf_under_eq M 𝔭).mem_toFinset.mp hP).symm.trans
              ((finite_setOf_under_eq M 𝔭').mem_toFinset.mp hP')
        _ ≤ ∑' P, (degOnePrimes E).indicator fE P :=
            (hsE.indicator _).sum_le_tsum _ fun P _ ↦ Set.indicator_nonneg (fun P _ ↦ hfE0 P) P
    calc (d : ℝ) * (Real.log (1 / (s - 1)) - CM - B)
        ≤ d * ∑' 𝔭, G.indicator fM 𝔭 :=
          mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      _ ≤ _ := h4.trans h2
  by_contra hd
  have hd2 : (2 : ℝ) ≤ d := by
    have : 0 < d := finrank_pos
    exact_mod_cast (by omega : 2 ≤ d)
  set X := (d : ℝ) * (CM + B) + CE
  obtain ⟨s, hs, hlog⟩ := exists_mem_Ioc_log_eq (by positivity : 0 ≤ |X| + 1)
  have := key s hs
  rw [hlog] at this
  nlinarith [le_abs_self X, abs_nonneg X]

/-- **Bauer's theorem.** Let `L` and `M` be number fields inside a field `Ω`, with `L / ℚ`
Galois. If, for all rational primes `p` outside a finite set, `p` splits completely in `L`
whenever `M` has a prime of norm `p` (i.e. a prime of degree one over `p`), then `L ⊆ M`. -/
theorem le_of_splitsCompletely {Ω : Type*} [Field Ω] [CharZero Ω] (L M : IntermediateField ℚ Ω)
    [NumberField L] [NumberField M] [IsGalois ℚ L]
    (h : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      (∃ P : IsDedekindDomain.HeightOneSpectrum (𝓞 M), Ideal.absNorm P.asIdeal = p) →
        NumberField.SplitsCompletely L p) : L ≤ M := by
  obtain ⟨S, hS⟩ := h
  have hLE : L ≤ L ⊔ M := le_sup_left
  have hME : M ≤ L ⊔ M := le_sup_right
  have : FiniteDimensional ℚ L :=
    (finiteDimensional_rat_iff _ _).mp (@NumberField.to_finiteDimensional L _ _)
  have : FiniteDimensional ℚ M :=
    (finiteDimensional_rat_iff _ _).mp (@NumberField.to_finiteDimensional M _ _)
  have : NumberField ↥(L ⊔ M) :=
    { to_finiteDimensional := (finiteDimensional_rat_iff _ _).mp
        (IntermediateField.finiteDimensional_sup L M) }
  set L' := IntermediateField.restrict hLE
  set M' := IntermediateField.restrict hME
  have hLM : L' ⊔ M' = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top, IntermediateField.lift_sup,
      IntermediateField.lift_restrict, IntermediateField.lift_restrict]
  let eL := IntermediateField.restrict_algEquiv hLE
  let eM := IntermediateField.restrict_algEquiv hME
  have : @IsGalois ℚ _ L _ (IntermediateField.algebra' L) :=
    (isGalois_rat_iff _ _).mp ‹IsGalois ℚ L›
  have : IsGalois ℚ L' := (isGalois_rat_iff _ _).mp (IsGalois.of_algEquiv eL)
  have hM' : M' = ⊤ := by
    rw [← IntermediateField.finrank_eq_one_iff_eq_top]
    refine finrank_eq_one_of_splitsCompletely L' M' hLM S fun 𝔭 hp hpS ↦ ?_
    letI : Algebra L' L := eL.symm.toRingEquiv.toRingHom.toAlgebra
    refine SplitsCompletely.of_algebra (F := L) (hS _ hp hpS ?_)
    exact exists_heightOneSpectrum_absNorm_eq (RingOfIntegers.mapRingEquiv eM.symm.toRingEquiv) 𝔭
  intro x hx
  have hx' : (⟨x, hLE hx⟩ : ↥(L ⊔ M)) ∈ M' := hM' ▸ IntermediateField.mem_top
  exact (IntermediateField.mem_restrict hME _).mp hx'

end Bauer

/-! ### Infinitely many completely split primes -/

section Infinite

variable (K : Type*) [Field K] [NumberField K]

/-- A number field has infinitely many primes of degree one. -/
theorem infinite_degOnePrimes : (degOnePrimes K).Infinite := by
  intro hfin
  have := hfin.fintype
  obtain ⟨C, hC⟩ := exists_abs_tsum_degOnePrimes_sub_log_le K
  obtain ⟨s, hs, hlog⟩ :=
    exists_mem_Ioc_log_eq (by positivity : 0 ≤ |C| + Fintype.card (degOnePrimes K) + 1)
  have h1 := (abs_le.mp (hC s hs)).1
  rw [hlog, tsum_fintype] at h1
  have h2 : ∑ P : degOnePrimes K, (absNorm P.1.asIdeal : ℝ) ^ (-s) ≤
      Fintype.card (degOnePrimes K) := by
    rw [Fintype.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact Finset.sum_le_sum fun P _ ↦
      rpow_neg_absNorm_le_one _ P.2.ne_zero (by linarith [hs.1])
  linarith [le_abs_self C]

/-- There are infinitely many rational primes having a prime of degree one in `K`. -/
theorem infinite_setOf_exists_absNorm_eq :
    {p : ℕ | p.Prime ∧ ∃ P ∈ degOnePrimes K, absNorm P.asIdeal = p}.Infinite := by
  intro hfin
  refine infinite_degOnePrimes K (Set.Finite.subset (hfin.biUnion fun p _ ↦
    (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) p).preimage
      (fun P _ Q _ h ↦ HeightOneSpectrum.ext h)) fun P hP ↦ ?_)
  exact Set.mem_biUnion (x := absNorm P.asIdeal) ⟨hP, P, hP, rfl⟩ rfl

/-- **Infinitely many rational primes split completely in a number field.** -/
theorem infinite_setOf_splitsCompletely :
    {p : ℕ | p.Prime ∧ NumberField.SplitsCompletely K p}.Infinite := by
  have : IsAlgClosure ℚ (AlgebraicClosure K) :=
    ⟨AlgebraicClosure.isAlgClosed K, Algebra.IsAlgebraic.trans ℚ K (AlgebraicClosure K)⟩
  let N := IntermediateField.normalClosure ℚ K (AlgebraicClosure K)
  have : IsGalois ℚ N :=
    (isGalois_rat_iff _ _).mp (IsGalois.normalClosure ℚ K (AlgebraicClosure K))
  have : FiniteDimensional ℚ N := (finiteDimensional_rat_iff _ _).mp
    (normalClosure.is_finiteDimensional ℚ K (AlgebraicClosure K))
  have : NumberField N := {}
  refine ((infinite_setOf_exists_absNorm_eq N).sdiff (finite_setOf_dvd_discr N)).mono ?_
  rintro p ⟨⟨hp, P, -, hPp⟩, hd⟩
  have := P.isPrime
  have hmem := mem_primesOver_of_absNorm_eq hp hPp
  exact ⟨hp, (splitsCompletely_of_isGalois hp P.asIdeal hmem
    (ramificationIdx_eq_one_of_not_dvd_discr hp hd hmem)
    ((absNorm_eq_iff_inertiaDeg_eq_one hp hmem).mp hPp)).of_algebra⟩

/-- Every number field `K` has a rational prime `p` with exactly `[K : ℚ]` primes above it
(the form used in [FrdI, Thm. 6.4 (iv)]). -/
theorem exists_ncard_primesOver_eq_finrank :
    ∃ p : ℕ, p.Prime ∧ ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard = finrank ℚ K :=
  let ⟨p, hp, h⟩ := (infinite_setOf_splitsCompletely K).nonempty
  ⟨p, hp, h.ncard_primesOver⟩

end Infinite

end NumberField
