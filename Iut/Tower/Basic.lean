/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.Arithmetic
import Iut.Tripod.TwoAdic

/-!
# Orders of ideals at finite places, and the fundamental identity in a relative extension

General facts about number fields used by the tower arithmetic of IUT IV, §1:

* `Iut.ordAt I v`: the exponent of the prime of the finite place `v` in the factorization of
  a nonzero ideal `I` of `𝓞_K` (`Iut.ordDifferent` is the case of the different);
* `Iut.absNorm_eq_prod_ordAt`, `Iut.log_absNorm_eq_sum_ordAt`: the factorization of the
  absolute norm `N(I) = ∏_v N(𝔭_v)^{ord_v(I)}`, and its logarithm
  `log N(I) = ∑_v ord_v(I)·f_v·log p_v`, over any finite set of places containing the
  support;
* `Iut.le_ordAt_of_pow_dvd`: `𝔭_v^n ∣ I → n ≤ ord_v(I)`;
* for an extension `K/k` of number fields: the places of `K` over a place `u` of `k` are
  finitely many (`Iut.liesOver_finite`), the fundamental identity
  `∑_{v ∣ u} e(v/u) f(v/u) = [K : k]` (`Iut.sum_relLocalDeg_liesOver`), and the bounds
  `e(v/u) ≤ [K : k]` (`Iut.relRamIdx_le_finrank`), `e_v ≤ [K : ℚ]` (`Iut.ramIdx_le_finrank`).
-/

namespace Iut

open NumberField IsDedekindDomain UniqueFactorizationMonoid

section Ord

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- The exponent `ord_v(I)` of the prime of the finite place `v` in a nonzero ideal `I`
of `𝓞_K` (`0` for `I = 0`). -/
noncomputable def ordAt (I : Ideal (𝓞 K)) (v : FinitePlace K) : ℕ :=
  Multiset.count v.maximalIdeal.asIdeal (normalizedFactors I)

lemma ordDifferent_eq_ordAt (v : FinitePlace K) :
    ordDifferent K v = ordAt (differentIdeal ℤ (𝓞 K)) v := rfl

/-- The prime of a finite place is a normalized factor of `I` iff `ord_v(I) ≠ 0`. -/
lemma ordAt_ne_zero_iff (I : Ideal (𝓞 K)) (v : FinitePlace K) :
    ordAt I v ≠ 0 ↔ v.maximalIdeal.asIdeal ∈ normalizedFactors I := by
  classical
  unfold ordAt
  rw [Ne, Multiset.count_eq_zero, not_not]

/-- Only finitely many places have `ord_v(I) ≠ 0`. -/
lemma ordAt_support_finite (I : Ideal (𝓞 K)) : {v : FinitePlace K | ordAt I v ≠ 0}.Finite := by
  classical
  have hfin : ((normalizedFactors I).toFinset : Set (Ideal (𝓞 K))).Finite :=
    Finset.finite_toSet _
  refine (hfin.preimage (f := fun v : FinitePlace K => v.maximalIdeal.asIdeal) ?_).subset ?_
  · intro w₁ _ w₂ _ h
    exact FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h)
  · intro v hv
    rw [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
    exact (ordAt_ne_zero_iff I v).mp hv

/-- The normalized factors of a nonzero ideal are the primes of the places with
`ord_v(I) ≠ 0`, for any finite set `s` of places containing them. -/
lemma normalizedFactors_toFinset_eq_image (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (s : Finset (FinitePlace K)) (hs : ∀ v, ordAt I v ≠ 0 → v ∈ s) :
    (normalizedFactors I).toFinset =
      (s.filter (fun v => ordAt I v ≠ 0)).image (fun v => v.maximalIdeal.asIdeal) := by
  classical
  ext P
  simp only [Multiset.mem_toFinset, Finset.mem_image, Finset.mem_filter]
  constructor
  · intro hP
    have hprime : P.IsPrime := ((Ideal.mem_normalizedFactors_iff hI).mp hP).1
    have hne : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP
    refine ⟨FinitePlace.mk ⟨P, hprime, hne⟩, ⟨hs _ ?_, ?_⟩, ?_⟩
    · rw [ordAt_ne_zero_iff, FinitePlace.maximalIdeal_mk]
      exact hP
    · rw [ordAt_ne_zero_iff, FinitePlace.maximalIdeal_mk]
      exact hP
    · rw [FinitePlace.maximalIdeal_mk]
  · rintro ⟨v, ⟨-, hv⟩, rfl⟩
    exact (ordAt_ne_zero_iff I v).mp hv

/-- **The factorization of the absolute norm**: `N(I) = ∏_v N(𝔭_v)^{ord_v(I)}` over any
finite set of places containing the support of `ord(I)`. -/
theorem absNorm_eq_prod_ordAt (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (s : Finset (FinitePlace K)) (hs : ∀ v, ordAt I v ≠ 0 → v ∈ s) :
    Ideal.absNorm I = ∏ v ∈ s, Ideal.absNorm v.maximalIdeal.asIdeal ^ ordAt I v := by
  classical
  have hprod : (normalizedFactors I).prod = I :=
    associated_iff_eq.mp (prod_normalizedFactors hI)
  calc Ideal.absNorm I = Ideal.absNorm (normalizedFactors I).prod := by rw [hprod]
    _ = ((normalizedFactors I).map Ideal.absNorm).prod := map_multiset_prod _ _
    _ = ∏ P ∈ (normalizedFactors I).toFinset,
          Ideal.absNorm P ^ (normalizedFactors I).count P :=
        Finset.prod_multiset_map_count _ _
    _ = ∏ v ∈ s.filter (fun v => ordAt I v ≠ 0),
          Ideal.absNorm v.maximalIdeal.asIdeal ^ ordAt I v := by
        rw [normalizedFactors_toFinset_eq_image I hI s hs, Finset.prod_image]
        · rfl
        · intro v₁ _ v₂ _ h
          exact FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h)
    _ = ∏ v ∈ s, Ideal.absNorm v.maximalIdeal.asIdeal ^ ordAt I v := by
        refine Finset.prod_filter_of_ne fun v _ hv => ?_
        contrapose! hv
        rw [hv, pow_zero]

/-- The absolute norm of a nonzero ideal is nonzero. -/
lemma absNorm_ne_zero_of_ne_zero (I : Ideal (𝓞 K)) (hI : I ≠ 0) : Ideal.absNorm I ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact hI

/-- **The logarithm of the absolute norm**: `log N(I) = ∑_v ord_v(I)·(f_v·log p_v)` over any
finite set of places containing the support of `ord(I)`. -/
theorem log_absNorm_eq_sum_ordAt (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (s : Finset (FinitePlace K)) (hs : ∀ v, ordAt I v ≠ 0 → v ∈ s) :
    Real.log (Ideal.absNorm I) =
      ∑ v ∈ s, (ordAt I v : ℝ) * (inertDeg K v * Real.log (residueChar v)) := by
  rw [absNorm_eq_prod_ordAt I hI s hs, Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [Nat.cast_pow, Real.log_pow, absNorm_eq_pow_residueChar, Nat.cast_pow, Real.log_pow]
  · intro v _
    have h := absNorm_ne_zero_of_ne_zero v.maximalIdeal.asIdeal v.maximalIdeal.ne_bot
    positivity

/-- `𝔭_v^n ∣ I → n ≤ ord_v(I)`, for `I ≠ 0`. -/
lemma le_ordAt_of_pow_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0) (v : FinitePlace K) (n : ℕ)
    (h : v.maximalIdeal.asIdeal ^ n ∣ I) : n ≤ ordAt I v := by
  classical
  have hirr : Irreducible v.maximalIdeal.asIdeal :=
    (Ideal.prime_of_isPrime v.maximalIdeal.ne_bot v.maximalIdeal.isPrime).irreducible
  have h1 := (pow_dvd_iff_le_emultiplicity).mp h
  rw [emultiplicity_eq_count_normalizedFactors hirr hI, normalize_eq] at h1
  exact_mod_cast h1

/-- `𝔭_v ∣ I ↔ ord_v(I) ≠ 0`, for `I ≠ 0`. -/
lemma ordAt_ne_zero_iff_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0) (v : FinitePlace K) :
    ordAt I v ≠ 0 ↔ v.maximalIdeal.asIdeal ∣ I := by
  rw [ordAt_ne_zero_iff, Ideal.mem_normalizedFactors_iff hI, Ideal.dvd_iff_le]
  exact ⟨fun h => h.2, fun h => ⟨v.maximalIdeal.isPrime, h⟩⟩

end Ord

/-! ### Places over a place of a subfield -/

section Relative

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The places of `K` over a finite place of `k` are finitely many. -/
lemma liesOver_finite (u : FinitePlace k) :
    {v : FinitePlace K | FinitePlace.LiesOver v u}.Finite := by
  classical
  have hp0 : u.maximalIdeal.asIdeal ≠ ⊥ := u.maximalIdeal.ne_bot
  haveI : u.maximalIdeal.asIdeal.IsMaximal :=
    u.maximalIdeal.isPrime.isMaximal u.maximalIdeal.ne_bot
  refine Set.Finite.of_finite_image (f := fun v : FinitePlace K => v.maximalIdeal.asIdeal) ?_ ?_
  · refine (IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 K)).finite_toSet.subset ?_
    rintro _ ⟨v, hv, rfl⟩
    haveI : v.maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal := hv
    exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mpr ⟨inferInstance, inferInstance⟩
  · intro v₁ _ v₂ _ h
    exact FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h)

/-- The finite set of places of `K` over a finite place of `k`. -/
noncomputable def placesOver (u : FinitePlace k) : Finset (FinitePlace K) :=
  (liesOver_finite (K := K) u).toFinset

@[simp] lemma mem_placesOver (u : FinitePlace k) (v : FinitePlace K) :
    v ∈ placesOver (K := K) u ↔ FinitePlace.LiesOver v u := by
  rw [placesOver, Set.Finite.mem_toFinset]
  rfl

/-- **The fundamental identity** `∑_{v ∣ u} e(v/u) f(v/u) = [K : k]`, for any finset `s` of
places of `K` consisting of exactly the places over `u`. -/
theorem sum_relLocalDeg_liesOver (u : FinitePlace k) (s : Finset (FinitePlace K))
    (hs : ∀ v, v ∈ s ↔ FinitePlace.LiesOver v u) :
    ∑ v ∈ s, relRamIdx v u * relInertDeg v u = Module.finrank k K := by
  classical
  haveI : u.maximalIdeal.asIdeal.IsMaximal :=
    u.maximalIdeal.isPrime.isMaximal u.maximalIdeal.ne_bot
  have hp0 : u.maximalIdeal.asIdeal ≠ ⊥ := u.maximalIdeal.ne_bot
  have hsum := Ideal.sum_ramification_inertia (𝓞 K) k K hp0 (p := u.maximalIdeal.asIdeal)
  rw [← hsum]
  refine Finset.sum_bij (fun v _ => v.maximalIdeal.asIdeal) ?_ ?_ ?_ ?_
  · intro v hv
    haveI : v.maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal := (hs v).mp hv
    exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mpr ⟨inferInstance, inferInstance⟩
  · intro v₁ _ v₂ _ h
    exact (FinitePlace.maximalIdeal_inj _ _).mp (HeightOneSpectrum.ext h)
  · intro P hP
    obtain ⟨hprime, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mp hP
    have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
    refine ⟨FinitePlace.mk ⟨P, hprime, hne⟩, ?_, ?_⟩
    · rw [hs]
      unfold FinitePlace.LiesOver
      rw [FinitePlace.maximalIdeal_mk]
      exact hover
    · rw [FinitePlace.maximalIdeal_mk]
  · intro v _
    rfl

/-- `∑_{v ∣ u} e(v/u) f(v/u) = [K : k]` over `placesOver u`. -/
theorem sum_placesOver_relLocalDeg (u : FinitePlace k) :
    ∑ v ∈ placesOver (K := K) u, relRamIdx v u * relInertDeg v u = Module.finrank k K :=
  sum_relLocalDeg_liesOver u _ (mem_placesOver u)

variable {v : FinitePlace K} {u : FinitePlace k} (hvu : FinitePlace.LiesOver v u)
include hvu

/-- `e(v/u) > 0`. -/
lemma relRamIdx_pos : 0 < relRamIdx v u := Nat.pos_of_ne_zero (relRamIdx_ne_zero hvu)

/-- `f(v/u) > 0`. -/
lemma relInertDeg_pos : 0 < relInertDeg v u := by
  haveI : v.maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal := hvu
  haveI : u.maximalIdeal.asIdeal.IsMaximal :=
    u.maximalIdeal.isPrime.isMaximal u.maximalIdeal.ne_bot
  exact Nat.pos_of_ne_zero (Ideal.inertiaDeg'_ne_zero _ _)

/-- `e(v/u) ≤ [K : k]`. -/
lemma relRamIdx_le_finrank : relRamIdx v u ≤ Module.finrank k K := by
  haveI : v.maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal := hvu
  haveI : u.maximalIdeal.asIdeal.IsMaximal :=
    u.maximalIdeal.isPrime.isMaximal u.maximalIdeal.ne_bot
  haveI : NoZeroSMulDivisors (𝓞 k) (𝓞 K) := ⟨fun {c x} h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl ((map_eq_zero_iff _ algebraMap_ringOfIntegers_injective).mp h)
    · exact Or.inr h⟩
  exact Ideal.ramificationIdx_le_finrank (S := 𝓞 K) k K v.maximalIdeal.asIdeal

end Relative

/-- `e_v ≤ [K : ℚ]`. -/
lemma ramIdx_le_finrank {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) :
    ramIdx K v ≤ Module.finrank ℚ K := by
  haveI := liesOver_span_residueChar v
  haveI : (Ideal.span {(residueChar v : ℤ)}).IsMaximal :=
    LocalConstruct.span_prime_isMaximal (residueChar_prime v)
  have h : ramIdx K v =
      (Ideal.span {(residueChar v : ℤ)}).ramificationIdx' v.maximalIdeal.asIdeal := by
    unfold ramIdx
    have := (Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(residueChar v : ℤ)})
      v.maximalIdeal.asIdeal (LocalConstruct.span_prime_ne_bot (residueChar_prime v))).symm
    exact this
  rw [h]
  exact Ideal.ramificationIdx_le_finrank (S := 𝓞 K) ℚ K v.maximalIdeal.asIdeal

end Iut
