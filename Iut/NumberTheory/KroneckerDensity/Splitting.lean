/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Rational primes splitting completely in a number field

We define what it means for a rational prime `p` to split completely in a number field `K`
and prove the basic counting lemmas.

## Main definitions

* `NumberField.SplitsCompletely K p`: `p` is prime and every prime of `𝓞 K` over `p` has
  ramification index and inertia degree `1`.

## Main results

* `NumberField.ncard_primesOver_le_finrank`: there are at most `[K : ℚ]` primes of `𝓞 K`
  over `p`.
* `NumberField.ncard_primesOver_eq_finrank_iff`: there are exactly `[K : ℚ]` of them iff `p`
  splits completely in `K`.
* `NumberField.SplitsCompletely.of_algebra`: a prime splitting completely in a finite extension
  splits completely in every subfield.
* `NumberField.splitsCompletely_of_isGalois`: if `K / ℚ` is Galois, one prime over `p` with
  ramification index and inertia degree `1` suffices.
* `NumberField.ramificationIdx_eq_one_of_not_dvd_discr`: primes not dividing the discriminant
  are unramified, so only finitely many rational primes ramify.
* `NumberField.ncard_primesOver_eq_finrank_of_splitsCompletely`: base change of splitting. If
  `E = L ⊔ M` with `L / ℚ` Galois and `p` splits completely in `L`, then every prime of `M`
  over `p` has exactly `[E : M]` primes above it in `E`, all of relative inertia degree `1`.
-/

open Ideal IsDedekindDomain Module

namespace NumberField

section RatAlgebra

/-! Over a field of characteristic zero, the `ℚ`-algebra structure is unique, but the instance
found for an intermediate field `L` of `E / ℚ` (`DivisionRing.toRatAlgebra`) is not reducibly
equal to `IntermediateField.algebra'`. These lemmas transport the relevant properties. -/

lemma isGalois_rat_iff {K : Type*} [Field K] (A₁ A₂ : Algebra ℚ K) :
    @IsGalois ℚ _ K _ A₁ ↔ @IsGalois ℚ _ K _ A₂ := by
  rw [Subsingleton.elim A₁ A₂]

lemma normal_rat_iff {K : Type*} [Field K] (A₁ A₂ : Algebra ℚ K) :
    @Normal ℚ K _ _ A₁ ↔ @Normal ℚ K _ _ A₂ := by
  rw [Subsingleton.elim A₁ A₂]

lemma finiteDimensional_rat_iff {K : Type*} [AddCommGroup K] (M₁ M₂ : Module ℚ K) :
    @FiniteDimensional ℚ K _ _ M₁ ↔ @FiniteDimensional ℚ K _ _ M₂ := by
  rw [Subsingleton.elim M₁ M₂]

end RatAlgebra

section Basic

variable (K : Type*) [Field K] [NumberField K]

/-- A natural number `p` *splits completely* in the number field `K` if it is prime and every
prime ideal of `𝓞 K` lying over `p` has ramification index and inertia degree `1`. -/
def SplitsCompletely (p : ℕ) : Prop :=
  p.Prime ∧ ∀ P ∈ (span {(p : ℤ)}).primesOver (𝓞 K),
    P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1

variable {K}

omit [NumberField K] in
lemma SplitsCompletely.prime {p : ℕ} (h : SplitsCompletely K p) : p.Prime := h.1

lemma isPrime_span_natCast {p : ℕ} (hp : p.Prime) : (span {(p : ℤ)}).IsPrime :=
  (span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)

lemma span_natCast_ne_bot {p : ℕ} (hp : p.Prime) : span {(p : ℤ)} ≠ ⊥ := by
  simpa using hp.ne_zero

lemma isMaximal_of_mem_primesOver {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K)) : P.IsMaximal := by
  have := hP.2
  exact hP.1.isMaximal (ne_bot_of_liesOver_of_ne_bot (span_natCast_ne_bot hp) P)

variable (K) in
lemma finite_primesOver_span (p : ℕ) : ((span {(p : ℤ)}).primesOver (𝓞 K)).Finite :=
  Algebra.QuasiFinite.finite_primesOver _

/-- The fundamental identity `∑ e f = [K : ℚ]` over the primes of `𝓞 K` above `p`. -/
lemma sum_ramificationIdx_mul_inertiaDeg {p : ℕ} (hp : p.Prime)
    [Fintype ((span {(p : ℤ)}).primesOver (𝓞 K))] :
    ∑ P : (span {(p : ℤ)}).primesOver (𝓞 K), P.1.ramificationIdx ℤ * P.1.inertiaDeg ℤ =
      finrank ℚ K := by
  have := isPrime_span_natCast hp
  rw [sum_ramification_inertia_eq_finrank, RingOfIntegers.rank]

lemma one_le_ramificationIdx_mul_inertiaDeg (P : (span {(p : ℤ)}).primesOver (𝓞 K)) :
    1 ≤ P.1.ramificationIdx ℤ * P.1.inertiaDeg ℤ :=
  Nat.one_le_iff_ne_zero.mpr <| Nat.mul_ne_zero (P.1.ramificationIdx_pos ℤ).ne'
    (P.1.inertiaDeg_pos ℤ).ne'

/-- There are at most `[K : ℚ]` primes of `𝓞 K` over a rational prime `p`. -/
theorem ncard_primesOver_le_finrank {p : ℕ} (hp : p.Prime) :
    ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard ≤ finrank ℚ K := by
  have := (finite_primesOver_span K p).fintype
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_ones, ← sum_ramificationIdx_mul_inertiaDeg hp]
  exact Finset.sum_le_sum fun P _ ↦ one_le_ramificationIdx_mul_inertiaDeg P

/-- `p` splits completely iff there are exactly `[K : ℚ]` primes of `𝓞 K` over `p`. -/
theorem ncard_primesOver_eq_finrank_iff {p : ℕ} (hp : p.Prime) :
    ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard = finrank ℚ K ↔ SplitsCompletely K p := by
  have := (finite_primesOver_span K p).fintype
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_ones, ← sum_ramificationIdx_mul_inertiaDeg hp,
    Finset.sum_eq_sum_iff_of_le fun P _ ↦ one_le_ramificationIdx_mul_inertiaDeg P]
  constructor
  · exact fun h ↦ ⟨hp, fun P hP ↦ mul_eq_one.mp (h ⟨P, hP⟩ (Finset.mem_univ _)).symm⟩
  · exact fun h P _ ↦ (mul_eq_one.mpr (h.2 P.1 P.2)).symm

/-- If `p` splits completely in `K`, there are exactly `[K : ℚ]` primes over `p`. -/
theorem SplitsCompletely.ncard_primesOver {p : ℕ} (h : SplitsCompletely K p) :
    ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard = finrank ℚ K :=
  (ncard_primesOver_eq_finrank_iff h.1).mpr h

/-- A prime splitting completely in an extension `F` of `K` splits completely in `K`. -/
theorem SplitsCompletely.of_algebra {F : Type*} [Field F] [NumberField F] [Algebra K F]
    {p : ℕ} (h : SplitsCompletely F p) : SplitsCompletely K p := by
  refine ⟨h.1, fun Q hQ ↦ ?_⟩
  have := hQ.1
  have := hQ.2
  obtain ⟨P, _, _⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 F)))
  have : P.LiesOver (span {(p : ℤ)}) := .trans P Q _
  obtain ⟨he, hf⟩ := h.2 P ⟨inferInstance, inferInstance⟩
  rw [ramificationIdx_tower (q := Q)] at he
  rw [inertiaDeg_tower (q := Q)] at hf
  exact ⟨Nat.eq_one_of_mul_eq_one_right he, Nat.eq_one_of_mul_eq_one_right hf⟩

/-- In a Galois number field, a single prime over `p` with ramification index and inertia degree
`1` forces `p` to split completely. -/
theorem splitsCompletely_of_isGalois [IsGalois ℚ K] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 K))
    (hP : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K)) (he : P.ramificationIdx ℤ = 1)
    (hf : P.inertiaDeg ℤ = 1) : SplitsCompletely K p := by
  refine ⟨hp, fun Q hQ ↦ ?_⟩
  have := hP.1
  have := hP.2
  have := hQ.1
  have := hQ.2
  exact ⟨(ramificationIdx_eq_of_isGaloisGroup (span {(p : ℤ)}) Q P Gal(K/ℚ)).trans he,
    (inertiaDeg_eq_of_isGaloisGroup (span {(p : ℤ)}) Q P Gal(K/ℚ)).trans hf⟩

/-- A prime of `𝓞 K` above a rational prime `p` not dividing the discriminant is unramified. -/
theorem ramificationIdx_eq_one_of_not_dvd_discr {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr K) {P : Ideal (𝓞 K)}
    (hP : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K)) : P.ramificationIdx ℤ = 1 := by
  have := hP.1
  have := hP.2
  have := (not_dvd_discr_iff_forall_liesOver K (𝓞 K) (Nat.prime_iff_prime_int.mp hp)).mp hd P
    (isMaximal_of_mem_primesOver hp hP) hP.2
  exact P.ramificationIdx_eq_one_of_isUnramifiedAt

variable (K) in
/-- Only finitely many rational primes divide the discriminant (and hence ramify). -/
theorem finite_setOf_dvd_discr : {p : ℕ | (p : ℤ) ∣ discr K}.Finite :=
  (Set.finite_Iic (discr K).natAbs).subset fun _ hp ↦
    Nat.le_of_dvd (Int.natAbs_pos.mpr (discr_ne_zero K)) (Int.natCast_dvd.mp hp)

/-- The absolute norm of a prime over `p` is `p ^ f`. -/
theorem absNorm_eq_pow_inertiaDeg_of_mem_primesOver {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K)) : absNorm P = p ^ P.inertiaDeg ℤ := by
  have := hP.1
  have := hP.2
  have := (isPrime_span_natCast hp).isMaximal (span_natCast_ne_bot hp)
  have := isMaximal_of_mem_primesOver hp hP
  rw [absNorm_eq_pow_inertiaDeg' P hp, inertiaDeg'_eq_inertiaDeg]

/-- A prime of `𝓞 K` over `p` has absolute norm `p` iff its inertia degree is `1`. -/
theorem absNorm_eq_iff_inertiaDeg_eq_one {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K)) : absNorm P = p ↔ P.inertiaDeg ℤ = 1 := by
  rw [absNorm_eq_pow_inertiaDeg_of_mem_primesOver hp hP]
  conv_lhs => rhs; rw [← pow_one p]
  exact (Nat.pow_right_injective hp.two_le).eq_iff

/-- A nonzero prime of `𝓞 K` whose absolute norm is a prime number `p` lies over `p`. -/
theorem mem_primesOver_of_absNorm_eq {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} [P.IsPrime]
    (h : absNorm P = p) : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by
  refine ⟨inferInstance, (liesOver_span_iff ?_ (Nat.prime_iff_prime_int.mp hp)).mpr ?_⟩
  · exact IsPrime.ne_top ‹_›
  · have := absNorm_mem P
    rw [h] at this
    simpa using this

end Basic

section BaseChange

open MulAction Pointwise

variable {K : Type*} [Field K] [NumberField K]

/-- If `p` splits completely in the Galois number field `K`, then `Gal(K/ℚ)` acts freely on the
primes of `𝓞 K` over `p`: all decomposition groups are trivial. (The `ℚ`-algebra structure on
`K` is arbitrary, so that the lemma applies to intermediate fields.) -/
theorem SplitsCompletely.stabilizer_eq_bot [Algebra ℚ K] [IsGalois ℚ K] {p : ℕ}
    (h : SplitsCompletely K p) (Q : Ideal (𝓞 K)) (hQ : Q ∈ (span {(p : ℤ)}).primesOver (𝓞 K)) :
    stabilizer Gal(K/ℚ) Q = ⊥ := by
  obtain rfl : ‹Algebra ℚ K› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have := hQ.1
  have := hQ.2
  have h1 := (stabilizer Gal(K/ℚ) Q).card_mul_index
  rw [index_stabilizer, Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 K) Gal(K/ℚ) (span {(p : ℤ)}) Q,
    h.ncard_primesOver, IsGalois.card_aut_eq_finrank] at h1
  exact Subgroup.card_eq_one.mp (Nat.eq_of_mul_eq_mul_right finrank_pos (h1.trans (one_mul _).symm))

variable {E : Type*} [Field E] [NumberField E] (L M : IntermediateField ℚ E) [IsGalois ℚ L]

/-- Base change of complete splitting, group-theoretic form. Let `E = L ⊔ M` with `L / ℚ`
Galois and let `p` split completely in `L`. Then `Gal(E/M)` acts freely on the primes of `𝓞 E`
above `p`. -/
theorem stabilizer_eq_bot_of_splitsCompletely (hLM : L ⊔ M = ⊤) {p : ℕ}
    (hL : SplitsCompletely L p) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    stabilizer Gal(E/M) P = ⊥ := by
  letI : Algebra ℚ L := IntermediateField.algebra' L
  have : IsGalois ℚ L := (isGalois_rat_iff DivisionRing.toRatAlgebra _).mp inferInstance
  set Q : Ideal (𝓞 L) := P.under (𝓞 L)
  have hQ : Q ∈ (span {(p : ℤ)}).primesOver (𝓞 L) := ⟨inferInstance, .tower_bot P Q _⟩
  have hcomm (σ : Gal(E/M)) (x : 𝓞 L) :
      algebraMap (𝓞 L) (𝓞 E) (IntermediateField.restrictRestrictAlgEquivMapHom ℚ L M E σ • x) =
        σ • algebraMap (𝓞 L) (𝓞 E) x := by
    ext
    exact IntermediateField.restrictRestrictAlgEquivMapHom_apply L M σ x
  refine (Subgroup.eq_bot_iff_forall _).mpr fun σ hσ ↦ ?_
  have hσ : σ • P = P := hσ
  apply IntermediateField.restrictRestrictAlgEquivMapHom_injective L M hLM
  rw [map_one, ← Subgroup.mem_bot, ← hL.stabilizer_eq_bot Q hQ, mem_stabilizer_iff]
  ext x
  rw [mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, Ideal.mem_comap]
  refine (iff_of_eq (congrArg (· ∈ P) (hcomm σ⁻¹ x))).trans ?_
  rw [← mem_pointwise_smul_iff_inv_smul_mem, hσ]
  exact Iff.rfl

/-- Base change of complete splitting. Let `E = L ⊔ M` with `L / ℚ` Galois and let `p` split
completely in `L`. Then every prime `𝔭` of `𝓞 M` over `p` has exactly `[E : M]` primes above it
in `𝓞 E`, each of relative inertia degree `1`. -/
theorem ncard_primesOver_eq_finrank_of_splitsCompletely (hLM : L ⊔ M = ⊤) {p : ℕ}
    (hL : SplitsCompletely L p) (𝔭 : Ideal (𝓞 M)) [𝔭.IsPrime] [𝔭.LiesOver (span {(p : ℤ)})] :
    (𝔭.primesOver (𝓞 E)).ncard = finrank M E ∧
      ∀ P ∈ 𝔭.primesOver (𝓞 E), P.inertiaDeg (𝓞 M) = 1 := by
  have : @IsGalois ℚ _ L _ (IntermediateField.algebra' L) := (isGalois_rat_iff _ _).mp ‹_›
  have := IsGalois.sup_right L M hLM
  obtain ⟨P, _, _⟩ := (inferInstance : Nonempty (𝔭.primesOver (𝓞 E)))
  have : P.LiesOver (span {(p : ℤ)}) := .trans P 𝔭 _
  have h1 := (stabilizer Gal(E/M) P).card_mul_index
  rw [index_stabilizer, Algebra.IsInvariant.orbit_eq_primesOver (𝓞 M) (𝓞 E) Gal(E/M) 𝔭 P,
    stabilizer_eq_bot_of_splitsCompletely L M hLM hL P, Subgroup.card_bot, one_mul] at h1
  have h2 := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭 (𝓞 E) Gal(E/M)
  rw [← h1, Nat.mul_eq_left (by rw [h1]; exact Nat.card_pos.ne'), mul_eq_one] at h2
  refine ⟨h1.trans (IsGalois.card_aut_eq_finrank M E), fun Q hQ ↦ ?_⟩
  have := hQ.1
  have := hQ.2
  rw [← inertiaDegIn_eq_inertiaDeg 𝔭 Q Gal(E/M)]
  exact h2.2

end BaseChange

end NumberField
