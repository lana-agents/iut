/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalTheory

/-!
# The tensor packets `⊗_j K_{c j}` as finite-dimensional topological algebras (taxis #4, #278)

This file constructs the data of `Iut.LocalTensor K` (`Iut/Concrete/LocalTheory.lean`):
for a rational place `v_ℚ` and a finite family `c : ι → Place K` of places of `K`, the
tensor packet `⊗_j K_{c j}` over the base field `ℚ_p` (for `v_ℚ = p`) or `ℝ` (for
`v_ℚ = ∞`), as a finite-dimensional commutative algebra over that base field with its
canonical (norm) topology, together with the inclusions of the factors at nonarchimedean
places.

## The factors

* At a prime `p`, the factor attached to a place `v` is the quotient
  `Factor K p v := K_{v} ⧸ junkIdeal`, where `junkIdeal = ⊥` when `v` is a finite place of
  residue characteristic `p` (so the factor *is* the completion `K_v`), and `junkIdeal = ⊤`
  otherwise (so the factor is the zero ring, and the whole packet is the zero ring: the
  junk convention for packets in which some place does not lie over `p`). This uniform
  presentation avoids type-level case splits and makes the inclusion `K_w →+* Factor`
  available for *every* finite place `w`, as the interface `LocalTheory.incl` requires.
  The `ℚ_p`-algebra structure of a genuine factor comes from the embedding
  `ℚ_p → K_w` constructed here by extending `ℚ → K → K_w` from the dense subring `ℚ`
  (`padicEmb`), and `K_w` is finite over `ℚ_p`.
* At the archimedean place the factor attached to a place `v` is the real subalgebra
  `ℝ` or `ℂ` of `ℂ` selected by whether the infinite place `archPlace v` is real
  (`archField`), lifted to the universe of `K`. (A finite place inside an archimedean
  packet is junk and is replaced by an arbitrary infinite place, so that every
  archimedean packet is a genuine nontrivial `ℝ`-algebra.)

## The packets

`Tensor K vQ c := ⨂[baseField vQ] j, Factor' K vQ (c j)` (Mathlib's `PiTensorProduct`),
a finite-dimensional commutative algebra over `baseField vQ ∈ {ℚ_p, ℝ}`. Its topology is
the unique Hausdorff vector space topology, presented by the sup norm in the coordinates of
the basis of elementary tensors of bases of the factors (`packetBasis`), and it is a
topological ring (`IsModuleTopology.isTopologicalRing`), a proper space, and, at a prime
`p`, an ultrametric space.
-/

namespace Iut

namespace LocalConstruct

open NumberField IsDedekindDomain
open scoped TensorProduct

universe u

/-- Every rational prime, as an element of `Nat.Primes`, is a prime (as an instance). -/
instance instFactPrime (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

variable (K : Type u) [Field K] [NumberField K]

/-! ### Places over a prime -/

/-- A place is *over the prime `p`* if it is a finite place of residue characteristic `p`. -/
def IsOver (p : Nat.Primes) (v : Place K) : Prop :=
  ∃ w : FinitePlace K, v = Place.finite w ∧ residueChar w = p

variable {K}

lemma isOver_finite_iff (p : Nat.Primes) (w : FinitePlace K) :
    IsOver K p (Place.finite w) ↔ residueChar w = p := by
  refine ⟨fun ⟨w', hw', h⟩ => ?_, fun h => ⟨w, rfl, h⟩⟩
  cases Sum.inl.inj hw'
  exact h

lemma not_isOver_infinite (p : Nat.Primes) (w : InfinitePlace K) :
    ¬ IsOver K p (Place.infinite w) := by
  rintro ⟨w', hw', -⟩
  simp [Place.infinite, Place.finite] at hw'

/-- The number field `K` has a finite place. -/
instance : Nonempty (FinitePlace K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨FinitePlace.mk ⟨M, hM.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩

variable (K) in
/-- The finite place underlying a place (an arbitrary finite place at infinite places;
junk, never used in a meaningful way). -/
noncomputable def finPart : Place K → FinitePlace K :=
  Sum.elim id fun _ => Classical.arbitrary _

@[simp] lemma finPart_finite (w : FinitePlace K) : finPart K (Place.finite w) = w := rfl

lemma eq_finPart {v : Place K} {w : FinitePlace K} (h : v = Place.finite w) :
    w = finPart K v := by subst h; rfl

lemma IsOver.residueChar_finPart {p : Nat.Primes} {v : Place K} (h : IsOver K p v) :
    residueChar (finPart K v) = p := by
  obtain ⟨w, rfl, hw⟩ := h
  exact hw

/-- Transport of completions along an equality of finite places. -/
noncomputable def completionCongr {w w' : FinitePlace K} (h : w = w') :
    completionAt K w ≃+* completionAt K w' :=
  h ▸ RingEquiv.refl _

@[simp] lemma completionCongr_rfl (w : FinitePlace K) :
    completionCongr (rfl : w = w) = RingEquiv.refl _ := rfl

@[simp] lemma norm_completionCongr {w w' : FinitePlace K} (h : w = w') (x : completionAt K w) :
    ‖completionCongr h x‖ = ‖x‖ := by subst h; rfl

/-! ### The embedding `ℚ_p → K_w` at a place `w` of residue characteristic `p` -/

section PadicEmbedding

variable (p : ℕ) [Fact p.Prime] (w : FinitePlace K)

/-- The residue characteristic detects the natural numbers in the maximal ideal. -/
lemma natCast_mem_maximalIdeal_iff (n : ℕ) :
    (n : 𝓞 K) ∈ w.maximalIdeal.asIdeal ↔ residueChar w ∣ n := by
  haveI : CharP (𝓞 K ⧸ w.maximalIdeal.asIdeal) (residueChar w) := ringChar.charP _
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff _ (residueChar w)]

/-- A rational number of `p`-adic norm at most `1` has denominator prime to `p`. -/
lemma not_dvd_den_of_norm_le_one {q : ℚ} (hq : ‖(q : ℚ_[p])‖ ≤ 1) : ¬ p ∣ q.den := by
  intro hden
  have hp := (Fact.out : p.Prime)
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp [Nat.Prime.ne_one hp] at hden
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro h
    have h' : p ∣ q.num.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h
      simpa using this
    have hg : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h' hden
    rw [Nat.Coprime.gcd_eq_one q.reduced] at hg
    exact hp.ne_one (Nat.dvd_one.mp hg)
  have hval : padicValRat p q = -(padicValNat p q.den : ℤ) := by
    unfold padicValRat
    rw [padicValInt.eq_zero_of_not_dvd hnum]
    simp
  have h1 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_nz hden
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hq0, hval, neg_neg] at hq
  have : (1 : ℚ) < (p : ℚ) ^ ((padicValNat p q.den : ℕ) : ℤ) := by
    rw [zpow_natCast]
    exact one_lt_pow₀ (by exact_mod_cast hp.one_lt) (by omega)
  have hq' : ((p : ℚ) ^ ((padicValNat p q.den : ℕ) : ℤ)) ≤ 1 := by exact_mod_cast hq
  exact absurd (lt_of_lt_of_le this hq') (lt_irrefl _)

/-- The ring homomorphism `ℚ → K_w`, on `ℚ` with its `p`-adic uniformity. -/
noncomputable def ratHom : WithVal (Rat.padicValuation p) →+* completionAt K w :=
  (FinitePlace.embedding w.maximalIdeal).comp
    ((Rat.castHom K).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)

/-- The inclusion `ℚ → ℚ_p`, on `ℚ` with its `p`-adic uniformity. -/
noncomputable abbrev padicCast : WithVal (Rat.padicValuation p) →+* ℚ_[p] :=
  (Rat.castHom ℚ_[p]).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom

lemma ratHom_apply (x : WithVal (Rat.padicValuation p)) :
    ratHom p w x = ((WithVal.equiv (Rat.padicValuation p) x : ℚ) : K) := rfl

variable {p w} (hw : residueChar w = p)
include hw

omit [Fact p.Prime] in
/-- `‖p‖ < 1` in `K_w` when `w` has residue characteristic `p`. -/
lemma norm_natCast_prime_lt_one : ‖((p : K) : completionAt K w)‖ < 1 := by
  have h : ((p : K) : completionAt K w) =
      FinitePlace.embedding w.maximalIdeal (algebraMap (𝓞 K) K (p : 𝓞 K)) := by
    rw [map_natCast]; rfl
  rw [h, FinitePlace.norm_lt_one_iff_mem, natCast_mem_maximalIdeal_iff, hw]

omit [Fact p.Prime] in
/-- Rational numbers whose denominator is prime to `p` are integral in `K_w`. -/
lemma norm_ratCast_le_one (q : ℚ) (hq : ¬ p ∣ q.den) : ‖((q : K) : completionAt K w)‖ ≤ 1 := by
  have hnum : ‖((q.num : K) : completionAt K w)‖ ≤ 1 := by
    have h : ((q.num : K) : completionAt K w) =
        FinitePlace.embedding w.maximalIdeal (algebraMap (𝓞 K) K (q.num : 𝓞 K)) := by
      rw [map_intCast]; rfl
    rw [h]
    exact FinitePlace.norm_le_one K _ _
  have hden : ‖((q.den : K) : completionAt K w)‖ = 1 := by
    have h : ((q.den : K) : completionAt K w) =
        FinitePlace.embedding w.maximalIdeal (algebraMap (𝓞 K) K (q.den : 𝓞 K)) := by
      rw [map_natCast]; rfl
    rw [h, FinitePlace.norm_eq_one_iff_notMem, natCast_mem_maximalIdeal_iff, hw]
    exact hq
  have : ((q : K) : completionAt K w) =
      ((q.num : K) : completionAt K w) / ((q.den : K) : completionAt K w) := by
    rw [Rat.cast_def]
    exact map_div₀ (FinitePlace.embedding w.maximalIdeal) _ _
  rw [this, norm_div, hden, div_one]
  exact hnum

/-- `p`-adically small rationals are small in `K_w`: if `‖q‖_p ≤ p^{-m}` then
`‖q‖_w ≤ ‖p‖_w^m`. -/
lemma norm_ratCast_le (q : ℚ) (m : ℕ) (hq : ‖(q : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ^ m) :
    ‖((q : K) : completionAt K w)‖ ≤ ‖((p : K) : completionAt K w)‖ ^ m := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set q' : ℚ := q / (p : ℚ) ^ m with hq'
  have hq'norm : ‖(q' : ℚ_[p])‖ ≤ 1 := by
    have hpm : ‖(((p : ℚ) ^ m : ℚ) : ℚ_[p])‖ = (p : ℝ)⁻¹ ^ m := by
      rw [Rat.cast_pow, Rat.cast_natCast, norm_pow, Padic.norm_p]
    rw [hq', Rat.cast_div, norm_div, hpm, div_le_one (by positivity)]
    exact hq
  have hden := not_dvd_den_of_norm_le_one p hq'norm
  have hle := norm_ratCast_le_one hw q' hden
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hqq : (q : K) = (p : K) ^ m * (q' : K) := by
    rw [hq']
    push_cast
    field_simp
  have : ((q : K) : completionAt K w) =
      FinitePlace.embedding w.maximalIdeal ((p : K) ^ m * (q' : K)) := by
    rw [hqq]; rfl
  rw [this, map_mul, map_pow, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) hle

/-- `ℚ → K_w` is uniformly continuous for the `p`-adic uniformity on `ℚ` when `w` has
residue characteristic `p`. -/
lemma uniformContinuous_ratHom : UniformContinuous (ratHom p w) := by
  have hb : (uniformity (WithVal (Rat.padicValuation p))).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => {x | dist (padicCast p x.1) (padicCast p x.2) < ε}) := by
    rw [← Padic.isUniformInducing_cast_withVal.comap_uniformity]
    exact Metric.uniformity_basis_dist.comap _
  rw [hb.uniformContinuous_iff Metric.uniformity_basis_dist]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_prime_lt_one hw)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨(p : ℝ)⁻¹ ^ m, pow_pos (inv_pos.mpr hp0) m, fun x y hxy => ?_⟩
  simp only [Set.mem_setOf_eq, dist_eq_norm, ← map_sub] at hxy ⊢
  calc ‖ratHom p w (x - y)‖
      = ‖(((WithVal.equiv (Rat.padicValuation p) (x - y) : ℚ) : K) : completionAt K w)‖ := rfl
    _ ≤ ‖((p : K) : completionAt K w)‖ ^ m := norm_ratCast_le hw _ m hxy.le
    _ < ε := hm

/-- **The embedding `ℚ_p → K_w`** at a finite place `w` of residue characteristic `p`:
the continuous extension of `ℚ → K → K_w` from the dense subring `ℚ ⊆ ℚ_p`. -/
noncomputable def padicEmb : ℚ_[p] →+* completionAt K w :=
  IsDenseInducing.extendRingHom (i := padicCast p) (f := ratHom p w)
    Padic.isUniformInducing_cast_withVal Padic.isDenseInducing_cast_withVal.dense
    (uniformContinuous_ratHom hw)

lemma padicEmb_apply (x : ℚ_[p]) :
    padicEmb hw x = (Padic.isUniformInducing_cast_withVal.isDenseInducing
      Padic.isDenseInducing_cast_withVal.dense).extend (ratHom p w) x := rfl

/-- The embedding `ℚ_p → K_w` restricts to `ℚ → K → K_w` on rational numbers. -/
lemma padicEmb_ratCast (q : ℚ) : padicEmb hw (q : ℚ_[p]) = ((q : K) : completionAt K w) := by
  have h := IsDenseInducing.extend_eq (Padic.isUniformInducing_cast_withVal.isDenseInducing
    Padic.isDenseInducing_cast_withVal.dense) (uniformContinuous_ratHom hw).continuous
    ((WithVal.equiv (Rat.padicValuation p)).symm q)
  rw [padicEmb_apply]
  have hx : padicCast p ((WithVal.equiv (Rat.padicValuation p)).symm q) = (q : ℚ_[p]) := by simp
  rw [← hx, h, ratHom_apply, RingEquiv.apply_symm_apply]

lemma continuous_padicEmb : Continuous (padicEmb hw) :=
  (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
    Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_ratHom hw)).continuous

/-- The `ℚ_p`-algebra structure of `K_w` (not an instance: it depends on `w ∣ p`). -/
noncomputable abbrev padicAlgebra : Algebra ℚ_[p] (completionAt K w) := (padicEmb hw).toAlgebra

lemma padicAlgebra_algebraMap : @algebraMap ℚ_[p] (completionAt K w) _ _ (padicAlgebra hw) =
    padicEmb hw := rfl

/-- The image of a `ℚ`-basis of `K` spans `K_w` over `ℚ_p`. -/
theorem span_range_finBasis_eq_top :
    letI := padicAlgebra hw
    Submodule.span ℚ_[p]
      (Set.range fun i => ((Module.finBasis ℚ K i : K) : completionAt K w)) = ⊤ := by
  letI := padicAlgebra hw
  haveI : ContinuousSMul ℚ_[p] (completionAt K w) :=
    continuousSMul_of_algebraMap ℚ_[p] _ (continuous_padicEmb hw)
  let b := Module.finBasis ℚ K
  let S : Submodule ℚ_[p] (completionAt K w) :=
    Submodule.span ℚ_[p] (Set.range fun i => ((b i : K) : completionAt K w))
  haveI : FiniteDimensional ℚ_[p] S := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hS : IsClosed (S : Set (completionAt K w)) := Submodule.closed_of_finiteDimensional S
  have hrange : Set.range (algebraMap K (completionAt K w)) ⊆ S := by
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : algebraMap K (completionAt K w) (b.repr x i • b i) =
        (b.repr x i : ℚ_[p]) • algebraMap K (completionAt K w) (b i) := by
      rw [Rat.smul_def, map_mul, Algebra.smul_def, padicAlgebra_algebraMap, padicEmb_ratCast]
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [eq_top_iff]
  intro x _
  have hdense : Dense (Set.range (algebraMap K (completionAt K w))) :=
    HeightOneSpectrum.denseRange_algebraMap K w.maximalIdeal
  exact (hS.closure_subset_iff.mpr hrange) (hdense.closure_eq ▸ Set.mem_univ x)

/-- `K_w` is finite-dimensional over `ℚ_p`. -/
theorem finite_padicAlgebra :
    @Module.Finite ℚ_[p] (completionAt K w) _ _ (padicAlgebra hw).toModule := by
  letI := padicAlgebra hw
  rw [Module.finite_def, ← span_range_finBasis_eq_top hw]
  exact Submodule.fg_span (Set.finite_range _)

end PadicEmbedding

/-! ### The nonarchimedean factors -/

section Factor

variable (K)

open Classical in
/-- The junk ideal: `⊥` when `v` lies over `p` (so that the factor is the completion),
`⊤` otherwise (so that the factor is the zero ring). -/
noncomputable def junkIdeal (p : Nat.Primes) (v : Place K) : Ideal (completionAt K (finPart K v)) :=
  if IsOver K p v then ⊥ else ⊤

/-- **The nonarchimedean factor** attached to the prime `p` and the place `v`: the completion
`K_v` when `v` is a finite place of residue characteristic `p`, the zero ring otherwise. -/
def Factor (p : Nat.Primes) (v : Place K) : Type u :=
  completionAt K (finPart K v) ⧸ junkIdeal K p v

variable {K}

lemma junkIdeal_eq_bot {p : Nat.Primes} {v : Place K} (h : IsOver K p v) :
    junkIdeal K p v = ⊥ := by
  unfold junkIdeal
  rw [if_pos h]

lemma junkIdeal_eq_top {p : Nat.Primes} {v : Place K} (h : ¬ IsOver K p v) :
    junkIdeal K p v = ⊤ := by
  unfold junkIdeal
  rw [if_neg h]

variable (p : Nat.Primes) (v : Place K)

noncomputable instance : CommRing (Factor K p v) :=
  inferInstanceAs (CommRing (completionAt K (finPart K v) ⧸ junkIdeal K p v))

/-- The quotient map from the completion to the factor. -/
noncomputable def factorMk : completionAt K (finPart K v) →+* Factor K p v :=
  Ideal.Quotient.mk (junkIdeal K p v)

lemma factorMk_surjective : Function.Surjective (factorMk p v) :=
  Ideal.Quotient.mk_surjective

lemma factorMk_eq_zero_iff {x : completionAt K (finPart K v)} :
    factorMk p v x = 0 ↔ x ∈ junkIdeal K p v :=
  Ideal.Quotient.eq_zero_iff_mem

lemma factorMk_injective (h : IsOver K p v) : Function.Injective (factorMk p v) := by
  intro x y hxy
  rw [← sub_eq_zero, ← map_sub, factorMk_eq_zero_iff, junkIdeal_eq_bot h, Ideal.mem_bot,
    sub_eq_zero] at hxy
  exact hxy

lemma subsingleton_factor (h : ¬ IsOver K p v) : Subsingleton (Factor K p v) :=
  (Ideal.Quotient.subsingleton_iff (I := junkIdeal K p v)).mpr (junkIdeal_eq_top h)

/-- Nonzero elements of the completion are units in the factor (trivially so in the zero
ring). -/
lemma isUnit_factorMk {x : completionAt K (finPart K v)} (hx : x ≠ 0) :
    IsUnit (factorMk p v x) :=
  ⟨⟨factorMk p v x, factorMk p v x⁻¹, by rw [← map_mul, mul_inv_cancel₀ hx, map_one],
    by rw [← map_mul, inv_mul_cancel₀ hx, map_one]⟩, rfl⟩

/-- The trivial ring homomorphism into a subsingleton ring. -/
def RingHom.toSubsingleton (R S : Type*) [Semiring R] [Semiring S] [Subsingleton S] :
    R →+* S where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := rfl
  map_add' _ _ := Subsingleton.elim _ _

open Classical in
/-- The structure map `ℚ_p → Factor K p v`: the embedding `ℚ_p → K_v` followed by the quotient
map when `v ∣ p`, the trivial map to the zero ring otherwise. -/
noncomputable def factorAlgebraMap : ℚ_[p] →+* Factor K p v :=
  if h : IsOver K p v then (factorMk p v).comp (padicEmb h.residueChar_finPart)
  else
    haveI := subsingleton_factor p v h
    RingHom.toSubsingleton _ _

lemma factorAlgebraMap_of_isOver (h : IsOver K p v) :
    factorAlgebraMap p v = (factorMk p v).comp (padicEmb h.residueChar_finPart) := by
  unfold factorAlgebraMap
  rw [dif_pos h]

noncomputable instance : Algebra ℚ_[p] (Factor K p v) := (factorAlgebraMap p v).toAlgebra

lemma algebraMap_factor : algebraMap ℚ_[p] (Factor K p v) = factorAlgebraMap p v := rfl

lemma algebraMap_factor_apply_of_isOver (h : IsOver K p v) (c : ℚ_[p]) :
    algebraMap ℚ_[p] (Factor K p v) c = factorMk p v (padicEmb h.residueChar_finPart c) := by
  rw [algebraMap_factor, factorAlgebraMap_of_isOver p v h]
  rfl

/-- The factors are finite-dimensional over `ℚ_p`. -/
instance : Module.Finite ℚ_[p] (Factor K p v) := by
  by_cases h : IsOver K p v
  · letI := padicAlgebra h.residueChar_finPart
    haveI := finite_padicAlgebra h.residueChar_finPart
    let f : completionAt K (finPart K v) →ₗ[ℚ_[p]] Factor K p v :=
      { toFun := factorMk p v
        map_add' := map_add _
        map_smul' := fun c x => by
          simp only [RingHom.id_apply]
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, algebraMap_factor_apply_of_isOver p v h]
          rfl }
    exact Module.Finite.of_surjective f (factorMk_surjective p v)
  · haveI := subsingleton_factor p v h
    exact Module.Finite.of_finite

lemma nontrivial_factor (h : IsOver K p v) : Nontrivial (Factor K p v) :=
  (factorMk_injective p v h).nontrivial

end Factor

/-! ### The archimedean factors -/

section ArchFactor

variable (K)

/-- The infinite place underlying a place (an arbitrary infinite place at finite places;
junk). -/
noncomputable def archPlace : Place K → InfinitePlace K :=
  Sum.elim (fun _ => Classical.arbitrary _) id

@[simp] lemma archPlace_infinite (w : InfinitePlace K) : archPlace K (Place.infinite w) = w := rfl

open Classical in
/-- The real subalgebra `ℝ` (for a real place) or `ℂ` (for a complex place) of `ℂ`
attached to an infinite place. -/
noncomputable def archField (w : InfinitePlace K) : Subalgebra ℝ ℂ :=
  if w.IsReal then ⊥ else ⊤

omit [NumberField K] in
lemma archField_of_isReal {w : InfinitePlace K} (h : w.IsReal) : archField K w = ⊥ := by
  unfold archField; rw [if_pos h]

omit [NumberField K] in
lemma archField_of_isComplex {w : InfinitePlace K} (h : w.IsComplex) : archField K w = ⊤ := by
  unfold archField; rw [if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr h)]

/-- **The archimedean factor** attached to a place `v`: the completion `ℝ` or `ℂ` of `K` at
the infinite place `archPlace v`, lifted to the universe of `K`. -/
def ArchFactor (v : Place K) : Type u := ULift.{u} (archField K (archPlace K v))

variable {K} (v : Place K)

noncomputable instance : CommRing (ArchFactor K v) :=
  inferInstanceAs (CommRing (ULift (archField K (archPlace K v))))

noncomputable instance : Algebra ℝ (ArchFactor K v) :=
  inferInstanceAs (Algebra ℝ (ULift (archField K (archPlace K v))))

instance : Module.Finite ℝ (ArchFactor K v) :=
  inferInstanceAs (Module.Finite ℝ (ULift (archField K (archPlace K v))))

instance : Nontrivial (ArchFactor K v) :=
  inferInstanceAs (Nontrivial (ULift (archField K (archPlace K v))))

end ArchFactor

/-! ### The base fields and the factors, uniformly in the rational place -/

/-- The base field of the packets at a rational place: `ℚ_p` at `p`, `ℝ` at `∞`. -/
abbrev baseField : RationalPlace → Type
  | .finite p => ℚ_[p]
  | .infinite => ℝ

noncomputable instance instNontriviallyNormedFieldBaseField (vQ : RationalPlace) :
    NontriviallyNormedField (baseField vQ) :=
  match vQ with
  | .finite p => inferInstanceAs (NontriviallyNormedField ℚ_[p])
  | .infinite => inferInstanceAs (NontriviallyNormedField ℝ)

instance instCompleteSpaceBaseField (vQ : RationalPlace) : CompleteSpace (baseField vQ) :=
  match vQ with
  | .finite p => inferInstanceAs (CompleteSpace ℚ_[p])
  | .infinite => inferInstanceAs (CompleteSpace ℝ)

instance instProperSpaceBaseField (vQ : RationalPlace) : ProperSpace (baseField vQ) :=
  match vQ with
  | .finite p => inferInstanceAs (ProperSpace ℚ_[p])
  | .infinite => inferInstanceAs (ProperSpace ℝ)

variable (K) in
/-- The factor attached to a rational place and a place of `K`. -/
abbrev Factor' : RationalPlace → Place K → Type u
  | .finite p => Factor K p
  | .infinite => ArchFactor K

noncomputable instance instCommRingFactor' (vQ : RationalPlace) (v : Place K) :
    CommRing (Factor' K vQ v) :=
  match vQ with
  | .finite p => inferInstanceAs (CommRing (Factor K p v))
  | .infinite => inferInstanceAs (CommRing (ArchFactor K v))

noncomputable instance instAlgebraFactor' (vQ : RationalPlace) (v : Place K) :
    Algebra (baseField vQ) (Factor' K vQ v) :=
  match vQ with
  | .finite p => inferInstanceAs (Algebra ℚ_[p] (Factor K p v))
  | .infinite => inferInstanceAs (Algebra ℝ (ArchFactor K v))

instance instFiniteFactor' (vQ : RationalPlace) (v : Place K) :
    Module.Finite (baseField vQ) (Factor' K vQ v) :=
  match vQ with
  | .finite p => inferInstanceAs (Module.Finite ℚ_[p] (Factor K p v))
  | .infinite => inferInstanceAs (Module.Finite ℝ (ArchFactor K v))

/-! ### The tensor packets -/

variable (K) in
/-- **The tensor packet** `⊗_j K_{c j}` over `ℚ_p` (at `v_ℚ = p`) or `ℝ` (at `v_ℚ = ∞`). -/
abbrev Tensor {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K) : Type u :=
  ⨂[baseField vQ] j, Factor' K vQ (c j)

section Tensor

variable {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K)


end Tensor

section Tensor

variable {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K)

/-- The index type of the basis of elementary tensors of the packet. -/
abbrev PacketIndex : Type := ∀ j, Fin (Module.finrank (baseField vQ) (Factor' K vQ (c j)))

noncomputable instance : Fintype (PacketIndex vQ c) := by classical exact inferInstance

/-- **The basis of elementary tensors** `⊗_j b_j(k_j)` of the packet, from chosen bases
`b_j` of the factors. -/
noncomputable def packetBasis :
    Module.Basis (PacketIndex vQ c) (baseField vQ) (Tensor K vQ c) :=
  Basis.piTensorProduct fun j => Module.finBasis (baseField vQ) (Factor' K vQ (c j))

/-- **The norm of the packet**: the sup norm of the coordinates in the basis of elementary
tensors. Its topology is the unique Hausdorff vector space topology of the packet. -/
noncomputable instance instNormedAddCommGroupTensor : NormedAddCommGroup (Tensor K vQ c) :=
  NormedAddCommGroup.induced (Tensor K vQ c) (PacketIndex vQ c → baseField vQ)
    (packetBasis vQ c).equivFun (packetBasis vQ c).equivFun.injective

noncomputable instance instNormedSpaceTensor : NormedSpace (baseField vQ) (Tensor K vQ c) :=
  NormedSpace.induced (baseField vQ) (Tensor K vQ c) (PacketIndex vQ c → baseField vQ)
    (packetBasis vQ c).equivFun

lemma norm_def (x : Tensor K vQ c) : ‖x‖ = ‖(packetBasis vQ c).equivFun x‖ := rfl

lemma dist_def (x y : Tensor K vQ c) :
    dist x y = dist ((packetBasis vQ c).equivFun x) ((packetBasis vQ c).equivFun y) := rfl

/-- The packet carries the module topology. -/
instance instIsModuleTopologyTensor : IsModuleTopology (baseField vQ) (Tensor K vQ c) :=
  isModuleTopologyOfFiniteDimensional

/-- **The packet is a topological ring.** -/
instance instIsTopologicalRingTensor : IsTopologicalRing (Tensor K vQ c) :=
  IsModuleTopology.isTopologicalRing (baseField vQ) _

/-- **The packet is a proper (locally compact) space.** -/
instance instProperSpaceTensor : ProperSpace (Tensor K vQ c) :=
  FiniteDimensional.proper (baseField vQ) _

instance instSecondCountableTopologyTensor : SecondCountableTopology (Tensor K vQ c) := by
  haveI : SecondCountableTopology (PacketIndex vQ c → baseField vQ) := by
    haveI : ∀ vQ : RationalPlace, SecondCountableTopology (baseField vQ) := fun vQ =>
      match vQ with
      | .finite p =>
        haveI : TopologicalSpace.SeparableSpace ℚ_[p] :=
          ⟨⟨Set.range ((↑) : ℚ → ℚ_[p]), Set.countable_range _, Padic.denseRange_ratCast p⟩⟩
        inferInstanceAs (SecondCountableTopology ℚ_[p])
      | .infinite => inferInstanceAs (SecondCountableTopology ℝ)
    infer_instance
  exact (packetBasis vQ c).equivFunL.toHomeomorph.isInducing.secondCountableTopology

/-! The instances above are keyed on a variable rational place; instance search does not
find them at the constructors `.finite p` and `.infinite` (the base field reduces there),
so we restate them. -/

noncomputable instance (p : Nat.Primes) : NormedAddCommGroup (Tensor K (.finite p) c) :=
  instNormedAddCommGroupTensor (.finite p) c

noncomputable instance : NormedAddCommGroup (Tensor K .infinite c) :=
  instNormedAddCommGroupTensor .infinite c

instance (p : Nat.Primes) : IsTopologicalRing (Tensor K (.finite p) c) :=
  instIsTopologicalRingTensor (.finite p) c

instance : IsTopologicalRing (Tensor K .infinite c) := instIsTopologicalRingTensor .infinite c

instance (p : Nat.Primes) : ProperSpace (Tensor K (.finite p) c) :=
  instProperSpaceTensor (.finite p) c

instance : ProperSpace (Tensor K .infinite c) := instProperSpaceTensor .infinite c

instance (p : Nat.Primes) : SecondCountableTopology (Tensor K (.finite p) c) :=
  instSecondCountableTopologyTensor (.finite p) c

instance : SecondCountableTopology (Tensor K .infinite c) :=
  instSecondCountableTopologyTensor .infinite c

/-- The nonarchimedean packets are ultrametric. -/
instance (p : Nat.Primes) : IsUltrametricDist (Tensor K (.finite p) c) :=
  ⟨fun x y z => IsUltrametricDist.dist_triangle_max ((packetBasis (.finite p) c).equivFun x)
    ((packetBasis (.finite p) c).equivFun y) ((packetBasis (.finite p) c).equivFun z)⟩

/-- Specialization of the normed-space instance at a prime. -/
noncomputable instance (p : Nat.Primes) : NormedSpace ℚ_[p] (Tensor K (.finite p) c) :=
  instNormedSpaceTensor (.finite p) c

/-- Specialization of the normed-space instance at the archimedean place. -/
noncomputable instance : NormedSpace ℝ (Tensor K .infinite c) :=
  instNormedSpaceTensor .infinite c

end Tensor

/-! ### The inclusions of the factors -/

section Incl

variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K) (j : ι) (w : FinitePlace K)
  (h : c j = Place.finite w)

/-- The inclusion of the factor `Factor K p (c j)` into the packet, `a ↦ 1 ⊗ ⋯ ⊗ a ⊗ ⋯ ⊗ 1`. -/
noncomputable def inclFactor : Factor K p (c j) →ₐ[ℚ_[p]] Tensor K (.finite p) c :=
  haveI := Classical.decEq ι
  PiTensorProduct.singleAlgHom (R := ℚ_[p]) (A := fun j => Factor K p (c j)) j

/-- **The inclusion of the `j`-th tensor factor** `K_w → ⊗_i K_{c i}` at a nonarchimedean
place (`LocalTheory.incl`): `x ↦ 1 ⊗ ⋯ ⊗ x ⊗ ⋯ ⊗ 1`. -/
noncomputable def incl : completionAt K w →+* Tensor K (.finite p) c :=
  (inclFactor p c j).toRingHom.comp
    ((factorMk p (c j)).comp (completionCongr (eq_finPart h)).toRingHom)

lemma incl_apply (x : completionAt K w) :
    incl p c j w h x = inclFactor p c j (factorMk p (c j) (completionCongr (eq_finPart h) x)) :=
  rfl

/-- **Units of a factor are units of the packet** (`LocalTheory.isUnit_incl`). -/
lemma isUnit_incl (x : completionAt K w) (hx : x ≠ 0) : IsUnit (incl p c j w h x) := by
  rw [incl_apply]
  exact (isUnit_factorMk p (c j) ((map_ne_zero_iff _ (completionCongr _).injective).mpr hx)).map _

end Incl

/-- **The concrete tensor packets** as a `LocalTensor K`. -/
noncomputable def concreteLocalTensor : LocalTensor.{u, u} K where
  Tensor := Tensor K
  ring _ _ := inferInstance
  top _ _ := inferInstance
  algR _ := inferInstance

end LocalConstruct

end Iut
