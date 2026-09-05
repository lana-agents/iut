/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.PadicLog
import Iut.Concrete.LocalConstruct.ThetaAdmissible
import Iut.Concrete.LocalConstruct.Arithmetic

/-!
# The tensor product of the log-shells at a prime (taxis #4, #278)

The **log-shell** `𝓘_I = ⊗_j 𝓘_{c j}` of a nonarchimedean packet (IUT III, Proposition 3.2;
`LocalTheory.logShell` at a prime) is the `ℤ_p`-span of the elementary tensors of the
log-shells `𝓘_v = (2p)⁻¹·log(𝓞_v^×)` of the factors (`Iut.logShell`, `PadicLog.lean`),
transported to the factors `Factor K p v` (`factorLogShell`, `logShell`). We prove:

* `order_subset_logShell`: `R_I ⊆ 𝓘_I` (factorwise `closedBall_subset_logShell`);
* `isOpen_logShell`, `isClosed_logShell`, `isCompact_logShell`: `𝓘_I` is a compact open
  subgroup (it contains `R_I`, and is bounded since the factor log-shells are);
* `logShell_eq_order_of_unramified`: at an odd prime unramified in every factor,
  `𝓘_I = R_I` (factorwise `logShell_eq_closedBall`);
* `mapAlgHom_image_logShell_subset`: the indeterminacy automorphisms preserve `𝓘_I`
  (IUT IV, Proposition 1.2). The key point is that an automorphism `τ` of `K_v` over `ℚ_p`
  is continuous (`ℚ_p`-linear on a finite-dimensional space), hence preserves the principal
  units (`‖u − 1‖ < 1` iff `(u − 1)^n → 0`) and commutes with the `p`-adic logarithm (a
  convergent power series), so it preserves `𝓘_v` (`RingHom.image_logShell_subset`);
* `thetaShell_admissible` at a prime.

Along the way: the completions `K_w` are proper spaces and have characteristic zero.
-/

namespace Iut

open Filter Topology
open scoped Valued

universe u

/-! ### Continuous ring homomorphisms preserve the log-shell -/

section RingHom

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]

/-- In a normed field, `‖a‖ < 1` iff `a^n → 0`. -/
theorem norm_lt_one_iff_tendsto_pow {F : Type*} [NormedField F] (a : F) :
    ‖a‖ < 1 ↔ Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := by
  refine ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one, fun h => ?_⟩
  by_contra hle
  push Not at hle
  rw [NormedAddGroup.tendsto_nhds_zero] at h
  obtain ⟨n, hn⟩ := (h 1 one_pos).exists
  rw [norm_pow] at hn
  exact absurd hn (not_lt.mpr (one_le_pow₀ hle))

/-- A continuous ring endomorphism preserves the principal units. -/
theorem norm_map_sub_one_lt (τ : k →+* k) (hτ : Continuous τ) {u : k} (hu : ‖u - 1‖ < 1) :
    ‖τ u - 1‖ < 1 := by
  rw [norm_lt_one_iff_tendsto_pow] at hu ⊢
  have h := (hτ.tendsto 0).comp hu
  rw [map_zero] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, map_pow, map_sub, map_one]

/-- `0` lies in the log-shell. -/
theorem zero_mem_logShell {p : ℕ} : (0 : k) ∈ logShell k p :=
  ⟨1, by simp, by simp⟩

variable [CompleteSpace k] [CharZero k] {p : ℕ}

/-- A continuous ring endomorphism commutes with the `p`-adic logarithm. -/
theorem map_padicLog (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) (τ : k →+* k) (hτ : Continuous τ)
    {u : k} (hu : ‖u - 1‖ < 1) : τ (padicLog u) = padicLog (τ u) := by
  have h := (hasSum_padicLog hp hpk hu).map τ hτ
  have hterm : (⇑τ ∘ logTerm u) = logTerm (τ u) := by
    funext n
    simp only [Function.comp_apply, logTerm, map_div₀, map_mul, map_pow, map_neg, map_one,
      map_sub, map_add, map_natCast]
  rw [hterm] at h
  exact h.tsum_eq.symm

/-- **A continuous ring endomorphism preserves the log-shell.** -/
theorem RingHom.image_logShell_subset (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) (τ : k →+* k)
    (hτ : Continuous τ) : τ '' logShell k p ⊆ logShell k p := by
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨τ u, norm_map_sub_one_lt τ hτ hu, ?_⟩
  rw [map_mul, map_inv₀, map_mul, map_ofNat, map_natCast, map_padicLog hp hpk τ hτ hu]

end RingHom

namespace LocalConstruct

open NumberField MeasureTheory
open scoped TensorProduct Pointwise

variable {K : Type u} [Field K] [NumberField K]

/-! ### The completions are proper spaces of characteristic zero -/

/-- The completions of a number field have characteristic zero. -/
instance instCharZeroCompletionAt (w : FinitePlace K) : CharZero (completionAt K w) :=
  charZero_of_injective_algebraMap (algebraMap K (completionAt K w)).injective

/-- **The completions of a number field are proper spaces**: closed balls are compact (they
are contained in a rescaling of the compact set of `exists_isCompact_closedBall_subset`). -/
instance instProperSpaceCompletionAt (w : FinitePlace K) : ProperSpace (completionAt K w) := by
  haveI : Fact (residueChar w).Prime := ⟨residueChar_prime w⟩
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_closedBall_subset (p := residueChar w) (w := w) rfl
  have hp1 := norm_natCast_prime_lt_one (p := residueChar w) (w := w) rfl
  have hp0 : (((residueChar w : ℕ) : K) : completionAt K w) ≠ 0 := by
    have : ((residueChar w : ℕ) : K) ≠ 0 := by exact_mod_cast (residueChar_prime w).ne_zero
    exact (map_ne_zero_iff _ (FinitePlace.embedding w.maximalIdeal).injective).mpr this
  refine ProperSpace.of_isCompact_closedBall_of_le 0 fun x r hr => ?_
  -- `closedBall x r ⊆ x + p^{-m} • C` for `‖p‖^m r ≤ 1`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ‖(((residueChar w : ℕ) : K) : completionAt K w)‖ ^ m * r ≤ 1 := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (r + 1) by positivity) hp1
    refine ⟨m, ?_⟩
    calc ‖(((residueChar w : ℕ) : K) : completionAt K w)‖ ^ m * r
        ≤ 1 / (r + 1) * r := mul_le_mul_of_nonneg_right hm.le hr
      _ ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
        linarith
  set q : completionAt K w := (((residueChar w : ℕ) : K) : completionAt K w) ^ m with hq
  have hq0 : q ≠ 0 := pow_ne_zero _ hp0
  have hcpt : IsCompact ((fun y => x + q⁻¹ * y) '' C) := hC.image (by fun_prop)
  refine hcpt.of_isClosed_subset Metric.isClosed_closedBall fun y hy => ?_
  refine ⟨q * (y - x), hsub ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_mul, hq, norm_pow]
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    calc ‖(((residueChar w : ℕ) : K) : completionAt K w)‖ ^ m * ‖y - x‖
        ≤ ‖(((residueChar w : ℕ) : K) : completionAt K w)‖ ^ m * r :=
          mul_le_mul_of_nonneg_left hy (by positivity)
      _ ≤ 1 := hm
  · dsimp only
    rw [← mul_assoc, inv_mul_cancel₀ hq0, one_mul, add_sub_cancel]

/-- `‖p‖ < 1` in `K_w` for `w ∣ p`, for the natural number cast into the completion. -/
lemma norm_natCast_lt_one_completion {p : Nat.Primes} {w : FinitePlace K}
    (hw : residueChar w = p) : ‖((p : ℕ) : completionAt K w)‖ < 1 := by
  have := norm_natCast_prime_lt_one (p := (p : ℕ)) (w := w) hw
  rwa [← FinitePlace.embedding_apply, map_natCast] at this

/-! ### The log-shells of the factors -/

section Factor

variable (p : Nat.Primes) (v : Place K)

/-- **The log-shell of a factor**: the image in `Factor K p v` of the log-shell
`𝓘_v = (2p)⁻¹·log(𝓞_v^×)` of the completion. -/
def factorLogShell : Set (Factor K p v) :=
  factorMk p v '' Iut.logShell (completionAt K (finPart K v)) p

lemma mem_factorLogShell {b : Factor K p v} :
    b ∈ factorLogShell p v ↔
      ∃ y ∈ Iut.logShell (completionAt K (finPart K v)) p, factorMk p v y = b :=
  Iff.rfl

/-- Integral elements of the completion map into the log-shell of the factor. -/
lemma factorMk_mem_factorLogShell_of_norm_le_one (a : completionAt K (finPart K v))
    (ha : ‖a‖ ≤ 1) : factorMk p v a ∈ factorLogShell p v := by
  by_cases h : IsOver K p v
  · exact ⟨a, closedBall_subset_logShell p.2 (norm_natCast_lt_one_completion h.residueChar_finPart)
      (by simpa using ha), rfl⟩
  · haveI := subsingleton_factor p v h
    exact ⟨0, zero_mem_logShell, Subsingleton.elim _ _⟩

/-- At an odd prime unramified at `v`, the log-shell of the factor consists of the images of
the integral elements. -/
lemma factorLogShell_eq_of_unramified (hodd : Odd (p : ℕ))
    (hunr : ∀ w, v = Place.finite w → ramIdx K w = 1) :
    factorLogShell p v = factorMk p v '' Metric.closedBall 0 1 := by
  by_cases h : IsOver K p v
  · have hw := h.residueChar_finPart
    have hpk := norm_natCast_lt_one_completion hw
    unfold factorLogShell
    rw [logShell_eq_closedBall p.2 hpk hodd]
    intro a ha
    -- `‖a‖ < 1 → ‖a‖ ≤ ‖p‖`: `p` is a uniformizer since `e_w = 1`
    obtain ⟨w', hw', -⟩ := h
    have he : ramIdx K (finPart K v) = 1 := by
      rw [hw', finPart_finite]
      exact hunr w' hw'
    have hvp : Valued.v ((p : ℕ) : completionAt K (finPart K v)) = WithZero.exp (-1 : ℤ) := by
      have := valued_residueChar (finPart K v)
      rw [he, hw, Nat.cast_one] at this
      rwa [map_natCast] at this
    rw [Valued.toNormedField.norm_le_iff, hvp]
    rw [Valued.toNormedField.norm_lt_one_iff] at ha
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [map_zero]; exact zero_le
    · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v a = WithZero.exp m :=
        ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 ha0)).symm⟩
      rw [hm] at ha ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at ha
      rw [WithZero.exp_le_exp]
      omega
  · haveI := subsingleton_factor p v h
    ext b
    simp only [factorLogShell, Set.mem_image]
    exact ⟨fun _ => ⟨0, by simp, Subsingleton.elim _ _⟩, fun _ => ⟨0, zero_mem_logShell,
      Subsingleton.elim _ _⟩⟩

/-- **Automorphisms of a factor preserve its log-shell.** -/
theorem algEquiv_image_factorLogShell_subset (σ : Factor K p v ≃ₐ[ℚ_[p]] Factor K p v) :
    σ '' factorLogShell p v ⊆ factorLogShell p v := by
  by_cases h : IsOver K p v
  · letI := padicAlgebra h.residueChar_finPart
    haveI := finite_padicAlgebra h.residueChar_finPart
    haveI : ContinuousSMul ℚ_[p] (completionAt K (finPart K v)) :=
      continuousSMul_of_algebraMap ℚ_[p] _ (continuous_padicEmb h.residueChar_finPart)
    set f := completionAlgEquivFactor p v h
    have hf : ∀ y, f y = factorMk p v y := fun y => rfl
    set τ : completionAt K (finPart K v) ≃ₐ[ℚ_[p]] completionAt K (finPart K v) :=
      f.trans (σ.trans f.symm)
    have hτ : Continuous τ := LinearMap.continuous_of_finiteDimensional τ.toLinearMap
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨τ y, RingHom.image_logShell_subset p.2
      (norm_natCast_lt_one_completion h.residueChar_finPart) τ.toRingEquiv.toRingHom hτ
      ⟨y, hy, rfl⟩, ?_⟩
    rw [← hf y, ← hf (τ y)]
    change f (f.symm (σ (f y))) = σ (f y)
    rw [f.apply_symm_apply]
  · haveI := subsingleton_factor p v h
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨0, zero_mem_logShell, Subsingleton.elim _ _⟩

/-- The coordinates of the elements of the log-shell of a factor are bounded. -/
theorem exists_factorLogShell_coord_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ b ∈ factorLogShell p v, ∀ k, ‖(Module.finBasis ℚ_[p] (Factor K p v)).repr b k‖ ≤ C := by
  by_cases h : IsOver K p v
  · letI := padicAlgebra h.residueChar_finPart
    haveI : ContinuousSMul ℚ_[p] (completionAt K (finPart K v)) :=
      continuousSMul_of_algebraMap ℚ_[p] _ (continuous_padicEmb h.residueChar_finPart)
    haveI := finite_padicAlgebra h.residueChar_finPart
    have hC : IsCompact (closure (Iut.logShell (completionAt K (finPart K v)) p)) :=
      isCompact_closure_logShell p.2 (norm_natCast_lt_one_completion h.residueChar_finPart)
    let g : completionAt K (finPart K v) →ₗ[ℚ_[p]]
        (Fin (Module.finrank ℚ_[p] (Factor K p v)) → ℚ_[p]) :=
      (Module.finBasis ℚ_[p] (Factor K p v)).equivFun.toLinearMap ∘ₗ factorMkₗ p v h
    have hg : Continuous g := LinearMap.continuous_of_finiteDimensional g
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hg.continuousOn
    refine ⟨max M 0, le_max_right _ _, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ k
    have hga : ‖g a‖ ≤ M := hM a (subset_closure ha)
    calc ‖(Module.finBasis ℚ_[p] (Factor K p v)).repr (factorMk p v a) k‖
        = ‖g a k‖ := by
          simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_apply]
          rfl
      _ ≤ ‖g a‖ := norm_le_pi_norm _ _
      _ ≤ max M 0 := hga.trans (le_max_left _ _)
  · refine ⟨0, le_rfl, fun b _ k => ?_⟩
    haveI := subsingleton_factor p v h
    have : Module.finrank ℚ_[p] (Factor K p v) = 0 := Module.finrank_zero_of_subsingleton
    exact absurd k.2 (by omega)

end Factor

/-! ### The log-shell of a packet -/

section Packet

variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)

/-- The elementary tensors of tuples of elements of the factor log-shells. -/
def logShellSet : Set (Tensor K (.finite p) c) :=
  Set.range fun a : ∀ j, factorLogShell p (c j) =>
    PiTensorProduct.tprod ℚ_[p] fun j => (a j : Factor K p (c j))

/-- **The tensor product of the log-shells** `𝓘_I = ⊗_j 𝓘_{c j}` as a `ℤ_p`-submodule: the
`ℤ_p`-span of the elementary tensors of tuples of elements of the factor log-shells. -/
noncomputable def logShellSubmodule : Submodule ℤ_[p] (Tensor K (.finite p) c) :=
  Submodule.span ℤ_[p] (logShellSet p c)

/-- **The tensor product of the log-shells** (`LocalTheory.logShell` at a prime). -/
noncomputable def logShell : Set (Tensor K (.finite p) c) := logShellSubmodule p c

lemma mem_logShell {x : Tensor K (.finite p) c} :
    x ∈ logShell p c ↔ x ∈ logShellSubmodule p c := Iff.rfl

/-- `R_I ⊆ 𝓘_I` (IUT III, Proposition 1.2). -/
theorem order_subset_logShell : order p c ⊆ logShell p c := by
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨fun j => ⟨factorMk p (c j) (a j).1,
    factorMk_mem_factorLogShell_of_norm_le_one p (c j) (a j).1 (a j).2⟩, rfl⟩

/-- The log-shell as an additive subgroup. -/
noncomputable def logShellAddSubgroup : AddSubgroup (Tensor K (.finite p) c) :=
  (logShellSubmodule p c).toAddSubgroup

lemma coe_logShellAddSubgroup :
    (logShellAddSubgroup p c : Set (Tensor K (.finite p) c)) = logShell p c := rfl

/-- **`𝓘_I` is open.** -/
lemma isOpen_logShell : IsOpen (logShell p c) := by
  obtain ⟨r, hr, hsub⟩ := exists_closedBall_subset_order p c
  rw [← coe_logShellAddSubgroup]
  exact AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 hr)
    (hsub.trans (order_subset_logShell p c)))

/-- **`𝓘_I` is closed.** -/
lemma isClosed_logShell : IsClosed (logShell p c) := by
  rw [← coe_logShellAddSubgroup]
  exact AddSubgroup.isClosed_of_isOpen _ (isOpen_logShell p c)

/-- The `ℤ_p`-span of a uniformly bounded set is bounded by the same bound. -/
lemma span_subset_closedBall_of_forall_norm_le (s : Set (Tensor K (.finite p) c)) (M : ℝ)
    (hM : 0 ≤ M) (hs : ∀ x ∈ s, ‖x‖ ≤ M) :
    (Submodule.span ℤ_[p] s : Set (Tensor K (.finite p) c)) ⊆ Metric.closedBall 0 M := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simpa using hM
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | smul r x _ hx =>
    change ‖(r : ℚ_[p]) • x‖ ≤ _
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one r)).trans hx

/-- The elementary tensors of tuples of elements of the factor log-shells are bounded. -/
lemma exists_norm_logShellSet_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ logShellSet p c, ‖x‖ ≤ M := by
  choose C hC0 hC using fun j => exists_factorLogShell_coord_bound p (c j)
  refine ⟨∏ j, C j, Finset.prod_nonneg fun j _ => hC0 j, ?_⟩
  rintro _ ⟨a, rfl⟩
  change ‖(packetBasis (RationalPlace.finite p) c).equivFun
    (PiTensorProduct.tprod ℚ_[p] fun j => (a j : Factor K p (c j)))‖ ≤ _
  rw [pi_norm_le_iff_of_nonneg (Finset.prod_nonneg fun j _ => hC0 j)]
  intro k
  rw [Module.Basis.equivFun_apply]
  unfold packetBasis
  rw [Basis.piTensorProduct_repr_tprod_apply, norm_prod]
  exact Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => hC j _ (a j).2 _

/-- **`𝓘_I` is bounded.** -/
lemma exists_logShell_subset_closedBall : ∃ M : ℝ, logShell p c ⊆ Metric.closedBall 0 M := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_logShellSet_le p c
  exact ⟨M, span_subset_closedBall_of_forall_norm_le p c _ M hM0 hM⟩

lemma isBounded_logShell : Bornology.IsBounded (logShell p c) := by
  obtain ⟨M, hM⟩ := exists_logShell_subset_closedBall p c
  exact (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨M, hM⟩

/-- **`𝓘_I` is compact.** -/
lemma isCompact_logShell : IsCompact (logShell p c) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_logShell p c) (isBounded_logShell p c)

/-- `𝓘_I` is relatively compact (`LocalTheory.logShell_relCompact` at a prime). -/
lemma isCompact_closure_logShell : IsCompact (closure (logShell p c)) := by
  rw [(isClosed_logShell p c).closure_eq]
  exact isCompact_logShell p c

lemma haar_logShell_pos : 0 < haar (.finite p) c (logShell p c) :=
  lt_of_lt_of_le ((isOpen_order p c).measure_pos _ (order_nonempty p c))
    (measure_mono (order_subset_logShell p c))

/-- **At an odd prime unramified in every factor, `𝓘_I = R_I`** (IUT I, Definition 5.4.5). -/
theorem logShell_eq_order_of_unramified (hodd : Odd (p : ℕ))
    (hunr : ∀ j w, c j = Place.finite w → ramIdx K w = 1) : logShell p c = order p c := by
  refine Set.Subset.antisymm ?_ (order_subset_logShell p c)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, rfl⟩
  have : ∀ j, ∃ y : completionAt K (finPart K (c j)), ‖y‖ ≤ 1 ∧ factorMk p (c j) y = a j := by
    intro j
    have hmem : ((a j : Factor K p (c j))) ∈ factorMk p (c j) '' Metric.closedBall 0 1 := by
      rw [← factorLogShell_eq_of_unramified p (c j) hodd (hunr j)]
      exact (a j).2
    obtain ⟨y, hy, hy'⟩ := hmem
    exact ⟨y, by simpa using hy, hy'⟩
  choose y hy hy' using this
  have : (PiTensorProduct.tprod ℚ_[p] fun j => (a j : Factor K p (c j))) =
      tprodIntegral p c fun j => ⟨y j, hy j⟩ := by
    unfold tprodIntegral
    exact congrArg _ (funext fun j => (hy' j).symm)
  change PiTensorProduct.tprod ℚ_[p] (fun j => (a j : Factor K p (c j))) ∈ order p c
  rw [this]
  exact tprodIntegral_mem p c _

/-- **The indeterminacy automorphisms preserve `𝓘_I`** (IUT IV, Proposition 1.2;
`LocalTheory.indAut_logShell` at a prime). -/
theorem mapAlgHom_image_logShell_subset
    (σ : ∀ j, Factor K p (c j) ≃ₐ[ℚ_[p]] Factor K p (c j)) :
    mapAlgHom (.finite p) c σ '' logShell p c ⊆ logShell p c :=
  mapAlgHom_image_span_subset p σ (fun j => factorLogShell p (c j))
    fun j => algEquiv_image_factorLogShell_subset p (c j) (σ j)

theorem indAut_logShell : ∀ φ ∈ indAut (.finite p) c, φ '' logShell p c ⊆ logShell p c := by
  rintro _ ⟨σ, rfl⟩
  exact mapAlgHom_image_logShell_subset p c σ

/-- **`LocalTheory.thetaShell_admissible`** at a prime. -/
theorem thetaShell_admissible :
    (⋃ φ ∈ indAut (.finite p) c, φ '' logShell p c) ∈ admissible (.finite p) c :=
  iUnion_indAut_admissible (.finite p) c (isCompact_logShell p c) (haar_logShell_pos p c)

end Packet

end LocalConstruct

end Iut
