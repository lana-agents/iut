/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.Packet

/-!
# The order `R_I = ⊗_{ℤ_p} 𝓞_{c j}` of a nonarchimedean tensor packet (taxis #4, #278)

At a prime `p`, the **order** `R_I` of the packet `⊗_j K_{c j}` is the `ℤ_p`-span of the
elementary tensors `⊗_j a_j` with every `a_j` in the ring of integers `𝓞_{c j}`
(`‖a_j‖ ≤ 1`), i.e. the image of `⊗_{ℤ_p} 𝓞_{c j}` (`order`). It is a subring, open, closed,
and relatively compact. Its normalization `(R_I)^∼` — the integral structure of the packet
in the sense of `LocalTheory.integral` — is constructed in `MaximalOrder.lean` as the
integral closure of `ℤ_p` in the packet; `R_I` is the tool for its openness and for the
inclusions of the factors.

The key analytic input at a prime is the relative compactness of the ring of integers of
a completion in its `ℚ_p`-coordinates (`exists_isCompact_closedBall_subset`), proved from
the finite-dimensionality of `K_w` over `ℚ_p`: the `ℤ_p`-span of a `ℚ`-basis of `K` is a
compact open subgroup of `K_w`, hence contains `p^r·𝓞_w`.

## Remark

`R_I` is the image of `⊗_{ℤ_p} 𝓞_{c j}`, not its normalization `(R_I)^∼` (the product of
the rings of integers of the field factors of the packet, which is the ring of integers of
the packet). The two coincide when at most one factor is ramified, and differ in general
by a bounded amount controlled by the different (this is the content of IUT IV,
Proposition 1.4(iii)). Least hull regions need not exist for `R_I`, which is why the
interface is instantiated with `(R_I)^∼` (see `MaximalOrder.lean`).
-/

namespace Iut

namespace LocalConstruct

open NumberField IsDedekindDomain
open scoped TensorProduct Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K]

/-! ### Local degrees are positive -/

/-- Ramification indices are positive. -/
lemma ramIdx_pos (w : FinitePlace K) : 0 < ramIdx K w :=
  Ideal.ramificationIdx_pos _ _

/-- Residue degrees are positive. -/
lemma inertDeg_pos (w : FinitePlace K) : 0 < inertDeg K w :=
  Ideal.inertiaDeg_pos _ _

/-- Local degrees are positive. -/
lemma localDeg_pos (w : FinitePlace K) : 0 < localDeg K w :=
  Nat.mul_pos (ramIdx_pos w) (inertDeg_pos w)

/-- `0 ≤ ord_p x` iff `‖x‖ ≤ 1`, for `x ≠ 0`. -/
lemma norm_le_one_of_ordp_nonneg {w : FinitePlace K} {x : completionAt K w}
    (h : 0 ≤ ordp K w x) : ‖x‖ ≤ 1 := by
  have hp : (1 : ℝ) < residueChar w := by exact_mod_cast (residueChar_prime w).one_lt
  have hlog : 0 < Real.log (residueChar w) := Real.log_pos hp
  have hn : (0 : ℝ) < localDeg K w := by exact_mod_cast localDeg_pos w
  unfold ordp at h
  have h' : 0 ≤ -Real.log ‖x‖ := by
    have := mul_nonneg h (mul_pos hn hlog).le
    rwa [div_mul_cancel₀ _ (mul_pos hn hlog).ne'] at this
  exact (Real.log_nonpos_iff (norm_nonneg x)).mp (by linarith)

/-! ### Relative compactness of the ring of integers of a completion -/

section Compact

variable {p : ℕ} [Fact p.Prime] {w : FinitePlace K} (hw : residueChar w = p)
include hw

/-- **The ring of integers `𝓞_w` of a completion is relatively compact in the
`ℚ_p`-coordinates**: it is contained in a compact subset of `K_w`. -/
theorem exists_isCompact_closedBall_subset :
    ∃ C : Set (completionAt K w), IsCompact C ∧ Metric.closedBall (0 : completionAt K w) 1 ⊆ C := by
  letI := padicAlgebra hw
  haveI : ContinuousSMul ℚ_[p] (completionAt K w) :=
    continuousSMul_of_algebraMap ℚ_[p] _ (continuous_padicEmb hw)
  haveI := finite_padicAlgebra hw
  haveI : IsModuleTopology ℚ_[p] (completionAt K w) := isModuleTopologyOfFiniteDimensional
  let b := Module.finBasis ℚ K
  let φ : (Fin (Module.finrank ℚ K) → ℚ_[p]) →ₗ[ℚ_[p]] completionAt K w :=
    Fintype.linearCombination ℚ_[p] fun i => ((b i : K) : completionAt K w)
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact span_range_finBasis_eq_top hw
  set B : Set (Fin (Module.finrank ℚ K) → ℚ_[p]) := Set.pi Set.univ fun _ => Metric.closedBall 0 1
    with hB
  have hBopen : IsOpen B :=
    isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBcompact : IsCompact B := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hΛopen : IsOpen (φ '' B) := IsModuleTopology.isOpenMap_of_surjective hφ _ hBopen
  have hΛcompact : IsCompact (φ '' B) :=
    hBcompact.image (IsModuleTopology.continuous_of_linearMap φ)
  have h0 : φ '' B ∈ nhds (0 : completionAt K w) :=
    hΛopen.mem_nhds ⟨0, fun _ _ => by simp, by simp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h0
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_prime_lt_one hw)
  have hp0 : ((p : K) : completionAt K w) ≠ 0 := by
    have : (p : K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact (map_ne_zero_iff _ (FinitePlace.embedding w.maximalIdeal).injective).mpr this
  refine ⟨(fun y => (((p : K) : completionAt K w) ^ r)⁻¹ * y) '' (φ '' B),
    hΛcompact.image (by fun_prop), fun x hx => ?_⟩
  refine ⟨((p : K) : completionAt K w) ^ r * x, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow]
    calc ‖((p : K) : completionAt K w)‖ ^ r * ‖x‖
        ≤ ‖((p : K) : completionAt K w)‖ ^ r * 1 :=
          mul_le_mul_of_nonneg_left (by simpa using hx) (by positivity)
      _ < ε := by simpa using hr
  · dsimp only
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]

end Compact

/-! ### Coordinates of integral elements of a factor are bounded -/

section FactorBound

variable (p : Nat.Primes) (v : Place K)

/-- The quotient map from the completion to the factor, as a `ℚ_p`-linear map (for
`v ∣ p`, with the `ℚ_p`-structure of the completion). -/
noncomputable def factorMkₗ (h : IsOver K p v) :
    letI := padicAlgebra h.residueChar_finPart
    completionAt K (finPart K v) →ₗ[ℚ_[p]] Factor K p v :=
  letI := padicAlgebra h.residueChar_finPart
  { toFun := factorMk p v
    map_add' := map_add _
    map_smul' := fun c x => by
      simp only [RingHom.id_apply]
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, algebraMap_factor_apply_of_isOver p v h]
      rfl }

/-- **The coordinates of integral elements of a factor are bounded**, in the basis
`Module.finBasis ℚ_p (Factor K p v)`. -/
theorem exists_factor_coord_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ a : completionAt K (finPart K v), ‖a‖ ≤ 1 →
      ∀ k, ‖(Module.finBasis ℚ_[p] (Factor K p v)).repr (factorMk p v a) k‖ ≤ C := by
  by_cases h : IsOver K p v
  · letI := padicAlgebra h.residueChar_finPart
    haveI : ContinuousSMul ℚ_[p] (completionAt K (finPart K v)) :=
      continuousSMul_of_algebraMap ℚ_[p] _ (continuous_padicEmb h.residueChar_finPart)
    haveI := finite_padicAlgebra h.residueChar_finPart
    obtain ⟨C, hC, hsub⟩ := exists_isCompact_closedBall_subset h.residueChar_finPart
    let g : completionAt K (finPart K v) →ₗ[ℚ_[p]]
        (Fin (Module.finrank ℚ_[p] (Factor K p v)) → ℚ_[p]) :=
      (Module.finBasis ℚ_[p] (Factor K p v)).equivFun.toLinearMap ∘ₗ factorMkₗ p v h
    have hg : Continuous g := LinearMap.continuous_of_finiteDimensional g
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hg.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun a ha k => ?_⟩
    have hga : ‖g a‖ ≤ M := hM a (hsub (by simpa using ha))
    calc ‖(Module.finBasis ℚ_[p] (Factor K p v)).repr (factorMk p v a) k‖
        = ‖g a k‖ := by
          simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_apply]
          rfl
      _ ≤ ‖g a‖ := norm_le_pi_norm _ _
      _ ≤ max M 0 := hga.trans (le_max_left _ _)
  · refine ⟨0, le_rfl, fun a _ k => ?_⟩
    haveI := subsingleton_factor p v h
    have : Module.finrank ℚ_[p] (Factor K p v) = 0 := Module.finrank_zero_of_subsingleton
    exact absurd k.2 (by omega)

end FactorBound

/-! ### The nonarchimedean integral structure -/

section Integral

variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)

/-- The integral tuples: families of elements of norm at most `1` of the completions. -/
abbrev IntegralTuple : Type u := ∀ j, {x : completionAt K (finPart K (c j)) // ‖x‖ ≤ 1}

/-- The elementary tensor of an integral tuple. -/
noncomputable def tprodIntegral (a : IntegralTuple c) : Tensor K (.finite p) c :=
  PiTensorProduct.tprod ℚ_[p] fun j => factorMk p (c j) (a j).1

/-- The elementary tensors of integral tuples. -/
def integralSet : Set (Tensor K (.finite p) c) := Set.range (tprodIntegral p c)

/-- The `ℤ_p`-algebra structure of a nonarchimedean packet (restriction of scalars along
`ℤ_p → ℚ_p`; the scalar action is `r • x = (r : ℚ_p) • x` definitionally). -/
noncomputable instance instAlgebraPadicIntTensor : Algebra ℤ_[p] (Tensor K (.finite p) c) where
  smul r x := (r : ℚ_[p]) • x
  algebraMap := (algebraMap ℚ_[p] (Tensor K (.finite p) c)).comp (algebraMap ℤ_[p] ℚ_[p])
  commutes' r x := Algebra.commutes (r : ℚ_[p]) x
  smul_def' r x := Algebra.smul_def (r : ℚ_[p]) x

lemma algebraMap_padicInt_apply (r : ℤ_[p]) :
    algebraMap ℤ_[p] (Tensor K (.finite p) c) r = algebraMap ℚ_[p] _ (r : ℚ_[p]) := rfl

lemma padicInt_smul_def (r : ℤ_[p]) (x : Tensor K (.finite p) c) :
    r • x = (r : ℚ_[p]) • x := rfl

instance : IsScalarTower ℤ_[p] ℚ_[p] (Tensor K (.finite p) c) :=
  ⟨fun r s x => by
    change ((r : ℚ_[p]) * s) • x = (r : ℚ_[p]) • s • x
    exact mul_smul _ _ _⟩

/-- **The order `R_I`** of a nonarchimedean packet: the `ℤ_p`-span of the elementary tensors
of integral tuples, i.e. the image of `⊗_{ℤ_p} 𝓞_{c j}`. -/
noncomputable def orderSubmodule : Submodule ℤ_[p] (Tensor K (.finite p) c) :=
  Submodule.span ℤ_[p] (integralSet p c)

/-- The order `R_I` as a set. -/
noncomputable def order : Set (Tensor K (.finite p) c) := orderSubmodule p c

lemma mem_order {x : Tensor K (.finite p) c} : x ∈ order p c ↔ x ∈ orderSubmodule p c :=
  Iff.rfl

lemma integralSet_subset_order : integralSet p c ⊆ order p c := Submodule.subset_span

lemma tprodIntegral_mem (a : IntegralTuple c) : tprodIntegral p c a ∈ order p c :=
  integralSet_subset_order p c ⟨a, rfl⟩

/-- `1 ∈ R_I`. -/
lemma one_mem_order : (1 : Tensor K (.finite p) c) ∈ order p c := by
  have : (1 : Tensor K (.finite p) c) = tprodIntegral p c fun _ => ⟨1, by simp⟩ := by
    rw [PiTensorProduct.one_def]
    unfold tprodIntegral
    refine congrArg (PiTensorProduct.tprod ℚ_[p]) ?_
    funext j
    exact (map_one _).symm
  rw [this]
  exact tprodIntegral_mem p c _

lemma tprodIntegral_mul (a b : IntegralTuple c) :
    tprodIntegral p c a * tprodIntegral p c b =
      tprodIntegral p c fun j => ⟨(a j).1 * (b j).1, by
        rw [norm_mul]; exact mul_le_one₀ (a j).2 (norm_nonneg _) (b j).2⟩ := by
  unfold tprodIntegral
  rw [PiTensorProduct.tprod_mul_tprod]
  refine congrArg (PiTensorProduct.tprod ℚ_[p]) ?_
  funext j
  exact (map_mul (factorMk p (c j)) _ _).symm

/-- `R_I` is closed under multiplication. -/
lemma mul_mem_order {x y : Tensor K (.finite p) c} (hx : x ∈ order p c)
    (hy : y ∈ order p c) : x * y ∈ order p c := by
  rw [mem_order] at hx hy ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [tprodIntegral_mul]
      exact tprodIntegral_mem p c _
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul r y _ hy =>
      change tprodIntegral p c a * ((r : ℚ_[p]) • y) ∈ _
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul r x _ hx =>
    change ((r : ℚ_[p]) • x) * y ∈ _
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r hx

/-- The inclusion of an integral element of a factor lies in `R_I`. -/
lemma incl_mem_order (j : ι) (w : FinitePlace K) (h : c j = Place.finite w)
    (x : completionAt K w) (hx : ‖x‖ ≤ 1) : incl p c j w h x ∈ order p c := by
  classical
  set x' := completionCongr (eq_finPart h) x with hx'
  have hx'norm : ‖x'‖ ≤ 1 := by
    rw [hx', norm_completionCongr]
    exact hx
  let a : IntegralTuple c := fun i =>
    ⟨Function.update (fun i => (1 : completionAt K (finPart K (c i)))) j x' i, by
      by_cases hij : i = j
      · subst hij
        rw [Function.update_self]
        exact hx'norm
      · rw [Function.update_of_ne hij]
        simp⟩
  have : incl p c j w h x = tprodIntegral p c a := by
    rw [incl_apply]
    unfold inclFactor tprodIntegral
    rw [PiTensorProduct.singleAlgHom_apply]
    congr 1
    funext i
    by_cases hij : i = j
    · subst hij
      simp [a, MonoidHom.mulSingle_apply, hx']
    · simp [a, MonoidHom.mulSingle_apply, hij]
  rw [this]
  exact tprodIntegral_mem p c a

/-- **Scaling by an integral element of a factor preserves `R_I`.** -/
lemma smul_order_subset (j : ι) (w : FinitePlace K) (h : c j = Place.finite w)
    (x : completionAt K w) (hx : ‖x‖ ≤ 1) : incl p c j w h x • order p c ⊆ order p c := by
  rintro _ ⟨y, hy, rfl⟩
  exact mul_mem_order p c (incl_mem_order p c j w h x hx) hy

/-- `smul_order_subset` with the hypothesis `0 ≤ ord_p x`. -/
lemma smul_order_subset_of_ordp (j : ι) (w : FinitePlace K) (h : c j = Place.finite w)
    (x : completionAt K w) (_hx : x ≠ 0) (hord : 0 ≤ ordp K w x) :
    incl p c j w h x • order p c ⊆ order p c :=
  smul_order_subset p c j w h x (norm_le_one_of_ordp_nonneg hord)

/-! #### Boundedness -/

/-- The elementary tensors of integral tuples are bounded. -/
lemma exists_norm_tprodIntegral_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : IntegralTuple c, ‖tprodIntegral p c a‖ ≤ M := by
  choose C hC0 hC using fun j => exists_factor_coord_bound p (c j)
  refine ⟨∏ j, C j, Finset.prod_nonneg fun j _ => hC0 j, fun a => ?_⟩
  rw [norm_def, pi_norm_le_iff_of_nonneg (Finset.prod_nonneg fun j _ => hC0 j)]
  intro k
  rw [Module.Basis.equivFun_apply]
  unfold packetBasis tprodIntegral
  rw [Basis.piTensorProduct_repr_tprod_apply, norm_prod]
  exact Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => hC j _ (a j).2 _

/-- **`R_I` is bounded.** -/
lemma exists_order_subset_closedBall :
    ∃ M : ℝ, order p c ⊆ Metric.closedBall 0 M := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_tprodIntegral_le p c
  refine ⟨M, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [mem_order] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact hM a
  | zero => simpa using hM0
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | smul r x _ hx =>
    change ‖(r : ℚ_[p]) • x‖ ≤ M
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one r)).trans hx

lemma isBounded_order : Bornology.IsBounded (order p c) := by
  obtain ⟨M, hM⟩ := exists_order_subset_closedBall p c
  exact (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨M, hM⟩

/-- **`R_I` is relatively compact.** -/
lemma isCompact_closure_order : IsCompact (closure (order p c)) :=
  (isBounded_order p c).isCompact_closure

/-! #### Openness -/

/-- Rescaling the chosen basis of a factor into the ring of integers. -/
lemma exists_pow_smul_finBasis_mem (v : Place K) : ∃ m : ℕ,
    ∀ k, ∃ y : completionAt K (finPart K v), ‖y‖ ≤ 1 ∧
      factorMk p v y = ((p : ℕ) : ℚ_[p]) ^ m • Module.finBasis ℚ_[p] (Factor K p v) k := by
  by_cases h : IsOver K p v
  · have hw := h.residueChar_finPart
    have hp1 := norm_natCast_prime_lt_one hw
    have hp0 : (0 : ℝ) ≤ ‖(((p : ℕ) : K) : completionAt K (finPart K v))‖ := norm_nonneg _
    choose y hy using fun k => factorMk_surjective p v (Module.finBasis ℚ_[p] (Factor K p v) k)
    have hm : ∀ k, ∃ m : ℕ, ‖(((p : ℕ) : K) : completionAt K (finPart K v))‖ ^ m * ‖y k‖ ≤ 1 := by
      intro k
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖y k‖ + 1) by positivity) hp1
      refine ⟨m, ?_⟩
      calc ‖(((p : ℕ) : K) : completionAt K (finPart K v))‖ ^ m * ‖y k‖
          ≤ 1 / (‖y k‖ + 1) * ‖y k‖ := mul_le_mul_of_nonneg_right hm.le (norm_nonneg _)
        _ ≤ 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
          linarith
    choose m hm using hm
    refine ⟨Finset.univ.sup m, fun k => ⟨(((p : ℕ) : K) : completionAt K (finPart K v)) ^
      Finset.univ.sup m * y k, ?_, ?_⟩⟩
    · rw [norm_mul, norm_pow]
      calc ‖(((p : ℕ) : K) : completionAt K (finPart K v))‖ ^ Finset.univ.sup m * ‖y k‖
          ≤ ‖(((p : ℕ) : K) : completionAt K (finPart K v))‖ ^ m k * ‖y k‖ :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_of_le_one hp0 hp1.le (Finset.le_sup (Finset.mem_univ k))) (norm_nonneg _)
        _ ≤ 1 := hm k
    · have hpe : padicEmb hw ((p : ℕ) : ℚ_[p]) =
          (((p : ℕ) : K) : completionAt K (finPart K v)) := by
        rw [← Rat.cast_natCast, padicEmb_ratCast, Rat.cast_natCast]
      rw [Algebra.smul_def, algebraMap_factor_apply_of_isOver p v h, map_pow, hpe, ← hy k,
        ← map_mul]
  · refine ⟨0, fun k => ?_⟩
    haveI := subsingleton_factor p v h
    have : Module.finrank ℚ_[p] (Factor K p v) = 0 := Module.finrank_zero_of_subsingleton
    exact absurd k.2 (by omega)

/-- A power of `p` times each vector of the basis of elementary tensors lies in `R_I`. -/
lemma exists_pow_smul_packetBasis_mem : ∃ M : ℕ, ∀ k : PacketIndex (.finite p) c,
    ((p : ℕ) : ℚ_[p]) ^ M • packetBasis (.finite p) c k ∈ order p c := by
  choose m hm using fun j => exists_pow_smul_finBasis_mem p (c j)
  refine ⟨∑ j, m j, fun k => ?_⟩
  choose y hy hy' using fun j => hm j (k j)
  have : ((p : ℕ) : ℚ_[p]) ^ (∑ j, m j) • packetBasis (.finite p) c k =
      tprodIntegral p c fun j => ⟨y j, hy j⟩ := by
    unfold packetBasis tprodIntegral
    rw [Basis.piTensorProduct_apply, ← Finset.prod_pow_eq_pow_sum, ← MultilinearMap.map_smul_univ]
    congr 1
    funext j
    exact (hy' j).symm
  rw [this]
  exact tprodIntegral_mem p c _

/-- **`R_I` contains a ball around `0`.** -/
lemma exists_closedBall_subset_order :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : Tensor K (.finite p) c) r ⊆ order p c := by
  obtain ⟨M, hM⟩ := exists_pow_smul_packetBasis_mem p c
  have hp : (0 : ℝ) < ‖((p : ℕ) : ℚ_[p]) ^ M‖ := by
    rw [norm_pow, Padic.norm_p]
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : (p : ℕ).Prime).one_lt
    positivity
  refine ⟨_, hp, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, norm_def, pi_norm_le_iff_of_nonneg hp.le] at hx
  have hpM : ((p : ℕ) : ℚ_[p]) ^ M ≠ 0 := by
    have : ((p : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : (p : ℕ).Prime).ne_zero
    exact pow_ne_zero _ this
  rw [← (packetBasis (.finite p) c).sum_equivFun x, mem_order]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : ‖(packetBasis (.finite p) c).equivFun x k / ((p : ℕ) : ℚ_[p]) ^ M‖ ≤ 1 := by
    rw [norm_div, div_le_one hp]
    exact hx k
  let r : ℤ_[p] := ⟨_, hk⟩
  have : (packetBasis (.finite p) c).equivFun x k • packetBasis (.finite p) c k =
      r • (((p : ℕ) : ℚ_[p]) ^ M • packetBasis (.finite p) c k) := by
    change _ = ((packetBasis (.finite p) c).equivFun x k / ((p : ℕ) : ℚ_[p]) ^ M) •
      (((p : ℕ) : ℚ_[p]) ^ M • packetBasis (.finite p) c k)
    rw [smul_smul, div_mul_cancel₀ _ hpM]
  rw [this]
  exact Submodule.smul_mem _ r (hM k)

/-- The order as an additive subgroup. -/
noncomputable def orderAddSubgroup : AddSubgroup (Tensor K (.finite p) c) :=
  (orderSubmodule p c).toAddSubgroup

lemma coe_orderAddSubgroup : (orderAddSubgroup p c : Set (Tensor K (.finite p) c)) =
    order p c := rfl

/-- **`R_I` is open.** -/
lemma isOpen_order : IsOpen (order p c) := by
  obtain ⟨r, hr, hsub⟩ := exists_closedBall_subset_order p c
  rw [← coe_orderAddSubgroup]
  exact AddSubgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 hr) hsub)

/-- **`R_I` is closed.** -/
lemma isClosed_order : IsClosed (order p c) := by
  rw [← coe_orderAddSubgroup]
  exact AddSubgroup.isClosed_of_isOpen _ (isOpen_order p c)

/-- **`R_I` is compact.** -/
lemma isCompact_order : IsCompact (order p c) :=
  (isClosed_order p c).closure_eq ▸ isCompact_closure_order p c

lemma order_nonempty : (order p c).Nonempty := ⟨1, one_mem_order p c⟩

/-! #### The junk packets -/

/-- A packet at `p` with a place not over `p` is the zero ring. -/
lemma subsingleton_tensor_of_not_isOver (j : ι) (h : ¬ IsOver K p (c j)) :
    Subsingleton (Tensor K (.finite p) c) := by
  classical
  haveI := subsingleton_factor p (c j) h
  refine ⟨fun x y => ?_⟩
  have hzero : ∀ z : Tensor K (.finite p) c, z = 0 := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      have hf : f = Function.update f j 0 := by
        funext i
        by_cases hij : i = j
        · subst hij
          rw [Function.update_self]
          exact Subsingleton.elim _ _
        · rw [Function.update_of_ne hij]
      rw [hf, MultilinearMap.map_update_zero, smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [hzero x, hzero y]

end Integral

end LocalConstruct

end Iut
