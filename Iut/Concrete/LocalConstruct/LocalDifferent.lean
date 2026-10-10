/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.Packet
import Iut.Concrete.LocalConstruct.Arithmetic
import Iut.Concrete.ThetaLocalConstruct.Ordp
import Iut.Concrete.LocalConstruct.MaximalOrder

/-!
# The global different inside the local different (IUT IV, Propositions 1.1 and 1.3)

The local–global half of the different bound of IUT IV, Proposition 1.1: for a finite place
`w` of `K` of residue characteristic `p` and an element `D` of the global different
`𝔡_{K/ℚ} = differentIdeal ℤ (𝓞 K)`, multiplication by `D` maps the trace-dual
`{y ∈ K_w | Tr_{K_w/ℚ_p}(y·𝓞_{K_w}) ⊆ ℤ_p}` of `𝓞_{K_w}` into `𝓞_{K_w}`
(`norm_mul_le_one_of_mem_differentIdeal`); and some nonzero `D ∈ 𝔡_{K/ℚ}` has
`ord_p(D) = d_w = ord_𝔭(𝔡_{K/ℚ})/e_w` exactly (`exists_different_elt`; the local different
is the completion of the global one, IUT IV, Proposition 1.3). Together:
`exists_local_different_elt`.

The proof of the first statement runs through `A = ℚ_p ⊗_ℚ K`: the multiplication map
`Ψ : A → K_w` is surjective (`span_range_finBasis_eq_top`), `A` is reduced Artinian (base change
of the étale algebra `K/ℚ`), hence semisimple, so `ker Ψ` has a complement and there is
`e ∈ A` with `Ψ e = 1`, `e·ker Ψ = 0`; then `Tr_{A/ℚ_p}(e·a) = Tr_{K_w/ℚ_p}(Ψ a)`
(`trace_mul_eq_of_surjective`). Expanding `e·ỹ` (with `Ψ ỹ = y`) in the base change of the
trace-dual basis `b^∨` of an integral basis `b` of `𝓞_K` gives
`y = Σ_k Tr_{K_w/ℚ_p}(y·b_k)·b^∨_k` with coefficients in `ℤ_p`, and `D·b^∨_k ∈ 𝓞_K`
since `b^∨_k ∈ 𝓞_K^∨ = 𝔡_{K/ℚ}^{-1}`.
-/

namespace Iut

namespace LocalConstruct

open NumberField IsDedekindDomain WithZero
open scoped TensorProduct

section Generic

variable {F A L : Type*} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
  [CommRing L] [Algebra F L] [Module.Finite F L]

omit [Module.Finite F A] in
/-- In a semisimple commutative ring every ideal `I` is annihilated by some `e` with
`1 - e ∈ I`. -/
theorem exists_mul_eq_zero_of_isSemisimpleRing [IsSemisimpleRing A] (I : Ideal A) :
    ∃ e : A, 1 - e ∈ I ∧ ∀ x ∈ I, e * x = 0 := by
  obtain ⟨J, hJ⟩ := exists_isCompl I
  have h1 : (1 : A) ∈ I ⊔ J := by rw [hJ.sup_eq_top]; trivial
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp h1
  refine ⟨j, by rw [← hij, add_sub_cancel_right]; exact hi, fun x hx => ?_⟩
  have hI : j * x ∈ I := I.mul_mem_left j hx
  have hJ' : j * x ∈ J := by rw [mul_comm]; exact J.smul_mem x hj
  exact (Submodule.disjoint_def.mp hJ.disjoint) _ hI hJ'

/-- If `Ψ : A → L` is surjective and `e` satisfies `Ψ e = 1`, `e·ker Ψ = 0`, then
`Tr_{A/F}(e·a) = Tr_{L/F}(Ψ a)`. -/
theorem trace_mul_eq_of_surjective (Ψ : A →ₐ[F] L) (hΨ : Function.Surjective Ψ) (e : A)
    (he1 : Ψ e = 1) (he : ∀ x, Ψ x = 0 → e * x = 0) (a : A) :
    Algebra.trace F A (e * a) = Algebra.trace F L (Ψ a) := by
  obtain ⟨σ, hσ⟩ := (Ψ.toLinearMap).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hΨ)
  have hσ' : ∀ z, Ψ (σ z) = z := fun z => LinearMap.congr_fun hσ z
  let s : L →ₗ[F] A := Algebra.lmul F A e ∘ₗ σ
  have hs : ∀ x, s (Ψ x) = e * x := by
    intro x
    have h0 := he (σ (Ψ x) - x) (by rw [map_sub, hσ', sub_self])
    rw [mul_sub, sub_eq_zero] at h0
    exact h0
  have h1 : Algebra.lmul F A (e * a) = s ∘ₗ (Ψ.toLinearMap ∘ₗ Algebra.lmul F A a) := by
    ext x
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.coe_lmul_eq_mul,
      LinearMap.mul_apply', hs]
    ring
  have h2 : (Ψ.toLinearMap ∘ₗ Algebra.lmul F A a) ∘ₗ s = Algebra.lmul F L (Ψ a) := by
    ext z
    simp [s, he1, hσ']
  rw [Algebra.trace_apply, Algebra.trace_apply, h1, LinearMap.trace_comp_comm', h2]

end Generic

section BaseChange

variable {K : Type*} [Field K] [NumberField K] (F : Type*) [Field F] [Algebra ℚ F]

/-- `Tr_{F ⊗ K/F}(1 ⊗ x) = Tr_{K/ℚ}(x)`. -/
lemma trace_one_tmul (x : K) :
    Algebra.trace F (F ⊗[ℚ] K) (1 ⊗ₜ x) = algebraMap ℚ F (Algebra.trace ℚ K x) := by
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange,
    Algebra.trace_apply]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ K)

/-- The trace-dual basis expansion `x = Σ_k Tr(x·b_k)·b^∨_k`. -/
lemma sum_trace_smul_traceDual (x : K) :
    ∑ k, Algebra.trace ℚ K (x * b k) • b.traceDual k = x := by
  conv_rhs => rw [← b.traceDual.sum_repr x]
  simp [Algebra.traceForm_apply]

/-- The trace-dual basis expansion on the base change `F ⊗_ℚ K`. -/
lemma sum_trace_smul_one_tmul (Y : F ⊗[ℚ] K) :
    ∑ k, Algebra.trace F (F ⊗[ℚ] K) (Y * (1 ⊗ₜ b k)) • ((1 : F) ⊗ₜ[ℚ] b.traceDual k) = Y := by
  induction Y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    have h : ∀ k, (r ⊗ₜ[ℚ] x) * (1 ⊗ₜ b k) = r • ((1 : F) ⊗ₜ[ℚ] (x * b k)) := by
      intro k
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
    simp_rw [h, map_smul, trace_one_tmul, smul_eq_mul, mul_smul, algebraMap_smul,
      ← TensorProduct.tmul_smul, ← Finset.smul_sum, ← TensorProduct.tmul_sum,
      sum_trace_smul_traceDual, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add Y₁ Y₂ h₁ h₂ =>
    simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib, h₁, h₂]

end BaseChange

variable {K : Type*} [Field K] [NumberField K]

section Local

variable {p : ℕ} [Fact p.Prime] {w : FinitePlace K} (hw : residueChar w = p)
include hw

/-- `ℚ → ℚ_p → K_w` is the canonical `ℚ`-algebra structure of `K_w`. -/
lemma isScalarTower_padicAlgebra :
    letI := padicAlgebra hw
    IsScalarTower ℚ ℚ_[p] (completionAt K w) := by
  letI := padicAlgebra hw
  exact IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

/-- The map `ℚ_p ⊗_ℚ K → K_w`, `r ⊗ x ↦ r·x`. -/
noncomputable def tensorToCompletion :
    letI := padicAlgebra hw
    ℚ_[p] ⊗[ℚ] K →ₐ[ℚ_[p]] completionAt K w :=
  letI := padicAlgebra hw
  haveI := isScalarTower_padicAlgebra hw
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[p] _) (algebraMap K (completionAt K w)).toRatAlgHom
    (fun _ _ => Commute.all _ _)

lemma tensorToCompletion_one_tmul (x : K) :
    tensorToCompletion hw (1 ⊗ₜ x) = algebraMap K (completionAt K w) x := by
  simp [tensorToCompletion]

/-- `ℚ_p ⊗_ℚ K → K_w` is surjective. -/
lemma tensorToCompletion_surjective : Function.Surjective (tensorToCompletion hw) := by
  letI := padicAlgebra hw
  refine (LinearMap.range_eq_top (f := (tensorToCompletion hw).toLinearMap)).mp ?_
  refine eq_top_iff.mpr ((span_range_finBasis_eq_top hw).symm.le.trans (Submodule.span_le.mpr ?_))
  rintro _ ⟨i, rfl⟩
  exact ⟨1 ⊗ₜ _, tensorToCompletion_one_tmul hw _⟩

/-- `ℤ_p` maps into `𝓞_{K_w}`. -/
lemma norm_padicEmb_le_one {t : ℚ_[p]} (ht : ‖t‖ ≤ 1) : ‖padicEmb hw t‖ ≤ 1 := by
  have hc : Continuous (fun x : ℤ_[p] => (x : ℚ_[p])) := continuous_subtype_val
  have hf : Continuous (fun x : ℤ_[p] => ‖padicEmb hw (x : ℚ_[p])‖) :=
    continuous_norm.comp ((continuous_padicEmb hw).comp hc)
  have hclosed : IsClosed {x : ℤ_[p] | ‖padicEmb hw (x : ℚ_[p])‖ ≤ 1} :=
    isClosed_le hf continuous_const
  have hsub : Set.range (Int.cast : ℤ → ℤ_[p]) ⊆ {x | ‖padicEmb hw (x : ℚ_[p])‖ ≤ 1} := by
    rintro _ ⟨n, rfl⟩
    change ‖padicEmb hw ((n : ℤ_[p]) : ℚ_[p])‖ ≤ 1
    rw [PadicInt.coe_intCast, map_intCast]
    exact IsUltrametricDist.norm_intCast_le_one _ n
  have h := hclosed.closure_subset_iff.mpr hsub
  rw [PadicInt.denseRange_intCast.closure_range] at h
  obtain ⟨x, rfl⟩ : ∃ x : ℤ_[p], (x : ℚ_[p]) = t := ⟨⟨t, ht⟩, rfl⟩
  exact h (Set.mem_univ x)

end Local

lemma algebraMap_completionAt (w : FinitePlace K) (x : K) :
    algebraMap K (completionAt K w) x = ((x : K) : completionAt K w) := rfl

/-- Elements of `𝓞_K` are integral in `K_w`. -/
lemma norm_coe_le_one (w : FinitePlace K) (x : 𝓞 K) :
    ‖algebraMap K (completionAt K w) (x : K)‖ ≤ 1 :=
  FinitePlace.norm_le_one K w.maximalIdeal x


/-- `D·b^∨_k ∈ 𝓞_K` for `D ∈ 𝔡_{K/ℚ}` and the trace-dual `b^∨` of the integral basis. -/
lemma exists_mul_traceDual_eq {D : 𝓞 K} (hD : D ∈ differentIdeal ℤ (𝓞 K))
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    ∃ c : 𝓞 K, (c : K) = (D : K) * (integralBasis K).traceDual k := by
  classical
  have hD' : (D : K) ∈ 1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K) := by
    rw [← coeSubmodule_differentIdeal (A := ℤ) (K := ℚ) (B := 𝓞 K) (L := K)]
    exact Submodule.mem_map_of_mem hD
  have hb : (1 : Submodule (𝓞 K) K).restrictScalars ℤ =
      Submodule.span ℤ (Set.range (integralBasis K)) := by
    ext x
    rw [Submodule.restrictScalars_mem, Submodule.mem_one, mem_span_integralBasis]
    rfl
  have hk : (integralBasis K).traceDual k ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K) := by
    have h := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 K) K) (integralBasis K) hb
    have : (integralBasis K).traceDual k ∈
        (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K)).restrictScalars ℤ := by
      rw [h]; exact Submodule.subset_span ⟨k, rfl⟩
    exact this
  exact Submodule.mem_one.mp ((Submodule.mem_div_iff_forall_mul_mem.mp hD') _ hk)

section Local

variable {p : ℕ} [Fact p.Prime] {w : FinitePlace K} (hw : residueChar w = p)
include hw

/-- **The global different lies in the local different** (IUT IV, Proposition 1.1, via the
trace-dual basis of `𝓞_K`): if `y ∈ K_w` has `Tr_{K_w/ℚ_p}(y·𝓞_{K_w}) ⊆ ℤ_p`, then
`D·y ∈ 𝓞_{K_w}` for every `D` in the global different `𝔡_{K/ℚ}`. -/
theorem norm_mul_le_one_of_mem_differentIdeal {D : 𝓞 K} (hD : D ∈ differentIdeal ℤ (𝓞 K))
    {y : completionAt K w}
    (hy : letI := padicAlgebra hw
      ∀ z : completionAt K w, ‖z‖ ≤ 1 → ‖Algebra.trace ℚ_[p] (completionAt K w) (y * z)‖ ≤ 1) :
    ‖((D : K) : completionAt K w) * y‖ ≤ 1 := by
  classical
  letI := padicAlgebra hw
  haveI := finite_padicAlgebra hw
  set Ψ := tensorToCompletion hw
  haveI : Algebra.FormallyUnramified ℚ K := Algebra.FormallyUnramified.of_isSeparable ℚ K
  haveI : IsReduced (ℚ_[p] ⊗[ℚ] K) := Algebra.FormallyUnramified.isReduced_of_field ℚ_[p] _
  haveI : IsArtinianRing (ℚ_[p] ⊗[ℚ] K) := IsArtinianRing.of_finite ℚ_[p] _
  haveI : IsSemisimpleRing (ℚ_[p] ⊗[ℚ] K) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  obtain ⟨e, he1, he⟩ := exists_mul_eq_zero_of_isSemisimpleRing (RingHom.ker Ψ)
  have hΨe : Ψ e = 1 := by
    have h := RingHom.mem_ker.mp he1
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h.symm
  obtain ⟨Y, rfl⟩ := tensorToCompletion_surjective hw y
  set b := integralBasis K
  have hcoef : ∀ k, Algebra.trace ℚ_[p] _ (e * Y * (1 ⊗ₜ b k)) =
      Algebra.trace ℚ_[p] (completionAt K w) (Ψ Y * algebraMap K (completionAt K w) (b k)) := by
    intro k
    rw [mul_assoc, trace_mul_eq_of_surjective Ψ (tensorToCompletion_surjective hw) e hΨe
      (fun x hx => he x (RingHom.mem_ker.mpr hx)), map_mul, tensorToCompletion_one_tmul]
  have hY : Ψ Y = ∑ k, padicEmb hw (Algebra.trace ℚ_[p] _ (e * Y * (1 ⊗ₜ b k))) *
      algebraMap K (completionAt K w) (b.traceDual k) := by
    have h := congrArg Ψ (sum_trace_smul_one_tmul ℚ_[p] b (e * Y))
    rw [map_mul, hΨe, one_mul] at h
    rw [← h, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [AlgHom.map_smul_of_tower, tensorToCompletion_one_tmul, Algebra.smul_def,
      padicAlgebra_algebraMap]
  rw [hY, Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  obtain ⟨c, hc⟩ := exists_mul_traceDual_eq hD k
  rw [mul_left_comm, norm_mul]
  refine mul_le_one₀ (norm_padicEmb_le_one hw ?_) (norm_nonneg _) ?_
  · rw [hcoef]
    refine hy _ ?_
    rw [integralBasis_apply]
    exact norm_coe_le_one w _
  · rw [← algebraMap_completionAt, ← map_mul, ← hc]
    exact norm_coe_le_one w c

end Local

/-- **An element of the global different of exact local order** (IUT IV, Proposition 1.3):
some nonzero `D ∈ 𝔡_{K/ℚ}` has `ord_p(D) = d_w` in `K_w`. -/
theorem exists_different_elt (w : FinitePlace K) :
    ∃ D ∈ differentIdeal ℤ (𝓞 K), D ≠ 0 ∧
      ordp K w ((D : K) : completionAt K w) = differentExponent K w := by
  classical
  set m := ordDifferent K w with hm
  have hne : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hmult : emultiplicity w.maximalIdeal.asIdeal (differentIdeal ℤ (𝓞 K)) = m := by
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      w.maximalIdeal.irreducible hne, normalize_eq, hm, ordDifferent]
  have hle : differentIdeal ℤ (𝓞 K) ≤ w.maximalIdeal.asIdeal ^ m :=
    Ideal.le_of_dvd (pow_dvd_of_le_emultiplicity hmult.ge)
  have hnle : ¬ differentIdeal ℤ (𝓞 K) ≤ w.maximalIdeal.asIdeal ^ (m + 1) := fun h =>
    not_pow_dvd_of_emultiplicity_lt (by rw [hmult]; exact_mod_cast Nat.lt_succ_self m)
      (Ideal.dvd_iff_le.mpr h)
  obtain ⟨D, hD, hDn⟩ := SetLike.not_le_iff_exists.mp hnle
  have hD0 : D ≠ 0 := by rintro rfl; exact hDn (Submodule.zero_mem _)
  refine ⟨D, hD, hD0, ?_⟩
  have hv1 : w.maximalIdeal.intValuation D ≤ exp (-(m : ℤ)) :=
    (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).mpr (hle hD)
  have hv2 : ¬ w.maximalIdeal.intValuation D ≤ exp (-((m + 1 : ℕ) : ℤ)) := fun h =>
    hDn ((HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).mp h)
  rw [w.maximalIdeal.intValuation_eq_exp_neg_multiplicity hD0, exp_le_exp] at hv1 hv2
  have hmul : multiplicity w.maximalIdeal.asIdeal (Ideal.span {D}) = m := by omega
  have hval : Valued.v ((D : K) : completionAt K w) = exp (-(m : ℤ)) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap,
      w.maximalIdeal.intValuation_eq_exp_neg_multiplicity hD0, hmul]
  rw [ordp_eq_of_valued w _ _ hval, differentExponent]
  push_cast
  ring

/-- **The local different element** (IUT IV, Propositions 1.1 and 1.3): at a finite place `w`
of residue characteristic `p` there is `δ ∈ K_w`, `δ ≠ 0`, with `ord_p δ = d_w` and
`δ·y ∈ 𝓞_{K_w}` whenever `Tr_{K_w/ℚ_p}(y·𝓞_{K_w}) ⊆ ℤ_p`. -/
theorem exists_local_different_elt {p : ℕ} [Fact p.Prime] {w : FinitePlace K}
    (hw : residueChar w = p) :
    ∃ δ : completionAt K w, δ ≠ 0 ∧ ordp K w δ = differentExponent K w ∧
      ∀ y : completionAt K w, (letI := padicAlgebra hw
        ∀ z : completionAt K w, ‖z‖ ≤ 1 →
          ‖Algebra.trace ℚ_[p] (completionAt K w) (y * z)‖ ≤ 1) → ‖δ * y‖ ≤ 1 := by
  obtain ⟨D, hD, hD0, hord⟩ := exists_different_elt w
  refine ⟨((D : K) : completionAt K w), ?_, hord, fun y hy =>
    norm_mul_le_one_of_mem_differentIdeal hw hD hy⟩
  rw [← algebraMap_completionAt, map_ne_zero]
  exact_mod_cast hD0

end LocalConstruct

end Iut
