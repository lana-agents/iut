/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.ResidueField
import PadicLogVolume.TraceDuality

/-!
# The different bounds the index of `R_I` in `(R_I)^∼` (IUT IV, Proposition 1.1)

Let `p` be a prime, `c : ι → Place K` a finite family of places of `K` over `p`, and let
`P = ⊗_j K_{c j}` be the corresponding tensor packet over `ℚ_p`, with its order
`R_I = ⊗_{ℤ_p} 𝓞_{c j}` (`order`) and its maximal order `(R_I)^∼` (`integral`, the integral
closure of `ℤ_p`). This file proves the packet-level half of IUT IV, Proposition 1.1:

> if `δ_j ∈ K_{c j}` multiplies the local inverse different `𝔡_j^{-1}` of `K_{c j}/ℚ_p`
> into `𝓞_{c j}`, then `(∏_j δ_j) · (R_I)^∼ ⊆ R_I`.

The local-different hypothesis is phrased through the trace: `y ∈ 𝔡_j^{-1}` iff
`Tr_{K_{c j}/ℚ_p}(y z) ∈ ℤ_p` for all `z ∈ 𝓞_{c j}`.

## Main results

* `norm_trace_le_one_of_isIntegral`, `trace_mem_padicInt_of_mem_integral`: traces of
  elements integral over `ℤ_p` lie in `ℤ_p` (the integral closure of `ℤ_p` in a finite
  `ℚ_p`-algebra is a full `ℤ_p`-lattice `Λ`, and multiplication by an integral element
  preserves `Λ`, so its trace is computed by a matrix over `ℤ_p`);
* `trace_tprod`: the trace of an elementary tensor is the product of the traces of the
  factors (computed in the basis of elementary tensors);
* `exists_traceDual_basis`: a `ℤ_p`-basis `β_j` of the integral closure in each factor and
  its trace-dual basis `β_j^*`;
* `tprod_mul_mem_order_of_mem_integral`, `prod_incl_mul_mem_order_of_mem_integral`:
  **IUT IV, Proposition 1.1** (packet level): every `x ∈ (R_I)^∼` is
  `x = ∑_l Tr_P(x · ⊗_j β_j(l_j)) · ⊗_j β_j^*(l_j)` with coefficients in `ℤ_p`, and
  `δ_j β_j^*(l_j) ∈ 𝓞_{c j}`, so `(∏_j δ_j) x ∈ R_I`;
* `trace_factorMk`: the translation between the traces of the factor `Factor K p v` and of
  the completion `K_v` (with its `ℚ_p`-structure `padicAlgebra`).
-/

namespace Iut

open PadicLogVolume

namespace LocalConstruct

open NumberField
open scoped TensorProduct

universe u

variable {K : Type u} [Field K] [NumberField K]

/-! ### Factors and completions -/

section Factor

variable (p : Nat.Primes)

lemma IsOver.eq_finite_finPart {v : Place K} (h : IsOver K p v) :
    v = Place.finite (finPart K v) := by
  obtain ⟨w, rfl, -⟩ := h
  rfl

lemma IsOver.residueChar_of_eq {v : Place K} {w : FinitePlace K} (hv : IsOver K p v)
    (h : v = Place.finite w) : residueChar w = p :=
  (isOver_finite_iff p w).mp (h ▸ hv)

variable (v : Place K)

/-- For `v ∣ p`, the quotient map `K_v → Factor K p v` is an isomorphism of `ℚ_p`-algebras
(with the `ℚ_p`-structure `padicAlgebra` of the completion). -/
noncomputable def factorAlgEquiv (h : IsOver K p v) :
    letI := padicAlgebra h.residueChar_finPart
    completionAt K (finPart K v) ≃ₐ[ℚ_[p]] Factor K p v :=
  letI := padicAlgebra h.residueChar_finPart
  AlgEquiv.ofBijective
    { factorMk p v with commutes' := fun r => (algebraMap_factor_apply_of_isOver p v h r).symm }
    ⟨factorMk_injective p v h, factorMk_surjective p v⟩

lemma factorAlgEquiv_apply (h : IsOver K p v) (x : completionAt K (finPart K v)) :
    factorAlgEquiv p v h x = factorMk p v x := rfl

/-- **The trace of a factor is the trace of the completion** `K_v/ℚ_p`. -/
theorem trace_factorMk (h : IsOver K p v) (y : completionAt K (finPart K v)) :
    Algebra.trace ℚ_[p] (Factor K p v) (factorMk p v y) =
      letI := padicAlgebra h.residueChar_finPart
      Algebra.trace ℚ_[p] (completionAt K (finPart K v)) y := by
  letI := padicAlgebra h.residueChar_finPart
  exact Algebra.trace_eq_of_algEquiv (factorAlgEquiv p v h) y

/-- `trace_factorMk` along an identification `v = w` of places. -/
theorem trace_factorMk_completionCongr {w : FinitePlace K} (hw : residueChar w = p)
    (h : v = Place.finite w) (y : completionAt K w) :
    Algebra.trace ℚ_[p] (Factor K p v) (factorMk p v (completionCongr (eq_finPart h) y)) =
      letI := padicAlgebra hw
      Algebra.trace ℚ_[p] (completionAt K w) y := by
  subst h
  exact trace_factorMk p _ ⟨w, rfl, hw⟩ y

end Factor

/-! ### The packet -/

section Packet

variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)

/-- A packet all of whose places lie over `p` is a nonzero ring. -/
lemma nontrivial_tensor (hc : ∀ j, IsOver K p (c j)) : Nontrivial (Tensor K (.finite p) c) := by
  haveI := fun j => nontrivial_factor p (c j) (hc j)
  let k : PacketIndex (.finite p) c := fun j => ⟨0, Module.finrank_pos⟩
  exact ⟨⟨packetBasis (.finite p) c k, 0, (packetBasis (.finite p) c).ne_zero k⟩⟩

/-- An elementary tensor is the product of the inclusions of its factors. -/
lemma tprod_eq_prod_inclFactor (y : ∀ j, Factor K p (c j)) :
    PiTensorProduct.tprod ℚ_[p] y = ∏ j, inclFactor p c j (y j) := by
  classical
  unfold inclFactor
  simp only [PiTensorProduct.singleAlgHom_apply, MonoidHom.mulSingle_apply]
  rw [← PiTensorProduct.tprod_prod, Finset.univ_prod_mulSingle]

/-- **The trace of an elementary tensor of the packet** is the product of the traces of the
factors. -/
theorem trace_tprod (y : ∀ j, Factor K p (c j)) :
    Algebra.trace ℚ_[p] (Tensor K (.finite p) c) (PiTensorProduct.tprod ℚ_[p] y) =
      ∏ j, Algebra.trace ℚ_[p] (Factor K p (c j)) (y j) :=
  PiTensorProduct.trace_tprod _ y

/-- The trace of a product of elementary tensors. -/
theorem trace_tprod_mul_tprod (y z : ∀ j, Factor K p (c j)) :
    Algebra.trace ℚ_[p] (Tensor K (.finite p) c)
        (PiTensorProduct.tprod ℚ_[p] y * PiTensorProduct.tprod ℚ_[p] z) =
      ∏ j, Algebra.trace ℚ_[p] (Factor K p (c j)) (y j * z j) := by
  rw [PiTensorProduct.tprod_mul_tprod, trace_tprod]
  rfl

/-- The `ℤ_p`-structure of the packet is the restriction of its `ℚ_p`-structure. -/
lemma isScalarTower_padicInt_tensor : IsScalarTower ℤ_[p] ℚ_[p] (Tensor K (.finite p) c) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- **Traces of elements of `(R_I)^∼` lie in `ℤ_p`.** -/
theorem trace_mem_padicInt_of_mem_integral {x : Tensor K (.finite p) c}
    (hx : x ∈ integral p c) : ‖Algebra.trace ℚ_[p] (Tensor K (.finite p) c) x‖ ≤ 1 := by
  haveI := finite_integralClosure p c
  exact @norm_trace_le_one_of_isIntegral p (Tensor K (.finite p) c) _ _ _
    (isScalarTower_padicInt_tensor p c) _ _ x hx

/-- **Integral bases and their trace-dual bases of the factors**: for each factor
`F_j = K_{c j}` there are a `ℚ_p`-basis `β_j` consisting of integral elements and its
trace-dual basis `β_j^*` (`Tr(β_j^*(k) β_j(l)) = δ_{kl}`), such that
`Tr(β_j^*(l) z) ∈ ℤ_p` for every `z ∈ 𝓞_{c j}`. -/
theorem exists_traceDual_basis (hc : ∀ j, IsOver K p (c j)) (j : ι) :
    ∃ (n : ℕ) (b b' : Module.Basis (Fin n) ℚ_[p] (Factor K p (c j))),
      (∀ k l, Algebra.trace ℚ_[p] (Factor K p (c j)) (b' k * b l) = if k = l then 1 else 0) ∧
      (∀ l, inclFactor p c j (b l) ∈ integral p c) ∧
      (∀ z : completionAt K (finPart K (c j)), ‖z‖ ≤ 1 → ∀ l,
        ‖Algebra.trace ℚ_[p] (Factor K p (c j)) (b' l * factorMk p (c j) z)‖ ≤ 1) := by
  classical
  haveI := nontrivial_tensor p c hc
  have hw := (hc j).residueChar_finPart
  letI := padicAlgebra hw
  letI : Algebra ℤ_[p] (completionAt K (finPart K (c j))) :=
    ((algebraMap ℚ_[p] (completionAt K (finPart K (c j)))).comp
      (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  haveI : IsScalarTower ℤ_[p] ℚ_[p] (completionAt K (finPart K (c j))) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := finite_padicAlgebra hw
  haveI : Module.Finite ℤ_[p] (integralClosure ℤ_[p] (completionAt K (finPart K (c j)))) := by
    haveI : IsNoetherian ℤ_[p] (integralClosure ℤ_[p] (completionAt K (finPart K (c j)))) :=
      IsIntegralClosure.isNoetherian ℤ_[p] ℚ_[p] (completionAt K (finPart K (c j))) _
    infer_instance
  obtain ⟨n, bL, hbL, hrepr⟩ := exists_basis_isIntegral p (completionAt K (finPart K (c j)))
  have hnd := traceForm_nondegenerate ℚ_[p] (completionAt K (finPart K (c j)))
  set bL' := (Algebra.traceForm ℚ_[p] (completionAt K (finPart K (c j)))).dualBasis hnd bL
  set e := factorAlgEquiv p (c j) (hc j)
  let φ : completionAt K (finPart K (c j)) →ₐ[ℤ_[p]] Tensor K (.finite p) c :=
    { ((inclFactor p c j).comp e.toAlgHom).toRingHom with
      commutes' := fun r => ((inclFactor p c j).comp e.toAlgHom).commutes (r : ℚ_[p]) }
  have hφ : Function.Injective φ := φ.toRingHom.injective
  have htr : ∀ x, Algebra.trace ℚ_[p] (Factor K p (c j)) (e x) =
      Algebra.trace ℚ_[p] (completionAt K (finPart K (c j))) x :=
    Algebra.trace_eq_of_algEquiv e
  have hdual : ∀ k l, Algebra.trace ℚ_[p] (completionAt K (finPart K (c j))) (bL' k * bL l) =
      if k = l then 1 else 0 := by
    intro k l
    rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_dualBasis_left]
    simp only [eq_comm]
  refine ⟨n, bL.map e.toLinearEquiv, bL'.map e.toLinearEquiv, fun k l => ?_, fun l => ?_,
    fun z hz l => ?_⟩
  · rw [Module.Basis.map_apply, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
      AlgEquiv.toLinearEquiv_apply, ← map_mul, htr, hdual]
  · rw [Module.Basis.map_apply]
    exact (isIntegral_algHom_iff φ hφ).mpr (hbL l)
  · have hzi : IsIntegral ℤ_[p] z := by
      rw [← isIntegral_algHom_iff φ hφ]
      have := incl_mem_integral p c j _ (hc j).eq_finite_finPart z hz
      rw [incl_apply, completionCongr_rfl] at this
      exact this
    rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, ← factorAlgEquiv_apply p _ (hc j),
      ← map_mul, htr]
    have : Algebra.trace ℚ_[p] (completionAt K (finPart K (c j))) (bL' l * z) =
        bL.repr z l := by
      conv_lhs => rw [← bL.sum_repr z]
      rw [Finset.mul_sum, map_sum]
      simp_rw [mul_smul_comm, map_smul, hdual, smul_eq_mul, mul_ite, mul_one, mul_zero]
      simp [Finset.sum_ite_eq]
    rw [this]
    exact hrepr z hzi l

/-- **IUT IV, Proposition 1.1** (packet level, factor form): let all places `c j` lie over
`p`, and let `δ_j ∈ K_{c j}` multiply the inverse different into the ring of integers:
`‖δ_j y‖ ≤ 1` whenever `Tr_{K_{c j}/ℚ_p}(y z) ∈ ℤ_p` for all `z ∈ 𝓞_{c j}`. Then
`(⊗_j δ_j) · (R_I)^∼ ⊆ R_I`. -/
theorem tprod_mul_mem_order_of_mem_integral (hc : ∀ j, IsOver K p (c j))
    (δ : ∀ j, completionAt K (finPart K (c j)))
    (hδ : ∀ j (y : completionAt K (finPart K (c j))),
      (∀ z : completionAt K (finPart K (c j)), ‖z‖ ≤ 1 →
        ‖Algebra.trace ℚ_[p] (Factor K p (c j)) (factorMk p (c j) (y * z))‖ ≤ 1) →
      ‖δ j * y‖ ≤ 1)
    {x : Tensor K (.finite p) c} (hx : x ∈ integral p c) :
    PiTensorProduct.tprod ℚ_[p] (fun j => factorMk p (c j) (δ j)) * x ∈ order p c := by
  classical
  choose n b b' hdual hint htr using fun j => exists_traceDual_basis p c hc j
  set T := Basis.piTensorProduct b
  set T' := Basis.piTensorProduct b'
  have hTint : ∀ l, T l ∈ integral p c := by
    intro l
    rw [Basis.piTensorProduct_apply, tprod_eq_prod_inclFactor]
    exact prod_mem (S := integralClosure ℤ_[p] (Tensor K (.finite p) c))
      fun j _ => hint j (l j)
  have hcoef : ∀ (y : Tensor K (.finite p) c) l,
      T'.repr y l = Algebra.trace ℚ_[p] (Tensor K (.finite p) c) (y * T l) := by
    intro y l
    have : T'.coord l = (Algebra.trace ℚ_[p] (Tensor K (.finite p) c)) ∘ₗ
        (LinearMap.mulRight ℚ_[p] (T l)) := by
      refine T'.ext fun m => ?_
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.comp_apply,
        LinearMap.mulRight_apply, Basis.piTensorProduct_apply, Basis.piTensorProduct_apply,
        trace_tprod_mul_tprod, Finset.prod_congr rfl fun j _ => hdual j (m j) (l j)]
      rw [Finsupp.single_apply]
      split_ifs with hml
      · subst hml
        simp
      · obtain ⟨j, hj⟩ : ∃ j, m j ≠ l j := Function.ne_iff.mp hml
        exact (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)).symm
    exact LinearMap.congr_fun this y
  have hδb : ∀ j l, ∃ a : completionAt K (finPart K (c j)), ‖a‖ ≤ 1 ∧
      factorMk p (c j) a = factorMk p (c j) (δ j) * b' j l := by
    intro j l
    obtain ⟨y, hy⟩ := factorMk_surjective p (c j) (b' j l)
    refine ⟨δ j * y, hδ j y fun z hz => ?_, by rw [map_mul, hy]⟩
    rw [map_mul, hy]
    exact htr j z hz l
  choose a ha ha' using hδb
  rw [← T'.sum_repr x, Finset.mul_sum]
  refine Submodule.sum_mem (orderSubmodule p c) fun l _ => ?_
  have hcoeff : ‖T'.repr x l‖ ≤ 1 := by
    rw [hcoef]
    exact trace_mem_padicInt_of_mem_integral p c (mul_mem_integral p c hx (hTint l))
  rw [mul_smul_comm, Basis.piTensorProduct_apply, PiTensorProduct.tprod_mul_tprod]
  have : ((fun j => factorMk p (c j) (δ j)) * fun j => b' j (l j)) =
      fun j => factorMk p (c j) (a j (l j)) := funext fun j => (ha' j (l j)).symm
  rw [this]
  exact Submodule.smul_mem (orderSubmodule p c) (⟨_, hcoeff⟩ : ℤ_[p])
    (tprodIntegral_mem p c fun j => ⟨a j (l j), ha j (l j)⟩)

/-- **IUT IV, Proposition 1.1** (packet level): let all places `c j = w_j` lie over `p`,
and let `δ_j ∈ K_{w_j}` satisfy the local-different hypothesis: `‖δ_j y‖ ≤ 1` whenever
`Tr_{K_{w_j}/ℚ_p}(y z) ∈ ℤ_p` for all `z ∈ 𝓞_{w_j}` (i.e. `δ_j 𝔡_{w_j}^{-1} ⊆ 𝓞_{w_j}`).
Then `(∏_j δ_j) · (R_I)^∼ ⊆ R_I`. -/
theorem prod_incl_mul_mem_order_of_mem_integral (hc : ∀ j, IsOver K p (c j))
    (w : ι → FinitePlace K) (h : ∀ j, c j = Place.finite (w j))
    (δ : ∀ j, completionAt K (w j))
    (hδ : ∀ j (y : completionAt K (w j)),
      (∀ z : completionAt K (w j), ‖z‖ ≤ 1 →
        letI := padicAlgebra ((hc j).residueChar_of_eq p (h j))
        ‖Algebra.trace ℚ_[p] (completionAt K (w j)) (y * z)‖ ≤ 1) →
      ‖δ j * y‖ ≤ 1) :
    ∀ x ∈ integral p c, (∏ j, incl p c j (w j) (h j) (δ j)) * x ∈ order p c := by
  obtain rfl : w = fun j => finPart K (c j) := funext fun j => eq_finPart (h j)
  intro x hx
  have hprod : ∏ j, incl p c j (finPart K (c j)) (h j) (δ j) =
      PiTensorProduct.tprod ℚ_[p] fun j => factorMk p (c j) (δ j) := by
    rw [tprod_eq_prod_inclFactor]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [incl_apply, completionCongr_rfl]
    rfl
  rw [hprod]
  refine tprod_mul_mem_order_of_mem_integral p c hc δ (fun j y hy => hδ j y fun z hz => ?_) hx
  have := hy z hz
  rwa [trace_factorMk p (c j) (hc j)] at this

end Packet

end LocalConstruct

end Iut
