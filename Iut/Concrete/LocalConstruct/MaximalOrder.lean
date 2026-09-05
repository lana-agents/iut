/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.Indeterminacy

/-!
# The maximal order `(R_I)^∼` of a nonarchimedean tensor packet (taxis #4, #278)

The **integral structure** of the packet `⊗_j K_{c j}` at a prime `p` used by
`Iut.LocalTheory` is the normalization `(R_I)^∼` of the order `R_I = ⊗_{ℤ_p} 𝓞_{c j}`
(IUT IV, Proposition 1.2): the ring of integers of the packet, i.e. the product of the
rings of integers of its field factors. We define it as the **integral closure of `ℤ_p` in
the packet** (`integral`, the field `LocalTheory.integral` at a prime) and prove:

* `R_I ⊆ (R_I)^∼` (`order_subset_integral`): `R_I` is a subring which is a finitely
  generated `ℤ_p`-module (a bounded `ℤ_p`-submodule of a finite-dimensional `ℚ_p`-space,
  `fg_of_subset_closedBall`), so its elements are integral;
* `(R_I)^∼` is **bounded** (`exists_integral_subset_closedBall`), hence compact, open and
  closed. This uses that the packet is **reduced**: it is formally unramified over `ℚ_p`
  (a tensor product of finite separable field extensions, `formallyUnramified_tensor`), so
  reduced (`Algebra.FormallyUnramified.isReduced_of_field`), hence, being Artinian, embeds
  in the product of its residue fields `⊗_j K_{c j} ↪ ∏_𝔪 A/𝔪` (`IsArtinianRing.equivPi`);
  each residue field is a finite separable extension of `ℚ_p`, in which the integral
  closure of `ℤ_p` is a finitely generated `ℤ_p`-module (`IsIntegralClosure.isNoetherian`);
  so `(R_I)^∼` embeds in a finitely generated `ℤ_p`-module, hence is finitely generated
  (`finite_integralClosure`) and bounded;
* automorphisms of the packet over `ℚ_p` preserve `(R_I)^∼`
  (`mapAlgHom_image_integral_subset`; IUT IV, Proposition 1.4(iv), at every prime).
-/

namespace Iut

namespace LocalConstruct

open NumberField
open scoped TensorProduct Pointwise

universe u

/-! ### Formal unramifiedness of tensor products -/

/-- A tensor product of formally unramified algebras is formally unramified. -/
theorem PiTensorProduct.formallyUnramified {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.FormallyUnramified R (A i)] :
    Algebra.FormallyUnramified R (⨂[R] i, A i) := by
  classical
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f g hfg
  refine PiTensorProduct.algHom_ext fun i => ?_
  apply Algebra.FormallyUnramified.comp_injective I hI
  ext x
  exact AlgHom.congr_fun hfg (PiTensorProduct.singleAlgHom i x)

variable {K : Type u} [Field K] [NumberField K]

section Factor

variable (p : Nat.Primes)

/-- `K_w` is formally unramified over `ℚ_p` (a finite extension of a field of
characteristic zero). -/
lemma formallyUnramified_completion {w : FinitePlace K} (hw : residueChar w = (p : ℕ)) :
    letI := padicAlgebra hw
    Algebra.FormallyUnramified ℚ_[p] (completionAt K w) := by
  letI := padicAlgebra hw
  haveI := finite_padicAlgebra hw
  exact Algebra.FormallyUnramified.of_isSeparable ℚ_[p] (completionAt K w)

variable (v : Place K)

/-- For `v ∣ p`, the factor `Factor K p v` with its `ℚ_p`-algebra structure is the quotient
algebra `K_v ⧸ ⊥` of the completion (with the `ℚ_p`-structure `padicAlgebra`). -/
noncomputable def factorQuotAlgEquiv (h : IsOver K p v) :
    letI := padicAlgebra h.residueChar_finPart
    (completionAt K (finPart K v) ⧸ junkIdeal K p v) ≃ₐ[ℚ_[p]] Factor K p v :=
  letI := padicAlgebra h.residueChar_finPart
  AlgEquiv.ofRingEquiv (f := RingEquiv.refl (completionAt K (finPart K v) ⧸ junkIdeal K p v))
    fun r => by
      rw [algebraMap_factor_apply_of_isOver p v h]
      rfl

/-- The factors are formally unramified over `ℚ_p`. -/
instance formallyUnramified_factor : Algebra.FormallyUnramified ℚ_[p] (Factor K p v) := by
  by_cases h : IsOver K p v
  · letI := padicAlgebra h.residueChar_finPart
    haveI := formallyUnramified_completion p h.residueChar_finPart
    exact Algebra.FormallyUnramified.of_equiv (factorQuotAlgEquiv p v h)
  · haveI := subsingleton_factor p v h
    exact ⟨Module.subsingleton (Factor K p v) _⟩

end Factor

variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)

/-- **The nonarchimedean packets are formally unramified over `ℚ_p`.** -/
instance formallyUnramified_tensor :
    Algebra.FormallyUnramified ℚ_[p] (Tensor K (.finite p) c) :=
  PiTensorProduct.formallyUnramified _

/-- **The nonarchimedean packets are reduced.** -/
instance isReduced_tensor : IsReduced (Tensor K (.finite p) c) :=
  Algebra.FormallyUnramified.isReduced_of_field ℚ_[p] _

/-! ### The `ℤ_p`-algebra structure -/

/-- The quotients of a packet by ideals are `ℤ_p`-algebras compatibly with their
`ℚ_p`-structure. -/
instance instIsScalarTowerQuotient (I : Ideal (Tensor K (.finite p) c)) :
    IsScalarTower ℤ_[p] ℚ_[p] (Tensor K (.finite p) c ⧸ I) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    change Ideal.Quotient.mk I (algebraMap ℤ_[p] _ r) =
      Ideal.Quotient.mk I (algebraMap ℚ_[p] _ (r : ℚ_[p]))
    rw [algebraMap_padicInt_apply]

/-- The order `R_I` as a `ℤ_p`-subalgebra of the packet. -/
noncomputable def orderSubalgebra : Subalgebra ℤ_[p] (Tensor K (.finite p) c) where
  carrier := order p c
  mul_mem' := mul_mem_order p c
  one_mem' := one_mem_order p c
  add_mem' := (orderSubmodule p c).add_mem
  zero_mem' := (orderSubmodule p c).zero_mem
  algebraMap_mem' r := (orderSubmodule p c).smul_mem r (one_mem_order p c)

lemma toSubmodule_orderSubalgebra :
    Subalgebra.toSubmodule (orderSubalgebra p c) = orderSubmodule p c :=
  Submodule.ext fun _ => Iff.rfl

/-! ### Bounded `ℤ_p`-submodules are finitely generated -/

/-- A bounded `ℤ_p`-submodule of a packet is finitely generated: it is contained in the
`ℤ_p`-lattice spanned by `p^{-n}` times the basis of elementary tensors. -/
theorem fg_of_subset_closedBall (N : Submodule ℤ_[p] (Tensor K (.finite p) c)) (M : ℝ)
    (hN : (N : Set (Tensor K (.finite p) c)) ⊆ Metric.closedBall 0 M) : N.FG := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : (p : ℕ).Prime).one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hp1
  set q : ℚ_[p] := ((p : ℕ) : ℚ_[p]) ^ n with hq
  have hq0 : q ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : (p : ℕ).Prime).ne_zero)
  have hqnorm : ‖q‖ = ((p : ℝ) ^ n)⁻¹ := by rw [hq, norm_pow, Padic.norm_p, inv_pow]
  set L : Submodule ℤ_[p] (Tensor K (.finite p) c) :=
    Submodule.span ℤ_[p] (Set.range fun k =>
      (q⁻¹ • packetBasis (RationalPlace.finite p) c k : Tensor K (.finite p) c)) with hL
  have hLfg : L.FG := Submodule.fg_span (Set.finite_range _)
  have hNL : N ≤ L := by
    intro x hx
    have hxM : ‖x‖ ≤ M := by simpa using hN hx
    rw [← (packetBasis (RationalPlace.finite p) c).sum_equivFun x]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hk : ‖(packetBasis (RationalPlace.finite p) c).equivFun x k * q‖ ≤ 1 := by
      rw [norm_mul, hqnorm, ← div_eq_mul_inv, div_le_one (by positivity)]
      refine le_trans ?_ hn.le
      exact (norm_le_pi_norm _ k).trans (by rw [← norm_def]; exact hxM)
    let r : ℤ_[p] := ⟨_, hk⟩
    have : (packetBasis (RationalPlace.finite p) c).equivFun x k •
          packetBasis (RationalPlace.finite p) c k =
        r • (q⁻¹ • packetBasis (RationalPlace.finite p) c k : Tensor K (.finite p) c) := by
      change _ = ((packetBasis (RationalPlace.finite p) c).equivFun x k * q) •
        (q⁻¹ • packetBasis (RationalPlace.finite p) c k : Tensor K (.finite p) c)
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hq0, mul_one]
    rw [this]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨k, rfl⟩)
  haveI : IsNoetherian ℤ_[p] L := isNoetherian_of_fg_of_noetherian L hLfg
  have h := (IsNoetherian.noetherian (N.comap L.subtype)).map L.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hNL] at h

/-- **`R_I` is a finitely generated `ℤ_p`-module.** -/
theorem orderSubmodule_fg : (orderSubmodule p c).FG := by
  obtain ⟨M, hM⟩ := exists_order_subset_closedBall p c
  exact fg_of_subset_closedBall p c _ M hM

/-- **Elements of `R_I` are integral over `ℤ_p`.** -/
theorem isIntegral_of_mem_order {x : Tensor K (.finite p) c} (hx : x ∈ order p c) :
    IsIntegral ℤ_[p] x :=
  IsIntegral.of_mem_of_fg (orderSubalgebra p c)
    (by rw [toSubmodule_orderSubalgebra]; exact orderSubmodule_fg p c) x hx

/-! ### The maximal order -/

/-- **The integral structure `(R_I)^∼`** of a nonarchimedean packet: the integral closure of
`ℤ_p` in the packet, i.e. its ring of integers (`LocalTheory.integral` at a prime; IUT IV,
Proposition 1.2). -/
noncomputable def integral : Set (Tensor K (.finite p) c) :=
  integralClosure ℤ_[p] (Tensor K (.finite p) c)

lemma mem_integral {x : Tensor K (.finite p) c} : x ∈ integral p c ↔ IsIntegral ℤ_[p] x :=
  Iff.rfl

/-- The order is contained in the maximal order. -/
lemma order_subset_integral : order p c ⊆ integral p c := fun _ hx =>
  isIntegral_of_mem_order p c hx

/-- `1 ∈ (R_I)^∼` (`LocalTheory.one_mem_integral` at a prime). -/
lemma one_mem_integral : (1 : Tensor K (.finite p) c) ∈ integral p c :=
  order_subset_integral p c (one_mem_order p c)

lemma mul_mem_integral {x y : Tensor K (.finite p) c} (hx : x ∈ integral p c)
    (hy : y ∈ integral p c) : x * y ∈ integral p c :=
  (integralClosure ℤ_[p] (Tensor K (.finite p) c)).mul_mem hx hy

lemma integral_nonempty : (integral p c).Nonempty := ⟨1, one_mem_integral p c⟩

/-- The inclusion of an integral element of a factor lies in `(R_I)^∼`. -/
lemma incl_mem_integral (j : ι) (w : FinitePlace K) (h : c j = Place.finite w)
    (x : completionAt K w) (hx : ‖x‖ ≤ 1) : incl p c j w h x ∈ integral p c :=
  order_subset_integral p c (incl_mem_order p c j w h x hx)

/-- **Scaling by an integral element of a factor preserves `(R_I)^∼`**. -/
lemma smul_integral_subset (j : ι) (w : FinitePlace K) (h : c j = Place.finite w)
    (x : completionAt K w) (hx : ‖x‖ ≤ 1) :
    incl p c j w h x • integral p c ⊆ integral p c := by
  rintro _ ⟨y, hy, rfl⟩
  exact mul_mem_integral p c (incl_mem_integral p c j w h x hx) hy

/-- **`LocalTheory.smul_integral_subset`**, with the hypothesis `0 ≤ ord_p x`. -/
lemma smul_integral_subset_of_ordp (j : ι) (w : FinitePlace K) (h : c j = Place.finite w)
    (x : completionAt K w) (_hx : x ≠ 0) (hord : 0 ≤ ordp K w x) :
    incl p c j w h x • integral p c ⊆ integral p c :=
  smul_integral_subset p c j w h x (norm_le_one_of_ordp_nonneg hord)

/-- **Automorphisms of the packet over `ℚ_p` preserve `(R_I)^∼`** (IUT IV,
Proposition 1.4(iv), at every prime). -/
theorem mapAlgHom_image_integral_subset
    (σ : ∀ j, Factor K p (c j) ≃ₐ[ℚ_[p]] Factor K p (c j)) :
    mapAlgHom (.finite p) c σ '' integral p c ⊆ integral p c := by
  rintro _ ⟨x, hx, rfl⟩
  refine IsIntegral.map_of_comp_eq (RingHom.id ℤ_[p]) (mapAlgHom (.finite p) c σ).toRingHom
    (RingHom.ext fun r => ?_) hx
  exact ((mapAlgHom (.finite p) c σ).commutes (r : ℚ_[p])).symm

/-! ### Finiteness of the maximal order -/

/-- The nonarchimedean packets are Artinian rings. -/
instance isArtinianRing_tensor : IsArtinianRing (Tensor K (.finite p) c) :=
  IsArtinianRing.of_finite ℚ_[p] _

/-- The integral closure of `ℤ_p` in a residue field of the packet — a finite separable
extension of `ℚ_p` — is a finitely generated `ℤ_p`-module. -/
theorem finite_integralClosure_quotient (I : MaximalSpectrum (Tensor K (.finite p) c)) :
    Module.Finite ℤ_[p] (integralClosure ℤ_[p] (Tensor K (.finite p) c ⧸ I.asIdeal)) := by
  haveI := I.isMaximal
  letI : Field (Tensor K (.finite p) c ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  haveI : Module.Finite ℚ_[p] (Tensor K (.finite p) c ⧸ I.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ_[p] I.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : IsNoetherian ℤ_[p] (integralClosure ℤ_[p] (Tensor K (.finite p) c ⧸ I.asIdeal)) :=
    IsIntegralClosure.isNoetherian ℤ_[p] ℚ_[p] (Tensor K (.finite p) c ⧸ I.asIdeal) _
  infer_instance

/-- **A reduced Artinian ring embeds in the product of its residue fields**: the packet is
determined by its images in the quotients by the maximal ideals. -/
lemma eq_of_forall_quotient_mk_eq {x y : Tensor K (.finite p) c}
    (h : ∀ I : MaximalSpectrum (Tensor K (.finite p) c),
      Ideal.Quotient.mk I.asIdeal x = Ideal.Quotient.mk I.asIdeal y) : x = y :=
  (IsArtinianRing.equivPi _).injective (funext fun I => h I)

/-- **`(R_I)^∼` is a finitely generated `ℤ_p`-module**: it embeds in the product of the
integral closures of `ℤ_p` in the residue fields of the packet. -/
theorem finite_integralClosure :
    Module.Finite ℤ_[p] (integralClosure ℤ_[p] (Tensor K (.finite p) c)) := by
  haveI := fun I => finite_integralClosure_quotient p c I
  let ρ : integralClosure ℤ_[p] (Tensor K (.finite p) c) →ₗ[ℤ_[p]]
      ∀ I : MaximalSpectrum (Tensor K (.finite p) c),
        integralClosure ℤ_[p] (Tensor K (.finite p) c ⧸ I.asIdeal) :=
    { toFun := fun x I => ⟨Ideal.Quotient.mk I.asIdeal x,
        IsIntegral.map_of_comp_eq (RingHom.id ℤ_[p]) (Ideal.Quotient.mk I.asIdeal)
          (RingHom.ext fun _ => rfl) x.2⟩
      map_add' := fun x y => by
        funext I
        exact Subtype.ext (map_add _ _ _)
      map_smul' := fun r x => by
        funext I
        exact Subtype.ext (Submodule.Quotient.mk_smul _ r _) }
  have hρ : Function.Injective ρ := by
    intro x y hxy
    refine Subtype.ext (eq_of_forall_quotient_mk_eq p c fun I => ?_)
    exact congrArg Subtype.val (congrFun hxy I)
  haveI : IsNoetherian ℤ_[p] (integralClosure ℤ_[p] (Tensor K (.finite p) c)) :=
    isNoetherian_of_injective ρ hρ
  infer_instance

/-! ### Boundedness, openness, compactness -/

/-- The `ℤ_p`-span of a finite set is bounded. -/
lemma exists_span_subset_closedBall (s : Set (Tensor K (.finite p) c)) (hs : s.Finite) :
    ∃ M : ℝ, (Submodule.span ℤ_[p] s : Set (Tensor K (.finite p) c)) ⊆
      Metric.closedBall 0 M := by
  obtain ⟨M, hM⟩ := (hs.image norm).bddAbove
  refine ⟨max M 0, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  induction hx using Submodule.span_induction with
  | mem x hx => exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  | zero => simp
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | smul r x _ hx =>
    change ‖(r : ℚ_[p]) • x‖ ≤ _
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one r)).trans hx

/-- **`(R_I)^∼` is bounded.** -/
theorem exists_integral_subset_closedBall :
    ∃ M : ℝ, integral p c ⊆ Metric.closedBall 0 M := by
  haveI := finite_integralClosure p c
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[p])
    (M := integralClosure ℤ_[p] (Tensor K (.finite p) c))
  obtain ⟨M, hM⟩ := exists_span_subset_closedBall p c
    ((integralClosure ℤ_[p] (Tensor K (.finite p) c)).val '' (s : Set _))
    (s.finite_toSet.image _)
  refine ⟨M, fun x hx => hM ?_⟩
  have hmem : (⟨x, hx⟩ : integralClosure ℤ_[p] (Tensor K (.finite p) c)) ∈
      Submodule.span ℤ_[p] (s : Set _) := hs ▸ Submodule.mem_top
  have := Submodule.mem_map_of_mem
    (f := (integralClosure ℤ_[p] (Tensor K (.finite p) c)).val.toLinearMap) hmem
  rw [← Submodule.span_image] at this
  exact this

lemma isBounded_integral : Bornology.IsBounded (integral p c) := by
  obtain ⟨M, hM⟩ := exists_integral_subset_closedBall p c
  exact (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨M, hM⟩

/-- The maximal order as an additive subgroup. -/
noncomputable def integralAddSubgroup : AddSubgroup (Tensor K (.finite p) c) :=
  (Subalgebra.toSubmodule (integralClosure ℤ_[p] (Tensor K (.finite p) c))).toAddSubgroup

lemma coe_integralAddSubgroup :
    (integralAddSubgroup p c : Set (Tensor K (.finite p) c)) = integral p c := rfl

/-- **`(R_I)^∼` is open.** -/
lemma isOpen_integral : IsOpen (integral p c) := by
  obtain ⟨r, hr, hsub⟩ := exists_closedBall_subset_order p c
  rw [← coe_integralAddSubgroup]
  exact AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 hr)
    (hsub.trans (order_subset_integral p c)))

/-- **`(R_I)^∼` is closed.** -/
lemma isClosed_integral : IsClosed (integral p c) := by
  rw [← coe_integralAddSubgroup]
  exact AddSubgroup.isClosed_of_isOpen _ (isOpen_integral p c)

/-- **`(R_I)^∼` is compact.** -/
lemma isCompact_integral : IsCompact (integral p c) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_integral p c) (isBounded_integral p c)

/-- `(R_I)^∼` contains a ball around `0`. -/
lemma exists_closedBall_subset_integral :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : Tensor K (.finite p) c) r ⊆ integral p c := by
  obtain ⟨r, hr, hsub⟩ := exists_closedBall_subset_order p c
  exact ⟨r, hr, hsub.trans (order_subset_integral p c)⟩

end LocalConstruct

end Iut
