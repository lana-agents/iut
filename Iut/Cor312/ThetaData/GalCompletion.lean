/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.PlacesOver
import Iut.Cor312.ThetaData.TateFamily

/-!
# The Galois action on the completions at finite places

For number fields `k ⊆ K`, `σ ∈ Gal(K/k)` and a finite place `w` of `K`, the automorphism `σ`
carries the `w`-adic valuation to the `σ·w`-adic valuation
(`Iut.galPlace_valuation`), hence extends to an isomorphism of the completions
`σ_w : K_w ≃+* K_{σ·w}` (`Iut.galCompletion σ w`) which is continuous with continuous inverse,
extends `σ` (`Iut.galCompletion_emb`), preserves the valuation
(`Iut.valued_galCompletion`) and the norm (`Iut.norm_galCompletion`).

The construction is done in two general layers:

* `Iut.ValuedHom`: a ring homomorphism `φ : K → K` with `v' ∘ φ = v` between two valuations on a
  field is uniformly continuous for the valuation uniformities, so extends to a continuous ring
  homomorphism `Iut.completionMap : v.Completion →+* v'.Completion` preserving the valuation;
* `Iut.adicCompletionMap`: the same for the adic completions of a Dedekind domain at two height-one
  primes, together with an extensionality principle for continuous ring homomorphisms out of an
  adic completion (`Iut.adicCompletion_hom_ext`).

The input `Iut.galPlace_valuation` is obtained from the general transport of `intValuation` and
`valuation` along a ring isomorphism of Dedekind domains (`Iut.intValuation_of_comap`,
`Iut.valuation_of_comap`). The file also records `Iut.galPlace_one` and
`Iut.galPlace_inv_galPlace` (the action of `Gal(K/k)` on places is an action).
-/

namespace Iut

open NumberField IsDedekindDomain WithZero

noncomputable section

/-! ### Valuation-preserving homomorphisms and completions -/

section ValuedHom

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v v' : Valuation K Γ₀) (φ : K →+* K)

/-- The valuation of `WithVal.map v v' φ x` for a valuation-preserving `φ`. -/
theorem valued_withValMap (hφ : ∀ x, v' (φ x) = v x) (x : WithVal v) :
    Valued.v (WithVal.map v v' φ x) = Valued.v x := by
  rw [WithVal.map_apply, WithVal.valued_toVal, hφ, WithVal.apply_ofVal]

/-- A valuation-preserving ring homomorphism is uniformly continuous (for `v` surjective). -/
theorem uniformContinuous_withValMap (hφ : ∀ x, v' (φ x) = v x)
    (hv : Function.Surjective v) : UniformContinuous (WithVal.map v v' φ) := by
  refine uniformContinuous_of_continuousAt_zero (WithVal.map v v' φ) ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨x₀, hx₀⟩ := hv (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have hne : (Valued.v : Valuation (WithVal v) Γ₀).restrict (WithVal.toVal v x₀) ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, WithVal.valued_toVal, hx₀]
    exact MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  refine Valued.mem_nhds_zero.2 ⟨Units.mk0 _ hne, fun x hx => hγ ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff, WithVal.valued_toVal,
    hx₀] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding,
    valued_withValMap v v' φ hφ]
  exact hx

/-- The continuous ring homomorphism of completions induced by a valuation-preserving `φ`. -/
def completionMap (hφ : ∀ x, v' (φ x) = v x) (hv : Function.Surjective v) :
    v.Completion →+* v'.Completion :=
  UniformSpace.Completion.mapRingHom (WithVal.map v v' φ)
    (uniformContinuous_withValMap v v' φ hφ hv).continuous

variable {v v' φ}

theorem continuous_completionMap (hφ : ∀ x, v' (φ x) = v x) (hv : Function.Surjective v) :
    Continuous (completionMap v v' φ hφ hv) :=
  UniformSpace.Completion.continuous_map

theorem completionMap_coe' (hφ : ∀ x, v' (φ x) = v x) (hv : Function.Surjective v)
    (x : WithVal v) :
    completionMap v v' φ hφ hv (x : v.Completion) = (WithVal.map v v' φ x : v'.Completion) :=
  UniformSpace.Completion.mapRingHom_coe _ x

theorem completionMap_coe (hφ : ∀ x, v' (φ x) = v x) (hv : Function.Surjective v) (x : K) :
    completionMap v v' φ hφ hv (x : v.Completion) = (φ x : v'.Completion) :=
  completionMap_coe' hφ hv _

/-- The extension of a valuation-preserving homomorphism to the completions preserves the
valuation. -/
theorem valued_completionMap (hφ : ∀ x, v' (φ x) = v x) (hv : Function.Surjective v)
    (y : v.Completion) : Valued.v (completionMap v v' φ hφ hv y) = Valued.v y := by
  by_cases hy : y = 0
  · subst hy; simp
  have hfy : completionMap v v' φ hφ hv y ≠ 0 := (map_ne_zero _).2 hy
  have h1 : {z | Valued.v z = Valued.v y} ∈ nhds y :=
    Valued.locally_const ((Valuation.ne_zero_iff _).2 hy)
  have h2 : (completionMap v v' φ hφ hv) ⁻¹'
      {z | Valued.v z = Valued.v (completionMap v v' φ hφ hv y)} ∈ nhds y :=
    (continuous_completionMap hφ hv).continuousAt.preimage_mem_nhds
      (Valued.locally_const ((Valuation.ne_zero_iff _).2 hfy))
  obtain ⟨t, hts, ht, hyt⟩ := mem_nhds_iff.1 (Filter.inter_mem h1 h2)
  obtain ⟨r, hr⟩ := UniformSpace.Completion.denseRange_coe.exists_mem_open ht ⟨y, hyt⟩
  obtain ⟨hr1, hr2⟩ := hts hr
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hr1 hr2
  rw [← hr1, ← hr2, completionMap_coe', Valued.valuedCompletion_apply,
    Valued.valuedCompletion_apply, valued_withValMap v v' φ hφ]

end ValuedHom

/-! ### Adic completions -/

section Adic

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The image of `K` is dense in its `v`-adic completion. -/
theorem denseRange_coe_adicCompletion (v : HeightOneSpectrum R) :
    DenseRange ((↑) : K → v.adicCompletion K) := by
  have h : ((↑) : K → v.adicCompletion K) =
      HeightOneSpectrum.adicCompletion.ofCompletion ∘ ((↑) : WithVal (v.valuation K) → _) ∘
        (WithVal.equiv (v.valuation K)).symm := rfl
  rw [h]
  exact ((HeightOneSpectrum.adicCompletion.ofCompletion_surjective K v).denseRange.comp
    (UniformSpace.Completion.denseRange_coe.comp
      (WithVal.equiv (v.valuation K)).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _))
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v))

/-- Continuous ring homomorphisms out of an adic completion are determined by their values on
`K`. -/
theorem adicCompletion_hom_ext (v : HeightOneSpectrum R) {A : Type*} [TopologicalSpace A]
    [T2Space A] [NonAssocSemiring A] {f g : v.adicCompletion K →+* A} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ x : K, f x = g x) : f = g :=
  RingHom.ext (congr_fun ((denseRange_coe_adicCompletion v).equalizer hf hg (funext h)))

variable (v v' : HeightOneSpectrum R) (φ : K →+* K)

/-- The continuous ring homomorphism `K_v → K_{v'}` induced by `φ : K → K` carrying the `v`-adic
valuation to the `v'`-adic valuation. -/
def adicCompletionMap (hφ : ∀ x, v'.valuation K (φ x) = v.valuation K x) :
    v.adicCompletion K →+* v'.adicCompletion K :=
  (HeightOneSpectrum.adicCompletion.equiv K v').symm.toRingHom.comp
    ((completionMap (v.valuation K) (v'.valuation K) φ hφ (v.valuation_surjective K)).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom)

variable {v v' φ}

theorem adicCompletionMap_coe (hφ : ∀ x, v'.valuation K (φ x) = v.valuation K x) (x : K) :
    adicCompletionMap v v' φ hφ (x : v.adicCompletion K) = (φ x : v'.adicCompletion K) := by
  apply HeightOneSpectrum.adicCompletion.ext
  exact completionMap_coe hφ (v.valuation_surjective K) x

theorem adicCompletionMap_embedding (hφ : ∀ x, v'.valuation K (φ x) = v.valuation K x) (x : K) :
    adicCompletionMap v v' φ hφ (FinitePlace.embedding v x) = FinitePlace.embedding v' (φ x) :=
  adicCompletionMap_coe hφ x

theorem continuous_adicCompletionMap (hφ : ∀ x, v'.valuation K (φ x) = v.valuation K x) :
    Continuous (adicCompletionMap v v' φ hφ) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v').comp
    ((continuous_completionMap hφ (v.valuation_surjective K)).comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K v))

theorem valued_adicCompletionMap (hφ : ∀ x, v'.valuation K (φ x) = v.valuation K x)
    (y : v.adicCompletion K) : Valued.v (adicCompletionMap v v' φ hφ y) = Valued.v y :=
  valued_completionMap hφ (v.valuation_surjective K) y.toCompletion

end Adic

/-! ### Valuations along ring isomorphisms of Dedekind domains -/

section IntValuation

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]

omit [IsDedekindDomain R] [IsDedekindDomain S] in
lemma mem_comap_pow_iff (f : R →+* S) (hf : Function.Bijective f) (I : Ideal S) (a : R)
    (n : ℕ) : a ∈ (I.comap f) ^ n ↔ f a ∈ I ^ n := by
  let e := RingEquiv.ofBijective f hf
  have he : I.comap f = I.comap e := by
    ext x; rw [Ideal.mem_comap, Ideal.mem_comap, RingEquiv.coe_ofBijective]
  have hea : f a = e a := (RingEquiv.coe_ofBijective f hf).symm ▸ rfl
  rw [he, hea, ← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]

/-- The `intValuation` at the prime `w = f⁻¹(v)` of `a` is the `intValuation` at `v` of `f a`. -/
theorem intValuation_of_comap {v : HeightOneSpectrum S} {w : HeightOneSpectrum R} (f : R →+* S)
    (hf : Function.Bijective f) (hw : w.asIdeal = v.asIdeal.comap f) (a : R) :
    w.intValuation a = v.intValuation (f a) := by
  have key : ∀ n : ℕ, w.intValuation a ≤ exp (-(n : ℤ)) ↔
      v.intValuation (f a) ≤ exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      hw]
    exact mem_comap_pow_iff f hf v.asIdeal a n
  by_cases ha : a = 0
  · subst ha; simp
  have hfa : f a ≠ 0 := (map_ne_zero_iff f hf.injective).2 ha
  obtain ⟨m, hm⟩ : ∃ m : ℕ, w.intValuation a = exp (-(m : ℤ)) :=
    ⟨_, w.intValuation_if_neg ha⟩
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, v.intValuation (f a) = exp (-(m' : ℤ)) :=
    ⟨_, v.intValuation_if_neg hfa⟩
  rw [hm, hm'] at key ⊢
  simp only [exp_le_exp, neg_le_neg_iff, Nat.cast_le] at key
  rw [le_antisymm ((key m).1 le_rfl) ((key m').2 le_rfl)]

/-- The valuation at `w = f⁻¹(v)` of `x` is the valuation at `v` of `φ x`, for `φ` a field
homomorphism extending `f`. -/
theorem valuation_of_comap {K L : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
    [Algebra S L] [IsFractionRing S L] {v : HeightOneSpectrum S} {w : HeightOneSpectrum R}
    (f : R →+* S) (hf : Function.Bijective f) (hw : w.asIdeal = v.asIdeal.comap f)
    (φ : K →+* L) (hφ : ∀ r : R, φ (algebraMap R K r) = algebraMap S L (f r)) (x : K) :
    w.valuation K x = v.valuation L (φ x) := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have h3 : v.valuation L (algebraMap S L (f r)) = v.intValuation (f r) :=
    v.valuation_of_algebraMap (K := L) (f r)
  have h4 : v.valuation L (algebraMap S L (f s)) = v.intValuation (f s) :=
    v.valuation_of_algebraMap (K := L) (f s)
  change w.valuation K (IsLocalization.mk' K r s) = v.valuation L (φ (IsLocalization.mk' K r s))
  rw [HeightOneSpectrum.valuation_of_mk', IsFractionRing.mk'_eq_div, map_div₀, hφ, hφ, map_div₀,
    h3, h4, intValuation_of_comap f hf hw, intValuation_of_comap f hf hw]

end IntValuation

/-! ### The Galois action on valuations and completions -/

section Galois

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

lemma galRestrictInt_bijective (σ : K ≃ₐ[k] K) :
    Function.Bijective (galRestrictInt σ : 𝓞 K →+* 𝓞 K) :=
  (galRestrictInt σ).bijective

lemma algebraMap_galRestrictInt (σ : K ≃ₐ[k] K) (r : 𝓞 K) :
    (σ : K →+* K) (algebraMap (𝓞 K) K r) =
      algebraMap (𝓞 K) K ((galRestrictInt σ : 𝓞 K →+* 𝓞 K) r) :=
  (coe_galRestrictInt σ r).symm

lemma galRestrictInt_inv_apply (σ : K ≃ₐ[k] K) (a : 𝓞 K) :
    galRestrictInt σ⁻¹ (galRestrictInt σ a) = a := by
  apply RingOfIntegers.coe_injective
  change ((galRestrictInt σ⁻¹ (galRestrictInt σ a) : 𝓞 K) : K) = (a : K)
  rw [coe_galRestrictInt, coe_galRestrictInt, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

/-- **`σ⁻¹` carries the `σ·w`-adic valuation to the `w`-adic valuation.** -/
theorem galPlace_valuation_inv (σ : K ≃ₐ[k] K) (w : FinitePlace K) (x : K) :
    w.maximalIdeal.valuation K (σ⁻¹ x) = (galPlace σ w).maximalIdeal.valuation K x := by
  have h := valuation_of_comap (galRestrictInt σ⁻¹ : 𝓞 K →+* 𝓞 K)
    (galRestrictInt_bijective σ⁻¹) (galPlace_maximalIdeal σ w)
    ((σ⁻¹ : K ≃ₐ[k] K) : K →+* K) (algebraMap_galRestrictInt σ⁻¹) x
  rw [RingHom.coe_coe] at h
  exact h.symm

/-- **`σ` carries the `w`-adic valuation to the `σ·w`-adic valuation.** -/
theorem galPlace_valuation (σ : K ≃ₐ[k] K) (w : FinitePlace K) (x : K) :
    (galPlace σ w).maximalIdeal.valuation K (σ x) = w.maximalIdeal.valuation K x := by
  rw [← galPlace_valuation_inv σ w (σ x), AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

/-- **The absolute norm of the prime of `σ·w` is that of the prime of `w`.** -/
theorem absNorm_galPlace (σ : K ≃ₐ[k] K) (w : FinitePlace K) :
    Ideal.absNorm (galPlace σ w).maximalIdeal.asIdeal = Ideal.absNorm w.maximalIdeal.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  let e : 𝓞 K ≃+* 𝓞 K := (galRestrictInt σ⁻¹).toRingEquiv
  have hIJ : w.maximalIdeal.asIdeal = (galPlace σ w).maximalIdeal.asIdeal.map (e : 𝓞 K →+* 𝓞 K) := by
    rw [galPlace_maximalIdeal]
    have : (e : 𝓞 K →+* 𝓞 K) = (galRestrictInt σ⁻¹ : 𝓞 K →+* 𝓞 K) := RingHom.ext fun _ => rfl
    rw [this, Ideal.map_comap_of_surjective (galRestrictInt σ⁻¹ : 𝓞 K →+* 𝓞 K)
      (galRestrictInt_bijective σ⁻¹).surjective]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ e hIJ).toEquiv

/-- **The isomorphism of completions `K_w ≃ K_{σ·w}` induced by `σ ∈ Gal(K/k)`.** -/
def galCompletion (σ : K ≃ₐ[k] K) (w : FinitePlace K) :
    localCompletion w ≃+* localCompletion (galPlace σ w) :=
  RingEquiv.ofRingHom
    (adicCompletionMap w.maximalIdeal (galPlace σ w).maximalIdeal (σ : K →+* K)
      (galPlace_valuation σ w))
    (adicCompletionMap (galPlace σ w).maximalIdeal w.maximalIdeal (σ⁻¹ : K ≃ₐ[k] K)
      (galPlace_valuation_inv σ w))
    (adicCompletion_hom_ext _
      ((continuous_adicCompletionMap _).comp (continuous_adicCompletionMap _)) continuous_id
      (fun x => by
        rw [RingHom.comp_apply, adicCompletionMap_coe, adicCompletionMap_coe, RingHom.id_apply]
        simp))
    (adicCompletion_hom_ext _
      ((continuous_adicCompletionMap _).comp (continuous_adicCompletionMap _)) continuous_id
      (fun x => by
        rw [RingHom.comp_apply, adicCompletionMap_coe, adicCompletionMap_coe, RingHom.id_apply]
        simp))

variable (σ : K ≃ₐ[k] K) (w : FinitePlace K)

theorem galCompletion_apply (x : localCompletion w) :
    galCompletion σ w x =
      adicCompletionMap w.maximalIdeal (galPlace σ w).maximalIdeal (σ : K →+* K)
        (galPlace_valuation σ w) x := rfl

theorem galCompletion_symm_apply (x : localCompletion (galPlace σ w)) :
    (galCompletion σ w).symm x =
      adicCompletionMap (galPlace σ w).maximalIdeal w.maximalIdeal (σ⁻¹ : K ≃ₐ[k] K)
        (galPlace_valuation_inv σ w) x := rfl

/-- `σ_w` extends `σ`. -/
theorem galCompletion_embedding (x : K) :
    galCompletion σ w (FinitePlace.embedding w.maximalIdeal x) =
      FinitePlace.embedding (galPlace σ w).maximalIdeal (σ x) :=
  adicCompletionMap_coe _ x

theorem galCompletion_symm_embedding (x : K) :
    (galCompletion σ w).symm (FinitePlace.embedding (galPlace σ w).maximalIdeal x) =
      FinitePlace.embedding w.maximalIdeal (σ⁻¹ x) :=
  adicCompletionMap_coe _ x

theorem continuous_galCompletion : Continuous (galCompletion σ w) :=
  continuous_adicCompletionMap _

theorem continuous_galCompletion_symm : Continuous (galCompletion σ w).symm :=
  continuous_adicCompletionMap _

/-- **`σ_w` preserves the valuation.** -/
theorem valued_galCompletion (x : localCompletion w) :
    Valued.v (galCompletion σ w x) = Valued.v x :=
  valued_adicCompletionMap _ x

theorem valued_galCompletion_symm (x : localCompletion (galPlace σ w)) :
    Valued.v ((galCompletion σ w).symm x) = Valued.v x :=
  valued_adicCompletionMap _ x

lemma toNNReal_congr {e e' : NNReal} (h : e = e') (he : e ≠ 0) (he' : e' ≠ 0) (x : ℤᵐ⁰) :
    WithZeroMulInt.toNNReal he x = WithZeroMulInt.toNNReal he' x := by
  subst h; rfl

/-- **`σ_w` is an isometry** for the normed-field structures of the completions. -/
theorem norm_galCompletion (x : localCompletion w) : ‖galCompletion σ w x‖ = ‖x‖ := by
  rw [FinitePlace.norm_def, FinitePlace.norm_def, valued_galCompletion]
  congr 1
  exact toNNReal_congr (by rw [absNorm_galPlace]) _ _ _

theorem norm_galCompletion_symm (x : localCompletion (galPlace σ w)) :
    ‖(galCompletion σ w).symm x‖ = ‖x‖ := by
  rw [FinitePlace.norm_def, FinitePlace.norm_def, valued_galCompletion_symm]
  congr 1
  exact toNNReal_congr (by rw [absNorm_galPlace]) _ _ _

/-- **The trivial automorphism fixes every place.** -/
theorem galPlace_one (w : FinitePlace K) : galPlace (1 : K ≃ₐ[k] K) w = w := by
  unfold galPlace
  conv_rhs => rw [← FinitePlace.mk_maximalIdeal w]
  congr 1
  ext1
  simp only [HeightOneSpectrum.comap_asIdeal]
  have : (galRestrictInt (1 : K ≃ₐ[k] K)⁻¹ : 𝓞 K →+* 𝓞 K) = RingHom.id _ := by
    ext a
    rw [RingHom.coe_coe, coe_galRestrictInt, inv_one, AlgEquiv.one_apply, RingHom.id_apply]
  rw [this, Ideal.comap_id]

/-- **`σ⁻¹·(σ·w) = w`.** -/
theorem galPlace_inv_galPlace (σ : K ≃ₐ[k] K) (w : FinitePlace K) :
    galPlace σ⁻¹ (galPlace σ w) = w := by
  unfold galPlace
  rw [FinitePlace.maximalIdeal_mk]
  conv_rhs => rw [← FinitePlace.mk_maximalIdeal w]
  congr 1
  ext1
  simp only [HeightOneSpectrum.comap_asIdeal, Ideal.comap_comap]
  have : (galRestrictInt σ⁻¹ : 𝓞 K →+* 𝓞 K).comp (galRestrictInt σ⁻¹⁻¹ : 𝓞 K →+* 𝓞 K) =
      RingHom.id _ := by
    ext a
    rw [RingHom.comp_apply, RingHom.id_apply, RingHom.coe_coe, RingHom.coe_coe, inv_inv,
      galRestrictInt_inv_apply]
  rw [this, Ideal.comap_id]

/-- **`σ·(σ⁻¹·w) = w`.** -/
theorem galPlace_galPlace_inv (σ : K ≃ₐ[k] K) (w : FinitePlace K) :
    galPlace σ (galPlace σ⁻¹ w) = w := by
  simpa using galPlace_inv_galPlace σ⁻¹ w

end Galois

/-! ### The form used by the Θ-data modules -/

section ThetaData

universe u

variable {F : Type u} [Field F] [NumberField F]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]

/-- `σ_w` extends `σ`, in terms of `Iut.emb`. -/
theorem galCompletion_emb (σ : ↥K ≃ₐ[F] ↥K) (w : FinitePlace ↥K) (x : ↥K) :
    galCompletion σ w (emb K w x) = emb K (galPlace σ w) (σ x) :=
  galCompletion_embedding σ w x

theorem galCompletion_symm_emb (σ : ↥K ≃ₐ[F] ↥K) (w : FinitePlace ↥K) (x : ↥K) :
    (galCompletion σ w).symm (emb K (galPlace σ w) x) = emb K w (σ⁻¹ x) :=
  galCompletion_symm_embedding σ w x

end ThetaData

end

end Iut
