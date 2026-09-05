/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.GalCompletion
import Iut.Cor312.ThetaData.ValuationTransfer

/-!
# The comparison map of completions `F_w → K_v` for `v ∣ w`

For number fields `k ⊆ K` and finite places `v ∣ w` (`Iut.FinitePlace.LiesOver v w`), the
inclusion `k → K` satisfies `v(x) = w(x)^e` with `e = e(v/w) ≠ 0`
(`Iut.valuation_algebraMap_eq_pow`). Such a ring homomorphism is uniformly continuous for
the valuation uniformities (the neighbourhood bases `{v < γ}` correspond), so it extends to
a continuous ring homomorphism of the completions

`Iut.embedCompletion hvw : k_w →+* K_v`

which extends the inclusion (`Iut.embedCompletion_embedding`) and raises the valuation to
the `e`-th power (`Iut.valued_embedCompletion`). This generalises `Iut.completionMap` and
`Iut.adicCompletionMap` (valuation-preserving endomorphisms) of
`Iut.Cor312.ThetaData.GalCompletion`.
-/

namespace Iut

open NumberField IsDedekindDomain WithZero

noncomputable section

/-! ### Valuation-power homomorphisms and completions -/

section PowHom

variable {k K : Type*} [Field k] [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation k Γ₀) (v' : Valuation K Γ₀) (φ : k →+* K) (e : ℕ)

/-- The valuation of `WithVal.map v v' φ x` for `φ` raising valuations to the `e`-th power. -/
theorem valued_withValMap_pow (hφ : ∀ x, v' (φ x) = v x ^ e) (x : WithVal v) :
    Valued.v (WithVal.map v v' φ x) = Valued.v x ^ e := by
  rw [WithVal.map_apply, WithVal.valued_toVal, hφ, WithVal.apply_ofVal]

/-- A ring homomorphism raising valuations to a fixed positive power is uniformly continuous
(for `v` surjective). -/
theorem uniformContinuous_withValMap_pow (hφ : ∀ x, v' (φ x) = v x ^ e) (he : e ≠ 0)
    (hv : Function.Surjective v) : UniformContinuous (WithVal.map v v' φ) := by
  refine uniformContinuous_of_continuousAt_zero (WithVal.map v v' φ) ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  obtain ⟨x₀, hx₀⟩ := hv (min (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) 1)
  have hmin : min (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) 1 ≠ 0 := by
    rw [ne_eq, min_eq_iff]
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact hγ0 h
    · exact one_ne_zero h
  have hne : (Valued.v : Valuation (WithVal v) Γ₀).restrict (WithVal.toVal v x₀) ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, WithVal.valued_toVal, hx₀]
    exact hmin
  refine Valued.mem_nhds_zero.2 ⟨Units.mk0 _ hne, fun x hx => hγ ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff, WithVal.valued_toVal,
    hx₀, lt_min_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding,
    valued_withValMap_pow v v' φ e hφ]
  calc Valued.v x ^ e ≤ Valued.v x := pow_le_of_le_one zero_le hx.2.le he
    _ < _ := hx.1

/-- The continuous ring homomorphism of completions induced by a valuation-power `φ`. -/
def completionMapPow (hφ : ∀ x, v' (φ x) = v x ^ e) (he : e ≠ 0)
    (hv : Function.Surjective v) : v.Completion →+* v'.Completion :=
  UniformSpace.Completion.mapRingHom (WithVal.map v v' φ)
    (uniformContinuous_withValMap_pow v v' φ e hφ he hv).continuous

variable {v v' φ e}

theorem continuous_completionMapPow (hφ : ∀ x, v' (φ x) = v x ^ e) (he : e ≠ 0)
    (hv : Function.Surjective v) : Continuous (completionMapPow v v' φ e hφ he hv) :=
  UniformSpace.Completion.continuous_map

theorem completionMapPow_coe' (hφ : ∀ x, v' (φ x) = v x ^ e) (he : e ≠ 0)
    (hv : Function.Surjective v) (x : WithVal v) :
    completionMapPow v v' φ e hφ he hv (x : v.Completion) =
      (WithVal.map v v' φ x : v'.Completion) :=
  UniformSpace.Completion.mapRingHom_coe _ x

theorem completionMapPow_coe (hφ : ∀ x, v' (φ x) = v x ^ e) (he : e ≠ 0)
    (hv : Function.Surjective v) (x : k) :
    completionMapPow v v' φ e hφ he hv (x : v.Completion) = (φ x : v'.Completion) :=
  completionMapPow_coe' hφ he hv _

/-- The extension to the completions raises the valuation to the `e`-th power. -/
theorem valued_completionMapPow (hφ : ∀ x, v' (φ x) = v x ^ e) (he : e ≠ 0)
    (hv : Function.Surjective v) (y : v.Completion) :
    Valued.v (completionMapPow v v' φ e hφ he hv y) = Valued.v y ^ e := by
  by_cases hy : y = 0
  · subst hy; simp [zero_pow he]
  have hfy : completionMapPow v v' φ e hφ he hv y ≠ 0 := (map_ne_zero _).2 hy
  have h1 : {z | Valued.v z = Valued.v y} ∈ nhds y :=
    Valued.locally_const ((Valuation.ne_zero_iff _).2 hy)
  have h2 : (completionMapPow v v' φ e hφ he hv) ⁻¹'
      {z | Valued.v z = Valued.v (completionMapPow v v' φ e hφ he hv y)} ∈ nhds y :=
    (continuous_completionMapPow hφ he hv).continuousAt.preimage_mem_nhds
      (Valued.locally_const ((Valuation.ne_zero_iff _).2 hfy))
  obtain ⟨t, hts, ht, hyt⟩ := mem_nhds_iff.1 (Filter.inter_mem h1 h2)
  obtain ⟨r, hr⟩ := UniformSpace.Completion.denseRange_coe.exists_mem_open ht ⟨y, hyt⟩
  obtain ⟨hr1, hr2⟩ := hts hr
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hr1 hr2
  rw [← hr1, ← hr2, completionMapPow_coe', Valued.valuedCompletion_apply,
    Valued.valuedCompletion_apply, valued_withValMap_pow v v' φ e hφ]

end PowHom

/-! ### Adic completions -/

section Adic

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  {k K : Type*} [Field k] [Algebra R k] [IsFractionRing R k] [Field K] [Algebra S K]
  [IsFractionRing S K]
variable (v : HeightOneSpectrum R) (v' : HeightOneSpectrum S) (φ : k →+* K) (e : ℕ)

/-- The continuous ring homomorphism `k_v → K_{v'}` induced by `φ : k → K` raising the
`v`-adic valuation to the `e`-th power of the `v'`-adic valuation. -/
def adicCompletionMapPow (hφ : ∀ x, v'.valuation K (φ x) = v.valuation k x ^ e) (he : e ≠ 0) :
    v.adicCompletion k →+* v'.adicCompletion K :=
  (HeightOneSpectrum.adicCompletion.equiv K v').symm.toRingHom.comp
    ((completionMapPow (v.valuation k) (v'.valuation K) φ e hφ he (v.valuation_surjective k)).comp
      (HeightOneSpectrum.adicCompletion.equiv k v).toRingHom)

variable {v v' φ e}

theorem adicCompletionMapPow_coe (hφ : ∀ x, v'.valuation K (φ x) = v.valuation k x ^ e)
    (he : e ≠ 0) (x : k) :
    adicCompletionMapPow v v' φ e hφ he (x : v.adicCompletion k) = (φ x : v'.adicCompletion K) := by
  apply HeightOneSpectrum.adicCompletion.ext
  exact completionMapPow_coe hφ he (v.valuation_surjective k) x

theorem continuous_adicCompletionMapPow (hφ : ∀ x, v'.valuation K (φ x) = v.valuation k x ^ e)
    (he : e ≠ 0) : Continuous (adicCompletionMapPow v v' φ e hφ he) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v').comp
    ((continuous_completionMapPow hφ he (v.valuation_surjective k)).comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion k v))

theorem valued_adicCompletionMapPow (hφ : ∀ x, v'.valuation K (φ x) = v.valuation k x ^ e)
    (he : e ≠ 0) (y : v.adicCompletion k) :
    Valued.v (adicCompletionMapPow v v' φ e hφ he y) = Valued.v y ^ e :=
  valued_completionMapPow hφ he (v.valuation_surjective k) y.toCompletion

end Adic

/-! ### The comparison map `k_w → K_v` for `v ∣ w` -/

section Places

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {v : FinitePlace K} {w : FinitePlace k}

/-- The ramification index `e(v/w)` of `v` over `w`. -/
abbrev relRamIdx (v : FinitePlace K) (w : FinitePlace k) : ℕ :=
  w.maximalIdeal.asIdeal.ramificationIdx' v.maximalIdeal.asIdeal

/-- **The comparison map of completions** `k_w → K_v` for `v ∣ w`. -/
def embedCompletion (hvw : FinitePlace.LiesOver v w) :
    localCompletion w →+* localCompletion v :=
  adicCompletionMapPow w.maximalIdeal v.maximalIdeal (algebraMap k K) (relRamIdx v w)
    (valuation_algebraMap_eq_pow hvw) (ramificationIdx'_ne_zero hvw)

variable (hvw : FinitePlace.LiesOver v w)

/-- The comparison map extends the inclusion `k → K`. -/
theorem embedCompletion_embedding (x : k) :
    embedCompletion hvw (FinitePlace.embedding w.maximalIdeal x) =
      FinitePlace.embedding v.maximalIdeal (algebraMap k K x) :=
  adicCompletionMapPow_coe _ _ x

theorem continuous_embedCompletion : Continuous (embedCompletion hvw) :=
  continuous_adicCompletionMapPow _ _

/-- The comparison map raises the valuation to the power `e(v/w)`. -/
theorem valued_embedCompletion (y : localCompletion w) :
    Valued.v (embedCompletion hvw y) = Valued.v y ^ relRamIdx v w :=
  valued_adicCompletionMapPow _ _ y

/-- The comparison map preserves the condition `‖y‖ < 1`. -/
theorem norm_embedCompletion_lt_one_iff (y : localCompletion w) :
    ‖embedCompletion hvw y‖ < 1 ↔ ‖y‖ < 1 := by
  rw [norm_lt_one_iff_valued, norm_lt_one_iff_valued, valued_embedCompletion]
  exact pow_lt_one_iff_of_nonneg zero_le (ramificationIdx'_ne_zero hvw)

end Places

end

end Iut
