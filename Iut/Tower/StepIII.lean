/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.Different

/-!
# Step (iii): the distinguished primes

**Step (iii)** of the proof of IUT IV, Theorem 1.10: the logarithmic size of the set of
distinguished primes — the primes dividing `2·3·5·ℓ`, the residue characteristics of the
bad places, and the primes ramified in `K` — is bounded by
`2·d_mod·(log(d_{F_tpd}) + log(f_{F_tpd})) + 5 + log ℓ` (`Iut.sum_log_distinguished_le`):

* the primes `2, 3, 5` contribute `log 30 < 5`;
* a bad prime `p ∉ {2, 3, 5, ℓ}` has a place `u₀ ∈ V_mod^bad` over it, all places `u` of
  `F_tpd` over `u₀` are bad, and `e(u/u₀) ≤ 2` (`Iut.RelRamIdxModLeTwo`), so
  `∑_{u ∣ u₀} f_u ≥ [F_tpd : F_mod]/2` and `[F_tpd : F_mod]·log p ≤ 2·∑_{u ∣ u₀} log N(u)`
  (`Iut.sum_bad_log_le`);
* a prime `p ∉ {2, 3, 5, ℓ}` ramified in `K` but not bad is, by Néron–Ogg–Shafarevich,
  ramified in `F_tpd`; `F_tpd/F_mod` being Galois, all places `u'` of `F_tpd` over the
  place `u₀` of `F_mod` below a ramified place have `e_{u'} ≥ 2`, so
  `ord_{u'}(𝔡_{F_tpd}) ≥ e_{u'} − 1 ≥ e_{u'}/2` and
  `[F_tpd : F_mod]·log p ≤ 2·∑_{u' ∣ u₀} ord_{u'}(𝔡_{F_tpd})·log N(u')`
  (`Iut.sum_ramified_log_le`).

The sums over the places over distinct `u₀` are disjoint and bounded by the conductor and
different degrees of `F_tpd`; with `[F_tpd : ℚ] = [F_tpd : F_mod]·d_mod` this gives the
factor `2·d_mod`.
-/

namespace Iut

open NumberField IsDedekindDomain

universe u

/-! ### General lemmas -/

section General

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- In a Galois extension, the ramification indices of the places over a given place
coincide. -/
lemma relRamIdx_eq_of_isGalois [IsGalois k K] {u u' : FinitePlace K} {u₀ : FinitePlace k}
    (h : FinitePlace.LiesOver u u₀) (h' : FinitePlace.LiesOver u' u₀) :
    relRamIdx u u₀ = relRamIdx u' u₀ := by
  haveI : u.maximalIdeal.asIdeal.LiesOver u₀.maximalIdeal.asIdeal := h
  haveI : u'.maximalIdeal.asIdeal.LiesOver u₀.maximalIdeal.asIdeal := h'
  unfold relRamIdx
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ u₀.maximalIdeal.ne_bot,
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ u₀.maximalIdeal.ne_bot]
  exact Ideal.ramificationIdx_eq_of_isGaloisGroup u₀.maximalIdeal.asIdeal _ _ (K ≃ₐ[k] K)

/-- The places over a place `u₀` form a family of pairwise disjoint finsets. -/
lemma placesOver_pairwiseDisjoint (s : Finset (FinitePlace k)) :
    (s : Set (FinitePlace k)).PairwiseDisjoint (placesOver (K := K)) := by
  intro u₀ _ u₀' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro u hu hu'
  rw [mem_placesOver] at hu hu'
  exact hne ((eq_placeUnder_of_liesOver hu).trans (eq_placeUnder_of_liesOver hu').symm)

end General

section DifferentLower

attribute [local instance] FractionRing.liftAlgebra

/-- `e_u − 1 ≤ ord_u(𝔡_{T/ℚ})` (`pow_sub_one_dvd_differentIdeal`). -/
lemma ramIdx_sub_one_le_ordAt_different {T : Type*} [Field T] [NumberField T]
    (u : FinitePlace T) : ramIdx T u - 1 ≤ ordAt (differentIdeal ℤ (𝓞 T)) u := by
  have hp : (residueChar u).Prime := residueChar_prime u
  set p : Ideal ℤ := Ideal.span {(residueChar u : ℤ)} with hp_def
  haveI : p.IsMaximal := LocalConstruct.span_prime_isMaximal hp
  have hp0 : p ≠ ⊥ := LocalConstruct.span_prime_ne_bot hp
  haveI := liesOver_span_residueChar u
  have he : ramIdx T u = p.ramificationIdx' u.maximalIdeal.asIdeal :=
    (Ideal.ramificationIdx'_eq_ramificationIdx p u.maximalIdeal.asIdeal hp0).symm
  have hdvd : u.maximalIdeal.asIdeal ^ ramIdx T u ∣ p.map (algebraMap ℤ (𝓞 T)) := by
    rw [he, Ideal.dvd_iff_le]
    exact Ideal.le_pow_ramificationIdx' (p := p) (P := u.maximalIdeal.asIdeal)
  exact le_ordAt_of_pow_dvd _ differentIdeal_ne_bot u _
    (pow_sub_one_dvd_differentIdeal ℤ (p := p) u.maximalIdeal.asIdeal (ramIdx T u) hp0 hdvd)

end DifferentLower

/-! ### The tower `F_mod ⊆ F_tpd` -/

section Tpd

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

/-- `V_mod^bad` is finite when the bad places of `F` are. -/
lemma vbad_finite (hfin : (badPlacesOver F E VBad).Finite) : VBad.Finite := by
  refine (hfin.image (placeUnder (k := ↥(fieldOfModuli F E)))).subset fun u₀ hu₀ => ?_
  obtain ⟨w, hw⟩ := FinitePlace.exists_liesOver (K := F) u₀
  exact ⟨w, ⟨u₀, hu₀, hw⟩, (eq_placeUnder_of_liesOver hw).symm⟩

/-- A place of `F_tpd` over a place of `V_mod^bad` is bad. -/
lemma isBadTpdOf_of_liesOver {u : FinitePlace ↥(tripodalFieldOf F E)}
    {u₀ : FinitePlace ↥(fieldOfModuli F E)} (hu₀ : u₀ ∈ VBad) (hu : FinitePlace.LiesOver u u₀) :
    IsBadTpdOf F E VBad u := by
  obtain ⟨w, hw⟩ := FinitePlace.exists_liesOver (K := F) u
  exact ⟨w, ⟨u₀, hu₀, FinitePlace.liesOver_trans hw hu⟩, hw⟩

/-- A bad place of `F_tpd` lies over a place of `V_mod^bad` of the same residue
characteristic. -/
lemma exists_vbad_of_isBadTpdOf {u : FinitePlace ↥(tripodalFieldOf F E)}
    (hu : IsBadTpdOf F E VBad u) : ∃ u₀ ∈ VBad, residueChar u₀ = residueChar u := by
  obtain ⟨w, ⟨u₀, hu₀, hwu₀⟩, hwu⟩ := hu
  have hwu' : FinitePlace.LiesOver w u := hwu
  exact ⟨u₀, hu₀, by rw [← residueChar_eq_of_liesOver hwu₀, residueChar_eq_of_liesOver hwu']⟩

variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable {Pr : AdmissiblePrimeData F E Fbar VBad} [NumberField ↥Pr.torsionField]

/-- **The bad primes** `p ∉ {2,3,5,ℓ}`:
`[F_tpd : F_mod]·∑_{p ∈ B} log p ≤ 2·[F_tpd : ℚ]·log(f_{F_tpd})` for a finite set `B` of
residue characteristics of places of `V_mod^bad`. -/
lemma sum_bad_log_le (he2 : RelRamIdxModLeTwo E VBad) (hfin : (badPlacesOver F E VBad).Finite)
    (B : Finset ℕ) (hB : ∀ p ∈ B, ∃ u₀ ∈ VBad, residueChar u₀ = p) :
    (Module.finrank ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) : ℝ) * ∑ p ∈ B, Real.log p ≤
      2 * Module.finrank ℚ ↥(tripodalFieldOf F E) * logConductorDegOf F E VBad := by
  classical
  set T := ↥(tripodalFieldOf F E)
  set M := ↥(fieldOfModuli F E)
  set n := Module.finrank M T with hn
  have hlog : ∀ p : ℕ, 0 ≤ Real.log p := fun p => Real.log_natCast_nonneg p
  set U₀ := (vbad_finite hfin).toFinset.filter (fun u₀ => residueChar u₀ ∈ B) with hU₀
  -- `∑_{p ∈ B} log p ≤ ∑_{u₀ ∈ U₀} log p_{u₀}`
  have h1 : ∑ p ∈ B, Real.log p ≤ ∑ u₀ ∈ U₀, Real.log (residueChar u₀) := by
    have hsub : B ⊆ U₀.image residueChar := by
      intro p hp
      obtain ⟨u₀, hu₀, rfl⟩ := hB p hp
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
        ⟨(Set.Finite.mem_toFinset _).mpr hu₀, hp⟩)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hlog p).trans ?_
    exact Finset.sum_image_le_of_nonneg fun p _ => hlog p
  -- `n·log p_{u₀} ≤ 2·∑_{u ∣ u₀} f_u log p_u`
  have h2 : ∀ u₀ ∈ U₀, (n : ℝ) * Real.log (residueChar u₀) ≤
      2 * ∑ u ∈ placesOver (K := T) u₀, (inertDeg T u : ℝ) * Real.log (residueChar u) := by
    intro u₀ hu₀
    have hu₀' : u₀ ∈ VBad := (Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp hu₀).1
    have hle : n ≤ 2 * ∑ u ∈ placesOver (K := T) u₀, inertDeg T u := by
      rw [hn, ← sum_placesOver_relLocalDeg (K := T) u₀, Finset.mul_sum]
      refine Finset.sum_le_sum fun u hu => ?_
      have huu₀ : FinitePlace.LiesOver u u₀ := (mem_placesOver u₀ u).mp hu
      have he := he2 u u₀ hu₀' huu₀
      have hf : relInertDeg u u₀ ≤ inertDeg T u := by
        rw [inertDeg_eq_mul huu₀]
        exact Nat.le_mul_of_pos_left _ (inertDeg_pos' u₀)
      exact Nat.mul_le_mul he hf
    calc (n : ℝ) * Real.log (residueChar u₀)
        ≤ (2 * ∑ u ∈ placesOver (K := T) u₀, (inertDeg T u : ℕ) : ℝ) * Real.log (residueChar u₀) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (hlog _)
      _ = 2 * ∑ u ∈ placesOver (K := T) u₀, (inertDeg T u : ℝ) * Real.log (residueChar u) := by
          push_cast
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [residueChar_eq_of_liesOver ((mem_placesOver u₀ u).mp hu)]
          ring
  -- the places over the `u₀ ∈ U₀` are bad, and disjoint
  have h3 : ∑ u₀ ∈ U₀, ∑ u ∈ placesOver (K := T) u₀, (inertDeg T u : ℝ) * Real.log (residueChar u)
      = ∑ u ∈ U₀.biUnion (placesOver (K := T)),
          (inertDeg T u : ℝ) * Real.log (residueChar u) :=
    (Finset.sum_biUnion (placesOver_pairwiseDisjoint U₀)).symm
  have h4 : ∑ u ∈ U₀.biUnion (placesOver (K := T)),
      (inertDeg T u : ℝ) * Real.log (residueChar u) ≤
      Module.finrank ℚ T * logConductorDegOf F E VBad := by
    have hT0 : (0 : ℝ) < Module.finrank ℚ T := by exact_mod_cast Module.finrank_pos
    have := sum_bad_inertDeg_div_le hfin (U₀.biUnion (placesOver (K := T))) fun u hu => by
      obtain ⟨u₀, hu₀, hu⟩ := Finset.mem_biUnion.mp hu
      exact isBadTpdOf_of_liesOver ((Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp hu₀).1)
        ((mem_placesOver u₀ u).mp hu)
    rw [← Finset.sum_div, div_le_iff₀ hT0] at this
    linarith
  calc (n : ℝ) * ∑ p ∈ B, Real.log p ≤ (n : ℝ) * ∑ u₀ ∈ U₀, Real.log (residueChar u₀) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ∑ u₀ ∈ U₀, (n : ℝ) * Real.log (residueChar u₀) := Finset.mul_sum _ _ _
    _ ≤ ∑ u₀ ∈ U₀, 2 * ∑ u ∈ placesOver (K := T) u₀,
          (inertDeg T u : ℝ) * Real.log (residueChar u) := Finset.sum_le_sum h2
    _ = 2 * ∑ u ∈ U₀.biUnion (placesOver (K := T)),
          (inertDeg T u : ℝ) * Real.log (residueChar u) := by
        rw [← Finset.mul_sum, h3]
    _ ≤ 2 * (Module.finrank ℚ T * logConductorDegOf F E VBad) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = 2 * Module.finrank ℚ T * logConductorDegOf F E VBad := by ring

/-- **The ramified primes** `p ∉ {2,3,5,ℓ}`:
`[F_tpd : F_mod]·∑_{p ∈ R} log p ≤ 2·[F_tpd : ℚ]·log(d_{F_tpd})` for a finite set `R` of
residue characteristics of places of `F_tpd` ramified over `ℚ`, when `F_tpd/F_mod` is
Galois. -/
lemma sum_ramified_log_le [IsGalois ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E)]
    (R : Finset ℕ)
    (hR : ∀ p ∈ R, ∃ u : FinitePlace ↥(tripodalFieldOf F E),
      residueChar u = p ∧ ramIdx ↥(tripodalFieldOf F E) u ≠ 1) :
    (Module.finrank ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) : ℝ) * ∑ p ∈ R, Real.log p ≤
      2 * Module.finrank ℚ ↥(tripodalFieldOf F E) * logDifferentDeg ↥(tripodalFieldOf F E) := by
  classical
  set T := ↥(tripodalFieldOf F E)
  set M := ↥(fieldOfModuli F E)
  set n := Module.finrank M T with hn
  have hlog : ∀ p : ℕ, 0 ≤ Real.log p := fun p => Real.log_natCast_nonneg p
  set 𝔡 := differentIdeal ℤ (𝓞 T) with h𝔡
  -- the ramified places of residue characteristic in `R`, and the places of `F_mod` below
  set U₁ := (LocalConstruct.ramified_finite (K := T)).toFinset.filter
    (fun u => residueChar u ∈ R) with hU₁
  set U₀ := U₁.image (placeUnder (k := M)) with hU₀
  -- `∑_{p ∈ R} log p ≤ ∑_{u₀ ∈ U₀} log p_{u₀}`
  have h1 : ∑ p ∈ R, Real.log p ≤ ∑ u₀ ∈ U₀, Real.log (residueChar u₀) := by
    have hsub : R ⊆ U₀.image residueChar := by
      intro p hp
      obtain ⟨u, hu, hram⟩ := hR p hp
      have hu₁ : u ∈ U₁ := Finset.mem_filter.mpr
        ⟨(Set.Finite.mem_toFinset _).mpr hram, hu ▸ hp⟩
      refine Finset.mem_image.mpr ⟨placeUnder (k := M) u, Finset.mem_image_of_mem _ hu₁, ?_⟩
      rw [← hu]
      exact (residueChar_eq_of_liesOver (liesOver_placeUnder (k := M) u)).symm
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hlog p).trans ?_
    exact Finset.sum_image_le_of_nonneg fun p _ => hlog p
  -- `n·log p_{u₀} ≤ 2·∑_{u' ∣ u₀} (e_{u'} − 1) f_{u'} log p_{u'}`
  have h2 : ∀ u₀ ∈ U₀, (n : ℝ) * Real.log (residueChar u₀) ≤
      2 * ∑ u' ∈ placesOver (K := T) u₀,
        ((ramIdx T u' - 1 : ℕ) : ℝ) * (inertDeg T u' * Real.log (residueChar u')) := by
    intro u₀ hu₀
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hu₀
    have hram : ramIdx T u ≠ 1 := (Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp hu).1
    have huu₀ : FinitePlace.LiesOver u (placeUnder (k := M) u) := liesOver_placeUnder (k := M) u
    have hle : n ≤ 2 * ∑ u' ∈ placesOver (K := T) (placeUnder (k := M) u),
        (ramIdx T u' - 1) * inertDeg T u' := by
      rw [hn, ← sum_placesOver_relLocalDeg (K := T) (placeUnder (k := M) u), Finset.mul_sum]
      refine Finset.sum_le_sum fun u' hu' => ?_
      have hu'u₀ : FinitePlace.LiesOver u' (placeUnder (k := M) u) := (mem_placesOver _ u').mp hu'
      -- `e_{u'} = e_u ≥ 2`
      have hee : ramIdx T u' = ramIdx T u := by
        rw [ramIdx_eq_mul hu'u₀, ramIdx_eq_mul huu₀, relRamIdx_eq_of_isGalois hu'u₀ huu₀]
      have he2 : 2 ≤ ramIdx T u' := by
        rw [hee]
        have := ramIdx_pos' u
        omega
      have hrel : relRamIdx u' (placeUnder (k := M) u) ≤ ramIdx T u' := by
        rw [ramIdx_eq_mul hu'u₀]
        exact Nat.le_mul_of_pos_left _ (ramIdx_pos' _)
      have hf : relInertDeg u' (placeUnder (k := M) u) ≤ inertDeg T u' := by
        rw [inertDeg_eq_mul hu'u₀]
        exact Nat.le_mul_of_pos_left _ (inertDeg_pos' _)
      calc relRamIdx u' (placeUnder (k := M) u) * relInertDeg u' (placeUnder (k := M) u)
          ≤ (2 * (ramIdx T u' - 1)) * inertDeg T u' := Nat.mul_le_mul (by omega) hf
        _ = 2 * ((ramIdx T u' - 1) * inertDeg T u') := by ring
    calc (n : ℝ) * Real.log (residueChar (placeUnder (k := M) u))
        ≤ (2 * ∑ u' ∈ placesOver (K := T) (placeUnder (k := M) u),
            (ramIdx T u' - 1) * inertDeg T u' : ℕ) *
              Real.log (residueChar (placeUnder (k := M) u)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (hlog _)
      _ = 2 * ∑ u' ∈ placesOver (K := T) (placeUnder (k := M) u),
            ((ramIdx T u' - 1 : ℕ) : ℝ) * (inertDeg T u' * Real.log (residueChar u')) := by
          push_cast
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun u' hu' => ?_
          rw [residueChar_eq_of_liesOver ((mem_placesOver _ u').mp hu')]
          ring
  -- disjointness
  have h3 : ∑ u₀ ∈ U₀, ∑ u' ∈ placesOver (K := T) u₀,
      ((ramIdx T u' - 1 : ℕ) : ℝ) * (inertDeg T u' * Real.log (residueChar u')) =
      ∑ u' ∈ U₀.biUnion (placesOver (K := T)),
        ((ramIdx T u' - 1 : ℕ) : ℝ) * (inertDeg T u' * Real.log (residueChar u')) :=
    (Finset.sum_biUnion (placesOver_pairwiseDisjoint U₀)).symm
  -- the lower bound `e − 1 ≤ ord(𝔡)` and the norm of the different
  have h4 : ∑ u' ∈ U₀.biUnion (placesOver (K := T)),
      ((ramIdx T u' - 1 : ℕ) : ℝ) * (inertDeg T u' * Real.log (residueChar u')) ≤
      Module.finrank ℚ T * logDifferentDeg T := by
    set s := U₀.biUnion (placesOver (K := T)) ∪ (ordAt_support_finite 𝔡).toFinset with hs
    have hs' : ∀ u', ordAt 𝔡 u' ≠ 0 → u' ∈ s := fun u' hu' =>
      Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr hu')
    have hT0 : (0 : ℝ) < Module.finrank ℚ T := by exact_mod_cast Module.finrank_pos
    unfold logDifferentDeg
    rw [mul_div_cancel₀ _ hT0.ne', log_absNorm_eq_sum_ordAt 𝔡 differentIdeal_ne_bot s hs']
    calc ∑ u' ∈ U₀.biUnion (placesOver (K := T)),
          ((ramIdx T u' - 1 : ℕ) : ℝ) * (inertDeg T u' * Real.log (residueChar u'))
        ≤ ∑ u' ∈ U₀.biUnion (placesOver (K := T)),
            (ordAt 𝔡 u' : ℝ) * (inertDeg T u' * Real.log (residueChar u')) := by
          refine Finset.sum_le_sum fun u' _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by positivity) (hlog _))
          exact_mod_cast ramIdx_sub_one_le_ordAt_different u'
      _ ≤ ∑ u' ∈ s, (ordAt 𝔡 u' : ℝ) * (inertDeg T u' * Real.log (residueChar u')) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) ?_
          intro u' _ _
          exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (hlog _))
  calc (n : ℝ) * ∑ p ∈ R, Real.log p ≤ (n : ℝ) * ∑ u₀ ∈ U₀, Real.log (residueChar u₀) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ∑ u₀ ∈ U₀, (n : ℝ) * Real.log (residueChar u₀) := Finset.mul_sum _ _ _
    _ ≤ ∑ u₀ ∈ U₀, 2 * ∑ u' ∈ placesOver (K := T) u₀,
          ((ramIdx T u' - 1 : ℕ) : ℝ) * (inertDeg T u' * Real.log (residueChar u')) :=
        Finset.sum_le_sum h2
    _ = 2 * ∑ u' ∈ U₀.biUnion (placesOver (K := T)),
          ((ramIdx T u' - 1 : ℕ) : ℝ) * (inertDeg T u' * Real.log (residueChar u')) := by
        rw [← Finset.mul_sum, h3]
    _ ≤ 2 * (Module.finrank ℚ T * logDifferentDeg T) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = 2 * Module.finrank ℚ T * logDifferentDeg T := by ring

end Tpd

/-! ### Step (iii) -/

section Main

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable {Pr : AdmissiblePrimeData F E Fbar VBad} [NumberField ↥Pr.torsionField]

/-- `log 2 + log 3 + log 5 ≤ 5`. -/
lemma log_two_add_log_three_add_log_five_le : Real.log 2 + Real.log 3 + Real.log 5 ≤ 5 := by
  have h2 := Real.log_two_lt_d9
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num), show ((2 : ℝ) ^ (2 : ℝ)) = 4 by norm_num]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h5 : Real.log 5 ≤ 3 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num), show ((2 : ℝ) ^ (3 : ℝ)) = 8 by norm_num]
    exact Real.log_le_log (by norm_num) (by norm_num)
  linarith

/-- `∑_{p ∈ {2,3,5,ℓ}} log p ≤ 5 + log ℓ`. -/
lemma sum_log_small_le (ℓ : ℕ) :
    ∑ p ∈ ({2, 3, 5, ℓ} : Finset ℕ), Real.log p ≤ 5 + Real.log ℓ := by
  classical
  have hlog : ∀ p : ℕ, 0 ≤ Real.log (p : ℕ) := fun p => Real.log_natCast_nonneg p
  have h := log_two_add_log_three_add_log_five_le
  calc ∑ p ∈ ({2, 3, 5, ℓ} : Finset ℕ), Real.log p
      ≤ Real.log (2 : ℕ) + ∑ p ∈ ({3, 5, ℓ} : Finset ℕ), Real.log p :=
        sum_insert_le_of_nonneg _ _ _ hlog
    _ ≤ Real.log (2 : ℕ) + (Real.log (3 : ℕ) + ∑ p ∈ ({5, ℓ} : Finset ℕ), Real.log p) := by
        have := sum_insert_le_of_nonneg (3 : ℕ) {5, ℓ} _ hlog
        linarith
    _ ≤ Real.log (2 : ℕ) + (Real.log (3 : ℕ) + (Real.log (5 : ℕ) + ∑ p ∈ ({ℓ} : Finset ℕ),
          Real.log p)) := by
        have := sum_insert_le_of_nonneg (5 : ℕ) {ℓ} _ hlog
        linarith
    _ = Real.log 2 + Real.log 3 + Real.log 5 + Real.log ℓ := by
        rw [Finset.sum_singleton]
        push_cast
        ring
    _ ≤ 5 + Real.log ℓ := by linarith

/-- **Step (iii)** for a finite set `S` of primes each of which divides `2·3·5·ℓ`, is the
residue characteristic of a bad place of `F`, or is ramified in `K`:
`∑_{p ∈ S} log p ≤ 2·d_mod·(log(d_{F_tpd}) + log(f_{F_tpd})) + 5 + log ℓ`. -/
theorem sum_log_distinguished_le (H : TowerLocalFacts E VBad Pr) (he2 : RelRamIdxModLeTwo E VBad)
    [IsGalois ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E)]
    (hfin : (badPlacesOver F E VBad).Finite) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ ({2, 3, 5, Pr.ℓ} : Finset ℕ) ∨
      (∃ w ∈ badPlacesOver F E VBad, residueChar w = p) ∨
      (∃ v : FinitePlace ↥Pr.torsionField, residueChar v = p ∧ ramIdx (↥Pr.torsionField) v ≠ 1)) :
    ∑ p ∈ S, Real.log p ≤
      2 * Module.finrank ℚ ↥(fieldOfModuli F E) *
        (logDifferentDeg ↥(tripodalFieldOf F E) + logConductorDegOf F E VBad) + 5 +
          Real.log Pr.ℓ := by
  classical
  set T := ↥(tripodalFieldOf F E)
  set M := ↥(fieldOfModuli F E)
  set n := Module.finrank M T with hn
  set d := Module.finrank ℚ M with hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Module.finrank_pos
  have hTd : (Module.finrank ℚ T : ℝ) = d * n := by
    rw [hd, hn, finrank_tripodal_eq_mul F E]
    push_cast
    ring
  have hlog : ∀ p : ℕ, 0 ≤ Real.log p := fun p => Real.log_natCast_nonneg p
  set P : Finset ℕ := {2, 3, 5, Pr.ℓ} with hP
  -- the primes dividing `2·3·5·ℓ`
  have h1 : ∑ p ∈ S.filter (fun p => p ∈ P), Real.log p ≤ 5 + Real.log Pr.ℓ :=
    (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).2)
      fun p _ _ => hlog p).trans (sum_log_small_le Pr.ℓ)
  -- the remaining primes: bad, or ramified in `F_tpd`
  set S₂ := S.filter (fun p => p ∉ P) with hS₂
  set B := S₂.filter (fun p => ∃ u₀ ∈ VBad, residueChar u₀ = p) with hB
  set R := S₂.filter (fun p => ¬ ∃ u₀ ∈ VBad, residueChar u₀ = p) with hR
  have hB' : ∀ p ∈ B, ∃ u₀ ∈ VBad, residueChar u₀ = p := fun p hp => (Finset.mem_filter.mp hp).2
  have hR' : ∀ p ∈ R, ∃ u : FinitePlace T, residueChar u = p ∧ ramIdx T u ≠ 1 := by
    intro p hp
    have hp2 := Finset.mem_filter.mp hp
    have hpS := Finset.mem_filter.mp hp2.1
    have hnot := hp2.2
    rcases hS p hpS.1 with h | ⟨w, hw, hwp⟩ | ⟨v, hvp, hv⟩
    · exact absurd h hpS.2
    · exfalso
      obtain ⟨u₀, hu₀, hwu₀⟩ := hw
      exact hnot ⟨u₀, hu₀, by rw [← hwp, residueChar_eq_of_liesOver hwu₀]⟩
    · refine ⟨placeTpd F E Pr.torsionField v, by rw [residueChar_placeTpd, hvp], ?_⟩
      have hbad : ¬ IsBadTpdOf F E VBad (placeTpd F E Pr.torsionField v) := by
        intro hbad
        obtain ⟨u₀, hu₀, hu₀v⟩ := exists_vbad_of_isBadTpdOf hbad
        exact hnot ⟨u₀, hu₀, by rw [hu₀v, residueChar_placeTpd, hvp]⟩
      have hp' : residueChar v ∉ P := by rw [hvp]; exact hpS.2
      have he := H.relRamIdx_eq_one v hp' hbad
      rw [ramIdx_eq_ramIdx_placeTpd_mul (F := F) (E := E) v, he, mul_one] at hv
      exact hv
  have hBle := sum_bad_log_le he2 hfin B hB'
  have hRle := sum_ramified_log_le R hR'
  have h2 : ∑ p ∈ S₂, Real.log p ≤
      2 * d * (logDifferentDeg T + logConductorDegOf F E VBad) := by
    rw [← Finset.sum_filter_add_sum_filter_not S₂ (fun p => ∃ u₀ ∈ VBad, residueChar u₀ = p)]
    rw [hTd] at hBle hRle
    have hcond := logConductorDegOf_nonneg F E VBad
    have hdiff := logDifferentDeg_nonneg T
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have := add_le_add hBle hRle
    rw [← mul_add] at this
    have h' : ∑ p ∈ B, Real.log p + ∑ p ∈ R, Real.log p ≤
        2 * d * (logConductorDegOf F E VBad + logDifferentDeg T) := by
      by_contra hcon
      rw [not_le] at hcon
      have := mul_lt_mul_of_pos_left hcon hn0
      nlinarith
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ∈ P)]
  linarith

end Main

end Iut
