/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.Residual

/-!
# Step (ii): the different of the torsion field

For the tower `F_tpd ⊆ K = F(E[ℓ])` of the Θ-data:

* `Iut.logDifferentDeg_torsionField_eq`: the tower formula
  `log(d_K) = log(d_{F_tpd}) + log N(𝔇_{K/F_tpd})/[K : ℚ]`, from
  `𝔡_{K/ℚ} = 𝔇_{K/F_tpd}·𝔡_{F_tpd/ℚ}𝓞_K` (Mathlib's
  `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`);
* `Iut.log_absNorm_different_div_le`: from the local facts (`Iut.TowerLocalFacts`),
  `log N(𝔇_{K/F_tpd})/[K : ℚ] ≤ log(f_{F_tpd}) + ∑_{p ∈ {2,3,5,ℓ}} (1 + c_p)·log p`.
  Writing `log N(𝔇) = ∑_v ord_v(𝔇)·f_v·log p_v` and `ord_v(𝔇) ≤ (e(v/u) − 1) + e_v c_p`,
  the wild part `∑_v w_v c_p log p_v` is at most `∑_p c_p log p` (`∑_{v ∣ p} w_v = 1`), and
  the tame part, grouped by the places `u` of `F_tpd`, is at most
  `∑_{u} f_u log p_u/[F_tpd : ℚ]` over the `u` below a place ramified in `K/F_tpd`
  (`∑_{v ∣ u} e(v/u) f(v/u) = [K : F_tpd]`); by Néron–Ogg–Shafarevich such `u` has
  `p_u ∈ {2, 3, 5, ℓ}` or is bad, and the bad ones contribute at most `log(f_{F_tpd})`;
* `Iut.logDifferentDeg_torsionField_le`, **Step (ii)**:
  `log(d_K) ≤ log(d_{F_tpd}) + log(f_{F_tpd}) + 2·log ℓ + 21`, since
  `13·log 2 + 3·log 3 + 2·log 5 < 21`.
-/

namespace Iut

open NumberField IsDedekindDomain

universe u

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable {Pr : AdmissiblePrimeData F E Fbar VBad} [NumberField ↥Pr.torsionField]

/-! ### The tower formula -/

/-- **The tower formula for the different degree**:
`log(d_K) = log(d_{F_tpd}) + log N(𝔇_{K/F_tpd})/[K : ℚ]`. -/
theorem logDifferentDeg_torsionField_eq :
    logDifferentDeg ↥Pr.torsionField = logDifferentDeg ↥(tripodalFieldOf F E) +
      Real.log (Ideal.absNorm
        (differentIdeal (𝓞 ↥(tripodalFieldOf F E)) (𝓞 ↥Pr.torsionField))) /
        Module.finrank ℚ ↥Pr.torsionField := by
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := ↥(tripodalFieldOf F E)) (𝒪 := 𝓞 ↥(tripodalFieldOf F E)) (L := ↥Pr.torsionField)
    (𝒪' := 𝓞 ↥Pr.torsionField)
  rw [← absNorm_differentIdeal ↥Pr.torsionField (𝓞 ↥Pr.torsionField),
    ← absNorm_differentIdeal ↥(tripodalFieldOf F E) (𝓞 ↥(tripodalFieldOf F E))] at h
  have hD : Ideal.absNorm (differentIdeal (𝓞 ↥(tripodalFieldOf F E)) (𝓞 ↥Pr.torsionField)) ≠ 0 :=
    absNorm_ne_zero_of_ne_zero _ differentIdeal_ne_bot
  have hT : Ideal.absNorm (differentIdeal ℤ (𝓞 ↥(tripodalFieldOf F E))) ≠ 0 :=
    absNorm_ne_zero_of_ne_zero _ differentIdeal_ne_bot
  have hKT : (Module.finrank ↥(tripodalFieldOf F E) ↥Pr.torsionField : ℝ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  unfold logDifferentDeg
  rw [h, Nat.cast_mul, Nat.cast_pow, Real.log_mul (by exact_mod_cast hD) (by positivity),
    Real.log_pow, ← Module.finrank_mul_finrank ℚ ↥(tripodalFieldOf F E) ↥Pr.torsionField,
    Nat.cast_mul, add_div, add_comm]
  congr 1
  rw [mul_comm ((Module.finrank ↥(tripodalFieldOf F E) ↥Pr.torsionField : ℕ) : ℝ),
    mul_div_mul_right _ _ hKT]

/-! ### The wild and tame parts -/

/-- `∑_{v ∈ s, p_v = p} w_v ≤ 1`. -/
lemma sum_placeWeight_filter_le {K : Type*} [Field K] [NumberField K]
    (s : Finset (FinitePlace K)) (p : ℕ) :
    ∑ v ∈ s.filter (fun v => residueChar v = p), placeWeight K v ≤ 1 := by
  unfold placeWeight
  rw [← Finset.sum_div, div_le_one (by exact_mod_cast (Module.finrank_pos : 0 < _))]
  exact_mod_cast sum_localDeg_filter_le s p

/-- `∑_{u ∈ s, p_u = p} f_u/[T : ℚ] ≤ 1`. -/
lemma sum_inertDeg_div_filter_le {T : Type*} [Field T] [NumberField T]
    (s : Finset (FinitePlace T)) (p : ℕ) :
    ∑ u ∈ s.filter (fun u => residueChar u = p), (inertDeg T u : ℝ) / Module.finrank ℚ T ≤ 1 := by
  rw [← Finset.sum_div, div_le_one (by exact_mod_cast (Module.finrank_pos : 0 < _))]
  exact_mod_cast sum_inertDeg_filter_le s p

/-- The sum of a nonnegative function over a finset is at most the sum over `insert a s`
plus nothing: `∑_{insert a s} g ≤ g a + ∑_s g`. -/
lemma sum_insert_le_of_nonneg {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i, 0 ≤ g i) : ∑ i ∈ insert a s, g i ≤ g a + ∑ i ∈ s, g i := by
  by_cases h : a ∈ s
  · rw [Finset.insert_eq_of_mem h]
    linarith [hg a]
  · rw [Finset.sum_insert h]

/-- The wild part: `∑_{v ∈ s} w_v·c_{p_v}·log p_v ≤ ∑_{p ∈ {2,3,5,ℓ}} c_p·log p`. -/
lemma sum_placeWeight_wildConst_le {K : Type*} [Field K] [NumberField K] (ℓ : ℕ)
    (s : Finset (FinitePlace K)) :
    ∑ v ∈ s, placeWeight K v * (wildConst ℓ (residueChar v) * Real.log (residueChar v)) ≤
      ∑ p ∈ ({2, 3, 5, ℓ} : Finset ℕ), wildConst ℓ p * Real.log p := by
  classical
  set P : Finset ℕ := {2, 3, 5, ℓ} with hP
  have hw : ∀ v : FinitePlace K, 0 ≤ placeWeight K v :=
    fun v => div_nonneg (by positivity) (by positivity)
  have hlog : ∀ p : ℕ, 0 ≤ Real.log p := fun p => Real.log_natCast_nonneg p
  -- restrict to the places of residue characteristic in `P`
  have h1 : ∑ v ∈ s, placeWeight K v * (wildConst ℓ (residueChar v) * Real.log (residueChar v)) =
      ∑ v ∈ s.filter (fun v => residueChar v ∈ P),
        placeWeight K v * (wildConst ℓ (residueChar v) * Real.log (residueChar v)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with h
    · rfl
    · rw [wildConst_eq_zero h]
      simp
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (s := s.filter (fun v => residueChar v ∈ P)) (t := P)
    (g := residueChar) (fun v hv => (Finset.mem_filter.mp hv).2)]
  refine Finset.sum_le_sum fun p _ => ?_
  calc ∑ v ∈ (s.filter (fun v => residueChar v ∈ P)).filter (fun v => residueChar v = p),
        placeWeight K v * (wildConst ℓ (residueChar v) * Real.log (residueChar v))
      = (∑ v ∈ (s.filter (fun v => residueChar v ∈ P)).filter (fun v => residueChar v = p),
          placeWeight K v) * (wildConst ℓ p * Real.log p) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [(Finset.mem_filter.mp hv).2]
    _ ≤ 1 * (wildConst ℓ p * Real.log p) := by
        refine mul_le_mul_of_nonneg_right (sum_placeWeight_filter_le _ p) ?_
        exact mul_nonneg (by positivity) (hlog p)
    _ = wildConst ℓ p * Real.log p := one_mul _

section Tame

variable (Pr)

open scoped Classical in
/-- The tame contribution of the places of `K` over `u`:
`∑_{v ∈ s, u_v = u} (e(v/u) − 1)·f_v·log p_v/[K : ℚ] ≤ f_u·log p_u/[F_tpd : ℚ]`. -/
lemma sum_tame_fiber_le (s : Finset (FinitePlace ↥Pr.torsionField))
    (u : FinitePlace ↥(tripodalFieldOf F E)) :
    ∑ v ∈ s.filter (fun v => placeTpd F E Pr.torsionField v = u),
      ((relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) *
        (inertDeg (↥Pr.torsionField) v * Real.log (residueChar v)) /
          Module.finrank ℚ ↥Pr.torsionField ≤
      (inertDeg ↥(tripodalFieldOf F E) u : ℝ) * Real.log (residueChar u) /
        Module.finrank ℚ ↥(tripodalFieldOf F E) := by
  classical
  set T := ↥(tripodalFieldOf F E)
  set K := ↥Pr.torsionField
  have hKT : Module.finrank ℚ K = Module.finrank ℚ T * Module.finrank T K :=
    (Module.finrank_mul_finrank ℚ T K).symm
  have hT0 : (0 : ℝ) < Module.finrank ℚ T := by exact_mod_cast Module.finrank_pos
  have hTK0 : (0 : ℝ) < Module.finrank T K := by exact_mod_cast Module.finrank_pos
  have hlog : 0 ≤ Real.log (residueChar u) := Real.log_natCast_nonneg _
  -- each summand is at most `e(v/u) f(v/u) · f_u log p_u / [K : ℚ]`
  have hterm : ∀ v ∈ s.filter (fun v => placeTpd F E Pr.torsionField v = u),
      ((relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) *
        (inertDeg K v * Real.log (residueChar v)) / Module.finrank ℚ K ≤
      ((relRamIdx v u * relInertDeg v u : ℕ) : ℝ) *
        (inertDeg T u * Real.log (residueChar u)) / Module.finrank ℚ K := by
    intro v hv
    have hvu : placeTpd F E Pr.torsionField v = u := (Finset.mem_filter.mp hv).2
    have hrc : residueChar v = residueChar u := by rw [← hvu, residueChar_placeTpd]
    have hf : inertDeg K v = inertDeg T u * relInertDeg v u := by
      rw [← hvu]
      exact inertDeg_eq_inertDeg_placeTpd_mul v
    rw [hvu, hrc, hf]
    apply div_le_div_of_nonneg_right _ (by positivity)
    push_cast
    have h1 : ((relRamIdx v u - 1 : ℕ) : ℝ) ≤ relRamIdx v u := by
      exact_mod_cast Nat.sub_le _ _
    have h2 : (0 : ℝ) ≤ relInertDeg v u := by positivity
    have h3 : (0 : ℝ) ≤ inertDeg T u := by positivity
    calc ((relRamIdx v u - 1 : ℕ) : ℝ) * (inertDeg T u * relInertDeg v u * Real.log (residueChar u))
        ≤ (relRamIdx v u : ℝ) * (inertDeg T u * relInertDeg v u * Real.log (residueChar u)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (relRamIdx v u : ℝ) * relInertDeg v u * (inertDeg T u * Real.log (residueChar u)) := by
          ring
  refine (Finset.sum_le_sum hterm).trans ?_
  -- the sum over the places over `u` of `e(v/u) f(v/u)` is `[K : T]`
  rw [← Finset.sum_div, ← Finset.sum_mul]
  have hsub : s.filter (fun v => placeTpd F E Pr.torsionField v = u) ⊆ placesOver (K := K) u := by
    intro v hv
    rw [mem_placesOver, ← (Finset.mem_filter.mp hv).2]
    exact liesOver_placeTpd v
  have hle : ∑ v ∈ s.filter (fun v => placeTpd F E Pr.torsionField v = u),
      ((relRamIdx v u * relInertDeg v u : ℕ) : ℝ) ≤ Module.finrank T K := by
    rw [← sum_placesOver_relLocalDeg (K := K) u, Nat.cast_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  calc (∑ v ∈ s.filter (fun v => placeTpd F E Pr.torsionField v = u),
        ((relRamIdx v u * relInertDeg v u : ℕ) : ℝ)) *
        (inertDeg T u * Real.log (residueChar u)) / Module.finrank ℚ K
      ≤ (Module.finrank T K : ℝ) * (inertDeg T u * Real.log (residueChar u)) /
          Module.finrank ℚ K := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (inertDeg T u : ℝ) * Real.log (residueChar u) / Module.finrank ℚ T := by
        rw [hKT, Nat.cast_mul, mul_comm ((Module.finrank ℚ T : ℕ) : ℝ),
          mul_div_mul_left _ _ hTK0.ne']

end Tame

/-! ### The bound on the different of `K/F_tpd` -/

open scoped Classical in
/-- The bad places of `F_tpd` are finitely many, given the finiteness of the bad places of
`F`. -/
lemma isBadTpdOf_finite (hfin : (badPlacesOver F E VBad).Finite) :
    {u : FinitePlace ↥(tripodalFieldOf F E) | IsBadTpdOf F E VBad u}.Finite := by
  refine (hfin.image (placeUnder (k := ↥(tripodalFieldOf F E)))).subset ?_
  rintro u ⟨w, hw, hwu⟩
  exact ⟨w, hw, (eq_placeUnder_of_liesOver hwu).symm⟩

/-- `∑_{u ∈ s bad} f_u log p_u/[F_tpd : ℚ] ≤ log(f_{F_tpd})`. -/
lemma sum_bad_inertDeg_div_le (hfin : (badPlacesOver F E VBad).Finite)
    (s : Finset (FinitePlace ↥(tripodalFieldOf F E))) (hs : ∀ u ∈ s, IsBadTpdOf F E VBad u) :
    ∑ u ∈ s, (inertDeg ↥(tripodalFieldOf F E) u : ℝ) * Real.log (residueChar u) /
      Module.finrank ℚ ↥(tripodalFieldOf F E) ≤ logConductorDegOf F E VBad := by
  classical
  unfold logConductorDegOf
  rw [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  set B := (isBadTpdOf_finite hfin).toFinset with hB
  have hsB : s ⊆ B := fun u hu => (Set.Finite.mem_toFinset _).mpr (hs u hu)
  rw [finsum_eq_sum_of_support_subset (s := B)]
  · calc ∑ u ∈ s, (inertDeg ↥(tripodalFieldOf F E) u : ℝ) * Real.log (residueChar u)
        = ∑ u ∈ s, (if IsBadTpdOf F E VBad u then
            Real.log (Ideal.absNorm u.maximalIdeal.asIdeal) else 0) := by
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [if_pos (hs u hu), absNorm_eq_pow_residueChar, Nat.cast_pow, Real.log_pow]
      _ ≤ ∑ u ∈ B, (if IsBadTpdOf F E VBad u then
            Real.log (Ideal.absNorm u.maximalIdeal.asIdeal) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsB fun u _ _ => ?_
          split_ifs
          · exact Real.log_nonneg (by exact_mod_cast
              (NumberField.HeightOneSpectrum.one_lt_absNorm u.maximalIdeal).le)
          · exact le_rfl
  · intro u hu
    rw [Function.mem_support] at hu
    rw [Finset.mem_coe, hB, Set.Finite.mem_toFinset]
    by_contra h
    exact hu (if_neg h)

variable (Pr)

/-- **The bound on the different of `K/F_tpd`** from the local facts:
`log N(𝔇_{K/F_tpd})/[K : ℚ] ≤ log(f_{F_tpd}) + ∑_{p ∈ {2,3,5,ℓ}} (1 + c_p)·log p`. -/
theorem log_absNorm_different_div_le (H : TowerLocalFacts E VBad Pr)
    (hfin : (badPlacesOver F E VBad).Finite) :
    Real.log (Ideal.absNorm
        (differentIdeal (𝓞 ↥(tripodalFieldOf F E)) (𝓞 ↥Pr.torsionField))) /
        Module.finrank ℚ ↥Pr.torsionField ≤
      logConductorDegOf F E VBad +
        ∑ p ∈ ({2, 3, 5, Pr.ℓ} : Finset ℕ), (1 + wildConst Pr.ℓ p) * Real.log p := by
  classical
  -- the termwise bound `ord_v(𝔇) ≤ (e(v/u) − 1) + e_v c_p`
  have hord : ∀ v : FinitePlace ↥Pr.torsionField,
      (ordAt (differentIdeal (𝓞 ↥(tripodalFieldOf F E)) (𝓞 ↥Pr.torsionField)) v : ℝ) ≤
      ((relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) +
        ramIdx (↥Pr.torsionField) v * wildConst Pr.ℓ (residueChar v) := by
    intro v
    have h1 := H.ordAt_different_le v
    have h2 := relRamIdx_pos (liesOver_placeTpd (F := F) (E := E) v)
    have h3 : ordAt (differentIdeal (𝓞 ↥(tripodalFieldOf F E)) (𝓞 ↥Pr.torsionField)) v ≤
        (relRamIdx v (placeTpd F E Pr.torsionField v) - 1) +
        ramIdx (↥Pr.torsionField) v * wildConst Pr.ℓ (residueChar v) := by omega
    exact_mod_cast h3
  set T := ↥(tripodalFieldOf F E)
  set K := ↥Pr.torsionField
  set 𝔇 := differentIdeal (𝓞 T) (𝓞 K) with h𝔇
  set P : Finset ℕ := {2, 3, 5, Pr.ℓ} with hP
  set s := (ordAt_support_finite 𝔇).toFinset with hs_def
  have hs : ∀ v, ordAt 𝔇 v ≠ 0 → v ∈ s := fun v hv => (Set.Finite.mem_toFinset _).mpr hv
  have hK0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hlog : ∀ p : ℕ, 0 ≤ Real.log p := fun p => Real.log_natCast_nonneg p
  rw [log_absNorm_eq_sum_ordAt 𝔇 differentIdeal_ne_bot s hs, Finset.sum_div]
  -- split into the tame and the wild part
  have hsplit : ∑ v ∈ s, (ordAt 𝔇 v : ℝ) * (inertDeg K v * Real.log (residueChar v)) /
      Module.finrank ℚ K ≤
      ∑ v ∈ s, ((relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) *
        (inertDeg K v * Real.log (residueChar v)) / Module.finrank ℚ K +
      ∑ v ∈ s, placeWeight K v * (wildConst Pr.ℓ (residueChar v) * Real.log (residueChar v)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have hfl : 0 ≤ (inertDeg K v : ℝ) * Real.log (residueChar v) := by
      exact mul_nonneg (by positivity) (hlog _)
    have hw : placeWeight K v * (wildConst Pr.ℓ (residueChar v) * Real.log (residueChar v)) =
        (ramIdx K v * wildConst Pr.ℓ (residueChar v) : ℝ) *
          (inertDeg K v * Real.log (residueChar v)) / Module.finrank ℚ K := by
      unfold placeWeight localDeg
      push_cast
      ring
    rw [hw, ← add_div, ← add_mul]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hord v) hfl) hK0.le
  refine hsplit.trans ?_
  -- the wild part
  have hwild := sum_placeWeight_wildConst_le (K := K) Pr.ℓ s
  -- the tame part: only the places ramified in `K/F_tpd` contribute
  set s' := s.filter (fun v => relRamIdx v (placeTpd F E Pr.torsionField v) ≠ 1) with hs'
  have htame1 : ∑ v ∈ s, ((relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) *
      (inertDeg K v * Real.log (residueChar v)) / Module.finrank ℚ K =
      ∑ v ∈ s', ((relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) *
      (inertDeg K v * Real.log (residueChar v)) / Module.finrank ℚ K := by
    rw [hs', Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with h
    · rfl
    · rw [not_not] at h
      rw [h]
      simp
  -- group by the place of `F_tpd` below
  set t := s'.image (placeTpd F E Pr.torsionField) with ht
  have htame2 : ∑ v ∈ s', ((relRamIdx v (placeTpd F E Pr.torsionField v) - 1 : ℕ) : ℝ) *
      (inertDeg K v * Real.log (residueChar v)) / Module.finrank ℚ K ≤
      ∑ u ∈ t, (inertDeg T u : ℝ) * Real.log (residueChar u) / Module.finrank ℚ T := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s') (t := t) (g := placeTpd F E Pr.torsionField)
      (fun v hv => Finset.mem_image_of_mem _ hv)]
    exact Finset.sum_le_sum fun u _ => sum_tame_fiber_le Pr s' u
  -- the places of `t` have residue characteristic in `P` or are bad
  have htP : ∀ u ∈ t, residueChar u ∉ P → IsBadTpdOf F E VBad u := by
    intro u hu hp
    rw [ht, Finset.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [hs', Finset.mem_filter] at hv
    by_contra hbad
    rw [residueChar_placeTpd] at hp
    exact hv.2 (H.relRamIdx_eq_one v hp hbad)
  have hg : ∀ u : FinitePlace T,
      0 ≤ (inertDeg T u : ℝ) * Real.log (residueChar u) / Module.finrank ℚ T :=
    fun u => div_nonneg (mul_nonneg (by positivity) (hlog _)) (by positivity)
  have htame3 : ∑ u ∈ t, (inertDeg T u : ℝ) * Real.log (residueChar u) / Module.finrank ℚ T ≤
      ∑ p ∈ P, Real.log p + logConductorDegOf F E VBad := by
    rw [← Finset.sum_filter_add_sum_filter_not t (fun u => residueChar u ∈ P)]
    refine add_le_add ?_ ?_
    · rw [← Finset.sum_fiberwise_of_maps_to (s := t.filter (fun u => residueChar u ∈ P)) (t := P)
        (g := residueChar) (fun u hu => (Finset.mem_filter.mp hu).2)]
      refine Finset.sum_le_sum fun p _ => ?_
      calc ∑ u ∈ (t.filter (fun u => residueChar u ∈ P)).filter (fun u => residueChar u = p),
            (inertDeg T u : ℝ) * Real.log (residueChar u) / Module.finrank ℚ T
          = (∑ u ∈ (t.filter (fun u => residueChar u ∈ P)).filter (fun u => residueChar u = p),
              (inertDeg T u : ℝ) / Module.finrank ℚ T) * Real.log p := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun u hu => ?_
            rw [(Finset.mem_filter.mp hu).2]
            ring
        _ ≤ 1 * Real.log p :=
            mul_le_mul_of_nonneg_right (sum_inertDeg_div_filter_le _ p) (hlog p)
        _ = Real.log p := one_mul _
    · exact sum_bad_inertDeg_div_le hfin _ fun u hu =>
        htP u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2
  have hfinal : ∑ p ∈ P, Real.log p + ∑ p ∈ P, wildConst Pr.ℓ p * Real.log p =
      ∑ p ∈ P, (1 + wildConst Pr.ℓ p) * Real.log p := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [htame1]
  linarith

/-! ### The numerical constant -/

/-- `∑_{p ∈ {2,3,5,ℓ}} (1 + c_p)·log p ≤ 13·log 2 + 3·log 3 + 2·log 5 + 2·log ℓ` for `ℓ ≥ 5`. -/
lemma sum_one_add_wildConst_le (ℓ : ℕ) (hℓ : 5 ≤ ℓ) :
    ∑ p ∈ ({2, 3, 5, ℓ} : Finset ℕ), (1 + wildConst ℓ p) * Real.log p ≤
      13 * Real.log 2 + 3 * Real.log 3 + 2 * Real.log 5 + 2 * Real.log ℓ := by
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  rcases eq_or_ne ℓ 5 with rfl | h5
  · have h : ({2, 3, 5, 5} : Finset ℕ) = {2, 3, 5} := by decide
    rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [wildConst]
    norm_num
    linarith
  · have h2 : ℓ ≠ 2 := by omega
    have h3 : ℓ ≠ 3 := by omega
    rw [Finset.sum_insert (by simp [h2.symm]), Finset.sum_insert (by simp [h3.symm]),
      Finset.sum_insert (by simp [h5.symm]), Finset.sum_singleton]
    simp only [wildConst, h2, h3, h5, h2.symm, h3.symm, h5.symm]
    norm_num
    linarith

/-- `13·log 2 + 3·log 3 + 2·log 5 ≤ 21`. -/
lemma constant_le_21 : 13 * Real.log 2 + 3 * Real.log 3 + 2 * Real.log 5 ≤ 21 := by
  have h2 := Real.log_two_lt_d9
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num), show ((2 : ℝ) ^ (2 : ℝ)) = 4 by norm_num]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h5 : Real.log 5 ≤ 3 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num), show ((2 : ℝ) ^ (3 : ℝ)) = 8 by norm_num]
    exact Real.log_le_log (by norm_num) (by norm_num)
  linarith

/-- **Step (ii)**: `log(d_K) ≤ log(d_{F_tpd}) + log(f_{F_tpd}) + 2·log ℓ + 21`. -/
theorem logDifferentDeg_torsionField_le (H : TowerLocalFacts E VBad Pr)
    (hfin : (badPlacesOver F E VBad).Finite) :
    logDifferentDeg ↥Pr.torsionField ≤ logDifferentDeg ↥(tripodalFieldOf F E) +
      logConductorDegOf F E VBad + 2 * Real.log Pr.ℓ + 21 := by
  rw [logDifferentDeg_torsionField_eq]
  have h1 := log_absNorm_different_div_le Pr H hfin
  have h2 := sum_one_add_wildConst_le Pr.ℓ Pr.five_le
  have h3 := constant_le_21
  linarith

end Iut
