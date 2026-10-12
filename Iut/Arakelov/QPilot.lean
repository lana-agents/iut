/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Arakelov.Container

/-!
# The `q`-pilot divisor and the left-hand side of Corollary 3.12 in Arakelov terms

IUT III, Definition 3.8(i) (and the introduction of IUT III) calls the arithmetic divisor
determined by the zero locus of the `q_v`, `v ∈ V^bad`, in the global realified Frobenioid
`F^⊛_mod` the **`q`-pilot object**, and that of the theta values `{q_v^{j²}}_{j=1,…,ℓ*}` the
**`Θ`-pilot object**. IUT III, Corollary 3.12 compares log-volumes of the `q`-pilot and
theta-pilot regions; its left-hand side `−|log(q)|` is the log-volume of the `q`-pilot region
`{q_v·𝒪_v}`, which by IUT III, Proposition 3.9(iii) is minus the (normalized) degree of the
**`q`-pilot divisor** — the arithmetic divisor of the `2ℓ`-th roots `q_v = q^{1/2ℓ}` of the
Tate parameters (IUT I, Example 3.2(iv); IUT III, Proposition 3.10; IUT IV, proof of
Theorem 1.10: "`|log(q)|` … is equal to `(1/2ℓ)·log(q)`"). This file makes this precise for
the concrete objects of the repository.

## Contents

* `qDivisor D`: the arithmetic line bundle on `F` with idelic description the Tate parameters
  `q_w` at the bad places `w ∈ V(F)^bad` (trivial elsewhere); **`degNorm_qDivisor`**: its
  normalized Arakelov degree is `log(q)` (`QPilotData.logQ`, the `q`-divisor degree of
  `Iut/Cor312/LeftHandSide.lean`);
* **`lhs_eq_neg_degNorm_qDivisor`**: `(qPilot D).lhs = −(1/2ℓ)·deg(q-divisor)/[F : ℚ]`;
* `qPowDatum D m`: the idelic datum `(q_v^m)_v` on the `ℓ`-torsion field `K` (`F_mod`-rational,
  `isModInvariant_qPowDatum`, from `ord_p(q_v) = q-deg(v|_{F_mod})/2ℓ`, `ordp_qroot_placeUnder`);
  `qPilotBundle D` (`m = 1`, the `q`-pilot divisor on `K`) and `thetaBundle D j` (`m = j²`, the
  divisor of the theta value `q^{j²}`);
* **`degNorm_qPowDatum`**: `deg(q^m)/[K : ℚ] = m·|log(q)|`; in particular
  `degNorm_qPilotBundle_eq : deg(q-pilot on K)/[K : ℚ] = (1/2ℓ)·deg(q-divisor on F)/[F : ℚ]`
  (base-change invariance of the normalized degree);
* `pow_eq_scale`: the regions `pow D e lab S` of `Iut/Wall/QPilotRegion.lean` are scalings by
  `qPowDatum`;
* **`logVol_qRegion_eq_neg_degNorm`**: `log-vol(qRegion D) = −deg(q-pilot)/[K : ℚ]`
  `= −(1/2ℓ)·deg(q-divisor)/[F : ℚ] = (qPilot D).lhs` (IUT III, Proposition 3.9(iii) and
  Corollary 3.12);
* **`logVol_lgp_integral_eq_degNorm`**: the theta-value version, `log-vol(LGP·O) =
  −(1/ℓ*)·Σ_{j=1}^{ℓ*} deg(q^{j²})/[K : ℚ]` (the `ℓ*`-average of the degrees of the theta-value
  divisors, IUT III, Proposition 3.4 and Corollary 3.12's procession normalization);
  `logVol_pow_integral_eq_degNorm` for general exponents.
-/

namespace Iut

namespace Arakelov

open NumberField Wall

universe u

variable (D : InitialThetaData.{u})

/-! ### The `q`-divisor on `F` -/

open scoped Classical in
/-- **The `q`-divisor of the Θ-data** as an arithmetic line bundle on `F`: the Tate parameter
`q_w` at each bad place `w ∈ V(F)^bad`, `1` at the other finite places, trivial metrics at the
archimedean places (IUT I, Example 3.2(iv)). -/
noncomputable def qDivisor : ArithLineBundle D.F where
  fin w := if hw : w ∈ badPlacesOver D.F D.E D.VBad then
    ((D.tateParam w hw).q : localCompletion w) else 1
  fin_ne_zero w := by
    split_ifs
    · exact Units.ne_zero _
    · exact one_ne_zero
  finite_fin := D.bad_finite.subset fun w hw => by
    by_contra h
    exact hw (show ‖_‖ = 1 by rw [dif_neg h, norm_one])
  inf _ := 1
  inf_pos _ := one_pos

/-- **The normalized Arakelov degree of the `q`-divisor is `log(q)`**:
`deg(q-divisor)/[F : ℚ] = Σ_{w ∈ V(F)^bad} (f_w/[F : ℚ])·ord_w(q_w)·log p_w`. -/
theorem degNorm_qDivisor : (qDivisor D).degNorm = D.qPilot.logQ := by
  classical
  rw [ArithLineBundle.degNorm_eq]
  have hinf : ∑ v, -(infPlaceWeight D.F v * Real.log ((qDivisor D).inf v)) = 0 := by
    simp [qDivisor]
  rw [hinf, add_zero]
  have hsub : Function.support (fun w => placeWeight D.F w *
      (ordp D.F w ((qDivisor D).fin w) * Real.log (residueChar w))) ⊆ ↑D.qPilot.badFinset := by
    intro w hw
    by_contra h
    apply hw
    have h' : w ∉ badPlacesOver D.F D.E D.VBad := by
      rw [← D.qPilot.badFinset_spec]
      exact h
    simp [qDivisor, dif_neg h', ordp]
  rw [finsum_eq_sum_of_support_subset _ hsub, QPilotData.logQ,
    ← Finset.sum_attach D.qPilot.badFinset]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hw := D.qPilot.mem_bad w.2
  have hq : ordp D.F w.1 ((qDivisor D).fin w.1) = (D.qOrder w.1 hw : ℝ) / ramIdx D.F w.1 := by
    simp only [qDivisor, dif_pos hw]
    rw [ordp_tateParameter _ (isUniformizer_unifAt w.1), ← D.qOrder_eq_orderNat]
  rw [hq]
  have he : (ramIdx D.F w.1 : ℝ) ≠ 0 := by exact_mod_cast (ramIdx_pos' w.1).ne'
  change _ = (inertDeg D.F w.1 : ℝ) / Module.finrank ℚ D.F * _ * _
  unfold placeWeight localDeg
  push_cast
  field_simp

/-- **The left-hand side of the Corollary 3.12 variant in Arakelov terms**:
`−|log(q)| = −(1/2ℓ)·deg(q-divisor)/[F : ℚ]`. -/
theorem lhs_eq_neg_degNorm_qDivisor :
    (concreteVariantData D).qPilot.lhs = -((qDivisor D).degNorm / (2 * D.ℓ)) := by
  rw [degNorm_qDivisor]
  rfl

/-! ### The `q`-pilot divisor on `K` -/

/-- `ord_p(q_v) = q-deg(v|_{F_mod})/2ℓ` at **every** finite place `v` of `K` (not only at the
places of the valuation section). -/
lemma ordp_qroot_placeUnder (v : FinitePlace D.Kt) :
    ordp D.Kt v (D.qroot v) = D.qDeg (placeUnder (k := D.Fmod) v) / (2 * D.ℓ) := by
  classical
  have hvw : FinitePlace.LiesOver v (placeUnder (k := D.Fmod) v) := liesOver_placeUnder v
  by_cases hw : placeUnder (k := D.Fmod) v ∈ D.VBad
  · set u : FinitePlace D.F := placeUnder (k := D.F) v with hu_def
    have huw : FinitePlace.LiesOver u (placeUnder (k := D.Fmod) v) := by
      haveI : v.maximalIdeal.asIdeal.LiesOver
          (placeUnder (k := D.Fmod) v).maximalIdeal.asIdeal := hvw
      haveI : v.maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal := liesOver_placeUnder v
      exact Ideal.LiesOver.tower_bot v.maximalIdeal.asIdeal _ _
    have hu : u ∈ badPlacesOver D.F D.E D.VBad := ⟨_, hw, huw⟩
    rw [D.ordp_qroot v u (liesOver_placeUnder _) hu]
    have h := D.qOrder_div_ramIdx u hu
    rw [← eq_placeUnder_of_liesOver huw] at h
    rw [← h]
    have he : (ramIdx D.F u : ℝ) ≠ 0 := by exact_mod_cast (ramIdx_pos' u).ne'
    have hℓ : (D.ℓ : ℝ) ≠ 0 := by
      have : (5 : ℝ) ≤ D.ℓ := by exact_mod_cast D.prime.five_le
      positivity
    field_simp
  · have hnot : ¬ IsBadK D v := by
      rintro ⟨w', hw', hvw'⟩
      rw [eq_placeUnder_of_liesOver hvw'] at hw'
      exact hw hw'
    rw [InitialThetaData.qroot, qrootOf_of_not D hnot]
    unfold InitialThetaData.qDeg
    rw [if_neg hw]
    simp [ordp, norm_one]

/-- **The idelic datum `(q_v^m)_v`** on the `ℓ`-torsion field (`q_v` the `2ℓ`-th root of the
Tate parameter, `1` away from the bad places). -/
noncomputable def qPowDatum (m : ℕ) : ScalingDatum D where
  elt w := D.qroot w ^ m
  elt_ne_zero w := pow_ne_zero _ (D.qroot_ne_zero w)
  chars := D.badChars
  elt_eq_one w hw := by rw [D.qroot_eq_one w hw, one_pow]

/-- The capsule-wise data `(q_v^{e(i)})_v`. -/
noncomputable def qPow (e : Fin (nC D) → ℕ) (i : Fin (nC D)) : ScalingDatum D :=
  qPowDatum D (e i)

/-- **The regions `pow D e lab S` of `Iut/Wall/QPilotRegion.lean` are scalings by `q^{e(i)}`.** -/
theorem pow_eq_scale (e : Fin (nC D) → ℕ) (lab : ∀ i, InitialThetaData.Lab (nC D) i)
    (S : Region D) : pow D e lab S = scale D (qPow D e) lab S :=
  rfl

lemma ordp_qPowDatum (m : ℕ) (v : FinitePlace D.Kt) :
    ordp D.Kt v ((qPowDatum D m).elt v) =
      m * (D.qDeg (placeUnder (k := D.Fmod) v) / (2 * D.ℓ)) := by
  change ordp D.Kt v (D.qroot v ^ m) = _
  rw [ordp_pow', ordp_qroot_placeUnder]

/-- `(q_v^m)_v` is `F_mod`-rational. -/
theorem isModInvariant_qPowDatum (m : ℕ) : (qPowDatum D m).IsModInvariant := by
  intro v v' h
  rw [ordp_qPowDatum, ordp_qPowDatum, h]

/-- The contribution of `p` to the section-average degree of `q^m` is `m·log(q_p)/2ℓ`. -/
lemma sectDegAt_qPowDatum (m : ℕ) (p : Nat.Primes) :
    (qPowDatum D m).sectDegAt p = m * ((concreteVariantData D).logQAt p / (2 * D.ℓ)) := by
  have hℓ : (D.ℓ : ℝ) ≠ 0 := by
    have : (5 : ℝ) ≤ D.ℓ := by exact_mod_cast D.prime.five_le
    positivity
  rw [InitialThetaData.logQAt_eq_sect, ScalingDatum.sectDegAt]
  have h : ∀ u : LocalTheory.Fiber D.Fmod (.finite p),
      LocalTheory.weight D.Fmod _ u * ordp D.Kt (LocalTheory.sectPlace D.placeSect u)
        ((qPowDatum D m).elt (LocalTheory.sectPlace D.placeSect u)) =
      m * (LocalTheory.weight D.Fmod _ u * ordp D.Kt (LocalTheory.sectPlace D.placeSect u)
        (D.qroot (LocalTheory.sectPlace D.placeSect u))) := by
    intro u
    change _ * ordp D.Kt _ (D.qroot _ ^ m) = _
    rw [ordp_pow']
    ring
  rw [Finset.sum_congr rfl fun u _ => h u, ← Finset.mul_sum]
  field_simp

/-- **The section-average degree of `q^m` is `m·|log(q)|`.** -/
theorem sectDeg_qPowDatum (m : ℕ) : (qPowDatum D m).sectDeg = m * D.qPilot.absLogQ := by
  classical
  unfold ScalingDatum.sectDeg
  simp only [sectDegAt_qPowDatum]
  rw [← Finset.mul_sum, ← Finset.sum_div,
    ScalingDatum.sum_primes _ (fun q : ℕ => (concreteVariantData D).logQAt q)]
  congr 1
  rw [QPilotData.absLogQ]
  congr 1
  refine (concreteVariantData D).sum_logQAt fun w hw => ?_
  refine Finset.mem_filter.mpr ⟨?_, residueChar_prime w⟩
  exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

/-- **The normalized Arakelov degree of `q^m` on `K` is `m·|log(q)|`.** -/
theorem degNorm_qPowDatum (m : ℕ) :
    (qPowDatum D m).toBundle.degNorm = m * D.qPilot.absLogQ := by
  rw [ScalingDatum.degNorm_toBundle _ (isModInvariant_qPowDatum D m), sectDeg_qPowDatum]

/-- **The `q`-pilot divisor on `K`**: the arithmetic line bundle of `(q_v)_v`. -/
noncomputable def qPilotBundle : ArithLineBundle D.Kt := (qPowDatum D 1).toBundle

/-- **The divisor of the theta value `q^{j²}`** on `K`. -/
noncomputable def thetaBundle (j : ℕ) : ArithLineBundle D.Kt := (qPowDatum D (j ^ 2)).toBundle

/-- **`deg(q-pilot)/[K : ℚ] = |log(q)|`.** -/
theorem degNorm_qPilotBundle : (qPilotBundle D).degNorm = D.qPilot.absLogQ := by
  rw [qPilotBundle, degNorm_qPowDatum, Nat.cast_one, one_mul]

/-- **Base change of the `q`-divisor**: `deg(q-pilot on K)/[K : ℚ] =
(1/2ℓ)·deg(q-divisor on F)/[F : ℚ]` (`q_v^{2ℓ} = q_w`). -/
theorem degNorm_qPilotBundle_eq : (qPilotBundle D).degNorm = (qDivisor D).degNorm / (2 * D.ℓ) := by
  rw [degNorm_qPilotBundle, degNorm_qDivisor]
  rfl

theorem degNorm_thetaBundle (j : ℕ) :
    (thetaBundle D j).degNorm = (j : ℝ) ^ 2 * D.qPilot.absLogQ := by
  rw [thetaBundle, degNorm_qPowDatum]
  push_cast
  rfl

/-! ### The log-volumes -/

/-- **IUT III, Proposition 3.9(iii) for the `q`-pilot**: `log-vol({q_v·𝒪_v}) = −deg(q-pilot)/[K : ℚ]
= −(1/2ℓ)·deg(q-divisor)/[F : ℚ]`, and this is the left-hand side `(qPilot D).lhs` of the
Corollary 3.12 variant. -/
theorem logVol_qRegion_eq_neg_degNorm :
    logVol D (qRegion D) = -(qPilotBundle D).degNorm ∧
      -(qPilotBundle D).degNorm = -((qDivisor D).degNorm / (2 * D.ℓ)) ∧
      -((qDivisor D).degNorm / (2 * D.ℓ)) = (concreteVariantData D).qPilot.lhs := by
  refine ⟨?_, by rw [degNorm_qPilotBundle_eq], (lhs_eq_neg_degNorm_qDivisor D).symm⟩
  rw [qRegion, pow_eq_scale]
  exact logVol_scaleConst_eq_neg_degNorm D (labOne D) (qPowDatum D 1)
    (isModInvariant_qPowDatum D 1)

/-- The log-volume of `pow D e lab O` as minus the capsule-average of the normalized degrees
of the divisors of `q^{e(i)}`. -/
theorem logVol_pow_integral_eq_degNorm (e : Fin (nC D) → ℕ)
    (lab : ∀ i, InitialThetaData.Lab (nC D) i) :
    logVol D (pow D e lab (integralRegion D)) =
      -(∑ i, (qPowDatum D (e i)).toBundle.degNorm) / nC D := by
  rw [pow_eq_scale]
  exact logVol_scale_integral_eq_degNorm D _ lab fun i => isModInvariant_qPowDatum D (e i)

/-- **The theta values**: `log-vol(LGP·O) = −(1/ℓ*)·Σ_{j=1}^{ℓ*} deg(q^{j²})/[K : ℚ]`, the
`ℓ*`-average over the capsules of minus the degrees of the theta-value divisors; in terms of the
`q`-divisor on `F`, `−(1/ℓ*)·Σ_j j²·(1/2ℓ)·deg(q-divisor)/[F : ℚ]`. -/
theorem logVol_lgp_integral_eq_degNorm :
    logVol D (lgp D (integralRegion D)) =
        -(∑ i : Fin (nC D), (thetaBundle D (i.1 + 1)).degNorm) / nC D ∧
      logVol D (lgp D (integralRegion D)) =
        -(∑ i : Fin (nC D), ((i.1 + 1 : ℕ) : ℝ) ^ 2) / nC D *
          ((qDivisor D).degNorm / (2 * D.ℓ)) := by
  have h1 : logVol D (lgp D (integralRegion D)) =
      -(∑ i : Fin (nC D), (thetaBundle D (i.1 + 1)).degNorm) / nC D := by
    rw [lgp_eq_pow, logVol_pow_integral_eq_degNorm]
    rfl
  refine ⟨h1, ?_⟩
  rw [h1]
  simp only [degNorm_thetaBundle, ← degNorm_qPilotBundle, degNorm_qPilotBundle_eq,
    ← Finset.sum_mul]
  ring

end Arakelov

end Iut
