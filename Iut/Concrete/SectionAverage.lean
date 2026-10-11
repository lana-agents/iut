/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.Invariants
import Iut.Concrete.GaloisPlaces
import Iut.Concrete.TorsionFieldGalois

/-!
# Averages over the valuation section `V ≅ V_mod` (IUT III, Remark 3.1.1(ii))

The direct summands of the tensor packets of the concrete container are indexed by the places
of the valuation section `V ⊆ V(K)`, `V ≅ V_mod` (IUT III, Propositions 3.1, 3.2, Theorem 3.11
(Ind2)), with the weights `[(F_mod)_w : ℚ_p]/[F_mod : ℚ]` of Remark 3.1.1(ii). The local
estimates of IUT IV, Theorem 1.10, Step (v), average over these summands two local quantities,
which are identified here with the global invariants of Theorem 1.10:

* `Iut.sum_placeWeight_placeUnder`: for number fields `k ⊆ K`, the `[K_v : ℚ_p]/[K : ℚ]`-average
  over the places `v ∣ p` of `K` of a function of the place of `k` below `v` is the
  `[k_w : ℚ_p]/[k : ℚ]`-average over the places `w ∣ p` of `k` (from
  `∑_{v ∣ w} e_v f_v = [K : k]·e_w f_w`);
* **the different term** `InitialThetaData.logDK_sect`: `log(d^K_p)` (the contribution of `p` to
  the normalized degree of the different of `K`, averaged over *all* places of `K` over `p`) is
  the `V`-average `∑_{w ∣ p} [(F_mod)_w : ℚ_p]/[F_mod : ℚ]·d_{v(w)}·log p` of the different
  exponents at the places `v(w) ∈ V`, because `d_v` is constant on the places of `K` over a place
  of `F_mod` (`Iut.differentExponent_eq_of_liesOver`) for `K/F_mod` Galois (IUT I,
  Remark 3.1.5);
* **the `q`-degree** `InitialThetaData.logQAt_eq_sect`: `log(q_p)` (the normalized degree of
  the `q`-divisor of `F` at `p`) is `2ℓ·log p` times the `V`-average of `ord_p(q_v)`, because
  `ord_p(q_v) = −ord_p(j(E))/2ℓ` at the places over `V_mod^bad` (`‖q‖ = ‖j(E)‖⁻¹`,
  `TateCurvesTheta.TateParameter.norm_tateJ`) depends only on the place of `F_mod` below `v`,
  as `j(E) ∈ F_mod` (`InitialThetaData.ordp_qroot_sect`, `InitialThetaData.qOrder_div_ramIdx`).
-/

namespace Iut

open NumberField

universe u

/-! ### Averages of functions of the place below -/

section Average

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

open scoped Classical in
/-- **Averages of functions of the place below**: for `c` a function on the places of `k`,
`∑_{v ∣ p} ([K_v : ℚ_p]/[K : ℚ])·c(v|_k) = ∑_{w ∣ p} ([k_w : ℚ_p]/[k : ℚ])·c(w)`. -/
theorem sum_placeWeight_placeUnder (p : ℕ) [Fintype {v : FinitePlace K // residueChar v = p}]
    [Fintype {w : FinitePlace k // residueChar w = p}] (c : FinitePlace k → ℝ) :
    ∑ v : {v : FinitePlace K // residueChar v = p}, placeWeight K v.1 * c (placeUnder v.1) =
      ∑ w : {w : FinitePlace k // residueChar w = p}, placeWeight k w.1 * c w.1 := by
  have hfin : {w : FinitePlace k | residueChar w = p}.Finite :=
    Set.finite_coe_iff.mp (Finite.of_fintype {w : FinitePlace k // residueChar w = p})
  have h := sum_placeWeight_mul (F := k) (K := K) p {w | residueChar w = p} hfin.toFinset
    hfin.coe_toFinset (fun w => c w * ramIdx k w)
    (fun v => if residueChar v = p then c (placeUnder v) else 0)
    (fun v w hvw hw => by
      have hw' : residueChar w = p := hw
      have hv : residueChar v = p := (residueChar_eq_of_liesOver hvw).trans hw'
      have he : (ramIdx k w : ℝ) ≠ 0 := by exact_mod_cast (ramIdx_pos' w).ne'
      simp only [if_pos hv, ← eq_placeUnder_of_liesOver hvw]
      field_simp)
    (fun v hv => by
      rw [if_neg]
      intro hvp
      exact hv (placeUnder v)
        ((residueChar_eq_of_liesOver (liesOver_placeUnder v)).symm.trans hvp)
        (liesOver_placeUnder v))
  have h1 : ∑ v : {v : FinitePlace K // residueChar v = p}, placeWeight K v.1 * c (placeUnder v.1) =
      ∑ v : {v : FinitePlace K // residueChar v = p}, placeWeight K v.1 *
        (if residueChar v.1 = p then c (placeUnder v.1) else 0) :=
    Finset.sum_congr rfl fun v _ => by rw [if_pos v.2]
  rw [h1, h, Finset.filter_true_of_mem (p := fun w => residueChar w = p)
    (fun w hw => (hfin.mem_toFinset.mp hw : residueChar w = p))]
  rw [Finset.sum_subtype hfin.toFinset (p := fun w => residueChar w = p)
    (fun w => hfin.mem_toFinset)]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold placeWeight localDeg
  push_cast
  ring

/-- **Averages over the fibers of functions of the place below**, in the weights of the
container: `∑_{v ∣ p} w_v·c(v|_k) = ∑_{w ∣ p} w_w·c(w)`. -/
theorem LocalTheory.sum_weight_placeUnder (p : Nat.Primes) (c : FinitePlace k → ℝ) :
    ∑ v : LocalTheory.Fiber K (.finite p), LocalTheory.weight K _ v *
        c (placeUnder (LocalTheory.fiberPlace K v)) =
      ∑ w : LocalTheory.Fiber k (.finite p), LocalTheory.weight k _ w *
        c (LocalTheory.fiberPlace k w) := by
  haveI := LocalTheory.fiber_finite K p
  haveI := LocalTheory.fiber_finite k p
  haveI : Fintype {w : FinitePlace K // residueChar w = p} := Fintype.ofFinite _
  haveI : Fintype {w : FinitePlace k // residueChar w = p} := Fintype.ofFinite _
  rw [Fintype.sum_equiv (LocalTheory.fiberFiniteEquiv K p) _
      (fun v => placeWeight K v.1 * c (placeUnder v.1))
      (fun v => by rw [LocalTheory.weight_finite_eq]; rfl),
    Fintype.sum_equiv (LocalTheory.fiberFiniteEquiv k p) _
      (fun w => placeWeight k w.1 * c w.1)
      (fun w => by rw [LocalTheory.weight_finite_eq]; rfl)]
  exact sum_placeWeight_placeUnder (p : ℕ) c

end Average

namespace InitialThetaData

variable (D : InitialThetaData.{u})

/-! ### The different term -/

/-- The place of the section `V` over the place of `F_mod` below a place `v` of `K`. -/
lemma sectFin_placeUnder_liesOver (v : FinitePlace D.Kt) :
    FinitePlace.LiesOver (D.V.sectFin (placeUnder (k := D.Fmod) v)) (placeUnder (k := D.Fmod) v) :=
  D.V.sectFin_liesOver _

/-- **The different exponent at a place of `K` is the one at the place of `V` over the same place
of `F_mod`** (`K/F_mod` Galois). -/
lemma differentExponent_eq_sect (v : FinitePlace D.Kt) :
    differentExponent D.Kt v =
      differentExponent D.Kt (D.V.sectFin (placeUnder (k := D.Fmod) v)) :=
  differentExponent_eq_of_liesOver (liesOver_placeUnder v) (D.sectFin_placeUnder_liesOver v)

/-- **`log(d^K_p)` as an average over `V`** (IUT III, Remark 3.1.1(ii); IUT IV, Theorem 1.10,
Step (v)): `log(d^K_p) = ∑_{w ∣ p} [(F_mod)_w : ℚ_p]/[F_mod : ℚ]·d_{v(w)}·log p`, with
`v(w) ∈ V` the place of the section over `w`. -/
theorem logDK_sect (p : Nat.Primes) :
    D.logDK p = ∑ w : LocalTheory.Fiber D.Fmod (.finite p),
      LocalTheory.weight D.Fmod _ w *
        differentExponent D.Kt (LocalTheory.sectPlace D.placeSect w) * Real.log p := by
  unfold InitialThetaData.logDK
  rw [dif_pos p.2]
  simp_rw [mul_assoc]
  have h := LocalTheory.sum_weight_placeUnder (K := D.Kt) (k := D.Fmod) p
    (fun w => differentExponent D.Kt (D.V.sectFin w) * Real.log p)
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [D.differentExponent_eq_sect]
  rfl

/-! ### The `q`-degree -/

/-- The `j`-invariant `j(E)` as an element of `F_mod = ℚ(j(E))`. -/
noncomputable def jmod : D.Fmod :=
  ⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩

/-- The local `q`-degree at a place `w` of `F_mod`: `ord_p(q) = −ord_p(j(E))` at
`w ∈ V_mod^bad` (where `‖q‖ = ‖j(E)‖⁻¹`), `0` elsewhere. -/
noncomputable def qDeg (w : FinitePlace D.Fmod) : ℝ :=
  open scoped Classical in
  if w ∈ D.VBad then -ordp D.Fmod w (FinitePlace.embedding w.maximalIdeal D.jmod) else 0

/-- A place of `F` (resp. `K`) is bad iff the place of `F_mod` below it is in `V_mod^bad`. -/
lemma mem_badPlacesOver_iff (u : FinitePlace D.F) :
    u ∈ badPlacesOver D.F D.E D.VBad ↔ placeUnder (k := D.Fmod) u ∈ D.VBad := by
  constructor
  · rintro ⟨w, hw, huw⟩
    rwa [← eq_placeUnder_of_liesOver huw]
  · intro h
    exact ⟨_, h, liesOver_placeUnder u⟩

/-- `ord_p(q_u) = −ord_p(j(E))` at a bad place `u` of `F` (`‖q_u‖ = ‖j(E)‖⁻¹`). -/
lemma ordp_tateParam_q (u : FinitePlace D.F) (hu : u ∈ badPlacesOver D.F D.E D.VBad) :
    ordp D.F u ((D.tateParam u hu).q : localCompletion u) =
      -ordp D.F u (FinitePlace.embedding u.maximalIdeal D.E.j) := by
  have hn := (D.tateParam u hu).norm_tateJ (twelve_ne_zero u)
  rw [D.tateParam_tateJ u hu] at hn
  unfold ordp
  rw [hn, Real.log_inv]
  ring

/-- **`ord_w(q_w)/e_w` depends only on the place of `F_mod` below**:
`ord_w(q_w)/e_w = ord_p(q_w) = −ord_p(j(E))`, and `j(E) ∈ F_mod`. -/
lemma qOrder_div_ramIdx (u : FinitePlace D.F) (hu : u ∈ badPlacesOver D.F D.E D.VBad) :
    (D.qOrder u hu : ℝ) / ramIdx D.F u = D.qDeg (placeUnder (k := D.Fmod) u) := by
  have hw : placeUnder (k := D.Fmod) u ∈ D.VBad := (D.mem_badPlacesOver_iff u).mp hu
  have hj : FinitePlace.embedding u.maximalIdeal D.E.j =
      embedCompletion (liesOver_placeUnder (k := D.Fmod) u)
        (FinitePlace.embedding (placeUnder (k := D.Fmod) u).maximalIdeal D.jmod) := by
    rw [embedCompletion_embedding]
    rfl
  unfold qDeg
  rw [if_pos hw, ← ordp_embedCompletion (liesOver_placeUnder (k := D.Fmod) u), ← hj,
    ← D.ordp_tateParam_q u hu, ordp_tateParameter _ (isUniformizer_unifAt u),
    D.qOrder_eq_orderNat]

/-- **`ord_p(q_v)` at the place `v(w) ∈ V` over a place `w` of `F_mod`**:
`ord_p(q_{v(w)}) = q-deg(w)/2ℓ`. -/
lemma ordp_qroot_sect (w : FinitePlace D.Fmod) :
    ordp D.Kt (D.V.sectFin w) (D.qroot (D.V.sectFin w)) = D.qDeg w / (2 * D.ℓ) := by
  classical
  have hvw : FinitePlace.LiesOver (D.V.sectFin w) w := D.V.sectFin_liesOver w
  by_cases hw : w ∈ D.VBad
  · set u : FinitePlace D.F := placeUnder (k := D.F) (D.V.sectFin w) with hu_def
    have huw : FinitePlace.LiesOver u w := by
      haveI : (D.V.sectFin w).maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
      haveI : (D.V.sectFin w).maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal :=
        liesOver_placeUnder (D.V.sectFin w)
      exact Ideal.LiesOver.tower_bot (D.V.sectFin w).maximalIdeal.asIdeal _ _
    have hu : u ∈ badPlacesOver D.F D.E D.VBad := ⟨w, hw, huw⟩
    rw [D.ordp_qroot (D.V.sectFin w) u (liesOver_placeUnder _) hu]
    have h := D.qOrder_div_ramIdx u hu
    rw [← eq_placeUnder_of_liesOver huw] at h
    rw [← h]
    have he : (ramIdx D.F u : ℝ) ≠ 0 := by exact_mod_cast (ramIdx_pos' u).ne'
    have hℓ : (D.ℓ : ℝ) ≠ 0 := by
      have : (5 : ℝ) ≤ D.ℓ := by exact_mod_cast D.prime.five_le
      positivity
    field_simp
  · have hnot : ¬ IsBadK D (D.V.sectFin w) := by
      rintro ⟨w', hw', hvw'⟩
      rw [eq_placeUnder_of_liesOver hvw', ← eq_placeUnder_of_liesOver hvw] at hw'
      exact hw hw'
    rw [qroot, qrootOf_of_not D hnot]
    unfold qDeg
    rw [if_neg hw]
    simp [ordp, norm_one]

/-- `log(q_p)` as the average of the local `q`-degrees over the places of `F_mod` above `p`
(the base-change invariance of the `q`-degree from `F` to `F_mod`). -/
theorem logQAt_eq_sum_qDeg (p : Nat.Primes) :
    (concreteVariantData D).logQAt p = ∑ w : LocalTheory.Fiber D.Fmod (.finite p),
      LocalTheory.weight D.Fmod _ w * D.qDeg (LocalTheory.fiberPlace D.Fmod w) * Real.log p := by
  classical
  haveI := LocalTheory.fiber_finite D.F p
  haveI : Fintype {u : FinitePlace D.F // residueChar u = p} := Fintype.ofFinite _
  set bad := (D.qPilot).badFinset with hbad
  -- the `q`-degree at a place of `F`
  set g : FinitePlace D.F → ℝ := fun u =>
    placeWeight D.F u * (D.qDeg (placeUnder (k := D.Fmod) u) * Real.log p) with hg
  have h1 : (concreteVariantData D).logQAt p = ∑ u ∈ bad.attach.filter
      (fun u => residueChar u.1 = p),
      (inertDeg D.F u.1 : ℝ) / Module.finrank ℚ D.F *
        (D.qOrder u.1 ((D.qPilot).mem_bad u.2) : ℝ) * Real.log (residueChar u.1) := rfl
  have h2 : (concreteVariantData D).logQAt p = ∑ u ∈ bad.filter (fun u => residueChar u = p),
      g u := by
    rw [h1, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_attach bad]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs with hp
    · have hq := D.qOrder_div_ramIdx u.1 ((D.qPilot).mem_bad u.2)
      have he : (ramIdx D.F u.1 : ℝ) ≠ 0 := by exact_mod_cast (ramIdx_pos' u.1).ne'
      rw [hg]
      dsimp only
      rw [← hq, hp]
      unfold placeWeight localDeg
      push_cast
      field_simp
    · rfl
  -- the sum over the bad places is the sum over all places over `p`
  have h3 : ∑ u ∈ bad.filter (fun u => residueChar u = p), g u =
      ∑ u : {u : FinitePlace D.F // residueChar u = p}, g u.1 := by
    have hm := Finset.sum_map Finset.univ
      (Function.Embedding.subtype fun u : FinitePlace D.F => residueChar u = p) g
    simp only [Function.Embedding.coe_subtype] at hm
    rw [← hm]
    refine Finset.sum_subset ?_ ?_
    · intro u hu
      rw [Finset.mem_map]
      exact ⟨⟨u, (Finset.mem_filter.mp hu).2⟩, Finset.mem_univ _, rfl⟩
    · intro u hu hnot
      obtain ⟨u', -, rfl⟩ := Finset.mem_map.mp hu
      have hnb : (u' : FinitePlace D.F) ∉ badPlacesOver D.F D.E D.VBad := by
        intro hb
        apply hnot
        refine Finset.mem_filter.mpr ⟨?_, u'.2⟩
        rw [← Finset.mem_coe, hbad, (D.qPilot).badFinset_spec]
        exact hb
      rw [D.mem_badPlacesOver_iff] at hnb
      simp only [hg, Function.Embedding.coe_subtype, qDeg, if_neg hnb, zero_mul, mul_zero]
  rw [h2, h3]
  haveI := LocalTheory.fiber_finite D.Fmod p
  haveI : Fintype {w : FinitePlace D.Fmod // residueChar w = p} := Fintype.ofFinite _
  have h4 := sum_placeWeight_placeUnder (K := D.F) (k := D.Fmod) (p : ℕ)
    (fun w => D.qDeg w * Real.log p)
  rw [h4]
  simp_rw [mul_assoc]
  refine (Fintype.sum_equiv (LocalTheory.fiberFiniteEquiv D.Fmod p) _ _ fun w => ?_).symm
  rw [LocalTheory.weight_finite_eq]
  rfl

/-- **`log(q_p)` as an average over `V`** (IUT III, Remark 3.1.1(ii); IUT IV, Theorem 1.10,
Step (v)): `log(q_p) = 2ℓ·log p·∑_{w ∣ p} [(F_mod)_w : ℚ_p]/[F_mod : ℚ]·ord_p(q_{v(w)})`, with
`v(w) ∈ V` the place of the section over `w`. -/
theorem logQAt_eq_sect (p : Nat.Primes) :
    (concreteVariantData D).logQAt p = 2 * D.ℓ * Real.log p *
      ∑ w : LocalTheory.Fiber D.Fmod (.finite p), LocalTheory.weight D.Fmod (.finite p) w *
        ordp D.Kt (LocalTheory.sectPlace D.placeSect w)
          (D.qroot (LocalTheory.sectPlace D.placeSect w)) := by
  rw [D.logQAt_eq_sum_qDeg p, Finset.mul_sum]
  have hℓ : (D.ℓ : ℝ) ≠ 0 := by
    have : (5 : ℝ) ≤ D.ℓ := by exact_mod_cast D.prime.five_le
    positivity
  refine Finset.sum_congr rfl fun w _ => ?_
  change _ = _ * (_ * ordp D.Kt (D.V.sectFin (LocalTheory.fiberPlace D.Fmod w))
    (D.qroot (D.V.sectFin (LocalTheory.fiberPlace D.Fmod w))))
  rw [D.ordp_qroot_sect]
  field_simp

end InitialThetaData

end Iut
