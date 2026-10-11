/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Wall.BPS
import Iut.Concrete.ThetaRegion

/-!
# The `q`-pilot and Θ-pilot BPSs, the Θ-link and the scale factor `s` (the wall, M1a)

The two value-group BPSs glued by the Θ-link, after the LANA interim report (July 2026,
[LANA]) and IUT III, Definition 3.8, Corollary 3.12:

* **the `q`-pilot value-group BPS** ([LANA], §4.2(c), p. 26): `C = ℝ` with local pilots
  `φ_v = deg(q_v)` at the bad places (`q_v` the `2ℓ`-th root of the Tate parameter),
  `deg(p_v)` at the good nonarchimedean places and `2π` at the archimedean ones (`qVal`);
* **the Θ-pilot value-group BPS** ([LANA], §7.1(a), pp. 37–38): `C = (⊕_v ℝ·Θ_v)/PF`, `PF` the
  kernel of `ψ = ∑_v ψ_v`, `ψ_v(Θ_v) = s·φ^q_v`, with local pilots the classes of the `Θ_v`
  (`thetaVal`);
* **the scale factor** `s = (1² + 2² + ⋯ + (ℓ*)²)/ℓ*` ([LANA], §7.1(a); `sFactor`), equal to
  `(ℓ*+1)(2ℓ*+1)/6` (`sFactor_eq`) and `> 1` for `ℓ* ≥ 2` (`one_lt_sFactor`), i.e. for every
  admissible prime `ℓ ≥ 5`.

Proved: the two value-group BPSs have the same product formula (`PF_thetaVal`), so by
[LANA], Lemma 4.1.7, they are isomorphic, by a *unique* isomorphism `thetaLink` (the
value-group part of the Θ-link, [LANA], §7.1(b)(b)); the degree map of the Θ-pilot line
(`degTheta`, the composite `R_{⊙,Θ} → R_Θ` of the Scholze–Stix hexagon, [LANA], §10.2,
Figure 7, Table 2) is `s` times the Θ-link (`degTheta_eq_smul_thetaLink`), so the hexagon
commutes iff `s = 1` (`hexagon_commutes_iff`): the Scholze–Stix observation, which [LANA],
§10.5, accepts.

For initial Θ-data `D` the `q`-pilot value-group BPS is built on the places of `F`
(`InitialThetaData.bpsDegrees`), with the degrees of the left-hand side `−|log(q)|` of the
Corollary 3.12 variant (`Iut/Cor312/LeftHandSide.lean`), and its pilot is `|log(q)|`:
`(qVal D.bpsDegrees).pilot = D.qPilot.absLogQ = −(qPilot D).lhs` (`pilot_qVal`).

**Deviation.** [LANA] indexes the local pilots by `V ≅ V_mod` (places of `F_mod`) but uses
`deg(a) = [F : ℚ]⁻¹ log #(O_{F_v}/a)`; here the index set is the set of places of `F`, which is
the indexing of the left-hand side of the variant (`QPilotData`). Only the pilot `φ_C` (a sum
over the bad places) enters the wall; the good-place degrees only fix the product formula.
-/

namespace Iut

namespace Wall

open NumberField

/-! ### The scale factor `s` -/

/-- **The scale factor** `s = (1² + 2² + ⋯ + n²)/n` of [LANA], §7.1(a), for `n = ℓ*`. It is
also the average of the exponents `j²` of the theta values `q^{j²}` over the capsules
`j = 1, …, ℓ*` of the procession (IUT III, Corollary 3.12; `InitialThetaData.scaleEltAt`). -/
noncomputable def sFactor (n : ℕ) : ℝ := (∑ j ∈ Finset.range n, ((j : ℝ) + 1) ^ 2) / n

lemma sum_range_succ_sq (n : ℕ) :
    ∑ j ∈ Finset.range n, ((j : ℝ) + 1) ^ 2 = (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `s = (ℓ*+1)(2ℓ*+1)/6`. -/
theorem sFactor_eq {n : ℕ} (hn : 0 < n) : sFactor n = (n + 1) * (2 * n + 1) / 6 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [sFactor, sum_range_succ_sq]
  field_simp

lemma sFactor_pos {n : ℕ} (hn : 0 < n) : 0 < sFactor n := by
  rw [sFactor_eq hn]
  positivity

/-- `s > 1` as soon as `ℓ* ≥ 2`. -/
theorem one_lt_sFactor {n : ℕ} (hn : 2 ≤ n) : 1 < sFactor n := by
  rw [sFactor_eq (by omega)]
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [lt_div_iff₀ (by norm_num)]
  nlinarith

/-! ### Local degrees and the two value-group BPSs -/

/-- **Local degrees** on an index set of places `V`: a finite nonempty bad locus and positive
degrees `deg_v` (the local pilots of the `q`-pilot, [LANA], §4.2(c)). -/
structure LocalDegrees (V : Type) where
  /-- The bad locus `V^bad`. -/
  bad : Finset V
  /-- The local degrees (`deg(q_v)`, `deg(p_v)`, `2π`). -/
  deg : V → ℝ
  deg_pos : ∀ v, 0 < deg v
  bad_nonempty : bad.Nonempty

variable {V : Type} (L : LocalDegrees V)

namespace LocalDegrees

/-- The `q`-pilot `φ_C = ∑_{v ∈ V^bad} deg_v`. -/
lemma sum_bad_pos : 0 < ∑ v ∈ L.bad, L.deg v :=
  Finset.sum_pos (fun v _ => L.deg_pos v) L.bad_nonempty

end LocalDegrees

/-- **The `q`-pilot value-group BPS** ([LANA], §4.2(c)): `C = ℝ`, `φ_v = deg_v`. -/
noncomputable def qVal : ValBPS V L.bad where
  C := ℝ
  finrank_eq_one := Module.finrank_self ℝ
  localPilot := L.deg
  localPilot_ne_zero v := (L.deg_pos v).ne'
  pilot_ne_zero := L.sum_bad_pos.ne'

lemma qVal_pilot : (qVal L).pilot = ∑ v ∈ L.bad, L.deg v := rfl

variable (s : ℝ)

/-- The map `ψ = ∑_v ψ_v : ⊕_v ℝ·Θ_v → ℝ`, `ψ_v(Θ_v) = s·deg_v` ([LANA], (7-1)). -/
noncomputable def psi : (V →₀ ℝ) →ₗ[ℝ] ℝ := s • Finsupp.linearCombination ℝ L.deg

lemma psi_single (v : V) (a : ℝ) : psi L s (Finsupp.single v a) = s * (a * L.deg v) := by
  simp [psi]

variable {s}

lemma psi_surjective (hs : s ≠ 0) : Function.Surjective (psi L s) := by
  obtain ⟨v, -⟩ := L.bad_nonempty
  intro y
  refine ⟨Finsupp.single v (y / (s * L.deg v)), ?_⟩
  rw [psi_single]
  have := (L.deg_pos v).ne'
  field_simp

/-- **The degree map of the Θ-pilot line** `C_Θ = (⊕_v ℝ·Θ_v)/PF ≅ ℝ` induced by `ψ`: the
composite `R_{⊙,Θ} → R_Θ` of the Scholze–Stix hexagon ([LANA], §10.2, Table 2). -/
noncomputable def degTheta (hs : s ≠ 0) : ((V →₀ ℝ) ⧸ LinearMap.ker (psi L s)) ≃ₗ[ℝ] ℝ :=
  (psi L s).quotKerEquivOfSurjective (psi_surjective L hs)

lemma degTheta_mk (hs : s ≠ 0) (x : V →₀ ℝ) :
    degTheta L hs (Submodule.Quotient.mk x) = psi L s x :=
  (psi L s).quotKerEquivOfSurjective_apply_mk (psi_surjective L hs) x

/-- **The Θ-pilot value-group BPS** ([LANA], §7.1(a)): `C = (⊕_v ℝ·Θ_v)/PF`, `PF = ker ψ`,
local pilots the classes of the formal symbols `Θ_v`. -/
noncomputable def thetaVal (hs : s ≠ 0) : ValBPS V L.bad where
  C := (V →₀ ℝ) ⧸ LinearMap.ker (psi L s)
  finrank_eq_one := by
    rw [(degTheta L hs).finrank_eq, Module.finrank_self]
  localPilot v := Submodule.Quotient.mk (Finsupp.single v 1)
  localPilot_ne_zero v h := by
    have := congrArg (degTheta L hs) h
    rw [degTheta_mk, psi_single, map_zero, one_mul] at this
    exact mul_ne_zero hs (L.deg_pos v).ne' this
  pilot_ne_zero h := by
    have := congrArg (degTheta L hs) h
    rw [map_sum, map_zero] at this
    simp only [degTheta_mk, psi_single, one_mul, ← Finset.mul_sum] at this
    exact mul_ne_zero hs L.sum_bad_pos.ne' this

lemma degTheta_localPilot (hs : s ≠ 0) (v : V) :
    degTheta L hs ((thetaVal L hs).localPilot v) = s * L.deg v := by
  change degTheta L hs (Submodule.Quotient.mk _) = _
  rw [degTheta_mk, psi_single, one_mul]

/-- **The scale factor on pilots**: the degree of the Θ-pilot is `s` times the `q`-pilot
([LANA], §7.1(a), §10.2: "the composition `R_{⊙,Θ} → R_Θ` scales by a factor of `s`"). -/
theorem degTheta_pilot (hs : s ≠ 0) :
    degTheta L hs (thetaVal L hs).pilot = s * ∑ v ∈ L.bad, L.deg v := by
  change degTheta L hs (∑ v ∈ L.bad, (Submodule.Quotient.mk (Finsupp.single v 1) :
    (V →₀ ℝ) ⧸ LinearMap.ker (psi L s))) = _
  rw [map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => degTheta_localPilot L hs v

/-- **The Θ-pilot and `q`-pilot value-group BPSs have the same product formula.** -/
theorem PF_thetaVal (hs : s ≠ 0) : (thetaVal L hs).PF = (qVal L).PF := by
  have h1 : ∀ x, (thetaVal L hs).sumMap x = (Submodule.Quotient.mk x : (thetaVal L hs).C) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact (Submodule.Quotient.mk_zero _).symm
    | add x y hx hy => rw [map_add, hx, hy]; rfl
    | single v a =>
      rw [ValBPS.sumMap_single]
      change a • (Submodule.Quotient.mk (Finsupp.single v 1) :
        (V →₀ ℝ) ⧸ LinearMap.ker (psi L s)) = Submodule.Quotient.mk (Finsupp.single v a)
      rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  ext x
  simp only [ValBPS.PF, LinearMap.mem_ker]
  rw [h1]
  change Submodule.Quotient.mk x = (0 : (V →₀ ℝ) ⧸ LinearMap.ker (psi L s)) ↔ _
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker]
  change s • (Finsupp.linearCombination ℝ L.deg x) = 0 ↔ Finsupp.linearCombination ℝ L.deg x = 0
  rw [smul_eq_zero, or_iff_right hs]

/-- **The value-group part of the Θ-link** ([LANA], §7.1(b)(b)): the isomorphism of the
Θ-pilot value-group BPS with the `q`-pilot value-group BPS, which exists by [LANA],
Lemma 4.1.7 (`ValBPS.nonempty_iso_iff`) and is unique (`ValBPS.valIso_subsingleton`). -/
noncomputable def thetaLink (hs : s ≠ 0) : ValBPS.Iso (thetaVal L hs) (qVal L) :=
  ((ValBPS.nonempty_iso_iff _ _).mpr (PF_thetaVal L hs)).some

/-- The Θ-link maps `Θ_v` to `deg_v`. -/
lemma thetaLink_localPilot (hs : s ≠ 0) (v : V) :
    (thetaLink L hs).toLinearEquiv ((thetaVal L hs).localPilot v) = L.deg v :=
  (thetaLink L hs).map_localPilot v

/-- **The Scholze–Stix hexagon, quantitatively** ([LANA], §10.2): the degree map of the
Θ-pilot line is `s` times the Θ-link followed by the (identity) degree map of the `q`-pilot
line. -/
theorem degTheta_eq_smul_thetaLink (hs : s ≠ 0) :
    (degTheta L hs).toLinearMap = s • (thetaLink L hs).toLinearEquiv.toLinearMap := by
  refine LinearMap.ext_on_range (thetaVal L hs).span_localPilot fun v => ?_
  change degTheta L hs _ = s • (thetaLink L hs).toLinearEquiv _
  rw [degTheta_localPilot, thetaLink_localPilot]
  rfl

/-- **The hexagon commutes iff `s = 1`** ([LANA], §10.2, §10.5; Scholze–Stix): for `ℓ* ≥ 2`
(`one_lt_sFactor`) it does not. -/
theorem hexagon_commutes_iff (hs : s ≠ 0) :
    (degTheta L hs).toLinearMap = (thetaLink L hs).toLinearEquiv.toLinearMap ↔ s = 1 := by
  rw [degTheta_eq_smul_thetaLink]
  constructor
  · intro h
    have h' := congrArg (fun f => f (thetaVal L hs).pilot) h
    change s • (thetaLink L hs).toLinearEquiv (thetaVal L hs).pilot =
      (thetaLink L hs).toLinearEquiv (thetaVal L hs).pilot at h'
    rw [ValBPS.Iso.map_pilot] at h'
    have hp : (qVal L).pilot ≠ 0 := (qVal L).pilot_ne
    exact (mul_eq_right₀ hp).mp h'
  · rintro rfl
    rw [one_smul]

/-! ### The `q`-pilot of initial Θ-data -/

/-- Every finite place of `k` has a finite place of `K ⊇ k` over it (going up). -/
lemma exists_finitePlace_liesOver {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] (v : FinitePlace k) :
    ∃ w : FinitePlace K, FinitePlace.LiesOver w v := by
  haveI : v.maximalIdeal.asIdeal.IsMaximal := v.maximalIdeal.isMaximal
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K)
    v.maximalIdeal.asIdeal (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 K))]
      exact bot_le)
  have hne : Q ≠ ⊥ := by
    rintro rfl
    apply v.maximalIdeal.ne_bot
    rw [← hQ, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp
      (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 K))]
  refine ⟨FinitePlace.mk ⟨Q, hQmax.isPrime, hne⟩, ⟨?_⟩⟩
  rw [FinitePlace.maximalIdeal_mk]
  exact hQ.symm

end Wall

namespace InitialThetaData

open Wall NumberField

variable (D : InitialThetaData.{0})

/-- The bad locus `V(F)^bad` is nonempty (IUT I, Definition 3.1(b): `V_mod^bad ≠ ∅`). -/
lemma badFinset_nonempty : D.qPilot.badFinset.Nonempty := by
  obtain ⟨v, hv⟩ := D.global.bad_nonempty
  obtain ⟨w, hw⟩ := exists_finitePlace_liesOver (K := D.F) v
  refine ⟨w, ?_⟩
  have : w ∈ badPlacesOver D.F D.E D.VBad := ⟨v, hv, hw⟩
  rw [← D.qPilot.badFinset_spec] at this
  exact this

/-- The degree `deg(q_w) = f_w·ord_w(q_w)·log p_w/([F : ℚ]·2ℓ)` of the `2ℓ`-th root of the
Tate parameter at a bad place, `deg(p_w) = e_w f_w log p_w/[F : ℚ]` at a good place
([LANA], §4.2(c)). -/
noncomputable def finDeg (w : FinitePlace D.F) : ℝ :=
  haveI := Classical.dec (w ∈ D.qPilot.badFinset)
  if h : w ∈ D.qPilot.badFinset then
    D.qPilot.weight w * (D.qOrder w (D.qPilot.mem_bad h) : ℝ) * Real.log (residueChar w) /
      (2 * (D.ℓ : ℝ))
  else (localDeg D.F w : ℝ) * Real.log (residueChar w) / Module.finrank ℚ D.F

lemma ℓ_pos : (0 : ℝ) < D.ℓ := by
  have := D.prime.five_le
  change (0 : ℝ) < D.prime.ℓ
  exact_mod_cast (by omega : 0 < D.prime.ℓ)

lemma finDeg_pos (w : FinitePlace D.F) : 0 < D.finDeg w := by
  have hp : 0 < Real.log (residueChar w) :=
    Real.log_pos (by exact_mod_cast (Iut.residueChar_prime w).one_lt)
  unfold finDeg
  split_ifs with h
  · have := D.qOrder_pos w (D.qPilot.mem_bad h)
    have := D.qPilot.weight_pos w h
    have := D.ℓ_pos
    positivity
  · have := LocalTheory.localDeg_pos D.F w
    have := LocalTheory.finrank_pos D.F
    positivity

/-- **The local degrees of the `q`-pilot of `D`** ([LANA], §4.2(c)), on the places of `F`. -/
noncomputable def bpsDegrees : LocalDegrees (FinitePlace D.F ⊕ InfinitePlace D.F) where
  bad := D.qPilot.badFinset.map Function.Embedding.inl
  deg := Sum.elim D.finDeg fun _ => 2 * Real.pi
  deg_pos v := by
    rcases v with w | w
    · exact D.finDeg_pos w
    · exact mul_pos two_pos Real.pi_pos
  bad_nonempty := D.badFinset_nonempty.map

/-- **The pilot of the `q`-pilot value-group BPS of `D` is `|log(q)|`**, the negative of the
left-hand side `−|log(q)|` of the Corollary 3.12 variant. -/
theorem pilot_qVal : (qVal D.bpsDegrees).pilot = D.qPilot.absLogQ := by
  rw [qVal_pilot]
  simp only [bpsDegrees, Finset.sum_map, Function.Embedding.inl_apply, Sum.elim_inl]
  rw [QPilotData.absLogQ, QPilotData.logQ, Finset.sum_div,
    ← Finset.sum_attach D.qPilot.badFinset]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [finDeg, dif_pos w.2]

theorem pilot_qVal_eq_neg_lhs : (qVal D.bpsDegrees).pilot = -D.qPilot.lhs := by
  rw [pilot_qVal, QPilotData.lhs, neg_neg]

/-- **The left-hand side is negative**: `−|log(q)| < 0`. -/
theorem lhs_neg : D.qPilot.lhs < 0 := by
  have h := D.bpsDegrees.sum_bad_pos
  rw [← qVal_pilot, pilot_qVal_eq_neg_lhs] at h
  linarith

/-- `ℓ* = (ℓ − 1)/2 ≥ 2`. -/
lemma two_le_ellStar : 2 ≤ (D.ℓ - 1) / 2 := by
  have := D.prime.five_le
  change 2 ≤ (D.prime.ℓ - 1) / 2
  omega

/-- The scale factor `s` of `D`, for `ℓ* = (ℓ − 1)/2`. -/
noncomputable abbrev wallS : ℝ := sFactor ((D.ℓ - 1) / 2)

lemma one_lt_wallS : 1 < D.wallS := one_lt_sFactor D.two_le_ellStar

lemma wallS_ne_zero : D.wallS ≠ 0 := (zero_lt_one.trans D.one_lt_wallS).ne'

/-- **The Θ-pilot value-group BPS of `D`** ([LANA], §7.1(a)). -/
noncomputable abbrev thetaValD : ValBPS _ D.bpsDegrees.bad := thetaVal D.bpsDegrees D.wallS_ne_zero

/-- **For initial Θ-data the Scholze–Stix hexagon does not commute** ([LANA], §10.2, §10.5). -/
theorem hexagon_not_commutes :
    (degTheta D.bpsDegrees D.wallS_ne_zero).toLinearMap ≠
      (thetaLink D.bpsDegrees D.wallS_ne_zero).toLinearEquiv.toLinearMap := by
  rw [Ne, hexagon_commutes_iff]
  exact D.one_lt_wallS.ne'

end InitialThetaData

end Iut
