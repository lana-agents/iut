/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Wall.IdentifiedCopies

/-!
# The `q`-pilot region `{q_v O_v}` (the wall, Milestone 2, roadmap package P21)

In Milestone 1 (`Iut/Wall/Rss.lean`) the class of the `q`-pilot region `{q_v O_v}` in `R_ss`
was *defined* by its log-volume `−|log(q)|`, so `logVol_etaQ_pilot` was a normalization. Here the
region is constructed in the concrete large volume container of `D`, and its
procession-normalized log-volume is computed: `logVol_qRegion : log-vol(qRegion) = −|log(q)|`.

## Placement (a modelling choice, documented)

The `q`-pilot is placed as **the theta value for `j = 1`**, i.e. the `q`-parameter itself
`q_v = q_v^{1²}` (IUT III, Corollary 3.12, whose left-hand side is the log-volume of the
`q`-pilot, the theta value `q^{j²}` for `j = 1`; [LANA], §5.2(f), §9.2: `{q_v O_v}` "embedded
diagonally" into the container):

* in **every** capsule `S_{j+1} = {0, …, j}` of the procession (the diagonal embedding);
* at each prime `p` and each tuple `c : S_{j+1} → V_{p}` of places of the valuation section over
  `p`, the scaled integral structure `q_{v}·O`, with `q_{v}` the `2ℓ`-th root `D.qroot` of the
  Tate parameter at the place `v = c(1)` of the **label `1`** (`labOne`) placed in the tensor
  factor of label `1` (`q_v = 1` at the good places, so almost all packets are integral);
* at `∞`, the integral structure.

The label `1` belongs to every capsule; in the first capsule (`j = 1`) it is the distinguished
label, and there the `q`-pilot region **coincides with `LGP·O`** (`qRegion_first`). The log-volume
does not depend on the label (`logVol_pow_integral` holds for every label choice `lab`), as
expected from the (Ind1) label permutations (`Iut/Concrete/Ind1Invariance.lean`).

## Contents

* `powElt D e lab`, `pow D e lab S`: the region obtained from `S` by multiplying, at each
  capsule `i` and prime `p`, by `q_{v}^{e(i)}` in the tensor factor of the label `lab i` — a
  common generalization of `LGP·S` (`lgp_eq_pow`, `e(i) = (i+1)²` at the distinguished label) and
  of the `q`-pilot region (`e = 1` at the label `1`);
* `logVol_pow_integral : log-vol(pow D e lab O) = −(avg_i e(i))·|log(q)|`, from the
  elementary-scaling volume formula `componentVol_prod_incl_smul_integral` (IUT IV,
  Proposition 1.4) and `InitialThetaData.logQAt_eq_sect` (`Iut/Concrete/SectionAverage.lean`);
* `qRegion D`, `isAdelic_qRegion`, **`logVol_qRegion : log-vol(qRegion D) = (qPilot D).lhs`**;
* `etaQReg D`: `η_q` defined from the constructed region, `etaQReg_eq_etaQ : etaQReg D = etaQ D`
  and `etaQ_pilot_eq_mk`: `η_q` sends the pilot to the class `[qRegion D] ∈ R_ss`. This turns the
  normalization `logVol_etaQ_pilot` of Milestone 1 into a statement about a constructed region
  (`logVol_etaQ_pilot_eq_qRegion`).
-/

namespace Iut

open NumberField MeasureTheory
open scoped Pointwise

universe u

namespace Wall

variable (D : InitialThetaData.{u})

/-! ### Scaling by powers of `q` at chosen labels -/

/-- The label `1` of the capsule `S_{i+2} = {0, …, i+1}` (the label of the theta value for
`j = 1`). -/
def labOne (i : Fin (nC D)) : InitialThetaData.Lab (nC D) i :=
  ⟨1, by simp [Procession.standard, procLabels]⟩

/-- The element `q_{v}^{e(i)}` in the tensor factor of the label `lab i`, `v = c(lab i)`. -/
noncomputable def powElt (e : Fin (nC D) → ℕ) (lab : ∀ i, InitialThetaData.Lab (nC D) i)
    (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c) :=
  LocalTheory.incl D.Kt p (LocalTheory.tuple D.placeSect _ c) (lab i)
    (LocalTheory.sectPlace D.placeSect (c (lab i)))
    (LocalTheory.tuple_finite D.placeSect c (lab i))
    (D.qroot (LocalTheory.sectPlace D.placeSect (c (lab i))) ^ e i)

/-- The theta value `q^{j²}` at the distinguished label is `powElt` with `e(i) = (i+1)²`. -/
lemma scaleElt_eq_powElt (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    D.scaleElt (nC D) i p c =
      powElt D (fun i => (i.1 + 1) ^ 2) (InitialThetaData.distinguished _) i p c :=
  rfl

lemma isUnit_powElt (e : Fin (nC D) → ℕ) (lab : ∀ i, InitialThetaData.Lab (nC D) i)
    (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    IsUnit (powElt D e lab i p c) :=
  LocalTheory.isUnit_incl D.Kt p _ _ _ _ _ (pow_ne_zero _ (D.qroot_ne_zero _))

variable (e : Fin (nC D) → ℕ) (lab : ∀ i, InitialThetaData.Lab (nC D) i)

/-- Multiplication by `powElt`. -/
noncomputable def powMap (i : Fin (nC D)) (p : Nat.Primes) :
    (LocalTheory.packet D.placeSect (InitialThetaData.Lab (nC D) i) (.finite p)).Total →
      (LocalTheory.packet D.placeSect (InitialThetaData.Lab (nC D) i) (.finite p)).Total :=
  fun x c => @HMul.hMul (LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c))
    (LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c))
    (LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)) instHMul
    (powElt D e lab i p c) (x c)

lemma powMap_eq_id (i : Fin (nC D)) (p : Nat.Primes) (hbad : (p : ℕ) ∉ D.badChars) :
    powMap D e lab i p = id := by
  funext x c
  have h1 : powElt D e lab i p c = 1 := by
    unfold powElt
    rw [D.qroot_eq_one _ (by rw [LocalTheory.residueChar_sectPlace D.placeSect]; exact hbad),
      one_pow, map_one]
  simp only [powMap, h1, one_mul, id]

/-- The packet regions of `pow D e lab R`. -/
noncomputable def powRegion (i : Fin (VC D).proc.length) (R : (VC D).AdmissibleRegion i) :
    ∀ vQ : RationalPlace, Set ((VC D).packet i vQ).Total
  | .finite p => powMap D e lab i p '' R.region (.finite p)
  | .infinite => R.region .infinite

/-- `pow D e lab R` at capsule `i`. -/
noncomputable def powAt (i : Fin (VC D).proc.length) (R : (VC D).AdmissibleRegion i) :
    (VC D).AdmissibleRegion i where
  region := powRegion D e lab i R
  finiteSupport := by
    refine (R.finiteSupport.union ((D.badChars.finite_toSet.image
      fun q : ℕ => if h : q.Prime then RationalPlace.finite ⟨q, h⟩ else .infinite))).subset
      fun vQ hvQ => ?_
    rcases vQ with p | _
    · by_cases hbad : (p : ℕ) ∈ D.badChars
      · exact Or.inr ⟨p, hbad, by simp [p.2]⟩
      · refine Or.inl fun h => hvQ ?_
        change powMap D e lab i p '' R.region (.finite p) = _
        rw [powMap_eq_id D e lab i p hbad, Set.image_id]
        exact h
    · exact Or.inl hvQ

/-- **The region `S` scaled by `q^{e(i)}` at the labels `lab i`.** -/
noncomputable def pow (S : Region D) : Region D := fun i => powAt D e lab i (S i)

/-- **`LGP·S` is a scaling by powers of `q`**: `e(i) = (i+1)²` at the distinguished labels. -/
lemma lgp_eq_pow (S : Region D) :
    lgp D S = pow D (fun i => (i.1 + 1) ^ 2) (InitialThetaData.distinguished _) S :=
  rfl

lemma proj_pow (S : Region D) (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    LocalTheory.proj D.placeSect (.finite p) c ((pow D e lab S i).region (.finite p)) =
      powElt D e lab i p c • LocalTheory.proj D.placeSect (.finite p) c
        ((S i).region (.finite p)) := by
  change (fun x => x c) '' (powMap D e lab i p '' (S i).region (.finite p)) = _
  rw [Set.image_image]
  unfold LocalTheory.proj
  rw [← Set.image_smul, Set.image_image]
  rfl

/-- `pow D e lab S` is adelic for adelic `S`. -/
theorem isAdelic_pow {S : Region D} (hS : IsAdelic D S) : IsAdelic D (pow D e lab S) := by
  intro i vQ
  rcases vQ with p | _
  · obtain ⟨fam, hfam, hR⟩ := hS i (.finite p)
    refine ⟨fun c => powElt D e lab i p c • fam c, fun c =>
      LocalConstruct.units_smul_mem_admissible (isUnit_powElt D e lab i p c) (hfam c), ?_⟩
    change powMap D e lab i p '' (S i).region (.finite p) = _
    rw [hR]
    ext x
    simp only [DirectSumPresentation.mem_productRegion, Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩ c
      exact ⟨y c, hy c, rfl⟩
    · intro hx
      choose y hy hxy using hx
      exact ⟨y, hy, funext hxy⟩
  · exact hS i .infinite

/-! ### The log-volume of `pow D e lab O` -/

/-- `μ^log(q_v^{e(i)}·O) = −e(i)·ord_p(q_v)·log p`, `v = c(lab i)`. -/
theorem componentVol_powElt (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)
        (powElt D e lab i p c • LocalTheory.integral D.Kt (.finite p)
          (LocalTheory.tuple D.placeSect _ c)) =
      -((e i : ℝ) * ordp D.Kt (LocalTheory.sectPlace D.placeSect (c (lab i)))
        (D.qroot (LocalTheory.sectPlace D.placeSect (c (lab i))))) * Real.log p := by
  classical
  set j := lab i
  set W := fun l => LocalTheory.sectPlace D.placeSect (c l)
  set y : ∀ l, completionAt D.Kt (W l) := Function.update (fun _ => 1) j
    (D.qroot (W j) ^ e i)
  have hy : ∀ l, y l ≠ 0 := by
    intro l
    by_cases h : l = j
    · subst h
      simp only [y, Function.update_self]
      exact pow_ne_zero _ (D.qroot_ne_zero _)
    · simp only [y, Function.update_of_ne h]
      exact one_ne_zero
  have hprod : (∏ l, LocalConstruct.incl p (LocalTheory.tuple D.placeSect _ c) l (W l)
      (LocalTheory.tuple_finite D.placeSect c l) (y l)) = powElt D e lab i p c := by
    rw [Finset.prod_eq_single j]
    · simp only [y, Function.update_self]
      rfl
    · intro l _ hl
      simp only [y, Function.update_of_ne hl, map_one]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hsum : ∑ l, ordp D.Kt (W l) (y l) = (e i : ℝ) * ordp D.Kt (W j) (D.qroot (W j)) := by
    rw [Finset.sum_eq_single j]
    · simp only [y, Function.update_self]
      rw [LocalTheory.ordp_pow D.Kt _ _ (D.qroot_ne_zero _)]
    · intro l _ hl
      simp only [y, Function.update_of_ne hl]
      simp [ordp, norm_one]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have := LocalConstruct.componentVol_prod_incl_smul_integral
    (LocalTheory.tuple_isOver D.placeSect p c) W (LocalTheory.tuple_finite D.placeSect c) y hy
  rw [hprod, hsum] at this
  exact this

/-- The packet log-volume of `pow D e lab O` at `p` is `−e(i)·log(q_p)/(2ℓ)`. -/
theorem packetVol_pow_integral_finite (i : Fin (nC D)) (p : Nat.Primes) :
    (LocalTheory.vol D.placeSect (nC D)).packetVol i (.finite p)
        ((pow D e lab (integralRegion D) i).region (.finite p)) =
      -(e i : ℝ) * ((concreteVariantData D).logQAt p / (2 * D.ℓ)) := by
  rw [LocalTheory.packetVol_eq]
  have hpO : ∀ c, LocalTheory.proj D.placeSect (.finite p) c
      ((integralRegion D i).region (.finite p)) =
      LocalTheory.integral D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c) := fun c =>
    LocalTheory.proj_productRegion D.placeSect _ _
      (fun c => ⟨1, LocalTheory.one_mem_integral D.Kt _ _⟩) c
  have hc : ∀ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
      LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)
        (LocalTheory.proj D.placeSect (.finite p) c
          ((pow D e lab (integralRegion D) i).region (.finite p))) =
      -((e i : ℝ) * ordp D.Kt (LocalTheory.sectPlace D.placeSect (c (lab i)))
        (D.qroot (LocalTheory.sectPlace D.placeSect (c (lab i))))) * Real.log p := by
    intro c
    rw [proj_pow, hpO]
    exact componentVol_powElt D e lab i p c
  simp only [hc]
  have hℓ : (D.ℓ : ℝ) ≠ 0 := by
    have := D.prime.five_le
    change (D.prime.ℓ : ℝ) ≠ 0
    exact_mod_cast (by omega : D.prime.ℓ ≠ 0)
  rw [InitialThetaData.logQAt_eq_sect]
  have key := sum_prod_tuple_mul_coord (LocalTheory.weight D.Fmod (.finite p))
    (LocalTheory.weight_sum_one D.Fmod _)
    (fun v => ordp D.Kt (LocalTheory.sectPlace D.placeSect v)
      (D.qroot (LocalTheory.sectPlace D.placeSect v))) (lab i)
  have hsplit : ∀ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
      LocalTheory.tupleWeight (.finite p) c * (-((e i : ℝ) * ordp D.Kt
        (LocalTheory.sectPlace D.placeSect (c (lab i)))
        (D.qroot (LocalTheory.sectPlace D.placeSect (c (lab i))))) * Real.log p) =
      (-(e i : ℝ) * Real.log p) *
        ((∏ l, LocalTheory.weight D.Fmod (.finite p) (c l)) *
          ordp D.Kt (LocalTheory.sectPlace D.placeSect (c (lab i)))
            (D.qroot (LocalTheory.sectPlace D.placeSect (c (lab i))))) := by
    intro c
    unfold LocalTheory.tupleWeight
    ring
  rw [Finset.sum_congr rfl fun c _ => hsplit c, ← Finset.mul_sum, key]
  field_simp

/-- The global log-volume of `pow D e lab O` at capsule `i` is `−e(i)·log(q)/(2ℓ)`. -/
theorem globalVol_pow_integral (i : Fin (nC D)) :
    (LocalTheory.vol D.placeSect (nC D)).globalVol (pow D e lab (integralRegion D) i) =
      -(e i : ℝ) * (D.qPilot.logQ / (2 * D.ℓ)) := by
  classical
  unfold LogVolumeData.globalVol
  set g := fun vQ => (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ
    ((pow D e lab (integralRegion D) i).region vQ)
  have hinf : g .infinite = 0 :=
    (LocalTheory.vol D.placeSect (nC D)).packetVol_integral i .infinite
  have hsupp : Function.support g ⊆ ↑(badPrimePlaces D) := by
    intro vQ hvQ
    rcases vQ with p | _
    · by_contra h
      apply hvQ
      change (LocalTheory.vol D.placeSect (nC D)).packetVol i (.finite p) _ = 0
      rw [packetVol_pow_integral_finite, logQAt_eq_zero D p, zero_div, mul_zero]
      intro hp
      apply h
      simp only [badPrimePlaces, Finset.coe_image, Set.mem_image, Finset.mem_coe,
        Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨p, hp, rfl⟩
    · exact absurd hinf hvQ
  rw [finsum_eq_sum_of_support_subset g hsupp, badPrimePlaces, Finset.sum_image]
  · rw [Finset.sum_congr rfl fun q _ => (packetVol_pow_integral_finite D e lab i _ :
        g (RationalPlace.finite _) = _),
      Finset.sum_attach (D.qPilot.badFinset.image residueChar)
        (fun q => -(e i : ℝ) * ((concreteVariantData D).logQAt q / (2 * D.ℓ))),
      ← Finset.mul_sum, ← Finset.sum_div, (concreteVariantData D).sum_logQAt
        (s := D.qPilot.badFinset.image residueChar) (fun w hw => Finset.mem_image_of_mem _ hw)]
    rfl
  · intro p _ q _ h
    have := congrArg Subtype.val (RationalPlace.finite.inj h)
    exact Subtype.ext this

/-- **`log-vol(pow D e lab O) = −(avg_i e(i))·|log(q)|`**, for every placement `lab` of the
powers of `q` (the procession-normalized log-volume averages over the capsules). -/
theorem logVol_pow_integral :
    logVol D (pow D e lab (integralRegion D)) =
      -((∑ i, (e i : ℝ)) / nC D * D.qPilot.absLogQ) := by
  unfold logVol LogVolumeData.processionVol
  simp only [globalVol_pow_integral]
  rw [← Finset.sum_mul, QPilotData.absLogQ, Finset.sum_neg_distrib]
  change (-∑ i : Fin (nC D), (e i : ℝ)) * _ / (nC D : ℝ) = _
  ring

/-! ### The `q`-pilot region -/

/-- **The `q`-pilot region `{q_v O_v}`** in the concrete container: in every capsule, the
integral structure scaled by `q_v` (the theta value for `j = 1`) in the tensor factor of the
label `1`; integral at `∞` (see the module docstring for the placement). -/
noncomputable def qRegion : Region D := pow D (fun _ => 1) (labOne D) (integralRegion D)

theorem isAdelic_qRegion : IsAdelic D (qRegion D) :=
  isAdelic_pow D _ _ (isAdelic_integralRegion D)

/-- **The log-volume of the constructed `q`-pilot region is `−|log(q)|`**, the left-hand side of
the Corollary 3.12 variant (IUT III, Corollary 3.12; [LANA], §8.1(a)). -/
theorem logVol_qRegion : logVol D (qRegion D) = (concreteVariantData D).qPilot.lhs := by
  rw [qRegion, logVol_pow_integral]
  have hn : (nC D : ℝ) ≠ 0 := by exact_mod_cast (nC_pos D).ne'
  simp only [Nat.cast_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  rw [div_self hn, one_mul]
  rfl

/-- **In the first capsule (`j = 1`) the `q`-pilot region is `LGP·O`**: there the label `1` is
the distinguished label and the theta value is `q^{1²} = q`. -/
theorem qRegion_first :
    qRegion D ⟨0, nC_pos D⟩ = lgp D (integralRegion D) ⟨0, nC_pos D⟩ :=
  rfl

end Wall

namespace Wall

variable (D : InitialThetaData.{0})

/-- **`η_q` from the constructed region**: the pointed map sending the pilot of the `q`-pilot
BPS to the log-volume (class in `R_ss ≅ ℝ`) of `qRegion D`. -/
noncomputable def etaQReg : (qVal D.bpsDegrees).C →ₗ[ℝ] ℝ :=
  (qVal D.bpsDegrees).eta (logVol D (qRegion D))

/-- The Milestone 1 normalization of `η_q` agrees with the map from the constructed region. -/
theorem etaQReg_eq_etaQ : etaQReg D = etaQ D := by
  rw [etaQReg, etaQ, logVol_qRegion]
  rfl

/-- **`η_q` sends the pilot to the class of the `q`-pilot region `{q_v O_v}` in `R_ss`**
([LANA], §9.2). -/
theorem etaQ_pilot_eq_mk :
    (rssEquiv D).symm (etaQ D (qVal D.bpsDegrees).pilot) =
      Rss.mk D (qRegion D) (isAdelic_qRegion D) := by
  rw [Equiv.symm_apply_eq]
  change etaQ D (qVal D.bpsDegrees).pilot = logVol D (qRegion D)
  rw [← etaQReg_eq_etaQ, etaQReg, ValBPS.eta_pilot]

/-- **`logVol_etaQ_pilot` as a statement about the constructed region**: the class `η_q(φ_C)` is
`[qRegion D]`, whose log-volume is `−|log(q)|`. -/
theorem logVol_etaQ_pilot_eq_qRegion :
    Rss.logVol D ((rssEquiv D).symm (etaQ D (qVal D.bpsDegrees).pilot)) =
      logVol D (qRegion D) ∧ logVol D (qRegion D) = (concreteVariantData D).qPilot.lhs := by
  rw [etaQ_pilot_eq_mk]
  exact ⟨rfl, logVol_qRegion D⟩

end Wall

end Iut
