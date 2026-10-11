/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Wall.Pilots
import Iut.Concrete.Ind1Invariance

/-!
# The real lines `R_val`, `R_ss` and the map `η_q` (the wall, Milestone 1b; taxis #1450)

The two pointed real lines of the LANA interim report (July 2026, [LANA]), §9.2–§9.3, on the
concrete large volume container of the Corollary 3.12 variant (`Iut/Concrete/ThetaRegion.lean`):

* `R_val` is the value-group line `(C, φ_C)` of a BPS (`ValBPS`, `Iut/Wall/BPS.lean`);
* `R_ss = {T ⊆ VC(I) adelic measurable}/(equal volume)` ([LANA], §9.2). Here an *adelic
  measurable region* (`IsAdelic`) is a capsule-indexed family of admissible regions of the
  concrete container (`LocalTheory.container`) each of whose packet regions is a product of
  nonempty, relatively compact, measurable components of positive finite Haar measure — the
  admissible class of the concrete holomorphic hull (`LocalTheory.hull`). `R_ss` is the
  quotient by equality of the procession-normalized log-volume (`Rss`, `logVol`; IUT III,
  Proposition 3.9, Corollary 3.12), and log-volume is a **bijection `R_ss ≃ ℝ`** (`rssEquiv`):
  injective by construction, surjective because rescaling the archimedean components by
  `t > 0` adds `log t` (`logVol_archScale`). This makes `R_ss` a pointed real line, with the
  linear structure transported along `log-vol` ([LANA], §9.3: "another real line `R_ss`").
* `η_q : R_val → R_ss` ([LANA], §9.2) for the `q`-pilot BPS of `D` sends the pilot `|log(q)|`
  to the class of the `q`-pilot region `{q_v O_v}`, whose log-volume is `−|log(q)|`
  (`etaQ`, `logVol_etaQ_pilot : log-vol(η_q(φ_C)) = (qPilot D).lhs`).

**Modelling choice (documented).** The region `{q_v O_v}` "embedded diagonally" into the
container is not constructed: its class in `R_ss` is taken to be the class of log-volume
`(qPilot D).lhs = −|log(q)|`. That the actual region has this log-volume is IUT III,
Proposition 3.9(iii), with the product formula (roadmap package P21; uncontested). So the
lemma `logVol_etaQ_pilot` is a normalization, not a theorem about a region.

## The comparison with the right-hand side

`logVol_le_rhs`: an adelic region contained in the holomorphic hull of a **single
(Ind1)-image** of the concrete theta-pilot region (the theta values `q^{j²}` at labels `l_i`)
has log-volume at most `−|log(Θ)| = (concreteVariantData D).rhsData.rhs`: monotonicity of the
Haar log-volume (`packetVol_le_of_subset`), the computation of the hull (`thetaPilotOn` for
labels `{l_i}`) and the (Ind1)-invariance of its volume (`InitialThetaData.rhsDataOn_singleton`).

`exists_adelic_iff`: conversely every `x ≤ −|log(Θ)|` is the log-volume of such a region (the
hull, rescaled at `∞`). So the set of log-volumes of the adelic regions in the hull of a single
(Ind1)-image is exactly `ℝ_{≤ −|log(Θ)|}`, the set of IUT III, Corollary 3.12 (and [LANA],
§8.3).
-/

namespace Iut

open NumberField MeasureTheory
open scoped Pointwise

universe u

namespace LocalConstruct

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι] {vQ : RationalPlace}
  {c : ι → Place K}

/-- **Monotonicity of the normalized Haar log-volume** for sets of positive finite measure. -/
theorem componentVol_le_of_subset {S T : Set (Tensor K vQ c)} (hST : S ⊆ T)
    (hS : 0 < haar vQ c S) (hT : haar vQ c T < ⊤) :
    componentVol vQ c S ≤ componentVol vQ c T := by
  unfold componentVol
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine Real.log_le_log (div_pos (ENNReal.toReal_pos hS.ne'
    (lt_of_le_of_lt (measure_mono hST) hT).ne) toReal_haar_integralAt_pos) ?_
  exact div_le_div_of_nonneg_right (ENNReal.toReal_mono hT.ne (measure_mono hST))
    toReal_haar_integralAt_pos.le

/-- **Archimedean rescaling of an arbitrary region**: `μ^log(t·S) = μ^log(S) + log t` for
`t > 0` and `S` of positive finite Haar measure. -/
theorem componentVol_smul_infinite {c : ι → Place K} {S : Set (Tensor K .infinite c)}
    (hS : 0 < haar .infinite c S) (hS' : haar .infinite c S < ⊤) {t : ℝ} (ht : 0 < t) :
    componentVol .infinite c (t • S) = componentVol .infinite c S + Real.log t := by
  unfold componentVol
  have hn : (Module.finrank (baseField .infinite) (Tensor K .infinite c) : ℝ) ≠ 0 := by
    exact_mod_cast (finrank_tensor_infinite_pos (c := c)).ne'
  rw [Measure.addHaar_smul (haar .infinite c), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (pow_pos ht _), mul_div_assoc,
    Real.log_mul (pow_pos ht _).ne' (div_pos (ENNReal.toReal_pos hS.ne' hS'.ne)
      toReal_haar_integralAt_pos).ne', Real.log_pow,
    show Module.finrank ℝ (Tensor K .infinite c) =
      Module.finrank (baseField .infinite) (Tensor K .infinite c) from rfl]
  field_simp
  ring

/-- Archimedean rescaling preserves admissibility. -/
theorem smul_mem_admissible_infinite {c : ι → Place K} {S : Set (Tensor K .infinite c)}
    (hS : S ∈ admissible .infinite c) {t : ℝ} (ht : 0 < t) :
    t • S ∈ admissible .infinite c := by
  obtain ⟨hne, hcpt, hmeas, hpos, hfin⟩ := hS
  have hmul := Measure.addHaar_smul (haar .infinite c) t S
  refine ⟨hne.smul_set, ?_, hmeas.const_smul₀ t, ?_, ?_⟩
  · exact (hcpt.smul t).of_isClosed_subset isClosed_closure
      (closure_minimal (Set.smul_set_mono subset_closure) (hcpt.smul t).isClosed)
  · rw [hmul]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (abs_pos.mpr (pow_ne_zero _ ht.ne'))).ne'
      hpos.ne'
  · rw [hmul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- `t·(a·B_I) ⊆ a·B_I` for `0 < t ≤ 1`. -/
theorem smul_smul_integralAt_infinite_subset {c : ι → Place K} (a : Tensor K .infinite c)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    t • (a • integralAt .infinite c) ⊆ a • integralAt .infinite c := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  have hmono := smul_integralAt_infinite_mono c t 1 ht ht1
  rw [map_one, one_smul] at hmono
  refine ⟨algebraMap ℝ (Tensor K .infinite c) t * y, hmono ⟨y, hy, rfl⟩, ?_⟩
  simp only [smul_eq_mul]
  rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc, mul_comm a]

end LocalConstruct

namespace LocalTheory

variable {K : Type u} [Field K] [NumberField K] {k : Type u} [Field k] [NumberField k]
  (σ : PlaceSection K k) (n : ℕ)

/-- A packet region is admissible for the concrete hull system iff it is a product of
admissible components. -/
lemma mem_admissible_hull_iff (i : Fin (container σ n).proc.length) (vQ : RationalPlace)
    (U : Set ((container σ n).packet i vQ).Total) :
    U ∈ ((hull σ n).system i vQ).Admissible ↔
      ∃ fam : ∀ c, Set (Tensor K vQ (tuple σ vQ c)),
        (∀ c, fam c ∈ admissible K vQ (tuple σ vQ c)) ∧ U = (packet σ _ vQ).productRegion fam :=
  Iff.rfl

/-- The packet log-volume as a sum over the tuples `c : S_{j+1} → V_{v_ℚ}`. -/
lemma packetVol_eq (i : Fin (container σ n).proc.length) (vQ : RationalPlace)
    (U : Set ((container σ n).packet i vQ).Total) :
    (vol σ n).packetVol i vQ U =
      ∑ c : ((Procession.standard n).capsule i).LabelType → Fiber k vQ,
        tupleWeight vQ c * componentVol K vQ (tuple σ vQ c) (proj σ vQ c U) :=
  @Fintype.sum_equiv _ _ ℝ ((container σ n).instFintypeComponents i vQ) Pi.instFintype _
    (Equiv.refl _) _ _ fun _ => rfl

/-- **Monotonicity of the packet log-volume** between a product region with admissible
components and any region whose components have finite measure. -/
theorem packetVol_le_of_subset (i : Fin (container σ n).proc.length) (vQ : RationalPlace)
    {U R : Set ((container σ n).packet i vQ).Total}
    (hU : U ∈ ((hull σ n).system i vQ).Admissible)
    (hR : ∀ c, LocalConstruct.haar vQ (tuple σ vQ c) (proj σ vQ c R) < ⊤) (hUR : U ⊆ R) :
    (vol σ n).packetVol i vQ U ≤ (vol σ n).packetVol i vQ R := by
  obtain ⟨fam, hfam, rfl⟩ := hU
  rw [packetVol_eq, packetVol_eq]
  refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_
    (Finset.prod_nonneg fun l _ => (weight_pos k _ _).le)
  have hproj := proj_productRegion σ vQ fam (fun c => admissible_nonempty K vQ _ _ (hfam c)) c
  refine LocalConstruct.componentVol_le_of_subset (Set.image_mono hUR) ?_ (hR c)
  rw [hproj]
  exact (hfam c).2.2.2.1

/-- The components of a hull region `a·O` have finite measure. -/
lemma haar_proj_scaledIntegral_lt_top (i : Fin n) (vQ : RationalPlace)
    (a : (packet σ ((Procession.standard n).capsule i).LabelType vQ).Total)
    (c : ((Procession.standard n).capsule i).LabelType → Fiber k vQ) :
    LocalConstruct.haar vQ (tuple σ vQ c)
      (proj σ vQ c ((packet σ _ vQ).scaledIntegral a)) < ⊤ := by
  have h : (packet σ ((Procession.standard n).capsule i).LabelType vQ).scaledIntegral a =
      (packet σ _ vQ).productRegion fun c => scaled σ vQ c (a c) := rfl
  have hp := proj_productRegion σ vQ (fun c => scaled σ vQ c (a c)) (fun c => ⟨_,
    Set.smul_mem_smul_set (one_mem_integral K vQ (tuple σ vQ c))⟩) c
  rw [h, hp]
  exact LocalConstruct.haar_smul_integralAt_lt_top _

/-- **Monotonicity of the procession-normalized log-volume**, from the placewise inequalities
of the packet log-volumes. -/
theorem processionVol_le_of_packetVol (R S : ∀ i : Fin (container σ n).proc.length,
      (container σ n).AdmissibleRegion i)
    (h : ∀ i vQ, (vol σ n).packetVol i vQ ((R i).region vQ) ≤
      (vol σ n).packetVol i vQ ((S i).region vQ)) :
    (vol σ n).processionVol R ≤ (vol σ n).processionVol S := by
  unfold LogVolumeData.processionVol
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _)
  exact finsum_le_finsum' ((vol σ n).finite_support_packetVol _)
    ((vol σ n).finite_support_packetVol _) (h i)

/-! ### Archimedean rescaling of a region of the container -/

/-- The packet regions of the archimedean rescaling: unchanged at the primes, the product of
the rescaled components `t·U_c` at `∞`. -/
def archRegion (t : ℝ) (i : Fin (container σ n).proc.length)
    (R : (container σ n).AdmissibleRegion i) :
    ∀ vQ : RationalPlace, Set ((container σ n).packet i vQ).Total
  | .finite p => R.region (.finite p)
  | .infinite => (packet σ _ .infinite).productRegion fun c =>
      t • proj σ .infinite c (R.region .infinite)

/-- **The archimedean rescaling** of an admissible region by `t`. -/
def archScale (t : ℝ) (i : Fin (container σ n).proc.length)
    (R : (container σ n).AdmissibleRegion i) : (container σ n).AdmissibleRegion i where
  region := archRegion σ n t i R
  finiteSupport := (R.finiteSupport.union (Set.finite_singleton .infinite)).subset
    fun vQ hvQ => by
      rcases vQ with p | _
      · exact Or.inl hvQ
      · exact Or.inr rfl

lemma archScale_region_finite (t : ℝ) (i : Fin (container σ n).proc.length)
    (R : (container σ n).AdmissibleRegion i) (p : Nat.Primes) :
    (archScale σ n t i R).region (.finite p) = R.region (.finite p) := rfl

lemma archScale_region_infinite (t : ℝ) (i : Fin (container σ n).proc.length)
    (R : (container σ n).AdmissibleRegion i) :
    (archScale σ n t i R).region .infinite = (packet σ _ .infinite).productRegion fun c =>
      t • proj σ .infinite c (R.region .infinite) := rfl

/-- The archimedean rescaling of a hull-admissible region is hull-admissible. -/
theorem isAdmissible_archScale {t : ℝ} (ht : 0 < t) (i : Fin (container σ n).proc.length)
    {R : (container σ n).AdmissibleRegion i} (hR : (hull σ n).IsAdmissible R) :
    (hull σ n).IsAdmissible (archScale σ n t i R) := by
  intro vQ
  rcases vQ with p | _
  · exact hR (.finite p)
  · obtain ⟨fam, hfam, hR'⟩ := hR .infinite
    refine ⟨fun c => t • fam c, fun c => ?_, ?_⟩
    · exact LocalConstruct.smul_mem_admissible_infinite (hfam c) ht
    · rw [archScale_region_infinite, hR']
      congr 1
      funext c
      rw [proj_productRegion σ _ fam (fun c => admissible_nonempty K _ _ _ (hfam c))]

/-- The tuple weights over the archimedean place sum to `1`. -/
lemma sum_tupleWeight (i : Fin (container σ n).proc.length) (vQ : RationalPlace) :
    ∑ c : ((Procession.standard n).capsule i).LabelType → Fiber k vQ, tupleWeight vQ c = 1 :=
  sum_prod_tuple_eq_one _ (weight_sum_one k vQ)

/-- **The archimedean rescaling adds `log t` to the packet log-volume at `∞`.** -/
theorem packetVol_archScale_infinite {t : ℝ} (ht : 0 < t) (i : Fin (container σ n).proc.length)
    {R : (container σ n).AdmissibleRegion i} (hR : (hull σ n).IsAdmissible R) :
    (vol σ n).packetVol i .infinite ((archScale σ n t i R).region .infinite) =
      (vol σ n).packetVol i .infinite (R.region .infinite) + Real.log t := by
  obtain ⟨fam, hfam, hR'⟩ := hR .infinite
  have hne : ∀ c, (fam c).Nonempty := fun c => admissible_nonempty K _ _ _ (hfam c)
  have hp : ∀ c, proj σ .infinite c (R.region .infinite) = fam c := fun c => by
    rw [hR', proj_productRegion σ _ fam hne]
  rw [packetVol_eq, packetVol_eq]
  have key : ∀ c : ((Procession.standard n).capsule i).LabelType → Fiber k .infinite,
      tupleWeight .infinite c * componentVol K .infinite (tuple σ .infinite c)
        (proj σ .infinite c ((archScale σ n t i R).region .infinite)) =
      tupleWeight .infinite c * componentVol K .infinite (tuple σ .infinite c)
        (proj σ .infinite c (R.region .infinite)) + Real.log t * tupleWeight .infinite c := by
    intro c
    have hq : proj σ .infinite c ((archScale σ n t i R).region .infinite) = t • fam c := by
      rw [archScale_region_infinite]
      refine (proj_productRegion σ _ (fun c => t • proj σ .infinite c (R.region .infinite))
        (fun c => by rw [hp c]; exact (hne c).smul_set) c).trans ?_
      rw [hp c]
    rw [hq, hp c]
    change tupleWeight .infinite c * LocalConstruct.componentVol .infinite _ (t • fam c) = _
    rw [LocalConstruct.componentVol_smul_infinite (hfam c).2.2.2.1 (hfam c).2.2.2.2 ht]
    change _ = tupleWeight .infinite c * LocalConstruct.componentVol .infinite _ (fam c) + _
    ring
  rw [Finset.sum_congr rfl fun c _ => key c, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_tupleWeight, mul_one]

/-- **The archimedean rescaling adds `log t` to the global log-volume.** -/
theorem globalVol_archScale {t : ℝ} (ht : 0 < t) (i : Fin (container σ n).proc.length)
    {R : (container σ n).AdmissibleRegion i} (hR : (hull σ n).IsAdmissible R) :
    (vol σ n).globalVol (archScale σ n t i R) = (vol σ n).globalVol R + Real.log t := by
  classical
  unfold LogVolumeData.globalVol
  have key : (fun vQ => (vol σ n).packetVol i vQ ((archScale σ n t i R).region vQ)) =
      fun vQ => (vol σ n).packetVol i vQ (R.region vQ) +
        if vQ = RationalPlace.infinite then Real.log t else 0 := by
    funext vQ
    rcases vQ with p | _
    · rw [if_neg (by simp), add_zero]
      rfl
    · rw [if_pos rfl, packetVol_archScale_infinite σ n ht i hR]
  rw [key, finsum_add_distrib ((vol σ n).finite_support_packetVol R)
    ((Set.finite_singleton RationalPlace.infinite).subset fun vQ hvQ => by
      by_contra h
      exact hvQ (if_neg h)),
    finsum_eq_single _ RationalPlace.infinite fun x hx => if_neg hx, if_pos rfl]

/-- **The archimedean rescaling adds `log t` to the procession-normalized log-volume**,
for `n ≥ 1` capsules. -/
theorem processionVol_archScale {t : ℝ} (ht : 0 < t) (hn : 0 < n)
    {R : ∀ i : Fin (container σ n).proc.length, (container σ n).AdmissibleRegion i}
    (hR : ∀ i, (hull σ n).IsAdmissible (R i)) :
    (vol σ n).processionVol (fun i => archScale σ n t i (R i)) =
      (vol σ n).processionVol R + Real.log t := by
  unfold LogVolumeData.processionVol
  simp only [globalVol_archScale σ n ht _ (hR _), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ((container σ n).proc.length : ℝ) = n := rfl
  rw [this]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end LocalTheory

namespace Wall

variable (D : InitialThetaData.{u})

/-- The number of capsules `ℓ* = (ℓ − 1)/2`. -/
abbrev nC : ℕ := (D.ℓ - 1) / 2

lemma nC_pos : 0 < nC D := by
  have := D.prime.five_le
  change 0 < (D.prime.ℓ - 1) / 2
  omega

/-- The concrete large volume container of `D` (`LocalTheory.container`). -/
noncomputable abbrev VC := LocalTheory.container D.placeSect (nC D)

/-- **A region of the container**: a capsule-indexed family of admissible regions. -/
abbrev Region := ∀ i : Fin (VC D).proc.length, (VC D).AdmissibleRegion i

/-- **Adelic measurable regions** ([LANA], §6 (Ind3), §9.2): every packet region is a product of
admissible components (nonempty, relatively compact, measurable, of positive finite Haar
measure), and almost all of them are the integral structure. -/
def IsAdelic (U : Region D) : Prop :=
  ∀ i, (LocalTheory.hull D.placeSect (nC D)).IsAdmissible (U i)

/-- **The log-volume** of a region: the procession-normalized log-volume (IUT III,
Proposition 3.9(iii); [LANA], §5.2(e)). -/
noncomputable def logVol (U : Region D) : ℝ :=
  (LocalTheory.vol D.placeSect (nC D)).processionVol U

/-- The holomorphic hull of a region, capsule-wise. -/
noncomputable abbrev hullOf (U : Region D) : Region D :=
  (LocalTheory.hull D.placeSect (nC D)).hullFamily U

/-- **The concrete theta-pilot region with the theta value of capsule `i` at the label
`l i`**: one (Ind1)-image of IUT IV's theta-pilot region (`thetaFiniteOn_singleton_eq_image`). -/
noncomputable abbrev thetaImage (l : ∀ i : Fin (nC D), InitialThetaData.Lab (nC D) i) :
    Region D :=
  D.thetaPilotOn (nC D) (fun i => {l i}) fun _ => Set.singleton_nonempty _

/-- **An adelic region in the hull of a single (Ind1)-image of the theta-pilot region.** -/
def InHullOfImage (U : Region D) : Prop :=
  ∃ l : ∀ i : Fin (nC D), InitialThetaData.Lab (nC D) i, ∀ i, U i ≤ hullOf D (thetaImage D l) i

/-- **An adelic region in a single (Ind1)-image of the theta-pilot region** (the possible
images `LGP·U` of [LANA], §6.2(i)). -/
def InImage (U : Region D) : Prop :=
  ∃ l : ∀ i : Fin (nC D), InitialThetaData.Lab (nC D) i, ∀ i, U i ≤ thetaImage D l i

lemma thetaImage_isAdmissible (l : ∀ i : Fin (nC D), InitialThetaData.Lab (nC D) i) (i) :
    (LocalTheory.hull D.placeSect (nC D)).IsAdmissible (thetaImage D l i) :=
  (D.rhsDataOn (fun i => {l i}) fun _ => Set.singleton_nonempty _).thetaPilot_hullAdmissible i

lemma InImage.inHullOfImage {U : Region D} (h : InImage D U) : InHullOfImage D U := by
  obtain ⟨l, hl⟩ := h
  exact ⟨l, fun i vQ => (hl i vQ).trans
    ((LocalTheory.hull D.placeSect (nC D)).le_hullAdmissible (thetaImage_isAdmissible D l i) vQ)⟩

/-- The right-hand side `−|log(Θ)|` is the log-volume of the hull of the theta-pilot region. -/
lemma rhs_eq_logVol : (concreteVariantData D).rhsData.rhs = logVol D (hullOf D (D.thetaPilot _)) :=
  rfl

/-- The right-hand side is the log-volume of the hull of any single (Ind1)-image. -/
lemma rhs_eq_logVol_image (l : ∀ i : Fin (nC D), InitialThetaData.Lab (nC D) i) :
    (concreteVariantData D).rhsData.rhs = logVol D (hullOf D (thetaImage D l)) :=
  (D.rhsDataOn_singleton l).symm

/-- Hull regions are hull-admissible. -/
lemma isAdmissible_hullOf (U : Region D) (hU : IsAdelic D U) : IsAdelic D (hullOf D U) := by
  intro i vQ
  obtain ⟨a, ha, h⟩ := LocalTheory.isHullRegion_of_mem_hullRegions D.placeSect _ vQ _
    (((LocalTheory.hull D.placeSect (nC D)).system i vQ).hull_mem_hullRegions (hU i vQ))
  exact ⟨fun c => LocalTheory.scaled D.placeSect vQ c (a c),
    fun c => LocalTheory.smul_integral_admissible D.Kt vQ _ (a c) (ha c), h⟩

/-- **The log-volume bound**: an adelic region in the hull of a single (Ind1)-image of the
theta-pilot region has log-volume at most `−|log(Θ)|`. -/
theorem logVol_le_rhs {U : Region D} (hU : IsAdelic D U) (hI : InHullOfImage D U) :
    logVol D U ≤ (concreteVariantData D).rhsData.rhs := by
  obtain ⟨l, hl⟩ := hI
  rw [rhs_eq_logVol_image D l]
  refine LocalTheory.processionVol_le_of_packetVol _ _ _ _ fun i vQ => ?_
  refine LocalTheory.packetVol_le_of_subset _ _ i vQ (hU i vQ) (fun c => ?_) (hl i vQ)
  obtain ⟨a, -, h⟩ := LocalTheory.isHullRegion_of_mem_hullRegions D.placeSect _ vQ _
    (((LocalTheory.hull D.placeSect (nC D)).system i vQ).hull_mem_hullRegions
      (thetaImage_isAdmissible D l i vQ))
  change LocalConstruct.haar vQ _ (LocalTheory.proj D.placeSect vQ c
    (((LocalTheory.hull D.placeSect (nC D)).system i vQ).hull ((thetaImage D l i).region vQ)))
    < ⊤
  rw [h]
  exact LocalTheory.haar_proj_scaledIntegral_lt_top D.placeSect _ i vQ a c

/-- The archimedean rescaling of a region. -/
noncomputable def archScale (t : ℝ) (U : Region D) : Region D :=
  fun i => LocalTheory.archScale D.placeSect (nC D) t i (U i)

lemma isAdelic_archScale {t : ℝ} (ht : 0 < t) {U : Region D} (hU : IsAdelic D U) :
    IsAdelic D (archScale D t U) :=
  fun i => LocalTheory.isAdmissible_archScale _ _ ht i (hU i)

theorem logVol_archScale {t : ℝ} (ht : 0 < t) {U : Region D} (hU : IsAdelic D U) :
    logVol D (archScale D t U) = logVol D U + Real.log t :=
  LocalTheory.processionVol_archScale _ _ ht (nC_pos D) hU

/-- **The set of log-volumes of the adelic regions in the hull of a single (Ind1)-image of the
theta-pilot region is `ℝ_{≤ −|log(Θ)|}`** (IUT III, Corollary 3.12; [LANA], §8.3). -/
theorem exists_adelic_iff (x : ℝ) :
    (∃ U : Region D, IsAdelic D U ∧ InHullOfImage D U ∧ logVol D U = x) ↔
      x ≤ (concreteVariantData D).rhsData.rhs := by
  constructor
  · rintro ⟨U, hU, hI, rfl⟩
    exact logVol_le_rhs D hU hI
  · intro hx
    set H := hullOf D (D.thetaPilot (nC D))
    have hH : IsAdelic D H := isAdmissible_hullOf D _ fun i =>
      (D.rhsDataOn _ (InitialThetaData.ivLabels_nonempty _)).thetaPilot_hullAdmissible i
    set t := Real.exp (x - (concreteVariantData D).rhsData.rhs)
    have ht : 0 < t := Real.exp_pos _
    have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    refine ⟨archScale D t H, isAdelic_archScale D ht hH, ⟨InitialThetaData.distinguished _,
      fun i => ?_⟩, ?_⟩
    · intro vQ
      rcases vQ with p | _
      · exact subset_rfl
      · intro y hy
        obtain ⟨a, -, h⟩ := LocalTheory.isHullRegion_of_mem_hullRegions D.placeSect _ _ _
          (((LocalTheory.hull D.placeSect (nC D)).system i .infinite).hull_mem_hullRegions
            ((D.rhsDataOn _ (InitialThetaData.ivLabels_nonempty _)).thetaPilot_hullAdmissible
              i .infinite))
        have hHi : (H i).region .infinite =
            (LocalTheory.packet D.placeSect _ .infinite).productRegion fun c =>
              LocalTheory.scaled D.placeSect .infinite c (a c) := h
        change y ∈ (H i).region .infinite
        have hy' : ∀ c, y c ∈ t • LocalTheory.proj D.placeSect .infinite c
            ((H i).region .infinite) := hy
        rw [hHi]
        intro c
        have hy'' := hy' c
        rw [hHi, LocalTheory.proj_productRegion D.placeSect _
          (fun c => LocalTheory.scaled D.placeSect .infinite c (a c)) (fun c => ⟨_,
            Set.smul_mem_smul_set (LocalTheory.one_mem_integral D.Kt _
              (LocalTheory.tuple D.placeSect _ c))⟩) c] at hy''
        exact LocalConstruct.smul_smul_integralAt_infinite_subset _ ht ht1 hy''
    · rw [logVol_archScale D ht hH, ← rhs_eq_logVol, Real.log_exp]
      ring

/-! ### The real line `R_ss` -/

/-- **`R_ss`** ([LANA], §9.2): adelic measurable regions modulo equal log-volume. -/
noncomputable def Rss : Type _ :=
  Quotient (Setoid.comap (fun U : {U : Region D // IsAdelic D U} => logVol D U.1) ⊥)

/-- The class `[T] ∈ R_ss` of an adelic region. -/
noncomputable def Rss.mk (U : Region D) (hU : IsAdelic D U) : Rss D := Quotient.mk _ ⟨U, hU⟩

/-- The log-volume `R_ss → ℝ`. -/
noncomputable def Rss.logVol : Rss D → ℝ :=
  Quotient.lift (fun U : {U : Region D // IsAdelic D U} => Wall.logVol D U.1) fun _ _ h => h

lemma Rss.logVol_mk (U : Region D) (hU : IsAdelic D U) :
    Rss.logVol D (Rss.mk D U hU) = Wall.logVol D U := rfl

/-- Two classes agree iff the log-volumes agree. -/
theorem Rss.mk_eq_mk_iff (U U' : Region D) (hU : IsAdelic D U) (hU' : IsAdelic D U') :
    Rss.mk D U hU = Rss.mk D U' hU' ↔ Wall.logVol D U = Wall.logVol D U' :=
  Quotient.eq

lemma Rss.logVol_injective : Function.Injective (Rss.logVol D) := by
  rintro ⟨U⟩ ⟨U'⟩ h
  exact Quotient.sound h

/-- The integral structure, as an adelic region of log-volume `0`. -/
noncomputable def integralRegion : Region D := fun i => (VC D).integralAdmissible i

lemma isAdelic_integralRegion : IsAdelic D (integralRegion D) := fun i vQ =>
  (LocalTheory.hull D.placeSect (nC D)).integral_admissible i vQ

lemma logVol_integralRegion : logVol D (integralRegion D) = 0 := by
  simp [logVol, LogVolumeData.processionVol, integralRegion]

/-- Every real number is the log-volume of an adelic region. -/
lemma logVol_surjective (x : ℝ) :
    ∃ U, ∃ _ : IsAdelic D U, logVol D U = x :=
  ⟨archScale D (Real.exp x) (integralRegion D),
    isAdelic_archScale D (Real.exp_pos x) (isAdelic_integralRegion D), by
    rw [logVol_archScale D (Real.exp_pos x) (isAdelic_integralRegion D),
      logVol_integralRegion, Real.log_exp, zero_add]⟩

/-- **`R_ss` is a real line**: the log-volume is a bijection `R_ss ≃ ℝ` ([LANA], §9.3). -/
noncomputable def rssEquiv : Rss D ≃ ℝ :=
  Equiv.ofBijective (Rss.logVol D) ⟨Rss.logVol_injective D, fun x => by
    obtain ⟨U, hU, h⟩ := logVol_surjective D x
    exact ⟨Rss.mk D U hU, h⟩⟩

end Wall

namespace Wall

variable (D : InitialThetaData.{0})

/-- **The map `η_q : R_val → R_ss`** ([LANA], §9.2) of the `q`-pilot BPS of `D`, with `R_ss`
identified with `ℝ` by log-volume (`rssEquiv`): it sends the pilot `|log(q)|` to the class of
the `q`-pilot region `{q_v O_v}`, of log-volume `−|log(q)|` (see the module docstring for the
modelling choice). It is an isomorphism of pointed real lines (`etaQ_bijective`). -/
noncomputable def etaQ : (qVal D.bpsDegrees).C →ₗ[ℝ] ℝ :=
  (qVal D.bpsDegrees).eta D.qPilot.lhs

/-- **`log-vol(η_q(φ_C)) = −|log(q)|`**, the left-hand side of the Corollary 3.12 variant. -/
theorem logVol_etaQ_pilot :
    Rss.logVol D ((rssEquiv D).symm (etaQ D (qVal D.bpsDegrees).pilot)) =
      (concreteVariantData D).qPilot.lhs := by
  change rssEquiv D ((rssEquiv D).symm _) = _
  rw [Equiv.apply_symm_apply, etaQ, ValBPS.eta_pilot]
  rfl

theorem etaQ_bijective : Function.Bijective (etaQ D) :=
  (qVal D.bpsDegrees).eta_bijective D.lhs_neg.ne

end Wall

end Iut
