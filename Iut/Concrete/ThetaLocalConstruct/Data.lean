/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.ThetaRegion
import Iut.Concrete.ThetaLocalConstruct.Ordp
import Iut.Concrete.ThetaLocalConstruct.Roots
import Iut.Concrete.ThetaLocalConstruct.TateCompat
import Iut.Anabelian.LocalInputs
import Iut.Cor312.ThetaData.SqrtAtBadPlace

/-!
# Construction of the local theta data

The data `Iut.ThetaLocalData D LT` of `Iut.Concrete.ThetaRegion` (the `2ℓ`-th roots
`q_v = q^{1/2ℓ}` of the Tate parameters at the bad places of the `ℓ`-torsion field `K`, with
the comparison maps `F_w → K_v`) are constructed here from the initial Θ-data `D`:

* the comparison map `F_w → K_v` is `Iut.embedCompletion` (the inclusion `F → K` raises the
  `w`-adic valuation to the power `e(v/w)`, hence is uniformly continuous);
* at a place `v ∣ w` over `V(F)^bad`, the Tate structure `D.tate.S v` of `E` over `K_v` has
  Tate parameter the image of the Tate parameter `q_w` of `E` over `F_w`
  (`Iut.TateStructure.t_q_eq_embedCompletion`, from the uniqueness of the Tate parameter
  with given `j`-invariant), and `q_w` has a `2ℓ`-th root in `K_v` because `E(K_v)[ℓ]` has
  `ℓ²` elements (`E[ℓ] ⊆ E(K)`, `Iut.TateFamily.sq_le_card_torsion`) and `E(K_v)[2]` has `4`
  elements (`E[2] ⊆ E(F)`, the hypothesis `htwo`; `Iut.TateStructure.exists_pow_eq_q`);
* `ord_p(q_v) = ord_w(q_w)/(2ℓ·e_w)` from the invariance of `ord_p` under the comparison map
  (`Iut.ordp_embedCompletion`) and `ord_p(q_w) = ord_w(q_w)/e_w` (`Iut.ordp_tateParameter`);
* the base-change invariance of the `q`-degree from the fundamental identity
  `∑_{v ∣ w} e_v f_v = [K : F]·e_w f_w` (`Iut.sum_localDeg_liesOver`).

The hypotheses on `D` beyond its fields are the `q`-pilot inputs `QI : QPilotInputs D` (the
finiteness of the bad locus) and the rationality of the `2`-torsion over `F` in the form
`htwo : 2 * 2 ≤ Nat.card (E(F)[2])` (a consequence of `SixTorsionRational`, i.e. of IUT I,
Definition 3.1(b), together with `|E(F̄)[2]| = 4`).
-/

namespace Iut

open NumberField WeierstrassCurve Iut.Anabelian TateCurvesTheta
open scoped Classical

universe u v

noncomputable section

/-! ### The place below a place -/

section Under

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The place of `k` below a place of `K` over `w` is `w`. -/
lemma eq_placeUnder_of_liesOver {v : FinitePlace K} {w : FinitePlace k}
    (hvw : FinitePlace.LiesOver v w) : w = placeUnder v := by
  apply (FinitePlace.maximalIdeal_inj _ _).mp
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [placeUnder_maximalIdeal]
  exact hvw.over

end Under

/-! ### Places over the bad places of `F` -/

section BadPlaces

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

/-- The classical decidable equality on `K`, as used by the model orbicurves. -/
local instance (priority := 1100) instDecidableEqIntermediateFieldTLC : DecidableEq ↥K :=
  fun a b => Classical.propDecidable (a = b)

/-- A place of `K` over a place of `V(F)^bad` is a bad place of `K`. -/
lemma isBadPlace_of_liesOver {v : FinitePlace ↥K} {w : FinitePlace F}
    (hvw : FinitePlace.LiesOver v w) (hw : w ∈ badPlacesOver F E VBad) :
    IsBadPlace E K VBad v := by
  obtain ⟨u, hu, hwu⟩ := hw
  exact ⟨u, hu, FinitePlace.liesOver_trans hvw hwu⟩

/-- A bad place of `K` lies over a place of `V(F)^bad`. -/
lemma exists_liesOver_of_isBadPlace {v : FinitePlace ↥K} (hv : IsBadPlace E K VBad v) :
    ∃ w ∈ badPlacesOver F E VBad, FinitePlace.LiesOver v w := by
  obtain ⟨u, hu, hvu⟩ := hv
  refine ⟨placeUnder v, ⟨u, hu, ?_⟩, liesOver_placeUnder v⟩
  haveI : v.maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal := hvu
  refine ⟨?_⟩
  rw [hvu.over, placeUnder_maximalIdeal, Ideal.under_def, Ideal.under_def, Ideal.comap_comap,
    ← IsScalarTower.algebraMap_eq]

omit [E.IsElliptic] in
/-- Four rational `2`-torsion points over `F` give four rational `2`-torsion points over
`K_v`. -/
lemma four_le_card_torsion_two
    (htwo : 2 * 2 ≤ Nat.card ↥(AddSubgroup.torsionBy E.toAffine.Point ((2 : ℕ) : ℤ)))
    (v : FinitePlace ↥K) (S : TateStructure (curveKw E K v)) :
    2 * 2 ≤ Nat.card ↥(TateStructure.torsion 2 (curveKw E K v)) := by
  haveI := S.finite_torsion 2
  let f : E.toAffine.Point →+ (curveKw E K v).toAffine.Point :=
    (pointMap (curveK E K) (emb K v)).comp (pointMap E (algebraMap F ↥K))
  have hf : Function.Injective f := by
    intro a b hab
    simp only [f, AddMonoidHom.comp_apply] at hab
    exact pointMap_injective _ _ (pointMap_injective _ _ hab)
  have hmem : ∀ P ∈ AddSubgroup.torsionBy E.toAffine.Point ((2 : ℕ) : ℤ),
      f P ∈ TateStructure.torsion 2 (curveKw E K v) := by
    intro P hP
    rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
    rw [← map_nsmul, hP, map_zero]
  refine htwo.trans (Nat.card_le_card_of_injective (fun P => ⟨f P.1, hmem P.1 P.2⟩) ?_)
  intro P Q h
  exact Subtype.ext (hf (congrArg Subtype.val h))

end BadPlaces

/-! ### The roots at the bad places of the torsion field -/

section Roots

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable (P : AdmissiblePrimeData F E Fbar VBad) [NumberField ↥P.torsionField]
variable (TF : TateFamily E P.torsionField P.ℓ VBad)

/-- **Existence of the `2ℓ`-th root of the Tate parameter** at a bad place of `K`. -/
theorem exists_qroot
    (htwo : 2 * 2 ≤ Nat.card ↥(AddSubgroup.torsionBy E.toAffine.Point ((2 : ℕ) : ℤ)))
    {v : FinitePlace ↥P.torsionField} (hv : IsBadPlace E P.torsionField VBad v) :
    ∃ x : localCompletion v, x ^ (2 * P.ℓ) = ((TF.S v hv).t.q : localCompletion v) :=
  haveI : NeZero P.ℓ := ⟨P.ℓ_prime.ne_zero⟩
  (TF.S v hv).exists_pow_eq_q P.ℓ (P.ℓ_prime.odd_of_ne_two (by have := P.five_le; omega))
    (TF.sq_le_card_torsion P hv) (four_le_card_torsion_two E P.torsionField htwo v (TF.S v hv))

end Roots

/-! ### The weighted sum over the places above a prime -/

section Sum

variable {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

/-- The weighted sum `∑_{v ∣ p} ([K_v : ℚ_p]/[K : ℚ])·o(v)` for a function `o` on the places
of `K` which is `c(w)/e_w` at the places over `w ∈ B` and `0` at the places over no `w ∈ B`,
equals `∑_{w ∈ B, w ∣ p} (f_w/[F : ℚ])·c(w)`. -/
theorem sum_placeWeight_mul (p : ℕ) [Fintype {v : FinitePlace K // residueChar v = p}]
    (B : Set (FinitePlace F)) (bad : Finset (FinitePlace F)) (hbad : ↑bad = B)
    (c : FinitePlace F → ℝ) (o : FinitePlace K → ℝ)
    (ho : ∀ v w, FinitePlace.LiesOver v w → w ∈ B → o v = c w / ramIdx F w)
    (ho0 : ∀ v, (∀ w ∈ B, ¬ FinitePlace.LiesOver v w) → o v = 0) :
    ∑ v : {v : FinitePlace K // residueChar v = p}, placeWeight K v.1 * o v.1 =
      ∑ w ∈ bad.filter (fun w => residueChar w = p),
        (inertDeg F w : ℝ) / Module.finrank ℚ F * c w := by
  have hmemB : ∀ w, w ∈ bad ↔ w ∈ B := fun w => by rw [← Finset.mem_coe, hbad]
  set s : Finset {v : FinitePlace K // residueChar v = p} :=
    Finset.univ.filter (fun v => ∃ w ∈ B, FinitePlace.LiesOver v.1 w) with hs
  set t : Finset (FinitePlace F) := bad.filter (fun w => residueChar w = p) with ht
  -- only the places over `B` contribute
  have h1 : ∑ v : {v : FinitePlace K // residueChar v = p}, placeWeight K v.1 * o v.1 =
      ∑ v ∈ s, placeWeight K v.1 * o v.1 := by
    symm
    apply Finset.sum_filter_of_ne
    intro v _ hne
    by_contra h
    push Not at h
    exact hne (by rw [ho0 v.1 h, mul_zero])
  -- group the places by the place of `F` below
  have hmaps : ∀ v ∈ s, placeUnder v.1 ∈ t := by
    intro v hv
    obtain ⟨w, hwB, hvw⟩ := (Finset.mem_filter.mp hv).2
    have hw : w = placeUnder v.1 := eq_placeUnder_of_liesOver hvw
    rw [← hw]
    refine Finset.mem_filter.mpr ⟨(hmemB _).mpr hwB, ?_⟩
    rw [← residueChar_eq_of_liesOver hvw]
    exact v.2
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun w hw => ?_
  obtain ⟨hwbad, hwp⟩ := Finset.mem_filter.mp hw
  have hwB : w ∈ B := (hmemB w).mp hwbad
  have hfib : ∀ v ∈ s.filter (fun v => placeUnder v.1 = w), FinitePlace.LiesOver v.1 w := by
    intro v hv
    have := (Finset.mem_filter.mp hv).2
    rw [← this]
    exact liesOver_placeUnder v.1
  have hsum : ∑ v ∈ s.filter (fun v => placeUnder v.1 = w), placeWeight K v.1 * o v.1 =
      (c w / ramIdx F w / Module.finrank ℚ K) *
        ∑ v ∈ s.filter (fun v => placeUnder v.1 = w), (localDeg K v.1 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [ho v.1 w (hfib v hv) hwB]
    unfold placeWeight
    ring
  -- the fundamental identity for the places over `w`
  have hS : ∑ v ∈ (s.filter (fun v => placeUnder v.1 = w)).map
      (Function.Embedding.subtype _), localDeg K v = Module.finrank F K * localDeg F w := by
    apply sum_localDeg_liesOver w
    intro v
    rw [Finset.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hfib u hu
    · intro hvw
      refine ⟨⟨v, by rw [residueChar_eq_of_liesOver hvw, hwp]⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hwB, hvw⟩,
        (eq_placeUnder_of_liesOver hvw).symm⟩
  rw [Finset.sum_map] at hS
  simp only [Function.Embedding.coe_subtype] at hS
  rw [hsum, ← Nat.cast_sum, hS]
  have hKQ : (Module.finrank ℚ K : ℝ) = Module.finrank ℚ F * Module.finrank F K := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F K).symm
  have he : (ramIdx F w : ℝ) ≠ 0 := by exact_mod_cast (ramIdx_pos' w).ne'
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hK : (Module.finrank F K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  unfold localDeg
  rw [hKQ]
  push_cast
  field_simp

end Sum

/-! ### The local theta data -/

section Data

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt)

/-- The bad places of `K`: the places over `V_mod^bad`. -/
abbrev IsBadK (v : FinitePlace D.Kt) : Prop := IsBadPlace D.E D.prime.torsionField D.VBad v

/-- The hypothesis **`E[2] ⊆ E(F)`**, in the form used here: `E(F)[2]` has (at least) four
elements. A consequence of `SixTorsionRational` (IUT I, Definition 3.1(b)). -/
abbrev TwoTorsionRational : Prop :=
  2 * 2 ≤ Nat.card ↥(AddSubgroup.torsionBy D.E.toAffine.Point ((2 : ℕ) : ℤ))

variable (htwo : TwoTorsionRational D)

/-- The chosen `2ℓ`-th root of the Tate parameter at a bad place of `K`; `1` elsewhere. -/
def qrootOf (v : FinitePlace D.Kt) : completionAt D.Kt v :=
  if hv : IsBadK D v then Classical.choose (exists_qroot D.prime D.tate htwo hv) else 1

lemma qrootOf_spec {v : FinitePlace D.Kt} (hv : IsBadK D v) :
    qrootOf D htwo v ^ (2 * D.ℓ) = ((D.tate.S v hv).t.q : localCompletion v) := by
  unfold qrootOf
  rw [dif_pos hv]
  exact Classical.choose_spec (exists_qroot D.prime D.tate htwo hv)

lemma qrootOf_of_not {v : FinitePlace D.Kt} (hv : ¬ IsBadK D v) : qrootOf D htwo v = 1 := by
  unfold qrootOf
  rw [dif_neg hv]

/-- The comparison map `F_w → K_v` of the local theta data. -/
def embedFOf (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : (Place.finite v).LiesOver (Place.finite w)) : localCompletion w →+* completionAt D.Kt v :=
  embedCompletion (v := v) (w := w) h

/-- `q_v^{2ℓ}` is the image of the Tate parameter of `E` at `w`. -/
lemma qrootOf_pow (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : (Place.finite v).LiesOver (Place.finite w)) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    qrootOf D htwo v ^ (2 * D.ℓ) =
      embedFOf D v w h ((D.prime.tate w hw).q : localCompletion w) := by
  have hvw : FinitePlace.LiesOver v w := h
  have hv : IsBadK D v := isBadPlace_of_liesOver D.E D.prime.torsionField hvw hw
  rw [qrootOf_spec D htwo hv]
  exact TateStructure.t_q_eq_embedCompletion hvw (D.tate.S v hv) (D.prime.tate w hw)
    (D.prime.tateJ_eq w hw)

lemma qrootOf_ne_zero (v : FinitePlace D.Kt) : qrootOf D htwo v ≠ 0 := by
  by_cases hv : IsBadK D v
  · intro h0
    have := qrootOf_spec D htwo hv
    rw [h0, zero_pow (by have := D.prime.five_le; unfold InitialThetaData.ℓ; omega)] at this
    exact Units.ne_zero _ this.symm
  · rw [qrootOf_of_not D htwo hv]
    exact one_ne_zero

/-- `ord_p(q_v) = ord_w(q_w)/(2ℓ e_w)`. -/
lemma ordp_qrootOf (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : (Place.finite v).LiesOver (Place.finite w)) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    ordp D.Kt v (qrootOf D htwo v) = (D.prime.qOrder w hw : ℝ) / (2 * D.ℓ * ramIdx D.F w) := by
  have hvw : FinitePlace.LiesOver v w := h
  have hℓ : (2 * D.ℓ : ℝ) ≠ 0 := by
    have : (5 : ℝ) ≤ D.ℓ := by exact_mod_cast D.prime.five_le
    positivity
  have h1 := ordp_pow' v (qrootOf D htwo v) (2 * D.ℓ)
  rw [qrootOf_pow D htwo v w h hw] at h1
  unfold embedFOf at h1
  rw [ordp_embedCompletion hvw, ordp_tateParameter _ (D.prime.unif_isUniformizer w hw)] at h1
  have h2 : ordp D.Kt v (qrootOf D htwo v) =
      ((D.prime.tate w hw).toOrdered (D.prime.unif_isUniformizer w hw)).orderNat /
        ramIdx D.F w / (2 * D.ℓ) := by
    rw [h1]
    push_cast
    rw [mul_div_cancel_left₀ _ hℓ]
  rw [h2]
  unfold AdmissiblePrimeData.qOrder
  ring

/-- The residue characteristics of the bad places of `F`. -/
def badCharsOf (QI : QPilotInputs D) : Finset ℕ :=
  QI.bad_finite.toFinset.image residueChar

lemma residueChar_mem_badCharsOf (QI : QPilotInputs D) {v : FinitePlace D.Kt}
    {w : FinitePlace D.F} (hvw : FinitePlace.LiesOver v w)
    (hw : w ∈ badPlacesOver D.F D.E D.VBad) : residueChar v ∈ badCharsOf D QI :=
  Finset.mem_image.mpr ⟨w, QI.bad_finite.mem_toFinset.mpr hw, (residueChar_eq_of_liesOver hvw).symm⟩

lemma not_isBadK_of_notMem (QI : QPilotInputs D) {v : FinitePlace D.Kt}
    (hv : residueChar v ∉ badCharsOf D QI) : ¬ IsBadK D v := by
  intro h
  obtain ⟨w, hw, hvw⟩ := exists_liesOver_of_isBadPlace D.E D.prime.torsionField h
  exact hv (residueChar_mem_badCharsOf D QI hvw hw)

/-- **The local theta data of the initial Θ-data** (IUT I, Example 3.2(iv)). -/
def thetaLocalData (QI : QPilotInputs D) : ThetaLocalData D LT where
  badChars := badCharsOf D QI
  qroot := qrootOf D htwo
  qroot_ne_zero := qrootOf_ne_zero D htwo
  ordp_qroot_nonneg v := by
    by_cases hv : IsBadK D v
    · obtain ⟨w, hw, hvw⟩ := exists_liesOver_of_isBadPlace D.E D.prime.torsionField hv
      rw [ordp_qrootOf D htwo v w hvw hw]
      positivity
    · rw [qrootOf_of_not D htwo hv]
      simp [ordp, norm_one]
  qroot_eq_one v hv := qrootOf_of_not D htwo (not_isBadK_of_notMem D QI hv)
  embedF := embedFOf D
  qroot_pow := qrootOf_pow D htwo
  ordp_qroot := ordp_qrootOf D htwo
  residueChar_mem v w h hw := residueChar_mem_badCharsOf D QI h hw
  bad_residueChar_mem w hw :=
    Finset.mem_image.mpr ⟨w, QI.bad_finite.mem_toFinset.mpr hw, rfl⟩
  badChars_prime p hp := by
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hp
    exact residueChar_prime w
  sum_weight_ordp_qroot p bad hbad := by
    haveI := LT.fiber_finite p
    haveI : Fintype {w : FinitePlace D.Kt // residueChar w = p} := Fintype.ofFinite _
    have hℓ : (2 * D.ℓ : ℝ) ≠ 0 := by
      have : (5 : ℝ) ≤ D.ℓ := by exact_mod_cast D.prime.five_le
      positivity
    -- the weight function on the places of `K`
    have h1 : ∑ v : LT.Fiber (.finite p), LT.weight (.finite p) v *
        ordp D.Kt (LT.fiberPlace v) (qrootOf D htwo (LT.fiberPlace v)) =
        ∑ u : {w : FinitePlace D.Kt // residueChar w = p},
          placeWeight D.Kt u.1 * ordp D.Kt u.1 (qrootOf D htwo u.1) := by
      refine Fintype.sum_equiv (LT.fiberFiniteEquiv p) _ _ fun v => ?_
      rcases v with ⟨v, hv⟩
      rcases v with w | w
      · rfl
      · exact absurd hv (by simp [LocalTheory.toRational])
    rw [h1]
    -- the order function `c` on the places of `F`
    let c : FinitePlace D.F → ℝ := fun w =>
      if h : w ∈ badPlacesOver D.F D.E D.VBad then (D.prime.qOrder w h : ℝ) / (2 * D.ℓ) else 0
    rw [sum_placeWeight_mul p (badPlacesOver D.F D.E D.VBad) bad hbad c
      (fun v => ordp D.Kt v (qrootOf D htwo v))
      (fun v w hvw hw => by
        simp only [c, dif_pos hw]
        rw [ordp_qrootOf D htwo v w hvw hw]
        field_simp)
      (fun v hv => by
        have : ¬ IsBadK D v := fun h => by
          obtain ⟨w, hw, hvw⟩ := exists_liesOver_of_isBadPlace D.E D.prime.torsionField h
          exact hv w hw hvw
        rw [qrootOf_of_not D htwo this]
        simp [ordp, norm_one])]
    -- match the right-hand side
    rw [Finset.sum_div, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_attach bad]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hw : w.1 ∈ badPlacesOver D.F D.E D.VBad := by rw [← hbad]; exact Finset.mem_coe.mpr w.2
    simp only [c, dif_pos hw]
    split_ifs
    · ring
    · rfl

end Data

end

end Iut
