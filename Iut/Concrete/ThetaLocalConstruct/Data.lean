/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.Container
import Iut.Cor312.ThetaData.Basic
import Iut.Cor312.ThetaData.TwoTorsion
import Iut.Concrete.ThetaLocalConstruct.Ordp
import Iut.Concrete.ThetaLocalConstruct.Roots
import Iut.Concrete.ThetaLocalConstruct.TateCompat
import Iut.Anabelian.LocalInputs
import Iut.Cor312.ThetaData.SqrtAtBadPlace

/-!
# Construction of the local theta data

The local theta data of initial Θ-data `D` (IUT I, Example 3.2(iv)) — the `2ℓ`-th roots
`q_v = q^{1/2ℓ}` of the Tate parameters at the bad places of the `ℓ`-torsion field `K`
(`InitialThetaData.qroot`), the comparison maps `F_w → K_v` (`InitialThetaData.embedF`) and the
bad residue characteristics (`InitialThetaData.badChars`) — are constructed here from `D` alone,
with their properties as theorems:

* the comparison map `F_w → K_v` is `Iut.embedCompletion` (the inclusion `F → K` raises the
  `w`-adic valuation to the power `e(v/w)`, hence is uniformly continuous);
* at a place `v ∣ w` over `V(F)^bad`, the Tate structure `D.tate.S v` of `E` over `K_v` has
  Tate parameter the image of the Tate parameter `q_w` of `E` over `F_w`
  (`Iut.TateStructure.t_q_eq_embedCompletion`, from the uniqueness of the Tate parameter
  with given `j`-invariant), and `q_w` has a `2ℓ`-th root in `K_v` because `E(K_v)[ℓ]` has
  `ℓ²` elements (`E[ℓ] ⊆ E(K)`, `Iut.TateFamily.sq_le_card_torsion`) and `E(K_v)[2]` has `4`
  elements (`E[2] ⊆ E(F)`, `InitialThetaData.twoTorsionRational`;
  `Iut.TateStructure.exists_pow_eq_q`);
* `ord_p(q_v) = ord_w(q_w)/(2ℓ·e_w)` from the invariance of `ord_p` under the comparison map
  (`Iut.ordp_embedCompletion`) and `ord_p(q_w) = ord_w(q_w)/e_w` (`Iut.ordp_tateParameter`);
* the base-change invariance of the `q`-degree from the fundamental identity
  `∑_{v ∣ w} e_v f_v = [K : F]·e_w f_w` (`Iut.sum_localDeg_liesOver`).

The two arithmetic facts used beyond the fields of `D` are theorems about every `D`: the
finiteness of the bad locus (`InitialThetaData.bad_finite`, from the multiplicative reduction
at the places over `V_mod^bad`, IUT I, Definition 3.1(b)) and the rationality of the
`2`-torsion over `F` (`InitialThetaData.twoTorsionRational`, from `SixTorsionRational`, IUT I,
Definition 3.1(b), and `|E(F̄)[2]| = 4`, `Iut.four_le_card_torsionBy_two`).
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

variable (D : InitialThetaData.{u})

/-- The bad places of `K`: the places over `V_mod^bad`. -/
abbrev IsBadK (v : FinitePlace D.Kt) : Prop := IsBadPlace D.E D.prime.torsionField D.VBad v

/-- The hypothesis **`E[2] ⊆ E(F)`**, in the form used here: `E(F)[2]` has (at least) four
elements. A consequence of `SixTorsionRational` (IUT I, Definition 3.1(b);
`InitialThetaData.twoTorsionRational`). -/
abbrev TwoTorsionRational : Prop :=
  2 * 2 ≤ Nat.card ↥(AddSubgroup.torsionBy D.E.toAffine.Point ((2 : ℕ) : ℤ))

/-- **`E[2] ⊆ E(F)`** for initial Θ-data, from the rationality of the `6`-torsion (IUT I,
Definition 3.1(b)). -/
theorem InitialThetaData.twoTorsionRational : TwoTorsionRational D :=
  four_le_card_torsionBy_two D.E D.global.six_torsion_rational

/-- **The bad locus `V(F)^bad` is finite**: `E` has multiplicative reduction at every place of
`F` over `V_mod^bad` (IUT I, Definition 3.1(b)), where `v_w(j(E)) > 1`, and a nonzero `j(E)` has
`w`-adic norm `1` at all but finitely many places (for `j(E) = 0` there is no such place). -/
theorem InitialThetaData.bad_finite : (badPlacesOver D.F D.E D.VBad).Finite := by
  have hmult : ∀ w ∈ badPlacesOver D.F D.E D.VBad, HasMultiplicativeReductionAt D.E w := by
    rintro w ⟨v, hv, hwv⟩
    exact D.global.bad_multiplicative v hv w hwv
  by_cases hj : D.E.j = 0
  · refine Set.Finite.subset (Set.finite_empty) fun w hw => ?_
    have := one_lt_valuation_j_of_mult D.E w (hmult w hw)
    rw [hj, map_zero] at this
    exact absurd this (not_lt.2 zero_le_one)
  refine (FinitePlace.hasFiniteMulSupport hj).subset fun w hw => ?_
  rw [Function.mem_mulSupport, ← FinitePlace.norm_embedding_eq]
  intro h
  exact absurd ((norm_emb_le_one_iff _).1 h.le)
    (not_le.2 (one_lt_valuation_j_of_mult D.E w (hmult w hw)))

/-- The chosen `2ℓ`-th root of the Tate parameter at a bad place of `K`; `1` elsewhere. -/
def qrootOf (v : FinitePlace D.Kt) : completionAt D.Kt v :=
  if hv : IsBadK D v then
    Classical.choose (exists_qroot D.prime D.tate D.twoTorsionRational hv)
  else 1

lemma qrootOf_spec {v : FinitePlace D.Kt} (hv : IsBadK D v) :
    qrootOf D v ^ (2 * D.ℓ) = ((D.tate.S v hv).t.q : localCompletion v) := by
  unfold qrootOf
  rw [dif_pos hv]
  exact Classical.choose_spec (exists_qroot D.prime D.tate D.twoTorsionRational hv)

lemma qrootOf_of_not {v : FinitePlace D.Kt} (hv : ¬ IsBadK D v) : qrootOf D v = 1 := by
  unfold qrootOf
  rw [dif_neg hv]

/-- The comparison map `F_w → K_v` of the local theta data. -/
def embedFOf (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : (Place.finite v).LiesOver (Place.finite w)) : localCompletion w →+* completionAt D.Kt v :=
  embedCompletion (v := v) (w := w) h

/-- `q_v^{2ℓ}` is the image of the Tate parameter of `E` at `w`. -/
lemma qrootOf_pow (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : (Place.finite v).LiesOver (Place.finite w)) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    qrootOf D v ^ (2 * D.ℓ) =
      embedFOf D v w h ((D.prime.tate w hw).q : localCompletion w) := by
  have hvw : FinitePlace.LiesOver v w := h
  have hv : IsBadK D v := isBadPlace_of_liesOver D.E D.prime.torsionField hvw hw
  rw [qrootOf_spec D hv]
  exact TateStructure.t_q_eq_embedCompletion hvw (D.tate.S v hv) (D.prime.tate w hw)
    (D.prime.tateJ_eq w hw)

lemma qrootOf_ne_zero (v : FinitePlace D.Kt) : qrootOf D v ≠ 0 := by
  by_cases hv : IsBadK D v
  · intro h0
    have := qrootOf_spec D hv
    rw [h0, zero_pow (by have := D.prime.five_le; unfold InitialThetaData.ℓ; omega)] at this
    exact Units.ne_zero _ this.symm
  · rw [qrootOf_of_not D hv]
    exact one_ne_zero

/-- `ord_p(q_v) = ord_w(q_w)/(2ℓ e_w)`. -/
lemma ordp_qrootOf (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : (Place.finite v).LiesOver (Place.finite w)) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    ordp D.Kt v (qrootOf D v) = (D.prime.qOrder w hw : ℝ) / (2 * D.ℓ * ramIdx D.F w) := by
  have hvw : FinitePlace.LiesOver v w := h
  have hℓ : (2 * D.ℓ : ℝ) ≠ 0 := by
    have : (5 : ℝ) ≤ D.ℓ := by exact_mod_cast D.prime.five_le
    positivity
  have h1 := ordp_pow' v (qrootOf D v) (2 * D.ℓ)
  rw [qrootOf_pow D v w h hw] at h1
  unfold embedFOf at h1
  rw [ordp_embedCompletion hvw, ordp_tateParameter _ (D.prime.unif_isUniformizer w hw)] at h1
  have h2 : ordp D.Kt v (qrootOf D v) =
      ((D.prime.tate w hw).toOrdered (D.prime.unif_isUniformizer w hw)).orderNat /
        ramIdx D.F w / (2 * D.ℓ) := by
    rw [h1]
    push_cast
    rw [mul_div_cancel_left₀ _ hℓ]
  rw [h2]
  unfold AdmissiblePrimeData.qOrder
  ring

/-- The residue characteristics of the bad places of `F`. -/
def badCharsOf : Finset ℕ :=
  D.bad_finite.toFinset.image residueChar

lemma residueChar_mem_badCharsOf {v : FinitePlace D.Kt}
    {w : FinitePlace D.F} (hvw : FinitePlace.LiesOver v w)
    (hw : w ∈ badPlacesOver D.F D.E D.VBad) : residueChar v ∈ badCharsOf D :=
  Finset.mem_image.mpr
    ⟨w, D.bad_finite.mem_toFinset.mpr hw, (residueChar_eq_of_liesOver hvw).symm⟩

lemma not_isBadK_of_notMem {v : FinitePlace D.Kt}
    (hv : residueChar v ∉ badCharsOf D) : ¬ IsBadK D v := by
  intro h
  obtain ⟨w, hw, hvw⟩ := exists_liesOver_of_isBadPlace D.E D.prime.torsionField h
  exact hv (residueChar_mem_badCharsOf D hvw hw)

/-! ### The local theta data of the initial Θ-data (IUT I, Example 3.2(iv))

The `2ℓ`-th roots `q_v = q^{1/2ℓ}` of the Tate parameters at the places of `K` over the bad
places of `F`, with the comparison maps of completions `F_w → K_v`, as definitions on `D`
together with their properties. The places whose residue characteristic is not in the
finite set `badChars` (the residue characteristics of the bad places) carry `q_v = 1`. -/

namespace InitialThetaData

/-- The residue characteristics of the bad places. -/
abbrev badChars : Finset ℕ := badCharsOf D

/-- The `2ℓ`-th root `q_v` of the Tate parameter at `v` (`1` away from the bad places). -/
abbrev qroot (v : FinitePlace D.Kt) : completionAt D.Kt v := qrootOf D v

/-- The comparison map of completions `F_w → K_v` for `v ∣ w`. -/
abbrev embedF (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : (Place.finite v).LiesOver (Place.finite w)) : localCompletion w →+* completionAt D.Kt v :=
  embedFOf D v w h

/-- `q_v ≠ 0`. -/
theorem qroot_ne_zero (v : FinitePlace D.Kt) : D.qroot v ≠ 0 := qrootOf_ne_zero D v

/-- `ord_p(q_v) ≥ 0`. -/
theorem ordp_qroot_nonneg (v : FinitePlace D.Kt) : 0 ≤ ordp D.Kt v (D.qroot v) := by
  by_cases hv : IsBadK D v
  · obtain ⟨w, hw, hvw⟩ := exists_liesOver_of_isBadPlace D.E D.prime.torsionField hv
    rw [qroot, ordp_qrootOf D v w hvw hw]
    positivity
  · rw [qroot, qrootOf_of_not D hv]
    simp [ordp, norm_one]

/-- Away from the bad residue characteristics, `q_v = 1`. -/
theorem qroot_eq_one (v : FinitePlace D.Kt) (hv : residueChar v ∉ D.badChars) :
    D.qroot v = 1 :=
  qrootOf_of_not D (not_isBadK_of_notMem D hv)

/-- `q_v^{2ℓ}` is the Tate parameter of `E` at `w` (IUT I, Example 3.2(iv)). -/
theorem qroot_pow (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : (Place.finite v).LiesOver (Place.finite w)) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    D.qroot v ^ (2 * D.ℓ) = D.embedF v w h ((D.prime.tate w hw).q : localCompletion w) :=
  qrootOf_pow D v w h hw

/-- `ord_p(q_v) = ord_w(q_w)/(2ℓ·e_w)`. -/
theorem ordp_qroot (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : (Place.finite v).LiesOver (Place.finite w)) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    ordp D.Kt v (D.qroot v) = (D.prime.qOrder w hw : ℝ) / (2 * D.ℓ * ramIdx D.F w) :=
  ordp_qrootOf D v w h hw

/-- The bad places of `K` have residue characteristic in `badChars`. -/
theorem residueChar_mem (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : (Place.finite v).LiesOver (Place.finite w)) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    residueChar v ∈ D.badChars :=
  residueChar_mem_badCharsOf D h hw

/-- The bad places of `F` have residue characteristic in `badChars`. -/
theorem bad_residueChar_mem (w : FinitePlace D.F) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    residueChar w ∈ D.badChars :=
  Finset.mem_image.mpr ⟨w, D.bad_finite.mem_toFinset.mpr hw, rfl⟩

/-- The bad residue characteristics are prime. -/
theorem badChars_prime (p : ℕ) (hp : p ∈ D.badChars) : p.Prime := by
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hp
  exact residueChar_prime w

/-- **Base-change invariance of the `q`-degree** at each prime `p`: the weighted sum over the
places `v ∣ p` of `K` of `[K_v : ℚ_p]/[K : ℚ]·ord_p(q_v)` equals
`(1/2ℓ)·∑_{w ∣ p, w bad} (f_w/[F : ℚ])·ord_w(q_w)` (from `∑_{v ∣ w} e_v f_v = [K : F]·e_w f_w`
and `ord_p(q_v) = ord_w(q_w)/(2ℓ e_w)`). -/
theorem sum_weight_ordp_qroot (p : Nat.Primes) (bad : Finset (FinitePlace D.F))
    (hbad : ↑bad = badPlacesOver D.F D.E D.VBad) :
    ∑ v : LocalTheory.Fiber D.Kt (.finite p), LocalTheory.weight D.Kt (.finite p) v *
        ordp D.Kt (LocalTheory.fiberPlace D.Kt v) (D.qroot (LocalTheory.fiberPlace D.Kt v)) =
      (∑ w ∈ bad.attach.filter (fun w => residueChar w.1 = p),
        (inertDeg D.F w.1 : ℝ) / Module.finrank ℚ D.F *
          (D.prime.qOrder w.1 (hbad ▸ Finset.mem_coe.mpr w.2) : ℝ)) / (2 * D.ℓ) := by
  haveI := LocalTheory.fiber_finite D.Kt p
  haveI : Fintype {w : FinitePlace D.Kt // residueChar w = p} := Fintype.ofFinite _
  -- the weight function on the places of `K`
  have h1 : ∑ v : LocalTheory.Fiber D.Kt (.finite p), LocalTheory.weight D.Kt (.finite p) v *
      ordp D.Kt (LocalTheory.fiberPlace D.Kt v) (D.qroot (LocalTheory.fiberPlace D.Kt v)) =
      ∑ u : {w : FinitePlace D.Kt // residueChar w = p},
        placeWeight D.Kt u.1 * ordp D.Kt u.1 (qrootOf D u.1) := by
    refine Fintype.sum_equiv (LocalTheory.fiberFiniteEquiv D.Kt p) _ _ fun v => ?_
    rcases v with ⟨v, hv⟩
    rcases v with w | w
    · rfl
    · exact absurd hv (by simp [LocalTheory.toRational])
  rw [h1]
  -- the order function `c` on the places of `F`
  let c : FinitePlace D.F → ℝ := fun w =>
    if h : w ∈ badPlacesOver D.F D.E D.VBad then (D.prime.qOrder w h : ℝ) / (2 * D.ℓ) else 0
  rw [sum_placeWeight_mul p (badPlacesOver D.F D.E D.VBad) bad hbad c
    (fun v => ordp D.Kt v (qrootOf D v))
    (fun v w hvw hw => by
      simp only [c, dif_pos hw]
      rw [ordp_qrootOf D v w hvw hw]
      field_simp)
    (fun v hv => by
      have : ¬ IsBadK D v := fun h => by
        obtain ⟨w, hw, hvw⟩ := exists_liesOver_of_isBadPlace D.E D.prime.torsionField h
        exact hv w hw hvw
      rw [qrootOf_of_not D this]
      simp [ordp, norm_one])]
  -- match the right-hand side
  rw [Finset.sum_div, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_attach bad]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hw : w.1 ∈ badPlacesOver D.F D.E D.VBad := by rw [← hbad]; exact Finset.mem_coe.mpr w.2
  simp only [c, dif_pos hw]
  split_ifs
  · ring
  · rfl

end InitialThetaData

end Data

end

end Iut
