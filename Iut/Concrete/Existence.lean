/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.Main

/-!
# Existence of initial Θ-data from an elliptic curve (taxis #1469)

This module constructs the initial Θ-data of IUT I, Definition 3.1 attached to an
elliptic curve `E/F` and a prime `ℓ` satisfying the conditions (P1)–(P6) of the proof of
IUT IV, Corollary 2.2, and derives from it the concrete existence statement
`Iut.ConcreteThetaDataExistence` of `Iut.Concrete.Main`.

## The inputs

The curve is packaged as `Iut.EllipticCurveData` (a number field `F` with an algebraic
closure and an elliptic curve `E/F`). The construction consumes four kinds of standard
inputs, each a structure with a precise target statement:

* `EllipticCurveData.CurveArithmetic` (`Prop`): the arithmetic of `E/F` of IUT IV,
  Proposition 1.8 and of the places of `F/F_mod` — `√−1 ∈ F`, everywhere stable
  reduction, rational `6`-torsion, `F/F_mod` Galois of degree prime to `ℓ ≥ 7`, places
  of `F` over places of `F_mod` and their residue characteristics, Galois-invariance of
  multiplicative reduction, finiteness of the bad locus, and the residue-degree bound
  `∑_{w ∣ p} f_w ≤ [F : ℚ]`.
* `EllipticCurveData.TateInputs`: the Tate parameters and uniformizers of `E` at its
  multiplicative places (the interface of taxis #37).
* `EllipticCurveData.ModEllRepData ℓ`: the mod-`ℓ` Galois representation on `E[ℓ]` with
  a basis, its characterizing property, and the openness of its kernel (taxis #277).
* `Iut.AnabelianExistence AG TG` (`Prop`): the anabelian part of Definition 3.1 — for
  every admissible prime datum, orbicurve data `C̲_K`, `ε` and local theta data `V`
  exist (taxis #276, #279).

From these, `EllipticCurveData.thetaData` **is** initial Θ-data with `V_mod^bad` the set
`VBadOf ℓ` of places of `F_mod` not over `2ℓ` at which `E` has multiplicative reduction
((P5) in the proof of Corollary 2.2).

## The existence statement

`Iut.CurveInputs T K d` is the form of the inputs of Corollary 2.2 in which the local
height data of each point is *computed* from its curve (`EllipticCurveData.localHeightData`)
and the image condition (P6) is the image of the mod-`ℓ` representation. It provides
`Corollary22Inputs` (`CurveInputs.toCorollary22Inputs`), and
`CurveInputs.concreteThetaDataExistence` proves `ConcreteThetaDataExistence` for it from
the anabelian existence and the universal providers of the local theory (taxis #1462),
the local theta data (taxis #1464) and the tower arithmetic (taxis #1493). The final
theorem `Iut.cor312Variant_implies_abc_curves` assembles everything.
-/

namespace Iut

universe u v

open NumberField WeierstrassCurve TateCurvesTheta OrbicurveDataSection

/-! ## Residue characteristics -/

/-- The residue characteristic of a finite place of a number field is prime. -/
lemma residueChar_prime {k : Type*} [Field k] [NumberField k] (w : FinitePlace k) :
    (residueChar w).Prime := by
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  letI : Field (𝓞 k ⧸ w.maximalIdeal.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 k ⧸ w.maximalIdeal.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ w.maximalIdeal.ne_bot
  exact CharP.char_is_prime (𝓞 k ⧸ w.maximalIdeal.asIdeal) (ringChar _)

/-! ## Elliptic curves over number fields -/

/-- An elliptic curve `E` over a number field `F` with a chosen algebraic closure `F̄`. -/
structure EllipticCurveData : Type (u + 1) where
  /-- The number field `F`. -/
  F : Type u
  /-- `F` is a field. -/
  [fieldF : Field F]
  /-- `F` is a number field. -/
  [numberFieldF : NumberField F]
  /-- The algebraic closure `F̄`. -/
  Fbar : Type u
  /-- `F̄` is a field. -/
  [fieldFbar : Field Fbar]
  /-- `F̄` is an `F`-algebra. -/
  [algebraFbar : Algebra F Fbar]
  /-- `F̄` is an algebraic closure of `F`. -/
  [isAlgClosure : IsAlgClosure F Fbar]
  /-- The elliptic curve `E/F`. -/
  E : WeierstrassCurve F
  /-- `E` is an elliptic curve. -/
  [isElliptic : E.IsElliptic]

namespace EllipticCurveData

attribute [instance] fieldF numberFieldF fieldFbar algebraFbar isAlgClosure isElliptic

variable (C : EllipticCurveData.{u})

/-- The places of `F` at which `E` has (bad) multiplicative reduction. -/
def badAll : Set (FinitePlace C.F) := {w | HasMultiplicativeReductionAt C.E w}

/-- The set `V_mod^bad` attached to the prime `ℓ` ((P5) in the proof of IUT IV,
Corollary 2.2): the places of `F_mod` of residue characteristic `≠ 2, ℓ` over which `E`
has multiplicative reduction (at every place of `F` above, and there is one). -/
def VBadOf (ℓ : ℕ) : Set (FinitePlace ↥(fieldOfModuli C.F C.E)) :=
  {v | residueChar v ≠ 2 ∧ residueChar v ≠ ℓ ∧
    (∃ w : FinitePlace C.F, FinitePlace.LiesOver w v) ∧
    ∀ w : FinitePlace C.F, FinitePlace.LiesOver w v → HasMultiplicativeReductionAt C.E w}

/-- Places over `V_mod^bad(ℓ)` are multiplicative. -/
lemma mem_badAll_of_mem_badPlacesOver {ℓ : ℕ} {w : FinitePlace C.F}
    (hw : w ∈ badPlacesOver C.F C.E (C.VBadOf ℓ)) : w ∈ C.badAll := by
  obtain ⟨v, hv, hwv⟩ := hw
  exact hv.2.2.2 w hwv

/-! ### The standard inputs -/

/-- **The arithmetic of the curve** (IUT IV, Proposition 1.8; the places of `F/F_mod`):
the standard facts about `E/F` consumed by the construction of initial Θ-data. -/
structure CurveArithmetic : Prop where
  /-- `√−1 ∈ F`. -/
  sqrt_neg_one : IsSquare (-1 : C.F)
  /-- `E` has stable reduction at every finite place of `F`. -/
  stable_reduction : ∀ w : FinitePlace C.F, HasStableReductionAt C.E w
  /-- The `6`-torsion of `E` is rational over `F`. -/
  six_torsion_rational : SixTorsionRational C.F C.E C.Fbar
  /-- `F/F_mod` is Galois of degree prime to every prime `ℓ ≥ 7`. -/
  galois_deg_prime : ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ → IsGaloisOfDegreePrimeTo C.F C.E ℓ
  /-- Every finite place of `F` lies over a finite place of `F_mod`. -/
  exists_liesOver : ∀ w : FinitePlace C.F,
    ∃ v : FinitePlace ↥(fieldOfModuli C.F C.E), FinitePlace.LiesOver w v
  /-- A place of `F` over a place of `F_mod` has the same residue characteristic. -/
  residueChar_liesOver : ∀ (v : FinitePlace ↥(fieldOfModuli C.F C.E)) (w : FinitePlace C.F),
    FinitePlace.LiesOver w v → residueChar w = residueChar v
  /-- Multiplicative reduction does not depend on the place of `F` over a given place of
  `F_mod` of odd residue characteristic (`E` descends to `F_tpd` up to twist and has
  semistable reduction). -/
  mult_invariant : ∀ v : FinitePlace ↥(fieldOfModuli C.F C.E), residueChar v ≠ 2 →
    ∀ w w' : FinitePlace C.F, FinitePlace.LiesOver w v → FinitePlace.LiesOver w' v →
    HasMultiplicativeReductionAt C.E w → HasMultiplicativeReductionAt C.E w'
  /-- The bad locus is finite. -/
  badAll_finite : C.badAll.Finite
  /-- Residue degrees are positive. -/
  inertDeg_pos : ∀ w : FinitePlace C.F, 0 < inertDeg C.F w
  /-- Over a rational prime, the residue degrees of the bad places sum to at most
  `[F : ℚ]`. -/
  sum_inertDeg_le : ∀ q : ℕ,
    ∑ w ∈ badAll_finite.toFinset.filter (fun w => residueChar w = q), inertDeg C.F w ≤
      Module.finrank ℚ C.F

/-- **Tate parameters** of `E` at its multiplicative places, with uniformizers of the
completions (the interface of taxis #37). -/
structure TateInputs : Type u where
  /-- The Tate parameter `q_w` of `E` at each multiplicative place. -/
  tate : ∀ w ∈ C.badAll, TateParameter (localCompletion w)
  /-- The Tate parameter is that of `E`: the `j`-invariant of its Tate curve is `j(E)`. -/
  tateJ_eq : ∀ w (hw : w ∈ C.badAll),
    (tate w hw).tateJ = FinitePlace.embedding w.maximalIdeal C.E.j
  /-- A chosen uniformizer of each completion. -/
  unif : ∀ w ∈ C.badAll, localCompletion w
  /-- The chosen elements are uniformizers. -/
  unif_isUniformizer : ∀ w (hw : w ∈ C.badAll), IsUniformizer (unif w hw)

variable {C} in
/-- The normalized order `h_w = ord_w(q_w)` of the Tate parameter. -/
noncomputable def TateInputs.qOrder (TI : C.TateInputs) (w : FinitePlace C.F)
    (hw : w ∈ C.badAll) : ℕ :=
  ((TI.tate w hw).toOrdered (TI.unif_isUniformizer w hw)).orderNat

variable {C} in
lemma TateInputs.qOrder_pos (TI : C.TateInputs) (w : FinitePlace C.F) (hw : w ∈ C.badAll) :
    0 < TI.qOrder w hw :=
  ((TI.tate w hw).toOrdered (TI.unif_isUniformizer w hw)).orderNat_pos

open scoped Classical in
/-- **The mod-`ℓ` Galois representation** of `E` (taxis #277): a basis of `E(F̄)[ℓ]`, the
representation `ρ : Gal(F̄/F) → GL₂(𝔽_ℓ)` computing the Galois action in this basis,
and the openness of its kernel. -/
structure ModEllRepData (ℓ : ℕ) : Type u where
  /-- A chosen `𝔽_ℓ`-basis of the `ℓ`-torsion. -/
  torsionBasis :
    AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ ≃+
      (Fin 2 → ZMod ℓ)
  /-- The mod-`ℓ` representation. -/
  rep : (C.Fbar ≃ₐ[C.F] C.Fbar) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod ℓ)
  /-- `ρ σ` is the matrix of the Galois action of `σ` in the chosen basis. -/
  rep_spec : ∀ (σ : C.Fbar ≃ₐ[C.F] C.Fbar)
    (P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ),
    torsionBasis ⟨galPointMap C.F C.E C.Fbar σ P.1, galPointMap_torsionBy C.F C.E C.Fbar σ P.2⟩ =
      (rep σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).mulVec (torsionBasis P)
  /-- The kernel of `ρ` is open. -/
  ker_isOpen : IsOpen (rep.ker : Set (C.Fbar ≃ₐ[C.F] C.Fbar))

/-! ### The local height data of the curve -/

open scoped Classical in
/-- **The local height data** of `E/F` (IUT IV, Theorem 1.10; [GenEll], Definition 3.3):
the multiplicative places with their residue characteristics, the orders of the Tate
parameters, and the residue degrees. -/
noncomputable def localHeightData (CA : C.CurveArithmetic) (TI : C.TateInputs) :
    LocalHeightData.{u} where
  ι := FinitePlace C.F
  bad := CA.badAll_finite.toFinset
  p := residueChar
  hv w := if h : w ∈ C.badAll then TI.qOrder w h else 0
  f := inertDeg C.F
  deg := Module.finrank ℚ C.F
  one_le_deg := Module.finrank_pos
  p_prime w _ := residueChar_prime w
  one_le_hv w hw := by
    rw [Set.Finite.mem_toFinset] at hw
    rw [dif_pos hw]
    exact TI.qOrder_pos w hw
  one_le_f w _ := CA.inertDeg_pos w
  sum_f_le := CA.sum_inertDeg_le

/-! ### Construction of the initial Θ-data -/

section Construct

variable (CA : C.CurveArithmetic) (TI : C.TateInputs) {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
  (R : C.ModEllRepData ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ R.rep.range)
  (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
  (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)

include CA in
/-- The places of `F` over `V_mod^bad(ℓ)` are exactly the multiplicative places of residue
characteristic `≠ 2, ℓ`. -/
lemma badPlacesOver_VBadOf :
    badPlacesOver C.F C.E (C.VBadOf ℓ) =
      {w | w ∈ C.badAll ∧ residueChar w ≠ 2 ∧ residueChar w ≠ ℓ} := by
  ext w
  constructor
  · rintro ⟨v, ⟨h2, hl, -, hmult⟩, hwv⟩
    refine ⟨hmult w hwv, ?_, ?_⟩ <;> rw [CA.residueChar_liesOver v w hwv] <;> assumption
  · rintro ⟨hm, h2, hl⟩
    obtain ⟨v, hwv⟩ := CA.exists_liesOver w
    have hv2 : residueChar v ≠ 2 := by rwa [← CA.residueChar_liesOver v w hwv]
    refine ⟨v, ⟨hv2, by rwa [← CA.residueChar_liesOver v w hwv], ⟨w, hwv⟩,
      fun w' hw' => CA.mult_invariant v hv2 w w' hwv hw' hm⟩, hwv⟩

include CA hP5 in
/-- **IUT I, Definition 3.1(a)–(b)** for `(F̄/F, E, V_mod^bad(ℓ))`. -/
theorem globalData : IsInitialThetaGlobalData C.F C.E C.Fbar (C.VBadOf ℓ) where
  sqrt_neg_one := CA.sqrt_neg_one
  stable_reduction := CA.stable_reduction
  six_torsion_rational := CA.six_torsion_rational
  bad_nonempty := by
    obtain ⟨w, hw, h2, hl⟩ := hP5
    have hmem : w ∈ badPlacesOver C.F C.E (C.VBadOf ℓ) := by
      rw [C.badPlacesOver_VBadOf CA]
      exact ⟨hw, h2, hl⟩
    obtain ⟨v, hv, -⟩ := hmem
    exact ⟨v, hv⟩
  bad_odd v hv := (residueChar_prime v).odd_of_ne_two hv.1
  bad_multiplicative v hv w hwv := hv.2.2.2 w hwv

/-- **IUT I, Definition 3.1(b)–(c)** for the prime `ℓ`: the admissible prime datum. -/
noncomputable def primeData : AdmissiblePrimeData C.F C.E C.Fbar (C.VBadOf ℓ) where
  ℓ := ℓ
  ℓ_prime := hℓ
  five_le := by omega
  torsionBasis := R.torsionBasis
  rep := R.rep
  rep_spec := R.rep_spec
  sl_le_range := hsl
  ker_isOpen := R.ker_isOpen
  galois_deg_prime := CA.galois_deg_prime ℓ hℓ h7
  residueChar_coprime v hv :=
    (Nat.coprime_primes hℓ (residueChar_prime v)).mpr (Ne.symm hv.2.1)
  tate w hw := TI.tate w (C.mem_badAll_of_mem_badPlacesOver hw)
  tateJ_eq w hw := TI.tateJ_eq w _
  unif w hw := TI.unif w (C.mem_badAll_of_mem_badPlacesOver hw)
  unif_isUniformizer w hw := TI.unif_isUniformizer w _
  q_order_coprime w hw :=
    (Nat.Prime.coprime_iff_not_dvd hℓ).mpr (hP2 w (C.mem_badAll_of_mem_badPlacesOver hw))

end Construct

end EllipticCurveData

/-! ## The anabelian existence -/

/-- **Existence of the anabelian part of initial Θ-data** (IUT I, Definition 3.1(d)–(f);
*The Étale Theta Function*, Definitions 2.1–2.5; taxis #276, #279): for every admissible
prime datum over global data whose once-punctured curve `X_F` admits the `F`-core
`C_F = X_F/{±1}` ([CanLift], Proposition 2.7; taxis #10), there are orbicurve data `C̲_K`,
`X̲_K`, `ε` and local theta data `V`. Proved for the linear-algebraic model of the
anabelian interface in `Iut.Anabelian.Existence`. -/
structure AnabelianExistence (AG : AnabelianGeometry.{u}) (TG : TemperedGeometry AG) :
    Prop where
  /-- The existence statement. -/
  exists_data : ∀ (F : Type u) [Field F] [NumberField F] (E : WeierstrassCurve F)
    [E.IsElliptic] (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
    (VBad : Set (FinitePlace ↥(fieldOfModuli F E))) (P : AdmissiblePrimeData F E Fbar VBad)
    [NumberField ↥P.torsionField] [Algebra ↥(fieldOfModuli F E) ↥P.torsionField],
    (∀ x : ↥(fieldOfModuli F E),
      algebraMap _ ↥P.torsionField x = algebraMap F ↥P.torsionField (algebraMap _ F x)) →
    IsInitialThetaGlobalData F E Fbar VBad →
    AG.HasCore (AG.oncePunctured E) (CF AG F E) →
    ∃ O : OrbicurveData AG F E Fbar VBad P,
      Nonempty (LocalThetaData AG TG F E Fbar VBad P O)

namespace EllipticCurveData

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic) (TI : C.TateInputs) {ℓ : ℕ}
  (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) (R : C.ModEllRepData ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ R.rep.range)
  (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
  (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)
  (anab : AnabelianExistence AG TG)
  (hcore : AG.HasCore (AG.oncePunctured C.E) (OrbicurveDataSection.CF AG C.F C.E))

/-- **The initial Θ-data attached to `(E/F, ℓ)`** (IUT I, Definition 3.1; (P7) in the
proof of IUT IV, Corollary 2.2), with `V_mod^bad = VBadOf ℓ`. -/
noncomputable def thetaData : InitialThetaData AG TG :=
  letI := (C.primeData CA TI hℓ h7 R hsl hP2).numberField_torsionField
  let h := anab.exists_data C.F C.E C.Fbar (C.VBadOf ℓ) (C.primeData CA TI hℓ h7 R hsl hP2)
    (fun _ => rfl) (C.globalData CA hP5) hcore
  { F := C.F
    Fbar := C.Fbar
    E := C.E
    VBad := C.VBadOf ℓ
    global := C.globalData CA hP5
    prime := C.primeData CA TI hℓ h7 R hsl hP2
    orb := h.choose
    localData := h.choose_spec.some }

/-- The `q`-pilot inputs of the constructed Θ-data: the bad locus is finite and residue
degrees are positive. -/
theorem qPilotInputs : QPilotInputs (C.thetaData CA TI hℓ h7 R hsl hP2 hP5 anab hcore) where
  bad_finite := CA.badAll_finite.subset fun _ hw => C.mem_badAll_of_mem_badPlacesOver hw
  inertDeg_pos := CA.inertDeg_pos

open scoped Classical in
/-- **`log(q)` of the constructed Θ-data is the part of `log(q_∀)` away from `2` and
`ℓ`.** -/
theorem logQ_eq (LT : LocalTheory.{u, v} (C.thetaData CA TI hℓ h7 R hsl hP2 hP5 anab hcore).Kt)
    (TL : ThetaLocalData (C.thetaData CA TI hℓ h7 R hsl hP2 hP5 anab hcore) LT) :
    (concreteVariantData.{u, v} (C.thetaData CA TI hℓ h7 R hsl hP2 hP5 anab hcore) LT TL
      (C.qPilotInputs CA TI hℓ h7 R hsl hP2 hP5 anab hcore)).qPilot.logQ =
      (C.localHeightData CA TI).heightOther 2 ℓ := by
  have hfin : (badPlacesOver C.F C.E (C.VBadOf ℓ)).Finite :=
    CA.badAll_finite.subset fun _ hw => C.mem_badAll_of_mem_badPlacesOver hw
  change ∑ w ∈ hfin.toFinset.attach,
      ((inertDeg C.F w.1 : ℝ) / Module.finrank ℚ C.F) *
        ((TI.qOrder w.1 (C.mem_badAll_of_mem_badPlacesOver (hfin.mem_toFinset.mp w.2)) : ℕ) : ℝ) *
        Real.log (residueChar w.1) =
    (∑ w ∈ CA.badAll_finite.toFinset.filter (fun w => residueChar w ≠ 2 ∧ residueChar w ≠ ℓ),
      (((if h : w ∈ C.badAll then TI.qOrder w h else 0 : ℕ) : ℝ) * (inertDeg C.F w : ℝ) *
        Real.log (residueChar w))) / Module.finrank ℚ C.F
  have hfinset : hfin.toFinset =
      CA.badAll_finite.toFinset.filter (fun w => residueChar w ≠ 2 ∧ residueChar w ≠ ℓ) := by
    ext w
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
    exact Set.ext_iff.mp (C.badPlacesOver_VBadOf CA) w
  rw [Finset.sum_div]
  refine (Finset.sum_congr rfl (g := fun w => ((inertDeg C.F w.1 : ℝ) / Module.finrank ℚ C.F) *
      ((if h : w.1 ∈ C.badAll then TI.qOrder w.1 h else 0 : ℕ) : ℝ) *
      Real.log (residueChar w.1)) fun w _ => ?_).trans ?_
  · rw [dif_pos (C.mem_badAll_of_mem_badPlacesOver (hfin.mem_toFinset.mp w.2))]
  · rw [Finset.sum_attach _ (fun w => ((inertDeg C.F w : ℝ) / Module.finrank ℚ C.F) *
      ((if h : w ∈ C.badAll then TI.qOrder w h else 0 : ℕ) : ℝ) * Real.log (residueChar w)),
      hfinset]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end EllipticCurveData

/-! ## The inputs of Corollary 2.2 in terms of curves -/

variable (T : Genl.HeightTheory) (AG : AnabelianGeometry.{u})

/-- **The inputs of IUT IV, Corollary 2.2 in terms of the curves of the points**: to each
point `x` of `K_V ∩ U_X(ℚ̄)^{≤d}` is attached an elliptic curve `E_x` over the number
field `F_x = F_tpd(√−1, E_x[15])` with its arithmetic, Tate parameters and mod-`ℓ`
representations, and the height-theoretic facts of [GenEll] relating `x` to `E_x`. The
local height data and the image condition (P6) are *computed* from the curve
(`toCorollary22Inputs`). -/
structure CurveInputs (K : T.CBS) (d : ℕ) where
  /-- The height `h = log(q_∀(−))`. -/
  h : T.Pt T.tripod → ℝ
  /-- The curve `E_x/F_x` of a point. -/
  curve : ∀ x : T.Pt T.tripod, x ∈ T.cbsSet K ∩ T.ptLE T.tripod d → EllipticCurveData.{u}
  /-- The arithmetic of `E_x/F_x` (IUT IV, Proposition 1.8). -/
  arith : ∀ x hx, (curve x hx).CurveArithmetic
  /-- The Tate parameters of `E_x`. -/
  tate : ∀ x hx, (curve x hx).TateInputs
  /-- The mod-`ℓ` representations of `E_x`. -/
  modRep : ∀ x hx (ℓ : ℕ), (curve x hx).ModEllRepData ℓ
  /-- The local height data of `E_x` computes `h`. -/
  height_eq : ∀ x hx, ((curve x hx).localHeightData (arith x hx) (tate x hx)).height = h x
  /-- `[F_x : ℚ] ≤ 2¹²·3³·5·d` ((E3)–(E5) in the proof of Theorem 1.10). -/
  deg_le : ∀ x hx, Module.finrank ℚ (curve x hx).F ≤ 552960 * d
  /-- `d_mod = [F_mod : ℚ] ≤ d`. -/
  dmod_le : ∀ x hx, Module.finrank ℚ ↥(fieldOfModuli (curve x hx).F (curve x hx).E) ≤ d
  /-- **Corollary 2.2(i)**: `(1/6)·log(q_∀) ≈ ht_{ω_X(D)}` on `K_V`. -/
  htCan_equiv : ((1 / 6 : ℝ) • h) ≈[T.cbsSet K] T.htCan T.tripod
  /-- **Northcott finiteness**. -/
  northcott : ∀ H : ℝ, {x | x ∈ T.cbsSet K ∩ T.ptLE T.tripod d ∧ h x ≤ H}.Finite
  /-- The bound `B_K` on the contribution of the prime `2` to `log(q_∀)`. -/
  B : ℝ
  /-- `B_K ≥ 0`. -/
  B_nonneg : 0 ≤ B
  /-- The contribution of the places over `2` is bounded on `K_V`. -/
  heightEq_two_le : ∀ x hx,
    ((curve x hx).localHeightData (arith x hx) (tate x hx)).heightEq 2 ≤ B
  /-- `E_x` has an `ℓ`-cyclic subgroup scheme. -/
  HasCyclicSubgroup : T.Pt T.tripod → ℕ → Prop
  /-- The number `T_K` of [GenEll], Lemma 3.5. -/
  TK : ℝ
  /-- **[GenEll], Lemma 3.5 with Proposition 3.4.** -/
  cyclic_bound : ∀ (x : T.Pt T.tripod) (_hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
    ∀ ℓ : ℕ, ℓ.Prime → HasCyclicSubgroup x ℓ →
    ((ℓ : ℝ) - 2) / 24 * h x ≤ 2 * Real.log ℓ + TK
  /-- **[GenEll], Lemma 3.1(iii)**: (P2), (P4), (P5) imply that the image of the mod-`ℓ`
  representation contains `SL₂(𝔽_ℓ)`. -/
  sl2_of : ∀ x hx (ℓ : ℕ), ℓ.Prime → 5 ≤ ℓ →
    (∀ w ∈ ((curve x hx).localHeightData (arith x hx) (tate x hx)).bad,
      ¬ ℓ ∣ ((curve x hx).localHeightData (arith x hx) (tate x hx)).hv w) →
    ¬ HasCyclicSubgroup x ℓ →
    (∃ w ∈ ((curve x hx).localHeightData (arith x hx) (tate x hx)).bad,
      ((curve x hx).localHeightData (arith x hx) (tate x hx)).p w ≠ 2 ∧
      ((curve x hx).localHeightData (arith x hx) (tate x hx)).p w ≠ ℓ) →
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (modRep x hx ℓ).rep.range
  /-- **[CanLift], Proposition 2.7** (taxis #10): only finitely many points of bounded
  degree have a once-punctured elliptic curve `X_x` that fails to have the `F_x`-core
  `C_x = X_x/{±1}`. -/
  excCore_finite : {x | ∃ hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d,
    ¬ AG.HasCore (AG.oncePunctured (curve x hx).E)
      (OrbicurveDataSection.CF AG (curve x hx).F (curve x hx).E)}.Finite
  /-- `log-diff_X(x)` is the normalized degree of the different of `F_tpd`. -/
  logDiff_eq : ∀ x hx,
    T.logDiff T.tripod x = logDifferentDeg ↥(tripodalFieldOf (curve x hx).F (curve x hx).E)
  /-- The conductor invariant of `F_tpd` (away from `2ℓ`) is at most `log-cond_D(x)`. -/
  logCond_ge : ∀ x hx (ℓ : ℕ), ℓ.Prime → 7 ≤ ℓ →
    logConductorDegOf (curve x hx).F (curve x hx).E ((curve x hx).VBadOf ℓ) ≤
      T.logCond T.tripod x
  /-- `log-cond_D(x)` exceeds the conductor invariant of `F_tpd` away from `2ℓ` by at most
  `log(2ℓ)`. -/
  logCond_le : ∀ x hx (ℓ : ℕ), ℓ.Prime → 7 ≤ ℓ →
    T.logCond T.tripod x ≤
      logConductorDegOf (curve x hx).F (curve x hx).E ((curve x hx).VBadOf ℓ) +
        Real.log (2 * ℓ)

variable {T AG}

namespace CurveInputs

variable {K : T.CBS} {d : ℕ} (CI : CurveInputs.{u} T AG K d)

/-- The points whose once-punctured elliptic curve fails to have an `F`-core. -/
def excCore : Set (T.Pt T.tripod) :=
  {x | ∃ hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d,
    ¬ AG.HasCore (AG.oncePunctured (CI.curve x hx).E)
      (OrbicurveDataSection.CF AG (CI.curve x hx).F (CI.curve x hx).E)}

/-- The inputs of Corollary 2.2 derived from the curves. -/
noncomputable def toCorollary22Inputs : Corollary22Inputs T K d where
  h := CI.h
  localData x hx := (CI.curve x hx).localHeightData (CI.arith x hx) (CI.tate x hx)
  localData_height := CI.height_eq
  localData_deg_le := CI.deg_le
  htCan_equiv := CI.htCan_equiv
  northcott := CI.northcott
  B := CI.B
  B_nonneg := CI.B_nonneg
  heightEq_two_le := CI.heightEq_two_le
  HasCyclicSubgroup := CI.HasCyclicSubgroup
  TK := CI.TK
  cyclic_bound := CI.cyclic_bound
  SL2Image x ℓ := ∀ hx, ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ),
    A.toGL ∈ (CI.modRep x hx ℓ).rep.range
  sl2_of x hx ℓ hp h5 hP2 hcyc hP5 _ := CI.sl2_of x hx ℓ hp h5 hP2 hcyc hP5
  excCore := CI.excCore
  excCore_finite := CI.excCore_finite.subset Set.inter_subset_left

variable {TG : TemperedGeometry AG}

open scoped Classical in
/-- **Existence of suitable initial Θ-data** ((P7) in the proof of IUT IV, Corollary 2.2)
from the curves of the points, the anabelian existence, and the universal providers of
the local theory, the local theta data and the tower arithmetic. -/
theorem concreteThetaDataExistence (anab : AnabelianExistence AG TG)
    (LTp : ∀ D : InitialThetaData AG TG, LocalTheory.{u, v} D.Kt)
    (TLp : ∀ (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt), ThetaLocalData D LT)
    (TAp : ∀ (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt)
      (TL : ThetaLocalData D LT), TowerArithmetic D LT TL) :
    ConcreteThetaDataExistence.{u, v} (AG := AG) (TG := TG) CI.toCorollary22Inputs := by
  intro x hx hxe ℓ hℓ h7 hP2 hP3 hP5 hsl
  have hcore : AG.HasCore (AG.oncePunctured (CI.curve x hx).E)
      (OrbicurveDataSection.CF AG (CI.curve x hx).F (CI.curve x hx).E) := by
    by_contra h
    exact hxe ⟨hx, h⟩
  have hP2' : ∀ w (hw : w ∈ (CI.curve x hx).badAll), ¬ ℓ ∣ (CI.tate x hx).qOrder w hw := by
    intro w hw
    have := hP2 w ((CI.arith x hx).badAll_finite.mem_toFinset.mpr hw)
    change ¬ ℓ ∣ (if h : w ∈ (CI.curve x hx).badAll then (CI.tate x hx).qOrder w h else 0)
      at this
    rwa [dif_pos hw] at this
  have hP5' : ∃ w ∈ (CI.curve x hx).badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ := by
    obtain ⟨w, hw, h⟩ := hP5
    exact ⟨w, (CI.arith x hx).badAll_finite.mem_toFinset.mp hw, h⟩
  let D := (CI.curve x hx).thetaData (CI.arith x hx) (CI.tate x hx) hℓ h7 (CI.modRep x hx ℓ)
    (hsl hx) hP2' hP5' anab hcore
  refine ⟨D, LTp D, TLp D (LTp D),
    (CI.curve x hx).qPilotInputs (CI.arith x hx) (CI.tate x hx) hℓ h7 (CI.modRep x hx ℓ)
      (hsl hx) hP2' hP5' anab hcore,
    TAp _ _ _, rfl, CI.dmod_le x hx, ?_, CI.logDiff_eq x hx, CI.logCond_ge x hx ℓ hℓ h7,
    CI.logCond_le x hx ℓ hℓ h7⟩
  exact (CI.curve x hx).logQ_eq (CI.arith x hx) (CI.tate x hx) hℓ h7 (CI.modRep x hx ℓ)
    (hsl hx) hP2' hP5' anab hcore _ _

end CurveInputs

/-- **The Corollary 3.12 variant for the concrete data bundles implies ABC**, from the
curve inputs of Corollary 2.2, the anabelian existence, the universal providers, and the
analytic inputs. -/
theorem cor312Variant_implies_abc_curves {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
    (A : T.ProofPackage) (CI : ∀ (K : T.CBS) (d : ℕ), CurveInputs.{u} T AG K d)
    (anab : AnabelianExistence AG TG)
    (LTp : ∀ D : InitialThetaData AG TG, LocalTheory.{u, v} D.Kt)
    (TLp : ∀ (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt), ThetaLocalData D LT)
    (TAp : ∀ (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt)
      (TL : ThetaLocalData D LT), TowerArithmetic D LT TL)
    (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData.{u, v} D LT TL QI)) :
    ABC T :=
  cor312Variant_implies_abc_concrete A (fun K d => (CI K d).toCorollary22Inputs)
    (fun K d => (CI K d).concreteThetaDataExistence anab LTp TLp TAp) cheb pnt h312

end Iut
