/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.Tower
import Iut.Tripod.CyclicLocal
import Iut.Tower.WildBound

/-!
# The wild ramification bound for the curves of the tripod

For the tower `ℚ(λ) = F_tpd ⊆ F_λ ⊆ K = F_λ(E_λ[ℓ])` of a point of the tripod and a place
`v` of `K` over `w` of `F_λ` over `u` of `F_tpd`:

* `Iut.Tripod.relRamIdx_dvd_finrank`: `e(w/v) ∣ [K : k]` for a Galois extension `K/k` of
  number fields (the ramification index divides the order of the decomposition group);
* `Iut.Tripod.finrank_tpd_dvd`: `[F_λ : ℚ(λ)] ∣ 2¹²·3²·5 = 184320`
  (`F_λ = ℚ(λ)(√−1, √λ, √(1 − λ), E_λ[3], E_λ[5])`, the quadratic steps have degree `∣ 2`,
  the torsion steps degree `∣ |GL₂(𝔽_3)| = 48`, `∣ |GL₂(𝔽_5)| = 480`);
* `Iut.Tripod.TameTorsionHyp`: **the residual tameness of `K/F_λ` away from `ℓ`**
  (IUT IV, Proposition 1.8: `E_λ` has semistable reduction over `F_λ`, so the inertia at a
  place of residue characteristic `p ≠ ℓ` acts on `E_λ[ℓ]` through a group of order
  dividing `ℓ` — Tate uniformization at the bad places, Néron–Ogg–Shafarevich at the good
  ones): `p ∤ e(v/w)` for `p ≠ ℓ`;
* `Iut.Tripod.padicValNat_relRamIdx_le_of_tame`, **the wild ramification bound**
  `v_p(e(v/u)) ≤ c_p` (the field `padicValNat_relRamIdx_le` of `Iut.TowerLocalFacts`) from
  the tameness and the divisibilities `e(v/w) ∣ [K : F_λ] ∣ |GL₂(𝔽_ℓ)|`,
  `e(w/u) ∣ [F_λ : ℚ(λ)] ∣ 2¹²·3²·5`.
-/

namespace Iut.Tripod

open Iut Iut.EllipticCurveData NumberField IntermediateField

section General

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **`e(w/v) ∣ [K : k]` for `K/k` Galois**: the ramification index divides the order of the
decomposition group, a subgroup of `Gal(K/k)`. -/
theorem relRamIdx_dvd_finrank {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) : relRamIdx w v ∣ Module.finrank k K := by
  haveI : FiniteDimensional k K := Module.Finite.of_restrictScalars_finite ℚ k K
  rw [← IsGalois.card_aut_eq_finrank k K]
  exact (ramificationIdx'_dvd_card_stabilizer hwv).trans (Subgroup.card_subgroup_dvd_card _)

end General

section Degree

/-- A positive integer `≤ 2` divides `2`. -/
theorem dvd_two_of_le_two {d : ℕ} (hd : d ≠ 0) (h : d ≤ 2) : d ∣ 2 := by
  rcases (show d = 1 ∨ d = 2 by omega) with rfl | rfl <;> norm_num

/-- **`[F_λ : ℚ(λ)] ∣ 2¹²·3²·5`**: the product of the relative degrees of the tower
`ℚ(λ) ⊆ ℚ(λ, √−1) ⊆ ℚ(λ, √−1, √λ) ⊆ ℚ(λ, √−1, √λ, √(1 − λ)) ⊆ …(E_λ[3]) ⊆ F_λ`, of
degrees `∣ 2`, `∣ 2`, `∣ 2`, `∣ 48`, `∣ 480`. -/
theorem relfinrank_fieldOf_fieldOf'_dvd (x : Pt)
    (hpos : IntermediateField.relfinrank (fieldOf x.1) (fieldOf' x.1) ≠ 0) :
    IntermediateField.relfinrank (fieldOf x.1) (fieldOf' x.1) ∣ 184320 := by
  set l := x.1 with hl
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have b3 := (legendre_torsionBasis x 3).some
  have b5 := (legendre_torsionBasis x 5).some
  have hF : fieldOf' l = fieldOf l ⊔ ℚ⟮sqrtNegOne⟯ ⊔ ℚ⟮sqrtLam l⟯ ⊔ ℚ⟮sqrtOneSubLam l⟯ ⊔
      IntermediateField.adjoin ℚ (torsionCoords l 3) ⊔
      IntermediateField.adjoin ℚ (torsionCoords l 5) := by
    have hset : ({l, sqrtNegOne, sqrtLam l, sqrtOneSubLam l} : Set Qbar) =
        (({l} ∪ {sqrtNegOne}) ∪ {sqrtLam l}) ∪ {sqrtOneSubLam l} := by
      ext a
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, or_assoc]
    rw [fieldOf', IntermediateField.adjoin_union, IntermediateField.adjoin_union, hset,
      IntermediateField.adjoin_union, IntermediateField.adjoin_union,
      IntermediateField.adjoin_union]
  set K₁ : IntermediateField ℚ Qbar := fieldOf l with hK₁
  set K₂ : IntermediateField ℚ Qbar := K₁ ⊔ ℚ⟮sqrtNegOne⟯ with hK₂
  set K₃ : IntermediateField ℚ Qbar := K₂ ⊔ ℚ⟮sqrtLam l⟯ with hK₃
  set K₄ : IntermediateField ℚ Qbar := K₃ ⊔ ℚ⟮sqrtOneSubLam l⟯ with hK₄
  set K₅ : IntermediateField ℚ Qbar := K₄ ⊔ IntermediateField.adjoin ℚ (torsionCoords l 3)
    with hK₅
  set K₆ : IntermediateField ℚ Qbar := K₅ ⊔ IntermediateField.adjoin ℚ (torsionCoords l 5)
    with hK₆
  have hl₁ : l ∈ K₁ := IntermediateField.mem_adjoin_simple_self ℚ l
  have hl₂ : l ∈ K₂ := le_sup_left (a := K₁) hl₁
  have hl₃ : l ∈ K₃ := le_sup_left (a := K₂) hl₂
  have hl₄ : l ∈ K₄ := le_sup_left (a := K₃) hl₃
  have h12 : K₁ ≤ K₂ := le_sup_left
  have h23 : K₂ ≤ K₃ := le_sup_left
  have h34 : K₃ ≤ K₄ := le_sup_left
  have h45 : K₄ ≤ K₅ := le_sup_left
  have h56 : K₅ ≤ K₆ := le_sup_left
  have h13 : K₁ ≤ K₃ := h12.trans h23
  have h14 : K₁ ≤ K₄ := h13.trans h34
  have h15 : K₁ ≤ K₅ := h14.trans h45
  have hprod : IntermediateField.relfinrank K₁ (fieldOf' l) =
      IntermediateField.relfinrank K₁ K₂ * IntermediateField.relfinrank K₂ K₃ *
        IntermediateField.relfinrank K₃ K₄ * IntermediateField.relfinrank K₄ K₅ *
        IntermediateField.relfinrank K₅ K₆ := by
    rw [hF, IntermediateField.relfinrank_mul_relfinrank h12 h23,
      IntermediateField.relfinrank_mul_relfinrank h13 h34,
      IntermediateField.relfinrank_mul_relfinrank h14 h45,
      IntermediateField.relfinrank_mul_relfinrank h15 h56]
  rw [hprod] at hpos ⊢
  simp only [ne_eq, mul_eq_zero, not_or] at hpos
  obtain ⟨⟨⟨⟨n2, n3⟩, n4⟩, n5⟩, n6⟩ := hpos
  have d2 : IntermediateField.relfinrank K₁ K₂ ∣ 2 :=
    dvd_two_of_le_two n2 (relfinrank_sup_adjoin_sq_le K₁ (s := sqrtNegOne)
      (by rw [sqrtNegOne_sq]; exact neg_mem (one_mem _)))
  have d3 : IntermediateField.relfinrank K₂ K₃ ∣ 2 :=
    dvd_two_of_le_two n3 (relfinrank_sup_adjoin_sq_le K₂ (s := sqrtLam l)
      (by rw [sqrtLam_sq]; exact hl₂))
  have d4 : IntermediateField.relfinrank K₃ K₄ ∣ 2 :=
    dvd_two_of_le_two n4 (relfinrank_sup_adjoin_sq_le K₃ (s := sqrtOneSubLam l)
      (by rw [sqrtOneSubLam_sq]; exact sub_mem (one_mem _) hl₃))
  have d5 : IntermediateField.relfinrank K₄ K₅ ∣ (3 ^ 2 - 1) * (3 ^ 2 - 3) :=
    relfinrank_sup_torsion_dvd K₄ hl₄ 3 b3
  have d6 : IntermediateField.relfinrank K₅ K₆ ∣ (5 ^ 2 - 1) * (5 ^ 2 - 5) :=
    relfinrank_sup_torsion_dvd K₅ (le_sup_left (a := K₄) hl₄) 5 b5
  norm_num at d5 d6
  have h184320 : (184320 : ℕ) = 2 * 2 * 2 * 48 * 480 := by norm_num
  rw [h184320]
  exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul d2 d3) d4) d5) d6

variable (P : CurveProviders) (x : Pt)

/-- The lift of `F_tpd = ℚ(λ) ⊆ F_λ` to `ℚ̄` is `ℚ(λ) ⊆ ℚ̄`. -/
theorem lift_tpd : IntermediateField.lift (tpd P x) = fieldOf x.1 := by
  have hemb : IntermediateField.lift (tpd P x) =
      (tpd P x).map (embC x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)) := rfl
  rw [hemb]
  change IntermediateField.map _ (tripodalFieldOf (curveOf x _ _).F (curveOf x _ _).E) = _
  rw [tripodalFieldOf_eq, IntermediateField.adjoin_map, Set.image_singleton, embC_apply]
  rfl

/-- **`[F_λ : F_tpd] ∣ 2¹²·3²·5`** for the curve of a point of the tripod. -/
theorem finrank_tpd_dvd : Module.finrank (tpd P x) (P.curve x).F ∣ 184320 := by
  haveI : Module.Finite (tpd P x) (P.curve x).F :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  have hpos : Module.finrank (tpd P x) (P.curve x).F ≠ 0 := Module.finrank_pos.ne'
  have key : Module.finrank (tpd P x) (P.curve x).F =
      IntermediateField.relfinrank (fieldOf x.1) (fieldOf' x.1) :=
    finrank_eq_relfinrank_of_lift_eq (lift_tpd P x) (fieldOf_le_fieldOf' x.1)
  rw [key] at hpos ⊢
  exact relfinrank_fieldOf_fieldOf'_dvd x hpos

/-- **`F_λ/F_tpd` is Galois** (`F_λ/ℚ(j)` is Galois, `Iut.Tripod.galois_deg_prime`). -/
theorem isGalois_tpd_curve (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    IsGalois (tpdC x h3 h5) (curveOf x h3 h5).F :=
  haveI : IsGalois (modC x h3 h5) (curveOf x h3 h5).F :=
    (galois_deg_prime x h3 h5 7 (by norm_num) le_rfl).1
  IsGalois.tower_top_of_isGalois (modC x h3 h5) _ _

end Degree

section Tame

variable (P : CurveProviders)

/-- **The residual tameness of `K/F_λ` away from `ℓ`** (IUT IV, Proposition 1.8: `E_λ` has
semistable reduction over `F_λ`, so at a place of residue characteristic `p ≠ ℓ` the inertia
acts on `E_λ[ℓ]` through a group of order dividing `ℓ`, by the Tate uniformization at the
bad places and Néron–Ogg–Shafarevich at the good ones): `p ∤ e(v/w)` for every place `v`
of `K = F_λ(E_λ[ℓ])` of residue characteristic `p ≠ ℓ`, `w` the place of `F_λ` below `v`. -/
def TameTorsionHyp : Prop :=
  ∀ (x : Pt) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
    (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw),
    haveI := ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl
      hP2).numberField_torsionField
    ∀ v : FinitePlace ↥((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ)
      hsl hP2).torsionField, residueChar v ≠ ℓ →
      ¬ residueChar v ∣ relRamIdx v (placeUnder (k := (P.curve x).F) v)

variable (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
  (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw)

/-- **The wild ramification bound** `v_p(e(v/u)) ≤ c_p` for the curves of the tripod (the
field `padicValNat_relRamIdx_le` of `Iut.TowerLocalFacts`), from the residual tameness of
`K/F_λ` away from `ℓ`, `e(v/w) ∣ [K : F_λ] ∣ |GL₂(𝔽_ℓ)|` and
`e(w/u) ∣ [F_λ : ℚ(λ)] ∣ 2¹²·3²·5`. -/
theorem padicValNat_relRamIdx_le_of_tame (htame : TameTorsionHyp P) :
    haveI := ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl
      hP2).numberField_torsionField
    ∀ v : FinitePlace ↥((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ)
      hsl hP2).torsionField,
      padicValNat (residueChar v)
        (relRamIdx v (placeTpd (P.curve x).F (P.curve x).E _ v)) ≤
        wildConst ℓ (residueChar v) := by
  haveI := ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl
    hP2).numberField_torsionField
  haveI : IsGalois (tpd P x) (P.curve x).F :=
    isGalois_tpd_curve x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)
  intro v
  set w : FinitePlace (P.curve x).F := placeUnder (k := (P.curve x).F) v with hw
  set u : FinitePlace (tpd P x) := placeTpd (P.curve x).F (P.curve x).E _ v with hu
  have hvw : FinitePlace.LiesOver v w := liesOver_placeUnder v
  have hwu : FinitePlace.LiesOver w u := by
    haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
    haveI : w.maximalIdeal.asIdeal.LiesOver
        (placeUnder (k := tpd P x) w).maximalIdeal.asIdeal := liesOver_placeUnder w
    have h : FinitePlace.LiesOver v (placeUnder (k := tpd P x) w) :=
      Ideal.LiesOver.trans v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal _
    have := eq_placeUnder_of_liesOver h
    rw [hu]
    change FinitePlace.LiesOver w (placeUnder (k := tpd P x) v)
    rw [← this]
    exact liesOver_placeUnder w
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  haveI : w.maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal := hwu
  have hmul : relRamIdx v u = relRamIdx w u * relRamIdx v w :=
    Ideal.ramificationIdx'_algebra_tower' u.maximalIdeal.asIdeal w.maximalIdeal.asIdeal
      v.maximalIdeal.asIdeal
  rw [hmul, mul_comm]
  refine padicValNat_mul_le_wildConst hℓ h7 (residueChar_prime v) ?_ ?_ ?_
  · exact (relRamIdx_dvd_finrank hvw).trans (finrank_torsionField_dvd _)
  · exact (relRamIdx_dvd_finrank hwu).trans (finrank_tpd_dvd P x)
  · exact htame x ℓ hℓ h7 hsl hP2 v

/-- **The residual local facts of the tower from the tameness of `K/F_λ` away from `ℓ`**,
Néron–Ogg–Shafarevich and the ramification bound away from `2·3·5·ℓ`. -/
theorem towerLocalHyp_of_tame (htame : TameTorsionHyp P)
    (hNOS : ∀ (x : Pt) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
      (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ),
        A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
      (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw),
      haveI := ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl
        hP2).numberField_torsionField
      ∀ v : FinitePlace ↥((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7
        (P.modRep x ℓ hℓ) hsl hP2).torsionField,
        residueChar v ∉ ({2, 3, 5, ℓ} : Finset ℕ) →
        ¬ IsBadTpdOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ)
          (placeTpd (P.curve x).F (P.curve x).E _ v) →
        relRamIdx v (placeTpd (P.curve x).F (P.curve x).E _ v) = 1)
    (hle : ∀ (x : Pt) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
      (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ),
        A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
      (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw),
      haveI := ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl
        hP2).numberField_torsionField
      ∀ v : FinitePlace ↥((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7
        (P.modRep x ℓ hℓ) hsl hP2).torsionField,
        residueChar v ∉ ({2, 3, 5, ℓ} : Finset ℕ) →
        relRamIdx v (placeTpd (P.curve x).F (P.curve x).E _ v) ≤ 30 * ℓ) :
    TowerLocalHyp P :=
  fun x ℓ hℓ h7 hsl hP2 =>
    haveI := ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl
      hP2).numberField_torsionField
    { padicValNat_relRamIdx_le := padicValNat_relRamIdx_le_of_tame P x hℓ h7 hsl hP2 htame
      relRamIdx_eq_one := hNOS x ℓ hℓ h7 hsl hP2
      relRamIdx_le := hle x ℓ hℓ h7 hsl hP2 }

end Tame

end Iut.Tripod
