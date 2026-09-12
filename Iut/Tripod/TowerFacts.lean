/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.BadRamIdx
import Iut.Tripod.TpdInertia

/-!
# The local facts of the tower `ℚ(λ) ⊆ F_λ ⊆ F_λ(E_λ[ℓ])` for the curves of the tripod

* `Iut.Tripod.relRamIdx_le_thirty_mul`, **the ramification bound away from `2·3·5·ℓ`**
  (the field `relRamIdx_le` of `Iut.TowerLocalFacts`): `e(v/u) = e(w/u)·e(v/w) ≤ 30·ℓ`, from
  `e(w/u) ≤ 30` (`Iut.Tripod.relRamIdx_tpd_le_thirty` at the bad places,
  `Iut.Tripod.relRamIdx_placeUnder_eq_one` at the good ones) and `e(v/w) ≤ ℓ`
  (`Iut.Tripod.relRamIdx_torsionField_le`);
* `Iut.Tripod.TameTwoHyp`, **the residual tameness of `K/F_λ` at the places over `2`**:
  `2 ∤ e(v/w)` for the places `v` of residue characteristic `2`. Away from `2` (and `ℓ`) the
  tameness is the theorem `Iut.Tripod.not_dvd_relRamIdx_torsionField`, so
  `Iut.Tripod.TameTorsionHyp P` follows (`Iut.Tripod.tameTorsionHyp_of_two`);
* `Iut.Tripod.towerLocalHyp_of_tameTwo`: **the residual local facts `Iut.Tripod.TowerLocalHyp P`
  hold**, given the tameness at `2` (Néron–Ogg–Shafarevich,
  `Iut.Tripod.relRamIdx_eq_one_of_not_bad`,
  and the ramification bound away from `2·3·5·ℓ` are theorems).

The places of residue characteristic `2` are excluded from the arguments of this package because
the reduction theory of the Legendre model used here (`Iut/Tower/ReductionKernel.lean`,
`Iut/Tower/MultiplicativeKernel.lean`) requires `v(2) = 1`.
-/

namespace Iut.Tripod

open Iut Iut.EllipticCurveData NumberField

open scoped Classical

variable (P : CurveProviders) (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
  (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw)
  [NumberField ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField]

/-- **The ramification bound away from `2·3·5·ℓ`**: `e(v/u) ≤ 30ℓ` for every place `v` of
`K = F_λ(E_λ[ℓ])` of residue characteristic `∉ {2, 3, 5, ℓ}`, `u` the place of `ℚ(λ)` below. -/
theorem relRamIdx_le_thirty_mul (v : FinitePlace ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField)
    (hp : residueChar v ∉ ({2, 3, 5, ℓ} : Finset ℕ)) :
    relRamIdx v (placeTpd (P.curve x).F (P.curve x).E
      (primeDataOf P x hℓ h7 hsl hP2).torsionField v) ≤ 30 * ℓ := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  obtain ⟨h2, h3, h5, hℓ'⟩ := hp
  have hvu : FinitePlace.LiesOver v (placeTpd (P.curve x).F (P.curve x).E
    (primeDataOf P x hℓ h7 hsl hP2).torsionField v) := liesOver_placeTpd v
  have hvw : FinitePlace.LiesOver v (placeUnder (k := (P.curve x).F) v) := liesOver_placeUnder v
  have hwu : FinitePlace.LiesOver (placeUnder (k := (P.curve x).F) v)
      (placeTpd (P.curve x).F (P.curve x).E (primeDataOf P x hℓ h7 hsl hP2).torsionField v) :=
    liesOver_placeUnder_of_liesOver hvu
  have hpw : residueChar (placeUnder (k := (P.curve x).F) v) = residueChar v :=
    (residueChar_eq_of_liesOver hvw).symm
  rw [relRamIdx_eq_mul_placeUnder (k := (P.curve x).F) hvu]
  have h1 : relRamIdx (placeUnder (k := (P.curve x).F) v) (placeTpd (P.curve x).F (P.curve x).E
      (primeDataOf P x hℓ h7 hsl hP2).torsionField v) ≤ 30 := by
    by_cases hu : placeTpd (P.curve x).F (P.curve x).E
        (primeDataOf P x hℓ h7 hsl hP2).torsionField v ∈ badT P x
    · exact relRamIdx_tpd_le_thirty P x hwu (by rw [hpw]; exact h2) (by rw [hpw]; exact h3)
        (by rw [hpw]; exact h5) hu
    · rw [relRamIdx_placeUnder_eq_one divPolyLegendreHyp hwu (by rw [hpw]; exact h2)
        (by rw [hpw]; exact h3) (by rw [hpw]; exact h5) hu]
      omega
  have h2' : relRamIdx v (placeUnder (k := (P.curve x).F) v) ≤ ℓ :=
    relRamIdx_torsionField_le P x hℓ h7 hsl hP2 v h2 hℓ'
  exact Nat.mul_le_mul h1 h2'

end Iut.Tripod

namespace Iut.Tripod

open Iut Iut.EllipticCurveData NumberField

/-- **The residual tameness of `K = F_λ(E_λ[ℓ])` over `F_λ` at the places over `2`**:
`2 ∤ e(v/w)` for every place `v` of `K` of residue characteristic `2`, `w` the place of `F_λ`
below `v` (IUT IV, Proposition 1.8: the semistable reduction of `E_λ` at the places over `2`
and the Tate uniformization / Néron–Ogg–Shafarevich there). Away from `2` and `ℓ` the tameness
is the theorem `Iut.Tripod.not_dvd_relRamIdx_torsionField`. -/
def TameTwoHyp (P : CurveProviders) : Prop :=
  ∀ (x : Pt) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
    (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw),
    haveI := ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl
      hP2).numberField_torsionField
    ∀ v : FinitePlace ↥((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ)
      hsl hP2).torsionField, residueChar v = 2 →
      ¬ 2 ∣ relRamIdx v (placeUnder (k := (P.curve x).F) v)

variable (P : CurveProviders)

/-- **The tameness of `K/F_λ` away from `ℓ`** from the tameness at `2`: away from `2` and `ℓ`
it is the theorem `Iut.Tripod.not_dvd_relRamIdx_torsionField`. -/
theorem tameTorsionHyp_of_two (h : TameTwoHyp P) : TameTorsionHyp P := by
  intro x ℓ hℓ h7 hsl hP2 v hℓ'
  haveI := ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl
    hP2).numberField_torsionField
  by_cases h2 : residueChar v = 2
  · have := h x ℓ hℓ h7 hsl hP2 v h2
    rw [h2]
    exact this
  · exact not_dvd_relRamIdx_torsionField P x hℓ h7 hsl hP2 v h2 hℓ'

/-- **The residual local facts of the tower hold for the curves of the tripod**, given the
tameness of `F_λ(E_λ[ℓ])/F_λ` at the places over `2`: Néron–Ogg–Shafarevich and the
ramification bound away from `2·3·5·ℓ` are theorems. -/
theorem towerLocalHyp_of_tameTwo (h : TameTwoHyp P) : TowerLocalHyp P :=
  towerLocalHyp_of_tame P (tameTorsionHyp_of_two P h)
    (fun x ℓ hℓ h7 hsl hP2 =>
      haveI := ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl
        hP2).numberField_torsionField
      fun v hp hbad => relRamIdx_eq_one_of_not_bad hℓ h7 hsl hP2 divPolyLegendreHyp v hp hbad)
    (fun x ℓ hℓ h7 hsl hP2 =>
      haveI := ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl
        hP2).numberField_torsionField
      fun v hp => relRamIdx_le_thirty_mul P x hℓ h7 hsl hP2 v hp)

end Iut.Tripod
