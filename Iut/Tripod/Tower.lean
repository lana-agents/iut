/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.Main
import Iut.Tripod.TpdGalois
import Iut.Tripod.TwoAdic
import Iut.Concrete.ThetaLocalConstruct.Data

/-!
# The tower arithmetic for the curves of the tripod

For the Θ-data `Iut.EllipticCurveData.thetaData` of the Legendre curve `E_λ/F_λ` of a point
`λ` of the tripod and a prime `ℓ ≥ 7`, the tower arithmetic `Iut.TowerArithmetic` (IUT IV,
(R4) and Steps (ii), (iii) of Theorem 1.10) is derived from the residual local facts
`Iut.TowerLocalFacts` alone (`Iut.Tripod.towerArithmetic_of_towerLocalHyp`): the Galois
property and the degree bound of `F_tpd = ℚ(λ)` over `F_mod = ℚ(j)` are theorems
(`Iut.Tripod.isGalois_tpd`, `Iut.Tripod.finrank_tpd_le_six`), the degree bound
`[F_λ : ℚ] ≤ 552960·[ℚ(λ) : ℚ]` is `Iut.Tripod.deg_le`, and the bad locus and the bad residue
characteristics are those of the constructed `q`-pilot and theta local data.

`Iut.Tripod.TowerLocalHyp P` is the residual hypothesis: the local facts for every point,
prime `ℓ ≥ 7` and admissible-prime datum of the curves of `P : CurveProviders`.
-/

namespace Iut.Tripod

open Iut Iut.EllipticCurveData NumberField

universe v

variable (P : CurveProviders)

/-- **The residual local facts for the curves of the tripod** (IUT IV, Propositions 1.3
and 1.8, see `Iut.TowerLocalFacts`): for every point `λ`, prime `ℓ ≥ 7` with the
`SL₂`-image and coprimality conditions, the different bound, Néron–Ogg–Shafarevich, the
ramification bound away from `2·3·5·ℓ` and the ramification of `ℚ(λ)/ℚ(j)` at the bad
places, for the tower `ℚ(j) ⊆ ℚ(λ) ⊆ F_λ ⊆ F_λ(E_λ[ℓ])`. -/
def TowerLocalHyp : Prop :=
  ∀ (x : Pt) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
    (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw),
    haveI := ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl
      hP2).numberField_torsionField
    TowerLocalFacts (P.curve x).E ((P.curve x).VBadOf ℓ)
      ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl hP2)

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}

variable (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
  (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw)
  (hP5 : ∃ w ∈ (P.curve x).badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)
  (anab : AnabelianExistence AG TG)
  (hcore : AG.HasCore (AG.oncePunctured (P.curve x).E)
    (OrbicurveDataSection.CF AG (P.curve x).F (P.curve x).E))

/-- The Θ-data of the curve of a point of the tripod and a prime `ℓ`
(`Iut.EllipticCurveData.thetaData`). -/
noncomputable abbrev thetaDataOf : InitialThetaData AG TG :=
  (P.curve x).thetaData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl hP2 hP5 anab hcore

/-- The `q`-pilot inputs of the Θ-data of a point of the tripod. -/
theorem qPilotInputsOf : QPilotInputs (thetaDataOf P x hℓ h7 hsl hP2 hP5 anab hcore) :=
  (P.curve x).qPilotInputs (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl hP2 hP5 anab hcore

/-- **The tower arithmetic of the Θ-data of a point of the tripod**, from the residual local
facts and the torsion degree bounds. -/
theorem towerArithmetic_of_towerLocalHyp (hloc : TowerLocalHyp P)
    (hdeg3 : ∀ l : Qbar, TorsionDegreeBound l 3) (hdeg5 : ∀ l : Qbar, TorsionDegreeBound l 5)
    (LT : LocalTheory.{0, v} (thetaDataOf P x hℓ h7 hsl hP2 hP5 anab hcore).Kt)
    (htwo : TwoTorsionRational (thetaDataOf P x hℓ h7 hsl hP2 hP5 anab hcore)) :
    TowerArithmetic (thetaDataOf P x hℓ h7 hsl hP2 hP5 anab hcore) LT
      (thetaLocalData _ LT htwo (qPilotInputsOf P x hℓ h7 hsl hP2 hP5 anab hcore)) := by
  haveI : IsGalois
      ↥(fieldOfModuli (thetaDataOf P x hℓ h7 hsl hP2 hP5 anab hcore).F
        (thetaDataOf P x hℓ h7 hsl hP2 hP5 anab hcore).E)
      ↥(tripodalFieldOf (thetaDataOf P x hℓ h7 hsl hP2 hP5 anab hcore).F
        (thetaDataOf P x hℓ h7 hsl hP2 hP5 anab hcore).E) :=
    isGalois_tpd x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)
  refine towerArithmetic_of_localFacts _ LT _ (hloc x ℓ hℓ h7 hsl hP2)
    (finrank_tpd_le_six x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)) ?_ ?_ ?_
  · change Module.finrank ℚ (P.curve x).F ≤ 552960 * Module.finrank ℚ (tpd P x)
    rw [finrank_tpd]
    exact deg_le x _ _ (hdeg3 x.1) (hdeg5 x.1)
  · exact (qPilotInputsOf P x hℓ h7 hsl hP2 hP5 anab hcore).bad_finite
  · intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨w, (Set.Finite.mem_toFinset _).mp hw, rfl⟩

end Iut.Tripod
