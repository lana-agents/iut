/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Tower.Main
import Iut.Tripod.TpdGalois
import Iut.Tripod.TpdRamIdx
import Iut.Tripod.TwoAdic
import Iut.Concrete.ThetaLocalConstruct.Data

/-!
# The tower arithmetic for the curves of the tripod

For the Θ-data `Iut.EllipticCurveData.thetaData` of the Legendre curve `E_λ/F_λ` of a point
`λ` of the tripod and a prime `ℓ ≥ 7`, the tower arithmetic `Iut.TowerArithmetic` (IUT IV,
(R4) and Steps (ii), (iii) of Theorem 1.10) is derived from the residual local facts
`Iut.TowerLocalFacts` alone (`Iut.Tripod.towerArithmetic_of_towerLocalHyp`): the Galois
property and the degree bound of `F_tpd = ℚ(λ)` over `F_mod = ℚ(j)` are theorems
(`Iut.Tripod.isGalois_tpd`, `Iut.Tripod.finrank_tpd_le_six`), the ramification bound
`e(u/u₀) ≤ 2` of `ℚ(λ)/ℚ(j)` at the bad places is a theorem
(`Iut.Tripod.relRamIdx_tpd_le_two`), the degree bound
`[F_λ : ℚ] ≤ 552960·[ℚ(λ) : ℚ]` is `Iut.Tripod.deg_le`, and the bad locus and the bad residue
characteristics are those of the constructed `q`-pilot and theta local data.

`Iut.Tripod.TowerLocalHyp P` is the residual hypothesis: the three local facts (the wild
ramification bound `v_p(e(v/u)) ≤ c_p`, Néron–Ogg–Shafarevich, the ramification bound away
from `2·3·5·ℓ`) for every point, prime `ℓ ≥ 7` and admissible-prime datum of the curves of
`P : CurveProviders`. The wild ramification bound follows from the tameness of
`F_λ(E_λ[ℓ])/F_λ` away from `ℓ` (`Iut.Tripod.padicValNat_relRamIdx_le_of_tame`,
`Iut/Tripod/WildRamIdx.lean`), and the different bound of IUT IV, Proposition 1.3 is the
theorem `Iut.TowerLocalFacts.ordAt_different_le` (Serre's bound, `Iut/Tower/DifferentBound.lean`).
-/

namespace Iut.Tripod

open Iut Iut.EllipticCurveData NumberField


variable (P : CurveProviders)

/-- **The residual local facts for the curves of the tripod** (IUT IV, Proposition 1.8, see
`Iut.TowerLocalFacts`): for every point `λ`, prime `ℓ ≥ 7` with the `SL₂`-image and
coprimality conditions, the wild ramification bound `v_p(e(v/u)) ≤ c_p` (from the tameness
of `F_λ(E_λ[ℓ])/F_λ` away from `ℓ`, `Iut.Tripod.padicValNat_relRamIdx_le_of_tame`),
Néron–Ogg–Shafarevich and the ramification bound away from `2·3·5·ℓ`, for the tower
`ℚ(j) ⊆ ℚ(λ) ⊆ F_λ ⊆ F_λ(E_λ[ℓ])` (the ramification bound of `ℚ(λ)/ℚ(j)` at the bad
places is the theorem `Iut.Tripod.relRamIdx_tpd_le_two`; the different bound of
Proposition 1.3 is the theorem `Iut.TowerLocalFacts.ordAt_different_le`). -/
def TowerLocalHyp : Prop :=
  ∀ (x : Pt) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
    (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw),
    haveI := ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl
      hP2).numberField_torsionField
    TowerLocalFacts (P.curve x).E ((P.curve x).VBadOf ℓ)
      ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl hP2)

variable (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
  (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw)
  (hP5 : ∃ w ∈ (P.curve x).badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)
  (hcore : OrbicurveDataSection.HasCoreUniversally (P.curve x).F (P.curve x).E)

/-- The Θ-data of the curve of a point of the tripod and a prime `ℓ`
(`Iut.EllipticCurveData.thetaData`). -/
noncomputable abbrev thetaDataOf : InitialThetaData.{0} :=
  (P.curve x).thetaData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl hP2 hP5 hcore

/-- **The ramification of `ℚ(λ)/ℚ(j)` at the bad places of the Θ-data of a point**:
`e(u/u₀) ≤ 2` for `u₀ ∈ V_mod^bad(ℓ)` (`Iut.Tripod.relRamIdx_tpd_le_two`). -/
theorem relRamIdxModLeTwo_curve (ℓ : ℕ) :
    RelRamIdxModLeTwo (P.curve x).E ((P.curve x).VBadOf ℓ) :=
  fun u u₀ hu₀ huu₀ =>
    relRamIdx_tpd_le_two x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1) ℓ u u₀ hu₀ huu₀

/-- **The tower arithmetic of the Θ-data of a point of the tripod**, from the residual local
facts, the ramification bound at the bad places and the torsion degree bounds. -/
theorem towerArithmetic_of_towerLocalHyp (hloc : TowerLocalHyp P)
    (hdeg3 : ∀ x : Pt, TorsionDegreeBound x.1 3) (hdeg5 : ∀ x : Pt, TorsionDegreeBound x.1 5) :
    TowerArithmetic (thetaDataOf P x hℓ h7 hsl hP2 hP5 hcore) := by
  haveI : IsGalois
      ↥(fieldOfModuli (thetaDataOf P x hℓ h7 hsl hP2 hP5 hcore).F
        (thetaDataOf P x hℓ h7 hsl hP2 hP5 hcore).E)
      ↥(tripodalFieldOf (thetaDataOf P x hℓ h7 hsl hP2 hP5 hcore).F
        (thetaDataOf P x hℓ h7 hsl hP2 hP5 hcore).E) :=
    isGalois_tpd x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)
  refine towerArithmetic_of_localFacts _ (hloc x ℓ hℓ h7 hsl hP2)
    (relRamIdxModLeTwo_curve P x ℓ)
    (finrank_tpd_le_six x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)) ?_
  change Module.finrank ℚ (P.curve x).F ≤ 552960 * Module.finrank ℚ (tpd P x)
  rw [finrank_tpd]
  exact deg_le x _ _ (hdeg3 x) (hdeg5 x)

end Iut.Tripod
