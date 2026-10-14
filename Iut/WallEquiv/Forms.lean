/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.WallEquiv.Basic

/-!
# Further formulations of the Scholze–Stix inequality

Restatements of `SSIneq D : (s − 1)·|log q| ≤ log-vol(hull(VC(I)))`, each a formulation of the wall
found in the sources ([LANA] §§9–10; Scholze–Stix, as summarized in [LANA] §10):

* **`ss_iff_lgp_vcI`** (the output of the η-algorithm on the whole container): the region
  `LGP·hull(VC(I))` has log-volume at least `−|log q|` (the `q`-pilot side of the variant
  inequality): "the Θ-pilot, transported and enlarged by (Ind3), still contains a region of
  volume `−|log q|`".
* **`ss_iff_exists_ind3`** (the (Ind3)-choice): there is an (Ind3)-choice `S ⊆ hull(VC(I))` of
  log-volume exactly `(s − 1)·|log q|` (the region `S` of (9-1) for the identified-copies output
  law).
* **`ss_iff_pilot_degrees`** (value-group / Frobenioid degrees): the difference of the degrees
  of the Θ-pilot and of the `q`-pilot, `deg_Θ(Θ-pilot) − deg(q-pilot) = (s − 1)·|log q|`, is at
  most the log-volume of the container `hull(VC(I))`: the excess degree created by the Θ-link
  (the hexagon's factor `s`, `hexagon_commutes_iff`) must be absorbed by the log-shell
  indeterminacy.
* **`ss_iff_theta_link_degrees`**: the same with the degree of the Θ-pilot read through the
  Θ-link `R_Θ ≅ R_q` (`thetaLink`, the value-group portion of every P19 Θ-link,
  `ThetaLinkIso.val_eq`): `s·deg(Θ-link(Θ-pilot)) − deg(q-pilot) ≤ log-vol(hull(VC(I)))`.
* `ssNoHull_iff_lgp_vcI`: the no-hull wall `SSIneqNoHull` is `−|log q| ≤ log-vol(LGP·VC(I))`.
-/

namespace Iut

namespace WallEquiv

open Wall

noncomputable section

variable (D : InitialThetaData.{0})

/-- The value line of the `q`-pilot BPS is `ℝ`. -/
def asReal (x : (qVal D.bpsDegrees).C) : ℝ := x

/-- **(SS) is the volume inequality for `LGP·hull(VC(I))`**:
`−|log q| ≤ log-vol(LGP·hull(VC(I)))`. -/
theorem ss_iff_lgp_vcI :
    SSIneq D ↔ (concreteVariantData D).qPilot.lhs ≤ logVol D (lgp D (hullOf D (vcI D))) := by
  rw [logVol_lgp D (isAdelic_hullOf_vcI D), logVol_lgp_integral]
  have hlhs : (concreteVariantData D).qPilot.lhs = -D.qPilot.absLogQ := rfl
  rw [hlhs, SSIneq]
  constructor <;> intro h <;> linarith

/-- **The no-hull wall is the volume inequality for `LGP·VC(I)`**:
`−|log q| ≤ log-vol(LGP·VC(I))`. -/
theorem ssNoHull_iff_lgp_vcI :
    SSIneqNoHull D ↔ (concreteVariantData D).qPilot.lhs ≤ logVol D (lgp D (vcI D)) := by
  rw [logVol_lgp D (isAdelic_vcI D), logVol_lgp_integral]
  have hlhs : (concreteVariantData D).qPilot.lhs = -D.qPilot.absLogQ := rfl
  rw [hlhs, SSIneqNoHull]
  constructor <;> intro h <;> linarith

/-- **(SS) as the existence of an (Ind3)-choice of log-volume `(s − 1)·|log q|`.** -/
theorem ss_iff_exists_ind3 :
    SSIneq D ↔ ∃ S : Ind3 D, logVol D S.1 = (sFactor (nC D) - 1) * D.qPilot.absLogQ :=
  (exists_ind3_logVol_iff D _).symm

/-- The difference of the pilot degrees is `(s − 1)·|log q|`. -/
theorem pilot_degrees_sub :
    asReal D (degTheta D.bpsDegrees D.wallS_ne_zero D.thetaValD.pilot) -
      asReal D (qVal D.bpsDegrees).pilot = (sFactor (nC D) - 1) * D.qPilot.absLogQ := by
  unfold asReal
  rw [degTheta_pilot, ← qVal_pilot, D.pilot_qVal]
  ring

/-- **(SS) in terms of the degrees of the pilots**: `deg_Θ(Θ-pilot) − deg(q-pilot) ≤
log-vol(hull(VC(I)))`. -/
theorem ss_iff_pilot_degrees :
    SSIneq D ↔ asReal D (degTheta D.bpsDegrees D.wallS_ne_zero D.thetaValD.pilot) -
      asReal D (qVal D.bpsDegrees).pilot ≤ logVol D (hullOf D (vcI D)) := by
  rw [pilot_degrees_sub]
  rfl

/-- **(SS) through the Θ-link**: `deg_Θ = s · (Θ-link)` (`degTheta_eq_smul_thetaLink`), so the
excess degree is `s·deg(Θ-link(Θ-pilot)) − deg(q-pilot)`. -/
theorem ss_iff_theta_link_degrees :
    SSIneq D ↔ D.wallS *
      asReal D ((thetaLink D.bpsDegrees D.wallS_ne_zero).toLinearEquiv D.thetaValD.pilot) -
      asReal D (qVal D.bpsDegrees).pilot ≤ logVol D (hullOf D (vcI D)) := by
  have h := congrArg (fun f => f D.thetaValD.pilot)
    (degTheta_eq_smul_thetaLink D.bpsDegrees D.wallS_ne_zero)
  simp only [LinearEquiv.coe_coe] at h
  rw [ss_iff_pilot_degrees]
  unfold asReal
  rw [h]
  rfl

end

end WallEquiv

end Iut
