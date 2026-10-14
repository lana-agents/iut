/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Thm311LGP
import Iut.Wall.Checks
import Iut.Concrete.Literal

/-!
# Equivalent formulations of the wall

The "wall" is the step of IUT III from Theorem 3.11 to Corollary 3.12 that the LANA report
([LANA], §9.2) could not reconstruct. It appears in several forms in the sources and in this
repository; this file collects them for fixed initial Θ-data `D` and proves the equivalences
that hold, in the models built in `Iut/Wall`, `Iut/HodgeTheater`, `Iut/ThetaLink`, `Iut/LogLink`.

## The formulations (for fixed `D`)

* **(SS)** the **Scholze–Stix inequality** `SSIneq D : (s − 1)·|log q| ≤ log-vol(hull(VC(I)))`
  (`Iut/Wall/MultiContainer.lean`), with IUT's container volume, the log-volume of the
  holomorphic hull of the log-shell container (`Iut/WallEquiv/VcI.md`); the no-hull wall
  `SSIneqNoHull D` (`≤ log-vol(VC(I))`) implies it (`ssIneq_of_noHull`).
* **(9-1) literal, on Hodge theaters** (`Lana91 H`): for every P19 Θ-link
  `ThetaLinkIso D (H h₁) (H h₂)` between P18 Hodge theaters `H h₁`, `H h₂`, there are a choice
  `ι` and an (Ind3)-choice `S` with **`η^anab_{ι,S} = η_q`** as pointed linear maps
  `R_val → R_ss ≅ ℝ` ([LANA], §9.2, pp. 45–46: "there exists some suitable `S` such that
  `η_q = η^anab_S`"), for the η-algorithm `theaterAlg D H` whose sides are the theaters.
* **(9-1) on the BPS layer** (`Wall D A`, `Iut/Wall/EtaAlg.lean`), for an η-algorithm `A`.
* **(9-1) as an equation of numbers** (`Exists91 D`): there is an (Ind3)-choice `S` with
  `log-vol(LGP·S) = −|log q|` (the identified-copies output law).
* **(xi)** the (xi)-principle `XiPrinciple K` for a log-theta-lattice with Kummer data
  (IUT III, proof of Corollary 3.12, Step (xi); `Iut/LogLink/Thm311.lean`), also for
  LGP-Gaussian lattices (`Iut/LogLink/Thm311LGP.lean`).
* **(M3)** the multi-container walls `Wall3`, `WallOn` (`Iut/Wall/MultiContainer.lean`) of the
  identified-copies model and of the model over Hodge theaters.
* **(Var)** the **Corollary 3.12 variant** `Corollary312Variant (concreteVariantData D)`, i.e. the
  log-volume inequality **`−|log q| ≤ −|log Θ|`** (`Iut/Cor312/Statement.lean`), its numerical
  (9-1) form `NumericalWall D` and the existential forms `∃ A, Wall D A` (`Iut/Wall/Checks.lean`).
* (facts, not formulations of the wall) the **hexagon** of [LANA] §10.2/Scholze–Stix does not
  commute (`InitialThetaData.hexagon_not_commutes`, `s ≠ 1`); the Θ-pilot and `q`-pilot objects
  are not isomorphic in the global realified Frobenioid (`isEmpty_iso_thetaPilot_qPilot`).

## Results

* **`wallEquiv`**: (SS) ⇔ (9-1) on Hodge theaters ⇔ (9-1) on the BPS layer for `theaterAlg` ⇔
  (9-1) for the identified-copies algorithm ⇔ the numerical (9-1) `Exists91` ⇔ (xi) for every
  log-theta-lattice with Kummer data ⇔ (xi) for every LGP-Gaussian lattice ⇔ `Wall3` of the
  identified-copies model and of the model over any family of Hodge theaters.
* **`wall_iff_ss_of_thetaShift`**: for *every* η-algorithm whose outputs obey the
  identified-copies law (`ThetaShift`: `log-vol(LGP·S) = −s·|log q| + log-vol(S)`), (9-1) is (SS);
  a different wall needs a different output law or a nonzero distortion of the transport
  (`MultiContainer.wallOn_iff_of_thetaShift`:
  `(s − 1)·|log q| − distortion ≤ log-vol(hull(VC(I)))`).
* **`variant_of_ss`**: (SS) ⇒ (Var). The converse fails in general: (Var) is equivalent to the
  existence of *some* η-algorithm satisfying (9-1) (`exists_wall_iff`, the trivial instance),
  while (SS) is (9-1) for the identified-copies algorithms of the models.
* (Var) ⇔ `NumericalWall D` ⇔ `∃ A, Wall D A` (`variant_iff`).
* Global: (SS) for all `D` ⇒ `Cor312VariantHolds` ⇒ `Cor312LiteralHolds`, and
  `Cor312VariantHolds` ⇒ `ClassicalABC` (`classicalABC_of_ss`).

Everything here is a statement about the models; neither (SS) nor its negation is proved.
-/

namespace Iut

namespace WallEquiv

open Wall HodgeTheater ThetaLink LogLink NumberField

noncomputable section

variable (D : InitialThetaData.{0})

/-! ### (9-1) with Hodge theaters and Θ-links -/

/-- **The LANA report's (9-1), literally, on the Hodge theaters `H`** ([LANA], §9.2): for every
Θ-link between two of the theaters (P19's `ThetaLinkIso`), there is an `S` (with a choice `ι`
of Step 1) such that `η_q = η^anab_S` as pointed linear maps `R_val → R_ss ≅ ℝ`. -/
def Lana91 {σ : Type} [Nonempty σ] (H : σ → ThetaPmEllNFHT D) : Prop :=
  ∀ (h₁ h₂ : σ) (_lk : ThetaLinkIso D (H h₁) (H h₂)),
    ∃ (ι : (theaterAlg D H).Choice ((theaterAlg D H).qBPS h₂) h₁) (S : Ind3 D),
      (theaterAlg D H).etaAnab ι S = etaQ D

/-- **(9-1) as an equation of numbers**: some (Ind3)-choice `S` has
`log-vol(LGP·S) = −|log q|`. -/
def Exists91 : Prop :=
  ∃ S : Ind3 D, logVol D (lgp D S.1) = (concreteVariantData D).qPilot.lhs

variable {D}

/-- **(9-1) on Hodge theaters is (9-1) on the BPS layer** for the η-algorithm over the theaters:
the Θ-links exist (`nonempty_thetaLink`), so the quantifiers over them are vacuous on both
sides ([LANA], Remark 8.2.1). -/
theorem lana91_iff_wall {σ : Type} [Nonempty σ] (H : σ → ThetaPmEllNFHT D) :
    Lana91 D H ↔ Wall D (theaterAlg D H) := by
  rw [wall_iff_forall]
  constructor
  · intro h h₁ h₂
    exact h h₁ h₂ (ThetaLink.nonempty_thetaLink (H h₁) (H h₂)).some
  · intro h h₁ h₂ _
    exact h h₁ h₂

/-- **(9-1) on the BPS layer, for the η-algorithm over Hodge theaters, is (SS).** -/
theorem wall_theaterAlg_iff_ss {σ : Type} [Nonempty σ] (H : σ → ThetaPmEllNFHT D) :
    Wall D (theaterAlg D H) ↔ SSIneq D := by
  exact ((theaterModel D H).wall3_iff_wall_of_volCompat (theaterModel_volCompat D H)).symm.trans
    (wall3_theaterModel_iff D H)

/-- **(9-1) on Hodge theaters is (SS).** -/
theorem lana91_iff_ss {σ : Type} [Nonempty σ] (H : σ → ThetaPmEllNFHT D) :
    Lana91 D H ↔ SSIneq D :=
  (lana91_iff_wall H).trans (wall_theaterAlg_iff_ss H)

/-- **The numerical (9-1) is (SS).** -/
theorem exists91_iff_ss : Exists91 D ↔ SSIneq D := by
  unfold Exists91 SSIneq
  have hlhs : (concreteVariantData D).qPilot.lhs = -D.qPilot.absLogQ := rfl
  constructor
  · rintro ⟨S, hS⟩
    rw [logVol_lgp D S.2.1, logVol_lgp_integral, hlhs] at hS
    have hle := logVol_le_vcI D S
    linarith
  · intro h
    have hW := (wall_idAlg_iff D).2 h
    obtain ⟨ι, S, hη⟩ := (wall_iff_forall _).1 hW () ()
    exact ⟨S, ((idAlg D).etaAnab_eq_etaQ_iff ι S).1 hη⟩

/-- **For every η-algorithm with the identified-copies output law, (9-1) is (SS)**: in the
one-container model `ofAlg A` (all Kummer identifications the identity, no distortion). -/
theorem wall_iff_ss_of_thetaShift (A : EtaAlg D) (hS : A.ThetaShift) : Wall D A ↔ SSIneq D := by
  obtain ⟨h⟩ := A.side_nonempty
  exact (MultiContainer.wall3_ofAlg_iff A).symm.trans
    ((MultiContainer.ofAlg A).wallOn_iff_ss_of_volCompat hS (MultiContainer.ofAlg_volCompat A)
      ⟨h, h, trivial⟩)

/-- **(xi) is (SS)** for every log-theta-lattice with unit-induced Kummer data. -/
theorem xi_iff_ss_model (L : LogThetaLattice D) (K : LatticeKummer L) :
    XiPrinciple K ↔ SSIneq D :=
  xi_iff_ss (thm311_model L K)

/-- **(xi) is (SS)** for every LGP-Gaussian log-theta-lattice. -/
theorem xi_iff_ss_lgp_model (L : LGPLattice D) (K : LatticeKummer L.toLogThetaLattice) :
    XiPrinciple K ↔ SSIneq D :=
  xi_iff_ss_lgp (thm311LGP_model L K)

variable (D)

/-- **The collected equivalences** (see the module docstring). -/
theorem wallEquiv :
    (SSIneq D ↔ Exists91 D) ∧
    (SSIneq D ↔ Wall D (idAlg D)) ∧
    (∀ (σ : Type) [Nonempty σ], SSIneq D ↔ (idModel D σ).Wall3) ∧
    (∀ (σ : Type) [Nonempty σ] (H : σ → ThetaPmEllNFHT D),
      (SSIneq D ↔ Lana91 D H) ∧ (SSIneq D ↔ Wall D (theaterAlg D H)) ∧
      (SSIneq D ↔ (theaterModel D H).Wall3)) ∧
    (∀ (L : LogThetaLattice D) (K : LatticeKummer L), SSIneq D ↔ XiPrinciple K) ∧
    (∀ (L : LGPLattice D) (K : LatticeKummer L.toLogThetaLattice), SSIneq D ↔ XiPrinciple K) :=
  ⟨exists91_iff_ss.symm, (wall_idAlg_iff D).symm, fun σ _ => (wall3_idModel_iff D σ).symm,
    fun _ _ H => ⟨(lana91_iff_ss H).symm, (wall_theaterAlg_iff_ss H).symm,
      (wall3_theaterModel_iff D H).symm⟩,
    fun L K => (xi_iff_ss_model L K).symm, fun L K => (xi_iff_ss_lgp_model L K).symm⟩

/-! ### (SS) and the Corollary 3.12 variant -/

/-- **(SS) implies the Corollary 3.12 variant** `−|log q| ≤ −|log Θ|` (through the
identified-copies algorithm). -/
theorem variant_of_ss (h : SSIneq D) : Corollary312Variant (concreteVariantData D) :=
  variant_of_wall (idAlg D) ((wall_idAlg_iff D).2 h)

/-- **The variant, its numerical (9-1) form, and the existence of an η-algorithm with (9-1).** -/
theorem variant_iff :
    (Corollary312Variant (concreteVariantData D) ↔
      (concreteVariantData D).qPilot.lhs ≤ (concreteVariantData D).rhsData.rhs) ∧
    (Corollary312Variant (concreteVariantData D) ↔ NumericalWall D) ∧
    (Corollary312Variant (concreteVariantData D) ↔ ∃ A : EtaAlg D, Wall D A) :=
  ⟨corollary312Variant_iff _, (numericalWall_iff D).symm, (exists_wall_iff D).symm⟩

/-- **Globally: (SS) for all initial Θ-data implies the variant, its literal reading, and ABC.** -/
theorem classicalABC_of_ss (h : ∀ D : InitialThetaData.{0}, SSIneq D) :
    Cor312VariantHolds ∧ Cor312LiteralHolds ∧ ClassicalABC :=
  have hv : Cor312VariantHolds := fun D => variant_of_ss D (h D)
  ⟨hv, cor312Literal_of_variant hv, classicalABC_of_variant hv⟩

/-- **Facts accompanying the wall**: the hexagon does not commute (`s ≠ 1`), and the Θ-pilot and
`q`-pilot objects of the global realified Frobenioid are not isomorphic. -/
theorem wall_facts :
    (degTheta D.bpsDegrees D.wallS_ne_zero).toLinearMap ≠
      (thetaLink D.bpsDegrees D.wallS_ne_zero).toLinearEquiv.toLinearMap ∧
    IsEmpty (Frobenioid.thetaPilotObj D ≅ Frobenioid.qPilotObj D) :=
  ⟨D.hexagon_not_commutes, Frobenioid.isEmpty_iso_thetaPilot_qPilot D⟩

end

end WallEquiv

end Iut
