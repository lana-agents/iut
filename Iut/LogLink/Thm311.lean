/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Kummer

/-!
# Theorem 3.11 of IUT III as a statement, and the chain to the ABC conjecture

For a log-theta-lattice `L` (`LogThetaLattice`) with unit-induced Kummer data `K`
(`LatticeKummer`), the multi-container model `K.model` has the vertices of `L` as Hodge theaters,
P18's η-algorithm (output `LGP·S`), and the Kummer identifications `K.kum`.

## Theorem 3.11 (`Thm311`)

The parts of IUT III, Theorem 3.11 that the model objects can express:

* (i) **multiradial representation**: the (Ind1), (Ind2) indeterminacies act on the
  (Ind3)-choices (`ind12`, the field (T1) of `Wall.EtaAlg`), and the outputs through any two
  vertices, transported to a common vertex, agree up to (Ind3) (`multiradial`, the permutation
  symmetries of the étale-picture; `MultiContainer.Multiradial3`, (C6) of M3);
* (ii) **the log-Kummer correspondence**: along every local vertical line the Kummer images of
  the units and of all iterated log-link images lie in the coric log-shell (`upperSemi`, (Ind3));
  the Kummer isomorphisms of the log-shell containers are compatible with the log-shells
  (`logShell`) and with log-volumes (`volCompat`, Proposition 3.9(iv), the last sentence of
  Theorem 3.11(ii));
* (iii) **Θ-link compatibility**: the horizontal arrows induce the full poly-isomorphisms of the
  `F^{⊢×μ}`-prime-strips (`thetaCompat`, Theorem 3.11(iii)(a), via Theorem 1.5(ii)).

**`thm311_model`: all of this holds in the model**, for every lattice and every unit-induced
Kummer data. The multiradiality is proved by transporting the (Ind3)-choice along the
log-shell compatible scaling `κ_{h₁'}·κ_{h₁}⁻¹` (`act_lgp`, `ind3Act`).

## Step (xi) and the chain to ABC

The contested step of the proof of Corollary 3.12 is Step (xi): the output of the multiradial
algorithm through the `n`-th column, transported along the Θ-link to the `(n+1)`-st column,
computes the `q`-pilot of the target (up to the indeterminacies). In the model this is
`XiPrinciple K` (the wall of the multi-container model along the horizontal arrows); it is an
explicit hypothesis and never assumed.

* **`variant_of_thm311`**: `Thm311 L K` and `XiPrinciple K` imply the Corollary 3.12 variant;
* **`wall_of_thm311`**: they give the input of `Iut/Wall`: `Wall D (theaterAlg D L.H)`;
* **`classicalABC_of_thm311`**: for families over all initial Θ-data, Theorem 3.11 (as
  `Thm311`) and Step (xi) (as `XiPrinciple`) imply `ClassicalABC`, through
  `Wall.classicalABC_of_wall`;
* **`xi_iff_ss`**: in the lattice model, Step (xi) *is* the Scholze–Stix inequality
  `SSIneq D : (s − 1)·|log q| ≤ log-vol(VC(I))`.

## The answer to the question (5) of the work package

In the lattice model (`answer`): the distortion of the transport along every horizontal
(Θ-link) and every vertical (log-link) arrow is `0`; the η-algorithm through any vertex has the
identified-copies output law (`ThetaShift`: `log-vol(LGP·S) = −s·|log q| + log-vol(S)`, also read
in the coric container or transported to any vertex, `logVol_transport_out`); and Step (xi) is
`SSIneq D`. This holds also for alien Kummer data (`LatticeKummer.alt`: the transports along
all horizontal and vertical arrows are not ring isomorphisms, `alt_alien_horiz`,
`alt_alien_vert`). So the log-theta-lattice, as modelled here, does **not** provide an
η-algorithm whose output law differs from the identified-copies law: the vertical log-links
enter the containers only through (Ind3) (inclusions into the log-shell, which the wall already
quantifies over by `∃ S`) and through unit-induced, hence volume-neutral, Kummer
identifications. A different law would need a Kummer identification that is not unit-induced
(as `qScale^k`, which moves value-group data into the unit portion,
`not_unitInducedScaling_qScale_zpow`) or an output that is not `LGP` acting on an (Ind3)-choice;
neither is produced by the structures formalised here. This is a statement about the model; it
neither proves nor refutes `SSIneq D`.
-/

namespace Iut

namespace LogLink

open Wall ThetaLink HodgeTheater NumberField
open scoped Valued

noncomputable section

variable {D : InitialThetaData.{0}}

/-! ### Scalings, LGP and the (Ind3)-choices -/

theorem logShellCompat_mul {a b : Scaling D} (ha : LogShellCompat D a) (hb : LogShellCompat D b) :
    LogShellCompat D (a * b) := by
  unfold LogShellCompat at *
  rw [act_mul, hb, ha]

theorem logShellCompat_inv {a : Scaling D} (ha : LogShellCompat D a) : LogShellCompat D a⁻¹ := by
  unfold LogShellCompat at *
  conv_lhs => rw [← ha]
  exact act_inv_act D a _

theorem act_act_inv (w : Scaling D) (S : Region D) : act D w (act D w⁻¹ S) = S := by
  rw [← act_mul, mul_inv_cancel, act_one]

/-- **Scalings commute with `LGP`** (both are componentwise multiplications). -/
theorem act_lgp (w : Scaling D) (S : Region D) : act D w (lgp D S) = lgp D (act D w S) := by
  funext i
  refine admissibleRegion_ext D (funext fun vQ => ?_)
  rcases vQ with p | _
  · change actMap D w i p '' (lgpMap D i p '' (S i).region (.finite p)) =
      lgpMap D i p '' (actMap D w i p '' (S i).region (.finite p))
    rw [Set.image_image, Set.image_image]
    congr 1
    funext x
    funext c
    exact mul_left_comm _ _ _
  · rfl

/-- Scalings are monotone. -/
theorem act_le {w : Scaling D} {S T : Region D} (h : ∀ i, S i ≤ T i) (i : Fin (nC D)) :
    act D w S i ≤ act D w T i := by
  intro vQ
  rcases vQ with p | _
  · exact Set.image_mono (h i (.finite p))
  · exact h i .infinite

/-- A log-shell compatible scaling maps (Ind3)-choices to (Ind3)-choices. -/
def ind3Map {w : Scaling D} (hw : LogShellCompat D w) (S : Ind3 D) : Ind3 D :=
  ⟨act D w S.1, isAdelic_act D w S.2.1, fun i => by
    have := act_le (w := w) S.2.2 i
    rwa [show act D w (vcI D) i = vcI D i from congrFun hw i] at this⟩

/-- **A log-shell compatible scaling permutes the (Ind3)-choices.** -/
def ind3Act {w : Scaling D} (hw : LogShellCompat D w) : Ind3 D ≃ Ind3 D where
  toFun := ind3Map hw
  invFun := ind3Map (logShellCompat_inv hw)
  left_inv S := Subtype.ext (act_inv_act D w S.1)
  right_inv S := Subtype.ext (act_act_inv w S.1)

/-! ### Theorem 3.11 -/

/-- The horizontal arrows `(n, m) → (n + 1, m)` of the lattice. -/
def horizRel (a b : ℤ × ℤ) : Prop := b = (a.1 + 1, a.2)

/-- The vertical arrows `(n, m) → (n, m + 1)` of the lattice. -/
def vertRel (a b : ℤ × ℤ) : Prop := b = (a.1, a.2 + 1)

/-- **IUT III, Theorem 3.11, as a statement about a log-theta-lattice `L` with Kummer data `K`**
(see the module docstring for the parts). -/
structure Thm311 (L : LogThetaLattice D) (K : LatticeKummer L) : Prop where
  /-- (i) (Ind1), (Ind2) act on the (Ind3)-choices. -/
  ind12 : ∀ {B : K.model.alg.BPSA} {h : K.model.HT} (α : EtUnitIso B.et B.et)
    (ι : K.model.alg.Choice B h), ∃ τ : Ind3 D ≃ Ind3 D, ∀ S,
      K.model.alg.out ((BPS.Iso.mk α (ValBPS.Iso.refl _)).trans ι) S = K.model.alg.out ι (τ S)
  /-- (i) The multiradial representation: outputs through any two vertices, transported to a
  common vertex, agree up to (Ind3). -/
  multiradial : K.model.Multiradial3
  /-- (ii) Upper semi-compatibility of the log-Kummer correspondence along the local vertical
  lines (Ind3). -/
  upperSemi : ∀ (n : ℤ) (w : FinitePlace ↥(fieldOfModuli D.F D.E)) {p : ℕ} (_hp : p.Prime)
    (_hpk : ‖(p : Kfin D w)‖ < 1) (m' : ℕ) (m : ℤ),
      (L.loc n w).kum m '' (L.loc n w).iter m' m ⊆ Iut.logShell (Kfin D w) p
  /-- (ii) The Kummer isomorphisms of the containers are compatible with the log-shells. -/
  logShell : ∀ a, LogShellCompat D (K.kum a)
  /-- (ii) ... and with the log-volumes (Proposition 3.9(iv)). -/
  volCompat : K.model.KummerVolCompat
  /-- (iii) The horizontal arrows induce the full poly-isomorphisms of the
  `F^{⊢×μ}`-prime-strips. -/
  thetaCompat : ∀ (n m : ℤ) (f : (L.H (n, m)).Fmu.Iso (L.H (n + 1, m)).Fmu),
    ∃ θ : ThetaLinkIso D (L.H (n, m)) (L.H (n + 1, m)), ThetaLinkIso.unitEquiv _ _ θ = f

namespace LatticeKummer

variable {L : LogThetaLattice D} (K : LatticeKummer L)

theorem model_out {B : K.model.alg.BPSA} {h : K.model.HT} (ι : K.model.alg.Choice B h)
    (S : Ind3 D) : K.model.alg.out ι S = lgp D S.1 := rfl

theorem model_transport (a b : ℤ × ℤ) (U : Region D) :
    K.model.transport a b U = act D (K.kum b * (K.kum a)⁻¹) U := rfl

/-- **Theorem 3.11(i), multiradiality, holds in the lattice model.** -/
theorem model_multiradial3 : K.model.Multiradial3 := by
  intro h₁ h₁' h₂ ι ι'
  have hw : LogShellCompat D (K.kum h₁' * (K.kum h₁)⁻¹) :=
    logShellCompat_mul (K.logShellCompat h₁') (logShellCompat_inv (K.logShellCompat h₁))
  refine ⟨ind3Act hw, fun S => ?_⟩
  rw [model_out, model_out, model_transport, model_transport]
  change _ = act D _ (lgp D (act D _ S.1))
  rw [← act_lgp, ← act_mul]
  congr 1
  group

theorem model_thetaShift : K.model.alg.ThetaShift := theaterAlg_thetaShift D L.H

end LatticeKummer

/-- **Theorem 3.11 holds in the model** for every lattice with unit-induced Kummer data. -/
theorem thm311_model (L : LogThetaLattice D) (K : LatticeKummer L) : Thm311 L K where
  ind12 α ι := K.model.alg.ind12_acts_on_S α ι
  multiradial := K.model_multiradial3
  upperSemi n w _ hp hpk m' m := (L.loc n w).upperSemiCompat hp hpk m' m
  logShell := K.logShellCompat
  volCompat := K.model_kummerVolCompat
  thetaCompat n m f := L.horizCoric_full n m f

/-! ### Step (xi) and the chain to ABC -/

/-- **Step (xi) of the proof of Corollary 3.12** (the contested step), in the lattice model: the
output through each vertex, transported along the Θ-link to the next vertex of its row, computes
the `q`-pilot of the target up to the indeterminacies. A hypothesis, never assumed. -/
def XiPrinciple {L : LogThetaLattice D} (K : LatticeKummer L) : Prop :=
  K.model.WallOn horizRel

variable {L : LogThetaLattice D} {K : LatticeKummer L}

theorem horizRel_nonempty : ∃ a b : ℤ × ℤ, horizRel a b := ⟨(0, 0), (1, 0), rfl⟩

theorem model_volCompat_of_thm311 (h : Thm311 L K) : K.model.VolCompat :=
  K.model.volCompat_of_kummerVolCompat h.volCompat

/-- **Theorem 3.11 and Step (xi) imply the Corollary 3.12 variant.** -/
theorem variant_of_thm311 (h : Thm311 L K) (hx : XiPrinciple K) :
    Corollary312Variant (concreteVariantData D) :=
  K.model.variant_of_wallOn_of_volCompat (model_volCompat_of_thm311 h) horizRel_nonempty hx

/-- **In the lattice model, Step (xi) is the Scholze–Stix inequality.** -/
theorem xi_iff_ss (h : Thm311 L K) : XiPrinciple K ↔ SSIneq D :=
  K.model.wallOn_iff_ss_of_volCompat K.model_thetaShift (model_volCompat_of_thm311 h)
    horizRel_nonempty

/-- **Theorem 3.11 and Step (xi) give the input of `Iut/Wall`**: the wall `Wall D A` for the
η-algorithm `A = theaterAlg D L.H` over the vertices of the lattice. -/
theorem wall_of_thm311 (h : Thm311 L K) (hx : XiPrinciple K) : Iut.Wall D (theaterAlg D L.H) := by
  have hV := model_volCompat_of_thm311 h
  refine (K.model.wall3_iff_wall_of_volCompat hV).mp ?_
  exact (K.model.wallOn_iff_ss_of_volCompat K.model_thetaShift hV ⟨(0, 0), (0, 0), trivial⟩).mpr
    ((xi_iff_ss h).mp hx)

/-- **The formal chain "Theorem 3.11 + Step (xi) ⇒ ABC"**: for families of log-theta-lattices
with Kummer data over all initial Θ-data, Theorem 3.11 (`Thm311`) and Step (xi)
(`XiPrinciple`) imply the ABC conjecture, through `Wall.classicalABC_of_wall`. -/
theorem classicalABC_of_thm311 (L : ∀ D : InitialThetaData.{0}, LogThetaLattice D)
    (K : ∀ D, LatticeKummer (L D)) (h : ∀ D, Thm311 (L D) (K D)) (hx : ∀ D, XiPrinciple (K D)) :
    ClassicalABC :=
  classicalABC_of_wall (fun D => theaterAlg D (L D).H) fun D => wall_of_thm311 (h D) (hx D)

/-- Since Theorem 3.11 holds in the model, Step (xi) alone (for some lattice with Kummer data
over every initial Θ-data) implies the ABC conjecture. -/
theorem classicalABC_of_xi
    (hx : ∀ D : InitialThetaData.{0}, ∃ (L : LogThetaLattice D) (K : LatticeKummer L),
      XiPrinciple K) : ClassicalABC := by
  choose L K hK using hx
  exact classicalABC_of_thm311 L K (fun D => thm311_model (L D) (K D)) hK

/-- Step (xi) for one lattice is equivalent to Step (xi) for any other one. -/
theorem xi_iff_xi {L' : LogThetaLattice D} (K' : LatticeKummer L') :
    XiPrinciple K ↔ XiPrinciple K' :=
  (xi_iff_ss (thm311_model L K)).trans (xi_iff_ss (thm311_model L' K')).symm

/-! ### The answer to (5) -/

/-- The outputs through any vertex, transported to any vertex, have the identified-copies
log-volume. -/
theorem logVol_transport_out (a b : ℤ × ℤ) {B : K.model.alg.BPSA}
    (ι : K.model.alg.Choice B a) (S : Ind3 D) :
    logVol D (K.model.transport a b (K.model.alg.out ι S)) =
      -(sFactor (nC D) * D.qPilot.absLogQ) + logVol D S.1 := by
  have e := K.model.logVol_transport a b (K.model.alg.realisation ι S).1
  unfold MultiContainer.vol at e
  rw [e, K.distortion_eq_zero, add_zero]
  exact K.model_thetaShift ι S

/-- **The answer to (5)** in the lattice model: zero distortion along horizontal and vertical
arrows, the identified-copies output law, and Step (xi) equal to the Scholze–Stix inequality. -/
theorem answer (L : LogThetaLattice D) (K : LatticeKummer L) :
    (∀ n m, K.model.distortion (n, m) (n + 1, m) = 0) ∧
    (∀ n m, K.model.distortion (n, m) (n, m + 1) = 0) ∧
    K.model.alg.ThetaShift ∧ (XiPrinciple K ↔ SSIneq D) :=
  ⟨K.distortion_horiz, K.distortion_vert, K.model_thetaShift, xi_iff_ss (thm311_model L K)⟩

/-- In `LatticeKummer.alt`, the transports along the horizontal arrows are not ring
isomorphisms. -/
theorem alt_alien_horiz (L : LogThetaLattice D) (n m : ℤ) :
    ¬ (LatticeKummer.alt L).model.IsRingTransport (n, m) (n + 1, m) := by
  classical
  rw [MultiContainer.isRingTransport_iff]
  change (if Even (n + m) then 1 else negScale D) ≠ (if Even (n + 1 + m) then 1 else negScale D)
  have e : n + 1 + m = n + m + 1 := by ring
  rw [e]
  rcases Int.even_or_odd (n + m) with h | h
  · rw [if_pos h, if_neg (Int.not_even_iff_odd.mpr (Even.add_one h))]
    exact (negScale_ne_one D).symm
  · rw [if_neg (Int.not_even_iff_odd.mpr h), if_pos (Odd.add_one h)]
    exact negScale_ne_one D

/-- In `LatticeKummer.alt`, the transports along the vertical arrows are not ring isomorphisms. -/
theorem alt_alien_vert (L : LogThetaLattice D) (n m : ℤ) :
    ¬ (LatticeKummer.alt L).model.IsRingTransport (n, m) (n, m + 1) := by
  classical
  rw [MultiContainer.isRingTransport_iff]
  change (if Even (n + m) then 1 else negScale D) ≠ (if Even (n + (m + 1)) then 1 else negScale D)
  have e : n + (m + 1) = n + m + 1 := by ring
  rw [e]
  rcases Int.even_or_odd (n + m) with h | h
  · rw [if_pos h, if_neg (Int.not_even_iff_odd.mpr (Even.add_one h))]
    exact (negScale_ne_one D).symm
  · rw [if_neg (Int.not_even_iff_odd.mpr h), if_pos (Odd.add_one h)]
    exact negScale_ne_one D

end

end LogLink

end Iut
