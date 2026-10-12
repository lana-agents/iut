/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.ThetaLink.Link
import Iut.Wall.MultiConstraints

/-!
# Θ-linked Hodge theaters in the multi-container model of the wall

The multi-container model (`Iut/Wall/MultiContainer.lean`, M3) found that, for outputs with the
identified-copies log-volumes, the wall along a relation `L` of Hodge theaters is
`(s − 1)·|log q| − distortion(h₁, h₂) ≤ log-vol(VC(I))` for `L h₁ h₂`
(`MultiContainer.wallOn_iff_of_thetaShift`), where the **distortion** is the log-volume shift of
the transport `κ_{h₂} ∘ κ_{h₁}⁻¹` between the containers of the two theaters. The open point was
what the transport *along a Θ-link* is.

Here the sides are the Hodge theaters of a **Frobenius-picture** `n ↦ ⁿHT` with actual Θ-links
`ⁿHT → ⁿ⁺¹HT` (`Link.lean`), and the Kummer identification of each theater's log-shell
container with the coric one is required to be **log-shell compatible**:
`κ_n(VC(I)) = VC(I)` (`LogShellCompat`). The justification is the structure of the Θ-link: the
only data it transports are the unit portions (`ThetaLinkIso.unitEquiv`: a Θ-link *is* an
isomorphism of the `F^{⊢×μ}`-prime-strips), the log-shells are constructed from the unit
portions (IUT III, Proposition 1.2(vi), (vii), Definition 1.1), and the comparison of volumes on
the two sides goes through the coricity of the units (IUT II, Remark 4.10.3(i); IUT III,
Proposition 3.9(ii)). The value-group portion, which the Θ-link rescales by `1/s`
(`ThetaLinkIso.val_apply`), does not act on the containers.

## Results (the answer to the work package question (5))

For every `LinkedChain D` (a Frobenius-picture of theaters with log-shell compatible Kummer
identifications):

* `kummerVolCompat`, `volCompat`: the Kummer identifications preserve log-volume (C11, IUT III,
  Proposition 3.9(ii)) — `shift_eq_zero_of_logShellCompat`;
* **`distortion_eq_zero`: the distortion of the transport along every Θ-link (indeed between any
  two theaters) is `0`**;
* **`wallOn_thetaRow_iff`: the wall along the Θ-links is the Scholze–Stix inequality**
  `SSIneq D`, and so is the wall for all pairs (`wall3_iff`);
* `answer`: the value-group portion of each Θ-link rescales the pilot degree by `s`
  (`s·|log q| ↦ |log q|`), the unit portion is identified, the distortion is `0`, and the wall
  along the Θ-links is `SSIneq D`.

The examples: the chain built from `D` with identity Kummer identifications (`ofData`) is P18's
`HodgeTheater.chainModel` (`toModel_ofData`, `rfl`); the chain with alternating identifications
`1`, `x ↦ −x` (`negChain`) has **non-ring (alien) transports along every Θ-link**
(`negChain_alien`) and still distortion `0` and wall `SSIneq D`. The M3 example with drift,
`Wall.chainModel D k` (Kummer identifications `q^{−k·n}`, distortion `k·|log q|` per link, wall
`(s − 1 − k)·|log q| ≤ log-vol(VC(I))`), is **not** log-shell compatible for `k ≠ 0`
(`not_logShellCompat_chainModel`): its Kummer identifications move value-group (`q`-power) data
into the unit portion, which a Θ-link does not do in this model.

## Scope

The output law of the algorithm is the identified-copies law (`EtaAlg.ThetaShift`, the output
`LGP·S` computed in the ring structure of the source theater; P18's `theaterAlg`). Whether the
output of an actual η-algorithm through the Θ-link has this law is not decided here (it is the
content of IUT III, Theorem 3.11 / Corollary 3.12, roadmap P20–P22). Log-shell compatibility is a
modelling condition (a hypothesis field of `LinkedChain`), argued above but not derived from an
anabelian reconstruction of the log-shells (P17, P20). Neither `SSIneq D` nor its negation is
proved.
-/

noncomputable section

namespace Iut

namespace ThetaLink

open Wall HodgeTheater NumberField
open scoped Pointwise

variable (D : InitialThetaData.{0})

/-! ### Log-shell compatible Kummer identifications -/

/-- **Log-shell compatibility** of a Kummer identification: it carries the coric log-shell
container `VC(I)` onto the log-shell container of the theater. -/
def LogShellCompat (w : Scaling D) : Prop := act D w (vcI D) = vcI D

/-- **Log-shell compatible identifications preserve log-volume** (`shift = 0`). -/
theorem shift_eq_zero_of_logShellCompat {w : Scaling D} (h : LogShellCompat D w) :
    shift D w = 0 := by
  have h' := logVol_act D w (isAdelic_vcI D)
  rw [h] at h'
  linarith

theorem logShellCompat_one : LogShellCompat D 1 := act_one D _

/-- A scaling that preserves every log-shell component is log-shell compatible. -/
theorem logShellCompat_of_comp (w : Scaling D)
    (h : ∀ (i : Fin (nC D)) (p : Nat.Primes)
      (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)),
      ((w.u i p c : (Comp D i p c)ˣ) : Comp D i p c) • vcIComp D i (.finite p) c =
        vcIComp D i (.finite p) c) :
    LogShellCompat D w := by
  funext i
  refine admissibleRegion_ext D (funext fun vQ => ?_)
  rcases vQ with p | _
  · change actMap D w i p '' (LocalTheory.packet D.placeSect _ (.finite p)).productRegion
        (fun c => vcIComp D i (.finite p) c) =
      (LocalTheory.packet D.placeSect _ (.finite p)).productRegion
        (fun c => vcIComp D i (.finite p) c)
    ext x
    simp only [DirectSumPresentation.mem_productRegion, Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩ c
      rw [← h i p c]
      exact ⟨y c, hy c, rfl⟩
    · intro hx
      have hx' : ∀ c, ∃ y ∈ vcIComp D i (.finite p) c,
          ((w.u i p c : (Comp D i p c)ˣ) : Comp D i p c) • y = x c := by
        intro c
        have := hx c
        rw [← h i p c] at this
        exact this
      choose y hy hxy using hx'
      exact ⟨y, hy, funext hxy⟩
  · rfl

/-- `(−1)·M = M` for an additive subgroup-closed set given by a submodule. -/
lemma neg_one_smul_submodule {R T : Type*} [CommRing R] [Ring T] [Module R T]
    (M : Submodule R T) : (-1 : T) • (M : Set T) = M := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [smul_eq_mul, neg_one_mul]
    exact M.neg_mem hy
  · intro hx
    exact ⟨-x, M.neg_mem hx, by rw [smul_eq_mul, neg_one_mul, neg_neg]⟩

/-- **`x ↦ −x` at the bad primes is log-shell compatible** (the log-shells are `ℤ_p`-modules). -/
theorem logShellCompat_negScale : LogShellCompat D (negScale D) := by
  refine logShellCompat_of_comp D _ fun i p c => ?_
  change ((if (p : ℕ) ∈ D.badChars then (-1 : (Comp D i p c)ˣ) else 1 : (Comp D i p c)ˣ) :
    Comp D i p c) • (LocalConstruct.tensorLogShell p _ : Set _) =
      LocalConstruct.tensorLogShell p _
  split_ifs
  · rw [Units.val_neg, Units.val_one]
    exact neg_one_smul_submodule _
  · rw [Units.val_one, one_smul]

/-- **Identifications by nonzero powers of the `q`-scaling are not log-shell compatible.** -/
theorem not_logShellCompat_qScale_zpow {m : ℤ} (hm : m ≠ 0) :
    ¬ LogShellCompat D (qScale D ^ m) := fun h => by
  have h0 := shift_eq_zero_of_logShellCompat D h
  rw [shift_zpow, shift_qScale] at h0
  have hq := (Wall.absLogQ_pos D).ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  simp only [mul_neg, neg_eq_zero, mul_eq_zero] at h0
  tauto

/-! ### Θ-linked chains of Hodge theaters -/

/-- **A Θ-linked chain of Hodge theaters with log-shell compatible Kummer identifications**: a
Frobenius-picture (theaters `n ↦ ⁿHT`, Θ-links `ⁿHT → ⁿ⁺¹HT`) and, for each theater, the Kummer
identification of its log-shell container with the coric one. -/
structure LinkedChain where
  /-- The Frobenius-picture. -/
  pic : FrobeniusPicture D
  /-- The Kummer identifications. -/
  kum : ℤ → Scaling D
  /-- They are log-shell compatible (see the module docstring). -/
  logShell : ∀ n, LogShellCompat D (kum n)

namespace LinkedChain

variable {D} (C : LinkedChain D)

/-- **The multi-container model of the chain**: P18's η-algorithm over the theaters
(`HodgeTheater.theaterAlg`), with the chain's Kummer identifications. -/
def toModel : MultiContainer D := ⟨theaterAlg D C.pic.H, C.kum⟩

/-- The BPS-level Θ-link of the wall along the Θ-link `n → n + 1` of the chain. -/
def wallLink (n : ℤ) :
    BPS.Iso ((theaterAlg D C.pic.H).thetaBPS n) ((theaterAlg D C.pic.H).qBPS (n + 1)) :=
  ThetaLinkIso.toWallLink C.pic.H (C.pic.link n)

/-- **(C11) holds**: every Kummer identification preserves log-volume. -/
theorem kummerVolCompat : C.toModel.KummerVolCompat := fun n =>
  shift_eq_zero_of_logShellCompat D (C.logShell n)

theorem volCompat : C.toModel.VolCompat :=
  C.toModel.volCompat_of_kummerVolCompat C.kummerVolCompat

/-- **The distortion of the transport is `0`** (along every Θ-link, and between any two
theaters). -/
theorem distortion_eq_zero (m n : ℤ) : C.toModel.distortion m n = 0 :=
  C.toModel.distortion_eq_zero_of_volCompat C.volCompat m n

/-- **The wall along the Θ-links of the chain is the Scholze–Stix inequality.** -/
theorem wallOn_thetaRow_iff : C.toModel.WallOn thetaRow ↔ SSIneq D :=
  C.toModel.wallOn_iff_ss_of_volCompat (theaterAlg_thetaShift D C.pic.H) C.volCompat
    ⟨(0 : ℤ), (1 : ℤ), (zero_add 1).symm⟩

/-- The wall for all pairs is the Scholze–Stix inequality as well. -/
theorem wall3_iff : C.toModel.Wall3 ↔ SSIneq D :=
  C.toModel.wallOn_iff_ss_of_volCompat (theaterAlg_thetaShift D C.pic.H) C.volCompat
    ⟨(0 : ℤ), (0 : ℤ), trivial⟩

/-- **The answer to (5)**: along the Θ-link `n → n + 1`, the value-group portion sends the pilot
of degree `s·|log q|` to the pilot `|log q|` (rescaling by `s`), the unit portion is an
isomorphism of the `F^{⊢×μ}`-prime-strips (and every such isomorphism occurs), the transport of
containers has distortion `0`, and the wall along the Θ-links is the Scholze–Stix inequality. -/
theorem answer (n : ℤ) :
    (degTheta D.bpsDegrees D.wallS_ne_zero (gauStrip D (C.pic.H n)).pilot =
        D.wallS * D.qPilot.absLogQ ∧
      ThetaLinkIso.qCoord ((C.pic.link n).val.toLinearEquiv (gauStrip D (C.pic.H n)).pilot) =
        D.qPilot.absLogQ) ∧
    Function.Surjective
      (ThetaLinkIso.dLink : ThetaLinkIso D (C.pic.H n) (C.pic.H (n + 1)) → _) ∧
    C.toModel.distortion n (n + 1) = 0 ∧
    (C.toModel.WallOn thetaRow ↔ SSIneq D) :=
  ⟨ThetaLinkIso.pilot_degrees (C.pic.link n), ThetaLinkIso.dLink_surjective,
    C.distortion_eq_zero n (n + 1), C.wallOn_thetaRow_iff⟩

end LinkedChain

/-! ### Examples -/

/-- **The chain built from `D`** with the identity Kummer identifications. -/
def LinkedChain.ofData : LinkedChain D :=
  ⟨FrobeniusPicture.ofData D, fun _ => 1, fun _ => logShellCompat_one D⟩

/-- Its model is P18's `HodgeTheater.chainModel`. -/
theorem LinkedChain.toModel_ofData : (LinkedChain.ofData D).toModel = HodgeTheater.chainModel D :=
  rfl

open scoped Classical in
/-- **The chain with alternating Kummer identifications** `1`, `x ↦ −x` (at the bad primes). -/
def LinkedChain.negChain : LinkedChain D :=
  ⟨FrobeniusPicture.ofData D, fun n => if Even n then 1 else negScale D, fun n => by
    split_ifs
    · exact logShellCompat_one D
    · exact logShellCompat_negScale D⟩

/-- **Its transports along the Θ-links are not ring isomorphisms** (alien ring structures on the
two sides, (C10)), yet its distortion is `0` and its wall is the Scholze–Stix inequality
(`LinkedChain.distortion_eq_zero`, `LinkedChain.wallOn_thetaRow_iff`). -/
theorem LinkedChain.negChain_alien (n : ℤ) :
    ¬ (LinkedChain.negChain D).toModel.IsRingTransport n (n + 1) := by
  rw [MultiContainer.isRingTransport_iff]
  change (if Even n then 1 else negScale D) ≠ (if Even (n + 1) then 1 else negScale D)
  have hne := (negScale_ne_one D)
  rcases Int.even_or_odd n with h | h
  · rw [if_pos h, if_neg (Int.not_even_iff_odd.mpr (Even.add_one h))]
    exact hne.symm
  · rw [if_neg (Int.not_even_iff_odd.mpr h), if_pos (Odd.add_one h)]
    exact hne

/-- **The drifting M3 rows are not log-shell compatible**: for `k ≠ 0`, the Kummer
identification `q^{−k}` of the theater `1` of `Wall.chainModel D k` does not preserve the
log-shell container, so no `LinkedChain` has these Kummer identifications. -/
theorem not_logShellCompat_chainModel {k : ℤ} (hk : k ≠ 0) :
    ¬ LogShellCompat D ((Wall.chainModel D k).kum (1 : ℤ)) := by
  rw [Wall.chainModel_kum]
  exact not_logShellCompat_qScale_zpow D (by simpa using hk)

theorem LinkedChain.kum_ne_chainModel {k : ℤ} (hk : k ≠ 0) (C : LinkedChain D) :
    C.kum ≠ fun n => (Wall.chainModel D k).kum n := fun h =>
  not_logShellCompat_chainModel D hk (by rw [← congrFun h 1]; exact C.logShell 1)

end ThetaLink

end Iut
