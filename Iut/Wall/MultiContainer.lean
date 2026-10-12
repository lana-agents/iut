/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Wall.Scaling

/-!
# The multi-container model of the wall (the wall, Milestone 3, part 2)

Milestone 2 found that the BPS model has one container, one ring structure and one log-volume,
so that the constraints of IUT III about distinct ring structures cannot act on the output, and
listed the extra structure that is needed (`Iut/Wall/README.md`, M2, "Extra structure needed").
This file builds that structure.

## The model `MultiContainer D`

* An η-algorithm `alg : EtaAlg D` (Milestone 1) with its Hodge theaters `HT = alg.Side`; the
  étale-unit BPSs and the BPS-level Θ-links are those of `alg` (**coric data**, shared).
* For every Hodge theater `h`, **its own container** `VCh h` with **its own log-volume**
  `vol h`, and its own `q`-pilot region `qRegionAt h`. Instantiated concretely: every `h` carries
  a copy of the concrete container of `D` (the arithmetic holomorphic structure of `h` is a copy
  of that of `D`: IUT I, the Hodge theaters are isomorphs of one another), with its native
  procession-normalized log-volume (IUT III, Proposition 3.9(i)) and its native `q`-pilot region
  `{q_v O_v}` (IUT III, Corollary 3.12, Step (xi-a); [LANA], §8.1(a)).
* The **coric container** `Coric`: a copy of the container on which the étale-like
  (mono-analytic) log-shells live ([LANA], §5.1(d), type (ME); IUT III, Proposition 3.9(ii)).
* **Kummer isomorphisms** `kummer h : Coric → VCh h` (field `kum h : Scaling D`): the image under
  `x ↦ u_h·x` on every tensor component. They are mono-analytic (additive and topological,
  `kummerAddEquiv`, `continuous_kummer`), and are ring isomorphisms only for `u_h = 1`. Each
  Hodge theater thus induces a ring structure `x *_h y = u_h·x·y` on the common coric additive
  group (`ringAt`, `kummer_ringAt`), and two Hodge theaters induce the same one iff their
  Kummer isomorphisms agree (`ringAt_eq_iff`). The data of `h` is exactly its identification of
  the coric log-shells with its own (the modelling choice of the roadmap for Milestone 3).
* The **Θ-link transport** `transport h₁ h₂ = kummer h₂ ∘ kummer h₁⁻¹ : VCh h₁ → VCh h₂`,
  determined by the coric data via the Kummer isomorphisms ([LANA], §8.1(d): "under the Θ-link,
  the unit group portions … are identified"; IUT III, Corollary 3.12, Step (xi-b): the output
  possibilities in `0,◦U ≅ 1,◦U`). It is a mono-analytic isomorphism; it is a ring isomorphism
  iff `kum h₁ = kum h₂` (`isRingTransport_iff`).

## The wall in the model

`WallOn L`: for every pair `(h₁, h₂)` in the relation `L` and every BPS-level Θ-link, the output
of the η-algorithm through `h₁` (a region of `VCh h₁`), **transported** to `VCh h₂`, has the
log-volume of the `q`-pilot region of `h₂`:
`vol h₂ (transport h₁ h₂ (out ι S)) = vol h₂ (qRegionAt h₂)`
(equivalently, the classes agree in `R_ss` of `h₂`, `wallOn_iff_rss`). `Wall3 := WallOn ⊤`
(all pairs, as `Iut.Wall` of Milestone 1).

## Results

* `logVol_transport`: `vol h₂ (transport h₁ h₂ U) = vol h₁ U + distortion h₁ h₂` with the
  **volume distortion** `distortion h₁ h₂ = shift(u_{h₂}) − shift(u_{h₁})` (a cocycle:
  `distortion_self`, `distortion_swap`, `distortion_trans`).
* `wallOn_iff_of_shift`, **`wallOn_iff_of_thetaShift`**: if the outputs have the
  identified-copies log-volumes `−s·|log(q)| + log-vol(S)` (`ThetaShift`), then
  `WallOn L ↔ ∀ L h₁ h₂, (s − 1)·|log(q)| − distortion h₁ h₂ ≤ log-vol(VC(I))`.
* `VolCompat` (all Kummer isomorphisms shift log-volume equally, i.e. every transport preserves
  log-volume; IUT III, Proposition 3.9(ii), (iv)): then `Wall3 ↔ Wall D alg`
  (`wall3_iff_wall_of_volCompat`), and with `ThetaShift` the wall is the Scholze–Stix inequality
  `SSIneq D` (`wallOn_iff_ss_of_volCompat`). Ring transports have zero distortion
  (`distortion_eq_zero_of_isRingTransport`).
* Whenever the wall is required for a pair in both directions (in particular for `Wall3`, which
  contains the diagonal pairs with identity transport), `ThetaShift` gives `SSIneq D`
  (`ss_of_wallOn_pair`, `ss_of_wall3`); precisely,
  `Wall3 ↔ ∀ h₁ h₂, (s − 1)·|log(q)| + |distortion h₁ h₂| ≤ log-vol(VC(I))`
  (`wall3_iff_of_thetaShift`).
* **`variant_of_wall` lifts**: `variant_of_wall3 : Wall3 → Corollary312Variant` for every model;
  for a relation `L`, `variant_of_wallOn` (with `TransportRealisation`: the transported outputs
  lie in the hull of a single (Ind1)-image of the theta-pilot region of `h₂`, IUT III, Step
  (xi-b), (xi-d): "contained in `1,◦U`") and `variant_of_wallOn_of_volCompat`.
* **Consistency**: `ofAlg A` (all Kummer isomorphisms the identity) is a model with
  `Wall3 (ofAlg A) ↔ Wall D A` (`wall3_ofAlg_iff`), and `variant_of_wall` factors through it
  (`variant_of_wall_eq_via_wall3`). The identified-copies model is `idModel D σ :=
  ofAlg (idAlgOn D σ)`: one container up to the identity transport, `μ_{h₁} = μ_{h₂}`
  (`transport_idModel`), and `Wall3 (idModel D σ) ↔ SSIneq D` (`wall3_idModel_iff`).
-/

namespace Iut

namespace Wall

/-- **The Scholze–Stix inequality** `(s − 1)·|log(q)| ≤ log-vol(VC(I))` (Milestone 1,
`wall_idAlg_iff`). Neither it nor its negation is proved in this repository. -/
def SSIneq (D : InitialThetaData.{0}) : Prop :=
  (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (vcI D)

/-- **The identified-copies log-volumes** (Milestone 2, (C9)): every output has log-volume
`−s·|log(q)| + log-vol(S)`, the log-volume of `LGP·S` computed in the ring structure of the
Hodge theater through which the algorithm runs. -/
def EtaAlg.ThetaShift {D : InitialThetaData.{0}} (A : EtaAlg D) : Prop :=
  ∀ {B : A.BPSA} {h : A.Side} (ι : A.Choice B h) (S : Ind3 D),
    logVol D (A.out ι S) = -(sFactor (nC D) * D.qPilot.absLogQ) + logVol D S.1

variable (D : InitialThetaData.{0})

/-- **The multi-container model** (see the module docstring): an η-algorithm together with, for
each Hodge theater `h`, the Kummer isomorphism `kum h` identifying the coric log-shell container
with the container of `h`. -/
structure MultiContainer where
  /-- The η-algorithm, with its Hodge theaters and coric étale-unit data. -/
  alg : EtaAlg D
  /-- The Kummer isomorphism of the Hodge theater `h` (a mono-analytic scaling). -/
  kum : alg.Side → Scaling D

namespace MultiContainer

variable {D} (M : MultiContainer D)

/-- The Hodge theaters. -/
abbrev HT : Type := M.alg.Side

/-- **The container `VC_h` of the Hodge theater `h`**: a copy of the concrete container of `D`. -/
abbrev VCh (_h : M.HT) : Type := Region D

/-- **The coric container** (étale-like mono-analytic log-shells): a copy of the container. -/
abbrev Coric (_M : MultiContainer D) : Type := Region D

/-- **The log-volume `μ_h` of `VC_h`**: the native procession-normalized log-volume. -/
noncomputable def vol (h : M.HT) (U : M.VCh h) : ℝ := logVol D U

/-- **The `q`-pilot region of `h`**, in the native ring structure of `h`. -/
noncomputable def qRegionAt (h : M.HT) : M.VCh h := qRegion D

theorem vol_qRegionAt (h : M.HT) :
    M.vol h (M.qRegionAt h) = (concreteVariantData D).qPilot.lhs :=
  logVol_qRegion D

/-- **The Kummer isomorphism `κ_h : Coric → VC_h`.** -/
noncomputable def kummer (h : M.HT) : M.Coric → M.VCh h := act D (M.kum h)

/-- Its inverse. -/
noncomputable def kummerInv (h : M.HT) : M.VCh h → M.Coric := act D (M.kum h)⁻¹

theorem kummerInv_kummer (h : M.HT) (U : M.Coric) : M.kummerInv h (M.kummer h U) = U := by
  unfold kummer kummerInv
  exact act_inv_act D _ U

theorem kummer_kummerInv (h : M.HT) (U : M.VCh h) : M.kummer h (M.kummerInv h U) = U := by
  unfold kummer kummerInv
  exact act_act_inv D _ U

/-- **The ring structure of `h` on the coric component** `(i, p, c)`: `x *_h y = u_h·x·y`. -/
noncomputable def ringAt (h : M.HT) (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    Comp D i p c → Comp D i p c → Comp D i p c :=
  kmul ((M.kum h).u i p c)

/-- The Kummer isomorphism of `h` carries `*_h` to the ring structure of the copy. -/
theorem kummer_ringAt (h : M.HT) (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p))
    (x y : Comp D i p c) :
    ((M.kum h).u i p c : Comp D i p c) * M.ringAt h i p c x y =
      (((M.kum h).u i p c : Comp D i p c) * x) * (((M.kum h).u i p c : Comp D i p c) * y) :=
  kummer_kmul _ x y

/-- **Two Hodge theaters induce the same ring structures on the coric data iff their Kummer
isomorphisms agree.** -/
theorem ringAt_eq_iff (h₁ h₂ : M.HT) : M.ringAt h₁ = M.ringAt h₂ ↔ M.kum h₁ = M.kum h₂ := by
  constructor
  · intro h
    ext i p c : 4
    exact (kmul_eq_iff _ _).mp (congrFun (congrFun (congrFun h i) p) c)
  · intro h
    unfold ringAt
    rw [h]

/-! ### The Θ-link transport -/

/-- **The Θ-link transport** `VC_{h₁} → VC_{h₂}`, `κ_{h₂} ∘ κ_{h₁}⁻¹`. -/
noncomputable def transport (h₁ h₂ : M.HT) : M.VCh h₁ → M.VCh h₂ :=
  act D (M.kum h₂ * (M.kum h₁)⁻¹)

/-- The transport is determined by the coric data via the Kummer isomorphisms. -/
theorem transport_eq (h₁ h₂ : M.HT) (U : M.VCh h₁) :
    M.transport h₁ h₂ U = M.kummer h₂ (M.kummerInv h₁ U) := by
  unfold transport kummer kummerInv
  exact act_mul D _ _ U

theorem transport_self (h : M.HT) (U : M.VCh h) : M.transport h h U = U := by
  rw [transport, mul_inv_cancel, act_one]

theorem transport_trans (h₁ h₂ h₃ : M.HT) (U : M.VCh h₁) :
    M.transport h₂ h₃ (M.transport h₁ h₂ U) = M.transport h₁ h₃ U := by
  rw [transport, transport, transport, ← act_mul]
  congr 1
  group

theorem isAdelic_transport (h₁ h₂ : M.HT) {U : M.VCh h₁} (hU : IsAdelic D U) :
    IsAdelic D (M.transport h₁ h₂ U) :=
  isAdelic_act D _ hU

/-- The unit by which the transport acts on the component `(i, p, c)`. -/
noncomputable def transportUnit (h₁ h₂ : M.HT) (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    (Comp D i p c)ˣ :=
  (M.kum h₂ * (M.kum h₁)⁻¹).u i p c

/-- **The transport is mono-analytic**: on every component it is the additive homeomorphism
`kummerAddEquiv (transportUnit h₁ h₂ i p c)`. -/
theorem transport_mono_analytic (h₁ h₂ : M.HT) (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    Continuous (kummerAddEquiv (M.transportUnit h₁ h₂ i p c)) ∧
      Continuous (kummerAddEquiv (M.transportUnit h₁ h₂ i p c)).symm :=
  ⟨continuous_kummer _, continuous_kummer_symm _⟩

/-- **The transport is a ring isomorphism** (on every component). -/
def IsRingTransport (h₁ h₂ : M.HT) : Prop :=
  ∀ (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p))
    (x y : Comp D i p c),
    (M.transportUnit h₁ h₂ i p c : Comp D i p c) * (x * y) =
      ((M.transportUnit h₁ h₂ i p c : Comp D i p c) * x) *
        ((M.transportUnit h₁ h₂ i p c : Comp D i p c) * y)

/-- **The transport is a ring isomorphism iff the two Kummer isomorphisms agree**, in which case
it is the identity. -/
theorem isRingTransport_iff (h₁ h₂ : M.HT) : M.IsRingTransport h₁ h₂ ↔ M.kum h₁ = M.kum h₂ := by
  have key : M.IsRingTransport h₁ h₂ ↔ M.kum h₂ * (M.kum h₁)⁻¹ = 1 := by
    constructor
    · intro h
      ext i p c : 4
      exact (units_mul_hom_iff _).mp (h i p c)
    · intro h i p c
      refine (units_mul_hom_iff _).mpr ?_
      change (M.kum h₂ * (M.kum h₁)⁻¹).u i p c = 1
      rw [h]
      rfl
  rw [key, mul_inv_eq_one, eq_comm]

/-! ### Volume distortion -/

/-- **The volume distortion of the transport** `h₁ → h₂`. -/
noncomputable def distortion (h₁ h₂ : M.HT) : ℝ := shift D (M.kum h₂) - shift D (M.kum h₁)

/-- **The transport shifts log-volumes by the distortion**:
`μ_{h₂}(transport U) = μ_{h₁}(U) + distortion h₁ h₂`. -/
theorem logVol_transport (h₁ h₂ : M.HT) {U : M.VCh h₁} (hU : IsAdelic D U) :
    M.vol h₂ (M.transport h₁ h₂ U) = M.vol h₁ U + M.distortion h₁ h₂ := by
  unfold vol transport distortion
  rw [logVol_act D _ hU, shift_mul, shift_inv]
  ring

theorem distortion_self (h : M.HT) : M.distortion h h = 0 := sub_self _

theorem distortion_swap (h₁ h₂ : M.HT) : M.distortion h₂ h₁ = -M.distortion h₁ h₂ := by
  unfold distortion
  ring

theorem distortion_trans (h₁ h₂ h₃ : M.HT) :
    M.distortion h₁ h₂ + M.distortion h₂ h₃ = M.distortion h₁ h₃ := by
  unfold distortion
  ring

/-- **Ring transports do not distort volume.** -/
theorem distortion_eq_zero_of_isRingTransport {h₁ h₂ : M.HT} (h : M.IsRingTransport h₁ h₂) :
    M.distortion h₁ h₂ = 0 := by
  rw [distortion, (M.isRingTransport_iff h₁ h₂).mp h, sub_self]

/-- **Volume compatibility** (IUT III, Proposition 3.9(ii), (iv); Corollary 3.12, Step (x)):
all Kummer isomorphisms shift log-volume by the same amount, i.e. every transport preserves
log-volume. -/
def VolCompat : Prop := ∀ h₁ h₂ : M.HT, shift D (M.kum h₁) = shift D (M.kum h₂)

/-- **Volume compatibility of each Kummer isomorphism** with the coric log-volume (IUT III,
Proposition 3.9(ii)): `shift(u_h) = 0`. It implies `VolCompat`. -/
def KummerVolCompat : Prop := ∀ h : M.HT, shift D (M.kum h) = 0

theorem volCompat_of_kummerVolCompat (hK : M.KummerVolCompat) : M.VolCompat := fun h₁ h₂ => by
  rw [hK h₁, hK h₂]

theorem distortion_eq_zero_of_volCompat (hV : M.VolCompat) (h₁ h₂ : M.HT) :
    M.distortion h₁ h₂ = 0 := by
  rw [distortion, hV h₂ h₁, sub_self]

/-! ### The wall in the multi-container model -/

/-- **The wall along a relation `L` of Hodge theaters**: for each pair `L h₁ h₂` and each Θ-link,
some output through `h₁`, transported to `VC_{h₂}`, has the log-volume of the `q`-pilot region of
`h₂`. -/
def WallOn (L : M.HT → M.HT → Prop) : Prop :=
  ∀ h₁ h₂ : M.HT, L h₁ h₂ → ∀ _gl : BPS.Iso (M.alg.thetaBPS h₁) (M.alg.qBPS h₂),
    ∃ (ι : M.alg.Choice (M.alg.qBPS h₂) h₁) (S : Ind3 D),
      M.vol h₂ (M.transport h₁ h₂ (M.alg.out ι S)) = M.vol h₂ (M.qRegionAt h₂)

/-- **The wall in the multi-container model, for all pairs** (as `Iut.Wall`). -/
def Wall3 : Prop := M.WallOn fun _ _ => True

/-- **The wall in `R_ss` form**: the classes of the transported output and of the `q`-pilot
region of `h₂` agree. -/
theorem wallOn_iff_rss (L : M.HT → M.HT → Prop) :
    M.WallOn L ↔ ∀ h₁ h₂ : M.HT, L h₁ h₂ → ∀ _gl : BPS.Iso (M.alg.thetaBPS h₁) (M.alg.qBPS h₂),
      ∃ (ι : M.alg.Choice (M.alg.qBPS h₂) h₁) (S : Ind3 D),
        Rss.mk D (M.transport h₁ h₂ (M.alg.out ι S))
            (M.isAdelic_transport h₁ h₂ (M.alg.realisation ι S).1) =
          Rss.mk D (qRegion D) (isAdelic_qRegion D) := by
  refine forall₂_congr fun h₁ h₂ => forall₂_congr fun _ _ => exists₂_congr fun ι S => ?_
  rw [Rss.mk_eq_mk_iff]
  rfl

/-- **The wall in terms of the distortion**, for outputs with the LGP law
`log-vol(out ι S) = κ_ι + log-vol(S)`. -/
theorem wallOn_iff_of_shift (L : M.HT → M.HT → Prop)
    (κ : ∀ {B : M.alg.BPSA} {h : M.HT}, M.alg.Choice B h → ℝ)
    (hκ : ∀ {B : M.alg.BPSA} {h : M.HT} (ι : M.alg.Choice B h) (S : Ind3 D),
      logVol D (M.alg.out ι S) = κ ι + logVol D S.1) :
    M.WallOn L ↔ ∀ h₁ h₂ : M.HT, L h₁ h₂ → ∃ ι : M.alg.Choice (M.alg.qBPS h₂) h₁,
      (concreteVariantData D).qPilot.lhs - κ ι - M.distortion h₁ h₂ ≤ logVol D (vcI D) := by
  constructor
  · intro hW h₁ h₂ hL
    obtain ⟨ι, S, hS⟩ := hW h₁ h₂ hL (M.alg.nonempty_thetaLink h₁ h₂).some
    refine ⟨ι, ?_⟩
    have hle := logVol_le_vcI D S
    rw [M.logVol_transport h₁ h₂ (M.alg.realisation ι S).1, vol_qRegionAt, vol, hκ] at hS
    linarith
  · intro h h₁ h₂ hL _
    obtain ⟨ι, hι⟩ := h h₁ h₂ hL
    obtain ⟨S, hS⟩ := (exists_ind3_logVol_iff D
      ((concreteVariantData D).qPilot.lhs - κ ι - M.distortion h₁ h₂)).mpr hι
    refine ⟨ι, S, ?_⟩
    rw [M.logVol_transport h₁ h₂ (M.alg.realisation ι S).1, vol_qRegionAt, vol, hκ, hS]
    ring

/-- **The wall for identified-copies log-volumes**:
`WallOn L ↔ ∀ L h₁ h₂, (s − 1)·|log(q)| − distortion h₁ h₂ ≤ log-vol(VC(I))`. -/
theorem wallOn_iff_of_thetaShift (hS : M.alg.ThetaShift) (L : M.HT → M.HT → Prop) :
    M.WallOn L ↔ ∀ h₁ h₂ : M.HT, L h₁ h₂ →
      (sFactor (nC D) - 1) * D.qPilot.absLogQ - M.distortion h₁ h₂ ≤ logVol D (vcI D) := by
  rw [M.wallOn_iff_of_shift L (fun _ => -(sFactor (nC D) * D.qPilot.absLogQ)) hS]
  have hlhs : (concreteVariantData D).qPilot.lhs = -D.qPilot.absLogQ := rfl
  refine forall₂_congr fun h₁ h₂ => forall_congr' fun _ => ?_
  rw [hlhs]
  constructor
  · rintro ⟨_, h⟩
    linarith
  · intro h
    exact ⟨(M.alg.nonempty_choice h₁ h₂).some, by linarith⟩

/-- **A pair in both directions gives the Scholze–Stix inequality**: the distortions cancel. -/
theorem ss_of_wallOn_pair (hS : M.alg.ThetaShift) {L : M.HT → M.HT → Prop} (hW : M.WallOn L)
    {h₁ h₂ : M.HT} (h12 : L h₁ h₂) (h21 : L h₂ h₁) : SSIneq D := by
  have hw := (M.wallOn_iff_of_thetaShift hS L).mp hW
  have a := hw h₁ h₂ h12
  have b := hw h₂ h₁ h21
  rw [distortion_swap] at b
  unfold SSIneq
  linarith

/-- **`Wall3` implies the Scholze–Stix inequality** (the diagonal pairs have identity
transport). -/
theorem ss_of_wall3 (hS : M.alg.ThetaShift) (hW : M.Wall3) : SSIneq D := by
  obtain ⟨h⟩ := M.alg.side_nonempty
  exact M.ss_of_wallOn_pair hS hW (h₁ := h) (h₂ := h) trivial trivial

/-- **`Wall3` for identified-copies log-volumes**:
`∀ h₁ h₂, (s − 1)·|log(q)| + |distortion h₁ h₂| ≤ log-vol(VC(I))`. -/
theorem wall3_iff_of_thetaShift (hS : M.alg.ThetaShift) :
    M.Wall3 ↔ ∀ h₁ h₂ : M.HT,
      (sFactor (nC D) - 1) * D.qPilot.absLogQ + |M.distortion h₁ h₂| ≤ logVol D (vcI D) := by
  rw [Wall3, M.wallOn_iff_of_thetaShift hS]
  constructor
  · intro h h₁ h₂
    have a := h h₁ h₂ trivial
    have b := h h₂ h₁ trivial
    rw [distortion_swap] at b
    rcases abs_cases (M.distortion h₁ h₂) with ⟨hc, _⟩ | ⟨hc, _⟩ <;> linarith
  · intro h h₁ h₂ _
    have := neg_abs_le (M.distortion h₁ h₂)
    linarith [h h₁ h₂]

/-- **Under volume compatibility the transport is invisible to the wall**: `Wall3 M` is the
wall of Milestone 1 for the algorithm. -/
theorem wall3_iff_wall_of_volCompat (hV : M.VolCompat) : M.Wall3 ↔ Wall D M.alg := by
  refine forall₂_congr fun h₁ h₂ => ?_
  refine ⟨fun h gl => ?_, fun h _ gl => ?_⟩
  · obtain ⟨ι, S, hS⟩ := h trivial gl
    refine ⟨ι, S, (M.alg.etaAnab_eq_etaQ_iff ι S).mpr ?_⟩
    rw [M.logVol_transport h₁ h₂ (M.alg.realisation ι S).1,
      M.distortion_eq_zero_of_volCompat hV, add_zero, vol_qRegionAt] at hS
    exact hS
  · obtain ⟨ι, S, hS⟩ := h gl
    refine ⟨ι, S, ?_⟩
    rw [M.logVol_transport h₁ h₂ (M.alg.realisation ι S).1,
      M.distortion_eq_zero_of_volCompat hV, add_zero, vol_qRegionAt]
    exact (M.alg.etaAnab_eq_etaQ_iff ι S).mp hS

/-- **Under volume compatibility and identified-copies log-volumes, the wall along any nonempty
relation is the Scholze–Stix inequality**, whatever the (mono-analytic, possibly non-ring)
transports are. -/
theorem wallOn_iff_ss_of_volCompat (hS : M.alg.ThetaShift) (hV : M.VolCompat)
    {L : M.HT → M.HT → Prop} (hL : ∃ h₁ h₂, L h₁ h₂) : M.WallOn L ↔ SSIneq D := by
  rw [M.wallOn_iff_of_thetaShift hS]
  simp only [M.distortion_eq_zero_of_volCompat hV, sub_zero]
  obtain ⟨a, b, hab⟩ := hL
  exact ⟨fun h => h a b hab, fun h _ _ _ => h⟩

/-! ### The Corollary 3.12 variant from the wall -/

/-- **`variant_of_wall` lifts**: in every multi-container model, `Wall3` implies the variant
(through a diagonal pair, whose transport is the identity). -/
theorem variant_of_wall3 (hW : M.Wall3) : Corollary312Variant (concreteVariantData D) := by
  obtain ⟨h⟩ := M.alg.side_nonempty
  obtain ⟨ι, S, hS⟩ := hW h h trivial (M.alg.nonempty_thetaLink h h).some
  rw [transport_self, vol_qRegionAt] at hS
  exact (corollary312Variant_iff _).mpr
    (hS ▸ logVol_le_rhs D (M.alg.realisation ι S).1 (M.alg.realisation ι S).2)

/-- **Realisation in the target container** (IUT III, Corollary 3.12, Step (xi-b), (xi-d): the
output possibilities, transported, are contained in the hull `1,◦U` of the `1`-column): every
transported output lies in the hull of a single (Ind1)-image of the theta-pilot region of
`h₂`. A hypothesis, not a field. -/
def TransportRealisation : Prop :=
  ∀ (h₁ h₂ : M.HT) (ι : M.alg.Choice (M.alg.qBPS h₂) h₁) (S : Ind3 D),
    InHullOfImage D (M.transport h₁ h₂ (M.alg.out ι S))

/-- **The wall along a nonempty relation, with realisation in the target container, implies the
variant**, whatever the distortion. -/
theorem variant_of_wallOn (hR : M.TransportRealisation) {L : M.HT → M.HT → Prop}
    (hL : ∃ h₁ h₂, L h₁ h₂) (hW : M.WallOn L) : Corollary312Variant (concreteVariantData D) := by
  obtain ⟨h₁, h₂, hl⟩ := hL
  obtain ⟨ι, S, hS⟩ := hW h₁ h₂ hl (M.alg.nonempty_thetaLink h₁ h₂).some
  rw [vol_qRegionAt] at hS
  exact (corollary312Variant_iff _).mpr
    (hS ▸ logVol_le_rhs D (M.isAdelic_transport h₁ h₂ (M.alg.realisation ι S).1) (hR h₁ h₂ ι S))

/-- **The wall along a nonempty relation, under volume compatibility, implies the variant.** -/
theorem variant_of_wallOn_of_volCompat (hV : M.VolCompat) {L : M.HT → M.HT → Prop}
    (hL : ∃ h₁ h₂, L h₁ h₂) (hW : M.WallOn L) : Corollary312Variant (concreteVariantData D) := by
  obtain ⟨h₁, h₂, hl⟩ := hL
  obtain ⟨ι, S, hS⟩ := hW h₁ h₂ hl (M.alg.nonempty_thetaLink h₁ h₂).some
  rw [M.logVol_transport h₁ h₂ (M.alg.realisation ι S).1,
    M.distortion_eq_zero_of_volCompat hV, add_zero, vol_qRegionAt] at hS
  exact (corollary312Variant_iff _).mpr
    (hS ▸ logVol_le_rhs D (M.alg.realisation ι S).1 (M.alg.realisation ι S).2)

end MultiContainer

/-! ### Consistency: the identified-copies model is an instance -/

/-- **An η-algorithm as a multi-container model**: every Kummer isomorphism is the identity. -/
noncomputable def MultiContainer.ofAlg {D : InitialThetaData.{0}} (A : EtaAlg D) :
    MultiContainer D :=
  ⟨A, fun _ => 1⟩

namespace MultiContainer

variable {D}

theorem transport_ofAlg (A : EtaAlg D) (h₁ h₂ : A.Side) (U : Region D) :
    (ofAlg A).transport h₁ h₂ U = U := by
  change act D (1 * 1⁻¹) U = U
  rw [mul_inv_cancel, act_one]

theorem ofAlg_volCompat (A : EtaAlg D) : (ofAlg A).VolCompat := fun _ _ => rfl

theorem ofAlg_isRingTransport (A : EtaAlg D) (h₁ h₂ : A.Side) :
    (ofAlg A).IsRingTransport h₁ h₂ :=
  ((ofAlg A).isRingTransport_iff h₁ h₂).mpr rfl

/-- **Consistency with Milestone 1**: `Wall3 (ofAlg A) ↔ Wall D A`. -/
theorem wall3_ofAlg_iff (A : EtaAlg D) : (ofAlg A).Wall3 ↔ Wall D A :=
  (ofAlg A).wall3_iff_wall_of_volCompat (ofAlg_volCompat A)

/-- **`variant_of_wall` factors through the multi-container model.** -/
theorem variant_of_wall_eq_via_wall3 (A : EtaAlg D) (hW : Wall D A) :
    variant_of_wall A hW = (ofAlg A).variant_of_wall3 ((wall3_ofAlg_iff A).mpr hW) :=
  rfl

end MultiContainer

/-- **The identified-copies model** with Hodge theaters `σ`: the identified-copies algorithm
`idAlgOn D σ`, every Kummer isomorphism the identity — one container up to the identity
transport, `μ_{h₁} = μ_{h₂}`. -/
noncomputable def idModel (σ : Type) [Nonempty σ] : MultiContainer D :=
  MultiContainer.ofAlg (idAlgOn D σ)

variable (σ : Type) [Nonempty σ]

theorem transport_idModel (h₁ h₂ : σ) (U : Region D) :
    (idModel D σ).transport h₁ h₂ U = U :=
  MultiContainer.transport_ofAlg (idAlgOn D σ) h₁ h₂ U

/-- The identified-copies algorithm has the identified-copies log-volumes. -/
theorem idAlgOn_thetaShift : (idAlgOn D σ).ThetaShift := fun _ S => by
  change logVol D (lgp D S.1) = _
  rw [logVol_lgp D S.2.1, logVol_lgp_integral]

/-- **The wall of the identified-copies model in the multi-container form is the Scholze–Stix
inequality** (consistent with `wall_idAlgOn_iff`). -/
theorem wall3_idModel_iff : (idModel D σ).Wall3 ↔ SSIneq D :=
  ((idModel D σ).wall3_iff_wall_of_volCompat (MultiContainer.ofAlg_volCompat _)).trans
    (wall_idAlgOn_iff D σ)

end Wall

end Iut
