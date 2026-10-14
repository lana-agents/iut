/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Wall.QPilotRegion

/-!
# What excludes the identified-copies algorithm? (the wall, Milestone 2 (b))

Milestone 1 showed that the identified-copies algorithm `idAlg D` (Scholze–Stix; `out ι S =
LGP·S` computed in the one ring structure of `D`) satisfies every field (T1)–(T3) of `EtaAlg D`
and the LGP law (T4), and that on it the wall is exactly the Scholze–Stix inequality
`(s − 1)·|log(q)| ≤ log-vol(hull(VC(I)))` (`wall_idAlg_iff`). Here the conditions that IUT III and
the LANA interim report ([LANA]) put forward as distinguishing Mochizuki's algorithm from the
identified-copies one are formalized as **candidate** constraints on an `EtaAlg D` (each a `Prop`,
never assumed), and for each it is proved whether `idAlg` (or its variant `idAlgOn σ` with an
arbitrary nonempty type `σ` of identified Hodge theaters) satisfies or violates it. Nothing here
takes a side in the dispute: a constraint "excludes the collapse" only if it is violated by every
identified-copies algorithm whose wall is the Scholze–Stix inequality.

## The candidates

* **(C1) IPL** (`EtaAlg.IPL`; IUT III, Remark 3.11.1(iii); [LANA], §8.2, Remark 8.2.1): the
  output Θ-pilot BPS is linked to the input `q`-pilot BPS by a pilot-preserving isomorphism.
  Satisfied by **every** `EtaAlg` (`EtaAlg.ipl`): BPSs with the same product formula form a
  connected groupoid and value-group isomorphisms preserve pilots.
* **(C2) SHE, two-sided expressibility** (`EtaAlg.SHESides`; Remark 3.11.1(iii); [LANA], §8.2):
  the output is a function of the domain Hodge theater and also a function of the codomain Hodge
  theater. With opaque Hodge theaters this is **equivalent to side-independence of the output**
  (`EtaAlg.sheSides_iff`), i.e. to the shape of the identified-copies model; `idAlgOn σ` satisfies
  it (`idAlgOn_sheSides`).
* **(C3) SHE, Step (xi-e)** (`EtaAlg.SHEq`; IUT III, proof of Corollary 3.12, (xi-e), (xi-f);
  [LANA], §8.3): some output possibility has the class of the constructed `q`-pilot region
  `[qRegion D] ∈ R_ss`. It is **equivalent to the wall** (`EtaAlg.sheq_iff_wall`), and on
  `idAlg` to the Scholze–Stix inequality (`sheq_idAlg_iff`): undecided here.
* **(C4) distinct Hodge theaters** (`EtaAlg.DistinctSides`; IUT III, Theorem 3.11: "a collection
  of distinct Θ^{±ell}NF-Hodge theaters"; [LANA], §7.1(b), §8.1): violated by `idAlg`
  (`idAlg_not_distinctSides`), satisfied by `idAlgOn σ` for nontrivial `σ`
  (`idAlgOn_distinctSides`), whose wall is still the Scholze–Stix inequality
  (`wall_idAlgOn_iff`). It excludes the literal `idAlg`, not the collapse.
* **(C5) the wall only across distinct sides** (`WallDistinct`; [LANA], §7.1(b): Θ-links from
  `†HT` to `‡HT`): vacuous on `idAlg` (`wallDistinct_idAlg`); on `idAlgOn σ`, `σ` nontrivial,
  equivalent to the Scholze–Stix inequality (`wallDistinct_idAlgOn_iff`); with (C4) it still
  implies the variant (`variant_of_wallDistinct`).
* **(C6) multiradiality** (`EtaAlg.Multiradial`; IUT III, Theorem 3.11(i), the étale-picture
  permutation symmetries; [LANA], §8.1(d)): outputs computed through different Hodge theaters
  agree up to (Ind3). Satisfied by `idAlgOn σ` (`idAlgOn_multiradial`).
* **(C7) provenance as side-dependence** (`EtaAlg.SideDependent`; [LANA], §10.3): the set of
  output possibilities depends on the Hodge theater used. Violated by `idAlgOn σ`, but
  **incompatible with (C6)** (`EtaAlg.not_sideDependent_of_multiradial`).
* **(C8) dependence on the input value group** (`EtaAlg.ValDependent`; [LANA], Remark 6.2.2, the
  (SHE) reading): the output changes with the value-group portion of the input. **No** `EtaAlg`
  satisfies it (`EtaAlg.not_valDependent`): it contradicts (T2).
* **(C9) APT, negative form** (`EtaAlg.SetTransport`, APT := `¬ SetTransport`; IUT III,
  Remark 3.11.1(iv); [LANA], §8.2, §8.3): the output is *not* the image of `S` under one fixed
  set-theoretic map. Violated by `idAlgOn σ` (`idAlgOn_setTransport`). But the wall depends on the
  output only through its log-volume: **every** `EtaAlg` whose outputs have the identified-copies
  log-volumes `−s·|log(q)| + log-vol(S)` has the Scholze–Stix inequality as its wall
  (`wall_iff_ss_of_thetaShift`), whether or not it is a set-theoretic transport. APT excludes the
  collapse only if it changes these log-volumes, which needs per-side log-volumes (see (C10)).
* **(C10) mutually alien ring structures** (`HoloStructure`, `HoloStructure.Alien`; [LANA],
  §7.1(b)(c), §10.5; IUT III, Theorem 3.11): each Hodge theater carries a ring, and no ring
  isomorphism between distinct sides is compatible with a Θ-link. Every `EtaAlg` carries such a
  structure (`exists_alien`), since `out` lands in the one container of `D` and is not coupled
  to the rings.

## The extra structure the BPS model lacks (input to roadmap P15–P20)

(C4), (C5), (C9), (C10) can only exclude the collapse once `out` is **coupled** to per-side
arithmetic holomorphic structures. Concretely the interface needs: a ring (local fields
`K_v^{(h)}`) for each Hodge theater `h`, with its own container `VC_h` and log-volume `μ_h`;
Kummer isomorphisms from the coric étale-unit data to the log-shells of each side; the output of
the algorithm through `h₁` as a region of `VC_{h₁}`; the transport `VC_{h₁} → VC_{h₂}` induced by
a Θ-link on log-shells as mono-analytic (additive, topological, not ring) isomorphisms; and the
wall as the comparison `μ_{h₂}(transport(out)) = μ_{h₂}(q-pilot region of h₂)`. The
identified-copies model is the case of one container, identity transport and `μ_{h₁} = μ_{h₂}`.
Whether a different admissible transport/normalization changes the log-volume `−s·|log(q)|` of
`LGP·O` is the question the constraints above cannot decide.
-/

namespace Iut

namespace Wall

variable {D : InitialThetaData.{0}}

namespace EtaAlg

variable (A : EtaAlg D)

/-! ### (C1) IPL -/

/-- **(C1) The input prime-strip link (IPL)** (IUT III, Remark 3.11.1(iii); [LANA], §8.2): for
every run of the algorithm on the `q`-pilot BPS of `h₂` through `h₁`, the output Θ-pilot BPS of
`h₁` is linked to the input `q`-pilot BPS by an isomorphism of BPSs carrying pilot to pilot. -/
def IPL : Prop :=
  ∀ (h₁ h₂ : A.Side) (_ι : A.Choice (A.qBPS h₂) h₁) (_S : Ind3 D),
    ∃ e : BPS.Iso (A.thetaBPS h₁) (A.qBPS h₂),
      e.val.toLinearEquiv (A.thetaBPS h₁).val.pilot = (A.qBPS h₂).val.pilot

/-- **(C1) holds for every `EtaAlg`** ([LANA], Remark 8.2.1). -/
theorem ipl : A.IPL := fun _ _ ι _ => ⟨ι.symm, ValBPS.Iso.map_pilot _⟩

/-! ### (C2) SHE as two-sided expressibility -/

/-- **(C2) Simultaneous holomorphic expressibility, two-sided form** (IUT III,
Remark 3.11.1(iii); [LANA], §8.2): the output is a function of the Hodge theater in the domain of
the Θ-link and also a function of the Hodge theater in its codomain. -/
def SHESides : Prop :=
  ∃ F G : A.Side → Ind3 D → Region D, ∀ (h₁ h₂ : A.Side) (ι : A.Choice (A.qBPS h₂) h₁)
    (S : Ind3 D), A.out ι S = F h₁ S ∧ A.out ι S = G h₂ S

/-- **With opaque Hodge theaters, (C2) is side-independence**: the output on `q`-pilot inputs
depends only on `S`. -/
theorem sheSides_iff : A.SHESides ↔ ∃ g : Ind3 D → Region D, ∀ (h₁ h₂ : A.Side)
    (ι : A.Choice (A.qBPS h₂) h₁) (S : Ind3 D), A.out ι S = g S := by
  constructor
  · rintro ⟨F, G, hFG⟩
    obtain ⟨h₀⟩ := A.side_nonempty
    refine ⟨F h₀, fun h₁ h₂ ι S => ?_⟩
    obtain ⟨ι₀⟩ := A.nonempty_choice h₀ h₂
    rw [(hFG h₁ h₂ ι S).2, ← (hFG h₀ h₂ ι₀ S).2, (hFG h₀ h₂ ι₀ S).1]
  · rintro ⟨g, hg⟩
    exact ⟨fun _ => g, fun _ => g, fun h₁ h₂ ι S => ⟨hg h₁ h₂ ι S, hg h₁ h₂ ι S⟩⟩

/-! ### (C3) SHE in the form of Step (xi-e) -/

/-- **(C3) (SHE) in the form of IUT III, Corollary 3.12, Step (xi-e)**: the construction is
valid subject to the condition that the pilot log-volume of the input be `−|log(q)|`, i.e. some
output possibility has the class of the constructed `q`-pilot region in `R_ss`. -/
def SHEq : Prop :=
  ∀ h₁ h₂ : A.Side, ∃ (ι : A.Choice (A.qBPS h₂) h₁) (S : Ind3 D),
    Rss.mk D (A.out ι S) (A.realisation ι S).1 = Rss.mk D (qRegion D) (isAdelic_qRegion D)

/-- **(C3) is the wall.** -/
theorem sheq_iff_wall : A.SHEq ↔ Wall D A := by
  rw [wall_iff_forall]
  refine forall₂_congr fun h₁ h₂ => exists_congr fun ι => exists_congr fun S => ?_
  rw [Rss.mk_eq_mk_iff, etaAnab_eq_etaQ_iff, logVol_qRegion]

/-! ### (C4) distinct Hodge theaters -/

/-- **(C4) There are distinct Hodge theaters** (IUT III, Theorem 3.11; [LANA], §7.1(b)). -/
def DistinctSides : Prop := Nontrivial A.Side

/-! ### (C6), (C7) multiradiality and side-dependence -/

/-- **(C6) Multiradiality** (IUT III, Theorem 3.11(i); [LANA], §8.1(d)): the outputs computed
through any two Hodge theaters agree up to a relabelling of the (Ind3)-choices. -/
def Multiradial : Prop :=
  ∀ {B : A.BPSA} {h h' : A.Side} (ι : A.Choice B h) (ι' : A.Choice B h'),
    ∃ τ : Ind3 D ≃ Ind3 D, ∀ S, A.out ι S = A.out ι' (τ S)

/-- **(C7) Side-dependence** ([LANA], §10.3: `η^anab` is produced from the Θ-side): for some
input, the sets of output possibilities through two Hodge theaters differ. -/
def SideDependent : Prop :=
  ∃ (B : A.BPSA) (h h' : A.Side) (ι : A.Choice B h) (ι' : A.Choice B h'),
    Set.range (A.out ι) ≠ Set.range (A.out ι')

/-- **(C6) and (C7) are incompatible.** -/
theorem not_sideDependent_of_multiradial (hM : A.Multiradial) : ¬ A.SideDependent := by
  rintro ⟨B, h, h', ι, ι', hne⟩
  obtain ⟨τ, hτ⟩ := hM ι ι'
  apply hne
  have : A.out ι = A.out ι' ∘ τ := funext hτ
  rw [this, EquivLike.range_comp]

/-! ### (C8) dependence on the input value group -/

/-- **(C8) The output depends on the value-group portion of the input** ([LANA],
Remark 6.2.2, the reading suggested by (SHE)): two inputs with the same étale-unit portion and
choices with the same étale-unit part give different outputs. -/
def ValDependent : Prop :=
  ∃ (E : EtUnitBPS A.model) (V V' : ValBPS (Pl D) D.bpsDegrees.bad) (h : A.Side)
    (ι : A.Choice ⟨E, V⟩ h) (ι' : A.Choice ⟨E, V'⟩ h),
      ι.et = ι'.et ∧ ∃ S, A.out ι S ≠ A.out ι' S

/-- **No `EtaAlg` satisfies (C8)**: it contradicts (T2) (`etUnitOnly`). -/
theorem not_valDependent : ¬ A.ValDependent := by
  rintro ⟨E, V, V', h, ι, ι', het, S, hne⟩
  obtain ⟨f, hf⟩ := A.etUnitOnly
  apply hne
  rw [hf ι S, hf ι' S, het]

/-! ### (C9) APT -/

/-- **Set-theoretic transport** (the negation of (C9), IUT III, Remark 3.11.1(iv): APT says the
parallel transport "does not consist of a simple instance of transport of some set-theoretic
region via some set-theoretic function"): the output is the image of `S` under one fixed map. -/
def SetTransport : Prop :=
  ∃ φ : Region D → Region D, ∀ {B : A.BPSA} {h : A.Side} (ι : A.Choice B h) (S : Ind3 D),
    A.out ι S = φ S.1

/-- **(C9) APT** (negative form). -/
def APT : Prop := ¬ A.SetTransport

/-- **The wall depends only on the log-volumes of the outputs**: every `EtaAlg` whose outputs
have the identified-copies log-volumes `−s·|log(q)| + log-vol(S)` has the Scholze–Stix
inequality as its wall, whether or not it satisfies APT. -/
theorem wall_iff_ss_of_thetaShift
    (hκ : ∀ {B : A.BPSA} {h : A.Side} (ι : A.Choice B h) (S : Ind3 D),
      logVol D (A.out ι S) = -(sFactor (nC D) * D.qPilot.absLogQ) + logVol D S.1) :
    Wall D A ↔ (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D)) := by
  rw [A.wall_iff_of_lgpLaw (fun _ => -(sFactor (nC D) * D.qPilot.absLogQ)) hκ]
  have hlhs : (concreteVariantData D).qPilot.lhs = -D.qPilot.absLogQ := rfl
  rw [hlhs]
  constructor
  · intro h
    obtain ⟨h₀⟩ := A.side_nonempty
    obtain ⟨_, h⟩ := h h₀ h₀
    linarith
  · intro h h₁ h₂
    exact ⟨(A.nonempty_choice h₁ h₂).some, by linarith⟩

end EtaAlg

/-! ### (C5) the wall across distinct Hodge theaters -/

/-- **(C5) The wall restricted to Θ-links between distinct Hodge theaters** ([LANA], §7.1(b):
the Θ-link goes from `†HT` to `‡HT`). -/
def WallDistinct (D : InitialThetaData.{0}) (A : EtaAlg D) : Prop :=
  ∀ (h₁ h₂ : A.Side), h₁ ≠ h₂ → ∀ (_gl : BPS.Iso (A.thetaBPS h₁) (A.qBPS h₂)),
    ∃ (ι : A.Choice (A.qBPS h₂) h₁) (S : Ind3 D), A.etaAnab ι S = etaQ D

/-- The wall implies its restriction to distinct sides. -/
theorem wallDistinct_of_wall (A : EtaAlg D) (hW : Wall D A) : WallDistinct D A :=
  fun h₁ h₂ _ gl => hW h₁ h₂ gl

/-- **With distinct Hodge theaters (C4), (C5) implies the variant.** -/
theorem variant_of_wallDistinct (A : EtaAlg D) (hD : A.DistinctSides) (hW : WallDistinct D A) :
    Corollary312Variant (concreteVariantData D) := by
  obtain ⟨h₁, h₂, hne⟩ := hD.exists_pair_ne
  obtain ⟨ι, S, hη⟩ := hW h₁ h₂ hne (A.nonempty_thetaLink h₁ h₂).some
  have hvol := (A.etaAnab_eq_etaQ_iff ι S).mp hη
  exact (corollary312Variant_iff _).mpr
    (hvol ▸ logVol_le_rhs D (A.realisation ι S).1 (A.realisation ι S).2)

/-! ### (C10) alien ring structures -/

/-- **Extra structure: an arithmetic holomorphic structure for each Hodge theater** — a ring,
and a predicate saying which ring isomorphisms between two sides are compatible with a given
Θ-link. -/
structure HoloStructure (A : EtaAlg D) where
  /-- The ring of the Hodge theater `h`. -/
  Ring : A.Side → Type
  /-- Its ring structure. -/
  commRing : ∀ h, CommRing (Ring h)
  /-- Ring isomorphisms compatible with the coric identifications of a Θ-link. -/
  Compatible : ∀ h₁ h₂, BPS.Iso (A.thetaBPS h₁) (A.qBPS h₂) →
    (letI := commRing h₁; letI := commRing h₂; Ring h₁ ≃+* Ring h₂) → Prop

/-- **(C10) The ring structures on the two sides of a Θ-link are not identified** ([LANA],
§7.1(b)(c)): between distinct Hodge theaters no ring isomorphism is compatible with a Θ-link. -/
def HoloStructure.Alien {A : EtaAlg D} (H : HoloStructure A) : Prop :=
  ∀ h₁ h₂ gl, h₁ ≠ h₂ → ∀ e, ¬ H.Compatible h₁ h₂ gl e

/-- **Every `EtaAlg` carries alien ring structures**: (C10) is not coupled to the output. -/
theorem exists_alien (A : EtaAlg D) : ∃ H : HoloStructure A, H.Alien :=
  ⟨⟨fun _ => ℤ, fun _ => inferInstance, fun _ _ _ _ => False⟩, fun _ _ _ _ _ h => h⟩

end Wall

namespace Wall

variable (D : InitialThetaData.{0})

/-! ### The identified-copies algorithm with an arbitrary type of identified Hodge theaters -/

/-- **The identified-copies η-algorithm with Hodge theaters indexed by `σ`**: all of them are
identified with `D`, and the output is `LGP·S` for every choice. -/
noncomputable def idAlgOn (σ : Type) [Nonempty σ] : EtaAlg D where
  model _ := trivialGM
  Side := σ
  side_nonempty := inferInstance
  etUnit _ := trivialEtUnit _
  out _ S := lgp D S.1
  ind12_acts_on_S _ _ := ⟨Equiv.refl _, fun _ => rfl⟩
  etUnitOnly := ⟨fun _ S => lgp D S.1, fun _ _ => rfl⟩
  realisation _ S := ⟨isAdelic_lgp D S.2.1, inHullOfImage_lgp D S⟩

theorem idAlg_eq_idAlgOn : idAlg D = idAlgOn D Unit := rfl

variable (σ : Type) [Nonempty σ]

theorem idAlgOn_ipl : (idAlgOn D σ).IPL := (idAlgOn D σ).ipl

theorem idAlgOn_sheSides : (idAlgOn D σ).SHESides :=
  (idAlgOn D σ).sheSides_iff.mpr ⟨fun S => lgp D S.1, fun _ _ _ _ => rfl⟩

theorem idAlgOn_multiradial : (idAlgOn D σ).Multiradial := fun _ _ => ⟨Equiv.refl _, fun _ => rfl⟩

theorem idAlgOn_not_sideDependent : ¬ (idAlgOn D σ).SideDependent :=
  (idAlgOn D σ).not_sideDependent_of_multiradial (idAlgOn_multiradial D σ)

theorem idAlgOn_setTransport : (idAlgOn D σ).SetTransport := ⟨lgp D, fun _ _ => rfl⟩

theorem idAlgOn_not_apt : ¬ (idAlgOn D σ).APT := fun h => h (idAlgOn_setTransport D σ)

theorem idAlgOn_distinctSides [Nontrivial σ] : (idAlgOn D σ).DistinctSides :=
  inferInstanceAs (Nontrivial σ)

/-- **The wall on `idAlgOn σ` is the Scholze–Stix inequality**, for every `σ`. -/
theorem wall_idAlgOn_iff :
    Wall D (idAlgOn D σ) ↔ (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D)) :=
  (idAlgOn D σ).wall_iff_ss_of_thetaShift fun _ S => by
    change logVol D (lgp D S.1) = _
    rw [logVol_lgp D S.2.1, logVol_lgp_integral]

/-- (C3) on the identified-copies model is the Scholze–Stix inequality. -/
theorem sheq_idAlgOn_iff :
    (idAlgOn D σ).SHEq ↔ (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D)) :=
  ((idAlgOn D σ).sheq_iff_wall).trans (wall_idAlgOn_iff D σ)

theorem sheq_idAlg_iff :
    (idAlg D).SHEq ↔ (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D)) :=
  sheq_idAlgOn_iff D Unit

/-- **`idAlg` violates (C4)**: it has one Hodge theater. -/
theorem idAlg_not_distinctSides : ¬ (idAlg D).DistinctSides := fun h => by
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  exact hab rfl

/-- **(C5) is vacuous on `idAlg`.** -/
theorem wallDistinct_idAlg : WallDistinct D (idAlg D) := fun _ _ hab => absurd rfl hab

/-- **On `idAlgOn σ` with distinct Hodge theaters, (C5) is the Scholze–Stix inequality.** -/
theorem wallDistinct_idAlgOn_iff [Nontrivial σ] :
    WallDistinct D (idAlgOn D σ) ↔
      (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D)) := by
  refine ⟨fun h => ?_, fun h => wallDistinct_of_wall _ ((wall_idAlgOn_iff D σ).mpr h)⟩
  rw [← wall_idAlgOn_iff D σ, wall_iff_forall]
  obtain ⟨a, b, hab⟩ := exists_pair_ne σ
  obtain ⟨ι, S, hη⟩ := h a b hab ((idAlgOn D σ).nonempty_thetaLink a b).some
  -- the output does not depend on the sides or the choice
  intro h₁ h₂
  exact ⟨((idAlgOn D σ).nonempty_choice h₁ h₂).some, S, hη⟩

end Wall

end Iut
