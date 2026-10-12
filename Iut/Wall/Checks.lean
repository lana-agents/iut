/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Wall.EtaAlg

/-!
# Faithfulness checks of the wall interface (the wall, Milestone 1d (i), (ii))

**(i) The shadow lemma** (`numericalWall_iff`). The purely numerical form of (9-1) — "there is
an adelic region in the hull of a single (Ind1)-image of the theta-pilot region whose pointed
map `R_val → R_ss` equals `η_q`", i.e. whose class in `R_ss` is the class of `{q_v O_v}` — is
*equivalent* to `Corollary312Variant (concreteVariantData D)`. Since two pointed maps out of a
pointed line agree iff they send the pilot to the same point (`ValBPS.eta_eq_eta_iff`), (9-1)
by itself is an equation of real numbers; and the set of log-volumes available is exactly
`ℝ_{≤ −|log(Θ)|}` (`exists_adelic_iff`). So the numerical form of (9-1) restates the variant:
it is circular. This formalizes [LANA], §10.3 ((9-1) is a comparison "*before* computing
degrees") from the other side: everything that is not about the provenance of `η^anab` is a
restatement of Corollary 3.12.

**(ii) The trivial instance.** `EtaAlg.IsTrivial A`: `η^anab_{ι,S} = η_q` (transported) for
*every* choice `(ι, S)` — "`etaAnab := etaQ`". Results:

* `exists_isTrivial_iff`: an admissible `EtaAlg D` with `IsTrivial` exists **iff** the
  variant holds for `D`. So the fields (T1)–(T3) do **not** rule out the trivial solution
  unconditionally; ruling it out is as hard as refuting the variant. The instance
  `trivialAlg` (one Hodge theater, one output region of log-volume `−|log(q)|`) satisfies
  (T1), (T2) and (T3) as soon as such a region exists.
* `exists_wall_iff`: consequently `∃ A : EtaAlg D, Wall D A` **iff** the variant holds. As an
  existential statement over interfaces, the wall is a restatement of the variant: the
  interface (T1)–(T3) is too weak to encode the provenance of `η^anab` (it is not forced to be
  computed from the Θ-side). The wall is non-circular only for a *given* algorithm `A`,
  i.e. once the η-algorithm is constructed (Milestone 2–3 of the roadmap).
* `EtaAlg.LGPLaw` (**T4**, a strengthening, not in [LANA] as a separate statement): the output
  is `M = 1·S`, the image of `S` under the action of the theta values (a unit of the
  container), so its log-volume is `κ_ι + log-vol(S)` for a shift `κ_ι` depending only on the
  choice `ι` ([LANA], §9.2: "`M = 1·S` … represents `LGP·S`"). Under (T4) the trivial
  instance is excluded (`not_isTrivial_of_lgpLaw`), since `S ↦ log-vol(S)` takes several values on
  the (Ind3)-choices; but the wall is then the numerical condition
  `−|log(q)| − κ_ι ≤ log-vol(VC(I))` for some `ι` (`wall_iff_of_lgpLaw`), again a statement about
  real numbers, whose content is the value of `κ_ι`. For the identified-copies model `κ` is
  computed in `Iut/Wall/IdentifiedCopies.lean`.
-/

namespace Iut

namespace Wall

variable (D : InitialThetaData.{0})

/-! ### (i) The shadow lemma -/

/-- **The numerical form of (9-1)**: an adelic region in the hull of a single (Ind1)-image of
the theta-pilot region whose pointed map `R_val → R_ss` is `η_q`. -/
def NumericalWall : Prop :=
  ∃ U : Region D, IsAdelic D U ∧ InHullOfImage D U ∧ (qVal D.bpsDegrees).eta (logVol D U) = etaQ D

/-- **The shadow lemma**: the numerical form of (9-1) is equivalent to the Corollary 3.12
variant for `D`. -/
theorem numericalWall_iff : NumericalWall D ↔ Corollary312Variant (concreteVariantData D) := by
  unfold NumericalWall etaQ
  simp only [ValBPS.eta_eq_eta_iff]
  rw [corollary312Variant_iff, ← exists_adelic_iff]
  rfl

/-- The numerical form of (9-1) in terms of classes in `R_ss`: the class of the output is the
class of log-volume `−|log(q)|`. -/
theorem numericalWall_iff_rss : NumericalWall D ↔ ∃ (U : Region D) (hU : IsAdelic D U),
    InHullOfImage D U ∧ Rss.mk D U hU = (rssEquiv D).symm (concreteVariantData D).qPilot.lhs := by
  unfold NumericalWall etaQ
  simp only [ValBPS.eta_eq_eta_iff, Equiv.eq_symm_apply]
  exact ⟨fun ⟨U, hU, hI, h⟩ => ⟨U, hU, hI, h⟩, fun ⟨U, hU, hI, h⟩ => ⟨U, hU, hI, h⟩⟩

/-! ### (ii) The trivial instance -/

namespace EtaAlg

variable {D} (A : EtaAlg D)

/-- **The trivial instance** "`etaAnab := etaQ`": for every input `B` and every choice
`(ι, S)`, `η^anab_{ι,S}` is the pointed map of `η_q` (pilot to `−|log(q)|`). -/
def IsTrivial : Prop :=
  ∀ {B : A.BPSA} {h : A.Side} (ι : A.Choice B h) (S : Ind3 D),
    A.etaAnab ι S = B.val.eta (concreteVariantData D).qPilot.lhs

/-- A trivial instance satisfies the wall. -/
theorem wall_of_isTrivial (hT : A.IsTrivial) : Wall D A := fun h₁ h₂ _ =>
  ⟨(A.nonempty_choice h₁ h₂).some, Ind3.top D, hT _ _⟩

/-- **(T4) The LGP law**: the output is the image of `S` under multiplication by the theta
values, so its log-volume is `κ_ι + log-vol(S)` ([LANA], §9.2). -/
def LGPLaw : Prop :=
  ∀ {B : A.BPSA} {h : A.Side} (ι : A.Choice B h), ∃ κ : ℝ, ∀ S : Ind3 D,
    logVol D (A.out ι S) = κ + logVol D S.1

/-- **Under the LGP law the trivial instance is excluded.** -/
theorem not_isTrivial_of_lgpLaw (hL : A.LGPLaw) : ¬ A.IsTrivial := by
  intro hT
  obtain ⟨h⟩ := A.side_nonempty
  obtain ⟨κ, hκ⟩ := hL (BPS.Iso.refl (A.thetaBPS h))
  obtain ⟨S, hS⟩ := (exists_ind3_logVol_iff D (logVol D (vcI D) - 1)).mpr (by linarith)
  have h1 := (ValBPS.eta_eq_eta_iff _ _ _).mp (hT (BPS.Iso.refl (A.thetaBPS h)) (Ind3.top D))
  have h2 := (ValBPS.eta_eq_eta_iff _ _ _).mp (hT (BPS.Iso.refl (A.thetaBPS h)) S)
  rw [hκ] at h1 h2
  change κ + logVol D (vcI D) = _ at h1
  rw [hS] at h2
  linarith

/-- **Under the LGP law the wall is a numerical condition on the shifts `κ_ι`**:
`−|log(q)| − κ_ι ≤ log-vol(VC(I))` for some choice `ι`. -/
theorem wall_iff_of_lgpLaw (κ : ∀ {B : A.BPSA} {h : A.Side}, A.Choice B h → ℝ)
    (hκ : ∀ {B : A.BPSA} {h : A.Side} (ι : A.Choice B h) (S : Ind3 D),
      logVol D (A.out ι S) = κ ι + logVol D S.1) :
    Wall D A ↔ ∀ h₁ h₂ : A.Side, ∃ ι : A.Choice (A.qBPS h₂) h₁,
      (concreteVariantData D).qPilot.lhs - κ ι ≤ logVol D (vcI D) := by
  rw [wall_iff_forall]
  refine forall₂_congr fun h₁ h₂ => exists_congr fun ι => ?_
  simp only [etaAnab_eq_etaQ_iff, hκ]
  rw [← exists_ind3_logVol_iff]
  exact ⟨fun ⟨S, hS⟩ => ⟨S, by linarith⟩, fun ⟨S, hS⟩ => ⟨S, by linarith⟩⟩

end EtaAlg

/-- The trivial GM-datum (the trivial group acting on the trivial monoid). -/
def trivialGM : GMData where
  G := Unit
  M := Unit
  instAction :=
    { smul := fun _ m => m
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_mul := fun _ _ _ => rfl
      smul_one := fun _ => rfl }
  compact := Set.univ

/-- The trivial étale-unit BPS. -/
def trivialEtUnit (V : Type) : EtUnitBPS (fun _ : V => trivialGM) :=
  ⟨fun _ => trivialGM, fun _ => ⟨GMIso.refl _⟩⟩

/-- **The trivial η-algorithm**: one Hodge theater, and the same output `U` for every choice. -/
noncomputable def trivialAlg (U : Region D) (hU : IsAdelic D U) (hI : InHullOfImage D U) :
    EtaAlg D where
  model _ := trivialGM
  Side := Unit
  side_nonempty := ⟨()⟩
  etUnit _ := trivialEtUnit _
  out _ _ := U
  ind12_acts_on_S _ _ := ⟨Equiv.refl _, fun _ => rfl⟩
  etUnitOnly := ⟨fun _ _ => U, fun _ _ => rfl⟩
  realisation _ _ := ⟨hU, hI⟩

theorem trivialAlg_isTrivial (U : Region D) (hU : IsAdelic D U) (hI : InHullOfImage D U)
    (hvol : logVol D U = (concreteVariantData D).qPilot.lhs) :
    (trivialAlg D U hU hI).IsTrivial := by
  intro B h ι S
  unfold EtaAlg.etaAnab
  rw [ValBPS.eta_eq_eta_iff]
  exact hvol

/-- **The interface (T1)–(T3) has a trivial instance iff the variant holds.** -/
theorem exists_isTrivial_iff :
    (∃ A : EtaAlg D, A.IsTrivial) ↔ Corollary312Variant (concreteVariantData D) := by
  constructor
  · rintro ⟨A, hT⟩
    exact variant_of_wall A (A.wall_of_isTrivial hT)
  · intro h
    obtain ⟨U, hU, hI, hvol⟩ := (exists_adelic_iff D _).mpr ((corollary312Variant_iff _).mp h)
    exact ⟨trivialAlg D U hU hI, trivialAlg_isTrivial D U hU hI hvol⟩

/-- **The existence of an η-algorithm satisfying the wall is equivalent to the variant**: as an
existential statement over the interface, the wall restates Corollary 3.12. -/
theorem exists_wall_iff :
    (∃ A : EtaAlg D, Wall D A) ↔ Corollary312Variant (concreteVariantData D) := by
  constructor
  · rintro ⟨A, hW⟩
    exact variant_of_wall A hW
  · intro h
    obtain ⟨A, hT⟩ := (exists_isTrivial_iff D).mpr h
    exact ⟨A, A.wall_of_isTrivial hT⟩

end Wall

end Iut
