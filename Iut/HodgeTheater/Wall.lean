/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.HodgeTheater
import Iut.Wall.MultiContainer

/-!
# Hodge theaters in the multi-container model of the wall

The multi-container model `Iut.Wall.MultiContainer` (`Iut/Wall/MultiContainer.lean`) uses an
η-algorithm `EtaAlg D` whose Hodge theaters `Side` are an opaque type, each with an étale-unit BPS
(an `F^{⊢×μ}`-prime-strip) over the places `Pl D = V(F)`. Here the sides are **actual
`Θ^{±ell}NF`-Hodge theaters built from `D`**:

* `theaterAlg D H` (for a family `H : σ → ThetaPmEllNFHT D` of theaters, e.g. the column
  `ℤ → ThetaPmEllNFHT D` of copies of the theater built from `D`, `chain D`): the η-algorithm whose
  Hodge theater `h` has as étale-unit BPS **the `F^{⊢×μ}`-prime-strip of `H h`** (`etUnitOf`),
  pulled back along `V(F) → V_mod ≅ V` (`underPl`; the wall indexes by the places of `F`, IUT by
  `V ≅ V_mod`), and whose output is the identified-copies output `LGP·S` (the output of the
  η-algorithm is not constructed here; this is the output of `Iut.Wall.idAlgOn`);
* **isomorphisms of Hodge theaters induce isomorphisms of étale-unit BPSs** (`etUnitIsoOf`, from
  the isomorphism of `F^{⊢×μ}`-prime-strips of an isomorphism of theaters): the étale-unit portion
  of the BPS-level Θ-link comes from the theaters;
* `theaterModel D H`: the multi-container model over `theaterAlg D H` whose **Kummer
  isomorphisms are those of the theaters**: every theater built from `D` carries the arithmetic
  holomorphic structure of `D` (its `F`-prime-strips are the tautological ones), so its Kummer
  isomorphism with the coric container is the identity scaling (`kummer_theaterModel`);
  consequently `VolCompat` holds and **the wall of the model is the Scholze–Stix inequality**
  (`wall3_theaterModel_iff`), as for `Iut.Wall.idModel`;
* **the containers come from the theaters' prime-strips** (as far as the objects allow): the
  container of every Hodge theater is indexed by the places of the valuation section `V` that
  indexes the theater's prime-strips (`placeSect_fin`, `placeSect_inf`), and its procession of
  tensor-packet capsules `S_2 ⊆ ⋯ ⊆ S_{ℓ*+1}` is carried onto the `±`-label capsules
  `S^±_2 ⊆ ⋯ ⊆ S^±_{ℓ±}` of the theater's procession (`container_capsule_eq`,
  Proposition 6.9(i)).
-/

namespace Iut

namespace HodgeTheater

open NumberField Wall

variable (D : InitialThetaData.{0})

/-! ### `V(F) → V_mod` -/

/-- **The place of `F_mod` below a place of `F`** (the wall indexes by `V(F)`, IUT by
`V ≅ V_mod`). -/
noncomputable def underPl : Pl D → Vp D
  | Sum.inl w => Sum.inl (placeUnder w)
  | Sum.inr w => Sum.inr (w.comap (algebraMap ↥(fieldOfModuli D.F D.E) D.F))

/-! ### GM-data of the wall -/

/-- The GM-data of the wall from universe-`0` GM-data. -/
def gmToWall (X : Kind.GM.{0}) : GMData where
  G := X.G
  M := X.M
  compact := X.compact

/-- Isomorphisms of GM-data, for the wall. -/
def gmIsoToWall {X Y : Kind.GM.{0}} (e : Kind.GMIso X Y) : GMIso (gmToWall X) (gmToWall Y) where
  G := e.G
  M := e.M
  equivariant := e.equivariant
  compact := e.compact

/-- **The model étale-unit BPS of the wall**: the tautological `F^{⊢×μ}`-prime-strip
`{G_v ↷ O^{×μ}(K_v)}`, pulled back to the places of `F`. -/
noncomputable def etModel : Pl D → GMData := fun w => gmToWall (fmuModel D (underPl D w))

/-- **The étale-unit BPS of an `F^{⊢×μ}`-prime-strip.** -/
noncomputable def etUnitOf (P : FMuStrip D) : EtUnitBPS (etModel D) where
  gm w := gmToWall (P.obj (underPl D w))
  iso_model w := ⟨gmIsoToWall (P.iso_model (underPl D w)).some⟩

/-- **Isomorphisms of `F^{⊢×μ}`-prime-strips induce isomorphisms of étale-unit BPSs.** -/
noncomputable def etUnitIsoOfStrip {P Q : FMuStrip D} (f : P.Iso Q) :
    EtUnitIso (etUnitOf D P) (etUnitOf D Q) :=
  fun w => gmIsoToWall (f (underPl D w))

/-! ### The η-algorithm with Hodge theaters as sides -/

variable {σ : Type} [Nonempty σ]

/-- **The η-algorithm whose Hodge theaters are the `Θ^{±ell}NF`-Hodge theaters `H h`**, with the
étale-unit BPS of `H h` given by its `F^{⊢×μ}`-prime-strip and the identified-copies output. -/
noncomputable def theaterAlg (H : σ → ThetaPmEllNFHT D) : EtaAlg D where
  model := etModel D
  Side := σ
  side_nonempty := inferInstance
  etUnit h := etUnitOf D (H h).Fmu
  out _ S := lgp D S.1
  ind12_acts_on_S _ _ := ⟨Equiv.refl _, fun _ => rfl⟩
  etUnitOnly := ⟨fun _ S => lgp D S.1, fun _ _ => rfl⟩
  realisation _ S := ⟨isAdelic_lgp D S.2.1, inHullOfImage_lgp D S⟩

/-- **Isomorphisms of Hodge theaters induce isomorphisms of their étale-unit BPSs** (the étale-unit
portion of the BPS-level Θ-link comes from the theaters). -/
noncomputable def etUnitIsoOf (H : σ → ThetaPmEllNFHT D) {h h' : σ} (f : (H h).Iso (H h')) :
    EtUnitIso ((theaterAlg D H).etUnit h) ((theaterAlg D H).etUnit h') :=
  etUnitIsoOfStrip D f.Fmu

/-- The identified-copies log-volumes hold for `theaterAlg`. -/
theorem theaterAlg_thetaShift (H : σ → ThetaPmEllNFHT D) : (theaterAlg D H).ThetaShift :=
  fun _ S => by
    change logVol D (lgp D S.1) = _
    rw [logVol_lgp D S.2.1, logVol_lgp_integral]

/-- **The Kummer isomorphism of a Hodge theater built from `D`** with the coric container: every
such theater carries the arithmetic holomorphic structure of `D`, so it is the identity scaling. -/
noncomputable def theaterKummer (_h : ThetaPmEllNFHT D) : Scaling D := 1

/-- **The multi-container model whose sides are the Hodge theaters `H h`**, with their Kummer
isomorphisms. -/
noncomputable def theaterModel (H : σ → ThetaPmEllNFHT D) : MultiContainer D :=
  ⟨theaterAlg D H, fun h => theaterKummer D (H h)⟩

/-- The Kummer isomorphisms of the model are the identity on every container. -/
theorem kummer_theaterModel (H : σ → ThetaPmEllNFHT D) (h : σ) (U : Region D) :
    (theaterModel D H).kummer h U = U :=
  act_one D U

/-- The model is `ofAlg` of its η-algorithm. -/
theorem theaterModel_eq_ofAlg (H : σ → ThetaPmEllNFHT D) :
    theaterModel D H = MultiContainer.ofAlg (theaterAlg D H) := rfl

/-- Volume compatibility holds. -/
theorem theaterModel_volCompat (H : σ → ThetaPmEllNFHT D) : (theaterModel D H).VolCompat :=
  fun _ _ => rfl

/-- **The wall of the multi-container model over Hodge theaters built from `D` is the
Scholze–Stix inequality** (as for `Iut.Wall.idModel`, `Iut.Wall.wall3_idModel_iff`). -/
theorem wall3_theaterModel_iff (H : σ → ThetaPmEllNFHT D) :
    (theaterModel D H).Wall3 ↔ SSIneq D :=
  (theaterModel D H).wallOn_iff_ss_of_volCompat (theaterAlg_thetaShift D H)
    (theaterModel_volCompat D H) (let h := Classical.arbitrary σ; ⟨h, h, trivial⟩)

/-- **The column of Hodge theaters** `n ↦ ^nHT` (`n ∈ ℤ`), copies of the theater built from `D`
(the Hodge theaters linked by the Θ-links, IUT III). -/
noncomputable def chain : ℤ → ThetaPmEllNFHT D := fun _ => ThetaPmEllNFHT.ofData D

/-- The multi-container model over the column of Hodge theaters built from `D`. -/
noncomputable def chainModel : MultiContainer D := theaterModel D (chain D)

theorem wall3_chainModel_iff : (chainModel D).Wall3 ↔ SSIneq D := wall3_theaterModel_iff D _

/-- Any two Hodge theaters of the column are isomorphic, so their étale-unit BPSs are isomorphic
through an isomorphism of Hodge theaters. -/
theorem nonempty_etUnitIso_chain (m n : ℤ) :
    Nonempty (EtUnitIso ((theaterAlg D (chain D)).etUnit m) ((theaterAlg D (chain D)).etUnit n)) :=
  (ThetaPmEllNFHT.nonempty_iso _ _).map (etUnitIsoOf D (chain D))

/-! ### The containers come from the theaters' prime-strips -/

/-- The container's tensor packets are indexed by the valuation section `V` that indexes the
prime-strips: finite places. -/
theorem placeSect_fin : D.placeSect.fin = D.V.sectFin := rfl

/-- The container's tensor packets are indexed by the valuation section `V`: archimedean
places. -/
theorem placeSect_inf : D.placeSect.inf = D.V.sectInf := rfl

/-- The local field of the container at a finite place of the section is the base field of the
`p`-adic Frobenioid of the theaters' `F`-prime-strips there. -/
theorem padicModel_eq (w : FinitePlace ↥(fieldOfModuli D.F D.E)) :
    padicModel D w = CategoryTheory.Cat.of (Frobenioid.PAdic (D.placeSect.fin w)) := rfl

/-- The container procession is the standard procession of `ℓ* = nC D` capsules. -/
theorem container_proc : (VC D).proc = Procession.standard (ellStar D.ℓ) := rfl

omit [Nonempty σ] in
open scoped Classical in
/-- **The capsules of the container of every Hodge theater are the `±`-label capsules of the
theater's procession** (IUT I, Proposition 6.9(i)): the `i`-th capsule `S_{i+2}` of tensor-packet
labels of the container `VC D` (the container `VCh h` of every Hodge theater `h` of
`theaterModel D H` is a copy of it) is carried by `ℕ → |F_ℓ|` onto the capsule `S^±_{i+2}` of the
`ℓ±`-procession of the theater `H h`. -/
theorem container_capsule_eq (H : σ → ThetaPmEllNFHT D) (h : σ) (i : Fin (ellStar D.ℓ)) :
    ((VC D).proc.capsule i).labels.image (natAbs D.ℓ) =
      ((H h).labels.procPm.capsule (succEmb (ellStar D.ℓ) i)).labels :=
  standard_image_eq D.ℓ i

end HodgeTheater

end Iut
