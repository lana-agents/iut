/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Tempered
import Iut.Anabelian.Genuine.Punctured

/-!
# The genuine étale theory of the model orbicurves

This module assembles a term of `Iut.Anabelian.GenuineEtaleData`, hence of
`Iut.Anabelian.EtalePi1Theory` (`genuinePi1Theory`) with `temperedTheory` over it, from

* the genuine arithmetic étale fundamental groups `Orbicurve.genuinePi1 X = Genuine.pi1C E ℓ M ±`
  (`Aut(Ω / F_X) ⧸ ⟨⟨inertia⟩⟩` in characteristic `0`, a trivial junk value in positive
  characteristic), with the maps induced by covers (`Genuine.pi1MapC`, open embeddings);
* **the genuine `k`-cores** of [CanLift], §2: `genuineHasCore X C` says that (`k` has
  characteristic `0` and) the realization of `C` as an affine orbicurve is the `k`-core, i.e. the
  terminal object of `\\overline{Loc}_k`, of the realization of `X` (`Genuine.realize`,
  `AffOrbicurve.IsCoreOf`);
* covers do not change cores (`Genuine.isCoreOf_realize_iff`, by pullbacks of finite étale
  covers);
* [CanLift], Proposition 2.7 (`AffOrbicurve.CanLift27`, stated in the `pi1` project for the
  once-punctured elliptic curve and its `±1`-quotient; the realizations are isomorphic to these,
  `Genuine.isCoreOf_realize_oncePunctured`), a hypothesis, with `excJ` the four exceptional
  `j`-invariants `0, 1728, 488095744/125, 1556068/81` (Takeuchi; Sijsling);
* the compatibility of cores with base change (`GenuineCoreBaseChange`, [CanLift],
  Proposition 2.3), a hypothesis.
-/

namespace Iut.Anabelian

universe u

open AffOrbicurve

noncomputable section

attribute [local instance low] Classical.propDecidable

variable {k : Type u} [Field k]

/-- **`C` is the `k`-core of `X`** ([CanLift], Definition 2.1, Remark 2.1.1), for model
orbicurves over a field of characteristic `0`: the affine orbicurve realizing `C` is the terminal
object of `\\overline{Loc}_k` of the affine orbicurve realizing `X`. (Never true in positive
characteristic, where the notion is not used.) -/
def genuineHasCore (X C : Orbicurve k) : Prop :=
  ∃ _ : CharZero k, IsCoreOf (Genuine.realize X.E X.level X.M X.pm)
    (Genuine.realize C.E C.level C.M C.pm)

/-- **The homomorphism of genuine fundamental groups induced by a cover**. -/
def genuinePi1Cover {X Y : Orbicurve k} (c : Orbicurve.Cover X Y) :
    X.genuinePi1 →* Y.genuinePi1 := by
  cases X with | @mk E hE ℓ M pm =>
  cases Y with | @mk E' hE' ℓ' M' pm' =>
  have h : E = E' := c.E_eq
  subst h
  exact Genuine.pi1MapC E

lemma genuinePi1Cover_continuous {X Y : Orbicurve k} (c : Orbicurve.Cover X Y) :
    Continuous (genuinePi1Cover c) := by
  cases X with | @mk E hE ℓ M pm =>
  cases Y with | @mk E' hE' ℓ' M' pm' =>
  obtain ⟨h, n, hn, hmul, hM, hpm⟩ := c
  change E = E' at h
  subst h
  exact Genuine.continuous_pi1MapC E

lemma genuinePi1Cover_isOpenEmbedding {X Y : Orbicurve k} (c : Orbicurve.Cover X Y) :
    Topology.IsOpenEmbedding (genuinePi1Cover c) := by
  cases X with | @mk E hE ℓ M pm =>
  cases Y with | @mk E' hE' ℓ' M' pm' =>
  obtain ⟨h, n, hn, hmul, hM, hpm⟩ := c
  change E = E' at h
  subst h
  exact Genuine.isOpenEmbedding_pi1MapC E hn hmul hM hpm

/-- **Orbicurves related by a cover have the same cores.** -/
lemma genuineHasCore_iff_of_cover [CharZero k] {X Y C : Orbicurve k} (c : Orbicurve.Cover X Y) :
    genuineHasCore X C ↔ genuineHasCore Y C := by
  cases X with | @mk E hE ℓ M pm =>
  cases Y with | @mk E' hE' ℓ' M' pm' =>
  obtain ⟨h, n, hn, hmul, hM, hpm⟩ := c
  change E = E' at h
  subst h
  unfold genuineHasCore
  exact ⟨fun ⟨_, h⟩ => ⟨inferInstance, (Genuine.isCoreOf_realize_iff E hn hmul hM hpm _).mp h⟩,
    fun ⟨_, h⟩ => ⟨inferInstance, (Genuine.isCoreOf_realize_iff E hn hmul hM hpm _).mpr h⟩⟩

/-- **[CanLift], Proposition 2.7** for the genuine cores. -/
lemma genuineHasCore_oncePunctured (h27 : CanLift27.{u}) [CharZero k] (E : WeierstrassCurve k)
    [E.IsElliptic] (hj : ∀ c ∈ AffOrbicurve.excJ, E.j ≠ (c : k)) :
    genuineHasCore (Orbicurve.oncePunctured E) (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)) :=
  ⟨inferInstance, Genuine.isCoreOf_realize_oncePunctured E h27 hj⟩

/-- **The compatibility of cores with base change** ([CanLift], Proposition 2.3, for the model
orbicurves): if `C` is the `k`-core of `X`, then `C_K` is the `K`-core of `X_K`. A hypothesis of
the genuine étale theory. -/
def GenuineCoreBaseChange : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [CharZero k] [CharZero K] (f : k →+* K)
    {X C : Orbicurve k}, genuineHasCore X C → genuineHasCore (X.baseChange f) (C.baseChange f)

/-- **The genuine étale data**: genuine fundamental groups and genuine cores, given [CanLift],
Proposition 2.7 and the compatibility of cores with base change. -/
def genuineEtaleData (h27 : CanLift27.{u}) (hbc : GenuineCoreBaseChange.{u}) :
    GenuineEtaleData.{u} where
  pi1Cover := genuinePi1Cover
  pi1Cover_continuous := genuinePi1Cover_continuous
  pi1Cover_isOpenEmbedding := genuinePi1Cover_isOpenEmbedding
  HasCore := genuineHasCore
  hasCore_iff_of_cover := genuineHasCore_iff_of_cover
  hasCore_baseChange := hbc
  excJ := AffOrbicurve.excJ
  hasCore_oncePunctured := fun E _ hj => genuineHasCore_oncePunctured h27 E hj

/-- **The genuine étale theory of the model orbicurves** (`EtalePi1Theory`). -/
def genuinePi1Theory (h27 : CanLift27.{u}) (hbc : GenuineCoreBaseChange.{u}) :
    EtalePi1Theory.{u} :=
  (genuineEtaleData h27 hbc).toEtalePi1Theory

lemma genuinePi1Theory_pi1 (h27 : CanLift27.{u}) (hbc : GenuineCoreBaseChange.{u})
    (X : Orbicurve k) : (genuinePi1Theory h27 hbc).pi1 X = X.genuinePi1 := rfl

lemma genuinePi1Theory_hasCore (h27 : CanLift27.{u}) (hbc : GenuineCoreBaseChange.{u})
    (X C : Orbicurve k) : (genuinePi1Theory h27 hbc).HasCore X C ↔ genuineHasCore X C := Iff.rfl

lemma genuinePi1Theory_excJ (h27 : CanLift27.{u}) (hbc : GenuineCoreBaseChange.{u}) :
    (genuinePi1Theory h27 hbc).excJ = {0, 1728, 488095744 / 125, 1556068 / 81} := rfl

end

end Iut.Anabelian
