/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Tempered
import Iut.Anabelian.Genuine.Punctured

/-!
# The genuine étale fundamental groups and cores of the model orbicurves

* the genuine arithmetic étale fundamental groups `Orbicurve.genuinePi1 X = Genuine.pi1C E ℓ M ±`
  (`Aut(Ω / F_X) ⧸ ⟨⟨inertia⟩⟩` in characteristic `0`, a trivial junk value in positive
  characteristic), with the maps induced by covers (`genuinePi1Cover`, `Genuine.pi1MapC`),
  which are continuous open embeddings (`genuinePi1Cover_isOpenEmbedding`);
* **the genuine `k`-cores** of [CanLift], §2: `genuineHasCore X C` says that (`k` has
  characteristic `0` and) the realization of `C` as an affine orbicurve is the `k`-core, i.e. the
  terminal object of `\\overline{Loc}_k`, of the realization of `X` (`Genuine.realize`,
  `AffOrbicurve.IsCoreOf`);
* covers do not change cores (`genuineHasCore_iff_of_cover`, by pullbacks of finite étale
  covers);
* [CanLift], Proposition 2.7 for the genuine cores (`genuineHasCore_oncePunctured`), from the
  statement `AffOrbicurve.CanLift27` of the `pi1` project for the once-punctured elliptic curve
  and its `±1`-quotient (the realizations are isomorphic to these,
  `Genuine.isCoreOf_realize_oncePunctured`), with exceptional set `AffOrbicurve.excJ` the four
  `j`-invariants `0, 1728, 488095744/125, 1556068/81` (Takeuchi; Sijsling). The statement is a
  theorem, `Iut.Anabelian.canLift27` (`Iut.Anabelian.CanLift`).
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

end

end Iut.Anabelian
