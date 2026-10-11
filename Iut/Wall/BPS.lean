/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Real.Basic

/-!
# Basic prime strips (the wall, Milestone 1a; taxis #1450)

The **basic prime strips** (BPSs) of the LANA interim report (July 2026; cited as [LANA]),
§4.1, pp. 23–24: LANA's simplified, "nearly equivalent" stand-in for the
`F^{⊩▶×µ}`-prime-strips of IUT II, Definition 4.9(viii) (and IUT III, Definition 2.4,
Theorem 3.11), between which the Θ-link of IUT III, Definition 3.8, is a full
poly-isomorphism.

A BPS is a pair of an **étale-unit portion** and a **value-group portion**
([LANA], Definition 4.1.6):

* `GMData`, `GMIso`: mono-analytic GM-data `G ↷ M` with compact structure and their
  isomorphisms ([LANA], §3.9, §0.4(c), Definition 4.1.2);
* `EtUnitBPS model`, `EtUnitIso`: étale-unit BPSs ([LANA], Definition 4.1.2), i.e. families
  `{G_v ↷ M_v}_{v ∈ V}` *abstractly isomorphic* to a fixed model `{G_v ↷ O^{×µ}_v}_v`;
* `ValBPS V bad`, `ValIso`: value-group BPSs `(C, {φ_v}_v)` ([LANA], Definitions 4.1.3,
  4.1.4) with their product formula `PF` (the kernel of `⊕_v ℝ_v → C`);
* `BPS`, `BPSIso` ([LANA], Definition 4.1.6).

Proved here:

* **[LANA], Lemma 4.1.7**: two value-group BPSs are isomorphic iff they have the same product
  formula (`ValBPS.nonempty_valIso_iff`), and two BPSs are isomorphic iff their value-group
  portions have the same product formula (`BPS.nonempty_iso_iff`);
* **[LANA], Remark 8.2.1** ("the category of BPSs is a connected groupoid"): BPSs with a fixed
  product formula form a connected groupoid (`BPS.Iso.refl`, `BPS.Iso.symm`,
  `BPS.Iso.trans`, `BPS.connected`); so "linked by an isomorphism of BPSs" is vacuous for
  them, and value-group isomorphisms are unique (`ValBPS.valIso_subsingleton`);
* **[LANA], Remark 4.1.5**: a value-group BPS is a "pointed real line" with pilot
  `φ_C = ∑_{v ∈ V^bad} φ_v`, and a linear map out of it is determined by the image of the
  pilot (`ValBPS.eta`, `ValBPS.eta_unique`, `ValBPS.eta_eq_eta_iff`).

## Simplifications (documented deviations from [LANA])

* The compact structure `{N_{v,H}}_H` (one subset for each open subgroup `H ⊆ G_v`) is
  replaced by a single subset `GMData.compact` of `M` (the term for `H = G_v`); isomorphisms
  are required to match it. Nothing below uses the compact structure.
* The orientation of `C` ([LANA], Definition 4.1.3, Remark 4.1.5) is not recorded:
  isomorphisms of value-group BPSs ([LANA], Definition 4.1.4) do not refer to it. The sign
  convention of Remark 4.1.5 (the pilot is "negative") is not imposed: §4.2(c) itself defines
  the `q`-pilot with positive local pilots `deg(q_v)`.
* The topological groups `G_v` and monoids `M_v` are arbitrary; "abstractly isomorphic to the
  model `G_v ↷ O^{×µ}_v`" is a field (`EtUnitBPS.iso_model`) relative to a model supplied as a
  parameter (the absolute Galois groups of the local fields are not constructed here).
-/

namespace Iut

namespace Wall

/-! ### Mono-analytic GM-data -/

/-- **Mono-analytic GM-data with compact structure** `G ↷ M` ([LANA], §3.9, Definition 4.1.2;
IUT II, Definition 4.9; simplified): a topological group `G` acting on a commutative monoid `M`
by monoid automorphisms, with a compact structure, simplified to one subset of `M`. -/
structure GMData where
  /-- The topological group `G_v` (abstractly isomorphic to a local Galois group). -/
  G : Type
  /-- The monoid `M_v` (abstractly isomorphic to `O^{×µ}_v`). -/
  M : Type
  [instGroup : Group G]
  [instTop : TopologicalSpace G]
  [instMonoid : CommMonoid M]
  [instAction : MulDistribMulAction G M]
  /-- The compact structure (simplified: the term `N_{v,G}` of the family `{N_{v,H}}_H`). -/
  compact : Set M

attribute [instance] GMData.instGroup GMData.instTop GMData.instMonoid GMData.instAction

/-- **An isomorphism of GM-data** `G ↷ M ≅ G' ↷ M'` ([LANA], §0.4(c), Definition 4.1.2(2)):
an isomorphism of topological groups and an isomorphism of monoids, compatible with the
actions and with the compact structures. -/
structure GMIso (X Y : GMData) where
  /-- The isomorphism of topological groups `φ_G`. -/
  G : X.G ≃ₜ* Y.G
  /-- The isomorphism of monoids `φ_M`. -/
  M : X.M ≃* Y.M
  /-- Equivariance: `φ_M(g·m) = φ_G(g)·φ_M(m)`. -/
  equivariant : ∀ (g : X.G) (m : X.M), M (g • m) = G g • M m
  /-- The compact structures correspond. -/
  compact : M '' X.compact = Y.compact

namespace GMIso

/-- The identity isomorphism. -/
def refl (X : GMData) : GMIso X X where
  G := ContinuousMulEquiv.refl X.G
  M := MulEquiv.refl X.M
  equivariant _ _ := rfl
  compact := Set.image_id _

/-- The inverse isomorphism. -/
def symm {X Y : GMData} (e : GMIso X Y) : GMIso Y X where
  G := e.G.symm
  M := e.M.symm
  equivariant g m := by
    apply e.M.injective
    rw [MulEquiv.apply_symm_apply, e.equivariant, ContinuousMulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
  compact := by
    rw [← e.compact, ← Set.image_comp]
    simp

/-- The composite isomorphism. -/
def trans {X Y Z : GMData} (e : GMIso X Y) (f : GMIso Y Z) : GMIso X Z where
  G := e.G.trans f.G
  M := e.M.trans f.M
  equivariant g m := by
    change f.M (e.M (g • m)) = f.G (e.G g) • f.M (e.M m)
    rw [e.equivariant, f.equivariant]
  compact := by
    rw [MulEquiv.coe_trans, Set.image_comp, e.compact, f.compact]

end GMIso

/-! ### Étale-unit BPSs -/

variable {V : Type}

/-- **An étale-unit BPS** ([LANA], Definition 4.1.2(1)): an `F^{⊢×µ}`-prime-strip
`{G_v ↷ M_v, {N_{v,H}}_H}_{v ∈ V}`, i.e. a family of mono-analytic GM-data abstractly
isomorphic to the model `{G_v ↷ O^{×µ}_v, {I^κ_H}_H}_{v ∈ V}`, here a parameter `model`. -/
structure EtUnitBPS (model : V → GMData) where
  /-- The GM-data `G_v ↷ M_v` at each `v ∈ V`. -/
  gm : V → GMData
  /-- Each `G_v ↷ M_v` is abstractly isomorphic to the model. -/
  iso_model : ∀ v, Nonempty (GMIso (gm v) (model v))

variable {model : V → GMData}

/-- **An isomorphism of étale-unit BPSs** ([LANA], Definition 4.1.2(2)): a family of
isomorphisms of GM-data. Its `G`-components are the isomorphism of the étale portions
(`D^⊢`-prime-strips, [LANA], Definition 4.1.1). -/
def EtUnitIso (E E' : EtUnitBPS model) : Type := ∀ v, GMIso (E.gm v) (E'.gm v)

namespace EtUnitIso

/-- The identity. -/
def refl (E : EtUnitBPS model) : EtUnitIso E E := fun _ => GMIso.refl _

/-- The inverse. -/
def symm {E E' : EtUnitBPS model} (e : EtUnitIso E E') : EtUnitIso E' E := fun v => (e v).symm

/-- The composite. -/
def trans {E E' E'' : EtUnitBPS model} (e : EtUnitIso E E') (f : EtUnitIso E' E'') :
    EtUnitIso E E'' := fun v => (e v).trans (f v)

/-- **Any two étale-unit BPSs are isomorphic** (the first step of the proof of [LANA],
Lemma 4.1.7: "we always have an isomorphism of the étale-unit portions"), since both are
abstractly isomorphic to the model. -/
theorem nonempty (E E' : EtUnitBPS model) : Nonempty (EtUnitIso E E') :=
  ⟨fun v => ((E.iso_model v).some).trans ((E'.iso_model v).some.symm)⟩

end EtUnitIso

/-! ### Value-group BPSs -/

/-- **A value-group BPS** ([LANA], Definition 4.1.3) over the index set `V` with bad locus
`bad ⊆ V`: a one-dimensional real vector space `C` with nonzero local pilots `φ_v ∈ C`
whose sum `φ_C = ∑_{v ∈ V^bad} φ_v` over the bad places (the *pilot*) is nonzero. The
orientation of `C` is not recorded (see the module docstring). -/
structure ValBPS (V : Type) (bad : Finset V) where
  /-- The one-dimensional real vector space `C`. -/
  C : Type
  [instAddCommGroup : AddCommGroup C]
  [instModule : Module ℝ C]
  /-- `C` is one-dimensional. -/
  finrank_eq_one : Module.finrank ℝ C = 1
  /-- The local pilots `φ_v ∈ C`. -/
  localPilot : V → C
  /-- The local pilots are nonzero. -/
  localPilot_ne_zero : ∀ v, localPilot v ≠ 0
  /-- The pilot `φ_C = ∑_{v ∈ V^bad} φ_v` is nonzero. -/
  pilot_ne_zero : ∑ v ∈ bad, localPilot v ≠ 0

attribute [instance] ValBPS.instAddCommGroup ValBPS.instModule

namespace ValBPS

variable {bad : Finset V}

/-- **The pilot** `φ_C = ∑_{v ∈ V^bad} φ_v` of a value-group BPS ([LANA], Definition 4.1.3). -/
def pilot (B : ValBPS V bad) : B.C := ∑ v ∈ bad, B.localPilot v

lemma pilot_ne (B : ValBPS V bad) : B.pilot ≠ 0 := B.pilot_ne_zero

/-- The `ℝ`-linear map `⊕_{v ∈ V} ℝ_v → C`, `a_v ↦ a_v·φ_v` ([LANA], (4-3)). -/
noncomputable def sumMap (B : ValBPS V bad) : (V →₀ ℝ) →ₗ[ℝ] B.C :=
  Finsupp.linearCombination ℝ B.localPilot

lemma sumMap_single (B : ValBPS V bad) (v : V) (a : ℝ) :
    B.sumMap (Finsupp.single v a) = a • B.localPilot v :=
  Finsupp.linearCombination_single ℝ a v

/-- **The product formula** `PF(B) ⊆ ⊕_{v ∈ V} ℝ_v` of a value-group BPS: the kernel of
`sumMap` ([LANA], after (4-3)). -/
noncomputable def PF (B : ValBPS V bad) : Submodule ℝ (V →₀ ℝ) := LinearMap.ker B.sumMap

/-- Every nonzero vector spans a one-dimensional space. -/
lemma span_singleton_eq_top (B : ValBPS V bad) {x : B.C} (hx : x ≠ 0) :
    Submodule.span ℝ {x} = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun w => ?_
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' x hx).mp B.finrank_eq_one w
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self x)

/-- `sumMap` is surjective ([LANA], after (4-3)). -/
lemma sumMap_surjective (B : ValBPS V bad) : Function.Surjective B.sumMap := by
  obtain ⟨v, -⟩ : bad.Nonempty := by
    by_contra h
    exact B.pilot_ne_zero (by simp [Finset.not_nonempty_iff_eq_empty.mp h])
  intro w
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ (B.localPilot_ne_zero v)).mp
    B.finrank_eq_one w
  exact ⟨Finsupp.single v c, B.sumMap_single v c⟩

/-- **An isomorphism of value-group BPSs** ([LANA], Definition 4.1.4): an `ℝ`-linear
isomorphism `C ≅ C'` mapping `φ_v` to `φ'_v` for every `v`. -/
structure Iso (B B' : ValBPS V bad) where
  /-- The linear isomorphism `Φ : C ≅ C'`. -/
  toLinearEquiv : B.C ≃ₗ[ℝ] B'.C
  /-- `Φ(φ_v) = φ'_v`. -/
  map_localPilot : ∀ v, toLinearEquiv (B.localPilot v) = B'.localPilot v

namespace Iso

/-- The identity. -/
def refl (B : ValBPS V bad) : Iso B B := ⟨LinearEquiv.refl ℝ B.C, fun _ => rfl⟩

/-- The inverse. -/
def symm {B B' : ValBPS V bad} (e : Iso B B') : Iso B' B :=
  ⟨e.toLinearEquiv.symm, fun v => by
    rw [LinearEquiv.symm_apply_eq, e.map_localPilot]⟩

/-- The composite. -/
def trans {B B' B'' : ValBPS V bad} (e : Iso B B') (f : Iso B' B'') : Iso B B'' :=
  ⟨e.toLinearEquiv.trans f.toLinearEquiv, fun v => by
    rw [LinearEquiv.trans_apply, e.map_localPilot, f.map_localPilot]⟩

/-- An isomorphism maps the pilot to the pilot. -/
lemma map_pilot {B B' : ValBPS V bad} (e : Iso B B') : e.toLinearEquiv B.pilot = B'.pilot := by
  simp only [pilot, map_sum, e.map_localPilot]

/-- An isomorphism intertwines the maps `⊕_v ℝ_v → C` of (4-3). -/
lemma comp_sumMap {B B' : ValBPS V bad} (e : Iso B B') :
    e.toLinearEquiv.toLinearMap ∘ₗ B.sumMap = B'.sumMap := by
  ext v
  simp [sumMap_single, e.map_localPilot]

end Iso

/-- **[LANA], Lemma 4.1.7, for value-group BPSs**: two value-group BPSs are isomorphic if and
only if they have the same product formula. -/
theorem nonempty_iso_iff (B B' : ValBPS V bad) : Nonempty (Iso B B') ↔ B.PF = B'.PF := by
  constructor
  · rintro ⟨e⟩
    rw [PF, PF, ← e.comp_sumMap, LinearEquiv.ker_comp]
  · intro h
    let e : B.C ≃ₗ[ℝ] B'.C :=
      (B.sumMap.quotKerEquivOfSurjective B.sumMap_surjective).symm.trans
        ((Submodule.quotEquivOfEq _ _ h).trans
          (B'.sumMap.quotKerEquivOfSurjective B'.sumMap_surjective))
    refine ⟨⟨e, fun v => ?_⟩⟩
    have h1 : B.localPilot v = B.sumMap (Finsupp.single v 1) := by
      rw [sumMap_single, one_smul]
    have h2 : B'.localPilot v = B'.sumMap (Finsupp.single v 1) := by
      rw [sumMap_single, one_smul]
    rw [h1, h2]
    change (B'.sumMap.quotKerEquivOfSurjective B'.sumMap_surjective)
      ((Submodule.quotEquivOfEq _ _ h)
        ((B.sumMap.quotKerEquivOfSurjective B.sumMap_surjective).symm
          (B.sumMap (Finsupp.single v 1)))) = _
    rw [(LinearEquiv.symm_apply_eq _).mpr
      (B.sumMap.quotKerEquivOfSurjective_apply_mk B.sumMap_surjective _).symm]
    rfl

/-- The local pilots span `C`. -/
lemma span_localPilot (B : ValBPS V bad) : Submodule.span ℝ (Set.range B.localPilot) = ⊤ := by
  rw [eq_top_iff, ← LinearMap.range_eq_top.mpr B.sumMap_surjective, sumMap,
    Finsupp.range_linearCombination]

/-- **Isomorphisms of value-group BPSs are unique**: a linear map is determined by its values
on the local pilots, which span `C`. -/
theorem valIso_subsingleton (B B' : ValBPS V bad) : Subsingleton (Iso B B') := by
  constructor
  rintro ⟨e, he⟩ ⟨f, hf⟩
  have : e = f := LinearEquiv.toLinearMap_injective <|
    LinearMap.ext_on_range B.span_localPilot fun v => by simp [he, hf]
  subst this
  rfl

/-! #### The pointed real line of a value-group BPS ([LANA], Remark 4.1.5, §9.3) -/

/-- The linear equivalence `C ≅ ℝ` sending the pilot to `1`. -/
noncomputable def pilotCoord (B : ValBPS V bad) : B.C ≃ₗ[ℝ] ℝ :=
  (LinearEquiv.ofTop _ (B.span_singleton_eq_top B.pilot_ne)).symm.trans
    (LinearEquiv.toSpanNonzeroSingleton ℝ B.C B.pilot B.pilot_ne).symm

lemma pilotCoord_pilot (B : ValBPS V bad) : B.pilotCoord B.pilot = 1 := by
  unfold pilotCoord
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq,
    LinearEquiv.toSpanNonzeroSingleton_one]
  rfl

/-- **The pointed linear map `η : R_val → ℝ` with `η(φ_C) = x`** ([LANA], §9.2): the
`ℝ`-linear map out of the pointed real line `(C, φ_C)` of a value-group BPS sending the pilot
to `x`. It is an isomorphism iff `x ≠ 0` (`eta_bijective`). -/
noncomputable def eta (B : ValBPS V bad) (x : ℝ) : B.C →ₗ[ℝ] ℝ :=
  x • B.pilotCoord.toLinearMap

@[simp]
lemma eta_pilot (B : ValBPS V bad) (x : ℝ) : B.eta x B.pilot = x := by
  simp [eta, pilotCoord_pilot]

/-- **A linear map out of `(C, φ_C)` is determined by the image of the pilot** ([LANA],
Remark 4.1.5: a value-group BPS is a pointed real line). -/
theorem eta_unique (B : ValBPS V bad) (f : B.C →ₗ[ℝ] ℝ) : f = B.eta (f B.pilot) := by
  refine LinearMap.ext_on (B.span_singleton_eq_top B.pilot_ne) ?_
  intro y hy
  rw [Set.mem_singleton_iff.mp hy, eta_pilot]

/-- Two pointed maps agree iff they send the pilot to the same point. -/
theorem eta_eq_eta_iff (B : ValBPS V bad) (x y : ℝ) : B.eta x = B.eta y ↔ x = y := by
  constructor
  · intro h
    simpa using congrArg (fun f : B.C →ₗ[ℝ] ℝ => f B.pilot) h
  · rintro rfl
    rfl

/-- `η` is an isomorphism of pointed real lines iff the target point is nonzero. -/
theorem eta_bijective (B : ValBPS V bad) {x : ℝ} (hx : x ≠ 0) :
    Function.Bijective (B.eta x) := by
  have : (B.eta x : B.C → ℝ) = (fun t => x * t) ∘ B.pilotCoord := by
    funext y
    simp [eta]
  rw [this]
  exact (mulLeft_bijective₀ x hx).comp B.pilotCoord.bijective

end ValBPS

/-! ### BPSs -/

/-- **A basic prime strip (BPS)** ([LANA], Definition 4.1.6(1)): a pair of an étale-unit BPS
and a value-group BPS. -/
structure BPS (model : V → GMData) (bad : Finset V) where
  /-- The étale-unit portion. -/
  et : EtUnitBPS model
  /-- The value-group portion. -/
  val : ValBPS V bad

namespace BPS

variable {bad : Finset V}

/-- **An isomorphism of BPSs** ([LANA], Definition 4.1.6(2)): an isomorphism of the
étale-unit portions and an isomorphism of the value-group portions. -/
structure Iso (B B' : BPS model bad) where
  /-- The isomorphism of the étale-unit portions. -/
  et : EtUnitIso B.et B'.et
  /-- The isomorphism of the value-group portions. -/
  val : ValBPS.Iso B.val B'.val

namespace Iso

/-- The identity. -/
def refl (B : BPS model bad) : Iso B B := ⟨EtUnitIso.refl _, ValBPS.Iso.refl _⟩

/-- The inverse. -/
def symm {B B' : BPS model bad} (e : Iso B B') : Iso B' B := ⟨e.et.symm, e.val.symm⟩

/-- The composite. -/
def trans {B B' B'' : BPS model bad} (e : Iso B B') (f : Iso B' B'') : Iso B B'' :=
  ⟨e.et.trans f.et, e.val.trans f.val⟩

end Iso

/-- **[LANA], Lemma 4.1.7**: two BPSs are isomorphic if and only if their value-group portions
have the same product formula. -/
theorem nonempty_iso_iff (B B' : BPS model bad) : Nonempty (Iso B B') ↔ B.val.PF = B'.val.PF := by
  rw [← ValBPS.nonempty_iso_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨e.val⟩
  · rintro ⟨f⟩
    exact ⟨⟨(EtUnitIso.nonempty _ _).some, f⟩⟩

/-- **[LANA], Remark 8.2.1: the BPSs with a given product formula form a connected groupoid**
(identities, inverses and composites: `Iso.refl`, `Iso.symm`, `Iso.trans`): any two are
isomorphic. Hence "the BPSs `B` and `B'` are linked", in the sense that an isomorphism exists,
is a vacuous assertion for them. -/
theorem connected {P : Submodule ℝ (V →₀ ℝ)} (B B' : BPS model bad) (hB : B.val.PF = P)
    (hB' : B'.val.PF = P) : Nonempty (Iso B B') :=
  (nonempty_iso_iff B B').mpr (hB.trans hB'.symm)

end BPS

end Wall

end Iut
