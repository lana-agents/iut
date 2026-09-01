/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib

/-!
# Direct-sum-of-fields presentations of tensor-packets (taxis #43, #45)

A local tensor-packet of log-shells (IUT III, Propositions 3.1–3.3) is, at each rational
place `v_Q` and each capsule `S` of the procession, the tensor product over `j ∈ S` of
direct sums over `v ∣ v_Q` of local fields. As a module with integral structure this
tensor product is **presented as a finite direct sum of fields**, each summand carrying
its holomorphic integral structure `O`; IUT III, Remark 3.9.5 phrases the holomorphic
hull entirely in terms of such a presentation.

This module fixes that presentation as an interface: a finite family of (topological)
fields, one for each *component* of the packet, together with an integral structure in
each summand. It also defines the region classes on the total space that the later
modules operate on:

* arbitrary regions (`Set` of the total space), with Borel-measurable regions singled
  out via `IsBorelRegion`;
* direct-product [pre-]regions (`IsProductRegion`), the class from which the log-volume
  combination laws of taxis #44 are stated;
* the scaled-integral regions `a·O` with every component of `a` nonzero
  (`IsHullRegion`), among which the holomorphic hull of taxis #45 is the least one.

## Honesty boundary

The identification of an actual tensor-packet `⊗_{j ∈ S} (⊕_{v ∣ v_Q} log(F_v))` with a
direct sum of fields (semisimple decomposition of tensor products of local fields) is
**not** proved here; it is part of the local-field infrastructure tracked in taxis #4
(`lana-agents/padic-log-volume`). This module only fixes the interface through which the
container consumes such a presentation; every instantiation obligation is an explicit
structure field of the container data (taxis #43).

## Source correspondence

* Presentation as a direct sum of fields with integral structure `O`: IUT III,
  Remark 3.9.5, first display and part (i).
* Direct-product [pre-]regions vs arbitrary (measurable) regions: IUT III,
  Proposition 3.9 and Remark 3.9.5(ii).
-/

open scoped Pointwise

namespace Iut

universe u v

/-- A **direct-sum-of-fields presentation** with integral structures: for each component
`c` of a finite index type `C`, a topological field `Summand c` with a designated
integral structure `integral c` (the *holomorphic integral structure* `O` of the
summand).

In the intended instantiation `C` is the set of tuples `(v_j)_{j ∈ S}` of places
`v_j ∣ v_Q` indexed by the labels of a capsule `S`, and `Summand c` is the corresponding
tensor factor field of the semisimple decomposition of the tensor-packet
(IUT III, Remark 3.9.5). -/
structure DirectSumPresentation (C : Type u) : Type (max u (v + 1)) where
  /-- The summand field at component `c`. -/
  Summand : C → Type v
  /-- Each summand is a commutative ring: a field, or — for the tensor products of
  local fields that present the tensor-packets (IUT III, Proposition 3.1) — a finite
  product of fields. Nonzero components of hull regions are accordingly *units*. -/
  [ring_summand : ∀ c, CommRing (Summand c)]
  /-- Each summand carries a topology (used for the relative-compactness hypotheses of
  the holomorphic hull, taxis #45). -/
  [topology_summand : ∀ c, TopologicalSpace (Summand c)]
  /-- The holomorphic integral structure `O` of each summand: the ring of integers of a
  nonarchimedean summand (a subring), the unit ball of an archimedean one (a subset,
  IUT IV, Proposition 1.5(iii)). Carried as a set so that both cases are covered. -/
  integral : ∀ c, Set (Summand c)

attribute [instance] DirectSumPresentation.ring_summand
  DirectSumPresentation.topology_summand

namespace DirectSumPresentation

variable {C : Type u} (P : DirectSumPresentation.{u, v} C)

/-- The total space of a direct-sum-of-fields presentation. Since the component index is
finite in every intended instantiation, the direct sum is the plain dependent product. -/
def Total : Type (max u v) := ∀ c, P.Summand c

instance : TopologicalSpace P.Total := inferInstanceAs (TopologicalSpace (∀ c, P.Summand c))

/-- The holomorphic integral region `⊕_c O_c` of the presentation: the set of vectors
with every component in the integral structure of its summand. -/
def integralRegion : Set P.Total := {x | ∀ c, x c ∈ P.integral c}

@[simp]
lemma mem_integralRegion {x : P.Total} : x ∈ P.integralRegion ↔ ∀ c, x c ∈ P.integral c :=
  Iff.rfl

/-- A **direct-product [pre-]region**: a region of the total space which is the product
of one region in each summand field (IUT III, Remark 3.9.5(ii) distinguishes these from
arbitrary regions). -/
def IsProductRegion (R : Set P.Total) : Prop :=
  ∃ U : ∀ c, Set (P.Summand c), R = {x | ∀ c, x c ∈ U c}

/-- The product region attached to a family of component regions. -/
def productRegion (U : ∀ c, Set (P.Summand c)) : Set P.Total := {x | ∀ c, x c ∈ U c}

@[simp]
lemma mem_productRegion {U : ∀ c, Set (P.Summand c)} {x : P.Total} :
    x ∈ P.productRegion U ↔ ∀ c, x c ∈ U c := Iff.rfl

lemma isProductRegion_productRegion (U : ∀ c, Set (P.Summand c)) :
    P.IsProductRegion (P.productRegion U) := ⟨U, rfl⟩

lemma isProductRegion_integralRegion : P.IsProductRegion P.integralRegion :=
  ⟨fun c => P.integral c, rfl⟩

/-- A region of the total space is a **Borel region** if it is measurable for the Borel
σ-algebra of the product topology. This is the class "arbitrary measurable subsets"
of taxis #43, kept distinct from the direct-product [pre-]regions. -/
def IsBorelRegion (R : Set P.Total) : Prop := @MeasurableSet P.Total (borel P.Total) R

/-- The scaled integral region `a · O`: the set of vectors whose `c`-component lies in
`a c • O_c` for every component `c`. For `a` with every component nonzero these are the
candidate holomorphic hulls of IUT III, Remark 3.9.5(i). -/
def scaledIntegral (a : P.Total) : Set P.Total :=
  {x | ∀ c, x c ∈ a c • P.integral c}

@[simp]
lemma mem_scaledIntegral {a x : P.Total} :
    x ∈ P.scaledIntegral a ↔ ∀ c, x c ∈ a c • P.integral c :=
  Iff.rfl

lemma isProductRegion_scaledIntegral (a : P.Total) :
    P.IsProductRegion (P.scaledIntegral a) :=
  ⟨fun c => a c • P.integral c, rfl⟩

@[simp]
lemma scaledIntegral_one : P.scaledIntegral (fun _ => 1) = P.integralRegion := by
  ext x
  simp [scaledIntegral, integralRegion]

/-- A **hull region**: a region of the form `a · O` with every component of `a` a
unit — nonzero in every field factor (IUT III, Remark 3.9.5(i)). The holomorphic hull
of a region `U` is the least hull region containing `U`; see `Iut.HullSystem`. -/
def IsHullRegion (R : Set P.Total) : Prop :=
  ∃ a : P.Total, (∀ c, IsUnit (a c)) ∧ R = P.scaledIntegral a

lemma isHullRegion_integralRegion : P.IsHullRegion P.integralRegion :=
  ⟨fun _ => 1, fun _ => isUnit_one, (P.scaledIntegral_one).symm⟩

end DirectSumPresentation

end Iut
