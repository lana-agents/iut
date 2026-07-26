/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib

/-!
# Places of number fields for the Θ-data modules (taxis #39–#42)

Small helper layer over Mathlib's `NumberField.FinitePlace` and
`NumberField.InfinitePlace`: the combined type `Iut.Place` of all places `V(k)`, the
residue characteristic of a finite place, and the "lies over" relation between places
of an extension, all used by the initial Θ-data modules (IUT I, Definition 3.1).
-/

namespace Iut

open NumberField

variable (k : Type*) [Field k] [NumberField k]

/-- The set of places `V(k)` of a number field: finite (nonarchimedean) places and
infinite (archimedean) places (IUT I, Definition 3.1(b): `V_mod = V(F_mod)`). -/
def Place : Type _ := FinitePlace k ⊕ InfinitePlace k

variable {k}

namespace Place

/-- The nonarchimedean place attached to a finite place. -/
def finite (w : FinitePlace k) : Place k := Sum.inl w

/-- The archimedean place attached to an infinite place. -/
def infinite (w : InfinitePlace k) : Place k := Sum.inr w

/-- A place is nonarchimedean if it comes from a finite place. -/
def IsFinite : Place k → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- The underlying absolute value of a place. -/
def absoluteValue : Place k → AbsoluteValue k ℝ :=
  Sum.elim Subtype.val Subtype.val

/-- The **lies over** relation between a place of an extension `K/k` and a place of
`k`, via Mathlib's `AbsoluteValue.LiesOver` on the underlying absolute values. -/
def LiesOver {K : Type*} [Field K] [NumberField K] [Algebra k K]
    (w : Place K) (v : Place k) : Prop :=
  w.absoluteValue.LiesOver v.absoluteValue

end Place

/-- The residue characteristic of a finite place: the characteristic of its residue
field. For a place over the rational prime `p` this is `p`. -/
noncomputable def residueChar (w : FinitePlace k) : ℕ :=
  ringChar (𝓞 k ⧸ w.maximalIdeal.asIdeal)

end Iut
