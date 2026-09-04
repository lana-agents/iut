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

end Place

/-- The **lies over** relation between finite places of an extension `K/k`: the prime of
`𝓞_K` attached to `w` lies over the prime of `𝓞_k` attached to `v` (`Ideal.LiesOver`; the
normalized absolute value of `w` restricts to a *power* of that of `v`, so the relation
is stated on the primes). -/
def FinitePlace.LiesOver {K : Type*} [Field K] [NumberField K] [Algebra k K]
    (w : FinitePlace K) (v : FinitePlace k) : Prop :=
  w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal

namespace Place

/-- The **lies over** relation between a place of an extension `K/k` and a place of
`k`: on finite places the prime-ideal relation `Iut.FinitePlace.LiesOver`, on infinite
places the restriction of the absolute value (`AbsoluteValue.LiesOver`); a finite and an
infinite place never lie over each other. -/
def LiesOver {K : Type*} [Field K] [NumberField K] [Algebra k K] :
    Place K → Place k → Prop
  | Sum.inl w, Sum.inl v => FinitePlace.LiesOver w v
  | Sum.inr w, Sum.inr v => w.1.LiesOver v.1
  | _, _ => False

end Place

/-- The residue characteristic of a finite place: the characteristic of its residue
field. For a place over the rational prime `p` this is `p`. -/
noncomputable def residueChar (w : FinitePlace k) : ℕ :=
  ringChar (𝓞 k ⧸ w.maximalIdeal.asIdeal)

/-- The residue characteristic of a finite place of a number field is prime. -/
lemma residueChar_prime (w : FinitePlace k) : (residueChar w).Prime := by
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  letI : Field (𝓞 k ⧸ w.maximalIdeal.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 k ⧸ w.maximalIdeal.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ w.maximalIdeal.ne_bot
  exact CharP.char_is_prime (𝓞 k ⧸ w.maximalIdeal.asIdeal) (ringChar _)

end Iut
