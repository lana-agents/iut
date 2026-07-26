/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib

/-!
# Rational places (taxis #43)

The index set `V_Q = V(ℚ)` of rational places used by the large volume container of the
Corollary 3.12 variant (taxis #33): one nonarchimedean place for each rational prime `p`,
and the unique archimedean place `∞`.

The container of taxis #43 keeps its data indexed by `v_Q ∈ V_Q` throughout — the
`v_Q`-level direct-sum decomposition of the tensor-packets must not be collapsed — so
this small module fixes the indexing type once and for all.

## Source correspondence

`V_Q := V(ℚ)` as in IUT I, Definition 3.1(e), and the `v_Q`-indexed tensor-packets of
IUT III, Propositions 3.1–3.3.
-/

namespace Iut

/-- A place of `ℚ`: either the nonarchimedean place attached to a rational prime `p`,
or the archimedean place `∞`. This is the index set `V_Q` of the `v_Q`-indexed local
tensor-packets of IUT III, Propositions 3.1–3.3. -/
inductive RationalPlace : Type
  /-- The nonarchimedean place of `ℚ` attached to the rational prime `p`. -/
  | finite (p : Nat.Primes) : RationalPlace
  /-- The archimedean place of `ℚ`. -/
  | infinite : RationalPlace
  deriving DecidableEq

namespace RationalPlace

/-- A rational place is nonarchimedean if it is attached to a rational prime. -/
def IsFinite : RationalPlace → Prop
  | finite _ => True
  | infinite => False

/-- The residue characteristic of a nonarchimedean rational place, and (by the junk
convention, documented here) `0` at the archimedean place. -/
def residueChar : RationalPlace → ℕ
  | finite p => p
  | infinite => 0

@[simp] lemma residueChar_finite (p : Nat.Primes) : (finite p).residueChar = p := rfl

@[simp] lemma residueChar_infinite : (infinite).residueChar = 0 := rfl

end RationalPlace

end Iut
