/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Iut.Concrete.ThetaRegion
import Iut.Abc.FormalConjectures

/-!
# Comparator solution: the Corollary 3.12 variant implies formal-conjectures' `ABC.abc`

The challenge statement, proved by `Iut.formalConjecturesABC_of_variant`
(`Iut/Abc/FormalConjectures.lean`), which derives `FormalConjecturesABC.abc` from the main
theorem `Iut.classicalABC_of_variant`. The definitions `ABC.radical` and `ABC` are the
challenge's, character for character (the comparator compares them, values included).
`ABC.radical` has the same body as the project's verbatim copy `FormalConjecturesABC.radical`,
and `ABC` is the body of `FormalConjecturesABC.abc` with `ABC.radical` in place of
`FormalConjecturesABC.radical`, so the two agree by unfolding definitions.

The definition `ABC.radical` and the body of `ABC` are copied from
google-deepmind/formal-conjectures
(`FormalConjectures/Wikipedia/ABC.lean`, commit `1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89`),
"Copyright 2025 The Formal Conjectures Authors", under the Apache License, Version 2.0; see
`Comparator/Challenge.lean` for the full notice.
-/

namespace ABC

/--
The radical of `n` denoted is the product of the distinct prime factors of `n`.
-/
def radical (n : ℕ) : ℕ := n.primeFactors.prod id

end ABC

open ABC in
/-- The ABC conjecture as stated by formal-conjectures (`ABC.abc`, verbatim body). -/
def ABC : Prop := ∀ ε : ℝ, 0 < ε →
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
    a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c}.Finite

/-- **The Corollary 3.12 variant implies the ABC conjecture as stated by formal-conjectures
(`ABC.abc`).** -/
-- `_root_.ABC`: inside `Iut.abc_of_cor312Variant` the namespace `Iut` is open, and the
-- Solution's imports contain the unrelated `Iut.ABC` (`Iut/Abc/Target.lean`), which `ABC` would
-- denote. The Challenge does not import it, so there `ABC` already denotes `_root_.ABC`.
theorem Iut.abc_of_cor312Variant : Iut.Cor312VariantHolds → _root_.ABC :=
  Iut.formalConjecturesABC_of_variant
