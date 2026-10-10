/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Radical.NatInt
import Iut.Concrete.ThetaRegion
import Iut.MainTheorem

/-!
# Comparator solution: the Corollary 3.12 variant implies the classical ABC conjecture

The challenge statement, proved by the main theorem `Iut.classicalABC_of_variant`. The
challenge spells `Iut.ClassicalABC` out; the two statements agree by unfolding that
definition, so the main theorem is the proof term as it stands.
-/

namespace Iut

/-- **The Corollary 3.12 variant implies the classical ABC conjecture.** -/
theorem classicalABC_of_cor312Variant :
    Cor312VariantHolds →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ C * ((UniqueFactorizationMonoid.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε) :=
  classicalABC_of_variant

end Iut
