/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Radical.NatInt
import Iut.Concrete.ThetaRegion

/-!
# Comparator challenge: the Corollary 3.12 variant implies the classical ABC conjecture

The single target `Iut.classicalABC_of_cor312Variant` is the main theorem of the project
(`Iut.classicalABC_of_variant` in `Iut/MainTheorem.lean`):

* the hypothesis is `Iut.Cor312VariantHolds`, i.e.
  `∀ D : Iut.InitialThetaData.{0}, Iut.Corollary312Variant (Iut.concreteVariantData D)`
  (`Iut/Concrete/ThetaRegion.lean`);
* the conclusion is the classical ABC conjecture of Masser and Oesterlé, spelled out here in
  plain Mathlib terms: for every `ε > 0` there is a real `C` such that
  `c ≤ C · rad(abc)^{1+ε}` for all coprime positive integers `a`, `b` with `a + b = c`.
  It is, symbol for symbol, the body of the project definition `Iut.ClassicalABC`
  (`Iut/Abc/Classical.lean`), which this module does not import.

## Trusted vocabulary

Besides the two Mathlib modules for `Real.rpow` and `UniqueFactorizationMonoid.radical` on
`ℕ`, the only import is `Iut.Concrete.ThetaRegion`, the module that defines
`Iut.Cor312VariantHolds`. Its import closure consists of the modules that define the
statement vocabulary (the initial Θ-data with the genuine étale and tempered fundamental
groups from `pi1` and `tempered-fundamental-groups`, the tensor packets with their
log-shells, log-volumes and hulls, the theta-pilot region, the variant inequality). None of
the modules that prove the implication (`Iut.MainTheorem`, `Iut.Tripod`, `Iut.Implication`,
`Iut.Abc`, ...) is imported; `scripts/AuditComparatorChallenge.lean` checks this, and that no
declaration of the trusted closure refers to `sorryAx` or to non-standard axioms.
-/

namespace Iut

/-- **The Corollary 3.12 variant implies the classical ABC conjecture.** -/
theorem classicalABC_of_cor312Variant :
    Cor312VariantHolds →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ C * ((UniqueFactorizationMonoid.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε) := by
  sorry

end Iut
