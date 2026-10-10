/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Iut.Concrete.ThetaRegion

/-!
# Comparator challenge: the Corollary 3.12 variant implies formal-conjectures' `ABC.abc`

The single target `Iut.abc_of_cor312Variant` says that the hypothesis of the main theorem of
the project implies the **official** statement of the ABC conjecture of
google-deepmind/formal-conjectures, the theorem `ABC.abc` of
`FormalConjectures/Wikipedia/ABC.lean` at commit `1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89`:
<https://github.com/google-deepmind/formal-conjectures/blob/1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89/FormalConjectures/Wikipedia/ABC.lean>.

* The hypothesis is `Iut.Cor312VariantHolds`, i.e.
  `∀ D : Iut.InitialThetaData.{0}, Iut.Corollary312Variant (Iut.concreteVariantData D)`
  (`Iut/Concrete/ThetaRegion.lean`).
* The conclusion is the statement of their `ABC.abc`, verbatim: their arguments
  `(ε : ℝ) (hε : 0 < ε)` are written `∀ ε : ℝ, 0 < ε →`, and everything else (the
  set-builder, the pairwise coprimality, the coercions) is theirs, unchanged. It uses their
  definition `ABC.radical`, which is copied here verbatim (same name, docstring and body).

The copied code (the definition `ABC.radical` and the statement of `ABC.abc`) is
"Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file
except in compliance with the License. You may obtain a copy of the License at
<https://www.apache.org/licenses/LICENSE-2.0>. Unless required by applicable law or agreed to
in writing, software distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for
the specific language governing permissions and limitations under the License."

## Trusted vocabulary

Besides the Mathlib module `Mathlib.Analysis.SpecialFunctions.Pow.Real` (for `Real.rpow`; its
closure also provides `Set.Finite`, `Set.Pairwise`, `Nat.Coprime` and `Nat.primeFactors`), the
only import is `Iut.Concrete.ThetaRegion`, the module that defines
`Iut.Cor312VariantHolds`. Its import closure consists of the modules that define the
statement vocabulary of the hypothesis (the initial Θ-data with the genuine étale and
tempered fundamental groups from `pi1` and `tempered-fundamental-groups`, the tensor packets
with their log-shells, log-volumes and hulls, the theta-pilot region, the variant
inequality). None of the modules that prove the implication (`Iut.MainTheorem`,
`Iut.Tripod`, `Iut.Implication`, `Iut.Abc`, ...) is imported;
`scripts/AuditComparatorChallenge.lean` checks this, and that no declaration of the trusted
closure refers to `sorryAx` or to non-standard axioms.

The comparator compares every definition the statement uses, `ABC.radical` included, between
Challenge and Solution (it is not a definition hole), so the Solution declares the identical
definition.
-/

namespace ABC

/--
The radical of `n` denoted is the product of the distinct prime factors of `n`.
-/
def radical (n : ℕ) : ℕ := n.primeFactors.prod id

end ABC

namespace Iut

open ABC

/-- **The Corollary 3.12 variant implies the ABC conjecture as stated by formal-conjectures
(`ABC.abc`).** -/
theorem abc_of_cor312Variant :
    Cor312VariantHolds → ∀ ε : ℝ, 0 < ε →
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
    a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c}.Finite := by
  sorry

end Iut
