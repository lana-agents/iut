/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Model
import Iut.Cor312.ThetaData.TateStructure

/-!
# The local predicates of the model (taxis #279)

Over a complete rank-one valued field `k` and relative to a Tate structure
`S : Iut.TateStructure X.E` on the underlying curve (a pinned Tate uniformization), the
model orbicurve `X = (E, ℓ, M, ±)` is

* of **type `(1, ℤ/ℓℤ)^±`** (*Étale Theta*, Definition 2.5) if `ℓ` is prime, the level is
  `ℓ` and `M` is the **graph line** `μ_ℓ ⊆ E(k)[ℓ]` of `S` — the kernel of the graph
  quotient `E[ℓ] → E[ℓ]/μ_ℓ ≅ ℤ/ℓℤ` (the quotient of the tempered fundamental group of
  the Tate curve corresponding to the dual graph of its special fibre), so that the cover
  `X_M → X` is the one attached to the graph quotient;
* a **theta-root model** (*Étale Theta*, Definition 2.5): in the model, the natural model
  `X̲` obtained by extracting an ℓ-th root of the theta function is again the orbicurve of
  type `(1, ℤ/ℓℤ)^±` attached to the graph quotient (the identification with the
  Kummer-theoretic description of *Étale Theta* is the documented correspondence of
  taxis #279);

and its **canonical graph cusp** is the cusp of a canonical generator `±q^{1/ℓ}` of the
graph quotient (`Iut.TateStructure.IsCanonical`), or `0` if there is none.
-/

namespace Iut.Anabelian

universe u

open WeierstrassCurve
open scoped Classical

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

namespace Orbicurve

/-- **Type `(1, ℤ/ℓℤ)^±`** relative to a Tate structure: level a prime `ℓ` and `M` the graph
line `μ_ℓ`. The `±`-flag is not constrained: both `X̲` and `C̲ = X̲/±` of the Θ-data are
required to be of this type at the bad places. -/
def IsTypeOneZModPM (ℓ : ℕ) (X : Orbicurve k) (S : TateStructure X.E) : Prop :=
  ℓ.Prime ∧ X.level = ℓ ∧ X.M = S.graphLine ℓ ∧ Nat.card X.M = ℓ

/-- **Theta-root models** (*Étale Theta*, Definition 2.5), in the model: the orbicurve of
type `(1, ℤ/ℓℤ)^±` attached to the graph quotient of the Tate structure. -/
def IsThetaRootModel (ℓ : ℕ) (X : Orbicurve k) (S : TateStructure X.E) : Prop :=
  IsTypeOneZModPM ℓ X S

/-- **The canonical graph cusp**: the cusp of a canonical generator `±q^{1/ℓ}` of the graph
quotient (`0` if there is none). -/
noncomputable def canonicalGraphCusp (X : Orbicurve k) (S : TateStructure X.E) : X.Cusp :=
  if h : ∃ P : ↥X.torsion, S.IsCanonical X.level P.1 then X.cuspOf (X.toQ h.choose)
  else X.cuspOf 0

end Orbicurve

end Iut.Anabelian
