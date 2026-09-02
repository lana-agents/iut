/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Model
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# The local predicates of the model (taxis #279)

Over a valued field `k` (a `Valued k ℤᵐ⁰` structure, e.g. an adic completion of a number
field), this module defines, from **minimal Weierstrass models**:

* `Iut.Anabelian.ReducesToZero E P`: the point `P ∈ E(k)` reduces to the identity of the
  special fibre — in every minimal model of `E` its `x`-coordinate is non-integral;
* `Iut.Anabelian.graphLine E ℓ`: the **graph line** `E(k)[ℓ] ∩ E₁(k)`, the ℓ-torsion of
  the kernel of reduction. For `E` with split multiplicative reduction and Tate parameter
  `q` this is `μ_ℓ ⊆ k^×/q^ℤ`, the kernel of the **graph quotient**
  `E[ℓ] → E[ℓ]/μ_ℓ ≅ ℤ/ℓℤ` of *The Étale Theta Function*, Definitions 2.3–2.5 (the
  quotient of the tempered fundamental group corresponding to the dual graph of the
  special fibre);
* `Iut.Anabelian.IsCanonicalGenerator E ℓ P`: `P` is an ℓ-torsion point lying on the
  component `±v(q)/ℓ` of the special fibre — `ℓ·v(x(P)) = -v(j(E))` in every minimal
  model — i.e. `P` is an ℓ-th root `q^{±1/ℓ}` of the Tate parameter modulo `μ_ℓ`: the
  **canonical generators `±1` of the graph quotient**;
* `Iut.Anabelian.HasSplitMultiplicativeReduction E`: some model of `E` is minimal with
  split multiplicative reduction (Mathlib's predicate).

On the model orbicurves this gives the type `(1, ℤ/ℓℤ)^±` (*Étale Theta*, Definition 2.5:
`M` is the graph line), the theta-root models (the natural model `X̲` obtained by
extracting an ℓ-th root of the theta function is the cover attached to the graph
quotient, i.e. again `M` = graph line; the identification with the Kummer-theoretic
description of *Étale Theta* is the residual content of taxis #279), and the canonical
graph cusp (the cusp of a canonical generator).

The statements *about* these definitions needed by the existence of initial Θ-data —
that the graph line has order `ℓ` at a place of split multiplicative reduction with
`ℓ ∤ v(q)`, its Galois equivariance, and the characterization of the canonical
generators — are the reduction-theoretic inputs of `Iut.Anabelian.Existence`.
-/

namespace Iut.Anabelian

universe u

open WeierstrassCurve
open scoped Classical

section Valued

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]

/-- The `x`-coordinate of an affine point in the model `C • E`
(`(X, Y) ↦ (u²X + r, …)`, so the transformed coordinate is `(x - r)/u²`); `0` for the
point at infinity. -/
def xCoord (C : VariableChange k) : {E : WeierstrassCurve k} → E.toAffine.Point → k
  | _, Affine.Point.zero => 0
  | _, Affine.Point.some x _ _ => (x - C.r) / (C.u : k) ^ 2

/-- **`P` reduces to the identity**: in every minimal model of `E` (with respect to the
valuation ring `𝒪[k]`, assumed a discrete valuation ring with fraction field `k`), the
`x`-coordinate of `P` is non-integral (or `P = 0`). -/
def ReducesToZero (E : WeierstrassCurve k) (P : E.toAffine.Point) : Prop :=
  ∀ (h₁ : IsDiscreteValuationRing (Valued.integer k))
    (h₂ : IsFractionRing (Valued.integer k) k) (C : VariableChange k),
    (letI := h₁; letI := h₂; (C • E).IsMinimal (Valued.integer k)) →
    (P = 0 ∨ 1 < Valued.v (xCoord C P))

/-- **The graph line** `E(k)[ℓ] ∩ E₁(k)`: the ℓ-torsion points reducing to the identity. -/
def graphLine (E : WeierstrassCurve k) (ℓ : ℕ) : Set E.toAffine.Point :=
  {P | P ∈ AddSubgroup.torsionBy E.toAffine.Point ℓ ∧ ReducesToZero E P}

/-- **Canonical generators of the graph quotient**: ℓ-torsion points `P ≠ 0` with
`ℓ·v(x(P)) = -v(j(E))` in every minimal model — the ℓ-th roots `q^{±1/ℓ}` of the Tate
parameter modulo the graph line. -/
def IsCanonicalGenerator (E : WeierstrassCurve k) [E.IsElliptic] (ℓ : ℕ)
    (P : E.toAffine.Point) : Prop :=
  P ∈ AddSubgroup.torsionBy E.toAffine.Point ℓ ∧ P ≠ 0 ∧
    ∀ (h₁ : IsDiscreteValuationRing (Valued.integer k))
      (h₂ : IsFractionRing (Valued.integer k) k) (C : VariableChange k),
      (letI := h₁; letI := h₂; (C • E).IsMinimal (Valued.integer k)) →
      Valued.v (xCoord C P) ^ ℓ * Valued.v E.j = 1

/-- **Split multiplicative reduction**: some model of `E` is minimal with split
multiplicative reduction over `𝒪[k]`. -/
def HasSplitMultiplicativeReduction (E : WeierstrassCurve k) : Prop :=
  ∃ (h₁ : IsDiscreteValuationRing (Valued.integer k))
    (h₂ : IsFractionRing (Valued.integer k) k) (C : VariableChange k),
    letI := h₁; letI := h₂; (C • E).HasSplitMultiplicativeReduction (Valued.integer k)

namespace Orbicurve

/-- **Type `(1, ℤ/ℓℤ)^±`** (*Étale Theta*, Definition 2.5) for a model orbicurve over a
valued field: level a prime `ℓ`, `E` with split multiplicative reduction, `M ⊆ E(k)[ℓ]` of
order `ℓ` equal to the graph line (so the cover `X_M → X` is the one attached to the
graph quotient). The `±`-flag is not constrained: both `X̲` and `C̲ = X̲/±` of the Θ-data
are required to be of this type at the bad places. -/
def IsTypeOneZModPM (ℓ : ℕ) (X : Orbicurve k) : Prop :=
  ℓ.Prime ∧ X.level = ℓ ∧ HasSplitMultiplicativeReduction X.E ∧
    (X.M : Set X.E.toAffine.Point) = graphLine X.E ℓ ∧ Nat.card X.M = ℓ

/-- **Theta-root models** (*Étale Theta*, Definition 2.5): in the model, the natural
model obtained by extracting an ℓ-th root of the theta function is the orbicurve of type
`(1, ℤ/ℓℤ)^±` attached to the graph quotient. -/
def IsThetaRootModel (ℓ : ℕ) (X : Orbicurve k) : Prop := IsTypeOneZModPM ℓ X

open scoped Classical in
/-- **The canonical graph cusp**: the cusp of a canonical generator `±1` of the graph
quotient (`0` if there is none). -/
noncomputable def canonicalGraphCusp (X : Orbicurve k) : X.Cusp :=
  if h : ∃ P : ↥X.torsion, IsCanonicalGenerator X.E X.level P.1 then X.cuspOf (X.toQ h.choose)
  else X.cuspOf 0

end Orbicurve

end Valued

end Iut.Anabelian
