/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.ModelFrobenioid
import TemperedFundamentalGroups.Tempered.Category

/-!
# Tempered Frobenioids: the shape ([EtTh] §3)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*,
§3 (Definitions 3.1, 3.3, 3.6, Theorem 3.7). For a hyperbolic orbicurve `X^log` over a
`p`-adic field with split stable reduction (in IUT: the Tate orbicurves `X_v`, `v ∈ V^bad`) and
a tempered filter `Δ^fil` on `Δ^tp_X`:

* the base category `D₀ = B^temp(Π^tp_X)⁰` is the category of connected tempered coverings
  `Y^log → X^log`;
* `Φ₀(Y^log) = lim Div⁺(Z^log_∞)^{Gal(Z_∞/Y)}`, the (Galois-invariant) effective Cartier
  log-divisors on the universal combinatorial coverings `Z^log_∞` of the `Δ^fil`-closures
  (divisors supported on the special fibre and the cusps), a divisorial monoid
  ([EtTh], Proposition 3.4(i));
* `B₀(Y^log) = lim Mero(Z^log_∞)^{Gal(Z_∞/Y)}`, the log-meromorphic functions, with
  `B₀ → Φ₀^gp` the divisor of zeroes and poles;

and the **tempered Frobenioid** is the model Frobenioid `C₀` of `(D₀, Φ₀, B₀)` ([EtTh],
Definition 3.6, Theorem 3.7 — "the Frobenioid `C₀` of model type").

## What is formalised

`TemperedFrobenioidData O R A` is an **interface**: it records `D₀` together with a fully
faithful realization functor into the tempered category `TempObj O R A` of the dependency
`tempered-fundamental-groups` (`Tempered/Category.lean`: tempered coverings of `[Spec R / A]`
presented through integral models), the monoids `Φ₀`, `B₀` and the divisor map, and the two
category-theoretic hypotheses of [FrdI], Definition 1.1(iv) on `D₀` (connected, totally
epimorphic). From these data the tempered Frobenioid is the model Frobenioid
(`TemperedFrobenioidData.Frob`), and it **is a Frobenioid** (`isFrobenioid`, by [FrdI], Theorem
5.2(ii)).

What is *not* constructed (and is the reason for the interface): the subcategory of connected
objects of `TempObj O R A` and its total epimorphicity; stable models of the universal
combinatorial coverings `Z^log_∞` (the dependency works with projective models of finite levels
and covering spaces of special fibres, not with log-divisors on `Z^log_∞`); the monoids
`Φ₀`, `B₀`; the theta function `Θ̈ ∈ B₀` of [EtTh], Proposition 1.4 and Theorem 5.10.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory TemperedFundamentalGroups

universe u

variable {K : Type u} [Field K] (O : ValuationSubring K)
  (R : Type u) [CommRing R] [Algebra K R] (A : Type u) [Group A] [MulSemiringAction A R]

/-- **The data of a tempered Frobenioid** ([EtTh], Definitions 3.3, 3.6), as an interface. -/
structure TemperedFrobenioidData where
  /-- The base category `D₀ = B^temp(Π^tp_X)⁰` of connected tempered coverings. -/
  D₀ : Type u
  [cat : Category.{u} D₀]
  /-- Its realization in the tempered category of `[Spec R / A]`. -/
  realize : D₀ ⥤ TempObj O R A
  realize_fullyFaithful : realize.FullyFaithful
  /-- `D₀` is connected and totally epimorphic ([FrdI], Definition 1.1(iv)). -/
  connected : IsConnected D₀
  epi : TotallyEpimorphic D₀
  /-- The divisor monoid `Φ₀` of effective log-divisors. -/
  Φ₀ : DivMonoid.{u} D₀
  /-- The rational function monoid `B₀` of log-meromorphic functions. -/
  B₀ : GrpOn.{u} D₀
  /-- The divisor of zeroes and poles `B₀ → Φ₀^gp`. -/
  div₀ : DivHom B₀ Φ₀.toGrpOn

attribute [instance] TemperedFrobenioidData.cat

namespace TemperedFrobenioidData

variable {O R A} (T : TemperedFrobenioidData O R A)

/-- **The tempered Frobenioid** `C₀` ([EtTh], Definition 3.6): the model Frobenioid of
`(D₀, Φ₀, B₀)`. -/
abbrev Frob : Type u := Model T.Φ₀ T.B₀ T.div₀

/-- **The tempered Frobenioid is a Frobenioid** ([EtTh], Theorem 3.7; [FrdI], Theorem
5.2(ii)). -/
theorem isFrobenioid : IsFrobenioid (Model.toElem T.Φ₀ T.B₀ T.div₀) :=
  haveI := T.connected
  haveI := T.epi
  Model.isFrobenioid

/-- The projection of the tempered Frobenioid to the tempered category of `[Spec R / A]`. -/
noncomputable def toTemp : T.Frob ⥤ TempObj O R A := Model.forget T.Φ₀ T.B₀ T.div₀ ⋙ T.realize

end TemperedFrobenioidData

end Frobenioid

end Iut
