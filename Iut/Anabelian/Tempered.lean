/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Geometry
import Iut.Anabelian.Genuine.Orbifold
import Iut.Anabelian.Genuine.Theory
import TemperedFundamentalGroups

/-!
# Tempered fundamental groups of the model orbicurves (taxis #7)

This module builds a term of the residual interface `Iut.Anabelian.TemperedPi1Theory` over the
genuine étale fundamental groups `Orbicurve.genuinePi1 X = Genuine.pi1C E ℓ M ±` of the model
orbicurves (`Iut.Anabelian.Genuine.Theory`: `Aut(Ω / F_X) ⧸ ⟨⟨inertia over X_M⟩⟩` in
characteristic `0`, the trivial group otherwise), from the
construction of lana-agents/tempered-fundamental-groups, with **no comparison parameter**: the
tempered and the étale fundamental group are computed from the same presentation.

* In characteristic `0`, a model orbicurve `X = (E, ℓ, M, ±)` over `k` is presented as the
  affine orbifold `[Spec R / A]` of `Iut.Anabelian.Genuine.orbifold`: `R` is the integral closure
  of `k[x]` in the function field `L_X = Ω^{Aut(Ω / L_X)}` and `A = Aut(Ω / F_X) ⧸ Aut(Ω / L_X)`,
  at the geometric point `R ⊆ Ω` (`Ω` an algebraic closure of `k(E)`). Its étale fundamental
  group `Pi1.Orbifold.etalePi1 R A Ω` is identified with `Genuine.pi1Of E ℓ M ±` by
  `Genuine.etaleEquiv` (SGA 1 V.8.2 with a finite group action, from the `pi1` project), and
  `Genuine.pi1Of E ℓ M ± = Genuine.pi1C E ℓ M ±` by `Genuine.pi1EquivC`.
* `tempPi1 X` is `TemperedFundamentalGroups.AffineOrbifold.canonicalTemperedPi1` of this
  presentation: the tempered fundamental group over the canonical valuation of `k` (the
  henselian discrete valuation ring of `k` if there is one — by F. K. Schmidt's theorem it is
  unique, so it is `O_v` for the completions `K_v` — and the trivial valuation otherwise),
  extended to `Ω` by the chosen extension of valuation rings (see that repository's
  `Blueprint.md` for the identification with André's definition and what is cited there).
* `tempToEtale X` is the tempered-to-étale comparison `AffineOrbifold.temperedToEtale` of the
  presentation followed by `Genuine.etaleEquiv`.
* **Outside characteristic `0`** (where the comparison `Genuine.etaleEquiv` is not available)
  the tempered group is that of the geometric presentation `Orbicurve.affineOrbifold`
  (`[(E ∖ (E[ℓ] + M)) / A]` at the generic point) and `tempToEtale X` is the trivial
  homomorphism. This is a junk value: IUT only evaluates the theory over fields of
  characteristic `0` (the core fields of `EtalePi1Theory` are also stated in characteristic
  `0`).

`GenuineEtaleData` collects the fields of a term of `EtalePi1Theory` with
`pi1 X = genuinePi1 X` other than `pi1` (`GenuineEtaleData.toEtalePi1Theory`), and
`temperedTheory G : TemperedPi1Theory G.toEtalePi1Theory`. The genuine term, with the genuine
`k`-cores of [CanLift], §2, is `Iut.Anabelian.genuineEtaleData` (`Iut.Anabelian.GenuineEtale`).
-/

namespace Iut.Anabelian

universe u

open TemperedFundamentalGroups

-- the decidability instances of `Iut.Anabelian.Model` (points of `E` need `DecidableEq k`)
attribute [local instance low] Classical.propDecidable

noncomputable section

/-- **The geometric affine presentation** of a model orbicurve: `[Spec R / A]` with
`Spec R = E ∖ S`, `S = E(k)[ℓ] + M`, `A = {P ↦ εP + m}`, at the generic geometric point. -/
def Orbicurve.affineOrbifold {k : Type u} [Field k] (X : Orbicurve k) : AffineOrbifold k :=
  TemperedFundamentalGroups.Orbicurve.orbicurveOrbifold X.E X.level X.M X.pm

/-- **The étale fundamental group** of a model orbicurve used by the genuine étale theory
(`Genuine.pi1C`): the genuine étale fundamental group `Genuine.pi1Of` in characteristic `0`
(`Genuine.pi1EquivC`), the trivial group (a junk value) in positive characteristic. -/
abbrev Orbicurve.genuinePi1 {k : Type u} [Field k] (X : Orbicurve k) : ProfiniteGrp.{u} :=
  Genuine.pi1C X.E X.level X.M X.pm

/-- **The presentation used for the tempered fundamental group**, with the continuous comparison
of its étale fundamental group with the genuine one: in characteristic `0`, the Galois
presentation `Genuine.orbifold` with the isomorphism `Genuine.etaleEquiv`; otherwise (a junk
value, never evaluated by IUT) the geometric presentation with the trivial homomorphism. -/
def Orbicurve.temperedPresentation {k : Type u} [Field k] (X : Orbicurve k) :
    Σ Y : AffineOrbifold k, {φ : Y.etalePi1 →* X.genuinePi1 // Continuous φ} :=
  if h : CharZero k then
    haveI := h
    ⟨Genuine.orbifold X.E X.level X.M X.pm,
      ((Genuine.etaleEquiv X.E X.level X.M X.pm).trans
        (Genuine.pi1EquivC X.E X.level X.M X.pm)).toMulEquiv.toMonoidHom,
      ((Genuine.etaleEquiv X.E X.level X.M X.pm).trans
        (Genuine.pi1EquivC X.E X.level X.M X.pm)).continuous⟩
  else ⟨X.affineOrbifold, 1, continuous_const⟩

lemma Orbicurve.temperedPresentation_of_charZero {k : Type u} [Field k] [CharZero k]
    (X : Orbicurve k) :
    X.temperedPresentation = ⟨Genuine.orbifold X.E X.level X.M X.pm,
      ((Genuine.etaleEquiv X.E X.level X.M X.pm).trans
        (Genuine.pi1EquivC X.E X.level X.M X.pm)).toMulEquiv.toMonoidHom,
      ((Genuine.etaleEquiv X.E X.level X.M X.pm).trans
        (Genuine.pi1EquivC X.E X.level X.M X.pm)).continuous⟩ := by
  rw [Orbicurve.temperedPresentation, dif_pos (inferInstance : CharZero k)]

/-- **The fields of an étale theory over the genuine étale fundamental groups**: the fields of
`EtalePi1Theory` other than `pi1`, for `pi1 X = X.genuinePi1`. -/
structure GenuineEtaleData : Type (u + 1) where
  /-- The homomorphism induced by a cover. -/
  pi1Cover : {k : Type u} → [Field k] → {X Y : Orbicurve k} → Orbicurve.Cover X Y →
    (X.genuinePi1 →* Y.genuinePi1)
  /-- The induced homomorphisms are continuous. -/
  pi1Cover_continuous : ∀ {k : Type u} [Field k] {X Y : Orbicurve k}
    (f : Orbicurve.Cover X Y), Continuous (pi1Cover f)
  /-- The induced homomorphisms are open immersions. -/
  pi1Cover_isOpenEmbedding : ∀ {k : Type u} [Field k] {X Y : Orbicurve k}
    (f : Orbicurve.Cover X Y), Topology.IsOpenEmbedding (pi1Cover f)
  /-- `C` is the `k`-core of `X`. -/
  HasCore : {k : Type u} → [Field k] → Orbicurve k → Orbicurve k → Prop
  /-- Orbicurves related by a finite étale cover have the same cores. -/
  hasCore_iff_of_cover : ∀ {k : Type u} [Field k] [CharZero k] {X Y C : Orbicurve k},
    Orbicurve.Cover X Y → (HasCore X C ↔ HasCore Y C)
  /-- Cores are compatible with base change. -/
  hasCore_baseChange : ∀ {k K : Type u} [Field k] [Field K] [CharZero k] [CharZero K]
    (f : k →+* K) {X C : Orbicurve k}, HasCore X C → HasCore (X.baseChange f) (C.baseChange f)
  /-- The exceptional `j`-invariants of [CanLift], Proposition 2.7. -/
  excJ : Finset ℚ
  /-- [CanLift], Proposition 2.7. -/
  hasCore_oncePunctured : ∀ {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k)
    [E.IsElliptic], (∀ c ∈ excJ, E.j ≠ (c : k)) →
      HasCore (Orbicurve.oncePunctured E) (Orbicurve.pmQuotient (Orbicurve.oncePunctured E))

/-- The étale theory with the genuine étale fundamental groups `pi1 X = X.genuinePi1`. -/
def GenuineEtaleData.toEtalePi1Theory (G : GenuineEtaleData.{u}) : EtalePi1Theory.{u} where
  pi1 X := X.genuinePi1
  pi1Cover := G.pi1Cover
  pi1Cover_continuous := G.pi1Cover_continuous
  pi1Cover_isOpenEmbedding := G.pi1Cover_isOpenEmbedding
  HasCore := G.HasCore
  hasCore_iff_of_cover := G.hasCore_iff_of_cover
  hasCore_baseChange := G.hasCore_baseChange
  excJ := G.excJ
  hasCore_oncePunctured := G.hasCore_oncePunctured

/-- **The tempered fundamental groups of the model orbicurves** over the genuine étale theory,
from the construction through integral models (lana-agents/tempered-fundamental-groups) over the
canonical valuation of the base field, for the same presentation `[Spec R / A]` as the étale
fundamental group (`Orbicurve.temperedPresentation`). -/
def temperedTheory (G : GenuineEtaleData.{u}) : TemperedPi1Theory G.toEtalePi1Theory where
  tempPi1 X := X.temperedPresentation.1.canonicalTemperedPi1
  tempPi1Group _ := inferInstance
  tempPi1Topology _ := inferInstance
  tempToEtale X := X.temperedPresentation.2.1.comp (X.temperedPresentation.1.temperedToEtale _)
  tempToEtale_continuous X :=
    X.temperedPresentation.2.2.comp (X.temperedPresentation.1.continuous_temperedToEtale _)

end

end Iut.Anabelian
