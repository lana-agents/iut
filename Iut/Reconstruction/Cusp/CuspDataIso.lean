/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.BelyiSpec
import CurvesJacobian.CuspChar.FinalW
import CurvesJacobian.CuspChar.FinalPadic

/-!
# Isomorphisms of arithmetic fundamental groups preserve the genuine cusp data (MR3 consumer)

[AbsTopI] Lemma 4.5 (v): for affine hyperbolic curves `U`, `U'` over number fields (or over
finite extensions of `ℚ_p`), every isomorphism `Π_U ≃ₜ* Π_{U'}` lying over an isomorphism
`G_K ≃ₜ* G_{K'}` maps the cuspidal inertia groups of `Π_U` onto those of `Π_{U'}`. This is
curves-jacobian's `CurvesJacobian.CuspChar.arithmeticExtIso'` (number fields, through the cusp
weight identity `cuspWeightIdentity`, no hypotheses) and `arithmeticExtIso_padic`. Here it is
packaged for the cusp data of `BelyiSpec.lean`, so that `filledEquiv` and the group-theoretic
cusp filling apply to every such isomorphism (not only to isomorphisms of cuspidal extensions):

* `arithCuspDataIso`: number fields;
* `arithCuspData_padic`, `arithCuspDataIso_padic`: finite extensions of `ℚ_p`.
-/

universe u

open CategoryTheory AlgebraicGeometry Belyi.Anabelian CurvesJacobian.Cusp

noncomputable section

namespace Iut.Reconstruction

section NumberField

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
  {K' : Type u} [Field K'] [NumberField K'] {Ω' : Type u} [Field Ω'] [Algebra K' Ω']
  [IsAlgClosed Ω'] [Algebra.IsAlgebraic K' Ω'] [CharZero Ω'] {C' : HypCurve K'}
  {hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty}

/-- **[AbsTopI] Lemma 4.5 (v) for the genuine cusp data** (number fields): an isomorphism
`Π_U ≃ₜ* Π_{U'}` over `G_K ≃ₜ* G_{K'}` is an isomorphism of cusp data. -/
def arithCuspDataIso (Φ : (arithmeticExt Ω C hc).Pi ≃ₜ* (arithmeticExt Ω' C' hc').Pi)
    (ψ : (arithmeticExt Ω C hc).G ≃ₜ* (arithmeticExt Ω' C' hc').G)
    (hpr : ∀ x, (arithmeticExt Ω' C' hc').pr (Φ x) = ψ ((arithmeticExt Ω C hc).pr x)) :
    (arithCuspData Ω C hc).Iso (arithCuspData Ω' C' hc') :=
  CuspData.Iso.ofExtIso (CurvesJacobian.CuspChar.arithmeticExtIso' Φ ψ hpr)

lemma arithCuspDataIso_toMulEquiv
    (Φ : (arithmeticExt Ω C hc).Pi ≃ₜ* (arithmeticExt Ω' C' hc').Pi)
    (ψ : (arithmeticExt Ω C hc).G ≃ₜ* (arithmeticExt Ω' C' hc').G)
    (hpr : ∀ x, (arithmeticExt Ω' C' hc').pr (Φ x) = ψ ((arithmeticExt Ω C hc).pr x)) :
    (arithCuspDataIso Φ ψ hpr).toMulEquiv = Φ.toMulEquiv :=
  rfl

end NumberField

section Padic

variable (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

/-- **The genuine cusp data of `Π_U` over a `p`-adic field**: the arithmetic fundamental group
of an affine hyperbolic curve over a finite extension of `ℚ_p` with its cuspidal inertia
groups. -/
abbrev arithCuspData_padic :
    CuspData (arithmeticExt_padic p Ω C hc).Pi (arithmeticExt_padic p Ω C hc).cusps :=
  CuspData.ofExt (arithmeticExt_padic p Ω C hc)

variable {p Ω C hc} (p' : ℕ) [Fact p'.Prime] {K' : Type u} [Field K'] [Algebra ℚ_[p'] K']
  [FiniteDimensional ℚ_[p'] K'] {Ω' : Type u} [Field Ω'] [Algebra K' Ω'] [IsAlgClosed Ω']
  [Algebra.IsAlgebraic K' Ω'] [CharZero Ω'] {C' : HypCurve K'}
  {hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty}

/-- **[AbsTopI] Lemma 4.5 (v) for the genuine cusp data** (`p`-adic fields). -/
def arithCuspDataIso_padic
    (Φ : (arithmeticExt_padic p Ω C hc).Pi ≃ₜ* (arithmeticExt_padic p' Ω' C' hc').Pi)
    (ψ : (arithmeticExt_padic p Ω C hc).G ≃ₜ* (arithmeticExt_padic p' Ω' C' hc').G)
    (hpr : ∀ x, (arithmeticExt_padic p' Ω' C' hc').pr (Φ x) =
      ψ ((arithmeticExt_padic p Ω C hc).pr x)) :
    (arithCuspData_padic p Ω C hc).Iso (arithCuspData_padic p' Ω' C' hc') :=
  CuspData.Iso.ofExtIso (CurvesJacobian.CuspChar.arithmeticExtIso_padic p p' Φ ψ hpr)

end Padic

end Iut.Reconstruction
