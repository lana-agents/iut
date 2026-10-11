/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.Existence
import Iut.Cor312.ThetaData.PlaceUnder
import Iut.Cor312.ThetaData.BadPlaceNorm
import Iut.Cor312.ThetaData.TateParameterAt

/-!
# Construction of the Tate inputs of an elliptic curve

For an elliptic curve `E/F` over a number field (`Iut.EllipticCurveData`), the Tate
inputs `EllipticCurveData.TateInputs` — a Tate parameter of `E` at every place of
multiplicative reduction, and a uniformizer of every such completion — exist
unconditionally:

* at a place `w` of multiplicative reduction, `‖c₄‖ = 1` and `‖Δ‖ < 1` on `F_w` for a minimal
  model `C • E`, hence `‖j(E)‖ > 1` for the invariant `j`-invariant
  (`Iut.EllipticCurveData.one_lt_norm_j`), and the `j`-parametrization of Tate
  curves (`TateCurvesTheta.TateParameter.exists_tateParameter_tateJ_eq`) yields a Tate
  parameter `q_w` with `j(E_{q_w}) = j(E)`;
* the image in `F_w` of a uniformizer of the `w`-adic valuation of `F` is a uniformizer of
  the norm of `F_w` in the sense of `TateCurvesTheta.IsUniformizer`
  (`Iut.exists_isUniformizer`, in `Iut.Cor312.ThetaData.TateParameterAt`).

The resulting inputs are `EllipticCurveData.tateInputs`.
-/

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WeierstrassCurve
  TateCurvesTheta

/-! ## The Tate inputs of an elliptic curve -/

namespace EllipticCurveData

variable (C : EllipticCurveData.{u})

/-- At a place of multiplicative reduction, the `j`-invariant has norm `> 1` in `F_w`
(`Iut.one_lt_valuation_j_of_mult`, via a minimal model `C • E`). -/
lemma one_lt_norm_j {w : FinitePlace C.F} (hw : w ∈ C.badAll) :
    1 < ‖FinitePlace.embedding w.maximalIdeal C.E.j‖ :=
  one_lt_norm_j_of_mult C.E hw

/-- The Tate parameter of `E` at a place of multiplicative reduction: the unique Tate
parameter of `F_w` whose Tate curve has `j`-invariant `j(E)`. -/
noncomputable def tateParameter {w : FinitePlace C.F} (hw : w ∈ C.badAll) :
    TateParameter (localCompletion w) :=
  (TateParameter.exists_tateParameter_tateJ_eq (twelve_ne_zero w) (C.one_lt_norm_j hw)).choose

lemma tateParameter_tateJ {w : FinitePlace C.F} (hw : w ∈ C.badAll) :
    (C.tateParameter hw).tateJ = FinitePlace.embedding w.maximalIdeal C.E.j :=
  (TateParameter.exists_tateParameter_tateJ_eq (twelve_ne_zero w)
    (C.one_lt_norm_j hw)).choose_spec

/-- **The Tate inputs** of an elliptic curve over a number field: Tate parameters at the
multiplicative places, via the `j`-parametrization of Tate curves, and uniformizers of the
completions. -/
noncomputable def tateInputs : C.TateInputs where
  tate _ hw := C.tateParameter hw
  tateJ_eq _ hw := C.tateParameter_tateJ hw
  unif w _ := (exists_isUniformizer w).choose
  unif_isUniformizer w _ := (exists_isUniformizer w).choose_spec

end EllipticCurveData

end Iut
