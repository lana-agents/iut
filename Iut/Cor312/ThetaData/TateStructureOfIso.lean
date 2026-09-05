/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.TateStructure
import Iut.Cor312.ThetaData.VariableChangePoint

/-!
# Tate structures on curves isomorphic to Tate curves

A change of variables `C` with `C • E = E_q` transports the Tate uniformization of `E_q`
(`Iut.TateStructure.ofTateParameter`, the uniformization of `lana-agents/tate-curves-theta`)
to a Tate structure on `E` (`Iut.TateStructure.ofVariableChange`): the group isomorphism is
composed with the isomorphism on points `E(k) ≃+ (C • E)(k)` of
`Iut.Anabelian.vcEquiv`, and the coordinate pins hold because the coordinates of a point in
the model `C • E` are by definition its coordinates after the change of variables.
-/

namespace Iut

open WeierstrassCurve TateCurvesTheta Iut.Anabelian
open scoped Classical Valued

universe u

noncomputable section

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

variable {E : WeierstrassCurve k}

lemma xCoord_eq_ptX (C : VariableChange k) (P : E.toAffine.Point) :
    xCoord C P = ptX (vcPoint C E P) := by
  cases P <;> rfl

lemma yCoord_eq_ptY (C : VariableChange k) (P : E.toAffine.Point) :
    yCoord C P = ptY (vcPoint C E P) := by
  cases P <;> rfl

lemma xCoord_one (P : E.toAffine.Point) : xCoord 1 P = ptX P := by
  cases P with
  | zero => rfl
  | some x y h =>
    change (x - 0) / ((1 : kˣ) : k) ^ 2 = x
    simp

lemma yCoord_one (P : E.toAffine.Point) : yCoord 1 P = ptY P := by
  cases P with
  | zero => rfl
  | some x y h =>
    change (y - 0 - 0 * (x - 0)) / ((1 : kˣ) : k) ^ 3 = y
    simp

namespace TateStructure

/-- The Tate structure of `E_q` itself, under `TameResidueChar k`. -/
def base (t : TateParameter k) (h12 : TameResidueChar k) : TateStructure t.tateCurve :=
  ofTateParameter t (fun _ hu => t.tatePoint_mem' h12.2 hu) h12

@[simp] lemma base_t (t : TateParameter k) (h12 : TameResidueChar k) : (base t h12).t = t := rfl

@[simp] lemma base_C (t : TateParameter k) (h12 : TameResidueChar k) : (base t h12).C = 1 := rfl

/-- **The Tate structure of a curve isomorphic to a Tate curve**: `C • E = E_q` transports the
uniformization of `E_q` to `E`. -/
def ofVariableChange (t : TateParameter k) (C : VariableChange k) (hC : C • E = t.tateCurve)
    (h12 : TameResidueChar k) : TateStructure E where
  t := (base t h12).t
  C := C
  hC := hC
  iso := ((base t h12).iso.trans (pointCongr hC).symm).trans (vcEquiv C E).symm
  iso_x u hu := by
    have h0 := (base t h12).iso_x u hu
    rw [base_C, xCoord_one] at h0
    simp only [AddEquiv.trans_apply]
    rw [xCoord_eq_ptX, vcEquiv_symm_apply, ptX_pointCongr_symm]
    exact h0
  iso_y u hu := by
    have h0 := (base t h12).iso_y u hu
    rw [base_C, yCoord_one] at h0
    simp only [AddEquiv.trans_apply]
    rw [yCoord_eq_ptY, vcEquiv_symm_apply, ptY_pointCongr_symm]
    exact h0

@[simp] lemma ofVariableChange_t (t : TateParameter k) (C : VariableChange k)
    (hC : C • E = t.tateCurve) (h12 : TameResidueChar k) :
    (ofVariableChange t C hC h12).t = t := rfl

@[simp] lemma ofVariableChange_C (t : TateParameter k) (C : VariableChange k)
    (hC : C • E = t.tateCurve) (h12 : TameResidueChar k) :
    (ofVariableChange t C hC h12).C = C := rfl

/-- **A Tate structure on `E` from one on a model `C • E = E'`**: the change of variables of
`E'` to its Tate curve is composed with `C`. -/
def ofCurveVariableChange {E' : WeierstrassCurve k} (C : VariableChange k) (h : C • E = E')
    (S : TateStructure E') (h12 : TameResidueChar k) : TateStructure E :=
  ofVariableChange S.t (S.C * C) (by rw [mul_smul, h]; exact S.hC) h12

@[simp] lemma ofCurveVariableChange_t {E' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • E = E') (S : TateStructure E') (h12 : TameResidueChar k) :
    (ofCurveVariableChange C h S h12).t = S.t := rfl

@[simp] lemma ofCurveVariableChange_C {E' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • E = E') (S : TateStructure E') (h12 : TameResidueChar k) :
    (ofCurveVariableChange C h S h12).C = S.C * C := rfl

end TateStructure

end

end Iut
