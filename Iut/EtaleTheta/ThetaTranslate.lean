/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.TateFunctionField
import Iut.EtaleTheta.TateMulByN
import EllipticCurves.FunctionField.TranslationAutomorphism

/-!
# Values of the translation automorphisms of `K(E_q)` at Tate points

For `w ∉ qᶻ`, `transT h12 hw` is the translation `g ↦ g ∘ (· + P(w))` of `K(E_q)`
(`translateAlgEquiv` of `elliptic-curves`). `hasTateValue_trans`: the value of `transT hw g` at
`u` is the value of `g` at `u·w` (when `X(u) ≠ X(w)`).
-/

open Polynomial

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K}

/-- The Tate point `(X(w), Y(w))` lies on `E_q`. -/
theorem tateEquation (h12 : (12 : K) ≠ 0) {w : Kˣ} (hw : OffOrbit t w) :
    t.tateCurve.toAffine.Equation (t.X w) (t.Y w) :=
  t.tatePoint_mem' h12 hw

/-- Translation by the Tate point of `w` on `K(E_q)`: `g ↦ g ∘ (· + P(w))`. -/
abbrev transT (h12 : (12 : K) ≠ 0) {w : Kˣ} (hw : OffOrbit t w) :
    TateField t ≃ₐ[K] TateField t :=
  haveI := t.tateCurve_isElliptic h12
  translateAlgEquiv (tateEquation h12 hw)

variable {h12 : (12 : K) ≠ 0}

theorem HasTateValue.neg {g : TateField t} {u : Kˣ} {hu : OffOrbit t u} {v : K}
    (h : HasTateValue t h12 g hu v) : HasTateValue t h12 (-g) hu (-v) := by
  simpa using (HasTateValue.const (h12 := h12) hu (-1)).mul h

theorem HasTateValue.sub {g g' : TateField t} {u : Kˣ} {hu : OffOrbit t u} {v v' : K}
    (h : HasTateValue t h12 g hu v) (h' : HasTateValue t h12 g' hu v') :
    HasTateValue t h12 (g - g') hu (v - v') := by
  simpa [sub_eq_add_neg] using h.add h'.neg

/-- The addition law of `E_q` at Tate points: `P(u·w) = P(u) + P(w)` in coordinates. -/
theorem tate_mul_coords (h12 : (12 : K) ≠ 0) (h2 : ‖(2 : K)‖ = 1) {u w : Kˣ} (hu : OffOrbit t u)
    (hw : OffOrbit t w) (huw : OffOrbit t (u * w)) (hx : t.X u ≠ t.X w) :
    t.X (u * w) = t.tateCurve.toAffine.addX (t.X u) (t.X w)
        ((t.Y u - t.Y w) / (t.X u - t.X w)) ∧
      t.Y (u * w) = t.tateCurve.toAffine.addY (t.X u) (t.X w) (t.Y u)
        ((t.Y u - t.Y w) / (t.X u - t.X w)) := by
  classical
  have hmem : ∀ v : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (v : K) ≠ 1) →
      t.tateCurve.toAffine.Equation (t.X v) (t.Y v) := fun v hv => t.tatePoint_mem' h12 hv
  have tame : TameResidueChar K := ⟨h2, h12⟩
  have nq : ∀ {v : Kˣ}, OffOrbit t v → v ∉ t.qpowers := fun hv h =>
    (t.mem_qpowers_iff _).mp h |>.elim fun n hn => hv n hn
  have h := t.tatePoint_mul hmem tame u w
  rw [t.tatePoint_of_notMem hmem tame (nq huw), t.tatePoint_of_notMem hmem tame (nq hu),
    t.tatePoint_of_notMem hmem tame (nq hw), Point.add_of_X_ne hx, Point.some.injEq,
    slope_of_X_ne hx] at h
  exact h



/-- Values at `u` of the images `x(P + P(w))`, `y(P + P(w))` of `genX`, `genY`. -/
theorem hasTateValue_trans_gen (h2 : ‖(2 : K)‖ = 1) {u w : Kˣ} (hu : OffOrbit t u)
    (hw : OffOrbit t w) (huw : OffOrbit t (u * w)) (hx : t.X u ≠ t.X w) :
    HasTateValue t h12 (translateCoordHom (tateEquation h12 hw) (mk _ (C X))) hu
        (t.X (u * w)) ∧
      HasTateValue t h12 (translateCoordHom (tateEquation h12 hw)
        (AdjoinRoot.root t.tateCurve.toAffine.polynomial)) hu (t.Y (u * w)) := by
  classical
  obtain ⟨eX, eY⟩ := tate_mul_coords h12 h2 hu hw huw hx
  rw [translateCoordHom_X, translateCoordHom_root, eX, eY]
  have hgX : HasTateValue t h12 (genX t.tateCurve.toAffine) hu (t.X u) := HasTateValue.x hu
  have hgY : HasTateValue t h12 (genY t.tateCurve.toAffine) hu (t.Y u) := HasTateValue.y hu
  have hxw := HasTateValue.const (h12 := h12) hu (t.X w)
  have hyw := HasTateValue.const (h12 := h12) hu (t.Y w)
  have hsub : t.X u - t.X w ≠ 0 := sub_ne_zero.mpr hx
  have hℓ := (hgY.sub hyw).div (hgX.sub hxw) hsub
  rw [← slope_of_X_ne (W := t.tateCurve.toAffine.map (algebraMap K (TateField t)))
    (genX_ne (t.X w))] at hℓ
  have hA := ((((hℓ.pow 2).add ((HasTateValue.const (h12 := h12) hu
    t.tateCurve.toAffine.a₁).mul hℓ)).sub (HasTateValue.const (h12 := h12) hu
    t.tateCurve.toAffine.a₂)).sub hgX).sub hxw
  refine ⟨hA, ?_⟩
  have hN := (hℓ.mul (hA.sub hgX)).add hgY
  have hY := ((hN.neg.sub ((HasTateValue.const (h12 := h12) hu
    t.tateCurve.toAffine.a₁).mul hA)).sub (HasTateValue.const (h12 := h12) hu
    t.tateCurve.toAffine.a₃))
  exact hY

/-- Values at `u` of the translates of elements of `K[E_q]`: `a(u·w)`. -/
theorem hasTateValue_translateCoordHom (h2 : ‖(2 : K)‖ = 1) {u w : Kˣ} (hu : OffOrbit t u)
    (hw : OffOrbit t w) (huw : OffOrbit t (u * w)) (hx : t.X u ≠ t.X w) (a : TateRing t) :
    HasTateValue t h12 (translateCoordHom (tateEquation h12 hw) a) hu
      (evalTate t h12 huw a) := by
  obtain ⟨hX, hY⟩ := hasTateValue_trans_gen (h12 := h12) h2 hu hw huw hx
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
  have hC : ∀ r : K[X], translateCoordHom (tateEquation h12 hw)
      (mk t.tateCurve.toAffine (C r)) =
      Polynomial.aeval (translateCoordHom (tateEquation h12 hw) (mk _ (C X))) r := by
    intro r
    rw [translateCoordHom_X, translateCoordHom,
      show mk t.tateCurve.toAffine (C r) = AdjoinRoot.of _ r from rfl,
      AdjoinRoot.lift_of, coe_eval₂RingHom, aeval_def]
  rw [evalTate_smul_basis, CoordinateRing.smul, CoordinateRing.smul, map_add, map_mul, map_mul,
    map_one, mul_one, hC p, hC q]
  refine ((hX.aeval p).add ((hX.aeval q).mul hY)).congr ?_
  ring

/-- **Values of the translation**: the value of `transT hw g` at `u` is the value of `g` at
`u·w` (for `X(u) ≠ X(w)`). -/
theorem hasTateValue_trans (h2 : ‖(2 : K)‖ = 1) {u w : Kˣ} (hu : OffOrbit t u)
    (hw : OffOrbit t w) (huw : OffOrbit t (u * w)) (hx : t.X u ≠ t.X w) (g : TateField t)
    (v : K) (h : HasTateValue t h12 g huw v) : HasTateValue t h12 (transT h12 hw g) hu v := by
  obtain ⟨n, d, hg, hd, hv⟩ := h
  have hn := hasTateValue_translateCoordHom (h12 := h12) h2 hu hw huw hx n
  have hd' := hasTateValue_translateCoordHom (h12 := h12) h2 hu hw huw hx d
  have hd0 := hd'.ne_zero hd
  have e : transT h12 hw g = translateCoordHom (tateEquation h12 hw) n /
      translateCoordHom (tateEquation h12 hw) d := by
    haveI := t.tateCurve_isElliptic h12
    have := congrArg (translateEndo (tateEquation h12 hw)) hg
    rw [map_mul, translateEndo_algebraMap, translateEndo_algebraMap] at this
    change translateEndo (tateEquation h12 hw) g = _
    rw [← this, mul_div_assoc, div_self hd0, mul_one]
  rw [e]
  refine (hn.div hd' hd).congr ?_
  rw [← hv]
  field_simp

end Iut.EtaleTheta
