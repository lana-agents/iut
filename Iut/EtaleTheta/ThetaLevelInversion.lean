/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaLevelSystem

/-!
# The inversion `ι` on the levels `Ÿ'_N` (MR14, [EtTh] Prop. 1.5(iii), inversion part)

[EtTh], Prop. 1.5(iii) (`The Etale Theta Function ….txt`, l.1449–1459): an inversion automorphism
`ι` (lying over `[-1]` on the elliptic curve) fixes `η̈^Θ + log(O^×)`. At the level `Ÿ'_N` of
route R-alg (`MR14-plan.md`), `ι` is `[-1]` on `E_Q`, `Q = s^N`; pulled back along
`ψ(u) = u^N` it is the hyperelliptic involution `[-1]^* = negYAlgEquiv` of `K(E_q)`
(`x ↦ x`, `y ↦ -y - x` on the Tate curve, `X(u⁻¹) = X(u)`, `Y(u⁻¹) = -Y(u) - X(u)`).

* `hasTateValue_negY`: the value of `[-1]^* g` at `u` is the value of `g` at `u⁻¹`;
* `thetaLevel_inv`: `f_N(Ü⁻¹) = -f_N(Ü)` for even `N` (`Θ̈(Ü⁻¹) = -Θ̈(Ü)`, [EtTh] Prop. 1.4(ii));
* **`levelData_inv`**: `[-1]^*` fixes `x_Q∘ψ`, sends `y_Q∘ψ` to `-y_Q∘ψ - x_Q∘ψ` (so it preserves
  the function field `K(x_Q∘ψ, y_Q∘ψ)` of `Ÿ'_N`), and **`[-1]^* F_N = -F_N`**: the unit `η_N`
  is fixed up to the unit `-1` of the field of constants (the cohomological form
  `κ_n(ι^*η_N) = κ_n(-1)·κ_n(η_N)` is not yet stated).

The lift of `[-1]^*` to an automorphism of `Ω` normalising `Π_{Ÿ'_N}` and its action on
`H¹(Π_{Ÿ'_N}, μ_n)` are the next step (see the MR14 plan, run-5 hand-off).
-/

open Polynomial

noncomputable section

universe u

namespace Iut.EtaleTheta

open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K} {h12 : (12 : K) ≠ 0}

/-- `[-1]^*` on `K(E_q)`. -/
abbrev negT (t : TateParameter K) : TateField t ≃ₐ[K] TateField t :=
  WeierstrassCurve.Affine.CoordinateRing.negYAlgEquiv t.tateCurve.toAffine

theorem evalTate_negY {u : Kˣ} (hu : OffOrbit t u) (a : TateRing t) :
    evalTate t h12 hu
        (WeierstrassCurve.Affine.CoordinateRing.negYCoordHom t.tateCurve.toAffine a) =
      evalTate t h12 (offOrbit_inv t hu) a := by
  have e : (evalTate t h12 hu).comp
      (WeierstrassCurve.Affine.CoordinateRing.negYCoordHom t.tateCurve.toAffine).toRingHom =
      evalTate t h12 (offOrbit_inv t hu) := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · refine Polynomial.ringHom_ext (fun c => ?_) ?_
      · change evalTate t h12 hu (WeierstrassCurve.Affine.CoordinateRing.negYCoordHom _
          (mkT t (C (C c)))) = evalTate t h12 (offOrbit_inv t hu) (mkT t (C (C c)))
        rw [WeierstrassCurve.Affine.CoordinateRing.negYCoordHom_mk, C_comp, evalTate_mk_C,
          evalTate_mk_C]
        simp
      · change evalTate t h12 hu (WeierstrassCurve.Affine.CoordinateRing.negYCoordHom _
          (mkT t (C X))) = evalTate t h12 (offOrbit_inv t hu) (mkT t (C X))
        rw [WeierstrassCurve.Affine.CoordinateRing.negYCoordHom_mk, C_comp, evalTate_mk_C,
          evalTate_mk_C, eval_X, eval_X, t.X_inv hu]
    · change evalTate t h12 hu (WeierstrassCurve.Affine.CoordinateRing.negYCoordHom _
        (mkT t X)) = evalTate t h12 (offOrbit_inv t hu) (mkT t X)
      rw [WeierstrassCurve.Affine.CoordinateRing.negYCoordHom_mk, X_comp, evalTate_mk_Y,
        t.Y_inv hu, WeierstrassCurve.Affine.negPolynomial, evalTate_mkT]
      simp [tateCurve_a₁, tateCurve_a₃, Polynomial.evalEval_C]
  exact congrArg (fun f => f a) e

/-- **Values of `[-1]^*`**: the value of `[-1]^* g` at `u` is the value of `g` at `u⁻¹`. -/
theorem hasTateValue_negY {u : Kˣ} (hu : OffOrbit t u) {g : TateField t} {v : K}
    (h : HasTateValue t h12 g (offOrbit_inv t hu) v) : HasTateValue t h12 (negT t g) hu v := by
  obtain ⟨n, d, hg, hd, hv⟩ := h
  refine ⟨WeierstrassCurve.Affine.CoordinateRing.negYCoordHom _ n,
    WeierstrassCurve.Affine.CoordinateRing.negYCoordHom _ d, ?_, ?_, ?_⟩
  · have := congrArg (negT t) hg
    rw [map_mul] at this
    rwa [WeierstrassCurve.Affine.CoordinateRing.negYAlgEquiv_genPsi,
      WeierstrassCurve.Affine.CoordinateRing.negYAlgEquiv_genPsi] at this
  · rwa [evalTate_negY]
  · rwa [evalTate_negY, evalTate_negY]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- `f_N(Ü⁻¹) = -f_N(Ü)` for even `N` ([EtTh] Prop. 1.4(ii): `Θ̈(Ü⁻¹) = -Θ̈(Ü)`). -/
theorem thetaLevel_inv (N : ℕ) (hN : 0 < N) (hev : Even N) (U : Kˣ) :
    thetaLevel t N hN U⁻¹ = -thetaLevel t N hN U := by
  simp only [thetaLevel, etaleTheta_inv, Even.neg_pow hev, neg_div]

variable [CharZero K]

/-- **The inversion on the level `Ÿ'_N`**, function fields: for the level data of
`exists_levelData`, `[-1]^*` fixes `x_Q∘ψ`, sends `y_Q∘ψ` to `-y_Q∘ψ - x_Q∘ψ`, and sends the theta
level function `F_N` to `-F_N`. -/
theorem levelData_inv (h2 : ‖(2 : K)‖ = 1) {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ} (hN : 0 < N)
    (hev : Even N) [t.tateCurve.IsElliptic] [NeZero (2 * N)] {gX gY F : TateField t}
    (hval : ∀ (u : Kˣ) (hu : OffOrbit t u), OffOrbit t (u ^ (2 * N)) →
      HasTateValue t h12 gX hu ((sqrtPow hs N hN).X (u ^ N)) ∧
      HasTateValue t h12 gY hu ((sqrtPow hs N hN).Y (u ^ N)) ∧
      HasTateValue t h12 F hu (thetaLevel t N hN (u ^ N))) :
    negT t gX = gX ∧ negT t gY = -gY - gX ∧ negT t F = -F := by
  set T := sqrtPow hs N hN
  have hD₀ := psiN_ne_zero_of_neZero t.tateCurve (2 * N)
  -- at a good point `u`, the point `u⁻¹` is good too
  have good : ∀ (u : Kˣ) (hu : OffOrbit t u),
      evalTate t h12 hu (psiN t.tateCurve (2 * N)) ≠ 0 →
      OffOrbit t (u ^ (2 * N)) ∧ OffOrbit t (u⁻¹ ^ (2 * N)) ∧ OffOrbit T (u ^ N) := by
    intro u hu hψ
    obtain ⟨hum, -⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu hψ
    refine ⟨hum, by rw [inv_pow]; exact offOrbit_inv t hum,
      offOrbit_sqrt_pow hs T rfl hum⟩
  refine ⟨?_, ?_, ?_⟩
  · refine eq_of_hasTateValue (h12 := h12) hD₀ (G := fun u => T.X (u ^ N))
      (fun u hu hψ => ?_) (fun u hu hψ => (hval u hu (good u hu hψ).1).1)
    obtain ⟨-, hinv, hT⟩ := good u hu hψ
    refine hasTateValue_negY hu ((hval _ _ hinv).1.congr ?_)
    rw [inv_pow, T.X_inv hT]
  · refine eq_of_hasTateValue (h12 := h12) hD₀ (G := fun u => -T.Y (u ^ N) - T.X (u ^ N))
      (fun u hu hψ => ?_) (fun u hu hψ => ?_)
    · obtain ⟨-, hinv, hT⟩ := good u hu hψ
      refine hasTateValue_negY hu ((hval _ _ hinv).2.1.congr ?_)
      rw [inv_pow, T.Y_inv hT]
    · obtain ⟨vX, vY, -⟩ := hval u hu (good u hu hψ).1
      have := ((HasTateValue.const (h12 := h12) hu (-1)).mul vY).add
        ((HasTateValue.const (h12 := h12) hu (-1)).mul vX)
      rw [show -gY - gX = algebraMap K (TateField t) (-1) * gY +
        algebraMap K (TateField t) (-1) * gX by simp only [map_neg, map_one]; ring]
      exact this.congr (by ring)
  · refine eq_of_hasTateValue (h12 := h12) hD₀ (G := fun u => -thetaLevel t N hN (u ^ N))
      (fun u hu hψ => ?_) (fun u hu hψ => ?_)
    · obtain ⟨-, hinv, -⟩ := good u hu hψ
      refine hasTateValue_negY hu ((hval _ _ hinv).2.2.congr ?_)
      rw [inv_pow, thetaLevel_inv N hN hev]
    · have := (HasTateValue.const (h12 := h12) hu (-1)).mul (hval u hu (good u hu hψ).1).2.2
      simpa using this

end Iut.EtaleTheta
