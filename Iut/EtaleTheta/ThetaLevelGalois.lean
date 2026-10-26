/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.TateMulByN
import Iut.EtaleTheta.MulByNGalois

/-!
# The level `Ÿ'_N` of the étale theta function is étale over `X` (MR14, G1)

Let `q` be a Tate parameter over a complete nonarchimedean field `K` of characteristic `0` with
`‖2‖ = 1`, `s² = q`, `N` even, `Q = s^N`, and let `E = E_q`, `X = E ∖ {O}`. In `Ω = K(Ē)^alg`
with the coordinate `τ = x`, `curves-jacobian`'s Galois data `hemiData E` has function field
`L_X = K(E)` and coordinate ring `K[E]`. The level `Ÿ'_N = E_Q ∖ ker φ` (`φ(Ü) = Ü²`) of
`MR14-plan.md` (route R-alg, ψ-route) is realised as

  `L' = K(τ)(φ_{2N}(x_Q∘ψ), φ_{2N}(y_Q∘ψ)) ⊆ Ω`,

where `ψ(u) = u^N`, `x_Q∘ψ, y_Q∘ψ ∈ K(E)` are the value-defined elements of
`exists_levelField_mulByN` and `φ_{2N} = mulByNEmb E (2N)` embeds the source of `[2N] = φ∘ψ`.

**Main theorem** (`exists_thetaLevel_etale`): `L_X ≤ L'`, `coordRing L_X → coordRing L'` is étale,
and `L'` contains the image of the theta level function `F_N = f_N∘ψ`
(`F_N(u) = Θ̈_q(u^N)/Θ̈_{q^N}(u^N)^N`).
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open CurvesJacobian.Cusp AffOrbicurve

noncomputable section

universe u

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

/-- **The level `Ÿ'_N` in `Ω` is étale over `X = E_q ∖ {O}`, and carries `F_N`.** For even `N`
there are `x_Q∘ψ, y_Q∘ψ, F_N ∈ K(E_q)` (values `X_Q(u^N)`, `Y_Q(u^N)`, `f_N(u^N)`) such that
`L' = K(τ)(φ_{2N}(x_Q∘ψ), φ_{2N}(y_Q∘ψ))` contains `L_X = K(E_q)`, the map of coordinate rings
`coordRing L_X → coordRing L'` is étale, and `φ_{2N}(F_N) ∈ L'`. -/
theorem exists_thetaLevel_etale (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ}
    (hs : s ^ 2 = t.q) {N : ℕ} (hN : 0 < N) (T : TateParameter K) (hT : T.q = s ^ N)
    (hev : Even N) :
    haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
    haveI : NeZero (2 * N) := ⟨by omega⟩
    ∃ (gX gY F : TateField t) (D : TateRing t), D ≠ 0 ∧
      F ∈ IntermediateField.adjoin K ({gX, gY} : Set (TateField t)) ∧
      (∃ h₁ : (hemiData t.tateCurve).L ≤ IntermediateField.adjoin
          (K₀ K (coordT (xN t.tateCurve))) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}),
        (ringMap (coordT (xN t.tateCurve)) h₁).toRingHom.Etale) ∧
      mulByNEmb t.tateCurve (2 * N) F ∈ IntermediateField.adjoin
          (K₀ K (coordT (xN t.tateCurve))) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}) ∧
      ∀ (u : Kˣ) (hu : OffOrbit t u),
        (evalTate t h12 hu D ≠ 0 ↔ T.theta (-(u ^ N)) ≠ 0) ∧
        (T.theta (-(u ^ N)) ≠ 0 →
          HasTateValue t h12 gX hu (T.X (u ^ N)) ∧ HasTateValue t h12 gY hu (T.Y (u ^ N)) ∧
          (etaleTheta (tatePow t N hN) (u ^ N) ≠ 0 →
            HasTateValue t h12 F hu (thetaLevel t N hN (u ^ N)))) := by
  haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
  haveI : NeZero (2 * N) := ⟨by omega⟩
  obtain ⟨gX, gY, F, D, hD, hF, hmul, hspec⟩ :=
    exists_levelField_mulByN (h12 := h12) h2 hs hN T hT hev
  exact ⟨gX, gY, F, D, hD, hF, ⟨hemiL_le_adjoin _ _ hmul, etale_adjoin_image _ _ hmul⟩,
    mem_adjoin_image _ _ hF, hspec⟩

end Iut.EtaleTheta
