/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFConstEquiv
import Iut.Reconstruction.Thm19.EllipticNF
import Iut.Reconstruction.Thm19.OriginMatch

/-!
# `σ(j) = j` (MR9, `CKSemiAbsConj` item 5)

Let `E` be an elliptic curve over a number field `K`, `X = E ∖ {O}` (`hypCurveE E`, i.e.
curves-jacobian's `hypCurveX E`, with coordinate `x`: `XE_eq_chartOne`) and `Φ` an automorphism
of the arithmetic fundamental group `Π_X` (curves-jacobian `arithmeticExt`). [AbsTopIII] Thm 1.9
(`Topics in Absolute Anabelian Geometry III.txt` l.2109–2199) reconstructs from `Φ` a field
automorphism `nfRingEquiv` of the NF-portion `F_NF = k̄(E)`, which is `σ = nfConstEquiv` on
`k̄ = ℚ̄` (`Thm19/NFConstEquiv.lean`) and preserves the valuations along the bijection of points
`nfPlaceEquiv`. If this bijection fixes the origin `O` (the unique cusp of `X`), then
`EllipticJ.j_eq_of_semilinear` applies (`Thm19/EllipticNF.lean` supplies the Weierstrass data,
`[F_NF : k̄(x)] = 2` and `g(F_NF) = 1`):

* `psiE`, `sigmaE`, `placeE`: `nfRingEquiv`, `σ = nfConstEquiv` and `nfPlaceEquiv` for `X`;
* `qbarConst`: `σ` on `k̄_NF = ℚ̄`, `nfRingEquiv_algebraMap`;
* `nfConstEquiv_j`: `σ(j(E)) = j(E)` if the bijection of points fixes `O`;
* **`nfConstEquiv_fix_j`**: `σ(j(E)) = j(E)` (the origin is fixed: `Thm19/OriginMatch.lean`).
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

section J

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  [hc : Fact ((hypCurveE E).U : Set (hypCurveE E).Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic
  Thm19.isAlgClosed_algebraicClosure Thm19.isFunctionField_fnf

variable {Φ : (arithmeticExt Ω (hypCurveE E) hc.out).Iso (arithmeticExt Ω (hypCurveE E) hc.out)}
  (hS : BelyiCuspSpec Ω (hypCurveE E) hc.out)
  (σ₀ : Spec (CommRingCat.of K) ⟶ (hypCurveE E).Xbar)
  (hσ₀ : σ₀ ≫ ((hypCurveE E).Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
  (hDGC : RelIsomDGC.Exists K)
  (N : NFModel (curveGaloisData K (transcendental_xN E)))

local notation "hgE" => curveGenus_hypCurveE_ne E

instance isGalois_hypCurveE :
    IsGalois (K₀ K (coordT (xN E))) (FFClosure (hypCurveE E).Xbar) :=
  isGalois_K₀_hemi E

instance charZero_hypCurveE : CharZero (FFClosure (hypCurveE E).Xbar) :=
  charZero_FFClosure_curveE E

variable (Φ) in
/-- `nfRingEquiv` for `X = E ∖ {O}` (`F_NF ≃+* F_NF`). -/
abbrev psiE : fnf N ≃+* fnf N :=
  @nfRingEquiv K _ _ Ω _ _ _ _ _ (hypCurveE E) hc K _ _ Ω _ _ _ _ _ (hypCurveE E) hc
    (xN E) (transcendental_xN E) _ (XE_eq_chartOne E) (xN E) (transcendental_xN E) _
    (XE_eq_chartOne E) Φ _ _ _ _ hS hS σ₀ hσ₀ hgE σ₀ hσ₀ hgE hDGC hDGC N N

variable (Φ) in
/-- `σ = nfConstEquiv` for `X = E ∖ {O}`. -/
abbrev sigmaE : kbar K (FFClosure (curveE E)) ≃+* kbar K (FFClosure (curveE E)) :=
  @nfConstEquiv K _ _ Ω _ _ _ _ _ (hypCurveE E) hc K _ _ Ω _ _ _ _ _ (hypCurveE E) hc
    (xN E) (transcendental_xN E) _ (XE_eq_chartOne E) (xN E) (transcendental_xN E) _
    (XE_eq_chartOne E) Φ _ _ _ _ hS hS σ₀ hσ₀ hgE σ₀ hσ₀ hgE hDGC hDGC N N

variable (Φ) in
/-- The bijection of points for `X = E ∖ {O}`. -/
abbrev placeE : Place (algebraicClosure ℚ (FFClosure (curveE E))) (fnf N) ≃
    Place (algebraicClosure ℚ (FFClosure (curveE E))) (fnf N) :=
  @nfPlaceEquiv K _ _ Ω _ _ _ _ _ (hypCurveE E) hc K _ _ Ω _ _ _ _ _ (hypCurveE E) hc
    (xN E) (transcendental_xN E) _ (XE_eq_chartOne E) (xN E) (transcendental_xN E) _
    (XE_eq_chartOne E) Φ _ _ _ _ hS hS σ₀ hσ₀ hgE σ₀ hσ₀ hgE hDGC hDGC N N

variable (Φ) in
/-- **`σ` on `k̄_NF = ℚ̄`**. -/
def qbarConst : algebraicClosure ℚ (FFClosure (curveE E)) ≃+*
    algebraicClosure ℚ (FFClosure (curveE E)) :=
  (kbarQbar K (FFClosure (curveE E))).symm.trans
    ((sigmaE E Φ hS σ₀ hσ₀ hDGC N).trans (kbarQbar K (FFClosure (curveE E))))

/-- `nfRingEquiv` is `σ` on `k̄_NF`. -/
lemma nfRingEquiv_algebraMap (c : algebraicClosure ℚ (FFClosure (curveE E))) :
    psiE E Φ hS σ₀ hσ₀ hDGC N (algebraMap (algebraicClosure ℚ (FFClosure (curveE E))) (fnf N) c) =
      algebraMap (algebraicClosure ℚ (FFClosure (curveE E))) (fnf N)
        (qbarConst E Φ hS σ₀ hσ₀ hDGC N c) :=
  @nfRingEquiv_constFnf K _ _ Ω _ _ _ _ _ (hypCurveE E) hc K _ _ Ω _ _ _ _ _ (hypCurveE E) hc
    (xN E) (transcendental_xN E) _ (XE_eq_chartOne E) (xN E) (transcendental_xN E) _
    (XE_eq_chartOne E) Φ _ _ _ _ hS hS σ₀ hσ₀ hgE σ₀ hσ₀ hgE hDGC hDGC N N
    ((kbarQbar K (FFClosure (curveE E))).symm c)

set_option maxHeartbeats 800000 in
-- `nfRingEquiv` and the bijection of points unify slowly
/-- **`σ(j) = j`** (MR9, `CKSemiAbsConj` item 5): if the bijection of points of `Z_NF` induced by
`Φ` fixes the origin `O` (the pole of `x`), then `σ = nfConstEquiv` fixes `j(E)`. -/
theorem nfConstEquiv_j
    (P₀ : Place (algebraicClosure ℚ (FFClosure (curveE E))) (fnf N)) (hP₀ : xNF E N ∉ P₀.1)
    (hO : placeE E Φ hS σ₀ hσ₀ hDGC N P₀ = P₀) :
    sigmaE E Φ hS σ₀ hσ₀ hDGC N (algebraMap K (kbar K (FFClosure (curveE E))) E.j) =
      algebraMap K (kbar K (FFClosure (curveE E))) E.j := by
  have hord : ∀ (P : Place (algebraicClosure ℚ (FFClosure (curveE E))) (fnf N)) (f : fnf N),
      f ≠ 0 → (placeE E Φ hS σ₀ hσ₀ hDGC N P).ord (psiE E Φ hS σ₀ hσ₀ hDGC N f) = P.ord f :=
    fun P f hf => @ord_nfRingEquiv K _ _ Ω _ _ _ _ _ (hypCurveE E) hc K _ _ Ω _ _ _ _ _
      (hypCurveE E) hc
      (xN E) (transcendental_xN E) _ (XE_eq_chartOne E) (xN E) (transcendental_xN E) _
      (XE_eq_chartOne E) Φ _ _ _ _ hS hS σ₀ hσ₀ hgE σ₀ hσ₀ hgE hDGC hDGC N N P f hf
  have hj := EllipticJ.j_eq_of_semilinear (psiE E Φ hS σ₀ hσ₀ hDGC N)
    (qbarConst E Φ hS σ₀ hσ₀ hDGC N) (nfRingEquiv_algebraMap E hS σ₀ hσ₀ hDGC N)
    (weq_fnf E N) (transcendental_xNF E N) (finrank_fnf_xNF E N)
    (weq_fnf E N) (transcendental_xNF E N) (finrank_fnf_xNF E N) (genus_fnf E N) hP₀ hP₀
    (fun f hf Q' hQ' => by
      by_cases hf0 : f = 0
      · rw [hf0, map_zero]
        exact zero_mem _
      obtain ⟨Q, rfl⟩ := (placeE E Φ hS σ₀ hσ₀ hDGC N).surjective Q'
      have hQ : Q ≠ P₀ := fun h => hQ' (by rw [h, hO])
      exact (placeE E Φ hS σ₀ hσ₀ hDGC N Q).mem_of_ord_nonneg
        (by rw [hord Q f hf0]; exact Q.ord_nonneg_of_mem (hf Q hQ)))
    (fun f hf => by
      have := hord P₀ f hf
      rwa [hO] at this)
  have hjNF : (eNF E).j = kbarQbar K (FFClosure (curveE E))
      (algebraMap K (kbar K (FFClosure (curveE E))) E.j) := by
    rw [WeierstrassCurve.map_j, WeierstrassCurve.map_j]
    rfl
  rw [hjNF] at hj
  apply (kbarQbar K (FFClosure (curveE E))).injective
  rw [hj, qbarConst, RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]

/-- **`σ(j) = j`** (MR9, `CKSemiAbsConj` item 5), unconditionally on `Φ`: the bijection of points
fixes the origin `O`, the unique pole of `x`, because it maps cusps of `X` to cusps of `X`
(`not_mem_nfPlaceEquiv`; the cuspidal inertia of `Π_{E ∖ {O}}` is nontrivial,
`cusps_ne_bot_hypCurveE`). -/
theorem nfConstEquiv_fix_j :
    sigmaE E Φ hS σ₀ hσ₀ hDGC N (algebraMap K (kbar K (FFClosure (curveE E))) E.j) =
      algebraMap K (kbar K (FFClosure (curveE E))) E.j := by
  obtain ⟨P₀, hP₀, -, huniq⟩ := exists_unique_pole_of_weq₂ (eNF E) (weq_fnf E N)
    (transcendental_xNF E N) (finrank_fnf_xNF E N)
  refine nfConstEquiv_j E hS σ₀ hσ₀ hDGC N P₀ hP₀ (huniq _ ?_)
  exact @not_mem_nfPlaceEquiv K _ _ Ω _ _ _ _ _ (hypCurveE E) hc K _ _ Ω _ _ _ _ _
    (hypCurveE E) hc
    (xN E) (transcendental_xN E) _ (XE_eq_chartOne E) (xN E) (transcendental_xN E) _
    (XE_eq_chartOne E) Φ _ _ _ _ hS hS σ₀ hσ₀ hgE σ₀ hσ₀ hgE hDGC hDGC N N
    (fun I hI => cusps_ne_bot_hypCurveE Ω E hc.out hI) P₀ hP₀

end J

end Iut.Reconstruction.Thm19
