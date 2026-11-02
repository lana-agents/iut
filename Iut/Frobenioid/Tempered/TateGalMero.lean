/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.TateStab

/-!
# Galois equivariance of `K(E_t) → Mero K` (MR18 T7c)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*
(text `~/iut-scratch/wall/txt/The Etale Theta Function …txt`, cited by line).

An isometric automorphism `σ` of `K` fixing `q` (`IsoAut t`, the Galois part of `GalDeck t`)
acts on `Mero K` on coefficients (`Mero.gal σ`) and on the function field `K(E_t)` of the Tate
curve on coefficients (`tateFieldGal σ`; `σ` fixes `a₄(q)`, `a₆(q)`, convergent `q`-series with
rational coefficients). This file proves that the embedding `tateFieldHom` of `TateMero`
intertwines them:

* `IsoAut.map_tsum`; `IsoAut.map_eisenstein`, `IsoAut.map_a₄`, `IsoAut.map_a₆`;
  **`IsoAut.map_X`, `IsoAut.map_Y`, `IsoAut.map_theta`**: `σ(X(u)) = X(σu)`, `σ(Y(u)) = Y(σu)`,
  `σ(θ(u)) = θ(σu)` (termwise, by continuity);
* `Entire.map_iso_eq_self` (an entire series whose values commute with `σ` off `q^ℤ` has
  `σ`-fixed coefficients, by the identity principle `Entire.eq_zero_of_offOrbit`);
  `Mero.gal_sq` (`σ` commutes with `U = Ü²`); **`gal_xM`, `gal_yM`** (`σ` fixes `x(Ü²)`, `y(Ü²)`),
  **`gal_kumM`** (`σ` fixes `√(x - e)` when `σ(s) = s`);
* `tateRingGal σ`, `tateFieldGal σ`: `σ` on `K[E_t]` and `K(E_t)` (on coefficients);
  **`gal_comp_tateFieldHom`**: `σ ∘ tateFieldHom = tateFieldHom ∘ σ_*`;
  **`galDeckHom_tateFieldHom`**: an element `⟨c, σ⟩` of `GalDeck t` acts on `K(E_t) ⊆ Mero K` by
  `σ_*` (its deck part acts trivially);
* **`gal_dataRingHom`**: if `σ` fixes `φ(F)`, it fixes the image of the coordinate ring of the
  `F`-curve of tfg's Tate data `D` (`EllTateAn.dataRingHom`);
* **`galDeckHom_tateGalDeck_kumM`**, **`galDeckHom_tateGalDeck_tateFieldHom`**: for the Tate
  action `tateGalDeck σ hσ` of `Π^tp_X` (explicit Galois part `σ` fixing `s`), `g` acts on
  `K(X') = K(E_t)(√(x - e)) ⊆ Mero K` by `σ(g)_*` on `K(E_t)` and by the sign `(-1)^ε` of
  `character₂ g` on `√(x - e)`, as on tfg's `B(X') = R[√c]`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open TateCurvesTheta TateParameter Polynomial Iut.EtaleTheta

universe u

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K}

/-! ### `σ` on Tate's series -/

section Series

lemma IsoAut.continuous (σ : IsoAut t) : Continuous ((σ : RingAut K) : K → K) :=
  continuous_of_isometric ((σ : RingAut K) : K →+* K) (IsoAut.norm σ)

lemma IsoAut.map_tsum (σ : IsoAut t) {ι : Type*} {f : ι → K} (hf : Summable f) :
    (σ : RingAut K) (∑' i, f i) = ∑' i, (σ : RingAut K) (f i) :=
  ((hf.hasSum.map ((σ : RingAut K) : K →+* K) (IsoAut.continuous σ)).tsum_eq).symm

lemma IsoAut.map_zpow_q (σ : IsoAut t) (n : ℤ) :
    (σ : RingAut K) ((t.q : K) ^ n) = (t.q : K) ^ n := by
  rw [map_zpow₀, IsoAut.q]

lemma IsoAut.map_eisenstein (σ : IsoAut t) (k : ℕ) :
    (σ : RingAut K) (t.eisenstein k) = t.eisenstein k := by
  rw [eisenstein, IsoAut.map_tsum σ (t.eisenstein_summand_summable k)]
  congr 1; funext n
  simp only [map_div₀, map_mul, map_pow, map_natCast, map_sub, map_one, IsoAut.q]

lemma IsoAut.map_a₄ (σ : IsoAut t) : (σ : RingAut K) t.a₄ = t.a₄ := by
  rw [a₄_def, map_mul, map_neg, map_ofNat, IsoAut.map_eisenstein]

lemma IsoAut.map_a₆ (σ : IsoAut t) : (σ : RingAut K) t.a₆ = t.a₆ := by
  rw [a₆_def, map_div₀, map_neg, map_add, map_mul, map_mul, map_ofNat, map_ofNat, map_ofNat,
    IsoAut.map_eisenstein, IsoAut.map_eisenstein]

/-- **`σ(X(u)) = X(σu)`.** -/
lemma IsoAut.map_X (σ : IsoAut t) (u : Kˣ) : (σ : RingAut K) (t.X u) = t.X (IsoAut.u σ u) := by
  rw [X_apply, X_apply, map_sub, map_mul, map_ofNat, IsoAut.map_eisenstein,
    IsoAut.map_tsum σ (t.Xterm_summable u)]
  congr 2; funext n
  simp only [Xterm_apply, map_div₀, map_mul, map_pow, map_sub, map_one, IsoAut.map_zpow_q,
    IsoAut.coe_u]

/-- **`σ(Y(u)) = Y(σu)`.** -/
lemma IsoAut.map_Y (σ : IsoAut t) (u : Kˣ) : (σ : RingAut K) (t.Y u) = t.Y (IsoAut.u σ u) := by
  rw [Y_apply, Y_apply, map_add, IsoAut.map_eisenstein, IsoAut.map_tsum σ (t.Yterm_summable u)]
  congr 2; funext n
  simp only [Yterm_apply, map_div₀, map_mul, map_pow, map_sub, map_one, IsoAut.map_zpow_q,
    IsoAut.coe_u]

/-- **`σ(θ(u)) = θ(σu)`.** -/
lemma IsoAut.map_theta (σ : IsoAut t) (u : Kˣ) :
    (σ : RingAut K) (t.theta u) = t.theta (IsoAut.u σ u) := by
  rw [theta, theta, IsoAut.map_tsum σ (t.thetaTerm_summable u)]
  congr 1; funext n
  simp only [thetaTerm, map_mul, map_zpow₀, IsoAut.q, IsoAut.coe_u]

lemma IsoAut.u_neg (σ : IsoAut t) (u : Kˣ) : IsoAut.u σ (-u) = -IsoAut.u σ u :=
  Units.ext (by simp only [IsoAut.coe_u, Units.val_neg, map_neg])

lemma offOrbit_iso (σ : IsoAut t) {w : Kˣ} (hw : OffOrbit t w) : OffOrbit t (IsoAut.u σ w) :=
  fun n hn => hw n (by
    have h := congrArg ((σ⁻¹ : IsoAut t) : RingAut K) hn
    rwa [map_mul, IsoAut.coe_u, IsoAut.inv_apply_apply, map_zpow₀, IsoAut.q, map_one] at h)

end Series

/-! ### `σ` on `Mero K`: `x(Ü²)`, `y(Ü²)`, `√(x - e)` -/

section MeroGal

/-- **An entire series whose values commute with `σ` off `q^ℤ` is `σ`-fixed.** -/
theorem Entire.map_iso_eq_self (σ : IsoAut t) {f : Entire K}
    (h : ∀ w : Kˣ, OffOrbit t w →
      (f : Kˣ → K) (IsoAut.u σ w) = (σ : RingAut K) ((f : Kˣ → K) w)) :
    Entire.map ((σ : RingAut K) : K →+* K) (IsoAut.norm σ) f = f := by
  rw [← sub_eq_zero]
  refine Entire.eq_zero_of_offOrbit t fun v hv => ?_
  have hv' : v = IsoAut.u σ (IsoAut.u (σ⁻¹ : IsoAut t) v) := (IsoAut.u_mul_inv σ v).symm
  have hw : OffOrbit t (IsoAut.u (σ⁻¹ : IsoAut t) v) := offOrbit_iso σ⁻¹ hv
  rw [Entire.coe_sub_apply, hv']
  erw [Entire.map_apply ((σ : RingAut K) : K →+* K) (IsoAut.norm σ) f]
  rw [h _ hw]
  exact sub_eq_zero.mpr rfl

lemma gal_thetaE (σ : IsoAut t) :
    Entire.map ((σ : RingAut K) : K →+* K) (IsoAut.norm σ) (thetaE t) = thetaE t :=
  Entire.map_iso_eq_self σ fun w _ => by
    rw [thetaE_apply, thetaE_apply, IsoAut.map_theta, IsoAut.u_neg]

lemma gal_xThetaE (σ : IsoAut t) :
    Entire.map ((σ : RingAut K) : K →+* K) (IsoAut.norm σ) (xThetaE t) = xThetaE t :=
  Entire.map_iso_eq_self σ fun w hw => by
    rw [xThetaE_apply t hw, xThetaE_apply t (offOrbit_iso σ hw), map_mul, map_pow, IsoAut.map_X,
      IsoAut.map_theta, IsoAut.u_neg]

lemma gal_yThetaE (σ : IsoAut t) :
    Entire.map ((σ : RingAut K) : K →+* K) (IsoAut.norm σ) (yThetaE t) = yThetaE t :=
  Entire.map_iso_eq_self σ fun w hw => by
    rw [yThetaE_apply t hw, yThetaE_apply t (offOrbit_iso σ hw), map_mul, map_pow, IsoAut.map_Y,
      IsoAut.map_theta, IsoAut.u_neg]

lemma gal_thetaSE (σ : IsoAut t) {s : Kˣ} (hσs : (σ : RingAut K) s = s) :
    Entire.map ((σ : RingAut K) : K →+* K) (IsoAut.norm σ) (thetaSE t s) = thetaSE t s :=
  Entire.map_iso_eq_self σ fun w _ => by
    rw [thetaSE_apply, thetaSE_apply, IsoAut.map_theta]
    congr 1
    ext
    simp only [IsoAut.coe_u, Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val, map_mul,
      map_neg, map_inv₀, hσs]

lemma Entire.map_sq (σ : IsoAut t) (f : Entire K) :
    Entire.map ((σ : RingAut K) : K →+* K) (IsoAut.norm σ) (Entire.sq f) =
      Entire.sq (Entire.map ((σ : RingAut K) : K →+* K) (IsoAut.norm σ) f) := by
  refine Entire.ext_coeff (funext fun n => ?_)
  rw [Entire.coeff_map, Entire.sq, Entire.sq, Entire.coeff_ofCoeff, Entire.coeff_ofCoeff,
    Entire.coeff_map]
  by_cases hn : ∃ m, dblEmb m = n
  · obtain ⟨m, rfl⟩ := hn
    simp only [dblEmb, sqCoeff_dbl]
  · simp only [sqCoeff_of_notMem _ hn, map_zero]

/-- `σ` commutes with `U = Ü²`. -/
lemma Mero.gal_sq (σ : IsoAut t) (x : Mero K) :
    Mero.gal σ (Mero.sq x) = Mero.sq (Mero.gal σ x) := by
  have : (Mero.gal σ).comp (Mero.sq (K := K)) = (Mero.sq (K := K)).comp (Mero.gal σ) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (Entire K)) (RingHom.ext fun f => by
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← Mero.ofE, Mero.sq_ofE, Mero.gal_ofE, Mero.gal_ofE, Mero.sq_ofE, Entire.map_sq])
  exact RingHom.congr_fun this x

lemma Mero.gal_const (σ : IsoAut t) (a : K) :
    Mero.gal σ (Mero.const a) = Mero.const ((σ : RingAut K) a) := by
  rw [Mero.gal_ofE, Entire.map_algebraMap]
  rfl

lemma gal_xU (σ : IsoAut t) : Mero.gal σ (xU t) = xU t := by
  rw [xU, map_div₀, map_pow, Mero.gal_ofE, Mero.gal_ofE, gal_xThetaE, gal_thetaE]

lemma gal_yU (σ : IsoAut t) : Mero.gal σ (yU t) = yU t := by
  rw [yU, map_div₀, map_pow, Mero.gal_ofE, Mero.gal_ofE, gal_yThetaE, gal_thetaE]

/-- **`σ` fixes `x(Ü²)`.** -/
theorem gal_xM (σ : IsoAut t) : Mero.gal σ (xM t) = xM t := by
  rw [xM, Mero.gal_sq, gal_xU]

/-- **`σ` fixes `y(Ü²)`.** -/
theorem gal_yM (σ : IsoAut t) : Mero.gal σ (yM t) = yM t := by
  rw [yM, Mero.gal_sq, gal_yU]

/-- **`σ` fixes the Kummer function `√(x - e)` when `σ(s) = s`.** -/
theorem gal_kumM (σ : IsoAut t) {s : Kˣ} (hσs : (σ : RingAut K) s = s) :
    Mero.gal σ (kumM t s) = kumM t s := by
  rw [kumM, map_div₀, Mero.gal_ofE, Mero.gal_ofE, map_mul, Entire.map_sq, Entire.map_sq,
    Entire.map_mono, gal_thetaSE σ hσs, gal_thetaE]

end MeroGal

/-! ### `σ` on `K[E_t]`, `K(E_t)` and the equivariance -/

section Field

variable (σ : IsoAut t)

lemma tateCurve_map_iso : t.tateCurve.map ((σ : RingAut K) : K →+* K) = t.tateCurve := by
  ext <;> simp [WeierstrassCurve.map, IsoAut.map_a₄, IsoAut.map_a₆]

lemma tatePolynomial_map_iso :
    t.tateCurve.toAffine.polynomial.map (mapRingHom ((σ : RingAut K) : K →+* K)) =
      t.tateCurve.toAffine.polynomial := by
  rw [← WeierstrassCurve.Affine.map_polynomial]
  exact congrArg (fun W : WeierstrassCurve K => W.toAffine.polynomial) (tateCurve_map_iso σ)

/-- **`σ` on `K[E_t]`** (on coefficients; `x ↦ x`, `y ↦ y`). -/
def tateRingGal : TateRing t →+* TateRing t :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp
    (mapRingHom ((σ : RingAut K) : K →+* K))) (AdjoinRoot.root _) (by
      rw [← Polynomial.eval₂_map, tatePolynomial_map_iso σ, AdjoinRoot.eval₂_root])

lemma tateRingGal_mk (p : K[X][X]) :
    tateRingGal σ (mkT t p) = mkT t (p.map (mapRingHom ((σ : RingAut K) : K →+* K))) := by
  rw [tateRingGal, mkT, WeierstrassCurve.Affine.CoordinateRing.mk, AdjoinRoot.lift_mk,
    ← Polynomial.eval₂_map, mkT, WeierstrassCurve.Affine.CoordinateRing.mk, ← AdjoinRoot.aeval_eq,
    Polynomial.aeval_def]
  rfl

lemma tateRingGal_inv_apply (a : TateRing t) : tateRingGal σ⁻¹ (tateRingGal σ a) = a := by
  induction a using AdjoinRoot.induction_on with
  | ih p =>
    change tateRingGal σ⁻¹ (tateRingGal σ (mkT t p)) = mkT t p
    rw [tateRingGal_mk, tateRingGal_mk, Polynomial.map_map]
    have hid : (mapRingHom (((σ⁻¹ : IsoAut t) : RingAut K) : K →+* K)).comp
        (mapRingHom ((σ : RingAut K) : K →+* K)) = RingHom.id _ := by
      refine RingHom.ext fun r => ?_
      rw [RingHom.comp_apply, coe_mapRingHom, coe_mapRingHom, Polynomial.map_map,
        show (((σ⁻¹ : IsoAut t) : RingAut K) : K →+* K).comp ((σ : RingAut K) : K →+* K) =
          RingHom.id K from RingHom.ext fun x => IsoAut.inv_apply_apply σ x,
        Polynomial.map_id, RingHom.id_apply]
    rw [hid, Polynomial.map_id]

lemma tateRingGal_injective : Function.Injective (tateRingGal σ) :=
  Function.LeftInverse.injective (tateRingGal_inv_apply σ)

/-- **`σ` on `K(E_t)`** (on coefficients). -/
def tateFieldGal : TateField t →+* TateField t :=
  IsFractionRing.lift (g := (algebraMap (TateRing t) (TateField t)).comp (tateRingGal σ))
    fun _ _ h => tateRingGal_injective σ (IsFractionRing.injective (TateRing t) (TateField t) h)

lemma tateFieldGal_algebraMap (a : TateRing t) :
    tateFieldGal σ (algebraMap (TateRing t) (TateField t) a) =
      algebraMap (TateRing t) (TateField t) (tateRingGal σ a) :=
  IsFractionRing.lift_algebraMap _ _

/-- **`σ ∘ (K[E_t] → Mero K) = (K[E_t] → Mero K) ∘ σ_*`.** -/
theorem gal_comp_tateRingHom (h12 : (12 : K) ≠ 0) :
    (Mero.gal σ).comp (tateRingHom t h12) = (tateRingHom t h12).comp (tateRingGal σ) := by
  refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) ?_) ?_
  · change Mero.gal σ (tateRingHom t h12 (mkT t (C (C a)))) =
      tateRingHom t h12 (tateRingGal σ (mkT t (C (C a))))
    rw [tateRingGal_mk, Polynomial.map_C, coe_mapRingHom, Polynomial.map_C, tateRingHom,
      RingHom.comp_apply, RingHom.comp_apply, tateRingHomU_mk_C, tateRingHomU_mk_C, eval₂_C,
      eval₂_C, constHom_apply, constHom_apply, Mero.gal_sq, Mero.gal_const]
    rfl
  · change Mero.gal σ (tateRingHom t h12 (mkT t (C Polynomial.X))) =
      tateRingHom t h12 (tateRingGal σ (mkT t (C Polynomial.X)))
    rw [tateRingGal_mk, Polynomial.map_C, coe_mapRingHom, Polynomial.map_X, tateRingHom_x, gal_xM]
  · change Mero.gal σ (tateRingHom t h12 (mkT t Polynomial.X)) =
      tateRingHom t h12 (tateRingGal σ (mkT t Polynomial.X))
    rw [tateRingGal_mk, Polynomial.map_X, tateRingHom_y, gal_yM]

/-- **Galois equivariance of `K(E_t) → Mero K`**: `σ ∘ tateFieldHom = tateFieldHom ∘ σ_*`. -/
theorem gal_comp_tateFieldHom (h12 : (12 : K) ≠ 0) :
    (Mero.gal σ).comp (tateFieldHom t h12) = (tateFieldHom t h12).comp (tateFieldGal σ) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (TateRing t)) (RingHom.ext fun a => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [tateFieldHom_algebraMap, tateFieldGal_algebraMap, tateFieldHom_algebraMap]
  exact RingHom.congr_fun (gal_comp_tateRingHom σ h12) a

/-- **`⟨c, σ⟩ ∈ GalDeck t` acts on `K(E_t) ⊆ Mero K` by `σ_*`** (the deck part acts trivially). -/
theorem galDeckHom_tateFieldHom (h12 : (12 : K) ≠ 0) (x : GalDeck t) (f : TateField t) :
    galDeckHom t x (tateFieldHom t h12 f) = tateFieldHom t h12 (tateFieldGal x.right f) := by
  rw [galDeckHom_apply]
  rw [show Mero.gal x.right (tateFieldHom t h12 f) = tateFieldHom t h12 (tateFieldGal x.right f)
    from RingHom.congr_fun (gal_comp_tateFieldHom x.right h12) f]
  exact RingHom.congr_fun (scale_comp_tateFieldHom h12 x.left⁻¹) _

end Field

/-! ### The `F`-curve of tfg's Tate data -/

section Data

variable {F : Type u} [Field F] {O : ValuationSubring F} {R : Type u} [CommRing R] [Algebra F R]

/-- **`σ` fixing `φ(F)` fixes the image of the coordinate ring of the `F`-curve of `D`.** -/
theorem gal_dataRingHom (φ : F →+* K) (D : TemperedFundamentalGroups.TateObject.Data O R)
    (hT : IsTateParam φ D t) (h12 : (12 : K) ≠ 0) (σ : IsoAut t)
    (hσ : ∀ a, (σ : RingAut K) (φ a) = φ a) :
    (Mero.gal σ).comp (dataRingHom t φ D hT h12) = dataRingHom t φ D hT h12 := by
  refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) ?_) ?_
  · change Mero.gal σ (dataRingHom t φ D hT h12
        (WeierstrassCurve.Affine.CoordinateRing.mk _ (C (C a)))) =
      dataRingHom t φ D hT h12 (WeierstrassCurve.Affine.CoordinateRing.mk _ (C (C a)))
    rw [dataRingHom_mk_C, eval₂_C, RingHom.comp_apply, constHom_apply, Mero.gal_const, hσ]
  · change Mero.gal σ (dataRingHom t φ D hT h12
        (WeierstrassCurve.Affine.CoordinateRing.mk _ (C Polynomial.X))) =
      dataRingHom t φ D hT h12 (WeierstrassCurve.Affine.CoordinateRing.mk _ (C Polynomial.X))
    rw [dataRingHom_mk_C, eval₂_X, gal_xM]
  · change Mero.gal σ (dataRingHom t φ D hT h12
        (WeierstrassCurve.Affine.CoordinateRing.mk _ Polynomial.X)) =
      dataRingHom t φ D hT h12 (WeierstrassCurve.Affine.CoordinateRing.mk _ Polynomial.X)
    rw [dataRingHom_y, gal_yM]

end Data

/-! ### The Tate action of `Π^tp_X` on `K(X') ⊆ Mero K` -/

section Pi

open CategoryTheory TemperedFundamentalGroups TemperedFundamentalGroups.TateObject Pi1.Orbifold

variable {F : Type u} [Field F] {O : ValuationSubring F}
  {R : Type u} [CommRing R] [Algebra F R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra F Ω] [Algebra R Ω] [IsScalarTower F R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap F Ω) = O)
  [IsReduced R] (D : TateObject.DoubleData O R) (sΩ : Ω) (hsΩ : sΩ ^ 2 = algebraMap R Ω D.c)

/-- **`g ∈ Π^tp_X` acts on `√(x - e)` by the sign of `character₂ g`** under the Tate action
`tateGalDeck σ hσ` (Galois part fixing `s`, deck part `tateDeck`). -/
theorem galDeckHom_tateGalDeck_kumM {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    (σ : temperedPi1 O R A V hV →* IsoAut t) (hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s)
    (g : temperedPi1 O R A V hV) :
    galDeckHom t (tateGalDeck V hV D sΩ hsΩ hs σ hσ g) (kumM t s) =
      if (character₂ (A := A) D V hV sΩ hsΩ g).2 = 1 then kumM t s else -kumM t s := by
  rw [galDeckHom_apply, tateGalDeck_right, gal_kumM (σ g) (hσ g), tateGalDeck_left]
  exact deckHom_tateDeck_kumM V hV D sΩ hsΩ hs g

/-- **`g ∈ Π^tp_X` acts on `K(E_t) ⊆ Mero K` by `σ(g)_*`** under the Tate action. -/
theorem galDeckHom_tateGalDeck_tateFieldHom (h12 : (12 : K) ≠ 0) {s : Kˣ}
    (hs : (s : K) ^ 2 = t.q) (σ : temperedPi1 O R A V hV →* IsoAut t)
    (hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s) (g : temperedPi1 O R A V hV)
    (f : TateField t) :
    galDeckHom t (tateGalDeck V hV D sΩ hsΩ hs σ hσ g) (tateFieldHom t h12 f) =
      tateFieldHom t h12 (tateFieldGal (σ g) f) := by
  rw [galDeckHom_tateFieldHom, tateGalDeck_right]

end Pi

end Iut.Frobenioid.BAn
