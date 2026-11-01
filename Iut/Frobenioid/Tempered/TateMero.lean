/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.EllDiv
import Iut.EtaleTheta.TateFunctionField

/-!
# Tate's functions `x(U)`, `y(U)` in `Mero K` and the function field of `E_t` (MR18 T7c)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*
(text `~/iut-scratch/wall/txt/The Etale Theta Function …txt`, cited by line).

The B-an model of `Ÿ_∞` is `𝔾_m^an` with coordinate `Ü` (`Mero K = Frac E(K)`, `RatFunMero`);
the Tate curve `E_t = 𝔾_m/q^ℤ` has the coordinate `U = Ü²`. This file is the analytic half of
the comparison of tempered-fundamental-groups' schematic Tate curve with this model:

* `Entire.sq`, `Mero.sq`: the substitution `U = Ü²` (`f ↦ f(Ü²)`), an injective ring map, with
  `Mero.scale c ∘ Mero.sq = Mero.sq ∘ Mero.scale c²` (`Mero.scale_sq`).
* `Entire.eq_zero_of_offOrbit`: an entire Laurent series vanishing off the orbit `q^ℤ` is zero
  (the Lipschitz bound `norm_lsum_sub_le` at the orbit points).
* `thetaE t` (`θ(-U)`), `xThetaE t` (`x(U)θ(-U)²`), `yThetaE t` (`y(U)θ(-U)³`), `thetaSE t s`
  (`θ(-U/s)`): elements of `E(K)` from tate-curves-theta's weight families.
* **`xU t`, `yU t`** (Tate's `x(U)`, `y(U)`, tate-curves-theta `TateParameter.X`, `Y`) and
  **`xM t = x(Ü²)`, `yM t = y(Ü²)`** in `Mero K`; `yM_sq_add`: the Weierstrass equation of `E_t`.
* **`tateRingHom t h12 : K[E_t] →+* Mero K`** (`x ↦ x(Ü²)`, `y ↦ y(Ü²)`), injective
  (`tateRingHomU_injective`: values at the Tate points and `eq_zero_of_evalTate`), and
  **`tateFieldHom t h12 : K(E_t) →+* Mero K`**: the function field of `E_t` inside the
  meromorphic functions on `Ÿ_∞`.
* **Deck invariance**: `scale_xM`, `scale_yM`: `Ü ↦ c·Ü` fixes `x(Ü²)`, `y(Ü²)` for every
  `c ∈ Deck t` (`c² ∈ q^ℤ`).
* **The point of `s`** (`s² = q`): `offOrbit_s`; `two_Y_s_add_X_s`: the Tate point of `U = s` is
  the `2`-torsion point `(e, -e/2)`, `e = X(s)` (the generator of the kernel of the dual of the
  `2`-isogeny `E_s → E_t`, `Ü ↦ Ü² = U`; tfg `TateObjectDouble` docstring).
* **The analytic Kummer function** `kumM t s = θ(-Ü²/s)/(Ü·θ(-Ü²))`: `kumM_sq`
  (`kumM² = β⁻¹·(x(Ü²) - e)`, `β ≠ 0`, from the two-dimensional weight space `W(2, Aθ²)` and the
  zero of `θ(-U/s)θ(-sU)` at `U = s`), `scale_neg_one_kumM` (`Ü ↦ -Ü` negates it) and
  `scale_s_kumM` (`Ü ↦ s·Ü` fixes it): `√(x - e)` is a meromorphic function on `Ÿ_∞`, and the
  deck group acts on it through `ℤ × ℤ/2 → ℤ/2`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open TateCurvesTheta TateParameter Polynomial Iut.EtaleTheta

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! ### The substitution `U = Ü²` -/

/-- `n ↦ 2n`. -/
def dblEmb (n : ℤ) : ℤ := 2 * n

lemma dblEmb_injective : Function.Injective dblEmb := fun a b h => by
  simp only [dblEmb] at h; omega

/-- The coefficients of `f(Ü²)`. -/
def sqCoeff (c : ℤ → K) : ℤ → K := Function.extend dblEmb c 0

lemma sqCoeff_dbl (c : ℤ → K) (n : ℤ) : sqCoeff c (2 * n) = c n :=
  dblEmb_injective.extend_apply _ _ n

lemma sqCoeff_of_notMem (c : ℤ → K) {n : ℤ} (hn : ¬ ∃ m, dblEmb m = n) : sqCoeff c n = 0 := by
  rw [sqCoeff, Function.extend_apply' _ _ _ hn, Pi.zero_apply]

lemma hasSum_sqCoeff {c : ℤ → K} {u : Kˣ} {a : K}
    (h : HasSum (fun n : ℤ => c n * ((u ^ 2 : Kˣ) : K) ^ n) a) :
    HasSum (fun n : ℤ => sqCoeff c n * (u : K) ^ n) a := by
  rw [← Function.Injective.hasSum_iff dblEmb_injective (fun n hn => by
    rw [sqCoeff_of_notMem c (by simpa using hn), zero_mul])]
  refine h.congr_fun fun m => ?_
  simp only [Function.comp_apply, dblEmb, sqCoeff_dbl, Units.val_pow_eq_pow_val]
  rw [zpow_mul, zpow_ofNat]

lemma IsEntire.sqCoeff {c : ℤ → K} (hc : IsEntire c) : IsEntire (sqCoeff c) := fun u =>
  (hasSum_sqCoeff (hc.hasSum (u ^ 2))).summable

namespace Entire

/-- **`f ↦ f(Ü²)`** on entire Laurent series. -/
def sq (f : Entire K) : Entire K := ofCoeff (sqCoeff (coeff f)) (isEntire_coeff f).sqCoeff

lemma coe_sq (f : Entire K) (u : Kˣ) : ((sq f : Entire K) : Kˣ → K) u = (f : Kˣ → K) (u ^ 2) :=
  (hasSum_sqCoeff (coeff_spec f (u ^ 2))).tsum_eq

lemma coe_mul_apply (f g : Entire K) (u : Kˣ) :
    ((f * g : Entire K) : Kˣ → K) u = (f : Kˣ → K) u * (g : Kˣ → K) u := rfl

lemma coe_add_apply (f g : Entire K) (u : Kˣ) :
    ((f + g : Entire K) : Kˣ → K) u = (f : Kˣ → K) u + (g : Kˣ → K) u := rfl

lemma coe_sub_apply (f g : Entire K) (u : Kˣ) :
    ((f - g : Entire K) : Kˣ → K) u = (f : Kˣ → K) u - (g : Kˣ → K) u := rfl

lemma coe_pow_apply (f : Entire K) (n : ℕ) (u : Kˣ) :
    ((f ^ n : Entire K) : Kˣ → K) u = (f : Kˣ → K) u ^ n := by
  rw [SubmonoidClass.coe_pow, Pi.pow_apply]

lemma coe_algebraMap_apply (a : K) (u : Kˣ) :
    ((algebraMap K (Entire K) a : Entire K) : Kˣ → K) u = a := rfl

lemma coe_one_apply (u : Kˣ) : ((1 : Entire K) : Kˣ → K) u = 1 := rfl

lemma coe_zero_apply (u : Kˣ) : ((0 : Entire K) : Kˣ → K) u = 0 := rfl

lemma coe_mono_apply (k : ℤ) (u : Kˣ) : ((mono k : Entire K) : Kˣ → K) u = (u : K) ^ k := by
  rw [coe_mono]

lemma ext_apply {f g : Entire K} (h : ∀ u, (f : Kˣ → K) u = (g : Kˣ → K) u) : f = g :=
  Subtype.ext (funext h)

/-- `f ↦ f(Ü²)` as a ring map. -/
def sqHom : Entire K →+* Entire K where
  toFun := sq
  map_one' := ext_apply fun u => by rw [coe_sq]; rfl
  map_mul' f g := ext_apply fun u => by rw [coe_sq, coe_mul_apply, coe_mul_apply, coe_sq, coe_sq]
  map_zero' := ext_apply fun u => by rw [coe_sq]; rfl
  map_add' f g := ext_apply fun u => by rw [coe_sq, coe_add_apply, coe_add_apply, coe_sq, coe_sq]

lemma sqHom_apply (f : Entire K) : sqHom f = sq f := rfl

lemma sqHom_injective : Function.Injective (sqHom (K := K)) := fun f g h => by
  apply ext_coeff
  funext n
  have h' := congrArg (fun f => coeff f (2 * n)) h
  simp only [sqHom_apply, sq, coeff_ofCoeff, sqCoeff_dbl] at h'
  exact h'

lemma sq_mono (k : ℤ) : sq (mono k : Entire K) = mono (2 * k) := ext_apply fun u => by
  rw [coe_sq, coe_mono_apply, coe_mono_apply, Units.val_pow_eq_pow_val, ← zpow_natCast,
    ← zpow_mul]; norm_num

lemma sq_algebraMap (a : K) : sq (algebraMap K (Entire K) a) = algebraMap K (Entire K) a :=
  ext_apply fun u => by rw [coe_sq]; rfl

lemma scale_sq (c : Kˣ) (f : Entire K) : scale c (sq f) = sq (scale (c ^ 2) f) :=
  ext_apply fun u => by rw [coe_scale, coe_sq, coe_sq, coe_scale, mul_pow]

end Entire

namespace Mero

/-- **`f ↦ f(Ü²)`** on `Mero K`. -/
def sq : Mero K →+* Mero K :=
  IsFractionRing.lift (K := Mero K) (g := (algebraMap (Entire K) (Mero K)).comp Entire.sqHom)
    (ofE_injective.comp Entire.sqHom_injective)

lemma sq_ofE (f : Entire K) : sq (ofE f) = ofE (Entire.sq f) :=
  IsFractionRing.lift_algebraMap _ _

lemma sq_injective : Function.Injective (sq (K := K)) := (sq (K := K)).injective

lemma scale_sq (c : Kˣ) (x : Mero K) : scale c (sq x) = sq (scale (c ^ 2) x) := by
  have : (scale c).comp (sq (K := K)) = sq.comp (scale (c ^ 2)) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (Entire K)) (RingHom.ext fun f => by
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← ofE, sq_ofE, scale_ofE, scale_ofE, sq_ofE, Entire.scale_sq])
  exact RingHom.congr_fun this x

lemma sq_const (a : K) : sq (const a) = const a := by rw [sq_ofE, Entire.sq_algebraMap]

lemma ofE_add' (f g : Entire K) : ofE (f + g) = ofE f + ofE g :=
  (algebraMap (Entire K) (Mero K)).map_add f g

lemma ofE_neg (f : Entire K) : ofE (-f) = -ofE f := (algebraMap (Entire K) (Mero K)).map_neg f

/-- `Ü ↦ (d·c)·Ü` is `Ü ↦ c·Ü` after `Ü ↦ d·Ü`. -/
lemma scale_mul_apply (c d : Kˣ) (x : Mero K) : scale (d * c) x = scale c (scale d x) := by
  have : (scale c).comp (scale d) = scale (K := K) (d * c) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (Entire K)) (RingHom.ext fun f => by
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← ofE, scale_ofE, scale_ofE, scale_ofE, Entire.scale_scale])
  exact (RingHom.congr_fun this x).symm

lemma scale_one_apply (x : Mero K) : scale 1 x = x := by
  have : scale (K := K) 1 = RingHom.id _ :=
    IsLocalization.ringHom_ext (nonZeroDivisors (Entire K)) (RingHom.ext fun f => by
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [← ofE, scale_ofE, Entire.scale_one])
  exact RingHom.congr_fun this x

/-- Two quotients agree when the cross products agree pointwise. -/
lemma div_eq_div_of_apply {a b a' b' : Entire K} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (h : ∀ u, (a : Kˣ → K) u * (b' : Kˣ → K) u = (a' : Kˣ → K) u * (b : Kˣ → K) u) :
    ofE a / ofE b = ofE a' / ofE b' := by
  rw [div_eq_div_iff (ofE_ne_zero hb) (ofE_ne_zero hb'), ← ofE_mul, ← ofE_mul]
  exact congrArg ofE (Entire.ext_apply fun u => by
    rw [Entire.coe_mul_apply, Entire.coe_mul_apply]; exact h u)

end Mero

/-! ### The identity principle off the orbit `q^ℤ` -/

lemma exists_small_unit {r : ℝ} (hr : 0 < r) : ∃ x : Kˣ, ‖(x : K)‖ = 1 ∧ x ≠ 1 ∧
    ‖(x : K) - 1‖ < r := by
  obtain ⟨ε, hε0, hεr⟩ := NormedField.exists_norm_lt K (lt_min hr one_pos)
  have hε1 : ‖ε‖ < 1 := hεr.trans_le (min_le_right _ _)
  have hn : ‖(1 : K) + ε‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hε1.ne'),
      norm_one, max_eq_left hε1.le]
  have h0 : (1 : K) + ε ≠ 0 := fun h => by rw [h, norm_zero] at hn; exact zero_ne_one hn
  refine ⟨Units.mk0 _ h0, hn, fun h => ?_, ?_⟩
  · have := congrArg Units.val h
    simp only [Units.val_mk0, Units.val_one, add_eq_left] at this
    exact (norm_pos_iff.mp hε0) this
  · simp only [Units.val_mk0, add_sub_cancel_left]
    exact hεr.trans_le (min_le_left _ _)

/-- An entire series vanishing on the unit circle off `1` vanishes at `1`. -/
lemma Entire.apply_one_eq_zero {f : Entire K}
    (h : ∀ x : Kˣ, ‖(x : K)‖ = 1 → x ≠ 1 → (f : Kˣ → K) x = 0) : (f : Kˣ → K) 1 = 0 := by
  by_contra hne
  have hpos : 0 < ‖(f : Kˣ → K) 1‖ := norm_pos_iff.mpr hne
  set G := gnorm (Entire.coeff f) 1
  have hG : 0 ≤ G := gnorm_nonneg (Entire.isEntire_coeff f) one_pos
  obtain ⟨x, hx1, hxne, hxr⟩ := exists_small_unit (K := K) (r := ‖(f : Kˣ → K) 1‖ / (G + 1))
    (div_pos hpos (by linarith))
  have hb := norm_lsum_sub_le (Entire.isEntire_coeff f) (x := 1) (y := x)
    (by simp) hx1
  rw [← Entire.coe_eq_lsum, h x hx1 hxne, sub_zero, Units.val_one, norm_sub_rev] at hb
  have : G * ‖(x : K) - 1‖ < ‖(f : Kˣ → K) 1‖ := by
    calc G * ‖(x : K) - 1‖ ≤ (G + 1) * ‖(x : K) - 1‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (G + 1) * (‖(f : Kˣ → K) 1‖ / (G + 1)) :=
          mul_lt_mul_of_pos_left hxr (by linarith)
      _ = ‖(f : Kˣ → K) 1‖ := by field_simp
  linarith

/-- **An entire Laurent series vanishing off the orbit `q^ℤ` is zero.** -/
theorem Entire.eq_zero_of_offOrbit (t : TateParameter K) {f : Entire K}
    (h : ∀ u : Kˣ, OffOrbit t u → (f : Kˣ → K) u = 0) : f = 0 := by
  refine Entire.ext_apply fun u => ?_
  by_cases hu : OffOrbit t u
  · exact h u hu
  · simp only [OffOrbit, not_forall, not_not] at hu
    obtain ⟨m, hm⟩ := hu
    have key := Entire.apply_one_eq_zero (f := Entire.scale u f) fun x hx1 hxne => by
      rw [Entire.coe_scale]
      refine h _ fun n hn => hxne ?_
      have hx : (x : K) = (t.q : K) ^ (m - n) := by
        rw [Units.val_mul] at hn
        have e : (u : K) * ((x : K) * (t.q : K) ^ n - (t.q : K) ^ m) = 0 := by
          linear_combination hn - hm
        have e' := sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left u.ne_zero)
        rw [zpow_sub₀ t.q.ne_zero, ← e', mul_div_cancel_right₀ _ (zpow_ne_zero _ t.q.ne_zero)]
      have hmn : m - n = 0 := by
        have h1 := congrArg norm hx
        rw [hx1, norm_zpow] at h1
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact absurd h1.symm (one_lt_zpow_of_neg₀ t.norm_q_pos t.norm_lt_one hlt).ne'
        · exact absurd h1.symm (zpow_lt_one₀ t.norm_q_pos t.norm_lt_one hgt).ne
      exact Units.ext (by rw [hx, hmn, zpow_zero, Units.val_one])
    rwa [Entire.coe_scale, mul_one] at key

/-! ### Entire series from tate-curves-theta's weight families -/

section Fam

variable (t : TateParameter K)

/-- `θ(-U)` (tate-curves-theta `thetaBlock (-1)`). -/
def thetaE : Entire K :=
  Entire.ofCoeff (t.thetaBlock (-1)) (isWeightFamily_thetaBlock (t := t) (-1)).summable

/-- `θ(-U/s)`. -/
def thetaSE (s : Kˣ) : Entire K :=
  Entire.ofCoeff (t.thetaBlock (-s⁻¹)) (isWeightFamily_thetaBlock (t := t) (-s⁻¹)).summable

/-- `x(U)·θ(-U)²` (tate-curves-theta `XThetaSqCoeff`). -/
def xThetaE : Entire K := Entire.ofCoeff t.XThetaSqCoeff t.isWeightFamily_XThetaSq.summable

/-- `y(U)·θ(-U)³` (tate-curves-theta `YThetaCubeCoeff`). -/
def yThetaE : Entire K := Entire.ofCoeff t.YThetaCubeCoeff t.isWeightFamily_YThetaCube.summable

lemma coe_ofCoeff_apply (c : ℤ → K) (hc : IsEntire c) (u : Kˣ) :
    ((Entire.ofCoeff c hc : Entire K) : Kˣ → K) u = ∑' n : ℤ, c n * (u : K) ^ n := rfl

lemma thetaE_apply (u : Kˣ) : ((thetaE t : Entire K) : Kˣ → K) u = t.theta (-u) := by
  rw [thetaE, coe_ofCoeff_apply, tsum_thetaBlock, neg_one_mul]

lemma thetaSE_apply (s u : Kˣ) :
    ((thetaSE t s : Entire K) : Kˣ → K) u = t.theta (-s⁻¹ * u) := by
  rw [thetaSE, coe_ofCoeff_apply, tsum_thetaBlock]

lemma xThetaE_apply {u : Kˣ} (hu : OffOrbit t u) :
    ((xThetaE t : Entire K) : Kˣ → K) u = t.X u * t.theta (-u) ^ 2 :=
  (t.hasSum_XThetaSqCoeff hu).tsum_eq

lemma yThetaE_apply {u : Kˣ} (hu : OffOrbit t u) :
    ((yThetaE t : Entire K) : Kˣ → K) u = t.Y u * t.theta (-u) ^ 3 :=
  (t.hasSum_YThetaCubeCoeff hu).tsum_eq

/-- `u ↦ q·u` on a weight family. -/
lemma ofCoeff_q_apply {k : ℕ} {A : Kˣ} {c : ℤ → K} (hc : t.IsWeightFamily k A c) (u : Kˣ) :
    ((Entire.ofCoeff c hc.summable : Entire K) : Kˣ → K) (t.q * u) =
      (A : K) * (u : K) ^ (-(k : ℤ)) * ((Entire.ofCoeff c hc.summable : Entire K) : Kˣ → K) u := by
  rw [coe_ofCoeff_apply, coe_ofCoeff_apply, ← hc.tsum_q_smul u, Units.val_mul]

lemma offOrbit_exists : ∃ u : Kˣ, OffOrbit t u := ⟨unitSeq t 0, offOrbit_unitSeq t 0⟩

lemma thetaE_ne_zero : thetaE t ≠ 0 := fun h => by
  obtain ⟨u, hu⟩ := offOrbit_exists t
  have := thetaE_apply t u
  rw [h, Entire.coe_zero_apply] at this
  exact t.theta_neg_ne_zero hu this.symm

/-- **The Weierstrass equation** `(yθ³)² + (xθ²)(yθ³)θ = (xθ²)³ + a₄(xθ²)θ⁴ + a₆θ⁶` in `E(K)`. -/
theorem weierstrass_entire (h12 : (12 : K) ≠ 0) :
    yThetaE t ^ 2 + xThetaE t * yThetaE t * thetaE t =
      xThetaE t ^ 3 + algebraMap K (Entire K) t.a₄ * xThetaE t * thetaE t ^ 4 +
        algebraMap K (Entire K) t.a₆ * thetaE t ^ 6 := by
  rw [← sub_eq_zero]
  refine Entire.eq_zero_of_offOrbit t fun u hu => ?_
  have h := (WeierstrassCurve.Affine.equation_iff _ _).mp (t.tatePoint_mem' h12 hu)
  simp only [tateCurve_a₁, tateCurve_a₂, tateCurve_a₃, tateCurve_a₄, tateCurve_a₆] at h
  simp only [Entire.coe_sub_apply, Entire.coe_add_apply, Entire.coe_mul_apply,
    Entire.coe_pow_apply, Entire.coe_algebraMap_apply, xThetaE_apply t hu, yThetaE_apply t hu,
    thetaE_apply]
  linear_combination t.theta (-u) ^ 6 * h

end Fam

/-! ### `x(U)`, `y(U)` and `x(Ü²)`, `y(Ü²)` in `Mero K` -/

section XY

variable (t : TateParameter K)

/-- **Tate's `x(U)`** in `Mero K` (variable `U`): `x(U)θ(-U)²/θ(-U)²`. -/
def xU : Mero K := Mero.ofE (xThetaE t) / Mero.ofE (thetaE t) ^ 2

/-- **Tate's `y(U)`** in `Mero K` (variable `U`). -/
def yU : Mero K := Mero.ofE (yThetaE t) / Mero.ofE (thetaE t) ^ 3

/-- **`x(Ü²)`**: Tate's `x` on `Ÿ_∞ = 𝔾_m^an`. -/
def xM : Mero K := Mero.sq (xU t)

/-- **`y(Ü²)`**: Tate's `y` on `Ÿ_∞ = 𝔾_m^an`. -/
def yM : Mero K := Mero.sq (yU t)

lemma ofE_thetaE_ne_zero : Mero.ofE (thetaE t) ≠ 0 := Mero.ofE_ne_zero (thetaE_ne_zero t)

/-- **The Weierstrass equation of `E_t`** for `(x(U), y(U))` in `Mero K`. -/
theorem yU_sq_add (h12 : (12 : K) ≠ 0) :
    yU t ^ 2 + xU t * yU t = xU t ^ 3 + Mero.const t.a₄ * xU t + Mero.const t.a₆ := by
  have h := congrArg Mero.ofE (weierstrass_entire t h12)
  simp only [map_add, map_mul, map_pow] at h
  have h0 := ofE_thetaE_ne_zero t
  rw [xU, yU]
  field_simp
  linear_combination h

/-- **The Weierstrass equation of `E_t`** for `(x(Ü²), y(Ü²))`. -/
theorem yM_sq_add (h12 : (12 : K) ≠ 0) :
    yM t ^ 2 + xM t * yM t = xM t ^ 3 + Mero.const t.a₄ * xM t + Mero.const t.a₆ := by
  have e := yU_sq_add t h12
  let φ := Mero.sq (K := K)
  calc yM t ^ 2 + xM t * yM t = φ (yU t ^ 2 + xU t * yU t) := by
        rw [φ.map_add, φ.map_pow, φ.map_mul]; rfl
    _ = φ (xU t ^ 3 + Mero.const t.a₄ * xU t + Mero.const t.a₆) := by rw [e]
    _ = _ := by
        rw [φ.map_add, φ.map_add, φ.map_pow, φ.map_mul]
        rw [show φ (Mero.const t.a₄) = Mero.const t.a₄ from Mero.sq_const _,
          show φ (Mero.const t.a₆) = Mero.const t.a₆ from Mero.sq_const _]
        rfl

end XY

/-! ### `K[E_t] → Mero K` and `K(E_t) → Mero K` -/

section Ring

variable (t : TateParameter K)

/-- The field of constants `K → Mero K`. -/
abbrev constHom : K →+* Mero K := (algebraMap (Entire K) (Mero K)).comp (algebraMap K (Entire K))

lemma constHom_apply (a : K) : constHom a = Mero.const a := rfl

set_option synthInstance.maxHeartbeats 100000 in
-- the instance path `Mero K →+* Mero K`, `Field (Mero K)` is slow at the default budget
/-- **`K[E_t] → Mero K`** in the variable `U`: `x ↦ x(U)`, `y ↦ y(U)`. -/
def tateRingHomU (h12 : (12 : K) ≠ 0) : TateRing t →+* Mero K :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (constHom (K := K)) (xU t)) (yU t) (by
    have h := yU_sq_add t h12
    simp only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow,
      eval₂_X, eval₂_C, coe_eval₂RingHom, tateCurve_a₁, tateCurve_a₂, tateCurve_a₃,
      tateCurve_a₄, tateCurve_a₆, eval₂_one, eval₂_zero, map_one, map_zero, constHom_apply]
    linear_combination h)

lemma tateRingHomU_mk_C (h12 : (12 : K) ≠ 0) (p : K[X]) :
    tateRingHomU t h12 (mkT t (C p)) = p.eval₂ constHom (xU t) := by
  rw [tateRingHomU, mkT, WeierstrassCurve.Affine.CoordinateRing.mk, AdjoinRoot.lift_mk,
    eval₂_C, coe_eval₂RingHom]

lemma tateRingHomU_mk_Y (h12 : (12 : K) ≠ 0) :
    tateRingHomU t h12 (mkT t Polynomial.X) = yU t := by
  rw [tateRingHomU, mkT, WeierstrassCurve.Affine.CoordinateRing.mk, AdjoinRoot.lift_mk, eval₂_X]

/-- `m` **has the values `V` at the Tate points**: `θ(-U)^k·m` is entire, with value
`θ(-u)^k·V(u)` at every `u` off the orbit `q^ℤ`. -/
def HasVals (m : Mero K) (V : Kˣ → K) : Prop :=
  ∃ (k : ℕ) (H : Entire K), Mero.ofE (thetaE t) ^ k * m = Mero.ofE H ∧
    ∀ u, OffOrbit t u → (H : Kˣ → K) u = t.theta (-u) ^ k * V u

variable {t}

lemma HasVals.congr {m : Mero K} {V V' : Kˣ → K} (h : HasVals t m V)
    (hV : ∀ u, OffOrbit t u → V u = V' u) : HasVals t m V' := by
  obtain ⟨k, H, e, hv⟩ := h
  exact ⟨k, H, e, fun u hu => by rw [hv u hu, hV u hu]⟩

lemma HasVals.const (c : K) : HasVals t (Mero.const c) (fun _ => c) :=
  ⟨0, algebraMap K (Entire K) c, by rw [pow_zero, one_mul], fun u _ => by
    rw [pow_zero, one_mul]; rfl⟩

lemma HasVals.add {m m' : Mero K} {V V' : Kˣ → K} (h : HasVals t m V) (h' : HasVals t m' V') :
    HasVals t (m + m') (fun u => V u + V' u) := by
  obtain ⟨k, H, e, hv⟩ := h
  obtain ⟨k', H', e', hv'⟩ := h'
  refine ⟨k + k', thetaE t ^ k' * H + thetaE t ^ k * H', ?_, fun u hu => ?_⟩
  · rw [Mero.ofE_add', Mero.ofE_mul, Mero.ofE_mul, Mero.ofE_pow, Mero.ofE_pow, ← e, ← e']
    ring
  · rw [Entire.coe_add_apply, Entire.coe_mul_apply, Entire.coe_mul_apply, Entire.coe_pow_apply,
      Entire.coe_pow_apply, hv u hu, hv' u hu, thetaE_apply]
    ring

lemma HasVals.mul {m m' : Mero K} {V V' : Kˣ → K} (h : HasVals t m V) (h' : HasVals t m' V') :
    HasVals t (m * m') (fun u => V u * V' u) := by
  obtain ⟨k, H, e, hv⟩ := h
  obtain ⟨k', H', e', hv'⟩ := h'
  refine ⟨k + k', H * H', ?_, fun u hu => ?_⟩
  · rw [Mero.ofE_mul, ← e, ← e']
    ring
  · rw [Entire.coe_mul_apply, hv u hu, hv' u hu]
    ring

variable (t)

lemma hasVals_xU : HasVals t (xU t) (fun u => t.X u) :=
  ⟨2, xThetaE t, by rw [xU]; field_simp [ofE_thetaE_ne_zero t], fun u hu => by
    rw [xThetaE_apply t hu]; ring⟩

lemma hasVals_yU : HasVals t (yU t) (fun u => t.Y u) :=
  ⟨3, yThetaE t, by rw [yU]; field_simp [ofE_thetaE_ne_zero t], fun u hu => by
    rw [yThetaE_apply t hu]; ring⟩

lemma hasVals_eval₂ (p : K[X]) :
    HasVals t (p.eval₂ constHom (xU t)) (fun u => p.eval (t.X u)) := by
  induction p using Polynomial.induction_on with
  | C a =>
    rw [eval₂_C, constHom_apply]
    exact (HasVals.const a).congr fun u _ => (eval_C).symm
  | add p q hp hq =>
    rw [eval₂_add]
    exact (hp.add hq).congr fun u _ => by rw [eval_add]
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, eval₂_mul, eval₂_X]
    exact (h.mul (hasVals_xU t)).congr fun u _ => by
      simp only [eval_mul, eval_X, eval_C, eval_pow]

open scoped Classical in
theorem hasVals_tateRingHomU (h12 : (12 : K) ≠ 0) (a : TateRing t) :
    HasVals t (tateRingHomU t h12 a)
      (fun u => if hu : OffOrbit t u then evalTate t h12 hu a else 0) := by
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  have e : tateRingHomU t h12 (p • (1 : TateRing t) + q • mkT t Polynomial.X) =
      p.eval₂ constHom (xU t) + yU t * q.eval₂ constHom (xU t) := by
    rw [WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul,
      map_add, map_mul, map_mul, map_one, mul_one, ← mkT, ← mkT, tateRingHomU_mk_C,
      tateRingHomU_mk_C, tateRingHomU_mk_Y, mul_comm]
  rw [e]
  exact ((hasVals_eval₂ t p).add ((hasVals_yU t).mul (hasVals_eval₂ t q))).congr fun u hu => by
    rw [dif_pos hu, evalTate_smul_basis]

theorem tateRingHomU_injective (h12 : (12 : K) ≠ 0) : Function.Injective (tateRingHomU t h12) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨k, H, e, hv⟩ := hasVals_tateRingHomU t h12 a
  rw [ha, mul_zero] at e
  have hH : H = 0 := Mero.ofE_injective (e.symm.trans Mero.ofE_zero.symm)
  classical
  refine eq_zero_of_evalTate (h12 := h12) a fun u hu => ?_
  have h := hv u hu
  simp only [hH, Entire.coe_zero_apply, dif_pos hu] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (t.theta_neg_ne_zero hu))

/-- **`K[E_t] → Mero K`**: `x ↦ x(Ü²)`, `y ↦ y(Ü²)` (the coordinate ring of `E_t` as functions on
`Ÿ_∞ = 𝔾_m^an`). -/
def tateRingHom (h12 : (12 : K) ≠ 0) : TateRing t →+* Mero K := Mero.sq.comp (tateRingHomU t h12)

lemma tateRingHom_x (h12 : (12 : K) ≠ 0) :
    tateRingHom t h12 (mkT t (C Polynomial.X)) = xM t := by
  rw [tateRingHom, RingHom.comp_apply, tateRingHomU_mk_C, eval₂_X]; rfl

lemma tateRingHom_y (h12 : (12 : K) ≠ 0) : tateRingHom t h12 (mkT t Polynomial.X) = yM t := by
  rw [tateRingHom, RingHom.comp_apply, tateRingHomU_mk_Y]; rfl

theorem tateRingHom_injective (h12 : (12 : K) ≠ 0) : Function.Injective (tateRingHom t h12) :=
  Mero.sq_injective.comp (tateRingHomU_injective t h12)

/-- **`K(E_t) → Mero K`**: the function field of `E_t` inside the meromorphic functions on
`Ÿ_∞`. -/
def tateFieldHom (h12 : (12 : K) ≠ 0) : TateField t →+* Mero K :=
  IsFractionRing.lift (tateRingHom_injective t h12)

lemma tateFieldHom_algebraMap (h12 : (12 : K) ≠ 0) (a : TateRing t) :
    tateFieldHom t h12 (algebraMap (TateRing t) (TateField t) a) = tateRingHom t h12 a :=
  IsFractionRing.lift_algebraMap _ _

end Ring

/-! ### Deck invariance of `x(Ü²)`, `y(Ü²)` -/

section Deck

variable (t : TateParameter K)

lemma Mero.scale_inv_of_scale_eq {c : Kˣ} {x : Mero K} (h : Mero.scale c x = x) :
    Mero.scale c⁻¹ x = x := by
  conv_lhs => rw [← h]
  rw [← Mero.scale_mul_apply, mul_inv_cancel, Mero.scale_one_apply]

lemma Mero.scale_zpow_of_scale_eq {c : Kˣ} {x : Mero K} (h : Mero.scale c x = x) (k : ℤ) :
    Mero.scale (c ^ k) x = x := by
  induction k using Int.induction_on with
  | zero => rw [zpow_zero, Mero.scale_one_apply]
  | succ k ih => rw [zpow_add_one, Mero.scale_mul_apply, ih, h]
  | pred k ih => rw [zpow_sub_one, Mero.scale_mul_apply, ih, Mero.scale_inv_of_scale_eq h]

lemma thetaE_q (u : Kˣ) : ((thetaE t : Entire K) : Kˣ → K) (t.q * u) =
    (((t.q * (-1))⁻¹ : Kˣ) : K) * (u : K) ^ (-1 : ℤ) * ((thetaE t : Entire K) : Kˣ → K) u := by
  have := ofCoeff_q_apply t (isWeightFamily_thetaBlock (t := t) (-1)) u
  rw [Nat.cast_one] at this
  exact this

lemma xThetaE_q (u : Kˣ) : ((xThetaE t : Entire K) : Kˣ → K) (t.q * u) =
    (((t.q * (-1))⁻¹ : Kˣ) : K) ^ 2 * (u : K) ^ (-2 : ℤ) * ((xThetaE t : Entire K) : Kˣ → K) u := by
  have := ofCoeff_q_apply t t.isWeightFamily_XThetaSq u
  rw [Units.val_pow_eq_pow_val] at this
  exact this

lemma yThetaE_q (u : Kˣ) : ((yThetaE t : Entire K) : Kˣ → K) (t.q * u) =
    (((t.q * (-1))⁻¹ : Kˣ) : K) ^ 3 * (u : K) ^ (-3 : ℤ) * ((yThetaE t : Entire K) : Kˣ → K) u := by
  have := ofCoeff_q_apply t t.isWeightFamily_YThetaCube u
  rw [Units.val_pow_eq_pow_val] at this
  exact this

lemma scale_q_xU : Mero.scale t.q (xU t) = xU t := by
  rw [xU, ← Mero.ofE_pow, Mero.scale_div]
  refine Mero.div_eq_div_of_apply (Mero.entire_scale_ne_zero _ (pow_ne_zero _ (thetaE_ne_zero t)))
    (pow_ne_zero _ (thetaE_ne_zero t)) fun u => ?_
  rw [Entire.coe_scale, Entire.coe_scale, Entire.coe_pow_apply, Entire.coe_pow_apply, xThetaE_q,
    thetaE_q, show ((u : K)) ^ (-2 : ℤ) = ((u : K) ^ (-1 : ℤ)) ^ 2 by
      rw [← zpow_natCast, ← zpow_mul]; norm_num]
  ring

lemma scale_q_yU : Mero.scale t.q (yU t) = yU t := by
  rw [yU, ← Mero.ofE_pow, Mero.scale_div]
  refine Mero.div_eq_div_of_apply (Mero.entire_scale_ne_zero _ (pow_ne_zero _ (thetaE_ne_zero t)))
    (pow_ne_zero _ (thetaE_ne_zero t)) fun u => ?_
  rw [Entire.coe_scale, Entire.coe_scale, Entire.coe_pow_apply, Entire.coe_pow_apply, yThetaE_q,
    thetaE_q, show ((u : K)) ^ (-3 : ℤ) = ((u : K) ^ (-1 : ℤ)) ^ 3 by
      rw [← zpow_natCast, ← zpow_mul]; norm_num]
  ring

lemma Deck.sq_eq (c : Deck t) : ((c : Kˣ) ^ 2 : Kˣ) = t.q ^ Deck.idx c :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, Deck.idx_spec, Units.val_zpow_eq_zpow_val])

/-- **`Ü ↦ c·Ü` fixes `x(Ü²)`** for every deck transformation `c` (`c² ∈ q^ℤ`). -/
theorem scale_xM (c : Deck t) : Mero.scale (c : Kˣ) (xM t) = xM t := by
  rw [xM, Mero.scale_sq, Deck.sq_eq, Mero.scale_zpow_of_scale_eq (scale_q_xU t)]

/-- **`Ü ↦ c·Ü` fixes `y(Ü²)`** for every deck transformation `c`. -/
theorem scale_yM (c : Deck t) : Mero.scale (c : Kˣ) (yM t) = yM t := by
  rw [yM, Mero.scale_sq, Deck.sq_eq, Mero.scale_zpow_of_scale_eq (scale_q_yU t)]

end Deck

/-! ### The point of `s` and the analytic Kummer function `√(x - e)` -/

section Kummer

variable (t : TateParameter K) {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
include hs

lemma s_sq_unit : s ^ 2 = t.q := Units.ext (by rw [Units.val_pow_eq_pow_val, hs])

/-- `U = s` is off the orbit `q^ℤ`. -/
theorem offOrbit_s : OffOrbit t s := by
  intro n hn
  have h1 : (t.q : K) ^ (2 * n + 1) = 1 := by
    have e : ((t.q : K) ^ n * s) ^ 2 = (t.q : K) ^ (2 * n + 1) := by
      rw [mul_pow, hs, ← zpow_natCast ((t.q : K) ^ n) 2, ← zpow_mul, zpow_add_one₀ t.q.ne_zero,
        Nat.cast_ofNat, mul_comm n 2]
    rw [← e, hn, one_pow]
  have h2 := congrArg norm h1
  rw [norm_zpow, norm_one, ← zpow_zero ‖(t.q : K)‖] at h2
  have := (zpow_right_strictAnti₀ t.norm_q_pos t.norm_lt_one).injective h2
  omega

lemma s_inv_eq : (s⁻¹ : Kˣ) = t.q⁻¹ * s := by
  rw [← s_sq_unit t hs, pow_two, mul_inv_rev, inv_mul_cancel_right]

/-- **The Tate point of `U = s` is `2`-torsion**: `2·Y(s) + X(s) = 0`, i.e. it is the point
`(e, -e/2)` fixed by `(x, y) ↦ (x, -y - x)`, with `e = X(s)`. -/
theorem two_Y_s_add_X_s : 2 * t.Y s + t.X s = 0 := by
  have h := t.Y_inv (offOrbit_s t hs)
  have hp : t.Y s⁻¹ = t.Y s := by
    rw [s_inv_eq t hs]
    have := t.Y_q_smul (t.q⁻¹ * s)
    rw [mul_inv_cancel_left] at this
    exact this.symm
  rw [hp] at h
  linear_combination h

/-- `θ(-U/s)θ(-sU)` is a weight-`2` family with the multiplier of `θ(-U)²`. -/
lemma isWeightFamily_kum :
    t.IsWeightFamily 2 (multθ t ^ 2)
      (fun n => ∑' m : ℤ, t.thetaBlock (-s⁻¹) (n - m) * t.thetaBlock (-s) m) := by
  have h := (isWeightFamily_thetaBlock (t := t) (-s⁻¹)).conv
    (isWeightFamily_thetaBlock (t := t) (-s))
  have hA : ((t.q * -s⁻¹)⁻¹ * (t.q * -s)⁻¹ : Kˣ) = multθ t ^ 2 := by
    rw [multθ]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_neg, Units.val_pow_eq_pow_val,
      Units.val_one]
    field_simp
  rw [hA] at h
  exact weightFamily_of_eq t h rfl

omit hs in
/-- The weight space `W(2, Aθ²)` is spanned by `θ(-U)²` and `x(U)θ(-U)²`. -/
lemma exists_lin_of_weight_two (h12 : (12 : K) ≠ 0) {F : ℤ → K}
    (hF : t.IsWeightFamily 2 (multθ t ^ 2) F) :
    ∃ a b : K, ∀ u : Kˣ, OffOrbit t u →
      (∑' n : ℤ, F n * (u : K) ^ n) = (a + b * t.X u) * t.theta (-u) ^ 2 := by
  haveI := finiteDimensional_weightSpace (t := t) (A := multθ t ^ 2) two_pos
  have hli := linearIndependent_monoBasis t h12 2
  have hspan : Submodule.span K (Set.range (monoBasis t 2)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by rw [card_monoIdx two_pos, finrank_weightSpace two_pos])
  have hmem : (⟨F, hF⟩ : t.weightSpace 2 (multθ t ^ 2)) ∈
      Submodule.span K (Set.range (monoBasis t 2)) := hspan ▸ Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
  refine ⟨g (Sum.inl ⟨0, by decide⟩), g (Sum.inl ⟨1, by decide⟩), fun u hu => ?_⟩
  have h := tsum_monoBasis_comb t g hu
  rw [hg] at h
  rw [h, eval_polyOf, eval_polyOf]
  have e1 : (∑ i : Fin (2 / 2 + 1), g (Sum.inl i) * t.X u ^ (i : ℕ)) =
      g (Sum.inl ⟨0, by decide⟩) + g (Sum.inl ⟨1, by decide⟩) * t.X u := by
    rw [show (∑ i : Fin (2 / 2 + 1), g (Sum.inl i) * t.X u ^ (i : ℕ)) =
      ∑ i : Fin 2, g (Sum.inl i) * t.X u ^ (i : ℕ) from rfl, Fin.sum_univ_two]
    simp
  have e2 : (∑ i : Fin ((2 - 1) / 2), g (Sum.inr i) * t.X u ^ (i : ℕ)) = 0 := by
    rw [show (∑ i : Fin ((2 - 1) / 2), g (Sum.inr i) * t.X u ^ (i : ℕ)) =
      ∑ i : Fin 0, g (Sum.inr i) * t.X u ^ (i : ℕ) from rfl, Fin.sum_univ_zero]
  rw [e1, e2, mul_zero, add_zero]

lemma theta_neg_s_mul (u : Kˣ) :
    t.theta (-s * u) = (-(s : K) * u)⁻¹ * t.theta (-s⁻¹ * u) := by
  have he : (-s * u : Kˣ) = t.q * (-s⁻¹ * u) := by
    rw [← s_sq_unit t hs]; ext; simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val]; field_simp
  rw [he, theta_q_smul]
  congr 1
  rw [← hs]
  simp only [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val]
  field_simp

/-- **`x(U) - e` is a square on `𝔾_m^an`** (`e = X(s)`): there is `β ≠ 0` with
`(x(U)θ(-U)² - e·θ(-U)²)·U = β·θ(-U/s)²` in `E(K)`. -/
theorem exists_kummer_entire (h12 : (12 : K) ≠ 0) :
    ∃ β : K, β ≠ 0 ∧ (xThetaE t - algebraMap K (Entire K) (t.X s) * thetaE t ^ 2) * Entire.mono 1 =
      algebraMap K (Entire K) β * thetaSE t s ^ 2 := by
  classical
  obtain ⟨a, b, hab⟩ := exists_lin_of_weight_two t h12 (isWeightFamily_kum t hs)
  have hval : ∀ u : Kˣ, OffOrbit t u →
      t.theta (-s⁻¹ * u) * t.theta (-s * u) = (a + b * t.X u) * t.theta (-u) ^ 2 := fun u hu => by
    rw [← hab u hu, (t.hasSum_doubleBlock (-s⁻¹) (-s) u).tsum_eq]
  have hso := offOrbit_s t hs
  have ha : a = -(b * t.X s) := by
    have h := hval s hso
    rw [neg_mul, inv_mul_cancel, t.theta_neg_one, zero_mul] at h
    have := (mul_eq_zero.mp h.symm).resolve_right (pow_ne_zero _ (t.theta_neg_ne_zero hso))
    linear_combination this
  have hb : b ≠ 0 := by
    intro hb0
    obtain ⟨u, hu⟩ := t.exists_unit_avoiding {1, s}
    have hu1 : OffOrbit t u := fun n hn => hu 1 (by simp) (-n) (by
      rw [zpow_neg, Units.val_one, mul_one]
      field_simp
      linear_combination hn)
    have h := hval u hu1
    rw [ha, hb0, zero_mul, neg_zero, zero_add, zero_mul, zero_mul] at h
    rcases mul_eq_zero.mp h with h0 | h0
    · obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff _).mp h0
      refine hu s (by simp) k ?_
      rw [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val, neg_mul, neg_inj] at hk
      field_simp at hk
      linear_combination hk
    · obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff _).mp h0
      refine hu s (by simp) (k - 1) ?_
      rw [Units.val_mul, Units.val_neg, neg_mul, neg_inj] at hk
      have hs0 : (s : K) ≠ 0 := s.ne_zero
      have hu' : (u : K) = (t.q : K) ^ k / s := by
        field_simp
        linear_combination hk
      rw [hu', zpow_sub_one₀ t.q.ne_zero, ← hs]
      field_simp
  refine ⟨-(b * s)⁻¹, neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero hb s.ne_zero)), ?_⟩
  rw [← sub_eq_zero]
  refine Entire.eq_zero_of_offOrbit t fun u hu => ?_
  have h := hval u hu
  rw [theta_neg_s_mul t hs, ha] at h
  simp only [Entire.coe_sub_apply, Entire.coe_mul_apply, Entire.coe_pow_apply,
    Entire.coe_algebraMap_apply, xThetaE_apply t hu, thetaE_apply, thetaSE_apply,
    Entire.coe_mono_apply, zpow_one]
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  field_simp at h ⊢
  linear_combination -h

/-- The coefficient `β` of `exists_kummer_entire`. -/
def kumConst (h12 : (12 : K) ≠ 0) : K := (exists_kummer_entire t hs h12).choose

lemma kumConst_ne_zero (h12 : (12 : K) ≠ 0) : kumConst t hs h12 ≠ 0 :=
  (exists_kummer_entire t hs h12).choose_spec.1

omit hs in
/-- **The analytic Kummer function** `θ(-Ü²/s)/(Ü·θ(-Ü²))` on `Ÿ_∞`. -/
def kumM (s : Kˣ) : Mero K :=
  Mero.ofE (Entire.sq (thetaSE t s)) / Mero.ofE (Entire.mono 1 * Entire.sq (thetaE t))

omit hs in
lemma sq_thetaE_ne_zero : Entire.sq (thetaE t) ≠ 0 := fun h =>
  thetaE_ne_zero t (Entire.sqHom_injective (h.trans (map_zero Entire.sqHom).symm))

omit hs in
lemma kumDen_ne_zero : (Entire.mono 1 * Entire.sq (thetaE t) : Entire K) ≠ 0 :=
  mul_ne_zero (Entire.isUnit_mono 1).ne_zero (sq_thetaE_ne_zero t)

omit hs in
lemma xM_eq : xM t = Mero.ofE (Entire.sq (xThetaE t)) / Mero.ofE (Entire.sq (thetaE t)) ^ 2 := by
  rw [xM, xU, map_div₀, map_pow, Mero.sq_ofE, Mero.sq_ofE]

/-- **`β·kumM² = x(Ü²) - e`**, `e = X(s)`: the Kummer function is `√(x - e)` up to the field of
constants. -/
theorem kumM_sq (h12 : (12 : K) ≠ 0) :
    Mero.const (kumConst t hs h12) * kumM t s ^ 2 = xM t - Mero.const (t.X s) := by
  have e := (exists_kummer_entire t hs h12).choose_spec.2
  have e2 := congrArg (fun f => Mero.ofE (Entire.sqHom f)) e
  simp only [map_mul, map_sub, map_pow, Entire.sqHom_apply, Entire.sq_algebraMap,
    Entire.sq_mono] at e2
  rw [show (Entire.mono (2 * 1) : Entire K) = Entire.mono 1 ^ 2 by
    rw [Entire.mono_pow]; norm_num, map_pow] at e2
  rw [kumM, xM_eq, div_pow, Mero.ofE_mul, mul_pow]
  have h1 := Mero.ofE_ne_zero (sq_thetaE_ne_zero t)
  have h2 := Mero.ofE_ne_zero (Entire.isUnit_mono (K := K) 1).ne_zero
  change Mero.const (exists_kummer_entire t hs h12).choose * _ = _
  field_simp
  linear_combination -e2

omit hs in
lemma Entire.coe_neg_apply (f : Entire K) (u : Kˣ) :
    ((-f : Entire K) : Kˣ → K) u = -(f : Kˣ → K) u := rfl

omit hs in
/-- **`Ü ↦ -Ü` negates the Kummer function** (it is odd in `Ü`). -/
theorem scale_neg_one_kumM (s : Kˣ) : Mero.scale (-1) (kumM t s) = -kumM t s := by
  rw [kumM, Mero.scale_div, ← neg_div, ← Mero.ofE_neg]
  refine Mero.div_eq_div_of_apply (Mero.entire_scale_ne_zero _ (kumDen_ne_zero t))
    (kumDen_ne_zero t) fun u => ?_
  have hu2 : ((-1 : Kˣ) * u) ^ 2 = u ^ 2 := by rw [neg_one_mul, neg_sq]
  rw [Entire.coe_scale, Entire.coe_scale, Entire.coe_mul_apply, Entire.coe_mul_apply,
    Entire.coe_neg_apply]
  simp only [Entire.coe_sq, hu2, Entire.coe_mono_apply, zpow_one, Units.val_mul, Units.val_neg,
    Units.val_one]
  ring

lemma thetaSE_q (u : Kˣ) : ((thetaSE t s : Entire K) : Kˣ → K) (t.q * u) =
    (((t.q * -s⁻¹)⁻¹ : Kˣ) : K) * (u : K) ^ (-1 : ℤ) * ((thetaSE t s : Entire K) : Kˣ → K) u := by
  have := ofCoeff_q_apply t (isWeightFamily_thetaBlock (t := t) (-s⁻¹)) u
  rw [Nat.cast_one] at this
  exact this

/-- **`Ü ↦ s·Ü` fixes the Kummer function** (`U ↦ qU`). -/
theorem scale_s_kumM : Mero.scale s (kumM t s) = kumM t s := by
  rw [kumM, Mero.scale_div]
  refine Mero.div_eq_div_of_apply (Mero.entire_scale_ne_zero _ (kumDen_ne_zero t))
    (kumDen_ne_zero t) fun u => ?_
  have hu2 : (s * u) ^ 2 = t.q * u ^ 2 := by rw [mul_pow, s_sq_unit t hs]
  rw [Entire.coe_scale, Entire.coe_scale, Entire.coe_mul_apply, Entire.coe_mul_apply]
  simp only [Entire.coe_sq]
  rw [hu2, thetaSE_q t hs, thetaE_q, Entire.coe_mono_apply, Entire.coe_mono_apply, zpow_one,
    zpow_one]
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
  simp only [Units.val_mul, Units.val_neg, Units.val_one, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, zpow_neg, zpow_one]
  field_simp

/-- `Ü ↦ s^k·Ü` fixes the Kummer function. -/
theorem scale_zpow_s_kumM (k : ℤ) : Mero.scale (s ^ k) (kumM t s) = kumM t s :=
  Mero.scale_zpow_of_scale_eq (scale_s_kumM t hs) k

end Kummer

end Iut.Frobenioid.BAn
