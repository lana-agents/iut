/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.TateElliptic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Rational functions on the Tate curve from their values at Tate points (MR14, task G1)

Let `q` be a Tate parameter over a complete nonarchimedean field `K` with `12 ≠ 0`, and let
`K[E_q]` (`t.tateCurve.toAffine.CoordinateRing`) and `K(E_q)` (`…FunctionField`) be the affine
coordinate ring and the function field of the Tate Weierstrass curve
`E_q : y² + xy = x³ + a₄x + a₆`. This file is the bridge from the analytic theta functions of
`tate-curves-theta` to algebraic functions on `E_q`, used by route R-alg of MR14
(`~/iut-scratch/multiradial/MR14-plan.md`) to put the theta level functions on finite étale
covers of `E_q ∖ {O}`.

* `evalTate`: evaluation `K[E_q] → K` at the Tate point `(X(u), Y(u))`, `u ∉ qᶻ`
  (Tate uniformisation, `tatePoint_mem'`).
* `eq_zero_of_evalTate`: an element of `K[E_q]` vanishing at all Tate points is zero
  (`poly_eq_zero_of_eval`).
* `IsTateFun g G`: the element `g ∈ K(E_q)` has values `G(u)` — there are `n, d ∈ K[E_q]`,
  `d ≠ 0`, with `g = n/d` and `G(u) = n(u)/d(u)` whenever `d(u) ≠ 0`.
* `IsTateFun.unique`: an element is determined by its values; `IsTateFun.add`, `.mul`, `.div`,
  `.const`, `.x`, `.y`, `.ofWeight`: closure properties, and **elements from theta functions**:
  a quotient of two weight-`k` theta families with the multiplier of `θ(-u)ᵏ` is an element of
  `K(E_q)` (Tate's theorem `exists_poly_of_isWeightFamily`).
-/

open Polynomial

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-- The affine coordinate ring `K[E_q]` of the Tate curve. -/
abbrev TateRing : Type _ := WeierstrassCurve.Affine.CoordinateRing t.tateCurve.toAffine

/-- The function field `K(E_q)` of the Tate curve. -/
abbrev TateField : Type _ := WeierstrassCurve.Affine.FunctionField t.tateCurve.toAffine

/-- The quotient map `K[X][Y] → K[E_q]`. -/
abbrev mkT (p : K[X][X]) : TateRing t := WeierstrassCurve.Affine.CoordinateRing.mk _ p

variable (h12 : (12 : K) ≠ 0)

/-- **Evaluation at the Tate point** `(X(u), Y(u))` of `u ∉ qᶻ`. -/
def evalTate {u : Kˣ} (hu : OffOrbit t u) : TateRing t →+* K :=
  AdjoinRoot.lift (Polynomial.evalRingHom (t.X u)) (t.Y u) (by
    have h := (equation_iff _ _).mp (t.tatePoint_mem' h12 hu)
    simp only [tateCurve_a₁, tateCurve_a₂, tateCurve_a₃, tateCurve_a₄, tateCurve_a₆] at h
    simp only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow,
      eval₂_X, eval₂_C, coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, eval_pow,
      tateCurve_a₁, tateCurve_a₂, tateCurve_a₃, tateCurve_a₄, tateCurve_a₆]
    linear_combination h)

variable {t h12}

@[simp]
theorem evalTate_mk_C {u : Kˣ} (hu : OffOrbit t u) (p : K[X]) :
    evalTate t h12 hu (mkT t (C p)) = p.eval (t.X u) := by
  simp [evalTate, mkT]

@[simp]
theorem evalTate_mk_Y {u : Kˣ} (hu : OffOrbit t u) :
    evalTate t h12 hu (mkT t Polynomial.X) = t.Y u := by
  simp [evalTate, mkT]

@[simp]
theorem evalTate_algebraMap {u : Kˣ} (hu : OffOrbit t u) (c : K) :
    evalTate t h12 hu (algebraMap K (TateRing t) c) = c := by
  rw [IsScalarTower.algebraMap_apply K K[X] (TateRing t), AdjoinRoot.algebraMap_eq,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  simpa using evalTate_mk_C (h12 := h12) hu (C c)

theorem evalTate_smul_basis {u : Kˣ} (hu : OffOrbit t u) (p q : K[X]) :
    evalTate t h12 hu (p • (1 : TateRing t) + q • mkT t Polynomial.X) =
      p.eval (t.X u) + t.Y u * q.eval (t.X u) := by
  rw [CoordinateRing.smul, CoordinateRing.smul, map_add, map_mul, map_mul, map_one, mul_one,
    evalTate_mk_C, evalTate_mk_C, evalTate_mk_Y, mul_comm]

/-- **An element of `K[E_q]` vanishing at every Tate point is zero.** -/
theorem eq_zero_of_evalTate (a : TateRing t)
    (h : ∀ (u : Kˣ) (hu : OffOrbit t u), evalTate t h12 hu a = 0) : a = 0 := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
  obtain ⟨hp, hq⟩ := poly_eq_zero_of_eval t h12 p q fun u hu => by
    rw [← evalTate_smul_basis (h12 := h12) hu]; exact h u hu
  rw [hp, hq, zero_smul, zero_smul, add_zero]

/-! ### Values of elements of the function field at Tate points -/

variable (t h12)

/-- `g ∈ K(E_q)` **is regular at the Tate point of `u` with value `v`**: `g = n/d` with
`n, d ∈ K[E_q]`, `d(u) ≠ 0` and `v = n(u)/d(u)`. -/
def HasTateValue (g : TateField t) {u : Kˣ} (hu : OffOrbit t u) (v : K) : Prop :=
  ∃ n d : TateRing t, g * algebraMap (TateRing t) (TateField t) d =
      algebraMap (TateRing t) (TateField t) n ∧
    evalTate t h12 hu d ≠ 0 ∧ v * evalTate t h12 hu d = evalTate t h12 hu n

variable {t h12}

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem algebraMap_ne_zero {d : TateRing t} (hd : d ≠ 0) :
    algebraMap (TateRing t) (TateField t) d ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hd

theorem ne_zero_of_evalTate_ne_zero {u : Kˣ} {hu : OffOrbit t u} {d : TateRing t}
    (h : evalTate t h12 hu d ≠ 0) : d ≠ 0 := by
  rintro rfl; exact h (map_zero _)

/-- The value at a point is well defined. -/
theorem HasTateValue.unique {g : TateField t} {u : Kˣ} {hu : OffOrbit t u} {v v' : K}
    (h : HasTateValue t h12 g hu v) (h' : HasTateValue t h12 g hu v') : v = v' := by
  obtain ⟨n, d, hg, hd, hv⟩ := h
  obtain ⟨n', d', hg', hd', hv'⟩ := h'
  have e : n * d' = n' * d := by
    apply IsFractionRing.injective (TateRing t) (TateField t)
    rw [map_mul, map_mul, ← hg, ← hg']; ring
  have := congrArg (evalTate t h12 hu) e
  simp only [map_mul] at this
  rw [← hv, ← hv'] at this
  exact mul_right_cancel₀ (mul_ne_zero hd hd') (by linear_combination this)

theorem HasTateValue.congr {g : TateField t} {u : Kˣ} {hu : OffOrbit t u} {v v' : K}
    (h : HasTateValue t h12 g hu v) (e : v = v') : HasTateValue t h12 g hu v' := e ▸ h

theorem HasTateValue.ne_zero {g : TateField t} {u : Kˣ} {hu : OffOrbit t u} {v : K}
    (h : HasTateValue t h12 g hu v) (hv : v ≠ 0) : g ≠ 0 := by
  rintro rfl
  obtain ⟨n, d, hg, hd, hv'⟩ := h
  rw [zero_mul, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at hg
  rw [hg, map_zero] at hv'
  exact mul_ne_zero hv hd hv'

theorem HasTateValue.const {u : Kˣ} (hu : OffOrbit t u) (c : K) :
    HasTateValue t h12 (algebraMap K (TateField t) c) hu c :=
  ⟨algebraMap K (TateRing t) c, 1, by rw [map_one, mul_one, ← IsScalarTower.algebraMap_apply],
    by simp, by simp⟩

theorem HasTateValue.ofRing {u : Kˣ} (hu : OffOrbit t u) (a : TateRing t) :
    HasTateValue t h12 (algebraMap (TateRing t) (TateField t) a) hu (evalTate t h12 hu a) :=
  ⟨a, 1, by rw [map_one, mul_one], by simp, by simp⟩

theorem HasTateValue.x {u : Kˣ} (hu : OffOrbit t u) :
    HasTateValue t h12 (algebraMap (TateRing t) (TateField t)
      (mkT t (C X))) hu (t.X u) := by
  exact (HasTateValue.ofRing hu _).congr (by rw [evalTate_mk_C, eval_X])

theorem HasTateValue.y {u : Kˣ} (hu : OffOrbit t u) :
    HasTateValue t h12 (algebraMap (TateRing t) (TateField t)
      (mkT t Polynomial.X)) hu
      (t.Y u) := by
  exact (HasTateValue.ofRing hu _).congr (evalTate_mk_Y hu)

theorem HasTateValue.mul {g g' : TateField t} {u : Kˣ} {hu : OffOrbit t u} {v v' : K}
    (h : HasTateValue t h12 g hu v) (h' : HasTateValue t h12 g' hu v') :
    HasTateValue t h12 (g * g') hu (v * v') := by
  obtain ⟨n, d, hg, hd, hv⟩ := h
  obtain ⟨n', d', hg', hd', hv'⟩ := h'
  refine ⟨n * n', d * d', ?_, by rw [map_mul]; exact mul_ne_zero hd hd', ?_⟩
  · rw [map_mul, map_mul, ← hg, ← hg']; ring
  · rw [map_mul, map_mul, ← hv, ← hv']; ring

theorem HasTateValue.add {g g' : TateField t} {u : Kˣ} {hu : OffOrbit t u} {v v' : K}
    (h : HasTateValue t h12 g hu v) (h' : HasTateValue t h12 g' hu v') :
    HasTateValue t h12 (g + g') hu (v + v') := by
  obtain ⟨n, d, hg, hd, hv⟩ := h
  obtain ⟨n', d', hg', hd', hv'⟩ := h'
  refine ⟨n * d' + n' * d, d * d', ?_, by rw [map_mul]; exact mul_ne_zero hd hd', ?_⟩
  · rw [map_add, map_mul, map_mul, map_mul, ← hg, ← hg']; ring
  · rw [map_add, map_mul, map_mul, map_mul, ← hv, ← hv']; ring

theorem HasTateValue.inv {g : TateField t} {u : Kˣ} {hu : OffOrbit t u} {v : K}
    (h : HasTateValue t h12 g hu v) (hv : v ≠ 0) : HasTateValue t h12 g⁻¹ hu v⁻¹ := by
  have hg0 := h.ne_zero hv
  obtain ⟨n, d, hg, hd, hv'⟩ := h
  have hn : evalTate t h12 hu n ≠ 0 := by rw [← hv']; exact mul_ne_zero hv hd
  refine ⟨d, n, ?_, hn, ?_⟩
  · rw [← hg]; field_simp
  · rw [← hv']; field_simp

theorem HasTateValue.div {g g' : TateField t} {u : Kˣ} {hu : OffOrbit t u} {v v' : K}
    (h : HasTateValue t h12 g hu v) (h' : HasTateValue t h12 g' hu v') (hv' : v' ≠ 0) :
    HasTateValue t h12 (g / g') hu (v / v') := by
  simpa [div_eq_mul_inv] using h.mul (h'.inv hv')

theorem HasTateValue.pow {g : TateField t} {u : Kˣ} {hu : OffOrbit t u} {v : K}
    (h : HasTateValue t h12 g hu v) : ∀ m : ℕ, HasTateValue t h12 (g ^ m) hu (v ^ m)
  | 0 => by simpa using HasTateValue.const (h12 := h12) hu 1
  | m + 1 => by simpa [pow_succ] using (h.pow m).mul h

theorem HasTateValue.aeval {g : TateField t} {u : Kˣ} {hu : OffOrbit t u} {v : K}
    (h : HasTateValue t h12 g hu v) (P : K[X]) :
    HasTateValue t h12 (Polynomial.aeval g P) hu (P.eval v) := by
  induction P using Polynomial.induction_on with
  | C a => simpa using HasTateValue.const (h12 := h12) hu a
  | add p q hp hq => simpa using hp.add hq
  | monomial n a _ =>
    simpa [map_mul] using (HasTateValue.const (h12 := h12) hu a).mul (h.pow (n + 1))

/-- **An element of `K(E_q)` is determined by its values** on the Tate points where a fixed
nonzero `D₀ ∈ K[E_q]` does not vanish. -/
theorem eq_zero_of_hasTateValue {g : TateField t} {D₀ : TateRing t} (hD₀ : D₀ ≠ 0)
    (h : ∀ (u : Kˣ) (hu : OffOrbit t u), evalTate t h12 hu D₀ ≠ 0 → HasTateValue t h12 g hu 0) :
    g = 0 := by
  obtain ⟨n, d, hd, rfl⟩ : ∃ n d : TateRing t, d ≠ 0 ∧
      g = algebraMap _ (TateField t) n / algebraMap _ (TateField t) d := by
    obtain ⟨n, d, hd, e⟩ := IsFractionRing.div_surjective (A := TateRing t) g
    exact ⟨n, d, nonZeroDivisors.ne_zero hd, e.symm⟩
  have hn : n * (D₀ * d) = 0 := by
    refine eq_zero_of_evalTate (h12 := h12) _ fun u hu => ?_
    rw [map_mul, map_mul]
    by_cases h0 : evalTate t h12 hu D₀ = 0
    · simp [h0]
    by_cases h1 : evalTate t h12 hu d = 0
    · simp [h1]
    have hv := h u hu h0
    have hv' : HasTateValue t h12
        (algebraMap _ (TateField t) n / algebraMap _ (TateField t) d) hu
        (evalTate t h12 hu n / evalTate t h12 hu d) :=
      (HasTateValue.ofRing (h12 := h12) hu n).div (HasTateValue.ofRing (h12 := h12) hu d) h1
    have := hv.unique hv'
    rw [eq_comm, div_eq_zero_iff, or_iff_left h1] at this
    simp [this]
  rw [mul_eq_zero, or_iff_left (mul_ne_zero hD₀ hd)] at hn
  rw [hn, map_zero, zero_div]

/-- Equality of elements from equality of values off the zeros of `D₀ ≠ 0`. -/
theorem eq_of_hasTateValue {g g' : TateField t} {D₀ : TateRing t} (hD₀ : D₀ ≠ 0)
    {G : Kˣ → K}
    (h : ∀ (u : Kˣ) (hu : OffOrbit t u), evalTate t h12 hu D₀ ≠ 0 → HasTateValue t h12 g hu (G u))
    (h' : ∀ (u : Kˣ) (hu : OffOrbit t u), evalTate t h12 hu D₀ ≠ 0 →
      HasTateValue t h12 g' hu (G u)) : g = g' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_hasTateValue (h12 := h12) hD₀ fun u hu (h0 : evalTate t h12 hu D₀ ≠ 0) => ?_
  have h2 := (h u hu h0).add ((HasTateValue.const (h12 := h12) hu (-1)).mul (h' u hu h0))
  rw [map_neg, map_one, neg_one_mul, ← sub_eq_add_neg] at h2
  exact h2.congr (by ring)

variable (t) in
/-- The element `P(x) + y·Q(x)` of `K[E_q]`. -/
def polyXY (P Q : K[X]) : TateRing t :=
  P • (1 : TateRing t) + Q • mkT t
    Polynomial.X

theorem evalTate_polyXY {u : Kˣ} (hu : OffOrbit t u) (P Q : K[X]) :
    evalTate t h12 hu (polyXY t P Q) = P.eval (t.X u) + t.Y u * Q.eval (t.X u) :=
  evalTate_smul_basis hu P Q

/-- **Elements of `K(E_q)` from theta functions**: if `F₁, F₂` are weight-`k` theta families
(`k ≥ 1`) with the multiplier of `θ(-u)ᵏ`, there are `n, d ∈ K[E_q]` with
`∑ F₁(u) = n(u)·θ(-u)ᵏ` and `∑ F₂(u) = d(u)·θ(-u)ᵏ` off the period orbit (Tate's theorem
`exists_poly_of_isWeightFamily`); so `g = n/d` has the values `∑F₁/∑F₂` wherever `∑F₂ ≠ 0`. -/
theorem exists_hasTateValue_of_weight {k : ℕ} (hk : 0 < k) {F₁ F₂ : ℤ → K}
    (hF₁ : t.IsWeightFamily k (multθ t ^ k) F₁) (hF₂ : t.IsWeightFamily k (multθ t ^ k) F₂) :
    ∃ n d : TateRing t, ∀ (u : Kˣ) (hu : OffOrbit t u),
      (∑' m : ℤ, F₁ m * (u : K) ^ m) = evalTate t h12 hu n * t.theta (-u) ^ k ∧
      (∑' m : ℤ, F₂ m * (u : K) ^ m) = evalTate t h12 hu d * t.theta (-u) ^ k ∧
      ((∑' m : ℤ, F₂ m * (u : K) ^ m) ≠ 0 →
        HasTateValue t h12 (algebraMap _ (TateField t) n / algebraMap _ (TateField t) d) hu
          ((∑' m : ℤ, F₁ m * (u : K) ^ m) / ∑' m : ℤ, F₂ m * (u : K) ^ m)) := by
  obtain ⟨P₁, Q₁, h₁⟩ := exists_poly_of_isWeightFamily t h12 hk hF₁
  obtain ⟨P₂, Q₂, h₂⟩ := exists_poly_of_isWeightFamily t h12 hk hF₂
  refine ⟨polyXY t P₁ Q₁, polyXY t P₂ Q₂, fun u hu => ?_⟩
  have e₁ : (∑' m : ℤ, F₁ m * (u : K) ^ m) =
      evalTate t h12 hu (polyXY t P₁ Q₁) * t.theta (-u) ^ k := by
    rw [evalTate_polyXY, h₁ u hu]
  have e₂ : (∑' m : ℤ, F₂ m * (u : K) ^ m) =
      evalTate t h12 hu (polyXY t P₂ Q₂) * t.theta (-u) ^ k := by
    rw [evalTate_polyXY, h₂ u hu]
  refine ⟨e₁, e₂, fun h0 => ?_⟩
  have hθ : t.theta (-u) ^ k ≠ 0 := pow_ne_zero _ (theta_neg_ne_zero t hu)
  have hd : evalTate t h12 hu (polyXY t P₂ Q₂) ≠ 0 := by
    intro h; rw [e₂, h, zero_mul] at h0; exact h0 rfl
  refine ((HasTateValue.ofRing hu _).div (HasTateValue.ofRing hu _) hd).congr ?_
  rw [e₁, e₂]
  field_simp

end Iut.EtaleTheta
