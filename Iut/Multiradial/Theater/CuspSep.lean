/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.Theater.CuspAction
import Iut.Reconstruction.Cusp.GaloisConj

/-!
# Separation of cusps by decomposition groups (MR22 T5)

[AbsTopI] Lemma 4.5 (v) (`~/iut-scratch/papers/txt/Topics in Absolute Anabelian Geometry I.txt`
l.3331–3336) for the model orbicurves `X = (E, ℓ, M, ±)` in the Galois model
`π₁(X) = Aut(Ω / F_X) ⧸ ⟨⟨inertia⟩⟩` (`Genuine.pi1Of`), with `|E(k)[ℓ]| = ℓ²` and `ℓ` an odd
prime: **cusps of `X` correspond to the conjugacy classes of cuspidal decomposition groups**
(`CuspPlace.cusp_eq_iff_conj`; existence and conjugacy of places over one cusp are in
`CuspConj.lean`). Self-contained Kummer argument, no comparison with curves-jacobian's
scheme-theoretic `π₁`:

* for places `W₁, W₂` over `T₁ ≠ T₂`, write `Q_ℓ − T₁ = (a, b)` and take the secant `L` through
  `ℓ`-torsion points `S₁, S₂ = S₁ + (T₂ − T₁)` (`secant_aux`); `f = b − L(a)` vanishes only at
  cusps, so it is a unit at every non-cuspidal place (`val_line_eq_one`, via
  `x(G) ΨSq_ℓ(a) = Φ_ℓ(a)`); `f ≡ L(T₂ − T₁) ≠ 0` at `W₂` (`residue_of_pole`, `addXY_congr`);
  and `v_{W₁}(f)² = v_{W₁}(a)³`;
* `u = √(f / c₀)`: the inertia generators of `π₁(X)` fix `Q_ℓ` (`inertia_fixes_division`) and
  `u` (`fix_root_of_inertia`), hence so does the closed normal subgroup they generate
  (`fixSub`, `isClosed_fixSub`); some `τ ∈ D_{W₁}` fixes `Q_ℓ` and maps `u ↦ −u`
  (`exists_fix_neg_root`, parity of valuations `IntVal`); an element of `D_{W₂}` with the same
  image in `π₁(X)` would map `u ↦ −u` although `u ≡ ±1` at `W₂`
  (**`eq_of_galDecomp_le`**).
-/

noncomputable section

namespace Iut.Multiradial.Theater

open WeierstrassCurve Iut.Anabelian Iut.Anabelian.Genuine Polynomial Iut.HodgeTheater

universe u

attribute [local instance low] Classical.propDecidable

set_option linter.unusedSectionVars false

/-! ### A square root ramified at a place -/

section Kummer

variable {Kf Ω : Type*} [Field Kf] [Field Ω] [Algebra Kf Ω] [IsGalois Kf Ω]

/-- **Negating a square root inside a decomposition group**: if `u² ∈ Kf`, `u ∉ Kf` and the place
`W` of the Galois extension `Ω / Kf` satisfies `g + h u ∈ W ↔ g − h u ∈ W` for `g, h ∈ Kf`,
then some `ρ ∈ Aut(Ω / Kf)` fixes `W` and maps `u ↦ −u` (as in `exists_fix_neg_aux`). -/
theorem exists_fix_neg_gen (W : ValuationSubring Ω) {u : Ω} {d : Kf}
    (hud : u ^ 2 = algebraMap Kf Ω d) (hu : u ∉ (algebraMap Kf Ω).range)
    (hstab : ∀ g h : Kf, algebraMap Kf Ω g + algebraMap Kf Ω h * u ∈ W ↔
      algebraMap Kf Ω g - algebraMap Kf Ω h * u ∈ W) :
    ∃ ρ : Ω ≃ₐ[Kf] Ω, W.comap (ρ.symm : Ω →+* Ω) = W ∧ ρ u = -u := by
  obtain ⟨τ, hτ⟩ : ∃ τ : Ω ≃ₐ[Kf] Ω, τ u = -u := by
    let q : Kf[X] := X ^ 2 - C d
    have hqm : q.Monic := monic_X_pow_sub_C d two_ne_zero
    have hqd : q.natDegree = 2 := natDegree_X_pow_sub_C
    have hq : Irreducible q := by
      refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hqd]; decide) fun z hz => ?_
      have hz' : z ^ 2 = d := by
        have := hz.eq_zero
        simp only [q, eval_sub, eval_pow, eval_X, eval_C] at this
        exact sub_eq_zero.1 this
      have hz2 : (algebraMap Kf Ω z) ^ 2 = u ^ 2 := by rw [hud, ← map_pow, hz']
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hz2 with e | e
      · exact hu ⟨z, e⟩
      · exact hu ⟨-z, by rw [map_neg, e, neg_neg]⟩
    have hroot : ∀ w : Ω, w ^ 2 = u ^ 2 → aeval w q = 0 := fun w hw => by
      simp only [q, map_sub, map_pow, aeval_X, aeval_C, hw, hud, sub_self]
    have e1 := minpoly.eq_of_irreducible_of_monic hq (hroot u rfl) hqm
    have e2 := minpoly.eq_of_irreducible_of_monic hq (hroot (-u) (neg_sq u)) hqm
    obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := Kf) (E := Ω)).1 (e2.symm.trans e1)
    exact ⟨τ, hτ⟩
  have hτs : τ.symm u = -u := by
    rw [AlgEquiv.symm_apply_eq, map_neg, hτ, neg_neg]
  let L : IntermediateField Kf Ω := IntermediateField.adjoin Kf {u}
  haveI : IsGalois L Ω := IsGalois.tower_top_of_isGalois Kf L Ω
  have huint : IsIntegral Kf u := Algebra.IsIntegral.isIntegral u
  have huL : u ∈ L := IntermediateField.mem_adjoin_simple_self Kf u
  have hcomap : (W.comap (τ.symm : Ω →+* Ω)).comap (algebraMap L Ω) =
      W.comap (algebraMap L Ω) := by
    ext z
    have hz : (z : Ω) ∈ Algebra.adjoin Kf {u} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic huint.isAlgebraic]
      exact z.2
    obtain ⟨g, h, hgh⟩ := exists_add_mul_of_mem_adjoin hud hz
    change τ.symm (z : Ω) ∈ W ↔ (z : Ω) ∈ W
    rw [hgh, map_add, map_mul, τ.symm.commutes, τ.symm.commutes, hτs, mul_neg,
      ← sub_eq_add_neg]
    exact (hstab g h).symm
  obtain ⟨κ, hκ⟩ :=
    CurvesJacobian.Cusp.exists_algEquiv_comap_eq (W.comap (τ.symm : Ω →+* Ω)) W hcomap
  let κ' : Ω ≃ₐ[Kf] Ω := κ.restrictScalars Kf
  have hκu : κ u = u := κ.commutes (⟨u, huL⟩ : L)
  refine ⟨κ' * τ, ?_, ?_⟩
  · ext z
    change τ.symm (κ'.symm z) ∈ W ↔ z ∈ W
    exact (SetLike.ext_iff.1 hκ z).symm
  · change κ (τ u) = -u
    rw [hτ, map_neg, hκu]

end Kummer

/-! ### Parity of valuations on `k(a, y)` -/

section Parity

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {V : ValuationSubring F}

variable (V) in
/-- `v(z)²` is an integral power of `v(a)`. -/
def IntVal (a z : F) : Prop :=
  ∃ m n : ℕ, V.valuation z ^ 2 * V.valuation a ^ m = V.valuation a ^ n

variable (hk : ∀ c : k, algebraMap k F c ∈ V) {a : F} (ha : a ∉ V)

include ha in
lemma valuation_ne_zero_of_notMem : V.valuation a ≠ 0 :=
  (zero_lt_one.trans (one_lt_valuation_of_notMem ha)).ne'

include hk ha in
lemma intVal_of_mem_adjoin {z : F} (hz : z ∈ IntermediateField.adjoin k {a}) (hz0 : z ≠ 0) :
    IntVal V a z := by
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k z).1 hz
  have hr : aeval a r ≠ 0 := fun h0 => hz0 (by rw [h0, zero_div])
  have hs : aeval a s ≠ 0 := fun h0 => hz0 (by rw [h0, div_zero])
  have hr' : r ≠ 0 := fun h0 => hr (by rw [h0, map_zero])
  have hs' : s ≠ 0 := fun h0 => hs (by rw [h0, map_zero])
  have hv := valuation_ne_zero_of_notMem ha
  refine ⟨s.natDegree * 2, r.natDegree * 2, ?_⟩
  rw [map_div₀, val_aeval hk ha hr', val_aeval hk ha hs', div_pow, ← pow_mul, ← pow_mul,
    div_mul_cancel₀ _ (pow_ne_zero _ hv)]

lemma intVal_mul {z w : F} (hz : IntVal V a z) (hw : IntVal V a w) : IntVal V a (z * w) := by
  obtain ⟨m, n, h⟩ := hz
  obtain ⟨m', n', h'⟩ := hw
  refine ⟨m + m', n + n', ?_⟩
  rw [map_mul, mul_pow, pow_add, pow_add, ← h, ← h']
  exact mul_mul_mul_comm _ _ _ _

include hk ha in
lemma intVal_of_sq {y : F} {c : k[X]} (hc : c.natDegree = 3) (hy : y ^ 2 = aeval a c) :
    IntVal V a y := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨0, 3, ?_⟩
  rw [pow_zero, mul_one, ← map_pow, hy, val_aeval hk ha hc0, hc]

lemma intVal_add {z w : F} (hz : IntVal V a z) (hw : IntVal V a w)
    (hne : V.valuation z ≠ V.valuation w) : IntVal V a (z + w) := by
  rw [IntVal, Valuation.map_add_of_distinct_val _ hne]
  rcases max_choice (V.valuation z) (V.valuation w) with h | h <;> rw [h]
  · exact hz
  · exact hw

include hk ha in
/-- **Elements of `k(a, y)`** (`y² = c(a)`, `deg c = 3`) have `v(·)²` an integral power of
`v(a)`. -/
lemma intVal_add_mul {y : F} {c : k[X]} (hc : c.natDegree = 3) (hy : y ^ 2 = aeval a c)
    {g h : F} (hg : g ∈ IntermediateField.adjoin k {a}) (hh : h ∈ IntermediateField.adjoin k {a})
    (h0 : g + h * y ≠ 0) : IntVal V a (g + h * y) := by
  by_cases hg0 : g = 0
  · rw [hg0, zero_add] at h0 ⊢
    have hh0 : h ≠ 0 := fun e => h0 (by rw [e, zero_mul])
    exact intVal_mul (intVal_of_mem_adjoin hk ha hh hh0) (intVal_of_sq hk ha hc hy)
  by_cases hh0 : h = 0
  · rw [hh0, zero_mul, add_zero]
    exact intVal_of_mem_adjoin hk ha hg hg0
  exact intVal_add (intVal_of_mem_adjoin hk ha hg hg0)
    (intVal_mul (intVal_of_mem_adjoin hk ha hh hh0) (intVal_of_sq hk ha hc hy))
    (val_ne_mul hk ha hc hy hg hh hg0 hh0)

include ha in
/-- An element `u` with `v(u)⁴ = v(a)³` is not `IntVal`. -/
lemma not_intVal {w : F} (hw : V.valuation w ^ 4 = V.valuation a ^ 3) : ¬ IntVal V a w := by
  rintro ⟨m, n, h⟩
  have h1 := one_lt_valuation_of_notMem ha
  have key : V.valuation a ^ (2 * n) = V.valuation a ^ (3 + 2 * m) := by
    rw [pow_mul', ← h, mul_pow, ← pow_mul, show 2 * 2 = 4 from rfl, hw, ← pow_mul, pow_add,
      mul_comm m 2]
  have := (pow_right_strictMono₀ h1).injective key
  omega

include ha in
/-- **The parity argument for `u`**: for `IntVal` elements `g, h` and `v(u)⁴ = v(a)³`,
`v(g) ≠ v(h u)` unless `g = h = 0`. -/
lemma val_ne_mul_root {g h w : F} (hg : IntVal V a g) (hh : IntVal V a h) (hh0 : h ≠ 0)
    (hw : V.valuation w ^ 4 = V.valuation a ^ 3) :
    V.valuation g ≠ V.valuation (h * w) := by
  intro heq
  obtain ⟨m, n, hmn⟩ := hg
  obtain ⟨m', n', hmn'⟩ := hh
  have hv0 : V.valuation h ≠ 0 := (Valuation.ne_zero_iff _).2 hh0
  apply not_intVal ha hw
  refine ⟨m + n', n + m', ?_⟩
  have e : V.valuation w = V.valuation g / V.valuation h := by
    rw [heq, map_mul, mul_div_cancel_left₀ _ hv0]
  have hh2 : V.valuation h ^ 2 ≠ 0 := pow_ne_zero _ hv0
  rw [e, div_pow, pow_add, pow_add, ← hmn', ← hmn]
  field_simp

end Parity

/-! ### Lines through two points -/

section Line

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

/-- **The line through two points**: for `(x, y)` on `W`,
`(y − L(x)) (y + L(x) + a₁ x + a₃) = (x − x₁)(x − x₂)(x − x₃)` (`addPolynomial_slope`). -/
lemma line_identity {x₁ x₂ y₁ y₂ x y : K} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) (h : W.Equation x y) :
    (y - (W.slope x₁ x₂ y₁ y₂ * (x - x₁) + y₁)) *
      (y + (W.slope x₁ x₂ y₁ y₂ * (x - x₁) + y₁) + W.a₁ * x + W.a₃) =
      (x - x₁) * (x - x₂) * (x - W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)) := by
  have e := congrArg (Polynomial.eval x) (W.addPolynomial_slope h₁ h₂ (fun h => hx h.1))
  rw [Affine.addPolynomial_eq] at e
  simp only [Cubic.toPoly, eval_neg, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    eval_sub] at e
  rw [Affine.equation_iff] at h
  linear_combination h - e

end Line

/-! ### Valuations on a Weierstrass curve -/

section CurveVal

variable {F : Type*} [Field F] (V : ValuationSubring F)

/-- On a Weierstrass curve with coefficients in `V`, `x ∈ V` forces `y ∈ V`. -/
lemma mem_of_equation {W : WeierstrassCurve.Affine F} (h₁ : W.a₁ ∈ V) (h₂ : W.a₂ ∈ V)
    (h₃ : W.a₃ ∈ V) (h₄ : W.a₄ ∈ V) (h₆ : W.a₆ ∈ V) {x y : F} (hx : x ∈ V)
    (h : W.Equation x y) : y ∈ V := by
  rw [Affine.equation_iff] at h
  by_contra hy
  have hy0 : y ≠ 0 := fun e => hy (e ▸ V.zero_mem)
  have hr : V.valuation y⁻¹ < 1 := (ValuationSubring.mem_nonunits_iff V).1
    (V.inv_mem_nonunits_iff.2 (Or.inr hy))
  have hle : ∀ z ∈ V, V.valuation z ≤ 1 := fun z hz => (V.valuation_le_one_iff z).2 hz
  have hc : x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ ∈ V :=
    add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem h₂ (pow_mem hx 2))) (mul_mem h₄ hx)) h₆
  have hl : W.a₁ * x + W.a₃ ∈ V := add_mem (mul_mem h₁ hx) h₃
  have e : (1 : F) = (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) * y⁻¹ ^ 2 -
      (W.a₁ * x + W.a₃) * y⁻¹ := by
    field_simp
    linear_combination h
  have hlt : V.valuation (1 : F) < 1 := by
    rw [e]
    refine Valuation.map_sub_lt _ ?_ ?_
    · rw [map_mul, map_pow]
      exact (mul_le_of_le_one_left' (hle _ hc)).trans_lt (pow_lt_one₀ zero_le hr two_ne_zero)
    · rw [map_mul]
      exact (mul_le_of_le_one_left' (hle _ hl)).trans_lt hr
  rw [map_one] at hlt
  exact lt_irrefl _ hlt

lemma lt_one_of_mul3 {x y z : F} (hx : x ∈ V) (hy : y ∈ V) (hz : z ∈ V)
    (h : V.valuation (x * y * z) < 1) :
    V.valuation x < 1 ∨ V.valuation y < 1 ∨ V.valuation z < 1 := by
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have e1 := le_antisymm ((V.valuation_le_one_iff x).2 hx) h1
  have e2 := le_antisymm ((V.valuation_le_one_iff y).2 hy) h2
  have e3 := le_antisymm ((V.valuation_le_one_iff z).2 hz) h3
  rw [map_mul, map_mul, e1, e2, e3, mul_one, mul_one] at h
  exact lt_irrefl _ h

variable {k : Type*} [Field k] [Algebra k F] (hk : ∀ c : k, algebraMap k F c ∈ V)

include hk in
/-- **Polynomials preserve congruences**: `a ≡ b` mod `m_V` gives `p(a) ≡ p(b)`. -/
lemma aeval_sub_lt (p : k[X]) {a b : F} (ha : a ∈ V) (hb : b ∈ V)
    (hab : V.valuation (a - b) < 1) : V.valuation (aeval a p - aeval b p) < 1 := by
  let φ : k →+* V := (algebraMap k F).codRestrict V.toSubring hk
  have he : ∀ (z : F) (hz : z ∈ V), (((p.map φ).eval ⟨z, hz⟩ : V) : F) = aeval z p := by
    intro z hz
    rw [Polynomial.eval_map]
    exact Polynomial.hom_eval₂ p φ V.toSubring.subtype ⟨z, hz⟩
  obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub (⟨a, ha⟩ : V) ⟨b, hb⟩ (p.map φ)
  have key : aeval a p - aeval b p = (a - b) * (c : F) := by
    rw [← he a ha, ← he b hb]
    exact congrArg (fun z : V => (z : F)) hc
  rw [key, map_mul]
  exact (mul_le_of_le_one_right' ((V.valuation_le_one_iff _).2 c.2)).trans_lt hab

end CurveVal

/-! ### The model curve -/

section Model

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]

omit [E.IsElliptic] in
lemma baseChange_a₁ : (E⁄(Ω E)).toAffine.a₁ = algebraMap k (Ω E) E.a₁ := rfl
omit [E.IsElliptic] in
lemma baseChange_a₂ : (E⁄(Ω E)).toAffine.a₂ = algebraMap k (Ω E) E.a₂ := rfl
omit [E.IsElliptic] in
lemma baseChange_a₃ : (E⁄(Ω E)).toAffine.a₃ = algebraMap k (Ω E) E.a₃ := rfl
omit [E.IsElliptic] in
lemma baseChange_a₄ : (E⁄(Ω E)).toAffine.a₄ = algebraMap k (Ω E) E.a₄ := rfl
omit [E.IsElliptic] in
lemma baseChange_a₆ : (E⁄(Ω E)).toAffine.a₆ = algebraMap k (Ω E) E.a₆ := rfl

/-- The `x`-coordinate of a nonzero `ℓ`-torsion point is a root of `ΨSq_ℓ` but not of `Φ_ℓ`. -/
lemma ΨSq_torsion {ℓ : ℕ} (hℓ : ℓ ≠ 0) {xS yS : k} (hS : E.toAffine.Nonsingular xS yS)
    (hT : ℓ • (Affine.Point.some xS yS hS : E.toAffine.Point) = 0) :
    aeval (algebraMap k (Ω E) xS) ((shortModel E).ΨSq ℓ) = 0 ∧
      aeval (algebraMap k (Ω E) xS) ((shortModel E).Φ ℓ) ≠ 0 := by
  have ha₁ : ((shortModel E)⁄(Ω E)).toAffine.a₁ = 0 := by
    simp [WeierstrassCurve.baseChange, IntegralTorsion.completeSquare_a₁]
  have ha₃ : ((shortModel E)⁄(Ω E)).toAffine.a₃ = 0 := by
    simp [WeierstrassCurve.baseChange, IntegralTorsion.completeSquare_a₃]
  have h' : (E⁄(Ω E)).toAffine.Nonsingular (algebraMap k (Ω E) xS) (algebraMap k (Ω E) yS) :=
    (E.toAffine.map_nonsingular (algebraMap k (Ω E)).injective xS yS).mpr hS
  have h1 := (nonsingular_vc (vcΩ E) (E⁄(Ω E)) _ _).mp h'
  rw [vcΩ_smul] at h1
  obtain ⟨h'', hs⟩ := exists_some_eq (vcX_vcΩ E _) h1
  rw [← toShort_some E h' h1] at hs
  have hz : ℓ • toShort E (Affine.Point.some _ _ h') = 0 := by
    rw [← map_nsmul]
    have e : (Affine.Point.some _ _ h' : Pt E) = base E (Affine.Point.some xS yS hS) := rfl
    rw [e, ← map_nsmul, hT, map_zero, map_zero]
  rw [hs] at hz
  have hΨ := (Iut.Torsion.smul_eq_zero_iff_ΨSq ha₁ ha₃ h'' ℓ).1 hz
  have e1 : (((shortModel E)⁄(Ω E)).toAffine.ΨSq ℓ).eval (algebraMap k (Ω E) xS) =
      aeval (algebraMap k (Ω E) xS) ((shortModel E).ΨSq ℓ) := by
    rw [show ((shortModel E)⁄(Ω E)).toAffine.ΨSq ℓ = ((shortModel E).ΨSq ℓ).map
      (algebraMap k (Ω E)) from map_ΨSq _ _ _, eval_map_algebraMap]
  have e2 : (((shortModel E)⁄(Ω E)).toAffine.Φ ℓ).eval (algebraMap k (Ω E) xS) =
      aeval (algebraMap k (Ω E) xS) ((shortModel E).Φ ℓ) := by
    rw [show ((shortModel E)⁄(Ω E)).toAffine.Φ ℓ = ((shortModel E).Φ ℓ).map
      (algebraMap k (Ω E)) from map_Φ _ _ _, eval_map_algebraMap]
  refine ⟨by rw [← e1]; exact hΨ, fun h0 => ?_⟩
  exact Iut.Torsion.ΨSq_ne_zero_of_Φ_eq_zero ha₁ ha₃ ℓ hℓ (by rw [e2]; exact h0) hΨ

/-- **The secant line through two `ℓ`-torsion points is a unit at the non-cuspidal places**:
for `ℓ (a, b) = G` and a place `V ⊇ k` with `x(G) ∈ V`, `b − L(a)` has valuation `1` if the
`x`-coordinates `x₁, x₂, x₃` of the three points on the line are those of nonzero `ℓ`-torsion
points (`(b − L(a)) (b + L(a) + a₁ a + a₃) = ∏ (a − xᵢ)` and `x(G) ΨSq_ℓ(a) = Φ_ℓ(a)`). -/
theorem val_line_eq_one {ℓ : ℕ} (hℓ : ℓ ≠ 0) {V : ValuationSubring (Ω E)}
    (hk : ContainsBase E V) (hx : xG E ∈ V) {a b : Ω E}
    (hab : (E⁄(Ω E)).toAffine.Nonsingular a b)
    (hP : ℓ • (Affine.Point.some a b hab : Pt E) = genericPoint E) {x₁ x₂ y₁ y₂ : k}
    (h₁ : E.toAffine.Equation x₁ y₁) (h₂ : E.toAffine.Equation x₂ y₂) (hx₁₂ : x₁ ≠ x₂)
    (hΨ : ∀ z ∈ ({x₁, x₂, E.toAffine.addX x₁ x₂ (E.toAffine.slope x₁ x₂ y₁ y₂)} : Set k),
      aeval (algebraMap k (Ω E) z) ((shortModel E).ΨSq ℓ) = 0 ∧
        aeval (algebraMap k (Ω E) z) ((shortModel E).Φ ℓ) ≠ 0) :
    V.valuation (b - (algebraMap k (Ω E) (E.toAffine.slope x₁ x₂ y₁ y₂) *
      (a - algebraMap k (Ω E) x₁) + algebraMap k (Ω E) y₁)) = 1 := by
  have hk' : ∀ c : k, algebraMap k (Ω E) c ∈ V := hk
  have hle : ∀ z ∈ V, V.valuation z ≤ 1 := fun z hz => (V.valuation_le_one_iff z).2 hz
  have ha : a ∈ V := by
    by_contra h
    exact xG_notMem E hℓ hab hP hk h hx
  have hb : b ∈ V := mem_of_equation V (hk' _) (hk' _) (hk' _) (hk' _) (hk' _) ha hab.1
  set sl := E.toAffine.slope x₁ x₂ y₁ y₂
  set x₃ := E.toAffine.addX x₁ x₂ sl
  -- the identity over `Ω`
  have hΩ₁ : (E⁄(Ω E)).toAffine.Equation (algebraMap k (Ω E) x₁) (algebraMap k (Ω E) y₁) :=
    (E.toAffine.map_equation (algebraMap k (Ω E)).injective x₁ y₁).2 h₁
  have hΩ₂ : (E⁄(Ω E)).toAffine.Equation (algebraMap k (Ω E) x₂) (algebraMap k (Ω E) y₂) :=
    (E.toAffine.map_equation (algebraMap k (Ω E)).injective x₂ y₂).2 h₂
  have hxΩ : algebraMap k (Ω E) x₁ ≠ algebraMap k (Ω E) x₂ :=
    fun h => hx₁₂ ((algebraMap k (Ω E)).injective h)
  have hsl : (E⁄(Ω E)).toAffine.slope (algebraMap k (Ω E) x₁) (algebraMap k (Ω E) x₂)
      (algebraMap k (Ω E) y₁) (algebraMap k (Ω E) y₂) = algebraMap k (Ω E) sl := by
    have hsk : sl = (y₁ - y₂) / (x₁ - x₂) := Affine.slope_of_X_ne hx₁₂
    rw [Affine.slope_of_X_ne hxΩ, hsk, map_div₀, map_sub, map_sub]
  have hX3 : (E⁄(Ω E)).toAffine.addX (algebraMap k (Ω E) x₁) (algebraMap k (Ω E) x₂)
      (algebraMap k (Ω E) sl) = algebraMap k (Ω E) x₃ := by
    simp only [x₃, Affine.addX, map_sub, map_add, map_mul, map_pow]
    rfl
  have hid := line_identity (E⁄(Ω E)).toAffine hΩ₁ hΩ₂ hxΩ hab.1
  rw [hsl, hX3, baseChange_a₁, baseChange_a₃] at hid
  set f := b - (algebraMap k (Ω E) sl * (a - algebraMap k (Ω E) x₁) + algebraMap k (Ω E) y₁)
  have hL : algebraMap k (Ω E) sl * (a - algebraMap k (Ω E) x₁) + algebraMap k (Ω E) y₁ ∈ V :=
    add_mem (mul_mem (hk' _) (sub_mem ha (hk' _))) (hk' _)
  have hfV : f ∈ V := sub_mem hb hL
  refine le_antisymm (hle _ hfV) (not_lt.1 fun hlt => ?_)
  have hg : b + (algebraMap k (Ω E) sl * (a - algebraMap k (Ω E) x₁) + algebraMap k (Ω E) y₁) +
      algebraMap k (Ω E) E.a₁ * a + algebraMap k (Ω E) E.a₃ ∈ V :=
    add_mem (add_mem (add_mem hb hL) (mul_mem (hk' _) ha)) (hk' _)
  have hprod : V.valuation ((a - algebraMap k (Ω E) x₁) * (a - algebraMap k (Ω E) x₂) *
      (a - algebraMap k (Ω E) x₃)) < 1 := by
    rw [← hid, map_mul]
    exact (mul_le_of_le_one_right' (hle _ hg)).trans_lt hlt
  have hcase : ∀ z ∈ ({x₁, x₂, x₃} : Set k), V.valuation (a - algebraMap k (Ω E) z) < 1 →
      False := by
    intro z hz hlt'
    obtain ⟨hz1, hz2⟩ := hΨ z hz
    have hΨa : V.valuation (aeval a ((shortModel E).ΨSq ℓ)) < 1 := by
      have := aeval_sub_lt V hk' ((shortModel E).ΨSq ℓ) ha (hk' z) hlt'
      rwa [hz1, sub_zero] at this
    obtain ⟨-, hX⟩ := xG_mul_ΨSq E hab hP
    have hΦa : V.valuation (aeval a ((shortModel E).Φ ℓ)) < 1 := by
      rw [← hX, map_mul]
      exact (mul_le_of_le_one_left' (hle _ hx)).trans_lt hΨa
    have hd := aeval_sub_lt V hk' ((shortModel E).Φ ℓ) ha (hk' z) hlt'
    have hΦz : V.valuation (aeval (algebraMap k (Ω E) z) ((shortModel E).Φ ℓ)) < 1 := by
      have e : aeval (algebraMap k (Ω E) z) ((shortModel E).Φ ℓ) =
          aeval a ((shortModel E).Φ ℓ) -
            (aeval a ((shortModel E).Φ ℓ) - aeval (algebraMap k (Ω E) z) ((shortModel E).Φ ℓ)) :=
        by ring
      rw [e]
      exact Valuation.map_sub_lt _ hΦa hd
    rw [aeval_algebraMap_apply_eq_algebraMap_eval] at hz2 hΦz
    have hne : ((shortModel E).Φ ℓ).eval z ≠ 0 := fun h0 => hz2 (by rw [h0, map_zero])
    rw [valuation_algebraMap_base hk' hne] at hΦz
    exact lt_irrefl _ hΦz
  rcases lt_one_of_mul3 V (sub_mem ha (hk' _)) (sub_mem ha (hk' _)) (sub_mem ha (hk' _)) hprod
    with h | h | h
  · exact hcase x₁ (by simp) h
  · exact hcase x₂ (by simp) h
  · exact hcase x₃ (by simp) h

/-- The action of `σ ∈ Gal(Ω / k(x))` on an affine point, coordinatewise. -/
lemma act_some_eq {σ : Gal E} {a b : Ω E} (hab : (E⁄(Ω E)).toAffine.Nonsingular a b) :
    ∃ h', act E σ (.some a b hab) = .some (σ a) (σ b) h' :=
  ⟨_, act_some E σ hab ((E.toAffine.baseChange_nonsingular (σk E σ).injective a b).2 hab)⟩

/-- **Elements of `S0` fix the division point `Q_ℓ − T`.** -/
lemma fix_of_mem_S0 {ℓ : ℕ} (hℓ : ℓ ≠ 0) {T : E.toAffine.Point} {a b : Ω E}
    (hab : (E⁄(Ω E)).toAffine.Nonsingular a b) (hP : Qpt E ℓ - base E T = .some a b hab)
    {s : Gal E} (hs : s ∈ S0 E) : s a = a ∧ s b = b := by
  obtain ⟨hsG, V, hk, hx, hsV⟩ := hs
  have hQ := inertia_fixes_division E s V hk hx hsV hsG (Qpt E ℓ) ℓ (Nat.pos_of_ne_zero hℓ)
    (GenuineBaseChange.nsmul_Qpt E hℓ)
  have hPf : act E s (Qpt E ℓ - base E T) = Qpt E ℓ - base E T := by
    rw [map_sub, hQ, act_base]
  obtain ⟨h', e⟩ := act_some_eq (σ := s) hab
  rw [hP, e, Affine.Point.some.injEq] at hPf
  exact hPf

/-- **An inertia element fixing `f` fixes `√(f/c₀)` if `f` is a unit.** -/
lemma fix_root_of_inertia {s : Gal E} {V : ValuationSubring (Ω E)} (hk : ContainsBase E V)
    (hsV : s ∈ GaloisPi1.inertia V) {f u : Ω E} {c₀ : k} (hc₀ : c₀ ≠ 0)
    (hf : V.valuation f = 1) (hu : u ^ 2 = f / algebraMap k (Ω E) c₀) (hsf : s f = f) :
    s u = u := by
  have hk' : ∀ c : k, algebraMap k (Ω E) c ∈ V := hk
  have hvu2 : V.valuation u ^ 2 = 1 := by
    rw [← map_pow, hu, map_div₀, hf, valuation_algebraMap_base hk' hc₀, div_one]
  have hvu : V.valuation u = 1 := by
    rcases lt_trichotomy (V.valuation u) 1 with h | h | h
    · exact absurd hvu2 (pow_lt_one₀ zero_le h two_ne_zero).ne
    · exact h
    · exact absurd hvu2 (one_lt_pow₀ h two_ne_zero).ne'
  have huV : u ∈ V := (V.valuation_le_one_iff u).1 hvu.le
  have hsc : s (algebraMap k (Ω E) c₀) = algebraMap k (Ω E) c₀ :=
    s.commutes' ⟨_, (baseField E).algebraMap_mem c₀⟩
  have hsq : (s u) ^ 2 = u ^ 2 := by
    rw [← map_pow, hu, map_div₀, hsf, hsc]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact h
  · exfalso
    have hlt := hsV u huV
    rw [h, show -u - u = -(algebraMap k (Ω E) 2 * u) by rw [map_ofNat]; ring, Valuation.map_neg,
      map_mul, valuation_algebraMap_base hk' two_ne_zero, one_mul, hvu] at hlt
    exact lt_irrefl _ hlt

end Model

/-! ### Fixing subgroups -/

section Fix

variable {P Ω : Type*} [Field P] [Field Ω] [Algebra P Ω]

/-- The automorphisms fixing every element of `S`. -/
def fixSub (S : Set Ω) : Subgroup (Ω ≃ₐ[P] Ω) where
  carrier := {σ | ∀ z ∈ S, σ z = z}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {σ τ} hσ hτ z hz => by
    change σ (τ z) = z
    rw [hτ z hz, hσ z hz]
  inv_mem' := fun {σ} hσ z hz => by
    change σ.symm z = z
    rw [AlgEquiv.symm_apply_eq, hσ z hz]

lemma isClosed_fixSub [Algebra.IsAlgebraic P Ω] (S : Set Ω) [Finite S] :
    IsClosed (fixSub (P := P) S : Set (Ω ≃ₐ[P] Ω)) := by
  haveI : FiniteDimensional P (IntermediateField.adjoin P S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic (R := P) x).isIntegral
  refine Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono (fun σ hσ z hz => ?_)
    (IntermediateField.adjoin P S).fixingSubgroup_isOpen)
  exact (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ z
    (IntermediateField.subset_adjoin P S hz)

end Fix

section AddCongr

variable {F : Type*} [Field F]

/-- The `y`-part of the secant sum, cleared of the unit `(1 - s r) ^ 3`. -/
lemma addY_aux {r w s t l x D E Q : F}
    (hx : (x - s) * (1 - s * r) ^ 2 = r * E - D * (w * r ^ 2))
    (hl : l * (1 - s * r) = w * r - t * r) (hQ : w ^ 2 * r ^ 3 = Q) :
    (l * (x - s) + D) * (1 - s * r) ^ 3 = w * r ^ 2 * E - D * (Q - 1) -
      D * (1 - (1 - s * r) ^ 3) - t * r * (r * E - D * (w * r ^ 2)) := by
  linear_combination ((x - s) * (1 - s * r) ^ 2) * hl + (w * r - t * r) * hx - D * hQ

/-- The `x`-part of the secant sum, in the coordinate `r = 1/u`. -/
lemma addX_sub_aux {u w s r x B C D : F} (hur : u * r = 1)
    (key : x * (u - s) ^ 2 = s * u ^ 2 + B * u + C - D * w) :
    (x - s) * (1 - s * r) ^ 2 = r * (B + C * r + 2 * s ^ 2 - s ^ 3 * r) - D * (w * r ^ 2) := by
  linear_combination r ^ 2 * key + (-x * (1 + u * r - 2 * s * r) + s * (u * r + 1) + B * r) * hur

/-- The equation of the curve in the coordinates `r = 1/u`, `z = w/u²`. -/
lemma addY_hQ {a₁ a₂ a₃ a₄ a₆ u w r : F} (hur : u * r = 1)
    (heq : w ^ 2 + a₁ * u * w + a₃ * w = u ^ 3 + a₂ * u ^ 2 + a₄ * u + a₆) :
    w ^ 2 * r ^ 3 = 1 + a₂ * r + a₄ * r ^ 2 + a₆ * r ^ 3 - a₁ * (w * r ^ 2) -
      a₃ * (w * r ^ 2) * r := by
  linear_combination r ^ 3 * heq + ((u * r) ^ 2 + u * r + 1 + a₂ * r * (u * r + 1) +
    a₄ * r ^ 2 - a₁ * w * r ^ 2) * hur

/-- **The secant sum of a pole and an integral point reduces to the integral point.** -/
theorem addXY_congr (W : ValuationSubring F) {a₁ a₂ a₃ a₄ a₆ u w s t : F}
    (h₁ : a₁ ∈ W) (h₂ : a₂ ∈ W) (h₃ : a₃ ∈ W) (h₄ : a₄ ∈ W) (h₆ : a₆ ∈ W) (hs : s ∈ W)
    (ht : t ∈ W) (hu : u ∉ W)
    (heq : w ^ 2 + a₁ * u * w + a₃ * w = u ^ 3 + a₂ * u ^ 2 + a₄ * u + a₆) :
    W.valuation ((((w - t) / (u - s)) ^ 2 + a₁ * ((w - t) / (u - s)) - a₂ - u - s) - s) < 1 ∧
    W.valuation ((-((w - t) / (u - s) * ((((w - t) / (u - s)) ^ 2 + a₁ * ((w - t) / (u - s)) -
      a₂ - u - s) - u) + w) - a₁ * (((w - t) / (u - s)) ^ 2 + a₁ * ((w - t) / (u - s)) - a₂ - u
      - s) - a₃) - t) < 1 := by
  set v := W.valuation
  have hle : ∀ x ∈ W, v x ≤ 1 := fun x hx => (W.valuation_le_one_iff x).2 hx
  have hm : ∀ a b : F, a ∈ W → v b < 1 → v (a * b) < 1 := fun a b ha hb => by
    rw [map_mul]; exact (mul_le_of_le_one_left' (hle a ha)).trans_lt hb
  have hu0 : u ≠ 0 := fun h => hu (h ▸ W.zero_mem)
  have hus : u - s ≠ 0 := sub_ne_zero.2 fun h => hu (h ▸ hs)
  set r := u⁻¹ with hr_def
  have hur : u * r = 1 := mul_inv_cancel₀ hu0
  have hr : v r < 1 := (ValuationSubring.mem_nonunits_iff W).1
    (W.inv_mem_nonunits_iff.2 (Or.inr hu))
  have hrW : r ∈ W := (W.valuation_le_one_iff r).1 hr.le
  set z := w * r ^ 2 with hz_def
  set Q := 1 + a₂ * r + a₄ * r ^ 2 + a₆ * r ^ 3 - a₁ * z - a₃ * z * r with hQ_def
  have hQ : w ^ 2 * r ^ 3 = Q := addY_hQ hur heq
  have hP : (1 + a₂ * r + a₄ * r ^ 2 + a₆ * r ^ 3) ∈ W := by
    refine add_mem (add_mem (add_mem W.one_mem (mul_mem h₂ hrW)) ?_) ?_ <;>
      exact mul_mem ‹_› (pow_mem hrW _)
  have hz : v z < 1 := by
    by_contra hge
    rw [not_lt] at hge
    have hpos : 0 < v z := zero_lt_one.trans_le hge
    have e : z * z = (1 + a₂ * r + a₄ * r ^ 2 + a₆ * r ^ 3) * r - z * (a₁ * r) -
        z * (a₃ * r ^ 2) := by
      have hQ' := hQ
      rw [hQ_def, hz_def] at hQ'
      rw [hz_def]
      linear_combination r * hQ'
    have hlt : v ((1 + a₂ * r + a₄ * r ^ 2 + a₆ * r ^ 3) * r - z * (a₁ * r) -
        z * (a₃ * r ^ 2)) < v z := by
      refine v.map_sub_lt (v.map_sub_lt ((hm _ _ hP hr).trans_le hge) ?_) ?_
      · rw [map_mul]
        exact mul_lt_of_lt_one_right hpos (hm _ _ h₁ hr)
      · rw [map_mul]
        refine mul_lt_of_lt_one_right hpos (hm _ _ h₃ ?_)
        rw [map_pow]
        exact pow_lt_one₀ zero_le hr two_ne_zero
    rw [← e, map_mul] at hlt
    exact absurd (le_mul_of_one_le_right zero_le hge) (not_le.2 hlt)
  have hzW : z ∈ W := (W.valuation_le_one_iff z).1 hz.le
  have hQ1 : v (Q - 1) < 1 := by
    have : Q - 1 = (a₂ + a₄ * r + a₆ * r ^ 2) * r - (a₁ + a₃ * r) * z := by
      simp only [hQ_def]; ring
    rw [this]
    refine v.map_sub_lt (hm _ _ ?_ hr) (hm _ _ (add_mem h₁ (mul_mem h₃ hrW)) hz)
    exact add_mem (add_mem h₂ (mul_mem h₄ hrW)) (mul_mem h₆ (pow_mem hrW 2))
  have h2W : (2 : F) ∈ W := by exact_mod_cast natCast_mem W 2
  have h3W : (3 : F) ∈ W := by exact_mod_cast natCast_mem W 3
  set l := (w - t) / (u - s) with hl_def
  set x := l ^ 2 + a₁ * l - a₂ - u - s
  have hl' : l * (u - s) = w - t := div_mul_cancel₀ _ hus
  have hx := addX_sub_aux hur (addX_mul_sq (a₄ := a₄) (a₆ := a₆) hl' heq)
  have hl : l * (1 - s * r) = w * r - t * r := by
    linear_combination r * hl' - l * hur
  have hy := addY_aux hx hl hQ
  have hunit : v (1 - s * r) = 1 := by
    apply Valuation.map_one_sub_of_lt
    rw [map_mul]
    exact (mul_le_of_le_one_left' (hle s hs)).trans_lt hr
  have hB : a₄ + s ^ 2 - a₁ * t + (a₂ * s + a₂ * s) ∈ W :=
    add_mem (sub_mem (add_mem h₄ (pow_mem hs 2)) (mul_mem h₁ ht))
      (add_mem (mul_mem h₂ hs) (mul_mem h₂ hs))
  have hC : a₆ + t ^ 2 + a₁ * t * s - s ^ 3 - a₂ * s ^ 2 ∈ W := sub_mem (sub_mem (add_mem
    (add_mem h₆ (pow_mem ht 2)) (mul_mem (mul_mem h₁ ht) hs)) (pow_mem hs 3))
      (mul_mem h₂ (pow_mem hs 2))
  have hD : a₃ + t + t + a₁ * s ∈ W := add_mem (add_mem (add_mem h₃ ht) ht) (mul_mem h₁ hs)
  have hE : (a₄ + s ^ 2 - a₁ * t + (a₂ * s + a₂ * s)) +
      (a₆ + t ^ 2 + a₁ * t * s - s ^ 3 - a₂ * s ^ 2) * r + 2 * s ^ 2 - s ^ 3 * r ∈ W :=
    sub_mem (add_mem (add_mem hB (mul_mem hC hrW)) (mul_mem h2W (pow_mem hs 2)))
      (mul_mem (pow_mem hs 3) hrW)
  have hrE : v (r * ((a₄ + s ^ 2 - a₁ * t + (a₂ * s + a₂ * s)) +
      (a₆ + t ^ 2 + a₁ * t * s - s ^ 3 - a₂ * s ^ 2) * r + 2 * s ^ 2 - s ^ 3 * r) -
      (a₃ + t + t + a₁ * s) * (w * r ^ 2)) < 1 :=
    v.map_sub_lt (by rw [mul_comm]; exact hm _ _ hE hr) (hm _ _ hD hz)
  have hxs : v (x - s) < 1 := by
    have h2 := congrArg v hx
    rw [map_mul, map_pow, hunit, one_pow, mul_one] at h2
    rw [h2]; exact hrE
  refine ⟨hxs, ?_⟩
  have ey : -(l * (x - u) + w) - a₁ * x - a₃ - t =
      -(l * (x - s) + (a₃ + t + t + a₁ * s)) + a₁ * (s - x) := by
    linear_combination hl'
  rw [ey]
  have hsr3 : v (1 - (1 - s * r) ^ 3) < 1 := by
    have : 1 - (1 - s * r) ^ 3 = (s * (3 - 3 * (s * r) + (s * r) ^ 2)) * r := by ring
    rw [this]
    refine hm _ _ (mul_mem hs ?_) hr
    exact add_mem (sub_mem h3W (mul_mem h3W (mul_mem hs hrW)))
      (pow_mem (mul_mem hs hrW) 2)
  have hly : v (l * (x - s) + (a₃ + t + t + a₁ * s)) < 1 := by
    have h2 := congrArg v hy
    rw [map_mul, map_pow, hunit, one_pow, mul_one] at h2
    rw [h2]
    refine v.map_sub_lt (v.map_sub_lt (v.map_sub_lt ?_ (hm _ _ hD hQ1)) (hm _ _ hD hsr3)) ?_
    · rw [mul_comm]; exact hm _ _ hE hz
    · have hin : r * ((a₄ + s ^ 2 - a₁ * t + (a₂ * s + a₂ * s)) +
          (a₆ + t ^ 2 + a₁ * t * s - s ^ 3 - a₂ * s ^ 2) * r + 2 * s ^ 2 - s ^ 3 * r) -
          (a₃ + t + t + a₁ * s) * (w * r ^ 2) ∈ W :=
        sub_mem (mul_mem hrW hE) (mul_mem hD hzW)
      have h3 := hm _ _ hin hr
      rw [mul_comm] at h3
      rw [mul_assoc]
      exact hm _ _ ht h3
  refine v.map_add_lt (by rw [v.map_neg]; exact hly) (hm _ _ h₁ ?_)
  rw [← neg_sub, v.map_neg]
  exact hxs

end AddCongr

/-! ### The residue of `Q_ℓ − T₁` at a place over `T₂` -/

section Residue

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]

/-- **A pole plus a rational point reduces to the rational point** (`addXY_congr`). -/
theorem residue_of_pole {W : ValuationSubring (Ω E)} (hk : ContainsBase E W) {P' : Pt E}
    (hP' : IsPole E W P') {xR yR : k} (hR : E.toAffine.Nonsingular xR yR) {a b : Ω E}
    (hab : (E⁄(Ω E)).toAffine.Nonsingular a b)
    (hsum : P' + base E (.some xR yR hR) = .some a b hab) :
    W.valuation (a - algebraMap k (Ω E) xR) < 1 ∧ W.valuation (b - algebraMap k (Ω E) yR) < 1 := by
  have hk' : ∀ c : k, algebraMap k (Ω E) c ∈ W := hk
  rcases P' with _ | ⟨u, w, huw⟩
  · exact absurd hP' id
  have hu : u ∉ W := hP'
  have hR' : (E⁄(Ω E)).toAffine.Nonsingular (algebraMap k (Ω E) xR) (algebraMap k (Ω E) yR) :=
    (E.toAffine.map_nonsingular (algebraMap k (Ω E)).injective xR yR).mpr hR
  have hne : u ≠ algebraMap k (Ω E) xR := fun h => hu (h ▸ hk' xR)
  have hb : base E (.some xR yR hR) = .some _ _ hR' := rfl
  rw [hb, Affine.Point.add_some (fun h => hne h.1), Affine.Point.some.injEq] at hsum
  obtain ⟨hxa, hyb⟩ := hsum
  rw [← hxa, ← hyb, Affine.slope_of_X_ne hne]
  have heq := (Affine.equation_iff _ _).1 huw.1
  simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX]
  exact addXY_congr W (hk' _) (hk' _) (hk' _) (hk' _) (hk' _) (hk' _) (hk' _) hu heq

end Residue

/-! ### Choosing the secant -/

section Secant

variable {A : Type*} [AddCommGroup A] {ℓ : ℕ} [OddPrime ℓ]

lemma mem_of_two_nsmul_mem {Z : AddSubgroup A} {X : A} (hX : ℓ • X = 0) (h : 2 • X ∈ Z) :
    X ∈ Z := by
  obtain ⟨n, hn⟩ := OddPrime.prime.odd_of_ne_two (p := ℓ)
    (by have := OddPrime.two_lt (ℓ := ℓ); omega)
  have e : X = (n + 1) • (2 • X) := by
    calc X = ℓ • X + X := by rw [hX, zero_add]
      _ = (ℓ + 1) • X := by rw [add_smul, one_smul]
      _ = (n + 1) • (2 • X) := by rw [smul_smul]; congr 1; omega
  rw [e]
  exact Z.nsmul_mem h _

/-- **The secant through `S₁`, `S₁ + R`**: for `S₁ ∉ ⟨R⟩`, the points `S₁`, `S₂ = S₁ + R`,
`S₃ = −(S₁ + S₂)` are nonzero, `S₁ ≠ ±S₂` and `R ∉ {±S₁, ±S₂, ±S₃}`. -/
lemma secant_aux {R S₁ : A} (hS : S₁ ∉ AddSubgroup.zmultiples R) (hℓS : ℓ • S₁ = 0)
    (hR0 : R ≠ 0) :
    S₁ ≠ 0 ∧ S₁ + R ≠ 0 ∧ S₁ ≠ S₁ + R ∧ S₁ ≠ -(S₁ + R) ∧ R ≠ S₁ ∧ R ≠ -S₁ ∧
      R ≠ S₁ + R ∧ R ≠ -(S₁ + R) ∧ R ≠ -(S₁ + (S₁ + R)) ∧ R ≠ S₁ + (S₁ + R) := by
  have bad : ∀ m : ℕ, (m = 1 ∨ m = 2) → ∀ j : ℤ, m • S₁ - j • R = 0 → False := by
    intro m hm j e
    have hmem : m • S₁ ∈ AddSubgroup.zmultiples R := by
      rw [sub_eq_zero.1 e]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples R) j
    rcases hm with rfl | rfl
    · exact hS (by rwa [one_smul] at hmem)
    · exact hS (mem_of_two_nsmul_mem hℓS hmem)
  refine ⟨fun h => bad 1 (Or.inl rfl) 0 ?_, fun h => bad 1 (Or.inl rfl) (-1) ?_,
    fun h => hR0 ?_, fun h => bad 2 (Or.inr rfl) (-1) ?_, fun h => bad 1 (Or.inl rfl) 1 ?_,
    fun h => bad 1 (Or.inl rfl) (-1) ?_, fun h => bad 1 (Or.inl rfl) 0 ?_,
    fun h => bad 1 (Or.inl rfl) (-2) ?_, fun h => bad 2 (Or.inr rfl) (-2) ?_,
    fun h => bad 2 (Or.inr rfl) 0 ?_⟩
  · rw [← sub_eq_zero.2 h]; module
  · rw [← sub_eq_zero.2 h]; module
  · rw [← sub_eq_zero.2 h.symm]; module
  · rw [← sub_eq_zero.2 h]; module
  · rw [← sub_eq_zero.2 h.symm]; module
  · rw [← sub_eq_zero.2 h]; module
  · rw [← sub_eq_zero.2 h.symm]; module
  · rw [← sub_eq_zero.2 h]; module
  · rw [← sub_eq_zero.2 h]; module
  · rw [← sub_eq_zero.2 h.symm]; module

end Secant

/-! ### Separation -/

section Sep

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]

/-- Distinct affine points that are not negatives of each other have distinct `x`. -/
lemma x_ne_of_ne {x y x' y' : k} (h : E.toAffine.Nonsingular x y)
    (h' : E.toAffine.Nonsingular x' y')
    (hne : (Affine.Point.some x y h : E.toAffine.Point) ≠ .some x' y' h')
    (hne' : (Affine.Point.some x y h : E.toAffine.Point) ≠ -.some x' y' h') : x ≠ x' := by
  intro hx
  rcases Affine.Y_eq_of_X_eq h.1 h'.1 hx with hy | hy
  · subst hx hy
    exact hne rfl
  · apply hne'
    rw [Affine.Point.neg_some]
    subst hx hy
    rfl

lemma exists_not_mem_zmultiples {ℓ : ℕ} [OddPrime ℓ] (hcard : Nat.card (Tor E ℓ) = ℓ ^ 2)
    {R : E.toAffine.Point} (hR : ℓ • R = 0) :
    ∃ S ∈ Tor E ℓ, S ∉ AddSubgroup.zmultiples R := by
  by_contra hcon
  push Not at hcon
  have hle : Tor E ℓ ≤ AddSubgroup.zmultiples R := hcon
  have hℓ : 0 < ℓ := (OddPrime.prime (ℓ := ℓ)).pos
  haveI : Finite (AddSubgroup.zmultiples R) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_zmultiples]
    exact (IsOfFinAddOrder.addOrderOf_pos
      (isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨ℓ, hℓ, hR⟩)).ne'
  have h1 := AddSubgroup.card_le_of_le hle
  rw [hcard, Nat.card_zmultiples] at h1
  have h2 := addOrderOf_le_of_nsmul_eq_zero hℓ hR
  have h3 : ℓ < ℓ ^ 2 := by
    have := (OddPrime.prime (ℓ := ℓ)).one_lt
    nlinarith
  omega

/-- `δ` in the decomposition group of `W` preserves the maximal ideal. -/
lemma lt_one_of_mem_decompGal {P Ω : Type u} [Field P] [Field Ω] [Algebra P Ω]
    {W : ValuationSubring Ω} {δ : Ω ≃ₐ[P] Ω}
    (hδ : δ ∈ CurvesJacobian.Cusp.decompGal P W) {z : Ω} (hz : W.valuation z < 1) :
    W.valuation (δ z) < 1 := by
  have hδ' : ∀ x, δ x ∈ W ↔ x ∈ W := CurvesJacobian.Cusp.mem_decompGal.1 hδ
  rw [Iut.Reconstruction.HemiGenuine.valuation_lt_one_iff_mem'] at hz ⊢
  obtain ⟨hzW, h0⟩ := hz
  refine ⟨(hδ' z).2 hzW, ?_⟩
  rcases h0 with h0 | h0
  · left
    rw [h0, map_zero]
  · right
    intro h
    rw [← map_inv₀] at h
    exact h0 ((hδ' _).1 h)

end Sep

/-! ### The ramified square root at a cuspidal place -/

section Ramified

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]

/-- **The Kummer automorphism at a pole place**: for a point `(a, b)` of `E` with `a ∉ W`
(`W ⊇ k`), `x(G) ∈ k(a)`, a linear `m ∈ k[X]` and `u² = (y' − m(a))/c₀` with
`y' = b + (a₁ a + a₃)/2`, some `τ ∈ Gal(Ω / k(x))` stabilises `W`, fixes `a`, `b` and maps
`u ↦ −u` (`v(u)⁴ = v(a)³` is not an integral power of `v(a)^{1/2}`, `exists_fix_neg_gen`). -/
theorem exists_fix_neg_root {W : ValuationSubring (Ω E)} (hk : ContainsBase E W) {a b : Ω E}
    (hab : (E⁄(Ω E)).toAffine.Equation a b) (ha : a ∉ W)
    (hxa : xG E ∈ IntermediateField.adjoin k {a}) {m : k[X]} (hm : m.natDegree ≤ 1)
    {u : Ω E} {c₀ : k} (hc₀ : c₀ ≠ 0)
    (hu : u ^ 2 = (b + (algebraMap k (Ω E) E.a₁ * a + algebraMap k (Ω E) E.a₃) / 2 -
      aeval a m) / algebraMap k (Ω E) c₀) :
    ∃ τ : Gal E, W.comap (τ.symm : Ω E →+* Ω E) = W ∧ τ a = a ∧ τ b = b ∧ τ u = -u := by
  have hk' : ∀ c : k, algebraMap k (Ω E) c ∈ W := hk
  set y' := b + (algebraMap k (Ω E) E.a₁ * a + algebraMap k (Ω E) E.a₃) / 2 with hy'def
  let cp : k[X] := C 1 * X ^ 3 + C (E.a₂ + E.a₁ ^ 2 / 4) * X ^ 2 +
    C (E.a₄ + E.a₁ * E.a₃ / 2) * X + C (E.a₆ + E.a₃ ^ 2 / 4)
  have hcp : cp.natDegree = 3 := natDegree_cubic one_ne_zero
  have hcp0 : cp ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hcp
    exact absurd hcp (by norm_num)
  have hy : y' ^ 2 = aeval a cp := by
    rw [Affine.equation_iff, baseChange_a₁, baseChange_a₂, baseChange_a₃, baseChange_a₄,
      baseChange_a₆] at hab
    simp only [cp, hy'def, map_add, map_mul, aeval_C, aeval_X, map_pow, map_one, one_mul,
      map_div₀, map_ofNat]
    linear_combination hab
  have hv1 := one_lt_valuation_of_notMem ha
  have hvy : W.valuation y' ^ 2 = W.valuation a ^ 3 := by
    rw [← map_pow, hy, val_aeval hk' ha hcp0, hcp]
  have hay : W.valuation a < W.valuation y' := by
    by_contra hcon
    have h1 : W.valuation y' ^ 2 ≤ W.valuation a ^ 2 := pow_le_pow_left₀ zero_le (not_lt.1 hcon) 2
    rw [hvy] at h1
    exact absurd h1 (not_le.2 (pow_lt_pow_right₀ hv1 (by norm_num)))
  have hvm : W.valuation (aeval a m) < W.valuation y' := by
    refine lt_of_le_of_lt ?_ hay
    calc W.valuation (aeval a m) ≤ W.valuation a ^ m.natDegree := valuation_aeval_le hk' ha m
      _ ≤ W.valuation a ^ 1 := pow_le_pow_right₀ hv1.le hm
      _ = W.valuation a := pow_one _
  have hvf : W.valuation (y' - aeval a m) = W.valuation y' := by
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left _ (by rwa [Valuation.map_neg])]
  have hvu : W.valuation u ^ 4 = W.valuation a ^ 3 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, ← map_pow, hu, map_div₀,
      valuation_algebraMap_base hk' hc₀, div_one, hvf, hvy]
  -- the fields `k(a) ⊆ k(a, y')`
  have hle : baseField E ≤ IntermediateField.adjoin k {a} := by
    rw [hbase E]
    exact IntermediateField.adjoin_simple_le_iff.2 hxa
  let K0a : IntermediateField (baseField E) (Ω E) := IntermediateField.extendScalars hle
  have hK0a : ∀ z, z ∈ K0a ↔ z ∈ IntermediateField.adjoin k {a} := fun z =>
    IntermediateField.mem_extendScalars hle
  haveI : IsGalois K0a (Ω E) := IsGalois.tower_top_of_isGalois (baseField E) K0a (Ω E)
  have haK : a ∈ K0a := (hK0a a).2 (IntermediateField.mem_adjoin_simple_self k a)
  have hkK : ∀ c : k, algebraMap k (Ω E) c ∈ K0a := fun c =>
    (hK0a _).2 ((IntermediateField.adjoin k {a}).algebraMap_mem c)
  have hcpK : aeval a cp ∈ K0a := (hK0a _).2 (aeval_mem_adjoin_simple _ _)
  have hmK : aeval a m ∈ K0a := (hK0a _).2 (aeval_mem_adjoin_simple _ _)
  let d0 : K0a := ⟨aeval a cp, hcpK⟩
  have hy0 : y' ^ 2 = algebraMap K0a (Ω E) d0 := hy
  let K1 : IntermediateField K0a (Ω E) := IntermediateField.adjoin K0a {y'}
  haveI : IsGalois K1 (Ω E) := IsGalois.tower_top_of_isGalois K0a K1 (Ω E)
  have hyK1 : y' ∈ K1 := IntermediateField.mem_adjoin_simple_self K0a y'
  have hK0K1 : ∀ z ∈ K0a, z ∈ K1 := fun z hz => K1.algebraMap_mem ⟨z, hz⟩
  have hrep : ∀ z ∈ K1, ∃ p q : Ω E, p ∈ IntermediateField.adjoin k {a} ∧
      q ∈ IntermediateField.adjoin k {a} ∧ z = p + q * y' := by
    intro z hz
    have hyint : IsIntegral K0a y' := Algebra.IsIntegral.isIntegral y'
    have hz' : z ∈ Algebra.adjoin K0a {y'} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hyint.isAlgebraic]
      exact hz
    obtain ⟨g, h, hgh⟩ := exists_add_mul_of_mem_adjoin hy0 hz'
    exact ⟨g, h, (hK0a _).1 g.2, (hK0a _).1 h.2, hgh⟩
  have hint : ∀ z ∈ K1, z ≠ 0 → IntVal W a z := fun z hz hz0 => by
    obtain ⟨p, q, hp, hq, rfl⟩ := hrep z hz
    exact intVal_add_mul hk' ha hcp hy hp hq hz0
  have hfK : (y' - aeval a m) / algebraMap k (Ω E) c₀ ∈ K1 :=
    div_mem (sub_mem hyK1 (hK0K1 _ hmK)) (hK0K1 _ (hkK c₀))
  let d : K1 := ⟨_, hfK⟩
  have hud : u ^ 2 = algebraMap K1 (Ω E) d := hu
  have hu0 : W.valuation u ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hvu
    exact pow_ne_zero 3 (valuation_ne_zero_of_notMem ha) hvu.symm
  have hun : u ∉ (algebraMap K1 (Ω E)).range := by
    rintro ⟨z, hz⟩
    have hz0 : (z : Ω E) ≠ 0 := fun h => hu0 (by
      rw [← hz]
      change W.valuation (z : Ω E) = 0
      rw [h, map_zero])
    have := hint z z.2 hz0
    change IntVal W a (algebraMap K1 (Ω E) z) at this
    rw [hz] at this
    exact not_intVal ha hvu this
  have hstab : ∀ g h : K1, algebraMap K1 (Ω E) g + algebraMap K1 (Ω E) h * u ∈ W ↔
      algebraMap K1 (Ω E) g - algebraMap K1 (Ω E) h * u ∈ W := by
    intro g h
    suffices e : W.valuation ((g : Ω E) + (h : Ω E) * u) =
        W.valuation ((g : Ω E) - (h : Ω E) * u) by
      change (g : Ω E) + (h : Ω E) * u ∈ W ↔ (g : Ω E) - (h : Ω E) * u ∈ W
      rw [← W.valuation_le_one_iff, e, W.valuation_le_one_iff]
    by_cases hh0 : (h : Ω E) = 0
    · rw [hh0, zero_mul, add_zero, sub_zero]
    by_cases hg0 : (g : Ω E) = 0
    · rw [hg0, zero_add, zero_sub, Valuation.map_neg]
    have hne := val_ne_mul_root ha (hint _ g.2 hg0) (hint _ h.2 hh0) hh0 hvu
    have hne' : W.valuation (g : Ω E) ≠ W.valuation (-((h : Ω E) * u)) := by
      rwa [Valuation.map_neg]
    rw [sub_eq_add_neg, Valuation.map_add_of_distinct_val _ hne,
      Valuation.map_add_of_distinct_val _ hne', Valuation.map_neg]
  obtain ⟨ρ, hρW, hρu⟩ := exists_fix_neg_gen W hud hun hstab
  let τ : Gal E := (ρ.restrictScalars K0a).restrictScalars (baseField E)
  have hfix : ∀ z ∈ K1, τ z = z := fun z hz => ρ.commutes ⟨z, hz⟩
  have hbK : b ∈ K1 := by
    have e : b = y' - (algebraMap k (Ω E) E.a₁ * a + algebraMap k (Ω E) E.a₃) /
        algebraMap k (Ω E) 2 := by
      rw [map_ofNat, hy'def]
      ring
    rw [e]
    exact sub_mem hyK1 (div_mem (add_mem (mul_mem (hK0K1 _ (hkK _)) (hK0K1 _ haK))
      (hK0K1 _ (hkK _))) (hK0K1 _ (hkK _)))
  exact ⟨τ, hρW, hfix a (hK0K1 a haK), hfix b hbK, hρu⟩

end Ramified

/-! ### The main theorem -/

section Main

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]
  {ℓ : ℕ} [OddPrime ℓ]

open CurvesJacobian.Cusp Iut.Reconstruction.HemiCusp in
/-- **Distinct cusps are separated by decomposition groups** ([AbsTopI] Lemma 4.5, Galois model):
for places `W₁, W₂` over `T₁, T₂ ∈ E(k)[ℓ]` (`|E(k)[ℓ]| = ℓ²`), if the decomposition group of
`W₁` in `π₁(X) = Aut(Ω / F_X) ⧸ ⟨⟨inertia⟩⟩` is contained in that of `W₂`, then `T₁ = T₂`.
Kummer argument: with the secant `L` through `ℓ`-torsion points `S₁, S₂` avoiding `±(T₂ − T₁)`,
`u = √((b − L(a))/c₀)` for `Q_ℓ − T₁ = (a, b)` is ramified at `W₁`, unramified at the
non-cuspidal places (so fixed by the inertia kernel) and `≡ ±1` at `W₂`. -/
theorem eq_of_galDecomp_le (hcard : Nat.card (Tor E ℓ) = ℓ ^ 2) (M : AddSubgroup E.toAffine.Point)
    (pm : Bool) {T₁ T₂ : E.toAffine.Point} (hT₁ : ℓ • T₁ = 0) (hT₂ : ℓ • T₂ = 0)
    {W₁ W₂ : ValuationSubring (Ω E)} (h₁ : IsCuspPlace E ℓ T₁ W₁) (h₂ : IsCuspPlace E ℓ T₂ W₂)
    (hle : galDecomp (Hgp E ℓ M pm) (Sgen E ℓ M) (isClosed_Hgp E ℓ M pm) W₁ ≤
      galDecomp (Hgp E ℓ M pm) (Sgen E ℓ M) (isClosed_Hgp E ℓ M pm) W₂) : T₁ = T₂ := by
  by_contra hne
  have hℓ : ℓ ≠ 0 := ell_ne_zero
  have hk₁ : ∀ c : k, algebraMap k (Ω E) c ∈ W₁ := h₁.1
  have hk₂ : ∀ c : k, algebraMap k (Ω E) c ∈ W₂ := h₂.1
  obtain ⟨R, hRdef⟩ : ∃ R, R = T₂ - T₁ := ⟨_, rfl⟩
  have hR : ℓ • R = 0 := by rw [hRdef, nsmul_sub, hT₁, hT₂, sub_zero]
  have hR0 : R ≠ 0 := by rw [hRdef]; exact sub_ne_zero.2 (Ne.symm hne)
  -- the secant
  obtain ⟨S₁, hS₁T, hS₁Z⟩ := exists_not_mem_zmultiples hcard hR
  have hℓS₁ : ℓ • S₁ = 0 := mem_tor.1 hS₁T
  obtain ⟨n1, n2, d12, d12', r1, r1', r2, r2', r3, r3'⟩ := secant_aux hS₁Z hℓS₁ hR0
  have hℓS₂ : ℓ • (S₁ + R) = 0 := by rw [nsmul_add, hℓS₁, hR, add_zero]
  rcases hS1 : S₁ with _ | ⟨x₁, y₁, hs₁⟩
  · exact n1 hS1
  rcases hS2 : S₁ + R with _ | ⟨x₂, y₂, hs₂⟩
  · exact n2 hS2
  rcases hRp : R with _ | ⟨xR, yR, hsR⟩
  · exact hR0 hRp
  rw [hS2] at d12 d12' r2 r2' r3 r3' hℓS₂
  rw [hS1] at d12 d12' r1 r1' hℓS₁ r3 r3'
  rw [hRp] at r1 r1' r2 r2' r3 r3' hR
  have hx₁₂ : x₁ ≠ x₂ := x_ne_of_ne hs₁ hs₂ d12 d12'
  set sl := E.toAffine.slope x₁ x₂ y₁ y₂
  set x₃ := E.toAffine.addX x₁ x₂ sl
  have hsum : (Affine.Point.some x₁ y₁ hs₁ : E.toAffine.Point) + .some x₂ y₂ hs₂ =
      .some x₃ _ (Affine.nonsingular_add hs₁ hs₂ (fun h => hx₁₂ h.1)) :=
    Affine.Point.add_some (fun h => hx₁₂ h.1)
  rw [hsum] at r3 r3'
  rw [Affine.Point.neg_some] at r3
  have hℓS₃ : ℓ • (Affine.Point.some x₃ _ (Affine.nonsingular_add hs₁ hs₂ (fun h => hx₁₂ h.1)) :
      E.toAffine.Point) = 0 := by
    rw [← hsum, nsmul_add, hℓS₁, hℓS₂, add_zero]
  have hxR₁ : xR ≠ x₁ := x_ne_of_ne hsR hs₁ r1 r1'
  have hxR₂ : xR ≠ x₂ := x_ne_of_ne hsR hs₂ r2 r2'
  have hxR₃ : xR ≠ x₃ := x_ne_of_ne hsR _ r3' (by rwa [Affine.Point.neg_some])
  have hΨ : ∀ z ∈ ({x₁, x₂, x₃} : Set k),
      aeval (algebraMap k (Ω E) z) ((shortModel E).ΨSq ℓ) = 0 ∧
        aeval (algebraMap k (Ω E) z) ((shortModel E).Φ ℓ) ≠ 0 := by
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact ΨSq_torsion hℓ hs₁ hℓS₁
    · exact ΨSq_torsion hℓ hs₂ hℓS₂
    · exact ΨSq_torsion hℓ _ hℓS₃
  -- the scalar `c₀ = L(R)`
  set c₀ := yR - (sl * (xR - x₁) + y₁) with hc₀def
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    have hid := line_identity E.toAffine hs₁.1 hs₂.1 hx₁₂ hsR.1
    rw [← hc₀def, h0, zero_mul] at hid
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.2 hxR₁) (sub_ne_zero.2 hxR₂))
      (sub_ne_zero.2 hxR₃) hid.symm
  -- the point `Q_ℓ − T₁ = (a, b)`
  rcases hP : Qpt E ℓ - base E T₁ with _ | ⟨a, b, hab⟩
  · have := h₁.2
    rw [hP] at this
    exact this
  have ha₁ : a ∉ W₁ := by
    have := h₁.2
    rw [hP] at this
    exact this
  have hPG : ℓ • (Affine.Point.some a b hab : Pt E) = genericPoint E := by
    rw [← hP]
    exact nsmul_Qpt_sub_base E hℓ hT₁
  set f := b - (algebraMap k (Ω E) sl * (a - algebraMap k (Ω E) x₁) + algebraMap k (Ω E) y₁)
    with hfdef
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (f / algebraMap k (Ω E) c₀) two_pos
  -- `x(G) ∈ k(a)`
  have hxa : xG E ∈ IntermediateField.adjoin k {a} := by
    obtain ⟨hne0, hX⟩ := xG_mul_ΨSq E hab hPG
    have e : xG E = aeval a ((shortModel E).Φ ℓ) / aeval a ((shortModel E).ΨSq ℓ) := by
      rw [← hX, mul_div_cancel_right₀ _ hne0]
    rw [e]
    exact div_mem (aeval_mem_adjoin_simple _ _) (aeval_mem_adjoin_simple _ _)
  -- the ramified automorphism at `W₁`
  let m : k[X] := C (E.a₁ / 2 + sl) * X + C (E.a₃ / 2 - sl * x₁ + y₁)
  have hm : m.natDegree ≤ 1 := natDegree_linear_le
  have hfm : f = b + (algebraMap k (Ω E) E.a₁ * a + algebraMap k (Ω E) E.a₃) / 2 - aeval a m := by
    simp only [hfdef, m, map_add, map_mul, aeval_C, aeval_X, map_div₀, map_sub, map_ofNat]
    ring
  rw [hfm] at hu
  obtain ⟨τ, hτW, hτa, hτb, hτu⟩ := exists_fix_neg_root h₁.1 hab.1 ha₁ hxa hm hc₀ hu
  rw [← hfm] at hu
  -- `τ ∈ Aut(Ω / F_X)`
  have hτP : act E τ (Qpt E ℓ - base E T₁) = Qpt E ℓ - base E T₁ := by
    rw [hP]
    obtain ⟨h', e⟩ := act_some_eq (σ := τ) hab
    rw [e]
    exact some_ext hτa hτb
  have hτQ : act E τ (Qpt E ℓ) = Qpt E ℓ := by
    have e : Qpt E ℓ = (Qpt E ℓ - base E T₁) + base E T₁ := by abel
    rw [e, map_add, hτP, act_base]
  have hτH : τ ∈ Hgp E ℓ M pm := ⟨1, Or.inl rfl, by rw [hτQ, one_smul, sub_self]; exact zero_mem _⟩
  have hτD : τ ∈ decompGal (baseField E) W₁ := by
    have hinv : τ⁻¹ ∈ decompGal (baseField E) W₁ := mem_decompGal_iff_comap.2 hτW
    simpa using inv_mem hinv
  -- `δ ∈ D_{W₂}` with the same image in `π₁`
  let τh : Hgp E ℓ M pm := ⟨τ, hτH⟩
  have hmem : galProj (Hgp E ℓ M pm) (Sgen E ℓ M) (isClosed_Hgp E ℓ M pm) τh ∈
      galDecomp (Hgp E ℓ M pm) (Sgen E ℓ M) (isClosed_Hgp E ℓ M pm) W₁ :=
    ⟨τh, Subgroup.mem_subgroupOf.2 hτD, rfl⟩
  obtain ⟨δ, hδD, hδe⟩ := hle hmem
  have hker : (δ⁻¹ * τh : Hgp E ℓ M pm) ∈ GaloisPi1.kernel (Hgp E ℓ M pm) (Sgen E ℓ M) :=
    QuotientGroup.eq.1 hδe
  have hamb : (δ : Gal E)⁻¹ * τ ∈ GaloisPi1.ambientKernel (Hgp E ℓ M pm) (Sgen E ℓ M) :=
    Subgroup.mem_subgroupOf.1 hker
  -- the inertia kernel fixes `a`, `b`, `u`
  have hfix : GaloisPi1.ambientKernel (Hgp E ℓ M pm) (Sgen E ℓ M) ≤
      fixSub (P := baseField E) ({a, b, u} : Set (Ω E)) := by
    refine Subgroup.topologicalClosure_minimal _ ?_ (isClosed_fixSub _)
    rw [Subgroup.closure_le]
    rintro x ⟨h, hh, s, hs, rfl⟩
    rw [Sgen_eq_S0] at hs
    have hS0 := conj_mem_S0 E (compatible_divSys_of_charZero E) hh hs
    obtain ⟨hsa, hsb⟩ := fix_of_mem_S0 hℓ hab hP hS0
    obtain ⟨-, V, hkV, hxV, hsV⟩ := hS0
    have hfV := val_line_eq_one hℓ hkV hxV hab hPG hs₁.1 hs₂.1 hx₁₂ hΨ
    have hc : ∀ c : k, (h * s * h⁻¹) (algebraMap k (Ω E) c) = algebraMap k (Ω E) c :=
      fun c => (h * s * h⁻¹).commutes' ⟨_, (baseField E).algebraMap_mem c⟩
    have hsf : (h * s * h⁻¹) f = f := by
      rw [hfdef, map_sub, map_add, map_mul, map_sub, hsa, hsb, hc, hc, hc]
    have hsu := fix_root_of_inertia hkV hsV hc₀ hfV hu hsf
    rintro z (rfl | rfl | rfl)
    · exact hsa
    · exact hsb
    · exact hsu
  have hδu : (δ : Gal E) u = -u := by
    have h1 : ((δ : Gal E)⁻¹ * τ) u = u := hfix hamb u (by simp)
    change (δ : Gal E).symm (τ u) = u at h1
    rw [hτu, AlgEquiv.symm_apply_eq] at h1
    exact h1.symm
  -- the residue at `W₂`
  have hδD' : (δ : Gal E) ∈ decompGal (baseField E) W₂ := Subgroup.mem_subgroupOf.1 hδD
  have hsum2 : (Qpt E ℓ - base E T₂) + base E (.some xR yR hsR) = .some a b hab := by
    rw [← hRp, hRdef, map_sub, ← hP]
    abel
  obtain ⟨hca, hcb⟩ := residue_of_pole h₂.1 h₂.2 hsR hab hsum2
  have hle₂ : ∀ z ∈ W₂, W₂.valuation z ≤ 1 := fun z hz => (W₂.valuation_le_one_iff z).2 hz
  have ef : f - algebraMap k (Ω E) c₀ = (b - algebraMap k (Ω E) yR) -
      algebraMap k (Ω E) sl * (a - algebraMap k (Ω E) xR) := by
    simp only [hfdef, hc₀def, map_sub, map_add, map_mul]
    ring
  have hf2 : W₂.valuation (f - algebraMap k (Ω E) c₀) < 1 := by
    rw [ef]
    refine Valuation.map_sub_lt _ hcb ?_
    rw [map_mul]
    exact (mul_le_of_le_one_left' (hle₂ _ (hk₂ sl))).trans_lt hca
  have hc₀Ω : algebraMap k (Ω E) c₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap k (Ω E)).injective).2 hc₀
  have hu2 : W₂.valuation ((u - 1) * (u + 1)) < 1 := by
    have e2 : (u - 1) * (u + 1) = (f - algebraMap k (Ω E) c₀) / algebraMap k (Ω E) c₀ := by
      rw [show (u - 1) * (u + 1) = u ^ 2 - 1 by ring, hu]
      field_simp
    rw [e2, map_div₀, valuation_algebraMap_base hk₂ hc₀, div_one]
    exact hf2
  have huW : u ∈ W₂ := by
    by_contra hu'
    have h1 := one_lt_valuation_of_notMem hu'
    have e3 : u ^ 2 = (u - 1) * (u + 1) + 1 := by ring
    have h2 : W₂.valuation (u ^ 2) ≤ 1 := by
      rw [e3]
      exact Valuation.map_add_le _ hu2.le (by rw [map_one])
    rw [map_pow] at h2
    exact absurd h2 (not_le.2 (one_lt_pow₀ h1 two_ne_zero))
  have hδ1 : (δ : Gal E) 1 = 1 := map_one _
  have h2v : W₂.valuation (algebraMap k (Ω E) 2) = 1 := valuation_algebraMap_base hk₂ two_ne_zero
  rcases lt_one_of_mul3 W₂ (sub_mem huW W₂.one_mem) (add_mem huW W₂.one_mem) W₂.one_mem
      (by rwa [mul_one]) with h | h | h
  · have h' := lt_one_of_mem_decompGal hδD' h
    rw [map_sub, hδu, hδ1] at h'
    have hs := Valuation.map_add_lt _ h h'
    rw [show u - 1 + (-u - 1) = -algebraMap k (Ω E) 2 by rw [map_ofNat]; ring, Valuation.map_neg,
      h2v] at hs
    exact lt_irrefl _ hs
  · have h' := lt_one_of_mem_decompGal hδD' h
    rw [map_add, hδu, hδ1] at h'
    have hs := Valuation.map_add_lt _ h h'
    rw [show u + 1 + (-u + 1) = algebraMap k (Ω E) 2 by rw [map_ofNat]; ring, h2v] at hs
    exact lt_irrefl _ hs
  · rw [map_one] at h
    exact lt_irrefl _ h

end Main

/-! ### Cusps and conjugacy classes of cuspidal decomposition groups -/

section Orbicurve

variable {k : Type u} [Field k] [CharZero k] {X : Orbicurve k} [OddPrime X.level]

open CurvesJacobian.Cusp Iut.Reconstruction.HemiCusp in
open scoped Classical in
/-- **[AbsTopI] Lemma 4.5 (v) for the model orbicurves** (`Topics in Absolute Anabelian
Geometry I.txt` l.3331–3336: cusps correspond to conjugacy classes of cuspidal decomposition
groups): if a cuspidal decomposition group of `π₁(X)` is contained in a conjugate of
another one, the two places lie over the same cusp of `X` (`|E(k)[ℓ]| = ℓ²`, `ℓ` an odd prime). -/
theorem CuspPlace.cusp_eq_of_cuspDecomp_le (hcard : Nat.card X.torsion = X.level ^ 2)
    {c c' : CuspPlace X} (γ : pi1Of X.E X.level X.M X.pm)
    (h : cuspDecomp X c' ≤ (cuspDecomp X c).map (MulAut.conj γ).toMonoidHom) :
    c'.cusp = c.cusp := by
  have hℓ : X.level ≠ 0 := ell_ne_zero
  obtain ⟨ρ, rfl⟩ := galProj_surjective _ _ (isClosed_Hgp X.E X.level X.M X.pm) γ
  have hT : X.level • (c.T : X.E.toAffine.Point) = 0 :=
    (AddSubgroup.torsionBy.nsmul_iff (A := X.E.toAffine.Point)).1 c.T.2
  have hT' : X.level • (c'.T : X.E.toAffine.Point) = 0 :=
    (AddSubgroup.torsionBy.nsmul_iff (A := X.E.toAffine.Point)).1 c'.T.2
  obtain ⟨ε, hε, S, hS, hρQ⟩ := act_Qpt_eq X.E hℓ hcard (ρ : Gal X.E)
  have hcus := isCuspPlace_smul hε hρQ c.isCusp
  have hmem : ε • ((c.T : X.E.toAffine.Point) - S) ∈ X.torsion :=
    (AddSubgroup.torsionBy.nsmul_iff (A := X.E.toAffine.Point)).2 (by
      rw [smul_comm, nsmul_sub, hT, hS, sub_zero, zsmul_zero])
  let c'' : CuspPlace X := ⟨(placeSmul X.E ρ c.W, ⟨_, hmem⟩), hcus⟩
  have hc'' : c''.cusp = c.cusp := CuspPlace.cusp_eq_of_smul hℓ ρ.2 rfl
  have hD : cuspDecomp X c'' = (cuspDecomp X c).map
      (MulAut.conj (galProj _ _ (isClosed_Hgp X.E X.level X.M X.pm) ρ)).toMonoidHom :=
    galDecomp_smul ρ c.W
  have hTT := eq_of_galDecomp_le hcard X.M X.pm hT' (by
      rw [smul_comm, nsmul_sub, hT, hS, sub_zero, zsmul_zero]) c'.isCusp hcus (h.trans hD.symm.le)
  have hT'' : c'.T = c''.T := Subtype.ext hTT
  rw [← hc'']
  unfold CuspPlace.cusp
  rw [hT'']

open CurvesJacobian.Cusp Iut.Reconstruction.HemiCusp in
open scoped Classical in
/-- **Cusps of `X` = conjugacy classes of cuspidal decomposition groups**: two cuspidal places lie
over the same cusp iff their decomposition groups in `π₁(X)` are conjugate
(`exists_smul_of_cusp_eq`, `conj_of_smul`, `cusp_eq_of_cuspDecomp_le`). -/
theorem CuspPlace.cusp_eq_iff_conj (hcard : Nat.card X.torsion = X.level ^ 2)
    {c c' : CuspPlace X} : c'.cusp = c.cusp ↔ ∃ γ : pi1Of X.E X.level X.M X.pm,
      cuspDecomp X c' = (cuspDecomp X c).map (MulAut.conj γ).toMonoidHom := by
  have hℓ : X.level ≠ 0 := ell_ne_zero
  constructor
  · intro h
    obtain ⟨σ, hσ, hW⟩ := CuspPlace.exists_smul_of_cusp_eq hℓ hcard h
    exact ⟨_, (CuspPlace.conj_of_smul hℓ ⟨σ, hσ⟩ hW).2.1⟩
  · rintro ⟨γ, hγ⟩
    exact CuspPlace.cusp_eq_of_cuspDecomp_le hcard γ hγ.le

end Orbicurve

end Iut.Multiradial.Theater
