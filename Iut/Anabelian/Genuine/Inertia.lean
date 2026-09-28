/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Genuine.Pi1
import Iut.Tower.ReductionKernel

/-!
# Inertia fixes the division points of the generic point (characteristic `0`)

Let `E / k` be an elliptic curve over a field of characteristic `0`, `K ⊇ k` a field, `W` a
valuation subring of `K` containing `k`, and `σ` a `k`-automorphism of `K` in the inertia group
of `W` (`v_W(σ a − a) < 1` for `a ∈ W`). If `G ∈ E(K)` is an affine point with `W`-integral
`x`-coordinate fixed by `σ`, then `σ` fixes every point `Q` with `n Q = G`, `n ≥ 1`
(`Iut.Anabelian.Genuine.inertia_fixes_of_nsmul`).

Proof (for a model `y² = x³ + a₂x² + a₄x + a₆`; the general case by completing the square):
`x(Q)` is a root of the monic polynomial `Φₙ − x(G) ΨSqₙ` with `W`-integral coefficients, so
`Q` is `W`-integral; `σ Q ≡ Q` modulo the maximal ideal, so `σ Q − Q` is `0` or lies in the
kernel of reduction (`Iut.ReductionKernel.sub_eq_zero_or_one_lt`, at the good model: `Δ ∈ k^×`);
but `σ Q − Q` is `n`-torsion, and the `x`-coordinates of `n`-torsion points are roots of
`ΨSqₙ ∈ k[X]` (leading coefficient `n² ∈ k^×`), hence `W`-integral: so `σ Q = Q`.

Geometrically: the isogeny `[n] : E → E` is étale over `E ∖ {0}`, so the extensions
`k(Q_n) / k(G)` are unramified at all places centered on `E ∖ {0}`; this is the input for the
open-embedding property of the maps of fundamental groups induced by covers.
-/

namespace Iut.Anabelian.Genuine

universe u v

open WeierstrassCurve Polynomial

open scoped Classical

noncomputable section

section Integral

variable {K : Type v} [Field K] (W : ValuationSubring K)

/-- A root of a monic polynomial with coefficients in an integrally closed subring `R` lies in
`R`. -/
lemma mem_of_monic_root' (R : Subring K) (hR : ∀ x : K, IsIntegral R x → x ∈ R) {p : K[X]}
    (hp : p.Monic) (hc : ∀ i, p.coeff i ∈ R) {x : K} (hx : p.eval x = 0) : x ∈ R := by
  have hsub : (↑p.coeffs : Set K) ⊆ R := by
    intro c hc'
    obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc'
    exact hc i
  let q := p.toSubring R hsub
  have hq : q.Monic := (Polynomial.monic_toSubring p R hsub).mpr hp
  refine hR x ⟨q, hq, ?_⟩
  rw [eval₂_eq_eval_map]
  have : q.map (algebraMap R K) = p := Polynomial.map_toSubring p R hsub
  rw [this, hx]

/-- A root of a monic polynomial with coefficients in an integrally closed subalgebra `R` lies in
`R`. -/
lemma mem_of_monic_root_alg {k : Type*} [Field k] [Algebra k K] (R : Subalgebra k K)
    (hR : ∀ x : K, IsIntegral R x → x ∈ R) {p : K[X]} (hp : p.Monic) (hc : ∀ i, p.coeff i ∈ R)
    {x : K} (hx : p.eval x = 0) : x ∈ R := by
  have hl : p ∈ Polynomial.lifts (algebraMap R K) :=
    (Polynomial.lifts_iff_coeff_lifts p).mpr (fun i => ⟨⟨_, hc i⟩, rfl⟩)
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  exact hR x ⟨q, hqm, by rw [eval₂_eq_eval_map, hq, hx]⟩

lemma isIntegrallyClosed_valuationSubring (x : K) (hx : IsIntegral W.toSubring x) :
    x ∈ W.toSubring := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (show IsIntegral W x from hx)
  rw [← hy]
  exact y.2

/-- A root of a monic polynomial with `W`-integral coefficients is `W`-integral. -/
lemma mem_of_monic_root {p : K[X]} (hp : p.Monic) (hc : ∀ i, p.coeff i ∈ W) {x : K}
    (hx : p.eval x = 0) : x ∈ W :=
  mem_of_monic_root' W.toSubring (isIntegrallyClosed_valuationSubring W) hp hc hx

lemma valuation_eq_one_of_mem_of_inv_mem {c : K} (hc : c ∈ W) (hc' : c⁻¹ ∈ W) (h0 : c ≠ 0) :
    W.valuation c = 1 := by
  have h1 := (W.valuation_le_one_iff c).mpr hc
  have h2 := (W.valuation_le_one_iff c⁻¹).mpr hc'
  rw [map_inv₀] at h2
  exact le_antisymm h1 ((inv_le_one₀ ((Valuation.pos_iff _).mpr h0)).mp h2)

end Integral

section ShortModel

variable {k : Type u} [Field k] [CharZero k] {K : Type v} [Field K] [Algebra k K]
  (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (ha₁ : E₀.a₁ = 0) (ha₃ : E₀.a₃ = 0)
  (W : ValuationSubring K) (hk : ∀ c : k, algebraMap k K c ∈ W)
  (R : Subalgebra k K) (hR : ∀ x : K, IsIntegral R x → x ∈ R) (hRW : R.toSubring ≤ W.toSubring)

omit [CharZero k] in
include hk in
lemma valuation_algebraMap_eq_one {c : k} (hc : c ≠ 0) : W.valuation (algebraMap k K c) = 1 :=
  valuation_eq_one_of_mem_of_inv_mem W (hk c) (by rw [← map_inv₀]; exact hk _)
    ((map_ne_zero_iff _ (algebraMap k K).injective).mpr hc)

omit [CharZero k] in
include hk in
lemma coeff_map_mem (p : k[X]) (i : ℕ) : (p.map (algebraMap k K)).coeff i ∈ W := by
  rw [coeff_map]; exact hk _

omit [E₀.IsElliptic] in
include ha₁ ha₃ hR in
/-- The torsion points have `R`-integral `x`-coordinates. -/
lemma torsion_x_mem (n : ℕ) (hn : 0 < n) {x y : K} (h : (E₀⁄K).toAffine.Nonsingular x y)
    (hnt : n • (Affine.Point.some x y h : (E₀⁄K).toAffine.Point) = 0) : x ∈ R := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have ha₁' : (E₀⁄K).toAffine.a₁ = 0 := by simp [baseChange, ha₁]
  have ha₃' : (E₀⁄K).toAffine.a₃ = 0 := by simp [baseChange, ha₃]
  have hΨ := (Torsion.smul_eq_zero_iff_ΨSq ha₁' ha₃' h n).mp hnt
  have hmap : (E₀⁄K).ΨSq n = (E₀.ΨSq n).map (algebraMap k K) := map_ΨSq _ _ _
  have hn' : ((n : ℤ) : k) ≠ 0 := by exact_mod_cast hn.ne'
  let c : k := (E₀.ΨSq n).leadingCoeff
  have hc : c ≠ 0 := by
    rw [leadingCoeff_ne_zero]; intro h0
    have := E₀.leadingCoeff_ΨSq hn'
    rw [h0, leadingCoeff_zero] at this
    exact pow_ne_zero 2 hn' this.symm
  let p : K[X] := (C c⁻¹ * E₀.ΨSq n).map (algebraMap k K)
  refine mem_of_monic_root_alg R hR (p := p) ?_
    (fun i => by rw [coeff_map]; exact R.algebraMap_mem _) ?_
  · exact (monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hc)).map _
  · simp only [p, Polynomial.map_mul, map_C, eval_mul, eval_C, ← hmap, hΨ, mul_zero]

include ha₁ ha₃ hk hR hRW in
/-- **Inertia fixes the division points of an integral point** (short model). Here `R ⊆ W` is an
integrally closed subring containing `k` (e.g. `W` itself, or the coordinate ring of a curve whose
local ring at a closed point is `W`), and `σ` acts trivially on `R` modulo the maximal ideal of
`W`. -/
theorem inertia_fixes_of_nsmul_short' (σ : K →ₐ[k] K)
    (hσ : ∀ a ∈ R, W.valuation (σ a - a) < 1) (n : ℕ) (hn : 0 < n)
    {xg yg : K} (hG : (E₀⁄K).toAffine.Nonsingular xg yg) (hxg : xg ∈ R)
    (hσG : Affine.Point.map (W' := E₀) (S := k) σ (Affine.Point.some xg yg hG) =
      Affine.Point.some xg yg hG)
    (Q : (E₀⁄K).toAffine.Point) (hQ : n • Q = Affine.Point.some xg yg hG) :
    Affine.Point.map (W' := E₀) (S := k) σ Q = Q := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have ha₁' : (E₀⁄K).toAffine.a₁ = 0 := by simp [baseChange, ha₁]
  have ha₃' : (E₀⁄K).toAffine.a₃ = 0 := by simp [baseChange, ha₃]
  let v := W.valuation
  have hint : ∀ z, v z ≤ 1 ↔ z ∈ W := W.valuation_le_one_iff
  have ha₂ : v (E₀⁄K).toAffine.a₂ ≤ 1 := (hint _).mpr (hk _)
  have ha₄ : v (E₀⁄K).toAffine.a₄ ≤ 1 := (hint _).mpr (hk _)
  have ha₆ : v (E₀⁄K).toAffine.a₆ ≤ 1 := (hint _).mpr (hk _)
  have h2 : v 2 = 1 := by
    have := valuation_algebraMap_eq_one W hk (c := (2 : k)) two_ne_zero
    rwa [map_ofNat] at this
  have hΔ : v (E₀⁄K).toAffine.Δ = 1 := by
    have : (E₀⁄K).Δ = algebraMap k K E₀.Δ := by simp [baseChange]
    rw [show (E₀⁄K).toAffine.Δ = (E₀⁄K).Δ from rfl, this]
    exact valuation_algebraMap_eq_one W hk E₀.isUnit_Δ.ne_zero
  -- `Q` is affine with integral coordinates
  rcases Q with _ | ⟨x₁, y₁, h₁⟩
  · change n • (0 : (E₀⁄K).toAffine.Point) = _ at hQ
    rw [smul_zero] at hQ; exact absurd hQ.symm (Affine.Point.some_ne_zero hG)
  have hne : ((E₀⁄K).ΨSq n).eval x₁ ≠ 0 := by
    intro h0
    have := (Torsion.smul_eq_zero_iff_ΨSq ha₁' ha₃' h₁ n).mpr h0
    rw [this] at hQ
    exact Affine.Point.some_ne_zero hG hQ.symm
  obtain ⟨X, Y, hXY, hnQ, hX⟩ := Torsion.smul_eq_of_ΨSq_ne_zero ha₁' ha₃' h₁ n hne
  have hXg : X = xg := by rw [hnQ] at hQ; exact (Affine.Point.some.inj hQ).1
  subst hXg
  have hx₁R : x₁ ∈ R := by
    have hn' : ((n : ℤ) : k) ≠ 0 := by exact_mod_cast hn.ne'
    let p : K[X] := (E₀⁄K).Φ n - C X * (E₀⁄K).ΨSq n
    have hΦ : (E₀⁄K).Φ n = (E₀.Φ n).map (algebraMap k K) := map_Φ _ _ _
    have hΨ : (E₀⁄K).ΨSq n = (E₀.ΨSq n).map (algebraMap k K) := map_ΨSq _ _ _
    refine mem_of_monic_root_alg R hR (p := p) ?_ ?_ ?_
    · have hmon : ((E₀⁄K).Φ n).Monic := (E₀⁄K).leadingCoeff_Φ n
      refine hmon.sub_of_left ?_
      refine degree_lt_degree ?_
      rw [(E₀⁄K).natDegree_Φ]
      refine (natDegree_C_mul_le _ _).trans_lt ?_
      have := (E₀⁄K).natDegree_ΨSq_le n
      have h1 : 1 ≤ (n : ℤ).natAbs ^ 2 := Nat.one_le_pow _ _ (by simpa using hn)
      omega
    · intro i
      simp only [p, coeff_sub, coeff_C_mul, hΦ, hΨ, coeff_map]
      exact sub_mem (R.algebraMap_mem _) (mul_mem hxg (R.algebraMap_mem _))
    · simp only [p, eval_sub, eval_mul, eval_C]
      rw [hX]; ring
  have hy₁R : y₁ ∈ R := by
    have heq := (Iut.Torsion.equation_iff₀ ha₁' ha₃' x₁ y₁).mp h₁.1
    refine mem_of_monic_root_alg R hR
      (p := Polynomial.X ^ 2 - C (x₁ ^ 3 + (E₀⁄K).toAffine.a₂ * x₁ ^ 2 +
        (E₀⁄K).toAffine.a₄ * x₁ + (E₀⁄K).toAffine.a₆)) ?_ ?_ ?_
    · exact monic_X_pow_sub_C _ two_ne_zero
    · intro i
      rw [coeff_sub, coeff_C, coeff_X_pow]
      have hcoef : x₁ ^ 3 + (E₀⁄K).toAffine.a₂ * x₁ ^ 2 + (E₀⁄K).toAffine.a₄ * x₁ +
          (E₀⁄K).toAffine.a₆ ∈ R :=
        add_mem (add_mem (add_mem (pow_mem hx₁R _) (mul_mem (R.algebraMap_mem _)
          (pow_mem hx₁R _))) (mul_mem (R.algebraMap_mem _) hx₁R)) (R.algebraMap_mem _)
      refine sub_mem ?_ ?_
      · split_ifs
        · exact one_mem _
        · exact zero_mem _
      · split_ifs
        · exact hcoef
        · exact zero_mem _
    · simp [heq]
  have hx₁ : x₁ ∈ W := hRW hx₁R
  have hy₁ : y₁ ∈ W := hRW hy₁R
  have hcx : v (σ x₁ - x₁) < 1 := hσ x₁ hx₁R
  have hcy : v (σ y₁ - y₁) < 1 := hσ y₁ hy₁R
  have hmem_of_lt : ∀ z, v z < 1 → z ∈ W := fun z hz => (hint z).mp hz.le
  have hσx : σ x₁ ∈ W := by
    have := add_mem (hmem_of_lt _ hcx) hx₁; simpa using this
  have hσy : σ y₁ ∈ W := by
    have := add_mem (hmem_of_lt _ hcy) hy₁; simpa using this
  set Q := Affine.Point.some x₁ y₁ h₁ with hQdef
  have h₁σ : (E₀⁄K).toAffine.Nonsingular (σ x₁) (σ y₁) :=
    (Affine.baseChange_nonsingular (W := E₀) (f := σ) σ.toRingHom.injective x₁ y₁).mpr h₁
  have hσQ : Affine.Point.map (W' := E₀) (S := k) σ Q =
      Affine.Point.some (σ x₁) (σ y₁) h₁σ := rfl
  rw [hσQ]
  have hns := ReductionKernel.nonsingular_reduction_of_Δ v ha₁' ha₃' ha₂ ha₄ ha₆ hΔ h2 h₁σ.1
    ((hint _).mpr hσx)
  have hsub := ReductionKernel.sub_eq_zero_or_one_lt v ha₁' ha₃' ha₂ h2 h₁σ h₁
    ((hint _).mpr hσx) ((hint _).mpr hσy) ((hint _).mpr hx₁) ((hint _).mpr hy₁) hcx hcy hns
  rcases hsub with h0 | ⟨x, y, h, hxy, hv⟩
  · exact sub_eq_zero.mp h0
  · exfalso
    have htor : n • Affine.Point.some x y h = 0 := by
      rw [← hxy, smul_sub, ← hσQ, ← map_nsmul, hQ, hσG, sub_self]
    have := torsion_x_mem E₀ ha₁ ha₃ R hR n hn h htor
    exact absurd ((hint x).mpr (hRW this)) (not_le.mpr hv)

omit hR hRW in
include ha₁ ha₃ hk in
/-- **Inertia fixes the division points of an integral point** (short model, valuation-subring
version). -/
theorem inertia_fixes_of_nsmul_short (σ : K →ₐ[k] K)
    (hσ : ∀ a ∈ W, W.valuation (σ a - a) < 1) (n : ℕ) (hn : 0 < n)
    {xg yg : K} (hG : (E₀⁄K).toAffine.Nonsingular xg yg) (hxg : xg ∈ W)
    (hσG : Affine.Point.map (W' := E₀) (S := k) σ (Affine.Point.some xg yg hG) =
      Affine.Point.some xg yg hG)
    (Q : (E₀⁄K).toAffine.Point) (hQ : n • Q = Affine.Point.some xg yg hG) :
    Affine.Point.map (W' := E₀) (S := k) σ Q = Q :=
  inertia_fixes_of_nsmul_short' E₀ ha₁ ha₃ W hk
    { W.toSubring with algebraMap_mem' := hk }
    (fun x hx => by
      obtain ⟨q, hq, hqx⟩ := hx
      let f : ({ W.toSubring with algebraMap_mem' := hk } : Subalgebra k K) →+* W :=
        { toFun := fun a => ⟨a.1, a.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
          map_zero' := rfl, map_add' := fun _ _ => rfl }
      exact isIntegrallyClosed_valuationSubring W x ⟨q.map f, hq.map f, by
        rw [eval₂_map]; exact hqx⟩)
    le_rfl σ hσ n hn hG hxg hσG Q hQ

end ShortModel

section General

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

lemma pointCongr_some {K : Type*} [Field K] {W W' : WeierstrassCurve K} (h : W = W') {x y : K}
    (hxy : W.toAffine.Nonsingular x y) (hxy' : W'.toAffine.Nonsingular x y) :
    pointCongr h (Affine.Point.some x y hxy) = Affine.Point.some x y hxy' := by
  subst h; rfl

/-- The model `y² = x³ + a₂'x² + a₄'x + a₆'` of `E` (completing the square). -/
abbrev shortModel : WeierstrassCurve k := IntegralTorsion.completeSquare E • E

/-- The change of variables to the short model, over `Ω`. -/
abbrev vcΩ : VariableChange (Ω E) := (IntegralTorsion.completeSquare E).map (algebraMap k (Ω E))

omit [CharZero k] [E.IsElliptic] in
lemma vcΩ_smul : vcΩ E • (E⁄(Ω E)) = (shortModel E)⁄(Ω E) :=
  map_variableChange E (IntegralTorsion.completeSquare E) (algebraMap k (Ω E))

/-- The points of `E` over `Ω` as points of the short model. -/
def toShort : Pt E →+ ((shortModel E)⁄(Ω E)).toAffine.Point :=
  (pointCongr (vcΩ_smul E)).toAddMonoidHom.comp (vcEquiv (vcΩ E) (E⁄(Ω E))).toAddMonoidHom

omit [CharZero k] [E.IsElliptic] in
lemma toShort_injective : Function.Injective (toShort E) :=
  (pointCongr (vcΩ_smul E)).injective.comp (vcEquiv (vcΩ E) (E⁄(Ω E))).injective

omit [CharZero k] [E.IsElliptic] in
lemma toShort_some {x y : Ω E} (h : (E⁄(Ω E)).toAffine.Nonsingular x y)
    (h' : ((shortModel E)⁄(Ω E)).toAffine.Nonsingular (vcX (vcΩ E) x) (vcY (vcΩ E) x y)) :
    toShort E (Affine.Point.some x y h) = Affine.Point.some _ _ h' := by
  change pointCongr (vcΩ_smul E) (vcPoint (vcΩ E) (E⁄(Ω E)) (Affine.Point.some x y h)) = _
  rw [vcPoint_some]
  exact pointCongr_some _ _ _

omit [E.IsElliptic] in
lemma vcX_vcΩ (x : Ω E) : vcX (vcΩ E) x = x := by
  simp [vcX, IntegralTorsion.completeSquare, VariableChange.map]

omit [CharZero k] [E.IsElliptic] in
lemma toShort_act (σ : Gal E) (P : Pt E) :
    toShort E (act E σ P) = Affine.Point.map (W' := shortModel E) (S := k)
      (σk E σ) (toShort E P) := by
  rcases P with _ | ⟨x, y, h⟩
  · change toShort E (act E σ 0) = Affine.Point.map (σk E σ) (toShort E 0)
    rw [map_zero, map_zero, map_zero]
  · have hσ : ∀ c : k, σ (algebraMap k (Ω E) c) = algebraMap k (Ω E) c := fun c =>
      σ.commutes' ⟨_, (baseField E).algebraMap_mem c⟩
    have h1 := (nonsingular_vc (vcΩ E) (E⁄(Ω E)) x y).mp h
    rw [vcΩ_smul] at h1
    rw [toShort_some E h h1]
    have h2 : (E⁄(Ω E)).toAffine.Nonsingular (σ x) (σ y) :=
      (Affine.baseChange_nonsingular (W := E) (f := σk E σ)
        (σk E σ).toRingHom.injective x y).mpr h
    have h3 := (nonsingular_vc (vcΩ E) (E⁄(Ω E)) (σ x) (σ y)).mp h2
    rw [vcΩ_smul] at h3
    change toShort E (Affine.Point.some (σ x) (σ y) h2) = _
    rw [toShort_some E h2 h3]
    refine some_ext ?_ ?_
    · simp only [vcX, VariableChange.map, map_div₀, map_sub, map_pow, σk_apply, hσ,
        Units.coe_map, MonoidHom.coe_coe]
    · simp only [vcY, VariableChange.map, map_div₀, map_sub, map_mul, map_pow, σk_apply, hσ,
        Units.coe_map, MonoidHom.coe_coe]

/-- **Inertia fixes the division points of the generic point** (characteristic `0`): an
automorphism `σ` of `Ω` over `k(x)` fixing `G` and lying in the inertia group of a valuation
subring `W ⊇ k` with `x ∈ W` fixes every `Q` with `n Q = G`. -/
theorem inertia_fixes_division (σ : Gal E) (W : ValuationSubring (Ω E))
    (hk : ∀ c : k, algebraMap k (Ω E) c ∈ W) (hx : xG E ∈ W) (hσ : σ ∈ GaloisPi1.inertia W)
    (hG : act E σ (genericPoint E) = genericPoint E) (Q : Pt E) (n : ℕ) (hn : 0 < n)
    (hQ : n • Q = genericPoint E) : act E σ Q = Q := by
  apply toShort_injective E
  rw [toShort_act]
  have hNe : NeZero (2 : k) := ⟨two_ne_zero⟩
  have hns : ((shortModel E)⁄(Ω E)).toAffine.Nonsingular (vcX (vcΩ E) (xG E))
      (vcY (vcΩ E) (xG E) (yG E)) := by
    have := (nonsingular_vc (vcΩ E) (E⁄(Ω E)) _ _).mp (nonsingular_generic E)
    rwa [vcΩ_smul] at this
  have hG' := toShort_some E (nonsingular_generic E) hns
  refine inertia_fixes_of_nsmul_short (shortModel E) (IntegralTorsion.completeSquare_a₁ E)
    (IntegralTorsion.completeSquare_a₃ E) W hk (σk E σ) hσ n hn hns ?_ ?_ _ ?_
  · rw [vcX_vcΩ]; exact hx
  · rw [← hG', ← toShort_act]
    exact congrArg (toShort E) hG
  · rw [← map_nsmul, hQ]; exact hG'

end General

section GeneralField

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]
  (K : Type v) [Field K] [Algebra k K]

/-- The change of variables to the short model, over `K`. -/
abbrev vcK : VariableChange K := (IntegralTorsion.completeSquare E).map (algebraMap k K)

omit [CharZero k] [E.IsElliptic] in
lemma vcK_smul : vcK E K • (E⁄K) = (shortModel E)⁄K :=
  map_variableChange E (IntegralTorsion.completeSquare E) (algebraMap k K)

/-- The points of `E` over `K` as points of the short model. -/
def toShortK : (E⁄K).toAffine.Point →+ ((shortModel E)⁄K).toAffine.Point :=
  (pointCongr (vcK_smul E K)).toAddMonoidHom.comp (vcEquiv (vcK E K) (E⁄K)).toAddMonoidHom

omit [CharZero k] [E.IsElliptic] in
lemma toShortK_injective : Function.Injective (toShortK E K) :=
  (pointCongr (vcK_smul E K)).injective.comp (vcEquiv (vcK E K) (E⁄K)).injective

omit [CharZero k] [E.IsElliptic] in
lemma toShortK_some {x y : K} (h : (E⁄K).toAffine.Nonsingular x y)
    (h' : ((shortModel E)⁄K).toAffine.Nonsingular (vcX (vcK E K) x) (vcY (vcK E K) x y)) :
    toShortK E K (Affine.Point.some x y h) = Affine.Point.some _ _ h' := by
  change pointCongr (vcK_smul E K) (vcPoint (vcK E K) (E⁄K) (Affine.Point.some x y h)) = _
  rw [vcPoint_some]
  exact pointCongr_some _ _ _

omit [CharZero k] [E.IsElliptic] in
lemma vcX_vcK (x : K) : vcX (vcK E K) x = x := by
  simp [vcX, IntegralTorsion.completeSquare, VariableChange.map]

omit [CharZero k] [E.IsElliptic] in
lemma toShortK_map (σ : K →ₐ[k] K) (P : (E⁄K).toAffine.Point) :
    toShortK E K (Affine.Point.map (W' := E) (S := k) σ P) =
      Affine.Point.map (W' := shortModel E) (S := k) σ (toShortK E K P) := by
  rcases P with _ | ⟨x, y, h⟩
  · change toShortK E K (Affine.Point.map σ 0) = Affine.Point.map σ (toShortK E K 0)
    rw [map_zero, map_zero, map_zero]
  · have hσ : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c => σ.commutes c
    have h1 := (nonsingular_vc (vcK E K) (E⁄K) x y).mp h
    rw [vcK_smul] at h1
    rw [toShortK_some E K h h1]
    have h2 : (E⁄K).toAffine.Nonsingular (σ x) (σ y) :=
      (Affine.baseChange_nonsingular (W := E) (f := σ) σ.toRingHom.injective x y).mpr h
    have h3 := (nonsingular_vc (vcK E K) (E⁄K) (σ x) (σ y)).mp h2
    rw [vcK_smul] at h3
    change toShortK E K (Affine.Point.some (σ x) (σ y) h2) = _
    rw [toShortK_some E K h2 h3]
    refine some_ext ?_ ?_
    · simp only [vcX, VariableChange.map, map_div₀, map_sub, map_pow, hσ,
        Units.coe_map, MonoidHom.coe_coe]
    · simp only [vcY, VariableChange.map, map_div₀, map_sub, map_mul, map_pow, hσ,
        Units.coe_map, MonoidHom.coe_coe]

/-- **Inertia fixes the division points** (general Weierstrass model, over any field `K ⊇ k`,
relative to an integrally closed subring `R ⊆ W` containing `k`). -/
theorem inertia_fixes_of_nsmul (W : ValuationSubring K) (R : Subalgebra k K)
    (hR : ∀ x : K, IsIntegral R x → x ∈ R) (hRW : R.toSubring ≤ W.toSubring) (σ : K →ₐ[k] K)
    (hσ : ∀ a ∈ R, W.valuation (σ a - a) < 1) (n : ℕ) (hn : 0 < n)
    {xg yg : K} (hG : (E⁄K).toAffine.Nonsingular xg yg) (hxg : xg ∈ R)
    (hσG : Affine.Point.map (W' := E) (S := k) σ (Affine.Point.some xg yg hG) =
      Affine.Point.some xg yg hG)
    (Q : (E⁄K).toAffine.Point) (hQ : n • Q = Affine.Point.some xg yg hG) :
    Affine.Point.map (W' := E) (S := k) σ Q = Q := by
  apply toShortK_injective E K
  rw [toShortK_map]
  have hNe : NeZero (2 : k) := ⟨two_ne_zero⟩
  have hns : ((shortModel E)⁄K).toAffine.Nonsingular (vcX (vcK E K) xg)
      (vcY (vcK E K) xg yg) := by
    have := (nonsingular_vc (vcK E K) (E⁄K) _ _).mp hG
    rwa [vcK_smul] at this
  have hG' := toShortK_some E K hG hns
  have hk : ∀ c : k, algebraMap k K c ∈ W := fun c => hRW (R.algebraMap_mem c)
  refine inertia_fixes_of_nsmul_short' (shortModel E) (IntegralTorsion.completeSquare_a₁ E)
    (IntegralTorsion.completeSquare_a₃ E) W hk R hR hRW σ hσ n hn hns ?_ ?_ _ ?_
  · rw [vcX_vcK]; exact hxg
  · rw [← hG', ← toShortK_map]
    exact congrArg (toShortK E K) hσG
  · rw [← map_nsmul, hQ]; exact hG'

end GeneralField

end

end Iut.Anabelian.Genuine
