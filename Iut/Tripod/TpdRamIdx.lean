/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.TpdGalois
import Iut.Concrete.Existence

/-!
# `ℚ(λ)/ℚ(j)` has ramification index `≤ 2` at the places where `j` is non-integral

(IUT IV, Proposition 1.8; [GenEll].) For the curve `E_λ/F_λ` of a point of the tripod, the
tower `F_mod = ℚ(j) ⊆ F_tpd = ℚ(λ)` is Galois (`Iut.Tripod.isGalois_tpd`), and at a place
`u₀` of `ℚ(j)` at which `j` is non-integral — in particular at the places of `V_mod^bad`,
over which `E` has multiplicative reduction — every place `u` of `ℚ(λ)` over `u₀` has
ramification index `e(u/u₀) ≤ 2` (`Iut.Tripod.relRamIdx_tpd_le_two`).

The argument is the inertia-group form of the Tate uniformization of the `2`-torsion.
The six roots `λ, 1 − λ, 1/λ, 1/(1 − λ), λ/(λ − 1), (λ − 1)/λ` of the sextic
`256(X² − X + 1)³ − j·X²(X − 1)²` are permuted by `Gal(ℚ(λ)/ℚ(j))`. As `v_u(j) > 1`, one of
the three anharmonic representatives `λ' ∈ {λ, 1/λ, 1 − λ}` satisfies `v_u(λ') < 1`, and
among the six roots exactly `λ'` and `λ'/(λ' − 1)` have valuation `< 1`. An element `σ` of
the inertia group at `u` satisfies `v_u(σλ' − λ') < 1`, so `σλ' ∈ {λ', λ'/(λ' − 1)}`; since
`λ'` generates `ℚ(λ)` over `ℚ(j)`, `σ ↦ σλ'` is injective on the inertia group, whose
order is `e(u/u₀)` (Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn`). Hence
`e(u/u₀) ≤ 2`.

The general part (`Iut.relRamIdx_le_two_of_generator`) bounds `e(u/u₀)` in any Galois
extension of number fields by the number of conjugates of a `u`-integral generator that are
congruent to it modulo `u`.
-/

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise WithZero

/-! ### The inertia group and the valuation -/

section Inertia

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

omit [NumberField k] in
/-- An element `σ` of the inertia group of the prime `𝔓_w` satisfies `v_w(σx − x) < 1` for
every `w`-integral `x ∈ K`. -/
lemma valuation_sub_lt_one_of_mem_inertia {w : FinitePlace K} {σ : K ≃ₐ[k] K}
    (hσ : σ ∈ w.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K)) {x : K}
    (hx : w.maximalIdeal.valuation K x ≤ 1) :
    w.maximalIdeal.valuation K (σ x - x) < 1 := by
  set P := w.maximalIdeal with hP
  obtain ⟨n, d, hnd⟩ := exists_primeCompl_mul_eq_of_integer P x hx
  have hn : σ • n - n ∈ P.asIdeal := hσ n
  have hd : σ • (d : 𝓞 K) - d ∈ P.asIdeal := hσ d
  have hdP : (d : 𝓞 K) ∉ P.asIdeal := d.2
  have hd'P : σ • (d : 𝓞 K) ∉ P.asIdeal := fun h =>
    hdP (by simpa using P.asIdeal.sub_mem h hd)
  have hD : (d : 𝓞 K) * σ • (d : 𝓞 K) ∉ P.asIdeal := fun h =>
    (P.isPrime.mem_or_mem h).elim hdP hd'P
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 := fun h =>
    hdP (by rw [(IsFractionRing.to_map_eq_zero_iff (K := K)).mp h]; exact zero_mem _)
  have hcoe : ∀ a : 𝓞 K, algebraMap (𝓞 K) K (σ • a) = σ (algebraMap (𝓞 K) K a) :=
    fun a => rfl
  have hd'0 : algebraMap (𝓞 K) K (σ • (d : 𝓞 K)) ≠ 0 := by
    rw [hcoe]
    exact (map_ne_zero σ).mpr hd0
  have hx' : x = algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K d := by
    rw [eq_div_iff hd0]
    exact hnd
  have hσx : σ x = algebraMap (𝓞 K) K (σ • n) / algebraMap (𝓞 K) K (σ • (d : 𝓞 K)) := by
    rw [hx', map_div₀, hcoe, hcoe]
  have hkey : σ x - x =
      algebraMap (𝓞 K) K ((σ • n - n) * d - n * (σ • (d : 𝓞 K) - d)) /
        algebraMap (𝓞 K) K (d * σ • (d : 𝓞 K)) := by
    rw [hσx, hx']
    simp only [map_sub, map_mul]
    field_simp
    ring
  rw [hkey, map_div₀, (valuation_eq_one_iff_notMem (K := K) P).mpr hD, div_one]
  exact (valuation_lt_one_iff_mem P _).mpr
    (P.asIdeal.sub_mem (P.asIdeal.mul_mem_right _ hn) (P.asIdeal.mul_mem_left _ hd))

variable [IsGalois k K]

/-- `Gal(K/k)` is the Galois group of `𝓞_K/𝓞_k`. -/
noncomputable local instance instGalRingOfIntegersGaloisGroup' :
    IsGaloisGroup (K ≃ₐ[k] K) (𝓞 k) (𝓞 K) :=
  IsGaloisGroup.of_isFractionRing (K ≃ₐ[k] K) (𝓞 k) (𝓞 K) k K

/-- **The ramification index is the order of the inertia group** in a Galois extension. -/
lemma relRamIdx_eq_card_inertia {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) :
    relRamIdx w v = Nat.card (w.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K)) := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  haveI : Finite (𝓞 k ⧸ v.maximalIdeal.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ v.maximalIdeal.ne_bot
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[k] K) v.maximalIdeal.asIdeal
    w.maximalIdeal.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal
      (K ≃ₐ[k] K),
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal
      v.maximalIdeal.ne_bot]

/-- **The inertia bound**: if `a` generates `K` over `k`, is `w`-integral, and every conjugate
`σa` with `v_w(σa − a) < 1` is one of `b, c`, then `e(w/v) ≤ 2`. -/
lemma relRamIdx_le_two_of_generator {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) {a : K} (ha : IntermediateField.adjoin k {a} = ⊤)
    (hav : w.maximalIdeal.valuation K a ≤ 1) {b c : K}
    (hT : ∀ σ : K ≃ₐ[k] K, w.maximalIdeal.valuation K (σ a - a) < 1 → σ a = b ∨ σ a = c) :
    relRamIdx w v ≤ 2 := by
  classical
  have hadj : Algebra.adjoin k {a} = ⊤ := by
    have hint : IsAlgebraic k a := (IsIntegral.of_finite k a).isAlgebraic
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint, ha,
      IntermediateField.top_toSubalgebra]
  rw [relRamIdx_eq_card_inertia hwv]
  let f : w.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K) → ({b, c} : Finset K) := fun σ =>
    ⟨σ.1 a, by
      rcases hT σ.1 (valuation_sub_lt_one_of_mem_inertia σ.2 hav) with h | h <;> simp [h]⟩
  have hf : Function.Injective f := by
    intro σ τ h
    have h' : σ.1 a = τ.1 a := congrArg Subtype.val h
    have hst : (σ.1 : K →ₐ[k] K) = τ.1 :=
      AlgHom.ext_of_adjoin_eq_top hadj fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        exact h'
    exact Subtype.ext (AlgEquiv.ext fun y => AlgHom.congr_fun hst y)
  calc Nat.card (w.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K))
      ≤ Nat.card ({b, c} : Finset K) := Nat.card_le_card_of_injective f hf
    _ = ({b, c} : Finset K).card := Nat.card_eq_finsetCard _
    _ ≤ 2 := Finset.card_le_two

end Inertia

/-! ### The sextic of the Legendre parameter and its roots -/

section Sextic

variable {L : Type*} [Field L]

/-- `j(λ) = 256(λ² − λ + 1)³/(λ²(λ − 1)²)`, the `j`-invariant of the Legendre curve `E_λ`. -/
noncomputable def jOfLambda (l : L) : L := 256 * (l ^ 2 - l + 1) ^ 3 / (l ^ 2 * (l - 1) ^ 2)

/-- `S_j(s) = 256(s² − s + 1)³ − j·s²(s − 1)²`, the sextic of `λ` over `j` evaluated at `s`. -/
def sexticEval (j s : L) : L := 256 * (s ^ 2 - s + 1) ^ 3 - j * (s ^ 2 * (s - 1) ^ 2)

variable {l : L} (hl0 : l ≠ 0) (hl1 : l - 1 ≠ 0)

lemma one_sub_ne_zero_of_sub_one_ne_zero (hl1 : l - 1 ≠ 0) : 1 - l ≠ 0 := fun h =>
  hl1 (by rw [← neg_sub, h, neg_zero])

include hl0 hl1

/-- `j(1/λ) = j(λ)`. -/
lemma jOfLambda_inv : jOfLambda l⁻¹ = jOfLambda l := by
  have h1' := one_sub_ne_zero_of_sub_one_ne_zero hl1
  have e1 : l⁻¹ ^ 2 - l⁻¹ + 1 = (l ^ 2 - l + 1) / l ^ 2 := by
    field_simp
    ring
  have e2 : l⁻¹ - 1 = (1 - l) / l := by
    field_simp
  unfold jOfLambda
  rw [e1, e2, div_pow, div_pow, inv_pow, div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  ring

omit hl0 hl1 in
/-- `j(1 − λ) = j(λ)`. -/
lemma jOfLambda_one_sub : jOfLambda (1 - l) = jOfLambda l := by
  have e1 : (1 - l) ^ 2 - (1 - l) + 1 = l ^ 2 - l + 1 := by ring
  have e2 : (1 - l - 1) = -l := by ring
  have e3 : (1 - l) ^ 2 = (l - 1) ^ 2 := by ring
  unfold jOfLambda
  rw [e1, e2, neg_sq, e3]
  ring

/-- **The factorization of the sextic** `S_{j(λ)}`:
`S_{j(λ)}(s) = 256(s − λ)(s − (1 − λ))(s − 1/λ)(s − 1/(1 − λ))(s − λ/(λ − 1))(s − (λ − 1)/λ)`. -/
lemma sexticEval_jOfLambda (s : L) :
    sexticEval (jOfLambda l) s =
      256 * ((s - l) * (s - (1 - l)) * (s - l⁻¹) * (s - (1 - l)⁻¹) * (s - l / (l - 1)) *
        (s - (l - 1) / l)) := by
  have h1' := one_sub_ne_zero_of_sub_one_ne_zero hl1
  unfold sexticEval jOfLambda
  field_simp
  ring

/-- `S_{j(λ)}(λ) = 0`. -/
lemma sexticEval_jOfLambda_self : sexticEval (jOfLambda l) l = 0 := by
  rw [sexticEval_jOfLambda hl0 hl1, sub_self]
  ring

/-- The roots of `S_{j(λ)}` are the six anharmonic values of `λ` (in characteristic `0`). -/
lemma eq_of_sexticEval_jOfLambda_eq_zero [CharZero L] {s : L}
    (hs : sexticEval (jOfLambda l) s = 0) :
    s = l ∨ s = 1 - l ∨ s = l⁻¹ ∨ s = (1 - l)⁻¹ ∨ s = l / (l - 1) ∨ s = (l - 1) / l := by
  rw [sexticEval_jOfLambda hl0 hl1] at hs
  simp only [mul_eq_zero, sub_eq_zero] at hs
  rcases hs with h | ((((h | h) | h) | h) | h) | h
  · exact absurd h (by norm_num)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

omit hl1

variable [CharZero L] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)

/-- **The roots of valuation `< 1`**: if `v(λ) < 1`, the roots `s` of `S_{j(λ)}` with `v(s) < 1`
are `λ` and `λ/(λ − 1)`. -/
lemma eq_or_eq_of_valuation_lt_one (hl : v l < 1) {s : L} (hs : sexticEval (jOfLambda l) s = 0)
    (hsv : v s < 1) : s = l ∨ s = l / (l - 1) := by
  have hl1 : l - 1 ≠ 0 := fun h => by
    rw [sub_eq_zero.mp h, map_one] at hl
    exact lt_irrefl _ hl
  have hvl : 0 < v l := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hl0)
  have h1l : v (1 - l) = 1 := by
    rw [Valuation.map_sub_eq_of_lt_left v (by rwa [map_one]), map_one]
  have hl1' : v (l - 1) = 1 := by rw [Valuation.map_sub_swap, h1l]
  rcases eq_of_sexticEval_jOfLambda_eq_zero hl0 hl1 hs with h | h | h | h | h | h
  · exact Or.inl h
  · rw [h, h1l] at hsv
    exact absurd hsv (lt_irrefl _)
  · rw [h, map_inv₀] at hsv
    exact absurd ((one_lt_inv₀ hvl).mpr hl) (not_lt.mpr hsv.le)
  · rw [h, map_inv₀, h1l, inv_one] at hsv
    exact absurd hsv (lt_irrefl _)
  · exact Or.inr h
  · rw [h, map_div₀, hl1', one_div] at hsv
    exact absurd ((one_lt_inv₀ hvl).mpr hl) (not_lt.mpr hsv.le)

/-- A root `s` of `S_{j(λ)}` congruent to `λ` (`v(s − λ) < 1`) is `λ` or `λ/(λ − 1)`, when
`v(λ) < 1`. -/
lemma eq_or_eq_of_valuation_sub_lt_one (hl : v l < 1) {s : L}
    (hs : sexticEval (jOfLambda l) s = 0) (hsub : v (s - l) < 1) : s = l ∨ s = l / (l - 1) :=
  eq_or_eq_of_valuation_lt_one hl0 v hl hs (by
    have := Valuation.map_add_lt v hsub hl
    rwa [sub_add_cancel] at this)

omit hl0 [CharZero L] in
/-- **`λ` meets `{0, 1, ∞}` where `j` has a pole**: if `v(256) ≤ 1` and `v(j(λ)) > 1`, then one
of `λ, 1/λ, 1 − λ` has valuation `< 1`. -/
lemma valuation_lt_one_of_one_lt_jOfLambda (h256 : v 256 ≤ 1) (hj : 1 < v (jOfLambda l)) :
    v l < 1 ∨ v l⁻¹ < 1 ∨ v (1 - l) < 1 := by
  rcases lt_trichotomy (v l) 1 with h | h | h
  · exact Or.inl h
  · right; right
    by_contra hc
    have hvl1 : v (1 - l) = 1 :=
      le_antisymm (Valuation.map_sub_le v (by rw [map_one]) h.le) (not_lt.mp hc)
    have hl1' : v (l - 1) = 1 := by rw [Valuation.map_sub_swap, hvl1]
    have hc3 : v (l ^ 2 - l + 1) ≤ 1 := by
      refine Valuation.map_add_le v (Valuation.map_sub_le v ?_ h.le) (by rw [map_one])
      rw [map_pow, h, one_pow]
    have hle : v (jOfLambda l) ≤ 1 := by
      unfold jOfLambda
      rw [map_div₀, map_mul, map_mul, map_pow, map_pow, map_pow, h, hl1', one_pow, mul_one,
        div_one]
      exact mul_le_one' h256 (pow_le_one' hc3 3)
    exact absurd hj (not_lt.mpr hle)
  · right; left
    rw [map_inv₀]
    exact (inv_lt_one₀ (zero_lt_one.trans h)).mpr h

end Sextic

/-! ### The tripod: `F_tpd = ℚ(λ)` over `F_mod = ℚ(j)` -/

namespace Tripod

open Polynomial

open scoped IntermediateField

variable (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)

/-- `λ` as an element of `F_tpd`. -/
noncomputable def lamTpd : tpdC x h3 h5 :=
  ⟨genC x h3 h5, (mem_tpdC_iff x h3 h5 _).mpr (IntermediateField.mem_adjoin_simple_self ℚ _)⟩

@[simp] lemma coe_lamTpd : (lamTpd x h3 h5 : (curveOf x h3 h5).F) = genC x h3 h5 := rfl

/-- `j` as an element of `F_tpd`. -/
noncomputable def jTpd : tpdC x h3 h5 :=
  algebraMap (modC x h3 h5) (tpdC x h3 h5) (jCpt x h3 h5)

lemma coe_jTpd : (jTpd x h3 h5 : (curveOf x h3 h5).F) = (curveOf x h3 h5).E.j := by
  rw [jTpd, algebraMap_fieldOfModuli_tripodal_apply, coe_jC]

lemma lamTpd_ne_zero : lamTpd x h3 h5 ≠ 0 := fun h =>
  genC_ne_zero x h3 h5 (congrArg Subtype.val h)

lemma lamTpd_sub_one_ne_zero : lamTpd x h3 h5 - 1 ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  change genC x h3 h5 - 1 = 0 at this
  exact genC_ne_one x h3 h5 (sub_eq_zero.mp this)

/-- `j = j(λ)` in `F_tpd`. -/
lemma jTpd_eq : jTpd x h3 h5 = jOfLambda (lamTpd x h3 h5) := by
  apply Subtype.ext
  rw [coe_jTpd, j_eq]
  simp only [jOfLambda]
  push_cast [coe_lamTpd]
  rfl

/-- **`F_tpd = F_mod(λ)`**: `λ` generates `F_tpd` over `F_mod`. -/
lemma adjoin_lamTpd_eq_top :
    IntermediateField.adjoin (modC x h3 h5) {lamTpd x h3 h5} = ⊤ := by
  rw [eq_top_iff]
  intro t _
  have ht : (t : (curveOf x h3 h5).F) ∈ (modC x h3 h5)⟮genC x h3 h5⟯ :=
    (mem_adjoin_modC_iff x h3 h5 _).mpr ((mem_tpdC_iff x h3 h5 _).mp t.2)
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff (modC x h3 h5) _).mp ht
  rw [IntermediateField.mem_adjoin_simple_iff]
  refine ⟨r, s, ?_⟩
  have key : ∀ p : (modC x h3 h5)[X],
      algebraMap (tpdC x h3 h5) (curveOf x h3 h5).F (aeval (lamTpd x h3 h5) p) =
        aeval (genC x h3 h5) p := fun p => by
    rw [← aeval_algebraMap_apply]
    rfl
  apply Subtype.ext
  rw [hrs, ← IntermediateField.algebraMap_apply, map_div₀, key, key]

/-- `S_j(λ) = 0` in `F_tpd`. -/
lemma sexticEval_jTpd_lamTpd : sexticEval (jTpd x h3 h5) (lamTpd x h3 h5) = 0 := by
  rw [jTpd_eq]
  exact sexticEval_jOfLambda_self (lamTpd_ne_zero x h3 h5) (lamTpd_sub_one_ne_zero x h3 h5)

/-- `Gal(F_tpd/F_mod)` permutes the roots of the sextic: `S_j(σs) = σ(S_j(s))`. -/
lemma sexticEval_jTpd_algEquiv (σ : tpdC x h3 h5 ≃ₐ[modC x h3 h5] tpdC x h3 h5)
    (s : tpdC x h3 h5) :
    sexticEval (jTpd x h3 h5) (σ s) = σ (sexticEval (jTpd x h3 h5) s) := by
  simp only [sexticEval, jTpd, map_sub, map_mul, map_pow, map_add, map_one, map_ofNat,
    AlgEquiv.commutes]

/-- **`e(u/u₀) ≤ 2` for `ℚ(λ)/ℚ(j)` at a place `u₀` where `j` is non-integral**
(`v_{u₀}(j) > 1`). -/
theorem relRamIdx_tpd_le_two_of_one_lt_valuation (u : FinitePlace (tpdC x h3 h5))
    (u₀ : FinitePlace (modC x h3 h5)) (huu₀ : FinitePlace.LiesOver u u₀)
    (hj : 1 < u₀.maximalIdeal.valuation (modC x h3 h5) (jCpt x h3 h5)) :
    relRamIdx u u₀ ≤ 2 := by
  haveI : IsGalois (modC x h3 h5) (tpdC x h3 h5) := isGalois_tpd x h3 h5
  set v := u.maximalIdeal.valuation (tpdC x h3 h5) with hv
  set l := lamTpd x h3 h5 with hl
  have hl0 := lamTpd_ne_zero x h3 h5
  have hl1 := lamTpd_sub_one_ne_zero x h3 h5
  have hjT : 1 < v (jTpd x h3 h5) := by
    rw [jTpd, hv, valuation_algebraMap_eq_pow huu₀]
    exact one_lt_pow₀ hj (ramificationIdx'_ne_zero huu₀)
  have h256 : v 256 ≤ 1 := by
    have : v (algebraMap (𝓞 (tpdC x h3 h5)) (tpdC x h3 h5) 256) ≤ 1 :=
      valuation_le_one u.maximalIdeal _
    rwa [map_ofNat] at this
  rw [jTpd_eq] at hjT
  have hgen := adjoin_lamTpd_eq_top x h3 h5
  have main : ∀ a : tpdC x h3 h5, a ≠ 0 → IntermediateField.adjoin (modC x h3 h5) {a} = ⊤ →
      jTpd x h3 h5 = jOfLambda a → v a < 1 → relRamIdx u u₀ ≤ 2 := by
    intro a ha0 hadj hja hva
    refine relRamIdx_le_two_of_generator huu₀ hadj hva.le (b := a) (c := a / (a - 1)) ?_
    intro σ hσ
    have ha1 : a - 1 ≠ 0 := fun h => by
      rw [sub_eq_zero.mp h, map_one] at hva
      exact lt_irrefl _ hva
    have hroot : sexticEval (jOfLambda a) (σ a) = 0 := by
      rw [← hja, sexticEval_jTpd_algEquiv, hja, sexticEval_jOfLambda_self ha0 ha1, map_zero]
    exact eq_or_eq_of_valuation_sub_lt_one ha0 v hva hroot hσ
  rcases valuation_lt_one_of_one_lt_jOfLambda v h256 hjT with h | h | h
  · exact main l hl0 hgen (jTpd_eq x h3 h5) h
  · refine main l⁻¹ (inv_ne_zero hl0) ?_ ?_ h
    · rw [eq_top_iff, ← hgen, IntermediateField.adjoin_simple_le_iff]
      have := inv_mem (IntermediateField.mem_adjoin_simple_self (modC x h3 h5) l⁻¹)
      rwa [inv_inv] at this
    · rw [jTpd_eq, jOfLambda_inv hl0 hl1]
  · refine main (1 - l) (one_sub_ne_zero_of_sub_one_ne_zero hl1) ?_ ?_ h
    · rw [eq_top_iff, ← hgen, IntermediateField.adjoin_simple_le_iff]
      have := sub_mem (one_mem _) (IntermediateField.mem_adjoin_simple_self (modC x h3 h5) (1 - l))
      rwa [sub_sub_cancel] at this
    · rw [jTpd_eq, jOfLambda_one_sub]

/-- **`j` is non-integral at the places of `V_mod^bad`**: `v_{u₀}(j) > 1` for
`u₀ ∈ V_mod^bad(ℓ)` (multiplicative reduction at the places of `F` above `u₀`). -/
lemma one_lt_valuation_jCpt_of_mem_VBadOf {ℓ : ℕ} {u₀ : FinitePlace (modC x h3 h5)}
    (hu₀ : u₀ ∈ (curveOf x h3 h5).VBadOf ℓ) :
    1 < u₀.maximalIdeal.valuation (modC x h3 h5) (jCpt x h3 h5) := by
  obtain ⟨-, -, ⟨w, hwu₀⟩, hmult⟩ := hu₀
  have h := one_lt_valuation_j_of_mult (curveOf x h3 h5).E w (hmult w hwu₀)
  have h' := valuation_algebraMap_eq_pow hwu₀ (jCpt x h3 h5)
  rw [IntermediateField.algebraMap_apply, coe_jC] at h'
  rw [h'] at h
  by_contra hc
  exact absurd h (not_lt.mpr (pow_le_one₀ zero_le (not_lt.mp hc)))

/-- **IUT IV, Proposition 1.8 for `F_tpd/F_mod`**: `e(u/u₀) ≤ 2` for every place `u` of
`ℚ(λ)` over a place `u₀ ∈ V_mod^bad(ℓ)` of `ℚ(j)`. -/
theorem relRamIdx_tpd_le_two (ℓ : ℕ) (u : FinitePlace (tpdC x h3 h5))
    (u₀ : FinitePlace (modC x h3 h5)) (hu₀ : u₀ ∈ (curveOf x h3 h5).VBadOf ℓ)
    (huu₀ : FinitePlace.LiesOver u u₀) : relRamIdx u u₀ ≤ 2 :=
  relRamIdx_tpd_le_two_of_one_lt_valuation x h3 h5 u u₀ huu₀
    (one_lt_valuation_jCpt_of_mem_VBadOf x h3 h5 hu₀)

end Tripod

end Iut
