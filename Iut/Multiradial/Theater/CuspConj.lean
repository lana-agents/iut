/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.Theater.CuspPlaces

/-!
# Places over one cusp are `Aut(Ω / F_X)`-conjugate (MR22 T5, converse direction)

For a model orbicurve `X = (E, ℓ, M, ±)` over a field `k` of characteristic `0` with `ℓ ≠ 0` and
all of `E[ℓ]` rational (`|E(k)[ℓ]| = ℓ²`), two cuspidal places `c, c'` of `Ω` lying over the same
cusp of `X` are conjugate under `Hgp = Aut(Ω / F_X)` (`CuspPlace.exists_smul_of_cusp_eq`). With
`CuspPlace.cusp_eq_of_smul` and `CuspPlace.cusp_surjective`: the cusps of `X` are the
`Hgp`-orbits of cuspidal places.

## Proof

* (V1) `val_aeval`: for a valuation subring `V ⊇ k` and `a ∉ V`, `v(p(a)) = v(a)^{deg p}`;
  hence (`mem_iff_of_mem_adjoin`) all places `V ⊇ k` with `a ∉ V` agree on `k(a)`.
* (V2) `xG_notMem_of_isCuspPlace`: at a cuspidal place, `x(G) ∉ W`
  (`x(G) ΨSq_ℓ(a) = Φ_ℓ(a)` with `a = x(Q_ℓ − T)`, `deg Φ_ℓ = ℓ²`, `deg ΨSq_ℓ = ℓ² − 1`).
* (V3) `exists_gal_placeSmul`: any two cuspidal places are `Gal(Ω / k(x))`-conjugate
  (both restrict to the place at infinity of `k(x) = baseField E`; Galois acts transitively on
  the places over it, `CurvesJacobian.Cusp.exists_algEquiv_comap_eq`).
* (V4) `act_Qpt_eq`: every `σ ∈ Gal(Ω / k(x))` has `σ(Q_ℓ) = ε Q_ℓ + S` with `ε = ±1` and
  `S ∈ E(k)[ℓ]` (`σ(G) = ±G`; all `ℓ`-torsion of `E(Ω)` is rational by counting).
* (V5) `exists_fix_neg`: for a place `W` over `T` there is `ρ` fixing `W` with
  `ρ(Q_ℓ − T) = −(Q_ℓ − T)`: with `P = Q_ℓ − T = (a, b)` and `y` the `y`-coordinate of `P` in
  the model `y² = c(x)` (`c` cubic), `y ∉ k(a)` and `W ∩ k(a, y)` is stable under `y ↦ −y`,
  since `v(g) ≠ v(h y)` for nonzero `g, h ∈ k(a)` (`v(g)²` is an even and `v(h y)²` an odd power
  of `v(a)`); so some `τ ∈ Aut(Ω / k(a))` with `τ y = −y` maps `W` to a place with the same
  restriction to `k(a, y)`, and a correction in `Aut(Ω / k(a, y))` gives `ρ`.
* If `σ(W) = W'` with `σ(Q_ℓ) = ε Q_ℓ + S` and `T' ≡ η T` mod `M` (`η` an admissible sign), then
  `σ ∈ Hgp` if `ε = η`, and `σ ρ ∈ Hgp` otherwise.
-/

noncomputable section

namespace Iut.Multiradial.Theater

open WeierstrassCurve Iut.Anabelian Iut.Anabelian.Genuine Polynomial

universe u

/-! ### Valuations of polynomial expressions in an element outside the place -/

section Val

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {V : ValuationSubring F}
  (hk : ∀ c : k, algebraMap k F c ∈ V) {a : F} (ha : a ∉ V)

lemma aeval_mem_adjoin_simple (a : F) (p : k[X]) :
    aeval a p ∈ IntermediateField.adjoin k {a} :=
  IntermediateField.algebra_adjoin_le_adjoin k {a} (Polynomial.aeval_mem_adjoin_singleton k a)

include ha in
lemma one_lt_valuation_of_notMem : 1 < V.valuation a := by
  rw [← not_le, V.valuation_le_one_iff]
  exact ha

include hk in
lemma valuation_algebraMap_base {c : k} (hc : c ≠ 0) : V.valuation (algebraMap k F c) = 1 := by
  have h0 : algebraMap k F c ≠ 0 := (map_ne_zero_iff _ (algebraMap k F).injective).2 hc
  refine le_antisymm ((V.valuation_le_one_iff _).2 (hk c)) ?_
  have h2 := (V.valuation_le_one_iff _).2 (hk c⁻¹)
  rw [map_inv₀, map_inv₀] at h2
  exact (inv_le_one₀ ((Valuation.pos_iff _).2 h0)).1 h2

include hk ha in
lemma valuation_aeval_le (p : k[X]) :
    V.valuation (aeval a p) ≤ V.valuation a ^ p.natDegree := by
  have h1 := one_lt_valuation_of_notMem ha
  rw [aeval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i hi => ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  calc V.valuation (algebraMap k F (p.coeff i)) * V.valuation a ^ i ≤ 1 * V.valuation a ^ i :=
        mul_le_mul_left ((V.valuation_le_one_iff _).2 (hk _)) _
    _ ≤ V.valuation a ^ p.natDegree := by
        rw [one_mul]
        exact pow_le_pow_right₀ h1.le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

include hk ha in
/-- **(V1)** For `a ∉ V ⊇ k` and `p ≠ 0`: `v(p(a)) = v(a)^{deg p}` (the leading term dominates). -/
lemma val_aeval {p : k[X]} (hp : p ≠ 0) :
    V.valuation (aeval a p) = V.valuation a ^ p.natDegree := by
  have h1 := one_lt_valuation_of_notMem ha
  have hlc : V.valuation (algebraMap k F p.leadingCoeff) = 1 :=
    valuation_algebraMap_base hk (leadingCoeff_ne_zero.2 hp)
  have hmon : V.valuation (aeval a (monomial p.natDegree p.leadingCoeff)) =
      V.valuation a ^ p.natDegree := by
    rw [aeval_monomial, map_mul, map_pow, hlc, one_mul]
  have hlt : V.valuation (aeval a p.eraseLead) < V.valuation a ^ p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
    · obtain ⟨c, hc⟩ := natDegree_eq_zero.1 h0
      rw [← hc, eraseLead_C, map_zero, map_zero, natDegree_C, pow_zero]
      exact zero_lt_one
    · calc _ ≤ V.valuation a ^ p.eraseLead.natDegree := valuation_aeval_le hk ha _
        _ ≤ V.valuation a ^ (p.natDegree - 1) :=
          pow_le_pow_right₀ h1.le (eraseLead_natDegree_le p)
        _ < _ := pow_lt_pow_right₀ h1 (by omega)
  conv_lhs => rw [← eraseLead_add_monomial_natDegree_leadingCoeff p]
  rw [map_add, Valuation.map_add_eq_of_lt_right _ (hmon ▸ hlt), hmon]

include hk ha in
lemma div_mem_iff_natDegree_le {p q : k[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    aeval a p / aeval a q ∈ V ↔ p.natDegree ≤ q.natDegree := by
  have h1 := one_lt_valuation_of_notMem ha
  rw [← V.valuation_le_one_iff, map_div₀, val_aeval hk ha hp, val_aeval hk ha hq,
    div_le_one₀ (pow_pos (zero_lt_one.trans h1) _), pow_le_pow_iff_right₀ h1]

include hk ha in
/-- **(V3)** All places `V ⊇ k` with `a ∉ V` agree on `k(a)` (the place at infinity). -/
lemma mem_iff_of_mem_adjoin {V' : ValuationSubring F} (hk' : ∀ c : k, algebraMap k F c ∈ V')
    (ha' : a ∉ V') {z : F} (hz : z ∈ IntermediateField.adjoin k {a}) : z ∈ V ↔ z ∈ V' := by
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k z).1 hz
  by_cases hr : aeval a r = 0
  · rw [hr, zero_div]
    exact ⟨fun _ => V'.zero_mem, fun _ => V.zero_mem⟩
  by_cases hs : aeval a s = 0
  · rw [hs, div_zero]
    exact ⟨fun _ => V'.zero_mem, fun _ => V.zero_mem⟩
  have hr' : r ≠ 0 := by
    rintro rfl
    exact hr (map_zero _)
  have hs' : s ≠ 0 := by
    rintro rfl
    exact hs (map_zero _)
  rw [div_mem_iff_natDegree_le hk ha hr' hs', div_mem_iff_natDegree_le hk' ha' hr' hs']

include hk ha in
/-- **The parity argument**: if `y² = c(a)` with `deg c = 3`, then `v(g) ≠ v(h y)` for nonzero
`g, h ∈ k(a)` (`v(g)²` is an even, `v(h y)²` an odd power of `v(a)`). -/
lemma val_ne_mul {y : F} {c : k[X]} (hc : c.natDegree = 3) (hy : y ^ 2 = aeval a c) {g h : F}
    (hg : g ∈ IntermediateField.adjoin k {a}) (hh : h ∈ IntermediateField.adjoin k {a})
    (hg0 : g ≠ 0) (hh0 : h ≠ 0) : V.valuation g ≠ V.valuation (h * y) := by
  intro heq
  have h1 := one_lt_valuation_of_notMem ha
  obtain ⟨r₁, s₁, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k g).1 hg
  obtain ⟨r₂, s₂, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k h).1 hh
  have hr₁ : aeval a r₁ ≠ 0 := fun h0 => hg0 (by rw [h0, zero_div])
  have hs₁ : aeval a s₁ ≠ 0 := fun h0 => hg0 (by rw [h0, div_zero])
  have hr₂ : aeval a r₂ ≠ 0 := fun h0 => hh0 (by rw [h0, zero_div])
  have hs₂ : aeval a s₂ ≠ 0 := fun h0 => hh0 (by rw [h0, div_zero])
  have hp : ∀ p : k[X], aeval a p ≠ 0 → p ≠ 0 := fun p hp h0 => hp (by rw [h0, map_zero])
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have key : V.valuation ((aeval a r₁ * aeval a s₂) ^ 2) =
      V.valuation ((aeval a r₂ * aeval a s₁) ^ 2 * aeval a c) := by
    rw [← hy]
    have e1 : aeval a r₁ * aeval a s₂ =
        aeval a r₁ / aeval a s₁ * (aeval a s₁ * aeval a s₂) := by
      field_simp
    have e2 : (aeval a r₂ * aeval a s₁) ^ 2 * y ^ 2 =
        (aeval a r₂ / aeval a s₂ * y * (aeval a s₁ * aeval a s₂)) ^ 2 := by
      field_simp
    rw [e1, e2, map_pow, map_pow, map_mul, heq]
    simp only [map_mul]
  rw [map_pow, map_mul, map_mul, map_pow, map_mul, val_aeval hk ha (hp _ hr₁),
    val_aeval hk ha (hp _ hs₂), val_aeval hk ha (hp _ hr₂), val_aeval hk ha (hp _ hs₁),
    val_aeval hk ha hc0, hc, ← pow_add, ← pow_add, ← pow_mul, ← pow_mul, ← pow_add] at key
  have := (pow_right_strictMono₀ h1).injective key
  omega

include hk ha in
/-- **Stability under `y ↦ −y`**: for `g, h ∈ k(a)`, `g + h y ∈ V ↔ g − h y ∈ V`. -/
lemma add_mul_mem_iff_sub {y : F} {c : k[X]} (hc : c.natDegree = 3) (hy : y ^ 2 = aeval a c)
    {g h : F} (hg : g ∈ IntermediateField.adjoin k {a}) (hh : h ∈ IntermediateField.adjoin k {a}) :
    g + h * y ∈ V ↔ g - h * y ∈ V := by
  suffices e : V.valuation (g + h * y) = V.valuation (g - h * y) by
    rw [← V.valuation_le_one_iff, e, V.valuation_le_one_iff]
  by_cases hg0 : g = 0
  · rw [hg0, zero_add, zero_sub, Valuation.map_neg]
  by_cases hh0 : h = 0
  · rw [hh0, zero_mul, add_zero, sub_zero]
  have hne := val_ne_mul hk ha hc hy hg hh hg0 hh0
  have hne' : V.valuation g ≠ V.valuation (-(h * y)) := by rwa [Valuation.map_neg]
  rw [sub_eq_add_neg, Valuation.map_add_of_distinct_val _ hne,
    Valuation.map_add_of_distinct_val _ hne', Valuation.map_neg]

include hk ha in
/-- If `y² = c(a)` with `deg c = 3` then `y ∉ k(a)`. -/
lemma notMem_adjoin_of_sq {y : F} {c : k[X]} (hc : c.natDegree = 3) (hy : y ^ 2 = aeval a c) :
    y ∉ IntermediateField.adjoin k {a} := by
  intro hyk
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hy0 : y ≠ 0 := by
    rintro rfl
    have := val_aeval hk ha hc0
    rw [← hy, zero_pow two_ne_zero, map_zero] at this
    exact (pow_pos (zero_lt_one.trans (one_lt_valuation_of_notMem ha)) _).ne' this.symm
  exact val_ne_mul hk ha hc hy hyk (IntermediateField.adjoin k {a}).one_mem hy0 one_ne_zero
    (by rw [one_mul])

omit [Algebra k F] in
/-- The elements of `K[y]` with `y² ∈ K` are `g + h y`. -/
lemma exists_add_mul_of_mem_adjoin {K : Type*} [Field K] [Algebra K F] {y : F} {d : K}
    (hy : y ^ 2 = algebraMap K F d) {z : F} (hz : z ∈ Algebra.adjoin K {y}) :
    ∃ g h : K, z = algebraMap K F g + algebraMap K F h * y := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨0, 1, by simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨g, h, rfl⟩ := hx
    obtain ⟨g', h', rfl⟩ := hz
    exact ⟨g + g', h + h', by simp only [map_add]; ring⟩
  | mul x z _ _ hx hz =>
    obtain ⟨g, h, rfl⟩ := hx
    obtain ⟨g', h', rfl⟩ := hz
    refine ⟨g * g' + h * h' * d, g * h' + h * g', ?_⟩
    simp only [map_add, map_mul]
    linear_combination (algebraMap K F h * algebraMap K F h') * hy

end Val

/-! ### Fixing a place and negating a square root -/

section Aux

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {B : IntermediateField k Ω}
  [IsGalois B Ω]

/-- **(V5), field-theoretic part**: let `Ω / B` be Galois, `W ⊇ k` a place of `Ω`, `a ∉ W` with
`B ⊆ k(a)`, and `y² = c(a)` with `deg c = 3`. Then some `ρ ∈ Aut(Ω / B)` fixes `W` and `a` and
maps `y ↦ −y`. -/
theorem exists_fix_neg_aux {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    {a y : Ω} (ha : a ∉ W) {c : k[X]} (hc : c.natDegree = 3) (hy : y ^ 2 = aeval a c)
    (hle : B ≤ IntermediateField.adjoin k {a}) :
    ∃ ρ : Ω ≃ₐ[B] Ω, W.comap (ρ.symm : Ω →+* Ω) = W ∧ ρ a = a ∧ ρ y = -y := by
  let K0 : IntermediateField (B) Ω := IntermediateField.extendScalars hle
  haveI : IsGalois K0 Ω := IsGalois.tower_top_of_isGalois (B) K0 Ω
  have hK0 : ∀ z : Ω, z ∈ K0 ↔ z ∈ IntermediateField.adjoin k {a} := fun z =>
    IntermediateField.mem_extendScalars hle
  have haK : a ∈ K0 := (hK0 a).2 (IntermediateField.mem_adjoin_simple_self k a)
  have hyK : y ∉ K0 := fun h => notMem_adjoin_of_sq hk ha hc hy ((hK0 y).1 h)
  have hcK : aeval a c ∈ K0 := (hK0 _).2 (aeval_mem_adjoin_simple _ _)
  obtain ⟨d, hd⟩ : ∃ d : K0, (d : Ω) = aeval a c := ⟨⟨_, hcK⟩, rfl⟩
  have hy' : y ^ 2 = algebraMap K0 Ω d := by
    rw [IntermediateField.algebraMap_apply, hd]
    exact hy
  -- `τ ∈ Aut(Ω / k(a))` with `τ y = −y`
  obtain ⟨τ, hτ⟩ : ∃ τ : Ω ≃ₐ[K0] Ω, τ y = -y := by
    let q : K0[X] := X ^ 2 - C d
    have hqm : q.Monic := monic_X_pow_sub_C d two_ne_zero
    have hqd : q.natDegree = 2 := natDegree_X_pow_sub_C
    have hq : Irreducible q := by
      refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hqd]; decide) fun z hz => ?_
      have hz' : z ^ 2 = d := by
        have := hz.eq_zero
        simp only [q, eval_sub, eval_pow, eval_X, eval_C] at this
        exact sub_eq_zero.1 this
      have hz2 : (z : Ω) ^ 2 = y ^ 2 := by
        rw [hy']
        have := congrArg (algebraMap K0 Ω) hz'
        rw [map_pow] at this
        exact this
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hz2 with e | e
      · exact hyK (e ▸ z.2)
      · exact hyK (by rw [← neg_neg y, ← e]; exact neg_mem z.2)
    have hroot : ∀ w : Ω, w ^ 2 = y ^ 2 → aeval w q = 0 := fun w hw => by
      simp only [q, map_sub, map_pow, aeval_X, aeval_C, hw, hy', sub_self]
    have e1 := minpoly.eq_of_irreducible_of_monic hq (hroot y rfl) hqm
    have e2 := minpoly.eq_of_irreducible_of_monic hq (hroot (-y) (neg_sq y)) hqm
    obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K0) (E := Ω)).1 (e2.symm.trans e1)
    exact ⟨τ, hτ⟩
  have hτs : τ.symm y = -y := by
    rw [AlgEquiv.symm_apply_eq, map_neg, hτ, neg_neg]
  let ρ0 : Ω ≃ₐ[B] Ω := τ.restrictScalars B
  -- `L = k(a, y)`
  let L : IntermediateField K0 Ω := IntermediateField.adjoin K0 {y}
  haveI : IsGalois L Ω := IsGalois.tower_top_of_isGalois K0 L Ω
  have hyint : IsIntegral K0 y := Algebra.IsIntegral.isIntegral y
  have hyL : y ∈ L := IntermediateField.mem_adjoin_simple_self K0 y
  have haL : a ∈ L := L.algebraMap_mem ⟨a, haK⟩
  -- `W ∩ L` is `τ`-stable
  have hcomap : (W.comap (ρ0.symm : Ω →+* Ω)).comap (algebraMap L Ω) =
      W.comap (algebraMap L Ω) := by
    ext z
    have hz : (z : Ω) ∈ Algebra.adjoin K0 {y} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hyint.isAlgebraic]
      exact z.2
    obtain ⟨g, h, hgh⟩ := exists_add_mul_of_mem_adjoin hy' hz
    change τ.symm (z : Ω) ∈ W ↔ (z : Ω) ∈ W
    rw [hgh, map_add, map_mul, τ.symm.commutes, τ.symm.commutes, hτs, mul_neg,
      ← sub_eq_add_neg]
    exact (add_mul_mem_iff_sub hk ha hc hy ((hK0 _).1 g.2) ((hK0 _).1 h.2)).symm
  obtain ⟨κ, hκ⟩ :=
    CurvesJacobian.Cusp.exists_algEquiv_comap_eq (W.comap (ρ0.symm : Ω →+* Ω)) W hcomap
  let κ' : Ω ≃ₐ[B] Ω := (κ.restrictScalars K0).restrictScalars (B)
  have hκa : κ a = a := κ.commutes (⟨a, haL⟩ : L)
  have hκy : κ y = y := κ.commutes (⟨y, hyL⟩ : L)
  have hτa : τ a = a := τ.commutes (⟨a, haK⟩ : K0)
  refine ⟨κ' * ρ0, ?_, ?_, ?_⟩
  · ext z
    change ρ0.symm (κ'.symm z) ∈ W ↔ z ∈ W
    exact (SetLike.ext_iff.1 hκ z).symm
  · change κ (τ a) = a
    rw [hτa, hκa]
  · change κ (τ y) = -y
    rw [hτ, map_neg, hκy]

end Aux

/-! ### Cuspidal places and the generic point -/

section Generic

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

open scoped Classical in
/-- `x(G) ΨSq_ℓ(a) = Φ_ℓ(a)` for `ℓ (a, b) = G` (short model, same `x`-coordinates). -/
theorem xG_mul_ΨSq {ℓ : ℕ} {a b : Ω E} (h : (E⁄(Ω E)).toAffine.Nonsingular a b)
    (hP : ℓ • (Affine.Point.some a b h : Pt E) = Genuine.genericPoint E) :
    aeval a ((shortModel E).ΨSq ℓ) ≠ 0 ∧
      xG E * aeval a ((shortModel E).ΨSq ℓ) = aeval a ((shortModel E).Φ ℓ) := by
  have ha₁ : ((shortModel E)⁄(Ω E)).toAffine.a₁ = 0 := by
    simp [WeierstrassCurve.baseChange, IntegralTorsion.completeSquare_a₁]
  have ha₃ : ((shortModel E)⁄(Ω E)).toAffine.a₃ = 0 := by
    simp [WeierstrassCurve.baseChange, IntegralTorsion.completeSquare_a₃]
  have h1 := (nonsingular_vc (vcΩ E) (E⁄(Ω E)) a b).mp h
  rw [vcΩ_smul] at h1
  obtain ⟨h', hs⟩ := exists_some_eq (vcX_vcΩ E a) h1
  rw [← toShort_some E h h1] at hs
  have hG1 := (nonsingular_vc (vcΩ E) (E⁄(Ω E)) (xG E) (yG E)).mp (nonsingular_generic E)
  rw [vcΩ_smul] at hG1
  obtain ⟨hG', hsG⟩ := exists_some_eq (vcX_vcΩ E (xG E)) hG1
  rw [← toShort_some E (nonsingular_generic E) hG1] at hsG
  have hG : toShort E (Genuine.genericPoint E) ≠ 0 := by
    rw [Genuine.genericPoint, hsG]
    exact Affine.Point.some_ne_zero _
  have hne : (((shortModel E)⁄(Ω E)).toAffine.ΨSq ℓ).eval a ≠ 0 := by
    intro h0
    apply hG
    rw [← hP, map_nsmul, hs]
    exact (Iut.Torsion.smul_eq_zero_iff_ΨSq ha₁ ha₃ h' ℓ).2 h0
  obtain ⟨X, Y, hXY, hn, hX⟩ := Iut.Torsion.smul_eq_of_ΨSq_ne_zero ha₁ ha₃ h' ℓ hne
  have hXG : X = xG E := by
    have e : toShort E (Genuine.genericPoint E) = Affine.Point.some X Y hXY := by
      rw [← hP, map_nsmul, hs, hn]
    rw [Genuine.genericPoint, hsG, Affine.Point.some.injEq] at e
    exact e.1.symm
  have e1 : (((shortModel E)⁄(Ω E)).toAffine.ΨSq ℓ).eval a =
      aeval a ((shortModel E).ΨSq ℓ) := by
    rw [show ((shortModel E)⁄(Ω E)).toAffine.ΨSq ℓ = ((shortModel E).ΨSq ℓ).map
      (algebraMap k (Ω E)) from map_ΨSq _ _ _, eval_map_algebraMap]
  have e2 : (((shortModel E)⁄(Ω E)).toAffine.Φ ℓ).eval a =
      aeval a ((shortModel E).Φ ℓ) := by
    rw [show ((shortModel E)⁄(Ω E)).toAffine.Φ ℓ = ((shortModel E).Φ ℓ).map
      (algebraMap k (Ω E)) from map_Φ _ _ _, eval_map_algebraMap]
  refine ⟨e1 ▸ hne, ?_⟩
  rw [← e1, ← e2, ← hXG]
  exact hX

open scoped Classical in
/-- **(V2)** If `ℓ (a, b) = G` and `a ∉ W ⊇ k`, then `x(G) ∉ W`. -/
theorem xG_notMem {ℓ : ℕ} (hℓ : ℓ ≠ 0) {a b : Ω E} (h : (E⁄(Ω E)).toAffine.Nonsingular a b)
    (hP : ℓ • (Affine.Point.some a b h : Pt E) = Genuine.genericPoint E)
    {W : ValuationSubring (Ω E)} (hk : ContainsBase E W) (ha : a ∉ W) : xG E ∉ W := by
  replace hk : ∀ c : k, algebraMap k (Ω E) c ∈ W := hk
  obtain ⟨hne, hX⟩ := xG_mul_ΨSq E h hP
  have hΨ : (shortModel E).ΨSq ℓ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hne
    exact hne rfl
  have hl2 : 0 < ℓ ^ 2 := by positivity
  have hdΦ : ((shortModel E).Φ ℓ).natDegree = ℓ ^ 2 := by
    rw [natDegree_Φ]
    simp
  have hΦ : (shortModel E).Φ ℓ ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdΦ
    omega
  have hdΨ : ((shortModel E).ΨSq ℓ).natDegree = ℓ ^ 2 - 1 := by
    rw [natDegree_ΨSq]
    · simp
    · exact_mod_cast hℓ
  have h1 := one_lt_valuation_of_notMem ha
  have key := congrArg W.valuation hX
  rw [map_mul, val_aeval hk ha hΨ, val_aeval hk ha hΦ, hdΦ, hdΨ] at key
  have e : W.valuation a ^ (ℓ ^ 2) = W.valuation a ^ (ℓ ^ 2 - 1) * W.valuation a := by
    rw [← pow_succ]
    congr 1
    omega
  rw [e, mul_comm (W.valuation (xG E))] at key
  have hx := mul_left_cancel₀ (pow_ne_zero _ (zero_lt_one.trans h1).ne') key
  rw [← W.valuation_le_one_iff, hx]
  exact not_le.2 h1

open scoped Classical in
lemma nsmul_Qpt_sub_base {ℓ : ℕ} (hℓ : ℓ ≠ 0) {T : E.toAffine.Point} (hT : ℓ • T = 0) :
    ℓ • (Qpt E ℓ - base E T) = Genuine.genericPoint E := by
  rw [nsmul_sub, ← map_nsmul, hT, map_zero, sub_zero, GenuineBaseChange.nsmul_Qpt E hℓ]

open scoped Classical in
/-- **(V2)** At a cuspidal place, `x(G) ∉ W`. -/
theorem xG_notMem_of_isCuspPlace {ℓ : ℕ} (hℓ : ℓ ≠ 0) {T : E.toAffine.Point} (hT : ℓ • T = 0)
    {W : ValuationSubring (Ω E)} (h : IsCuspPlace E ℓ T W) : xG E ∉ W := by
  have hP := nsmul_Qpt_sub_base E hℓ hT
  have hpole := h.2
  rcases hQ : Qpt E ℓ - base E T with _ | ⟨a, b, hab⟩
  · rw [hQ] at hpole
    exact absurd hpole id
  rw [hQ] at hP hpole
  exact xG_notMem E hℓ hab hP h.1 hpole

open scoped Classical in
/-- **(V3) Any two cuspidal places are `Gal(Ω / k(x))`-conjugate.** -/
theorem exists_gal_placeSmul {ℓ : ℕ} (hℓ : ℓ ≠ 0) {T T' : E.toAffine.Point} (hT : ℓ • T = 0)
    (hT' : ℓ • T' = 0) {W W' : ValuationSubring (Ω E)} (h : IsCuspPlace E ℓ T W)
    (h' : IsCuspPlace E ℓ T' W') : ∃ σ : Gal E, W' = placeSmul E σ W := by
  have hx := xG_notMem_of_isCuspPlace E hℓ hT h
  have hx' := xG_notMem_of_isCuspPlace E hℓ hT' h'
  have hcomap : W.comap (algebraMap (baseField E) (Ω E)) =
      W'.comap (algebraMap (baseField E) (Ω E)) := by
    ext z
    have hz : (z : Ω E) ∈ IntermediateField.adjoin k {xG E} :=
      (SetLike.ext_iff.1 (hbase E) (z : Ω E)).1 z.2
    have hk : ∀ c : k, algebraMap k (Ω E) c ∈ W := h.1
    have hk' : ∀ c : k, algebraMap k (Ω E) c ∈ W' := h'.1
    exact mem_iff_of_mem_adjoin hk hx hk' hx' hz
  exact CurvesJacobian.Cusp.exists_algEquiv_comap_eq W W' hcomap

/-! ### The action of `Gal(Ω / k(x))` on the division point -/

open scoped Classical in
omit [CharZero k] in
/-- `σ(G) = ±G` for `σ ∈ Gal(Ω / k(x))`. -/
lemma act_genericPoint (σ : Gal E) :
    act E σ (genericPoint E) = genericPoint E ∨ act E σ (genericPoint E) = -genericPoint E := by
  have hx : σ (xG E) = xG E := σ.commutes' ⟨xG E, xG_mem_baseField E⟩
  have h2 : (E⁄(Ω E)).toAffine.Nonsingular (σ (xG E)) (σ (yG E)) :=
    (Affine.baseChange_nonsingular (W := E) (f := σk E σ)
      (σk E σ).toRingHom.injective _ _).mpr (nonsingular_generic E)
  rw [Genuine.genericPoint, act_some E σ _ h2]
  rcases Affine.Y_eq_of_X_eq h2.1 (nonsingular_generic E).1 hx with hy | hy
  · exact Or.inl (some_ext hx hy)
  · exact Or.inr (by rw [Affine.Point.neg_some]; exact some_ext hx hy)

open scoped Classical in
/-- If all `n`-torsion of `E` is `k`-rational, every `n`-torsion point of `E(Ω)` is rational. -/
lemma exists_base_of_nsmul {n : ℕ} (hn : n ≠ 0)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point (n : ℤ)) = n ^ 2)
    {D : Pt E} (hD : n • D = 0) : ∃ t : E.toAffine.Point, base E t = D := by
  have htgt : Nat.card (AddSubgroup.torsionBy (Pt E) (n : ℤ)) = n ^ 2 :=
    card_torsionBy_eq_sq' (E⁄(Ω E)) n hn
  haveI : Finite (AddSubgroup.torsionBy (Pt E) (n : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [htgt]; positivity)
  let g : AddSubgroup.torsionBy E.toAffine.Point (n : ℤ) →
      AddSubgroup.torsionBy (Pt E) (n : ℤ) := fun t => ⟨base E t.1, by
    have := t.2
    rw [AddSubgroup.torsionBy.nsmul_iff] at this ⊢
    rw [← map_nsmul, this, map_zero]⟩
  have hg : Function.Injective g := fun s t hst =>
    Subtype.ext (pointMap_injective E _ (congrArg Subtype.val hst))
  have hDt : D ∈ AddSubgroup.torsionBy (Pt E) (n : ℤ) :=
    AddSubgroup.torsionBy.nsmul_iff.mpr hD
  obtain ⟨t, ht⟩ := (hg.bijective_of_nat_card_le (htgt.trans hcard.symm).le).2 ⟨D, hDt⟩
  exact ⟨t.1, congrArg Subtype.val ht⟩

open scoped Classical in
/-- **(V4)** Every `σ ∈ Gal(Ω / k(x))` has `σ(Q_ℓ) = ε Q_ℓ + S`, `ε = ±1`, `S ∈ E(k)[ℓ]`. -/
theorem act_Qpt_eq {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point (ℓ : ℤ)) = ℓ ^ 2) (σ : Gal E) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∃ S : E.toAffine.Point, ℓ • S = 0 ∧
      act E σ (Qpt E ℓ) = ε • Qpt E ℓ + base E S := by
  obtain ⟨ε, hε, hG⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      act E σ (genericPoint E) = ε • genericPoint E := by
    rcases act_genericPoint E σ with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_zsmul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_zsmul]⟩
  have hD : ℓ • (act E σ (Qpt E ℓ) - ε • Qpt E ℓ) = 0 := by
    rw [nsmul_sub, ← map_nsmul, GenuineBaseChange.nsmul_Qpt E hℓ, hG, smul_comm,
      GenuineBaseChange.nsmul_Qpt E hℓ, sub_self]
  obtain ⟨S, hS⟩ := exists_base_of_nsmul E hℓ hcard hD
  refine ⟨ε, hε, S, ?_, ?_⟩
  · apply pointMap_injective E (algebraMap k (Ω E))
    change base E (ℓ • S) = base E 0
    rw [map_nsmul, hS, hD, map_zero]
  · rw [hS]
    abel

/-! ### An automorphism fixing a cuspidal place and negating `Q_ℓ − T` -/

open scoped Classical in
/-- **(V5)** For a place `W` over `T` there is `ρ ∈ Gal(Ω / k(x))` with `ρ(W) = W` and
`ρ(Q_ℓ − T) = −(Q_ℓ − T)`. -/
theorem exists_fix_neg {ℓ : ℕ} (hℓ : ℓ ≠ 0) {T : E.toAffine.Point} (hT : ℓ • T = 0)
    {W : ValuationSubring (Ω E)} (hW : IsCuspPlace E ℓ T W) :
    ∃ ρ : Gal E, placeSmul E ρ W = W ∧
      act E ρ (Qpt E ℓ - base E T) = -(Qpt E ℓ - base E T) := by
  have hP := nsmul_Qpt_sub_base E hℓ hT
  have hpole := hW.2
  generalize Qpt E ℓ - base E T = P at hP hpole ⊢
  rcases P with _ | ⟨a, b, hab⟩
  · exact absurd hpole id
  have ha : a ∉ W := hpole
  have hk : ∀ c : k, algebraMap k (Ω E) c ∈ W := hW.1
  -- the short model `y² = c(x)`
  have ha₁ : ((shortModel E)⁄(Ω E)).toAffine.a₁ = 0 := by
    simp [WeierstrassCurve.baseChange, IntegralTorsion.completeSquare_a₁]
  have ha₃ : ((shortModel E)⁄(Ω E)).toAffine.a₃ = 0 := by
    simp [WeierstrassCurve.baseChange, IntegralTorsion.completeSquare_a₃]
  have h1 := (nonsingular_vc (vcΩ E) (E⁄(Ω E)) a b).mp hab
  rw [vcΩ_smul] at h1
  obtain ⟨h', hs⟩ := exists_some_eq (vcX_vcΩ E a) h1
  rw [← toShort_some E hab h1] at hs
  set y := vcY (vcΩ E) a b with hydef
  set c : k[X] := C 1 * X ^ 3 + C (shortModel E).a₂ * X ^ 2 + C (shortModel E).a₄ * X +
    C (shortModel E).a₆ with hcdef
  have hc : c.natDegree = 3 := natDegree_cubic one_ne_zero
  have hy : y ^ 2 = aeval a c := by
    have e := (Affine.equation_iff _ _).1 h'.1
    have e2 : ((shortModel E)⁄(Ω E)).toAffine.a₂ = algebraMap k (Ω E) (shortModel E).a₂ := rfl
    have e4 : ((shortModel E)⁄(Ω E)).toAffine.a₄ = algebraMap k (Ω E) (shortModel E).a₄ := rfl
    have e6 : ((shortModel E)⁄(Ω E)).toAffine.a₆ = algebraMap k (Ω E) (shortModel E).a₆ := rfl
    rw [ha₁, ha₃, e2, e4, e6] at e
    simp only [hcdef, map_add, map_mul, aeval_C, aeval_X, aeval_X_pow, map_one, one_mul]
    linear_combination e
  -- `k(x) ⊆ k(a)`
  obtain ⟨hne, hX⟩ := xG_mul_ΨSq E hab hP
  have hxG : xG E ∈ IntermediateField.adjoin k {a} := by
    rw [eq_div_of_mul_eq hne hX]
    exact div_mem (aeval_mem_adjoin_simple _ _)
      (aeval_mem_adjoin_simple _ _)
  have hle : baseField E ≤ IntermediateField.adjoin k {a} := by
    rw [hbase E]
    exact IntermediateField.adjoin_simple_le_iff.2 hxG
  obtain ⟨ρ, hρW, hρa, hρy⟩ := exists_fix_neg_aux hk ha hc hy hle
  have hn : ((shortModel E)⁄(Ω E)).toAffine.Nonsingular a (-y) := by
    have ey : ((shortModel E)⁄(Ω E)).toAffine.negY a y = -y := by
      rw [Affine.negY, ha₁, ha₃]
      ring
    exact ey ▸ (Affine.nonsingular_neg _ _).mpr h'
  have hsn : toShort E (-(Affine.Point.some a b hab)) = Affine.Point.some a (-y) hn := by
    rw [map_neg, hs, Affine.Point.neg_some]
    refine some_ext rfl ?_
    rw [Affine.negY, ha₁, ha₃]
    ring
  refine ⟨ρ, hρW, ?_⟩
  apply toShort_injective E
  rw [toShort_act, hs, hsn, Affine.Point.map_some]
  exact some_ext hρa hρy

end Generic

/-! ### Places over one cusp are conjugate -/

section Orbicurve

variable {k : Type u} [Field k] [CharZero k] {X : Orbicurve k}

open scoped Classical in
omit [CharZero k] in
lemma placeSmul_mul (σ ρ : Gal X.E) (W : ValuationSubring (Ω X.E)) :
    placeSmul X.E (σ * ρ) W = placeSmul X.E σ (placeSmul X.E ρ W) :=
  ValuationSubring.ext _ _ fun _ => Iff.rfl

omit [CharZero k] in
/-- The equivalence closure of `cuspRel` is `cuspRel`. -/
lemma cuspRel_of_eqvGen {a b : X.Q} (h : Relation.EqvGen X.cuspRel a b) :
    a = b ∨ (X.pm = true ∧ a = -b) := by
  induction h with
  | rel x y hxy => exact hxy
  | refl x => exact Or.inl rfl
  | symm x y _ ih =>
    rcases ih with h1 | ⟨hp, h1⟩
    · exact Or.inl h1.symm
    · exact Or.inr ⟨hp, by rw [h1, neg_neg]⟩
  | trans x y z _ _ ih1 ih2 =>
    rcases ih1 with h1 | ⟨hp, h1⟩ <;> rcases ih2 with h2 | ⟨hp', h2⟩
    · exact Or.inl (h1.trans h2)
    · exact Or.inr ⟨hp', by rw [h1, h2]⟩
    · exact Or.inr ⟨hp, by rw [h1, h2]⟩
    · exact Or.inl (by rw [h1, h2, neg_neg])

open scoped Classical in
omit [CharZero k] in
/-- Places over the same cusp: `T' = η T + m` with `η` an admissible sign and `m ∈ M`. -/
lemma CuspPlace.exists_sign_of_cusp_eq {c c' : CuspPlace X} (h : c'.cusp = c.cusp) :
    ∃ η : ℤ, SignOK X.pm η ∧ ∃ m ∈ X.M,
      (c'.T : X.E.toAffine.Point) = η • (c.T : X.E.toAffine.Point) + m := by
  rcases cuspRel_of_eqvGen (Quot.eqvGen_exact h) with h1 | ⟨hp, h1⟩
  · have h2 := (QuotientAddGroup.eq_iff_sub_mem).1 h1
    rw [AddSubgroup.mem_addSubgroupOf] at h2
    refine ⟨1, Or.inl rfl, _, h2, ?_⟩
    simp only [AddSubgroup.coe_sub, one_zsmul]
    abel
  · rw [← map_neg] at h1
    have h2 := (QuotientAddGroup.eq_iff_sub_mem).1 h1
    rw [AddSubgroup.mem_addSubgroupOf] at h2
    refine ⟨-1, Or.inr ⟨hp, rfl⟩, _, h2, ?_⟩
    simp only [AddSubgroup.coe_sub, AddSubgroup.coe_neg, neg_one_zsmul]
    abel

open scoped Classical in
/-- **Places over the same cusp are `Aut(Ω / F_X)`-conjugate** (`X.level = ℓ ≠ 0`, all of `E[ℓ]`
rational): if `c, c'` are cuspidal places of `X` over the same cusp, then `c'.W = σ(c.W)` for
some `σ ∈ Hgp`. With `CuspPlace.cusp_eq_of_smul`: the cusps of `X` are the `Hgp`-orbits of
cuspidal places. -/
theorem CuspPlace.exists_smul_of_cusp_eq (hℓ : X.level ≠ 0)
    (hcard : Nat.card X.torsion = X.level ^ 2) {c c' : CuspPlace X} (h : c'.cusp = c.cusp) :
    ∃ σ ∈ Hgp X.E X.level X.M X.pm, c'.W = placeSmul X.E σ c.W := by
  have hT : X.level • (c.T : X.E.toAffine.Point) = 0 :=
    (AddSubgroup.torsionBy.nsmul_iff (A := X.E.toAffine.Point)).1 c.T.2
  have hT' : X.level • (c'.T : X.E.toAffine.Point) = 0 :=
    (AddSubgroup.torsionBy.nsmul_iff (A := X.E.toAffine.Point)).1 c'.T.2
  obtain ⟨σ, hσ⟩ := exists_gal_placeSmul X.E hℓ hT hT' c.isCusp c'.isCusp
  obtain ⟨ε, hε, S, hS, hσQ⟩ := act_Qpt_eq X.E hℓ hcard σ
  have h2 := isCuspPlace_smul hε hσQ c.isCusp
  rw [← hσ] at h2
  have hu : (c'.T : X.E.toAffine.Point) = ε • ((c.T : X.E.toAffine.Point) - S) :=
    isCuspPlace_unique c'.isCusp h2
  obtain ⟨η, hη, m, hm, hT'm⟩ := CuspPlace.exists_sign_of_cusp_eq h
  have heq := hu.symm.trans hT'm
  obtain ⟨ρ, hρW, hρ⟩ := exists_fix_neg X.E hℓ hT c.isCusp
  have hmem : ∀ {τ : Gal X.E} {ζ : ℤ} {R : X.E.toAffine.Point}, SignOK X.pm ζ → R ∈ X.M →
      X.level • R = 0 → act X.E τ (Qpt X.E X.level) = ζ • Qpt X.E X.level + base X.E R →
      τ ∈ Hgp X.E X.level X.M X.pm := by
    intro τ ζ R hζ hR hRt hτ
    refine ⟨ζ, hζ, ?_⟩
    rw [hτ, add_sub_cancel_left]
    refine ⟨R, ⟨hR, ?_⟩, rfl⟩
    have he : effLevel X.level = X.level := if_neg hℓ
    change R ∈ AddSubgroup.torsionBy _ ((effLevel X.level : ℕ) : ℤ)
    rw [he]
    exact AddSubgroup.torsionBy.nsmul_iff.2 hRt
  have hρQ : act X.E (σ * ρ) (Qpt X.E X.level) = (-ε) • Qpt X.E X.level +
      base X.E ((c.T : X.E.toAffine.Point) + c.T - S) := by
    have h3 : act X.E ρ (Qpt X.E X.level) =
        -Qpt X.E X.level + base X.E c.T + base X.E c.T := by
      have h4 := hρ
      rw [map_sub, act_base] at h4
      calc _ = (act X.E ρ (Qpt X.E X.level) - base X.E c.T) + base X.E c.T := by abel
        _ = _ := by rw [h4]; abel
    rw [act_mul, h3, map_add, map_add, map_neg, act_base, hσQ, neg_zsmul, map_sub, map_add]
    abel
  have hσρ : c'.W = placeSmul X.E (σ * ρ) c.W := by
    rw [placeSmul_mul, hρW, hσ]
  have htor : X.level • ((c.T : X.E.toAffine.Point) + c.T - S) = 0 := by
    rw [nsmul_sub, nsmul_add, hT, hS, add_zero, sub_zero]
  rcases hε with rfl | rfl <;> rcases hη with rfl | ⟨hpm, rfl⟩
  · -- `ε = η = 1`: `S = -m`
    have eS : S = -m := by
      calc S = (c.T : X.E.toAffine.Point) - (1 : ℤ) • ((c.T : X.E.toAffine.Point) - S) := by
            rw [one_zsmul]; abel
        _ = -m := by rw [heq, one_zsmul]; abel
    exact ⟨σ, hmem (Or.inl rfl) (eS ▸ neg_mem hm) hS hσQ, hσ⟩
  · -- `ε = 1`, `η = -1`: use `σ ρ`
    have eR : (c.T : X.E.toAffine.Point) + c.T - S = m := by
      calc (c.T : X.E.toAffine.Point) + c.T - S =
            (1 : ℤ) • ((c.T : X.E.toAffine.Point) - S) + c.T := by rw [one_zsmul]; abel
        _ = m := by rw [heq, neg_one_zsmul]; abel
    exact ⟨σ * ρ, hmem (Or.inr ⟨hpm, rfl⟩) (eR ▸ hm) htor hρQ, hσρ⟩
  · -- `ε = -1`, `η = 1`: use `σ ρ`
    have eR : (c.T : X.E.toAffine.Point) + c.T - S = -m := by
      calc (c.T : X.E.toAffine.Point) + c.T - S =
            c.T - (-1 : ℤ) • ((c.T : X.E.toAffine.Point) - S) := by rw [neg_one_zsmul]; abel
        _ = -m := by rw [heq, one_zsmul]; abel
    exact ⟨σ * ρ, hmem (Or.inl (neg_neg 1)) (eR ▸ neg_mem hm) htor hρQ, hσρ⟩
  · -- `ε = η = -1`: `S = m`
    have eS : S = m := by
      calc S = (-1 : ℤ) • ((c.T : X.E.toAffine.Point) - S) -
            (-1 : ℤ) • (c.T : X.E.toAffine.Point) := by simp only [neg_one_zsmul]; abel
        _ = m := by rw [heq]; abel
    exact ⟨σ, hmem (Or.inr ⟨hpm, rfl⟩) (eS ▸ hm) hS hσQ, hσ⟩

end Orbicurve

end Iut.Multiradial.Theater
