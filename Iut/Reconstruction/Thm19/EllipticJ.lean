/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticGenusOne
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic.ComputeDegree

/-!
# A semilinear automorphism of an elliptic function field fixing the origin preserves `j`

Generic input for MR9, `CKSemiAbsConj` item 5 (`σ(j) = j`). Let `F / k` be a function field of
genus one with a Weierstrass pair `(x, y)` (curves-jacobian `WEq₂ W x y`, `x` transcendental,
`[F : k(x)] = 2`), and `O` the unique pole of `x` (`exists_unique_pole_of_weq₂`).

* `ord_pole_x`, `ord_pole_y`: `ord_O x = -2`, `ord_O y = -3`;
* **`exists_eq_of_regular`** (Riemann–Roch, weil-curves `ell_eq_of_deg_gt`, `ℓ(3O) = 3`): a
  function regular away from `O` with `ord_O f ≥ -3` is `c y + a x + b`, and `c = 0` if
  `ord_O f ≥ -2`;
* `weierstrass_unique`: the Weierstrass equation satisfied by `(x, y)` is unique;
* **`j_eq_of_semilinear`**: let `ψ : F ≃+* F'` be semilinear over `σ : k ≃+* k'` between two such
  function fields, mapping functions regular away from `O` to functions regular away from `O'` and
  preserving `ord_O`. Then `ψ x = u² x' + r`, `ψ y = u³ y' + u² s x' + t`, so the curve `W^σ` is the
  variable change `(u, r, s, t)` of `W'` (`WeierstrassCurve.variableChange_j`), and
  `j(W') = σ(j(W))` (`WeierstrassCurve.map_j`).

This is the classical fact that `E^σ ≅ E'` when `k̄(E) ≅ k̄(E')` `σ`-semilinearly compatibly
with the origins (here proved directly from Riemann–Roch).
-/

open Polynomial WeilCurves.FunctionField CurvesJacobian.Cusp Module
open scoped IntermediateField

noncomputable section

namespace Iut.Reconstruction.Thm19.EllipticJ

/-! ### One elliptic function field -/

section One

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [PerfectField k] [IsFunctionField k F]
  {W : WeierstrassCurve k} {x y : F}

/-- **`[F : k(x)] ≤ 2` already gives `[F : k(x)] = 2`**: a pole of `x` has order `≥ 2`. -/
theorem finrank_eq_two_of_le (h : WEq₂ W x y) (hx : Transcendental k x)
    (h2 : finrank k⟮x⟯ F ≤ 2) : finrank k⟮x⟯ F = 2 := by
  obtain ⟨P, hP⟩ := Place.exists_ord_neg (k := k) hx
  have hxP : x ∉ P.1 := P.ord_neg_iff.1 hP
  have h1 := two_mul_ord_eq_of_weq₂ W h hxP
  have hle : Finsupp.single P 2 ≤ Divisor.polarDivisor k x := by
    refine Finsupp.le_def.2 fun R => ?_
    rw [Finsupp.single_apply, Divisor.polarDivisor_apply]
    split_ifs with hPR
    · subst hPR
      omega
    · exact le_max_left _ _
  have h3 := Divisor.deg_mono hle
  rw [Divisor.deg_single, Divisor.deg_polarDivisor hx] at h3
  have := P.deg_pos
  have h4 : (2 : ℤ) ≤ finrank k⟮x⟯ F := by nlinarith
  omega

/-- The divisor of poles of `x` is concentrated at its unique pole. -/
lemma polarDivisor_eq_single (h : WEq₂ W x y) (hx : Transcendental k x)
    (h2 : finrank k⟮x⟯ F = 2) {P : Place k F} (hP : x ∉ P.1) :
    Divisor.polarDivisor k x = Finsupp.single P (-P.ord x) := by
  obtain ⟨O, -, -, huniq⟩ := exists_unique_pole_of_weq₂ W h hx h2
  ext Q
  rw [Divisor.polarDivisor_apply, Finsupp.single_apply]
  split_ifs with hQ
  · subst hQ
    have := P.ord_neg_iff.2 hP
    omega
  · have hxQ : x ∈ Q.1 := by
      by_contra hxQ
      exact hQ ((huniq P hP).trans (huniq Q hxQ).symm)
    have := Q.ord_nonneg_of_mem hxQ
    omega

/-- **`ord_O x = -2`** at the pole `O` of `x`. -/
theorem ord_pole_x (h : WEq₂ W x y) (hx : Transcendental k x) (h2 : finrank k⟮x⟯ F = 2)
    {P : Place k F} (hP : x ∉ P.1) : P.ord x = -2 := by
  obtain ⟨O, hO, hdeg, huniq⟩ := exists_unique_pole_of_weq₂ W h hx h2
  obtain rfl := huniq P hP
  have h1 := Divisor.deg_polarDivisor (k := k) hx
  rw [polarDivisor_eq_single h hx h2 hP, Divisor.deg_single, hdeg, h2] at h1
  omega

/-- **`ord_O y = -3`** at the pole `O` of `x`. -/
theorem ord_pole_y (h : WEq₂ W x y) (hx : Transcendental k x) (h2 : finrank k⟮x⟯ F = 2)
    {P : Place k F} (hP : x ∉ P.1) : P.ord y = -3 := by
  have h1 := two_mul_ord_eq_of_weq₂ W h hP
  rw [ord_pole_x h hx h2 hP] at h1
  omega

/-- Away from the pole of `x`, `x` and `y` are regular. -/
lemma mem_of_ne_pole (h : WEq₂ W x y) (hx : Transcendental k x) (h2 : finrank k⟮x⟯ F = 2)
    {P Q : Place k F} (hP : x ∉ P.1) (hQ : Q ≠ P) : x ∈ Q.1 ∧ y ∈ Q.1 := by
  obtain ⟨O, -, -, huniq⟩ := exists_unique_pole_of_weq₂ W h hx h2
  have hxQ : x ∈ Q.1 := by
    by_contra hxQ
    exact hQ ((huniq Q hxQ).trans (huniq P hP).symm)
  exact ⟨hxQ, mem_of_weq₂ W h hxQ⟩

variable (k) in
/-- `((a, b), c) ↦ a x + b + c y`. -/
def lin3 (x y : F) : (k × k) × k →ₗ[k] F :=
  LinearMap.coprod (LinearMap.coprod (LinearMap.toSpanSingleton k F x)
    (LinearMap.toSpanSingleton k F 1)) (LinearMap.toSpanSingleton k F y)

omit [PerfectField k] [IsFunctionField k F] in
lemma lin3_apply (x y : F) (p : (k × k) × k) :
    lin3 k x y p = algebraMap k F p.1.1 * x + algebraMap k F p.1.2 + algebraMap k F p.2 * y := by
  simp [lin3, Algebra.smul_def]

lemma lin3_injective (h : WEq₂ W x y) (hx : Transcendental k x) {P : Place k F}
    (hP : P.ord x < 0) : Function.Injective (lin3 k x y) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
  rw [lin3_apply] at hp
  have e : aeval x (C p.1.1 * X + C p.1.2) + aeval x (C p.2) * y = 0 := by
    simp only [map_add, map_mul, aeval_C, aeval_X]
    linear_combination hp
  obtain ⟨h1, h2⟩ := eq_zero_of_aeval_add_mul₂ W h hx hP e
  have ha := congrArg (fun q => q.coeff 1) h1
  have hb := congrArg (fun q => q.coeff 0) h1
  simp only [coeff_add, coeff_C_mul, coeff_X, coeff_C, coeff_zero] at ha hb
  norm_num at ha hb
  rw [C_eq_zero] at h2
  exact Prod.ext (Prod.ext ha hb) h2

/-- **Functions regular away from `O` with a pole of order `≤ 3` at `O`** (`ℓ(3O) = 3` by
Riemann–Roch in genus one): they are `c y + a x + b`. -/
theorem exists_eq_of_regular (h : WEq₂ W x y) (hx : Transcendental k x)
    (h2 : finrank k⟮x⟯ F = 2) (hg : genus k F = 1) {P : Place k F} (hP : x ∉ P.1) {f : F}
    (hreg : ∀ Q : Place k F, Q ≠ P → f ∈ Q.1) (hf : f = 0 ∨ -3 ≤ P.ord f) :
    ∃ a b c : k, f = algebraMap k F a * x + algebraMap k F b + algebraMap k F c * y := by
  obtain ⟨-, -, hdeg1, -⟩ := exists_unique_pole_of_weq₂ W h hx h2
  have hPx := ord_pole_x h hx h2 hP
  have hPy := ord_pole_y h hx h2 hP
  set D : Divisor k F := Finsupp.single P 3 with hD
  have hdeg : D.deg = 3 := by
    rw [hD, Divisor.deg_single]
    obtain ⟨O, hO, hO1, huniq⟩ := exists_unique_pole_of_weq₂ W h hx h2
    obtain rfl := huniq P hP
    rw [hO1]
    rfl
  have hell := ell_eq_of_deg_gt (A := D) (by rw [hdeg, hg]; omega)
  rw [hdeg, hg] at hell
  have hmem : ∀ g : F, (∀ Q : Place k F, Q ≠ P → g ∈ Q.1) → (g = 0 ∨ -3 ≤ P.ord g) →
      g ∈ Divisor.L D := by
    intro g hgQ hgP
    refine Divisor.mem_L.2 ?_
    rcases hgP with h0 | hgP
    · exact Or.inl h0
    by_cases h0 : g = 0
    · exact Or.inl h0
    refine Or.inr fun Q => ?_
    by_cases hQ : Q = P
    · subst hQ
      rw [hD, Finsupp.single_eq_same]
      omega
    · rw [hD, Finsupp.single_eq_of_ne hQ]
      have := Q.ord_nonneg_of_mem (hgQ Q hQ)
      omega
  have hrange : ∀ p, lin3 k x y p ∈ Divisor.L D := by
    intro p
    refine hmem _ (fun Q hQ => ?_) ?_
    · obtain ⟨hxQ, hyQ⟩ := mem_of_ne_pole h hx h2 hP hQ
      rw [lin3_apply]
      exact add_mem (add_mem (mul_mem (Q.algebraMap_mem _) hxQ) (Q.algebraMap_mem _))
        (mul_mem (Q.algebraMap_mem _) hyQ)
    · rw [lin3_apply]
      have hx' : OrdGe₂ P (-2) x := Or.inr hPx.ge
      have hy' : OrdGe₂ P (-3) y := Or.inr hPy.ge
      have t1 : OrdGe₂ P (-3) (algebraMap k F p.1.1 * x) :=
        ordGe₂_mul (ordGe₂_algebraMap _) hx' (by norm_num)
      have t2 : OrdGe₂ P (-3) (algebraMap k F p.1.2) :=
        ordGe₂_mono (by norm_num) (ordGe₂_algebraMap _)
      have t3 : OrdGe₂ P (-3) (algebraMap k F p.2 * y) :=
        ordGe₂_mul (ordGe₂_algebraMap _) hy' (by norm_num)
      have e : OrdGe₂ P (-3) (algebraMap k F p.1.1 * x + algebraMap k F p.1.2 +
          algebraMap k F p.2 * y) := ordGe₂_add (ordGe₂_add t1 t2) t3
      exact e
  let φ : ((k × k) × k) →ₗ[k] Divisor.L D := (lin3 k x y).codRestrict _ hrange
  have hφi : Function.Injective φ := fun p q hpq =>
    lin3_injective h hx (P.ord_neg_iff.2 hP) (congrArg Subtype.val hpq)
  have hfin : finrank k ((k × k) × k) = finrank k (Divisor.L D) := by
    rw [finrank_prod, finrank_prod, finrank_self]
    change _ = Divisor.ell D
    omega
  haveI : FiniteDimensional k (Divisor.L D) :=
    Module.finite_of_finrank_pos (by rw [← hfin]; simp)
  have hφs : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hφi
  obtain ⟨p, hp⟩ := hφs ⟨f, hmem f hreg hf⟩
  refine ⟨p.1.1, p.1.2, p.2, ?_⟩
  have := congrArg Subtype.val hp
  rw [← lin3_apply]
  exact this.symm

/-- **Functions regular away from `O` with a pole of order `≤ 2` at `O`** are `a x + b`. -/
theorem exists_eq_of_regular_two (h : WEq₂ W x y) (hx : Transcendental k x)
    (h2 : finrank k⟮x⟯ F = 2) (hg : genus k F = 1) {P : Place k F} (hP : x ∉ P.1) {f : F}
    (hreg : ∀ Q : Place k F, Q ≠ P → f ∈ Q.1) (hf : f = 0 ∨ -2 ≤ P.ord f) :
    ∃ a b : k, f = algebraMap k F a * x + algebraMap k F b := by
  obtain ⟨a, b, c, rfl⟩ := exists_eq_of_regular h hx h2 hg hP hreg
    (hf.imp_right fun h' => by omega)
  refine ⟨a, b, ?_⟩
  by_contra hne
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hne
  have hPx := ord_pole_x h hx h2 hP
  have hPy := ord_pole_y h hx h2 hP
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [P.ord_zero] at hPy
    omega
  have hcy0 : algebraMap k F c * y ≠ 0 :=
    mul_ne_zero ((map_ne_zero_iff _ (algebraMap k F).injective).2 hc) hy0
  have hcy : P.ord (algebraMap k F c * y) = -3 := by
    rw [P.ord_mul ((map_ne_zero_iff _ (algebraMap k F).injective).2 hc) hy0,
      P.ord_algebraMap_base, hPy, zero_add]
  have hrest : OrdGe₂ P (-2) (algebraMap k F a * x + algebraMap k F b) :=
    ordGe₂_add (ordGe₂_mul (ordGe₂_algebraMap _) (Or.inr hPx.ge) (by omega))
      (ordGe₂_mono (by omega) (ordGe₂_algebraMap _))
  have e := ord_add_eq_of_ordGe₂ hrest hcy0 (by omega)
  rw [add_comm] at e
  rcases hf with h0 | hf
  · rw [h0, P.ord_zero] at e
    omega
  · omega

/-- **The Weierstrass equation of `(x, y)` is unique** (`x` transcendental with a pole). -/
theorem weierstrass_unique {W₁ W₂ : WeierstrassCurve k} (h₁ : WEq₂ W₁ x y) (h₂ : WEq₂ W₂ x y)
    (hx : Transcendental k x) {P : Place k F} (hP : P.ord x < 0) : W₁ = W₂ := by
  have e : aeval x (-(C (W₁.a₂ - W₂.a₂) * X ^ 2 + C (W₁.a₄ - W₂.a₄) * X + C (W₁.a₆ - W₂.a₆))) +
      aeval x (C (W₁.a₁ - W₂.a₁) * X + C (W₁.a₃ - W₂.a₃)) * y = 0 := by
    simp only [map_add, map_mul, map_neg, map_sub, map_pow, aeval_C, aeval_X]
    linear_combination h₁ - h₂
  obtain ⟨hA, hB⟩ := eq_zero_of_aeval_add_mul₂ W₁ h₁ hx hP e
  have hA' : C (W₁.a₂ - W₂.a₂) * X ^ 2 + C (W₁.a₄ - W₂.a₄) * X + C (W₁.a₆ - W₂.a₆) = 0 :=
    neg_eq_zero.1 hA
  have quad : ∀ α β γ : k, C α * X ^ 2 + C β * X + C γ = 0 → α = 0 ∧ β = 0 ∧ γ = 0 := by
    intro α β γ hq
    have e2 := congrArg (fun q => q.coeff 2) hq
    have e1 := congrArg (fun q => q.coeff 1) hq
    have e0 := congrArg (fun q => q.coeff 0) hq
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at e2 e1 e0
    norm_num at e2 e1 e0
    exact ⟨e2, e1, e0⟩
  have lin : ∀ α β : k, C α * X + C β = 0 → α = 0 ∧ β = 0 := by
    intro α β hq
    have e1 := congrArg (fun q => q.coeff 1) hq
    have e0 := congrArg (fun q => q.coeff 0) hq
    simp only [coeff_add, coeff_C_mul, coeff_X, coeff_C, coeff_zero] at e1 e0
    norm_num at e1 e0
    exact ⟨e1, e0⟩
  obtain ⟨e2, e1, e0⟩ := quad _ _ _ hA'
  obtain ⟨f1, f0⟩ := lin _ _ hB
  ext
  · exact sub_eq_zero.1 f1
  · exact sub_eq_zero.1 e2
  · exact sub_eq_zero.1 f0
  · exact sub_eq_zero.1 e1
  · exact sub_eq_zero.1 e0

end One

/-! ### Two elliptic function fields and a semilinear isomorphism -/

section Two

variable {k F k' F' : Type*} [Field k] [Field F] [Algebra k F] [Field k'] [Field F']
  [Algebra k' F']

/-- A semilinear ring homomorphism maps a Weierstrass pair of `W` to one of `W^σ`. -/
lemma weq_map {W : WeierstrassCurve k} {x y : F} (ψ : F →+* F') (σ : k →+* k')
    (hψσ : ∀ c, ψ (algebraMap k F c) = algebraMap k' F' (σ c)) (h : WEq₂ W x y) :
    WEq₂ (W.map σ) (ψ x) (ψ y) := by
  have e := congrArg ψ h
  simp only [map_add, map_mul, map_pow, hψσ] at e
  exact e

/-- **Change of variables**: if `(u² x + r, u³ y + u² s x + t)` satisfies `W₀`, then `(x, y)`
satisfies `V • W₀`, `V = (u, r, s, t)`. -/
lemma weq_variableChange (V : WeierstrassCurve.VariableChange k') {W₀ : WeierstrassCurve k'}
    {x y : F'}
    (h : WEq₂ W₀ (algebraMap k' F' ((V.u : k') ^ 2) * x + algebraMap k' F' V.r)
      (algebraMap k' F' ((V.u : k') ^ 3) * y + algebraMap k' F' ((V.u : k') ^ 2 * V.s) * x +
        algebraMap k' F' V.t)) :
    WEq₂ (V • W₀) x y := by
  have hu : algebraMap k' F' (V.u : k') ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap k' F').injective).2 V.u.ne_zero
  rw [WEq₂, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆]
  simp only [map_mul, map_pow, map_add, map_sub, map_ofNat, Units.val_inv_eq_inv_val,
    map_inv₀] at h ⊢
  field_simp
  linear_combination h

variable [PerfectField k] [IsFunctionField k F] [PerfectField k'] [IsFunctionField k' F']

/-- **A semilinear isomorphism of elliptic function fields respecting the origins preserves `j`**:
`j(W') = σ(j(W))` (MR9, `CKSemiAbsConj` item 5, generic). -/
theorem j_eq_of_semilinear {W : WeierstrassCurve k} [W.IsElliptic] {x y : F}
    {W' : WeierstrassCurve k'} [W'.IsElliptic] {x' y' : F'} (ψ : F ≃+* F') (σ : k ≃+* k')
    (hψσ : ∀ c, ψ (algebraMap k F c) = algebraMap k' F' (σ c))
    (h : WEq₂ W x y) (hx : Transcendental k x) (h2 : finrank k⟮x⟯ F = 2)
    (h' : WEq₂ W' x' y') (hx' : Transcendental k' x') (h2' : finrank k'⟮x'⟯ F' = 2)
    (hg' : genus k' F' = 1) {P : Place k F} (hP : x ∉ P.1) {P' : Place k' F'} (hP' : x' ∉ P'.1)
    (hreg : ∀ f : F, (∀ Q : Place k F, Q ≠ P → f ∈ Q.1) →
      ∀ Q' : Place k' F', Q' ≠ P' → ψ f ∈ Q'.1)
    (hord : ∀ f : F, f ≠ 0 → P'.ord (ψ f) = P.ord f) :
    W'.j = σ W.j := by
  have hx0 : x ≠ 0 := ne_zero_of_transcendental hx
  have hPx := ord_pole_x h hx h2 hP
  have hPy := ord_pole_y h hx h2 hP
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [P.ord_zero] at hPy
    omega
  have hψx : P'.ord (ψ x) = -2 := by rw [hord x hx0, hPx]
  have hψy : P'.ord (ψ y) = -3 := by rw [hord y hy0, hPy]
  obtain ⟨a, b, hxa⟩ := exists_eq_of_regular_two h' hx' h2' hg' hP'
    (hreg x fun Q hQ => (mem_of_ne_pole h hx h2 hP hQ).1) (Or.inr hψx.ge)
  obtain ⟨d, e, c, hyc⟩ := exists_eq_of_regular h' hx' h2' hg' hP'
    (hreg y fun Q hQ => (mem_of_ne_pole h hx h2 hP hQ).2) (Or.inr hψy.ge)
  have hPx' := ord_pole_x h' hx' h2' hP'
  have ha : a ≠ 0 := by
    rintro rfl
    rw [hxa, map_zero, zero_mul, zero_add, P'.ord_algebraMap_base] at hψx
    omega
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul, add_zero] at hyc
    have hrest : OrdGe₂ P' (-2) (algebraMap k' F' d * x' + algebraMap k' F' e) :=
      ordGe₂_add (ordGe₂_mul (ordGe₂_algebraMap _) (Or.inr hPx'.ge) (by omega))
        (ordGe₂_mono (by omega) (ordGe₂_algebraMap _))
    rw [← hyc] at hrest
    rcases hrest with h0 | h1
    · rw [h0, P'.ord_zero] at hψy
      omega
    · omega
  have hW := weq_map ψ.toRingHom σ.toRingHom hψσ h
  change WEq₂ (W.map σ.toRingHom) (ψ x) (ψ y) at hW
  rw [hxa, hyc] at hW
  -- `c² = a³`
  have hca : c ^ 2 = a ^ 3 := by
    set A₁ := (W.map σ.toRingHom).a₁
    set A₂ := (W.map σ.toRingHom).a₂
    set A₃ := (W.map σ.toRingHom).a₃
    set A₄ := (W.map σ.toRingHom).a₄
    set A₆ := (W.map σ.toRingHom).a₆
    set R : k'[X] := (C d * X + C e) ^ 2 + C A₁ * (C a * X + C b) * (C d * X + C e) +
      C A₃ * (C d * X + C e) - (3 * C a ^ 2 * C b * X ^ 2 + 3 * C a * C b ^ 2 * X + C b ^ 3 +
        C A₂ * (C a * X + C b) ^ 2 + C A₄ * (C a * X + C b) + C A₆) +
      C c ^ 2 * (C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆) with hR
    set B : k'[X] := 2 * C c * (C d * X + C e) + C A₁ * (C a * X + C b) * C c + C A₃ * C c -
      C c ^ 2 * (C W'.a₁ * X + C W'.a₃) with hB
    have e0 : aeval x' (C (c ^ 2 - a ^ 3) * X ^ 3 + R) + aeval x' B * y' = 0 := by
      simp only [hR, hB, map_add, map_mul, map_sub, map_pow, aeval_C, aeval_X, map_ofNat]
      linear_combination hW - algebraMap k' F' c ^ 2 * h'
    obtain ⟨hA, -⟩ := eq_zero_of_aeval_add_mul₂ W' h' hx' (P'.ord_neg_iff.2 hP') e0
    have hRd : R.natDegree ≤ 2 := by
      rw [hR]
      compute_degree
    have e3 := congrArg (fun q => q.coeff 3) hA
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_zero] at e3
    rw [coeff_eq_zero_of_natDegree_lt (by omega), add_zero] at e3
    exact sub_eq_zero.1 e3
  -- the change of variables
  set u : k' := c / a with hu
  have hu0 : u ≠ 0 := div_ne_zero hc ha
  have hu2 : u ^ 2 = a := by
    rw [hu, div_pow, hca]
    field_simp
  have hu3 : u ^ 3 = c := by
    rw [pow_succ, hu2, hu]
    field_simp
  let V : WeierstrassCurve.VariableChange k' := ⟨Units.mk0 u hu0, b, d / a, e⟩
  have hV : WEq₂ (V • W.map σ.toRingHom) x' y' := by
    refine weq_variableChange V ?_
    have e1 : ((V.u : k') ^ 2) = a := hu2
    have e2 : ((V.u : k') ^ 3) = c := hu3
    have e3 : ((V.u : k') ^ 2 * V.s) = d := by
      change u ^ 2 * (d / a) = d
      rw [hu2]
      field_simp
    have hy : algebraMap k' F' c * y' + algebraMap k' F' d * x' + algebraMap k' F' V.t =
        algebraMap k' F' d * x' + algebraMap k' F' e + algebraMap k' F' c * y' := by
      change _ + _ + algebraMap k' F' e = _
      ring
    rw [e3, e1, e2, hy]
    exact hW
  have hWW := weierstrass_unique hV h' hx' (P'.ord_neg_iff.2 hP')
  have hj := WeierstrassCurve.variableChange_j (C := V) (W := W.map σ.toRingHom)
  rw [WeierstrassCurve.map_j] at hj
  calc W'.j = (V • W.map σ.toRingHom).j := by simp_rw [hWW]
    _ = σ W.j := hj

end Two

end Iut.Reconstruction.Thm19.EllipticJ
