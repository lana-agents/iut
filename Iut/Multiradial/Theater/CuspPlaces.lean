/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.Theater.LabCuspModel
import Iut.Multiradial.Theater.GenuineBaseChange
import Iut.Reconstruction.Cusp.HemiCuspDecompC

/-!
# Cuspidal places, cuspidal inertia and decomposition groups of the model orbicurves (MR22 T5)

The group side of IUT I, Definition 4.1 (v) and Definition 6.1 (v), (vi) (l.6450, l.10840 ff.
of `~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`: "the set of cusps of
`†D^⊚`", "the cusps of `X̲_K`"), in the Galois model of the genuine étale fundamental group
`π₁(X) = Aut(Ω / F_X) ⧸ ⟨⟨inertia over X_M⟩⟩` of a model orbicurve `X = (E, ℓ, M, ±)`
(`Genuine.pi1Of`, `Anabelian/Genuine/Pi1.lean`): `Ω` is an algebraic closure of `k(E)`, the
generic point `G ∈ E(Ω)` has the chosen `ℓ`-division point `Q_ℓ` (`ℓ Q_ℓ = G`), and the function
field of `X_M = (E/M) ∖ (E[ℓ]/M)` is `k(Q_ℓ)^M`. The cusps of `X_M` are the points over
`E[ℓ]/M`: a place `W` of `Ω` (a valuation subring containing `k`) **lies over the cusp of
`T ∈ E(k)[ℓ]`** when `Q_ℓ − T` reduces to the origin at `W`, i.e. its `x`-coordinate is not in
`W` (`IsCuspPlace`).

* `IsPole W P`: the affine point `P` has `x(P) ∉ W`;
* **`not_isPole_add_base`**: if `x(P) ∉ W` and `S ≠ O` is `k`-rational, then `P + S` is affine
  with `x(P + S) ∈ W` (an explicit computation with the addition formula: with `r = 1/x(P)` and
  `z = y(P)/x(P)²` in `W`, `x(P + S) (1 − x(S) r)² = x(S) + B r + C r² − D z`);
* **`isCuspPlace_unique`**: a place lies over at most one `T`; **`exists_isCuspPlace`**: over
  every `T ∈ E(k)[ℓ]` lies a place (`x(Q_ℓ − T)` is transcendental over `k`, since
  `ℓ (Q_ℓ − T) = G`);
* **`isCuspPlace_smul`**: `σ ∈ Gal(Ω / k(x))` with `σ(Q_ℓ) = ε Q_ℓ + S` maps a place over `T` to
  a place over `ε (T − S)`; for `σ ∈ Aut(Ω / F_X)` (`Hgp`) the **cusp of the place**
  (`cuspOfPlace`, the class of `T` in `Cusp(X) = Q` or `Q/{±1}`) is unchanged
  (`cuspOfPlace_smul`), and every cusp arises (`cuspOfPlace_surjective`);
* `cuspInertia`, `cuspDecomp`: the images in `π₁(X)` of the inertia and decomposition groups of
  a cuspidal place (`HemiCusp.galInertia`, `HemiCusp.galDecomp`), and **their transport by
  conjugation** (`galInertia_smul`, `galDecomp_smul`): the cuspidal inertia (decomposition)
  groups over one `Hgp`-orbit of places form one conjugacy class.

Not covered here (next steps of `MR22-plan.md`): that places over the same cusp are
`Hgp`-conjugate, and that distinct cusps have non-conjugate cuspidal decomposition groups
([AbsTopI] Lemma 4.5; curves-jacobian `CuspCommensurable` for scheme-theoretic curves).
-/

noncomputable section

namespace Iut.Multiradial.Theater

open WeierstrassCurve Iut.Anabelian Iut.Anabelian.Genuine Iut.Reconstruction.HemiCusp
  CurvesJacobian.Cusp

universe u

/-! ### Poles of points at a place -/

section Pole

/-! #### The algebra of the addition formula -/

section Algebra

variable {F : Type*} [Field F]

/-- The `x`-coordinate of a secant sum, cleared of denominators. -/
lemma addX_mul_sq {a₁ a₂ a₃ a₄ a₆ u w s t l : F} (hl : l * (u - s) = w - t)
    (heq : w ^ 2 + a₁ * u * w + a₃ * w = u ^ 3 + a₂ * u ^ 2 + a₄ * u + a₆) :
    (l ^ 2 + a₁ * l - a₂ - u - s) * (u - s) ^ 2 =
      s * u ^ 2 + (a₄ + s ^ 2 - a₁ * t + (a₂ * s + a₂ * s)) * u +
        (a₆ + t ^ 2 + a₁ * t * s - s ^ 3 - a₂ * s ^ 2) - (a₃ + t + t + a₁ * s) * w := by
  linear_combination (l * (u - s) + (w - t) + a₁ * (u - s)) * hl + heq

/-- **The key computation**: if `(u, w)` is a point with `u ∉ W` and `(s, t)` a point with
coordinates in `W` (all coefficients in `W`), the `x`-coordinate of their secant sum lies in `W`.
With `r = 1/u`, `z = w/u²` (both in `W`): `x · (1 − s r)² = s + B r + C r² − D z`. -/
theorem addX_mem (W : ValuationSubring F) {a₁ a₂ a₃ a₄ a₆ u w s t : F} (h₁ : a₁ ∈ W)
    (h₂ : a₂ ∈ W) (h₃ : a₃ ∈ W) (h₄ : a₄ ∈ W) (h₆ : a₆ ∈ W) (hs : s ∈ W) (ht : t ∈ W)
    (hu : u ∉ W) (heq : w ^ 2 + a₁ * u * w + a₃ * w = u ^ 3 + a₂ * u ^ 2 + a₄ * u + a₆) :
    ((w - t) / (u - s)) ^ 2 + a₁ * ((w - t) / (u - s)) - a₂ - u - s ∈ W := by
  set v := W.valuation
  have hle : ∀ x ∈ W, v x ≤ 1 := fun x hx => (W.valuation_le_one_iff x).2 hx
  have hu0 : u ≠ 0 := fun h => hu (h ▸ W.zero_mem)
  have hus : u - s ≠ 0 := sub_ne_zero.2 fun h => hu (h ▸ hs)
  set r := u⁻¹
  have hr : v r < 1 := (ValuationSubring.mem_nonunits_iff W).1
    (W.inv_mem_nonunits_iff.2 (Or.inr hu))
  have hrW : r ∈ W := (W.valuation_le_one_iff r).1 hr.le
  set z := w * r ^ 2
  -- `z = w/u²` lies in `W`
  have hzW : z ∈ W := by
    by_contra hz
    have hz0 : z ≠ 0 := fun h => hz (h ▸ W.zero_mem)
    have hw0 : w ≠ 0 := fun h => hz0 (by simp [z, h])
    have hzi : v z⁻¹ < 1 := (ValuationSubring.mem_nonunits_iff W).1
      (W.inv_mem_nonunits_iff.2 (Or.inr hz))
    have e1 : (r + a₂ * r ^ 2 + a₄ * r ^ 3 + a₆ * r ^ 4) * z⁻¹ ^ 2 - a₁ * r * z⁻¹ -
        a₃ * r ^ 2 * z⁻¹ = (u ^ 3 + a₂ * u ^ 2 + a₄ * u + a₆ - a₁ * u * w - a₃ * w) / w ^ 2 := by
      simp only [z, r]
      field_simp
    have e2 : u ^ 3 + a₂ * u ^ 2 + a₄ * u + a₆ - a₁ * u * w - a₃ * w = w ^ 2 := by
      linear_combination -heq
    rw [e2, div_self (pow_ne_zero 2 hw0)] at e1
    have hziW : z⁻¹ ∈ W := (W.valuation_le_one_iff _).1 hzi.le
    have hA : r + a₂ * r ^ 2 + a₄ * r ^ 3 + a₆ * r ^ 4 ∈ W := by
      refine add_mem (add_mem (add_mem hrW ?_) ?_) ?_ <;>
        exact mul_mem ‹_› (pow_mem hrW _)
    have hlt : v ((r + a₂ * r ^ 2 + a₄ * r ^ 3 + a₆ * r ^ 4) * z⁻¹ ^ 2 - a₁ * r * z⁻¹ -
        a₃ * r ^ 2 * z⁻¹) < 1 := by
      refine v.map_sub_lt (v.map_sub_lt ?_ ?_) ?_
      · rw [map_mul, map_pow]
        refine (mul_le_of_le_one_left' (hle _ hA)).trans_lt ?_
        exact pow_lt_one₀ zero_le hzi two_ne_zero
      · rw [map_mul]
        exact (mul_le_of_le_one_left' (hle _ (mul_mem h₁ hrW))).trans_lt hzi
      · rw [map_mul]
        exact (mul_le_of_le_one_left' (hle _ (mul_mem h₃ (pow_mem hrW 2)))).trans_lt hzi
    rw [e1, map_one] at hlt
    exact lt_irrefl _ hlt
  -- the identity
  set B := a₄ + s ^ 2 - a₁ * t + (a₂ * s + a₂ * s)
  set C := a₆ + t ^ 2 + a₁ * t * s - s ^ 3 - a₂ * s ^ 2
  set D := a₃ + t + t + a₁ * s
  set x := ((w - t) / (u - s)) ^ 2 + a₁ * ((w - t) / (u - s)) - a₂ - u - s
  have key := addX_mul_sq (a₄ := a₄) (a₆ := a₆) (l := (w - t) / (u - s))
    (div_mul_cancel₀ _ hus) heq
  have hsr : 1 - s * r = (u - s) * r := by
    simp only [r]
    field_simp
  have key2 : x * (1 - s * r) ^ 2 = s + B * r + C * r ^ 2 - D * z := by
    rw [hsr, mul_pow, ← mul_assoc, key]
    simp only [z, r]
    field_simp
    ring
  have hunit : v (1 - s * r) = 1 := by
    apply Valuation.map_one_sub_of_lt
    rw [map_mul]
    exact (mul_le_of_le_one_left' (hle s hs)).trans_lt hr
  have hrhs : s + B * r + C * r ^ 2 - D * z ∈ W := by
    have hB : B ∈ W := add_mem (sub_mem (add_mem h₄ (pow_mem hs 2)) (mul_mem h₁ ht))
      (add_mem (mul_mem h₂ hs) (mul_mem h₂ hs))
    have hC : C ∈ W := sub_mem (sub_mem (add_mem (add_mem h₆ (pow_mem ht 2))
      (mul_mem (mul_mem h₁ ht) hs)) (pow_mem hs 3)) (mul_mem h₂ (pow_mem hs 2))
    have hD : D ∈ W := add_mem (add_mem (add_mem h₃ ht) ht) (mul_mem h₁ hs)
    exact sub_mem (add_mem (add_mem hs (mul_mem hB hrW)) (mul_mem hC (pow_mem hrW 2)))
      (mul_mem hD hzW)
  rw [← W.valuation_le_one_iff]
  have h2 := congrArg v key2
  rw [map_mul, map_pow, hunit, one_pow, mul_one] at h2
  rw [h2]
  exact hle _ hrhs

end Algebra

variable {k K : Type u} [Field k] [Field K] [Algebra k K] (E : WeierstrassCurve k)

open scoped Classical in
/-- A `k`-rational point as a point over `K`. -/
abbrev baseK (T : E.toAffine.Point) : (E⁄K).toAffine.Point := pointMap E (algebraMap k K) T

/-- **`x(P) ∉ W`**: the point `P` is affine and its `x`-coordinate is not in the valuation subring
`W` (for `W ⊇ k`: `P` reduces to the origin at `W`). -/
def IsPole (W : ValuationSubring K) : (E⁄K).toAffine.Point → Prop
  | .zero => False
  | .some x _ _ => x ∉ W

variable {E}

lemma isPole_some (W : ValuationSubring K) {x y : K} (h : (E⁄K).toAffine.Nonsingular x y) :
    IsPole E W (.some x y h) ↔ x ∉ W := Iff.rfl

lemma not_isPole_zero (W : ValuationSubring K) : ¬ IsPole E W 0 := id

open scoped Classical in
/-- Negation does not change the `x`-coordinate. -/
lemma isPole_neg (W : ValuationSubring K) (P : (E⁄K).toAffine.Point) :
    IsPole E W (-P) ↔ IsPole E W P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact Iff.rfl
  · exact Iff.rfl

open scoped Classical in
lemma isPole_zsmul_sign (W : ValuationSubring K) (P : (E⁄K).toAffine.Point) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) : IsPole E W (ε • P) ↔ IsPole E W P := by
  rcases hε with rfl | rfl
  · rw [one_zsmul]
  · rw [neg_one_zsmul, isPole_neg]

open scoped Classical in
/-- **A pole plus a nonzero `k`-rational point is affine with integral `x`-coordinate**
(`addX_mem`). -/
theorem not_isPole_add_base {W : ValuationSubring K} (hk : ∀ c : k, algebraMap k K c ∈ W)
    {P : (E⁄K).toAffine.Point} (hP : IsPole E W P) {T : E.toAffine.Point} (hT : T ≠ 0) :
    ¬ IsPole E W (P + baseK E T) ∧ P + baseK E T ≠ 0 := by
  rcases P with _ | ⟨u, w, hP'⟩
  · exact absurd hP id
  rcases T with _ | ⟨s, t, hT'⟩
  · exact absurd rfl hT
  have hu : u ∉ W := hP
  have hS' : (E⁄K).toAffine.Nonsingular (algebraMap k K s) (algebraMap k K t) :=
    (E.toAffine.map_nonsingular (algebraMap k K).injective s t).mpr hT'
  have hx : u ≠ algebraMap k K s := fun h => hu (h ▸ hk s)
  change ¬ IsPole E W (Affine.Point.some u w hP' + Affine.Point.some _ _ hS') ∧
    Affine.Point.some u w hP' + Affine.Point.some _ _ hS' ≠ 0
  rw [Affine.Point.add_of_X_ne hx]
  refine ⟨?_, Affine.Point.some_ne_zero _⟩
  rw [isPole_some, not_not, Affine.addX, Affine.slope_of_X_ne hx]
  exact addX_mem W (hk E.a₁) (hk E.a₂) (hk E.a₃) (hk E.a₄) (hk E.a₆) (hk s) (hk t) hu
    ((Affine.equation_iff _ _).1 hP'.1)

end Pole


/-! ### Transcendence of the division points -/

section Transcendence

/-- Rewriting the `x`-coordinate of an affine point. -/
lemma exists_some_eq {F : Type*} [Field F] {W : WeierstrassCurve F} {x x' y : F} (hx : x = x')
    (h : W.toAffine.Nonsingular x y) :
    ∃ h' : W.toAffine.Nonsingular x' y, Affine.Point.some x y h = Affine.Point.some x' y h' := by
  subst hx
  exact ⟨h, rfl⟩

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

open Polynomial

open scoped Classical in
/-- **An `ℓ`-division point of the generic point has transcendental `x`-coordinate**: if
`ℓ P = G` then `x(P)` is not algebraic over `k` (`x(G) ΨSq_ℓ(x(P)) = Φ_ℓ(x(P))` in the model with
`a₁ = a₃ = 0`, which has the same `x`-coordinates). -/
theorem transcendental_x_of_nsmul {ℓ : ℕ} {a b : Ω E} (h : (E⁄(Ω E)).toAffine.Nonsingular a b)
    (hP : ℓ • (Affine.Point.some a b h : Pt E) = Genuine.genericPoint E) : Transcendental k a := by
  intro halg
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
  have hxG : xG E = (((shortModel E)⁄(Ω E)).toAffine.Φ ℓ).eval a /
      (((shortModel E)⁄(Ω E)).toAffine.ΨSq ℓ).eval a := by
    rw [← hXG]
    exact eq_div_of_mul_eq hne hX
  have ha : a ∈ algebraicClosure k (Ω E) := (mem_algebraicClosure_iff).2 halg
  have hpoly : ∀ p : k[X], (p.map (algebraMap k (Ω E))).eval a ∈ algebraicClosure k (Ω E) :=
    fun p => by
      rw [eval_map_algebraMap, show a = IntermediateField.val _ (⟨a, ha⟩ :
        algebraicClosure k (Ω E)) from rfl, aeval_algHom_apply]
      exact SetLike.coe_mem _
  have hmem : xG E ∈ algebraicClosure k (Ω E) := by
    rw [hxG]
    refine div_mem ?_ ?_
    · rw [show ((shortModel E)⁄(Ω E)).toAffine.Φ ℓ = ((shortModel E).Φ ℓ).map
        (algebraMap k (Ω E)) from map_Φ _ _ _]
      exact hpoly _
    · rw [show ((shortModel E)⁄(Ω E)).toAffine.ΨSq ℓ = ((shortModel E).ΨSq ℓ).map
        (algebraMap k (Ω E)) from map_ΨSq _ _ _]
      exact hpoly _
  exact transcendental_xG E ((mem_algebraicClosure_iff).1 hmem)

end Transcendence

/-! ### Places over the cusps -/

section Places

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

open scoped Classical in
/-- **The action of `Gal(Ω / k(x))` on places**: `σ(W) = {a | σ⁻¹ a ∈ W}`. -/
def placeSmul (σ : Gal E) (W : ValuationSubring (Ω E)) : ValuationSubring (Ω E) :=
  W.comap ((σ.symm : Ω E ≃ₐ[baseField E] Ω E) : Ω E →+* Ω E)

variable {E}

open scoped Classical in
omit [CharZero k] [E.IsElliptic] in
lemma mem_placeSmul {σ : Gal E} {W : ValuationSubring (Ω E)} {a : Ω E} :
    a ∈ placeSmul E σ W ↔ σ.symm a ∈ W := Iff.rfl

variable (E) in
open scoped Classical in
/-- `W` contains the base field `k`. -/
def ContainsBase (W : ValuationSubring (Ω E)) : Prop := ∀ c : k, algebraMap k (Ω E) c ∈ W

open scoped Classical in
omit [CharZero k] [E.IsElliptic] in
lemma containsBase_placeSmul (σ : Gal E) {W : ValuationSubring (Ω E)}
    (h : ContainsBase E W) : ContainsBase E (placeSmul E σ W) := fun c => by
  rw [mem_placeSmul]
  have e : σ.symm (algebraMap k (Ω E) c) = algebraMap k (Ω E) c :=
    σ.symm.commutes' ⟨_, (baseField E).algebraMap_mem c⟩
  rw [e]
  exact h c

open scoped Classical in
omit [CharZero k] [E.IsElliptic] in
/-- `σ` maps a pole of `W` to a pole of `σ(W)`. -/
lemma isPole_act (σ : Gal E) {W : ValuationSubring (Ω E)} {P : Pt E} (h : IsPole E W P) :
    IsPole E (placeSmul E σ W) (act E σ P) := by
  rcases P with _ | ⟨x, y, hxy⟩
  · exact h
  · change σ x ∉ placeSmul E σ W
    rw [mem_placeSmul, AlgEquiv.symm_apply_apply]
    exact h

variable (E) in
open scoped Classical in
/-- **`W` lies over the cusp of `T ∈ E(k)`** at level `ℓ`: `W ⊇ k` and `Q_ℓ − T` reduces to the
origin at `W` (`x(Q_ℓ − T) ∉ W`). -/
def IsCuspPlace (ℓ : ℕ) (T : E.toAffine.Point) (W : ValuationSubring (Ω E)) : Prop :=
  ContainsBase E W ∧ IsPole E W (Qpt E ℓ - base E T)

open scoped Classical in
omit [CharZero k] in
/-- **A place lies over at most one cusp.** -/
theorem isCuspPlace_unique {ℓ : ℕ} {T T' : E.toAffine.Point} {W : ValuationSubring (Ω E)}
    (h : IsCuspPlace E ℓ T W) (h' : IsCuspPlace E ℓ T' W) : T = T' := by
  by_contra hne
  apply (not_isPole_add_base h.1 h.2 (sub_ne_zero.2 hne)).1
  have e : Qpt E ℓ - base E T + baseK E (T - T') = Qpt E ℓ - base E T' := by
    change _ + base E (T - T') = _
    rw [map_sub]
    abel
  rw [e]
  exact h'.2

open scoped Classical in
omit [CharZero k] in
/-- **Galois transport of cuspidal places**: if `σ(Q_ℓ) = ε Q_ℓ + S` (`ε = ±1`, `S ∈ E(k)`), then
`σ` maps a place over `T` to a place over `ε (T − S)`. -/
theorem isCuspPlace_smul {ℓ : ℕ} {σ : Gal E} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {S : E.toAffine.Point} (hσ : act E σ (Qpt E ℓ) = ε • Qpt E ℓ + base E S)
    {T : E.toAffine.Point} {W : ValuationSubring (Ω E)} (h : IsCuspPlace E ℓ T W) :
    IsCuspPlace E ℓ (ε • (T - S)) (placeSmul E σ W) := by
  refine ⟨containsBase_placeSmul σ h.1, ?_⟩
  have e : act E σ (Qpt E ℓ - base E T) = ε • (Qpt E ℓ - base E (ε • (T - S))) := by
    rw [map_sub, hσ, act_base, map_zsmul, map_sub]
    rcases hε with rfl | rfl
    · simp only [one_zsmul]
      abel
    · simp only [neg_one_zsmul, neg_sub]
      abel
  have h2 := isPole_act σ h.2
  rw [e, isPole_zsmul_sign _ _ hε] at h2
  exact h2

open scoped Classical in
/-- **Over every `ℓ`-torsion point lies a cuspidal place** (`x(Q_ℓ − T)` is transcendental over
`k`, so `k[1/x]` has the proper ideal `(1/x)`, which is dominated by a valuation subring). -/
theorem exists_isCuspPlace {ℓ : ℕ} (hℓ : ℓ ≠ 0) {T : E.toAffine.Point}
    (hT : ℓ • T = 0) : ∃ W, IsCuspPlace E ℓ T W := by
  have hP : ℓ • (Qpt E ℓ - base E T) = Genuine.genericPoint E := by
    rw [nsmul_sub, ← map_nsmul, hT, map_zero, sub_zero, GenuineBaseChange.nsmul_Qpt E hℓ]
  rcases hQ : Qpt E ℓ - base E T with _ | ⟨a, b, hab⟩
  · rw [hQ] at hP
    change ℓ • (0 : Pt E) = _ at hP
    rw [nsmul_zero] at hP
    exact absurd hP.symm (Affine.Point.some_ne_zero _)
  rw [hQ] at hP
  have htr := transcendental_x_of_nsmul E hab hP
  have ha0 : a ≠ 0 := fun h0 => htr (h0 ▸ isAlgebraic_zero)
  have hbtr : Transcendental k a⁻¹ := fun h => htr (IsAlgebraic.inv_iff.1 h)
  let A := (Algebra.adjoin k {a⁻¹}).toSubring
  let ainv : A := ⟨a⁻¹, Algebra.subset_adjoin rfl⟩
  have hI : Ideal.span {ainv} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    rintro ⟨u, hu⟩
    obtain ⟨c, hc⟩ := u.isUnit.exists_right_inv
    have hcmem : (c : Ω E) ∈ Algebra.adjoin k {a⁻¹} := c.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hcmem
    obtain ⟨q, hq⟩ := hcmem
    have e : ((u : A) : Ω E) * c = 1 := congrArg Subtype.val hc
    rw [hu] at e
    apply hbtr
    refine ⟨Polynomial.X * q - 1, fun h0 => ?_, ?_⟩
    · have := congrArg (Polynomial.coeff · 0) h0
      simp at this
    · simp only [map_sub, map_mul, Polynomial.aeval_X, map_one]
      change a⁻¹ * (Polynomial.aeval a⁻¹ q) - 1 = 0
      rw [show (Polynomial.aeval a⁻¹) q = (c : Ω E) from hq, ← e]
      exact sub_self _
  obtain ⟨V, hAV, hV⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  refine ⟨V, fun c => hAV (Subalgebra.algebraMap_mem _ c), ?_⟩
  rw [hQ]
  change a ∉ V
  have hmem : a⁻¹ ∈ V.nonunits := hV ⟨ainv, Ideal.subset_span rfl, rfl⟩
  exact (V.inv_mem_nonunits_iff.mp hmem).resolve_left ha0

end Places

/-! ### Cusps of a model orbicurve from its cuspidal places -/

section Orbicurve

variable {k : Type u} [Field k] [CharZero k] (X : Orbicurve k)

open scoped Classical in
/-- **A cuspidal place of the model orbicurve `X = (E, ℓ, M, ±)`**: a place `W` of `Ω` together with
a point `T ∈ E(k)[ℓ]` such that `W` lies over the cusp of `T`. -/
def CuspPlace : Type u :=
  {p : ValuationSubring (Ω X.E) × X.torsion // IsCuspPlace X.E X.level p.2 p.1}

variable {X} in
/-- The place. -/
def CuspPlace.W (c : CuspPlace X) : ValuationSubring (Ω X.E) := c.1.1

variable {X} in
/-- The `ℓ`-torsion point below the place. -/
def CuspPlace.T (c : CuspPlace X) : X.torsion := c.1.2

variable {X} in
open scoped Classical in
omit [CharZero k] in
lemma CuspPlace.isCusp (c : CuspPlace X) : IsCuspPlace X.E X.level c.T c.W := c.2

variable {X}

open scoped Classical in
/-- **The cusp of `X` under a cuspidal place**: the class of `T` in `Cusp(X)` (`Q`, or `Q/{±1}`). -/
def CuspPlace.cusp (c : CuspPlace X) : X.Cusp := X.cuspOf (X.toQ c.T)

open scoped Classical in
omit [CharZero k] in
/-- The torsion point below a place is determined by the place. -/
lemma CuspPlace.T_eq_of_W_eq {c c' : CuspPlace X} (h : c.W = c'.W) : c.T = c'.T :=
  Subtype.ext (isCuspPlace_unique c.isCusp (h ▸ c'.isCusp))

open scoped Classical in
omit [CharZero k] in
/-- **The cusp under a place is invariant under `Aut(Ω / F_X)`** (`Hgp`): `σ(Q_ℓ) = ±Q_ℓ + m`
with `m ∈ M`, and `σ(W)` lies over `±(T − m)`, which has the same class in `Cusp(X)`. -/
theorem CuspPlace.cusp_eq_of_smul (hℓ : X.level ≠ 0) {c c' : CuspPlace X} {σ : Gal X.E}
    (hσ : σ ∈ Hgp X.E X.level X.M X.pm) (h : c'.W = placeSmul X.E σ c.W) :
    c'.cusp = c.cusp := by
  obtain ⟨ε, hε, hm⟩ := hσ
  obtain ⟨m, ⟨hmM, hmt⟩, hm'⟩ := hm
  have he : effLevel X.level = X.level := if_neg hℓ
  rw [he] at hmt
  have hσQ : act X.E σ (Qpt X.E X.level) = ε • Qpt X.E X.level + base X.E m := by
    rw [hm']
    abel
  have hε' : ε = 1 ∨ ε = -1 := hε.imp_right And.right
  have h2 := isCuspPlace_smul hε' hσQ c.isCusp
  rw [← h] at h2
  let m' : X.torsion := ⟨m, hmt⟩
  have hT : c'.T = ε • (c.T - m') :=
    Subtype.ext (by rw [isCuspPlace_unique c'.isCusp h2]; simp [m'])
  have hm0 : X.toQ m' = 0 := (QuotientAddGroup.eq_zero_iff _).2 hmM
  unfold CuspPlace.cusp
  rw [hT, map_zsmul, map_sub, hm0, sub_zero]
  rcases hε with rfl | ⟨hpm, rfl⟩
  · rw [one_zsmul]
  · rw [neg_one_zsmul]
    exact X.cuspOf_neg hpm _

open scoped Classical in
/-- **Every cusp of `X` lies under a cuspidal place.** -/
theorem CuspPlace.cusp_surjective (hℓ : X.level ≠ 0) :
    Function.Surjective (CuspPlace.cusp : CuspPlace X → X.Cusp) := by
  intro c
  obtain ⟨q, rfl⟩ := Quot.exists_rep c
  obtain ⟨T, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hT : X.level • (T : X.E.toAffine.Point) = 0 :=
    (AddSubgroup.torsionBy.nsmul_iff (A := X.E.toAffine.Point)).1 T.2
  obtain ⟨W, hW⟩ := exists_isCuspPlace hℓ hT
  exact ⟨⟨(W, T), hW⟩, rfl⟩

end Orbicurve

/-! ### Cuspidal inertia and decomposition groups -/

section Groups

variable {P Ω : Type u} [Field P] [Field Ω] [Algebra P Ω] [IsGalois P Ω]
  {H : Subgroup (Ω ≃ₐ[P] Ω)} {S : Set (Ω ≃ₐ[P] Ω)} {hH : IsClosed (H : Set (Ω ≃ₐ[P] Ω))}

/-- **Transport of inertia groups**: the inertia group of `ρ(W)` is the conjugate by `ρ` of that of
`W`. -/
theorem galInertia_smul (ρ : H) (W : ValuationSubring Ω) :
    galInertia H S hH (W.comap (((ρ : Ω ≃ₐ[P] Ω).symm : Ω ≃ₐ[P] Ω) : Ω →+* Ω)) =
      (galInertia H S hH W).map (MulAut.conj (galProj H S hH ρ)).toMonoidHom := by
  have hgen : (Subgroup.closure (Subtype.val ⁻¹' GaloisPi1.inertia W : Set H)).map
      (MulAut.conj ρ).toMonoidHom = Subgroup.closure (Subtype.val ⁻¹'
        GaloisPi1.inertia (W.comap (((ρ : Ω ≃ₐ[P] Ω).symm : Ω ≃ₐ[P] Ω) : Ω →+* Ω)) : Set H) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext σ
    simp only [Set.mem_image, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      GaloisPi1.mem_inertia_comap_iff]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      simpa [mul_assoc] using hτ
    · intro hσ
      exact ⟨ρ⁻¹ * σ * ρ, by simpa using hσ, by group⟩
  have hcomm : (MulAut.conj (galProj H S hH ρ)).toMonoidHom.comp (galProj H S hH) =
      (galProj H S hH).comp (MulAut.conj ρ).toMonoidHom := by
    ext σ
    simp [map_mul, map_inv]
  rw [galInertia, galInertia, Subgroup.map_map, hcomm, ← Subgroup.map_map, hgen]

/-- **Transport of decomposition groups**: the decomposition group of `ρ(W)` is the conjugate by
`ρ` of that of `W`. -/
theorem galDecomp_smul (ρ : H) (W : ValuationSubring Ω) :
    galDecomp H S hH (W.comap (((ρ : Ω ≃ₐ[P] Ω).symm : Ω ≃ₐ[P] Ω) : Ω →+* Ω)) =
      (galDecomp H S hH W).map (MulAut.conj (galProj H S hH ρ)).toMonoidHom := by
  have hgen : ((decompGal P W).subgroupOf H).map (MulAut.conj ρ).toMonoidHom =
      (decompGal P (W.comap (((ρ : Ω ≃ₐ[P] Ω).symm : Ω ≃ₐ[P] Ω) : Ω →+* Ω))).subgroupOf H := by
    ext σ
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, mem_decompGal]
    constructor
    · rintro ⟨τ, hτ, rfl⟩ x
      simp only [ValuationSubring.mem_comap, RingHom.coe_coe, Subgroup.coe_mul,
        Subgroup.coe_inv, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
      exact hτ _
    · intro hσ
      refine ⟨ρ⁻¹ * σ * ρ, fun x => ?_, by group⟩
      have := hσ ((ρ : Ω ≃ₐ[P] Ω) x)
      simp only [ValuationSubring.mem_comap, RingHom.coe_coe, AlgEquiv.symm_apply_apply] at this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, AlgEquiv.aut_inv]
      exact this
  have hcomm : (MulAut.conj (galProj H S hH ρ)).toMonoidHom.comp (galProj H S hH) =
      (galProj H S hH).comp (MulAut.conj ρ).toMonoidHom := by
    ext σ
    simp [map_mul, map_inv]
  rw [galDecomp, galDecomp, Subgroup.map_map, hcomm, ← Subgroup.map_map, hgen]

end Groups

/-! ### Cuspidal subgroups of `π₁(X)` -/

section CuspGroups

variable {k : Type u} [Field k] [CharZero k] (X : Orbicurve k)

open scoped Classical in
/-- **The cuspidal inertia group** of a cuspidal place in `π₁(X) = Aut(Ω / F_X) ⧸ ⟨⟨inertia⟩⟩`. -/
def cuspInertia (c : CuspPlace X) : Subgroup (pi1Of X.E X.level X.M X.pm) :=
  galInertia _ _ (isClosed_Hgp X.E X.level X.M X.pm) c.W

open scoped Classical in
/-- **The cuspidal decomposition group** of a cuspidal place in `π₁(X)`. -/
def cuspDecomp (c : CuspPlace X) : Subgroup (pi1Of X.E X.level X.M X.pm) :=
  galDecomp _ _ (isClosed_Hgp X.E X.level X.M X.pm) c.W

variable {X}

open scoped Classical in
omit [CharZero k] in
/-- The cuspidal inertia group lies in the cuspidal decomposition group. -/
lemma cuspInertia_le_cuspDecomp (c : CuspPlace X) : cuspInertia X c ≤ cuspDecomp X c :=
  galInertia_le_galDecomp _

open scoped Classical in
omit [CharZero k] in
/-- **Conjugate places, conjugate cuspidal groups, same cusp**: for `ρ ∈ Aut(Ω / F_X)` and
cuspidal places `c, c'` with `c'.W = ρ(c.W)`, the cuspidal inertia and decomposition groups of
`c'` are the conjugates by the image of `ρ` in `π₁(X)` of those of `c`, and `c, c'` lie over the
same cusp. So the cuspidal inertia (decomposition) groups over one `Hgp`-orbit of places form one
`π₁(X)`-conjugacy class, attached to one cusp. -/
theorem CuspPlace.conj_of_smul (hℓ : X.level ≠ 0) {c c' : CuspPlace X}
    (ρ : Hgp X.E X.level X.M X.pm) (h : c'.W = placeSmul X.E ρ c.W) :
    cuspInertia X c' = (cuspInertia X c).map
        (MulAut.conj (galProj _ _ (isClosed_Hgp X.E X.level X.M X.pm) ρ)).toMonoidHom ∧
      cuspDecomp X c' = (cuspDecomp X c).map
        (MulAut.conj (galProj _ _ (isClosed_Hgp X.E X.level X.M X.pm) ρ)).toMonoidHom ∧
      c'.cusp = c.cusp := by
  refine ⟨?_, ?_, CuspPlace.cusp_eq_of_smul hℓ ρ.2 h⟩
  · rw [cuspInertia, h]
    exact galInertia_smul ρ c.W
  · rw [cuspDecomp, h]
    exact galDecomp_smul ρ c.W

end CuspGroups

/-! ### The models `D^⊚`, `D^⊚±`: labels of cuspidal places -/

section Labels

open scoped Classical in
/-- The prime `ℓ` of initial Θ-data is an odd prime (as in `LabCuspModel`). -/
local instance oddPrimeEllCusp (D : InitialThetaData.{u}) : HodgeTheater.OddPrime D.ℓ :=
  ⟨D.prime.ℓ_prime, by have := D.prime.five_le; change 2 < D.prime.ℓ; omega⟩

/-- The classical decidable equality on `K` (as in `LabCuspModel`). -/
local instance (priority := high) instDecidableEqKCusp (D : InitialThetaData.{u}) :
    DecidableEq ↥D.prime.torsionField :=
  fun a b => Classical.propDecidable (a = b)

variable (D : InitialThetaData.{0})

open scoped Classical in
/-- The level of `C̲_K` is `ℓ ≠ 0`. -/
lemma CKu_level_ne_zero : D.orb.CKu.level ≠ 0 := by
  rw [D.orb.CKu_type.2.1]
  exact D.orb.CKu_type.1.ne_zero

open scoped Classical in
/-- The level of `X̲_K` is `ℓ ≠ 0`. -/
lemma XKu_level_ne_zero : D.orb.XKu.level ≠ 0 := by
  rw [D.orb.XKu_type.2.1]
  exact D.orb.XKu_type.1.ne_zero

variable {D}

open scoped Classical in
/-- **The label of a cuspidal place of `C̲_K` over a nonzero cusp**: its element of
`LabCusp(D^⊚)` (IUT I, Definition 4.1 (v)). -/
def labOfPlace (c : CuspPlace D.orb.CKu) (hc : c.cusp ≠ D.orb.CKu.cuspOf 0) :
    (labCuspCirc D).carrier :=
  ⟨c.cusp, hc⟩

open scoped Classical in
/-- **`Aut(Ω / F_{C̲_K})`-conjugate cuspidal places of `C̲_K` have the same label.** -/
theorem labOfPlace_smul {c c' : CuspPlace D.orb.CKu} {σ : Gal D.orb.CKu.E}
    (hσ : σ ∈ Hgp D.orb.CKu.E D.orb.CKu.level D.orb.CKu.M D.orb.CKu.pm)
    (h : c'.W = placeSmul D.orb.CKu.E σ c.W) (hc : c.cusp ≠ D.orb.CKu.cuspOf 0) :
    ∃ hc' : c'.cusp ≠ D.orb.CKu.cuspOf 0, labOfPlace c' hc' = labOfPlace c hc := by
  have e := CuspPlace.cusp_eq_of_smul (CKu_level_ne_zero D) hσ h
  exact ⟨e ▸ hc, Subtype.ext e⟩

open scoped Classical in
/-- **Every element of `LabCusp(D^⊚)` is the label of a cuspidal place.** -/
theorem labOfPlace_surjective (l : (labCuspCirc D).carrier) :
    ∃ (c : CuspPlace D.orb.CKu) (hc : c.cusp ≠ D.orb.CKu.cuspOf 0), labOfPlace c hc = l := by
  obtain ⟨c, hc⟩ := CuspPlace.cusp_surjective (CKu_level_ne_zero D) l.1
  exact ⟨c, hc ▸ l.2, Subtype.ext hc⟩

open scoped Classical in
/-- **The `±`-label of a cuspidal place of `X̲_K`**: its element of `LabCusp^±(D^⊚±)` (IUT I,
Definition 6.1 (vi): the cusps of `X̲_K`). Conjugate places have the same `±`-label
(`CuspPlace.cusp_eq_of_smul`), and every `±`-label arises (`CuspPlace.cusp_surjective`). -/
def labPmOfPlace (c : CuspPlace D.orb.XKu) : (labCuspPmCirc D).carrier := c.cusp

open scoped Classical in
theorem labPmOfPlace_surjective : Function.Surjective (labPmOfPlace (D := D)) :=
  CuspPlace.cusp_surjective (XKu_level_ne_zero D)

end Labels

end Iut.Multiradial.Theater
