/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.MulByNTorsion
import EllipticCurves.Torsion.DoublingCoords
import EllipticCurves.Torsion.TwoTorsionSplittingField

/-!
# Inertia over the cusp fixes the source `L_2` of `[2]` (MR14, run 16)

Let `E` be an elliptic curve over a field `K` of characteristic `0`, `Ω = K(Ē)^alg`, `τ = x`,
`L_X = K(E) ⊆ Ω` and `L_2 = mulByNField E 2` the source of `[2] : E → E` (`MulByNGalois.lean`).
For a place `W ⊇ K` of `Ω` over the cusp (`τ ∉ W`) and an inertia element `σ` of `W` fixing `L_X`
(`σ(z) − z ∈ 𝔪_W` for `z ∈ W`), `σ` fixes `L_2` (`fix_mulByNField_two`): the isogeny `[2]` is
unramified over the cusp `O`.

## The argument (a Hensel-type lemma, no reduction map needed)

* `eq_of_quartic`: if `f = c₀ + c₁X + ⋯ + c₄X⁴` has `c₂, c₃, c₄ ∈ W`, `f(z) = f(w) = 0` with
  `z, w ∈ W`, `f′(z)` a unit and `w ≡ z mod 𝔪_W`, then `w = z`
  (`f(w) − f(z) = (w − z)(f′(z) + (w − z)T)` with `T ∈ W`).
* `P = ptM E 2 = (a, b)` satisfies `2P = P_X = (τ, y)`, so by the duplication formula
  (`addX_self_eq_div`) `Φ₂(a) = τ Ψ₂Sq(a)`, and so does `σa` (`σ` fixes `K` and `τ`).
  - If `a ∈ W`: `f = τ⁻¹Φ₂ − Ψ₂Sq ∈ W[X]`; `Ψ₂Sq(a) = τ⁻¹Φ₂(a) ∈ 𝔪_W`, and since `Ψ₂Sq ∈ K[X]` is
    separable (`separable_Ψ₂Sq`; `E` is elliptic), `Ψ₂Sq′(a)` and hence `f′(a)` is a unit.
  - If `a ∉ W`: `z = a⁻¹ ∈ 𝔪_W` is a root of the reversed `X⁴(Ψ₂Sq − τ⁻¹Φ₂)(1/X)`, whose
    derivative at `z` is `≡ 4 mod 𝔪_W`, a unit.
  In both cases `σa = a` (`eq_of_doubling`).
* Then `σP = ±P`; `σP = −P` would give `P_X = 2σP = −P_X`, impossible since `2P_X ≠ 0`. So
  `σP = P`, i.e. `σ` fixes the generators `mulByNEmb 2 x`, `mulByNEmb 2 y` of `L_2`.

The ramification input is read off the duplication formula itself: `Ψ₂Sq` has simple roots and
`deg Φ₂ = deg Ψ₂Sq + 1`, so `τ = Φ₂(a)/Ψ₂Sq(a)` has a simple pole in `a` (resp. in `1/a`) at each
cusp of `Ÿ'_2`. No order computation on `E_Q` (`ThetaCuspMain.lean`) and no reduction map of
`elliptic-curves` (which needs a complete DVR, while `W` is a valuation ring of `Ω = K(Ē)^alg`)
is used.
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open IntermediateField AffOrbicurve

noncomputable section

universe u

namespace CurvesJacobian.Cusp

/-! ### A Hensel-type uniqueness lemma -/

section Hensel

variable {Ω : Type*} [Field Ω] (W : ValuationSubring Ω)

lemma val_mul_lt_one {x y : Ω} (hx : W.valuation x < 1) (hy : y ∈ W) :
    W.valuation (x * y) < 1 := by
  rw [map_mul]
  calc W.valuation x * W.valuation y ≤ W.valuation x * 1 :=
        mul_le_mul_right ((W.valuation_le_one_iff y).2 hy) _
    _ = W.valuation x := mul_one _
    _ < 1 := hx

lemma val_add_eq_one {x y : Ω} (hx : W.valuation x = 1) (hy : W.valuation y < 1) :
    W.valuation (x + y) = 1 := by
  rw [Valuation.map_add_eq_of_lt_left _ (hx ▸ hy), hx]

lemma val_eq_one_of_mul {x y : Ω} (hx : x ∈ W) (hy : y ∈ W) (h : W.valuation (x * y) = 1) :
    W.valuation y = 1 := by
  rw [map_mul] at h
  refine le_antisymm ((W.valuation_le_one_iff y).2 hy) ?_
  calc (1 : W.ValueGroup) = W.valuation x * W.valuation y := h.symm
    _ ≤ 1 * W.valuation y := mul_le_mul_left ((W.valuation_le_one_iff x).2 hx) _
    _ = W.valuation y := one_mul _

lemma inv_mem_of_not_mem {x : Ω} (hx : x ∉ W) : x⁻¹ ∈ W :=
  (W.mem_or_inv_mem x).resolve_left hx

lemma val_inv_lt_one {x : Ω} (hx : x ∉ W) : W.valuation x⁻¹ < 1 := by
  refine lt_of_le_of_ne ((W.valuation_le_one_iff _).2 (inv_mem_of_not_mem W hx)) fun h => hx ?_
  rw [← W.valuation_le_one_iff, ← inv_inv x, map_inv₀, h, inv_one]

/-- **Hensel uniqueness for a quartic**: if `f = c₀ + c₁X + c₂X² + c₃X³ + c₄X⁴` has
`c₂, c₃, c₄ ∈ W`, vanishes at `z, w ∈ W`, `f′(z)` is a unit of `W` and `w ≡ z mod 𝔪_W`, then
`w = z`. -/
theorem eq_of_quartic {c₀ c₁ c₂ c₃ c₄ z w : Ω} (h₂ : c₂ ∈ W) (h₃ : c₃ ∈ W) (h₄ : c₄ ∈ W)
    (hz : z ∈ W) (hw : w ∈ W)
    (hfz : c₀ + c₁ * z + c₂ * z ^ 2 + c₃ * z ^ 3 + c₄ * z ^ 4 = 0)
    (hfw : c₀ + c₁ * w + c₂ * w ^ 2 + c₃ * w ^ 3 + c₄ * w ^ 4 = 0)
    (hD : W.valuation (c₁ + 2 * c₂ * z + 3 * c₃ * z ^ 2 + 4 * c₄ * z ^ 3) = 1)
    (hzw : W.valuation (w - z) < 1) : w = z := by
  have hT : c₂ + c₃ * (w + z + z) + c₄ * (w * w + w * z + w * z + z * z + z * z + z * z) ∈ W :=
    add_mem (add_mem h₂ (mul_mem h₃ (add_mem (add_mem hw hz) hz)))
      (mul_mem h₄ (add_mem (add_mem (add_mem (add_mem (add_mem (mul_mem hw hw) (mul_mem hw hz))
        (mul_mem hw hz)) (mul_mem hz hz)) (mul_mem hz hz)) (mul_mem hz hz)))
  have hS := val_add_eq_one W hD (val_mul_lt_one W hzw hT)
  have key : (w - z) * ((c₁ + 2 * c₂ * z + 3 * c₃ * z ^ 2 + 4 * c₄ * z ^ 3) + (w - z) *
      (c₂ + c₃ * (w + z + z) + c₄ * (w * w + w * z + w * z + z * z + z * z + z * z))) = 0 := by
    linear_combination hfw - hfz
  rcases mul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · rw [h, map_zero] at hS
    exact absurd hS zero_ne_one

/-- **Hensel for the duplication relation** `Φ₂(x) = τ Ψ₂Sq(x)` at a place with `τ ∉ W`
(`Φ₂ = X⁴ − b₄X² − 2b₆X − b₈`, `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`): two roots `a, a'` that are
congruent (`a ≡ a'` if `a ∈ W`, `a⁻¹ ≡ a'⁻¹` otherwise) are equal, provided `Ψ₂Sq` stays
separable modulo `𝔪_W` (`hsep`). -/
theorem eq_of_doubling {B₂ B₄ B₆ B₈ τ a a' : Ω} (h₂ : B₂ ∈ W) (h₄ : B₄ ∈ W) (h₆ : B₆ ∈ W)
    (h₈ : B₈ ∈ W) (hfour : W.valuation 4 = 1) (hτ : τ ∉ W)
    (hsep : ∀ x ∈ W, W.valuation (4 * x ^ 3 + B₂ * x ^ 2 + 2 * B₄ * x + B₆) < 1 →
      W.valuation (12 * x ^ 2 + 2 * B₂ * x + 2 * B₄) = 1)
    (hrel : a ^ 4 - B₄ * a ^ 2 - 2 * B₆ * a - B₈ = τ * (4 * a ^ 3 + B₂ * a ^ 2 + 2 * B₄ * a + B₆))
    (hrel' : a' ^ 4 - B₄ * a' ^ 2 - 2 * B₆ * a' - B₈ =
      τ * (4 * a' ^ 3 + B₂ * a' ^ 2 + 2 * B₄ * a' + B₆))
    (hin : a ∈ W → a' ∈ W ∧ W.valuation (a' - a) < 1)
    (hin' : a ∉ W → a'⁻¹ ∈ W ∧ W.valuation (a'⁻¹ - a⁻¹) < 1) (ha' : a ∉ W → a' ≠ 0) :
    a' = a := by
  have hτi := inv_mem_of_not_mem W hτ
  have hτv := val_inv_lt_one W hτ
  have hτ0 : τ ≠ 0 := fun h => hτ (h ▸ W.zero_mem)
  have hinv : τ⁻¹ * τ = 1 := inv_mul_cancel₀ hτ0
  have h2 : (2 : Ω) ∈ W := natCast_mem W 2
  have h3 : (3 : Ω) ∈ W := natCast_mem W 3
  have h4 : (4 : Ω) ∈ W := natCast_mem W 4
  by_cases ha : a ∈ W
  · obtain ⟨ha'W, hv⟩ := hin ha
    have hroot : ∀ x : Ω, x ^ 4 - B₄ * x ^ 2 - 2 * B₆ * x - B₈ =
        τ * (4 * x ^ 3 + B₂ * x ^ 2 + 2 * B₄ * x + B₆) →
        (-(τ⁻¹ * B₈) - B₆) + (-(2 * τ⁻¹ * B₆) - 2 * B₄) * x + (-(τ⁻¹ * B₄) - B₂) * x ^ 2 +
          (-4) * x ^ 3 + τ⁻¹ * x ^ 4 = 0 := fun x hx => by
      linear_combination τ⁻¹ * hx + (4 * x ^ 3 + B₂ * x ^ 2 + 2 * B₄ * x + B₆) * hinv
    refine eq_of_quartic W (sub_mem (neg_mem (mul_mem hτi h₄)) h₂) (neg_mem h4) hτi ha ha'W
      (hroot a hrel) (hroot a' hrel') ?_ hv
    have hΦ : a ^ 4 - B₄ * a ^ 2 - 2 * B₆ * a - B₈ ∈ W :=
      sub_mem (sub_mem (sub_mem (pow_mem ha 4) (mul_mem h₄ (pow_mem ha 2)))
        (mul_mem (mul_mem h2 h₆) ha)) h₈
    have hΨ : W.valuation (4 * a ^ 3 + B₂ * a ^ 2 + 2 * B₄ * a + B₆) < 1 := by
      have e : 4 * a ^ 3 + B₂ * a ^ 2 + 2 * B₄ * a + B₆ =
          τ⁻¹ * (a ^ 4 - B₄ * a ^ 2 - 2 * B₆ * a - B₈) := by
        rw [hrel, ← mul_assoc, hinv, one_mul]
      rw [e]
      exact val_mul_lt_one W hτv hΦ
    have hd := hsep a ha hΨ
    have e : (-(2 * τ⁻¹ * B₆) - 2 * B₄) + 2 * (-(τ⁻¹ * B₄) - B₂) * a + 3 * (-4) * a ^ 2 +
        4 * τ⁻¹ * a ^ 3 = -(12 * a ^ 2 + 2 * B₂ * a + 2 * B₄) +
          τ⁻¹ * (4 * a ^ 3 - 2 * B₄ * a - 2 * B₆) := by ring
    rw [e]
    refine val_add_eq_one W (by rw [Valuation.map_neg]; exact hd) (val_mul_lt_one W hτv ?_)
    exact sub_mem (sub_mem (mul_mem h4 (pow_mem ha 3)) (mul_mem (mul_mem h2 h₄) ha))
      (mul_mem h2 h₆)
  · obtain ⟨hz'W, hv⟩ := hin' ha
    have hzW := inv_mem_of_not_mem W ha
    have hzv := val_inv_lt_one W ha
    have ha0 : a ≠ 0 := fun h => ha (h ▸ W.zero_mem)
    have hroot : ∀ x : Ω, x ≠ 0 → x ^ 4 - B₄ * x ^ 2 - 2 * B₆ * x - B₈ =
        τ * (4 * x ^ 3 + B₂ * x ^ 2 + 2 * B₄ * x + B₆) →
        -τ⁻¹ + 4 * x⁻¹ + (B₂ + τ⁻¹ * B₄) * x⁻¹ ^ 2 + (2 * B₄ + 2 * τ⁻¹ * B₆) * x⁻¹ ^ 3 +
          (B₆ + τ⁻¹ * B₈) * x⁻¹ ^ 4 = 0 := fun x hx0 hx => by
      have hxi : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
      have e : -τ⁻¹ + 4 * x⁻¹ + (B₂ + τ⁻¹ * B₄) * x⁻¹ ^ 2 + (2 * B₄ + 2 * τ⁻¹ * B₆) * x⁻¹ ^ 3 +
          (B₆ + τ⁻¹ * B₈) * x⁻¹ ^ 4 = x⁻¹ ^ 4 * ((4 * x ^ 3 + B₂ * x ^ 2 + 2 * B₄ * x + B₆) -
            τ⁻¹ * (x ^ 4 - B₄ * x ^ 2 - 2 * B₆ * x - B₈)) := by
        field_simp
        ring
      rw [e, hx, ← mul_assoc τ⁻¹, hinv, one_mul, sub_self, mul_zero]
    have key := eq_of_quartic W (add_mem h₂ (mul_mem hτi h₄))
      (add_mem (mul_mem h2 h₄) (mul_mem (mul_mem h2 hτi) h₆)) (add_mem h₆ (mul_mem hτi h₈))
      hzW hz'W (hroot a ha0 hrel) (hroot a' (ha' ha) hrel') ?_ hv
    · exact inv_injective key
    · have e : 4 + 2 * (B₂ + τ⁻¹ * B₄) * a⁻¹ + 3 * (2 * B₄ + 2 * τ⁻¹ * B₆) * a⁻¹ ^ 2 +
          4 * (B₆ + τ⁻¹ * B₈) * a⁻¹ ^ 3 = 4 + a⁻¹ * (2 * (B₂ + τ⁻¹ * B₄) +
            3 * (2 * B₄ + 2 * τ⁻¹ * B₆) * a⁻¹ + 4 * (B₆ + τ⁻¹ * B₈) * a⁻¹ ^ 2) := by ring
      rw [e]
      refine val_add_eq_one W hfour (val_mul_lt_one W hzv ?_)
      exact add_mem (add_mem (mul_mem h2 (add_mem h₂ (mul_mem hτi h₄)))
        (mul_mem (mul_mem h3 (add_mem (mul_mem h2 h₄) (mul_mem (mul_mem h2 hτi) h₆))) hzW))
        (mul_mem (mul_mem h4 (add_mem h₆ (mul_mem hτi h₈))) (pow_mem hzW 2))

end Hensel

/-! ### Inertia over the cusp fixes `L_2` -/

section Inertia

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

local notation "FF" => E.toAffine.FunctionField
local notation "Ω" => FFClosure (curveE E)
local notation "τ" => coordT (xN E)
local notation "Pt" => WeierstrassCurve.Affine.Point (E.toAffine.baseChange Ω)

attribute [local instance] decEqΩ

/-- Values of `K`-polynomials at elements of `W` lie in `W` (if `K ⊆ W`). -/
lemma aeval_mem_W_of_K {W : ValuationSubring Ω} (hk : ∀ c : K, algebraMap K Ω c ∈ W) {x : Ω}
    (hx : x ∈ W) (U : K[X]) : aeval x U ∈ W := by
  induction U using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n c => rw [aeval_monomial]; exact mul_mem (hk c) (pow_mem hx n)

lemma val_algebraMap_K_eq_one {W : ValuationSubring Ω} (hk : ∀ c : K, algebraMap K Ω c ∈ W) {c : K}
    (hc : c ≠ 0) : W.valuation (algebraMap K Ω c) = 1 := by
  refine val_eq_one_of_mul W (hk c⁻¹) (hk c) ?_
  rw [← map_mul, inv_mul_cancel₀ hc, map_one, map_one]

/-- `Ψ₂Sq` stays separable modulo `𝔪_W` (`separable_Ψ₂Sq`, `E` elliptic). -/
lemma val_Ψ₂Sq_derivative {W : ValuationSubring Ω} (hk : ∀ c : K, algebraMap K Ω c ∈ W) :
    ∀ x ∈ W, W.valuation (4 * x ^ 3 + algebraMap K Ω E.b₂ * x ^ 2 +
        2 * algebraMap K Ω E.b₄ * x + algebraMap K Ω E.b₆) < 1 →
      W.valuation (12 * x ^ 2 + 2 * algebraMap K Ω E.b₂ * x + 2 * algebraMap K Ω E.b₄) = 1 := by
  intro x hx hv
  obtain ⟨U, V, hUV⟩ := WeierstrassCurve.Affine.separable_Ψ₂Sq (W := E.toAffine)
    (two_ne_zero : (2 : K) ≠ 0)
  have e := congrArg (aeval x) hUV
  have hΨ : aeval x E.toAffine.Ψ₂Sq = 4 * x ^ 3 + algebraMap K Ω E.b₂ * x ^ 2 +
      2 * algebraMap K Ω E.b₄ * x + algebraMap K Ω E.b₆ := by
    simp [WeierstrassCurve.Ψ₂Sq, map_ofNat]
  have hΨ' : aeval x (derivative E.toAffine.Ψ₂Sq) =
      12 * x ^ 2 + 2 * algebraMap K Ω E.b₂ * x + 2 * algebraMap K Ω E.b₄ := by
    simp [WeierstrassCurve.Ψ₂Sq, map_ofNat]
    ring
  rw [map_add, map_mul, map_mul, map_one, hΨ, hΨ'] at e
  have h1 : W.valuation (aeval x V * (12 * x ^ 2 + 2 * algebraMap K Ω E.b₂ * x +
      2 * algebraMap K Ω E.b₄)) = 1 := by
    have e' : aeval x V * (12 * x ^ 2 + 2 * algebraMap K Ω E.b₂ * x +
        2 * algebraMap K Ω E.b₄) = 1 + -(aeval x U * (4 * x ^ 3 + algebraMap K Ω E.b₂ * x ^ 2 +
          2 * algebraMap K Ω E.b₄ * x + algebraMap K Ω E.b₆)) := by
      rw [← e]; ring
    rw [e']
    refine val_add_eq_one W (map_one _) ?_
    rw [Valuation.map_neg, mul_comm]
    exact val_mul_lt_one W hv (aeval_mem_W_of_K E hk hx U)
  exact val_eq_one_of_mul W (aeval_mem_W_of_K E hk hx V)
    (add_mem (add_mem (mul_mem (natCast_mem W 12) (pow_mem hx 2))
      (mul_mem (mul_mem (natCast_mem W 2) (hk _)) hx)) (mul_mem (natCast_mem W 2) (hk _))) h1

/-- **Inertia over the cusp fixes `P = ptM E 2`**: for `σ ∈ Aut(Ω/K(τ))` fixing `L_X` and acting
trivially modulo `𝔪_W` on a place `W ⊇ K` with `τ ∉ W`, `σP = P`. -/
theorem act_ptM_two_of_inertia {σ : Ω ≃ₐ[K₀ K τ] Ω} (hσL : ∀ z ∈ (hemiData E).L, σ z = z)
    {W : ValuationSubring Ω} (hk : ∀ c : K, algebraMap K Ω c ∈ W) (hτ : τ ∉ W)
    (hσW : ∀ z ∈ W, W.valuation (σ z - z) < 1) : act E σ (ptM E 2) = ptM E 2 := by
  obtain ⟨h, hPdef⟩ := map_genPt E (mulByNEmb E 2)
  obtain ⟨hX, hXdef⟩ := map_genPt E (embE E)
  set a := mulByNEmb E 2 (WeierstrassCurve.Affine.CoordinateRing.genX E.toAffine) with ha_def
  set b := mulByNEmb E 2 (WeierstrassCurve.Affine.CoordinateRing.genY E.toAffine) with hb_def
  change ptM E 2 = _ at hPdef
  change ptX E = _ at hXdef
  have hτ0 : τ ≠ 0 := fun h0 => hτ (h0 ▸ W.zero_mem)
  -- the duplication relation `Φ₂(a) = τ Ψ₂Sq(a)`
  have hrel : a ^ 4 - algebraMap K Ω E.b₄ * a ^ 2 - 2 * algebraMap K Ω E.b₆ * a -
      algebraMap K Ω E.b₈ = τ * (4 * a ^ 3 + algebraMap K Ω E.b₂ * a ^ 2 +
        2 * algebraMap K Ω E.b₄ * a + algebraMap K Ω E.b₆) := by
    have h2P := nsmul_ptM E 2
    rw [hPdef, hXdef, two_nsmul] at h2P
    have hbne : b ≠ (E.toAffine.baseChange Ω).negY a b := by
      intro hb
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hb] at h2P
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ h2P.symm
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hbne,
      WeierstrassCurve.Affine.Point.some.injEq] at h2P
    have hxa := h2P.1
    rw [WeierstrassCurve.Affine.addX_self_eq_div h.1 hbne, embE_genX] at hxa
    have hΨ0 : ((E.toAffine.baseChange Ω).Ψ₂Sq).eval a ≠ 0 := by
      intro h0
      rw [h0, div_zero] at hxa
      exact hτ0 hxa.symm
    rw [div_eq_iff hΨ0] at hxa
    simpa [WeierstrassCurve.Φ_two, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
      WeierstrassCurve.map_b₈, map_ofNat] using hxa
  have hσc : ∀ c : K, σ (algebraMap K Ω c) = algebraMap K Ω c := fun c => (resK E σ).commutes c
  have hστ : σ τ = τ := hσL τ ((mem_hemiL_iff E τ).mpr ⟨_, embE_genX E⟩)
  have hrel' : σ a ^ 4 - algebraMap K Ω E.b₄ * σ a ^ 2 - 2 * algebraMap K Ω E.b₆ * σ a -
      algebraMap K Ω E.b₈ = τ * (4 * σ a ^ 3 + algebraMap K Ω E.b₂ * σ a ^ 2 +
        2 * algebraMap K Ω E.b₄ * σ a + algebraMap K Ω E.b₆) := by
    have e := congrArg σ hrel
    simpa only [map_sub, map_mul, map_pow, map_add, map_ofNat, hσc, hστ] using e
  have hmem : ∀ z ∈ W, σ z ∈ W := fun z hz => by
    have h1 : σ z - z ∈ W := (W.valuation_le_one_iff _).1 (hσW z hz).le
    simpa using add_mem h1 hz
  have hfour : W.valuation (4 : Ω) = 1 := by
    have := val_algebraMap_K_eq_one E hk (c := 4) (by norm_num)
    rwa [map_ofNat] at this
  have hσa : σ a = a := by
    refine eq_of_doubling W (hk _) (hk _) (hk _) (hk _) hfour hτ (val_Ψ₂Sq_derivative E hk) hrel
      hrel' (fun ha => ⟨hmem a ha, hσW a ha⟩) (fun ha => ?_) (fun ha => ?_)
    · have hi := inv_mem_of_not_mem W ha
      rw [← map_inv₀]
      exact ⟨hmem _ hi, hσW _ hi⟩
    · have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ W.zero_mem)
      exact (map_ne_zero σ).mpr ha0
  -- `σP = ±P`, and `σP = -P` is impossible
  obtain ⟨h', hQ⟩ : ∃ h', act E σ (ptM E 2) = WeierstrassCurve.Affine.Point.some (σ a) (σ b) h' :=
    ⟨_, by rw [hPdef]; rfl⟩
  rw [hQ, hPdef, WeierstrassCurve.Affine.Point.some.injEq]
  refine ⟨hσa, ?_⟩
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h'.1 h.1 hσa with hb | hb
  · exact hb
  exfalso
  have hneg : act E σ (ptM E 2) = -ptM E 2 := by
    rw [hQ, hPdef, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hσa, hb⟩
  have hXneg : ptX E = -ptX E := by
    calc ptX E = act E σ (ptX E) := (act_ptX E hσL).symm
      _ = act E σ (2 • ptM E 2) := by rw [nsmul_ptM]
      _ = 2 • act E σ (ptM E 2) := map_nsmul _ _ _
      _ = -(2 • ptM E 2) := by rw [hneg, smul_neg]
      _ = -ptX E := by rw [nsmul_ptM]
  have h2X : 2 • ptX E ≠ 0 := by
    rw [ptX, ← map_nsmul, nsmul_genPt, WeierstrassCurve.Affine.Point.map_map]
    obtain ⟨_, e⟩ := map_genPt E ((embE E).comp (pb E 2))
    rw [e]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
  apply h2X
  calc 2 • ptX E = ptX E + ptX E := two_nsmul _
    _ = ptX E + -ptX E := congrArg (ptX E + ·) hXneg
    _ = 0 := add_neg_cancel _

/-- **Inertia over the cusp fixes `L_2 = mulByNField E 2`** (`[2]` is unramified over `O`). -/
theorem fix_mulByNField_two {σ : Ω ≃ₐ[K₀ K τ] Ω} (hσL : ∀ z ∈ (hemiData E).L, σ z = z)
    {W : ValuationSubring Ω} (hk : ∀ c : K, algebraMap K Ω c ∈ W) (hτ : τ ∉ W)
    (hσW : ∀ z ∈ W, W.valuation (σ z - z) < 1) : ∀ z ∈ mulByNField E 2, σ z = z := by
  have hP := act_ptM_two_of_inertia E hσL hk hτ hσW
  obtain ⟨h, hPdef⟩ := map_genPt E (mulByNEmb E 2)
  change ptM E 2 = _ at hPdef
  rw [hPdef] at hP
  change WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (resK E σ) _ = _ at hP
  rw [WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.Affine.Point.some.injEq] at hP
  have hcomp : (resK E σ).comp (mulByNEmb E 2) = mulByNEmb E 2 := algHom_ext_genXY E hP.1 hP.2
  rintro z ⟨f, rfl⟩
  exact AlgHom.congr_fun hcomp f

end Inertia

end CurvesJacobian.Cusp
