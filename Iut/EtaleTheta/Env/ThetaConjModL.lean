/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.KummerConj

/-!
# Kummer classes mod `l` of units moved by `l`-th powers (MR15, 13c(iii), étale part)

[EtTh] Prop. 1.5(iii) mod `l` on `lℤ` (MR14, obligation 13c(ii)) says: an automorphism `σ` of `Ω`
lying over a translation `t_w`, `w = ±s^a`, `l ∣ a`, moves the theta level unit by an `l`-th power,
`σ(η_j) = z^l · η_j` with `z = d·y`, `d ∈ K^×`, `y` a function on the level. Then the Kummer class
of `η_j` mod `l` is invariant under conjugation by `σ`:

* `contH1_pow_eq_one`, `kummerMap_pow_eq_one`: `κ_l(z^l) = 1` (`H¹(Π_U, μ_l)` has exponent `l`);
* **`conjH1_kummerMap_of_pow`**: `conjH1 σ (κ_l(η)) = κ_l(η)` if `σ(η) = z^l·η`.

The tempered transport to `Π^tp_Ÿ` (conjugation by `e`, `g ∈ Π^tp_X̿`, through the translation
homomorphism `w_j` of 13c(i)) and the extraction of the coboundaries `me`, `mg` of
`exists_cX_of_invariant` are the remaining steps (MR15-plan, run 7 hand-off).
-/

open Pi1.Orbifold KummerTheory KummerTheory.Curve AffOrbicurve

noncomputable section

universe u

namespace Iut.EtaleTheta.Env

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {D : GaloisData k t}

variable [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω]

omit [IsSepClosed Ω] in
/-- **`H¹(Π_U, μ_l)` has exponent `l`.** -/
theorem contH1_pow_eq_one (l : ℕ) [NeZero l] (x : ContH1 (Pi D) (Mu l Ω)) : x ^ l = 1 := by
  induction x using ContH1.induction_on with
  | h c =>
    rw [← map_pow]
    convert map_one (ContH1.mk (G := Pi D) (M := Mu l Ω))
    refine Subtype.ext (funext fun g => ?_)
    change (c g) ^ l = 1
    exact Mu.ext (by rw [map_pow, Mu.val_pow_n, map_one])

/-- **`κ_l(z^l) = 1`.** -/
theorem kummerMap_pow_eq_one (l : ℕ) [NeZero l] (z : units D) : kummerMap D l (z ^ l) = 1 := by
  rw [map_pow]
  exact contH1_pow_eq_one l _

/-- **Conjugation-invariance of Kummer classes mod `l`** ([EtTh] Prop. 1.5(iii) mod `l`): if
`σ(η) = z^l · η` for a unit `z`, then `conjH1 σ (κ_l(η)) = κ_l(η)`. -/
theorem conjH1_kummerMap_of_pow {σ : Ω ≃ₐ[K₀ k t] Ω} (hH : ∀ h ∈ D.H, σ⁻¹ * h * σ ∈ D.H)
    (hHL : ∀ h ∈ D.HL, σ⁻¹ * h * σ ∈ D.HL) (l : ℕ) [NeZero l] (v z : units D)
    (hv : σ (((v : (F D)ˣ) : F D) : Ω) = ((((z ^ l * v : units D) : (F D)ˣ) : F D) : Ω)) :
    conjH1 hH hHL l (kummerMap D l v) = kummerMap D l v := by
  rw [conjH1_kummerMap hH hHL l v (z ^ l * v) hv, map_mul, kummerMap_pow_eq_one, one_mul]

end Iut.EtaleTheta.Env
