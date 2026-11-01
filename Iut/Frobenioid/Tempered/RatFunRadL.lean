/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.RatFunBase
import Iut.Frobenioid.Tempered.RatFunRad

/-!
# The radical layer over `L` (MR18 T8, route B-an)

`RatFunRad.lean` treats radicals of meromorphic functions over an algebraically closed complete
field `Ω` (`ℚ`-valued orders and Gauss norms, [EtTh] Prop 3.4(ii) on the radical layer).
In [EtTh] §3 (Def 3.3(iii), Ex 3.9(iii): perfections) the functions are defined over a finite
extension `L` of `ℚ_p`, while the divisors are only visible over `Ω` (e.g. `ℂ_p`, see
`PadicEmbed.lean`). This file transports radicals along the isometric `φ : L → Ω` of
`RatFunBase.lean`:

* the radicals of `Mero L` live in a field `R ⊇ Mero L`, those of `Mero Ω` in `R' ⊇ Mero Ω`, and
  `ψ : R → R'` is a field homomorphism extending `Mero.map φ hφ`;
  `exists_radHom` constructs such a `ψ` between the algebraic closures;
* `IsRad.map`, `rord_map_eq`, `rgn_map_eq`: a radical over `Mero L` maps to a radical over
  `Mero Ω`, with divisor `div_Ω(yⁿ)/n`;
* **[EtTh] Proposition 3.4(ii) on the radical layer over `L`**: `radL_ker_iff` (trivial divisor
  over `Ω` iff some power `yⁿ` is a scalar of `O_L^×`) and `radL_eff_iff` (effective iff some
  `yⁿ` is a nonzero scalar of `O_L`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open Polynomial

variable {L Ω : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  [NontriviallyNormedField Ω] [CompleteSpace Ω] [IsUltrametricDist Ω]

namespace Mero

variable (φ : L →+* Ω) (hφ : ∀ x, ‖φ x‖ = ‖x‖)

variable {R R' : Type*} [Field R] [Algebra (Mero L) R] [Field R'] [Algebra (Mero Ω) R']

/-- **An extension of `Mero.map` to radical fields** exists between the algebraic closures. -/
theorem exists_radHom :
    ∃ ψ : AlgebraicClosure (Mero L) →+* AlgebraicClosure (Mero Ω),
      ∀ x : Mero L, ψ (ι _ x) = ι _ (map φ hφ x) := by
  letI : Algebra (Mero L) (AlgebraicClosure (Mero Ω)) :=
    ((algebraMap (Mero Ω) (AlgebraicClosure (Mero Ω))).comp (map φ hφ)).toAlgebra
  let ψ : AlgebraicClosure (Mero L) →ₐ[Mero L] AlgebraicClosure (Mero Ω) := IsAlgClosed.lift
  exact ⟨ψ.toRingHom, fun x => ψ.commutes x⟩

variable {φ hφ} {ψ : R →+* R'} (hψ : ∀ x : Mero L, ψ (ι R x) = ι R' (map φ hφ x))
include hψ

lemma IsRad.map {y : R} (hy : IsRad L y) : IsRad Ω (ψ y) := by
  obtain ⟨n, hn, x, hx⟩ := hy
  exact ⟨n, hn, Mero.map φ hφ x, by rw [← hψ, hx, map_pow]⟩

/-- The `ℚ`-valued orders over `Ω` of the image of a radical `y` with `yⁿ = x ∈ Mero L`. -/
lemma rord_map_eq {y : R} (hy : y ≠ 0) {n : ℕ} (hn : 0 < n) {x : Mero L} (hx : ι R x = y ^ n)
    (α : Ωˣ) : rord (ψ y) α = (ord (map φ hφ x) α : ℚ) / n :=
  rord_eq ((map_ne_zero ψ).mpr hy) hn (by rw [← hψ, hx, map_pow]) α

/-- The Gauss norms of the image of a radical: `|yⁿ|_r^{1/n}`, computed over `L`. -/
lemma rgn_map_eq {y : R} (hy : y ≠ 0) {n : ℕ} (hn : 0 < n) {x : Mero L} (hx : ι R x = y ^ n)
    {r : ℝ} (hr : 0 < r) : rgn Ω (ψ y) r = gn x r ^ ((1 : ℝ) / n) := by
  rw [rgn_eq ((map_ne_zero ψ).mpr hy) hn (by rw [← hψ, hx, map_pow]) hr, gn_map φ hφ x hr]

variable [IsAlgClosed Ω]

/-- **[EtTh] Proposition 3.4(ii) on the radical layer over `L`, the kernel**: a radical over
`Mero L` has trivial divisor over `Ω` (order `0` at every point of `Ωˣ`, Gauss norm `1` on the
component circles `|U| = ‖q‖^a`) iff some power `yⁿ`, `n ≥ 1`, is a scalar `c ∈ O_L^×`. -/
theorem radL_ker_iff {y : R} (hy0 : y ≠ 0) (hy : IsRad L y) {q : L} (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) :
    ((∀ α : Ωˣ, rord (ψ y) α = 0) ∧ ∀ a : ℤ, rgn Ω (ψ y) (‖q‖ ^ a) = 1) ↔
      ∃ n : ℕ, 0 < n ∧ ∃ c : L, ‖c‖ = 1 ∧ ι R (const c) = y ^ n := by
  constructor
  · rintro ⟨hord, hgn⟩
    obtain ⟨n, hn, x, hx⟩ := hy
    have hx0 := ne_zero_of_ι_eq hy0 hx
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have hordx : ∀ α : Ωˣ, ord (map φ hφ x) α = 0 := fun α => by
      have := hord α
      rw [rord_map_eq hψ hy0 hn hx, div_eq_zero_iff, or_iff_left hn0] at this
      exact_mod_cast this
    have hgnx : ∀ a : ℤ, gn x (‖q‖ ^ a) = 1 := fun a => by
      have := hgn a
      rw [rgn_map_eq hψ hy0 hn hx (zpow_pos hq0 a)] at this
      have hpos := gn_pos hx0 (zpow_pos hq0 a)
      have h1 := congrArg (fun t : ℝ => t ^ (n : ℝ)) this
      simp only [Real.one_rpow] at h1
      rwa [← Real.rpow_mul hpos.le, one_div, inv_mul_cancel₀ (by exact_mod_cast hn.ne'),
        Real.rpow_one] at h1
    obtain ⟨c, hc, rfl⟩ := (ker_iff_of_map φ hφ hx0 hq0 hq1).mp ⟨hordx, hgnx⟩
    exact ⟨n, hn, c, hc, hx⟩
  · rintro ⟨n, hn, c, hc, hx⟩
    have hc0 : c ≠ 0 := fun h => by rw [h, norm_zero] at hc; exact zero_ne_one hc
    have hφc : φ c ≠ 0 := (map_ne_zero φ).mpr hc0
    refine ⟨fun α => ?_, fun a => ?_⟩
    · rw [rord_map_eq hψ hy0 hn hx, map_const, ord_const hφc, Int.cast_zero, zero_div]
    · rw [rgn_map_eq hψ hy0 hn hx (zpow_pos hq0 a), gn_const c (zpow_pos hq0 a), hc,
        Real.one_rpow]

/-- **[EtTh] Proposition 3.4(ii) on the radical layer over `L`, the effective part**: a radical
over `Mero L` has effective divisor over `Ω` iff some power `yⁿ`, `n ≥ 1`, is a nonzero scalar
`c ∈ O_L`. -/
theorem radL_eff_iff {y : R} (hy0 : y ≠ 0) (hy : IsRad L y) {q : L} (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) :
    ((∀ α : Ωˣ, 0 ≤ rord (ψ y) α) ∧ ∀ a : ℤ, rgn Ω (ψ y) (‖q‖ ^ a) ≤ 1) ↔
      ∃ n : ℕ, 0 < n ∧ ∃ c : L, c ≠ 0 ∧ ‖c‖ ≤ 1 ∧ ι R (const c) = y ^ n := by
  constructor
  · rintro ⟨hord, hgn⟩
    obtain ⟨n, hn, x, hx⟩ := hy
    have hx0 := ne_zero_of_ι_eq hy0 hx
    have hnpos : (0 : ℚ) < n := by exact_mod_cast hn
    have hordx : ∀ α : Ωˣ, 0 ≤ ord (map φ hφ x) α := fun α => by
      have := hord α
      rw [rord_map_eq hψ hy0 hn hx, div_nonneg_iff] at this
      rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact_mod_cast h1
      · exact absurd h2 (not_le.mpr hnpos)
    have hgnx : ∀ a : ℤ, gn x (‖q‖ ^ a) ≤ 1 := fun a => by
      have := hgn a
      rw [rgn_map_eq hψ hy0 hn hx (zpow_pos hq0 a)] at this
      by_contra hlt
      push Not at hlt
      have := Real.one_lt_rpow hlt (by positivity : (0 : ℝ) < 1 / n)
      linarith
    obtain ⟨c, hc0, hc, rfl⟩ := (eff_iff_of_map φ hφ hx0 hq0 hq1).mp ⟨hordx, hgnx⟩
    exact ⟨n, hn, c, hc0, hc, hx⟩
  · rintro ⟨n, hn, c, hc0, hc, hx⟩
    have hφc : φ c ≠ 0 := (map_ne_zero φ).mpr hc0
    have hnpos : (0 : ℚ) < n := by exact_mod_cast hn
    refine ⟨fun α => ?_, fun a => ?_⟩
    · rw [rord_map_eq hψ hy0 hn hx, map_const, ord_const hφc, Int.cast_zero, zero_div]
    · rw [rgn_map_eq hψ hy0 hn hx (zpow_pos hq0 a), gn_const c (zpow_pos hq0 a)]
      exact Real.rpow_le_one (norm_nonneg c) hc (by positivity)

end Mero

end Iut.Frobenioid.BAn
