/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Cor312.Statement

/-!
# Local arithmetic of a number field (taxis #4, #278)

The quantities of the local theory of IUT IV, §1 that Mathlib expresses directly: the
completion `K_w`, the ramification index `e_w`, the residue degree `f_w`, the local degree
`[K_w : ℚ_p] = e_w f_w`, the normalized weights `[K_w : ℚ_p]/[K : ℚ]`, the valuation `ord_p`
normalized by `ord_p(p) = 1` on each completion (from the norm of the adic completion,
which is normalized by `‖π_w‖ = (#𝓞_K/𝔭_w)⁻¹`), and the different exponents.

The tensor packets `⊗_{j ∈ S} K_{v_j}` (IUT III, Proposition 3.1) with their integral
structures, log-shells, normalized Haar log-volumes, holomorphic hulls and indeterminacy
automorphisms are constructed in `Iut/Concrete/LocalConstruct/*` and exposed, uniformly in
the rational place, in the namespace `Iut.LocalTheory` (`Iut/Concrete/LocalConstruct/Theory.lean`).
-/

namespace Iut

universe u

open NumberField IsDedekindDomain
open scoped Pointwise

variable (K : Type u) [Field K] [NumberField K]

/-- The completion `K_w` of `K` at a finite place. -/
noncomputable abbrev completionAt (w : FinitePlace K) : Type u :=
  w.maximalIdeal.adicCompletion K

/-- The ramification index `e_w` of the finite place `w` over its residue
characteristic. -/
noncomputable def ramIdx (w : FinitePlace K) : ℕ :=
  Ideal.ramificationIdx w.maximalIdeal.asIdeal ℤ

/-- The residue degree `f_w` of the finite place `w` over its residue characteristic. -/
noncomputable def inertDeg (w : FinitePlace K) : ℕ :=
  Ideal.inertiaDeg w.maximalIdeal.asIdeal ℤ

/-- The local degree `[K_w : ℚ_p] = e_w · f_w`. -/
noncomputable def localDeg (w : FinitePlace K) : ℕ := ramIdx K w * inertDeg K w

/-- The normalized weight `[K_w : ℚ_p]/[K : ℚ]` of a finite place
(IUT III, Remark 3.1.1). -/
noncomputable def placeWeight (w : FinitePlace K) : ℝ :=
  (localDeg K w : ℝ) / Module.finrank ℚ K

/-- The normalized weight `[K_w : ℝ]/[K : ℚ]` of an infinite place (`mult w ∈ {1, 2}`). -/
noncomputable def infPlaceWeight (w : InfinitePlace K) : ℝ :=
  (w.mult : ℝ) / Module.finrank ℚ K

/-- The valuation `ord_p` on `K_w`, normalized by `ord_p(p) = 1`: since the norm of the
adic completion satisfies `‖p‖ = p^{−[K_w : ℚ_p]}`, `ord_p(x) = −log‖x‖/([K_w : ℚ_p]·log p)`. -/
noncomputable def ordp (w : FinitePlace K) (x : completionAt K w) : ℝ :=
  -Real.log ‖x‖ / (localDeg K w * Real.log (residueChar w))

/-- The ramification index of a place of `K` over its rational place (`1` at infinite
places, by convention). -/
noncomputable def ramIdxAt : Place K → ℕ
  | .finite w => ramIdx K w
  | .infinite _ => 1

open scoped Classical in
/-- The exponent `ord_𝔭(𝔡_{K/ℚ})` of the different ideal of `K` at the finite place `w`. -/
noncomputable def ordDifferent (w : FinitePlace K) : ℕ :=
  Multiset.count w.maximalIdeal.asIdeal
    (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (𝓞 K)))

/-- The **different exponent** `d_w` of `K_w` over `ℚ_p` in the normalization
`ord_p(p) = 1`: `d_w = ord_𝔭(𝔡_{K/ℚ})/e_w` (the local different at `w` is the
completion of the global one; IUT IV, Proposition 1.3). -/
noncomputable def differentExponent (w : FinitePlace K) : ℝ :=
  (ordDifferent K w : ℝ) / ramIdx K w

end Iut
