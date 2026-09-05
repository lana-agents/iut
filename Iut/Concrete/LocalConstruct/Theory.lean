/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.LogShell
import Iut.Concrete.LocalConstruct.ArchLogShell
import Iut.Concrete.LocalConstruct.Prop14

/-!
# The concrete local theory (taxis #4, #278)

This file assembles the constructions of `Iut/Concrete/LocalConstruct/*` into a term
`concreteLocalTheory K hyps : Iut.LocalTheory K`. Every field of `LocalTheory` is proved
from the construction except the three collected in the propositional record
`LocalTheoryFacts K` (the third only on the junk packets):

* `integral_subset_logShell`: `(R_I)^∼ ⊆ 𝓘_I` (IUT III, Proposition 1.2; IUT IV,
  Proposition 1.2). Proved here for the order `R_I` (`order_subset_logShell`); for the
  maximal order it requires the comparison of `(R_I)^∼` with `R_I` through the different.
  At an odd prime unramified in every factor it says that `R_I` is integrally closed
  (`𝓘_I = R_I` there, `logShell_eq_order_of_unramified`), which is the content of
  `logShell_eq_integral`; that field is derived from this one.
* `exists_leastHull`: existence of least hull regions `a·(R_I)^∼` containing an admissible
  region at a prime (IUT III, Remark 3.9.5(i)). This is the statement that bounded open
  `(R_I)^∼`-submodules of the packet are principal — true because `(R_I)^∼` is a finite
  product of complete discrete valuation rings, a fact about the integral closure of `ℤ_p` in
  finite extensions of `ℚ_p` (uniqueness of the extension of the valuation) not available in
  Mathlib. The archimedean counterpart `exists_leastHull_infinite` (least real radial
  scaling `t·B_I` containing an admissible region) is proved (`Admissible.lean`).
* `prop14_iii_junk`: IUT IV, Proposition 1.4(iii), the log-volume estimate for the hull of
  the images of `x·(R_I)^∼` under the indeterminacies, **on the junk packets** (a component
  not over `p`). On the packets all of whose components lie over `p` the field is proved
  (`prop14iii_of_isOver`, `Prop14.lean`: the hull region `p^{⌊ord_p x⌋}·(R_I)^∼`). The junk
  case is **false** for the construction (`not_prop14iiiJunk`: the junk packets are the zero
  ring, where the log-volume vanishes while the bound is negative for `ord_p x` large), so
  `LocalTheoryFacts K` is unsatisfiable (`not_localTheoryFacts`) until the interface field
  `LocalTheory.prop14_iii` carries the hypothesis of `componentVol_prime_preimage` that every
  component lies over `p` — which is how the field is applied (`LocalTheory.tuple_isOver`).
-/

namespace Iut

namespace LocalConstruct

open NumberField
open scoped Pointwise

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- **The log-shell of a packet**, uniformly in the rational place (`LocalTheory.logShell`):
`⊗_j 𝓘_{c j}` at a prime, `π^{|I|}·B_I` at the archimedean place. -/
noncomputable def logShellAt {ι : Type} [Fintype ι] :
    ∀ (vQ : RationalPlace) (c : ι → Place K), Set (Tensor K vQ c)
  | .finite p, c => logShell p c
  | .infinite, c => archLogShell c

variable {K}

lemma logShellAt_finite {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K) :
    logShellAt K (.finite p) c = logShell p c := rfl

lemma logShellAt_infinite {ι : Type} [Fintype ι] (c : ι → Place K) :
    logShellAt K .infinite c = archLogShell c := rfl

variable (K)

/-- **Existence of least hull regions at a prime** (IUT III, Remark 3.9.5(i); the field
`LocalTheory.exists_leastHull` for the concrete packets): every admissible region of a
nonarchimedean packet is contained in a least region `a·(R_I)^∼` with `a` a unit. -/
def HullExists : Prop :=
  ∀ {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)
    (U : Set (Tensor K (.finite p) c)), U ∈ admissible (.finite p) c →
    ∃ a : Tensor K (.finite p) c, IsUnit a ∧ U ⊆ a • integralAt (.finite p) c ∧
      ∀ b : Tensor K (.finite p) c, IsUnit b → U ⊆ b • integralAt (.finite p) c →
        a • integralAt (.finite p) c ⊆ b • integralAt (.finite p) c

/-- **The residual inputs of the concrete local theory**: the three fields of
`Iut.LocalTheory K` not proved by the construction (see the module docstring). -/
structure LocalTheoryFacts : Prop where
  /-- `(R_I)^∼ ⊆ 𝓘_I` (IUT III, Proposition 1.2). -/
  integral_subset_logShell : ∀ {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K),
    integral p c ⊆ logShell p c
  /-- Existence of least hull regions at a prime (IUT III, Remark 3.9.5(i)). -/
  exists_leastHull : HullExists K
  /-- IUT IV, Proposition 1.4(iii) on the junk packets (a component not over `p`); the
  case of the packets over `p` is proved (`prop14iii_of_isOver`). This case is false for the
  construction (`not_prop14iiiJunk`), see the module docstring. -/
  prop14_iii_junk : Prop14iiiJunk K

variable {K}

/-- At an odd prime unramified in every factor, `𝓘_I = (R_I)^∼` follows from
`(R_I)^∼ ⊆ 𝓘_I`, since `𝓘_I = R_I ⊆ (R_I)^∼` there. -/
theorem logShell_eq_integral_of_unramified {ι : Type} [Fintype ι] (p : Nat.Primes)
    (c : ι → Place K) (hsub : integral p c ⊆ logShell p c) (hodd : Odd (p : ℕ))
    (hunr : ∀ j w, c j = Place.finite w → ramIdx K w = 1) : logShell p c = integral p c :=
  Set.Subset.antisymm
    ((logShell_eq_order_of_unramified p c hodd hunr).le.trans (order_subset_integral p c)) hsub

variable (K)

/-- **The concrete local theory**: `Iut.LocalTheory K` from the constructions of
`Iut/Concrete/LocalConstruct/*` and the residual facts `LocalTheoryFacts K`. -/
noncomputable def concreteLocalTheory (hyps : LocalTheoryFacts K) : LocalTheory.{u, u} K where
  toLocalTensor := concreteLocalTensor (K := K)
  residueChar_prime := residueChar_prime
  fiber_finite := fiber_finite
  ramified_finite := ramified_finite
  localDeg_pos := localDeg_pos
  ramIdx_pos := ramIdx_pos
  ordDifferent_eq_zero := ordDifferent_eq_zero
  sum_localDeg p hp _ := sum_localDeg p hp
  sum_mult := sum_mult
  ordp_p := ordp_p
  ordp_mul := ordp_mul
  incl := incl
  isUnit_incl := isUnit_incl
  integral := integralAt
  one_mem_integral := one_mem_integralAt
  smul_integral_subset := smul_integral_subset_of_ordp
  logShell := logShellAt K
  logShell_relCompact vQ c := by
    cases vQ with
    | finite p => exact isCompact_closure_logShell p c
    | infinite => exact isCompact_closure_archLogShell c
  integral_subset_logShell := hyps.integral_subset_logShell
  logShell_eq_integral p c hodd hunr :=
    logShell_eq_integral_of_unramified p c (hyps.integral_subset_logShell p c) hodd hunr
  componentVol := componentVol
  componentVol_integral vQ c := componentVol_integral
  componentVol_prime_preimage p c hc U hU := componentVol_prime_preimage_of_admissible p hc hU
  componentVol_mono vQ c := componentVol_mono
  componentVol_arch_scale c := componentVol_arch_scale
  admissible := admissible
  admissible_nonempty vQ c U := admissible_nonempty
  admissible_relCompact vQ c U := admissible_relCompact
  integral_admissible vQ c := integral_admissible
  smul_integral_admissible vQ c := smul_integral_admissible
  exists_leastHull := hyps.exists_leastHull
  exists_leastHull_infinite c U hU := exists_leastHull_infinite c hU
  smul_integral_infinite_mono c := smul_integralAt_infinite_mono c
  indAut := indAut
  id_mem_indAut := id_mem_indAut
  indAut_logShell vQ c := by
    cases vQ with
    | finite p => exact indAut_logShell p c
    | infinite => exact indAut_archLogShell c
  theta_admissible := theta_admissible
  thetaShell_admissible vQ c := by
    cases vQ with
    | finite p => exact thetaShell_admissible p c
    | infinite => exact thetaShell_admissible_infinite c
  prop14_iii := prop14iii_of_junk hyps.prop14_iii_junk
  prop14_iv := prop14_iv
  prop15 := prop15

/-- **`LocalTheoryFacts K` is unsatisfiable**: its field `prop14_iii_junk` — the statement
of `LocalTheory.prop14_iii` on the junk packets — is false for the construction
(`not_prop14iiiJunk`). -/
theorem not_localTheoryFacts : ¬ LocalTheoryFacts K := fun hyps =>
  not_prop14iiiJunk hyps.prop14_iii_junk

end LocalConstruct

end Iut
