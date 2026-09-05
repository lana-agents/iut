/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.Volume

/-!
# The admissible class of the holomorphic hull (taxis #4, #278)

The **admissible regions** of a packet (IUT III, Remark 3.9.5(i)) are the nonempty,
relatively compact, measurable regions of positive finite Haar measure (`admissible`, the
field `LocalTheory.admissible`). This file proves `admissible_nonempty`,
`admissible_relCompact`, `integral_admissible`, `smul_integral_admissible`, and restates
the scaling law of the log-volume for admissible regions.

## Remark on `LocalTheory.exists_leastHull`

The existence of a *least* hull region `a·I` (`a` a unit) containing an admissible region
is not proved here: it requires the decomposition of the packet `⊗_j K_{c j}` into a
product of local fields (for which `I` is the product of the rings of integers and the hull
regions are the products of fractional ideals, whose least upper bound is computed
componentwise). For the integral structure `R_I = ⊗_{ℤ_p} 𝓞_{c j}` of this package (as
opposed to its normalization) least hull regions need not exist at all, since `R_I` is in
general only an order in the ring of integers of the packet. See the report.
-/

namespace Iut

namespace LocalConstruct

open MeasureTheory NumberField
open scoped Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]

variable (vQ : RationalPlace) (c : ι → Place K)

/-- **The admissible class** of the holomorphic hull: nonempty, relatively compact,
measurable regions of positive finite Haar measure (`LocalTheory.admissible`). -/
def admissible : Set (Set (Tensor K vQ c)) :=
  {S | S.Nonempty ∧ IsCompact (closure S) ∧ MeasurableSet S ∧ 0 < haar vQ c S ∧ haar vQ c S < ⊤}

variable {vQ c}

lemma mem_admissible {S : Set (Tensor K vQ c)} :
    S ∈ admissible vQ c ↔
      S.Nonempty ∧ IsCompact (closure S) ∧ MeasurableSet S ∧ 0 < haar vQ c S ∧ haar vQ c S < ⊤ :=
  Iff.rfl

/-- Admissible regions are nonempty (`LocalTheory.admissible_nonempty`). -/
lemma admissible_nonempty {U : Set (Tensor K vQ c)} (hU : U ∈ admissible vQ c) : U.Nonempty :=
  hU.1

/-- Admissible regions are relatively compact (`LocalTheory.admissible_relCompact`). -/
lemma admissible_relCompact {U : Set (Tensor K vQ c)} (hU : U ∈ admissible vQ c) :
    IsCompact (closure U) :=
  hU.2.1

lemma admissible_measurableSet {U : Set (Tensor K vQ c)} (hU : U ∈ admissible vQ c) :
    MeasurableSet U :=
  hU.2.2.1

lemma admissible_haar_pos {U : Set (Tensor K vQ c)} (hU : U ∈ admissible vQ c) :
    0 < haar vQ c U :=
  hU.2.2.2.1

lemma admissible_haar_lt_top {U : Set (Tensor K vQ c)} (hU : U ∈ admissible vQ c) :
    haar vQ c U < ⊤ :=
  hU.2.2.2.2

/-- Scaled integral structures are admissible (`LocalTheory.smul_integral_admissible`). -/
lemma smul_integral_admissible (a : Tensor K vQ c) (ha : IsUnit a) :
    a • integralAt vQ c ∈ admissible vQ c :=
  ⟨(integralAt_nonempty vQ c).smul_set,
    by rw [(isCompact_smul_integralAt a).isClosed.closure_eq]; exact isCompact_smul_integralAt a,
    measurableSet_smul_integralAt a, haar_smul_integralAt_pos ha, haar_smul_integralAt_lt_top a⟩

/-- The integral structure is admissible (`LocalTheory.integral_admissible`). -/
lemma integral_admissible : integralAt vQ c ∈ admissible vQ c := by
  simpa using smul_integral_admissible (vQ := vQ) (c := c) 1 isUnit_one

/-- The scaling law of the log-volume at `p` for admissible regions. -/
theorem componentVol_prime_preimage_of_admissible (p : Nat.Primes) (hc : ∀ j, IsOver K p (c j))
    {U : Set (Tensor K (.finite p) c)} (hU : U ∈ admissible (.finite p) c) :
    componentVol (.finite p) c ((fun x => ((p : ℕ) : Tensor K (.finite p) c) * x) ⁻¹' U) =
      componentVol (.finite p) c U + Real.log p :=
  componentVol_prime_preimage' p hc U (admissible_measurableSet hU) (admissible_haar_pos hU).ne'
    (admissible_haar_lt_top hU).ne

end LocalConstruct

end Iut
