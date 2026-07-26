/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.Basic

/-!
# The left-hand side of the Corollary 3.12 variant (taxis #34)

The **`q`-pilot side** `−|log(q)|` of the project-owner-specified variant of IUT III,
Corollary 3.12 (taxis #33), built from the bad-place Tate parameters of the initial
Θ-data (taxis #38, through the `q`-parameter interface of taxis #37).

## Normalization (documented)

For initial Θ-data with prime `ℓ` and bad locus `V(F)^bad`:

* `log(q)` is the normalized degree of the `q`-divisor: the weighted sum, over the bad
  places `w`, of `ord_w(q_w) · log p_w`, where `ord_w(q_w)` is the normalized integer
  order of the Tate parameter at `w` (`AdmissiblePrimeData.qOrder`, from taxis #37),
  `p_w` the residue characteristic, and the weights are the normalized
  arithmetic-degree weights (in the intended instantiation `[F_w : ℚ_{p_w}]/[F : ℚ]`),
  carried as data with their positivity exposed (`QPilotData.weight`,
  `QPilotData.weight_pos`). This corresponds to the `q`-divisor conventions of IUT I,
  Example 3.2(iv).
* `|log(q)| := (1/2ℓ) · log(q)`: the quantity `|log(q)| ∈ ℝ_{>0}` of IUT III,
  Corollary 3.12, whose value in this normalization is recorded in IUT IV, the proof
  of Theorem 1.10 ("the quantity `|log(q)|` … is equal to `(1/2ℓ)·log(q)`").
* The left-hand side is `−|log(q)|` (`QPilotData.lhs`), a real number — the ordered
  ambient type shared with the right-hand side (taxis #35).

## Honesty boundary

The finiteness of the bad locus and the values of the weights are *inputs* (fields of
`QPilotData`), not theorems of this repository; both are provable for actual number
fields and the intended weights, and nothing here asserts any disputed equality or
inequality. The local Tate-parameter orders come pinned to `E` by the `j`-invariant
characterization of taxis #37 (see `AdmissiblePrimeData.tateJ_eq`). The `q`-pilot
*object* of IUT III (a Frobenioid-theoretic gadget) is not constructed; this module
computes only its log-volume side, which is all that the variant statement uses —
this distinction is exactly the "local `q`-parameter vs global `q`-pilot" separation
requested by taxis #37.
-/

namespace Iut

universe u

open NumberField

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- The **`q`-pilot input data** for the left-hand side of the Corollary 3.12 variant
(taxis #34): a finite enumeration of the bad locus `V(F)^bad` and the normalized
arithmetic-degree weights of its places. All choices and assumptions are fields; see
the module docstring for the normalization. -/
structure QPilotData (D : InitialThetaData AG TG) : Type u where
  /-- The bad locus as a finite set of places. -/
  badFinset : Finset (FinitePlace D.F)
  /-- The finite set enumerates exactly `V(F)^bad`. -/
  badFinset_spec : ↑badFinset = badPlacesOver D.F D.E D.VBad
  /-- The normalized arithmetic-degree weight of each place (intended:
  `[F_w : ℚ_{p_w}]/[F : ℚ]`). -/
  weight : FinitePlace D.F → ℝ
  /-- Weights of bad places are positive. -/
  weight_pos : ∀ w ∈ badFinset, 0 < weight w

namespace QPilotData

variable {D : InitialThetaData AG TG} (Q : QPilotData D)

/-- Membership in the enumerating finite set gives membership in `V(F)^bad`. -/
lemma mem_bad {w : FinitePlace D.F} (hw : w ∈ Q.badFinset) :
    w ∈ badPlacesOver D.F D.E D.VBad :=
  Q.badFinset_spec ▸ Finset.mem_coe.mpr hw

/-- The normalized degree `log(q)` of the `q`-divisor of the Θ-data: the weighted sum
over the bad places of `ord_w(q_w) · log p_w` (IUT I, Example 3.2(iv); see the module
docstring). -/
noncomputable def logQ : ℝ :=
  ∑ w ∈ Q.badFinset.attach,
    Q.weight w.1 * (D.prime.qOrder w.1 (Q.mem_bad w.2) : ℝ) *
      Real.log (residueChar w.1)

/-- The quantity `|log(q)| = (1/2ℓ) · log(q)` of IUT III, Corollary 3.12, in the
normalization recorded in IUT IV, proof of Theorem 1.10. -/
noncomputable def absLogQ : ℝ := Q.logQ / (2 * (D.ℓ : ℝ))

/-- **The left-hand side of the Corollary 3.12 variant** (taxis #34): `−|log(q)|`,
a real number in the ordered ambient type shared with the right-hand side. No
disputed equality or inequality is asserted. -/
noncomputable def lhs : ℝ := -Q.absLogQ

end QPilotData

end Iut
