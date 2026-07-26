/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.Container

/-!
# Log-volume on the large volume container (taxis #44)

The counterpart, for the large volume container of taxis #43, of the packet-normalized
and procession-normalized log-volumes on tensor-packets of log-shells of IUT III,
Proposition 3.9 and Remarks 3.1.1, 3.9.1, 3.9.3.

## Codomain and zero/infinite volume (documented design choice)

The codomain of every log-volume in this module is `ℝ`. Regions of zero or infinite
volume are *not* excluded from the domain — the volume functions are total — but no law
is recorded for them: the interface fields below constrain the values only through the
normalizations and combination laws listed, all of which concern the finite, nonzero
volume regime of IUT III, Proposition 3.9. In particular monotonicity is deliberately
**not** recorded as a global law: with a real (rather than `±∞`-valued) codomain it
fails for empty or unbounded junk regions, and imposing it would silently constrain the
junk values. Callers needing finiteness or positivity must carry those hypotheses where
they use them (as the holomorphic hull interface of taxis #45 does).

## Normalizations (source correspondence)

* **Local nonarchimedean normalization**: on each direct-summand field of a packet the
  log-volume of the holomorphic integral structure `O` is `0`
  (`componentVol_integral_nonarch`) and taking the preimage under multiplication by the
  residue characteristic `p` adds `log p` (`componentVol_prime_preimage`; equivalently,
  multiplication by `p` itself subtracts `log p`). This is the normalized Haar
  log-volume of IUT III, Proposition 3.9(i); its construction from `p`-adic measure
  theory is the infrastructure of taxis #4 and enters here as interface fields.
* **Archimedean radial normalization**: a designated Hermitian unit ball in each
  archimedean summand has log-volume `0` (`archBall`, `componentVol_archBall`;
  IUT III, Proposition 3.9(ii)).
* **Place weights**: direct summands over `v ∣ v_Q` are combined with the normalized
  weights `weight v_Q v` (in the intended instantiation `[K_v : ℚ_{v_Q}]/[K : ℚ]`,
  positive and summing to `1` over each fiber; IUT III, Remark 3.1.1).
* **Tensor-packet convention**: the weight of a component — a tuple `(v_j)_{j ∈ S}` —
  is the *product* of the place weights of its entries (`packetWeight`; IUT III,
  Remark 3.1.1; the same convention as the weighted averages of IUT IV,
  Proposition 1.7). The combination law for direct-product regions is
  `packetVol_product`.
* **Packet normalization vs procession normalization**: `packetVol` (weighted, per
  capsule and rational place) and `processionVol` (the *unweighted* average over the
  capsules of the procession, IUT III, Proposition 3.9(iii)) are distinct operations;
  neither is identified with the local Haar normalization `componentVol`, and the
  `v_Q`-indexing is never suppressed — the global log-volume is the sum over rational
  places (`globalVol`), well-defined by the finite-support condition of the container's
  admissible regions.
* **Permutation of packet labels**: the recorded combination law is invariant under
  permutation of the capsule labels; this is *proved* below
  (`packetWeight_comp_perm`, `sum_components_comp_perm`), not postulated.
  Invariance under multiplication by global principal elements concerns data (global
  multiplicative monoids acting on the packets) not included in this abstraction; it is
  deliberately omitted here and must be added by any refinement that includes that
  action (taxis #44 "where included in the chosen abstraction").
-/

namespace Iut

universe u₁ u₂ v

variable {ι : Type u₁} {V : Type u₂}

/-- Log-volume data on a large volume container (taxis #44): local log-volumes on the
direct-summand fields of each packet, normalized place weights, and packet log-volumes,
with the normalization and combination laws of IUT III, Proposition 3.9 and
Remark 3.1.1 recorded as explicit fields. See the module docstring for the codomain
convention and the treatment of zero/infinite volume. -/
structure LogVolumeData (D : LargeVolumeContainerData.{u₁, u₂, v} ι V) :
    Type (max u₁ u₂ v) where
  /-- The normalized weight of a place `v ∣ v_Q`; in the intended instantiation
  `[K_v : ℚ_{v_Q}]/[K : ℚ]` (IUT III, Remark 3.1.1). -/
  weight : (vQ : RationalPlace) → D.Fiber vQ → ℝ
  /-- Place weights are positive. -/
  weight_pos : ∀ vQ v, 0 < weight vQ v
  /-- The weights over each rational place sum to `1`
  (`∑_{v ∣ v_Q} [K_v : ℚ_{v_Q}] = [K : ℚ]`). -/
  weight_sum_one : ∀ vQ, ∑ v, weight vQ v = 1
  /-- The local log-volume on regions of each direct-summand field of each packet. -/
  componentVol : ∀ (i : Fin D.proc.length) (vQ : RationalPlace)
    (c : D.Components i vQ), Set ((D.packet i vQ).Summand c) → ℝ
  /-- Nonarchimedean normalization: the holomorphic integral structure has
  log-volume `0`. -/
  componentVol_integral_nonarch : ∀ i (p : Nat.Primes) (c : D.Components i (.finite p)),
    componentVol i (.finite p) c ((D.packet i (.finite p)).integral c) = 0
  /-- Nonarchimedean normalization: the preimage under multiplication by the residue
  characteristic `p` (that is, scaling by `p⁻¹`) adds `log p` to the log-volume. -/
  componentVol_prime_preimage : ∀ i (p : Nat.Primes) (c : D.Components i (.finite p))
    (U : Set ((D.packet i (.finite p)).Summand c)),
    componentVol i (.finite p) c ((fun x => ((p : ℕ) : _) * x) ⁻¹' U) =
      componentVol i (.finite p) c U + Real.log p
  /-- The designated Hermitian unit ball of each archimedean summand
  (IUT III, Proposition 3.9(ii)). -/
  archBall : ∀ (i : Fin D.proc.length) (c : D.Components i .infinite),
    Set ((D.packet i .infinite).Summand c)
  /-- Archimedean radial normalization: the Hermitian unit ball has log-volume `0`. -/
  componentVol_archBall : ∀ i (c : D.Components i .infinite),
    componentVol i .infinite c (archBall i c) = 0
  /-- The packet-normalized log-volume on regions of each packet total. -/
  packetVol : ∀ (i : Fin D.proc.length) (vQ : RationalPlace),
    Set (D.packet i vQ).Total → ℝ
  /-- The holomorphic integral region of each packet has packet log-volume `0`. This
  normalization makes the global sum over rational places finitely supported on
  admissible regions. -/
  packetVol_integral : ∀ i vQ, packetVol i vQ (D.packet i vQ).integralRegion = 0
  /-- Combination law (IUT III, Remark 3.1.1): on a direct-product region, the packet
  log-volume is the weighted sum over components of the local log-volumes, with the
  tensor-packet weight `packetWeight` — the product of the place weights over the
  labels — attached to each component. This combines the direct summands over
  `v ∣ v_Q` by the normalized place weights and the tensor factors by the
  tensor-packet convention. -/
  packetVol_product : ∀ i vQ (U : ∀ c : D.Components i vQ,
      Set ((D.packet i vQ).Summand c)),
    packetVol i vQ ((D.packet i vQ).productRegion U) =
      ∑ c, (∏ j, weight vQ (c j)) * componentVol i vQ c (U c)

namespace LogVolumeData

variable {D : LargeVolumeContainerData.{u₁, u₂, v} ι V} (vol : LogVolumeData D)

/-- The tensor-packet weight of a component: the product of the normalized place
weights over the labels of the capsule (IUT III, Remark 3.1.1). -/
def packetWeight (i : Fin D.proc.length) (vQ : RationalPlace)
    (c : D.Components i vQ) : ℝ :=
  ∏ j, vol.weight vQ (c j)

lemma packetVol_product' (i : Fin D.proc.length) (vQ : RationalPlace)
    (U : ∀ c : D.Components i vQ, Set ((D.packet i vQ).Summand c)) :
    vol.packetVol i vQ ((D.packet i vQ).productRegion U) =
      ∑ c, vol.packetWeight i vQ c * vol.componentVol i vQ c (U c) :=
  vol.packetVol_product i vQ U

/-- Packet weights are positive. -/
lemma packetWeight_pos (i : Fin D.proc.length) (vQ : RationalPlace)
    (c : D.Components i vQ) : 0 < vol.packetWeight i vQ c :=
  Finset.prod_pos fun j _ => vol.weight_pos vQ (c j)

/-- **Invariance of the packet weight under permutation of the capsule labels**:
precomposing a component with a permutation of the labels does not change its weight. -/
lemma packetWeight_comp_perm (i : Fin D.proc.length) (vQ : RationalPlace)
    (σ : Equiv.Perm (D.proc.capsule i).LabelType) (c : D.Components i vQ) :
    vol.packetWeight i vQ (c ∘ σ) = vol.packetWeight i vQ c :=
  Equiv.prod_comp σ fun j => vol.weight vQ (c j)

/-- **Invariance of the weighted combination law under permutation of the packet
labels**: reindexing the components of a packet by a permutation of the capsule labels
leaves the weighted sum over components unchanged. Together with
`packetWeight_comp_perm` this is the permutation invariance of the log-volume recorded
by taxis #44, proved rather than postulated. -/
lemma sum_components_comp_perm (i : Fin D.proc.length) (vQ : RationalPlace)
    (σ : Equiv.Perm (D.proc.capsule i).LabelType) (f : D.Components i vQ → ℝ) :
    ∑ c : D.Components i vQ, f (c ∘ σ) = ∑ c : D.Components i vQ, f c :=
  Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl _)) f

/-- The global log-volume of an admissible region: the sum over all rational places of
the packet log-volumes. The sum is finitely supported by the admissibility condition
and the normalization `packetVol_integral`; see `finite_support_packetVol`. -/
noncomputable def globalVol {i : Fin D.proc.length} (R : D.AdmissibleRegion i) : ℝ :=
  ∑ᶠ vQ, vol.packetVol i vQ (R.region vQ)

/-- The function summed by `globalVol` has finite support: away from the finite
support of the admissible region the packet region is the holomorphic integral region,
whose packet log-volume is `0`. -/
lemma finite_support_packetVol {i : Fin D.proc.length} (R : D.AdmissibleRegion i) :
    (Function.support fun vQ => vol.packetVol i vQ (R.region vQ)).Finite := by
  refine R.finiteSupport.subset fun vQ hvQ h => ?_
  apply hvQ
  change vol.packetVol i vQ (R.region vQ) = 0
  rw [h]
  exact vol.packetVol_integral i vQ

/-- The global log-volume of the holomorphic integral structure is `0`. -/
@[simp]
lemma globalVol_integralAdmissible (i : Fin D.proc.length) :
    vol.globalVol (D.integralAdmissible i) = 0 := by
  unfold globalVol
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro vQ
  exact vol.packetVol_integral i vQ

/-- The **procession-normalized log-volume** (IUT III, Proposition 3.9(iii)): the
*unweighted* average, over the capsules of the procession, of the global log-volumes
of a family of admissible regions indexed by the capsules. The procession labels
`S_{j+1}` are retained: the family is indexed by the capsules of the procession, not
flattened. This averaging is a separate operation from the local Haar normalization
`componentVol` and from the packet normalization `packetVol`, and is not identified
with either. -/
noncomputable def processionVol (R : ∀ i : Fin D.proc.length, D.AdmissibleRegion i) :
    ℝ :=
  (∑ i, vol.globalVol (R i)) / D.proc.length

end LogVolumeData

end Iut
