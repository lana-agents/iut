/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.CyclicLocal
import Iut.Tripod.Providers

/-!
# The cyclic-subgroup bound ([GenEll], Lemma 3.5) for the tripod: the proved part

`Iut.Tripod.CyclicBoundHyp P K d TK` ([GenEll], Lemma 3.5 with Proposition 3.4; IUT IV,
the proof of Corollary 2.2) says: for a point `x ∈ K ∩ U^{≤ d}` and a prime `ℓ ≥ 7` prime
to the local heights of `E_λ` at all multiplicative places ((P2)), if `E_λ` has a Galois-stable
subgroup `H ⊆ E_λ(ℚ̄)` of order `ℓ`, then `(ℓ − 2)/24 · log q_∀(E_λ) ≤ 2 log ℓ + T_K`.

The proof in [GenEll] has two parts:

1. **Lemma 3.2(i)**: by (P2), `H` is the *graph line* `μ_ℓ ⊆ E_λ[ℓ]` at every multiplicative
   place, so the isogenous curve `E_H = E_λ/H` has Tate parameter `q^ℓ` at every such place
   (Lemma 3.2(ii)) and `log q_∀(E_H) = ℓ · log q_∀(E_λ)`;
2. **the Faltings height** `ht_Falt(E_H) ≤ ht_Falt(E_λ) + 2 log ℓ` (the isogeny extends to the
   semi-abelian schemes, and the cokernel on invariant differentials is killed by `ℓ`) and the
   comparison `ht_Falt ≈ (1/12) log q_∀` of Proposition 3.4 (Silverman), on compactly bounded
   subsets.

Part 1 is proved here at the multiplicative places of **odd** residue characteristic
(`Iut.Tripod.isGraphPlace_of_not_dvd`, from
`Iut.EllipticCurveData.ModEllRepData.comap_bcKR_eq_graphLineAt`; the Tate uniformisation of
the library `tate-curves-theta` requires `‖2‖ = 1`, so the graph line is not available at the
places over `2`). The decomposition of `log q_∀` according to the places where `H` is the graph
line is `Iut.Tripod.h_eq_heightOn_graph_add`, and under (P2) the remaining part is supported
over `2`, hence bounded by the `2`-adic bound `4c` on `K` (`heightOn_not_graph_le`).

Part 2 has no infrastructure in Mathlib or in this repository (isogenies and quotient curves,
Néron models, Faltings heights, the archimedean comparison), and is isolated as the `Prop`
`Iut.Tripod.CyclicGraphBoundHyp`: the same bound under the hypotheses that `H` is the graph
line at the odd multiplicative places and (P2) holds at the places over `2`. The derivation
`Iut.Tripod.cyclicBound_of : CyclicGraphBoundHyp P K d TK → CyclicBoundHyp P K d TK` is the
content of Lemma 3.2(i) at the odd places.
-/

namespace Iut

/-! ### The decomposition of the height by a predicate on the bad places -/

namespace LocalHeightData

variable (L : LocalHeightData)

open scoped Classical in
/-- The part of `log(q_∀)` supported at the bad places satisfying a predicate `p`. -/
noncomputable def heightOn (p : L.ι → Prop) : ℝ :=
  (∑ v ∈ L.bad.filter p, (L.hv v : ℝ) * L.f v * Real.log (L.p v)) / L.deg

lemma heightOn_nonneg (p : L.ι → Prop) : 0 ≤ L.heightOn p := by
  classical
  exact div_nonneg (Finset.sum_nonneg fun v _ => L.term_nonneg v) (by positivity)

/-- The decomposition `h = h_p + h_{¬p}` of the height by a predicate on the bad places. -/
lemma height_eq_heightOn_add (p : L.ι → Prop) :
    L.height = L.heightOn p + L.heightOn (fun v => ¬ p v) := by
  classical
  unfold height heightOn
  rw [← add_div, Finset.sum_filter_add_sum_filter_not]

/-- Monotonicity of `heightOn` in the predicate. -/
lemma heightOn_le_heightOn {p q : L.ι → Prop} (h : ∀ v ∈ L.bad, p v → q v) :
    L.heightOn p ≤ L.heightOn q := by
  classical
  unfold heightOn
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun v _ _ => L.term_nonneg v
  intro v hv
  rw [Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, h v hv.1 hv.2⟩

/-- The part supported over `q` is `heightOn (p = q)`. -/
lemma heightEq_eq_heightOn (q : ℕ) : L.heightEq q = L.heightOn (fun v => L.p v = q) := by
  classical
  unfold heightEq heightOn
  congr 1
  exact Finset.sum_congr (by convert rfl) fun _ _ => rfl

end LocalHeightData

end Iut

namespace Iut.Tripod

open Iut Iut.EllipticCurveData Iut.EllipticCurveData.ModEllRepData WeierstrassCurve NumberField
open scoped Classical

variable (P : CurveProviders) (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)

attribute [local instance 1100] Iut.EllipticCurveData.ModEllRepData.instDecidableEqTorsionFieldR

/-! ### The graph-line condition at the odd multiplicative places -/

/-- The mod-`ℓ` representation data of `E_λ`, as data of the curve `P.curve x`. -/
noncomputable def repOf : (P.curve x).ModEllRepData ℓ := P.modRep x ℓ hℓ

/-- The Tate family of `E_λ` over its ℓ-torsion field `K = F_λ(E_λ[ℓ])` at the places of `K`
over the multiplicative places of odd residue characteristic. -/
noncomputable def tateFamilyOddOf :
    TateFamily (P.curve x).E (repOf P x hℓ).torsionField ℓ (P.curve x).VBadOdd :=
  (repOf P x hℓ).tateFamilyOdd hℓ hodd

/-- **`H` is the graph line at the multiplicative place `w₀` of `F_λ`**: at every place `w` of
the ℓ-torsion field over `w₀` (and over `VBadOdd`), the pull-back of `H` to `E_λ(K)` is the
graph line `μ_ℓ` of the Tate uniformisation of `E_λ` over `K_w`. -/
def IsGraphPlace
    (H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar)))
    (w₀ : FinitePlace (P.curve x).F) : Prop :=
  ∀ (w : FinitePlace ↥(repOf P x hℓ).torsionField)
    (hw : IsBadPlace (P.curve x).E (repOf P x hℓ).torsionField (P.curve x).VBadOdd w),
    placeUnder w = w₀ →
    H.comap (repOf P x hℓ).bcKR = (tateFamilyOddOf P x hℓ hodd).graphLineAt w hw

/-- **`H` is the graph line at all odd multiplicative places.** -/
def IsGraphLineOdd
    (H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar))) :
    Prop :=
  ∀ (w : FinitePlace ↥(repOf P x hℓ).torsionField)
    (hw : IsBadPlace (P.curve x).E (repOf P x hℓ).torsionField (P.curve x).VBadOdd w),
    H.comap (repOf P x hℓ).bcKR = (tateFamilyOddOf P x hℓ hodd).graphLineAt w hw

lemma isGraphLineOdd_iff
    (H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar))) :
    IsGraphLineOdd P x hℓ hodd H ↔ ∀ w₀, IsGraphPlace P x hℓ hodd H w₀ :=
  ⟨fun h _ w hw _ => h w hw, fun h w hw => h _ w hw rfl⟩

/-- The local height `h_{w₀}` of the local height data is the order of the Tate parameter. -/
lemma localData_hv_eq {w₀ : FinitePlace (P.curve x).F} (hw₀ : w₀ ∈ (P.curve x).badAll) :
    (P.localData x).hv w₀ = (P.curve x).tateInputs.qOrder w₀ hw₀ := by
  change (if h : w₀ ∈ (P.curve x).badAll then (P.tate x).qOrder w₀ h else 0) = _
  rw [dif_pos hw₀]
  rfl

/-- The bad places of the local height data are the multiplicative places. -/
lemma mem_localData_bad_iff (w₀ : FinitePlace (P.curve x).F) :
    w₀ ∈ (P.localData x).bad ↔ w₀ ∈ (P.curve x).badAll :=
  (P.arith x).badAll_finite.mem_toFinset

/-- **[GenEll], Lemma 3.2(i) for `E_λ`**: under (P2) at `w₀`, a Galois-stable subgroup of order
`ℓ` is the graph line at `w₀`. -/
theorem isGraphPlace_of_not_dvd
    {H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar))}
    (hH : Nat.card H = ℓ)
    (hgal : ∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
      galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H)
    (w₀ : FinitePlace (P.curve x).F) (hP2 : ¬ ℓ ∣ (P.localData x).hv w₀) :
    IsGraphPlace P x hℓ hodd H w₀ := by
  intro w hw hww₀
  subst hww₀
  refine (repOf P x hℓ).comap_bcKR_eq_graphLineAt (tateFamilyOddOf P x hℓ hodd) hw hℓ hodd hH
    hgal ?_
  rwa [localData_hv_eq P x] at hP2

/-! ### The decomposition of `log q_∀` by the graph-line places -/

/-- **The decomposition of `log q_∀(E_λ)`** into the parts supported at the multiplicative
places where `H` is the graph line and at the others. -/
theorem h_eq_heightOn_graph_add
    (H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar))) :
    P.h x = (P.localData x).heightOn (IsGraphPlace P x hℓ hodd H) +
      (P.localData x).heightOn (fun w₀ => ¬ IsGraphPlace P x hℓ hodd H w₀) :=
  (P.localData x).height_eq_heightOn_add _

/-- **Under (P2), the places where `H` is not the graph line lie over `2`**: the non-graph
part of `log q_∀(E_λ)` is at most the `2`-adic part. -/
theorem heightOn_not_graph_le
    {H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar))}
    (hH : Nat.card H = ℓ)
    (hgal : ∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
      galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H)
    (hP2 : ∀ w ∈ (P.localData x).bad, ¬ ℓ ∣ (P.localData x).hv w) :
    (P.localData x).heightOn (fun w₀ => ¬ IsGraphPlace P x hℓ hodd H w₀) ≤
      (P.localData x).heightEq 2 := by
  rw [(P.localData x).heightEq_eq_heightOn]
  refine (P.localData x).heightOn_le_heightOn fun w₀ hw₀ hng => ?_
  by_contra h2
  exact hng (isGraphPlace_of_not_dvd P x hℓ hodd hH hgal w₀ (hP2 w₀ hw₀))

/-- On a compactly bounded subset, under (P2), the non-graph part of `log q_∀(E_λ)` is bounded
by the `2`-adic bound `max (4c) 0` (`Iut.Tripod.twoAdicBound`). -/
theorem heightOn_not_graph_le_of_mem {K : CompactlyBounded} (hx : x ∈ K.set)
    {H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar))}
    (hH : Nat.card H = ℓ)
    (hgal : ∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
      galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H)
    (hP2 : ∀ w ∈ (P.localData x).bad, ¬ ℓ ∣ (P.localData x).hv w) :
    (P.localData x).heightOn (fun w₀ => ¬ IsGraphPlace P x hℓ hodd H w₀) ≤ max (4 * K.c) 0 :=
  (heightOn_not_graph_le P x hℓ hodd hH hgal hP2).trans (twoAdicBound P K x hx)

/-! ### The residual statement and the derivation of the cyclic bound -/

variable (K : CompactlyBounded) (d : ℕ)

/-- **[GenEll], Lemma 3.5 with Proposition 3.4, for a cyclic subgroup which is the graph line
at the odd multiplicative places**: for `x ∈ K ∩ U^{≤ d}`, a prime `ℓ ≥ 7` prime to the local
heights at the places over `2`, and a Galois-stable subgroup `H ⊆ E_λ(ℚ̄)` of order `ℓ` which
is the graph line `μ_ℓ` at every multiplicative place of odd residue characteristic,
`(ℓ − 2)/24 · log q_∀(E_λ) ≤ 2 log ℓ + T_K`.

This is the part of the cyclic-subgroup bound `CyclicBoundHyp` without Lean infrastructure:
its content is (a) Lemma 3.2(i) at the places over `2` (where the Tate uniformisation of
`tate-curves-theta`, which assumes `‖2‖ = 1`, is not available), so that `H` is the graph line
at *every* multiplicative place; (b) Lemma 3.2(ii): the quotient `E_H = E_λ/H` has Tate
parameter `q^ℓ` at every multiplicative place, so `log q_∀(E_H) = ℓ · log q_∀(E_λ)`; (c) the
Faltings-height inequality `ht_Falt(E_H) ≤ ht_Falt(E_λ) + 2 log ℓ` for the degree-`ℓ` isogeny
`E_λ → E_H` ([GenEll], proof of Lemma 3.5; [FC], Chapter I, Proposition 2.7); (d) Proposition
3.4, the comparison `(1/(12(1+ε))) log q_∀ ≲ ht_Falt ≲ ((1+ε)/12) log q_∀` on compactly bounded
subsets (Silverman, *Heights and elliptic curves*, Proposition 2.1). None of (b)–(d) has a
counterpart in Mathlib (isogenies, quotient curves, Néron models, Faltings heights). Recorded as
a `Prop`, not postulated. -/
def CyclicGraphBoundHyp (TK : ℝ) : Prop :=
  ∀ x ∈ K.set ∩ ptLE d, ∀ ℓ : ℕ, ∀ hℓ : ℓ.Prime, ∀ h7 : 7 ≤ ℓ,
    (∀ w ∈ (P.localData x).bad, (P.localData x).p w = 2 → ¬ ℓ ∣ (P.localData x).hv w) →
    ∀ H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar)),
      Nat.card H = ℓ →
      (∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
        galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H) →
      IsGraphLineOdd P x hℓ (by omega) H →
      ((ℓ : ℝ) - 2) / 24 * P.h x ≤ 2 * Real.log ℓ + TK

/-- **The cyclic-subgroup bound from its residual statement**: `CyclicBoundHyp` follows from
`CyclicGraphBoundHyp` by [GenEll], Lemma 3.2(i) at the odd multiplicative places
(`isGraphPlace_of_not_dvd`). -/
theorem cyclicBound_of {TK : ℝ} (h : CyclicGraphBoundHyp P K d TK) :
    CyclicBoundHyp P K d TK := by
  intro x hx ℓ hℓ h7 hP2 hcyc
  obtain ⟨H, hH, hgal⟩ := hcyc
  refine h x hx ℓ hℓ h7 (fun w hw _ => hP2 w hw) H hH hgal ?_
  rw [isGraphLineOdd_iff]
  intro w₀
  by_cases hw₀ : w₀ ∈ (P.localData x).bad
  · exact isGraphPlace_of_not_dvd P x hℓ (by omega) hH hgal w₀ (hP2 w₀ hw₀)
  · -- a place of `K` over `VBadOdd` lies over a multiplicative place
    intro w hw hww₀
    exfalso
    apply hw₀
    rw [← hww₀, mem_localData_bad_iff P]
    exact (P.curve x).placeUnder_mem_badAll_of_isBadPlace _ hw

/-- **The facts about the curves of the points with the cyclic-subgroup bound in its residual
form**: `CurveFactsProp` from `CyclicGraphBoundHyp` and the other three fields. -/
theorem curveFactsProp_of_cyclicGraph {AG : AnabelianGeometry.{0}} {TK : ℝ}
    (height : LegendreHeightHyp P K) (cyclic : CyclicGraphBoundHyp P K d TK)
    (sl2 : SL2ImageHyp P) (core : CoreFinitenessHyp P K d AG) :
    CurveFactsProp P K d AG TK :=
  ⟨height, cyclicBound_of P K d cyclic, sl2, core⟩

end Iut.Tripod
