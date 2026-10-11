/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.Volume

/-!
# The admissible class of the holomorphic hull (taxis #4, #278)

The **admissible regions** of a packet (IUT III, Remark 3.9.5(i)) are the nonempty,
relatively compact, measurable regions of positive finite Haar measure (`admissible`,
`Iut.LocalTheory.admissible`). This file proves `admissible_nonempty`,
`admissible_relCompact`, `integral_admissible`, `smul_integral_admissible`, and restates
the scaling law of the log-volume for admissible regions.

## Least hull regions at the archimedean place

At the archimedean place the hull regions are the regions `a·B_I` with `a` a unit of the
packet, i.e. with every component of `a` in the direct sum decomposition of the packet into
copies of `ℝ` and `ℂ` nonzero (IUT III, Remark 3.9.5(i)). These are the polydiscs with radii
`‖archChar 𝔪 a‖` (`mem_smul_archIntegral_iff`, `Archimedean.lean`), and the least one
containing an admissible region `U` is computed componentwise: its radius at `𝔪` is
`sup_{x ∈ U} ‖archChar 𝔪 x‖` (`exists_leastHull_infinite`,
`Iut.LocalTheory.exists_leastHull_infinite`), positive because a region of positive Haar
measure is not contained in the kernel of a component. The real radial scalings `t·B_I` are
monotone in `t` (`smul_integralAt_infinite_mono`).

## Least hull regions at a prime

At a prime, the existence of a *least* hull region `a·(R_I)^∼` (`a` a unit) containing an
admissible region is proved in `Hull.lean` (`exists_leastHull_finite`), through the
decomposition of the packet `⊗_j K_{c j}` into the product of its residue fields
(`ResidueField.lean`), for which `(R_I)^∼` is the product of the rings of integers and the
hull regions are the products of closed balls, whose least upper bound is computed
componentwise. For the order `R_I = ⊗_{ℤ_p} 𝓞_{c j}` (as opposed to its normalization)
least hull regions need not exist at all, since `R_I` is in general only an order in the
ring of integers of the packet.
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

/-! ### Least hull regions at the archimedean place -/

variable (c)

/-- **Radial monotonicity of `B_I`**: `t·B_I ⊆ t'·B_I` for `0 < t ≤ t'`
(`LocalTheory.smul_integral_infinite_mono`). -/
theorem smul_integralAt_infinite_mono (t t' : ℝ) (ht : 0 < t) (htt' : t ≤ t') :
    algebraMap ℝ (Tensor K .infinite c) t • integralAt .infinite c ⊆
      algebraMap ℝ (Tensor K .infinite c) t' • integralAt .infinite c := by
  rw [integralAt_infinite]
  intro x hx
  exact (mem_algebraMap_smul_archIntegral (ht.trans_le htt')).mpr fun m =>
    ((mem_algebraMap_smul_archIntegral ht).mp hx m).trans htt'

/-- A region of positive Haar measure has, at every maximal ideal `𝔪`, a point with nonzero
`𝔪`-component: the kernel of a component is a proper subspace, of Haar measure zero
(`MeasureTheory.Measure.addHaar_submodule`). -/
lemma exists_archChar_ne_zero_of_haar_pos {U : Set (Tensor K .infinite c)}
    (hU : 0 < haar .infinite c U) (m : MaximalSpectrum (Tensor K .infinite c)) :
    ∃ x ∈ U, archChar c m x ≠ 0 := by
  by_contra h
  push Not at h
  have hsub : U ⊆ (LinearMap.ker (archChar c m).toLinearMap : Set (Tensor K .infinite c)) :=
    fun x hx => h x hx
  have hne : LinearMap.ker (archChar c m).toLinearMap ≠ ⊤ := by
    intro htop
    have h1 : (1 : Tensor K .infinite c) ∈ LinearMap.ker (archChar c m).toLinearMap :=
      htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, map_one] at h1
    exact one_ne_zero h1
  exact absurd hU (not_lt.mpr ((measure_mono hsub).trans
    (Measure.addHaar_submodule (haar .infinite c) _ hne).le))

/-- **Existence of least hull regions at the archimedean place** (IUT III, Remark 3.9.5(i);
`LocalTheory.exists_leastHull_infinite`): every admissible region `U` of an archimedean packet
is contained in a least region `a·B_I` with `a` a unit, i.e. with every component of `a`
nonzero. It is the polydisc whose radius at a maximal ideal `𝔪` is the supremum
`M_𝔪 = sup_{x ∈ U} ‖x mod 𝔪‖`, finite since `U` is bounded and positive since `U` has positive
Haar measure (`exists_archChar_ne_zero_of_haar_pos`); by the Chinese remainder theorem it is
`a·B_I` for an element `a` with real components `M_𝔪` (`exists_forall_archChar_eq`). -/
theorem exists_leastHull_infinite {U : Set (Tensor K .infinite c)}
    (hU : U ∈ admissible .infinite c) :
    ∃ a : Tensor K .infinite c, IsUnit a ∧ U ⊆ a • integralAt .infinite c ∧
      ∀ b : Tensor K .infinite c, IsUnit b → U ⊆ b • integralAt .infinite c →
        a • integralAt .infinite c ⊆ b • integralAt .infinite c := by
  rw [integralAt_infinite]
  have hne := admissible_nonempty hU
  set M : MaximalSpectrum (Tensor K .infinite c) → ℝ :=
    fun m => sSup ((fun x => ‖archChar c m x‖) '' U) with hM
  have hMbdd : ∀ m, BddAbove ((fun x => ‖archChar c m x‖) '' U) := fun m =>
    ((admissible_relCompact hU).image
      (continuous_norm.comp (continuous_archChar c m))).bddAbove.mono
        (Set.image_mono subset_closure)
  have hMle : ∀ m, ∀ x ∈ U, ‖archChar c m x‖ ≤ M m := fun m x hx =>
    le_csSup (hMbdd m) ⟨x, hx, rfl⟩
  have hMpos : ∀ m, 0 < M m := fun m => by
    obtain ⟨x, hx, hx0⟩ := exists_archChar_ne_zero_of_haar_pos c (admissible_haar_pos hU) m
    exact (norm_pos_iff.mpr hx0).trans_le (hMle m x hx)
  have hMsup : ∀ m (t : ℝ), (∀ x ∈ U, ‖archChar c m x‖ ≤ t) → M m ≤ t :=
    fun m t ht => csSup_le (hne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact ht x hx)
  obtain ⟨a, ha⟩ := exists_forall_archChar_eq c M
  have hna : ∀ m, ‖archChar c m a‖ = M m := fun m => by
    rw [ha m, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hMpos m)]
  have haU : IsUnit a := (isUnit_iff_forall_archChar_ne_zero c).mpr fun m h0 => by
    have := hna m
    rw [h0, norm_zero] at this
    exact (hMpos m).ne this
  refine ⟨a, haU, fun x hx => ?_, fun b hb hUb => ?_⟩
  · rw [mem_smul_archIntegral_iff haU]
    intro m
    rw [hna m]
    exact hMle m x hx
  · intro x hx
    rw [mem_smul_archIntegral_iff haU] at hx
    rw [mem_smul_archIntegral_iff hb]
    intro m
    refine (hx m).trans ?_
    rw [hna m]
    exact hMsup m _ fun y hy => (mem_smul_archIntegral_iff hb).mp (hUb hy) m

end LocalConstruct

end Iut
