/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Elliptic.Chart
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The once-punctured elliptic curve `E_Λ = T_Λ ∖ {0}` ([AbsTopIII] Corollary 2.7 (a)–(c))

* `exists_sub_mem_lattice`: every `z ∈ ℂ` is congruent mod `Λ` to a point of the compact
  parallelogram `fund L = {s ω₁ + t ω₂ | s, t ∈ [0, 1]}`; hence `T_Λ` is compact
  (`instCompactSpaceTorus`);
* `isConnected_compl_finite`: `T_Λ` minus a finite set is connected;
* `isClosed_discrete_preimage`: the preimage under `mk` of a finite set has no accumulation points;
* `punct L`, `ellStr L`: the once-punctured curve `E_Λ = T_Λ ∖ {0}` with its Aut-holomorphic
  structure (the Aut-holomorphic space `E` of Corollary 2.7 (a));
* `onePointEquiv L : OnePoint E_Λ ≃ₜ T_Λ` (`∞ ↦ 0`): `T_Λ` is the one-point compactification of
  `E_Λ`.
-/

namespace Iut

namespace AutHol

namespace Ell

open Set Topology Filter TopologicalSpace Metric Torus

variable {L : PeriodPair}

/-! ### Compactness -/

/-- The fundamental parallelogram. -/
def fund (L : PeriodPair) : Set ℂ :=
  (fun p : ℝ × ℝ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂) '' (Icc 0 1 ×ˢ Icc 0 1)

theorem isCompact_fund : IsCompact (fund L) :=
  (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

theorem exists_real_coords (z : ℂ) : ∃ s t : ℝ, (s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂ = z := by
  refine ⟨L.basis.repr z 0, L.basis.repr z 1, ?_⟩
  have := L.basis.sum_repr z
  rw [Fin.sum_univ_two, PeriodPair.basis_zero, PeriodPair.basis_one] at this
  rw [← Complex.real_smul, ← Complex.real_smul]
  exact this

/-- Every point of `ℂ` is congruent mod `Λ` to a point of the fundamental parallelogram. -/
theorem exists_sub_mem_lattice (z : ℂ) : ∃ p ∈ fund L, z - p ∈ L.lattice := by
  obtain ⟨s, t, rfl⟩ := exists_real_coords (L := L) z
  refine ⟨((Int.fract s : ℝ) : ℂ) * L.ω₁ + ((Int.fract t : ℝ) : ℂ) * L.ω₂,
    ⟨(Int.fract s, Int.fract t), ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩,
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩, rfl⟩, ?_⟩
  rw [PeriodPair.mem_lattice]
  refine ⟨⌊s⌋, ⌊t⌋, ?_⟩
  rw [Int.fract, Int.fract]
  push_cast
  ring

theorem mk_image_fund : mk L '' fund L = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨z, rfl⟩ := mk_surjective (L := L) x
  obtain ⟨p, hp, hzp⟩ := exists_sub_mem_lattice (L := L) z
  exact ⟨p, hp, mk_eq_mk.2 (by rw [← neg_mem_iff, neg_sub]; exact hzp)⟩

instance instCompactSpaceTorus : CompactSpace (Torus L) :=
  ⟨by rw [← mk_image_fund]; exact isCompact_fund.image continuous_mk⟩

/-- A continuous `Λ`-periodic function is bounded. -/
theorem exists_bound_of_periodic {h : ℂ → ℂ} (hc : Continuous h)
    (hp : ∀ z, ∀ l ∈ L.lattice, h (z + l) = h z) : ∃ M, ∀ z, ‖h z‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_fund (L := L)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun z => ?_⟩
  obtain ⟨p, hp', hzp⟩ := exists_sub_mem_lattice (L := L) z
  have : h z = h p := by
    have := hp p (z - p) hzp
    rwa [add_sub_cancel] at this
  rw [this]
  exact hM p hp'

/-! ### Connectedness and discreteness -/

theorem countable_lattice : (L.lattice : Set ℂ).Countable := by
  refine (countable_range fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂).mono ?_
  intro x hx
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hx
  exact ⟨(m, n), rfl⟩

theorem countable_preimage_mk {K : Set (Torus L)} (hK : K.Countable) :
    (mk L ⁻¹' K).Countable := by
  have : mk L ⁻¹' K ⊆ ⋃ x ∈ K, (fun l => (mk_surjective x).choose + l) '' (L.lattice : Set ℂ) := by
    intro z hz
    refine mem_biUnion hz ⟨z - (mk_surjective (mk L z)).choose, ?_, by ring⟩
    have := (mk_surjective (L := L) (mk L z)).choose_spec
    exact mk_eq_mk.1 this.symm
  exact (hK.biUnion fun x _ => countable_lattice.image _).mono this

theorem one_lt_rank_complex : 1 < Module.rank ℝ ℂ := by
  rw [Complex.rank_real_complex]
  exact Cardinal.one_lt_two

/-- `ℂ` minus the preimage of a countable subset of `T_Λ` is connected. -/
theorem isConnected_compl_preimage {K : Set (Torus L)} (hK : K.Countable) :
    IsConnected (mk L ⁻¹' K)ᶜ :=
  (countable_preimage_mk hK).isConnected_compl_of_one_lt_rank one_lt_rank_complex

/-- **`T_Λ` minus a countable set is connected.** -/
theorem isConnected_compl_countable {K : Set (Torus L)} (hK : K.Countable) : IsConnected Kᶜ := by
  have h := (isConnected_compl_preimage hK).image (mk L) continuous_mk.continuousOn
  convert h using 1
  ext x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := mk_surjective (L := L) x
    exact ⟨z, hx, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact hz

/-- **The preimage under `mk` of a finite set has no accumulation points.** -/
theorem eventually_notMem_preimage {K : Set (Torus L)} (hK : K.Finite) (d : ℂ) :
    ∀ᶠ z in 𝓝[≠] d, mk L z ∉ K := by
  obtain ⟨ρ, hρ0, hρ⟩ := exists_sep L
  have hinj : InjOn (mk L) (ball d (ρ / 2)) := injOn_mk_ball hρ (by linarith) d
  have hcl : IsClosed (K \ {mk L d}) := hK.sdiff.isClosed
  have hO : (K \ {mk L d})ᶜ ∈ 𝓝 (mk L d) := hcl.isOpen_compl.mem_nhds (by simp)
  have h1 : ∀ᶠ z in 𝓝 d, mk L z ∈ (K \ {mk L d})ᶜ := continuous_mk.continuousAt.preimage_mem_nhds hO
  have h2 : ∀ᶠ z in 𝓝 d, z ∈ ball d (ρ / 2) := ball_mem_nhds d (by positivity)
  have h3 : ∀ᶠ z in 𝓝[≠] d, z ≠ d := self_mem_nhdsWithin
  filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, h3] with z hz1 hz2 hz3 hzK
  have hzd : mk L z = mk L d := by
    by_contra hne
    exact hz1 ⟨hzK, hne⟩
  exact hz3 (hinj hz2 (mem_ball_self (by positivity)) hzd)

/-! ### The once-punctured curve -/

/-- **The once-punctured elliptic curve** `E_Λ = T_Λ ∖ {0}`. -/
def punct (L : PeriodPair) : Opens (Torus L) := ⟨{0}ᶜ, isOpen_compl_singleton⟩

/-- **The Aut-holomorphic space `E_Λ`** ([AbsTopIII] Corollary 2.7 (a): the Aut-holomorphic space
associated to a once-punctured elliptic curve). -/
noncomputable def ellStr (L : PeriodPair) : AutHolStr (punct L) := (torusStr L).restrict (punct L)

theorem range_val_punct : range (Subtype.val : punct L → Torus L) = {0}ᶜ := by
  ext x
  simp [punct]

/-- **`T_Λ` is the one-point compactification of `E_Λ`**, with `∞ ↦ 0`. -/
noncomputable def onePointEquiv (L : PeriodPair) : OnePoint (punct L) ≃ₜ Torus L :=
  OnePoint.equivOfIsEmbeddingOfRangeEq 0 Subtype.val IsEmbedding.subtypeVal range_val_punct

@[simp]
theorem onePointEquiv_coe (x : punct L) : onePointEquiv L x = x := rfl

@[simp]
theorem onePointEquiv_infty : onePointEquiv L OnePoint.infty = 0 := rfl

theorem onePointEquiv_symm_of_ne {x : Torus L} (hx : x ≠ 0) :
    (onePointEquiv L).symm x = ((⟨x, hx⟩ : punct L) : OnePoint (punct L)) := by
  rw [Homeomorph.symm_apply_eq]
  rfl

theorem onePointEquiv_symm_zero : (onePointEquiv L).symm 0 = OnePoint.infty := by
  rw [Homeomorph.symm_apply_eq]
  rfl

end Ell

end AutHol

end Iut
