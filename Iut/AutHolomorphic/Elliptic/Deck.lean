/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Elliptic.Lift
import Iut.AutHolomorphic.Cusp

/-!
# Deck transformations of the cuspidalisations induced by isogenies

Let `f : T_Λ → T_Λ` be a continuous group endomorphism, `U = {x ∈ E_Λ | f x ≠ 0}` and
`q = f|_U : U → E_Λ` (for `f = [N]`: the diagram `E ⊇ U → E` of [AbsTopII] Example 3.2 (i)).
Then:

* `cuspExt_eq`: under `OnePoint E_Λ ≃ₜ T_Λ`, the extension `cuspExt U q` is `f`;
* `translU`, `translU_mem_deck`: translation by `t ∈ ker f` is a deck transformation;
* `exists_eq_translU`: if `U` has finite complement and `q` is locally injective, every deck
  transformation is such a translation (`U` is connected: `preconnectedSpace_of_finite_compl`);
* `cuspLim_iff`: the extension of the translation by `t` sends `∞` to `t`.
-/

namespace Iut

namespace AutHol

namespace Ell

open Set Topology Filter TopologicalSpace Metric Torus OnePoint

variable {L : PeriodPair}

instance : T2Space (OnePoint (punct L)) := (onePointEquiv L).isEmbedding.t2Space

theorem onePointEquiv_symm_coe (x : punct L) :
    (onePointEquiv L).symm (x : Torus L) = ((x : punct L) : OnePoint (punct L)) := by
  rw [Homeomorph.symm_apply_eq]
  rfl

/-- The points of `U ⊆ E_Λ`, as points of `T_Λ`. -/
def jU (U : Opens (punct L)) (x : U) : Torus L := ((x : punct L) : Torus L)

theorem continuous_jU (U : Opens (punct L)) : Continuous (jU U) :=
  continuous_subtype_val.comp continuous_subtype_val

/-- An open subset of `E_Λ` with finite complement is connected. -/
theorem preconnectedSpace_of_finite_compl (U : Opens (punct L))
    (h : (U : Set (punct L))ᶜ.Finite) : PreconnectedSpace U ∧ Nonempty U := by
  set K : Set (Torus L) := insert 0 (Subtype.val '' (U : Set (punct L))ᶜ)
  have hK : K.Finite := (h.image _).insert 0
  have hc := isConnected_compl_countable hK.countable
  have hrange : range (jU U) = Kᶜ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      simp only [K, mem_compl_iff, mem_insert_iff, mem_image, not_or]
      refine ⟨(y : punct L).2, ?_⟩
      rintro ⟨z, hz, hzy⟩
      exact hz (by rw [Subtype.ext hzy]; exact y.2)
    · intro hx
      simp only [K, mem_compl_iff, mem_insert_iff, mem_image, not_or] at hx
      have hU : (⟨x, hx.1⟩ : punct L) ∈ U := by
        by_contra hn
        exact hx.2 ⟨_, hn, rfl⟩
      exact ⟨⟨⟨x, hx.1⟩, hU⟩, rfl⟩
  have hind : IsInducing (jU U) := IsInducing.subtypeVal.comp IsInducing.subtypeVal
  refine ⟨⟨?_⟩, ?_⟩
  · rw [← hind.isPreconnected_image, image_univ, hrange]
    exact hc.isPreconnected
  · obtain ⟨x, hx⟩ := hc.nonempty
    rw [← hrange] at hx
    obtain ⟨y, -⟩ := hx
    exact ⟨y⟩

section Hom

variable (f : Torus L →+ Torus L) {U : Opens (punct L)} (hU : ∀ x : punct L, x ∈ U ↔ f x ≠ 0)
include hU

theorem f_ne_zero (x : U) : f (jU U x) ≠ 0 := (hU x).1 x.2

theorem add_ne_zero_of_ker (x : U) {t : Torus L} (ht : f t = 0) : jU U x + t ≠ 0 := by
  intro h
  have := congrArg f h
  rw [map_add, ht, add_zero, map_zero] at this
  exact f_ne_zero f hU x this

/-- The translation by `t ∈ ker f`, as a map of `U`. -/
def translFun {t : Torus L} (ht : f t = 0) (x : U) : U :=
  ⟨⟨jU U x + t, add_ne_zero_of_ker f hU x ht⟩, (hU _).2 (by
    change f (jU U x + t) ≠ 0
    rw [map_add, ht, add_zero]
    exact f_ne_zero f hU x)⟩

theorem continuous_translFun {t : Torus L} (ht : f t = 0) : Continuous (translFun f hU ht) :=
  (((continuous_jU U).add continuous_const).subtype_mk _).subtype_mk _

/-- **The translation by `t ∈ ker f`** as a homeomorphism of `U`. -/
def translU {t : Torus L} (ht : f t = 0) : U ≃ₜ U where
  toFun := translFun f hU ht
  invFun := translFun f hU (t := -t) (by rw [map_neg, ht, neg_zero])
  left_inv x := Subtype.ext (Subtype.ext (by simp [translFun, jU]))
  right_inv x := Subtype.ext (Subtype.ext (by simp [translFun, jU]))
  continuous_toFun := continuous_translFun f hU ht
  continuous_invFun := continuous_translFun f hU _

theorem jU_translU {t : Torus L} (ht : f t = 0) (x : U) :
    jU U (translU f hU ht x) = jU U x + t := rfl

variable {q : U → punct L} (hq : ∀ x, (q x : Torus L) = f (jU U x))
include hq

theorem translU_mem_deck {t : Torus L} (ht : f t = 0) : translU f hU ht ∈ deck q := by
  intro x
  apply Subtype.ext
  rw [hq, hq, jU_translU, map_add, ht, add_zero]

/-- **Every deck transformation is a translation by an element of `ker f`.** -/
theorem exists_eq_translU (hfin : (U : Set (punct L))ᶜ.Finite) (hql : IsLocallyInjective q)
    {g : U ≃ₜ U} (hg : g ∈ deck q) : ∃ t, ∃ ht : f t = 0, g = translU f hU ht := by
  obtain ⟨hpc, ⟨x₀⟩⟩ := preconnectedSpace_of_finite_compl U hfin
  set t := jU U (g x₀) - jU U x₀
  have ht : f t = 0 := by
    have h1 := congrArg Subtype.val (hg x₀)
    rw [hq, hq] at h1
    simp only [t, map_sub, h1, sub_self]
  refine ⟨t, ht, ?_⟩
  have := (T2Space.isSeparatedMap q).eq_of_comp_eq hql g.continuous (translU f hU ht).continuous
    (funext fun x => by
      simp only [Function.comp_apply]
      rw [hg x, translU_mem_deck f hU hq ht x]) x₀
    (Subtype.ext (Subtype.ext (by
      change jU U (g x₀) = jU U x₀ + t
      simp [t])))
  ext x
  rw [this]

end Hom

/-! ### Limits at the cusp -/

theorem comap_nhds_infty (U : Opens (punct L)) :
    comap (fun x : U => ((x : punct L) : OnePoint (punct L))) (𝓝 ∞) = comap (jU U) (𝓝 0) := by
  have h1 : 𝓝 (∞ : OnePoint (punct L)) = comap (onePointEquiv L) (𝓝 0) := by
    rw [← onePointEquiv_infty, Homeomorph.comap_nhds_eq, Homeomorph.symm_apply_apply]
  rw [h1, comap_comap]
  rfl

theorem neBot_comap (U : Opens (punct L)) (hfin : (U : Set (punct L))ᶜ.Finite) :
    (comap (jU U) (𝓝 0)).NeBot := by
  rw [comap_neBot_iff]
  intro s hs
  set K : Set (Torus L) := insert 0 (Subtype.val '' (U : Set (punct L))ᶜ)
  have hK : K.Finite := (hfin.image _).insert 0
  have h1 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), mk L z ∈ s :=
    nhdsWithin_le_nhds (continuous_mk.continuousAt.preimage_mem_nhds (by rwa [mk_zero]))
  obtain ⟨z, hz1, hz2⟩ := (h1.and (eventually_notMem_preimage hK 0)).exists
  simp only [K, mem_insert_iff, mem_image, not_or] at hz2
  have hU : (⟨mk L z, hz2.1⟩ : punct L) ∈ U := by
    by_contra hn
    exact hz2.2 ⟨_, hn, rfl⟩
  exact ⟨⟨⟨mk L z, hz2.1⟩, hU⟩, hz1⟩

/-- **The extension of a translation by `t` sends `∞` to `t`.** -/
theorem cuspLim_iff {U : Opens (punct L)} (hfin : (U : Set (punct L))ᶜ.Finite) {g : U → U}
    {t : Torus L} (hg : ∀ x, jU U (g x) = jU U x + t) (y : OnePoint (punct L)) :
    CuspLim U g y ↔ y = (onePointEquiv L).symm t := by
  have hlim : CuspLim U g ((onePointEquiv L).symm t) := by
    unfold CuspLim
    rw [comap_nhds_infty]
    have h1 : Tendsto (fun x => jU U x + t) (comap (jU U) (𝓝 0)) (𝓝 (0 + t)) :=
      tendsto_comap.add_const t
    rw [zero_add] at h1
    have h2 := ((onePointEquiv L).symm.continuous.tendsto t).comp h1
    refine h2.congr fun x => ?_
    simp only [Function.comp_apply]
    rw [← hg x]
    exact onePointEquiv_symm_coe _
  haveI := neBot_comap U hfin
  constructor
  · intro h
    unfold CuspLim at h hlim
    rw [comap_nhds_infty] at h hlim
    exact tendsto_nhds_unique h hlim
  · rintro rfl
    exact hlim

/-! ### The extension of `q` -/

/-- Under `OnePoint E_Λ ≃ₜ T_Λ`, the extension of `q = f|_U` to the one-point compactification is
`f`. -/
theorem cuspExt_eq (f : Torus L → Torus L) (hf0 : f 0 = 0) {U : Opens (punct L)}
    (hU : ∀ x : punct L, x ∈ U ↔ f x ≠ 0) {q : U → punct L}
    (hq : ∀ x, (q x : Torus L) = f (jU U x)) :
    cuspExt U q = (onePointEquiv L).symm ∘ f ∘ onePointEquiv L := by
  funext x
  induction x using OnePoint.rec with
  | infty => simp [hf0, onePointEquiv_symm_zero]
  | coe y =>
    simp only [Function.comp_apply, onePointEquiv_coe]
    by_cases hy : y ∈ U
    · rw [cuspExt_of_mem U q ⟨y, hy⟩, onePointEquiv_symm_of_ne ((hU y).1 hy)]
      congr 1
      exact Subtype.ext (hq ⟨y, hy⟩)
    · rw [cuspExt_of_notMem U q hy]
      have : f y = 0 := by
        by_contra hn
        exact hy ((hU y).2 hn)
      rw [this, onePointEquiv_symm_zero]

end Ell

end AutHol

end Iut
