/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Cusp

/-!
# Functoriality of holomorphic elliptic cuspidalisation

The constructions of `Cusp.lean` ([AbsTopIII] Corollary 2.7 (b), (c)) use only `E^top` and the
Aut-holomorphic structure `A`, so they are carried along isomorphisms of Aut-holomorphic spaces.
For an isomorphism `φ : (E, A) ≅ (E', A')` with extension `φ̄` to the one-point compactifications:

* `isEllCusp_transport`: `φ` carries elliptic cuspidalisation diagrams to diagrams;
* `mem_cuspTors_transport`: `φ̄` carries the torsion points onto the torsion points;
* `cuspSum_transport`: `φ̄` respects their group law;
* `isRecAdd_transport`, `recAdd_transport`: `φ̄` carries the group law of Corollary 2.7 (c).
-/

namespace Iut

namespace AutHol

open Set Topology Filter TopologicalSpace OnePoint

variable {E E' : Type*} [TopologicalSpace E] [TopologicalSpace E']

section Transport

variable (φ : E ≃ₜ E')

/-- The image of an open subset. -/
def imOpen (U : Opens E) : Opens E' := ⟨φ '' U, φ.isOpenMap _ U.2⟩

/-- `φ` restricted to `U`. -/
def imHomeo (U : Opens E) : U ≃ₜ imOpen φ U := φ.image U

@[simp]
theorem imHomeo_apply (U : Opens E) (x : U) : (imHomeo φ U x : E') = φ x := rfl

theorem imHomeo_symm_apply (U : Opens E) (y : imOpen φ U) :
    ((imHomeo φ U).symm y : E) = φ.symm y := by
  have := congrArg Subtype.val ((imHomeo φ U).apply_symm_apply y)
  rw [imHomeo_apply] at this
  rw [← this, Homeomorph.symm_apply_apply]

/-- The transported map `φ q φ⁻¹ : φ(U) → E'`. -/
def trQ (U : Opens E) (q : U → E) (y : imOpen φ U) : E' := φ (q ((imHomeo φ U).symm y))

theorem mem_imOpen_iff {U : Opens E} {y : E'} : y ∈ imOpen φ U ↔ φ.symm y ∈ U := by
  change y ∈ φ '' U ↔ _
  rw [← φ.preimage_symm, mem_preimage]
  rfl

theorem onePointCongr_symm_eq :
    (φ.symm.onePointCongr : OnePoint E' → OnePoint E) = φ.onePointCongr.symm := rfl

@[simp]
theorem onePointCongr_symm_apply' (y : OnePoint E') :
    φ.symm.onePointCongr y = φ.onePointCongr.symm y := rfl

@[simp]
theorem onePointCongr_symm_symm_apply' (x : OnePoint E) :
    φ.symm.onePointCongr.symm x = φ.onePointCongr x := rfl

theorem cuspExt_transport (U : Opens E) (q : U → E) :
    cuspExt (imOpen φ U) (trQ φ U q) =
      φ.onePointCongr ∘ cuspExt U q ∘ φ.onePointCongr.symm := by
  funext x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe y =>
    simp only [Function.comp_apply, Homeomorph.onePointCongr_symm_apply, map_some]
    by_cases hy : y ∈ imOpen φ U
    · have hy' : φ.symm y ∈ U := (mem_imOpen_iff φ).1 hy
      rw [cuspExt_of_mem _ _ ⟨y, hy⟩, cuspExt_of_mem U q ⟨φ.symm y, hy'⟩,
        Homeomorph.onePointCongr_apply, map_some]
      congr 2
    · have hy' : φ.symm y ∉ U := fun h => hy ((mem_imOpen_iff φ).2 h)
      rw [cuspExt_of_notMem _ _ hy, cuspExt_of_notMem U q hy']
      rfl

theorem mem_deck_transport {U : Opens E} {q : U → E} {g : U ≃ₜ U} (hg : g ∈ deck q) :
    conj (imHomeo φ U) g ∈ deck (trQ φ U q) := by
  intro y
  simp only [trQ, conj_apply, Homeomorph.symm_apply_apply]
  rw [hg]

theorem mem_deck_transport_iff {U : Opens E} {q : U → E} (g' : imOpen φ U ≃ₜ imOpen φ U) :
    g' ∈ deck (trQ φ U q) ↔ conj (imHomeo φ U).symm g' ∈ deck q := by
  constructor
  · intro hg x
    have := hg (imHomeo φ U x)
    simp only [trQ, Homeomorph.symm_apply_apply] at this
    exact φ.injective this
  · intro hg
    have := mem_deck_transport φ hg
    have h2 : conj (imHomeo φ U) (conj (imHomeo φ U).symm g') = g' := by ext; simp
    rwa [h2] at this

/-- **Isomorphisms carry elliptic cuspidalisation diagrams to diagrams.** -/
theorem isEllCusp_transport {A : AutHolStr E} {A' : AutHolStr E'} (hφ : IsIso A A' φ)
    {U : Opens E} {q : U → E} (hc : IsEllCusp A U q) :
    IsEllCusp A' (imOpen φ U) (trQ φ U q) := by
  obtain ⟨hfin, hmor, hqcov, hqfin, hgal, hab⟩ := hc
  have hiso : IsIso (A.restrict U) (A'.restrict (imOpen φ U)) (imHomeo φ U) :=
    isIso_of_isMorphism (IsMorphism.comp hφ (AutHolStr.isMorphism_val A U)) _ fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (hfin.image φ).subset fun y hy => ⟨φ.symm y, fun h => hy ((mem_imOpen_iff φ).2 h),
      φ.apply_symm_apply y⟩
  · exact IsMorphism.comp hφ (hmor.comp (IsIso.symm hiso))
  · exact (hqcov.comp_homeomorph (imHomeo φ U).symm).homeomorph_comp φ
  · intro y
    refine ((hqfin (φ.symm y)).image (imHomeo φ U)).subset fun x hx => ⟨(imHomeo φ U).symm x, ?_,
      Homeomorph.apply_symm_apply _ _⟩
    change q _ = φ.symm y
    rw [← show trQ φ U q x = y from hx, trQ, Homeomorph.symm_apply_apply]
  · intro x y hxy
    have h1 : q ((imHomeo φ U).symm x) = q ((imHomeo φ U).symm y) := φ.injective hxy
    obtain ⟨g, hg, hgxy⟩ := hgal _ _ h1
    refine ⟨conj (imHomeo φ U) g, mem_deck_transport φ hg, ?_⟩
    simp [hgxy]
  · intro g hg h hh
    rw [mem_deck_transport_iff] at hg hh
    have := hab _ hg _ hh
    have e : ∀ k : imOpen φ U ≃ₜ imOpen φ U,
        conj (imHomeo φ U) (conj (imHomeo φ U).symm k) = k := fun k => by ext; simp
    calc g * h = conj (imHomeo φ U) (conj (imHomeo φ U).symm g * conj (imHomeo φ U).symm h) := by
          rw [map_mul, e, e]
      _ = conj (imHomeo φ U) (conj (imHomeo φ U).symm h * conj (imHomeo φ U).symm g) := by
          rw [this]
      _ = h * g := by rw [map_mul, e, e]

theorem comap_infty_transport (U : Opens E) :
    comap (fun x : imOpen φ U => ((x : E') : OnePoint E')) (𝓝 ∞) =
      map (imHomeo φ U) (comap (fun x : U => ((x : E) : OnePoint E)) (𝓝 ∞)) := by
  rw [map_eq_comap_of_inverse (n := (imHomeo φ U).symm) (funext fun y => by simp)
    (funext fun x => by simp), comap_comap]
  have h1 : (fun x : U => ((x : E) : OnePoint E)) ∘ (imHomeo φ U).symm =
      φ.onePointCongr.symm ∘ fun x : imOpen φ U => ((x : E') : OnePoint E') := by
    funext y
    simp only [Function.comp_apply, Homeomorph.onePointCongr_symm_apply, map_some,
      imHomeo_symm_apply]
  rw [h1, ← comap_comap, Homeomorph.comap_nhds_eq]
  rfl

/-- **Isomorphisms respect the limits at `∞`** of deck transformations. -/
theorem cuspLim_transport {U : Opens E} (g : U ≃ₜ U) (y : OnePoint E) :
    CuspLim (imOpen φ U) (conj (imHomeo φ U) g) (φ.onePointCongr y) ↔ CuspLim U g y := by
  unfold CuspLim
  rw [comap_infty_transport, tendsto_map'_iff, φ.onePointCongr.isInducing.tendsto_nhds_iff]
  apply Iff.of_eq
  congr 1
  funext x
  simp [Homeomorph.onePointCongr_apply]

end Transport

variable {A : AutHolStr E} {A' : AutHolStr E'} {φ : E ≃ₜ E'}

theorem mem_cuspTors_of_transport (hφ : IsIso A A' φ) {y : OnePoint E} (hy : y ∈ cuspTors A) :
    φ.onePointCongr y ∈ cuspTors A' := by
  rcases hy with rfl | ⟨U, q, hc, x, hx, rfl⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨imOpen φ U, trQ φ U q, isEllCusp_transport φ hφ hc, φ x, ?_, rfl⟩
    rw [mem_imOpen_iff, Homeomorph.symm_apply_apply]
    exact hx

/-- **Isomorphisms carry the torsion points onto the torsion points.** -/
theorem mem_cuspTors_transport (hφ : IsIso A A' φ) (y : OnePoint E) :
    φ.onePointCongr y ∈ cuspTors A' ↔ y ∈ cuspTors A := by
  refine ⟨fun h => ?_, mem_cuspTors_of_transport hφ⟩
  have := mem_cuspTors_of_transport (φ := φ.symm) (IsIso.symm hφ) h
  rwa [onePointCongr_symm_apply', Homeomorph.symm_apply_apply] at this

theorem cuspSum_of_transport (hφ : IsIso A A' φ) {x y z : OnePoint E} (h : CuspSum A x y z) :
    CuspSum A' (φ.onePointCongr x) (φ.onePointCongr y) (φ.onePointCongr z) := by
  obtain ⟨U, q, hc, g, hg, k, hk, hgx, hky, hgkz⟩ := h
  refine ⟨imOpen φ U, trQ φ U q, isEllCusp_transport φ hφ hc, conj (imHomeo φ U) g,
    mem_deck_transport φ hg, conj (imHomeo φ U) k, mem_deck_transport φ hk,
    (cuspLim_transport φ g x).2 hgx, (cuspLim_transport φ k y).2 hky, ?_⟩
  rw [← map_mul]
  exact (cuspLim_transport φ (g * k) z).2 hgkz

/-- **Isomorphisms respect the group law of the torsion points.** -/
theorem cuspSum_transport (hφ : IsIso A A' φ) (x y z : OnePoint E) :
    CuspSum A' (φ.onePointCongr x) (φ.onePointCongr y) (φ.onePointCongr z) ↔ CuspSum A x y z := by
  refine ⟨fun h => ?_, cuspSum_of_transport hφ⟩
  have := cuspSum_of_transport (φ := φ.symm) (IsIso.symm hφ) h
  simpa only [onePointCongr_symm_apply', Homeomorph.symm_apply_apply] using this

/-- The transport of a binary operation along `φ̄`. -/
def trOp (φ : E ≃ₜ E') (μ : OnePoint E → OnePoint E → OnePoint E) :
    OnePoint E' → OnePoint E' → OnePoint E' :=
  fun x y => φ.onePointCongr (μ (φ.onePointCongr.symm x) (φ.onePointCongr.symm y))

theorem isRecAdd_of_transport (hφ : IsIso A A' φ) {μ : OnePoint E → OnePoint E → OnePoint E}
    (h : IsRecAdd A μ) : IsRecAdd A' (trOp φ μ) := by
  obtain ⟨hc, hs⟩ := h
  refine ⟨φ.onePointCongr.continuous.comp (hc.comp
    ((φ.onePointCongr.symm.continuous.comp continuous_fst).prodMk
      (φ.onePointCongr.symm.continuous.comp continuous_snd))), fun x hx y hy => ?_⟩
  have hx' : φ.onePointCongr.symm x ∈ cuspTors A := by
    rw [← mem_cuspTors_transport hφ, Homeomorph.apply_symm_apply]; exact hx
  have hy' : φ.onePointCongr.symm y ∈ cuspTors A := by
    rw [← mem_cuspTors_transport hφ, Homeomorph.apply_symm_apply]; exact hy
  have := cuspSum_of_transport hφ (hs _ hx' _ hy')
  simp only [Homeomorph.apply_symm_apply] at this
  exact this

/-- **Isomorphisms carry the group law of [AbsTopIII] Corollary 2.7 (c).** -/
theorem isRecAdd_transport (hφ : IsIso A A' φ) (ν : OnePoint E' → OnePoint E' → OnePoint E') :
    IsRecAdd A' ν ↔ IsRecAdd A (trOp φ.symm ν) := by
  constructor
  · exact isRecAdd_of_transport (IsIso.symm hφ)
  · intro h
    have e : trOp φ (trOp φ.symm ν) = ν := by
      funext x y
      simp only [trOp, onePointCongr_symm_apply', onePointCongr_symm_symm_apply',
        Homeomorph.apply_symm_apply]
    have := isRecAdd_of_transport hφ h
    rwa [e] at this

/-- If the operation of Corollary 2.7 (c) is unique on `(E, A)`, then `recAdd` on an isomorphic
`(E', A')` is its transport. -/
theorem recAdd_transport (hφ : IsIso A A' φ) {μ : OnePoint E → OnePoint E → OnePoint E}
    (hμ : ∀ ν, IsRecAdd A ν ↔ ν = μ) : recAdd A' = trOp φ μ := by
  refine recAdd_eq (isRecAdd_of_transport hφ ((hμ μ).2 rfl)) fun ν hν => ?_
  have := (hμ _).1 ((isRecAdd_transport hφ ν).1 hν)
  funext x y
  have h := congrFun (congrFun this (φ.onePointCongr.symm x)) (φ.onePointCongr.symm y)
  simp only [trOp, onePointCongr_symm_apply', onePointCongr_symm_symm_apply',
    Homeomorph.apply_symm_apply] at h
  rw [trOp, ← h, Homeomorph.apply_symm_apply]

end AutHol

end Iut
