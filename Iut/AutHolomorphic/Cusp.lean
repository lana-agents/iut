/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Morphism
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Covering.Basic

/-!
# Holomorphic elliptic cuspidalisation ([AbsTopIII] Corollary 2.7 (b), (c))

Model-implicit constructions on an Aut-holomorphic space `(E, A)` (for Corollary 2.7: the
Aut-holomorphic space of a once-punctured elliptic curve, Corollary 2.7 (a)), using only `E^top`
and `A`:

* `IsEllCusp A U q`: an **elliptic cuspidalisation diagram** `E ⊇ U → E` ([AbsTopIII]
  Corollary 2.7 (b), after [AbsTopII] Example 3.2 (i)): `U ⊆ E` is open with finite complement
  (the open immersion `E ← U`), and `q : U → E` is a morphism of Aut-holomorphic spaces which is
  a finite covering map ("finite étale") and is Galois with abelian group `deck q = Gal(U/E)`;
* `continuous_cuspExt`: the extension `cuspExt U q` of a finite covering to the one-point
  compactification (`q` on `U`, `∞` elsewhere) is continuous (a finite covering is proper,
  `isCompact_preimage_of_isCoveringMap`); `isCoveringMap_of_cuspExt`: conversely, if `cuspExt U q`
  is a covering map then `q` is a finite covering map;
* `cuspTors A`: **the torsion points** — `∞` and the points of `E` outside some such `U`;
* `CuspLim U g y`: the extension of a deck transformation `g` to the one-point compactification
  sends `∞` to `y`; `CuspSum A x y z`: `z` corresponds to `g h ∈ Gal(U/E)` when `x`, `y`
  correspond to `g`, `h` (**the group structure on the torsion points induced by `Gal(U/E)`**);
* `IsRecAdd A μ`: `μ` is a continuous binary operation on the one-point compactification that
  extends the group law of the torsion points (Corollary 2.7 (c)); `recAdd A`: the operation of
  Corollary 2.7 (c) (a chosen such `μ`; it is unique in the model, `Elliptic/CuspModel.lean`).

**Deviations.**

* The condition "`E ← U`, `U → E` are co-holomorphic" ([AbsTopIII] Definition 2.1 (iv),
  via co-orientations `Orn(-)`) is not imposed. The classification of the diagrams of the model
  (`Elliptic/CuspModel.lean`) shows that dropping it does not change the torsion points or their
  group law: an antiholomorphic `q` also has the form `x ↦ a x̄` and the same deck group.
* "which necessarily extends to a covering of the one-point compactification" is not imposed but
  proved: for `E_Λ` in `Elliptic/CuspModel.lean` (`isCoveringMap_cuspExt`), and for any
  `(E, A) ≅ E_Λ` in `Elliptic/EllModel.lean` (`isCoveringMap_cuspExt_of_isIso`).
* Corollary 2.7 (c) asks for "the unique topological group structure" extending the torsion law;
  `IsRecAdd` asks for a continuous binary operation, a weaker condition, which still determines the
  law uniquely in the model.
-/

namespace Iut

namespace AutHol

open Set Topology Filter TopologicalSpace OnePoint

variable {E : Type*} [TopologicalSpace E]

open Classical in
/-- The extension of `q : U → E` to the one-point compactification: `q` on `U`, `∞` elsewhere. -/
noncomputable def cuspExt (U : Opens E) (q : U → E) (x : OnePoint E) : OnePoint E :=
  x.elim ∞ fun y => if h : y ∈ U then ((q ⟨y, h⟩ : E) : OnePoint E) else ∞

@[simp]
theorem cuspExt_infty (U : Opens E) (q : U → E) : cuspExt U q ∞ = ∞ := rfl

open Classical in
theorem cuspExt_of_mem (U : Opens E) (q : U → E) (x : U) :
    cuspExt U q ((x : E) : OnePoint E) = ((q x : E) : OnePoint E) := by
  change (if h : (x : E) ∈ U then ((q ⟨x, h⟩ : E) : OnePoint E) else ∞) = _
  rw [dif_pos x.2]

open Classical in
theorem cuspExt_of_notMem (U : Opens E) (q : U → E) {y : E} (hy : y ∉ U) :
    cuspExt U q (y : OnePoint E) = ∞ := by
  change (if h : y ∈ U then ((q ⟨y, h⟩ : E) : OnePoint E) else ∞) = _
  rw [dif_neg hy]

/-- **A covering map with finite fibres is proper on compact sets**: the preimage of a compact set
is compact. -/
theorem isCompact_preimage_of_isCoveringMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsCoveringMap f) (hfin : ∀ y, (f ⁻¹' {y}).Finite) {K : Set Y}
    (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  rw [isCompact_iff_ultrafilter_le_nhds']
  intro 𝒰 h𝒰
  obtain ⟨y, hyK, hy⟩ := hK.ultrafilter_le_nhds' (𝒰.map f) (by simpa using h𝒰)
  obtain ⟨-, V, hyV, hVo, -, H, hH⟩ := hf y
  have hV : f ⁻¹' V ∈ 𝒰 := Ultrafilter.mem_map.1 (hy (hVo.mem_nhds hyV))
  let S : f ⁻¹' {y} → Set X := fun i => {e | ∃ h : f e ∈ V, (H ⟨e, h⟩).2 = i}
  have hU : (⋃ i ∈ (univ : Set (f ⁻¹' {y})), S i) ∈ 𝒰 := by
    refine 𝒰.mem_of_superset hV fun e he => ?_
    exact mem_biUnion (mem_univ (H ⟨e, he⟩).2) ⟨he, rfl⟩
  haveI : Finite (f ⁻¹' {y}) := hfin y
  obtain ⟨i, -, hi⟩ := (Ultrafilter.finite_biUnion_mem_iff finite_univ).1 hU
  refine ⟨(H.symm (⟨y, hyV⟩, i) : X), ?_, fun N hN => ?_⟩
  · have h1 := hH (H.symm (⟨y, hyV⟩, i))
    rw [Homeomorph.apply_symm_apply] at h1
    change f _ ∈ K
    rw [← h1]
    exact hyK
  · have hc : Continuous fun p : V × f ⁻¹' {y} => (H.symm p : X) :=
      continuous_subtype_val.comp H.symm.continuous
    have hN' : (fun p : V × f ⁻¹' {y} => (H.symm p : X)) ⁻¹' N ∈ 𝓝 ((⟨y, hyV⟩ : V), i) :=
      hc.continuousAt.preimage_mem_nhds hN
    rw [nhds_prod_eq] at hN'
    obtain ⟨W, hW, T, hT, hWT⟩ := mem_prod_iff.1 hN'
    obtain ⟨W₀, hW₀, hW₀W⟩ := (mem_nhds_subtype V _ W).1 hW
    have hfW : f ⁻¹' W₀ ∈ 𝒰 := Ultrafilter.mem_map.1 (hy hW₀)
    filter_upwards [hfW, hi] with e he1 he2
    obtain ⟨hev, hei⟩ := he2
    have hmem : H ⟨e, hev⟩ ∈ W ×ˢ T := by
      refine ⟨hW₀W ?_, ?_⟩
      · change ((H ⟨e, hev⟩).1 : Y) ∈ W₀
        rw [hH]
        exact he1
      · rw [hei]
        exact mem_of_mem_nhds hT
    have := hWT hmem
    simpa using this

/-- **The extension of a finite covering `q : U → E` to the one-point compactification is
continuous** (`q` is proper). -/
theorem continuous_cuspExt [T2Space E] {U : Opens E} {q : U → E} (hq : IsCoveringMap q)
    (hfin : ∀ y, (q ⁻¹' {y}).Finite) : Continuous (cuspExt U q) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : ∃ x : U, z = ((x : E) : OnePoint E)
  · obtain ⟨x, rfl⟩ := hz
    have hj : IsOpenEmbedding fun x : U => ((x : E) : OnePoint E) :=
      isOpenEmbedding_coe.comp U.isOpenEmbedding'
    have hcomp : cuspExt U q ∘ (fun x : U => ((x : E) : OnePoint E)) =
        fun x => ((q x : E) : OnePoint E) := by
      funext x
      exact cuspExt_of_mem U q x
    rw [← hj.isInducing.continuousAt_iff' (hj.isOpen_range.mem_nhds ⟨x, rfl⟩), hcomp]
    exact (continuous_coe.comp hq.continuous).continuousAt
  · push Not at hz
    rw [ContinuousAt]
    have hz' : cuspExt U q z = ∞ := by
      induction z using OnePoint.rec with
      | infty => rfl
      | coe y => exact cuspExt_of_notMem U q fun hy => hz ⟨y, hy⟩ rfl
    rw [hz', hasBasis_nhds_infty.tendsto_right_iff]
    rintro C ⟨-, hCk⟩
    have hK : IsCompact (q ⁻¹' C) := isCompact_preimage_of_isCoveringMap hq hfin hCk
    have hK' : IsCompact (((↑) : U → E) '' (q ⁻¹' C)) := hK.image continuous_subtype_val
    have hcl : IsClosed (((↑) : E → OnePoint E) '' (((↑) : U → E) '' (q ⁻¹' C))) :=
      isClosed_image_coe.2 ⟨hK'.isClosed, hK'⟩
    have hzn : z ∉ ((↑) : E → OnePoint E) '' (((↑) : U → E) '' (q ⁻¹' C)) := by
      rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
      exact hz x rfl
    filter_upwards [hcl.isOpen_compl.mem_nhds hzn] with w hw
    induction w using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe y =>
      by_cases hy : y ∈ U
      · rw [cuspExt_of_mem U q ⟨y, hy⟩]
        exact Or.inl ⟨_, fun hC => hw ⟨y, ⟨⟨y, hy⟩, hC, rfl⟩, rfl⟩, rfl⟩
      · rw [cuspExt_of_notMem U q hy]
        exact Or.inr rfl

theorem cuspExt_mem_range_iff {U : Opens E} {q : U → E} (w : OnePoint E) :
    cuspExt U q w ∈ range ((↑) : E → OnePoint E) ↔
      w ∈ range fun x : U => ((x : E) : OnePoint E) := by
  induction w using OnePoint.rec with
  | infty => simp [cuspExt_infty]
  | coe y =>
    by_cases hy : y ∈ U
    · rw [cuspExt_of_mem U q ⟨y, hy⟩]
      exact ⟨fun _ => ⟨⟨y, hy⟩, rfl⟩, fun _ => ⟨_, rfl⟩⟩
    · rw [cuspExt_of_notMem U q hy]
      simp only [mem_range, coe_ne_infty, exists_false, false_iff, not_exists]
      intro x hx
      exact hy (coe_injective hx ▸ x.2)

/-- Conversely, **if the extension to the one-point compactification is a covering map, then `q`
is a finite covering map**. -/
theorem isCoveringMap_of_cuspExt [T1Space E] {U : Opens E} {q : U → E}
    (hcov : IsCoveringMap (cuspExt U q)) : IsCoveringMap q ∧ ∀ y, (q ⁻¹' {y}).Finite := by
  have hj : IsEmbedding fun x : U => ((x : E) : OnePoint E) :=
    isOpenEmbedding_coe.isEmbedding.comp U.isOpenEmbedding'.isEmbedding
  have hrange : range (fun x : U => ((x : E) : OnePoint E)) =
      cuspExt U q ⁻¹' range ((↑) : E → OnePoint E) := by
    ext w
    exact (cuspExt_mem_range_iff w).symm
  let e₁ : U ≃ₜ cuspExt U q ⁻¹' range ((↑) : E → OnePoint E) :=
    hj.toHomeomorph.trans (Homeomorph.setCongr hrange)
  let e₂ : E ≃ₜ range ((↑) : E → OnePoint E) := isOpenEmbedding_coe.isEmbedding.toHomeomorph
  have hR := hcov.restrictPreimage (range ((↑) : E → OnePoint E))
  have h1 := (hR.comp_homeomorph e₁).homeomorph_comp e₂.symm
  have heq : (e₂.symm ∘ ((range ((↑) : E → OnePoint E)).restrictPreimage (cuspExt U q)) ∘ e₁) =
      q := by
    funext x
    simp only [Function.comp_apply]
    rw [Homeomorph.symm_apply_eq]
    apply Subtype.ext
    change cuspExt U q ((x : E) : OnePoint E) = ((q x : E) : OnePoint E)
    exact cuspExt_of_mem U q x
  rw [heq] at h1
  refine ⟨h1, fun y => ?_⟩
  have hcl : IsClosed (cuspExt U q ⁻¹' {((y : E) : OnePoint E)}) := by
    have : IsClosed ({((y : E) : OnePoint E)} : Set (OnePoint E)) := by
      rw [← image_singleton]
      exact isClosed_image_coe.2 ⟨isClosed_singleton, isCompact_singleton⟩
    exact this.preimage hcov.continuous
  have hfib : (cuspExt U q ⁻¹' {((y : E) : OnePoint E)}).Finite :=
    hcl.isCompact.finite (isDiscrete_iff_discreteTopology.2 (hcov _).discreteTopology_fiber)
  refine (hfib.preimage hj.injective.injOn).subset fun x hx => ?_
  change cuspExt U q ((x : E) : OnePoint E) = ((y : E) : OnePoint E)
  rw [cuspExt_of_mem U q x, show q x = y from hx]

/-- **The deck transformations** `Gal(U/E)` of `q : U → E`. -/
def deck {U : Opens E} (q : U → E) : Subgroup (U ≃ₜ U) where
  carrier := {g | ∀ x, q (g x) = q x}
  mul_mem' := by
    intro g h hg hh x
    change q (g (h x)) = q x
    rw [hg, hh]
  one_mem' := fun _ => rfl
  inv_mem' := by
    intro g hg x
    change q (g.symm x) = q x
    conv_rhs => rw [← g.apply_symm_apply x]
    rw [hg]

theorem mem_deck {U : Opens E} {q : U → E} {g : U ≃ₜ U} : g ∈ deck q ↔ ∀ x, q (g x) = q x :=
  Iff.rfl

/-- **An elliptic cuspidalisation diagram** `E ⊇ U → E` ([AbsTopIII] Corollary 2.7 (b)):
`U` has finite complement, `q` is a morphism of Aut-holomorphic spaces and a finite covering map
("an abelian finite étale covering"), and `q` is Galois with abelian group `deck q`. -/
def IsEllCusp (A : AutHolStr E) (U : Opens E) (q : U → E) : Prop :=
  (U : Set E)ᶜ.Finite ∧ IsMorphism (A.restrict U) A q ∧ IsCoveringMap q ∧
    (∀ y, (q ⁻¹' {y}).Finite) ∧
    (∀ x y : U, q x = q y → ∃ g ∈ deck q, g x = y) ∧
    ∀ g ∈ deck q, ∀ h ∈ deck q, g * h = h * g

/-- The extension of a self-map `g` of `U` to the one-point compactification sends `∞` to `y`:
`g x → y` as `x → ∞` in `U`. -/
def CuspLim (U : Opens E) (g : U → U) (y : OnePoint E) : Prop :=
  Tendsto (fun x : U => ((g x : E) : OnePoint E))
    (comap (fun x : U => ((x : E) : OnePoint E)) (𝓝 ∞)) (𝓝 y)

/-- **The torsion points** ([AbsTopIII] Corollary 2.7 (b)): `∞` (the origin) and the points in the
complement of the image of some elliptic cuspidalisation diagram. -/
def cuspTors (A : AutHolStr E) : Set (OnePoint E) :=
  {y | y = ∞ ∨ ∃ (U : Opens E) (q : U → E), IsEllCusp A U q ∧ ∃ x : E, x ∉ U ∧ y = x}

/-- **The group law on the torsion points induced by `Gal(U/E)`**: `x + y = z` if, for some
diagram, `x`, `y`, `z` are the images of `∞` under deck transformations `g`, `h`, `g h`. -/
def CuspSum (A : AutHolStr E) (x y z : OnePoint E) : Prop :=
  ∃ (U : Opens E) (q : U → E), IsEllCusp A U q ∧ ∃ g ∈ deck q, ∃ h ∈ deck q,
    CuspLim U g x ∧ CuspLim U h y ∧ CuspLim U (g * h) z

/-- `μ` is **a continuous operation extending the group law of the torsion points**
([AbsTopIII] Corollary 2.7 (c)). -/
def IsRecAdd (A : AutHolStr E) (μ : OnePoint E → OnePoint E → OnePoint E) : Prop :=
  Continuous (fun p : OnePoint E × OnePoint E => μ p.1 p.2) ∧
    ∀ x ∈ cuspTors A, ∀ y ∈ cuspTors A, CuspSum A x y (μ x y)

open Classical in
/-- **The group law on the one-point compactification** ([AbsTopIII] Corollary 2.7 (c)): an
operation satisfying `IsRecAdd A` (unique in the model, `recAdd_ellStr`). -/
noncomputable def recAdd (A : AutHolStr E) : OnePoint E → OnePoint E → OnePoint E :=
  if h : ∃ μ, IsRecAdd A μ then h.choose else fun x _ => x

theorem recAdd_eq {A : AutHolStr E} {μ : OnePoint E → OnePoint E → OnePoint E}
    (hμ : IsRecAdd A μ) (huniq : ∀ ν, IsRecAdd A ν → ν = μ) : recAdd A = μ := by
  have h : ∃ μ, IsRecAdd A μ := ⟨μ, hμ⟩
  rw [recAdd, dif_pos h]
  exact huniq _ h.choose_spec

end AutHol

end Iut
