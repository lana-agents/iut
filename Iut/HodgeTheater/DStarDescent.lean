/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.DStarCore

/-!
# `π₁(†D^⊛)` as the automorphism group of `π₁(C_K)` (descent from `K` to `F_mod`)

IUT I, Example 5.1 (i) (`Inter-universal Teichmuller Theory I.txt` l.8246–8257) constructs from
`π₁(†D^⊚) = π₁(C̲_K)` "a profinite group corresponding to "`C_{F_mod}`" […] which contains
`π₁(†D^⊚)` as an open subgroup", recalling from Remark 3.1.7 (i) (l.4316–4322) that "it follows
immediately from the definition of `F_mod` and the `K`-coricity of `C_K` […] that `C_F` admits a
unique […] model `C_{F_mod}` over `F_mod`". The model is algebro-geometric (here `curveMod`, with
`π₁(C_K) ↪ π₁(C_{F_mod})` from `genuine_CF_emb`); the group-theoretic passage from `K` down to
`F_mod` needs an *absolute* anabelian input, since [AbsTopII] Cor. 3.3 (i) only moves the base
field up (its chains have `G_j ⊆ G`, [AbsTopI] Def. 4.2 (iii) (1Π), `Topics in Absolute Anabelian
Geometry I.txt` l.2980).

This file records that input as the named hypothesis `hAbs` and derives the reconstruction
`π₁(C_{F_mod}) = Aut(π₁(C_K))`:

* `hAbs` (**named debt**, see MR8-plan round 40): every continuous automorphism `α` of `π₁(C_K)`
  acts on the image of `π₁(C_K)` in `Gal(F̄/F_mod)` by conjugation by an element of
  `Gal(F̄/F_mod)`. In the literature: `α` preserves the geometric subgroup and so induces an
  automorphism of `G_K` ([AbsTopI] Cor. 2.8 (ii), strict semi-absoluteness for number fields,
  l.1348–1358); the functorial reconstruction of the field `K̄_NF` with its `G_K`-action and of the
  NF-portion of the function field ([AbsTopIII] Thm. 1.9, `Topics in Absolute Anabelian Geometry
  III.txt` l.2109–2196; MR9) shows that this automorphism is conjugation by a lift `σ̃` of a field
  automorphism `σ` with `C_K^σ ≅ C_K`, i.e. `σ(j) = j`, i.e. `σ̃ ∈ Gal(F̄/F_mod)`
  (`F_mod = ℚ(j)`);
* **`piCK_aut_eq_conj`**: under `hAbs` (and the existing inputs `hDGC`, `hj`), every continuous
  automorphism of `π₁(C_K)` is the restriction of conjugation by a unique element of
  `π₁(C_{F_mod})` (existence: self-commensuration `piCmod_selfComm`; uniqueness: `π₁(C_{F_mod})` is
  slim, `isSlim_piCmod`);
* **`piCK_conj_aut`**: conversely, conjugation by every element of `π₁(C_{F_mod})` restricts to a
  continuous automorphism of `π₁(C_K)` (`π₁(C_K)` is open and normal in `π₁(C_{F_mod})`);
* **`piCmodAutEquiv`**: hence `π₁(C_{F_mod}) ≃* Aut(π₁(C_K))` (continuous automorphisms), so
  `π₁(†D^⊛)` is determined group-theoretically by `π₁(C_K)`, which in turn is the last group of the
  terminal `⋎`-chain of `ÉtLoc` over `K` ([AbsTopII] Cor. 3.3 (i) with `G′ ⊆ G`,
  `hemi_cor33i_terminal_baseChange`);
* `galK` (`G_K`, the image of `π₁(C_K)` in `Gal(F̄/F_mod)`), **`mem_range_piCKToCmod_iff`**
  (`π₁(C_K) = pr⁻¹(G_K)`, Galois compatibility of `genuine_CF_emb`), `piCKuToCK_unique` and
  **`piCKuToCK_unique_inner`**: `π₁(C̲_K) ↪ π₁(C_K)` is unique up to `Inn(π₁(C_K))` among open
  embeddings whose composite to `Gal(F̄/F_mod)` agrees up to conjugation by an element of `G_K`.
-/

noncomputable section

namespace Iut

namespace HodgeTheater

open CategoryTheory NumberField Frobenioid CurvesJacobian CurvesJacobian.Cusp
  Iut.Reconstruction.HemiGenuine Iut.Reconstruction.HemiCore Iut.Anabelian AlgebraicGeometry Belyi
  Belyi.Anabelian Topology Pi1.Profinite

attribute [local instance low] Classical.propDecidable

variable (D : InitialThetaData.{0})

/-- `π₁(C_K)`, `C_K = C_F ×_F K` (IUT I, Def. 3.1 (d)). -/
abbrev piCK : Type := (OrbicurveDataSection.CK D.F D.E D.Fbar D.VBad D.prime).genuinePi1

/-- `piCmodPr` unfolded: restriction to the field of constants, then `galConstEquiv`. -/
lemma piCmodPr_apply (y : piCmod D) :
    piCmodPr D y = galConstEquiv D
      (piConstC (hemiData (curveMod D.E)) (genuinePi1HemiEquiv (curveMod D.E) y)) :=
  rfl

set_option maxHeartbeats 1000000 in
-- matching `genuine_CF_emb`'s `piConstC (hemiData (curveMod D.E))` (instances over `F_mod` found
-- generically) with the one in `piCmodPr` (instances of `Fmod D`) unfolds the instance terms
/-- **`π₁(C_K) ↪ π₁(C_{F_mod})`**, open with normal image (`genuine_CF_emb`; `K/F_mod` is Galois,
IUT I Rem. 3.1.5), compatible with the projections to the Galois groups: the image is the full
preimage of its image in `Gal(F̄/F_mod)` (the preimage of `Gal(K̄/K)` under the restriction to the
field of constants, `genuine_CF_emb`). -/
theorem exists_piCK_emb :
    ∃ f : piCK D →ₜ* piCmod D, IsOpenEmbedding f ∧ f.toMonoidHom.range.Normal ∧
      ∀ y z, piCmodPr D y = piCmodPr D (f z) → y ∈ f.toMonoidHom.range := by
  have hCK : OrbicurveDataSection.CK D.F D.E D.Fbar D.VBad D.prime = Orbicurve.pmQuotient
      (Orbicurve.oncePunctured (D.E.map (algebraMap D.F D.Kt))) := by
    rw [OrbicurveDataSection.CK, OrbicurveDataSection.CF, Orbicurve.baseChange_pmQuotient,
      Orbicurve.baseChange_oncePunctured]
  have hj : (D.E.map (algebraMap D.F D.Kt)).j =
      algebraMap (fieldOfModuli D.F D.E) D.Kt (curveMod D.E).j := by
    rw [WeierstrassCurve.map_j, show (curveMod D.E).j = jMod D.E from WeierstrassCurve.ofJ_j _]
    rfl
  have hj0 : (curveMod D.E).j = jMod D.E := WeierstrassCurve.ofJ_j _
  obtain ⟨g, hg, hn, -, hgal⟩ := genuine_CF_emb (K := fieldOfModuli D.F D.E) (F := D.Kt)
    (curveMod D.E) (D.E.map (algebraMap D.F D.Kt)) hj (by rw [hj0]; exact (jMod_ne D).1)
    (by rw [hj0]; exact (jMod_ne D).2)
  let e := genuinePi1EqEquiv hCK
  have hr : (g.comp (ContinuousMonoidHom.toContinuousMonoidHom e)).toMonoidHom.range =
      g.toMonoidHom.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, by
        change g (e (e.symm x)) = g x
        rw [ContinuousMulEquiv.apply_symm_apply]⟩
  refine ⟨g.comp (ContinuousMonoidHom.toContinuousMonoidHom e), ?_, ?_, fun y z hyz => ?_⟩
  · exact hg.comp e.toHomeomorph.isOpenEmbedding
  · rw [hr]
    exact hn
  · rw [hr]
    set w := (g.comp (ContinuousMonoidHom.toContinuousMonoidHom e)) z with hw
    have hz : w ∈ g.toMonoidHom.range := ⟨e z, rfl⟩
    rw [piCmodPr_apply, piCmodPr_apply] at hyz
    have hP := (galConstEquiv D).injective hyz
    have h2 := (hgal w).1 hz
    have h3 := (hgal y).2
    exact h3 (hP ▸ h2)

/-- The chosen embedding `π₁(C_K) ↪ π₁(C_{F_mod})`. -/
def piCKToCmod : piCK D →ₜ* piCmod D := (exists_piCK_emb D).choose

lemma isOpenEmbedding_piCKToCmod : IsOpenEmbedding (piCKToCmod D) :=
  (exists_piCK_emb D).choose_spec.1

instance normal_range_piCKToCmod : (piCKToCmod D).toMonoidHom.range.Normal :=
  (exists_piCK_emb D).choose_spec.2.1

/-- **`G_K`**: the image of `π₁(C_K)` in `Gal(F̄/F_mod)` (an open normal subgroup; `Gal(F̄/K)` for
the realisation of `K` inside `F̄` given by the chosen embedding). -/
def galK : Subgroup (GalG (Fmod D) D.Fbar) := (piCKToCmod D).toMonoidHom.range.map (piCmodPr D)

/-- **`π₁(C_K) = pr⁻¹(G_K)`** inside `π₁(C_{F_mod})` (Galois compatibility of `genuine_CF_emb`). -/
lemma mem_range_piCKToCmod_iff (y : piCmod D) :
    y ∈ (piCKToCmod D).toMonoidHom.range ↔ piCmodPr D y ∈ galK D := by
  refine ⟨fun hy => ⟨y, hy, rfl⟩, ?_⟩
  rintro ⟨_, ⟨z, rfl⟩, hz⟩
  exact (exists_piCK_emb D).choose_spec.2.2 y z hz.symm

omit D in
/-- A topological group mapping to a slim group with open image and slim kernel is slim (as in
`ChainObj.isSlim_grp₄`). -/
lemma isSlim_of_ker {P G : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (p : P →ₜ* G) (hG : IsSlim G) (hp : IsOpen (Set.range p)) (hΔ : IsSlim (p : P →* G).ker) :
    IsSlim P := by
  intro U z hz
  have h1 : p z = 1 := eq_one_of_commute_open₄ hG p hp U.isOpen
    (fun u hu => by rw [← map_mul, ← map_mul, hz u hu])
  have hΔU : IsOpen (((U : Subgroup P).subgroupOf (p : P →* G).ker :
      Subgroup (p : P →* G).ker) : Set (p : P →* G).ker) :=
    U.isOpen.preimage continuous_subtype_val
  have := hΔ ⟨_, hΔU⟩ ⟨z, h1⟩ (by
    rintro ⟨u, hu⟩ hu'
    exact Subtype.ext (hz u hu'))
  exact congrArg Subtype.val this

/-- **`π₁(C_{F_mod})` is slim** (`Δ_C` and `Gal(F̄/F_mod)` are slim). -/
theorem isSlim_piCmod : IsSlim (piCmod D) := by
  have h : IsSlim (hemiCoreGrp₄ (curveMod D.E)) :=
    isSlim_of_ker (hemiCorePr₄ (curveMod D.E) D.Fbar)
      (arithmeticExt D.Fbar (hypCurveX (curveMod D.E)) (compl_XE_nonempty (curveMod D.E))).slim_G
      (isOpen_range_hemiCorePr₄ (curveMod D.E) D.Fbar)
      (isSlim_ker_hemiCorePr₄ (curveMod D.E) D.Fbar)
  exact IsSlim.of_continuousMulEquiv (piCmodCoreEquiv D).symm h

/-- An element of `π₁(C_{F_mod})` centralising `π₁(C_K)` is trivial. -/
lemma eq_one_of_commute_piCK {γ : piCmod D} (h : ∀ x, γ * piCKToCmod D x = piCKToCmod D x * γ) :
    γ = 1 :=
  eq_one_of_commute_open₄ (isSlim_piCmod D) (piCKToCmod D)
    (isOpenEmbedding_piCKToCmod D).isOpen_range (U := ⊤) isOpen_univ fun u _ => h u

/-- A map `c` of `π₁(C_K)` with `ι ∘ c = conj γ ∘ ι` is continuous (`ι` is an embedding). -/
lemma continuous_of_conj {γ : piCmod D} {c : piCK D → piCK D}
    (hc : ∀ x, piCKToCmod D (c x) = γ * piCKToCmod D x * γ⁻¹) : Continuous c := by
  refine (isOpenEmbedding_piCKToCmod D).isInducing.continuous_iff.mpr ?_
  have h : (piCKToCmod D ∘ c) = fun x => γ * piCKToCmod D x * γ⁻¹ := funext hc
  rw [h]
  exact (continuous_const.mul (piCKToCmod D).continuous).mul continuous_const

/-- **Conjugation by `γ ∈ π₁(C_{F_mod})` restricts to a continuous automorphism of `π₁(C_K)`**
(`π₁(C_K)` is normal in `π₁(C_{F_mod})`). -/
theorem piCK_conj_aut (γ : piCmod D) :
    ∃ α : piCK D ≃ₜ* piCK D, ∀ x, piCKToCmod D (α x) = γ * piCKToCmod D x * γ⁻¹ := by
  have hι := (isOpenEmbedding_piCKToCmod D).injective
  have hmem : ∀ x, γ * piCKToCmod D x * γ⁻¹ ∈ (piCKToCmod D).toMonoidHom.range := fun x =>
    (normal_range_piCKToCmod D).conj_mem _ ⟨x, rfl⟩ γ
  have hmem' : ∀ x, γ⁻¹ * piCKToCmod D x * γ⁻¹⁻¹ ∈ (piCKToCmod D).toMonoidHom.range := fun x =>
    (normal_range_piCKToCmod D).conj_mem _ ⟨x, rfl⟩ γ⁻¹
  choose a ha using hmem
  choose b hb using hmem'
  have ha' : ∀ x, piCKToCmod D (a x) = γ * piCKToCmod D x * γ⁻¹ := ha
  have hb' : ∀ x, piCKToCmod D (b x) = γ⁻¹ * piCKToCmod D x * γ⁻¹⁻¹ := hb
  have hab : ∀ x, a (b x) = x := fun x => hι (by rw [ha', hb']; group)
  have hba : ∀ x, b (a x) = x := fun x => hι (by rw [hb', ha']; group)
  have hmul : ∀ x y, a (x * y) = a x * a y := fun x y => hι (by
    rw [map_mul, ha', ha', ha', map_mul]
    group)
  let m : piCK D ≃* piCK D :=
    { toFun := a
      invFun := b
      left_inv := hba
      right_inv := hab
      map_mul' := hmul }
  exact ⟨⟨m, continuous_of_conj D ha', continuous_of_conj D hb'⟩, ha'⟩

/-- **Every continuous automorphism of `π₁(C_K)` is conjugation by a unique element of
`π₁(C_{F_mod})`**, given the absolute anabelian input `hAbs` (the named debt of this file: `α`
acts on the image of `π₁(C_K)` in `Gal(F̄/F_mod)` by conjugation by an element of
`Gal(F̄/F_mod)`; [AbsTopI] Cor. 2.8 (ii) and [AbsTopIII] Thm. 1.9, see the module docstring). -/
theorem piCK_aut_eq_conj (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F))
    (hAbs : ∀ α : piCK D ≃ₜ* piCK D, ∃ g : GalG (Fmod D) D.Fbar, ∀ x,
      piCmodPr D (piCKToCmod D (α x)) = g * piCmodPr D (piCKToCmod D x) * g⁻¹)
    (α : piCK D ≃ₜ* piCK D) :
    ∃! γ : piCmod D, ∀ x, piCKToCmod D (α x) = γ * piCKToCmod D x * γ⁻¹ := by
  have hι := isOpenEmbedding_piCKToCmod D
  obtain ⟨g, hg⟩ := hAbs α
  let f₂ : piCK D →ₜ* piCmod D := (piCKToCmod D).comp (ContinuousMonoidHom.toContinuousMonoidHom α)
  have hf₂ : ⇑f₂ = piCKToCmod D ∘ α := rfl
  have ho₂ : IsOpen (Set.range f₂) := by
    rw [hf₂, Set.range_comp, α.surjective.range_eq, Set.image_univ]
    exact hι.isOpen_range
  obtain ⟨γ, hγ⟩ := piCmod_selfComm D hDGC hj (piCK D) (piCKToCmod D) f₂ hι.injective
    hι.isOpen_range (hι.injective.comp α.injective) ho₂ g hg
  refine ⟨γ, hγ, fun δ hδ => ?_⟩
  have h1 : δ⁻¹ * γ = 1 := eq_one_of_commute_piCK D fun x => by
    have e : δ * piCKToCmod D x * δ⁻¹ = γ * piCKToCmod D x * γ⁻¹ := (hδ x).symm.trans (hγ x)
    calc δ⁻¹ * γ * piCKToCmod D x
        = δ⁻¹ * (γ * piCKToCmod D x * γ⁻¹) * γ := by group
      _ = δ⁻¹ * (δ * piCKToCmod D x * δ⁻¹) * γ := by rw [e]
      _ = piCKToCmod D x * (δ⁻¹ * γ) := by group
  calc δ = δ * (δ⁻¹ * γ) := by rw [h1, mul_one]
    _ = γ := by group

/-- The covering `π₁(C̲_K) ↪ π₁(C_K)` (IUT I, Def. 3.1 (d)) as a continuous homomorphism. -/
def piCKuToCK : D.orb.CKu.genuinePi1 →ₜ* piCK D :=
  ⟨D.orb.pi1CKu_to_CK, D.orb.pi1CKu_to_CK_isOpenEmbedding.continuous⟩

/-- **The embedding `π₁(†D^⊚) = π₁(C̲_K) ↪ π₁(C_K)` is unique up to conjugation** (the analogue
of `piCKuToCmod_unique` one step lower; IUT I, Example 5.1 (i), [AbsTopII] Cor. 3.3 (i) via the
self-commensuration `piCmod_selfComm`): if an open embedding `f : π₁(C̲_K) ↪ π₁(C_K)` has, after
`π₁(C_K) ↪ π₁(C_{F_mod}) ↠ Gal(F̄/F_mod)`, the composite of the covering `piCKuToCK` conjugated by
`g ∈ Gal(F̄/F_mod)`, then `f` is the covering followed by the automorphism `α` of `π₁(C_K)` given by
conjugation by an element `γ ∈ π₁(C_{F_mod})` lying over `g`; `γ` is unique (`isSlim_piCmod`).
For `g ∈ G_K` such `γ` lies in `π₁(C_K) = pr⁻¹(G_K)` and `α` is inner (`piCKuToCK_unique_inner`). -/
theorem piCKuToCK_unique (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F))
    (f : D.orb.CKu.genuinePi1 →* piCK D) (hf : IsOpenEmbedding f) (g : GalG (Fmod D) D.Fbar)
    (hg : ∀ x, piCmodPr D (piCKToCmod D (f x)) =
      g * piCmodPr D (piCKToCmod D (piCKuToCK D x)) * g⁻¹) :
    ∃! γ : piCmod D, piCmodPr D γ = g ∧
      ∃ α : piCK D ≃ₜ* piCK D, (∀ y, piCKToCmod D (α y) = γ * piCKToCmod D y * γ⁻¹) ∧
        ∀ x, f x = α (piCKuToCK D x) := by
  have hι := isOpenEmbedding_piCKToCmod D
  have h₀ : IsOpenEmbedding (piCKuToCK D) := D.orb.pi1CKu_to_CK_isOpenEmbedding
  let f₁ : D.orb.CKu.genuinePi1 →ₜ* piCmod D := (piCKToCmod D).comp (piCKuToCK D)
  let f₂ : D.orb.CKu.genuinePi1 →ₜ* piCmod D := (piCKToCmod D).comp ⟨f, hf.continuous⟩
  have hf₁ : IsOpenEmbedding f₁ := by
    have e : ⇑f₁ = piCKToCmod D ∘ piCKuToCK D := rfl
    rw [e]
    exact hι.comp h₀
  have hf₂ : IsOpenEmbedding f₂ := by
    have e : ⇑f₂ = piCKToCmod D ∘ f := rfl
    rw [e]
    exact hι.comp hf
  have hsc := piCmod_selfComm D hDGC hj D.orb.CKu.genuinePi1 f₁ f₂ hf₁.injective
    hf₁.isOpen_range hf₂.injective hf₂.isOpen_range g hg
  obtain ⟨γ, hγ⟩ := hsc
  -- `γ` lies over `g`: `g⁻¹ · pr γ` centralises the open subgroup `pr(f₁(π₁(C̲_K)))`
  have hpr : piCmodPr D γ = g := by
    let p : piCmod D →ₜ* GalG (Fmod D) D.Fbar := ⟨piCmodPr D, continuous_piCmodPr D⟩
    have hp : IsOpen (Set.range p) := by
      rw [show Set.range p = Set.univ from (piCmodPr_surjective D).range_eq]
      exact isOpen_univ
    have h1 : g⁻¹ * piCmodPr D γ = 1 := eq_one_of_commute_open₄
      (isSlim_galoisGroup_numberField (Fmod D) D.Fbar) p hp
      (U := (f₁ : D.orb.CKu.genuinePi1 →* piCmod D).range) (z := g⁻¹ * piCmodPr D γ)
      hf₁.isOpen_range fun u hu => by
        obtain ⟨x, rfl⟩ := hu
        have e1 := hg x
        have e2 : piCmodPr D (f₂ x) = piCmodPr D γ * piCmodPr D (f₁ x) * (piCmodPr D γ)⁻¹ := by
          rw [hγ x, map_mul, map_mul, map_inv]
        change g⁻¹ * piCmodPr D γ * p (f₁ x) = p (f₁ x) * (g⁻¹ * piCmodPr D γ)
        have e : g * piCmodPr D (f₁ x) * g⁻¹ =
            piCmodPr D γ * piCmodPr D (f₁ x) * (piCmodPr D γ)⁻¹ := e1.symm.trans e2
        calc g⁻¹ * piCmodPr D γ * piCmodPr D (f₁ x)
            = g⁻¹ * (piCmodPr D γ * piCmodPr D (f₁ x) * (piCmodPr D γ)⁻¹) * piCmodPr D γ := by
              group
          _ = g⁻¹ * (g * piCmodPr D (f₁ x) * g⁻¹) * piCmodPr D γ := by rw [e]
          _ = piCmodPr D (f₁ x) * (g⁻¹ * piCmodPr D γ) := by group
    calc piCmodPr D γ = g * (g⁻¹ * piCmodPr D γ) := by group
      _ = g := by rw [h1, mul_one]
  obtain ⟨α, hα⟩ := piCK_conj_aut D γ
  refine ⟨γ, ⟨hpr, α, hα, fun x => hι.injective ?_⟩, fun δ ⟨_, β, hβ, hfβ⟩ => ?_⟩
  · rw [hα]
    exact hγ x
  -- uniqueness: `δ⁻¹ γ` centralises the open subgroup `f₁(π₁(C̲_K))` of the slim `π₁(C_{F_mod})`
  have hδ : ∀ x, f₂ x = δ * f₁ x * δ⁻¹ := fun x => by
    change piCKToCmod D (f x) = δ * piCKToCmod D (piCKuToCK D x) * δ⁻¹
    rw [hfβ x, hβ]
  have h1 : δ⁻¹ * γ = 1 := eq_one_of_commute_open₄ (isSlim_piCmod D) f₁ hf₁.isOpen_range
    (U := ⊤) isOpen_univ fun x _ => by
      have e : δ * f₁ x * δ⁻¹ = γ * f₁ x * γ⁻¹ := (hδ x).symm.trans (hγ x)
      calc δ⁻¹ * γ * f₁ x
          = δ⁻¹ * (γ * f₁ x * γ⁻¹) * γ := by group
        _ = δ⁻¹ * (δ * f₁ x * δ⁻¹) * γ := by rw [e]
        _ = f₁ x * (δ⁻¹ * γ) := by group
  calc δ = δ * (δ⁻¹ * γ) := by rw [h1, mul_one]
    _ = γ := by group

/-- The continuous automorphisms of a topological group, as a subgroup of `MulAut`. -/
def contAut (G : Type*) [Group G] [TopologicalSpace G] : Subgroup (MulAut G) where
  carrier := {α | Continuous α ∧ Continuous α.symm}
  mul_mem' hα hβ := ⟨hα.1.comp hβ.1, hβ.2.comp hα.2⟩
  one_mem' := ⟨continuous_id, continuous_id⟩
  inv_mem' hα := ⟨hα.2, hα.1⟩

/-- Conjugation `π₁(C_{F_mod}) → Aut(π₁(C_K))`. -/
def piCmodToAut : piCmod D →* contAut (piCK D) where
  toFun γ := ⟨(piCK_conj_aut D γ).choose.toMulEquiv,
    (piCK_conj_aut D γ).choose.continuous, (piCK_conj_aut D γ).choose.symm.continuous⟩
  map_one' := Subtype.ext (MulEquiv.ext fun x => (isOpenEmbedding_piCKToCmod D).injective (by
    change piCKToCmod D ((piCK_conj_aut D 1).choose x) = piCKToCmod D x
    rw [(piCK_conj_aut D 1).choose_spec]
    group))
  map_mul' γ δ := Subtype.ext (MulEquiv.ext fun x => (isOpenEmbedding_piCKToCmod D).injective (by
    change piCKToCmod D ((piCK_conj_aut D (γ * δ)).choose x) =
      piCKToCmod D ((piCK_conj_aut D γ).choose ((piCK_conj_aut D δ).choose x))
    rw [(piCK_conj_aut D (γ * δ)).choose_spec, (piCK_conj_aut D γ).choose_spec,
      (piCK_conj_aut D δ).choose_spec]
    group))

lemma piCKToCmod_piCmodToAut (γ : piCmod D) (x : piCK D) :
    piCKToCmod D ((piCmodToAut D γ : MulAut (piCK D)) x) = γ * piCKToCmod D x * γ⁻¹ :=
  (piCK_conj_aut D γ).choose_spec x

/-- **`π₁(†D^⊛) = π₁(C_{F_mod}) ≅ Aut(π₁(C_K))`** (continuous automorphisms; IUT I, Example 5.1
(i), Remark 3.1.7 (i)): given the absolute anabelian input `hAbs` (named debt), conjugation is an
isomorphism from `π₁(C_{F_mod})` onto the group of continuous automorphisms of `π₁(C_K)`; so
`π₁(†D^⊛)`, with `π₁(C_K) ↪ π₁(†D^⊛)` (`piCKToCmod_piCmodToAut`), is determined by the profinite
group `π₁(C_K)` alone. -/
def piCmodAutEquiv (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F))
    (hAbs : ∀ α : piCK D ≃ₜ* piCK D, ∃ g : GalG (Fmod D) D.Fbar, ∀ x,
      piCmodPr D (piCKToCmod D (α x)) = g * piCmodPr D (piCKToCmod D x) * g⁻¹) :
    piCmod D ≃* contAut (piCK D) :=
  MulEquiv.ofBijective (piCmodToAut D) ⟨fun γ δ h => by
    have h1 : δ⁻¹ * γ = 1 := eq_one_of_commute_piCK D fun x => by
      have e : γ * piCKToCmod D x * γ⁻¹ = δ * piCKToCmod D x * δ⁻¹ := by
        rw [← piCKToCmod_piCmodToAut, ← piCKToCmod_piCmodToAut, h]
      calc δ⁻¹ * γ * piCKToCmod D x
          = δ⁻¹ * (γ * piCKToCmod D x * γ⁻¹) * γ := by group
        _ = δ⁻¹ * (δ * piCKToCmod D x * δ⁻¹) * γ := by rw [e]
        _ = piCKToCmod D x * (δ⁻¹ * γ) := by group
    calc γ = δ * (δ⁻¹ * γ) := by group
      _ = δ := by rw [h1, mul_one], fun α => by
    let α' : piCK D ≃ₜ* piCK D :=
      { toMulEquiv := (α : MulAut (piCK D)), continuous_toFun := α.2.1,
        continuous_invFun := α.2.2 }
    obtain ⟨γ, hγ, -⟩ := piCK_aut_eq_conj D hDGC hj hAbs α'
    refine ⟨γ, Subtype.ext (MulEquiv.ext fun x => (isOpenEmbedding_piCKToCmod D).injective ?_)⟩
    rw [piCKToCmod_piCmodToAut]
    exact (hγ x).symm⟩

/-- **The embedding `π₁(C̲_K) ↪ π₁(C_K)` is unique up to `Inn(π₁(C_K))`** (IUT I, Example 5.1 (i),
[AbsTopII] Cor. 3.3 (i), one step lower than `piCKuToCmod_unique`): if an open embedding
`f : π₁(C̲_K) ↪ π₁(C_K)` has, in `Gal(F̄/F_mod)`, the composite of the covering `piCKuToCK`
conjugated by an element `g` of `G_K` (the image of `π₁(C_K)`), then `f` is the covering followed by
conjugation by a unique `δ ∈ π₁(C_K)`. From `piCKuToCK_unique` (`γ ∈ π₁(C_{F_mod})` over `g`) and
`π₁(C_K) = pr⁻¹(G_K)` (`mem_range_piCKToCmod_iff`); uniqueness from the slimness of
`π₁(C_{F_mod})`. -/
theorem piCKuToCK_unique_inner
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F))
    (f : D.orb.CKu.genuinePi1 →* piCK D) (hf : IsOpenEmbedding f) (g : GalG (Fmod D) D.Fbar)
    (hgK : g ∈ galK D)
    (hg : ∀ x, piCmodPr D (piCKToCmod D (f x)) =
      g * piCmodPr D (piCKToCmod D (piCKuToCK D x)) * g⁻¹) :
    ∃! δ : piCK D, ∀ x, f x = δ * piCKuToCK D x * δ⁻¹ := by
  have hι := isOpenEmbedding_piCKToCmod D
  have h₀ : IsOpenEmbedding (piCKuToCK D) := D.orb.pi1CKu_to_CK_isOpenEmbedding
  have hu := piCKuToCK_unique D hDGC hj f hf g hg
  obtain ⟨γ, ⟨hpr, α, hα, hfα⟩, -⟩ := hu
  have hγ : γ ∈ (piCKToCmod D).toMonoidHom.range :=
    (mem_range_piCKToCmod_iff D γ).2 (hpr ▸ hgK)
  obtain ⟨δ, hδ⟩ := hγ
  have hδ' : piCKToCmod D δ = γ := hδ
  have hfδ : ∀ x, f x = δ * piCKuToCK D x * δ⁻¹ := fun x => hι.injective (by
    rw [hfα x, hα, map_mul, map_mul, map_inv, hδ'])
  refine ⟨δ, hfδ, fun δ₂ hδ₂ => ?_⟩
  -- `δ⁻¹ δ₂` centralises the open subgroup `π₁(C̲_K)` of `π₁(C_K)`, whose image in the slim
  -- `π₁(C_{F_mod})` is open
  let f₁ : D.orb.CKu.genuinePi1 →ₜ* piCmod D := (piCKToCmod D).comp (piCKuToCK D)
  have hf₁ : IsOpenEmbedding f₁ := by
    have e : ⇑f₁ = piCKToCmod D ∘ piCKuToCK D := rfl
    rw [e]
    exact hι.comp h₀
  have h1 : piCKToCmod D (δ⁻¹ * δ₂) = 1 := eq_one_of_commute_open₄ (isSlim_piCmod D) f₁
    hf₁.isOpen_range (U := ⊤) isOpen_univ fun x _ => by
      have e : δ₂ * piCKuToCK D x * δ₂⁻¹ = δ * piCKuToCK D x * δ⁻¹ := (hδ₂ x).symm.trans (hfδ x)
      have e' : δ⁻¹ * δ₂ * piCKuToCK D x = piCKuToCK D x * (δ⁻¹ * δ₂) := by
        calc δ⁻¹ * δ₂ * piCKuToCK D x
            = δ⁻¹ * (δ₂ * piCKuToCK D x * δ₂⁻¹) * δ₂ := by group
          _ = δ⁻¹ * (δ * piCKuToCK D x * δ⁻¹) * δ₂ := by rw [e]
          _ = piCKuToCK D x * (δ⁻¹ * δ₂) := by group
      change piCKToCmod D (δ⁻¹ * δ₂) * piCKToCmod D (piCKuToCK D x) =
        piCKToCmod D (piCKuToCK D x) * piCKToCmod D (δ⁻¹ * δ₂)
      rw [← map_mul, ← map_mul, e']
  have h2 : δ⁻¹ * δ₂ = 1 := hι.injective (by rw [h1, map_one])
  calc δ₂ = δ * (δ⁻¹ * δ₂) := by group
    _ = δ := by rw [h2, mul_one]

end HodgeTheater

end Iut
