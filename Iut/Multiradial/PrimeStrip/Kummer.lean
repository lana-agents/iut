/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Mu

/-!
# `×μ`-Kummer structures as `Ism`-orbits (IUT II, Definition 4.9 (i))

IUT II, Example 1.8 (iv) (l.2510–2550) and Definition 4.9 (i) (l.11580–11660) of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory II.txt`:

* `Ism(G)` is "the compact topological group of `G`-isometries of `O^{×μ}(G)`, i.e. `G`-equivariant
  automorphisms of the ind-topological module `O^{×μ}(G)` that, for each open subgroup `H ⊆ G`,
  preserve the 'lattice' in `O^{×μ}(G)^H` determined by the image of `O^×(G)^H`";
* a **`×μ`-Kummer structure** on a Frobenioid with `G = Aut(A)` is an `Ism`-orbit of isomorphisms
  `κ : O^{×μ}(G) ≅ O^{×μ}(A)` of ind-topological `G`-modules; it determines and is determined by
  the submodules `I^κ_H(A) = κ(Im(O^×(G)^H)) ⊆ O^{×μ}(A)`, `H` open (l.11640–11660).

## Formalisation

* `fixedUnits H = (O^×_{\bar{ℚ}_p})^H`, `latticeH H` its image in `O^{×μ}`, and **`Ism p K`**: the
  subgroup of `Aut(O^{×μ}_{\bar{ℚ}_p})` of `G_K`-equivariant automorphisms preserving every
  `latticeH H`, `H` open (`inv_mem_Ism`: inversion lies in `Ism`, the image of `-1 ∈ Ẑ^×`).
* **Model of `O^{×μ}(G)`.** The group-theoretic algorithm `G ↦ (G ↷ O^{×μ}(G))` of IUT II,
  Example 1.8 (iii), (iv) ([AbsTopIII]; MR9) is not formalised; `O^{×μ}(G)` is taken to be the
  model `G_v ↷ O^{×μ}_{\bar{ℚ}_p}` (`fmuModel`), and a `×μ`-Kummer structure on `G ↷ M`
  (`GMObj`) is an `Ism`-orbit of isomorphisms `κ : (G_v ↷ O^{×μ}_{\bar{ℚ}_p}) ≅ (G ↷ M)`
  (`KummerStr`, the quotient by `kummerRel`: same isomorphism of groups, module isomorphisms
  differing by an element of `Ism`). The isomorphism `G_v ≅ G` is thus part of the data
  (in the paper `O^{×μ}(G)` is built from `G` itself and is functorial in all isomorphisms of `G`).
  Topologies of the ind-topological modules are not recorded.
* `kummerSub κ H = I^κ_H` and `KummerStr.sub` (well defined on orbits, `kummerSub_of_rel`);
  **`kummerRel_of_sub`**: two isomorphisms with the same group part and the same submodules
  `I^κ_H` for all open `H` lie in the same `Ism`-orbit (l.11644–11660, "essentially a tautology").
* `KummerStr.map` (transport along isomorphisms of `G ↷ M` data; functorial), the tautological
  Kummer structure on the model, and `F^{⊢×μ}`-prime-strips with `×μ`-Kummer structures
  (`FMuKComp`, `FMuKStripNon`, isomorphisms compatible with the Kummer structures).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open NumberField Iut.Frobenioid

/-! ### `Ism` -/

section Ism

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- **`(O^×_{\bar{ℚ}_p})^H`**, the units fixed by `H ⊆ G_K`. -/
def fixedUnits (H : Subgroup (PAdicGalois.GK p K)) : Subgroup (unitsOneBar p) where
  carrier := {u | ∀ σ ∈ H, actU p K σ u = u}
  mul_mem' {a b} ha hb σ hσ := by rw [map_mul, ha σ hσ, hb σ hσ]
  one_mem' σ _ := map_one _
  inv_mem' {a} ha σ hσ := by rw [map_inv, ha σ hσ]

/-- **The lattice `Im(O^×(G)^H) ⊆ O^{×μ}(G)^H`** (IUT II, Example 1.8 (iv)). -/
def latticeH (H : Subgroup (PAdicGalois.GK p K)) : Subgroup (OxMuBar p) :=
  (fixedUnits p K H).map (QuotientGroup.mk' _)

/-- The lattice lies in the `H`-invariants. -/
lemma smul_of_mem_latticeH {H : Subgroup (PAdicGalois.GK p K)} {x : OxMuBar p}
    (hx : x ∈ latticeH p K H) {σ : PAdicGalois.GK p K} (hσ : σ ∈ H) : σ • x = x := by
  obtain ⟨u, hu, rfl⟩ := hx
  change σ • (QuotientGroup.mk u : OxMuBar p) = QuotientGroup.mk u
  rw [smul_mk, hu σ hσ]

/-- **`Ism(G_K)`** (IUT II, Example 1.8 (iv)): the `G_K`-equivariant automorphisms of
`O^{×μ}_{\bar{ℚ}_p}` preserving the lattices `Im(O^×(G)^H)` for all open subgroups `H`. -/
def Ism : Subgroup (OxMuBar p ≃* OxMuBar p) where
  carrier := {ι | (∀ (σ : PAdicGalois.GK p K) x, ι (σ • x) = σ • ι x) ∧
    ∀ H : Subgroup (PAdicGalois.GK p K), IsOpen (H : Set (PAdicGalois.GK p K)) →
      ∀ x, x ∈ latticeH p K H ↔ ι x ∈ latticeH p K H}
  mul_mem' {f g} hf hg :=
    ⟨fun σ x => by
      change f (g (σ • x)) = σ • f (g x)
      rw [hg.1, hf.1],
    fun H hH x => (hg.2 H hH x).trans (hf.2 H hH (g x))⟩
  one_mem' := ⟨fun _ _ => rfl, fun _ _ _ => Iff.rfl⟩
  inv_mem' {f} hf :=
    ⟨fun σ x => by
      apply f.injective
      change f (f.symm (σ • x)) = f (σ • f.symm x)
      rw [hf.1, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply],
    fun H hH x => by
      have := hf.2 H hH (f.symm x)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm⟩

/-- Inversion on the commutative group `O^{×μ}`. -/
def invAut : OxMuBar p ≃* OxMuBar p where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' := mul_inv

/-- **Inversion lies in `Ism`** (the image of `-1 ∈ Ẑ^×`; IUT II, Example 1.8 (iv)). -/
theorem invAut_mem_Ism : invAut p ∈ Ism p K :=
  ⟨fun σ x => (smul_inv' σ x).symm, fun H _ x =>
    ⟨fun h => (latticeH p K H).inv_mem h, fun h => by
      have := (latticeH p K H).inv_mem h
      rwa [show (invAut p x)⁻¹ = x from inv_inv x] at this⟩⟩

end Ism

/-! ### `×μ`-Kummer structures -/

section Kummer

variable {D : InitialThetaData.{0}} {v : Vnon D} {X : GMObj}

/-- `Ism(G_v)`. -/
abbrev IsmV (D : InitialThetaData.{0}) (v : Vnon D) :
    Subgroup (OxMuBar (pv D v) ≃* OxMuBar (pv D v)) :=
  Ism (pv D v) (Lv D v)

/-- The module part of `κ : (G_v ↷ O^{×μ}) ≅ (G ↷ M)`. -/
def kM (κ : (fmuModel D v).Iso X) : OxMuBar (pv D v) ≃* X.M := κ.M

/-- The group part of `κ`, as a homomorphism. -/
def kG (κ : (fmuModel D v).Iso X) : Gv D v →* X.G := κ.G.toMulEquiv.toMonoidHom

/-- **Two isomorphisms in the same `Ism`-orbit**: the same isomorphism of groups, module parts
differing by an element of `Ism(G_v)`. -/
def kummerRel (κ κ' : (fmuModel D v).Iso X) : Prop :=
  (∀ g, κ.G g = κ'.G g) ∧ ∃ ι ∈ IsmV D v, ∀ m, kM κ' m = kM κ (ι m)

lemma kummerRel_refl (κ : (fmuModel D v).Iso X) : kummerRel κ κ :=
  ⟨fun _ => rfl, 1, (IsmV D v).one_mem, fun _ => rfl⟩

lemma kummerRel_symm {κ κ' : (fmuModel D v).Iso X} (h : kummerRel κ κ') : kummerRel κ' κ := by
  obtain ⟨hG, ι, hι, hM⟩ := h
  refine ⟨fun g => (hG g).symm, ι⁻¹, (IsmV D v).inv_mem hι, fun m => ?_⟩
  rw [hM]
  change kM κ m = kM κ (ι (ι.symm m))
  rw [MulEquiv.apply_symm_apply]

lemma kummerRel_trans {κ κ' κ'' : (fmuModel D v).Iso X} (h : kummerRel κ κ')
    (h' : kummerRel κ' κ'') : kummerRel κ κ'' := by
  obtain ⟨hG, ι, hι, hM⟩ := h
  obtain ⟨hG', ι', hι', hM'⟩ := h'
  exact ⟨fun g => (hG g).trans (hG' g), ι * ι', (IsmV D v).mul_mem hι hι',
    fun m => (hM' m).trans (hM _)⟩

/-- The `Ism`-orbit relation. -/
def kummerSetoid (D : InitialThetaData.{0}) (v : Vnon D) (X : GMObj) :
    Setoid ((fmuModel D v).Iso X) :=
  ⟨kummerRel, ⟨kummerRel_refl, kummerRel_symm, kummerRel_trans⟩⟩

/-- **A `×μ`-Kummer structure on `G ↷ M`** (IUT II, Definition 4.9 (i)): an `Ism`-orbit of
isomorphisms `(G_v ↷ O^{×μ}_{\bar{ℚ}_p}) ≅ (G ↷ M)`. -/
def KummerStr (D : InitialThetaData.{0}) (v : Vnon D) (X : GMObj) : Type :=
  Quotient (kummerSetoid D v X)

/-- **`I^κ_H = κ(Im(O^×(G)^H)) ⊆ M`** for a subgroup `H ⊆ G` (IUT II, Definition 4.9 (i)). -/
def kummerSub (κ : (fmuModel D v).Iso X) (H : Subgroup X.G) : Submonoid X.M :=
  (latticeH (pv D v) (Lv D v) (H.comap (kG κ))).toSubmonoid.map (kM κ).toMonoidHom

lemma mem_kummerSub (κ : (fmuModel D v).Iso X) (H : Subgroup X.G) (y : X.M) :
    y ∈ kummerSub κ H ↔ (kM κ).symm y ∈ latticeH (pv D v) (Lv D v) (H.comap (kG κ)) :=
  Submonoid.mem_map_equiv

/-- **`I^κ_H` depends only on the `Ism`-orbit of `κ`** (for open `H`). -/
theorem kummerSub_of_rel {κ κ' : (fmuModel D v).Iso X} (h : kummerRel κ κ') {H : Subgroup X.G}
    (hH : IsOpen (H : Set X.G)) : kummerSub κ H = kummerSub κ' H := by
  obtain ⟨hG, ι, hι, hM⟩ := h
  have hc : H.comap (kG κ') = H.comap (kG κ) := by
    ext g
    simp only [Subgroup.mem_comap]
    change κ'.G g ∈ H ↔ κ.G g ∈ H
    rw [hG]
  have hopen : IsOpen ((H.comap (kG κ) : Subgroup (Gv D v)) : Set (Gv D v)) :=
    hH.preimage κ.G.continuous
  ext y
  rw [mem_kummerSub, mem_kummerSub, hc]
  have hy : (kM κ').symm y = ι.symm ((kM κ).symm y) := by
    apply (kM κ').injective
    rw [MulEquiv.apply_symm_apply, hM, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rw [hy]
  have := ((IsmV D v).inv_mem hι).2 _ hopen ((kM κ).symm y)
  exact this

/-- **The submodules `I_H ⊆ M` of a `×μ`-Kummer structure** (`H` open). -/
def KummerStr.sub (k : KummerStr D v X) (H : Subgroup X.G) (hH : IsOpen (H : Set X.G)) :
    Submonoid X.M :=
  Quotient.lift (fun κ => kummerSub κ H) (fun _ _ h => kummerSub_of_rel h hH) k

/-- **A `×μ`-Kummer structure is determined by its submodules `I^κ_H`** (IUT II, Definition 4.9
(i), l.11644–11660): isomorphisms with the same isomorphism of groups and the same `I^κ_H` for all
open `H` lie in the same `Ism`-orbit. -/
theorem kummerRel_of_sub {κ κ' : (fmuModel D v).Iso X} (hG : ∀ g, κ.G g = κ'.G g)
    (hI : ∀ H : Subgroup X.G, IsOpen (H : Set X.G) → kummerSub κ H = kummerSub κ' H) :
    kummerRel κ κ' := by
  refine ⟨hG, (kM κ').trans (kM κ).symm, ⟨fun σ x => ?_, fun H hH x => ?_⟩, fun m => ?_⟩
  · change (kM κ).symm (kM κ' (σ • x)) = σ • (kM κ).symm (kM κ' x)
    apply (kM κ).injective
    rw [MulEquiv.apply_symm_apply]
    change κ'.M (σ • x) = κ.M (σ • (kM κ).symm (κ'.M x))
    calc κ'.M (σ • x) = κ'.G σ • κ'.M x := κ'.equivariant σ x
      _ = κ.G σ • κ'.M x := congrArg (· • κ'.M x) (hG σ).symm
      _ = κ.G σ • κ.M ((kM κ).symm (κ'.M x)) :=
        congrArg (κ.G σ • ·) ((kM κ).apply_symm_apply _).symm
      _ = κ.M (σ • (kM κ).symm (κ'.M x)) := (κ.equivariant _ _).symm
  · let H₁ : Subgroup X.G := H.map (kG κ)
    have hH₁ : IsOpen (H₁ : Set X.G) := by
      have : (H₁ : Set X.G) = κ.G '' (H : Set (Gv D v)) := rfl
      rw [this]
      exact κ.G.toHomeomorph.isOpenMap _ hH
    have hc : H₁.comap (kG κ) = H := Subgroup.comap_map_eq_self_of_injective κ.G.injective H
    have hc' : H₁.comap (kG κ') = H := by
      rw [← hc]
      ext g
      simp only [Subgroup.mem_comap]
      change κ'.G g ∈ H₁ ↔ κ.G g ∈ H₁
      rw [hG]
    have h := hI H₁ hH₁
    have e := congrArg (fun S : Submonoid X.M => κ'.M x ∈ S) h
    simp only [mem_kummerSub, hc, hc'] at e
    have e' : (kM κ').symm (κ'.M x) = x := (kM κ').symm_apply_apply x
    have := (Iff.of_eq e).symm
    rw [e'] at this
    exact this
  · change kM κ' m = kM κ ((kM κ).symm (kM κ' m))
    rw [MulEquiv.apply_symm_apply]

/-! ### Functoriality and `F^{⊢×μ}`-prime-strips with Kummer structures -/

variable {Y Z : GMObj}

lemma kummerRel_trans_iso {κ κ' : (fmuModel D v).Iso X} (h : kummerRel κ κ') (e : X.Iso Y) :
    kummerRel (κ.trans e) (κ'.trans e) := by
  obtain ⟨hG, ι, hι, hM⟩ := h
  exact ⟨fun g => congrArg e.G (hG g), ι, hι, fun m => congrArg e.M (hM m)⟩

/-- **Transport of `×μ`-Kummer structures** along an isomorphism of `G ↷ M` data. -/
def KummerStr.map (e : X.Iso Y) : KummerStr D v X → KummerStr D v Y :=
  Quotient.map (fun κ => κ.trans e) fun _ _ h => kummerRel_trans_iso h e

lemma KummerStr.map_mk (e : X.Iso Y) (κ : (fmuModel D v).Iso X) :
    KummerStr.map e (Quotient.mk _ κ : KummerStr D v X) = Quotient.mk _ (κ.trans e) := rfl

lemma iso_trans_refl (κ : (fmuModel D v).Iso X) : κ.trans (GMObj.Iso.refl X) = κ :=
  GMObj.Iso.ext (fun _ => rfl) fun _ => rfl

lemma iso_refl_trans (κ : (fmuModel D v).Iso X) : (GMObj.Iso.refl _).trans κ = κ :=
  GMObj.Iso.ext (fun _ => rfl) fun _ => rfl

lemma KummerStr.map_refl (k : KummerStr D v X) : k.map (GMObj.Iso.refl X) = k := by
  obtain ⟨κ, rfl⟩ := Quotient.exists_rep k
  exact congrArg (Quotient.mk _) (iso_trans_refl κ)

lemma KummerStr.map_trans (e : X.Iso Y) (f : Y.Iso Z) (k : KummerStr D v X) :
    k.map (e.trans f) = (k.map e).map f := by
  obtain ⟨κ, rfl⟩ := Quotient.exists_rep k
  exact congrArg (Quotient.mk _) (GMObj.Iso.ext (fun _ => rfl) fun _ => rfl)

lemma KummerStr.map_symm (e : X.Iso Y) (k : KummerStr D v X) : (k.map e).map e.symm = k := by
  obtain ⟨κ, rfl⟩ := Quotient.exists_rep k
  refine congrArg (Quotient.mk _) (GMObj.Iso.ext (fun g => ?_) fun m => ?_)
  · exact ContinuousMulEquiv.symm_apply_apply e.G (κ.G g)
  · exact MulEquiv.symm_apply_apply e.M (κ.M m)

variable (D v)

/-- **The tautological `×μ`-Kummer structure** on the model `G_v ↷ O^{×μ}_{\bar{ℚ}_p}`. -/
def KummerStr.taut : KummerStr D v (fmuModel D v) := Quotient.mk _ (GMObj.Iso.refl _)

/-- **A constituent of an `F^{⊢×μ}`-prime-strip with a `×μ`-Kummer structure** (a
split-`×μ`-Kummer constituent, IUT II, Definition 4.9 (i), (vii)). -/
structure FMuKComp : Type 1 where
  /-- The `F^{⊢×μ}`-constituent. -/
  X : FMuComp D v
  /-- The `×μ`-Kummer structure. -/
  kappa : KummerStr D v X.X

variable {D v}

/-- **Isomorphisms compatible with the Kummer structures.** -/
structure FMuKComp.Iso (A B : FMuKComp D v) where
  /-- The isomorphism of `G ↷ M` data. -/
  e : A.X.X.Iso B.X.X
  /-- It maps the Kummer structure of `A` to that of `B`. -/
  kappa : A.kappa.map e = B.kappa

/-- The identity. -/
def FMuKComp.Iso.refl (A : FMuKComp D v) : A.Iso A := ⟨GMObj.Iso.refl _, KummerStr.map_refl _⟩

/-- The inverse. -/
def FMuKComp.Iso.symm {A B : FMuKComp D v} (f : A.Iso B) : B.Iso A :=
  ⟨f.e.symm, by rw [← f.kappa, KummerStr.map_symm]⟩

/-- The composite. -/
def FMuKComp.Iso.trans {A B C : FMuKComp D v} (f : A.Iso B) (g : B.Iso C) : A.Iso C :=
  ⟨f.e.trans g.e, by rw [KummerStr.map_trans, f.kappa, g.kappa]⟩

variable (D v)

/-- **The tautological `×μ`-Kummer constituent** `(G_v ↷ O^{×μ}_{\bar{ℚ}_p}, κ = id)`. -/
def FMuKComp.ofThetaData : FMuKComp D v :=
  ⟨⟨fmuModel D v, ⟨GMObj.Iso.refl _⟩⟩, KummerStr.taut D v⟩

/-- **A Kummer constituent is isomorphic to the tautological one** (through any representative
of its Kummer structure). -/
theorem FMuKComp.nonempty_iso (A : FMuKComp D v) :
    Nonempty ((FMuKComp.ofThetaData D v).Iso A) := by
  obtain ⟨κ, hκ⟩ := Quotient.exists_rep A.kappa
  refine ⟨⟨κ, ?_⟩⟩
  rw [← hκ]
  exact congrArg (Quotient.mk _) (iso_refl_trans κ)

end Kummer

/-- **The non-archimedean part of an `F^{⊢×μ}`-prime-strip with `×μ`-Kummer structures**. -/
structure FMuKStripNon (D : InitialThetaData.{0}) : Type 1 where
  /-- The constituents. -/
  comp : ∀ v : Vnon D, FMuKComp D v

namespace FMuKStripNon

variable {D : InitialThetaData.{0}}

/-- Isomorphisms (constituentwise, compatible with the Kummer structures). -/
def Iso (P Q : FMuKStripNon D) : Type := ∀ v, (P.comp v).Iso (Q.comp v)

/-- The forgetful map to `F^{⊢×μ}`-prime-strips. -/
def toFMu (P : FMuKStripNon D) : FMuStripNon D := ⟨fun v => (P.comp v).X⟩

variable (D) in
/-- The tautological strip. -/
def ofThetaData : FMuKStripNon D := ⟨fun v => FMuKComp.ofThetaData D v⟩

/-- **Any two `F^{⊢×μ}`-prime-strips with `×μ`-Kummer structures are isomorphic.** -/
theorem nonempty_iso (P Q : FMuKStripNon D) : Nonempty (P.Iso Q) :=
  ⟨fun v => ((FMuKComp.nonempty_iso D v (P.comp v)).some.symm).trans
    (FMuKComp.nonempty_iso D v (Q.comp v)).some⟩

end FMuKStripNon

end PrimeStrip

end Multiradial

end Iut
