/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Arch
import Iut.Cor312.ThetaData.Basic

/-!
# Prime-strips built from initial Θ-data (IUT I, Definitions 4.1, 5.2; IUT II, Definition 4.9)

The **object layer** of the prime-strips (see `README.md`, "Scope decisions"). A prime-strip is a
family, indexed by `V ≅ V_mod` (`Vp D`, the places of `F_mod`; IUT I, Definition 3.1(e)), of
objects each of which is isomorphic to a **model built from `D`**. The objects live in a **kind**
(`Kind`: a type of objects with isomorphisms; for instance topological groups with isomorphisms of
topological groups, or categories with equivalences of categories).

* `PrimeStrip K M`: prime-strips of the kinds `K v` relative to the models `M v`; `PrimeStrip.Iso`
  (componentwise isomorphisms, Definitions 4.1(iv), 5.2(iii)); any two prime-strips are isomorphic
  (`PrimeStrip.nonempty_iso`); the tautological prime-strip (`tautological`); capsules.
* **The models built from `D`** (`v ∈ V^non` | `v ∈ V^arc`):
  * `D`-prime-strips (Definition 4.1(i)): `Π_v` (`LocalThetaData.PivBad` at `V^bad`, tempered;
    `PivGood` at `V^good`, étale) as a topological group | the topological field `K_v`;
  * `D^⊢`-prime-strips (Definition 4.1(iii)): the decomposition group `G_v ⊆ Gal(F̄/K)`
    (`LocalThetaData.decomp`) | the topological monoid `O^▷(K_v) = {0 < |z| ≤ 1}`;
  * `F`-prime-strips (Definition 5.2(i)): the `p`-adic Frobenioid of `K_v` (P15, `PAdic`) up to
    equivalence | the archimedean Frobenioid of `K_v` (`Iut.Frobenioid.Arch`) with `K_v`;
  * `F^⊢`-prime-strips (Definition 5.2(ii)): the `p`-adic Frobenioid with the base `G_v` | the
    archimedean Frobenioid with `O^▷(K_v)`;
  * `F^{⊢×μ}`-prime-strips (IUT II, Definition 4.9(vii)): the GM-data `G_v ↷ O^{×μ}(K_v)` |
    `{1} ↷ O^{×μ}(K_v)` (`O^{×μ} = O^×/μ`, the unit circle modulo torsion);
  * `F^⊩`-prime-strips (Definition 5.2(iv)): the global realified Frobenioid `C^⊩_mod` of `F_mod`
    (P15, `GlobalRealified`) up to equivalence, with an `F^⊢`-prime-strip;
  * the global objects `D^⊚ = B(C̲_K)^0` and `D^⊚± = B(X̲_K)^0` (Definitions 4.1(v), 6.1(v)), by
    their (étale) fundamental groups.

## Simplifications (documented deviations)

* A category `D_v ≃ B^temp(Π_v)^0` is recorded by the topological group `Π_v` (the category
  determines and is determined by `Π_v` up to inner automorphism, [AbsTopI], [SemiAnbd]).
* At `v ∈ V^arc`, the Aut-holomorphic orbispace `D_v` is replaced by the topological field `K_v`
  (`≅ ℂ`), and the Kummer structure `κ_v` of `F_v` is not recorded.
* The Frobenioids are over the trivial Galois extension (base `Pt`, as in P15), not over `B(G_v)^0`
  or `D_v`; the tempered Frobenioid at `V^bad` is replaced by the `p`-adic Frobenioid of `K_v` (its
  base-field portion; P15 has only the interface `TemperedFrobenioidData`).
* `O^{×μ}` is the `G_v`-invariant (base-field) portion `O^×(K_v)/μ`, with the trivial `G_v`-action.
* `F^⊩`: the bijection `Prime(C^⊩) ≅ V` and the isomorphisms `ρ_v` are not recorded.
* **Mono-analyticization** `†D ↦ †D^⊢` and the passage from `F`- to `D`-prime-strips are
  group-theoretic reconstruction algorithms (P17); they are not defined on abstract prime-strips
  here (only the interface `PrimeStrip.map` for componentwise operations of kinds).
-/

namespace Iut

namespace HodgeTheater

open CategoryTheory NumberField Frobenioid

universe u w

/-! ### Kinds -/

/-- **A kind of local object**: a type of objects with types of isomorphisms, identities,
inverses and composites. -/
structure Kind : Type (u + 2) where
  /-- The objects. -/
  Obj : Type (u + 1)
  /-- The isomorphisms. -/
  Iso : Obj → Obj → Type u
  /-- Identities. -/
  refl : ∀ X, Iso X X
  /-- Inverses. -/
  symm : ∀ {X Y}, Iso X Y → Iso Y X
  /-- Composites. -/
  trans : ∀ {X Y Z}, Iso X Y → Iso Y Z → Iso X Z

namespace Kind

/-- The product of two kinds (pairs of objects, pairs of isomorphisms). -/
def prod (K L : Kind.{u}) : Kind.{u} where
  Obj := K.Obj × L.Obj
  Iso X Y := K.Iso X.1 Y.1 × L.Iso X.2 Y.2
  refl X := (K.refl X.1, L.refl X.2)
  symm f := (K.symm f.1, L.symm f.2)
  trans f g := (K.trans f.1 g.1, L.trans f.2 g.2)

/-- A topological group. -/
structure TGrp : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [grp : Group carrier]
  [top : TopologicalSpace carrier]

attribute [instance] TGrp.grp TGrp.top

/-- **Topological groups**, with isomorphisms of topological groups. -/
def tgrp : Kind.{u} where
  Obj := TGrp.{u}
  Iso G H := G.carrier ≃ₜ* H.carrier
  refl _ := ContinuousMulEquiv.refl _
  symm f := f.symm
  trans f g := f.trans g

/-- A topological monoid. -/
structure TMon : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [mon : Monoid carrier]
  [top : TopologicalSpace carrier]

attribute [instance] TMon.mon TMon.top

/-- **Topological monoids**, with isomorphisms of topological monoids. -/
def tmon : Kind.{u} where
  Obj := TMon.{u}
  Iso M N := M.carrier ≃ₜ* N.carrier
  refl _ := ContinuousMulEquiv.refl _
  symm f := f.symm
  trans f g := f.trans g

/-- A topological field. -/
structure TField : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [fld : Field carrier]
  [top : TopologicalSpace carrier]

attribute [instance] TField.fld TField.top

/-- **Topological fields**, with ring isomorphisms that are homeomorphisms. -/
def tfield : Kind.{u} where
  Obj := TField.{u}
  Iso A B := {e : A.carrier ≃+* B.carrier // Continuous e ∧ Continuous e.symm}
  refl _ := ⟨RingEquiv.refl _, continuous_id, continuous_id⟩
  symm f := ⟨f.1.symm, f.2.2, f.2.1⟩
  trans f g := ⟨f.1.trans g.1, g.2.1.comp f.2.1, f.2.2.comp g.2.2⟩

/-- **Categories**, with equivalences of categories (Frobenioids are recorded up to
equivalence, IUT I, Definition 5.2(i)). -/
def cat : Kind.{u} where
  Obj := Cat.{u, u}
  Iso C D := C ≌ D
  refl _ := CategoryTheory.Equivalence.refl
  symm f := f.symm
  trans f g := f.trans g

/-- GM-data `G ↷ M` (IUT II, Definition 4.9; the universe-polymorphic version of the wall's
`Iut.Wall.GMData`): a topological group acting on a commutative monoid, with a compact
structure (one subset). -/
structure GM : Type (u + 1) where
  /-- The topological group. -/
  G : Type u
  /-- The monoid. -/
  M : Type u
  [instGroup : Group G]
  [instTop : TopologicalSpace G]
  [instMonoid : CommMonoid M]
  [instAction : MulDistribMulAction G M]
  /-- The compact structure. -/
  compact : Set M

attribute [instance] GM.instGroup GM.instTop GM.instMonoid GM.instAction

/-- An isomorphism of GM-data. -/
structure GMIso (X Y : GM.{u}) where
  /-- The isomorphism of topological groups. -/
  G : X.G ≃ₜ* Y.G
  /-- The isomorphism of monoids. -/
  M : X.M ≃* Y.M
  equivariant : ∀ (g : X.G) (m : X.M), M (g • m) = G g • M m
  compact : M '' X.compact = Y.compact

/-- **GM-data**, with their isomorphisms. -/
def gm : Kind.{u} where
  Obj := GM.{u}
  Iso := GMIso
  refl X := ⟨ContinuousMulEquiv.refl _, MulEquiv.refl _, fun _ _ => rfl, Set.image_id _⟩
  symm e := ⟨e.G.symm, e.M.symm, fun g m => by
      apply e.M.injective
      rw [MulEquiv.apply_symm_apply, e.equivariant, ContinuousMulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply], by
      rw [← e.compact, ← Set.image_comp]
      simp⟩
  trans e f := ⟨e.G.trans f.G, e.M.trans f.M, fun g m => by
      change f.M (e.M (g • m)) = f.G (e.G g) • f.M (e.M m)
      rw [e.equivariant, f.equivariant], by
      rw [MulEquiv.coe_trans, Set.image_comp, e.compact, f.compact]⟩

end Kind

/-! ### Prime-strips -/

/-- **A prime-strip** of kinds `K v` relative to models `M v` (IUT I, Definitions 4.1, 5.2): an
object at every `v`, isomorphic to the model. -/
structure PrimeStrip {V : Type w} (K : V → Kind.{u}) (M : ∀ x, (K x).Obj) where
  /-- The constituent objects. -/
  obj : ∀ x, (K x).Obj
  /-- Each constituent object is isomorphic to the model. -/
  iso_model : ∀ x, Nonempty ((K x).Iso (obj x) (M x))

namespace PrimeStrip

variable {V : Type w} {K : V → Kind.{u}} {M : ∀ x, (K x).Obj}

/-- **A morphism of prime-strips** (IUT I, Definition 5.2(iii)): isomorphisms of the constituent
objects. -/
def Iso (P Q : PrimeStrip K M) : Type (max w u) := ∀ x, (K x).Iso (P.obj x) (Q.obj x)

/-- The identity. -/
def Iso.refl (P : PrimeStrip K M) : P.Iso P := fun x => (K x).refl _

/-- The inverse. -/
def Iso.symm {P Q : PrimeStrip K M} (f : P.Iso Q) : Q.Iso P := fun x => (K x).symm (f x)

/-- The composite. -/
def Iso.trans {P Q R : PrimeStrip K M} (f : P.Iso Q) (g : Q.Iso R) : P.Iso R :=
  fun x => (K x).trans (f x) (g x)

variable (K M) in
/-- **The tautological prime-strip** (IUT I, Examples 4.3(iv), 4.4(ii)): the models. -/
def tautological : PrimeStrip K M := ⟨M, fun x => ⟨(K x).refl _⟩⟩

/-- **Any two prime-strips are isomorphic.** -/
theorem nonempty_iso (P Q : PrimeStrip K M) : Nonempty (P.Iso Q) :=
  ⟨fun x => (K x).trans (P.iso_model x).some ((K x).symm (Q.iso_model x).some)⟩

/-- A componentwise operation of kinds (for instance mono-analyticization, IUT I, Definition
4.1(iv)): a map of objects with a map of isomorphisms. -/
structure KindMap (K L : Kind.{u}) where
  /-- The map of objects. -/
  obj : K.Obj → L.Obj
  /-- The map of isomorphisms. -/
  map : ∀ {X Y}, K.Iso X Y → L.Iso (obj X) (obj Y)

/-- A componentwise operation carrying the models to isomorphs of the models carries prime-strips
to prime-strips. -/
def map {L : V → Kind.{u}} {N : ∀ x, (L x).Obj} (F : ∀ x, KindMap (K x) (L x))
    (hF : ∀ x, Nonempty ((L x).Iso ((F x).obj (M x)) (N x))) (P : PrimeStrip K M) :
    PrimeStrip L N :=
  ⟨fun x => (F x).obj (P.obj x), fun x =>
    ⟨(L x).trans ((F x).map (P.iso_model x).some) (hF x).some⟩⟩

/-- The induced isomorphisms. -/
def mapIso {L : V → Kind.{u}} {N : ∀ x, (L x).Obj} (F : ∀ x, KindMap (K x) (L x))
    (hF : ∀ x, Nonempty ((L x).Iso ((F x).obj (M x)) (N x))) {P Q : PrimeStrip K M}
    (f : P.Iso Q) : (map F hF P).Iso (map F hF Q) := fun x => (F x).map (f x)

end PrimeStrip

/-! ### The models built from initial Θ-data -/

section Models

variable (D : InitialThetaData.{u})

/-- **`V ≅ V_mod`**: the places of `F_mod`, indexing the prime-strips (IUT I, Definition 3.1(e):
the section `V_mod → V(K)` identifies `V_mod` with `V`). -/
abbrev Vp : Type u := Place ↥(fieldOfModuli D.F D.E)

/-- The local field `K_v` at a finite place of the section. -/
abbrev Kfin (w : FinitePlace ↥(fieldOfModuli D.F D.E)) : Type u :=
  completionAt D.Kt (D.V.sectFin w)

/-- The local field `K_v` at an archimedean place of the section. -/
abbrev Karc (w : InfinitePlace ↥(fieldOfModuli D.F D.E)) : Type u := (D.V.sectInf w).Completion

/-- `O^▷(L) = {z ≠ 0 : |z| ≤ 1}` (IUT I, Example 3.4(ii)). -/
def orhdMonoid (L : Type u) [NormedField L] : Submonoid L where
  carrier := {z | z ≠ 0 ∧ ‖z‖ ≤ 1}
  mul_mem' {a b} ha hb := ⟨mul_ne_zero ha.1 hb.1, by
    rw [norm_mul]
    exact mul_le_one₀ ha.2 (norm_nonneg _) hb.2⟩
  one_mem' := ⟨one_ne_zero, by simp⟩

/-- **`Π_v`** (IUT I, Definition 3.1(e), (f)): tempered at `V^bad`, étale at `V^good ∩ V^non`. -/
noncomputable def piModel (w : FinitePlace ↥(fieldOfModuli D.F D.E)) : Kind.TGrp.{u} := by
  classical
  exact if w ∈ D.VBad then ⟨D.localData.PivBad w⟩ else ⟨D.localData.PivGood w⟩

/-- **The decomposition group `G_v ⊆ Gal(F̄/K)`** (IUT I, Definition 3.1(e)). -/
noncomputable def galModel (w : FinitePlace ↥(fieldOfModuli D.F D.E)) : Kind.TGrp.{u} :=
  ⟨D.localData.decomp (D.V.sectFin w)⟩

/-- The topological field `K_v` at `v ∈ V^arc`. -/
noncomputable def karcModel (w : InfinitePlace ↥(fieldOfModuli D.F D.E)) : Kind.TField.{u} :=
  ⟨(Karc D) w⟩

/-- The topological monoid `O^▷(K_v)` at `v ∈ V^arc`. -/
noncomputable def orhdModel (w : InfinitePlace ↥(fieldOfModuli D.F D.E)) : Kind.TMon.{u} :=
  ⟨orhdMonoid ((Karc D) w)⟩

/-- The `p`-adic Frobenioid of `K_v` at `v ∈ V^non` (P15), as a category. -/
noncomputable def padicModel (w : FinitePlace ↥(fieldOfModuli D.F D.E)) : Cat.{u, u} :=
  Cat.of (PAdic (D.V.sectFin w))

/-- The archimedean Frobenioid of `K_v` at `v ∈ V^arc`, as a category. -/
noncomputable def archModel (w : InfinitePlace ↥(fieldOfModuli D.F D.E)) : Cat.{u, u} :=
  Cat.of (Arch (D.V.sectInf w))

/-! #### `D`- and `D^⊢`-prime-strips -/

/-- The kinds of the constituents of a `D`-prime-strip. -/
def dKind : (Vp D) → Kind.{u} := Sum.elim (fun _ => Kind.tgrp) (fun _ => Kind.tfield)

/-- **The tautological `D`-prime-strip** `{D_v}_{v ∈ V}` (IUT I, Definition 4.1(i), Example
4.3(iv)). -/
noncomputable def dModel : ∀ x : (Vp D), ((dKind D) x).Obj
  | Sum.inl w => (piModel D) w
  | Sum.inr w => (karcModel D) w

/-- **`D`-prime-strips** (IUT I, Definition 4.1(i)). -/
abbrev DStrip : Type (u + 1) := PrimeStrip (dKind D) (dModel D)

/-- The kinds of the constituents of a `D^⊢`-prime-strip. -/
def dVdashKind : (Vp D) → Kind.{u} := Sum.elim (fun _ => Kind.tgrp) (fun _ => Kind.tmon)

/-- **The tautological `D^⊢`-prime-strip** (IUT I, Definition 4.1(iii)). -/
noncomputable def dVdashModel : ∀ x : (Vp D), ((dVdashKind D) x).Obj
  | Sum.inl w => (galModel D) w
  | Sum.inr w => (orhdModel D) w

/-- **`D^⊢`-prime-strips** (IUT I, Definition 4.1(iii)). -/
abbrev DVdashStrip : Type (u + 1) := PrimeStrip (dVdashKind D) (dVdashModel D)

/-! #### `F`-, `F^⊢`- and `F^⊩`-prime-strips -/

/-- The kinds of the constituents of an `F`-prime-strip. -/
def fKind : (Vp D) → Kind.{u} :=
  Sum.elim (fun _ => Kind.cat) (fun _ => Kind.prod Kind.cat Kind.tfield)

/-- **The tautological `F`-prime-strip** (IUT I, Definition 5.2(i)): `C_v` (and `D_v` at
`V^arc`). -/
noncomputable def fModel : ∀ x : (Vp D), ((fKind D) x).Obj
  | Sum.inl w => (padicModel D) w
  | Sum.inr w => ((archModel D) w, (karcModel D) w)

/-- **`F`-prime-strips** (IUT I, Definition 5.2(i)). -/
abbrev FStrip : Type (u + 1) := PrimeStrip (fKind D) (fModel D)

/-- The kinds of the constituents of an `F^⊢`-prime-strip. -/
def fVdashKind : (Vp D) → Kind.{u} :=
  Sum.elim (fun _ => Kind.prod Kind.cat Kind.tgrp) (fun _ => Kind.prod Kind.cat Kind.tmon)

/-- **The tautological `F^⊢`-prime-strip** (IUT I, Definition 5.2(ii)): the split Frobenioids,
recorded by the Frobenioid and the base (`G_v`, resp. `O^▷(K_v)`). -/
noncomputable def fVdashModel : ∀ x : (Vp D), ((fVdashKind D) x).Obj
  | Sum.inl w => ((padicModel D) w, (galModel D) w)
  | Sum.inr w => ((archModel D) w, (orhdModel D) w)

/-- **`F^⊢`-prime-strips** (IUT I, Definition 5.2(ii)). -/
abbrev FVdashStrip : Type (u + 1) := PrimeStrip (fVdashKind D) (fVdashModel D)

/-- **The global realified Frobenioid `C^⊩_mod` of `F_mod`** (IUT I, Example 3.5(i); P15). -/
noncomputable def rlfModel : Cat.{u, u} := Cat.of (GlobalRealified ↥(fieldOfModuli D.F D.E))

/-- **An `F^⊩`-prime-strip** (IUT I, Definition 5.2(iv), simplified): a category equivalent to
`C^⊩_mod` and an `F^⊢`-prime-strip. -/
structure FRlfStrip where
  /-- The global realified Frobenioid. -/
  C : Cat.{u, u}
  equiv_model : Nonempty (C ≌ (rlfModel D))
  /-- The `F^⊢`-prime-strip. -/
  strip : (FVdashStrip D)

/-- The tautological `F^⊩`-prime-strip `F^⊩_mod` (IUT I, Example 3.5(ii)). -/
noncomputable def FRlfStrip.tautological : (FRlfStrip D) :=
  ⟨rlfModel D, ⟨CategoryTheory.Equivalence.refl⟩, PrimeStrip.tautological _ _⟩

/-! #### The global objects `D^⊚`, `D^⊚±` -/

/-- **`π_1(D^⊚) = Π_{C̲_K}`** (IUT I, Definition 4.1(v): `D^⊚ = B(C̲_K)^0`). -/
noncomputable def dCircModel : Kind.TGrp.{u} := ⟨D.orb.CKu.genuinePi1⟩

/-- **`π_1(D^⊚±) = Π_{X̲_K}`** (IUT I, Definition 6.1(v): `D^⊚± = B(X̲_K)^0`). -/
noncomputable def dCircPmModel : Kind.TGrp.{u} := ⟨D.orb.XKu.genuinePi1⟩

/-- An isomorph of `D^⊚` (recorded by its fundamental group). -/
def DCirc : Type (u + 1) := {G : Kind.TGrp.{u} // Nonempty (G.carrier ≃ₜ* (dCircModel D).carrier)}

/-- An isomorph of `D^⊚±` (recorded by its fundamental group). -/
def DCircPm : Type (u + 1) :=
  {G : Kind.TGrp.{u} // Nonempty (G.carrier ≃ₜ* (dCircPmModel D).carrier)}

/-- The tautological `D^⊚`. -/
noncomputable def DCirc.tautological : (DCirc D) := ⟨(dCircModel D), ⟨ContinuousMulEquiv.refl _⟩⟩

/-- The tautological `D^⊚±`. -/
noncomputable def DCircPm.tautological : (DCircPm D) :=
  ⟨(dCircPmModel D), ⟨ContinuousMulEquiv.refl _⟩⟩

end Models

/-! #### `F^{⊢×μ}`-prime-strips -/

section FMu

variable (D : InitialThetaData.{u})

/-- The trivial action of a group on a commutative monoid. -/
@[reducible] def trivialMulDistribMulAction (G M : Type*) [Group G] [CommMonoid M] :
    MulDistribMulAction G M where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

/-- The units of norm one of a normed field. -/
def unitsOne (L : Type u) [NormedField L] : Subgroup Lˣ where
  carrier := {x | ‖(x : L)‖ = 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul, norm_mul] at ha hb ⊢
    rw [ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, norm_inv] at ha ⊢
    rw [ha, inv_one]

/-- **`O^{×μ}(L) = O^×(L)/μ(L)`** (IUT II, Definition 4.9): the units of norm one modulo
torsion. -/
abbrev OxMu (L : Type u) [NormedField L] : Type u :=
  unitsOne L ⧸ CommGroup.torsion (unitsOne L)

/-- The GM-data `G ↷ O^{×μ}(L)` with the trivial action and the full compact structure. -/
noncomputable def gmOf (G : Type u) [Group G] [TopologicalSpace G] (L : Type u) [NormedField L] :
    Kind.GM.{u} :=
  { G := G
    M := OxMu L
    instAction := trivialMulDistribMulAction G _
    compact := Set.univ }

/-- The kinds of the constituents of an `F^{⊢×μ}`-prime-strip. -/
def fmuKind : (Vp D) → Kind.{u} := fun _ => Kind.gm

/-- **The tautological `F^{⊢×μ}`-prime-strip** (IUT II, Definition 4.9(vii), simplified):
`G_v ↷ O^{×μ}(K_v)` at `v ∈ V^non`, `{1} ↷ O^{×μ}(K_v)` at `v ∈ V^arc`. -/
noncomputable def fmuModel : ∀ x : (Vp D), ((fmuKind D) x).Obj
  | Sum.inl w => gmOf ((galModel D) w).carrier ((Kfin D) w)
  | Sum.inr w => gmOf PUnit.{u + 1} ((Karc D) w)

/-- **`F^{⊢×μ}`-prime-strips** (IUT II, Definition 4.9(vii)). -/
abbrev FMuStrip : Type (u + 1) := PrimeStrip (fmuKind D) (fmuModel D)

end FMu

end HodgeTheater

end Iut
