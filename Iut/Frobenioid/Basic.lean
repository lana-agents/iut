/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.EpiMono
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.Abel

/-!
# Monoids on a category and elementary Frobenioids ([FrdI] §0, Definition 1.1)

References: [FrdI] = S. Mochizuki, *The geometry of Frobenioids I: the general theory*,
Kyushu J. Math. 62 (2008); page numbers are those of the RIMS PDF.

## Encoding of the divisor monoid

[FrdI], Definition 1.1(ii): a *monoid on* `D` is a contravariant functor `Φ : D → Mon`
(commutative monoids, written additively) such that (a) every `α^* : Φ(A) → Φ(B)` is
characteristically injective and (b) `α^*` is an isomorphism for every FSM-morphism `α`.
`Φ` is *divisorial* if every `Φ(A)` is integral, saturated, sharp (and of characteristic type,
automatic for sharp monoids).

An integral monoid `M` is the same as a submonoid of its groupification `M^gp` generating it
(as a group). We therefore record a divisorial monoid as a family of abelian groups
`Φ^gp(A)` (`DivMonoid.obj`) with pull-back homomorphisms, together with **cones**
`Φ(A) ⊆ Φ^gp(A)` (`DivMonoid.pos`) which are

* stable under pull-back,
* **sharp**: `Φ(A) ∩ −Φ(A) = 0`,
* **saturated**: `n·x ∈ Φ(A)`, `n ≥ 1` implies `x ∈ Φ(A)`,
* **generating**: `Φ^gp(A) = Φ(A) − Φ(A)` (so `Φ^gp(A)` is the groupification).

For a sharp monoid, `Φ^char = Φ`, so condition (a) is injectivity of `α^*` on `Φ(A)`, which
(for integral monoids generating their groups) is the same as injectivity on `Φ^gp(A)`;
we require the latter (`GrpOn.pb_injective`). Condition (b) is `GrpOn.pb_bijective_of_fsm`
together with `DivMonoid.pos_surj_of_fsm`.

A **group-like** monoid on `D` (the rational function monoid `B` of [FrdI], Theorem 5.2) is a
family of abelian groups with injective pull-backs (`GrpOn`; for groups, characteristic
injectivity is injectivity).

## Contents

* `IsFiberwiseSurjective`, `IsFSM`, `TotallyEpimorphic` ([FrdI] §0, pp. 14–15);
* `GrpOn D`, `DivMonoid D`, `DivMonoid.le` (`a ≤ b` iff `b − a ∈ Φ(A)`, [FrdI] §0, p. 12),
  `DivMonoid.IsPrimary`;
* `DivHom B Φ`: homomorphisms of monoids on `D` (natural transformations);
* **`Elem Φ`**: the elementary Frobenioid `F_Φ` ([FrdI], Definition 1.1(iii)): objects those of
  `D`, morphisms `(φ_D, Z_φ ∈ Φ(A_D), n_φ ∈ ℕ_{≥1})`, composition
  `ψ ∘ φ = (ψ_D ∘ φ_D, φ_D^*(Z_ψ) + n_ψ·Z_φ, n_ψ·n_φ)`; `Elem.proj : F_Φ ⥤ D`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u

section Category

variable {C : Type u} [Category.{v} C]

/-- **Fiberwise-surjective arrows** ([FrdI] §0, p. 14): `β : B → A` such that every `γ : X → A`
has arrows `δ_B : Y → B`, `δ_X : Y → X` with `β ∘ δ_B = γ ∘ δ_X`. -/
def IsFiberwiseSurjective {B A : C} (β : B ⟶ A) : Prop :=
  ∀ ⦃X : C⦄ (γ : X ⟶ A), ∃ (Y : C) (δB : Y ⟶ B) (δX : Y ⟶ X), δB ≫ β = δX ≫ γ

/-- **FSM-morphisms** ([FrdI] §0, p. 14): fiberwise-surjective monomorphisms. -/
def IsFSM {B A : C} (β : B ⟶ A) : Prop := Mono β ∧ IsFiberwiseSurjective β

lemma isFSM_of_isIso {B A : C} (β : B ⟶ A) [IsIso β] : IsFSM β :=
  ⟨inferInstance, fun _ γ => ⟨_, γ ≫ inv β, 𝟙 _, by simp⟩⟩

variable (C) in
/-- **Totally epimorphic categories** ([FrdI] §0, p. 15): every morphism is an epimorphism. -/
class TotallyEpimorphic : Prop where
  epi : ∀ {X Y : C} (f : X ⟶ Y), Epi f

lemma TotallyEpimorphic.cancel [TotallyEpimorphic C] {X Y Z : C} (f : X ⟶ Y) {g h : Y ⟶ Z}
    (e : f ≫ g = f ≫ h) : g = h :=
  haveI := TotallyEpimorphic.epi f
  (cancel_epi f).mp e

end Category

/-! ### Monoids on a category -/

variable (D : Type u) [Category.{v} D]

/-- **A group-like monoid on `D`** ([FrdI], Definition 1.1(ii), for groups): a contravariant
functor from `D` to abelian groups (written additively) with injective pull-backs, which are
bijective along FSM-morphisms. `pb f : obj B →+ obj A` is `f^*` for `f : A ⟶ B`. -/
structure GrpOn where
  /-- The groups `B(A)`. -/
  obj : D → Type w
  [inst : ∀ A, AddCommGroup (obj A)]
  /-- The pull-back `f^* : B(B) → B(A)` along `f : A ⟶ B`. -/
  pb : ∀ {A B : D}, (A ⟶ B) → obj B →+ obj A
  pb_id : ∀ (A : D) (x : obj A), pb (𝟙 A) x = x
  pb_comp : ∀ {A B E : D} (f : A ⟶ B) (g : B ⟶ E) (x : obj E), pb (f ≫ g) x = pb f (pb g x)
  /-- (a) Pull-backs are (characteristically) injective. -/
  pb_injective : ∀ {A B : D} (f : A ⟶ B), Function.Injective (pb f)
  /-- (b) Pull-backs along FSM-morphisms are isomorphisms. -/
  pb_bijective_of_fsm : ∀ {A B : D} (f : A ⟶ B), IsFSM f → Function.Bijective (pb f)

attribute [instance] GrpOn.inst

/-- **A divisorial monoid on `D`** ([FrdI], Definition 1.1(i), (ii)), encoded by the
groupifications `Φ^gp(A)` (the underlying `GrpOn`) and the cones `Φ(A) ⊆ Φ^gp(A)`. -/
structure DivMonoid extends GrpOn.{w} D where
  /-- The monoid `Φ(A)` as a submonoid of `Φ^gp(A)`. -/
  pos : ∀ A, AddSubmonoid (obj A)
  pb_mem : ∀ {A B : D} (f : A ⟶ B) {x : obj B}, x ∈ pos B → pb f x ∈ pos A
  /-- `Φ(A)` is sharp. -/
  sharp : ∀ {A : D} {x : obj A}, x ∈ pos A → -x ∈ pos A → x = 0
  /-- `Φ(A)` is saturated. -/
  saturated : ∀ {A : D} {x : obj A} (n : ℕ), 0 < n → n • x ∈ pos A → x ∈ pos A
  /-- `Φ^gp(A)` is the groupification of `Φ(A)`. -/
  generating : ∀ {A : D} (x : obj A), ∃ p ∈ pos A, ∃ q ∈ pos A, x = p - q
  /-- (b) along an FSM-morphism, `α^*` maps `Φ(B)` onto `Φ(A)`. -/
  pos_surj_of_fsm : ∀ {A B : D} (f : A ⟶ B), IsFSM f → ∀ y ∈ pos A, ∃ x ∈ pos B, pb f x = y

variable {D}

namespace GrpOn

variable (B : GrpOn.{w} D)

@[simp] lemma pb_id' (A : D) (x : B.obj A) : B.pb (𝟙 A) x = x := B.pb_id A x

@[simp] lemma pb_comp' {A A' E : D} (f : A ⟶ A') (g : A' ⟶ E) (x : B.obj E) :
    B.pb (f ≫ g) x = B.pb f (B.pb g x) := B.pb_comp f g x

@[simp] lemma pb_inv_pb {A A' : D} (f : A ⟶ A') [IsIso f] (x : B.obj A') :
    B.pb (inv f) (B.pb f x) = x := by
  rw [← pb_comp', IsIso.inv_hom_id, pb_id']

@[simp] lemma pb_pb_inv {A A' : D} (f : A ⟶ A') [IsIso f] (x : B.obj A) :
    B.pb f (B.pb (inv f) x) = x := by
  rw [← pb_comp', IsIso.hom_inv_id, pb_id']

end GrpOn

namespace DivMonoid

variable (Φ : DivMonoid.{w} D)

/-- The order `a ≤ b` iff `b = a + c` with `c ∈ Φ(A)` ([FrdI] §0, p. 12); the category
`Order(Φ(A))` is that of this partial order. -/
def le {A : D} (a b : Φ.obj A) : Prop := b - a ∈ Φ.pos A

/-- `a ≼ b` iff `a ≤ n·b` for some `n ≥ 1` ([FrdI] §0, p. 12). -/
def preceq {A : D} (a b : Φ.obj A) : Prop := ∃ n : ℕ, 0 < n ∧ Φ.le a (n • b)

/-- **Primary elements** ([FrdI] §0, p. 12): `0 ≠ a ∈ Φ(A)` such that every `0 ≠ b ∈ Φ(A)`
with `b ≼ a` satisfies `a ≼ b`. -/
def IsPrimary {A : D} (a : Φ.obj A) : Prop :=
  a ∈ Φ.pos A ∧ a ≠ 0 ∧ ∀ b ∈ Φ.pos A, b ≠ 0 → Φ.preceq b a → Φ.preceq a b

lemma le_refl {A : D} (a : Φ.obj A) : Φ.le a a := by simp [le, (Φ.pos A).zero_mem]

lemma le_antisymm {A : D} {a b : Φ.obj A} (h₁ : Φ.le a b) (h₂ : Φ.le b a) : a = b := by
  have := Φ.sharp h₁ (by rwa [neg_sub])
  exact (sub_eq_zero.mp this).symm

lemma zero_le {A : D} {a : Φ.obj A} (h : a ∈ Φ.pos A) : Φ.le 0 a := by simpa [le] using h

end DivMonoid

/-- **A homomorphism of monoids on `D`** `B → Φ^gp` (a natural transformation), e.g. the map
`Div_B : B → Φ^gp` of [FrdI], Theorem 5.2. -/
structure DivHom (B : GrpOn.{w} D) (Φ : GrpOn.{w} D) where
  app : ∀ A, B.obj A →+ Φ.obj A
  natural : ∀ {A A' : D} (f : A ⟶ A') (x : B.obj A'), app A (B.pb f x) = Φ.pb f (app A' x)

/-! ### The elementary Frobenioid -/

/-- **The elementary Frobenioid** `F_Φ` ([FrdI], Definition 1.1(iii)): its objects are the
objects of `D` (wrapped). -/
structure Elem (Φ : DivMonoid.{w} D) where
  /-- The underlying object of `D`. -/
  base : D

namespace Elem

variable {Φ : DivMonoid.{w} D}

/-- A morphism `(φ_D, Z_φ, n_φ)` of `F_Φ`: a morphism of `D`, the zero divisor
`Z_φ ∈ Φ(A_D)` and the Frobenius degree `n_φ ∈ ℕ_{≥1}`. -/
@[ext]
structure Hom (A B : Elem Φ) where
  base : A.base ⟶ B.base
  div : Φ.obj A.base
  div_mem : div ∈ Φ.pos A.base
  deg : ℕ+

/-- The identity `(id, 0, 1)`. -/
def Hom.id (A : Elem Φ) : Hom A A := ⟨𝟙 _, 0, (Φ.pos _).zero_mem, 1⟩

/-- **The composition law** `ψ ∘ φ = (ψ_D ∘ φ_D, φ_D^*(Z_ψ) + n_ψ·Z_φ, n_ψ·n_φ)`
([FrdI], Definition 1.1(iii); Remark 1.1.1). -/
def Hom.comp {A B E : Elem Φ} (φ : Hom A B) (ψ : Hom B E) : Hom A E where
  base := φ.base ≫ ψ.base
  div := Φ.pb φ.base ψ.div + (ψ.deg : ℕ) • φ.div
  div_mem := (Φ.pos _).add_mem (Φ.pb_mem _ ψ.div_mem) ((Φ.pos _).nsmul_mem φ.div_mem _)
  deg := ψ.deg * φ.deg

instance : Category (Elem Φ) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp φ := by
    refine Hom.ext (Category.id_comp _) ?_ (mul_one _)
    simp [Hom.comp, Hom.id]
  comp_id φ := by
    refine Hom.ext (Category.comp_id _) ?_ (one_mul _)
    simp [Hom.comp, Hom.id]
  assoc φ ψ χ := by
    refine Hom.ext (Category.assoc _ _ _) ?_ (mul_assoc _ _ _).symm
    simp only [Hom.comp, GrpOn.pb_comp', map_add, map_nsmul, smul_add, PNat.mul_coe, mul_smul]
    abel

@[ext] lemma hom_ext {A B : Elem Φ} {φ ψ : A ⟶ B} (h₁ : φ.base = ψ.base) (h₂ : φ.div = ψ.div)
    (h₃ : φ.deg = ψ.deg) : φ = ψ := Hom.ext h₁ h₂ h₃

@[simp] lemma id_base (A : Elem Φ) : (𝟙 A : A ⟶ A).base = 𝟙 A.base := rfl
@[simp] lemma id_div (A : Elem Φ) : (𝟙 A : A ⟶ A).div = 0 := rfl
@[simp] lemma id_deg (A : Elem Φ) : (𝟙 A : A ⟶ A).deg = 1 := rfl
@[simp] lemma comp_base {A B E : Elem Φ} (φ : A ⟶ B) (ψ : B ⟶ E) :
    (φ ≫ ψ).base = φ.base ≫ ψ.base := rfl
@[simp] lemma comp_div {A B E : Elem Φ} (φ : A ⟶ B) (ψ : B ⟶ E) :
    (φ ≫ ψ).div = Φ.pb φ.base ψ.div + (ψ.deg : ℕ) • φ.div := rfl
@[simp] lemma comp_deg {A B E : Elem Φ} (φ : A ⟶ B) (ψ : B ⟶ E) :
    (φ ≫ ψ).deg = ψ.deg * φ.deg := rfl

/-- **The projection functor** `F_Φ → D` ([FrdI], Definition 1.1(iii)). -/
@[simps]
def proj : Elem Φ ⥤ D where
  obj A := A.base
  map φ := φ.base

end Elem

end Frobenioid

end Iut
