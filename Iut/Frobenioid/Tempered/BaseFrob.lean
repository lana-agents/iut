/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.FracPair

/-!
# Base-Frobenius pairs of objects of a model Frobenioid

[FrdI], Definition 2.7, Proposition 5.6, Corollary 5.7.

[FrdI], Definition 2.7: a **base-Frobenius pair** `(P, F)` of a Frobenioid `C` is a base-section
`P` (a skeletal subcategory of pull-back morphisms between Frobenius-trivial objects, equivalent
to `D` via the projection) together with a `P`-Frobenius-section `F : ℕ_{≥1} → End(P ↪ C)` (a
homomorphism of monoids, splitting the Frobenius degree, with values base-identity endomorphisms
of Frobenius type; elements of `End(P ↪ C)` are natural transformations, so they commute with
the morphisms of `P`). Restricting `(P, F)` to a Frobenius-trivial object `A ∈ P` gives
([FrdI], Proposition 5.6) a pair

  `(σ : Aut_D(A_D) ↪ Aut_C(A), φ : ℕ_{≥1} → End_C(A))`,

`σ` a section of `Aut_C(A) ↠ Aut_D(A_D)` ([FrdI], Theorem 5.1(iii):
`Aut_C(A)/O^×(A) ≅ Aut_D(A_D)`), `φ` a monoid homomorphism, the values of `σ` commuting with
those of `φ`; Proposition 5.6 states that this pair depends on `(C, A)` only, up to conjugation by an element of `O^×(A)`. [EtTh],
Proposition 4.3(i), uses the resulting homomorphism `str^trv_N : H_{A_N} → Aut_C(A_N)` on a
subgroup `H_{A_N} ⊆ Aut_C(A_N)/O^×(A_N)` (and Lemma 5.9 its images).

Here, for a model Frobenioid `C = Model Φ B divB`:

* `Model.unitsAut X`: `O^×(X)` as a normal subgroup of `Aut_C(X)`;
* `Model.IsBaseFrobPair X σ φ`: `σ : Aut_C(X)/O^×(X) →* Aut_C(X)` is a section of the quotient map
  (the form used in [EtTh], Proposition 4.3), `φ : ℕ_{≥1} → End_C(X)` is multiplicative with
  `φ(n)` a base-identity endomorphism of Frobenius type of degree `n`, and `σ(q) ∘ φ(n) =
  φ(n) ∘ σ(q)`;
* `Model.isBaseFrobPair_triv` (existence, [FrdI], Remark 2.7.1 / Remark 5.6.1, "tautological
  section of a trivial line bundle"): the zero section of the trivial line bundle `(A_D, 0)`;
* `Model.baseFrobPair_unique` (**[FrdI], Proposition 5.6**): any two base-Frobenius pairs of `X`
  are conjugate by a unit `u ∈ O^×(X)`. In a model Frobenioid the proof needs no profiniteness of
  `O^×(X)`: writing `φ(n) = (n, id, 0, u_n)`, commutativity of `ℕ_{≥1}` gives
  `u_n = (n − 1)·u_2`, so `u = u'_2 − u_2` conjugates `φ` into `φ'`; the commutation with `φ(2)`
  then determines `σ` (as in the last step of the proof of Proposition 5.6, with `p = 2`);
* `Model.isBaseFrobPair_map` (**[FrdI], Corollary 5.7(iii),(iv)** for objects): a fully faithful
  functor which matches `O^×`, preserves base-identity morphisms of Frobenius type, and changes
  Frobenius degrees by an automorphism `ρ` of `ℕ_{≥1}`, maps base-Frobenius pairs of `X` to
  base-Frobenius pairs of `F(X)` (reindexing `φ` by `ρ^{-1}`, the "quasi-" of Corollary 5.7).
  `Model.isBaseFrobPair_map_fsm` supplies these hypotheses for equivalences over bases of
  FSM-type by [FrdI], Theorem 3.4 (`Iut/Frobenioid/Tempered/Thm34Temp.lean`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u w₁ w₂ v₁ v₂ u₁ u₂

namespace Model

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-! ### `O^×(X) ⊆ Aut_C(X)` -/

lemma deg_of_iso {X Y : Model Φ B divB} (a : X ≅ Y) : a.hom.deg = 1 :=
  ((isIso_iff a.hom).1 inferInstance).1

lemma div_of_iso {X Y : Model Φ B divB} (a : X ≅ Y) : a.hom.div = 0 :=
  ((isIso_iff a.hom).1 inferInstance).2.2

lemma inv_base_of_iso {X Y : Model Φ B divB} (a : X ≅ Y) : a.inv.base ≫ a.hom.base = 𝟙 _ := by
  rw [← comp_base, a.inv_hom_id, id_base]

lemma hom_base_inv_of_iso {X Y : Model Φ B divB} (a : X ≅ Y) : a.hom.base ≫ a.inv.base = 𝟙 _ := by
  rw [← comp_base, a.hom_inv_id, id_base]

/-- **`O^×(X)` as a subgroup of `Aut_C(X)`**: the base-identity (linear) automorphisms. -/
def unitsAut (X : Model Φ B divB) : Subgroup (Aut X) where
  carrier := {a | a.hom.base = 𝟙 _}
  mul_mem' {a b} ha hb := by
    change (b ≪≫ a).hom.base = _
    simp only [Iso.trans_hom, comp_base]
    rw [show a.hom.base = 𝟙 _ from ha, show b.hom.base = 𝟙 _ from hb, Category.comp_id]
  one_mem' := rfl
  inv_mem' {a} ha := by
    change a.inv.base = _
    have := hom_base_inv_of_iso a
    rwa [show a.hom.base = 𝟙 _ from ha, Category.id_comp] at this

lemma mem_unitsAut {X : Model Φ B divB} {a : Aut X} : a ∈ unitsAut X ↔ a.hom.base = 𝟙 _ :=
  Iff.rfl

lemma mem_unitsAut_iff_ounits {X : Model Φ B divB} {a : Aut X} :
    a ∈ unitsAut X ↔ a.hom ∈ Ounits 𝐏 X :=
  ⟨fun h => ⟨inferInstance, h, deg_of_iso a⟩, fun h => h.2.1⟩

instance (X : Model Φ B divB) : (unitsAut X).Normal :=
  ⟨fun a ha g => by
    rw [mem_unitsAut]
    change (g.symm ≪≫ a ≪≫ g).hom.base = _
    simp only [Iso.trans_hom, comp_base, show a.hom.base = 𝟙 _ from ha, Category.id_comp]
    exact inv_base_of_iso g⟩

/-- Two automorphisms with the same image in `Aut_C(X)/O^×(X)` have the same base. -/
lemma base_eq_of_mk_eq {X : Model Φ B divB} {a b : Aut X}
    (h : (QuotientGroup.mk a : Aut X ⧸ unitsAut X) = QuotientGroup.mk b) :
    a.hom.base = b.hom.base := by
  have hm : (a⁻¹ * b : Aut X) ∈ unitsAut X := QuotientGroup.eq.1 h
  rw [mem_unitsAut] at hm
  change (b ≪≫ a.symm).hom.base = _ at hm
  simp only [Iso.trans_hom, Iso.symm_hom, comp_base] at hm
  have := congrArg (· ≫ a.hom.base) hm
  simp only [Category.assoc, inv_base_of_iso, Category.comp_id, Category.id_comp] at this
  exact this.symm

/-! ### Base-Frobenius pairs of an object -/

/-- **A base-Frobenius pair of `X`** ([FrdI], Definition 2.7, Proposition 5.6): a section
`σ` of `Aut_C(X) ↠ Aut_C(X)/O^×(X)` and a monoid homomorphism `φ : ℕ_{≥1} → End_C(X)` splitting
the Frobenius degree, with values base-identity endomorphisms of Frobenius type, commuting with
the values of `σ`. -/
def IsBaseFrobPair (X : Model Φ B divB) (σ : Aut X ⧸ unitsAut X →* Aut X)
    (φ : ℕ+ → (X ⟶ X)) : Prop :=
  (∀ q, (QuotientGroup.mk (σ q) : Aut X ⧸ unitsAut X) = q) ∧ φ 1 = 𝟙 X ∧
    (∀ m n, φ (m * n) = φ m ≫ φ n) ∧
    (∀ n, (φ n).deg = n ∧ IsBaseIdentity 𝐏 (φ n) ∧ IsFrobeniusType 𝐏 (φ n)) ∧
    ∀ q n, (σ q).hom ≫ φ n = φ n ≫ (σ q).hom

/-- A base-Frobenius pair makes `X` Frobenius-trivial. -/
lemma IsBaseFrobPair.isFrobeniusTrivial {X : Model Φ B divB} {σ : Aut X ⧸ unitsAut X →* Aut X}
    {φ : ℕ+ → (X ⟶ X)} (h : IsBaseFrobPair X σ φ) : IsFrobeniusTrivial 𝐏 X :=
  ⟨φ, h.2.1, h.2.2.1, fun n => h.2.2.2.1 n⟩

/-! #### Existence: the zero section of the trivial line bundle -/

/-- The trivial line bundle `(A_D, 0)` over `A_D`. -/
abbrev trivObj (A : D) : Model Φ B divB := ⟨A, 0⟩

/-- The tautological lift `(1, f, 0, 0)` of an automorphism of `A_D` to the trivial line bundle. -/
def zeroLiftHom {A : D} (f : A ⟶ A) : trivObj (Φ := Φ) (B := B) (divB := divB) A ⟶ trivObj A :=
  mk1 f 0 (Φ.pos _).zero_mem 0 (by
    change (0 : Φ.obj A) + 0 = Φ.pb f 0 + divB.app A 0
    rw [map_zero, map_zero])

lemma zeroLiftHom_comp {A : D} (f g : A ⟶ A) :
    zeroLiftHom (Φ := Φ) (B := B) (divB := divB) f ≫ zeroLiftHom g = zeroLiftHom (f ≫ g) := by
  ext <;> first | rfl | simp [zeroLiftHom]

lemma zeroLiftHom_id (A : D) : zeroLiftHom (Φ := Φ) (B := B) (divB := divB) (𝟙 A) = 𝟙 _ := by
  ext <;> rfl

/-- The tautological lift as an automorphism. -/
def zeroLift {A : D} (f : A ≅ A) : Aut (trivObj (Φ := Φ) (B := B) (divB := divB) A) where
  hom := zeroLiftHom f.hom
  inv := zeroLiftHom f.inv
  hom_inv_id := by rw [zeroLiftHom_comp, f.hom_inv_id, zeroLiftHom_id]
  inv_hom_id := by rw [zeroLiftHom_comp, f.inv_hom_id, zeroLiftHom_id]

/-- The tautological lifts form a homomorphism `Aut_C(X) → Aut_C(X)`, `a ↦ zeroLift(Base a)`. -/
def zeroLiftAut (A : D) :
    Aut (trivObj (Φ := Φ) (B := B) (divB := divB) A) →*
      Aut (trivObj (Φ := Φ) (B := B) (divB := divB) A) where
  toFun a := zeroLift ((toElem Φ B divB ⋙ Elem.proj).mapIso a)
  map_one' := by
    ext1
    exact zeroLiftHom_id A
  map_mul' a b := by
    ext1
    change zeroLiftHom (b.hom ≫ a.hom).base = zeroLiftHom b.hom.base ≫ zeroLiftHom a.hom.base
    rw [zeroLiftHom_comp, comp_base]

/-- **The tautological section** `σ₀ : Aut_C(X)/O^×(X) → Aut_C(X)` of the trivial line bundle. -/
def trivSection (A : D) :
    Aut (trivObj (Φ := Φ) (B := B) (divB := divB) A) ⧸ unitsAut (trivObj A) →*
      Aut (trivObj (Φ := Φ) (B := B) (divB := divB) A) :=
  QuotientGroup.lift _ (zeroLiftAut A) fun a ha => by
    ext1
    change zeroLiftHom a.hom.base = 𝟙 _
    rw [show a.hom.base = 𝟙 _ from ha, zeroLiftHom_id]

/-- **The tautological Frobenius-section** `n ↦ (n, id, 0, 0)` of the trivial line bundle. -/
def trivFrob (A : D) (n : ℕ+) :
    trivObj (Φ := Φ) (B := B) (divB := divB) A ⟶ trivObj A :=
  mk' n (𝟙 A) 0 (Φ.pos _).zero_mem 0 (by
    change (n : ℕ) • (0 : Φ.obj A) + 0 = Φ.pb (𝟙 A) 0 + divB.app A 0
    rw [map_zero, map_zero, smul_zero])

/-- **Existence of base-Frobenius pairs** ([FrdI], Remarks 2.7.1, 5.6.1: the tautological
section of a trivial line bundle). -/
theorem isBaseFrobPair_triv (A : D) :
    IsBaseFrobPair (trivObj (Φ := Φ) (B := B) (divB := divB) A) (trivSection A) (trivFrob A) := by
  refine ⟨fun q => ?_, ?_, fun m n => ?_, fun n => ⟨rfl, rfl, ?_⟩, fun q n => ?_⟩
  · induction q using QuotientGroup.induction_on with
    | H a =>
      apply QuotientGroup.eq.2
      rw [mem_unitsAut]
      change (a ≪≫ (zeroLift ((toElem Φ B divB ⋙ Elem.proj).mapIso a)).symm).hom.base = _
      simp only [Iso.trans_hom, Iso.symm_hom, comp_base]
      change a.hom.base ≫ a.inv.base = _
      exact hom_base_inv_of_iso a
  · ext <;> simp [trivFrob]
  · ext <;> simp [trivFrob, mul_comm]
  · exact (isFrobeniusType_iff _).2 ⟨rfl, by simp only [trivFrob, mk'_base]; infer_instance⟩
  · induction q using QuotientGroup.induction_on with
    | H a =>
      change zeroLiftHom a.hom.base ≫ trivFrob A n = trivFrob A n ≫ zeroLiftHom a.hom.base
      ext <;> simp [zeroLiftHom, trivFrob]

/-! #### Uniqueness up to `O^×(X)` ([FrdI], Proposition 5.6) -/

section Unique

variable {X : Model Φ B divB} {σ : Aut X ⧸ unitsAut X →* Aut X} {φ : ℕ+ → (X ⟶ X)}

lemma IsBaseFrobPair.deg (h : IsBaseFrobPair X σ φ) (n : ℕ+) : (φ n).deg = n := (h.2.2.2.1 n).1

lemma IsBaseFrobPair.base (h : IsBaseFrobPair X σ φ) (n : ℕ+) : (φ n).base = 𝟙 _ :=
  (h.2.2.2.1 n).2.1

lemma IsBaseFrobPair.div (h : IsBaseFrobPair X σ φ) (n : ℕ+) : (φ n).div = 0 :=
  ((isFrobeniusType_iff _).1 (h.2.2.2.1 n).2.2).1

/-- `u_n = n·u_2 − u_2` (commutativity of `ℕ_{≥1}`: `φ(2)φ(n) = φ(n)φ(2)`). -/
lemma IsBaseFrobPair.u_eq (h : IsBaseFrobPair X σ φ) (n : ℕ+) :
    (φ n).u = (n : ℕ) • (φ 2).u - (φ 2).u := by
  have e : φ 2 ≫ φ n = φ n ≫ φ 2 := by rw [← h.2.2.1, ← h.2.2.1, mul_comm]
  have e' := congrArg Hom.u e
  simp only [comp_u, h.base, GrpOn.pb_id', h.deg] at e'
  rw [eq_sub_iff_add_eq]
  have : ((2 : ℕ+) : ℕ) = 2 := rfl
  rw [this, two_nsmul] at e'
  have e2 : (φ n).u + (n : ℕ) • (φ 2).u = (φ n).u + ((φ 2).u + (φ n).u) := by rw [e']; abel
  rw [add_left_cancel e2]
  abel

/-- `Div_B(u_2) = α_X`. -/
lemma IsBaseFrobPair.divB_u_two (h : IsBaseFrobPair X σ φ) : divB.app _ (φ 2).u = X.α := by
  have r := (φ 2).rel
  rw [h.deg, h.div, h.base, GrpOn.pb_id', add_zero] at r
  have : ((2 : ℕ+) : ℕ) = 2 := rfl
  rw [this, two_nsmul] at r
  exact (add_left_cancel r).symm

/-- `u_σ(q) = u_2 − f^* u_2` for `f = Base σ(q)` (commutation with `φ(2)`). -/
lemma IsBaseFrobPair.u_sigma (h : IsBaseFrobPair X σ φ) (q : Aut X ⧸ unitsAut X) :
    (σ q).hom.u = (φ 2).u - B.pb (σ q).hom.base (φ 2).u := by
  have e' := congrArg Hom.u (h.2.2.2.2 q 2)
  simp only [comp_u, h.base, GrpOn.pb_id', h.deg, deg_of_iso] at e'
  have : ((2 : ℕ+) : ℕ) = 2 := rfl
  rw [this, two_nsmul, PNat.one_coe, one_smul] at e'
  rw [eq_sub_iff_add_eq]
  linear_combination (norm := abel) e'

/-- The unit `(1, id, 0, d)` with `Div_B(d) = 0`. -/
def unitHom (X : Model Φ B divB) (d : B.obj X.base) (hd : divB.app _ d = 0) : X ⟶ X :=
  mk1 (𝟙 _) 0 (Φ.pos _).zero_mem d (by simp [hd])

lemma unitHom_comp (X : Model Φ B divB) (d e : B.obj X.base) (hd : divB.app _ d = 0)
    (he : divB.app _ e = 0) : unitHom X d hd ≫ unitHom X e he =
      unitHom X (d + e) (by rw [map_add, hd, he, add_zero]) := by
  ext <;> simp [unitHom, add_comm]

/-- The unit `(1, id, 0, d)` as an automorphism. -/
def unitIso (X : Model Φ B divB) (d : B.obj X.base) (hd : divB.app _ d = 0) : X ≅ X where
  hom := unitHom X d hd
  inv := unitHom X (-d) (by rw [map_neg, hd, neg_zero])
  hom_inv_id := by rw [unitHom_comp]; ext <;> simp [unitHom]
  inv_hom_id := by rw [unitHom_comp]; ext <;> simp [unitHom]

/-- **[FrdI], Proposition 5.6** (model Frobenioids): two base-Frobenius pairs of `X` are conjugate
by a unit `u ∈ O^×(X)`: `σ'(q) = u⁻¹ σ(q) u` and `φ'(n) = u ∘ φ(n) ∘ u⁻¹` (composition in
diagrammatic order: `u.hom ≫ φ(n) ≫ u.inv`). -/
theorem baseFrobPair_unique {σ' : Aut X ⧸ unitsAut X →* Aut X} {φ' : ℕ+ → (X ⟶ X)}
    (h : IsBaseFrobPair X σ φ) (h' : IsBaseFrobPair X σ' φ') :
    ∃ u ∈ unitsAut X, (∀ q, σ' q = u⁻¹ * σ q * u) ∧ ∀ n, φ' n = u.hom ≫ φ n ≫ u.inv := by
  set d := (φ' 2).u - (φ 2).u with hd
  have hd0 : divB.app _ d = 0 := by rw [hd, map_sub, h.divB_u_two, h'.divB_u_two, sub_self]
  refine ⟨unitIso X d hd0, rfl, fun q => ?_, fun n => ?_⟩
  · -- the bases agree, and `u` is determined by commutation with `φ(2)`
    have hb : (σ' q).hom.base = (σ q).hom.base :=
      base_eq_of_mk_eq ((h'.1 q).trans (h.1 q).symm)
    ext1
    change (σ' q).hom = unitHom X d hd0 ≫ (σ q).hom ≫
      unitHom X (-d) (by rw [map_neg, hd0, neg_zero])
    ext
    · simp [unitHom, deg_of_iso]
    · simp [unitHom, hb]
    · simp [unitHom, div_of_iso, deg_of_iso]
    · simp only [comp_u, unitHom, mk1_u, mk1_base, GrpOn.pb_id', mk1_deg,
        PNat.one_coe, one_smul]
      have e : (φ' 2).u = (φ 2).u + d := by rw [hd]; abel
      rw [h'.u_sigma, h.u_sigma, hb, e, comp_deg, mk1_deg, deg_of_iso, map_neg, map_add]
      simp only [mul_one, PNat.one_coe, one_smul]
      abel
  · ext
    · simp [unitIso, unitHom, h.deg, h'.deg]
    · simp [unitIso, unitHom, h.base, h'.base]
    · simp [unitIso, unitHom, h.div, h'.div, h.base]
    · simp only [unitIso, comp_u, unitHom, mk1_u, mk1_base, GrpOn.pb_id', mk1_deg, comp_deg,
        h.deg, h.base, PNat.one_coe, one_smul, one_mul]
      rw [h'.u_eq, h.u_eq, hd, smul_sub]
      abel

end Unique

/-! #### Category-theoreticity ([FrdI], Corollary 5.7) -/

section Map

variable {D₁ : Type u₁} [Category.{v₁} D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) (hF : F.FullyFaithful)

/-- `Aut_C(X) ≅ Aut_C(F X)` for a fully faithful `F`. -/
noncomputable abbrev autEquivFF (X : Model Φ₁ B₁ divB₁) : Aut X ≃* Aut (F.obj X) :=
  hF.autMulEquivOfFullyFaithful X

variable {F}

/-- The induced isomorphism `Aut_C(X)/O^×(X) ≅ Aut_C(F X)/O^×(F X)` when `F` matches the units. -/
noncomputable def quotAutEquiv {X : Model Φ₁ B₁ divB₁}
    (hU : ∀ a : Aut X, a ∈ unitsAut X ↔ autEquivFF F hF X a ∈ unitsAut (F.obj X)) :
    Aut X ⧸ unitsAut X ≃* Aut (F.obj X) ⧸ unitsAut (F.obj X) :=
  QuotientGroup.congr _ _ (autEquivFF F hF X) (by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hU a).1 ha
    · intro hb
      refine ⟨(autEquivFF F hF X).symm b, (hU _).2 (by simpa using hb), by simp⟩)

/-- **[FrdI], Corollary 5.7(iii),(iv)** (for objects of model Frobenioids): a fully faithful functor
which matches `O^×`, maps base-identity endomorphisms of Frobenius type to such, and changes
Frobenius degrees by an automorphism `ρ` of `ℕ_{≥1}` maps a base-Frobenius pair `(σ, φ)` of `X` to
the base-Frobenius pair `(F ∘ σ ∘ (F_*)^{-1}, F ∘ φ ∘ ρ^{-1})` of `F(X)`. -/
theorem isBaseFrobPair_map {X : Model Φ₁ B₁ divB₁} {σ : Aut X ⧸ unitsAut X →* Aut X}
    {φ : ℕ+ → (X ⟶ X)} (h : IsBaseFrobPair X σ φ)
    (hU : ∀ a : Aut X, a ∈ unitsAut X ↔ autEquivFF F hF X a ∈ unitsAut (F.obj X))
    (hfr : ∀ e : X ⟶ X, IsBaseIdentity 𝐏₁ e → IsFrobeniusType 𝐏₁ e →
      IsBaseIdentity 𝐏₂ (F.map e) ∧ IsFrobeniusType 𝐏₂ (F.map e))
    (ρ : ℕ+ ≃* ℕ+) (hρ : ∀ e : X ⟶ X, (F.map e).deg = ρ e.deg) :
    IsBaseFrobPair (F.obj X)
      (((autEquivFF F hF X).toMonoidHom.comp σ).comp (quotAutEquiv hF hU).symm.toMonoidHom)
      (fun n => F.map (φ (ρ.symm n))) := by
  obtain ⟨hsec, h1, hmul, hφ, hcomm⟩ := h
  refine ⟨fun q => ?_, ?_, fun m n => ?_, fun n => ⟨?_, hfr _ (hφ _).2.1 (hφ _).2.2⟩,
    fun q n => ?_⟩
  · obtain ⟨p, rfl⟩ := (quotAutEquiv hF hU).surjective q
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.symm_apply_apply]
    have key : ∀ a : Aut X, quotAutEquiv hF hU (QuotientGroup.mk a) =
        QuotientGroup.mk (autEquivFF F hF X a) := fun a => rfl
    rw [← key, hsec]
  · change F.map (φ (ρ.symm 1)) = 𝟙 _
    rw [map_one, h1, F.map_id]
  · change F.map (φ (ρ.symm (m * n))) = F.map (φ (ρ.symm m)) ≫ F.map (φ (ρ.symm n))
    rw [map_mul, hmul, F.map_comp]
  · rw [hρ, (hφ _).1, MulEquiv.apply_symm_apply]
  · simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    change F.map (σ _).hom ≫ F.map (φ _) = F.map (φ _) ≫ F.map (σ _).hom
    rw [← F.map_comp, ← F.map_comp, hcomm]

section MapFSM

variable [TotallyEpimorphic D₁] [TotallyEpimorphic D₂] [IsConnected D₁] [IsConnected D₂]

/-- **[FrdI], Corollary 5.7(iii),(iv) over bases of FSM-type** (e.g. tempered bases
`B^temp(Π)⁰`, both slim): every equivalence `F` of model Frobenioids maps a base-Frobenius pair
of `X` to a base-Frobenius pair of `F(X)`, with `φ` reindexed by the automorphism `ρ` of
`ℕ_{≥1}` of [FrdI], Theorem 3.4(iii). -/
theorem isBaseFrobPair_map_fsm (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁)
    (hΦ₁ : Φ₁.NonDilating) (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂)
    (hB₂ : HasAllTorsion B₂) (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (hS₁ : IsSlim D₁) (hS₂ : IsSlim D₂) (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂)
    [F.IsEquivalence] {X : Model Φ₁ B₁ divB₁} {σ : Aut X ⧸ unitsAut X →* Aut X}
    {φ : ℕ+ → (X ⟶ X)} (h : IsBaseFrobPair X σ φ) :
    ∃ (hU : ∀ a : Aut X, a ∈ unitsAut X ↔
        autEquivFF F (Functor.FullyFaithful.ofFullyFaithful F) X a ∈ unitsAut (F.obj X))
      (ρ : ℕ+ ≃* ℕ+),
      IsBaseFrobPair (F.obj X)
        (((autEquivFF F (Functor.FullyFaithful.ofFullyFaithful F) X).toMonoidHom.comp σ).comp
          (quotAutEquiv (Functor.FullyFaithful.ofFullyFaithful F) hU).symm.toMonoidHom)
        (fun n => F.map (φ (ρ.symm n))) := by
  have c := typeCorresp_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F
  obtain ⟨-, -, -, -, -, -, -, ρ, hρ⟩ :=
    thm34_fsm_preservesFrobeniusStructure hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F
  have hU : ∀ a : Aut X, a ∈ unitsAut X ↔
      autEquivFF F (Functor.FullyFaithful.ofFullyFaithful F) X a ∈ unitsAut (F.obj X) := by
    intro a
    rw [mem_unitsAut_iff_ounits, mem_unitsAut_iff_ounits]
    exact mem_ounits_iff_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ hS₁ hS₂ F a.hom
  refine ⟨hU, ρ, isBaseFrobPair_map _ h hU (fun e he hfe => ⟨?_, (c.frobType e).1 hfe⟩) ρ
    (fun e => hρ e)⟩
  exact base_map_eq_id F c.pullback c.baseIso hS₂ e he

end MapFSM

end Map

end Model

end Frobenioid

end Iut
