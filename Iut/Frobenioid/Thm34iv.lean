/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm34Base

/-!
# [FrdI], Theorem 3.4(iv) for model Frobenioids: `O^▷`, `O^×` and the Frobenius degree

In the situation of `Iut/Frobenioid/Thm34Base.lean` (model Frobenioids over base categories of
FSM- and Aut-type, rational functions with torsion of every order, slim base `D₂`):

* `Model.map_mem_orhd`, `Model.map_mem_ounits`: an equivalence `F` maps `O^▷(A)` into
  `O^▷(F A)` and `O^×(A)` into `O^×(F A)` ([FrdI], Theorem 3.4(iv): "Ψ preserves the submonoids
  `O^▷(−)`, `O^×(−)`"); with both bases slim, `F` restricts to bijections (`mem_orhd_iff`,
  `mem_ounits_iff`).
* `Model.degFr_map_eq`: **`F` preserves Frobenius degrees** (`Ψ_{ℕ≥1}` is the identity, [FrdI],
  Theorem 3.4(iii)/(iv)) as soon as some `O^×(A)` of `C₁` contains a unit of infinite order
  (`HasNonTorsionUnit`; e.g. `1 + p ∈ 𝒪_K^×` for the `p`-adic Frobenioids of IUT).

*Proof of the last point.* Let `u ∈ O^×(A, 0)` have infinite order and let `φ` be the
base-identity endomorphism `(d, id, 0, 0)` of `(A, 0)`. In a model Frobenioid,
`u ≫ φ = φ ≫ u^d` (the "Frobenius-normalized" relation). Applying `F`, `F u` and `F φ` are
base-identity endomorphisms (by slimness), so the same relation in `C₂` reads
`F u ≫ F φ = F φ ≫ (F u)^{σ(d)}`, where `σ(d) = deg F φ`. Cancelling the epimorphism `F φ`
gives `(F u)^d = (F u)^{σ(d)}`, hence `u^d = u^{σ(d)}` and `d = σ(d)`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w₁ w₂ v₁ v₂ u₁ u₂

/-- Some unit `u ∈ B(A)` with `Div_B(u) = 0` (an element of `O^×(A, 0)`) has infinite order. -/
def HasNonTorsionUnit {D : Type u₁} [Category.{v₁} D] {Φ : DivMonoid.{w₁} D}
    {B : GrpOn.{w₁} D} (divB : DivHom B Φ.toGrpOn) : Prop :=
  ∃ (A : D) (u : B.obj A), divB.app A u = 0 ∧ ∀ n : ℕ, 0 < n → n • u ≠ 0

namespace Model

variable {D₁ : Type u₁} [Category.{v₁} D₁] [IsConnected D₁] [TotallyEpimorphic D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂] [IsConnected D₂] [TotallyEpimorphic D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence]
variable (hD₁ : BaseHyp D₁) (hB₁ : HasAllTorsion B₁) (hD₂ : BaseHyp D₂)
  (hB₂ : HasAllTorsion B₂)

omit [IsConnected D₁] [IsConnected D₂] in
include hD₁ hB₁ hD₂ hB₂ in
/-- **`F` maps `O^▷(A)` into `O^▷(F A)`** ([FrdI], Theorem 3.4(iv)). -/
theorem map_mem_orhd (hD : IsSlim D₂) {X : Model Φ₁ B₁ divB₁} {e : X ⟶ X}
    (he : e ∈ Orhd 𝐏₁ X) : F.map e ∈ Orhd 𝐏₂ (F.obj X) := by
  have c := typeCorresp hD₁ hB₁ hD₂ hB₂ F
  exact ⟨base_map_eq_id F c.pullback c.baseIso hD e he.1, (c.linear e).1 he.2⟩

omit [IsConnected D₁] [IsConnected D₂] in
include hD₁ hB₁ hD₂ hB₂ in
/-- **`F` maps `O^×(A)` into `O^×(F A)`** ([FrdI], Theorem 3.4(iv)). -/
theorem map_mem_ounits (hD : IsSlim D₂) {X : Model Φ₁ B₁ divB₁} {e : X ⟶ X}
    (he : e ∈ Ounits 𝐏₁ X) : F.map e ∈ Ounits 𝐏₂ (F.obj X) := by
  obtain ⟨hi, hb, hl⟩ := he
  haveI := hi
  exact ⟨inferInstance, (map_mem_orhd F hD₁ hB₁ hD₂ hB₂ hD ⟨hb, hl⟩).1,
    (map_mem_orhd F hD₁ hB₁ hD₂ hB₂ hD ⟨hb, hl⟩).2⟩

omit [IsConnected D₁] [IsConnected D₂] in
include hD₁ hB₁ hD₂ hB₂ in
/-- With both bases slim, **`F` restricts to `O^▷(A) ≅ O^▷(F A)`**. -/
theorem mem_orhd_iff (hS₁ : IsSlim D₁) (hS₂ : IsSlim D₂) {X : Model Φ₁ B₁ divB₁}
    (e : X ⟶ X) : e ∈ Orhd 𝐏₁ X ↔ F.map e ∈ Orhd 𝐏₂ (F.obj X) := by
  refine ⟨map_mem_orhd F hD₁ hB₁ hD₂ hB₂ hS₂, fun h => ?_⟩
  have h' := map_mem_orhd F.inv hD₂ hB₂ hD₁ hB₁ hS₁ h
  have hn := (F.asEquivalence.unitIso.hom.naturality e)
  simp only [Functor.id_map, Functor.comp_map] at hn
  have hb := congrArg Hom.base hn
  simp only [comp_base] at hb
  have h1 : (F.inv.map (F.map e)).base = 𝟙 _ := h'.1
  change _ = _ ≫ (F.inv.map (F.map e)).base at hb
  rw [h1, Category.comp_id] at hb
  haveI : IsIso (F.asEquivalence.unitIso.hom.app X).base :=
    isIso_base_of_isIso (F.asEquivalence.unitIso.hom.app X)
  refine ⟨(cancel_mono (F.asEquivalence.unitIso.hom.app X).base).mp
    (hb.trans (Category.id_comp _).symm), ?_⟩
  have hl := (typeCorresp hD₁ hB₁ hD₂ hB₂ F).linear e
  exact hl.2 h.2

omit [IsConnected D₁] [IsConnected D₂] in
include hD₁ hB₁ hD₂ hB₂ in
/-- With both bases slim, **`F` restricts to `O^×(A) ≅ O^×(F A)`**. -/
theorem mem_ounits_iff (hS₁ : IsSlim D₁) (hS₂ : IsSlim D₂) {X : Model Φ₁ B₁ divB₁}
    (e : X ⟶ X) : e ∈ Ounits 𝐏₁ X ↔ F.map e ∈ Ounits 𝐏₂ (F.obj X) := by
  refine ⟨map_mem_ounits F hD₁ hB₁ hD₂ hB₂ hS₂, fun ⟨hi, hb, hl⟩ => ?_⟩
  have := (mem_orhd_iff F hD₁ hB₁ hD₂ hB₂ hS₁ hS₂ e).2 ⟨hb, hl⟩
  exact ⟨(corresp_isIso F e).2 hi, this.1, this.2⟩

/-! ### The Frobenius degree is preserved -/

section Degree

variable {A : D₁} (u : B₁.obj A) (hu : divB₁.app A u = 0)

/-- The unit `(1, id, 0, k·u)` of `(A, 0)`. -/
def unitPow (k : ℕ) : zeroObj Φ₁ B₁ divB₁ A ⟶ zeroObj Φ₁ B₁ divB₁ A :=
  mk1 (𝟙 _) 0 (Φ₁.pos _).zero_mem (k • u) (by simp [map_nsmul, hu])

/-- The base-identity endomorphism `(d, id, 0, 0)` of `(A, 0)`. -/
def frobEnd (d : ℕ+) : zeroObj Φ₁ B₁ divB₁ A ⟶ zeroObj Φ₁ B₁ divB₁ A :=
  mk' d (𝟙 _) 0 (Φ₁.pos _).zero_mem 0 (by simp)

omit [IsConnected D₁] [TotallyEpimorphic D₁] in
lemma unitPow_succ (k : ℕ) : unitPow u hu (k + 1) = unitPow u hu k ≫ unitPow u hu 1 := by
  ext <;> simp [unitPow, add_smul, add_comm]

omit [IsConnected D₁] [TotallyEpimorphic D₁] in
/-- The Frobenius-normalized relation `u ≫ φ_d = φ_d ≫ u^d`. -/
lemma unit_frob (d : ℕ+) :
    unitPow u hu 1 ≫ frobEnd (A := A) d = frobEnd d ≫ unitPow u hu d := by
  ext <;> simp [unitPow, frobEnd]

omit [IsConnected D₁] [IsConnected D₂] [TotallyEpimorphic D₂] in
/-- A base-identity, linear, isometric morphism of `C₂` composes on `u`-components by addition. -/
lemma u_comp_of_baseId {Y : Model Φ₂ B₂ divB₂} (a b : Y ⟶ Y) (ha : a.base = 𝟙 _)
    (hb₁ : b.deg = 1) : (a ≫ b).u = b.u + a.u := by
  simp [ha, hb₁]

omit [IsConnected D₂] in
include hD₁ hB₁ hD₂ hB₂ in
/-- **The Frobenius degree is preserved** if `C₁` has a unit of infinite order and `D₂` is
slim. -/
theorem degFr_map_eq (hD : IsSlim D₂) (hnt : HasNonTorsionUnit divB₁) {X Y : Model Φ₁ B₁ divB₁}
    (φ : X ⟶ Y) : degFr 𝐏₂ (F.map φ) = degFr 𝐏₁ φ := by
  have c := typeCorresp hD₁ hB₁ hD₂ hB₂ F
  obtain ⟨σ, hσ⟩ := exists_degHom F (fun _ _ φ h => (c.linear φ).1 h)
  rw [hσ]
  suffices h : ∀ d : ℕ+, σ d = d from h _
  intro d
  obtain ⟨A, u, hu0, hinf⟩ := hnt
  set Z := zeroObj Φ₁ B₁ divB₁ A
  -- images of the units and of `φ_d`
  have hbase : ∀ k, (F.map (unitPow u hu0 k)).base = 𝟙 _ := fun k =>
    base_map_eq_id F c.pullback c.baseIso hD _ rfl
  have hdeg : ∀ k, (F.map (unitPow u hu0 k)).deg = 1 := fun k =>
    (c.linear (unitPow u hu0 k)).1 rfl
  have hpow : ∀ k, (F.map (unitPow u hu0 k)).u = k • (F.map (unitPow u hu0 1)).u := by
    intro k
    induction k with
    | zero =>
      have : unitPow u hu0 0 = 𝟙 Z := by ext <;> simp [unitPow, Z]
      rw [this, F.map_id]
      simp
    | succ k ih =>
      rw [unitPow_succ, F.map_comp, u_comp_of_baseId _ _ (hbase k) (hdeg 1), ih, add_smul,
        one_smul, add_comm]
  have hφb : (F.map (frobEnd (A := A) (Φ₁ := Φ₁) (B₁ := B₁) (divB₁ := divB₁) d)).base = 𝟙 _ :=
    base_map_eq_id F c.pullback c.baseIso hD _ rfl
  have hφd : (F.map (frobEnd (A := A) (Φ₁ := Φ₁) (B₁ := B₁) (divB₁ := divB₁) d)).deg = σ d :=
    hσ (frobEnd d)
  have hdiv : ∀ k, (F.map (unitPow u hu0 k)).div = 0 := by
    intro k
    haveI : IsIso (unitPow u hu0 k) :=
      isIso_of _ rfl (by simp only [unitPow, mk1_base]; infer_instance) rfl
    exact Div_of_isIso (P := 𝐏₂) (F.map (unitPow u hu0 k))
  -- the relation `F u ≫ ψ = ψ ≫ F(u^d)` in `C₂`
  set v := (F.map (unitPow u hu0 1)).u with hv
  set ψ := F.map (frobEnd (A := A) (Φ₁ := Φ₁) (B₁ := B₁) (divB₁ := divB₁) d)
  have hrel := congrArg F.map (unit_frob u hu0 d)
  rw [F.map_comp, F.map_comp] at hrel
  have e₁ : (F.map (unitPow u hu0 1) ≫ ψ).u = ψ.u + (σ d : ℕ) • v := by
    rw [comp_u, hbase, GrpOn.pb_id', hφd]
  have e₂ : (ψ ≫ F.map (unitPow u hu0 d)).u = (d : ℕ) • v + ψ.u := by
    rw [comp_u, hφb, GrpOn.pb_id', hdeg, PNat.one_coe, one_smul, hpow]
  have hu := congrArg Hom.u hrel
  rw [e₁, e₂, add_comm ((d : ℕ) • v)] at hu
  have hdv : (σ d : ℕ) • v = (d : ℕ) • v := add_left_cancel hu
  -- transport back: `F(u^{σ(d)}) = F(u^d)`, hence `σ(d)·u = d·u`
  have key : F.map (unitPow u hu0 (σ d : ℕ)) = F.map (unitPow u hu0 d) := by
    ext
    · rw [hdeg, hdeg]
    · rw [hbase, hbase]
    · rw [hdiv, hdiv]
    · rw [hpow, hpow, hdv]
  have hk := congrArg Hom.u (F.map_injective key)
  simp only [unitPow, mk1_u] at hk
  by_contra hne
  have hne' : (σ d : ℕ) ≠ d := fun h => hne (PNat.eq h)
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · have h0 : ((d : ℕ) - σ d) • u = 0 := by
      simp [sub_nsmul _ hlt.le, hk]
    exact hinf _ (Nat.sub_pos_of_lt hlt) h0
  · have h0 : ((σ d : ℕ) - d) • u = 0 := by
      simp [sub_nsmul _ hlt.le, hk]
    exact hinf _ (Nat.sub_pos_of_lt hlt) h0

end Degree

end Model

end Frobenioid

end Iut
