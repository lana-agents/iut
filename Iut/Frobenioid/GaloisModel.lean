/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GaloisExample

/-!
# Model Frobenioids over `B(G)⁰` from a `G`-module ([FrdII], Example 1.1)

[FrdII], Example 1.1(ii): for a functor `D → D₀` (here `D = B(G)⁰`), a monoid `Φ ⊆ Φ₀^Λ|_D` and
`B = B₀^Λ|_D ×_{(Φ₀^Λ)^gp|_D} Φ^gp`, the *`p`-adic Frobenioid* is the model Frobenioid of
`(Φ, B → Φ^gp)`. For `D = B(G_K)⁰` the rational functions on `G/H` are `(K̄^H)^×`, i.e. the
`H`-invariants of the `G`-module `K̄^×`.

This file makes the construction for a topological group `G`, a `G`-module `M` (written
additively), a `G`-invariant homomorphism `ℓ : M → ℝ` (the valuation `ord`) and a subgroup
`Γ ⊆ ℝ` (`Γ = ℤ·ord(p)` for an absolutely primitive `Φ`, `Γ = ℚ` for the perfection):

* `invGrpOn G S` (`S ⊆ M` a `G`-stable subgroup): the group-like monoid `G/H ↦ S^H` on
  `B(G)⁰`, with pull-back along `f : G/H → G/H'`, `f(H) = gH'`, given by `m ↦ g·m`;
* `constPhi G Γ`: the fixed-value divisor monoid `Γ_{≥0} ⊆ Γ`;
* **`GaloisModel G ℓ Γ`**: the model Frobenioid with `Φ = Γ_{≥0}`,
  `B(G/H) = (ℓ⁻¹(Γ))^H = M^H ×_ℝ Γ` and `Div_B = ℓ`; `GaloisModel.isFrobenioid`;
* `GaloisModel.hasAllTorsion`: if `M` has nonzero `ℓ`-null `n`-torsion with open stabilizer for
  every `n ≥ 2` (roots of unity), the rational functions have torsion of every order cofinally;
  hence **`GaloisModel.thm34`** ([FrdI], Theorem 3.4(ii)–(iii) for these Frobenioids, via
  `Model.thm34_galois`) and `GaloisModel.thm34_base` (Theorem 3.4(v) for slim `G`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe u

/-! ### Invariants of a `G`-module as a group-like monoid on `B(G)⁰` -/

section Fixed

variable (G : Type u) [Group G] [TopologicalSpace G]
variable {M : Type u} [AddCommGroup M] [DistribMulAction G M]

/-- A `G`-stable subgroup of `M`. -/
structure StableSub (G : Type u) [Group G] (M : Type u) [AddCommGroup M]
    [DistribMulAction G M] where
  /-- The subgroup. -/
  S : AddSubgroup M
  smul_mem' : ∀ (g : G) {m : M}, m ∈ S → g • m ∈ S

variable {G}

/-- `S^H`. -/
def fixedSub (S : StableSub G M) (A : OrbitObj G) : AddSubgroup M where
  carrier := {m | m ∈ S.S ∧ ∀ h ∈ A.H, h • m = m}
  add_mem' ha hb := ⟨S.S.add_mem ha.1 hb.1, fun h hh => by rw [smul_add, ha.2 h hh, hb.2 h hh]⟩
  zero_mem' := ⟨S.S.zero_mem, fun _ _ => smul_zero _⟩
  neg_mem' ha := ⟨S.S.neg_mem ha.1, fun h hh => by rw [smul_neg, ha.2 h hh]⟩

omit [TopologicalSpace G] in
lemma mk_eq_one_iff {H : Subgroup G} {h : G} :
    (QuotientGroup.mk h : G ⧸ H) = QuotientGroup.mk 1 ↔ h ∈ H := by
  rw [QuotientGroup.eq, mul_one, inv_mem_iff]

namespace OrbitHom

/-- A representative `g` of `f(H) = gH'`. -/
noncomputable def rep {A B : OrbitObj G} (f : A ⟶ B) : G := (f.toFun (QuotientGroup.mk 1)).out

lemma mk_rep {A B : OrbitObj G} (f : A ⟶ B) :
    (QuotientGroup.mk (rep f) : G ⧸ B.H) = f.toFun (QuotientGroup.mk 1) :=
  QuotientGroup.out_eq' _

lemma conj_mem {A B : OrbitObj G} (f : A ⟶ B) {h : G} (hh : h ∈ A.H) :
    (rep f)⁻¹ * (h * rep f) ∈ B.H := by
  have e1 : (QuotientGroup.mk h : G ⧸ A.H) = QuotientGroup.mk 1 := mk_eq_one_iff.mpr hh
  have e2 := congrArg f.toFun e1
  rw [OrbitHom.apply_mk_of_eq f (mk_rep f).symm, OrbitHom.apply_mk_of_eq f (mk_rep f).symm,
    one_mul] at e2
  exact (QuotientGroup.eq.mp e2.symm)

lemma rep_id_mem (A : OrbitObj G) : rep (𝟙 A) ∈ A.H := by
  have := mk_rep (𝟙 A)
  rw [OrbitHom.id_toFun, id] at this
  exact mk_eq_one_iff.mp this

lemma rep_comp_mem {A B E : OrbitObj G} (f : A ⟶ B) (g : B ⟶ E) :
    (rep f * rep g)⁻¹ * rep (f ≫ g) ∈ E.H := by
  have h1 := mk_rep (f ≫ g)
  rw [OrbitHom.comp_toFun, Function.comp_apply, ← mk_rep f,
    OrbitHom.apply_mk_of_eq g (mk_rep g).symm] at h1
  exact QuotientGroup.eq.mp h1.symm

end OrbitHom

variable (S : StableSub G M)

lemma fixedSub_smul_mem {A B : OrbitObj G} (f : A ⟶ B) {m : M} (hm : m ∈ fixedSub S B) :
    OrbitHom.rep f • m ∈ fixedSub S A := by
  refine ⟨S.smul_mem' _ hm.1, fun h hh => ?_⟩
  have hc := OrbitHom.conj_mem f hh
  calc h • OrbitHom.rep f • m
      = OrbitHom.rep f • ((OrbitHom.rep f)⁻¹ * (h * OrbitHom.rep f)) • m := by
        rw [← mul_smul, ← mul_smul, mul_inv_cancel_left, mul_smul]
    _ = OrbitHom.rep f • m := by rw [hm.2 _ hc]

lemma fixed_smul_eq_of_mem {A : OrbitObj G} {m : M} (hm : m ∈ fixedSub S A) {g g' : G}
    (h : g⁻¹ * g' ∈ A.H) : g' • m = g • m := by
  calc g' • m = g • (g⁻¹ * g') • m := by rw [← mul_smul, mul_inv_cancel_left]
    _ = g • m := by rw [hm.2 _ h]

/-- **The group-like monoid `G/H ↦ S^H` on `B(G)⁰`.** -/
noncomputable def invGrpOn (S : StableSub G M) [IsTopologicalGroup G] : GrpOn.{u} (OrbitObj G) where
  obj A := fixedSub S A
  pb {A B} f :=
    { toFun := fun m => ⟨OrbitHom.rep f • m.1, fixedSub_smul_mem S f m.2⟩
      map_zero' := Subtype.ext (smul_zero _)
      map_add' := fun x y => Subtype.ext (smul_add _ _ _) }
  pb_id A x := Subtype.ext (by
    change OrbitHom.rep (𝟙 A) • x.1 = x.1
    exact x.2.2 _ (OrbitHom.rep_id_mem A))
  pb_comp f g x := Subtype.ext (by
    change OrbitHom.rep (f ≫ g) • x.1 = OrbitHom.rep f • OrbitHom.rep g • x.1
    rw [← mul_smul]
    exact fixed_smul_eq_of_mem S x.2 (OrbitHom.rep_comp_mem f g))
  pb_injective f x y h := Subtype.ext (MulAction.injective (OrbitHom.rep f)
    (congrArg Subtype.val h))
  pb_bijective_of_fsm {A B} f hf := by
    refine ⟨fun x y h => Subtype.ext (MulAction.injective (OrbitHom.rep f)
      (congrArg Subtype.val h)), fun y => ?_⟩
    have hinj := (OrbitHom.bijective_of_isFSM hf).1
    set g := OrbitHom.rep f
    have hk : ∀ k ∈ B.H, g * k * g⁻¹ ∈ A.H := fun k hk => by
      have e : f.toFun (QuotientGroup.mk (g * k * g⁻¹)) = f.toFun (QuotientGroup.mk 1) := by
        rw [OrbitHom.apply_mk_of_eq f (OrbitHom.mk_rep f).symm,
          OrbitHom.apply_mk_of_eq f (OrbitHom.mk_rep f).symm, one_mul, inv_mul_cancel_right]
        refine QuotientGroup.eq.mpr ?_
        simp only [g, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact B.H.inv_mem hk
      exact mk_eq_one_iff.mp (hinj e)
    refine ⟨⟨g⁻¹ • y.1, S.smul_mem' _ y.2.1, fun k hkB => ?_⟩, Subtype.ext ?_⟩
    · calc k • g⁻¹ • y.1 = g⁻¹ • (g * k * g⁻¹) • y.1 := by
            rw [← mul_smul, ← mul_smul]; group
        _ = g⁻¹ • y.1 := by rw [y.2.2 _ (hk k hkB)]
    · change g • g⁻¹ • y.1 = y.1
      rw [smul_inv_smul]

end Fixed

/-! ### Fixed-value divisor monoids `Γ_{≥0}` -/

section Const

variable (D : Type u) [Category D] (Γ : AddSubgroup ℝ)

/-- `Γ_{≥0}`. -/
def gammaCone : AddSubmonoid Γ where
  carrier := {x | 0 ≤ (x : ℝ)}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, AddSubgroup.coe_add] at ha hb ⊢
    exact add_nonneg ha hb
  zero_mem' := le_refl (0 : ℝ)

/-- **The fixed-value divisor monoid `Γ_{≥0}`** on `D` (identity pull-backs). -/
def constPhi : DivMonoid.{0} D where
  obj _ := Γ
  pb _ := AddMonoidHom.id Γ
  pb_id _ _ := rfl
  pb_comp _ _ _ := rfl
  pb_injective _ := Function.injective_id
  pb_bijective_of_fsm _ _ := Function.bijective_id
  pos _ := gammaCone Γ
  pb_mem _ _ h := h
  sharp {_ x} h h' := by
    change 0 ≤ (x : ℝ) at h
    change 0 ≤ ((-x : Γ) : ℝ) at h'
    rw [AddSubgroup.coe_neg] at h'
    exact Subtype.ext (by simp only [AddSubgroup.coe_zero]; linarith)
  saturated {_ x} n hn h := by
    change 0 ≤ ((n • x : Γ) : ℝ) at h
    change 0 ≤ (x : ℝ)
    rw [AddSubgroup.coe_nsmul, nsmul_eq_mul] at h
    exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hn)
  generating {_} x := by
    refine ⟨⟨max (x : ℝ) (0 : ℝ), ?_⟩, ?_, ⟨max (-(x : ℝ)) (0 : ℝ), ?_⟩, ?_, Subtype.ext ?_⟩
    · rcases le_total (x : ℝ) 0 with h | h
      · rw [max_eq_right h]; exact Γ.zero_mem
      · rw [max_eq_left h]; exact x.2
    · exact (le_max_right _ _ : (0 : ℝ) ≤ max _ _)
    · rcases le_total (-(x : ℝ)) 0 with h | h
      · rw [max_eq_right h]; exact Γ.zero_mem
      · rw [max_eq_left h]; exact Γ.neg_mem x.2
    · exact (le_max_right _ _ : (0 : ℝ) ≤ max _ _)
    · simp only [AddSubgroup.coe_sub]
      rw [max_zero_sub_max_neg_zero_eq_self]
  pos_surj_of_fsm _ _ y hy := ⟨y, hy, rfl⟩

end Const

/-! ### The model Frobenioid -/

section Model

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type} [AddCommGroup M] [DistribMulAction G M]
variable (ℓ : M →+ ℝ) (hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m) (Γ : AddSubgroup ℝ)

/-- `ℓ⁻¹(Γ)`, a `G`-stable subgroup (`M ×_ℝ Γ`). -/
def preSub (ℓ : M →+ ℝ) (hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m) (Γ : AddSubgroup ℝ) :
    StableSub G M where
  S := Γ.comap ℓ
  smul_mem' g m hm := by
    change ℓ (g • m) ∈ Γ
    rw [hℓ]; exact hm

/-- `B(G/H) = (ℓ⁻¹ Γ)^H`. -/
noncomputable abbrev bGal (ℓ : M →+ ℝ) (hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m)
    (Γ : AddSubgroup ℝ) : GrpOn.{0} (OrbitObj G) := invGrpOn (preSub G ℓ hℓ Γ)

/-- `Div_B = ℓ`. -/
noncomputable def divGal : DivHom (bGal G ℓ hℓ Γ) (constPhi (OrbitObj G) Γ).toGrpOn where
  app _ :=
    { toFun := fun m => ⟨ℓ m.1, m.2.1⟩
      map_zero' := Subtype.ext (map_zero ℓ)
      map_add' := fun _ _ => Subtype.ext (map_add ℓ _ _) }
  natural _ x := Subtype.ext (hℓ _ x.1)

/-- **The model Frobenioid of `(Γ_{≥0}, (ℓ⁻¹Γ)^{(-)} → Γ)` over `B(G)⁰`** ([FrdII], Example
1.1(ii)). -/
abbrev GaloisModel (ℓ : M →+ ℝ) (hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m)
    (Γ : AddSubgroup ℝ) : Type :=
  Model (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ)

namespace GaloisModel

/-- `GaloisModel` is a Frobenioid ([FrdI], Theorem 5.2(ii)). -/
theorem isFrobenioid :
    IsFrobenioid (Model.toElem (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ)) :=
  Model.isFrobenioid

variable {G ℓ hℓ Γ}

/-- **Torsion of every order, cofinally**, from nonzero `ℓ`-null torsion of `M` with open
stabilizers (roots of unity of `K̄`). -/
theorem hasAllTorsion
    (hT : ∀ n : ℕ, 2 ≤ n → ∃ m : M, m ≠ 0 ∧ n • m = 0 ∧ ℓ m = 0 ∧
      IsOpen (MulAction.stabilizer G m : Set G)) :
    HasAllTorsion (bGal G ℓ hℓ Γ) := by
  intro A n hn
  obtain ⟨m, hm0, hmn, hℓm, hopen⟩ := hT n hn
  let C : OrbitObj G := ⟨A.H ⊓ MulAction.stabilizer G m, A.isOpen.inter hopen⟩
  have hle : C.H ≤ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ A.H) := fun h hh => by
    rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact mk_eq_one_iff.mpr hh.1
  refine ⟨C, pointHom C A _ hle, ⟨m, ?_, fun h hh => hh.2⟩, fun h => hm0 ?_,
    Subtype.ext ?_⟩
  · change ℓ m ∈ Γ
    rw [hℓm]; exact Γ.zero_mem
  · exact congrArg Subtype.val h
  · change n • m = 0
    exact hmn

/-- **[FrdI], Theorem 3.4(ii), (iii) for the Frobenioids `GaloisModel`** (compact `G`):
every equivalence preserves the Frobenius structure. -/
theorem thm34 [CompactSpace G]
    (hT : ∀ n : ℕ, 2 ≤ n → ∃ m : M, m ≠ 0 ∧ n • m = 0 ∧ ℓ m = 0 ∧
      IsOpen (MulAction.stabilizer G m : Set G))
    (F : GaloisModel G ℓ hℓ Γ ⥤ GaloisModel G ℓ hℓ Γ) [F.IsEquivalence] :
    PreservesFrobeniusStructure
      (Model.toElem (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ))
      (Model.toElem (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ)) F :=
  Model.thm34_galois (hasAllTorsion hT) (hasAllTorsion hT) F

/-- **[FrdI], Theorem 3.4(v)** for `GaloisModel` over a slim profinite `G`. -/
theorem thm34_base [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space G]
    (hG : IsSlimGroup G)
    (hT : ∀ n : ℕ, 2 ≤ n → ∃ m : M, m ≠ 0 ∧ n • m = 0 ∧ ℓ m = 0 ∧
      IsOpen (MulAction.stabilizer G m : Set G))
    (F : GaloisModel G ℓ hℓ Γ ⥤ GaloisModel G ℓ hℓ Γ) [F.IsEquivalence] :
    PreservesBase
      (Model.toElem (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ))
      (Model.toElem (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ)) F :=
  Model.thm34_galois_preservesBase hG (hasAllTorsion hT) (hasAllTorsion hT) F

local notation "𝐏G" => Model.toElem (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ)

lemma div_eq_ell {X : GaloisModel G ℓ hℓ Γ} (e : X ⟶ X) (hb : e.base = 𝟙 _) (h : e.deg = 1) :
    ((show Γ from e.div) : ℝ) = ℓ e.u.1 := by
  have r := e.rel
  rw [h, hb] at r
  change (1 : ℕ) • (show Γ from X.α) + (show Γ from e.div) =
    (show Γ from X.α) + ⟨ℓ e.u.1, e.u.2.1⟩ at r
  have r' := congrArg (fun z : Γ => (z : ℝ)) r
  simp only [one_smul, AddSubgroup.coe_add] at r'
  linarith

/-- **`O^▷(A) ≅ {u ∈ B(A_D) : ℓ(u) ≥ 0}`** ([FrdII], Example 1.1: `O^▷` of a `p`-adic
Frobenioid is the monoid of `H`-invariant elements of norm `≤ 1` in `B`). -/
noncomputable def orhdEquiv (X : GaloisModel G ℓ hℓ Γ) :
    Orhd 𝐏G X ≃ {u : (bGal G ℓ hℓ Γ).obj X.base // 0 ≤ ℓ u.1} where
  toFun a := ⟨a.1.u, by
    rw [← div_eq_ell a.1 a.2.1 a.2.2]; exact a.1.div_mem⟩
  invFun u := ⟨Model.mk1 (𝟙 _) ⟨ℓ u.1.1, u.1.2.1⟩ u.2 u.1 (by
      change X.α + ⟨ℓ u.1.1, u.1.2.1⟩ = X.α + ⟨ℓ u.1.1, u.1.2.1⟩; rfl), rfl, rfl⟩
  left_inv a := by
    refine Subtype.ext (Model.hom_ext ?_ a.2.1.symm (Subtype.ext ?_) rfl)
    · exact (show a.1.deg = 1 from a.2.2).symm
    · exact (div_eq_ell a.1 a.2.1 a.2.2).symm
  right_inv u := rfl

/-- **`O^×(A) ≅ {u ∈ B(A_D) : ℓ(u) = 0}`** (the units: `H`-invariant elements of norm `1`). -/
noncomputable def ounitsEquiv (X : GaloisModel G ℓ hℓ Γ) :
    Ounits 𝐏G X ≃ {u : (bGal G ℓ hℓ Γ).obj X.base // ℓ u.1 = 0} where
  toFun a := ⟨a.1.u, by
    obtain ⟨-, -, h₃⟩ := (Model.isIso_iff a.1).mp a.2.1
    rw [← div_eq_ell a.1 a.2.2.1 a.2.2.2, h₃]; rfl⟩
  invFun u :=
    let φ : X ⟶ X := Model.mk1 (𝟙 _) 0 (gammaCone Γ).zero_mem u.1 (by
      change X.α + 0 = X.α + ⟨ℓ u.1.1, u.1.2.1⟩
      congr 1
      exact Subtype.ext u.2.symm)
    ⟨φ, Model.isIso_of φ rfl (inferInstanceAs (IsIso (𝟙 X.base))) rfl, rfl, rfl⟩
  left_inv a := by
    obtain ⟨h₁, -, h₃⟩ := (Model.isIso_iff a.1).mp a.2.1
    exact Subtype.ext (Model.hom_ext h₁.symm a.2.2.1.symm h₃.symm rfl)
  right_inv u := rfl

end GaloisModel

end Model

end Frobenioid

end Iut
