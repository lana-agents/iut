/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm34Rlf
import Iut.Frobenioid.GaloisBase

/-!
# [FrdI], Theorem 3.4(ii), (iii) for realified model Frobenioids over `B(G)⁰`

`Iut/Frobenioid/Thm34.lean` characterizes pre-steps as FSM-morphisms; this needs torsion of every
order in the rational functions (`HasAllTorsion`). `Iut/Frobenioid/Thm34Rlf.lean` treats
torsion-free realified Frobenioids, but only over groupoid bases. The realification
`C^rlf_{F̃/F}` of [FrdI], Example 6.3 over `B(Gal(F̃/F))⁰` (`GlobalGaloisRlf`) is neither: its
rational functions `ℝ·div(L^×)` are torsion-free and its base is not a groupoid. This file
covers it, following [FrdI], Proposition 1.14(i), (ii) (l.1806–1830 of
`~/iut-scratch/wall/txt/The Geometry of Frobenioids I.txt`): pre-steps are characterized through
the irreducible morphisms.

## Hypotheses

* `IrredBase D`: if `a ≫ b` is an isomorphism, so is `a`; and every non-isomorphism of `D`
  factors as `g ≫ i ≫ h` with `i` irreducible. For compact `G`, `B(G)⁰` satisfies this
  (`OrbitObj.irredBase`: equivariant maps between the finite transitive `G`-sets `G/H` are
  surjective, and a non-isomorphism strictly decreases the cardinality, so a factorization of
  maximal length exists).
* `NoIrreducible Φ`: nonzero effective divisors are sums of two nonzero ones (realified
  monoids).

## Results

* `Model.isIrreducible_of_prime_baseIso`: isometric base-isomorphisms of prime Frobenius degree
  are irreducible; `Model.isIrreducible_pullback`: pull-backs with irreducible base are
  irreducible ([FrdI], Proposition 1.14(i), (a), (c));
* **`Model.isPreStep_iff_midAdj`**: pre-steps are exactly the morphisms mid-adjoint to the
  irreducible morphisms (the analogue of [FrdI], Proposition 1.14(ii): with `NoIrreducible Φ`
  every irreducible morphism is a non-pre-step);
* **`Model.typeCorresp_irr`**, **`Model.thm34_irr`**: every equivalence of such model
  Frobenioids matches pre-steps, base-isomorphisms, pull-backs, linear morphisms, morphisms of
  Frobenius type and isometries, and preserves the Frobenius structure ([FrdI], Theorem
  3.4(ii), (iii)).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w₁ w₂ v₁ v₂ u₁ u₂ u

/-- **Base categories with irreducible factorizations**: a composite `a ≫ b` is an isomorphism
only if `a` is, and every non-isomorphism factors through an irreducible morphism. -/
def IrredBase (D : Type u₁) [Category.{v₁} D] : Prop :=
  (∀ ⦃A B C : D⦄ (a : A ⟶ B) (b : B ⟶ C), IsIso (a ≫ b) → IsIso a) ∧
    ∀ ⦃A B : D⦄ (f : A ⟶ B), ¬ IsIso f → ∃ (A' B' : D) (g : A ⟶ A') (i : A' ⟶ B')
      (h : B' ⟶ B), IsIrreducible i ∧ g ≫ i ≫ h = f

namespace IrredBase

variable {D : Type u₁} [Category.{v₁} D] (hD : IrredBase D)
include hD

lemma isIso_left {A B C : D} (a : A ⟶ B) (b : B ⟶ C) (h : IsIso (a ≫ b)) : IsIso a :=
  hD.1 a b h

lemma factor {A B : D} (f : A ⟶ B) (hf : ¬ IsIso f) : ∃ (A' B' : D) (g : A ⟶ A') (i : A' ⟶ B')
    (h : B' ⟶ B), IsIrreducible i ∧ g ≫ i ≫ h = f :=
  hD.2 f hf

lemma isIso_right {A B C : D} (a : A ⟶ B) (b : B ⟶ C) (h : IsIso (a ≫ b)) : IsIso b := by
  haveI := hD.isIso_left a b h
  have : b = inv a ≫ (a ≫ b) := by simp
  rw [this]
  infer_instance

lemma isIso_mid {A B C E : D} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (h : IsIso (a ≫ b ≫ c)) :
    IsIso b :=
  hD.isIso_left b c (hD.isIso_right a (b ≫ c) h)

end IrredBase

namespace Model

section Single

variable {D : Type u₁} [Category.{v₁} D]
variable {Φ : DivMonoid.{w₁} D} {B : GrpOn.{w₁} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

lemma div_eq_zero_of_comp {X W Y : Model Φ B divB} (a : X ⟶ W) (b : W ⟶ Y)
    (h : (a ≫ b).div = 0) : a.div = 0 ∧ b.div = 0 := by
  rw [comp_div] at h
  have hb0 : Φ.pb a.base b.div = 0 :=
    Φ.eq_zero_of_add_eq_zero_left (Φ.pb_mem _ b.div_mem) ((Φ.pos _).nsmul_mem a.div_mem _) h
  rw [hb0, zero_add] at h
  exact ⟨Φ.eq_zero_of_nsmul_eq_zero b.deg.pos h, Φ.pb_injective a.base (by rw [hb0, map_zero])⟩

/-- **Isometric base-isomorphisms of prime Frobenius degree are irreducible** ([FrdI],
Proposition 1.14(i)(a)). -/
theorem isIrreducible_of_prime_baseIso (hD : IrredBase D) {X Y : Model Φ B divB} (φ : X ⟶ Y)
    (h₀ : φ.div = 0) (hb : IsIso φ.base) (hp : (φ.deg : ℕ).Prime) : IsIrreducible φ := by
  refine ⟨fun hi => ?_, fun W a b hab => ?_⟩
  · haveI := hi
    have := degFr_of_isIso (P := 𝐏) φ
    exact hp.one_lt.ne' (congrArg PNat.val this)
  · have hdeg := congrArg (fun ψ => (Hom.deg ψ : ℕ)) hab
    simp only [comp_deg, PNat.mul_coe] at hdeg
    obtain ⟨ha0, hb0⟩ := div_eq_zero_of_comp a b (by rw [hab, h₀])
    have hbase : IsIso (a.base ≫ b.base) := by
      rw [← comp_base, hab]; exact hb
    haveI := hD.isIso_left _ _ hbase
    haveI := hD.isIso_right _ _ hbase
    rw [← hdeg] at hp
    rcases (Nat.prime_mul_iff.mp hp) with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl (isIso_of a (PNat.coe_eq_one_iff.mp h) inferInstance ha0)
    · exact Or.inr (isIso_of b (PNat.coe_eq_one_iff.mp h) inferInstance hb0)

/-- **Pull-backs with irreducible base are irreducible** ([FrdI], Proposition 1.14(i)(c)). -/
theorem isIrreducible_pullback {X Y : Model Φ B divB} (φ : X ⟶ Y) (h₁ : φ.deg = 1)
    (h₀ : φ.div = 0) (hi : IsIrreducible φ.base) : IsIrreducible φ := by
  refine ⟨fun h => hi.1 (by haveI := h; exact isIso_Base (P := 𝐏) φ), fun W a b hab => ?_⟩
  have hdeg := congrArg Hom.deg hab
  rw [comp_deg, h₁] at hdeg
  have ha1 : a.deg = 1 := PNat.eq (Nat.eq_one_of_mul_eq_one_left (congrArg PNat.val hdeg))
  have hb1 : b.deg = 1 := PNat.eq (Nat.eq_one_of_mul_eq_one_right (congrArg PNat.val hdeg))
  obtain ⟨ha0, hb0⟩ := div_eq_zero_of_comp a b (by rw [hab, h₀])
  rcases hi.2 a.base b.base (by rw [← comp_base, hab]) with h | h
  · exact Or.inl (isIso_of a ha1 h ha0)
  · exact Or.inr (isIso_of b hb1 h hb0)

/-- **An irreducible morphism is not a pre-step** (`Φ` without irreducible elements). -/
theorem not_preStep_of_irreducible (hΦ : NoIrreducible Φ) {X Y : Model Φ B divB} (φ : X ⟶ Y)
    (hi : IsIrreducible φ) (h1 : φ.deg = 1) (hb : IsIso φ.base) : False := by
  by_cases h0 : φ.div = 0
  · exact hi.1 (isIso_of φ h1 hb h0)
  obtain ⟨a, ha, b, hb', ha0, hb0, hab⟩ := hΦ _ _ φ.div_mem h0
  let W : Model Φ B divB := ⟨X.base, X.α + a⟩
  let s₁ : X ⟶ W := mk1 (𝟙 _) a ha 0 (by simp [W])
  let s₂ : W ⟶ Y := mk1 φ.base b hb' φ.u (by
    have r := φ.rel
    rw [h1, PNat.one_coe, one_smul, hab] at r
    simp only [W]
    rw [← r]
    abel)
  have hc : s₁ ≫ s₂ = φ := by
    ext
    · simp [s₁, s₂, h1]
    · simp [s₁, s₂]
    · simp [s₁, s₂, hab, add_comm]
    · simp [s₁, s₂]
  rcases hi.2 s₁ s₂ hc with h | h
  · haveI := h
    exact ha0 (Div_of_isIso (P := 𝐏) s₁)
  · haveI := h
    exact hb0 (Div_of_isIso (P := 𝐏) s₂)

/-- **Pre-steps are exactly the morphisms mid-adjoint to the irreducible morphisms** (base with
irreducible factorizations, `Φ` without irreducible elements; cf. [FrdI], Proposition 1.14(ii)).
-/
theorem isPreStep_iff_midAdj (hD : IrredBase D) (hΦ : NoIrreducible Φ) {X Y : Model Φ B divB}
    (φ : X ⟶ Y) : IsPreStep 𝐏 φ ↔ MidAdj (fun _ _ ψ => IsIrreducible ψ) φ := by
  constructor
  · rintro ⟨hl, hbi⟩ V W a b c habc hb
    exfalso
    have h1 : φ.deg = 1 := hl
    have hdeg := congrArg Hom.deg habc
    simp only [comp_deg, h1] at hdeg
    have hb1 : b.deg = 1 := by
      have := congrArg PNat.val hdeg
      simp only [PNat.mul_coe, PNat.val_ofNat] at this
      exact PNat.eq (Nat.eq_one_of_mul_eq_one_left (Nat.eq_one_of_mul_eq_one_right this))
    have hbase : IsIso (a.base ≫ b.base ≫ c.base) := by
      have : a.base ≫ b.base ≫ c.base = φ.base := by
        rw [← comp_base, ← comp_base, habc]
      rw [this]; exact hbi
    exact not_preStep_of_irreducible hΦ b hb hb1 (hD.isIso_mid _ _ _ hbase)
  · intro hm
    refine ⟨?_, ?_⟩
    · by_contra hl
      have hn : (φ.deg : ℕ) ≠ 1 := fun h => hl (PNat.coe_eq_one_iff.mp h)
      set p := (φ.deg : ℕ).minFac with hp
      have hpp : p.Prime := Nat.minFac_prime hn
      obtain ⟨k, hk⟩ := Nat.minFac_dvd (φ.deg : ℕ)
      rw [← hp] at hk
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, mul_zero] at hk; exact absurd hk φ.deg.pos.ne'
        · exact h
      let pP : ℕ+ := ⟨p, hpp.pos⟩
      let kP : ℕ+ := ⟨k, hkpos⟩
      let W : Model Φ B divB := ⟨X.base, (p : ℕ) • X.α⟩
      let γ : X ⟶ W := mk' pP (𝟙 _) 0 (Φ.pos _).zero_mem 0 (by simp [W, pP])
      let ρ : W ⟶ Y := mk' kP φ.base φ.div φ.div_mem φ.u (by
        have r := φ.rel
        simp only [W, kP, PNat.mk_coe, ← mul_smul]
        rw [show k * p = (φ.deg : ℕ) by rw [hk]; ring]
        exact r)
      have hc : 𝟙 X ≫ γ ≫ ρ = φ := by
        ext
        · apply PNat.eq
          simp only [comp_deg, id_deg, mk'_deg, PNat.mul_coe, mul_one, γ, ρ, pP,
            kP, PNat.mk_coe]
          rw [hk, mul_comm]
        · simp [γ, ρ]
        · simp [γ, ρ]
        · simp [γ, ρ]
      have hirr : IsIrreducible γ :=
        isIrreducible_of_prime_baseIso hD γ rfl (by simp only [γ, mk'_base]; infer_instance) hpp
      exact hirr.1 (hm (𝟙 X) γ ρ hc hirr)
    · by_contra hbi
      obtain ⟨A', B', g, i, h, hi, hf⟩ := hD.factor φ.base hbi
      let X' : Model Φ B divB := ⟨A', Φ.pb (i ≫ h) Y.α⟩
      let Y' : Model Φ B divB := ⟨B', Φ.pb h Y.α⟩
      let a : X ⟶ X' := mk' φ.deg g φ.div φ.div_mem φ.u (by
        have r := φ.rel
        rw [← hf] at r
        simpa [X'] using r)
      let b : X' ⟶ Y' := mk1 i 0 (Φ.pos _).zero_mem 0 (by simp [X', Y'])
      let c : Y' ⟶ Y := mk1 h 0 (Φ.pos _).zero_mem 0 (by simp [Y'])
      have habc : a ≫ b ≫ c = φ := by
        ext
        · simp [a, b, c]
        · simp [a, b, c, hf]
        · simp [a, b, c]
        · simp [a, b, c]
      have hbirr : IsIrreducible b := isIrreducible_pullback b rfl rfl hi
      haveI := hm a b c habc hbirr
      exact hi.1 (isIso_Base (P := 𝐏) b)

end Single

section Main

variable {D₁ : Type u₁} [Category.{v₁} D₁] [IsConnected D₁] [TotallyEpimorphic D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂] [IsConnected D₂] [TotallyEpimorphic D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

omit [IsConnected D₁] [IsConnected D₂] in
/-- **[FrdI], Theorem 3.4(ii), (iii) (types)** for model Frobenioids over bases with
irreducible factorizations and divisor monoids without irreducible elements. -/
theorem typeCorresp_irr (hD₁ : BaseHyp D₁) (hI₁ : IrredBase D₁) (hΦ₁ : NoIrreducible Φ₁)
    (hD₂ : BaseHyp D₂) (hI₂ : IrredBase D₂) (hΦ₂ : NoIrreducible Φ₂)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] : TypeCorresp F := by
  have cPre : Corresp F (fun _ _ φ => IsPreStep 𝐏₁ φ) (fun _ _ φ => IsPreStep 𝐏₂ φ) :=
    ((corresp_isIrreducible F).midAdj isIrreducible_respIso).of_iff
      (fun _ _ φ => isPreStep_iff_midAdj hI₁ hΦ₁ φ) (fun _ _ φ => isPreStep_iff_midAdj hI₂ hΦ₂ φ)
  have cBase : Corresp F (fun _ _ φ => IsBaseIso 𝐏₁ φ) (fun _ _ φ => IsBaseIso 𝐏₂ φ) := by
    intro X Y φ
    change IsBaseIso _ φ ↔ IsBaseIso _ (F.map φ)
    rw [isBaseIso_iff_spanOf hD₁, isBaseIso_iff_spanOf hD₂]
    exact cPre.spanOf (isPreStep_respIso _) X Y
  have cPb : Corresp F (fun _ _ φ => IsPullback 𝐏₁ φ) (fun _ _ φ => IsPullback 𝐏₂ φ) :=
    (cBase.minAdj (isBaseIso_respIso _)).of_iff (fun _ _ φ => isPullback_iff_minAdj φ)
      (fun _ _ φ => isPullback_iff_minAdj φ)
  have cLin : Corresp F (fun _ _ φ => IsLinear 𝐏₁ φ) (fun _ _ φ => IsLinear 𝐏₂ φ) :=
    (cPre.compOf cPb (isPreStep_respIso _) isPullback_respIso).of_iff
      (fun _ _ φ => isLinear_iff_compOf φ) (fun _ _ φ => isLinear_iff_compOf φ)
  have cFr : Corresp F (fun _ _ φ => IsFrobeniusType 𝐏₁ φ)
      (fun _ _ φ => IsFrobeniusType 𝐏₂ φ) :=
    (cLin.minCoadj (isLinear_respIso _)).of_iff (fun _ _ φ => isFrobeniusType_iff_minCoadj φ)
      (fun _ _ φ => isFrobeniusType_iff_minCoadj φ)
  have cIso : Corresp F (fun _ _ φ => IsIsometric 𝐏₁ φ) (fun _ _ φ => IsIsometric 𝐏₂ φ) :=
    (cFr.compOf cPb isFrobeniusType_respIso isPullback_respIso).of_iff
      (fun _ _ φ => isIsometric_iff_compOf φ) (fun _ _ φ => isIsometric_iff_compOf φ)
  exact ⟨cPre, cBase, cPb, cLin, cFr, cIso⟩

/-- **[FrdI], Theorem 3.4(iii)** for model Frobenioids over bases of FSM- and Aut-type with
irreducible factorizations whose divisor monoids have no irreducible elements (e.g. the
realification of [FrdI], Example 6.3 over `B(G)⁰`): every equivalence of categories preserves
the Frobenius structure. -/
theorem thm34_irr (hD₁ : BaseHyp D₁) (hI₁ : IrredBase D₁) (hΦ₁ : NoIrreducible Φ₁)
    (hD₂ : BaseHyp D₂) (hI₂ : IrredBase D₂) (hΦ₂ : NoIrreducible Φ₂)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] :
    PreservesFrobeniusStructure 𝐏₁ 𝐏₂ F := by
  have c := typeCorresp_irr hD₁ hI₁ hΦ₁ hD₂ hI₂ hΦ₂ F
  have c' := typeCorresp_irr hD₂ hI₂ hΦ₂ hD₁ hI₁ hΦ₁ F.inv
  obtain ⟨e, he⟩ := exists_degEquiv F (fun _ _ φ h => (c.linear φ).1 h)
    (fun _ _ φ h => (c'.linear φ).1 h)
  have cCoa : ∀ {A B : Model Φ₁ B₁ divB₁} (φ : A ⟶ B),
      IsCoangular 𝐏₁ φ ↔ IsCoangular 𝐏₂ (F.map φ) :=
    fun φ => ⟨fun _ => isCoangular _, fun _ => isCoangular _⟩
  refine ⟨fun φ => c.frobType φ, fun φ => c.linear φ, fun φ => c.baseIso φ, cCoa,
    fun φ => c.pullback φ, fun φ => c.isometric φ, fun φ => and_congr (cCoa φ) (c.isometric φ),
    e, fun φ => he φ⟩

end Main

end Model

/-! ### `B(G)⁰` has irreducible factorizations -/

section Orbit

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

lemma OrbitObj.finite (A : OrbitObj G) : Finite (G ⧸ A.H) :=
  Subgroup.quotient_finite_of_isOpen A.H A.isOpen

omit [IsTopologicalGroup G] [CompactSpace G] in
lemma OrbitHom.bijective_of_isIso {A B : OrbitObj G} (f : A ⟶ B) [IsIso f] :
    Function.Bijective f.toFun := by
  refine Function.bijective_iff_has_inverse.mpr ⟨(inv f).toFun, fun x => ?_, fun y => ?_⟩
  · change (f ≫ inv f).toFun x = x
    rw [IsIso.hom_inv_id]; rfl
  · change (inv f ≫ f).toFun y = y
    rw [IsIso.inv_hom_id]; rfl

omit [IsTopologicalGroup G] [CompactSpace G] in
lemma OrbitHom.isIso_iff_injective {A B : OrbitObj G} (f : A ⟶ B) :
    IsIso f ↔ Function.Injective f.toFun :=
  ⟨fun _ => (OrbitHom.bijective_of_isIso f).1,
    fun h => OrbitHom.isIso_of_bijective f ⟨h, f.surjective⟩⟩

lemma OrbitHom.card_lt_of_not_isIso {A B : OrbitObj G} (f : A ⟶ B) (hf : ¬ IsIso f) :
    Nat.card (G ⧸ B.H) < Nat.card (G ⧸ A.H) := by
  haveI := A.finite
  haveI := B.finite
  haveI := Fintype.ofFinite (G ⧸ A.H)
  haveI := Fintype.ofFinite (G ⧸ B.H)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_surjective_not_injective f.toFun f.surjective
    (fun h => hf ((OrbitHom.isIso_iff_injective f).mpr h))

/-- **`B(G)⁰` has irreducible factorizations** (compact `G`). -/
theorem OrbitObj.irredBase : IrredBase (OrbitObj G) := by
  refine ⟨fun A B C a b h => ?_, ?_⟩
  · rw [OrbitHom.isIso_iff_injective]
    have := (OrbitHom.bijective_of_isIso (a ≫ b)).1
    rw [OrbitHom.comp_toFun] at this
    exact this.of_comp
  · suffices ∀ (n : ℕ) {A B : OrbitObj G} (f : A ⟶ B), Nat.card (G ⧸ A.H) = n → ¬ IsIso f →
        ∃ (A' B' : OrbitObj G) (g : A ⟶ A') (i : A' ⟶ B') (h : B' ⟶ B),
          IsIrreducible i ∧ g ≫ i ≫ h = f from fun A B f hf => this _ f rfl hf
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro A B f hn hf
      by_cases hi : IsIrreducible f
      · exact ⟨A, B, 𝟙 _, f, 𝟙 _, hi, by simp⟩
      · have : ∃ (W : OrbitObj G) (a : A ⟶ W) (b : W ⟶ B), a ≫ b = f ∧ ¬ IsIso a ∧
            ¬ IsIso b := by
          by_contra hc
          push Not at hc
          exact hi ⟨hf, fun W a b hab => by
            by_cases ha : IsIso a
            · exact Or.inl ha
            · exact Or.inr (hc W a b hab ha)⟩
        obtain ⟨W, a, b, hab, ha, hb⟩ := this
        obtain ⟨A', B', g, i, h, hi', he⟩ :=
          ih _ (hn ▸ OrbitHom.card_lt_of_not_isIso a ha) b rfl hb
        exact ⟨A', B', a ≫ g, i, h, hi', by rw [Category.assoc, he, hab]⟩

end Orbit

end Frobenioid

end Iut
