/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm34
import Iut.Frobenioid.Global

/-!
# [FrdI], Theorem 3.4(iii) for realified model Frobenioids over groupoid bases

The characterization "pre-steps = FSM-morphisms" of `Iut/Frobenioid/ModelTypes.lean` needs
torsion in the rational functions. The **global realified Frobenioid** `C^⊩` of IUT I, Example
3.5 (`GlobalRealified`, over the one-morphism base `Pt`, with `B = ℝ·div(K^×)` torsion-free) is
covered by a second route, which uses irreducible morphisms as in [FrdI], Proposition 1.14(i):

* `NoIrreducible Φ`: every nonzero element of a divisor monoid `Φ(A)` is a sum of two nonzero
  elements (true for monoids of effective `ℝ`-divisors);
* `IsGroupoidBase D`: every morphism of `D` is an isomorphism (true for `Pt`).

Then (`Model.isIrreducible_iff`) the **irreducible morphisms are exactly the isometric morphisms
of prime Frobenius degree**, hence (`Model.isLinear_iff_midAdj`) **linear morphisms are exactly
the morphisms mid-adjoint to the irreducible morphisms**. Linear morphisms being
category-theoretic, so are the morphisms of Frobenius type (minimal-coadjoint to the linear
ones); every morphism is a base-isomorphism and co-angular, pull-backs are isomorphisms, pre-steps
are the linear morphisms and isometries the morphisms of Frobenius type.

**Theorem** (`Model.thm34_groupoid`, `GlobalRealified.thm34`): every equivalence between such
Frobenioids preserves the Frobenius structure (`PreservesFrobeniusStructure`); in particular every
equivalence `C^⊩(K) ≌ C^⊩(L)` of global realified Frobenioids does.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w₁ w₂ v₁ v₂ u₁ u₂ u

/-- No element of `Φ(A)` is irreducible: every nonzero `z ∈ Φ(A)` is `a + b` with `a, b ≠ 0`. -/
def NoIrreducible {D : Type u₁} [Category.{v₁} D] (Φ : DivMonoid.{w₁} D) : Prop :=
  ∀ (A : D) (z : Φ.obj A), z ∈ Φ.pos A → z ≠ 0 →
    ∃ a ∈ Φ.pos A, ∃ b ∈ Φ.pos A, a ≠ 0 ∧ b ≠ 0 ∧ z = a + b

/-- Every morphism of `D` is an isomorphism. -/
def IsGroupoidBase (D : Type u₁) [Category.{v₁} D] : Prop := ∀ ⦃A B : D⦄ (f : A ⟶ B), IsIso f

namespace Model

section Single

variable {D : Type u₁} [Category.{v₁} D]
variable {Φ : DivMonoid.{w₁} D} {B : GrpOn.{w₁} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-- In a model over a groupoid base, a linear isometry is an isomorphism. -/
lemma isIso_of_linear_isometric (hD : IsGroupoidBase D) {X Y : Model Φ B divB} (φ : X ⟶ Y)
    (h₁ : φ.deg = 1) (h₀ : φ.div = 0) : IsIso φ :=
  isIso_of φ h₁ (hD _) h₀

/-- **Isometric morphisms of prime Frobenius degree are irreducible** (groupoid base). -/
theorem isIrreducible_of_prime (hD : IsGroupoidBase D) {X Y : Model Φ B divB} (φ : X ⟶ Y)
    (h₀ : φ.div = 0) (hp : (φ.deg : ℕ).Prime) : IsIrreducible φ := by
  refine ⟨fun hi => ?_, fun W a b hab => ?_⟩
  · haveI := hi
    have := degFr_of_isIso (P := 𝐏) φ
    exact hp.one_lt.ne' (congrArg PNat.val this)
  · have hdeg := congrArg (fun ψ => (Hom.deg ψ : ℕ)) hab
    simp only [comp_deg, PNat.mul_coe] at hdeg
    have hdiv := congrArg Hom.div hab
    rw [comp_div, h₀] at hdiv
    have hb0 : Φ.pb a.base b.div = 0 :=
      Φ.eq_zero_of_add_eq_zero_left (Φ.pb_mem _ b.div_mem) ((Φ.pos _).nsmul_mem a.div_mem _)
        hdiv
    rw [hb0, zero_add] at hdiv
    have ha0 : a.div = 0 := Φ.eq_zero_of_nsmul_eq_zero b.deg.pos hdiv
    have hb0' : b.div = 0 := Φ.pb_injective a.base (by rw [hb0, map_zero])
    rw [← hdeg] at hp
    rcases (Nat.prime_mul_iff.mp hp) with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl (isIso_of_linear_isometric hD a (PNat.coe_eq_one_iff.mp h) ha0)
    · exact Or.inr (isIso_of_linear_isometric hD b (PNat.coe_eq_one_iff.mp h) hb0')

/-- **An irreducible morphism is not linear** (groupoid base, `Φ` without irreducible elements):
a linear morphism with nonzero zero divisor `a + b` factors through steps with zero divisors
`a`, `b`, and a linear isometry is an isomorphism. -/
theorem not_linear_of_irreducible (hD : IsGroupoidBase D) (hΦ : NoIrreducible Φ)
    {X Y : Model Φ B divB} (φ : X ⟶ Y) (hi : IsIrreducible φ) : φ.deg ≠ 1 := by
  intro h1
  by_cases h0 : φ.div = 0
  · exact hi.1 (isIso_of_linear_isometric hD φ h1 h0)
  obtain ⟨a, ha, b, hb, ha0, hb0, hab⟩ := hΦ _ _ φ.div_mem h0
  let W : Model Φ B divB := ⟨X.base, X.α + a⟩
  let s₁ : X ⟶ W := mk1 (𝟙 _) a ha 0 (by simp [W])
  let s₂ : W ⟶ Y := mk1 φ.base b hb φ.u (by
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
    have h' := Div_of_isIso (P := 𝐏) s₁
    exact ha0 h'
  · haveI := h
    have h' := Div_of_isIso (P := 𝐏) s₂
    exact hb0 h'

/-- **Linear morphisms are those mid-adjoint to the irreducible morphisms** (groupoid base, `Φ`
without irreducible elements). -/
theorem isLinear_iff_midAdj (hD : IsGroupoidBase D) (hΦ : NoIrreducible Φ)
    {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsLinear 𝐏 φ ↔ MidAdj (fun _ _ ψ => IsIrreducible ψ) φ := by
  constructor
  · intro hl V W a b c habc hb
    exfalso
    have h1 : φ.deg = 1 := hl
    have hdeg := congrArg Hom.deg habc
    simp only [comp_deg, h1] at hdeg
    have hb1 : b.deg = 1 := by
      have := congrArg PNat.val hdeg
      simp only [PNat.mul_coe, PNat.val_ofNat] at this
      exact PNat.eq (Nat.eq_one_of_mul_eq_one_left (Nat.eq_one_of_mul_eq_one_right this))
    exact not_linear_of_irreducible hD hΦ b hb hb1
  · intro hm
    by_contra hl
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
    have hirr : IsIrreducible γ := isIrreducible_of_prime hD γ rfl hpp
    exact hirr.1 (hm (𝟙 X) γ ρ hc hirr)

lemma isPullback_iff_isIso (hD : IsGroupoidBase D) {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsPullback 𝐏 φ ↔ IsIso φ := by
  rw [isPullback_iff, isIso_iff]
  exact ⟨fun ⟨h₁, h₀⟩ => ⟨h₁, hD _, h₀⟩, fun ⟨h₁, _, h₀⟩ => ⟨h₁, h₀⟩⟩

lemma isPreStep_iff_linear (hD : IsGroupoidBase D) {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsPreStep 𝐏 φ ↔ IsLinear 𝐏 φ :=
  ⟨fun h => h.1, fun h => ⟨h, hD _⟩⟩

lemma isIsometric_iff_frobType (hD : IsGroupoidBase D) {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsIsometric 𝐏 φ ↔ IsFrobeniusType 𝐏 φ := by
  rw [isFrobeniusType_iff]
  exact ⟨fun h => ⟨h, hD _⟩, fun h => h.1⟩

end Single

section Main

variable {D₁ : Type u₁} [Category.{v₁} D₁] [IsConnected D₁] [TotallyEpimorphic D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂] [IsConnected D₂] [TotallyEpimorphic D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

omit [IsConnected D₁] [IsConnected D₂] [TotallyEpimorphic D₁] [TotallyEpimorphic D₂] in
/-- An equivalence matches the linear morphisms. -/
theorem corresp_linear_groupoid (hD₁ : IsGroupoidBase D₁) (hΦ₁ : NoIrreducible Φ₁)
    (hD₂ : IsGroupoidBase D₂) (hΦ₂ : NoIrreducible Φ₂)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] :
    Corresp F (fun _ _ φ => IsLinear 𝐏₁ φ) (fun _ _ φ => IsLinear 𝐏₂ φ) :=
  ((corresp_isIrreducible F).midAdj isIrreducible_respIso).of_iff
    (fun _ _ φ => isLinear_iff_midAdj hD₁ hΦ₁ φ) (fun _ _ φ => isLinear_iff_midAdj hD₂ hΦ₂ φ)

/-- **[FrdI], Theorem 3.4(iii)** for model Frobenioids over connected groupoid bases whose divisor
monoids have no irreducible elements (e.g. realified Frobenioids). -/
theorem thm34_groupoid (hD₁ : IsGroupoidBase D₁) (hΦ₁ : NoIrreducible Φ₁)
    (hD₂ : IsGroupoidBase D₂) (hΦ₂ : NoIrreducible Φ₂)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] :
    PreservesFrobeniusStructure 𝐏₁ 𝐏₂ F := by
  have cLin := corresp_linear_groupoid hD₁ hΦ₁ hD₂ hΦ₂ F
  have cLin' := corresp_linear_groupoid hD₂ hΦ₂ hD₁ hΦ₁ F.inv
  have cFr : Corresp F (fun _ _ φ => IsFrobeniusType 𝐏₁ φ)
      (fun _ _ φ => IsFrobeniusType 𝐏₂ φ) :=
    (cLin.minCoadj (isLinear_respIso _)).of_iff (fun _ _ φ => isFrobeniusType_iff_minCoadj φ)
      (fun _ _ φ => isFrobeniusType_iff_minCoadj φ)
  obtain ⟨σ, hσ⟩ := exists_degEquiv F (fun _ _ φ h => (cLin φ).1 h)
    (fun _ _ φ h => (cLin' φ).1 h)
  have cCoa : ∀ {A B : Model Φ₁ B₁ divB₁} (φ : A ⟶ B),
      IsCoangular 𝐏₁ φ ↔ IsCoangular 𝐏₂ (F.map φ) :=
    fun φ => ⟨fun _ => isCoangular _, fun _ => isCoangular _⟩
  have cIsom : ∀ {A B : Model Φ₁ B₁ divB₁} (φ : A ⟶ B),
      IsIsometric 𝐏₁ φ ↔ IsIsometric 𝐏₂ (F.map φ) := fun φ => by
    rw [isIsometric_iff_frobType hD₁, isIsometric_iff_frobType hD₂]; exact cFr φ
  refine ⟨fun φ => cFr φ, fun φ => cLin φ, fun φ => ⟨fun _ => hD₂ _, fun _ => hD₁ _⟩, cCoa,
    fun φ => ?_, cIsom, fun φ => and_congr (cCoa φ) (cIsom φ), σ, fun φ => hσ φ⟩
  rw [isPullback_iff_isIso hD₁, isPullback_iff_isIso hD₂]
  exact corresp_isIso F φ

end Main

end Model

/-! ### The global realified Frobenioid -/

namespace GlobalRealified

lemma pt_isGroupoidBase : IsGroupoidBase Pt := fun _ _ f => isIso_pt f

/-- The monoid of effective `ℝ`-arithmetic divisors has no irreducible elements. -/
lemma phiRlf_noIrreducible (K : Type u) [Field K] [NumberField K] :
    NoIrreducible (phiRlf K) := by
  intro _ z hz h0
  have hh : (1 / 2 : ℝ) • z ∈ effCone K := by
    rw [mem_effCone] at hz ⊢
    refine ⟨fun w => ?_, fun v => ?_⟩
    · simp only [Prod.smul_fst, Finsupp.smul_apply, smul_eq_mul]
      exact mul_nonneg (by norm_num) (hz.1 w)
    · simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by norm_num) (hz.2 v)
  have hne : (1 / 2 : ℝ) • z ≠ 0 := by
    rw [Ne, smul_eq_zero, not_or]; exact ⟨by norm_num, h0⟩
  refine ⟨_, hh, _, hh, hne, hne, ?_⟩
  rw [← add_smul]; norm_num

/-- **[FrdI], Theorem 3.4(iii) for the global realified Frobenioids** (IUT I, Example 3.5):
every equivalence `C^⊩(K) ≌ C^⊩(L)` preserves the Frobenius structure. -/
theorem thm34 {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
    (F : GlobalRealified K ⥤ GlobalRealified L) [F.IsEquivalence] :
    PreservesFrobeniusStructure (Model.toElem (phiRlf K) (bRlf K) (divBRlf K))
      (Model.toElem (phiRlf L) (bRlf L) (divBRlf L)) F :=
  Model.thm34_groupoid pt_isGroupoidBase (phiRlf_noIrreducible K) pt_isGroupoidBase
    (phiRlf_noIrreducible L) F

end GlobalRealified

end Frobenioid

end Iut
