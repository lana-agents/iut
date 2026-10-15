/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.ModelTypes
import Iut.Frobenioid.Theoreticity

/-!
# [FrdI], Theorem 3.4(ii), (iii) for model Frobenioids

**Theorem** (`Model.thm34_preservesFrobeniusStructure`). Let `C₁ = Model Φ₁ B₁ divB₁`,
`C₂ = Model Φ₂ B₂ divB₂` be model Frobenioids ([FrdI], Theorem 5.2) over connected, totally
epimorphic base categories `D₁`, `D₂` of FSM-type and of Aut-type (`BaseHyp`), with rational
function monoids having torsion of every order (`HasAllTorsion`). Then every equivalence of
categories `F : C₁ ≌ C₂` preserves and reflects morphisms of Frobenius type, linear morphisms,
base-isomorphisms, co-angular morphisms, pull-back morphisms, isometries and LB-invertible
morphisms, and there is an automorphism `σ` of the monoid `ℕ_{≥1}` with
`degFr(F φ) = σ(degFr φ)`: this is the conclusion `PreservesFrobeniusStructure` of [FrdI],
Theorem 3.4(iii). Also pre-steps are preserved (Theorem 3.4(ii)).

## Proof

The types are characterized category-theoretically in `ModelTypes.lean` (pre-steps are the
FSM-morphisms, etc.) and these characterizations are transported by `F` (`Invariance.lean`).

For the Frobenius degree: if `λ : X → Y` is linear and `γ`, `δ` are morphisms of Frobenius type
of the same degree out of `X`, `Y`, there is a linear `λ'` with `γ ≫ λ' = λ ≫ δ` ([FrdI],
Proposition 1.10(i), `exists_linear_square`); since `F` preserves linear morphisms,
`degFr(F γ) = degFr(F δ)`. All objects are connected by linear morphisms (pre-steps to `(A, 0)`,
and the zero section of the connected base), so `σ(n) := degFr(F γ)` for any `γ` of Frobenius
type and degree `n` is well defined; it is multiplicative, and bijective because the same
construction for a quasi-inverse gives its inverse.

## Remark on the route

[FrdI] derives Theorem 3.4(ii) from Proposition 1.14(ii), (iii) (pre-steps via FSMI-chains);
`Iut/Frobenioid/Counterexample.lean` shows that Proposition 1.14(iii) fails for model
Frobenioids whose `B` has torsion of every order, which is the case for the Frobenioids of IUT.
The characterization "pre-step = FSM-morphism" used here holds exactly in that case.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace Model

section Square

variable {D : Type u₁} [Category.{v₁} D]
variable {Φ : DivMonoid.{w₁} D} {B : GrpOn.{w₁} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-- **[FrdI], Proposition 1.10(i)** for linear `λ`: given morphisms of Frobenius type `γ : X → X'`,
`δ : Y → Y'` of the same degree and a linear `λ : X → Y`, there is a linear `λ' : X' → Y'` with
`γ ≫ λ' = λ ≫ δ`. -/
theorem exists_linear_square {X X' Y Y' : Model Φ B divB} (γ : X ⟶ X') (δ : Y ⟶ Y')
    (lam : X ⟶ Y) (hγ : IsFrobeniusType 𝐏 γ) (hδ : IsFrobeniusType 𝐏 δ) (hd : γ.deg = δ.deg)
    (hl : IsLinear 𝐏 lam) : ∃ lam' : X' ⟶ Y', IsLinear 𝐏 lam' ∧ γ ≫ lam' = lam ≫ δ := by
  obtain ⟨hγ0, hγb⟩ := (isFrobeniusType_iff γ).mp hγ
  obtain ⟨hδ0, -⟩ := (isFrobeniusType_iff δ).mp hδ
  haveI : IsIso γ.base := hγb
  have hl1 : lam.deg = 1 := hl
  set n : ℕ := (δ.deg : ℕ) with hn
  have rγ := γ.rel
  have rδ := δ.rel
  have rl := lam.rel
  rw [hγ0, hd, ← hn] at rγ
  rw [hδ0, ← hn] at rδ
  rw [hl1, PNat.one_coe, one_smul] at rl
  let lam' : X' ⟶ Y' := mk1 (inv γ.base ≫ lam.base ≫ δ.base) (Φ.pb (inv γ.base) (n • lam.div))
    (Φ.pb_mem _ ((Φ.pos _).nsmul_mem lam.div_mem _))
    (B.pb (inv γ.base) (B.pb lam.base δ.u + n • lam.u - γ.u)) (by
      apply Φ.pb_injective γ.base
      have rδ' := congrArg (Φ.pb lam.base) rδ
      simp only [map_add, map_nsmul, add_zero, ← divB.natural] at rδ' rγ
      simp only [map_add, map_sub, map_nsmul, ← divB.natural, GrpOn.pb_pb_inv]
      simp only [GrpOn.pb_comp', GrpOn.pb_pb_inv] at rδ' ⊢
      linear_combination (norm := module) (n • rl) - rγ + rδ')
  refine ⟨lam', rfl, ?_⟩
  ext
  · simp [lam', hd, hl1]
  · simp [lam']
  · simp [lam', hγ0, hδ0, hn]
  · simp only [comp_u, lam', mk1_u, mk1_deg, PNat.one_coe, one_smul,
      GrpOn.pb_pb_inv, hn]
    abel

end Square

/-! ### The induced automorphism of `ℕ_{≥1}` -/

section Degree

variable {D₁ : Type u₁} [Category.{v₁} D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

/-- The canonical morphism of Frobenius type `(n, id, 0, 0) : (A, α) → (A, n·α)`. -/
def frob (X : Model Φ₁ B₁ divB₁) (n : ℕ+) : X ⟶ ⟨X.base, (n : ℕ) • X.α⟩ :=
  mk' n (𝟙 _) 0 (Φ₁.pos _).zero_mem 0 (by simp)

lemma frob_isFrobeniusType (X : Model Φ₁ B₁ divB₁) (n : ℕ+) :
    IsFrobeniusType 𝐏₁ (frob X n) :=
  (isFrobeniusType_iff _).mpr ⟨rfl, by simp only [frob, mk'_base]; infer_instance⟩

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂)
variable (hlin : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y), IsLinear (toElem Φ₁ B₁ divB₁) φ →
  IsLinear (toElem Φ₂ B₂ divB₂) (F.map φ))

include hlin

/-- The degrees of the images of morphisms of Frobenius type of a given degree agree along a
linear morphism. -/
lemma deg_map_eq_of_linear {X X' Y Y' : Model Φ₁ B₁ divB₁} (γ : X ⟶ X') (δ : Y ⟶ Y')
    (lam : X ⟶ Y) (hγ : IsFrobeniusType 𝐏₁ γ) (hδ : IsFrobeniusType 𝐏₁ δ) (hd : γ.deg = δ.deg)
    (hl : IsLinear 𝐏₁ lam) : degFr 𝐏₂ (F.map γ) = degFr 𝐏₂ (F.map δ) := by
  obtain ⟨lam', hl', hsq⟩ := exists_linear_square γ δ lam hγ hδ hd hl
  have h := congrArg (fun φ => degFr 𝐏₂ (F.map φ)) hsq
  simp only [F.map_comp, degFr_comp] at h
  rwa [hlin _ hl', hlin _ hl, one_mul, mul_one] at h

/-- The degree of the image of the canonical Frobenius morphism is the same at all objects
(the objects are connected by linear morphisms). -/
lemma deg_map_frob_eq [IsConnected D₁] (n : ℕ+) (X Y : Model Φ₁ B₁ divB₁) :
    degFr 𝐏₂ (F.map (frob X n)) = degFr 𝐏₂ (F.map (frob Y n)) := by
  have step : ∀ (X Y : Model Φ₁ B₁ divB₁) (lam : X ⟶ Y), IsLinear 𝐏₁ lam →
      degFr 𝐏₂ (F.map (frob X n)) = degFr 𝐏₂ (F.map (frob Y n)) := fun X Y lam hl =>
    deg_map_eq_of_linear F hlin _ _ lam (frob_isFrobeniusType X n) (frob_isFrobeniusType Y n)
      rfl hl
  have toZero : ∀ X : Model Φ₁ B₁ divB₁, degFr 𝐏₂ (F.map (frob X n)) =
      degFr 𝐏₂ (F.map (frob (zeroObj Φ₁ B₁ divB₁ X.base) n)) := by
    intro X
    obtain ⟨p, hp, q, hq, he⟩ := Φ₁.generating X.α
    let E : Model Φ₁ B₁ divB₁ := ⟨X.base, -q⟩
    let f₁ : E ⟶ X := mk1 (𝟙 _) p hp 0 (by simp [E, he]; abel)
    let f₂ : E ⟶ zeroObj Φ₁ B₁ divB₁ X.base := mk1 (𝟙 _) q hq 0 (by simp [E])
    exact (step E X f₁ rfl).symm.trans (step E _ f₂ rfl)
  have hz : ∀ A : D₁, degFr 𝐏₂ (F.map (frob (zeroObj Φ₁ B₁ divB₁ A) n)) =
      degFr 𝐏₂ (F.map (frob (zeroObj Φ₁ B₁ divB₁ Y.base) n)) := fun A =>
    (isPreconnected_induction
      (fun A : D₁ => degFr 𝐏₂ (F.map (frob (zeroObj Φ₁ B₁ divB₁ A) n)) =
        degFr 𝐏₂ (F.map (frob (zeroObj Φ₁ B₁ divB₁ Y.base) n)))
      (fun f h => (step _ _ ((zeroSection Φ₁ B₁ divB₁).map f) rfl).symm.trans h)
      (fun f h => (step _ _ ((zeroSection Φ₁ B₁ divB₁).map f) rfl).trans h) rfl A).some
  rw [toZero X, toZero Y]
  exact hz _

/-- Any morphism of Frobenius type of degree `n` has the same image degree as `frob X n`. -/
lemma deg_map_frobType {X X' : Model Φ₁ B₁ divB₁} (γ : X ⟶ X') (hγ : IsFrobeniusType 𝐏₁ γ) :
    degFr 𝐏₂ (F.map γ) = degFr 𝐏₂ (F.map (frob X γ.deg)) :=
  deg_map_eq_of_linear F hlin γ (frob X γ.deg) (𝟙 X) hγ (frob_isFrobeniusType X _) rfl
    (by simp [IsLinear])

/-- **The degree homomorphism** `σ : ℕ_{≥1} → ℕ_{≥1}` of a functor preserving linear morphisms:
`degFr(F φ) = σ(degFr φ)` for every `φ`. -/
theorem exists_degHom [IsConnected D₁] :
    ∃ σ : ℕ+ →* ℕ+, ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y),
      degFr 𝐏₂ (F.map φ) = σ (degFr 𝐏₁ φ) := by
  let X₀ : Model Φ₁ B₁ divB₁ := zeroObj Φ₁ B₁ divB₁ (Classical.arbitrary D₁)
  let s : ℕ+ → ℕ+ := fun n => degFr 𝐏₂ (F.map (frob X₀ n))
  have hs : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y), degFr 𝐏₂ (F.map φ) = s (degFr 𝐏₁ φ) := by
    intro X Y φ
    obtain ⟨X', Y', γ, β, α, hγ, hβ, hα, hc⟩ := factorization φ
    have hl : IsLinear 𝐏₁ (β ≫ α) := (isLinear_iff_compOf _).mpr ⟨Y', β, α, hβ, hα, rfl⟩
    have hlF := hlin _ hl
    have hdeg : degFr 𝐏₁ φ = γ.deg := by
      rw [← hc, degFr_comp, hl, one_mul]
      rfl
    rw [hdeg, ← hc, F.map_comp, degFr_comp, hlF, one_mul]
    change degFr 𝐏₂ (F.map γ) = degFr 𝐏₂ (F.map (frob X₀ γ.deg))
    rw [deg_map_frobType F hlin γ hγ]
    exact deg_map_frob_eq F hlin γ.deg X X₀
  refine ⟨⟨⟨s, ?_⟩, fun m n => ?_⟩, hs⟩
  · change degFr 𝐏₂ (F.map (frob X₀ 1)) = 1
    rw [deg_map_eq_of_linear F hlin (frob X₀ 1) (𝟙 X₀) (𝟙 X₀) (frob_isFrobeniusType X₀ 1)
      ((isFrobeniusType_iff _).mpr ⟨rfl, by simp only [id_base]; infer_instance⟩) rfl
      (by simp [IsLinear])]
    simp
  · change s (m * n) = s m * s n
    have h := hs (frob X₀ n ≫ frob _ m)
    rw [F.map_comp, degFr_comp, hs, hs] at h
    exact h.symm

end Degree

/-! ### The theorem -/

section Main

variable {D₁ : Type u₁} [Category.{v₁} D₁] [IsConnected D₁] [TotallyEpimorphic D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂] [IsConnected D₂] [TotallyEpimorphic D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

/-- The correspondences of morphism types under an equivalence of model Frobenioids. -/
structure TypeCorresp (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) : Prop where
  preStep : Corresp F (fun _ _ φ => IsPreStep 𝐏₁ φ) (fun _ _ φ => IsPreStep 𝐏₂ φ)
  baseIso : Corresp F (fun _ _ φ => IsBaseIso 𝐏₁ φ) (fun _ _ φ => IsBaseIso 𝐏₂ φ)
  pullback : Corresp F (fun _ _ φ => IsPullback 𝐏₁ φ) (fun _ _ φ => IsPullback 𝐏₂ φ)
  linear : Corresp F (fun _ _ φ => IsLinear 𝐏₁ φ) (fun _ _ φ => IsLinear 𝐏₂ φ)
  frobType : Corresp F (fun _ _ φ => IsFrobeniusType 𝐏₁ φ) (fun _ _ φ => IsFrobeniusType 𝐏₂ φ)
  isometric : Corresp F (fun _ _ φ => IsIsometric 𝐏₁ φ) (fun _ _ φ => IsIsometric 𝐏₂ φ)

omit [IsConnected D₁] [IsConnected D₂] in
/-- **[FrdI], Theorem 3.4(ii), (iii) (types)** for model Frobenioids: an equivalence matches
pre-steps, base-isomorphisms, pull-backs, linear morphisms, morphisms of Frobenius type and
isometries. -/
theorem typeCorresp (hD₁ : BaseHyp D₁) (hB₁ : HasAllTorsion B₁) (hD₂ : BaseHyp D₂)
    (hB₂ : HasAllTorsion B₂) (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] :
    TypeCorresp F := by
  have cPre : Corresp F (fun _ _ φ => IsPreStep 𝐏₁ φ) (fun _ _ φ => IsPreStep 𝐏₂ φ) :=
    (corresp_isFSM F).of_iff (fun _ _ φ => isPreStep_iff_isFSM hD₁ hB₁ φ)
      (fun _ _ φ => isPreStep_iff_isFSM hD₂ hB₂ φ)
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

/-- **[FrdI], Theorem 3.4(iii)** for model Frobenioids over base categories of FSM- and
Aut-type whose rational function monoids have torsion of every order (the Frobenioids of IUT):
every equivalence of categories preserves the Frobenius structure. -/
theorem thm34_preservesFrobeniusStructure (hD₁ : BaseHyp D₁) (hB₁ : HasAllTorsion B₁)
    (hD₂ : BaseHyp D₂) (hB₂ : HasAllTorsion B₂) (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂)
    [F.IsEquivalence] : PreservesFrobeniusStructure 𝐏₁ 𝐏₂ F := by
  have c := typeCorresp hD₁ hB₁ hD₂ hB₂ F
  have c' := typeCorresp hD₂ hB₂ hD₁ hB₁ F.inv
  obtain ⟨σ, hσ⟩ := exists_degHom F (fun _ _ φ h => (c.linear φ).1 h)
  obtain ⟨τ, hτ⟩ := exists_degHom F.inv (fun _ _ φ h => (c'.linear φ).1 h)
  have hτσ : ∀ n, τ (σ n) = n := by
    intro n
    let X₀ : Model Φ₁ B₁ divB₁ := zeroObj Φ₁ B₁ divB₁ (Classical.arbitrary D₁)
    have h := congrArg (degFr 𝐏₁) (F.asEquivalence.unitIso.hom.naturality (frob X₀ n))
    simp only [degFr_comp, degFr_of_isIso, Functor.id_map, Functor.comp_map, one_mul,
      mul_one] at h
    have h' := hτ (F.map (frob X₀ n))
    rw [hσ] at h'
    exact h'.symm.trans h.symm
  have hστ : ∀ n, σ (τ n) = n := by
    intro n
    let Y₀ : Model Φ₂ B₂ divB₂ := zeroObj Φ₂ B₂ divB₂ (Classical.arbitrary D₂)
    have h := congrArg (degFr 𝐏₂) (F.asEquivalence.counitIso.hom.naturality (frob Y₀ n))
    simp only [degFr_comp, degFr_of_isIso, Functor.id_map, Functor.comp_map, one_mul,
      mul_one] at h
    have h' := hσ (F.inv.map (frob Y₀ n))
    rw [hτ] at h'
    exact h'.symm.trans h
  let e : ℕ+ ≃* ℕ+ :=
    { toFun := σ, invFun := τ, left_inv := hτσ, right_inv := hστ, map_mul' := σ.map_mul }
  have cCoa : ∀ {A B : Model Φ₁ B₁ divB₁} (φ : A ⟶ B),
      IsCoangular 𝐏₁ φ ↔ IsCoangular 𝐏₂ (F.map φ) :=
    fun φ => ⟨fun _ => isCoangular _, fun _ => isCoangular _⟩
  refine ⟨fun φ => c.frobType φ, fun φ => c.linear φ, fun φ => c.baseIso φ, cCoa,
    fun φ => c.pullback φ, fun φ => c.isometric φ, fun φ => and_congr (cCoa φ) (c.isometric φ),
    e, fun φ => hσ φ⟩

end Main

end Model

end Frobenioid

end Iut
