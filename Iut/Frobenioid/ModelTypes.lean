/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.ModelFrobenioid
import Iut.Frobenioid.Invariance

/-!
# Category-theoretic characterizations of the morphism types of a model Frobenioid

This file supplies the characterizations used in the proof of [FrdI], Theorem 3.4, for the model
Frobenioids `Model Φ B divB` of [FrdI], Theorem 5.2 (every Frobenioid used in IUT is constructed as
such a model). Each type of morphism is expressed by a property that refers only to the category
structure and to types already characterized, in the order

  FSM-morphisms → pre-steps → base-isomorphisms → pull-back morphisms → linear morphisms →
  morphisms of Frobenius type → isometries.

## Hypotheses

* `BaseHyp D`: the base category `D` is of **FSM-type** (every FSM-morphism is an isomorphism)
  and of **Aut-type** (every endomorphism is an automorphism), [FrdI] §0, p. 14. Both hold for
  the categories `B(G)⁰` of connected objects of a Galois category (`GaloisBase.lean`).
* `HasAllTorsion B`: every group `B(A)` of rational functions contains a nonzero element of
  order dividing `n`, for every `n ≥ 2`. For the Frobenioids of IUT, `B(A)` contains the roots of
  unity `μ(K̄)` (the `p`-adic, archimedean and tempered Frobenioids of [FrdII] and [EtTh] §3).

## Results

* `isPreStep_iff_isFSM`: under both hypotheses, **pre-steps are exactly the FSM-morphisms**. The
  direction "pre-step ⇒ FSM" is [FrdI], Proposition 1.11(vii) (`isFSM_of_isPreStep`, no
  hypotheses). Conversely, a monomorphism of the model has a monomorphic base
  (`mono_base_of_mono`); the torsion of `B` makes every morphism of Frobenius degree `≥ 2`
  non-monomorphic (`deg_eq_one_of_mono`), and an FSM-morphism has an FSM base, hence an
  isomorphic one.
* `isBaseIso_iff_spanOf`: a morphism `X ⟶ Y` is a base-isomorphism iff `X`, `Y` are the
  ends of a span of pre-steps ([FrdI], Definition 1.3(i)(b)); uses Aut-type.
* `isPullback_iff_minAdj`: pull-back morphisms are those minimal-adjoint to the base-isomorphisms
  ([FrdI], Proposition 1.7(ii)).
* `isLinear_iff_compOf`: linear morphisms are the composites (pre-step) ≫ (pull-back)
  ([FrdI], Proposition 1.7(iii)).
* `isFrobeniusType_iff_minCoadj`: morphisms of Frobenius type are those minimal-coadjoint to the
  linear morphisms ([FrdI], Proposition 1.7(iii)).
* `isIsometric_iff_compOf`: isometries are the composites (Frobenius type) ≫ (pull-back).
* `RespIso` for all these classes.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u v' u'

/-! ### Stability of the morphism types under composition with isomorphisms -/

section TotEpi

variable {C : Type u'} [Category.{v'} C] [TotallyEpimorphic C]

/-- In a totally epimorphic category, if `a ≫ b` is an isomorphism, so is `a` ([FrdI] §0). -/
lemma isIso_left_of_isIso_comp {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) [IsIso (a ≫ b)] :
    IsIso a := by
  haveI : IsSplitMono a :=
    IsSplitMono.mk' ⟨b ≫ inv (a ≫ b), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
  haveI := TotallyEpimorphic.epi a
  exact isIso_of_epi_of_isSplitMono a

/-- In a totally epimorphic category, if `a ≫ b` is an isomorphism, so is `b`. -/
lemma isIso_right_of_isIso_comp {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) [IsIso (a ≫ b)] :
    IsIso b := by
  haveI := isIso_left_of_isIso_comp a b
  exact IsIso.of_isIso_comp_left a b

end TotEpi

section General

variable {D : Type u} [Category.{v} D] {Φ : DivMonoid.{w} D}
variable {C : Type u'} [Category.{v'} C] (P : C ⥤ Elem Φ)

lemma isLinear_respIso : RespIso (fun (X Y : C) (φ : X ⟶ Y) => IsLinear P φ) := by
  refine ⟨fun X X' Y e φ h => ?_, fun X Y Y' φ e h => ?_⟩
  · change degFr P (e.hom ≫ φ) = 1
    rw [degFr_comp, degFr_of_isIso e.hom, h, mul_one]
  · change degFr P (φ ≫ e.hom) = 1
    rw [degFr_comp, degFr_of_isIso e.hom, h, mul_one]

lemma isIsometric_respIso : RespIso (fun (X Y : C) (φ : X ⟶ Y) => IsIsometric P φ) := by
  refine ⟨fun X X' Y e φ h => ?_, fun X Y Y' φ e h => ?_⟩
  · change Div P (e.hom ≫ φ) = 0
    have h' : Div P φ = 0 := h
    rw [Div_comp, h', map_zero, Div_of_isIso e.hom, smul_zero, add_zero]
  · change Div P (φ ≫ e.hom) = 0
    have h' : Div P φ = 0 := h
    rw [Div_comp, h', Div_of_isIso e.hom, map_zero, smul_zero, add_zero]

lemma isBaseIso_respIso : RespIso (fun (X Y : C) (φ : X ⟶ Y) => IsBaseIso P φ) := by
  refine ⟨fun X X' Y e φ h => ?_, fun X Y Y' φ e h => ?_⟩
  · haveI : IsIso (Base P φ) := h
    change IsIso (Base P (e.hom ≫ φ))
    rw [Base_comp]; infer_instance
  · haveI : IsIso (Base P φ) := h
    change IsIso (Base P (φ ≫ e.hom))
    rw [Base_comp]; infer_instance

lemma isPreStep_respIso : RespIso (fun (X Y : C) (φ : X ⟶ Y) => IsPreStep P φ) :=
  ⟨fun _ _ _ e φ h => ⟨(isLinear_respIso P).left e φ h.1, (isBaseIso_respIso P).left e φ h.2⟩,
    fun _ _ _ φ e h => ⟨(isLinear_respIso P).right φ e h.1,
      (isBaseIso_respIso P).right φ e h.2⟩⟩

end General

/-! ### Torsion in divisor monoids -/

namespace DivMonoid

variable {D : Type u} [Category.{v} D] (Φ : DivMonoid.{w} D)

/-- `Φ^gp(A)` is torsion-free (sharp and saturated). -/
lemma eq_zero_of_nsmul_eq_zero {A : D} {x : Φ.obj A} {n : ℕ} (hn : 0 < n) (h : n • x = 0) :
    x = 0 := by
  refine Φ.sharp (Φ.saturated n hn (by rw [h]; exact (Φ.pos A).zero_mem))
    (Φ.saturated n hn (by rw [smul_neg, h, neg_zero]; exact (Φ.pos A).zero_mem))

/-- In the sharp monoid `Φ(A)`, a sum of two elements vanishes only if both do. -/
lemma eq_zero_of_add_eq_zero_left {A : D} {x y : Φ.obj A} (hx : x ∈ Φ.pos A) (hy : y ∈ Φ.pos A)
    (h : x + y = 0) : x = 0 :=
  Φ.sharp hx (by rw [eq_neg_of_add_eq_zero_left h, neg_neg]; exact hy)

end DivMonoid

/-! ### Hypotheses -/

/-- **Hypotheses on the base category** ([FrdI] §0, p. 14): `D` is of FSM-type and of
Aut-type. -/
structure BaseHyp (D : Type u) [Category.{v} D] : Prop where
  /-- FSM-type: every FSM-morphism is an isomorphism. -/
  fsm : ∀ ⦃A B : D⦄ (f : A ⟶ B), IsFSM f → IsIso f
  /-- Aut-type: every endomorphism is an automorphism. -/
  aut : ∀ ⦃A : D⦄ (f : A ⟶ A), IsIso f

/-- Every `B(A)` contains a nonzero element killed by `n`, for every `n ≥ 2` (e.g. a primitive
`n`-th root of unity). -/
def HasAllTorsion {D : Type u} [Category.{v} D] (B : GrpOn.{w} D) : Prop :=
  ∀ (A : D) (n : ℕ), 2 ≤ n → ∃ b : B.obj A, b ≠ 0 ∧ n • b = 0

namespace Model

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-! ### Stability of the model-specific types -/

lemma isPullback_respIso :
    RespIso (fun (X Y : Model Φ B divB) (φ : X ⟶ Y) => IsPullback 𝐏 φ) := by
  have h : ∀ {X Y : Model Φ B divB} (φ : X ⟶ Y),
      IsPullback 𝐏 φ ↔ IsLinear 𝐏 φ ∧ IsIsometric 𝐏 φ := fun φ => isPullback_iff φ
  refine ⟨fun X X' Y e φ hφ => ?_, fun X Y Y' φ e hφ => ?_⟩
  · rw [h] at hφ ⊢
    exact ⟨(isLinear_respIso 𝐏).left e φ hφ.1, (isIsometric_respIso 𝐏).left e φ hφ.2⟩
  · rw [h] at hφ ⊢
    exact ⟨(isLinear_respIso 𝐏).right φ e hφ.1, (isIsometric_respIso 𝐏).right φ e hφ.2⟩

lemma isFrobeniusType_respIso :
    RespIso (fun (X Y : Model Φ B divB) (φ : X ⟶ Y) => IsFrobeniusType 𝐏 φ) := by
  have h : ∀ {X Y : Model Φ B divB} (φ : X ⟶ Y),
      IsFrobeniusType 𝐏 φ ↔ IsIsometric 𝐏 φ ∧ IsBaseIso 𝐏 φ := fun φ => isFrobeniusType_iff φ
  refine ⟨fun X X' Y e φ hφ => ?_, fun X Y Y' φ e hφ => ?_⟩
  · rw [h] at hφ ⊢
    exact ⟨(isIsometric_respIso 𝐏).left e φ hφ.1, (isBaseIso_respIso 𝐏).left e φ hφ.2⟩
  · rw [h] at hφ ⊢
    exact ⟨(isIsometric_respIso 𝐏).right φ e hφ.1, (isBaseIso_respIso 𝐏).right φ e hφ.2⟩

/-! ### Pre-steps are FSM-morphisms ([FrdI], Proposition 1.11(vii)) -/

/-- **Pre-steps are fiberwise surjective** ([FrdI], Proposition 1.11(vii)). For a pre-step
`φ : X₀ → A` and `γ : X → A`, put `k = Base(γ) ∘ Base(φ)⁻¹`, `Z' = k^* Div(φ)`; then
`δ_X = (1, id, Z', 0) : (X_D, α_X − Z') → X` and `δ_B = (deg γ, k, Div γ + (deg γ − 1)·Z',
u_γ − k^* u_φ)` satisfy `δ_B ≫ φ = δ_X ≫ γ`. -/
theorem isFiberwiseSurjective_of_isPreStep {X₀ A : Model Φ B divB} (φ : X₀ ⟶ A)
    (hφ : IsPreStep 𝐏 φ) : IsFiberwiseSurjective φ := by
  haveI : IsIso φ.base := hφ.2
  have d : φ.deg = 1 := hφ.1
  intro X γ
  set k := γ.base ≫ inv φ.base with hk
  have hkf : k ≫ φ.base = γ.base := by simp [hk]
  set Z' := Φ.pb k φ.div with hZ'
  have hZ'm : Z' ∈ Φ.pos X.base := Φ.pb_mem _ φ.div_mem
  set m := γ.deg.natPred with hm
  have hmγ : (γ.deg : ℕ) = m + 1 := (PNat.natPred_add_one γ.deg).symm
  let Y : Model Φ B divB := ⟨X.base, X.α - Z'⟩
  let δX : Y ⟶ X := mk1 (𝟙 _) Z' hZ'm 0 (by simp [Y])
  let δB : Y ⟶ X₀ := mk' γ.deg k (γ.div + m • Z')
    ((Φ.pos _).add_mem γ.div_mem ((Φ.pos _).nsmul_mem hZ'm _)) (γ.u - B.pb k φ.u) (by
      have r₁ := γ.rel
      have r₂ := congrArg (Φ.pb k) φ.rel
      rw [d] at r₂
      simp only [PNat.one_coe, one_smul, map_add, ← GrpOn.pb_comp', hkf, ← divB.natural]
        at r₂
      rw [hmγ] at r₁ ⊢
      simp only [Y, map_sub]
      rw [← hZ'] at r₂
      linear_combination (norm := module) r₁ - r₂)
  refine ⟨Y, δB, δX, ?_⟩
  ext
  · simp [δB, δX, d, mul_comm]
  · simp [δB, δX, hkf]
  · simp only [comp_div, δB, δX, mk'_base, mk'_div, mk1_base, mk1_div, d, PNat.one_coe,
      one_smul, GrpOn.pb_id', hmγ, ← hZ']
    rw [add_smul, one_smul]
    abel
  · simp only [comp_u, δB, δX, mk'_base, mk'_u, mk1_base, mk1_u, d, PNat.one_coe, one_smul,
      GrpOn.pb_id', smul_zero, add_zero]
    abel

/-- **Pre-steps are FSM-morphisms** ([FrdI], Proposition 1.11(vii)). -/
theorem isFSM_of_isPreStep {X₀ A : Model Φ B divB} (φ : X₀ ⟶ A) (hφ : IsPreStep 𝐏 φ) :
    IsFSM φ :=
  ⟨preStep_mono φ hφ, isFiberwiseSurjective_of_isPreStep φ hφ⟩

/-! ### FSM-morphisms are pre-steps -/

/-- **A monomorphism of the model has Frobenius degree `1`** when `B` has all torsion: if
`deg φ = n ≥ 2` and `b ∈ B(X)` is nonzero with `n·b = 0`, the automorphism `(1, id, 0, b)` of `X`
is killed by `φ`. -/
theorem deg_eq_one_of_mono (hB : HasAllTorsion B) {X Y : Model Φ B divB} (φ : X ⟶ Y)
    [Mono φ] : φ.deg = 1 := by
  by_contra hne
  have h2 : 2 ≤ (φ.deg : ℕ) := by
    rcases Nat.lt_or_ge (φ.deg : ℕ) 2 with h | h
    · exact absurd (PNat.coe_eq_one_iff.mp (by have := φ.deg.pos; omega)) hne
    · exact h
  obtain ⟨b, hb0, hb⟩ := hB X.base φ.deg h2
  have hdb : divB.app X.base b = 0 :=
    Φ.eq_zero_of_nsmul_eq_zero φ.deg.pos (by rw [← map_nsmul, hb, map_zero])
  let a : X ⟶ X := mk1 (𝟙 _) 0 (Φ.pos _).zero_mem b (by simp [hdb])
  have h : a ≫ φ = 𝟙 X ≫ φ := by
    ext
    · simp [a]
    · simp [a]
    · simp [a]
    · simp [a, hb]
  have := congrArg Hom.u ((cancel_mono φ).mp h)
  exact hb0 (by simpa [a] using this)

/-- **A linear monomorphism of the model has a monomorphic base**: two morphisms
`g, h : T → X_D` with `g ≫ Base φ = h ≫ Base φ` lift to morphisms into `X` with the same
composite with `φ`. -/
theorem mono_base_of_mono {X Y : Model Φ B divB} (φ : X ⟶ Y) [Mono φ] (d : φ.deg = 1) :
    Mono φ.base := by
  refine ⟨fun {T} g h e => ?_⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Φ.generating (Φ.pb h φ.div - Φ.pb g φ.div)
  let τ : Model Φ B divB := ⟨T, Φ.pb g X.α - p⟩
  have r := φ.rel
  rw [d, PNat.one_coe, one_smul] at r
  have rg := congrArg (Φ.pb g) r
  have rh := congrArg (Φ.pb h) r
  simp only [map_add, ← GrpOn.pb_comp', e, ← divB.natural] at rg rh
  let ĝ : τ ⟶ X := mk1 g p hp 0 (by simp [τ])
  let ĥ : τ ⟶ X := mk1 h q hq (B.pb g φ.u - B.pb h φ.u) (by
    simp only [τ, map_sub]
    linear_combination (norm := module) rg - rh + hpq)
  have hc : ĝ ≫ φ = ĥ ≫ φ := by
    ext
    · simp [ĝ, ĥ]
    · simp [ĝ, ĥ, e]
    · simp only [comp_div, ĝ, ĥ, mk1_base, mk1_div, d, PNat.one_coe, one_smul]
      linear_combination (norm := module) -hpq
    · simp [ĝ, ĥ, d]
  simpa [ĝ, ĥ] using congrArg Hom.base ((cancel_mono φ).mp hc)

/-- **A fiberwise-surjective morphism of the model has a fiberwise-surjective base**: lift
`γ : T → Y_D` to the pull-back morphism `(1, γ, 0, 0) : (T, γ^* α_Y) → Y`. -/
theorem isFiberwiseSurjective_base {X Y : Model Φ B divB} (φ : X ⟶ Y)
    (h : IsFiberwiseSurjective φ) : IsFiberwiseSurjective φ.base := by
  intro T γ
  let γl : (⟨T, Φ.pb γ Y.α⟩ : Model Φ B divB) ⟶ Y := mk1 γ 0 (Φ.pos _).zero_mem 0 (by simp)
  obtain ⟨W, δB, δX, hδ⟩ := h γl
  exact ⟨W.base, δB.base, δX.base, by simpa [γl] using congrArg Hom.base hδ⟩

/-- **Pre-steps are exactly the FSM-morphisms** (for an FSM-type base category and `B` with all
torsion). This is the category-theoretic characterization of pre-steps used for [FrdI],
Theorem 3.4(ii). -/
theorem isPreStep_iff_isFSM (hD : BaseHyp D) (hB : HasAllTorsion B) {X Y : Model Φ B divB}
    (φ : X ⟶ Y) : IsPreStep 𝐏 φ ↔ IsFSM φ := by
  refine ⟨isFSM_of_isPreStep φ, fun ⟨hm, hf⟩ => ?_⟩
  haveI := hm
  have d := deg_eq_one_of_mono hB φ
  exact ⟨d, hD.fsm _ ⟨mono_base_of_mono φ d, isFiberwiseSurjective_base φ hf⟩⟩

/-! ### Base-isomorphisms, pull-backs, linear morphisms, Frobenius type, isometries -/

/-- **Base-isomorphisms** are the morphisms whose domain and codomain are the ends of a span of
pre-steps ([FrdI], Definition 1.3(i)(b) for "⇒"; the converse uses that `D` is of Aut-type). -/
theorem isBaseIso_iff_spanOf (hD : BaseHyp D) {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsBaseIso 𝐏 φ ↔ SpanOf (fun _ _ ψ => IsPreStep 𝐏 ψ) X Y := by
  constructor
  · intro h
    haveI : IsIso φ.base := h
    obtain ⟨E, a, b, ha, hb, -⟩ := preStep_span X Y (asIso φ.base)
    exact ⟨E, a, b, ha, hb⟩
  · rintro ⟨E, a, b, ha, hb⟩
    haveI : IsIso a.base := ha.2
    haveI : IsIso b.base := hb.2
    haveI := hD.aut (φ.base ≫ inv b.base ≫ a.base)
    have : φ.base = (φ.base ≫ inv b.base ≫ a.base) ≫ inv a.base ≫ b.base := by simp
    change IsIso φ.base
    rw [this]
    infer_instance

/-- **Pull-back morphisms are those minimal-adjoint to the base-isomorphisms** ([FrdI],
Proposition 1.7(ii)). -/
theorem isPullback_iff_minAdj {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsPullback 𝐏 φ ↔ MinAdj (fun _ _ ψ => IsBaseIso 𝐏 ψ) φ := by
  constructor
  · intro h W a b hab ha
    obtain ⟨h₁, h₀⟩ := (isPullback_iff φ).mp h
    have hdeg := congrArg Hom.deg hab
    have hdiv := congrArg Hom.div hab
    rw [comp_deg, h₁] at hdeg
    rw [comp_div, h₀] at hdiv
    have ha1 : a.deg = 1 := PNat.eq (Nat.eq_one_of_mul_eq_one_left (congrArg PNat.val hdeg))
    have hz : (b.deg : ℕ) • a.div = 0 :=
      Φ.eq_zero_of_add_eq_zero_left ((Φ.pos _).nsmul_mem a.div_mem _)
        (Φ.pb_mem _ b.div_mem) (by rw [add_comm]; exact hdiv)
    exact isIso_of a ha1 ha (Φ.eq_zero_of_nsmul_eq_zero b.deg.pos hz)
  · intro h
    obtain ⟨X', Y', γ, β, α, hγ, hβ, hα, hc⟩ := factorization φ
    have hb : IsBaseIso 𝐏 (γ ≫ β) := by
      haveI : IsIso γ.base := hγ.2
      haveI : IsIso β.base := hβ.2
      change IsIso (γ ≫ β).base
      rw [comp_base]; infer_instance
    haveI := h (γ ≫ β) α (by rw [Category.assoc, hc]) hb
    rw [← hc, ← Category.assoc]
    exact isPullback_respIso.left (asIso (γ ≫ β)) α hα

/-- **Linear morphisms are the composites (pre-step) ≫ (pull-back)** ([FrdI], Proposition
1.7(iii)). -/
theorem isLinear_iff_compOf {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsLinear 𝐏 φ ↔ CompOf (fun _ _ ψ => IsPreStep 𝐏 ψ) (fun _ _ ψ => IsPullback 𝐏 ψ) φ := by
  constructor
  · intro h
    have h' : φ.deg = 1 := h
    refine ⟨⟨X.base, Φ.pb φ.base Y.α⟩, mk1 (𝟙 _) φ.div φ.div_mem φ.u ?_,
      mk1 φ.base 0 (Φ.pos _).zero_mem 0 (by simp), isPreStep_mk1 _ _ _ _ _,
      (isPullback_iff _).mpr ⟨rfl, rfl⟩, ?_⟩
    · simpa [h'] using φ.rel
    · ext <;> simp [h']
  · rintro ⟨W, a, b, ha, hb, rfl⟩
    have h₁ : a.deg = 1 := ha.1
    have h₂ : b.deg = 1 := ((isPullback_iff b).mp hb).1
    change (a ≫ b).deg = 1
    rw [comp_deg, h₁, h₂, mul_one]

/-- **Morphisms of Frobenius type are those minimal-coadjoint to the linear morphisms**
([FrdI], Proposition 1.7(iii)). -/
theorem isFrobeniusType_iff_minCoadj [TotallyEpimorphic D] {X Y : Model Φ B divB}
    (φ : X ⟶ Y) : IsFrobeniusType 𝐏 φ ↔ MinCoadj (fun _ _ ψ => IsLinear 𝐏 ψ) φ := by
  constructor
  · intro h W a b hab hb
    obtain ⟨h₀, hbase⟩ := (isFrobeniusType_iff φ).mp h
    have hb1 : b.deg = 1 := hb
    have hdiv := congrArg Hom.div hab
    rw [comp_div, h₀] at hdiv
    have hz : Φ.pb a.base b.div = 0 :=
      Φ.eq_zero_of_add_eq_zero_left (Φ.pb_mem _ b.div_mem) ((Φ.pos _).nsmul_mem a.div_mem _)
        hdiv
    have hb0 : b.div = 0 := Φ.pb_injective a.base (by rw [hz, map_zero])
    have hbb : IsIso b.base := by
      have hc := congrArg Hom.base hab
      rw [comp_base] at hc
      haveI : IsIso (a.base ≫ b.base) := by rw [hc]; exact hbase
      exact isIso_right_of_isIso_comp a.base b.base
    exact isIso_of b hb1 hbb hb0
  · intro h
    obtain ⟨X', Y', γ, β, α, hγ, hβ, hα, hc⟩ := factorization φ
    have hl : IsLinear 𝐏 (β ≫ α) :=
      (isLinear_iff_compOf _).mpr ⟨Y', β, α, hβ, hα, rfl⟩
    haveI := h γ (β ≫ α) hc hl
    rw [← hc]
    exact isFrobeniusType_respIso.right γ (asIso (β ≫ α)) hγ

/-- **Isometries are the composites (Frobenius type) ≫ (pull-back)**. -/
theorem isIsometric_iff_compOf {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsIsometric 𝐏 φ ↔
      CompOf (fun _ _ ψ => IsFrobeniusType 𝐏 ψ) (fun _ _ ψ => IsPullback 𝐏 ψ) φ := by
  constructor
  · intro h
    have h' : φ.div = 0 := h
    refine ⟨⟨X.base, (φ.deg : ℕ) • X.α⟩, mk' φ.deg (𝟙 _) 0 (Φ.pos _).zero_mem 0 (by simp),
      mk1 φ.base 0 (Φ.pos _).zero_mem φ.u ?_,
      (isFrobeniusType_iff _).mpr ⟨rfl, by simp only [mk'_base]; infer_instance⟩,
      (isPullback_iff _).mpr ⟨rfl, rfl⟩, ?_⟩
    · simpa [h'] using φ.rel
    · ext <;> simp [h']
  · rintro ⟨W, a, b, ha, hb, rfl⟩
    have h₁ : a.div = 0 := ((isFrobeniusType_iff a).mp ha).1
    have h₂ : b.div = 0 := ((isPullback_iff b).mp hb).2
    change (a ≫ b).div = 0
    rw [comp_div, h₁, h₂, map_zero, smul_zero, add_zero]

end Model

end Frobenioid

end Iut
