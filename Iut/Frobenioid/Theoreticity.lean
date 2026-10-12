/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Wall

/-!
# Category-theoreticity ([FrdI], Theorem 3.4, Corollary 4.11)

[FrdI], Theorem 3.4 (iii): for Frobenioids `C₁, C₂` of *standard type* (and slim base
categories), every equivalence of categories `Ψ : C₁ ≅ C₂` preserves morphisms of Frobenius
type, linear morphisms, base-isomorphisms, co-angular morphisms, pull-back morphisms,
isometries and LB-invertible morphisms, and there is an automorphism `Ψ_{ℕ≥1}` of the monoid
`ℕ_{≥1}` with `degFr(Ψ(φ)) = Ψ_{ℕ≥1}(degFr(φ))`; (v): `Ψ` induces an equivalence
`Ψ_Base : D₁ ≅ D₂` of base categories; Corollary 4.11: also the divisor monoids are preserved.

## Status

* **Statements.** `PreservesFrobeniusStructure P₁ P₂ F` is the conclusion of Theorem 3.4(iii) for
  a functor `F : C₁ ⥤ C₂` (applied to `Ψ.functor`), `PreservesBase P₁ P₂ F` that of (v)
  (a functor `D₁ ⥤ D₂` with `F ⋙ Base₂ ≅ Base₁ ⋙ Ψ_Base`). The *theorem* that every equivalence
  between Frobenioids of standard type satisfies them is **research-level** for this
  formalisation: its proof in [FrdI] uses Propositions 1.4–1.14, 3.2, 3.3 (characterizations of
  isotropic objects via iso-subanchors, of pre-steps via FSMFF-type base categories, of
  Frobenius-type morphisms via Frobenius-compact objects, …) and is not attempted. The notions
  "standard type", "FSMFF-type", "slim", "non-dilating", "iso-subanchor" are not formalised.
* **Proved.**
  * `scale_preserves`: the `ℝ_{>0}`-scalings of the global realified Frobenioid satisfy the
    conclusion of Theorem 3.4(iii) (with `Ψ_{ℕ≥1} = id`) and (v) (with `Ψ_Base = id`); by
    `GlobalRealified.degree_scale` they multiply the degree by the scale, which is the content
    of [FrdI], Theorem 6.4(ii) (`deg(Ψ^rlf) ∈ ℝ_{>0}`) for scalings.
  * `endZeroEquiv`: in the global realified Frobenioid, the endomorphism monoid of the
    Frobenius-trivial object `(pt, 0)` is `ℕ_{≥1}` via the Frobenius degree (effective divisors
    of degree `0` vanish, `eq_zero_of_degArith_eq_zero`). Hence the Frobenius degree on the
    Frobenius-trivial objects is recovered from the category structure up to an automorphism of
    `ℕ_{≥1}`: `inducedDegAut` is the automorphism `Ψ_{ℕ≥1}` induced by any functor that maps
    `(pt, 0)` to an object isomorphic to it and is bijective on its endomorphisms
    (`inducedDegAut_spec`).
  * the model-level characterizations used in [FrdI] §3 are in `Iut/Frobenioid/Model.lean`
    (`Model.isIso_iff`, `Model.isPullback_iff`, every morphism co-angular, every object
    isotropic) and `ModelFrobenioid.lean` (`Model.nonempty_iso_iff`: `Pic_C = Pic_Φ`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory Arakelov

universe w₁ w₂ v₁ v₂ u₁ u₂ v₁' v₂' u₁' u₂'

section Statements

variable {D₁ : Type u₁} [Category.{v₁} D₁] {Φ₁ : DivMonoid.{w₁} D₁}
  {C₁ : Type u₁'} [Category.{v₁'} C₁] (P₁ : C₁ ⥤ Elem Φ₁)
  {D₂ : Type u₂} [Category.{v₂} D₂] {Φ₂ : DivMonoid.{w₂} D₂}
  {C₂ : Type u₂'} [Category.{v₂'} C₂] (P₂ : C₂ ⥤ Elem Φ₂)

/-- **The conclusion of [FrdI], Theorem 3.4(iii)** for a functor `F : C₁ ⥤ C₂`: `F` preserves
(and reflects) the morphism types, and the Frobenius degree up to an automorphism of
`ℕ_{≥1}`. -/
def PreservesFrobeniusStructure (F : C₁ ⥤ C₂) : Prop :=
  (∀ {A B : C₁} (φ : A ⟶ B), IsFrobeniusType P₁ φ ↔ IsFrobeniusType P₂ (F.map φ)) ∧
  (∀ {A B : C₁} (φ : A ⟶ B), IsLinear P₁ φ ↔ IsLinear P₂ (F.map φ)) ∧
  (∀ {A B : C₁} (φ : A ⟶ B), IsBaseIso P₁ φ ↔ IsBaseIso P₂ (F.map φ)) ∧
  (∀ {A B : C₁} (φ : A ⟶ B), IsCoangular P₁ φ ↔ IsCoangular P₂ (F.map φ)) ∧
  (∀ {A B : C₁} (φ : A ⟶ B), IsPullback P₁ φ ↔ IsPullback P₂ (F.map φ)) ∧
  (∀ {A B : C₁} (φ : A ⟶ B), IsIsometric P₁ φ ↔ IsIsometric P₂ (F.map φ)) ∧
  (∀ {A B : C₁} (φ : A ⟶ B), IsLBInvertible P₁ φ ↔ IsLBInvertible P₂ (F.map φ)) ∧
  ∃ σ : ℕ+ ≃* ℕ+, ∀ {A B : C₁} (φ : A ⟶ B), degFr P₂ (F.map φ) = σ (degFr P₁ φ)

/-- **The conclusion of [FrdI], Theorem 3.4(v)**: a functor of base categories compatible with
`F` up to isomorphism. -/
def PreservesBase (F : C₁ ⥤ C₂) : Prop :=
  ∃ G : D₁ ⥤ D₂, Nonempty (F ⋙ P₂ ⋙ Elem.proj ≅ (P₁ ⋙ Elem.proj) ⋙ G)

end Statements

/-! ### Scalings of the global realified Frobenioid -/

namespace GlobalRealified

variable {K : Type*} [Field K] [NumberField K]

local notation "𝐏" => Model.toElem (phiRlf K) (bRlf K) (divBRlf K)

lemma scale_map_deg (c : ℝ) (hc : 0 < c) {X Y : GlobalRealified K} (φ : X ⟶ Y) :
    ((scale c hc).map φ).deg = φ.deg := rfl

lemma scale_map_base (c : ℝ) (hc : 0 < c) {X Y : GlobalRealified K} (φ : X ⟶ Y) :
    ((scale c hc).map φ).base = φ.base := rfl

lemma scale_map_div (c : ℝ) (hc : 0 < c) {X Y : GlobalRealified K} (φ : X ⟶ Y) :
    ((scale c hc).map φ).div = c • φ.div := rfl

lemma smul_eq_zero_iff' (c : ℝ) (hc : 0 < c) (x : ArithDiv K) : c • x = 0 ↔ x = 0 := by
  rw [smul_eq_zero, or_iff_right hc.ne']

/-- **The scalings preserve the Frobenioid structure** ([FrdI], Theorem 3.4(iii), with
`Ψ_{ℕ≥1} = id`). -/
theorem scale_preserves (c : ℝ) (hc : 0 < c) :
    PreservesFrobeniusStructure 𝐏 𝐏 (scale (K := K) c hc) := by
  have hiso : ∀ {X Y : GlobalRealified K} (φ : X ⟶ Y),
      IsBaseIso 𝐏 φ ↔ IsBaseIso 𝐏 ((scale c hc).map φ) := fun _ => Iff.rfl
  have hiso0 : ∀ {X Y : GlobalRealified K} (φ : X ⟶ Y),
      IsIsometric 𝐏 φ ↔ IsIsometric 𝐏 ((scale c hc).map φ) := fun φ =>
    (smul_eq_zero_iff' c hc φ.div).symm
  refine ⟨fun φ => ?_, fun _ => Iff.rfl, hiso, fun φ => ⟨fun _ => Model.isCoangular _,
    fun _ => Model.isCoangular _⟩, fun φ => ?_, hiso0, fun φ => ?_, MulEquiv.refl _,
    fun _ => rfl⟩
  · rw [Model.isFrobeniusType_iff, Model.isFrobeniusType_iff]
    exact and_congr (hiso0 φ) Iff.rfl
  · rw [Model.isPullback_iff, Model.isPullback_iff]
    exact and_congr Iff.rfl (hiso0 φ)
  · exact and_congr ⟨fun _ => Model.isCoangular _, fun _ => Model.isCoangular _⟩ (hiso0 φ)

/-- The scalings lie over the identity of the base category ([FrdI], Theorem 3.4(v)). -/
theorem scale_preservesBase (c : ℝ) (hc : 0 < c) :
    PreservesBase 𝐏 𝐏 (scale (K := K) c hc) :=
  ⟨𝟭 _, ⟨Iso.refl _⟩⟩

/-! ### The endomorphisms of `(pt, 0)` -/

/-- An effective ℝ-divisor of arithmetic degree `0` vanishes. -/
theorem eq_zero_of_degArith_eq_zero {x : ArithDiv K} (hx : x ∈ effCone K)
    (h : degArith K x = 0) : x = 0 := by
  rw [degArith_apply] at h
  have h₁ : ∀ w ∈ x.1.support, 0 ≤ x.1 w * Real.log (primeNorm w) := fun w _ =>
    mul_nonneg (hx.1 w) (Real.log_pos (one_lt_primeNorm w)).le
  have h₂ : ∀ v ∈ (Finset.univ : Finset (NumberField.InfinitePlace K)),
      0 ≤ (v.mult : ℝ) * x.2 v := fun v _ =>
    mul_nonneg (by exact_mod_cast (Nat.zero_le _)) (hx.2 v)
  have hs₁ := Finset.sum_nonneg h₁
  have hs₂ := Finset.sum_nonneg h₂
  rw [Finsupp.sum] at h
  have e₁ : ∑ w ∈ x.1.support, x.1 w * Real.log (primeNorm w) = 0 := by linarith
  have e₂ : ∑ v, (v.mult : ℝ) * x.2 v = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg h₁] at e₁
  rw [Finset.sum_eq_zero_iff_of_nonneg h₂] at e₂
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · by_cases hw : w ∈ x.1.support
    · have := e₁ w hw
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (Real.log_pos (one_lt_primeNorm w)).ne'
    · simpa using hw
  · have := e₂ v (Finset.mem_univ v)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by exact_mod_cast v.mult_pos.ne')
    · exact h

/-- The Frobenius-trivial object `(pt, 0)`. -/
noncomputable abbrev zero : GlobalRealified K := Model.zeroObj _ _ _ pt

lemma endo_div_eq_zero (e : (zero : GlobalRealified K) ⟶ zero) : e.div = 0 := by
  have r := e.rel
  change (e.deg : ℕ) • (0 : ArithDiv K) + e.div = 0 + (e.u : ArithDiv K) at r
  simp only [smul_zero, zero_add] at r
  refine eq_zero_of_degArith_eq_zero e.div_mem ?_
  rw [r]
  exact degArith_ratFun e.u.2

lemma endo_u_eq_zero (e : (zero : GlobalRealified K) ⟶ zero) : e.u = 0 := by
  have r := e.rel
  change (e.deg : ℕ) • (0 : ArithDiv K) + e.div = 0 + (e.u : ArithDiv K) at r
  simp only [smul_zero, zero_add, endo_div_eq_zero e] at r
  exact Subtype.ext r.symm

/-- The endomorphism `(n, id, 0, 0)` of `(pt, 0)`. -/
noncomputable def frobZero (n : ℕ+) : (zero : GlobalRealified K) ⟶ zero :=
  Model.mk' n (𝟙 _) 0 (effCone K).zero_mem 0 (by
    change (n : ℕ) • (0 : ArithDiv K) + 0 = 0 + ((0 : ratFun K) : ArithDiv K)
    simp)

/-- **`End_{C^⊩}((pt, 0)) ≅ ℕ_{≥1}`** via the Frobenius degree: on Frobenius-trivial objects,
the Frobenius degree is determined by the category structure up to `Aut(ℕ_{≥1})`. -/
noncomputable def endZeroEquiv : End (zero : GlobalRealified K) ≃* ℕ+ where
  toFun e := degFr 𝐏 e
  invFun n := frobZero n
  left_inv e := by
    refine Model.hom_ext rfl (Subsingleton.elim _ _) ?_ ?_
    · exact (endo_div_eq_zero e).symm
    · exact (endo_u_eq_zero e).symm
  right_inv n := rfl
  map_mul' e f := by
    change degFr 𝐏 (f ≫ e) = degFr 𝐏 e * degFr 𝐏 f
    rw [degFr_comp]

/-- Conjugation of the endomorphisms of `(pt, 0)` by a functor `F` and `i : F(pt, 0) ≅ (pt, 0)`.
-/
noncomputable def conjHom (F : GlobalRealified K ⥤ GlobalRealified K) (i : F.obj zero ≅ zero) :
    End (zero : GlobalRealified K) →* End (zero : GlobalRealified K) where
  toFun e := i.inv ≫ F.map e ≫ i.hom
  map_one' := by
    change i.inv ≫ F.map (𝟙 _) ≫ i.hom = 𝟙 _
    simp
  map_mul' e f := by
    change i.inv ≫ F.map (f ≫ e) ≫ i.hom = (i.inv ≫ F.map f ≫ i.hom) ≫ i.inv ≫
      F.map e ≫ i.hom
    simp

/-- **The automorphism `Ψ_{ℕ≥1}`** induced by a functor `F` with `F(pt, 0) ≅ (pt, 0)` which is
bijective on endomorphisms of `(pt, 0)` ([FrdI], Theorem 3.4(iii)). -/
noncomputable def inducedDegAut (F : GlobalRealified K ⥤ GlobalRealified K)
    (i : F.obj zero ≅ zero) (hF : Function.Bijective (conjHom F i)) : ℕ+ ≃* ℕ+ :=
  (endZeroEquiv.symm.trans (MulEquiv.ofBijective (conjHom F i) hF)).trans endZeroEquiv

/-- `degFr(F(e)) = Ψ_{ℕ≥1}(degFr(e))` on the endomorphisms of `(pt, 0)`. -/
lemma inducedDegAut_spec (F : GlobalRealified K ⥤ GlobalRealified K) (i : F.obj zero ≅ zero)
    (hF : Function.Bijective (conjHom F i)) (e : End (zero : GlobalRealified K)) :
    degFr 𝐏 (i.inv ≫ F.map e ≫ i.hom) = inducedDegAut F i hF (degFr 𝐏 e) := by
  change _ = degFr 𝐏 (conjHom F i (endZeroEquiv.symm (endZeroEquiv e)))
  rw [MulEquiv.symm_apply_apply]
  rfl

end GlobalRealified

end Frobenioid

end Iut
