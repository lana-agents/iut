/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.RecPoints

/-!
# Isomorphisms of triples from the valuations (MR9 item 4, step 5)

An isomorphism of the triples of [AbsTopIII] Prop 1.3 (a)–(c) (`Uchida.ValEvalData.Iso`) consists
of a group isomorphism `φ`, a bijection `σ` of the points, and the compatibilities with `ord_x` and
`U_x`. For triples whose points are determined by their valuations (as for function fields:
`Uchida.ofFunctionField.val_injective`, a function with its only zero at `Q`), the bijection `σ` is
determined by `φ`: `σ x` is the point `x'` with `ord_{x'} ∘ φ = ord_x`. Here:

* **`Uchida.ofFunctionField.val_injective`**: distinct places have distinct valuations;
* `Uchida.ofFunctionField.val_eq_zero_of_mem_U` (`U_P ⊆ Ker(ord_P)`); the Prop-valued defs
  `ValInjective`, `UInKer` and their transport along isomorphisms of triples;
* **`Uchida.ValEvalData.Iso.ofVal`**: a group isomorphism `φ` for which every point on either side
  has a partner with the same valuations along `φ`, and which respects `U_x` for partners, is an
  isomorphism of triples;
* `Thm19.recTriple_valInjective`, `Thm19.recTriple_uInKer`: the two properties for the
  reconstructed triple `recTriple N hkF`.
-/

open WeilCurves.FunctionField

universe u

noncomputable section

namespace Iut.Reconstruction

namespace Uchida

namespace ofFunctionField

variable {k : Type*} {K : Type u} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  [IsFunctionField k K]

/-- **Distinct places of a function field have distinct valuations** (a function whose only zero is
`Q`, weil-curves `exists_zero_only_at`). -/
theorem val_injective {P Q : Place k K}
    (h : ∀ f : Kˣ, (ofFunctionField k K).val P f = (ofFunctionField k K).val Q f) : P = Q := by
  by_contra hne
  obtain ⟨x, hxt, hxQ, hx⟩ := exists_zero_only_at Q
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxt isAlgebraic_zero
  have e : P.ord x = Q.ord x := h (Units.mk0 x hx0)
  have := hx P hne
  omega

/-- `U_P ⊆ Ker(ord_P)`. -/
theorem val_eq_zero_of_mem_U {P : Place k K} {f : Kˣ} (hf : f ∈ (ofFunctionField k K).U P) :
    (ofFunctionField k K).val P f = 0 := by
  rw [mem_U_iff] at hf
  refine (P.ord_eq_zero_iff_isValue f.ne_zero).2 ⟨1, one_ne_zero, ?_⟩
  exact (P.isValue_iff_div_sub_one_mem one_ne_zero).2 (by simpa using hf)

end ofFunctionField

namespace ValEvalData

variable {D D' : ValEvalData.{u}}

/-- Points are determined by their valuations. -/
def ValInjective (D : ValEvalData.{u}) : Prop :=
  ∀ x y : D.P, (∀ f, D.val x f = D.val y f) → x = y

/-- `U_x ⊆ Ker(ord_x)` for every point. -/
def UInKer (D : ValEvalData.{u}) : Prop :=
  ∀ (x : D.P) (f : D.G), f ∈ D.U x → D.val x f = 0

lemma ord_eq_of_val_eq {x : D.P} {y : D'.P} {f : D.G} {f' : D'.G}
    (h : D'.val y f' = D.val x f) : D'.ord y f' = D.ord x f :=
  Multiplicative.toAdd.injective h

namespace Iso

/-- **`ValInjective` is transported by isomorphisms of triples.** -/
theorem valInjective (e : D.Iso D') (h : D.ValInjective) : D'.ValInjective := by
  intro x' y' hxy
  have h₁ : e.σ.symm x' = e.σ.symm y' := h _ _ fun f => by
    rw [← e.val_eq, ← e.val_eq, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hxy _
  simpa using congrArg e.σ h₁

/-- **`UInKer` is transported by isomorphisms of triples.** -/
theorem uInKer (e : D.Iso D') (h : D.UInKer) : D'.UInKer := by
  intro x' f' hf
  have h₁ := h (e.σ.symm x') (e.φ.symm f') (by
    rw [← e.mem_U_iff, Equiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hf)
  rw [← e.val_eq, Equiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h₁
  exact h₁

variable (φ : D.G ≃* D'.G) (hD : D.ValInjective) (hD' : D'.ValInjective)
  (hex : ∀ x : D.P, ∃ x' : D'.P, ∀ f, D'.val x' (φ f) = D.val x f)
  (hex' : ∀ x' : D'.P, ∃ x : D.P, ∀ f, D'.val x' (φ f) = D.val x f)
  (hU : ∀ (x : D.P) (x' : D'.P), (∀ f, D'.val x' (φ f) = D.val x f) →
    ∀ f, φ f ∈ D'.U x' ↔ f ∈ D.U x)

/-- The point with the same valuations along `φ`. -/
def ofValσ (x : D.P) : D'.P := (hex x).choose

lemma val_ofValσ (x : D.P) (f : D.G) : D'.val (ofValσ φ hex x) (φ f) = D.val x f :=
  (hex x).choose_spec f

include hD hD' hex' in
lemma ofValσ_bijective : Function.Bijective (ofValσ φ hex) := by
  refine ⟨fun x y hxy => hD x y fun f => ?_, fun x' => ?_⟩
  · rw [← val_ofValσ φ hex x f, ← val_ofValσ φ hex y f, hxy]
  · obtain ⟨x, hx⟩ := hex' x'
    refine ⟨x, hD' _ _ fun f' => ?_⟩
    obtain ⟨f, rfl⟩ := φ.surjective f'
    rw [val_ofValσ, hx]

/-- **An isomorphism of triples from the valuations**: a group isomorphism `φ` such that every point
on either side has a partner with the same valuations along `φ`, and which respects `U_x` for
partners. The bijection of the points is `x ↦` its partner (unique by `ValInjective`). -/
def ofVal : D.Iso D' where
  φ := φ
  σ := Equiv.ofBijective _ (ofValσ_bijective φ hD hD' hex hex')
  ord_eq x f := ord_eq_of_val_eq (val_ofValσ φ hex x f)
  mem_U_iff x f := hU x _ (val_ofValσ φ hex x) f

lemma ofVal_φ : (ofVal φ hD hD' hex hex' hU).φ = φ := rfl

end Iso

end ValEvalData

namespace ofFunctionField

variable (k : Type*) (K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  [IsFunctionField k K]

lemma valInjective : (ofFunctionField k K).ValInjective := fun _ _ h => val_injective h

lemma uInKer : (ofFunctionField k K).UInKer := fun _ _ hf => val_eq_zero_of_mem_U hf

end ofFunctionField

end Uchida

namespace Thm19

open KummerTheory Curve AffOrbicurve CurvesJacobian.Kummer CurvesJacobian

attribute [local instance] isAlgClosed_algebraicClosure isFunctionField_fnf

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [CharZero Ω] [Fact (D.H ≤ D.HL)] [NumberField k] (N : NFModel D)
  (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))

/-- **The points of the reconstructed triple are determined by their valuations.** -/
theorem recTriple_valInjective : (recTriple N hkF).ValInjective :=
  (recIso N hkF).valInjective (Uchida.ofFunctionField.valInjective _ _)

/-- `U_x ⊆ Ker(ord_x)` in the reconstructed triple. -/
theorem recTriple_uInKer : (recTriple N hkF).UInKer :=
  (recIso N hkF).uInKer (Uchida.ofFunctionField.uInKer _ _)

end Thm19

end Iut.Reconstruction
