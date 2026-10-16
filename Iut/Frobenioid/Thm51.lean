/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.ModelFrobenioid

/-!
# [FrdI], Theorem 5.1 (divisorial descriptions) for model Frobenioids

[FrdI], Theorem 5.1 (p. 96–97), for a Frobenioid of isotropic type and Frobenius-trivial
`A, A'`:

* (i) `Pic_Φ(A) = Φ^gp(A)/Φ^birat(A) ≅ Pic_C(A)` (isomorphism classes over `A_D`), and a morphism
  of Frobenius type `κ : C → C'` multiplies the class by `degFr(κ)`;
* (ii) there is a morphism `φ : B → B'` of Frobenius degree `d`, with `Base(φ) = θ` and
  `Div(φ) = z`, iff `d·β + z = Φ(θ)(β')` in `Pic_Φ`; such a morphism is unique up to
  unit-equivalence (its image in `F_Φ` is unique).

For the model Frobenioid `Model Φ B divB` (Theorem 5.2), the reference Frobenius-trivial objects
are `(A_D, 0)` and the class of `(A_D, α)` is `[α] ∈ Φ^gp(A_D)/Div_B(B(A_D))`. The bijection
`Pic_Φ ≅ Pic_C` is `Model.nonempty_iso_iff` (`ModelFrobenioid.lean`); here:

* `Model.exists_hom_iff` (Theorem 5.1(ii));
* `Model.toElem_map_eq_of` (uniqueness of the unit-equivalence class) and
  `Model.u_sub_mem_ker` (two such morphisms differ by a rational function with trivial divisor,
  i.e. by an element of `O^×`);
* `Model.class_frobeniusType` (Theorem 5.1(i), last assertion).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

namespace Model

local notation "𝐏" => toElem Φ B divB

/-- **[FrdI], Theorem 5.1(ii)** for model Frobenioids: a morphism `X → Y` of Frobenius degree
`d`, projection `θ` and zero divisor `z` exists iff `d·α + z ≡ θ^*β` modulo `Div_B(B)`. -/
theorem exists_hom_iff (X Y : Model Φ B divB) (d : ℕ+) (θ : X.base ⟶ Y.base)
    {z : Φ.obj X.base} (hz : z ∈ Φ.pos X.base) :
    (∃ φ : X ⟶ Y, φ.deg = d ∧ φ.base = θ ∧ φ.div = z) ↔
      ∃ u : B.obj X.base, (d : ℕ) • X.α + z - Φ.pb θ Y.α = divB.app X.base u := by
  constructor
  · rintro ⟨φ, rfl, rfl, rfl⟩
    exact ⟨φ.u, by rw [φ.rel]; abel⟩
  · rintro ⟨u, hu⟩
    exact ⟨mk' d θ z hz u (by rw [← hu]; abel), rfl, rfl, rfl⟩

/-- **Uniqueness of the unit-equivalence class** ([FrdI], Theorem 5.1(ii)): morphisms with the
same Frobenius degree, projection and zero divisor have the same image in `F_Φ`. -/
theorem toElem_map_eq_of {X Y : Model Φ B divB} {φ ψ : X ⟶ Y} (h₁ : φ.deg = ψ.deg)
    (h₂ : φ.base = ψ.base) (h₃ : φ.div = ψ.div) : 𝐏.map φ = 𝐏.map ψ := by
  rcases φ with ⟨d, b, z, hz, u, r⟩
  rcases ψ with ⟨d', b', z', hz', u', r'⟩
  dsimp only at h₁ h₂ h₃
  subst h₁ h₂ h₃
  rfl

/-- Two such morphisms differ by a rational function with trivial divisor. -/
theorem u_sub_mem_ker {X Y : Model Φ B divB} {φ ψ : X ⟶ Y} (h₁ : φ.deg = ψ.deg)
    (h₂ : φ.base = ψ.base) (h₃ : φ.div = ψ.div) : divB.app X.base (φ.u - ψ.u) = 0 := by
  have r₁ := φ.rel
  have r₂ := ψ.rel
  rw [h₁, h₂, h₃] at r₁
  rw [map_sub, ← sub_eq_zero.mpr (r₁.symm.trans r₂)]
  abel

/-- **[FrdI], Theorem 5.1(i)** (last assertion) for model Frobenioids: a base-identity
morphism of Frobenius type `κ : X → Y` multiplies the class: `[β] = degFr(κ)·[α]`. -/
theorem class_frobeniusType {X Y : Model Φ B divB} (κ : X ⟶ Y) (hb : X.base = Y.base)
    (hκ : κ.base = eqToHom hb) (h0 : κ.div = 0) :
    ∃ u : B.obj X.base, (κ.deg : ℕ) • X.α - Φ.pb (eqToHom hb) Y.α = divB.app X.base u := by
  refine ⟨κ.u, ?_⟩
  have r := κ.rel
  rw [h0, hκ, add_zero] at r
  rw [r]
  abel

end Model

end Frobenioid

end Iut
