/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.BiKummer

/-!
# Transport of Frobenioid-theoretic Kummer classes ([EtTh], Theorem 5.6, proof)

[EtTh], proof of Theorem 5.6: a self-equivalence `Ψ` of the tempered Frobenioid maps the pair of
base-equivalent pre-steps `s⊓, s⊔ : S₁ → S₂` of an `l·N`-th root of a right fraction-pair of `Θ̈` to
a pair `t⊓, t⊔` with `γ₂ ∘ s⊓ = t⊓ ∘ γ₁`, `u ∘ γ₂ ∘ s⊔ = t⊔ ∘ γ₁` for isomorphisms `γ₁, γ₂` and a
unit `u ∈ O^×(T₂)` (by Proposition 5.3(vi)); "forming the resulting group homomorphisms
`s⊓-gp, s⊔-gp; t⊓-gp, t⊔-gp` and Kummer classes, and observing that the Kummer class of the
'function `u` in O^×' does not affect the restriction of the resulting Kummer classes to
`(l·Δ_Θ)`", `Ψ` transports the isomorphism of Proposition 5.5. The two formal steps:

* `Model.map_unitHom_kummerUnit`: a functor `F` between model Frobenioids mapping pre-steps to
  pre-steps and base-equivalent pairs to base-equivalent pairs maps the Kummer unit
  `κ_{s,t}(a)` ([EtTh], Proposition 4.3(iii)) of `a ∈ Aut_C(X)` to the Kummer unit
  `κ_{F s, F t}(F a)`: `F(1, id, 0, κ(a)) = (1, id, 0, κ'(F a))`;
* `Model.kummerUnit_comp_unit`: replacing `s⊔` by `s⊔` followed by a unit `u` changes the Kummer
  unit of `a` by `a^*u − u` (transported), hence not at all when the base of the lift of `a` fixes
  `u` (`u` from the base field, `a` geometric); `Model.kummerUnit_iso_comp`: composing both
  pre-steps with an isomorphism `γ₂` transports the Kummer unit by `γ₂`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w w₁ w₂ v v₁ v₂ u u₁ u₂

namespace Model

section Unit

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

/-- **A unit multiple fixed by the lift does not change the Kummer unit**: if `u ∈ O^×(Y)` is
fixed by the base `Base(s)^{-1} Base(a) Base(s)` of the lift of `a`, then
`κ_{s, t ≫ u}(a) = κ_{s,t}(a)`. -/
theorem kummerUnit_comp_unit {X Y : Model Φ B divB} {s t : X ⟶ Y} [IsIso s.base]
    (hb : s.base = t.base) (u : B.obj Y.base) (hu0 : divB.app _ u = 0) (a : Aut X)
    (hu : B.pb (inv s.base ≫ a.hom.base ≫ s.base) u = u) :
    kummerUnit s (t ≫ unitHom Y u hu0) a = kummerUnit s t a := by
  have hu' : B.pb a.hom.base (B.pb s.base u) = B.pb s.base u := by
    have := congrArg (B.pb s.base) hu
    simpa only [GrpOn.pb_comp', GrpOn.pb_pb_inv] using this
  simp only [kummerUnit, comp_u, unitHom, mk1_u, mk1_deg, PNat.one_coe, one_smul, ← hb]
  rw [show s.u - (B.pb s.base u + t.u) = (s.u - t.u) - B.pb s.base u by abel]
  simp only [map_sub, hu']
  abel

/-- **Composing with an isomorphism transports the Kummer unit**: for `γ : Y ≅ Y'`,
`κ_{s ≫ γ, t ≫ γ}(a) = (Base γ^{-1})^* κ_{s,t}(a)`. -/
theorem kummerUnit_iso_comp {X Y Y' : Model Φ B divB} {s t : X ⟶ Y} [IsIso s.base]
    (hb : s.base = t.base) (γ : Y ≅ Y') [IsIso (s ≫ γ.hom).base] (a : Aut X) :
    kummerUnit (s ≫ γ.hom) (t ≫ γ.hom) a = B.pb γ.inv.base (kummerUnit s t a) := by
  have hγ : γ.inv.base = inv γ.hom.base := by
    rw [eq_comm, IsIso.inv_eq_of_hom_inv_id (hom_base_inv_of_iso γ)]
  have hdeg : (γ.hom.deg : ℕ) = 1 := by rw [deg_of_iso γ]; rfl
  simp only [kummerUnit, comp_u, hdeg, one_smul, comp_base, IsIso.inv_comp, GrpOn.pb_comp', hγ,
    ← hb, map_sub, map_add]
  abel

end Unit

section Map

variable {D₁ : Type u₁} [Category.{v₁} D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂)
  (hpre : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y),
    IsPreStep (toElem Φ₁ B₁ divB₁) φ ↔ IsPreStep (toElem Φ₂ B₂ divB₂) (F.map φ))
  (hbe : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ φ' : X ⟶ Y), φ.base = φ'.base →
    (F.map φ).base = (F.map φ').base)

include hpre hbe in
/-- **[EtTh], Theorem 5.6 (proof): the Kummer class is transported.** A functor `F` matching
pre-steps and preserving base-equivalent pairs maps the Kummer unit `(1, id, 0, κ_{s,t}(a))` of
`a ∈ Aut_C(X)` (for base-equivalent pre-steps `s, t` whose divisors `a` fixes) to the Kummer unit
`(1, id, 0, κ_{F s, F t}(F a))`. -/
theorem map_unitHom_kummerUnit {X Y : Model Φ₁ B₁ divB₁} {s t : X ⟶ Y} (hs : IsPreStep 𝐏₁ s)
    (ht : IsPreStep 𝐏₁ t) (hb : s.base = t.base) (a : Aut X)
    (has : Φ₁.pb a.hom.base s.div = s.div) (hat : Φ₁.pb a.hom.base t.div = t.div) :
    haveI : IsIso s.base := hs.2
    haveI : IsIso (F.map s).base := ((hpre s).1 hs).2
    F.map (unitHom Y (kummerUnit s t a) (divB_kummerUnit hs ht hb a has hat)) =
      unitHom (F.obj Y) (kummerUnit (F.map s) (F.map t) (F.mapIso a))
        (divB_kummerUnit ((hpre s).1 hs) ((hpre t).1 ht) (hbe s t hb) _
          (map_fixes F hpre hs a has) (map_fixes F hpre ht a hat)) := by
  haveI : IsIso s.base := hs.2
  haveI : IsIso t.base := ht.2
  have hs' := (hpre s).1 hs
  have ht' := (hpre t).1 ht
  haveI : IsIso (F.map s).base := hs'.2
  haveI : IsIso (F.map t).base := ht'.2
  have has' := map_fixes F hpre hs a has
  have hat' := map_fixes F hpre ht a hat
  have e1 := congrArg F.map (unit_comp_liftAut hs ht hb a has hat)
  rw [F.map_comp, map_liftAut F ht.1 a hat ht'.1 hat', map_liftAut F hs.1 a has hs'.1 has'] at e1
  have e2 := unit_comp_liftAut hs' ht' (hbe s t hb) (F.mapIso a) has' hat'
  exact (cancel_mono _).1 (e1.trans e2.symm)

end Map

end Model

end Frobenioid

end Iut
