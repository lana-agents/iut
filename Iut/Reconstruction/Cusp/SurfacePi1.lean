/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.SurfaceDiscrete
import Pi1.Surface.Profinite

/-!
# The model `Π̂_{g,0}` is `pi1`'s profinite closed surface group

`SurfaceDiscrete.lean` identifies the model `SurfGrp g = F̂ / cl⟨⟨∏ᵢ ⁅aᵢ, bᵢ⁆⟩⟩` with the
profinite completion `SurfCompl g` of the discrete group `⟨a, b | ∏ᵢ ⁅aᵢ, bᵢ⁆⟩`. Relabelling the
generators `SurfaceGen g 0 ≃ Gen g` (`a i ↦ inl i`, `b i ↦ inr i`; there are no cusp generators)
carries `pi1`'s relator `∏ᵢ [aᵢ, bᵢ] · ∏_∅` to `rel g`, so:

* `genEquiv g : Pi1.SurfaceGen g 0 ≃ Gen g` and `freeGroupCongr_relator`;
* `discEquiv g : Pi1.SurfaceGroup g 0 ≃* SurfDisc g`;
* **`surfPi1Equiv g : SurfGrp g ≃ₜ* Pi1.ProfiniteSurfaceGroup g 0`**, sending the class of each
  free generator to the image of the corresponding generator of `Π_{g,0}`
  (`surfPi1Equiv_surfMap_eta_of`).

Through `surfPi1Equiv` the results of `pi1` and `curves-jacobian` on `Π̂_{g,0}` (e.g.
`π₁ᵉᵗ(X) ≃ₜ* Π̂_{g,0}` for proper curves over algebraically closed fields of characteristic `0`)
apply to the model of `SurfaceH2.lean`.
-/

namespace Iut.Reconstruction.SurfaceH2

open CategoryTheory ProfiniteGrp Pi1 Pi1.SurfaceGen

variable (g : ℕ)

/-- The relabelling `a i ↦ inl i`, `b i ↦ inr i` of the generators of `Π_{g,0}`. -/
def genEquiv : SurfaceGen g 0 ≃ Gen g where
  toFun
    | .a i => Sum.inl i
    | .b i => Sum.inr i
    | .c j => j.elim0
  invFun
    | Sum.inl i => .a i
    | Sum.inr i => .b i
  left_inv x := by
    cases x with
    | a i => rfl
    | b i => rfl
    | c j => exact j.elim0
  right_inv x := by
    cases x with
    | inl i => rfl
    | inr i => rfl

/-- The relabelling carries `pi1`'s relator to `rel g`. -/
lemma freeGroupCongr_relator : FreeGroup.freeGroupCongr (genEquiv g) (relator g 0) = rel g := by
  simp [relator, commProd, ordProd, rel, map_list_prod, List.map_ofFn, Function.comp_def,
    genEquiv, commutatorElement_def]

lemma lift_relator :
    FreeGroup.lift (fun x : SurfaceGen g 0 => (PresentedGroup.of (genEquiv g x) : SurfDisc g))
      (relator g 0) = 1 := by
  have h : ∀ w : FreeGroup (SurfaceGen g 0),
      FreeGroup.lift (fun x : SurfaceGen g 0 => (PresentedGroup.of (genEquiv g x) : SurfDisc g))
        w = PresentedGroup.mk _ (FreeGroup.freeGroupCongr (genEquiv g) w) := by
    intro w
    induction w using FreeGroup.induction_on with
    | C1 => simp
    | of x => rfl
    | inv_of x _ => simp; rfl
    | mul x y hx hy => rw [map_mul, map_mul, map_mul, hx, hy]
  rw [h, freeGroupCongr_relator]
  exact PresentedGroup.one_of_mem rfl

lemma lift_rel :
    FreeGroup.lift (fun y : Gen g => (PresentedGroup.of ((genEquiv g).symm y) :
      SurfaceGroup g 0)) (rel g) = 1 := by
  have h : ∀ w : FreeGroup (Gen g),
      FreeGroup.lift (fun y : Gen g => (PresentedGroup.of ((genEquiv g).symm y) :
        SurfaceGroup g 0)) w =
        PresentedGroup.mk _ (FreeGroup.freeGroupCongr (genEquiv g).symm w) := by
    intro w
    induction w using FreeGroup.induction_on with
    | C1 => simp
    | of x => rfl
    | inv_of x _ => simp; rfl
    | mul x y hx hy => rw [map_mul, map_mul, map_mul, hx, hy]
  rw [h, ← freeGroupCongr_relator, ← MulEquiv.trans_apply, FreeGroup.freeGroupCongr_trans,
    Equiv.self_trans_symm, FreeGroup.freeGroupCongr_refl, MulEquiv.refl_apply]
  exact PresentedGroup.one_of_mem rfl

/-- `Π_{g,0}` of `pi1` is the discrete surface group `⟨a, b | rel g⟩`. -/
noncomputable def discEquiv : SurfaceGroup g 0 ≃* SurfDisc g :=
  MonoidHom.toMulEquiv
    (PresentedGroup.toGroup (rels := {relator g 0}) (by rintro r rfl; exact lift_relator g))
    (PresentedGroup.toGroup (rels := {rel g}) (by rintro r rfl; exact lift_rel g))
    (PresentedGroup.ext fun x => by simp [PresentedGroup.toGroup.of])
    (PresentedGroup.ext fun x => by simp [PresentedGroup.toGroup.of])

lemma discEquiv_of (x : SurfaceGen g 0) :
    discEquiv g (PresentedGroup.of x) = PresentedGroup.of (genEquiv g x) := by
  simp [discEquiv, PresentedGroup.toGroup.of]

/-- **The model `SurfGrp g` is `pi1`'s `Π̂_{g,0}`.** -/
noncomputable def surfPi1Equiv : SurfGrp g ≃ₜ* ProfiniteSurfaceGroup g 0 :=
  (surfComplEquiv g).trans (Pi1.Profinite.completionCongr (discEquiv g).symm)

/-- Generators go to generators. -/
lemma surfPi1Equiv_surfMap_eta_of (x : SurfaceGen g 0) :
    surfPi1Equiv g (surfMap g (eta g (FreeGroup.of (genEquiv g x)))) =
      ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (SurfaceGroup g 0))
        (PresentedGroup.of x) := by
  rw [surfPi1Equiv, ContinuousMulEquiv.trans_apply, surfComplEquiv_surfMap_eta_of,
    Pi1.Profinite.completionCongr_apply]
  have h : (discEquiv g).symm (PresentedGroup.of (genEquiv g x)) = PresentedGroup.of x := by
    rw [MulEquiv.symm_apply_eq, discEquiv_of]
  rw [← h]
  exact Pi1.Profinite.completionMap_eta _ _

end Iut.Reconstruction.SurfaceH2
