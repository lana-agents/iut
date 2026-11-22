/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Elliptic.EllField

/-!
# Naturality of `A_p ≅ ℂ` in the Aut-holomorphic space (MR21, for IUT I Prop 4.2 (i))

For an isomorphism `S : (E, A) ≅ (E', A')` of Aut-holomorphic spaces isomorphic to
once-punctured complex tori (`IsEllModel`):

* `ellMap hS : OnePoint E ≃ₜ OnePoint E'` (the extension of `S` by `∞ ↦ ∞`) is additive for the
  group laws of [AbsTopIII] Corollary 2.7 (c) (`ellMap_add`), since it is `ellHomeo hχ⁻¹ ∘
  ellHomeo (hS.trans hχ)` for any model `χ` of `(E', A')` (`ellHomeo_trans`);
* **`ellTransport hS p : A_p ∪ {0} ≃+* A'_{S p} ∪ {0}`**, conjugation of endomorphisms of the
  tangent space by `ellMap hS` (the "isomorphism of fields induced by `S`");
* **naturality** (`ellEquiv_trans`): for every isomorphism `ψ : (E', A') ≅ E_Λ`,
  `ellEquiv (hS.trans hψ) p = ellTransport hS p ≫ ellEquiv hψ (S p)`, i.e. the identification
  `A_p ≅ ℂ` through `S ≫ ψ` is the identification `A'_{S p} ≅ ℂ` through `ψ` after the
  transport along `S`.

This is the input from the Aut-holomorphic side needed for the surjectivity of
`Isom(F_v) → Isom(D_v)` at `v ∈ V^arc` (IUT I Cor 5.3 (ii), via [AbsTopIII] Prop 4.2 (i)).
-/

namespace Iut

namespace AutHol

namespace Ell

open OnePoint

section LieGeneric

variable {Y Y' Y'' : Type*} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [AddCommGroup Y'] [TopologicalSpace Y'] [IsTopologicalAddGroup Y']
  [AddCommGroup Y''] [TopologicalSpace Y''] [IsTopologicalAddGroup Y'']

omit [IsTopologicalAddGroup Y] [IsTopologicalAddGroup Y'] [IsTopologicalAddGroup Y''] in
theorem trans_add {Θ₁ : Y ≃ₜ Y'} {Θ₂ : Y' ≃ₜ Y''} (h₁ : ∀ x y, Θ₁ (x + y) = Θ₁ x + Θ₁ y)
    (h₂ : ∀ x y, Θ₂ (x + y) = Θ₂ x + Θ₂ y) : ∀ x y, (Θ₁.trans Θ₂) (x + y) =
      (Θ₁.trans Θ₂) x + (Θ₁.trans Θ₂) y := fun x y => by
  rw [Homeomorph.trans_apply, h₁, h₂]
  rfl

/-- **Conjugation is functorial**: `lieConj Θ₂ ∘ lieConj Θ₁ = lieConj (Θ₁ ≫ Θ₂)`. -/
theorem lieConj_lieConj (Θ₁ : Y ≃ₜ Y') (h₁ : ∀ x y, Θ₁ (x + y) = Θ₁ x + Θ₁ y) (Θ₂ : Y' ≃ₜ Y'')
    (h₂ : ∀ x y, Θ₂ (x + y) = Θ₂ x + Θ₂ y) (M : Lie Y →ₗ[ℝ] Lie Y) :
    lieConj Θ₂ h₂ (lieConj Θ₁ h₁ M) = lieConj (Θ₁.trans Θ₂) (trans_add h₁ h₂) M :=
  LinearMap.ext fun _ => rfl

/-- `lieConj` depends only on the homeomorphism. -/
theorem lieConj_congr {Θ Θ' : Y ≃ₜ Y'} (h : ∀ x, Θ x = Θ' x) (hΘ : ∀ x y, Θ (x + y) = Θ x + Θ y)
    (hΘ' : ∀ x y, Θ' (x + y) = Θ' x + Θ' y) (M : Lie Y →ₗ[ℝ] Lie Y) :
    lieConj Θ hΘ M = lieConj Θ' hΘ' M := by
  obtain rfl : Θ = Θ' := Homeomorph.ext h
  rfl

end LieGeneric

variable {E E' : Type*} [TopologicalSpace E] [TopologicalSpace E'] {A : AutHolStr E}
  {A' : AutHolStr E'} [hA : Fact (IsEllModel A)] [hA' : Fact (IsEllModel A')] {S : E ≃ₜ E'}

/-- **The extension `OnePoint E ≃ₜ OnePoint E'` of an isomorphism** `S` (`∞ ↦ ∞`). -/
noncomputable def ellMap (_hS : IsIso A A' S) : EllSpace A ≃ₜ EllSpace A' := S.onePointCongr

omit hA hA' in
theorem ellMap_ellPt (hS : IsIso A A' S) (p : E) : ellMap hS (ellPt A p) = ellPt A' (S p) := rfl

omit hA hA' in
/-- `ellHomeo (S ≫ ψ) = ellHomeo ψ ∘ ellMap S`. -/
theorem ellHomeo_trans (hS : IsIso A A' S) {L : PeriodPair} {ψ : E' ≃ₜ punct L}
    (hψ : IsIso A' (ellStr L) ψ) (x : EllSpace A) :
    ellHomeo (hS.trans hψ) x = ellHomeo hψ (ellMap hS x) := by
  rcases x with _ | x <;> rfl

/-- **`ellMap hS` is additive** for the group laws of [AbsTopIII] Corollary 2.7 (c). -/
theorem ellMap_add (hS : IsIso A A' S) (x y : EllSpace A) :
    ellMap hS (x + y) = ellMap hS x + ellMap hS y := by
  apply (ellHomeo (chosenIso_spec (A := A'))).injective
  rw [← ellHomeo_trans hS (chosenIso_spec (A := A')), ellHomeo_add, ellHomeo_add,
    ellHomeo_trans, ellHomeo_trans]

omit hA hA' in
theorem ellMap_symm (hS : IsIso A A' S) (x : EllSpace A') :
    (ellMap hS).symm x = ellMap hS.symm x := by
  rcases x with _ | x <;> rfl

/-- **`lieConj (ellMap hS)` maps `A_p ∪ {0}` into `A'_q ∪ {0}`** (for all `p`, `q`). -/
theorem lieConj_ellMap_mem (hS : IsIso A A' S) (p : E) (q : E')
    {M : Lie (EllSpace A) →ₗ[ℝ] Lie (EllSpace A)} (hM : M ∈ fieldSet (ellPtStr A) (ellPt A p)) :
    lieConj (ellMap hS) (ellMap_add hS) M ∈ fieldSet (ellPtStr A') (ellPt A' q) := by
  rw [mem_ellFieldSet_iff chosenIso_spec]
  obtain ⟨b, hb⟩ := (mem_ellFieldSet_iff (hS.trans chosenIso_spec) p M).1 hM
  refine ⟨b, ?_⟩
  rw [lieConj_lieConj, ← hb]
  exact lieConj_congr (fun x => (ellHomeo_trans hS chosenIso_spec x).symm) _ _ M

/-- **The isomorphism of fields `A_p ∪ {0} ≅ A'_{S p} ∪ {0}` induced by `S`**: conjugation of
endomorphisms of the tangent space by `ellMap hS`. -/
noncomputable def ellTransport (hS : IsIso A A' S) (p : E) :
    EllField A p ≃+* EllField A' (S p) where
  toFun M := ⟨lieConj (ellMap hS) (ellMap_add hS) M.1, lieConj_ellMap_mem hS p (S p) M.2⟩
  invFun N := ⟨lieConj (ellMap hS).symm (symm_add _ (ellMap_add hS)) N.1, by
    rw [lieConj_congr (ellMap_symm hS) _ (ellMap_add hS.symm)]
    exact lieConj_ellMap_mem hS.symm (S p) p N.2⟩
  left_inv M := Subtype.ext (lieConj_symm_lieConj _ _ _)
  right_inv N := Subtype.ext (lieConj_lieConj_symm _ _ _)
  map_add' M M' := by
    apply EllField.val_injective
    change lieConj _ _ (M + M').val = _
    rw [EllField.add_val, EllField.add_val, lieConj_add]
    rfl
  map_mul' M M' := by
    apply EllField.val_injective
    change lieConj _ _ (M * M').val = _
    rw [EllField.mul_val, EllField.mul_val, lieConj_mul]
    rfl

theorem ellTransport_val (hS : IsIso A A' S) (p : E) (M : EllField A p) :
    (ellTransport hS p M).val = lieConj (ellMap hS) (ellMap_add hS) M.val := rfl

/-- **Naturality of `A_p ≅ ℂ` in the Aut-holomorphic space**: for `S : (E, A) ≅ (E', A')` and
`ψ : (E', A') ≅ E_Λ`, `ellEquiv (S ≫ ψ) p = ellTransport S p ≫ ellEquiv ψ (S p)`. -/
theorem ellEquiv_trans_apply (hS : IsIso A A' S) {L : PeriodPair} {ψ : E' ≃ₜ punct L}
    (hψ : IsIso A' (ellStr L) ψ) (p : E) (M : EllField A p) :
    ellEquiv (hS.trans hψ) p M = ellEquiv hψ (S p) (ellTransport hS p M) := by
  rw [ellEquiv_apply, ellEquiv_apply]
  congr 2
  change _ = lieConj (ellHomeo hψ) (ellHomeo_add hψ) (lieConj (ellMap hS) (ellMap_add hS) M.1)
  rw [lieConj_lieConj]
  exact lieConj_congr (fun x => ellHomeo_trans hS hψ x) _ _ M.1

/-- **Naturality of `A_p ≅ ℂ`** as an equality of ring isomorphisms. -/
theorem ellEquiv_trans (hS : IsIso A A' S) {L : PeriodPair} {ψ : E' ≃ₜ punct L}
    (hψ : IsIso A' (ellStr L) ψ) (p : E) :
    ellEquiv (hS.trans hψ) p = (ellTransport hS p).trans (ellEquiv hψ (S p)) :=
  RingEquiv.ext fun M => ellEquiv_trans_apply hS hψ p M

end Ell

end AutHol

end Iut
