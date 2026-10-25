/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Elliptic.CuspModel
import Iut.AutHolomorphic.CuspTransport

/-!
# The group law on `OnePoint E` for an abstract once-punctured elliptic curve

Let `(E, A)` be an Aut-holomorphic space isomorphic to some `E_Λ = T_Λ ∖ {0}` (`IsEllModel A`;
this is the output of [AbsTopIII] Corollary 2.7 (a)). The model-implicit operation `recAdd A` of
Corollary 2.7 (c) (`Cusp.lean`) is then a group law:

* `recAdd_of_isIso`: for every isomorphism `ψ : (E, A) ≅ (E_Λ, ellStr L)`, the extension
  `OnePoint E ≃ₜ T_Λ` of `ψ` carries `recAdd A` to the group law of `T_Λ`;
* `isRecAdd_iff_of_isIso`: `recAdd A` is the unique continuous operation extending the torsion law;
* `isCoveringMap_cuspExt_of_isIso`: every elliptic cuspidalisation diagram of `(E, A)` extends to a
  covering of the one-point compactification (Corollary 2.7 (b), "necessarily extends");
* `ellAddCommGroup hA`: the resulting commutative group structure on `OnePoint E`, with
  `ellAddCommGroup_add : x + y = recAdd A x y`; the zero is `∞`.
-/

namespace Iut

namespace AutHol

namespace Ell

open Set Topology OnePoint

variable {E : Type*} [TopologicalSpace E] {A : AutHolStr E}

/-- `(E, A)` **is isomorphic to a once-punctured complex torus** `E_Λ`. -/
def IsEllModel (A : AutHolStr E) : Prop :=
  ∃ (L : PeriodPair) (ψ : E ≃ₜ punct L), IsIso A (ellStr L) ψ

/-- The extension `OnePoint E ≃ₜ T_Λ` of an isomorphism `E ≃ₜ E_Λ`. -/
noncomputable def compEquiv {L : PeriodPair} (ψ : E ≃ₜ punct L) : OnePoint E ≃ₜ Torus L :=
  ψ.onePointCongr.trans (onePointEquiv L)

theorem compEquiv_infty {L : PeriodPair} (ψ : E ≃ₜ punct L) : compEquiv ψ ∞ = 0 := rfl

/-- **[AbsTopIII] Corollary 2.7 (c) for `(E, A) ≅ E_Λ`**: the model-implicit operation `recAdd A`
is carried to the group law of `T_Λ`. -/
theorem recAdd_of_isIso {L : PeriodPair} {ψ : E ≃ₜ punct L} (hψ : IsIso A (ellStr L) ψ)
    (x y : OnePoint E) : compEquiv ψ (recAdd A x y) = compEquiv ψ x + compEquiv ψ y := by
  have h := recAdd_transport (φ := ψ.symm) (IsIso.symm hψ) (isRecAdd_iff (L := L))
  rw [h]
  simp only [compEquiv, Homeomorph.trans_apply, trOp, onePointCongr_symm_apply',
    onePointCongr_symm_symm_apply', Homeomorph.apply_symm_apply, torusAdd]

/-- **Uniqueness** ([AbsTopIII] Corollary 2.7 (c)): on `(E, A) ≅ E_Λ`, `recAdd A` is the only
continuous operation extending the group law of the torsion points. -/
theorem isRecAdd_iff_of_isIso {L : PeriodPair} {ψ : E ≃ₜ punct L} (hψ : IsIso A (ellStr L) ψ)
    (ν : OnePoint E → OnePoint E → OnePoint E) : IsRecAdd A ν ↔ ν = recAdd A := by
  rw [recAdd_transport (φ := ψ.symm) (IsIso.symm hψ) (isRecAdd_iff (L := L)),
    isRecAdd_transport (IsIso.symm hψ)]
  rw [isRecAdd_iff]
  constructor
  · intro h
    rw [Homeomorph.symm_symm] at h
    rw [← h]
    funext x y
    simp only [trOp, onePointCongr_symm_apply', onePointCongr_symm_symm_apply',
      Homeomorph.symm_apply_apply]
  · intro h
    rw [h]
    funext x y
    simp only [trOp, Homeomorph.symm_symm, onePointCongr_symm_apply',
      onePointCongr_symm_symm_apply', Homeomorph.apply_symm_apply]

/-- **"Necessarily extends"** ([AbsTopIII] Corollary 2.7 (b)): on `(E, A) ≅ E_Λ`, the extension
of every elliptic cuspidalisation diagram `E ⊇ U → E` to the one-point compactification is a
covering map. -/
theorem isCoveringMap_cuspExt_of_isIso {L : PeriodPair} {ψ : E ≃ₜ punct L}
    (hψ : IsIso A (ellStr L) ψ) {U : TopologicalSpace.Opens E} {q : U → E} (hc : IsEllCusp A U q) :
    IsCoveringMap (cuspExt U q) := by
  have h := isCoveringMap_cuspExt (isEllCusp_transport ψ hψ hc)
  rw [cuspExt_transport] at h
  have h' : IsCoveringMap (ψ.onePointCongr ∘ cuspExt U q) :=
    (IsCoveringMap.comp_homeomorph_iff ψ.onePointCongr.symm).1 h
  exact (IsCoveringMap.homeomorph_comp_iff ψ.onePointCongr).1 h'

/-- **The group structure on `OnePoint E`** ([AbsTopIII] Corollary 2.7 (c)), for `(E, A)`
isomorphic to some `E_Λ`: transported from `T_Λ` along a chosen isomorphism; its addition is the
model-implicit `recAdd A` (`ellAddCommGroup_add`). -/
@[reducible] noncomputable def ellAddCommGroup (hA : IsEllModel A) : AddCommGroup (OnePoint E) :=
  (compEquiv hA.choose_spec.choose).toEquiv.addCommGroup

theorem ellAddCommGroup_add (hA : IsEllModel A) (x y : OnePoint E) :
    (ellAddCommGroup hA).add x y = recAdd A x y := by
  set ψ := hA.choose_spec.choose
  have hψ : IsIso A (ellStr _) ψ := hA.choose_spec.choose_spec
  apply (compEquiv ψ).injective
  rw [recAdd_of_isIso hψ]
  change compEquiv ψ ((compEquiv ψ).toEquiv.symm
    ((compEquiv ψ).toEquiv x + (compEquiv ψ).toEquiv y)) = _
  simp

theorem ellAddCommGroup_zero (hA : IsEllModel A) :
    (ellAddCommGroup hA).zero = (∞ : OnePoint E) := by
  set ψ := hA.choose_spec.choose
  apply (compEquiv ψ).injective
  change compEquiv ψ ((compEquiv ψ).toEquiv.symm 0) = _
  simp [compEquiv_infty]

end Ell

end AutHol

end Iut
