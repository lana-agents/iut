/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.OutSemidirect

/-!
# Elliptic cuspidalisation: the group-theoretic steps (roadmap P17, M4b)

[AbsTopII], Corollary 3.3 (iii): for a `Π`-elliptically admissible hyperbolic orbicurve `X`
with `D → C` a semi-elliptic double cover, `U ⊆ D` the complement of the `N`-torsion points and
`V → X`, `V → D` finite étale coverings with `Π_V ⊴ Π` normal, the cuspidalisation
`Π_{U_X} ↠ Π` is constructed in three steps:

* (a) `Π_U ↠ Π_D` from a chain of `Π` (this uses the relative Grothendieck conjecture and the
  categories of [AbsTopI], §4); for IUT's `X = E ∖ {O}` with `N = 2` this is
  `Iut.Reconstruction.ellipticCuspSpec_oncePunctured` (`BelyiSpec.lean`, from curves-jacobian's
  `ellipticCusp_spec_oncePunctured`, part (b)), with `V = D = X`;
* (a′) `Π_{U_V} ↠ Π_V` as the fibre product of `Π_U ↠ Π_D` with `Π_V ↪ Π_D`
  (`Iut.Reconstruction.fibreSubgroup`, `Iut.Reconstruction.fibreSubgroup_surjective`);
* (b) `Π_{U_X}` as the out-semidirect product of `Π_{U_V}` with the finite group `Π/Π_V`,
  `Π_{U_X} ≃ Π_{U_V} ⋊^out (Π/Π_V)` (`Iut.Reconstruction.cuspidalizationEquiv`), using that
  `Π_{U_V}` is center-free and `Π_{U_X}/Π_{U_V} ≃ Π/Π_V`
  (`Iut.Reconstruction.quotientComapEquiv`).

The center-freeness of `Π_{U_V}` (an open subgroup of the slim profinite group `Π_{U_X}`,
[AbsTopI], Proposition 2.3) and the uniqueness of the lifting of the outer action of `Π/Π_V`
from `Π_V` to `Π_{U_V}` are the inputs of step (b); they enter as explicit hypotheses
(`Subgroup.center _ = ⊥`, resp. the given homomorphism `Π_{U_X} → Π`).
-/

namespace Iut.Reconstruction

variable {E P : Type*} [Group E] [Group P]

/-- (a′) The fibre product `Π_{U_V} = π⁻¹(Π_V)`. -/
def fibreSubgroup (π : E →* P) (V : Subgroup P) : Subgroup E := V.comap π

/-- The surjection `Π_{U_V} ↠ Π_V`. -/
def fibreSubgroupMap (π : E →* P) (V : Subgroup P) : fibreSubgroup π V →* V :=
  π.restrict (fibreSubgroup π V) |>.codRestrict V (fun x => x.2)

theorem fibreSubgroup_surjective {π : E →* P} (hπ : Function.Surjective π) (V : Subgroup P) :
    Function.Surjective (fibreSubgroupMap π V) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hπ y
  exact ⟨⟨x, hy⟩, rfl⟩

instance fibreSubgroup_normal (π : E →* P) (V : Subgroup P) [V.Normal] :
    (fibreSubgroup π V).Normal :=
  Subgroup.Normal.comap inferInstance π

/-- `Π_{U_X}/Π_{U_V} ≃ Π/Π_V`. -/
noncomputable def quotientComapEquiv {π : E →* P} (hπ : Function.Surjective π)
    (V : Subgroup P) [V.Normal] : E ⧸ fibreSubgroup π V ≃* P ⧸ V :=
  (QuotientGroup.quotientMulEquivOfEq (by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    rfl)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' V).comp π)
      ((QuotientGroup.mk'_surjective V).comp hπ))

theorem quotientComapEquiv_mk {π : E →* P} (hπ : Function.Surjective π) (V : Subgroup P)
    [V.Normal] (x : E) :
    quotientComapEquiv hπ V (QuotientGroup.mk x) = QuotientGroup.mk (π x) := rfl

/-- **[AbsTopII], Corollary 3.3 (iii) (b)**: `Π_{U_X}` is recovered from `Π_{U_V} = π⁻¹(Π_V)`
and the outer action of `Π/Π_V ≃ Π_{U_X}/Π_{U_V}` on it, provided `Π_{U_V}` is center-free. -/
noncomputable def cuspidalizationEquiv (π : E →* P) (V : Subgroup P) [V.Normal]
    (hZ : Subgroup.center (fibreSubgroup π V) = ⊥) :
    E ≃* outSemidirect (outerAction (fibreSubgroup π V)) :=
  extensionEquivOutSemidirect _ hZ

/-- The outer action of `Π/Π_V` on `Π_{U_V}`, transported along `Π_{U_X}/Π_{U_V} ≃ Π/Π_V`. -/
noncomputable def cuspOuterAction {π : E →* P} (hπ : Function.Surjective π) (V : Subgroup P)
    [V.Normal] : P ⧸ V →* Out (fibreSubgroup π V) :=
  (outerAction (fibreSubgroup π V)).comp (quotientComapEquiv hπ V).symm.toMonoidHom

/-- The same statement with the quotient written as `Π/Π_V`: `Π_{U_X} ≃ Π_{U_V} ⋊^out (Π/Π_V)`,
compatibly with the projections to `Π/Π_V`. -/
noncomputable def cuspidalizationEquiv' {π : E →* P} (hπ : Function.Surjective π)
    (V : Subgroup P) [V.Normal] (hZ : Subgroup.center (fibreSubgroup π V) = ⊥) :
    E ≃* outSemidirect (cuspOuterAction hπ V) :=
  (cuspidalizationEquiv π V hZ).trans
    { toFun := fun x => ⟨(x.1.1, quotientComapEquiv hπ V x.1.2), by
        have h := x.2
        rw [mem_outSemidirect] at h ⊢
        simp [cuspOuterAction, h]⟩
      invFun := fun x => ⟨(x.1.1, (quotientComapEquiv hπ V).symm x.1.2), by
        have h := x.2
        rw [mem_outSemidirect] at h ⊢
        simpa [cuspOuterAction] using h⟩
      left_inv := fun x => by ext <;> simp
      right_inv := fun x => by ext <;> simp
      map_mul' := fun x y => by ext <;> simp }

theorem cuspidalizationEquiv'_apply {π : E →* P} (hπ : Function.Surjective π)
    (V : Subgroup P) [V.Normal] (hZ : Subgroup.center (fibreSubgroup π V) = ⊥) (e : E) :
    (cuspidalizationEquiv' hπ V hZ e : MulAut (fibreSubgroup π V) × (P ⧸ V)) =
      (MulAut.conjNormal e, QuotientGroup.mk (π e)) := rfl

end Iut.Reconstruction
