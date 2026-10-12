/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Out-semidirect products (roadmap P17, M4a)

[AbsTopII], §0 ("`⋊^out`"): for a group `N` and a homomorphism `ρ : Q → Out(N)` the
**out-semidirect product** is the fibre product `N ⋊^out Q = Aut(N) ×_{Out(N)} Q`. If
`1 → N → E → Q → 1` is an extension whose kernel `N` is **center-free**, then `E` is
recovered from the outer action `Q → Out(N)` alone: conjugation and projection give an
isomorphism `E ≃ N ⋊^out Q` (`Iut.Reconstruction.extensionEquivOutSemidirect`).

This is the group-theoretic step of the elliptic cuspidalisation algorithm, [AbsTopII],
Corollary 3.3 (b): the surjection `Π_{U_X} ↠ Π` is recovered from `Π_{U_V} ↠ Π_V` and the
outer action of the finite group `Π/Π_V` on `Π_{U_V}`, since `Π_{U_V}` (an open subgroup of
the slim profinite group `Π_{U_X}`) is center-free.

## Main definitions and results

* `Iut.Reconstruction.inn N`, `Iut.Reconstruction.Out N`: inner and outer automorphisms;
* `Iut.Reconstruction.outSemidirect ρ ≤ MulAut N × Q`;
* `Iut.Reconstruction.outerAction H : E ⧸ H →* Out H` for a normal subgroup `H ⊴ E`;
* `Iut.Reconstruction.extensionEquivOutSemidirect` : `E ≃* outSemidirect (outerAction H)`
  when the center of `H` is trivial.
-/

namespace Iut.Reconstruction

section Out

variable (N : Type*) [Group N]

/-- The inner automorphisms. -/
def inn : Subgroup (MulAut N) := (MulAut.conj : N →* MulAut N).range

instance inn_normal : (inn N).Normal where
  conj_mem := by
    rintro _ ⟨n, rfl⟩ a
    refine ⟨a n, ?_⟩
    ext x
    simp [MulAut.conj_apply]

/-- The outer automorphism group `Out(N) = Aut(N)/Inn(N)`. -/
abbrev Out : Type _ := MulAut N ⧸ inn N

variable {N}

theorem conj_injective_of_center_eq_bot (hN : Subgroup.center N = ⊥) :
    Function.Injective (MulAut.conj : N →* MulAut N) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro n hn
  rw [← hN, Subgroup.mem_center_iff]
  intro g
  have h := congrArg (fun a : MulAut N => a g) ((MonoidHom.mem_ker).1 hn)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc g * n = n * g * n⁻¹ * n := by rw [h]
    _ = n * g := inv_mul_cancel_right _ _

variable {Q : Type*} [Group Q]

/-- **The out-semidirect product** `N ⋊^out Q = Aut(N) ×_{Out(N)} Q`. -/
def outSemidirect (ρ : Q →* Out N) : Subgroup (MulAut N × Q) :=
  MonoidHom.eqLocus ((QuotientGroup.mk' (inn N)).comp (MonoidHom.fst _ _))
    (ρ.comp (MonoidHom.snd _ _))

theorem mem_outSemidirect {ρ : Q →* Out N} {x : MulAut N × Q} :
    x ∈ outSemidirect ρ ↔ (QuotientGroup.mk x.1 : Out N) = ρ x.2 := Iff.rfl

end Out

section Extension

variable {E : Type*} [Group E] (H : Subgroup E) [H.Normal]

/-- The outer action `E/H → Out(H)` of an extension. -/
def outerAction : E ⧸ H →* Out H :=
  QuotientGroup.lift H ((QuotientGroup.mk' (inn H)).comp MulAut.conjNormal) (by
    intro h hh
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    refine ⟨⟨h, hh⟩, ?_⟩
    exact MulAut.conjNormal_val.symm)

theorem outerAction_mk (e : E) :
    outerAction H (QuotientGroup.mk e) = QuotientGroup.mk (MulAut.conjNormal e) := rfl

/-- Conjugation and projection, `E → Aut(H) × E/H`. -/
def toOutSemidirect : E →* MulAut H × (E ⧸ H) :=
  MonoidHom.prod MulAut.conjNormal (QuotientGroup.mk' H)

theorem toOutSemidirect_mem (e : E) : toOutSemidirect H e ∈ outSemidirect (outerAction H) :=
  rfl

theorem toOutSemidirect_injective (hH : Subgroup.center H = ⊥) :
    Function.Injective (toOutSemidirect H) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro e he
  rw [MonoidHom.mem_ker] at he
  have h1 : MulAut.conjNormal e = 1 := congrArg Prod.fst he
  have h2 : (QuotientGroup.mk e : E ⧸ H) = 1 := congrArg Prod.snd he
  have heH : e ∈ H := (QuotientGroup.eq_one_iff e).1 h2
  have h3 : MulAut.conj (⟨e, heH⟩ : H) = 1 := by
    rw [← MulAut.conjNormal_val]; exact h1
  have h4 := conj_injective_of_center_eq_bot hH (h3.trans (map_one _).symm)
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h4

theorem range_toOutSemidirect : (toOutSemidirect H).range = outSemidirect (outerAction H) := by
  apply le_antisymm
  · rintro _ ⟨e, rfl⟩
    exact toOutSemidirect_mem H e
  · rintro ⟨a, x⟩ hx
    induction x using QuotientGroup.induction_on with | H e => ?_
    rw [mem_outSemidirect, outerAction_mk, eq_comm, QuotientGroup.eq] at hx
    obtain ⟨h, hh⟩ := hx
    refine ⟨e * h, ?_⟩
    have hhe : (QuotientGroup.mk (e * h : E) : E ⧸ H) = QuotientGroup.mk e := by
      rw [QuotientGroup.eq]
      simp
    ext1
    · change MulAut.conjNormal (e * (h : E)) = a
      rw [map_mul, MulAut.conjNormal_val, hh, mul_inv_cancel_left]
    · exact hhe

/-- **Reconstruction of an extension from its outer action** ([AbsTopII], §0): for a normal
subgroup `H ⊴ E` with trivial center, `E ≃ H ⋊^out (E/H)`. -/
noncomputable def extensionEquivOutSemidirect (hH : Subgroup.center H = ⊥) :
    E ≃* outSemidirect (outerAction H) :=
  (MonoidHom.ofInjective (toOutSemidirect_injective H hH)).trans
    (MulEquiv.subgroupCongr (range_toOutSemidirect H))

theorem extensionEquivOutSemidirect_apply (hH : Subgroup.center H = ⊥) (e : E) :
    (extensionEquivOutSemidirect H hH e : MulAut H × (E ⧸ H)) =
      (MulAut.conjNormal e, QuotientGroup.mk e) := rfl

end Extension

end Iut.Reconstruction
