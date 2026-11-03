/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GlobalRho
import Iut.Cor312.ThetaData.Basic

/-!
# The global data of `F^⊩_mod`, `D^⊚` and `D^⊚±` (IUT I, Ex. 3.5, Defs. 4.1 (v), 6.1 (v))

The global (non-prime-strip) objects of a `Θ^{±ell}NF`-Hodge theater built from initial Θ-data
`D`; the prime-strips themselves are in `Iut/Multiradial/PrimeStrip/` (MR20).

* `Vp D`: `V ≅ V_mod`, the places of `F_mod` (IUT I, Definition 3.1 (e)); `Kfin`, `Karc`: the
  local fields `K_v` at the places of the section;
* **`FRlfGlobal D`**: the global realified Frobenioid `C^⊩` with an equivalence to
  `rlfModel D = C^⊩_mod` (IUT I, Example 3.5 (ii)); `Prime(C^⊩) ≅ V` and `ρ_v` derived from it;
  isomorphisms `FRlfGlobal.Iso` (properties in `FRlfMod.lean`, `FRlfIso.lean`);
* `DCirc`, `DCircPm`: isomorphs of `D^⊚ = B(C̲_K)^0` and `D^⊚± = B(X̲_K)^0` (IUT I,
  Definitions 4.1 (v), 6.1 (v)), recorded by their (étale) fundamental groups (a category
  `B(Π)^0` determines and is determined by `Π` up to inner automorphism, [AbsTopI]);
* `unitsOne`, `OxMu`: the units of norm one of a normed field and `O^{×μ} = O^×/μ`.
-/

namespace Iut

namespace HodgeTheater

open CategoryTheory NumberField Frobenioid

universe u

/-- **A topological group** (bundled). -/
structure TGrp : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [grp : Group carrier]
  [top : TopologicalSpace carrier]

attribute [instance] TGrp.grp TGrp.top

section Models

variable (D : InitialThetaData.{u})

/-- **`V ≅ V_mod`**: the places of `F_mod`, indexing the prime-strips (IUT I, Definition 3.1(e):
the section `V_mod → V(K)` identifies `V_mod` with `V`). -/
abbrev Vp : Type u := Place ↥(fieldOfModuli D.F D.E)

/-- The local field `K_v` at a finite place of the section. -/
abbrev Kfin (w : FinitePlace ↥(fieldOfModuli D.F D.E)) : Type u :=
  completionAt D.Kt (D.V.sectFin w)

/-- The local field `K_v` at an archimedean place of the section. -/
abbrev Karc (w : InfinitePlace ↥(fieldOfModuli D.F D.E)) : Type u := (D.V.sectInf w).Completion

/-- **The global realified Frobenioid `C^⊩_mod` of `F_mod`** (IUT I, Example 3.5(i); P15). -/
noncomputable def rlfModel : Cat.{u, u} := Cat.of (GlobalRealified ↥(fieldOfModuli D.F D.E))

namespace FRlfMod

/-- The place `v̲ ∈ V ⊆ V(K)` lying over `v ∈ V_mod` (IUT I, Definition 3.1(e)). -/
noncomputable def sectPlace : Vp D → GlobalRealified.Place D.Kt
  | Sum.inl v => Sum.inl (D.V.sectFin v)
  | Sum.inr v => Sum.inr (D.V.sectInf v)

/-- `ρ_v` of `F^⊩_mod`: `Φ_{C^⊩_mod} → ℝ` (`ρ_v` on `Φ_v`). -/
noncomputable def rhoMod (v : Vp D) : ArithDiv ↥(fieldOfModuli D.F D.E) → ℝ :=
  GlobalRealified.rho (sectPlace D v) v

end FRlfMod

/-- **The global data of `F^⊩_mod`** (IUT I, Example 3.5(ii); Definition 5.2(iv)(a), (f)): a
category `C^⊩` with an identification with the model `C^⊩_mod`.

IUT I, Definition 5.2(iv), requires the collection `(C^⊩, Prime(C^⊩) ≅ V, F^⊢, {ρ_v})` to be
isomorphic to `F^⊩_mod` (condition (f)), and `Prime(−)` is computed from the Frobenioid structure of
`C^⊩` (condition (b)), which is the one transported from `C^⊩_mod` along such an isomorphism. Hence
the bijection `Prime(C^⊩) ≅ V` and the maps `ρ_v` are not inputs: they are those of `F^⊩_mod`
transported along `equiv` (`FRlfGlobal.prime`, `FRlfGlobal.rho`), and an isomorphism `C^⊩₁ ≌ C^⊩₂`
acts on them through the induced `Ψ_Prime`, `Ψ_Φ` of the conjugated autoequivalence of `C^⊩_mod`
(`HodgeTheater/FRlfIso.lean`). The `F^⊩`-prime-strips (with the `F^⊢`-prime-strip and the
`ρ_v` into its realified divisor monoids) are `Multiradial.PrimeStrip.FRlfStrip`. -/
structure FRlfGlobal where
  /-- The global realified Frobenioid. -/
  C : Cat.{u, u}
  /-- Its identification with `C^⊩_mod`. -/
  equiv : C ≌ rlfModel D

namespace FRlfGlobal

variable {D}

/-- **`Prime(C^⊩) ≅ V`**: through `equiv`, `Prime(C^⊩) = Prime(C^⊩_mod) ≅ V(F_mod) = V`
(`GlobalRealified.primeEquiv`). -/
noncomputable def prime (_G : FRlfGlobal D) :
    GlobalRealified.Prime ↥(fieldOfModuli D.F D.E) ≃ Vp D :=
  GlobalRealified.primeEquiv

/-- **The local-global maps `ρ_v : Φ_{C^⊩,v} → ℝ_{≥0}`**, through `equiv` those of `F^⊩_mod`
(`FRlfMod.rhoMod`). -/
noncomputable def rho (_G : FRlfGlobal D) : Vp D → ArithDiv ↥(fieldOfModuli D.F D.E) → ℝ :=
  FRlfMod.rhoMod D

/-- **An isomorphism of the global data of `F^⊩`-prime-strips** (IUT I, Definition 5.2(iv): an
isomorphism of the collections of data): an equivalence `C^⊩₁ ≌ C^⊩₂` together with a natural
isomorphism identifying it, through the `equiv`s, with the identity of `C^⊩_mod`.

The natural isomorphism is unique when it exists (`GlobalRealified.unique_of_inducesIdRatFun`), and
it exists if and only if the conjugated autoequivalence of `C^⊩_mod` is compatible with
`Prime(−) ≅ V` and with the `ρ_v` (`FRlfGlobal.Iso.ofCompat`, `FRlfGlobal.Iso.placeEquiv_conj`,
`FRlfGlobal.Iso.rho_psiPhi_conj`, `HodgeTheater/FRlfIso.lean`), which is the compatibility required
by Definition 5.2(iv). -/
structure Iso (A B : FRlfGlobal D) where
  /-- `C^⊩₁ ≌ C^⊩₂`. -/
  equiv : A.C ≌ B.C
  /-- Compatibility with the identifications with `C^⊩_mod`. -/
  comm : equiv.functor ⋙ B.equiv.functor ≅ A.equiv.functor

/-- The isomorphism `A ≅ B` through `F^⊩_mod`. -/
noncomputable def Iso.viaModel (A B : FRlfGlobal D) : A.Iso B where
  equiv := A.equiv.trans B.equiv.symm
  comm := Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ B.equiv.counitIso ≪≫
    Functor.rightUnitor _

end FRlfGlobal

/-- **`F^⊩_mod`** (global part), constructed from the Θ-data. -/
noncomputable def FRlfGlobal.ofThetaData : FRlfGlobal D where
  C := rlfModel D
  equiv := CategoryTheory.Equivalence.refl

/-! ### The global objects `D^⊚`, `D^⊚±` -/

/-- **`π_1(D^⊚) = Π_{C̲_K}`** (IUT I, Definition 4.1(v): `D^⊚ = B(C̲_K)^0`). -/
noncomputable def dCircModel : TGrp.{u} := ⟨D.orb.CKu.genuinePi1⟩

/-- **`π_1(D^⊚±) = Π_{X̲_K}`** (IUT I, Definition 6.1(v): `D^⊚± = B(X̲_K)^0`). -/
noncomputable def dCircPmModel : TGrp.{u} := ⟨D.orb.XKu.genuinePi1⟩

/-- An isomorph of `D^⊚` (recorded by its fundamental group). -/
structure DCirc where
  /-- The fundamental group. -/
  G : TGrp.{u}
  iso_model : Nonempty (G.carrier ≃ₜ* (dCircModel D).carrier)

/-- An isomorph of `D^⊚±` (recorded by its fundamental group). -/
structure DCircPm where
  /-- The fundamental group. -/
  G : TGrp.{u}
  iso_model : Nonempty (G.carrier ≃ₜ* (dCircPmModel D).carrier)

/-- The tautological `D^⊚`. -/
noncomputable def DCirc.tautological : DCirc D := ⟨dCircModel D, ⟨ContinuousMulEquiv.refl _⟩⟩

/-- The tautological `D^⊚±`. -/
noncomputable def DCircPm.tautological : DCircPm D :=
  ⟨dCircPmModel D, ⟨ContinuousMulEquiv.refl _⟩⟩

end Models

/-! ### `O^{×μ}` of a normed field -/

/-- The units of norm one of a normed field. -/
def unitsOne (L : Type u) [NormedField L] : Subgroup Lˣ where
  carrier := {x | ‖(x : L)‖ = 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul, norm_mul] at ha hb ⊢
    rw [ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, norm_inv] at ha ⊢
    rw [ha, inv_one]

/-- **`O^{×μ}(L) = O^×(L)/μ(L)`** (IUT II, Definition 4.9): the units of norm one modulo
torsion. -/
abbrev OxMu (L : Type u) [NormedField L] : Type u :=
  unitsOne L ⧸ CommGroup.torsion (unitsOne L)

end HodgeTheater

end Iut
