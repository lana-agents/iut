/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.FRlfMod
import Iut.Frobenioid.Thm64ivCompat

/-!
# The global Frobenioids `F^⊛` and `F^⊛_mod` from initial Θ-data (IUT I, Example 5.1(ii), (iii))

IUT I, Example 5.1(ii) (l.8412–8433 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller
Theory I.txt`): the monoid `Φ^⊛(†D^⊚)` on `†D^⊛` ("the monoid denoted "Φ(−)" in [FrdI], Example
6.3") with the natural morphism `M^⊛(†D^⊚)_A → Φ^⊛(†D^⊚)(A)^gp` "determines, by applying [FrdI],
Theorem 5.2, (ii), a model Frobenioid `F^⊛(†D^⊚)` over the base category `†D^⊛`". Example 5.1(iii)
(l.8434–8466): "`†F^⊛_mod := †F^⊛|terminal objects` […] the restriction of `†F^⊛` to the full
subcategory of `†D^⊛` determined by the terminal objects [i.e., "`C_{F_mod}`"]".

This file gives the **field-theoretic** version, over the Galois base `B(Gal(F̄/F_mod))⁰` of
[FrdI], Example 6.3, for initial Θ-data `D` (in universe `0`, as `GlobalGaloisFrob`):

* `Fmod D = F_mod`, with `F̄` an `F_mod`-algebra (`F_mod ⊆ F ⊆ F̄`) and `F̄/F_mod` Galois;
* **`globalFrobenioid D = C_{F̄/F_mod}`** (`GlobalGaloisFrob`), a Frobenioid
  (`globalFrobenioid_isFrobenioid`);
* the terminal objects of the base: `topObj` is terminal (`isTerminalTopObj`) and it is the only
  terminal object (`eq_topObj_of_isTerminal`);
* **`globalFrobenioidMod D = F^⊛_mod`**, the full subcategory of objects over terminal objects, and
  **`modEquiv D : C(F_mod) ≌ F^⊛_mod`** with the Frobenioid of [FrdI], Example 6.3 over the
  one-morphism base (`fibreTop`), i.e. "the Frobenioid of arithmetic line bundles" of `F_mod`;
* the realification `F^⊛_mod → C^⊩_mod` (`modRealify`), essentially surjective
  (IUT II, Corollary 4.7(i): "the realification `F^⊛_mod → F^⊛R_mod`").

## Base category

IUT's base is `†D^⊛ = B(π_1(C_{F_mod}))⁰` (the orbicurve `C_{F_mod}`), whose objects are reached
through the surjection `π_1(C_{F_mod}) ↠ Gal(F̄/F_mod)`. This file works over the Galois base
`B(Gal(F̄/F_mod))⁰`; `HodgeTheater/DStar.lean` builds `F^⊛` over IUT's base `†D^⊛` (with
`π_1(C_{F_mod})` iut's genuine `π₁` of `C_{F_mod}`) as the pull-back of this Frobenioid along
`π_1(C_{F_mod}) ↠ Gal(F̄/F_mod)`, and identifies its `F^⊛_mod` with `globalFrobenioidMod D`
(`starModEquiv`); the realification and `F^⊩` (`HodgeTheater/FStarRlf.lean`) are stated over
`†D^⊛`, with this file's Galois-base Frobenioid as an intermediate step.
`π_1(†D^⊛)` is characterised group-theoretically in `HodgeTheater/DStarCore.lean` ([AbsTopII]
Cor. 3.3 (i)). Not formalised: the reconstruction of `M^⊛(†D^⊚)` from `π_1(†D^⊚)` (MR9,
[AbsTopIII] Theorem 1.9; MR22). The divisors are those of
[FrdI], Example 6.3 (not the "stack-theoretic" ones of IUT I, Remark 3.1.5).
-/

namespace Iut

namespace HodgeTheater

open CategoryTheory CategoryTheory.Limits NumberField Frobenioid

variable (D : InitialThetaData.{0})

/-- **`F_mod`**, the field of moduli. -/
abbrev Fmod : Type := ↥(fieldOfModuli D.F D.E)

set_option synthInstance.maxHeartbeats 200000 in
-- the search goes through the `IntermediateField` algebra instances `F_mod → F → F̄`
instance : Module.IsTorsionFree (Fmod D) D.Fbar := inferInstance

instance : FiniteDimensional (Fmod D) D.F := Module.Finite.of_restrictScalars_finite ℚ _ _

instance : IsAlgClosure (Fmod D) D.Fbar := by
  haveI : Algebra.IsAlgebraic (Fmod D) D.F := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic D.F D.Fbar := IsAlgClosure.isAlgebraic
  exact ⟨IsAlgClosure.isAlgClosed D.F, Algebra.IsAlgebraic.trans (Fmod D) D.F D.Fbar⟩

/-- **`F̄/F_mod` is Galois.** -/
instance : IsGalois (Fmod D) D.Fbar := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

/-- **The global Frobenioid `F^⊛ = C_{F̄/F_mod}`** over `B(Gal(F̄/F_mod))⁰` (IUT I, Example
5.1(ii), field-theoretic; [FrdI], Example 6.3). -/
abbrev globalFrobenioid : Type := GlobalGaloisFrob (Fmod D) D.Fbar

/-- **`F^⊛` is a Frobenioid** ([FrdI], Theorem 5.2(ii)). -/
theorem globalFrobenioid_isFrobenioid :
    IsFrobenioid (Model.toElem (phiGal (Fmod D) D.Fbar) (bGalNF (Fmod D) D.Fbar)
      (divGalNF (Fmod D) D.Fbar)) :=
  GlobalGaloisFrob.isFrobenioid _ _

/-! ### The terminal objects of `B(Gal(F̄/F))⁰` -/

section Terminal

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [IsGalois F E]

/-- **`G/G` is terminal.** -/
noncomputable def isTerminalTopObj : IsTerminal (topObj F E) :=
  IsTerminal.ofUniqueHom (fun A => toTopObj A) fun _ _ =>
    OrbitHom.hom_ext (funext fun _ => Subsingleton.elim _ _)

omit [NumberField F] [IsGalois F E] in
/-- **`G/G` is the only terminal object.** -/
theorem eq_topObj_of_isTerminal {A : OrbitObj (GalG F E)} (h : IsTerminal A) :
    A = topObj F E :=
  eq_topObj_of_hom (h.from _)

end Terminal

/-! ### `F^⊛_mod` -/

/-- The objects of `F^⊛` over the terminal object `G/G`. -/
def overTop : ObjectProperty (globalFrobenioid D) :=
  fun X => X.base = topObj (Fmod D) D.Fbar

/-- **`F^⊛_mod = F^⊛|terminal objects`** (IUT I, Example 5.1(iii)). -/
abbrev globalFrobenioidMod : Type := (overTop D).FullSubcategory

/-- The fibre functor `C(F_mod) → F^⊛_mod`. -/
noncomputable def modFunctor : GlobalFrobenioid (Fmod D) ⥤ globalFrobenioidMod D :=
  (overTop D).lift (fibreTop (Fmod D) D.Fbar) fun _ => rfl

instance : (modFunctor D).Faithful := by unfold modFunctor; infer_instance

instance : (modFunctor D).Full := by unfold modFunctor; infer_instance

instance : (modFunctor D).EssSurj where
  mem_essImage Y := by
    obtain ⟨⟨B, α⟩, hB⟩ := Y
    change B = topObj _ _ at hB
    subst hB
    refine ⟨⟨pt, eTop _ _ α⟩, ⟨ObjectProperty.isoMk _ (eqToIso ?_)⟩⟩
    exact fibreTop_obj_mk α

instance : (modFunctor D).IsEquivalence where

/-- **`C(F_mod) ≌ F^⊛_mod`**: `F^⊛_mod` is the Frobenioid of [FrdI], Example 6.3 of `F_mod` over
the one-morphism base ("the Frobenioid of arithmetic line bundles", IUT I, Example 5.1(iii)). -/
noncomputable def modEquiv : GlobalFrobenioid (Fmod D) ≌ globalFrobenioidMod D :=
  (modFunctor D).asEquivalence

/-- **The realification `F^⊛_mod → C^⊩_mod`** (IUT II, Corollary 4.7(i); [FrdI], Proposition
5.3). -/
noncomputable def modRealify : globalFrobenioidMod D ⥤ GlobalRealified (Fmod D) :=
  (modEquiv D).inverse ⋙ GlobalFrobenioid.realify (Fmod D)

instance : (modRealify D).EssSurj := by
  unfold modRealify
  infer_instance

end HodgeTheater

end Iut
