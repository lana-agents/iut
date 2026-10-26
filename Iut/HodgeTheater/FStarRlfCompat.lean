/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.FStarRlf

/-!
# `F^⊛_mod → F^⊛R_mod` is the realification of `C(F_mod)`

IUT II Cor 4.7 (i) / [FrdI] Prop 5.3: the restriction `modToRlf : F^⊛_mod → F^⊛R_mod` of the
realification `C_{F̄/F_mod} → C^rlf_{F̄/F_mod}` to the objects over the terminal object `G/G`
(`HodgeTheater/FStarRlf.lean`) corresponds, under `modEquiv : C(F_mod) ≌ F^⊛_mod` and
`modRlfEquiv : C^⊩(F_mod) ≌ F^⊛R_mod`, to the realification `C(F_mod) → C^⊩(F_mod)` of the
Frobenioid of [FrdI] Ex 6.3 over the one-morphism base:

* `castG_eTop_symm`, `realifyU_uTop`: the divisor and rational-function components agree
  (`castG ∘ eTop⁻¹ = τ^* ∘ castDiv` and the same on `F_mod^×`, `τ = fixTopEquiv`);
* **`modToRlfIso : modEquiv.functor ⋙ modToRlf ≅ realify ⋙ modRlfEquiv.functor`**;
* over IUT's base `†D^⊛`: **`modToRlfStarIso : starModEquivC.functor ⋙ modToRlfStar ≅
  realify ⋙ modRlfStarEquiv.functor`** (from `modToRlfIso` and `starModToRlfIso'`).
-/

namespace Iut

namespace HodgeTheater

open CategoryTheory NumberField Frobenioid GlobalGaloisFrob GlobalGaloisRlf

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [IsGalois F E]

/-- The divisor component: `castG (eTop⁻¹ α) = τ^* (castDiv α)` for `τ = fixTopEquiv`. -/
lemma castG_eTop_symm (α : ArithDivZ F) :
    castG (Fix (topObj F E)) ((eTop F E).symm α) =
      pbR ((fixTopEquiv F E : F →+* Fix (topObj F E))) (castDiv F α) := by
  have h : (eTop F E).symm α = pbDiv (fixTopEquiv F E : F →+* Fix (topObj F E))
      ((toZ F).symm α) := rfl
  rw [h, castG_pbDiv, castG_apply, AddEquiv.apply_symm_apply]

/-- The rational-function component: the realification of `uTop u` is `τ^*` of the
realification of `u`. -/
lemma realifyU_uTop (u : Additive Fˣ) :
    (realifyU (topObj F E) (uTop F E u)).1 =
      pbR ((fixTopEquiv F E : F →+* Fix (topObj F E)))
        (castDiv F (divZ F u)) := by
  change castG _ ((divGalNF F E).app (topObj F E) (uTop F E u)) = _
  rw [← eTop_symm_divZ, castG_eTop_symm]

end HodgeTheater

namespace Frobenioid.Model

open CategoryTheory

variable {D : Type*} [Category D] {Φ : DivMonoid D} {B : GrpOn D} {divB : DivHom B Φ.toGrpOn}

lemma eqToHom_deg {X Y : Model Φ B divB} (h : X = Y) : (eqToHom h).deg = 1 := by subst h; rfl

lemma eqToHom_div {X Y : Model Φ B divB} (h : X = Y) : (eqToHom h).div = 0 := by subst h; rfl

lemma eqToHom_u {X Y : Model Φ B divB} (h : X = Y) : (eqToHom h).u = 0 := by subst h; rfl

lemma eqToHom_base {X Y : Model Φ B divB} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg Model.base h) := by subst h; rfl

end Frobenioid.Model

namespace HodgeTheater

open CategoryTheory NumberField Frobenioid GlobalGaloisFrob GlobalGaloisRlf

variable (D : InitialThetaData.{0})

lemma modToRlf_obj_hom (X : GlobalFrobenioid (Fmod D)) :
    ((modToRlf D).obj ((modEquiv D).functor.obj X)).obj =
      ((modRlfEquiv D).functor.obj ((GlobalFrobenioid.realify (Fmod D)).obj X)).obj := by
  obtain ⟨⟨⟩, α⟩ := X
  change (⟨topObj (Fmod D) D.Fbar, castG _ ((eTop (Fmod D) D.Fbar).symm α)⟩ :
      globalFrobenioidRlf D) = ⟨topObj (Fmod D) D.Fbar,
        pbR ((fixTopEquiv (Fmod D) D.Fbar : Fmod D →+* Fix (topObj (Fmod D) D.Fbar)))
          (castDiv _ α)⟩
  rw [castG_eTop_symm]

/-- **`modToRlf` is the realification of `C(F_mod)`** (IUT II Cor 4.7 (i), [FrdI] Prop 5.3):
`modEquiv ⋙ modToRlf ≅ realify ⋙ modRlfEquiv`. -/
noncomputable def modToRlfIso :
    (modEquiv D).functor ⋙ modToRlf D ≅
      GlobalFrobenioid.realify (Fmod D) ⋙ (modRlfEquiv D).functor :=
  NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (eqToIso (modToRlf_obj_hom D X)))
    (fun {X Y} φ => by
      obtain ⟨⟨⟩, α⟩ := X
      obtain ⟨⟨⟩, β⟩ := Y
      refine ObjectProperty.hom_ext _ (Model.hom_ext ?_ ?_ ?_ ?_)
      · simp [Model.eqToHom_deg]
        rfl
      · exact Subsingleton.elim (α := topObj (Fmod D) D.Fbar ⟶ topObj (Fmod D) D.Fbar) _ _
      · simp only [Functor.comp_map, ObjectProperty.isoMk_hom, eqToIso.hom,
          ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, Model.comp_div,
          Model.eqToHom_div, Model.eqToHom_deg, Model.eqToHom_base, PNat.one_coe, one_smul,
          smul_zero, add_zero, map_zero, zero_add]
        erw [eqToHom_refl, (phiRlfGal (Fmod D) D.Fbar).pb_id]
        exact castG_eTop_symm (E := D.Fbar) φ.div
      · simp only [Functor.comp_map, ObjectProperty.isoMk_hom, eqToIso.hom,
          ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, Model.comp_u,
          Model.eqToHom_u, Model.eqToHom_deg, Model.eqToHom_base, PNat.one_coe, one_smul,
          smul_zero, add_zero, map_zero, zero_add]
        erw [eqToHom_refl, (bRlfGal (Fmod D) D.Fbar).pb_id]
        exact Subtype.ext (realifyU_uTop (E := D.Fbar) φ.u))

/-- **The realification `F^⊛_mod → F^⊛R_mod` over IUT's base `†D^⊛` is the realification of
`C(F_mod)`** (IUT II Cor 4.7 (i), [FrdI] Prop 5.3):
`starModEquivC ⋙ modToRlfStar ≅ realify ⋙ modRlfStarEquiv`. -/
noncomputable def modToRlfStarIso :
    (starModEquivC D).functor ⋙ modToRlfStar D ≅
      GlobalFrobenioid.realify (Fmod D) ⋙ (modRlfStarEquiv D).functor :=
  Functor.isoWhiskerLeft (modEquiv D).functor (starModToRlfIso' D) ≪≫
    Functor.isoWhiskerRight (modToRlfIso D) (starRlfModEquiv D).inverse

end HodgeTheater

end Iut
