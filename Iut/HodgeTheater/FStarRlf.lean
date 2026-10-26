/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.DStar
import Iut.HodgeTheater.FRlfIso

/-!
# The realified global Frobenioid `F^⊛R_mod` and `F^⊩` from `F^⊛` (IUT II, Corollaries 4.7, 4.8)

IUT II, Corollary 4.7(i) (l.10457–10535 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller
Theory II.txt`) constructs the Frobenioids `F^⊛_mod(†D^⊚) ⊆ F^⊛(†D^⊚)` and "the realification
`F^⊛_mod → F^⊛R_mod`"; Corollary 4.8(iii) (l.11393–11444) identifies `†C^⊩_j ≅ (†F^⊛R_mod)_j`.
Field-theoretically, first over the Galois base `B(Gal(F̄/F_mod))⁰` (`HodgeTheater/FStarMod.lean`),
then over IUT's base `†D^⊛ = B(π₁(C_{F_mod}))⁰` (`HodgeTheater/DStar.lean`):

* `GlobalRealified.mapRingEquiv τ : C^⊩(K) ≌ C^⊩(L)` for a ring isomorphism `τ : K ≅ L`
  (divisors pulled back by `pbR τ`);
* `globalFrobenioidRlfMod D`: the objects of the realification `C^rlf_{F̄/F_mod}` over the
  terminal object `G/G`, `modRlfEquiv D : C^⊩_mod ≌` it (the fibre over `G/G`, `fibreRlf`, and
  `F_mod ≅ F̄^G`), and `modToRlf D`, the restriction of the realification
  `C_{F̄/F_mod} → C^rlf_{F̄/F_mod}` ([FrdI], Proposition 5.3);
* over `†D^⊛`: **`globalFrobenioidRlfStar D = F^⊛R`** (the pull-back of `C^rlf_{F̄/F_mod}` along
  `π₁(C_{F_mod}) ↠ Gal(F̄/F_mod)`, a Frobenioid), the realification **`realifyStar D : F^⊛ ⥤ F^⊛R`**
  (`Model.mapFunctor` of `castG`, lying over the Galois-base realification,
  `realifyStar_comp_starRlfToGal`), **`globalFrobenioidRlfStarMod D = F^⊛R_mod`** (objects over the
  terminal object `Π/Π`), `starRlfModEquiv D` (≌ the Galois-base version),
  **`modRlfStarEquiv D : C^⊩_mod ≌ F^⊛R_mod`**, and **`modToRlfStar D : F^⊛_mod ⥤ F^⊛R_mod`**,
  compatible with `modToRlf` under `starModEquiv`/`starRlfModEquiv` (`starModToRlfIso`);
* **`FRlfGlobal.ofGlobalFrobenioid D`**: the global data of an `F^⊩`-prime-strip with
  `C^⊩ = F^⊛R_mod` over `†D^⊛` (IUT II, Corollary 4.8(iii), global part).
-/

namespace Iut

namespace Frobenioid

namespace GlobalRealified

open CategoryTheory NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] (τ : K ≃+* L)

lemma pbR_symm_pbR (x : ArithDiv K) : pbR (τ.symm : L →+* K) (pbR (τ : K →+* L) x) = x := by
  have h : (τ.symm : L →+* K).comp (τ : K →+* L) = RingHom.id K := by ext; simp
  rw [pbR_comp, h, pbR_id]

lemma pbR_pbR_symm (y : ArithDiv L) : pbR (τ : K →+* L) (pbR (τ.symm : L →+* K) y) = y := by
  have h : (τ : K →+* L).comp (τ.symm : L →+* K) = RingHom.id L := by ext; simp
  rw [pbR_comp, h, pbR_id]

/-- **`C^⊩(K) → C^⊩(L)` along a ring isomorphism `τ : K ≅ L`**: `(pt, α) ↦ (pt, τ^*α)`,
`(n, Z, u) ↦ (n, τ^*Z, τ^*u)`. -/
noncomputable def mapRingEquiv : GlobalRealified K ⥤ GlobalRealified L where
  obj X := ⟨pt, pbR (τ : K →+* L) X.α⟩
  map {X Y} φ := Model.mk' φ.deg (𝟙 _) (pbR (τ : K →+* L) φ.div)
    ((pbR_mem_iff _ _).mpr φ.div_mem) (pbRat (τ : K →+* L) φ.u) (by
      change (φ.deg : ℕ) • pbR (τ : K →+* L) X.α + pbR (τ : K →+* L) φ.div =
        pbR (τ : K →+* L) Y.α + pbR (τ : K →+* L) φ.u
      rw [← map_nsmul, ← map_add, ← map_add, rel_eq φ])
  map_id X := Model.hom_ext rfl rfl (map_zero _) (Subtype.ext (map_zero (pbR (τ : K →+* L))))
  map_comp {X Y Z} φ ψ := by
    refine Model.hom_ext rfl rfl ?_ (Subtype.ext ?_)
    · change pbR (τ : K →+* L) (ψ.div + (ψ.deg : ℕ) • φ.div) =
        pbR (τ : K →+* L) ψ.div + (ψ.deg : ℕ) • pbR (τ : K →+* L) φ.div
      rw [map_add, map_nsmul]
    · change pbR (τ : K →+* L) ((ψ.u : ArithDiv K) + (ψ.deg : ℕ) • (φ.u : ArithDiv K)) =
        pbR (τ : K →+* L) ψ.u + (ψ.deg : ℕ) • pbR (τ : K →+* L) φ.u
      rw [map_add, map_nsmul]

instance : (mapRingEquiv τ).Faithful where
  map_injective {X Y} φ ψ h := by
    have h1 : ((mapRingEquiv τ).map φ).deg = ((mapRingEquiv τ).map ψ).deg := by rw [h]
    have h3 : ((mapRingEquiv τ).map φ).div = ((mapRingEquiv τ).map ψ).div := by rw [h]
    have h4 : (((mapRingEquiv τ).map φ).u : ArithDiv L) = ((mapRingEquiv τ).map ψ).u := by rw [h]
    exact Model.hom_ext h1 (Subsingleton.elim _ _) (pbR_injective _ h3)
      (Subtype.ext (pbR_injective _ h4))

instance : (mapRingEquiv τ).Full where
  map_surjective {X Y} ψ := by
    have r := rel_eq ψ
    change (ψ.deg : ℕ) • pbR (τ : K →+* L) X.α + ψ.div =
      pbR (τ : K →+* L) Y.α + (ψ.u : ArithDiv L) at r
    refine ⟨Model.mk' ψ.deg (eqToHom (Subsingleton.elim _ _)) (pbR (τ.symm : L →+* K) ψ.div)
      ((pbR_mem_iff _ _).mpr ψ.div_mem) (pbRat (τ.symm : L →+* K) ψ.u) ?_, ?_⟩
    · change (ψ.deg : ℕ) • X.α + pbR (τ.symm : L →+* K) ψ.div =
        Y.α + pbR (τ.symm : L →+* K) ψ.u
      have := congrArg (pbR (τ.symm : L →+* K)) r
      rwa [map_add, map_add, map_nsmul, pbR_symm_pbR, pbR_symm_pbR] at this
    · refine Model.hom_ext rfl (Subsingleton.elim _ _) (pbR_pbR_symm τ _)
        (Subtype.ext (pbR_pbR_symm τ _))

instance : (mapRingEquiv τ).EssSurj where
  mem_essImage Y := ⟨⟨pt, pbR (τ.symm : L →+* K) Y.α⟩, ⟨eqToIso (by
    change (⟨pt, pbR (τ : K →+* L) (pbR (τ.symm : L →+* K) Y.α)⟩ : GlobalRealified L) = Y
    rw [pbR_pbR_symm])⟩⟩

instance : (mapRingEquiv τ).IsEquivalence where

/-- **`C^⊩(K) ≌ C^⊩(L)` for `K ≅ L`.** -/
noncomputable def congr : GlobalRealified K ≌ GlobalRealified L := (mapRingEquiv τ).asEquivalence

end GlobalRealified

namespace GlobalGaloisFrob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [IsGalois F E]

/-- `u ↦ div(u)` as a homomorphism `B(A) → B^rlf(A)`. -/
noncomputable def realifyUHom (A : OrbitObj (GalG F E)) :
    (bGalNF F E).obj A →+ (bRlfGal F E).obj A :=
  AddMonoidHom.mk' (realifyU A) (realifyU_add A)

/-- The realification of `C_{F̄/F}` is the functor induced by `castG` and `realifyU`. -/
theorem realify_eq_mapFunctor :
    realify F E = Model.mapFunctor (fun A => castG (Fix A)) (fun _ x => castG_pbDiv _ x)
      (fun _ x hx => (castG_mem_iff x).mpr hx) realifyUHom (fun f u => realifyU_pb f u)
      (fun _ _ => rfl) :=
  rfl

end GlobalGaloisFrob

end Frobenioid

namespace HodgeTheater

open CategoryTheory NumberField Frobenioid

variable (D : InitialThetaData.{0})

/-- The realified global Frobenioid `C^rlf_{F̄/F_mod}` ([FrdI], Proposition 5.3). -/
abbrev globalFrobenioidRlf : Type := GlobalGaloisRlf (Fmod D) D.Fbar

/-- The objects of `C^rlf_{F̄/F_mod}` over the terminal object `G/G`. -/
def overTopRlf : ObjectProperty (globalFrobenioidRlf D) :=
  fun X => X.base = topObj (Fmod D) D.Fbar

/-- **`F^⊛R_mod`**: the realified global Frobenioid over the terminal objects (IUT II,
Corollary 4.7(i)). -/
abbrev globalFrobenioidRlfMod : Type := (overTopRlf D).FullSubcategory

/-- The fibre functor `C^⊩(F̄^G) → F^⊛R_mod`. -/
noncomputable def modRlfFunctor :
    GlobalRealified (Fix (topObj (Fmod D) D.Fbar)) ⥤ globalFrobenioidRlfMod D :=
  (overTopRlf D).lift (GlobalGaloisRlf.fibreRlf _) fun _ => rfl

instance : (modRlfFunctor D).Faithful := by unfold modRlfFunctor; infer_instance

instance : (modRlfFunctor D).Full where
  map_surjective {X Y} ψ := by
    obtain ⟨φ, hφ⟩ := GlobalGaloisRlf.fibreRlf_preimage _ ψ.hom
      (Subsingleton.elim (α := topObj (Fmod D) D.Fbar ⟶ topObj (Fmod D) D.Fbar) _ _)
    exact ⟨φ, ObjectProperty.hom_ext _ hφ⟩

instance : (modRlfFunctor D).EssSurj where
  mem_essImage Y := by
    obtain ⟨⟨B, α⟩, hB⟩ := Y
    change B = topObj _ _ at hB
    subst hB
    exact ⟨⟨pt, α⟩, ⟨ObjectProperty.isoMk _ (Iso.refl _)⟩⟩

instance : (modRlfFunctor D).IsEquivalence where

/-- **`C^⊩_mod ≌ F^⊛R_mod`** (through `F_mod ≅ F̄^G`, `fixTopEquiv`). -/
noncomputable def modRlfEquiv : GlobalRealified (Fmod D) ≌ globalFrobenioidRlfMod D :=
  (GlobalRealified.congr (fixTopEquiv (Fmod D) D.Fbar)).trans (modRlfFunctor D).asEquivalence

/-- **The realification `F^⊛_mod → F^⊛R_mod`** (IUT II, Corollary 4.7(i)): the restriction of
`C_{F̄/F_mod} → C^rlf_{F̄/F_mod}` ([FrdI], Proposition 5.3) to the objects over `G/G`. -/
noncomputable def modToRlf : globalFrobenioidMod D ⥤ globalFrobenioidRlfMod D :=
  (overTopRlf D).lift ((overTop D).ι ⋙ GlobalGaloisFrob.realify (Fmod D) D.Fbar) fun X => X.2

/-! ### `F^⊛R` over IUT's base `†D^⊛ = B(π₁(C_{F_mod}))⁰` -/

/-- The realified divisor monoid on `†D^⊛`: `Φ^rlf` of the subfield of `F̄` fixed by the image of
`A` in `Gal(F̄/F_mod)`. -/
noncomputable abbrev phiRlfStar : DivMonoid.{0} (DStar D) :=
  (phiRlfGal (Fmod D) D.Fbar).comap (toGalBase D) (toGalBase_isFSM D)

/-- The realified rational functions on `†D^⊛`. -/
noncomputable abbrev bRlfStar : GrpOn.{0} (DStar D) :=
  (bRlfGal (Fmod D) D.Fbar).comap (toGalBase D) (toGalBase_isFSM D)

/-- `Div_B` on `†D^⊛`. -/
noncomputable abbrev divRlfStar : DivHom (bRlfStar D) (phiRlfStar D).toGrpOn :=
  (divRlfGal (Fmod D) D.Fbar).comap (toGalBase D) (toGalBase_isFSM D)

/-- **The realified global Frobenioid `F^⊛R` over `†D^⊛`** ([FrdI], Proposition 5.3; IUT II,
Corollary 4.7(i)). -/
abbrev globalFrobenioidRlfStar : Type := Model (phiRlfStar D) (bRlfStar D) (divRlfStar D)

/-- **`F^⊛R` is a Frobenioid** ([FrdI], Theorem 5.2(ii)). -/
theorem globalFrobenioidRlfStar_isFrobenioid :
    IsFrobenioid (Model.toElem (phiRlfStar D) (bRlfStar D) (divRlfStar D)) :=
  Model.isFrobenioid

/-- The change of base `F^⊛R → C^rlf_{F̄/F_mod}`. -/
noncomputable def starRlfToGal : globalFrobenioidRlfStar D ⥤ globalFrobenioidRlf D :=
  Model.comapFunctor (toGalBase D) (toGalBase_isFSM D)

/-- **The realification `F^⊛ → F^⊛R` over `†D^⊛`** ([FrdI], Proposition 5.3): the identity on
the base, `castG` on divisors (the realification of `C_{F̄/F_mod}`, pulled back along
`toGalBase`). -/
noncomputable def realifyStar : globalFrobenioidStar D ⥤ globalFrobenioidRlfStar D :=
  Model.mapFunctor (Φ := phiStar D) (Φ' := phiRlfStar D) (B := bStar D) (B' := bRlfStar D)
    (divB := divStar D) (divB' := divRlfStar D)
    (fun A => castG (Fix ((toGalBase D).obj A))) (fun _ x => castG_pbDiv _ x)
    (fun _ x hx => (castG_mem_iff x).mpr hx)
    (fun A => GlobalGaloisFrob.realifyUHom ((toGalBase D).obj A))
    (fun f u => GlobalGaloisFrob.realifyU_pb ((toGalBase D).map f) u) (fun _ _ => rfl)

/-- **`realifyStar` lies over the realification of `C_{F̄/F_mod}`.** -/
theorem realifyStar_comp_starRlfToGal :
    realifyStar D ⋙ starRlfToGal D = starToGal D ⋙ GlobalGaloisFrob.realify (Fmod D) D.Fbar := by
  rw [GlobalGaloisFrob.realify_eq_mapFunctor]
  exact Model.mapFunctor_comapFunctor (Φ := phiGal (Fmod D) D.Fbar)
    (Φ' := phiRlfGal (Fmod D) D.Fbar) (B := bGalNF (Fmod D) D.Fbar)
    (B' := bRlfGal (Fmod D) D.Fbar)
    (divB := divGalNF (Fmod D) D.Fbar) (divB' := divRlfGal (Fmod D) D.Fbar)
    (fun A => castG (Frobenioid.Fix A)) (fun _ x => castG_pbDiv _ x)
    (fun _ x hx => (castG_mem_iff x).mpr hx) GlobalGaloisFrob.realifyUHom
    (fun f u => GlobalGaloisFrob.realifyU_pb f u) (fun _ _ => rfl) (toGalBase D)
    (toGalBase_isFSM D)

/-- **`F^⊛R_mod` over `†D^⊛`**: the objects of `F^⊛R` over the terminal object `Π/Π`
(IUT II, Corollary 4.7(i)). -/
abbrev globalFrobenioidRlfStarMod : Type :=
  (Model.over (Φ := phiRlfStar D) (B := bRlfStar D) (divB := divRlfStar D)
    OrbitObj.top).FullSubcategory

/-- **`F^⊛R_mod` over `†D^⊛` is `F^⊛R_mod` over `B(Gal(F̄/F_mod))⁰`.** -/
noncomputable def starRlfModEquiv : globalFrobenioidRlfStarMod D ≌ globalFrobenioidRlfMod D :=
  (Model.comapOverEquiv (toGalBase D) (toGalBase_isFSM D) OrbitObj.top).trans
    (Model.overEquivOfEq (toGalBase_top D))

/-- **`C^⊩_mod ≌ F^⊛R_mod`** over IUT's base `†D^⊛`. -/
noncomputable def modRlfStarEquiv : GlobalRealified (Fmod D) ≌ globalFrobenioidRlfStarMod D :=
  (modRlfEquiv D).trans (starRlfModEquiv D).symm

/-- **The realification `F^⊛_mod → F^⊛R_mod` over `†D^⊛`** (IUT II, Corollary 4.7(i)): the
restriction of `realifyStar` to the objects over `Π/Π`. -/
noncomputable def modToRlfStar : globalFrobenioidStarMod D ⥤ globalFrobenioidRlfStarMod D :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ realifyStar D) fun X => X.2

/-- The realifications over `†D^⊛` and over `B(Gal(F̄/F_mod))⁰` correspond under `starModEquiv`
and `starRlfModEquiv`. -/
noncomputable def starModToRlfIso :
    (starModEquiv D).functor ⋙ modToRlf D ≅ modToRlfStar D ⋙ (starRlfModEquiv D).functor :=
  Iso.refl _

/-- The same square with the inverse equivalences. -/
noncomputable def starModToRlfIso' :
    (starModEquiv D).inverse ⋙ modToRlfStar D ≅ modToRlf D ⋙ (starRlfModEquiv D).inverse :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft ((starModEquiv D).inverse ⋙ modToRlfStar D)
      (starRlfModEquiv D).unitIso ≪≫
    Functor.isoWhiskerLeft (starModEquiv D).inverse
      (Functor.isoWhiskerRight (starModToRlfIso D).symm (starRlfModEquiv D).inverse) ≪≫
    Functor.isoWhiskerRight (starModEquiv D).counitIso (modToRlf D ⋙ (starRlfModEquiv D).inverse)
    ≪≫ Functor.leftUnitor _

/-- **The global data of an `F^⊩`-prime-strip from the global Frobenioid**:
`C^⊩ = F^⊛R_mod` over IUT's base `†D^⊛`, with `C^⊩_mod ≌ F^⊛R_mod` (IUT II, Corollary 4.8(iii),
global part: `†C^⊩ ≅ †F^⊛R_mod`). -/
noncomputable def _root_.Iut.HodgeTheater.FRlfGlobal.ofGlobalFrobenioid : FRlfGlobal D where
  C := Cat.of (globalFrobenioidRlfStarMod D)
  equiv := (modRlfStarEquiv D).symm

end HodgeTheater

end Iut
