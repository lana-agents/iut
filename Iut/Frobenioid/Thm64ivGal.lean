/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.ModelFib
import Iut.Frobenioid.GlobalGaloisBase
import Iut.Frobenioid.GlobalGaloisFibre
import Iut.Frobenioid.Thm64iv
import Iut.Frobenioid.BaseEquiv

/-!
# [FrdI], Theorem 6.4(iv) over the Galois base `B(Gal(F̃/F))⁰`

[FrdI], Theorem 6.4(iv) (l.5726–5735 of `~/iut-scratch/wall/txt/The Geometry of Frobenioids
I.txt`): "If the equivalence of categories `Ψ^rlf` of (ii) arises from an equivalence of
categories `Ψ : C₁ ≅ C₂` […], then `deg(Ψ^rlf) = 1`. If, moreover, there exists a finite
extension `L₁ ⊆ F̃₁` of `F₁` which is Galois over `ℚ`, then the corresponding [i.e., via the
equivalence `D₁ ≅ D₂` induced by `Ψ` — cf. (i); Corollary 4.11(ii)] finite extension
`L₂ ⊆ F̃₂` of `F₂` is isomorphic to `L₁` […]."

Here `C_i = C_{F̃_i/F_i}` (`GlobalGaloisFrob`), `C_i^rlf` its realification (`GlobalGaloisRlf`),
`Ψ^rlf : C₁^rlf ≌ C₂^rlf`, `Ψ : C₁ ≌ C₂` and "arises from" is a natural isomorphism
`e : realify ⋙ Ψ^rlf ≅ Ψ ⋙ realify`.

## Proof

* `Ψ^rlf` lies over an equivalence `Ψ_Base : B(G₁)⁰ ≌ B(G₂)⁰` (`GlobalGaloisRlf.preservesBase`,
  [FrdI], Corollary 4.11(ii), for `Ψ^rlf` and its inverse; `isEquivalence_base`).
* Through `e`, `Ψ` lies over the same `Ψ_Base` (`baseIsoOfRealify`).
* For every object `A₁ = G₁/H₁` with `A₂ = Ψ_Base(A₁)`, `L_i = F̃_i^{H_i}`, the restrictions of
  `Ψ^rlf`, `Ψ` to the fibres (`Model.resFib`, `ModelFib.lean`) are equivalences
  `GlobalRealified L₁ ≌ GlobalRealified L₂`, `GlobalFrobenioid L₁ ≌ GlobalFrobenioid L₂`
  (`ofFibR`, `ofFibZ`: the fibres of `C^rlf`, `C` are the Frobenioids of `L_i` over the
  one-morphism base, cf. `GlobalGaloisFibre.lean`), and `e` restricts to an isomorphism
  `realify ⋙ G_A ≅ Ψ_A ⋙ realify` (`resRealifyIso`, `fibRealifyIso`, `mateIso`).
* The one-morphism-base results `thm64iv_deg`, `finrank_eq`, `thm64iv_galois` (`Thm64iv.lean`)
  apply: **`GlobalGaloisRlf.thm64iv`**.

The compatibility of `L₁ ≅ L₂` with an isomorphism `F₁ ≅ F₂` (for `F₁/ℚ` Galois):
`Thm64ivCompat.lean`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField Model

section Fibres

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [IsGalois F E]

variable (F E) in
/-- The fibre of `C^rlf_{F̃/F}` over `A`. -/
abbrev FibR (A : OrbitObj (GalG F E)) : Type := Fib (phiRlfGal F E) (bRlfGal F E) (divRlfGal F E) A

variable (F E) in
/-- The fibre of `C_{F̃/F}` over `A`. -/
abbrev FibZ (A : OrbitObj (GalG F E)) : Type := Fib (phiGal F E) (bGalNF F E) (divGalNF F E) A

lemma fib_pb_eq {A : OrbitObj (GalG F E)} {X Y : FibR F E A} (f : X ⟶ Y) :
    (phiRlfGal F E).pb f.1.base Y.α = Y.α := by
  rw [f.2]; exact (phiRlfGal F E).pb_id A _

lemma fib_pb {A : OrbitObj (GalG F E)} {X Y : FibR F E A} (f : X ⟶ Y) (x : (phiRlfGal F E).obj A) :
    (phiRlfGal F E).pb f.1.base x = x := by
  rw [f.2]; exact (phiRlfGal F E).pb_id A _

lemma fib_pbB {A : OrbitObj (GalG F E)} {X Y : FibR F E A} (f : X ⟶ Y) (x : (bRlfGal F E).obj A) :
    (bRlfGal F E).pb f.1.base x = x := by
  rw [f.2]; exact (bRlfGal F E).pb_id A _

lemma fibZ_pb {A : OrbitObj (GalG F E)} {X Y : FibZ F E A} (f : X ⟶ Y) (x : (phiGal F E).obj A) :
    (phiGal F E).pb f.1.base x = x := by
  rw [f.2]; exact (phiGal F E).pb_id A _

lemma fibZ_pbB {A : OrbitObj (GalG F E)} {X Y : FibZ F E A} (f : X ⟶ Y) (x : (bGalNF F E).obj A) :
    (bGalNF F E).pb f.1.base x = x := by
  rw [f.2]; exact (bGalNF F E).pb_id A _

lemma fibZ_pb_eq {A : OrbitObj (GalG F E)} {X Y : FibZ F E A} (f : X ⟶ Y) :
    (phiGal F E).pb f.1.base Y.α = Y.α := by
  rw [f.2]; exact (phiGal F E).pb_id A _

/-- **The fibre of `C^rlf_{F̃/F}` over `G/H` is `GlobalRealified (E^H)`.** -/
@[simps]
noncomputable def ofFibR (A : OrbitObj (GalG F E)) : FibR F E A ⥤ GlobalRealified (Fix A) where
  obj X := ⟨pt, X.α⟩
  map {X Y} f := Model.mk' f.1.deg (𝟙 _) f.1.div f.1.div_mem f.1.u (by
    have r := f.1.rel
    rw [fib_pb_eq f] at r
    exact r)
  map_id X := Model.hom_ext rfl rfl rfl rfl
  map_comp {X Y Z} f g := by
    refine Model.hom_ext rfl rfl ?_ ?_
    · change (phiRlfGal F E).pb f.1.base g.1.div + _ = g.1.div + _
      rw [fib_pb f]
      rfl
    · change (bRlfGal F E).pb f.1.base g.1.u + _ = g.1.u + _
      rw [fib_pbB f]
      rfl

instance (A : OrbitObj (GalG F E)) : (ofFibR A).IsEquivalence where
  faithful := ⟨fun {X Y} f g h => by
    have h1 := congrArg Hom.deg h
    have h3 := congrArg Hom.div h
    have h4 := congrArg Hom.u h
    exact Fib.hom_ext (Model.hom_ext h1 (f.2.trans g.2.symm) h3 h4)⟩
  full := ⟨fun {X Y} g => ⟨⟨(GlobalGaloisRlf.fibreRlf A).map g, rfl⟩,
    Model.hom_ext rfl (Subsingleton.elim _ _) rfl rfl⟩⟩
  essSurj := ⟨fun Z => by
    obtain ⟨⟨⟨⟩⟩, α⟩ := Z
    exact ⟨⟨α⟩, ⟨Iso.refl _⟩⟩⟩

/-- `toZ` on the divisor groups `Φ^gp(G/H)` of `C_{F̃/F}`. -/
noncomputable def zG (A : OrbitObj (GalG F E)) : (phiGal F E).obj A ≃+ ArithDivZ (Fix A) :=
  toZ (Fix A)

lemma zG_divG (A : OrbitObj (GalG F E)) (u : (bGalNF F E).obj A) :
    zG A ((divGalNF F E).app A u) = divZ (Fix A) u :=
  toZ_divG (K := Fix A) u

lemma zG_symm_divZ (A : OrbitObj (GalG F E)) (u : (bGalNF F E).obj A) :
    (zG A).symm (divZ (Fix A) u) = (divGalNF F E).app A u :=
  GlobalGaloisFrob.toZ_symm_divZ A u

lemma zG_mem_iff (A : OrbitObj (GalG F E)) (x : (phiGal F E).obj A) :
    zG A x ∈ effConeZ (Fix A) ↔ x ∈ (phiGal F E).pos A :=
  toZ_mem_iff x

/-- **The fibre of `C_{F̃/F}` over `G/H` is `GlobalFrobenioid (E^H)`** (divisors via `toZ`). -/
@[simps]
noncomputable def ofFibZ (A : OrbitObj (GalG F E)) : FibZ F E A ⥤ GlobalFrobenioid (Fix A) where
  obj X := ⟨pt, zG A X.α⟩
  map {X Y} f := Model.mk' f.1.deg (𝟙 _) (zG A f.1.div) ((zG_mem_iff A _).2 f.1.div_mem)
    f.1.u (by
    have r := congrArg (zG A) f.1.rel
    rw [fibZ_pb_eq f, map_add, map_add, map_nsmul, zG_divG] at r
    exact r)
  map_id X := Model.hom_ext rfl rfl (map_zero _) rfl
  map_comp {X Y Z} f g := by
    refine Model.hom_ext rfl rfl ?_ ?_
    · change zG A (f.1 ≫ g.1).div = zG A g.1.div + (g.1.deg : ℕ) • zG A f.1.div
      rw [Model.comp_div, fibZ_pb f, map_add, map_nsmul]
    · change (bGalNF F E).pb f.1.base g.1.u + _ = g.1.u + _
      rw [fibZ_pbB f]
      rfl

instance (A : OrbitObj (GalG F E)) : (ofFibZ A).IsEquivalence where
  faithful := ⟨fun {X Y} f g h => by
    have h1 := congrArg Hom.deg h
    have h3 := congrArg Hom.div h
    have h4 := congrArg Hom.u h
    exact Fib.hom_ext (Model.hom_ext h1 (f.2.trans g.2.symm) ((zG A).injective h3) h4)⟩
  full := ⟨fun {X Y} g => by
    refine ⟨⟨Model.mk' g.deg (𝟙 A) ((zG A).symm g.div)
      ((zG_mem_iff A _).1 (by rw [AddEquiv.apply_symm_apply]; exact g.div_mem)) g.u ?_, rfl⟩, ?_⟩
    · have r0 : (g.deg : ℕ) • zG A X.α + g.div = zG A Y.α + divZ (Fix A) g.u := g.rel
      have r1 := congrArg (zG A).symm r0
      rw [map_add, map_add, map_nsmul, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
        zG_symm_divZ] at r1
      rw [(phiGal F E).pb_id]
      exact r1
    · exact Model.hom_ext rfl (Subsingleton.elim _ _) (AddEquiv.apply_symm_apply _ _) rfl⟩
  essSurj := ⟨fun Z => by
    obtain ⟨⟨⟨⟩⟩, α⟩ := Z
    exact ⟨⟨(zG A).symm α⟩, ⟨eqToIso (by
      change (⟨pt, zG A ((zG A).symm α)⟩ : GlobalFrobenioid (Fix A)) = ⟨pt, α⟩
      rw [AddEquiv.apply_symm_apply])⟩⟩⟩

/-- The realification restricted to the fibres over `A`. -/
@[simps]
noncomputable def realifyFib (A : OrbitObj (GalG F E)) : FibZ F E A ⥤ FibR F E A where
  obj X := ⟨castG _ X.α⟩
  map f := ⟨(GlobalGaloisFrob.realify F E).map f.1, f.2⟩
  map_id _ := Fib.hom_ext ((GlobalGaloisFrob.realify F E).map_id _)
  map_comp f g := Fib.hom_ext ((GlobalGaloisFrob.realify F E).map_comp f.1 g.1)

/-- **The realifications commute with the identifications of the fibres.** -/
noncomputable def fibRealifyIso (A : OrbitObj (GalG F E)) :
    realifyFib A ⋙ ofFibR A ≅ ofFibZ A ⋙ GlobalFrobenioid.realify (Fix A) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {X Y} f => by
    erw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    refine Model.hom_ext rfl rfl rfl (Subtype.ext ?_)
    change castG _ (divG _ f.1.u) = castDiv _ (divZ _ f.1.u)
    rw [castG_apply, toZ_divG])

/-- `ofFibR ⋙ fibreRlf` is the inclusion of the fibre. -/
noncomputable def ofFibRFibre (A : OrbitObj (GalG F E)) :
    ofFibR A ⋙ GlobalGaloisRlf.fibreRlf A ≅
      Fib.incl (phiRlfGal F E) (bRlfGal F E) (divRlfGal F E) A :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {X Y} f => by
    erw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact Model.hom_ext rfl f.2.symm rfl rfl)

end Fibres

/-! ### Mates of isomorphisms along equivalences -/

section Mate

variable {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']

/-- From `R ⋙ V ≅ U ⋙ R'` with `U`, `V` equivalences, `R' ⋙ V⁻¹ ≅ U⁻¹ ⋙ R`. -/
noncomputable def mateIso (U : A ⥤ A') (V : B ⥤ B') [U.IsEquivalence] [V.IsEquivalence]
    (R : A ⥤ B) (R' : A' ⥤ B') (s : R ⋙ V ≅ U ⋙ R') : R' ⋙ V.inv ≅ U.inv ⋙ R :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight U.asEquivalence.counitIso.symm (R' ⋙ V.inv) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft U.inv ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight s.symm V.inv ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft R V.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor R)

end Mate

/-! ### The base of `Ψ` from that of `Ψ^rlf` -/

section Main

variable {F₁ E₁ : Type} [Field F₁] [NumberField F₁] [Field E₁] [Algebra F₁ E₁] [IsGalois F₁ E₁]
variable {F₂ E₂ : Type} [Field F₂] [NumberField F₂] [Field E₂] [Algebra F₂ E₂] [IsGalois F₂ E₂]

variable (Ψr : GlobalGaloisRlf F₁ E₁ ⥤ GlobalGaloisRlf F₂ E₂)
  (Ψ : GlobalGaloisFrob F₁ E₁ ⥤ GlobalGaloisFrob F₂ E₂)
  (e : GlobalGaloisFrob.realify F₁ E₁ ⋙ Ψr ≅ Ψ ⋙ GlobalGaloisFrob.realify F₂ E₂)
  (Gb : OrbitObj (GalG F₁ E₁) ⥤ OrbitObj (GalG F₂ E₂))
  (ηr : Ψr ⋙ toElem (phiRlfGal F₂ E₂) (bRlfGal F₂ E₂) (divRlfGal F₂ E₂) ⋙ Elem.proj ≅
    (toElem (phiRlfGal F₁ E₁) (bRlfGal F₁ E₁) (divRlfGal F₁ E₁) ⋙ Elem.proj) ⋙ Gb)

/-- **`Ψ` lies over the base functor of `Ψ^rlf`** (through `e`). -/
noncomputable def baseIsoOfRealify :
    Ψ ⋙ toElem (phiGal F₂ E₂) (bGalNF F₂ E₂) (divGalNF F₂ E₂) ⋙ Elem.proj ≅
      (toElem (phiGal F₁ E₁) (bGalNF F₁ E₁) (divGalNF F₁ E₁) ⋙ Elem.proj) ⋙ Gb :=
  Functor.isoWhiskerRight e.symm
      (toElem (phiRlfGal F₂ E₂) (bRlfGal F₂ E₂) (divRlfGal F₂ E₂) ⋙ Elem.proj) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (GlobalGaloisFrob.realify F₁ E₁) ηr

lemma baseIsoOfRealify_hom_app (X : GlobalGaloisFrob F₁ E₁) :
    ((baseIsoOfRealify Ψr Ψ e Gb ηr).app X).hom =
      (e.inv.app X).base ≫ (ηr.app ((GlobalGaloisFrob.realify F₁ E₁).obj X)).hom := by
  simp [baseIsoOfRealify]
  rfl

/-- The isomorphism of `C₂^rlf` underlying `resRealifyIso`. -/
noncomputable def resRealifyComp (A : OrbitObj (GalG F₁ E₁))
    (X : FibZ F₁ E₁ A) :
    (resObj Ψr Gb ηr ((realifyFib A).obj X)).toModel ≅
      ((realifyFib (Gb.obj A)).obj (resObj Ψ Gb (baseIsoOfRealify Ψr Ψ e Gb ηr) X)).toModel :=
  @asIso _ _ _ _ (resRho Ψr Gb ηr ((realifyFib A).obj X)) (isIso_resRho _ _ _ _) ≪≫
    e.app X.toModel ≪≫ (GlobalGaloisFrob.realify F₂ E₂).mapIso
      (@asIso _ _ _ _ (resRho Ψ Gb (baseIsoOfRealify Ψr Ψ e Gb ηr) X)
        (isIso_resRho _ _ _ _)).symm

lemma resRealifyComp_base (A : OrbitObj (GalG F₁ E₁)) (X : FibZ F₁ E₁ A) :
    (resRealifyComp Ψr Ψ e Gb ηr A X).hom.base = 𝟙 _ := by
  have h : (resRealifyComp Ψr Ψ e Gb ηr A X).hom.base =
      (resRho Ψr Gb ηr ((realifyFib A).obj X)).base ≫ (e.hom.app X.toModel).base ≫
        (@inv _ _ _ _ (resRho Ψ Gb (baseIsoOfRealify Ψr Ψ e Gb ηr) X)
          (isIso_resRho _ _ _ _)).base := rfl
  rw [h, resRho_base, inv_resRho_base]
  change (ηr.app _).inv ≫ (e.hom.app X.toModel).base ≫
    ((baseIsoOfRealify Ψr Ψ e Gb ηr).app X.toModel).hom = _
  rw [baseIsoOfRealify_hom_app]
  have hc : (e.hom.app X.toModel).base ≫ (e.inv.app X.toModel).base = 𝟙 _ := by
    rw [← comp_base, Iso.hom_inv_id_app]; rfl
  erw [reassoc_of% hc]
  exact (ηr.app _).inv_hom_id

/-- **`e` restricts to the fibres**: `realifyFib ⋙ resFib Ψ^rlf ≅ resFib Ψ ⋙ realifyFib`. -/
noncomputable def resRealifyIso (A : OrbitObj (GalG F₁ E₁)) :
    realifyFib A ⋙ resFib Ψr Gb ηr ≅
      resFib Ψ Gb (baseIsoOfRealify Ψr Ψ e Gb ηr) ⋙ realifyFib (Gb.obj A) :=
  NatIso.ofComponents
    (fun X => Fib.isoMk (resRealifyComp Ψr Ψ e Gb ηr A X) (resRealifyComp_base Ψr Ψ e Gb ηr A X))
    (fun {X Y} f => by
      refine Fib.hom_ext ?_
      haveI := isIso_resRho Ψr Gb ηr ((realifyFib A).obj X)
      haveI := isIso_resRho Ψr Gb ηr ((realifyFib A).obj Y)
      haveI := isIso_resRho Ψ Gb (baseIsoOfRealify Ψr Ψ e Gb ηr) X
      haveI := isIso_resRho Ψ Gb (baseIsoOfRealify Ψr Ψ e Gb ηr) Y
      change (resRho Ψr Gb ηr _ ≫ Ψr.map ((GlobalGaloisFrob.realify F₁ E₁).map f.1) ≫
          @inv _ _ _ _ (resRho Ψr Gb ηr ((realifyFib A).obj Y)) (isIso_resRho _ _ _ _)) ≫
            (resRealifyComp Ψr Ψ e Gb ηr A Y).hom =
        (resRealifyComp Ψr Ψ e Gb ηr A X).hom ≫ (GlobalGaloisFrob.realify F₂ E₂).map
          (resRho Ψ Gb _ X ≫ Ψ.map f.1 ≫
            @inv _ _ _ _ (resRho Ψ Gb (baseIsoOfRealify Ψr Ψ e Gb ηr) Y) (isIso_resRho _ _ _ _))
      have := e.hom.naturality f.1
      simp only [Functor.comp_map] at this
      simp only [resRealifyComp, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom,
        asIso_inv, Functor.map_comp, Functor.map_inv, Category.assoc]
      erw [IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc, Iso.app_hom, Iso.app_hom,
        reassoc_of% this]
      rfl)

end Main

/-! ### [FrdI], Theorem 6.4(iv) over `B(Gal(F̃/F))⁰` -/

section Final

variable {F₁ E₁ : Type} [Field F₁] [NumberField F₁] [Field E₁] [Algebra F₁ E₁] [IsGalois F₁ E₁]
variable {F₂ E₂ : Type} [Field F₂] [NumberField F₂] [Field E₂] [Algebra F₂ E₂] [IsGalois F₂ E₂]

/-- **The fibre restrictions of `Ψ^rlf`, `Ψ`**: `Ψ^rlf` lies over an equivalence
`Ψ_Base : B(G₁)⁰ ≌ B(G₂)⁰`, and for every `A = G₁/H` the restrictions of `Ψ^rlf`, `Ψ` to the
fibres over `A`, `Ψ_Base(A)` are equivalences `G_A : C^rlf(L₁) ≌ C^rlf(L₂)`,
`Ψ_A : C(L₁) ≌ C(L₂)` with `realify ⋙ G_A ≅ Ψ_A ⋙ realify`. -/
theorem GlobalGaloisRlf.exists_fibreEquiv (Ψr : GlobalGaloisRlf F₁ E₁ ⥤ GlobalGaloisRlf F₂ E₂)
    [Ψr.IsEquivalence] (Ψ : GlobalGaloisFrob F₁ E₁ ⥤ GlobalGaloisFrob F₂ E₂) [Ψ.IsEquivalence]
    (e : GlobalGaloisFrob.realify F₁ E₁ ⋙ Ψr ≅ Ψ ⋙ GlobalGaloisFrob.realify F₂ E₂) :
    ∃ Gb : OrbitObj (GalG F₁ E₁) ⥤ OrbitObj (GalG F₂ E₂), Gb.IsEquivalence ∧
      Nonempty (Ψr ⋙ toElem (phiRlfGal F₂ E₂) (bRlfGal F₂ E₂) (divRlfGal F₂ E₂) ⋙ Elem.proj ≅
        (toElem (phiRlfGal F₁ E₁) (bRlfGal F₁ E₁) (divRlfGal F₁ E₁) ⋙ Elem.proj) ⋙ Gb) ∧
      ∀ A : OrbitObj (GalG F₁ E₁),
        ∃ (GA : GlobalRealified (Fix A) ⥤ GlobalRealified (Fix (Gb.obj A)))
          (_ : GA.IsEquivalence)
          (ΨA : GlobalFrobenioid (Fix A) ⥤ GlobalFrobenioid (Fix (Gb.obj A)))
          (_ : ΨA.IsEquivalence),
          Nonempty (GA ⋙ GlobalGaloisRlf.fibreRlf (Gb.obj A) ≅
            GlobalGaloisRlf.fibreRlf A ⋙ Ψr) ∧
          Nonempty (GlobalFrobenioid.realify (Fix A) ⋙ GA ≅
            ΨA ⋙ GlobalFrobenioid.realify (Fix (Gb.obj A))) := by
  obtain ⟨Gb, ⟨ηr⟩⟩ := GlobalGaloisRlf.preservesBase Ψr
  obtain ⟨Gb', ⟨ηr'⟩⟩ := GlobalGaloisRlf.preservesBase Ψr.inv
  haveI : Gb.IsEquivalence := isEquivalence_base (GlobalGaloisRlf.isFrobenioid F₁ E₁)
    (GlobalGaloisRlf.isFrobenioid F₂ E₂) Ψr Gb Gb' ηr ηr'
  refine ⟨Gb, inferInstance, ⟨ηr⟩, fun A => ?_⟩
  let η := baseIsoOfRealify Ψr Ψ e Gb ηr
  let A₂ := Gb.obj A
  let resR := resFib Ψr Gb ηr (A := A)
  let resZ := resFib Ψ Gb η (A := A)
  let GA := (ofFibR A).inv ⋙ resR ⋙ ofFibR A₂
  let ΨA := (ofFibZ A).inv ⋙ resZ ⋙ ofFibZ A₂
  let eA : GlobalFrobenioid.realify (Fix A) ⋙ GA ≅ ΨA ⋙ GlobalFrobenioid.realify (Fix A₂) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (mateIso (ofFibZ A) (ofFibR A) (realifyFib A)
        (GlobalFrobenioid.realify (Fix A)) (fibRealifyIso A)) (resR ⋙ ofFibR A₂) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (ofFibZ A).inv ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (resRealifyIso Ψr Ψ e Gb ηr A) (ofFibR A₂) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft resZ (fibRealifyIso A₂) ≪≫
        (Functor.associator _ _ _).symm) ≪≫
      (Functor.associator _ _ _).symm
  have hfib : GA ⋙ GlobalGaloisRlf.fibreRlf A₂ ≅ GlobalGaloisRlf.fibreRlf A ⋙ Ψr :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (ofFibR A).inv (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft resR (ofFibRFibre A₂) ≪≫ resFibIncl Ψr Gb ηr) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (ofFibR A).asEquivalence.counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (ofFibR A).inv (ofFibRFibre A)).symm Ψr
  exact ⟨GA, inferInstance, ΨA, inferInstance, ⟨hfib⟩, ⟨eA⟩⟩


/-- **[FrdI], Theorem 6.4(iv) over the Galois base.** Let `Ψ^rlf : C^rlf_{F̃₁/F₁} ≌ C^rlf_{F̃₂/F₂}`
arise from `Ψ : C_{F̃₁/F₁} ≌ C_{F̃₂/F₂}` (`e : realify ⋙ Ψ^rlf ≅ Ψ ⋙ realify`). Then `Ψ^rlf`
lies over an equivalence `Ψ_Base : B(G₁)⁰ ≌ B(G₂)⁰`, and for every `A = G₁/H` (field
`L₁ = F̃₁^H`), the restriction `G_A : C^rlf(L₁) ≌ C^rlf(L₂)` of `Ψ^rlf` to the fibres over `A` and
`Ψ_Base(A)` (`L₂ = F̃₂^{Ψ_Base(A)}`) has degree `deg(G_A) = 1`, `[L₁:ℚ] = [L₂:ℚ]`, and if `L₁` is
Galois over `ℚ`, then `L₁ ≅ L₂`. -/
theorem GlobalGaloisRlf.thm64iv (Ψr : GlobalGaloisRlf F₁ E₁ ⥤ GlobalGaloisRlf F₂ E₂)
    [Ψr.IsEquivalence] (Ψ : GlobalGaloisFrob F₁ E₁ ⥤ GlobalGaloisFrob F₂ E₂) [Ψ.IsEquivalence]
    (e : GlobalGaloisFrob.realify F₁ E₁ ⋙ Ψr ≅ Ψ ⋙ GlobalGaloisFrob.realify F₂ E₂) :
    ∃ Gb : OrbitObj (GalG F₁ E₁) ⥤ OrbitObj (GalG F₂ E₂), Gb.IsEquivalence ∧
      Nonempty (Ψr ⋙ toElem (phiRlfGal F₂ E₂) (bRlfGal F₂ E₂) (divRlfGal F₂ E₂) ⋙ Elem.proj ≅
        (toElem (phiRlfGal F₁ E₁) (bRlfGal F₁ E₁) (divRlfGal F₁ E₁) ⋙ Elem.proj) ⋙ Gb) ∧
      ∀ A : OrbitObj (GalG F₁ E₁),
        ∃ (GA : GlobalRealified (Fix A) ⥤ GlobalRealified (Fix (Gb.obj A)))
          (_ : GA.IsEquivalence),
          Nonempty (GA ⋙ GlobalGaloisRlf.fibreRlf (Gb.obj A) ≅
            GlobalGaloisRlf.fibreRlf A ⋙ Ψr) ∧
          GlobalRealified.degOf GA = 1 ∧
          Module.finrank ℚ (Fix A) = Module.finrank ℚ (Fix (Gb.obj A)) ∧
          (IsGalois ℚ (Fix A) → Nonempty (Fix A ≃+* Fix (Gb.obj A))) := by
  obtain ⟨Gb, hGb, hηr, hA⟩ := GlobalGaloisRlf.exists_fibreEquiv Ψr Ψ e
  refine ⟨Gb, hGb, hηr, fun A => ?_⟩
  obtain ⟨GA, _, ΨA, _, hfib, ⟨eA⟩⟩ := hA A
  exact ⟨GA, inferInstance, hfib, GlobalRealified.thm64iv_deg GA ΨA eA,
    GlobalRealified.finrank_eq GA ΨA eA, fun h => by
      haveI := h
      exact GlobalRealified.thm64iv_galois GA ΨA eA⟩

end Final

end Frobenioid

end Iut
