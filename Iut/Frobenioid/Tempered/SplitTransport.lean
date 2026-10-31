/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.ThetaMonoid

/-!
# Transport of split Frobenioids ([IUTchI], Example 3.2(vi)(e))

[IUTchI], Example 3.2(vi) (l.3936–3963 of `~/iut-scratch/wall/txt/Inter-universal Teichmuller
Theory I.txt`): "(b) the category `D^Θ_v` may be reconstructed category-theoretically from `D_v`
[...]; (d) the category `D_v` may be reconstructed category-theoretically [...] from `F_v`".
"Next, let us observe that by (b), (d), together with the discussion of (ii) concerning the
category-theoreticity of `Θ_v`, it follows that (e) one may reconstruct the split Frobenioid
`F^Θ_v` [up to the `l·Z` indeterminacy in `Θ_v` discussed in (ii)] category-theoretically from
`F_v` [cf. [FrdI], Theorem 3.4, (i), (v); [EtTh], Proposition 5.1]." Here "reconstructed
category-theoretically" means "preserved by equivalences of categories" (Remark 3.2.1(i)).

`Iut/Frobenioid/Tempered/ThetaMonoid.lean` treats (vi)(e) at the level of the monoids
(`Model.map_thetaPsi`). This file does it **for the whole split Frobenioid**
`F^Θ_v = (C^Θ_v, τ^Θ_v)`, represented as in `Iut/Frobenioid/Tempered/SplitFrob.lean` by
`SplitModel (unitGrpOn divB jΘ hj)` (`O^⊿_{C^Θ_v} = O^×(T_{jΘ(−)}) × ℕ`) with its standard splitting
and its realisation `(u, n) ↦ u·Θ^n` in `F^÷_v`.

## Inputs

* an equivalence `F : C₁ ⥤ C₂` of model Frobenioids (`F_v`, `F'_v`) matching pre-steps,
  base-equivalent pairs and linear morphisms ([FrdI], Theorem 3.4(ii),(iii),(v));
* (d) **the base functor** of `F`: `G : D₁ ⥤ D₂` with `ε : F ⋙ Base ≅ Base ⋙ G` (the conclusion
  `PreservesBase` of [FrdI], Theorem 3.4(v), `Model.thm34_fsm_preservesBase`);
* (b) **`D^Θ_v` from `D_v`**: functors `jΘ_i : E_i ⥤ D_i` (`D^Θ_v ⊆ (D_v)_Ÿ → D_v`), an equivalence
  `e : E₁ ⥤ E₂` and `β : jΘ₁ ⋙ G ≅ e ⋙ jΘ₂` (the reconstruction of [AbsAnab], Lemma 1.3.8,
  supplied by the anabelian side);
* (ii) **the theta functions**: natural families `Θ_i` with `Θ₂ = F^birat(Θ₁)` (transported along
  `ε`, `β`); that a given `F` maps the Frobenioid-theoretic theta function to one is [EtTh],
  Theorem 5.7 (not formalised here).

## Results

* `Model.mapUnit_pb_linear`: naturality of `F^birat` for linear morphisms whose image is linear
  (generalising `Model.mapUnit_pb` from pre-steps);
* `Model.splitUnitEquiv`: `F^birat` composed with the base isomorphisms gives natural isomorphisms
  `O^×(T_{jΘ₁ A}) ≅ O^×(T_{jΘ₂ (e A)})` (`Model.splitUnitEquiv_natural`);
* **[IUTchI], Example 3.2(vi)(e)** (`Model.splitTransport`, an equivalence of categories):
  `SplitModel U₁ ⥤ SplitModel U₂` over `e`, mapping the characteristic splitting `τ^Θ` to `τ^Θ`
  (`Model.splitTransport_stdSplit`), the `μ`-orbit `τ_ζ` to `τ_{F ζ}`
  (`Model.splitTransport_twist`), and compatible with the realisations in `F^÷_v`, `F'^÷_v`
  (`Model.realize_splitTransport`: `realize_{Θ₂}(F b) = F^birat(realize_{Θ₁}(b))`), in
  particular mapping `O^×·Θ₁^ℕ` onto `O^×·Θ₂^ℕ` (`Model.map_thetaMon_splitTransport`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u u₁ u₂ v₁ v₂ t₁ t₂

namespace Model

section Transport

variable {D₁ : Type u₁} [Category.{v} D₁]
variable {Φ₁ : DivMonoid.{w} D₁} {B₁ : GrpOn.{w} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v} D₂]
variable {Φ₂ : DivMonoid.{w} D₂} {B₂ : GrpOn.{w} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂)
  (hpre : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y),
    IsPreStep (toElem Φ₁ B₁ divB₁) φ ↔ IsPreStep (toElem Φ₂ B₂ divB₂) (F.map φ))
  (hbe : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ φ' : X ⟶ Y),
    φ.base = φ'.base ↔ (F.map φ).base = (F.map φ').base)

include hbe in
/-- **Naturality of `F^birat` on units for linear morphisms with linear image**:
`F^birat((Base φ)^* c) = (Base F φ)^* F^birat(c)`. -/
lemma mapUnit_pb_linear {X Y : Model Φ₁ B₁ divB₁} (φ : X ⟶ Y) (h₁ : φ.deg = 1)
    (h₂ : (F.map φ).deg = 1) (c : B₁.obj Y.base) :
    mapUnit F hpre (B₁.pb φ.base c) = B₂.pb (F.map φ).base (mapUnit F hpre c) := by
  have e := congrArg (biratFunctor F fun _ _ φ h => (hpre φ).1 h).map
    (toBirat_comp_birUnit φ h₁ c)
  rw [Functor.map_comp, Functor.map_comp, biratFunctor_map_toBirat, map_birUnit' F hpre hbe,
    map_birUnit' F hpre hbe] at e
  have eu := congrArg BHom.u e
  change B₂.pb (F.map φ).base (mapUnit F hpre c) + ((1 : ℕ+) : ℕ) • (F.map φ).u =
    B₂.pb (𝟙 _) (F.map φ).u + ((F.map φ).deg : ℕ) • mapUnit F hpre (B₁.pb φ.base c) at eu
  rw [h₂, GrpOn.pb_id', PNat.one_coe, one_smul, one_smul, add_comm] at eu
  exact (add_left_cancel eu).symm

/-- Pull-back along an isomorphism of the base as an additive isomorphism. -/
@[simps]
def pbIsoEquiv {D : Type u} [Category.{v} D] (B : GrpOn.{w} D) {A A' : D} (i : A ≅ A') :
    B.obj A' ≃+ B.obj A where
  toFun := B.pb i.hom
  invFun := B.pb i.inv
  left_inv x := by rw [← GrpOn.pb_comp', i.inv_hom_id, GrpOn.pb_id']
  right_inv x := by rw [← GrpOn.pb_comp', i.hom_inv_id, GrpOn.pb_id']
  map_add' := map_add _

variable {E₁ : Type t₁} [Category.{v₁} E₁] {E₂ : Type t₂} [Category.{v₂} E₂]
variable (jΘ₁ : E₁ ⥤ D₁) (jΘ₂ : E₂ ⥤ D₂) (e : E₁ ⥤ E₂) (G : D₁ ⥤ D₂)
  (ε : F ⋙ toElem Φ₂ B₂ divB₂ ⋙ Elem.proj ≅ (toElem Φ₁ B₁ divB₁ ⋙ Elem.proj) ⋙ G)
  (β : jΘ₁ ⋙ G ≅ e ⋙ jΘ₂)

/-- The Frobenius-trivial object `T_{jΘ₁ A} = (jΘ₁ A, 0)`. -/
abbrev triv (A : E₁) : Model Φ₁ B₁ divB₁ := zeroObj Φ₁ B₁ divB₁ (jΘ₁.obj A)

/-- The pull-back morphism `(1, jΘ₁ f, 0, 0) : T_{jΘ₁ A} → T_{jΘ₁ A'}`. -/
def trivPb {A A' : E₁} (f : A ⟶ A') : triv (Φ₁ := Φ₁) (B₁ := B₁) (divB₁ := divB₁) jΘ₁ A ⟶
    triv jΘ₁ A' :=
  mk1 (jΘ₁.map f) 0 (Φ₁.pos _).zero_mem 0 (by simp)

/-- The base comparison `Base(F T_{jΘ₁ A}) ≅ G(jΘ₁ A) ≅ jΘ₂(e A)`. -/
def baseCmp (A : E₁) : (F.obj (triv (Φ₁ := Φ₁) (B₁ := B₁) (divB₁ := divB₁) jΘ₁ A)).base ≅
    jΘ₂.obj (e.obj A) :=
  ε.app (triv jΘ₁ A) ≪≫ β.app A

lemma baseCmp_natural {A A' : E₁} (f : A ⟶ A') :
    (F.map (trivPb (Φ₁ := Φ₁) (B₁ := B₁) (divB₁ := divB₁) jΘ₁ f)).base ≫
        (baseCmp F jΘ₁ jΘ₂ e G ε β A').hom =
      (baseCmp F jΘ₁ jΘ₂ e G ε β A).hom ≫ jΘ₂.map (e.map f) := by
  have h₁ := ε.hom.naturality (trivPb (Φ₁ := Φ₁) (B₁ := B₁) (divB₁ := divB₁) jΘ₁ f)
  have h₂ := β.hom.naturality f
  simp only [Functor.comp_map] at h₁ h₂
  simp only [baseCmp, Iso.trans_hom, Iso.app_hom, ← Category.assoc]
  have h₁' : (F.map (trivPb (Φ₁ := Φ₁) (B₁ := B₁) (divB₁ := divB₁) jΘ₁ f)).base ≫
      ε.hom.app (triv jΘ₁ A') = ε.hom.app (triv jΘ₁ A) ≫ G.map (jΘ₁.map f) := h₁
  have h₂' : G.map (jΘ₁.map f) ≫ β.hom.app A' = β.hom.app A ≫ jΘ₂.map (e.map f) := h₂
  rw [h₁']
  exact (Category.assoc _ _ _).trans
    ((congrArg (ε.hom.app (triv jΘ₁ A) ≫ ·) h₂').trans (Category.assoc _ _ _).symm)

/-- **`O^×(T^÷_{jΘ₁ A}) ≅ O^×(T^÷_{jΘ₂ (e A)})`**: `F^birat` followed by the base comparison. -/
noncomputable def splitBEquiv [F.IsEquivalence] (A : E₁) :
    B₁.obj (jΘ₁.obj A) ≃+ B₂.obj (jΘ₂.obj (e.obj A)) :=
  (mapUnitEquiv F hpre hbe (triv jΘ₁ A)).trans (pbIsoEquiv B₂ (baseCmp F jΘ₁ jΘ₂ e G ε β A).symm)

lemma splitBEquiv_apply [F.IsEquivalence] (A : E₁) (x : B₁.obj (jΘ₁.obj A)) :
    splitBEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β A x =
      B₂.pb (baseCmp F jΘ₁ jΘ₂ e G ε β A).inv (mapUnit F hpre (X := triv jΘ₁ A) x) := rfl

variable (hlin : ∀ ⦃A A' : E₁⦄ (f : A ⟶ A'),
  (F.map (trivPb (Φ₁ := Φ₁) (B₁ := B₁) (divB₁ := divB₁) jΘ₁ f)).deg = 1)

include hlin in
/-- **Naturality** of `splitBEquiv` along `e`. -/
lemma splitBEquiv_natural [F.IsEquivalence] {A A' : E₁} (f : A ⟶ A') (x : B₁.obj (jΘ₁.obj A')) :
    splitBEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β A (B₁.pb (jΘ₁.map f) x) =
      B₂.pb (jΘ₂.map (e.map f)) (splitBEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β A' x) := by
  rw [splitBEquiv_apply, splitBEquiv_apply]
  have h : mapUnit F hpre (X := triv jΘ₁ A) (B₁.pb (jΘ₁.map f) x) =
      B₂.pb (F.map (trivPb (Φ₁ := Φ₁) (B₁ := B₁) (divB₁ := divB₁) jΘ₁ f)).base
        (mapUnit F hpre (X := triv jΘ₁ A') x) :=
    mapUnit_pb_linear F hpre hbe (trivPb (Φ₁ := Φ₁) (B₁ := B₁) (divB₁ := divB₁) jΘ₁ f)
      rfl (hlin f) x
  have key : (baseCmp F jΘ₁ jΘ₂ e G ε β A).inv ≫
      (F.map (trivPb (Φ₁ := Φ₁) (B₁ := B₁) (divB₁ := divB₁) jΘ₁ f)).base =
      jΘ₂.map (e.map f) ≫ (baseCmp F jΘ₁ jΘ₂ e G ε β A').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← baseCmp_natural, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [h, ← GrpOn.pb_comp', ← GrpOn.pb_comp', key]

variable [F.IsEquivalence]

lemma splitBEquiv_mem_unitSub (A : E₁) (x : B₁.obj (jΘ₁.obj A)) :
    x ∈ unitSub divB₁ (jΘ₁.obj A) ↔
      splitBEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β A x ∈ unitSub divB₂ (jΘ₂.obj (e.obj A)) := by
  rw [splitBEquiv_apply, mem_unitSub_mapUnit_iff F hpre hbe (Y := triv jΘ₁ A) x]
  constructor
  · exact fun h => pb_mem_unitSub _ h
  · intro h
    have := pb_mem_unitSub (divB := divB₂) (baseCmp F jΘ₁ jΘ₂ e G ε β A).hom h
    rwa [← GrpOn.pb_comp', Iso.hom_inv_id, GrpOn.pb_id'] at this

variable (hj₁ : ∀ {A A' : E₁} (f : A ⟶ A'), IsFSM f → IsFSM (jΘ₁.map f))
  (hj₂ : ∀ {A A' : E₂} (f : A ⟶ A'), IsFSM f → IsFSM (jΘ₂.map f))

/-- **The natural isomorphisms of units** `O^×(T_{jΘ₁ A}) ≅ O^×(T_{jΘ₂(e A)})`. -/
noncomputable def splitUnitEquiv (A : E₁) :
    (unitGrpOn divB₁ jΘ₁ hj₁).obj A ≃+ (unitGrpOn divB₂ jΘ₂ hj₂).obj (e.obj A) where
  toFun x := ⟨splitBEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β A x.1,
    (splitBEquiv_mem_unitSub F hpre hbe jΘ₁ jΘ₂ e G ε β A x.1).1 x.2⟩
  invFun y := ⟨(splitBEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β A).symm y.1,
    (splitBEquiv_mem_unitSub F hpre hbe jΘ₁ jΘ₂ e G ε β A _).2 (by simp [y.2])⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (map_add _ _ _)

lemma splitUnitEquiv_coe (A : E₁) (x : (unitGrpOn divB₁ jΘ₁ hj₁).obj A) :
    ((splitUnitEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β hj₁ hj₂ A x : unitSub divB₂ _) :
      B₂.obj (jΘ₂.obj (e.obj A))) = splitBEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β A x.1 := rfl

include hlin in
lemma splitUnitEquiv_natural ⦃A A' : E₁⦄ (f : A ⟶ A') (x : (unitGrpOn divB₁ jΘ₁ hj₁).obj A') :
    splitUnitEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β hj₁ hj₂ A ((unitGrpOn divB₁ jΘ₁ hj₁).pb f x) =
      (unitGrpOn divB₂ jΘ₂ hj₂).pb (e.map f)
        (splitUnitEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β hj₁ hj₂ A' x) :=
  Subtype.ext (splitBEquiv_natural F hpre hbe jΘ₁ jΘ₂ e G ε β hlin f x.1)

/-- **[IUTchI], Example 3.2(vi)(e)**: the equivalence of split Frobenioids
`F^Θ_v = (C^Θ_v, τ^Θ_v) ≅ F'^Θ_v` induced by `F` (over `e : D^Θ_v ≅ D'^Θ_v`). -/
noncomputable def splitTransport :
    SplitModel (unitGrpOn divB₁ jΘ₁ hj₁) ⥤ SplitModel (unitGrpOn divB₂ jΘ₂ hj₂) :=
  SplitModel.mapFunctor e (splitUnitEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β hj₁ hj₂)
    (splitUnitEquiv_natural F hpre hbe jΘ₁ jΘ₂ e G ε β hlin hj₁ hj₂)

instance [e.IsEquivalence] :
    (splitTransport F hpre hbe jΘ₁ jΘ₂ e G ε β hlin hj₁ hj₂).IsEquivalence := by
  unfold splitTransport
  infer_instance

/-- **`splitTransport` maps the characteristic splitting `τ^Θ` onto `τ^Θ`.** -/
lemma splitTransport_stdSplit (A : E₁) (b : (splitB (unitGrpOn divB₁ jΘ₁ hj₁)).obj A) :
    b ∈ SplitModel.stdSplit _ A ↔
      ((splitUnitEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β hj₁ hj₂ A b.1, b.2) :
        (splitB (unitGrpOn divB₂ jΘ₂ hj₂)).obj (e.obj A)) ∈ SplitModel.stdSplit _ (e.obj A) :=
  SplitModel.map_stdSplit e _ A b

/-- **`splitTransport` maps the `μ`-orbit of splittings**: `τ_ζ ↦ τ_{ζ'}` for families of units
`ζ`, `ζ'` corresponding under `F^birat` (`ζ'(e A) = F^birat(ζ A)`). -/
lemma splitTransport_twist (ζ : ∀ A, (unitGrpOn divB₁ jΘ₁ hj₁).obj A)
    (ζ' : ∀ A, (unitGrpOn divB₂ jΘ₂ hj₂).obj A)
    (hζ : ∀ A, ζ' (e.obj A) = splitUnitEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β hj₁ hj₂ A (ζ A))
    (A : E₁) (b : (splitB (unitGrpOn divB₁ jΘ₁ hj₁)).obj A) :
    b ∈ SplitModel.twistSplit _ ζ A ↔
      ((splitUnitEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β hj₁ hj₂ A b.1, b.2) :
        (splitB (unitGrpOn divB₂ jΘ₂ hj₂)).obj (e.obj A)) ∈
        SplitModel.twistSplit _ ζ' (e.obj A) := by
  change (0 ≤ b.2.down ∧ b.1 = b.2.down.toNat • ζ A) ↔
    (0 ≤ b.2.down ∧ splitUnitEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β hj₁ hj₂ A b.1 =
      b.2.down.toNat • ζ' (e.obj A))
  rw [hζ, ← map_nsmul, (splitUnitEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β hj₁ hj₂ A).injective.eq_iff]

/-- **Compatibility with the realisations** `(u, n) ↦ u·Θ^n` in `F^÷_v`, `F'^÷_v`: if
`Θ₂(e A) = F^birat(Θ₁ A)`, then `realize_{Θ₂}(splitTransport b) = F^birat(realize_{Θ₁} b)`. -/
theorem realize_splitTransport (θ₁ : ∀ A, B₁.obj (jΘ₁.obj A)) (θ₂ : ∀ A, B₂.obj (jΘ₂.obj A))
    (A : E₁) (hθ : θ₂ (e.obj A) = splitBEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β A (θ₁ A))
    (b : (splitB (unitGrpOn divB₁ jΘ₁ hj₁)).obj A) :
    SplitModel.realize divB₂ jΘ₂ hj₂ θ₂ (e.obj A)
        ((splitUnitEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β hj₁ hj₂ A b.1, b.2)) =
      splitBEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β A (SplitModel.realize divB₁ jΘ₁ hj₁ θ₁ A b) := by
  simp only [SplitModel.realize, map_add, map_zsmul, hθ]
  rfl

/-- **`F^birat` maps `O^×(T_{jΘ₁ A})·Θ₁^ℕ` onto `O^×(T_{jΘ₂(e A)})·Θ₂^ℕ`** (the monoid
`O^⊿_{C^Θ_v}` of [IUTchI], Example 3.2(v)). -/
theorem map_thetaMon_splitTransport (θ₁ : ∀ A, B₁.obj (jΘ₁.obj A))
    (θ₂ : ∀ A, B₂.obj (jΘ₂.obj A)) (A : E₁)
    (hθ : θ₂ (e.obj A) = splitBEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β A (θ₁ A)) :
    (thetaMon (unitSub divB₁ (jΘ₁.obj A)) (θ₁ A)).map
        (splitBEquiv F hpre hbe jΘ₁ jΘ₂ e G ε β A).toAddMonoidHom =
      thetaMon (unitSub divB₂ (jΘ₂.obj (e.obj A))) (θ₂ (e.obj A)) := by
  rw [hθ]
  exact thetaMon_map _ (splitBEquiv_mem_unitSub F hpre hbe jΘ₁ jΘ₂ e G ε β A) _

end Transport

end Model

end Frobenioid

end Iut
