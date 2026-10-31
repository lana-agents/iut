/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.ThetaEnvModel
import Iut.Frobenioid.Tempered.KummerTransport

/-!
# Transport of Frobenioid-theoretic theta environments ([EtTh], Theorem 5.6, Theorem 5.10(iii))

[EtTh], proof of Theorem 5.10(ii),(iii): a self-equivalence `Ψ` of the tempered Frobenioid
preserves pre-steps, base-equivalent pairs of pre-steps, `O^×(−)`, `O^×((−)^birat)` and the image of
`K^×` in `O^×(B^birat_N)`, and maps `N`-th roots of fraction-pairs together with their bi-Kummer
`N`-th roots ([EtTh], Theorem 4.4(ii),(iv)) to `N`-th roots of fraction-pairs and their bi-Kummer
roots. Here we show the formal consequence for the abstract Frobenioid-theoretic mono-theta
environment `Model.frobEnv` of `Iut/Frobenioid/Tempered/ThetaEnvModel.lean`:

* units (`O^×(Y^birat) ≅ B(Y_D)`, [FrdI], Proposition 4.4(ii)): for an equivalence `F` of model
  Frobenioids matching pre-steps and base-equivalent pairs (in both directions), the image
  `mapUnit F` of birational units is an **additive bijection** `B₁(Y_D) ≅ B₂(F(Y)_D)`
  (`Model.mapUnitEquiv`), natural for pre-steps (`Model.mapUnit_pb`), mapping `O^×(Y)` to
  `O^×(F Y)` (`Model.map_unitHom`), and `F(twUnit a c) = twUnit (F a) (mapUnit c)`
  (`Model.map_twUnit`: conjugation by birational units is preserved);
* **the image data** (`Model.imSigma`, `Model.imPi`): `F ∘ σ ∘ F_*^{-1}` (the image base-Frobenius
  section, [FrdI], Corollary 5.7) and `F_* ∘ π`; the bi-Kummer roots of the image pre-steps are the
  images of the bi-Kummer roots (`Model.sgp_map`, `Model.tgp_map`; [EtTh], Theorem 4.4(iv));
* **[EtTh], Theorem 5.10(iii) (core)** `Model.frobEnvMap`: `(e, p) ↦ (F e, p)` is an isomorphism of
  mono-theta environments `frobEnv(C₁) ≅ frobEnv(C₂)` from the environment of the data
  `(s⊓, s⊔, σ, π, K^×)` to that of the image data `(F s⊓, F s⊔, F σ F_*^{-1}, F_* π, F^birat(K^×))`,
  compatible with the projections `ε : E^Π_N → Aut_C(B_N)` (its map is `Model.ePiMap`);
* **[EtTh], Theorem 5.6 (core)** `Model.deltaE_map`, `Model.frobEnvMap_isCyc`: the Frobenioid
  cyclotomic rigidity isomorphism of Proposition 5.5 (`s⊓-Π(l) ↦ δ(l)`, the Kummer class) is
  transported by `F`.

`Model.frobEnvMap_fsm` supplies all hypotheses on `F` for equivalences of model Frobenioids over
slim bases of FSM-type ([FrdI], Theorem 3.4, `Iut/Frobenioid/Tempered/Thm34Temp.lean`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory Iut.EtaleTheta

universe w v u₁ u₂

namespace Model

/-! ### Units of the birationalization -/

section BiratUnits

variable {D : Type u₁} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

lemma toBirat_map_unitHom (Y : Model Φ B divB) (d : B.obj Y.base) (hd : divB.app _ d = 0) :
    (toBirat Φ B divB).map (unitHom Y d hd) = birUnit Y d := rfl

lemma birUnit_add (Y : Model Φ B divB) (c d : B.obj Y.base) :
    birUnit Y (c + d) = birUnit Y c ≫ birUnit Y d := by
  ext
  · rfl
  · simp
  · change c + d = B.pb (𝟙 _) d + (1 : ℕ) • c
    rw [GrpOn.pb_id', one_smul, add_comm]

/-- **Conjugating a birational unit by a linear morphism**: for `φ : X → Y` of Frobenius degree
`1`, `φ ∘ c = (Base φ)^* c ∘ φ` in `C^birat`. -/
lemma toBirat_comp_birUnit {X Y : Model Φ B divB} (φ : X ⟶ Y) (hφ : φ.deg = 1)
    (c : B.obj Y.base) :
    (toBirat Φ B divB).map φ ≫ birUnit Y c =
      birUnit X (B.pb φ.base c) ≫ (toBirat Φ B divB).map φ := by
  ext
  · simp [hφ]
  · simp
  · change B.pb φ.base c + (1 : ℕ) • φ.u = B.pb (𝟙 _) φ.u + (φ.deg : ℕ) • B.pb φ.base c
    rw [hφ, GrpOn.pb_id', PNat.one_coe, one_smul, one_smul, add_comm]

/-- An automorphism with identity base is the unit `(1, id, 0, u)`. -/
lemma eq_unitHom_of_base {Y : Model Φ B divB} (g : Y ⟶ Y) [IsIso g] (hg : g.base = 𝟙 _) :
    ∃ h : divB.app _ g.u = 0, g = unitHom Y g.u h := by
  have hdeg : g.deg = 1 := ((isIso_iff g).1 inferInstance).1
  have hdiv : g.div = 0 := div_of_isIso g
  have hrel := g.rel
  rw [hdeg, hdiv, hg, GrpOn.pb_id', PNat.one_coe, one_smul, add_zero] at hrel
  have h : divB.app _ g.u = 0 := by
    have := congrArg (· - Y.α) hrel
    simpa using this.symm
  refine ⟨h, ?_⟩
  ext
  · exact hdeg
  · exact hg
  · exact hdiv
  · rfl

lemma unitHom_congr {Y : Model Φ B divB} {d e : B.obj Y.base} (h : d = e)
    (hd : divB.app _ d = 0) (he : divB.app _ e = 0) : unitHom Y d hd = unitHom Y e he := by
  subst h
  rfl

/-- Two automorphisms have the same base iff their quotient is a unit. -/
lemma base_eq_iff_mul_inv_mem {Y : Model Φ B divB} (a b : Aut Y) :
    a.hom.base = b.hom.base ↔ a * b⁻¹ ∈ unitsAut Y := by
  rw [mem_unitsAut]
  change a.hom.base = b.hom.base ↔ (b.inv ≫ a.hom).base = 𝟙 _
  rw [comp_base]
  constructor
  · intro h
    rw [h, inv_base_of_iso]
  · intro h
    have := congrArg (b.hom.base ≫ ·) h
    simp only [← Category.assoc, hom_base_inv_of_iso, Category.id_comp, Category.comp_id] at this
    exact this

end BiratUnits

/-! ### The image of birational units under an equivalence -/

section MapUnit

variable {D₁ : Type u₁} [Category.{v} D₁]
variable {Φ₁ : DivMonoid.{w} D₁} {B₁ : GrpOn.{w} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v} D₂]
variable {Φ₂ : DivMonoid.{w} D₂} {B₂ : GrpOn.{w} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂
local notation "𝐓₁" => toBirat Φ₁ B₁ divB₁
local notation "𝐓₂" => toBirat Φ₂ B₂ divB₂

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂)
  (hpre : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y),
    IsPreStep (toElem Φ₁ B₁ divB₁) φ ↔ IsPreStep (toElem Φ₂ B₂ divB₂) (F.map φ))
  (hbe : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ φ' : X ⟶ Y),
    φ.base = φ'.base ↔ (F.map φ).base = (F.map φ').base)

set_option quotPrecheck false in
/-- The birational functor `F^birat` attached to `F`. -/
local notation "𝐅" => biratFunctor F fun _ _ φ h => (hpre φ).1 h

include hbe in
lemma map_birUnit' {X : Model Φ₁ B₁ divB₁} (f : B₁.obj X.base) :
    𝐅.map (birUnit X f) = birUnit (F.obj X) (mapUnit F hpre f) :=
  map_birUnit F hpre (fun _ _ φ φ' h => (hbe φ φ').1 h) f

include hbe in
lemma mapUnit_add {X : Model Φ₁ B₁ divB₁} (c d : B₁.obj X.base) :
    mapUnit F hpre (c + d) = mapUnit F hpre c + mapUnit F hpre d := by
  have e := congrArg 𝐅.map (birUnit_add X c d)
  rw [Functor.map_comp, map_birUnit' F hpre hbe, map_birUnit' F hpre hbe,
    map_birUnit' F hpre hbe] at e
  have eu := congrArg BHom.u e
  change mapUnit F hpre (c + d) =
    B₂.pb (𝟙 _) (mapUnit F hpre d) + ((1 : ℕ+) : ℕ) • mapUnit F hpre c at eu
  rw [GrpOn.pb_id', PNat.one_coe, one_smul, add_comm (mapUnit F hpre d)] at eu
  exact eu

include hbe in
/-- **Naturality of `F^birat` on units for pre-steps**: for a pre-step `φ : X → Y`,
`F^birat((Base φ)^* c) = (Base F φ)^* F^birat(c)`. -/
lemma mapUnit_pb {X Y : Model Φ₁ B₁ divB₁} (φ : X ⟶ Y) (hφ : IsPreStep 𝐏₁ φ)
    (c : B₁.obj Y.base) :
    mapUnit F hpre (B₁.pb φ.base c) = B₂.pb (F.map φ).base (mapUnit F hpre c) := by
  have hφ' : (F.map φ).deg = 1 := ((hpre φ).1 hφ).1
  have e := congrArg 𝐅.map (toBirat_comp_birUnit φ hφ.1 c)
  rw [Functor.map_comp, Functor.map_comp, biratFunctor_map_toBirat, map_birUnit' F hpre hbe,
    map_birUnit' F hpre hbe] at e
  have eu := congrArg BHom.u e
  change B₂.pb (F.map φ).base (mapUnit F hpre c) + ((1 : ℕ+) : ℕ) • (F.map φ).u =
    B₂.pb (𝟙 _) (F.map φ).u + ((F.map φ).deg : ℕ) • mapUnit F hpre (B₁.pb φ.base c) at eu
  rw [hφ', GrpOn.pb_id', PNat.one_coe, one_smul, one_smul, add_comm] at eu
  exact (add_left_cancel eu).symm

include hbe in
/-- **`F` maps units to units**: `F(1, id, 0, d) = (1, id, 0, F^birat(d))`; in particular
`Div_B(F^birat d) = 0` for `d ∈ O^×(Y)`. -/
theorem map_unitHom_eq {Y : Model Φ₁ B₁ divB₁} (d : B₁.obj Y.base) (hd : divB₁.app _ d = 0) :
    ∃ h : divB₂.app _ (mapUnit F hpre d) = 0,
      F.map (unitHom Y d hd) = unitHom (F.obj Y) (mapUnit F hpre d) h := by
  haveI : IsIso (unitHom Y d hd) := (unitIso Y d hd).isIso_hom
  have hb : (F.map (unitHom Y d hd)).base = 𝟙 _ := by
    have := (hbe (unitHom Y d hd) (𝟙 Y)).1 rfl
    rw [F.map_id] at this
    exact this
  obtain ⟨h, e⟩ := eq_unitHom_of_base (F.map (unitHom Y d hd)) hb
  have hu : (F.map (unitHom Y d hd)).u = mapUnit F hpre d := by
    have e' := biratFunctor_map_toBirat F (fun _ _ φ h => (hpre φ).1 h) (unitHom Y d hd)
    rw [toBirat_map_unitHom, map_birUnit' F hpre hbe] at e'
    exact (congrArg BHom.u e').symm
  exact ⟨hu ▸ h, e.trans (unitHom_congr hu _ _)⟩

include hbe in
lemma divB_mapUnit {Y : Model Φ₁ B₁ divB₁} {d : B₁.obj Y.base} (hd : divB₁.app _ d = 0) :
    divB₂.app _ (mapUnit F hpre d) = 0 :=
  (map_unitHom_eq F hpre hbe d hd).1

include hbe in
lemma map_unitHom {Y : Model Φ₁ B₁ divB₁} (d : B₁.obj Y.base) (hd : divB₁.app _ d = 0) :
    F.map (unitHom Y d hd) = unitHom (F.obj Y) (mapUnit F hpre d) (divB_mapUnit F hpre hbe hd) :=
  (map_unitHom_eq F hpre hbe d hd).2

include hbe in
lemma map_unitAut {Y : Model Φ₁ B₁ divB₁} (d : B₁.obj Y.base) (hd : divB₁.app _ d = 0) :
    F.mapIso (unitAut Y d hd) = unitAut (F.obj Y) (mapUnit F hpre d)
      (divB_mapUnit F hpre hbe hd) := by
  ext1
  exact map_unitHom F hpre hbe d hd

/-- `F^birat` on `O^×(Y^birat) = B(Y_D)` as an additive homomorphism. -/
noncomputable def mapUnitHom (Y : Model Φ₁ B₁ divB₁) : B₁.obj Y.base →+ B₂.obj (F.obj Y).base :=
  AddMonoidHom.mk' (mapUnit F hpre) (mapUnit_add F hpre hbe)

@[simp] lemma mapUnitHom_apply (Y : Model Φ₁ B₁ divB₁) (c : B₁.obj Y.base) :
    mapUnitHom F hpre hbe Y c = mapUnit F hpre c := rfl

include hbe in
lemma mapUnit_sub {Y : Model Φ₁ B₁ divB₁} (c d : B₁.obj Y.base) :
    mapUnit F hpre (c - d) = mapUnit F hpre c - mapUnit F hpre d :=
  map_sub (mapUnitHom F hpre hbe Y) c d

include hbe in
lemma mapUnit_nsmul {Y : Model Φ₁ B₁ divB₁} (n : ℕ) (c : B₁.obj Y.base) :
    mapUnit F hpre (n • c) = n • mapUnit F hpre c :=
  map_nsmul (mapUnitHom F hpre hbe Y) n c

include hbe in
/-- The divisor of a birational unit is fixed by an automorphism iff that of its image is. -/
lemma map_fix_divB {Y : Model Φ₁ B₁ divB₁} (a : Aut Y) (c : B₁.obj Y.base)
    (h : Φ₁.pb a.hom.base (divB₁.app _ c) = divB₁.app _ c) :
    Φ₂.pb (F.mapIso a).hom.base (divB₂.app _ (mapUnit F hpre c)) =
      divB₂.app _ (mapUnit F hpre c) := by
  have h0 : divB₁.app _ (B₁.pb a.hom.base c - c) = 0 := by
    rw [map_sub, divB₁.natural, h, sub_self]
  have h1 := divB_mapUnit F hpre hbe h0
  rw [mapUnit_sub F hpre hbe, mapUnit_pb F hpre hbe a.hom (isPreStep_of_isIso _), map_sub,
    divB₂.natural, sub_eq_zero] at h1
  exact h1

include hbe in
/-- **`F(twUnit a c) = twUnit (F a) (F^birat c)`**: conjugation by a birational unit is
transported by `F`. -/
theorem map_twUnit {Y : Model Φ₁ B₁ divB₁} (a : Aut Y) (c : B₁.obj Y.base)
    (h : Φ₁.pb a.hom.base (divB₁.app _ c) = divB₁.app _ c) :
    F.mapIso (twUnit a c h) =
      twUnit (F.mapIso a) (mapUnit F hpre c) (map_fix_divB F hpre hbe a c h) := by
  unfold twUnit
  rw [map_unitAut F hpre hbe]
  refine unitAut_congr ?_ _ _
  rw [mapUnit_sub F hpre hbe, mapUnit_pb F hpre hbe a.hom (isPreStep_of_isIso _)]
  rfl

include hbe in
/-- **`F` matches the units** `O^×(Y) ⊆ Aut_C(Y)`. -/
lemma mem_unitsAut_map_iff {Y : Model Φ₁ B₁ divB₁} (a : Aut Y) :
    a ∈ unitsAut Y ↔ F.mapIso a ∈ unitsAut (F.obj Y) := by
  change a.hom.base = 𝟙 _ ↔ (F.map a.hom).base = 𝟙 _
  have := hbe a.hom (𝟙 Y)
  rw [F.map_id] at this
  exact this

include hbe in
/-- **The fraction of the image pair** is the image of the fraction: for base-equivalent
pre-steps `s, t`, `F^birat(u_s − u_t) = u_{F s} − u_{F t}`. -/
lemma mapUnit_u_sub {X Y : Model Φ₁ B₁ divB₁} {s t : X ⟶ Y} (hs : IsPreStep 𝐏₁ s)
    (ht : IsPreStep 𝐏₁ t) (hb : s.base = t.base) :
    mapUnit F hpre (s.u - t.u) = (F.map s).u - (F.map t).u := by
  have e := congrArg 𝐅.map (toBirat_fracPair ht (hs.1.trans ht.1.symm) hb rfl)
  rw [Functor.map_comp, biratFunctor_map_toBirat, biratFunctor_map_toBirat,
    map_birUnit' F hpre hbe] at e
  have eu := congrArg BHom.u e
  have ht1 : (F.map t).deg = 1 := ((hpre t).1 ht).1
  change (F.map s).u = B₂.pb (𝟙 _) (F.map t).u +
    ((F.map t).deg : ℕ) • mapUnit F hpre (s.u - t.u) at eu
  rw [ht1, GrpOn.pb_id', PNat.one_coe, one_smul] at eu
  rw [eu]
  abel

section Equiv

variable [F.IsEquivalence]

include hbe in
/-- **`F^birat` is injective on units.** -/
theorem mapUnit_injective (Y : Model Φ₁ B₁ divB₁) :
    Function.Injective (mapUnit F hpre (X := Y)) := by
  refine (injective_iff_map_eq_zero (mapUnitHom F hpre hbe Y)).2 fun c hc => ?_
  change mapUnit F hpre c = 0 at hc
  obtain ⟨X', α, φ, hα, e⟩ := exists_rep (birUnit Y c)
  have e : (toBirat Φ₁ B₁ divB₁).map α ≫ birUnit Y c = (toBirat Φ₁ B₁ divB₁).map φ := e
  have e' := congrArg 𝐅.map e
  rw [Functor.map_comp, biratFunctor_map_toBirat, biratFunctor_map_toBirat,
    map_birUnit' F hpre hbe, hc] at e'
  have h0 : (toBirat Φ₂ B₂ divB₂).map (F.map α) =
      (toBirat Φ₂ B₂ divB₂).map (F.map α) ≫ birUnit (F.obj Y) 0 := by
    ext
    · simp
    · simp
    · change (F.map α).u = B₂.pb (F.map α).base 0 + ((1 : ℕ+) : ℕ) • (F.map α).u
      rw [map_zero, PNat.one_coe, one_smul, zero_add]
  have hαφ : α = φ := F.map_injective (toBirat_map_injective (h0.trans e'))
  subst hαφ
  have eu := congrArg BHom.u e
  simp only [Birat.comp_u, toBirat_map_u, toBirat_map_base, birUnit_u, birUnit_deg,
    PNat.one_coe, one_smul, add_eq_right] at eu
  haveI : IsIso α.base := hα.2
  have h2 : B₁.pb α.base c = 0 := eu
  have := congrArg (B₁.pb (inv α.base)) h2
  rwa [GrpOn.pb_inv_pb, map_zero] at this

include hbe in
/-- **`F^birat` is surjective on units** (`F` is an equivalence matching pre-steps and
base-equivalent pairs): every birational unit of `F(Y)` comes from one of `Y`. -/
theorem mapUnit_surjective (Y : Model Φ₁ B₁ divB₁) :
    Function.Surjective (mapUnit F hpre (X := Y)) := by
  intro c'
  obtain ⟨X'', α', φ', hα', e⟩ := exists_rep (birUnit (F.obj Y) c')
  have e : (toBirat Φ₂ B₂ divB₂).map α' ≫ birUnit (F.obj Y) c' = (toBirat Φ₂ B₂ divB₂).map φ' :=
    e
  have hd : α'.deg = φ'.deg := by
    have := congrArg BHom.deg e
    simpa using this
  have hb : α'.base = φ'.base := (Category.comp_id _).symm.trans (congrArg BHom.base e)
  let X₁ := F.objPreimage X''
  let ι : F.obj X₁ ≅ X'' := F.objObjPreimageIso X''
  let α : X₁ ⟶ Y := F.preimage (ι.hom ≫ α')
  let φ : X₁ ⟶ Y := F.preimage (ι.hom ≫ φ')
  have hFα : F.map α = ι.hom ≫ α' := F.map_preimage _
  have hFφ : F.map φ = ι.hom ≫ φ' := F.map_preimage _
  have hα : IsPreStep 𝐏₁ α := by
    rw [hpre, hFα]
    exact isPreStep_comp₀ (isPreStep_of_isIso _) hα'
  have hφ'pre : IsPreStep 𝐏₂ φ' := by
    refine ⟨?_, ?_⟩
    · change φ'.deg = 1
      rw [← hd]
      exact hα'.1
    · change IsIso φ'.base
      rw [← hb]
      exact hα'.2
  have hφ : IsPreStep 𝐏₁ φ := by
    rw [hpre, hFφ]
    exact isPreStep_comp₀ (isPreStep_of_isIso _) hφ'pre
  have hbase : α.base = φ.base := by
    rw [hbe, hFα, hFφ, comp_base, comp_base, hb]
  haveI : IsIso α.base := hα.2
  have hα1 : α.deg = 1 := hα.1
  have hφ1 : φ.deg = 1 := hφ.1
  refine ⟨B₁.pb (inv α.base) (φ.u - α.u), ?_⟩
  have key : (toBirat Φ₁ B₁ divB₁).map α ≫ birUnit Y (B₁.pb (inv α.base) (φ.u - α.u)) =
      (toBirat Φ₁ B₁ divB₁).map φ := by
    ext
    · change (1 : ℕ+) * α.deg = φ.deg
      rw [one_mul, hα1, hφ1]
    · change α.base ≫ 𝟙 _ = φ.base
      rw [Category.comp_id, hbase]
    · change B₁.pb α.base (B₁.pb (inv α.base) (φ.u - α.u)) + ((1 : ℕ+) : ℕ) • α.u = φ.u
      rw [GrpOn.pb_pb_inv, PNat.one_coe, one_smul, sub_add_cancel]
  have e1 := congrArg 𝐅.map key
  rw [Functor.map_comp, biratFunctor_map_toBirat, biratFunctor_map_toBirat,
    map_birUnit' F hpre hbe] at e1
  have e1 : (toBirat Φ₂ B₂ divB₂).map (F.map α) ≫
      birUnit (F.obj Y) (mapUnit F hpre (B₁.pb (inv α.base) (φ.u - α.u))) =
      (toBirat Φ₂ B₂ divB₂).map (F.map φ) := e1
  have e2 : (toBirat Φ₂ B₂ divB₂).map (F.map α) ≫ birUnit (F.obj Y) c' =
      (toBirat Φ₂ B₂ divB₂).map (F.map φ) := by
    rw [hFα, hFφ, Functor.map_comp, Functor.map_comp, Category.assoc, e]
  haveI : IsIso ((toBirat Φ₂ B₂ divB₂).map (F.map α)) :=
    (isIso_toBirat_map_iff _).2 ((hpre α).1 hα)
  exact congrArg BHom.u ((cancel_epi _).1 (e1.trans e2.symm))

/-- **`O^×(Y^birat) ≅ O^×(F(Y)^birat)`** ([FrdI], Corollary 4.10, Proposition 4.4(ii)). -/
noncomputable def mapUnitEquiv (Y : Model Φ₁ B₁ divB₁) :
    B₁.obj Y.base ≃+ B₂.obj (F.obj Y).base :=
  AddEquiv.ofBijective (mapUnitHom F hpre hbe Y)
    ⟨mapUnit_injective F hpre hbe Y, mapUnit_surjective F hpre hbe Y⟩

end Equiv

end MapUnit

/-! ### The image data and the transport of `E^Π_N` -/

section Env

variable {D₁ : Type u₁} [Category.{v} D₁]
variable {Φ₁ : DivMonoid.{w} D₁} {B₁ : GrpOn.{w} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v} D₂]
variable {Φ₂ : DivMonoid.{w} D₂} {B₂ : GrpOn.{w} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence]
  (hpre : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y),
    IsPreStep (toElem Φ₁ B₁ divB₁) φ ↔ IsPreStep (toElem Φ₂ B₂ divB₂) (F.map φ))
  (hbe : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ φ' : X ⟶ Y),
    φ.base = φ'.base ↔ (F.map φ).base = (F.map φ').base)

/-- `F` as a fully faithful functor. -/
local notation "𝐅𝐅" => Functor.FullyFaithful.ofFullyFaithful F

include hbe in
lemma mem_unitsAut_autEquivFF_iff (X : Model Φ₁ B₁ divB₁) (a : Aut X) :
    a ∈ unitsAut X ↔ autEquivFF F 𝐅𝐅 X a ∈ unitsAut (F.obj X) :=
  mem_unitsAut_map_iff F hbe a

/-- `Aut_C(X)/O^×(X) ≅ Aut_C(F X)/O^×(F X)`. -/
noncomputable abbrev quotMap (X : Model Φ₁ B₁ divB₁) :
    Aut X ⧸ unitsAut X ≃* Aut (F.obj X) ⧸ unitsAut (F.obj X) :=
  quotAutEquiv 𝐅𝐅 (mem_unitsAut_autEquivFF_iff F hbe X)

variable {X Y : Model Φ₁ B₁ divB₁}

/-- **The image section** `F ∘ σ ∘ F_*^{-1}` (the image base-Frobenius pair, [FrdI],
Corollary 5.7(iii),(iv); `Model.isBaseFrobPair_map`). -/
noncomputable def imSigma (σ : Aut X ⧸ unitsAut X →* Aut X) :
    Aut (F.obj X) ⧸ unitsAut (F.obj X) →* Aut (F.obj X) :=
  ((autEquivFF F 𝐅𝐅 X).toMonoidHom.comp σ).comp (quotMap F hbe X).symm.toMonoidHom

/-- **The image of `π`**: `F_* ∘ π : PX → Aut_C(F X)/O^×(F X)`. -/
noncomputable def imPi {PX : Type*} [Group PX] (π : PX →* Aut X ⧸ unitsAut X) :
    PX →* Aut (F.obj X) ⧸ unitsAut (F.obj X) :=
  (quotMap F hbe X).toMonoidHom.comp π

lemma imSigma_quotMap (σ : Aut X ⧸ unitsAut X →* Aut X) (q : Aut X ⧸ unitsAut X) :
    imSigma F hbe σ (quotMap F hbe X q) = F.mapIso (σ q) := by
  simp only [imSigma, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.symm_apply_apply]
  rfl

lemma imSigma_imPi (σ : Aut X ⧸ unitsAut X →* Aut X) {PX : Type*} [Group PX]
    (π : PX →* Aut X ⧸ unitsAut X) (p : PX) :
    imSigma F hbe σ (imPi F hbe π p) = F.mapIso (σ (π p)) :=
  imSigma_quotMap F hbe σ (π p)

lemma imSigma_sec {σ : Aut X ⧸ unitsAut X →* Aut X}
    (hsec : ∀ q, (QuotientGroup.mk (σ q) : Aut X ⧸ unitsAut X) = q)
    (q : Aut (F.obj X) ⧸ unitsAut (F.obj X)) :
    (QuotientGroup.mk (imSigma F hbe σ q) : Aut (F.obj X) ⧸ unitsAut (F.obj X)) = q := by
  obtain ⟨q₀, rfl⟩ := (quotMap F hbe X).surjective q
  rw [imSigma_quotMap]
  conv_rhs => rw [← hsec q₀]
  rfl

include hpre in
lemma imSigma_fix {s : X ⟶ Y} (hs : IsPreStep 𝐏₁ s) {σ : Aut X ⧸ unitsAut X →* Aut X}
    (hsfix : ∀ q, Φ₁.pb (σ q).hom.base s.div = s.div) (q : Aut (F.obj X) ⧸ unitsAut (F.obj X)) :
    Φ₂.pb (imSigma F hbe σ q).hom.base (F.map s).div = (F.map s).div := by
  obtain ⟨q₀, rfl⟩ := (quotMap F hbe X).surjective q
  rw [imSigma_quotMap]
  exact map_fixes F hpre hs (σ q₀) (hsfix q₀)

section Theta

variable {s t : X ⟶ Y} [IsIso s.base] [IsIso t.base] [IsIso (F.map s).base]
  [IsIso (F.map t).base]
  (hs : IsPreStep (toElem Φ₁ B₁ divB₁) s) (ht : IsPreStep (toElem Φ₁ B₁ divB₁) t)
  (hb : s.base = t.base) {σ : Aut X ⧸ unitsAut X →* Aut X}
  (hsec : ∀ q, (QuotientGroup.mk (σ q) : Aut X ⧸ unitsAut X) = q)
  {PX : Type (max v w)} [Group PX] (π : PX →* Aut X ⧸ unitsAut X)
  (hsfix : ∀ q, Φ₁.pb (σ q).hom.base s.div = s.div) (PY : Subgroup PX) (N : ℕ)


include hpre in
/-- **The bi-Kummer root of the image is the image of the bi-Kummer root** ([EtTh],
Theorem 4.4(iv)): `s⊓-gp_{F}(p) = F(s⊓-gp(p))`. -/
theorem sgp_map (p : PX) :
    sgp (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
        (imSigma_fix F hpre hbe hs hsfix) p = autEquivFF F 𝐅𝐅 Y (sgp hs π hsfix p) := by
  ext1
  symm
  refine liftAut_unique (((hpre s).1 hs)).1 ((imSigma F hbe σ).comp (imPi F hbe π) p) _ ?_
  rw [MonoidHom.comp_apply, imSigma_imPi]
  change F.map s ≫ F.map (sgp hs π hsfix p).hom = F.map (σ (π p)).hom ≫ F.map s
  rw [← F.map_comp, ← F.map_comp, liftGp_spec hs (σ.comp π) (fun p => hsfix (π p)) p]
  rfl

include hbe in
/-- `F` matches `μ_N`. -/
lemma mem_muN_map_iff (m : Aut Y) : m ∈ muN Y N ↔ autEquivFF F 𝐅𝐅 Y m ∈ muN (F.obj Y) N := by
  rw [mem_muN, mem_muN]
  exact and_congr (mem_unitsAut_map_iff F hbe m) (by rw [← map_pow, MulEquiv.map_eq_one_iff])

/-- `(e, p) ↦ (F e, p)` on `Aut_C(Y) × PX`. -/
noncomputable abbrev prodMap : Aut Y × PX ≃* Aut (F.obj Y) × PX :=
  MulEquiv.prodCongr (autEquivFF F 𝐅𝐅 Y) (MulEquiv.refl PX)

include hpre hbe in
lemma mem_thetaE_map_iff (e : Aut Y) :
    e ∈ thetaE hs π hsfix PY N ↔
      autEquivFF F 𝐅𝐅 Y e ∈ thetaE (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
          (imSigma_fix F hpre hbe hs hsfix) PY N := by
  constructor
  · rintro ⟨m, hm, p, hp, rfl⟩
    refine ⟨autEquivFF F 𝐅𝐅 Y m, (mem_muN_map_iff F hbe N m).1 hm, p, hp, ?_⟩
    rw [sgp_map F hpre hbe hs π hsfix]
    exact map_mul (autEquivFF F 𝐅𝐅 Y) m _
  · rintro ⟨m', hm', p, hp, he⟩
    obtain ⟨m, rfl⟩ := (autEquivFF F 𝐅𝐅 Y).surjective m'
    refine ⟨m, (mem_muN_map_iff F hbe N m).2 hm', p, hp, ?_⟩
    apply (autEquivFF F 𝐅𝐅 Y).injective
    rw [map_mul]
    exact he.trans (by rw [sgp_map F hpre hbe hs π hsfix])

include hpre hbe in
lemma mem_thetaEPi_map_iff (x : Aut Y × PX) :
    x ∈ thetaEPi hs π hsfix PY N ↔
      prodMap F x ∈ thetaEPi (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
          (imSigma_fix F hpre hbe hs hsfix) PY N := by
  rw [mem_thetaEPi, mem_thetaEPi]
  refine and_congr Iff.rfl (and_congr (mem_thetaE_map_iff F hpre hbe hs π hsfix PY N x.1) ?_)
  change x.1.hom.base = _ ↔ (autEquivFF F 𝐅𝐅 Y x.1).hom.base = _
  rw [sgp_map F hpre hbe hs π hsfix, base_eq_iff_mul_inv_mem, base_eq_iff_mul_inv_mem,
    mem_unitsAut_map_iff F hbe, Functor.mapIso]
  change autEquivFF F 𝐅𝐅 Y (x.1 * _) ∈ _ ↔ _
  rw [map_mul, map_inv]
  exact Iff.rfl

/-- **`E^Π_N(C₁) ≅ E^Π_N(C₂)`**, `(e, p) ↦ (F e, p)`. -/
noncomputable def ePiMap :
    thetaEPi hs π hsfix PY N ≃* thetaEPi (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
        (imSigma_fix F hpre hbe hs hsfix) PY N where
  toFun x := ⟨prodMap F x, (mem_thetaEPi_map_iff F hpre hbe hs π hsfix PY N x).1 x.2⟩
  invFun y := ⟨(prodMap F).symm y, (mem_thetaEPi_map_iff F hpre hbe hs π hsfix PY N _).2
    (by rw [MulEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext ((prodMap F).symm_apply_apply (x : Aut Y × PX))
  right_inv y := Subtype.ext ((prodMap F).apply_symm_apply (y : Aut (F.obj Y) × PX))
  map_mul' x y := Subtype.ext (map_mul (prodMap F) (x : Aut Y × PX) y)

@[simp] lemma coe_ePiMap (x : thetaEPi hs π hsfix PY N) :
    (ePiMap F hpre hbe hs π hsfix PY N x : Aut (F.obj Y) × PX) =
      (autEquivFF F 𝐅𝐅 Y (x : Aut Y × PX).1, (x : Aut Y × PX).2) := rfl

/-! #### Transport of the twists, the conjugations and the theta section -/

variable {PY}

include hpre hbe in
lemma ePiMap_inlE (m : muN Y N) :
    ePiMap F hpre hbe hs π hsfix PY N (inlE hs π hsfix PY N m) =
      inlE (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
          (imSigma_fix F hpre hbe hs hsfix) PY N
        ⟨autEquivFF F 𝐅𝐅 Y m, (mem_muN_map_iff F hbe N (m : Aut Y)).1 m.2⟩ := rfl

variable (PY)

/-- `F^birat(K^×)`: the image of the constants. -/
noncomputable abbrev imKcst (Kcst : AddSubgroup (B₁.obj Y.base)) :
    AddSubgroup (B₂.obj (F.obj Y).base) :=
  Kcst.map (mapUnitHom F hpre hbe Y)

variable (Kcst : AddSubgroup (B₁.obj Y.base))
  (hKfix : ∀ k ∈ Kcst, ∀ p : PX, B₁.pb (sgp hs π hsfix p).hom.base k = k)
  (htf : ∀ a : Φ₁.obj Y.base, N • a = 0 → a = 0)
  (htfF : ∀ a : Φ₂.obj (F.obj Y).base, N • a = 0 → a = 0)

include hKfix in
/-- The image constants are fixed by the image bi-Kummer root. -/
lemma imKcst_fix : ∀ k ∈ imKcst F hpre hbe Kcst, ∀ p : PX,
    B₂.pb (sgp (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
        (imSigma_fix F hpre hbe hs hsfix) p).hom.base k = k := by
  rintro _ ⟨k, hk, rfl⟩ p
  rw [sgp_map F hpre hbe hs π hsfix p]
  change B₂.pb (F.map (sgp hs π hsfix p).hom).base (mapUnit F hpre k) = mapUnit F hpre k
  rw [← mapUnit_pb F hpre hbe _ (isPreStep_of_isIso _), hKfix k hk p]

/-- The image `F^birat(c) ∈ (F^birat K^×)^{1/N}` of `c ∈ (K^×)^{1/N}`. -/
noncomputable def mapConstRoot (c : constRoots N Kcst) : constRoots N (imKcst F hpre hbe Kcst) :=
  ⟨mapUnit F hpre (c : B₁.obj Y.base), by
    rw [mem_constRoots, ← mapUnit_nsmul F hpre hbe]
    exact ⟨_, c.2, rfl⟩⟩

lemma mapConstRoot_surjective : Function.Surjective (mapConstRoot F hpre hbe N Kcst) := by
  rintro ⟨c', hc'⟩
  obtain ⟨c, rfl⟩ := mapUnit_surjective F hpre hbe Y c'
  refine ⟨⟨c, ?_⟩, rfl⟩
  obtain ⟨k, hk, e⟩ := hc'
  rw [mem_constRoots]
  rw [mapUnitHom_apply, ← mapUnit_nsmul F hpre hbe] at e
  rwa [← mapUnit_injective F hpre hbe Y e]

include hpre hbe in
/-- **`F` transports the `K^×`-twists** ([EtTh], Theorem 5.10(ii): `Ψ^birat` preserves
`(K^×)^{1/N}`). -/
lemma ePiMap_twistE (c : constRoots N Kcst) (x : thetaEPi hs π hsfix PY N) :
    ePiMap F hpre hbe hs π hsfix PY N (twistE hs π hsfix PY N Kcst hKfix htf c x) =
      twistE (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
          (imSigma_fix F hpre hbe hs hsfix) PY N (imKcst F hpre hbe Kcst)
        (imKcst_fix F hpre hbe hs π hsfix Kcst hKfix) htfF (mapConstRoot F hpre hbe N Kcst c)
        (ePiMap F hpre hbe hs π hsfix PY N x) := by
  apply Subtype.ext
  apply Prod.ext
  · change autEquivFF F 𝐅𝐅 Y ((x : Aut Y × PX).1 * twUnit _ _ _) = autEquivFF F 𝐅𝐅 Y
      (x : Aut Y × PX).1 * _
    rw [show autEquivFF F 𝐅𝐅 Y ((x : Aut Y × PX).1 * twUnit (x : Aut Y × PX).1 (c : B₁.obj Y.base)
        (divB_fix_of_mem hs π hsfix N Kcst hKfix htf c.2 x.2)) =
        autEquivFF F 𝐅𝐅 Y ((x : Aut Y × PX).1 * twUnit (x : Aut Y × PX).1 (c : B₁.obj Y.base)
        (divB_fix_of_mem hs π hsfix N Kcst hKfix htf c.2 x.2)) from rfl, map_mul]
    congr 1
    exact map_twUnit F hpre hbe _ _ _
  · rfl


include hpre hbe in
/-- Conjugations by `E^Π_X` are transported. -/
lemma ePiMap_conjE [PY.Normal] (z : thetaEPi hs π hsfix ⊤ N) (y : thetaEPi hs π hsfix PY N) :
    ePiMap F hpre hbe hs π hsfix PY N (conjE hs π hsfix PY N z y) =
      conjE (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
          (imSigma_fix F hpre hbe hs hsfix) PY N (ePiMap F hpre hbe hs π hsfix ⊤ N z)
        (ePiMap F hpre hbe hs π hsfix PY N y) := by
  apply Subtype.ext
  change prodMap F ((z : Aut Y × PX) * (y : Aut Y × PX) * (z : Aut Y × PX)⁻¹) =
    prodMap F (z : Aut Y × PX) * prodMap F (y : Aut Y × PX) * (prodMap F (z : Aut Y × PX))⁻¹
  rw [map_mul, map_mul, map_inv]

variable {PYdd : Subgroup PX} (hle : PYdd ≤ PY)
  (htfix : ∀ p : PYdd, Φ₁.pb (σ (π p)).hom.base t.div = t.div)
  (hFN : ∀ p : PYdd, B₁.pb (σ (π p)).hom.base (N • (s.u - t.u)) = N • (s.u - t.u))

omit [IsIso t.base] [IsIso (F.map t).base] in
include hpre ht htfix in
lemma imHtfix (p : PYdd) :
    Φ₂.pb (imSigma F hbe σ ((imPi F hbe π) p)).hom.base (F.map t).div = (F.map t).div := by
  rw [imSigma_imPi]
  exact map_fixes F hpre ht _ (htfix p)

omit [IsIso s.base] [IsIso t.base] [IsIso (F.map s).base] [IsIso (F.map t).base] in
include hpre hs ht hb hFN in
lemma imHFN (p : PYdd) :
    B₂.pb (imSigma F hbe σ ((imPi F hbe π) p)).hom.base (N • ((F.map s).u - (F.map t).u)) =
      N • ((F.map s).u - (F.map t).u) := by
  rw [imSigma_imPi, ← mapUnit_u_sub F hpre hbe hs ht hb, ← mapUnit_nsmul F hpre hbe]
  change B₂.pb (F.map (σ (π p)).hom).base _ = _
  rw [← mapUnit_pb F hpre hbe _ (isPreStep_of_isIso _), hFN p]


include hpre in
/-- **`s⊔-gp_F(q) = F(s⊔-gp(q))`** ([EtTh], Theorem 4.4(iv)). -/
theorem tgp_map (q : PYdd) :
    tgp (σ := imSigma F hbe σ) ((hpre t).1 ht) (imPi F hbe π)
        (imHtfix F hpre hbe ht π htfix) q = autEquivFF F 𝐅𝐅 Y (tgp ht π htfix q) := by
  ext1
  symm
  refine liftAut_unique (((hpre t).1 ht)).1 (((imSigma F hbe σ).comp
      (imPi F hbe π)).comp PYdd.subtype q) _ ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, imSigma_imPi]
  change F.map t ≫ F.map (tgp ht π htfix q).hom = F.map (σ (π q)).hom ≫ F.map t
  rw [← F.map_comp, ← F.map_comp, liftGp_spec ht ((σ.comp π).comp PYdd.subtype) htfix q]
  rfl


include hpre hbe in
lemma ePiMap_tPi (q : PYdd) :
    ePiMap F hpre hbe hs π hsfix PY N (tPi hs ht hb π hsfix N hle htfix hFN q) =
      tPi (σ := imSigma F hbe σ) ((hpre s).1 hs) ((hpre t).1 ht) ((hbe s t).1 hb) (imPi F hbe π)
          (imSigma_fix F hpre hbe hs hsfix) N hle (imHtfix F hpre hbe ht π htfix)
              (imHFN F hpre hbe hs ht hb π N hFN) q := by
  apply Subtype.ext
  apply Prod.ext
  · exact (tgp_map F hpre hbe ht π htfix q).symm
  · rfl

include hpre hbe in
lemma ePiMap_sPi (q : PYdd) :
    ePiMap F hpre hbe hs π hsfix PY N (sPi hs π hsfix N hle q) =
      sPi (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
          (imSigma_fix F hpre hbe hs hsfix) N hle q := by
  apply Subtype.ext
  apply Prod.ext
  · exact (sgp_map F hpre hbe hs π hsfix q).symm
  · rfl

include hpre hbe in
/-- **[EtTh], Theorem 5.6 (core): the Frobenioid theta cocycle (the Kummer class of
Proposition 5.5) is transported**: `δ_F(q) = F(δ(q))`. -/
theorem deltaE_map (q : PYdd) :
    (deltaE (σ := imSigma F hbe σ) ((hpre s).1 hs) ((hpre t).1 ht) ((hbe s t).1 hb) (imPi F hbe π)
        (imSigma_fix F hpre hbe hs hsfix) N (imHtfix F hpre hbe ht π htfix)
            (imHFN F hpre hbe hs ht hb π N hFN) q : Aut (F.obj Y)) =
      autEquivFF F 𝐅𝐅 Y (deltaE hs ht hb π hsfix N htfix hFN q : Aut Y) := by
  change tgp (σ := imSigma F hbe σ) ((hpre t).1 ht) (imPi F hbe π)
      (imHtfix F hpre hbe ht π htfix) q *
      (sgp (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π) (imSigma_fix F hpre hbe hs hsfix)
          (q : PX))⁻¹ =
    autEquivFF F 𝐅𝐅 Y (tgp ht π htfix q * (sgp hs π hsfix (q : PX))⁻¹)
  rw [map_mul, map_inv, tgp_map F hpre hbe ht π htfix q, sgp_map F hpre hbe hs π hsfix]


include hpre hbe in
lemma conjAut_conjE [PY.Normal] (z : thetaEPi hs π hsfix ⊤ N) :
    MonoThetaEnv.conjAut (ePiMap F hpre hbe hs π hsfix PY N) (conjE hs π hsfix PY N z) =
      conjE (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
          (imSigma_fix F hpre hbe hs hsfix) PY N (ePiMap F hpre hbe hs π hsfix ⊤ N z) := by
  ext y : 1
  obtain ⟨x, rfl⟩ := (ePiMap F hpre hbe hs π hsfix PY N).surjective y
  rw [MonoThetaEnv.conjAut_apply, MulEquiv.symm_apply_apply, ePiMap_conjE]

include hpre hbe in
lemma conjAut_twistE (c : constRoots N Kcst) :
    MonoThetaEnv.conjAut (ePiMap F hpre hbe hs π hsfix PY N)
        (twistE hs π hsfix PY N Kcst hKfix htf c) =
      twistE (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
          (imSigma_fix F hpre hbe hs hsfix) PY N (imKcst F hpre hbe Kcst)
        (imKcst_fix F hpre hbe hs π hsfix Kcst hKfix) htfF (mapConstRoot F hpre hbe N Kcst c) := by
  ext y : 1
  obtain ⟨x, rfl⟩ := (ePiMap F hpre hbe hs π hsfix PY N).surjective y
  rw [MonoThetaEnv.conjAut_apply, MulEquiv.symm_apply_apply, ePiMap_twistE]

include hpre hbe in
lemma map_thetaD_map [PY.Normal] :
    (thetaD hs π hsfix PY N Kcst hKfix htf).map
        (MonoThetaEnv.conjAut (ePiMap F hpre hbe hs π hsfix PY N)) =
      thetaD (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
          (imSigma_fix F hpre hbe hs hsfix) PY N (imKcst F hpre hbe Kcst)
        (imKcst_fix F hpre hbe hs π hsfix Kcst hKfix) htfF := by
  rw [thetaD, thetaD, MonoidHom.map_closure, Set.image_union]
  congr 2
  · ext α
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨_, (conjAut_conjE F hpre hbe hs π hsfix PY N z).symm⟩
    · rintro ⟨z', rfl⟩
      obtain ⟨z, rfl⟩ := (ePiMap F hpre hbe hs π hsfix ⊤ N).surjective z'
      exact ⟨_, ⟨z, rfl⟩, conjAut_conjE F hpre hbe hs π hsfix PY N z⟩
  · ext α
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨_, (conjAut_twistE F hpre hbe hs π hsfix PY N Kcst hKfix htf htfF c).symm⟩
    · rintro ⟨c', rfl⟩
      obtain ⟨c, rfl⟩ := mapConstRoot_surjective F hpre hbe N Kcst c'
      exact ⟨_, ⟨c, rfl⟩, conjAut_twistE F hpre hbe hs π hsfix PY N Kcst hKfix htf htfF c⟩

include hpre hbe in
lemma map_thetaSubgroup (m : muN Y N) :
    ((tPi hs ht hb π hsfix N hle htfix hFN).range.map
        (MulAut.conj (inlE hs π hsfix PY N m)).toMonoidHom).map
          (ePiMap F hpre hbe hs π hsfix PY N).toMonoidHom =
      (tPi (σ := imSigma F hbe σ) ((hpre s).1 hs) ((hpre t).1 ht) ((hbe s t).1 hb) (imPi F hbe π)
          (imSigma_fix F hpre hbe hs hsfix) N hle (imHtfix F hpre hbe ht π htfix)
              (imHFN F hpre hbe hs ht hb π N hFN)).range.map
        (MulAut.conj (inlE (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
            (imSigma_fix F hpre hbe hs hsfix) PY N
          ⟨autEquivFF F 𝐅𝐅 Y m, (mem_muN_map_iff F hbe N (m : Aut Y)).1 m.2⟩)).toMonoidHom := by
  rw [Subgroup.map_map, ← MonoidHom.range_comp, ← MonoidHom.range_comp]
  congr 1
  refine MonoidHom.ext fun q => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, map_mul, map_inv, ePiMap_inlE, ePiMap_tPi]

include hpre hbe in
lemma image_thetaSubgroupsE :
    Subgroup.map (ePiMap F hpre hbe hs π hsfix PY N).toMonoidHom ''
        thetaSubgroupsE hs ht hb π hsfix N hle htfix hFN =
      thetaSubgroupsE (σ := imSigma F hbe σ) ((hpre s).1 hs) ((hpre t).1 ht) ((hbe s t).1 hb)
          (imPi F hbe π) (imSigma_fix F hpre hbe hs hsfix) N hle (imHtfix F hpre hbe ht π htfix)
              (imHFN F hpre hbe hs ht hb π N hFN) := by
  ext H
  constructor
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨_, (map_thetaSubgroup F hpre hbe hs ht hb π hsfix PY N hle htfix hFN m).symm⟩
  · rintro ⟨m', rfl⟩
    obtain ⟨m, hm⟩ := (autEquivFF F 𝐅𝐅 Y).surjective m'
    have hm' : m ∈ muN Y N := (mem_muN_map_iff F hbe N m).2 (hm ▸ m'.2)
    refine ⟨_, ⟨⟨m, hm'⟩, rfl⟩, ?_⟩
    rw [map_thetaSubgroup F hpre hbe hs ht hb π hsfix PY N hle htfix hFN]
    congr 4
    exact Subtype.ext hm

include hpre hbe in
/-- **[EtTh], Theorem 5.6 (core)**: the transport isomorphism maps the cyclotomic rigidity pair
`(s⊓-Π(l), δ(l))` of Proposition 5.5 to that of the image data. -/
lemma ePiMap_inlE_deltaE (q : PYdd) :
    ePiMap F hpre hbe hs π hsfix PY N (inlE hs π hsfix PY N
        (deltaE hs ht hb π hsfix N htfix hFN q)) =
      inlE (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
        (imSigma_fix F hpre hbe hs hsfix) PY N
        (deltaE (σ := imSigma F hbe σ) ((hpre s).1 hs) ((hpre t).1 ht) ((hbe s t).1 hb)
          (imPi F hbe π) (imSigma_fix F hpre hbe hs hsfix) N (imHtfix F hpre hbe ht π htfix)
          (imHFN F hpre hbe hs ht hb π N hFN) q) := by
  rw [ePiMap_inlE]
  congr 1
  exact Subtype.ext (deltaE_map F hpre hbe hs ht hb π hsfix N htfix hFN q).symm

section Top

variable [TopologicalSpace (Aut Y)] [DiscreteTopology (Aut Y)]
  [TopologicalSpace (Aut (F.obj Y))] [DiscreteTopology (Aut (F.obj Y))] [TopologicalSpace PX]
  [IsTopologicalGroup PX]

/-- **`E^Π_N(C₁) ≅ E^Π_N(C₂)` as topological groups.** -/
noncomputable def ePiMapₜ :
    thetaEPi hs π hsfix PY N ≃ₜ* thetaEPi (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
        (imSigma_fix F hpre hbe hs hsfix) PY N where
  toMulEquiv := ePiMap F hpre hbe hs π hsfix PY N
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    change Continuous fun x : thetaEPi hs π hsfix PY N =>
      ((autEquivFF F 𝐅𝐅 Y (x : Aut Y × PX).1 : Aut (F.obj Y)), (x : Aut Y × PX).2)
    exact ((continuous_of_discreteTopology (f := fun a : Aut Y => autEquivFF F 𝐅𝐅 Y a)).comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
        (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    change Continuous fun y : thetaEPi (σ := imSigma F hbe σ) ((hpre s).1 hs) (imPi F hbe π)
        (imSigma_fix F hpre hbe hs hsfix) PY N =>
      (((autEquivFF F 𝐅𝐅 Y).symm (y : Aut (F.obj Y) × PX).1 : Aut Y), (y : Aut (F.obj Y) × PX).2)
    exact ((continuous_of_discreteTopology
      (f := fun a : Aut (F.obj Y) => (autEquivFF F 𝐅𝐅 Y).symm a)).comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
        (continuous_snd.comp continuous_subtype_val)

/-- **[EtTh], Theorem 5.10(iii) (core)**: an equivalence `F` of model Frobenioids matching
pre-steps and base-equivalent pairs induces, by `(e, p) ↦ (F e, p)`, an isomorphism of
Frobenioid-theoretic mono-theta environments from the environment of `(s⊓, s⊔, σ, π, K^×)` to that
of the image data `(F s⊓, F s⊔, F σ F_*^{-1}, F_* π, F^birat(K^×))`
    (its underlying map is `ePiMap`, so it is
compatible with the projections `ε` to `Aut_C(B_N)`, `Aut_C(F B_N)` via `F`). -/
noncomputable def frobEnvMap [PY.Normal] :
    MonoThetaEnv.Iso (frobEnv hs ht hb π hsfix N Kcst hKfix htf hle htfix hFN)
      (frobEnv (σ := imSigma F hbe σ) ((hpre s).1 hs) ((hpre t).1 ht) ((hbe s t).1 hb)
          (imPi F hbe π) (imSigma_fix F hpre hbe hs hsfix) N (imKcst F hpre hbe Kcst)
        (imKcst_fix F hpre hbe hs π hsfix Kcst hKfix) htfF hle (imHtfix F hpre hbe ht π htfix)
            (imHFN F hpre hbe hs ht hb π N hFN)) where
  e := ePiMapₜ F hpre hbe hs π hsfix PY N
  map_D := map_thetaD_map F hpre hbe hs π hsfix PY N Kcst hKfix htf htfF
  map_theta := image_thetaSubgroupsE F hpre hbe hs ht hb π hsfix PY N hle htfix hFN

/-- **[EtTh], Theorem 5.6**: the isomorphism of cyclotomes of [EtTh], Corollary 2.19(i)
(`MonoThetaEnv.IsCyc`; by Lemma 5.9(v) = `Model.frobEnv_isCyc` it is the Frobenioid cyclotomic
rigidity isomorphism of Proposition 5.5) is transported by `F`. -/
theorem frobEnvMap_isCyc [PY.Normal] (Lsub Ksub Dsub : Subgroup (thetaEPi hs π hsfix PY N))
    (x m : thetaEPi hs π hsfix PY N) :
    (frobEnv (σ := imSigma F hbe σ) ((hpre s).1 hs) ((hpre t).1 ht) ((hbe s t).1 hb)
        (imPi F hbe π) (imSigma_fix F hpre hbe hs hsfix) N (imKcst F hpre hbe Kcst)
        (imKcst_fix F hpre hbe hs π hsfix Kcst hKfix) htfF hle (imHtfix F hpre hbe ht π htfix)
        (imHFN F hpre hbe hs ht hb π N hFN)).IsCyc
        (Lsub.map (ePiMap F hpre hbe hs π hsfix PY N).toMonoidHom)
        (Ksub.map (ePiMap F hpre hbe hs π hsfix PY N).toMonoidHom)
        (Dsub.map (ePiMap F hpre hbe hs π hsfix PY N).toMonoidHom)
        (ePiMap F hpre hbe hs π hsfix PY N x) (ePiMap F hpre hbe hs π hsfix PY N m) ↔
      (frobEnv hs ht hb π hsfix N Kcst hKfix htf hle htfix hFN).IsCyc Lsub Ksub Dsub x m :=
  (frobEnvMap F hpre hbe hs ht hb π hsfix PY N Kcst hKfix htf htfF hle htfix hFN).isCyc_iff
    rfl rfl rfl x m


end Top

end Theta

end Env

/-! ### Equivalences over slim bases of FSM-type -/

section FSM

variable {D₁ : Type u₁} [Category.{v} D₁] [TotallyEpimorphic D₁]
variable {Φ₁ : DivMonoid.{w} D₁} {B₁ : GrpOn.{w} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v} D₂] [TotallyEpimorphic D₂]
variable {Φ₂ : DivMonoid.{w} D₂} {B₂ : GrpOn.{w} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

/-- **The hypothesis `hpre` of `Model.frobEnvMap` over bases of FSM-type** ([FrdI],
Theorem 3.4(ii), `Model.typeCorresp_fsm`). -/
theorem preStep_iff_fsm (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁) (hΦ₁ : Φ₁.NonDilating)
    (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂) (hB₂ : HasAllTorsion B₂)
    (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] :
    ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y),
      IsPreStep (toElem Φ₁ B₁ divB₁) φ ↔ IsPreStep (toElem Φ₂ B₂ divB₂) (F.map φ) :=
  fun _ _ φ => (typeCorresp_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F).preStep φ

/-- **The hypothesis `hbe` of `Model.frobEnvMap` over slim bases of FSM-type** ([FrdI],
Theorem 3.4(v), applied to `F` and to a quasi-inverse of `F`): `F` preserves and reflects
the equality of bases. -/
theorem base_eq_iff_fsm (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁) (hΦ₁ : Φ₁.NonDilating)
    (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂) (hB₂ : HasAllTorsion B₂)
    (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike) (hS₁ : IsSlim D₁) (hS₂ : IsSlim D₂)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] :
    ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ φ' : X ⟶ Y),
      φ.base = φ'.base ↔ (F.map φ).base = (F.map φ').base := by
  intro X Y φ φ'
  have c := typeCorresp_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F
  refine ⟨fun e => base_map_eq_of_base_eq F c.pullback c.baseIso φ φ' e hS₂, fun e => ?_⟩
  have c' := typeCorresp_fsm hD₂ hB₂ hΦ₂ hG₂ hD₁ hB₁ hΦ₁ hG₁ F.inv
  have e' := base_map_eq_of_base_eq F.inv c'.pullback c'.baseIso (F.map φ) (F.map φ') e hS₁
  rw [Functor.inv_fun_map, Functor.inv_fun_map, comp_base, comp_base, comp_base,
    comp_base] at e'
  have ha : IsIso (F.asEquivalence.unitInv.app X).base :=
    ((isIso_iff _).1 (F.asEquivalence.unitIso.app X).isIso_inv).2.1
  have hb : IsIso (F.asEquivalence.unit.app Y).base :=
    ((isIso_iff _).1 (F.asEquivalence.unitIso.app Y).isIso_hom).2.1
  have e'' := congrArg (fun g => inv (F.asEquivalence.unitInv.app X).base ≫ g ≫
    inv (F.asEquivalence.unit.app Y).base) e'
  simpa using e''

end FSM

end Model

end Frobenioid

end Iut
