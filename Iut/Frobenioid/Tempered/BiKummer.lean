/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.BaseFrob

/-!
# Bi-Kummer roots ([EtTh], Proposition 4.3, Theorem 4.4)

[EtTh], Proposition 4.3(i): for an `N`-th root `s⊓_N, s⊔_N : A_N → B_N` of a fraction-pair
(base-equivalent pre-steps) and the homomorphism `str^trv_N : H_{A_N} → Aut_C(A_N)` of a
base-Frobenius pair, there are unique homomorphisms `s⊓-gp_N, s⊔-gp_N : H_{B_N} → Aut_C(B_N)` with

  `s⊓-gp_N(h) ∘ s⊓_N = s⊓_N ∘ str^trv_N(h)`, `s⊔-gp_N(h) ∘ s⊔_N = s⊔_N ∘ str^trv_N(h)`

(the **bi-Kummer `N`-th root**). The proof there: by the equivalences of categories determined by
pre-steps ([FrdI], Definition 1.3(iii)(d)) and total epimorphicity it suffices that
`Div(s⊓_N), Div(s⊔_N)` are fixed by `H_{A_N}`. (iii): the difference `s⊓-gp_N · (s⊔-gp_N)^{-1}` is a
twisted homomorphism `H_{B_N} → μ_N(B_N)`, the Kummer class of `f|_{B_N}`.

Here, for a model Frobenioid `C = Model Φ B divB`:

* `Model.exists_unique_lift_iff` (**Proposition 4.3(i)**, one automorphism): for a pre-step
  `s : X → Y` and `a ∈ Aut_C(X)` there is a (unique) `b ∈ Aut_C(Y)` with `s ≫ b = a ≫ s` iff
  `Base(a)^* Div(s) = Div(s)`; the lift `Model.liftAut` is explicit;
* `Model.liftGp s ρ` (**Proposition 4.3(i)**): for a homomorphism `ρ : H →* Aut_C(X)` whose
  values fix `Div(s)`, the unique homomorphism `H →* Aut_C(Y)` with `s ≫ liftGp(h) = ρ(h) ≫ s`;
* `Model.kummerUnit` and `Model.unit_comp_liftAut` (**Proposition 4.3(iii)**): for base-equivalent
  pre-steps `s, t : X → Y` (with `F = u_s − u_t`, the root of the fraction-pair), the two lifts of
  `a` differ by the unit `κ(a) = (Base s^{-1})^*(Base(a)^* F − F) ∈ O^×(Y)` — the Kummer cocycle
  `h ↦ h(F)/F` of `F`, transported to `Y`; `Model.nsmul_kummerUnit` (it is `N`-torsion when `a`
  fixes `N·F`, i.e. it lies in `μ_N(Y)`), `Model.kummerUnit_mul` (the cocycle relation);
* `Model.liftAut_unit` and `Model.liftAut_comp_iso` (**Proposition 4.3(ii)**, the indeterminacies):
  lifts of units of `X` are units of `Y`, the same for `s` and `t` (simultaneous conjugation), and
  replacing `s` by `s ≫ ζ` for `ζ ∈ Aut_C(Y)` conjugates the lift by `ζ` (non-simultaneous
  conjugation by `μ_N(B_N)`, and the isomorphisms `v` of Proposition 4.2(i));
* **Theorem 4.4(ii),(iv)** for functors `F` of model Frobenioids matching pre-steps and preserving
  base-equivalent pairs (e.g. equivalences over slim bases of FSM-type, [FrdI], Theorem 3.4):
  `Model.coprime_map_iff` (disjoint supports are preserved, through the co-primary
  characterization `Model.coprime_iff_coprimary`), `Model.isFracPair_map` (fraction-pairs map to
  fraction-pairs for the image of `f` under `F^birat`), `Model.map_liftAut` (bi-Kummer roots map to
  bi-Kummer roots, `Model.map_fixes`); the Kummer cocycles, being differences of the two lifts,
  are then preserved as well. `Model.isFracPair_map_fsm` supplies the hypotheses for equivalences
  over bases of FSM-type ([FrdI], Theorem 3.4, `Iut/Frobenioid/Tempered/Thm34Temp.lean`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u w₁ w₂ v₁ v₂ u₁ u₂

namespace Model

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-! ### Lifting automorphisms along pre-steps ([EtTh], Proposition 4.3(i)) -/

section Lift

variable {X Y : Model Φ B divB} (s : X ⟶ Y) [IsIso s.base]

/-- **The lift of `a ∈ Aut_C(X)` along the pre-step `s`** (as a morphism): base
`Base(s)^{-1} Base(a) Base(s)`, rational function `(Base s^{-1})^*(Base(a)^* u_s + u_a − u_s)`. -/
noncomputable def liftHom (hs : s.deg = 1) (a : Aut X) (ha : Φ.pb a.hom.base s.div = s.div) :
    Y ⟶ Y :=
  mk1 (inv s.base ≫ a.hom.base ≫ s.base) 0 (Φ.pos _).zero_mem
    (B.pb (inv s.base) (B.pb a.hom.base s.u + a.hom.u - s.u)) (by
      apply (show Function.Injective (Φ.pb s.base) from fun x y hxy => by
        simpa only [GrpOn.pb_inv_pb] using congrArg (Φ.pb (inv s.base)) hxy)
      have rs := s.rel
      rw [hs, PNat.one_coe, one_smul] at rs
      have ra := a.hom.rel
      rw [deg_of_iso a, PNat.one_coe, one_smul, div_of_iso a, add_zero] at ra
      have rs' := congrArg (Φ.pb a.hom.base) rs
      simp only [map_add, ← GrpOn.pb_comp'] at rs'
      rw [ha] at rs'
      simp only [add_zero, map_add, map_sub, divB.natural, ← GrpOn.pb_comp',
        IsIso.hom_inv_id_assoc, IsIso.hom_inv_id, GrpOn.pb_id']
      simp only [GrpOn.pb_comp'] at rs' ⊢
      linear_combination (norm := abel) rs' + ra - rs)

variable {s}

lemma liftHom_spec (hs : s.deg = 1) (a : Aut X) (ha : Φ.pb a.hom.base s.div = s.div) :
    s ≫ liftHom s hs a ha = a.hom ≫ s := by
  ext
  · simp [liftHom, hs, deg_of_iso a]
  · simp [liftHom]
  · simp [liftHom, hs, div_of_iso a, ha]
  · simp only [comp_u, liftHom, mk1_u, mk1_deg, PNat.one_coe, one_smul, GrpOn.pb_pb_inv,
      hs]
    abel

lemma isIso_liftHom (hs : s.deg = 1) (a : Aut X) (ha : Φ.pb a.hom.base s.div = s.div) :
    IsIso (liftHom s hs a ha) :=
  isIso_of _ rfl (by simp only [liftHom, mk1_base]; infer_instance) rfl

/-- **The lift `b ∈ Aut_C(Y)` of `a ∈ Aut_C(X)` along the pre-step `s`** ([EtTh],
Proposition 4.3(i)): `s ≫ b = a ≫ s`. -/
noncomputable def liftAut (hs : s.deg = 1) (a : Aut X) (ha : Φ.pb a.hom.base s.div = s.div) :
    Aut Y :=
  haveI := isIso_liftHom hs a ha
  asIso (liftHom s hs a ha)

lemma liftAut_spec (hs : s.deg = 1) (a : Aut X) (ha : Φ.pb a.hom.base s.div = s.div) :
    s ≫ (liftAut hs a ha).hom = a.hom ≫ s := liftHom_spec hs a ha

lemma liftAut_hom (hs : s.deg = 1) (a : Aut X) (ha : Φ.pb a.hom.base s.div = s.div) :
    (liftAut hs a ha).hom = liftHom s hs a ha := rfl

/-- Uniqueness of lifts (pre-steps are epimorphisms). -/
lemma liftAut_unique (hs : s.deg = 1) (a : Aut X) (ha : Φ.pb a.hom.base s.div = s.div)
    {b : Y ⟶ Y} (hb : s ≫ b = a.hom ≫ s) : b = (liftAut hs a ha).hom :=
  cancel_preStep_left ⟨hs, (inferInstance : IsIso s.base)⟩ (hb.trans (liftAut_spec hs a ha).symm)

/-- **[EtTh], Proposition 4.3(i)** (for one automorphism): `a ∈ Aut_C(X)` lifts along the
pre-step `s` to a (unique) automorphism `b` of `Y` with `s ≫ b = a ≫ s` iff `Base(a)` fixes
`Div(s)`. -/
theorem exists_unique_lift_iff (hs : s.deg = 1) (a : Aut X) :
    (∃! b : Y ⟶ Y, IsIso b ∧ s ≫ b = a.hom ≫ s) ↔ Φ.pb a.hom.base s.div = s.div := by
  constructor
  · rintro ⟨b, ⟨hb, e⟩, -⟩
    have := congrArg Hom.div e
    simp only [comp_div, div_of_isIso b, map_zero, zero_add, PNat.one_coe,
      one_smul, div_of_iso a, add_zero, hs] at this
    rw [show (b.deg : ℕ) = 1 from by rw [((isIso_iff b).1 hb).1]; rfl, one_smul] at this
    exact this.symm
  · intro ha
    exact ⟨(liftAut hs a ha).hom, ⟨inferInstance, liftAut_spec hs a ha⟩,
      fun b ⟨_, hb⟩ => liftAut_unique hs a ha hb⟩

lemma liftAut_mul (hs : s.deg = 1) (a a' : Aut X) (ha : Φ.pb a.hom.base s.div = s.div)
    (ha' : Φ.pb a'.hom.base s.div = s.div) (haa : Φ.pb (a * a').hom.base s.div = s.div) :
    liftAut hs (a * a') haa = liftAut hs a ha * liftAut hs a' ha' := by
  ext1
  symm
  refine liftAut_unique hs _ haa ?_
  change s ≫ (liftAut hs a' ha').hom ≫ (liftAut hs a ha).hom = (a' ≪≫ a).hom ≫ s
  rw [reassoc_of% (liftAut_spec hs a' ha'), liftAut_spec hs a ha, Iso.trans_hom, Category.assoc]

lemma liftAut_one (hs : s.deg = 1) (h1 : Φ.pb (1 : Aut X).hom.base s.div = s.div) :
    liftAut hs 1 h1 = 1 := by
  ext1
  symm
  exact liftAut_unique hs _ h1 (by change s ≫ 𝟙 Y = 𝟙 X ≫ s; simp)

variable (hs : IsPreStep (toElem Φ B divB) s)

/-- **The bi-Kummer root homomorphism** ([EtTh], Proposition 4.3(i)): for `ρ : H →* Aut_C(X)`
whose values fix `Div(s)` (e.g. `str^trv_N` on `H_{A_N}`), the unique homomorphism
`H →* Aut_C(Y)` with `s ≫ liftGp(h) = ρ(h) ≫ s`. -/
noncomputable def liftGp {H : Type*} [Group H] (ρ : H →* Aut X)
    (hρ : ∀ h, Φ.pb (ρ h).hom.base s.div = s.div) : H →* Aut Y where
  toFun h := liftAut hs.1 (ρ h) (hρ h)
  map_one' := by
    rw [← liftAut_one hs.1 (by rw [← map_one ρ]; exact hρ 1)]
    congr 1
    exact map_one ρ
  map_mul' h h' := by
    rw [← liftAut_mul hs.1 _ _ (hρ h) (hρ h') (by rw [← map_mul]; exact hρ _)]
    congr 1
    exact map_mul ρ h h'

lemma liftGp_spec {H : Type*} [Group H] (ρ : H →* Aut X)
    (hρ : ∀ h, Φ.pb (ρ h).hom.base s.div = s.div) (h : H) :
    s ≫ (liftGp hs ρ hρ h).hom = (ρ h).hom ≫ s := liftAut_spec hs.1 _ _

/-- Uniqueness of the bi-Kummer root homomorphism. -/
lemma liftGp_unique {H : Type*} [Group H] (ρ : H →* Aut X)
    (hρ : ∀ h, Φ.pb (ρ h).hom.base s.div = s.div) (σ : H →* Aut Y)
    (hσ : ∀ h, s ≫ (σ h).hom = (ρ h).hom ≫ s) : σ = liftGp hs ρ hρ := by
  ext h : 2
  exact liftAut_unique hs.1 _ _ (hσ h)

end Lift

/-! ### Indeterminacies ([EtTh], Proposition 4.3(ii)) -/

section Indet

variable {X Y : Model Φ B divB} {s : X ⟶ Y} [IsIso s.base]

/-- **Lifts of units are units**, independent of the rational function of the pre-step: for
`c ∈ O^×(X)`, `lift_s(c) = (1, id, 0, (Base s^{-1})^* u_c)`. -/
lemma liftHom_unit (hs : s.deg = 1) (c : Aut X) (hc : c.hom.base = 𝟙 _)
    (hcs : Φ.pb c.hom.base s.div = s.div) :
    liftHom s hs c hcs = mk1 (𝟙 _) 0 (Φ.pos _).zero_mem (B.pb (inv s.base) c.hom.u) (by
      have ra := c.hom.rel
      rw [deg_of_iso c, PNat.one_coe, one_smul, div_of_iso c, add_zero, hc, GrpOn.pb_id'] at ra
      have : divB.app _ c.hom.u = 0 := by
        have := congrArg (· - X.α) ra
        simpa using this.symm
      simp [divB.natural, this]) := by
  ext
  · rfl
  · simp [liftHom, hc]
  · rfl
  · simp [liftHom, hc]

/-- **Simultaneous conjugation** ([EtTh], Proposition 4.3(ii)(a)): for base-equivalent pre-steps
`s, t`, the lifts of a unit `c ∈ O^×(X)` along `s` and along `t` agree. -/
lemma liftAut_unit_eq {t : X ⟶ Y} (hb : s.base = t.base) (hs : s.deg = 1) (ht : t.deg = 1)
    (c : Aut X) (hc : c.hom.base = 𝟙 _) (hcs : Φ.pb c.hom.base s.div = s.div)
    (hct : Φ.pb c.hom.base t.div = t.div) :
    haveI : IsIso t.base := by rw [← hb]; infer_instance
    (liftAut hs c hcs).hom = (liftAut ht c hct).hom := by
  haveI : IsIso t.base := by rw [← hb]; infer_instance
  rw [liftAut_hom, liftAut_hom]
  ext
  · rfl
  · simp [liftHom, hb]
  · rfl
  · simp [liftHom, hc, hb]

/-- **Non-simultaneous conjugation** ([EtTh], Proposition 4.3(ii)(b); also the isomorphisms `v`
of Proposition 4.2(i),(iv)): replacing `s` by `s ≫ ζ` for `ζ : Y ≅ Y'` conjugates the lift by
`ζ`. -/
lemma liftAut_comp_iso {Y' : Model Φ B divB} (hs : s.deg = 1) (ζ : Y ≅ Y') (a : Aut X)
    (ha : Φ.pb a.hom.base s.div = s.div) (hsζ : (s ≫ ζ.hom).deg = 1) [IsIso (s ≫ ζ.hom).base]
    (ha' : Φ.pb a.hom.base (s ≫ ζ.hom).div = (s ≫ ζ.hom).div) :
    (liftAut hsζ a ha').hom = ζ.inv ≫ (liftAut hs a ha).hom ≫ ζ.hom := by
  symm
  refine liftAut_unique hsζ a ha' ?_
  rw [Category.assoc, ζ.hom_inv_id_assoc, reassoc_of% (liftAut_spec hs a ha)]

end Indet

/-! ### The Kummer cocycle ([EtTh], Proposition 4.3(iii)) -/

section Kummer

variable {X Y : Model Φ B divB} {s t : X ⟶ Y} [IsIso s.base]

/-- **The Kummer cocycle** of the fraction `F = u_s − u_t` at `a ∈ Aut_C(X)`, transported to `Y`:
`κ(a) = (Base s^{-1})^*(Base(a)^* F − F)` (additive notation for `h(F)/F`). -/
noncomputable def kummerUnit (s t : X ⟶ Y) [IsIso s.base] (a : Aut X) : B.obj Y.base :=
  B.pb (inv s.base) (B.pb a.hom.base (s.u - t.u) - (s.u - t.u))

/-- `κ(a)` is a unit of `Y` (`Div_B κ(a) = 0`) when `Base(a)` fixes `Div(s)` and `Div(t)`. -/
lemma divB_kummerUnit (hs : IsPreStep 𝐏 s) (ht : IsPreStep 𝐏 t) (hb : s.base = t.base)
    (a : Aut X) (has : Φ.pb a.hom.base s.div = s.div) (hat : Φ.pb a.hom.base t.div = t.div) :
    divB.app _ (kummerUnit s t a) = 0 := by
  rw [kummerUnit, divB.natural, map_sub, divB.natural, ← div_sub_div hs ht hb,
    map_sub (Φ.pb a.hom.base), has, hat, sub_self, map_zero]

/-- **[EtTh], Proposition 4.3(iii)**: the lifts of `a` along base-equivalent pre-steps `s, t`
differ by the unit `κ(a)`: `κ(a) ≫ lift_t(a) = lift_s(a)`. -/
theorem unit_comp_liftAut (hs : IsPreStep 𝐏 s) (ht : IsPreStep 𝐏 t) (hb : s.base = t.base)
    (a : Aut X) (has : Φ.pb a.hom.base s.div = s.div) (hat : Φ.pb a.hom.base t.div = t.div) :
    haveI : IsIso t.base := by rw [← hb]; infer_instance
    unitHom Y (kummerUnit s t a) (divB_kummerUnit hs ht hb a has hat) ≫
      (liftAut ht.1 a hat).hom = (liftAut hs.1 a has).hom := by
  haveI : IsIso t.base := by rw [← hb]; infer_instance
  rw [liftAut_hom, liftAut_hom]
  ext
  · simp [unitHom, liftHom]
  · simp [unitHom, liftHom, hb]
  · simp [unitHom, liftHom]
  · simp only [comp_u, unitHom, liftHom, mk1_u, mk1_base, mk1_deg, GrpOn.pb_id', PNat.one_coe,
      one_smul, kummerUnit, ← hb, map_sub, map_add]
    abel

/-- **The Kummer cocycle takes values in `μ_N`**: if `Base(a)` fixes `N·F` (`a` fixes `f = F^N`),
then `N·κ(a) = 0`. -/
lemma nsmul_kummerUnit (a : Aut X) (N : ℕ)
    (hN : B.pb a.hom.base (N • (s.u - t.u)) = N • (s.u - t.u)) :
    N • kummerUnit s t a = 0 := by
  rw [kummerUnit, ← map_nsmul, smul_sub, ← map_nsmul, hN, sub_self, map_zero]

/-- **The cocycle relation**: `κ(a a') = a'^* κ(a) + κ(a')` (on `X`, before transport to `Y`),
i.e. `κ` is a twisted homomorphism for the action of `Aut_C(X)` on `B(X_D)` by pull-back along
bases. -/
lemma kummerUnit_mul (a a' : Aut X) :
    kummerUnit s t (a * a') = B.pb (inv s.base) (B.pb a'.hom.base
      (B.pb (s.base) (kummerUnit s t a))) + kummerUnit s t a' := by
  simp only [kummerUnit, GrpOn.pb_pb_inv]
  change B.pb (inv s.base) (B.pb (a'.hom ≫ a.hom).base _ - _) = _
  rw [comp_base, GrpOn.pb_comp', ← map_add]
  congr 1
  simp only [map_sub]
  abel

end Kummer

/-! ### Category-theoreticity ([EtTh], Theorem 4.4) -/

section Map

variable {D₁ : Type u₁} [Category.{v₁} D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂
local notation "𝐓₁" => toBirat Φ₁ B₁ divB₁
local notation "𝐓₂" => toBirat Φ₂ B₂ divB₂

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence]
  (hpre : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y),
    IsPreStep (toElem Φ₁ B₁ divB₁) φ ↔ IsPreStep (toElem Φ₂ B₂ divB₂) (F.map φ))

include hpre in
/-- **Co-primary pairs of pre-steps are preserved** by an equivalence matching pre-steps (the
co-primary condition of [FrdI], Proposition 4.1(iii), is phrased in terms of pre-steps and
isomorphisms only). -/
theorem coprimary_map_iff {E I G : Model Φ₁ B₁ divB₁} (ε : E ⟶ G) (ι : I ⟶ G) :
    (∀ (Z : Model Φ₁ B₁ divB₁) (ζ : Z ⟶ G) (ε' : E ⟶ Z) (ι' : I ⟶ Z), IsPreStep 𝐏₁ ζ →
        IsPreStep 𝐏₁ ε' → IsPreStep 𝐏₁ ι' → ε' ≫ ζ = ε → ι' ≫ ζ = ι → IsIso ζ) ↔
      (∀ (Z : Model Φ₂ B₂ divB₂) (ζ : Z ⟶ F.obj G) (ε' : F.obj E ⟶ Z) (ι' : F.obj I ⟶ Z),
        IsPreStep 𝐏₂ ζ → IsPreStep 𝐏₂ ε' → IsPreStep 𝐏₂ ι' → ε' ≫ ζ = F.map ε →
          ι' ≫ ζ = F.map ι → IsIso ζ) := by
  constructor
  · intro h Z ζ ε' ι' hζ hε' hι' e₁ e₂
    let Z₁ := F.objPreimage Z
    let e : F.obj Z₁ ≅ Z := F.objObjPreimageIso Z
    let ζ₁ : Z₁ ⟶ G := F.preimage (e.hom ≫ ζ)
    let ε₁ : E ⟶ Z₁ := F.preimage (ε' ≫ e.inv)
    let ι₁ : I ⟶ Z₁ := F.preimage (ι' ≫ e.inv)
    have hζ₁ : IsPreStep 𝐏₁ ζ₁ := by
      rw [hpre, Functor.map_preimage]
      exact isPreStep_comp₀ (isPreStep_of_isIso _) hζ
    have hε₁ : IsPreStep 𝐏₁ ε₁ := by
      rw [hpre, Functor.map_preimage]
      exact isPreStep_comp₀ hε' (isPreStep_of_isIso _)
    have hι₁ : IsPreStep 𝐏₁ ι₁ := by
      rw [hpre, Functor.map_preimage]
      exact isPreStep_comp₀ hι' (isPreStep_of_isIso _)
    have hiso := h Z₁ ζ₁ ε₁ ι₁ hζ₁ hε₁ hι₁
      (F.map_injective (by simp [ε₁, ζ₁, e₁])) (F.map_injective (by simp [ι₁, ζ₁, e₂]))
    have : IsIso (F.map ζ₁) := inferInstance
    rw [Functor.map_preimage] at this
    have : ζ = e.inv ≫ (e.hom ≫ ζ) := by simp
    rw [this]
    infer_instance
  · intro h Z ζ ε' ι' hζ hε' hι' e₁ e₂
    have := h (F.obj Z) (F.map ζ) (F.map ε') (F.map ι') ((hpre ζ).1 hζ) ((hpre ε').1 hε')
      ((hpre ι').1 hι') (by rw [← F.map_comp, e₁]) (by rw [← F.map_comp, e₂])
    exact isIso_of_fully_faithful F ζ

include hpre in
/-- **Disjoint supports are preserved** ([EtTh], Theorem 4.4(ii), proof): for base-equivalent
pre-steps `s, t`, `Div(s)` and `Div(t)` are coprime iff `Div(F s)` and `Div(F t)` are. -/
theorem coprime_map_iff {X Y : Model Φ₁ B₁ divB₁} {s t : X ⟶ Y} (hs : IsPreStep 𝐏₁ s)
    (ht : IsPreStep 𝐏₁ t) (hb : s.base = t.base) (hb' : (F.map s).base = (F.map t).base) :
    Φ₁.Coprime s.div t.div ↔ Φ₂.Coprime (F.map s).div (F.map t).div := by
  have hs' := (hpre s).1 hs
  have ht' := (hpre t).1 ht
  haveI : IsIso s.base := hs.2
  haveI : IsIso t.base := ht.2
  haveI : IsIso (F.map s).base := hs'.2
  haveI : IsIso (F.map t).base := ht'.2
  have key₁ : Φ₁.Coprime s.div t.div ↔
      Φ₁.Coprime (Φ₁.pb (inv s.base) s.div) (Φ₁.pb (inv t.base) t.div) := by
    have e : Φ₁.pb (inv t.base) t.div = Φ₁.pb (inv s.base) t.div := by
      congr 1
      simp [hb]
    rw [e, DivMonoid.coprime_pb_iff]
  have key₂ : Φ₂.Coprime (F.map s).div (F.map t).div ↔
      Φ₂.Coprime (Φ₂.pb (inv (F.map s).base) (F.map s).div)
        (Φ₂.pb (inv (F.map t).base) (F.map t).div) := by
    have e : Φ₂.pb (inv (F.map t).base) (F.map t).div =
        Φ₂.pb (inv (F.map s).base) (F.map t).div := by
      congr 1
      simp [hb']
    rw [e, DivMonoid.coprime_pb_iff]
  rw [key₁, key₂, coprime_iff_coprimary hs ht, coprime_iff_coprimary hs' ht']
  exact coprimary_map_iff F hpre s t

variable (hbe : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ φ' : X ⟶ Y), φ.base = φ'.base →
  (F.map φ).base = (F.map φ').base)

/-- The image `F^birat(f) ∈ O^×(F(X)^birat)` of `f ∈ O^×(X^birat)` ([FrdI], Corollary 4.10). -/
noncomputable def mapUnit {X : Model Φ₁ B₁ divB₁} (f : B₁.obj X.base) : B₂.obj (F.obj X).base :=
  ((biratFunctor F fun _ _ φ h => (hpre φ).1 h).map (birUnit X f)).u

omit [F.IsEquivalence] in
include hbe in
lemma map_birUnit {X : Model Φ₁ B₁ divB₁} (f : B₁.obj X.base) :
    (biratFunctor F fun _ _ φ h => (hpre φ).1 h).map (birUnit X f) =
      birUnit (F.obj X) (mapUnit F hpre f) := by
  obtain ⟨hd, hb⟩ := biratFunctor_map_unit F (fun _ _ φ h => (hpre φ).1 h) hbe (birUnit X f)
    rfl rfl
  ext
  · exact hd
  · exact hb
  · rfl

include hbe in
/-- **[EtTh], Theorem 4.4(ii)**: an equivalence matching pre-steps and preserving base-equivalent
pairs maps fraction-pairs for `f` to fraction-pairs for `F^birat(f)`. -/
theorem isFracPair_map {X Y : Model Φ₁ B₁ divB₁} {s t : X ⟶ Y} {f : B₁.obj X.base}
    (h : IsFracPair s t f) : IsFracPair (F.map s) (F.map t) (mapUnit F hpre f) := by
  obtain ⟨hs, ht, hb, hf, hc⟩ := h
  have hs' := (hpre s).1 hs
  have ht' := (hpre t).1 ht
  have hb' := hbe s t hb
  refine ⟨hs', ht', hb', ?_, (coprime_map_iff F hpre hs ht hb hb').1 hc⟩
  have e := toBirat_fracPair ht (show s.deg = t.deg from hs.1.trans ht.1.symm) hb hf
  have e' := congrArg (biratFunctor F fun _ _ φ h => (hpre φ).1 h).map e
  rw [Functor.map_comp, biratFunctor_map_toBirat, biratFunctor_map_toBirat,
    map_birUnit F hpre hbe] at e'
  have eu := congrArg BHom.u e'
  simp only [toBirat_map_u, Birat.comp_u, birUnit_u, birUnit_base, toBirat_map_deg,
    show (F.map t).deg = 1 from ht'.1, PNat.one_coe, one_smul] at eu
  rw [eu]
  change B₂.pb (𝟙 _) (F.map t).u + _ - (F.map t).u = _
  rw [GrpOn.pb_id']
  abel

omit [F.IsEquivalence] in
/-- **[EtTh], Theorem 4.4(iv)** (bi-Kummer roots are preserved): `F` maps the lift of `a` along
`s` to the lift of `F(a)` along `F(s)`. -/
theorem map_liftAut {X Y : Model Φ₁ B₁ divB₁} {s : X ⟶ Y} [IsIso s.base] (hs : s.deg = 1)
    (a : Aut X) (ha : Φ₁.pb a.hom.base s.div = s.div) [IsIso (F.map s).base]
    (hs' : (F.map s).deg = 1) (ha' : Φ₂.pb (F.mapIso a).hom.base (F.map s).div = (F.map s).div) :
    F.map (liftAut hs a ha).hom = (liftAut hs' (F.mapIso a) ha').hom :=
  liftAut_unique hs' _ ha' (by rw [← F.map_comp, liftAut_spec, F.map_comp]; rfl)

omit [F.IsEquivalence] in
include hpre in
/-- The image of a lift preserves `Div`-fixedness: `F(a)` fixes `Div(F s)` when it lifts. -/
lemma map_fixes {X Y : Model Φ₁ B₁ divB₁} {s : X ⟶ Y} (hs : IsPreStep 𝐏₁ s) (a : Aut X)
    (ha : Φ₁.pb a.hom.base s.div = s.div) :
    Φ₂.pb (F.mapIso a).hom.base (F.map s).div = (F.map s).div := by
  haveI : IsIso s.base := hs.2
  have hs' := (hpre s).1 hs
  haveI : IsIso (F.map s).base := hs'.2
  refine (exists_unique_lift_iff hs'.1 (F.mapIso a)).1 ?_
  obtain ⟨b, ⟨hb, e⟩, -⟩ := (exists_unique_lift_iff hs.1 a).2 ha
  refine ⟨F.map b, ⟨inferInstance, by rw [← F.map_comp, e, F.map_comp]; rfl⟩, ?_⟩
  rintro c ⟨hc, ec⟩
  exact cancel_preStep_left hs' (ec.trans (by rw [← F.map_comp, e, F.map_comp]; rfl))

end Map

section FSM

variable {D₁ : Type u₁} [Category.{v₁} D₁] [TotallyEpimorphic D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂] [TotallyEpimorphic D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

/-- **[EtTh], Theorem 4.4(ii) over bases of FSM-type** (the tempered bases `B^temp(Π)⁰`, `D₂`
slim): every equivalence of model Frobenioids maps fraction-pairs for `f` to fraction-pairs for
the image `f'` of `f` under `F^birat`. -/
theorem isFracPair_map_fsm (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁)
    (hΦ₁ : Φ₁.NonDilating) (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂)
    (hB₂ : HasAllTorsion B₂) (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (hS₂ : IsSlim D₂) (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence]
    {X Y : Model Φ₁ B₁ divB₁} {s t : X ⟶ Y} {f : B₁.obj X.base} (h : IsFracPair s t f) :
    ∃ f' : B₂.obj (F.obj X).base, IsFracPair (F.map s) (F.map t) f' ∧
      ∀ hF, (biratFunctor F hF).map (birUnit X f) = birUnit (F.obj X) f' := by
  have c := typeCorresp_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F
  have hpre : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y),
      IsPreStep (toElem Φ₁ B₁ divB₁) φ ↔ IsPreStep (toElem Φ₂ B₂ divB₂) (F.map φ) :=
    fun _ _ φ => c.preStep φ
  have hbe : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ φ' : X ⟶ Y), φ.base = φ'.base →
      (F.map φ).base = (F.map φ').base :=
    fun _ _ φ φ' e => base_map_eq_of_base_eq F c.pullback c.baseIso φ φ' e hS₂
  exact ⟨mapUnit F hpre f, isFracPair_map F hpre hbe h, fun _ => map_birUnit F hpre hbe f⟩

end FSM

end Model

end Frobenioid

end Iut
