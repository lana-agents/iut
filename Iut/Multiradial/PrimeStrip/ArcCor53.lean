/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.ArcVdash
import Iut.Multiradial.PrimeStrip.RlfClass
import Iut.Multiradial.PrimeStrip.Cor53Bij
import Iut.AutHolomorphic.Elliptic.EllNat

/-!
# IUT I, Corollary 5.3 (ii) at `v ∈ V^arc`: surjectivity (MR21, session 7)

IUT I, Corollary 5.3 (ii) (`Inter-universal Teichmuller Theory I.txt`, l.9891–9894) cites
[AbsTopIII], Proposition 4.2 (i) (`Topics in Absolute Anabelian Geometry III.txt`, l.6210–6225)
at `V^arc`. Here, for the constituents `F_v = (C_v, E_{Λ₀}, κ_v)` (`Arc.lean`, deviation H5):

* `elem_isIso_div_deg`, `elem_eq_of_isIso`: isomorphisms in `F_{ℝ_{≥0}}` over `Pt` have divisor
  `0` and degree `1`, so parallel isomorphisms coincide;
* **the conjugation autoequivalence** of the Frobenioid of angular regions
  (`Angular.conjEquiv`: `(B, τ) ↦ (B̄, τ)`, `(d, μ) ↦ (d, μ̄)`; `val_conjF`) and **`conjFrobIso`**,
  the corresponding automorphism of `C_v` as a `FrobCat.Iso` (identity on the base and on `Φ`);
* `c_S = ellConj S p` (the automorphism of `ℂ` induced by `S ∈ Aut(D_v)` on `A_{D_v}`) does not
  depend on `p` (`ellConj_indep`), satisfies the cocycle relation `c_{S≫T} = c_T ∘ c_S`
  (`ellConj_trans`, from the naturality `Ell.ellEquiv_trans` of `EllNat.lean`) and
  `c_{S⁻¹} = c_S` (`ellConj_symm`);
* `FArcData.Iso.ofS`: an automorphism of `F_v` over `S` from an automorphism of `C_v` acting on
  `μ` of linear endomorphisms of isotropic objects by `c_S` (Kummer compatibility `kappa_of_val`,
  read through every `ψ : D_v ≅ E_Λ`);
* **`FArcData.IsoClass.toD_surjective_model`**, **`FArcComp.isoClassToD_surjective`**:
  `Isom(‡F_v, ‡F'_v) → Isom(‡D_v, ‡D'_v)` is surjective (lift by the identity if `c_S = id`, by
  the conjugation if `c_S = conj`);
* `DStrip.IsoClass`, `FStrip.isoClassToD` and **`FStrip.isoClassToD_surjective`**: Corollary 5.3
  (ii), surjectivity, over all of `V` (inputs at `V^non` as in `FStripNon.isoClassToD_bijective`).

Injectivity at `V^arc` (the `F ≅ 𝟭` rigidity of the Frobenioid of angular regions) and the
bijectivity over all of `V` are in `ArcRigid.lean`.
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory Iut.Frobenioid Iut.AutHol Set Pointwise

/-! ### Isomorphisms in `F_{ℝ_{≥0}}` over the one-morphism category -/

/-- In `F_{ℝ_{≥0}}` over `Pt`, an isomorphism has divisor `0` and degree `1`. -/
lemma elem_isIso_div_deg {X Y : Elem phiReal.{0}} (φ : X ⟶ Y) [IsIso φ] :
    φ.div = 0 ∧ φ.deg = 1 := by
  have h := IsIso.hom_inv_id φ
  have hd : (inv φ).deg * φ.deg = 1 := congrArg Elem.Hom.deg h
  have hd1 : φ.deg = 1 := PNat.eq (Nat.eq_one_of_mul_eq_one_left (congrArg PNat.val hd))
  have hd2 : (inv φ).deg = 1 := PNat.eq (Nat.eq_one_of_mul_eq_one_right (congrArg PNat.val hd))
  have hv := congrArg (fun f : X ⟶ X => (Elem.Hom.div f).down) h
  simp only [Elem.comp_div, hd2, PNat.one_coe, one_smul, ULift.add_down] at hv
  have h1 : 0 ≤ φ.div.down := φ.div_mem
  have h2 : 0 ≤ (inv φ).div.down := (inv φ).div_mem
  change (inv φ).div.down + φ.div.down = 0 at hv
  exact ⟨ULift.ext _ _ (by change φ.div.down = 0; linarith), hd1⟩

/-- In `F_{ℝ_{≥0}}` over `Pt`, two isomorphisms between the same objects coincide. -/
lemma elem_eq_of_isIso {X Y : Elem phiReal.{0}} (φ ψ : X ⟶ Y) [IsIso φ] [IsIso ψ] : φ = ψ :=
  Elem.hom_ext (Subsingleton.elim _ _)
    ((elem_isIso_div_deg φ).1.trans (elem_isIso_div_deg ψ).1.symm)
    ((elem_isIso_div_deg φ).2.trans (elem_isIso_div_deg ψ).2.symm)

/-- In `F_{ℝ_{≥0}}` over `Pt`, two isomorphisms between the same objects coincide. -/
lemma elem_iso_hom_eq {X Y : Elem phiReal.{0}} (e e' : X ≅ Y) : e.hom = e'.hom :=
  elem_eq_of_isIso _ _

/-! ### The conjugation autoequivalence of the Frobenioid of angular regions -/

namespace Angular

open Iut.Frobenioid.Angular

lemma IsAngular.inv {B : Set Circle} (h : IsAngular B) : IsAngular B⁻¹ := by
  refine ⟨h.1.inv, ?_, h.2.2.inv⟩
  rw [← Set.image_inv_eq_inv]
  exact h.2.1.image _ continuous_inv.continuousOn

/-- **The complex conjugate `Ā = B̄ × (0, e^τ]` of an angular region.** -/
def conjObj (A : Obj) : Obj := ⟨A.ang⁻¹, IsAngular.inv A.isAngular, A.tip⟩

lemma conj_ang_le {A A' : Obj} (f : A ⟶ A') :
    {f.rot⁻¹} * (conjObj A).ang ^ (f.deg : ℕ) ⊆ (conjObj A').ang := by
  have h := Set.inv_subset_inv.2 f.ang_le
  rwa [mul_inv, Set.inv_singleton, ← inv_pow] at h

/-- **The complex conjugate of a morphism**: `(d, μ) ↦ (d, μ̄)`. -/
def conjHom {A A' : Obj} (f : A ⟶ A') : conjObj A ⟶ conjObj A' :=
  mkHom f.deg f.rad f.rot⁻¹ (conj_ang_le f) f.tip_le

/-- **The conjugation functor** of the Frobenioid of angular regions. -/
def conjF : Obj ⥤ Obj where
  obj := conjObj
  map := conjHom
  map_id A := by ext <;> simp [conjHom]
  map_comp f g := by
    ext
    · rfl
    · rfl
    · simp only [conjHom, comp_rot, mkHom_rot, mkHom_deg, mul_inv, inv_pow]

@[simp] lemma conjF_deg {A A' : Obj} (f : A ⟶ A') : (conjF.map f).deg = f.deg := rfl
@[simp] lemma conjF_rad {A A' : Obj} (f : A ⟶ A') : (conjF.map f).rad = f.rad := rfl
@[simp] lemma conjF_rot {A A' : Obj} (f : A ⟶ A') : (conjF.map f).rot = f.rot⁻¹ := rfl

lemma conjObj_conjObj (A : Obj) : conjObj (conjObj A) = A := Obj.ext (inv_inv _) rfl

/-- `A ≅ conj(conj A)`. -/
def conjUnit (A : Obj) : A ≅ conjF.obj (conjF.obj A) :=
  isoMk 0 1 (by rw [Set.singleton_one, one_mul]; exact (congrArg Obj.ang (conjObj_conjObj A)).symm)
    (by simp [conjF, conjObj])

/-- **The conjugation autoequivalence** (an involution). -/
def conjEquiv : Obj ≌ Obj where
  functor := conjF
  inverse := conjF
  unitIso := NatIso.ofComponents conjUnit fun f => by ext <;> simp [conjUnit]
  counitIso := NatIso.ofComponents (fun A => (conjUnit A).symm) fun f => by
    ext <;> simp [conjUnit]
  functor_unitIso_comp A := by ext <;> simp [conjUnit]

/-- **`val` of a conjugate morphism is the complex conjugate.** -/
lemma val_conjF {A A' : Obj} (f : A ⟶ A') : val (conjF.map f) = starRingEnd ℂ (val f) := by
  simp only [val, conjF_rad, conjF_rot, map_mul, Complex.conj_ofReal, Circle.coe_inv_eq_conj]

lemma isIsotropic_conjF {A : Obj} (hA : IsIsotropic P A) : IsIsotropic P (conjF.obj A) := by
  rw [isIsotropic_iff] at hA ⊢
  change A.ang⁻¹ = univ
  rw [hA, Set.inv_univ]

lemma conjF_mem_orhd {A : Obj} (e : A ⟶ A) (he : e ∈ Orhd P A) :
    conjF.map e ∈ Orhd P (conjF.obj A) := by
  rw [mem_orhd] at he ⊢
  exact he

/-- `P ∘ conj = P`. -/
@[reducible] def conjCommP :
    CatCommSq conjF P P
      (FrobCat.elemMap (𝟭 Pt) (fun A => AddEquiv.refl (phiReal.obj A)) (fun _ _ => Iff.rfl)
        (fun _ _ => rfl)) :=
  ⟨NatIso.ofComponents (fun _ => CategoryTheory.Iso.refl _) fun f => by
    refine (Category.comp_id _).trans ((Elem.hom_ext (Subsingleton.elim _ _) ?_ rfl).trans
      (Category.id_comp _).symm)
    rfl⟩

end Angular

open Angular in
/-- **The conjugation autoequivalence of the Frobenioid of angular regions as an automorphism of
the Frobenioid `C_v`** (`v ∈ V^arc`; identity on the base `Pt` and on `Φ = ℝ_{≥0}`). -/
def conjFrobIso : fArcModel.F.Iso fArcModel.F where
  C := conjEquiv
  D := CategoryTheory.Equivalence.refl
  phi _ := AddEquiv.refl _
  phi_pos _ _ := Iff.rfl
  phi_pb _ _ := rfl
  phiInv _ := AddEquiv.refl _
  phiInv_pos _ _ := Iff.rfl
  phiInv_pb _ _ := rfl
  phi_unit A x := fArcModel.F.Φ.pb_id A x
  phi_counit B y := fArcModel.F.Φ.pb_id B y
  commP := conjCommP
  commPInv := conjCommP
  commP_counit B := elem_iso_hom_eq
    ((FrobCat.sqIso conjCommP).app _ ≪≫ (FrobCat.elemMap _ _ _ _).mapIso
      ((FrobCat.sqIso conjCommP).app B) ≪≫ FrobCat.elemIsoOfBase _)
    (Angular.P.mapIso (X := conjF.obj (conjF.obj B)) (Y := B) (conjEquiv.counitIso.app B))
  commP_unit A := elem_iso_hom_eq
    ((FrobCat.sqIso conjCommP).app _ ≪≫ (FrobCat.elemMap _ _ _ _).mapIso
      ((FrobCat.sqIso conjCommP).app A) ≪≫ (FrobCat.elemIsoOfBase _).symm)
    (Angular.P.mapIso (X := conjF.obj (conjF.obj A)) (Y := A)
      (conjEquiv.unitIso.app A).symm)

end PrimeStrip

end Multiradial

end Iut

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory Iut.Frobenioid Iut.AutHol

/-! ### `c_S`: independence of the point and the cocycle relation -/

/-- `c_p` does not depend on `p` (`A_p ∪ {0}` is the same set of endomorphisms for every `p`). -/
lemma ellConj_indep (S : ellModel.Iso ellModel) (p q : ellModel.X) : ellConj S p = ellConj S q :=
  RingHom.ext fun _ => rfl

/-- `c_p(ellEquiv p x) = ellEquiv_{S} p x`. -/
lemma ellConj_ellEquiv (S : ellModel.Iso ellModel) (p : ellModel.X)
    (x : Ell.EllField ellModel.A p) :
    ellConj S p (Ell.ellEquiv isIso_refl_model p x) =
      Ell.ellEquiv (S.hol.trans isIso_refl_model) p x := by
  simp [ellConj]

/-- **`c_S` through the transport along `S`** (naturality of `ellEquiv`). -/
lemma ellEquiv_ellTransport (S : ellModel.Iso ellModel) (p : ellModel.X)
    (x : Ell.EllField ellModel.A p) :
    Ell.ellEquiv isIso_refl_model (S.e p) (Ell.ellTransport S.hol p x) =
      ellConj S p (Ell.ellEquiv isIso_refl_model p x) :=
  (Ell.ellEquiv_trans_apply S.hol isIso_refl_model p x).symm.trans (ellConj_ellEquiv S p x).symm

/-- **Cocycle relation** `c_{S ≫ T} = c_T ∘ c_S`. -/
lemma ellConj_trans (S T : ellModel.Iso ellModel) (p : ellModel.X) (z : ℂ) :
    ellConj (S.trans T) p z = ellConj T (S.e p) (ellConj S p z) := by
  obtain ⟨x, rfl⟩ := (Ell.ellEquiv isIso_refl_model p).surjective z
  rw [ellConj_ellEquiv, ← ellEquiv_ellTransport, ellConj_ellEquiv]
  exact Ell.ellEquiv_trans_apply S.hol (T.hol.trans isIso_refl_model) p x

/-- `c_S = id` if `S` is the identity map. -/
lemma ellConj_of_id (S : ellModel.Iso ellModel) (hS : ∀ x, S.e x = x) (p : ellModel.X) (z : ℂ) :
    ellConj S p z = z := by
  obtain ⟨x, rfl⟩ := (Ell.ellEquiv isIso_refl_model p).surjective z
  rw [ellConj_ellEquiv]
  have h : (S.e.trans (Homeomorph.refl ellModel.X)) = Homeomorph.refl ellModel.X :=
    Homeomorph.ext hS
  have key : ∀ {φ : ellModel.X ≃ₜ Ell.punct lam0}
      (hφ : AutHol.IsIso ellModel.A (Ell.ellStr lam0) φ), φ = Homeomorph.refl ellModel.X →
        Ell.ellEquiv hφ p x = Ell.ellEquiv isIso_refl_model p x := by
    intro φ hφ hφe
    subst hφe
    rfl
  exact key _ h

/-- **`c_{S⁻¹} = c_S`** (both are `id` or `conj`, and `c_{S⁻¹} ∘ c_S = id`). -/
lemma ellConj_symm (S : ellModel.Iso ellModel) (p q : ellModel.X) :
    ellConj S.symm q = ellConj S p := by
  have h1 : ∀ z, ellConj S.symm (S.e p) (ellConj S p z) = z := fun z => by
    rw [← ellConj_trans]
    exact ellConj_of_id _ (fun x => S.e.symm_apply_apply x) p z
  rw [ellConj_indep S.symm q (S.e p)]
  refine RingHom.ext fun z => ?_
  have h2 := h1 (ellConj S p z)
  rwa [invol_id_or_conj (ellConj_eq S p)] at h2

/-! ### Lifting automorphisms of `D_v` to `F_v` -/

/-- Kummer compatibility for the model from `μ(e') = c_S(μ(e))`. -/
lemma kappa_of_val (S : ellModel.Iso ellModel) (p : ellModel.X) (A : Angular.Obj)
    (hA : IsIsotropic Angular.P A) (e : Orhd Angular.P A) (A' : Angular.Obj)
    (hA' : IsIsotropic Angular.P A') (e' : Orhd Angular.P A')
    (hv : Angular.val e'.1 = ellConj S ptE (Angular.val e.1)) (L : PeriodPair)
    (ψ : ellModel.X ≃ₜ Ell.punct L) (hψ : AutHol.IsIso ellModel.A (Ell.ellStr L) ψ) :
    Ell.ellEquiv (S.hol.trans hψ) p (fArcModel.kappa p A hA e) =
      Ell.ellEquiv hψ (S.e p) (fArcModel.kappa (S.e p) A' hA' e') := by
  refine (Ell.ellEquiv_trans_apply S.hol hψ p _).trans (congrArg _ ?_)
  apply (Ell.ellEquiv isIso_refl_model (S.e p)).injective
  refine (ellEquiv_ellTransport S p _).trans ?_
  refine ((congrArg (ellConj S p) (Angular.ellEquiv_kummerEll
    (AutHol.IsIso.refl (Ell.ellStr lam0)) p hA e)).trans ?_).trans
      (Angular.ellEquiv_kummerEll (AutHol.IsIso.refl (Ell.ellStr lam0)) (S.e p) hA' e').symm
  rw [hv, ellConj_indep S p ptE]

/-- **An automorphism of `F_v` over a given automorphism `S` of `D_v`** from an automorphism of
the Frobenioid `C_v` preserving isotropic objects and `O^▷`, acting on `μ` of linear
endomorphisms of isotropic objects by `c_S`. -/
def FArcData.Iso.ofS (S : ellModel.Iso ellModel) (F : fArcModel.F.Iso fArcModel.F)
    (hiso : ∀ A, IsIsotropic Angular.P A → IsIsotropic Angular.P (F.C.functor.obj A))
    (horhd : ∀ A (e : A ⟶ A), e ∈ Orhd Angular.P A →
      F.C.functor.map e ∈ Orhd Angular.P (F.C.functor.obj A))
    (hiso' : ∀ A, IsIsotropic Angular.P A → IsIsotropic Angular.P (F.C.inverse.obj A))
    (horhd' : ∀ A (e : A ⟶ A), e ∈ Orhd Angular.P A →
      F.C.inverse.map e ∈ Orhd Angular.P (F.C.inverse.obj A))
    (hval : ∀ A (_ : IsIsotropic Angular.P A) (e : Orhd Angular.P A),
      Angular.val (F.C.functor.map e.1) = ellConj S ptE (Angular.val e.1))
    (hval' : ∀ A (_ : IsIsotropic Angular.P A) (e : Orhd Angular.P A),
      Angular.val (F.C.inverse.map e.1) = ellConj S ptE (Angular.val e.1)) :
    FArcData.Iso fArcModel fArcModel where
  F := F
  S := S
  map_iso := hiso
  map_orhd := horhd
  inv_iso := hiso'
  inv_orhd := horhd'
  kappa p A hA e L ψ hψ := kappa_of_val S p A hA e _ _ _ (hval A hA e) L ψ hψ
  kappaInv p B hB e L ψ hψ := kappa_of_val S.symm p B hB e _ _ _
    ((hval' B hB e).trans (by rw [ellConj_symm S ptE ptE])) L ψ hψ

/-- **IUT I, Corollary 5.3 (ii), surjectivity at `v ∈ V^arc`, for the model**: every automorphism
of `D_v` lifts to an automorphism of `F_v` (by the identity of `C_v` if `c_S = id`, by the
conjugation autoequivalence if `c_S = conj`; [AbsTopIII] Prop 4.2 (i)). -/
theorem FArcData.IsoClass.toD_surjective_model :
    Function.Surjective (FArcData.IsoClass.toD : FArcData.IsoClass fArcModel fArcModel →
      ellModel.Iso ellModel) := by
  intro S
  rcases ellConj_eq S ptE with h | h
  · refine ⟨FArcData.IsoClass.mk (FArcData.Iso.ofS S (FrobCat.Iso.refl _) (fun _ h => h)
      (fun _ _ h => h) (fun _ h => h) (fun _ _ h => h) (fun _ _ e => ?_) (fun _ _ e => ?_)), rfl⟩
    · rw [h]; rfl
    · rw [h]; rfl
  · refine ⟨FArcData.IsoClass.mk (FArcData.Iso.ofS S conjFrobIso
      (fun _ h => Angular.isIsotropic_conjF h) (fun _ e h => Angular.conjF_mem_orhd e h)
      (fun _ h => Angular.isIsotropic_conjF h) (fun _ e h => Angular.conjF_mem_orhd e h)
      (fun _ _ e => ?_) (fun _ _ e => ?_)), rfl⟩
    · rw [h]; exact Angular.val_conjF e.1
    · rw [h]; exact Angular.val_conjF e.1

/-- **IUT I, Corollary 5.3 (ii), surjectivity at `v ∈ V^arc`**: for constituents `‡F_v`, `‡F'_v`
of `F`-prime-strips, `Isom(‡F_v, ‡F'_v) → Isom(‡D_v, ‡D'_v)` is surjective. -/
theorem FArcComp.isoClassToD_surjective (X Y : FArcComp) :
    Function.Surjective (FArcData.IsoClass.toD : FArcData.IsoClass X.X Y.X → X.X.S.Iso Y.X.S) := by
  intro S
  obtain ⟨a, ha⟩ := FArcData.IsoClass.toD_surjective_model
    ((X.model.S.symm.trans S).trans Y.model.S)
  obtain ⟨f, rfl⟩ := FArcData.IsoClass.mk_surjective a
  refine ⟨FArcData.IsoClass.mk ((X.model.trans f).trans Y.model.symm), ?_⟩
  rw [FArcData.IsoClass.toD_mk] at ha ⊢
  apply EllSp.Iso.ext'
  ext x
  change Y.model.S.e.symm (f.S.e (X.model.S.e x)) = S.e x
  rw [ha]
  change Y.model.S.e.symm (Y.model.S.e (S.e (X.model.S.e.symm (X.model.S.e x)))) = S.e x
  simp

end PrimeStrip

end Multiradial

end Iut

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

variable {D : InitialThetaData.{0}}

/-- **Isomorphisms of `D`-prime-strips in the sense of IUT I, §0**: classes of equivalences at
`V^non`, isomorphisms of Aut-holomorphic spaces at `V^arc`. -/
def DStrip.IsoClass (P Q : DStrip D) : Type :=
  P.non.IsoClass Q.non × ∀ v, (P.arc v).S.Iso (Q.arc v).S

/-- **The map `Isom(¹F, ²F) → Isom(¹D, ²D)` of IUT I, Corollary 5.3 (ii)** over all of `V`. -/
def FStrip.isoClassToD {P Q : FStrip D} (a : P.IsoClass Q) : P.toD.IsoClass Q.toD :=
  (FStripNon.isoClassToD a.1, fun v => (a.2 v).toD)

/-- **IUT I, Corollary 5.3 (ii), surjectivity, over all of `V`** (l.9891–9894): at `V^non` from
`FStripNon.isoClassToD_bijective`'s inputs (`DeltaCharacteristic`, H3, `PivCountable` at
`V^bad`), at `V^arc` unconditional (`FArcComp.isoClassToD_surjective`). -/
theorem FStrip.isoClassToD_surjective (hΔ : ∀ v : Vnon D, DeltaCharacteristic D v)
    (h3 : ∀ v : Vnon D, PiToGQuotient D v) (hc : ∀ v : Vnon D, v ∈ D.VBad → PivCountable D v)
    (P Q : FStrip D) :
    Function.Surjective (FStrip.isoClassToD : P.IsoClass Q → P.toD.IsoClass Q.toD) := by
  intro a
  obtain ⟨b, hb⟩ := (FStripNon.isoClassToD_bijective hΔ h3 hc P.non Q.non).2 a.1
  choose c hc' using fun v => FArcComp.isoClassToD_surjective (P.arc v) (Q.arc v) (a.2 v)
  exact ⟨(b, c), Prod.ext hb (funext hc')⟩

end PrimeStrip

end Multiradial

end Iut
