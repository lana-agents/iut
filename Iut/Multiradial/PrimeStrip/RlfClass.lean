/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.ArcVdash
import Iut.Multiradial.PrimeStrip.VdashRes
import Iut.Multiradial.PrimeStrip.FRlf

/-!
# `F ↦ F^⊢` and `F ↦ F^⊩` on isomorphism classes of prime-strips (MR21)

IUT I, Remark 5.2.1 (ii) (l.9827–9850 of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`): there is a functorial
algorithm `‡F ↦ ‡F^⊢` (the mono-analyticisation) and, "from the rigidity of the divisor monoids
associated to the Frobenioids that appear at each of the components at `v ∈ V` of an
`F`-prime-strip [cf., especially, the topological field structure of the field `A_{D_v}`]", a
functorial algorithm `‡F ↦ ‡F^⊩ = (‡C^⊩, Prime(‡C^⊩) ≅ V, ‡F^⊢, {‡ρ_v})`, isomorphic to
`F^⊩_mod`.

As for the constituents (`VdashRes.lean`, `ArcVdash.lean`), the mono-analyticisation of every
`F`-prime-strip is, up to isomorphism, the model (`F^⊢_mod`, `F^⊩_mod`); the content of the
algorithm is its action on isomorphisms, here on isomorphism classes (IUT I, §0):

* `FStrip.IsoClass`, `FVdashStrip.IsoClass` (constituentwise classes) and
  **`FStrip.vdashClass : Isom(‡F, ‡F') → Aut(F^⊢_mod)`** (`FComp.vdashClass` at `V^non`,
  `FArcComp.vdashClass` at `V^arc`), functorial (`FStrip.vdashClass_trans`, `_refl`);
* `FRlfData.IsoClass`: isomorphisms of `F^⊩`-data modulo natural isomorphism of the global
  equivalences and 2-isomorphism of the `F^⊢`-parts;
* **`ρ_v` compatibility**: every class in the image of `F ↦ F^⊢` has a representative acting as
  the identity on the divisor monoids (`PhiTriv`; at `V^non` the isomorphisms `resIso` are the
  identity on `Φ`, at `V^arc` this is the rigidity `FArcData.Iso.phi_apply`), hence compatible with
  the `ρ_v` of `F^⊩_mod` (`rlfIsoOf`);
* **`FStrip.rlfClass : Isom(‡F, ‡F') → Aut(F^⊩_mod)`** (the global part acts as the identity),
  with `FStrip.rlfClass_toVdash` (its `F^⊢`-part is `FStrip.vdashClass`) and functoriality
  (`FStrip.rlfClass_trans`, `FStrip.rlfClass_refl`).

Inputs: at `V^non` those of `vdashRes` (`ResInputs D v`: `DeltaCharacteristic`, H3,
`PivCountable` at `V^bad`, `TauLift`); none at `V^arc` (deviation H5 of `Arc.lean` stays).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

section Strips

variable {D : InitialThetaData.{0}}

/-! ### Classes of isomorphisms of prime-strips -/

/-- **Isomorphisms of `F`-prime-strips in the sense of IUT I, §0**: constituentwise classes. -/
def FStrip.IsoClass (P Q : FStrip D) : Type :=
  P.non.IsoClass Q.non × ∀ v, FArcData.IsoClass (P.arc v).X (Q.arc v).X

/-- **Isomorphisms of `F^⊢`-prime-strips in the sense of IUT I, §0**: constituentwise classes. -/
def FVdashStrip.IsoClass (P Q : FVdashStrip D) : Type :=
  P.non.IsoClass Q.non × ∀ v, FVdashArcData.IsoClass (P.arc v).X (Q.arc v).X

/-- The class of an isomorphism of `F`-prime-strips. -/
def FStrip.Iso.cls {P Q : FStrip D} (f : P.Iso Q) : P.IsoClass Q :=
  (FStripNon.Iso.cls f.1, fun v => FArcData.IsoClass.mk (f.2 v))

/-- The identity class. -/
def FStrip.IsoClass.refl (P : FStrip D) : P.IsoClass P :=
  (fun _ => FrobCat.IsoClass.refl _, fun _ => FArcData.IsoClass.refl _)

/-- The composite. -/
def FStrip.IsoClass.trans {P Q R : FStrip D} (a : P.IsoClass Q) (b : Q.IsoClass R) :
    P.IsoClass R :=
  (fun v => (a.1 v).trans (b.1 v), fun v => (a.2 v).trans (b.2 v))

/-- The identity class. -/
def FVdashStrip.IsoClass.refl (P : FVdashStrip D) : P.IsoClass P :=
  (fun _ => SplitFrobCat.IsoClass.refl _, fun _ => FVdashArcData.IsoClass.refl _)

/-- The composite. -/
def FVdashStrip.IsoClass.trans {P Q R : FVdashStrip D} (a : P.IsoClass Q) (b : Q.IsoClass R) :
    P.IsoClass R :=
  (fun v => (a.1 v).trans (b.1 v), fun v => (a.2 v).trans (b.2 v))

/-! ### `F ↦ F^⊢` on classes of strips -/

/-- **`F ↦ F^⊢` on isomorphism classes of `F`-prime-strips** (IUT I, Remark 5.2.1 (ii)): an
isomorphism class `‡F ≅ ‡F'` gives an automorphism class of `F^⊢_mod` (`FComp.vdashClass` at
`V^non`, `FArcComp.vdashClass` at `V^arc`). -/
def FStrip.vdashClass (h : ∀ v : Vnon D, ResInputs D v) {P Q : FStrip D} (a : P.IsoClass Q) :
    (FVdashStrip.ofThetaData D).IsoClass (FVdashStrip.ofThetaData D) :=
  (fun v => FComp.vdashClass (h v) (a.1 v), fun v => FArcComp.vdashClass (a.2 v))

/-- **Functoriality of `F ↦ F^⊢` on strips**: composites. -/
theorem FStrip.vdashClass_trans (h : ∀ v : Vnon D, ResInputs D v) {P Q R : FStrip D}
    (a : P.IsoClass Q) (b : Q.IsoClass R) :
    FStrip.vdashClass h (a.trans b) = (FStrip.vdashClass h a).trans (FStrip.vdashClass h b) :=
  Prod.ext (funext fun v => FComp.vdashClass_trans (h v) (a.1 v) (b.1 v))
    (funext fun v => FArcComp.vdashClass_trans (a.2 v) (b.2 v))

/-- **Functoriality of `F ↦ F^⊢` on strips**: identities. -/
theorem FStrip.vdashClass_refl (h : ∀ v : Vnon D, ResInputs D v) (P : FStrip D) :
    FStrip.vdashClass h (FStrip.IsoClass.refl P) = FVdashStrip.IsoClass.refl _ :=
  Prod.ext (funext fun v => FComp.vdashClass_refl (h v) (P.non.comp v))
    (funext fun v => FArcComp.vdashClass_refl (P.arc v))

/-! ### Classes of isomorphisms of `F^⊩`-data -/

namespace FRlfData.Iso

variable {P Q R : FRlfData D}

/-- **2-isomorphism of isomorphisms of `F^⊩`-data**: the global equivalences are naturally
isomorphic and the isomorphisms of `F^⊢`-prime-strips are constituentwise 2-isomorphic. -/
def Rel (f g : P.Iso Q) : Prop :=
  Nonempty (f.glob.equiv.functor ≅ g.glob.equiv.functor) ∧
    (∀ w, FrobCat.Iso.Rel (f.strip.1 w).iso (g.strip.1 w).iso) ∧
      ∀ w, FVdashArcData.Iso.Rel (f.strip.2 w) (g.strip.2 w)

/-- The setoid of 2-isomorphism. -/
def setoid (P Q : FRlfData D) : Setoid (P.Iso Q) where
  r := Rel
  iseqv := ⟨fun _ => ⟨⟨CategoryTheory.Iso.refl _⟩, fun _ => FrobCat.Iso.Rel.refl _,
      fun _ => ⟨FrobCat.Iso.Rel.refl _, rfl⟩⟩,
    fun h => ⟨h.1.map CategoryTheory.Iso.symm, fun w => (h.2.1 w).symm,
      fun w => ⟨(h.2.2 w).1.symm, (h.2.2 w).2.symm⟩⟩,
    fun h h' => ⟨h.1.elim fun a => h'.1.elim fun b => ⟨a ≪≫ b⟩,
      fun w => (h.2.1 w).trans (h'.2.1 w),
      fun w => ⟨(h.2.2 w).1.trans (h'.2.2 w).1, (h.2.2 w).2.trans (h'.2.2 w).2⟩⟩⟩

end FRlfData.Iso

/-- **Isomorphisms of `F^⊩`-data in the sense of IUT I, §0.** -/
def FRlfData.IsoClass (P Q : FRlfData D) : Type := Quotient (FRlfData.Iso.setoid P Q)

namespace FRlfData.IsoClass

variable {P Q R : FRlfData D}

/-- The class of an isomorphism. -/
def mk (f : P.Iso Q) : IsoClass P Q := Quotient.mk (FRlfData.Iso.setoid P Q) f

lemma mk_eq_mk {f g : P.Iso Q} : mk f = mk g ↔ FRlfData.Iso.Rel f g :=
  Quotient.eq (r := FRlfData.Iso.setoid P Q)

lemma mk_surjective : Function.Surjective (mk : P.Iso Q → IsoClass P Q) :=
  Quotient.mk_surjective

/-- The identity class. -/
def refl (P : FRlfData D) : IsoClass P P := mk (FRlfData.Iso.refl P)

/-- The composite. -/
def trans : IsoClass P Q → IsoClass Q R → IsoClass P R :=
  Quotient.map₂ (sa := FRlfData.Iso.setoid P Q) (sb := FRlfData.Iso.setoid Q R)
    (sc := FRlfData.Iso.setoid P R) FRlfData.Iso.trans fun _ _ a _ _ b =>
      ⟨a.1.elim fun a1 => b.1.elim fun b1 =>
          ⟨Functor.isoWhiskerRight a1 _ ≪≫ Functor.isoWhiskerLeft _ b1⟩,
        fun w => FrobCat.Iso.Rel.hcomp (a.2.1 w) (b.2.1 w),
        fun w => ⟨FrobCat.Iso.Rel.hcomp (a.2.2 w).1 (b.2.2 w).1, by
          change TMVdash.Iso.trans _ _ = TMVdash.Iso.trans _ _
          rw [(a.2.2 w).2, (b.2.2 w).2]⟩⟩

@[simp] lemma trans_mk (f : P.Iso Q) (g : Q.Iso R) :
    (mk f).trans (mk g) = mk (FRlfData.Iso.trans f g) := rfl

/-- **The `F^⊢`-part of a class**. -/
def toVdash : IsoClass P Q → P.strip.IsoClass Q.strip :=
  Quotient.lift (s := FRlfData.Iso.setoid P Q)
    (fun f => (fun w => SplitFrobCat.IsoClass.mk (f.strip.1 w),
      fun w => FVdashArcData.IsoClass.mk (f.strip.2 w)))
    fun _ _ h => Prod.ext (funext fun w => SplitFrobCat.IsoClass.mk_eq_mk.2 (h.2.1 w))
      (funext fun w => FVdashArcData.IsoClass.mk_eq_mk.2 (h.2.2 w))

/-- Two isomorphisms with naturally isomorphic global equivalences and equal classes of their
`F^⊢`-parts have the same class. -/
lemma mk_eq_of {f g : P.Iso Q} (hglob : Nonempty (f.glob.equiv.functor ≅ g.glob.equiv.functor))
    (hv : (mk f).toVdash = (mk g).toVdash) : mk f = mk g := by
  refine mk_eq_mk.2 ⟨hglob, fun w => ?_, fun w => ?_⟩
  · exact SplitFrobCat.IsoClass.mk_eq_mk.1 (congrFun (congrArg Prod.fst hv) w)
  · exact FVdashArcData.IsoClass.mk_eq_mk.1 (congrFun (congrArg Prod.snd hv) w)

end FRlfData.IsoClass

/-! ### `ρ_v` compatibility -/

/-- **A class of automorphisms of `F^⊢_v` (`v ∈ V^non`) with a representative acting as the
identity on the divisor monoid** (in both directions). -/
def PhiTrivNon {v : Vnon D} (b : SplitFrobCat.IsoClass (fVdashModel D v) (fVdashModel D v)) :
    Prop :=
  ∃ g : (fVdashModel D v).Iso (fVdashModel D v), SplitFrobCat.IsoClass.mk g = b ∧
    (∀ A x, g.iso.phi A x = x) ∧ ∀ B y, g.iso.phiInv B y = y

/-- **A class of automorphisms of `F^⊢_v` (`v ∈ V^arc`) with a representative acting as the
identity on the divisor monoid** (in both directions). -/
def PhiTrivArc (b : FVdashArcData.IsoClass fVdashArcModel fVdashArcModel) : Prop :=
  ∃ g : fVdashArcModel.Iso fVdashArcModel, FVdashArcData.IsoClass.mk g = b ∧
    (∀ A x, g.F.iso.phi A x = x) ∧ ∀ B y, g.F.iso.phiInv B y = y

/-- The restrictions `vdashRes` act trivially on `Φ` (they are classes of `resIso`). -/
theorem phiTrivNon_vdashRes {v : Vnon D} (h : ResInputs D v)
    (a : FrobCat.IsoClass (cvFrob D v) (cvFrob D v)) : PhiTrivNon (vdashRes h a) := by
  obtain ⟨σ, ψ, hψ, hψℓ, σ', hσ', hψ', hτ, -, hb⟩ := vdashRes_isRes h a
  exact ⟨_, hb.symm, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **The automorphisms of `F^⊢_v` (`v ∈ V^arc`) coming from `F_v` act trivially on `Φ`**
(`FArcData.Iso.phi_apply`). -/
theorem phiTrivArc_vdashArcClass (b : FArcData.IsoClass fArcModel fArcModel) :
    PhiTrivArc (vdashArcClass b) := by
  obtain ⟨f, rfl⟩ := FArcData.IsoClass.mk_surjective b
  exact ⟨f.vdashArc, rfl, f.phi_apply, (FArcData.Iso.symm f).phi_apply⟩

variable (D) in
/-- **The automorphism of `F^⊩_mod`** given by automorphisms of the constituents of `F^⊢_mod`
acting as the identity on the divisor monoids and the identity of the global data: it is
compatible with the `ρ_v`. -/
def rlfIsoOf (gn : ∀ w : Vnon D, (fVdashModel D w).Iso (fVdashModel D w))
    (hn : ∀ w A x, (gn w).iso.phi A x = x) (hn' : ∀ w B y, (gn w).iso.phiInv B y = y)
    (ga : ∀ _ : Varc D, fVdashArcModel.Iso fVdashArcModel)
    (ha : ∀ w A x, (ga w).F.iso.phi A x = x) (ha' : ∀ w B y, (ga w).F.iso.phiInv B y = y) :
    (FRlfData.ofThetaData D).Iso (FRlfData.ofThetaData D) where
  glob := FRlfGlobalIso.refl _
  strip := (gn, ga)
  rhoNon w A _ := rlfMap_id_of ((gn w).iso.posMap A) (fun y => Subtype.ext (hn w A y.1)) _
  rhoNonInv w B _ :=
    rlfMap_id_of ((gn w).iso.posInvMap B) (fun y => Subtype.ext (hn' w B y.1)) _
  rhoArc w A _ := Subtype.ext (ha w A _)
  rhoArcInv w B _ := Subtype.ext (ha' w B _)

/-- `F ↦ F^⊢` of a class of `F`-prime-strips acts trivially on `Φ` at `V^non`. -/
theorem phiTrivNon_vdashClass (h : ∀ v : Vnon D, ResInputs D v) {P Q : FStrip D}
    (a : P.IsoClass Q) (w : Vnon D) : PhiTrivNon ((FStrip.vdashClass h a).1 w) :=
  phiTrivNon_vdashRes (h w) _

/-- `F ↦ F^⊢` of a class of `F`-prime-strips acts trivially on `Φ` at `V^arc`. -/
theorem phiTrivArc_vdashClass (h : ∀ v : Vnon D, ResInputs D v) {P Q : FStrip D}
    (a : P.IsoClass Q) (w : Varc D) : PhiTrivArc ((FStrip.vdashClass h a).2 w) :=
  phiTrivArc_vdashArcClass _

/-! ### `F ↦ F^⊩` -/

/-- **`F ↦ F^⊩` on isomorphism classes of `F`-prime-strips** (IUT I, Remark 5.2.1 (ii)): the
class of the automorphism of `F^⊩_mod` which is the identity on the global data and
`FStrip.vdashClass a` on `F^⊢_mod` (through representatives acting trivially on `Φ`, so that the
`ρ_v` are respected). -/
def FStrip.rlfClass (h : ∀ v : Vnon D, ResInputs D v) {P Q : FStrip D} (a : P.IsoClass Q) :
    (FRlfData.ofThetaData D).IsoClass (FRlfData.ofThetaData D) :=
  FRlfData.IsoClass.mk (rlfIsoOf D (fun w => (phiTrivNon_vdashClass h a w).choose)
    (fun w => (phiTrivNon_vdashClass h a w).choose_spec.2.1)
    (fun w => (phiTrivNon_vdashClass h a w).choose_spec.2.2)
    (fun w => (phiTrivArc_vdashClass h a w).choose)
    (fun w => (phiTrivArc_vdashClass h a w).choose_spec.2.1)
    (fun w => (phiTrivArc_vdashClass h a w).choose_spec.2.2))

/-- **The `F^⊢`-part of `F^⊩`** is `F ↦ F^⊢`. -/
theorem FStrip.rlfClass_toVdash (h : ∀ v : Vnon D, ResInputs D v) {P Q : FStrip D}
    (a : P.IsoClass Q) : (FStrip.rlfClass h a).toVdash = FStrip.vdashClass h a :=
  Prod.ext (funext fun w => (phiTrivNon_vdashClass h a w).choose_spec.1)
    (funext fun w => (phiTrivArc_vdashClass h a w).choose_spec.1)

/-- **Functoriality of `F ↦ F^⊩`**: composites. -/
theorem FStrip.rlfClass_trans (h : ∀ v : Vnon D, ResInputs D v) {P Q R : FStrip D}
    (a : P.IsoClass Q) (b : Q.IsoClass R) :
    FStrip.rlfClass h (a.trans b) = (FStrip.rlfClass h a).trans (FStrip.rlfClass h b) := by
  have h1 := FStrip.rlfClass_toVdash h (a.trans b)
  have h2 := FStrip.rlfClass_toVdash h a
  have h3 := FStrip.rlfClass_toVdash h b
  unfold FStrip.rlfClass at h1 h2 h3 ⊢
  rw [FRlfData.IsoClass.trans_mk]
  refine FRlfData.IsoClass.mk_eq_of ⟨CategoryTheory.Iso.refl _⟩ ?_
  exact h1.trans ((FStrip.vdashClass_trans h a b).trans
    (congrArg₂ FVdashStrip.IsoClass.trans h2.symm h3.symm))

/-- **Functoriality of `F ↦ F^⊩`**: identities. -/
theorem FStrip.rlfClass_refl (h : ∀ v : Vnon D, ResInputs D v) (P : FStrip D) :
    FStrip.rlfClass h (FStrip.IsoClass.refl P) = FRlfData.IsoClass.refl _ := by
  have h1 := FStrip.rlfClass_toVdash h (FStrip.IsoClass.refl P)
  unfold FStrip.rlfClass at h1 ⊢
  rw [FRlfData.IsoClass.refl]
  refine FRlfData.IsoClass.mk_eq_of ⟨CategoryTheory.Iso.refl _⟩ ?_
  exact h1.trans (FStrip.vdashClass_refl h P)

end Strips

end PrimeStrip

end Multiradial

end Iut
