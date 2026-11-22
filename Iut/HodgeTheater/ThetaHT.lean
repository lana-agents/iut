/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.ArcRigid

/-!
# Θ-Hodge theaters (IUT I, Definition 3.6) and IUT I, Corollary 5.6 (i) (MR21, session 8)

IUT I, Definition 3.6 (`Inter-universal Teichmuller Theory I.txt`, l.5790–5871): a
**Θ-Hodge theater** is a collection `†HT^Θ = ({†F_v}_{v ∈ V}, †F^⊩_mod)` with (a) at
`v ∈ V^non` a category `†F_v` equivalent to `F_v` (the tempered Frobenioid of Example 3.2 (i) at
`v ∈ V^bad`, the `p_v`-adic Frobenioid of Example 3.3 (i) at `v ∈ V^good`), (b) at `v ∈ V^arc`
data `(†C_v, †D_v, †κ_v)` isomorphic to `F_v` of Example 3.4 (i), and (c) `†F^⊩_mod =
(†C^⊩_mod, Prime(†C^⊩_mod) ≅ V, {†F^⊢_v}_{v ∈ V}, {†ρ_v}_{v ∈ V})`, where `†F^⊢_v` is the
`F^⊢_v` constructed from `†F_v` and the collection is isomorphic to `F^⊩_mod`. Isomorphisms are
the evident ones (Remark 3.6.2), with isomorphisms of categories understood as isomorphism
classes of equivalences (§0, Example 3.5 conventions (i), (ii), l.5780–5789).

The **`F`-prime-strip `†F_>` tautologically associated** to `†HT^Θ` (discussion preceding
Example 5.4, l.10043–10057) has constituents `†F_v` at `v ∈ V^good` and the base-field-theoretic
hull `†C_v ⊆ †F_v` (Example 3.2 (iii)) at `v ∈ V^bad`. **Corollary 5.6 (i)** (l.10594–10603):
`Isom(†HT^Θ, ‡HT^Θ) → Isom(†D_>, ‡D_>)` is bijective; proof (l.10613–10631): the only data of
`†HT^Θ` not contained in `†F_>` are the global data, obtained from `†F_>` by `F ↦ F^⊩` (Remark
5.2.1 (ii)), and the tempered Frobenioids at `V^bad`; apply Corollary 5.3 (ii) to `†F_>` and
Corollary 5.3 (iv) at `V^bad`.

## Formalisation

* **The tempered Frobenioids at `V^bad` are an abstract slot** (`TempSlot`): iut has no
  tempered Frobenioid `F_v` yet (MR18 T10). A slot provides, for `v ∈ V^non`, a type of
  constituents `†F_v` with isomorphism classes `IsoClass`, the base-field-theoretic hull
  `hull : †F_v ↦ †C_v` (a constituent of an `F`-prime-strip, Example 3.2 (iii)) and its action
  `hullClass` on isomorphism classes. **IUT I, Corollary 5.3 (iv)** (l.9899–9965:
  `Aut(F_v) → Aut(D_v)` bijective, `D_v` the common base of `F_v` and `C_v`) is the named
  theorem argument `TempSlot.Cor53iv` of `ThetaHT.isoToD_bijective` (debt, owner MR18 T10).
* `ThetaHT D T`: the `F`-prime-strip `†F_>` (`F`; its constituents at `V^good` and `V^arc` are
  the `†F_v`), the tempered constituents `temp v` at `v ∈ V^bad`, the identification `hullCls`
  of the hull of `temp v` with the constituent of `†F_>` at `v`, the `F^⊩`-prime-strip `rlf`
  and the identification `link` of `F^⊩(†F_>)` (in iut the model `F^⊩_mod`, `RlfClass.lean`)
  with `rlf` (Definition 3.6 (c): the `†F^⊢_v` of `†F^⊩_mod` are those constructed from the
  `†F_v`).
* `ThetaHT.Iso h A B`: classes of isomorphisms of all constituents (`F`, `temp`, `rlf`),
  compatible with the hulls (`temp_compat`) and with `F ↦ F^⊩` (`rlf_compat`). `F ↦ F^⊩` on
  isomorphisms (`FStrip.rlfClass`) uses the inputs `ResInputs` at `V^non` (`h`), so the notion of
  isomorphism is relative to them.
* **IUT I, Corollary 5.6 (i)** (`ThetaHT.isoToD_bijective`): with the inputs `h` (which contain
  those of Corollary 5.3 (ii)) and the named Corollary 5.3 (iv) (`TempSlot.Cor53iv`).
* Auxiliary: the global part of an isomorphism of `F^⊩`-data is unique up to natural
  isomorphism (`FRlfGlobal.Iso.nonempty_functor_iso`), and the classes of isomorphisms of
  `F^⊩`-data form a groupoid (`FRlfData.IsoClass.symm`, `trans_assoc`, `trans_symm`, …).
-/

noncomputable section

namespace Iut

namespace HodgeTheater

open CategoryTheory

/-- **The global part of an isomorphism of `F^⊩`-data is unique up to natural isomorphism**:
both functors are identified with `equiv₁ ⋙ equiv₂⁻¹`. -/
theorem FRlfGlobal.Iso.nonempty_functor_iso {D : InitialThetaData.{0}} {A B : FRlfGlobal D}
    (f g : A.Iso B) : Nonempty (f.equiv.functor ≅ g.equiv.functor) := by
  let φ : ∀ e : A.Iso B, e.equiv.functor ≅ A.equiv.functor ⋙ B.equiv.inverse := fun e =>
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ B.equiv.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.comm _
  exact ⟨φ f ≪≫ (φ g).symm⟩

end HodgeTheater

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

variable {D : InitialThetaData.{0}}

/-! ### Classes of isomorphisms of `F^⊩`-data form a groupoid -/

namespace FRlfData.Iso

variable {P Q : FRlfData D}

/-- Two isomorphisms of `F^⊩`-data are 2-isomorphic as soon as their `F^⊢`-parts are (the global
parts always are). -/
lemma rel_of {f g : P.Iso Q} (hn : ∀ w, FrobCat.Iso.Rel (f.strip.1 w).iso (g.strip.1 w).iso)
    (ha : ∀ w, FrobCat.Iso.Rel (f.strip.2 w).F.iso (g.strip.2 w).F.iso)
    (ht : ∀ w x, (f.strip.2 w).T.e x = (g.strip.2 w).T.e x) : Rel f g :=
  ⟨HodgeTheater.FRlfGlobal.Iso.nonempty_functor_iso f.glob g.glob, hn,
    fun w => ⟨ha w, TMVdash.Iso.ext' (ht w)⟩⟩

end FRlfData.Iso

namespace FRlfData.IsoClass

variable {P Q R S : FRlfData D}

/-- The inverse. -/
def symm : IsoClass P Q → IsoClass Q P :=
  Quotient.map (sa := FRlfData.Iso.setoid P Q) (sb := FRlfData.Iso.setoid Q P)
    FRlfData.Iso.symm fun _ _ h => FRlfData.Iso.rel_of
      (fun w => FrobCat.Iso.Rel.symm_iso (h.2.1 w))
      (fun w => FrobCat.Iso.Rel.symm_iso (h.2.2 w).1)
      (fun w x => congrArg (fun T => (TMVdash.Iso.symm T).e x) (h.2.2 w).2)

@[simp] lemma symm_mk (f : P.Iso Q) : (mk f).symm = mk (FRlfData.Iso.symm f) := rfl

lemma trans_assoc (a : IsoClass P Q) (b : IsoClass Q R) (c : IsoClass R S) :
    (a.trans b).trans c = a.trans (b.trans c) := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  obtain ⟨g, rfl⟩ := mk_surjective b
  obtain ⟨k, rfl⟩ := mk_surjective c
  exact mk_eq_mk.2 (FRlfData.Iso.rel_of (fun _ => FrobCat.Iso.Rel.assoc _ _ _)
    (fun _ => FrobCat.Iso.Rel.assoc _ _ _) fun _ _ => rfl)

lemma refl_trans (a : IsoClass P Q) : (refl P).trans a = a := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 (FRlfData.Iso.rel_of (fun _ => FrobCat.Iso.Rel.reflTrans _)
    (fun _ => FrobCat.Iso.Rel.reflTrans _) fun _ _ => rfl)

lemma trans_refl (a : IsoClass P Q) : a.trans (refl Q) = a := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 (FRlfData.Iso.rel_of (fun _ => FrobCat.Iso.Rel.transRefl _)
    (fun _ => FrobCat.Iso.Rel.transRefl _) fun _ _ => rfl)

lemma trans_symm (a : IsoClass P Q) : a.trans a.symm = refl P := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 (FRlfData.Iso.rel_of (fun _ => FrobCat.Iso.Rel.transSymm _)
    (fun _ => FrobCat.Iso.Rel.transSymm _) fun _ x => (f.strip.2 _).T.e.symm_apply_apply x)

lemma symm_trans (a : IsoClass P Q) : a.symm.trans a = refl Q := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 (FRlfData.Iso.rel_of (fun _ => FrobCat.Iso.Rel.symmTrans _)
    (fun _ => FrobCat.Iso.Rel.symmTrans _) fun _ x => (f.strip.2 _).T.e.apply_symm_apply x)

lemma cancel_left (a : IsoClass P Q) {b c : IsoClass Q R} (h : a.trans b = a.trans c) :
    b = c := by
  rw [← refl_trans b, ← refl_trans c, ← symm_trans a, trans_assoc, trans_assoc, h]

end FRlfData.IsoClass

namespace FrobCat.IsoClass

variable {X Y Z : FrobCat}

lemma cancel_right {a b : IsoClass X Y} (c : IsoClass Y Z) (h : a.trans c = b.trans c) :
    a = b := by
  rw [← trans_refl a, ← trans_refl b, ← trans_symm c, ← trans_assoc, ← trans_assoc, h]

end FrobCat.IsoClass

end PrimeStrip

end Multiradial

namespace HodgeTheater

open CategoryTheory Iut.Frobenioid Iut.Multiradial.PrimeStrip

variable (D : InitialThetaData.{0})

/-! ### The tempered Frobenioids at `V^bad`: an abstract slot -/

/-- **The tempered Frobenioids `†F_v` at `v ∈ V^bad` (IUT I, Example 3.2 (i); Definition 3.6
(a)) as an abstract slot** (iut has no tempered Frobenioid yet, MR18 T10): constituents, their
isomorphism classes (IUT I, §0), the base-field-theoretic hull `†C_v ⊆ †F_v` (Example 3.2
(iii)), a constituent of an `F`-prime-strip, and its action on isomorphism classes. -/
structure TempSlot : Type 2 where
  /-- The constituents `†F_v` (categories equivalent to `F_v`, with their structure). -/
  Comp : Vnon D → Type 1
  /-- Isomorphisms of constituents (classes of equivalences). -/
  IsoClass : ∀ {v : Vnon D}, Comp v → Comp v → Type
  /-- The base-field-theoretic hull `†C_v ⊆ †F_v`. -/
  hull : ∀ {v : Vnon D}, Comp v → FComp D v
  /-- The hull of an isomorphism. -/
  hullClass : ∀ {v : Vnon D} {X Y : Comp v}, IsoClass X Y →
    FrobCat.IsoClass (hull X).F (hull Y).F

variable {D}

/-- **IUT I, Corollary 5.3 (iv)** for a slot (named input, debt; owner MR18 T10): at
`v ∈ V^bad`, `Isom(†F_v, ‡F_v) → Isom(†D_v, ‡D_v)` is bijective, `D_v` the base category of
`F_v` (equal to that of its hull `C_v`). -/
def TempSlot.Cor53iv (T : TempSlot D) : Prop :=
  ∀ v : Vnon D, v ∈ D.VBad → ∀ X Y : T.Comp v,
    Function.Bijective (fun a : T.IsoClass X Y => (T.hullClass a).toD)

/-! ### Θ-Hodge theaters -/

variable (D) in
/-- **A Θ-Hodge theater** (IUT I, Definition 3.6), relative to a slot `T` for the tempered
Frobenioids at `V^bad`: the `F`-prime-strip `†F_>` (whose constituents at `V^good`, `V^arc` are
the `†F_v`), the tempered constituents `†F_v` at `v ∈ V^bad` with the identification of their
hulls with the constituents of `†F_>`, the `F^⊩`-prime-strip `†F^⊩_mod` and its identification
with `F^⊩(†F_>)`. -/
structure ThetaHT (T : TempSlot D) : Type 1 where
  /-- The `F`-prime-strip `†F_>`. -/
  F : FStrip D
  /-- The tempered Frobenioids `†F_v`, `v ∈ V^bad`. -/
  temp : ∀ v : Vnon D, v ∈ D.VBad → T.Comp v
  /-- The constituent of `†F_>` at `v ∈ V^bad` is the hull of `†F_v`. -/
  hullCls : ∀ v (hv : v ∈ D.VBad), FrobCat.IsoClass (T.hull (temp v hv)).F (F.non.comp v).F
  /-- `†F^⊩_mod`. -/
  rlf : FRlfStrip D
  /-- `†F^⊩_mod` is `F^⊩(†F_>)` (Definition 3.6 (c)). -/
  link : FRlfData.IsoClass (FRlfData.ofThetaData D) rlf.X

variable {T : TempSlot D}

/-- **The `D`-prime-strip `†D_>` associated to a Θ-Hodge theater.** -/
def ThetaHT.toD (A : ThetaHT D T) : DStrip D := A.F.toD

/-- **An isomorphism of Θ-Hodge theaters** (IUT I, Remark 3.6.2; classes in the sense of §0):
isomorphisms of `†F_>`, of the tempered Frobenioids and of `†F^⊩_mod`, compatible with the
hulls and with `F ↦ F^⊩` (relative to the inputs `h` of `FStrip.rlfClass`). -/
@[ext]
structure ThetaHT.Iso (h : ∀ v : Vnon D, ResInputs D v) (A B : ThetaHT D T) where
  /-- The isomorphism of `F`-prime-strips. -/
  F : A.F.IsoClass B.F
  /-- The isomorphisms of tempered Frobenioids. -/
  temp : ∀ v (hv : v ∈ D.VBad), T.IsoClass (A.temp v hv) (B.temp v hv)
  /-- The isomorphism of `F^⊩`-prime-strips. -/
  rlf : FRlfData.IsoClass A.rlf.X B.rlf.X
  /-- Compatibility with the hulls. -/
  temp_compat : ∀ v (hv : v ∈ D.VBad),
    (A.hullCls v hv).trans (F.1 v) = (T.hullClass (temp v hv)).trans (B.hullCls v hv)
  /-- Compatibility with `F ↦ F^⊩`. -/
  rlf_compat : A.link.trans rlf = (FStrip.rlfClass h F).trans B.link

/-- **The map `Isom(†HT^Θ, ‡HT^Θ) → Isom(†D_>, ‡D_>)`** (IUT I, Corollary 5.6 (i)). -/
def ThetaHT.Iso.toD {h : ∀ v : Vnon D, ResInputs D v} {A B : ThetaHT D T}
    (x : ThetaHT.Iso h A B) : A.toD.IsoClass B.toD :=
  FStrip.isoClassToD x.F

/-- **IUT I, Corollary 5.6 (i)** (l.10594–10603, proof l.10613–10631): the map from
isomorphisms of Θ-Hodge theaters to isomorphisms of the associated `D`-prime-strips is bijective.
Inputs: `ResInputs` at `V^non` (`h`; containing those of Corollary 5.3 (ii)) and Corollary
5.3 (iv) for the tempered Frobenioids (`hT`, named input). -/
theorem ThetaHT.isoToD_bijective (h : ∀ v : Vnon D, ResInputs D v) (hT : T.Cor53iv)
    (A B : ThetaHT D T) :
    Function.Bijective (ThetaHT.Iso.toD : ThetaHT.Iso h A B → A.toD.IsoClass B.toD) := by
  have hF := FStrip.isoClassToD_bijective (fun v => (h v).1) (fun v => (h v).2.1)
    (fun v hv => (h v).2.2.1 hv) A.F B.F
  -- injectivity of `F ↦ D` at the hulls (Corollary 5.3 (ii) at `v`)
  have hinj : ∀ v (X Y : FComp D v), Function.Injective
      (FrobCat.IsoClass.toD : FrobCat.IsoClass X.F Y.F → CatIsom X.F.D Y.F.D) := fun v X Y =>
    FrobCat.IsoClass.toD_injective (FrobCat.autRigid_of_iso (Classical.choice X.equiv_model)
      (cvFrob_autRigid D v (h v).2.1.1))
  constructor
  · intro x y hxy
    have eF : x.F = y.F := hF.1 hxy
    have eT : ∀ v hv, x.temp v hv = y.temp v hv := by
      intro v hv
      have e1 := x.temp_compat v hv
      have e2 := y.temp_compat v hv
      rw [eF, e2] at e1
      have e3 := FrobCat.IsoClass.cancel_right _ e1
      exact (hT v hv _ _).1 (congrArg FrobCat.IsoClass.toD e3.symm)
    have eR : x.rlf = y.rlf := by
      apply FRlfData.IsoClass.cancel_left A.link
      rw [x.rlf_compat, y.rlf_compat, eF]
    exact ThetaHT.Iso.ext eF (funext fun v => funext fun hv => eT v hv) eR
  · intro d
    obtain ⟨f, hf⟩ := hF.2 d
    let c : ∀ v (hv : v ∈ D.VBad), FrobCat.IsoClass (T.hull (A.temp v hv)).F
        (T.hull (B.temp v hv)).F := fun v hv =>
      ((A.hullCls v hv).trans (f.1 v)).trans (B.hullCls v hv).symm
    choose t ht using fun v hv => (hT v hv (A.temp v hv) (B.temp v hv)).2 (c v hv).toD
    refine ⟨⟨f, t, A.link.symm.trans ((FStrip.rlfClass h f).trans B.link), fun v hv => ?_, ?_⟩,
      hf⟩
    · have e : T.hullClass (t v hv) = c v hv := hinj v _ _ (ht v hv)
      rw [e, FrobCat.IsoClass.trans_assoc, FrobCat.IsoClass.symm_trans,
        FrobCat.IsoClass.trans_refl]
    · rw [← FRlfData.IsoClass.trans_assoc, FRlfData.IsoClass.trans_symm,
        FRlfData.IsoClass.refl_trans]

end HodgeTheater

end Iut
