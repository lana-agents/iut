/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.ThetaHT
import Iut.Multiradial.PrimeStrip.ModelAutRigid
import Iut.Frobenioid.Tempered

/-!
# The tempered slot of model Frobenioids over `D_v` and IUT I, Corollary 5.3 (iv) (MR18 T10)

IUT I, Example 3.2 (i), (iii) (`Inter-universal Teichmuller Theory I.txt`, l.4483–4566): at
`v ∈ V^bad` the hyperbolic curve `X̲_v` determines a tempered Frobenioid `F_v` over
`D_v = B^temp(Π_v)⁰`, with base-field-theoretic hull `C_v ⊆ F_v` (`C^{bs-fld}` of [EtTh],
Definition 3.6 (iv)). IUT I, Corollary 5.3 (iv) (l.9899–9965): `Aut(F_v) → Aut(D_v)` is
bijective. `ThetaHT.lean` (MR21) uses an abstract slot `TempSlot` for the `†F_v` and the named
input `TempSlot.Cor53iv`.

This file fills the slot with **model Frobenioids over the genuine base `D_v`**:

* `tempFrob T v = modelFrob (T v).Φ₀ (T v).B₀ (T v).div₀`, the tempered Frobenioid ([EtTh],
  Definition 3.6) of tempered Frobenioid data `T v : TemperedFrobenioidData Π_v` on
  `D_v = OrbitObj Π_v` (`Dv D v`). `T` is a parameter here; the data of `X̲_v` on the genuine
  `Π_v` at `v ∈ V^bad` are `PrimeStrip.tempFrobV` (`PrimeStrip/PivTateFrob.lean`, MR18 run 17;
  it still takes the analytic field `𝕂` as a parameter).
* **`tempSlot T`**: constituents at `v` are the Frobenioids isomorphic to `tempFrob T v`, with
  isomorphism classes `FrobCat.IsoClass` (IUT I, §0). The hull of a constituent is represented by
  the model `C_v = cvFrob D v` (MR20; that this model is the hull `C^{bs-fld}` of the tempered
  Frobenioid of `X̲_v` is MR20's debt H4). The **hull of an isomorphism class** `a : †F_v ≅ ‡F_v`
  is the class of `C_v` with the same base equivalence (`tempHullClass`, transported to `D_v`
  through the chosen identifications of `†F_v`, `‡F_v` with `tempFrob T v`): the hull and the
  Frobenioid have the same base (IUT I, Example 3.2 (vi) (d); `Model.hullEquiv_base`), and by
  IUT I, Corollary 5.3 (ii) at `v` (`cvFrob_autRigid`, `cvFrob_autLift`) an isomorphism of `C_v`
  is determined by its base equivalence and every base equivalence occurs
  (`tempHullClass_toD`).
* **`tempSlot_cor53iv`: `TempSlot.Cor53iv (tempSlot T)`**, from
  - the inputs `ResInputs` of `ThetaHT.isoToD_bijective` (they give Corollary 5.3 (ii) at `v`
    and `OrbitIsoRecon Π_v`),
  - `FrobCat.AutRigid (tempFrob T v)`: injectivity, reduced in `ModelAutRigid.lean`
    (`modelFrob_autRigid`) to IUT's two steps (rational functions fixed by the Kummer map,
    `FixesRat`; divisors from principal divisors, `CuspCompat`, `DivGen`), and
  - **`TempAutLift T v`** (named input, debt): every automorphism `σ` of the topological group
    `Π_v` lifts to an automorphism of `tempFrob T v` over `B^temp(σ)` (IUT I, Corollary 5.3 (iv),
    proof: automorphisms of `D_v` arise from automorphisms of the scheme `X̲_v`, [AbsTopIII],
    Theorem 1.9, and `F_v` is constructed functorially from `X̲_v`).
  `tempSlot_cor53iv_of_fixes` states it with the injectivity inputs of `modelFrob_autRigid`.
* **`ThetaHT.isoToD_bijective_tempSlot`: IUT I, Corollary 5.6 (i)** for Θ-Hodge theaters with
  tempered constituents in `tempSlot T`, with these inputs in place of `TempSlot.Cor53iv`.
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory

/-! ### Groupoid laws for `CatIsom` -/

namespace CatIsom

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]
  {F : Type u₃} [Category.{v₃} F] {G : Type u₄} [Category.{v₄} G]

lemma trans_assoc (a : CatIsom C E) (b : CatIsom E F) (c : CatIsom F G) :
    (a.trans b).trans c = a.trans (b.trans c) := by
  obtain ⟨e, rfl⟩ := CatIsom.mk_surjective a
  obtain ⟨e', rfl⟩ := CatIsom.mk_surjective b
  obtain ⟨e'', rfl⟩ := CatIsom.mk_surjective c
  exact CatIsom.mk_eq_mk.2 ⟨Functor.associator _ _ _⟩

lemma refl_trans (a : CatIsom C E) : (CatIsom.refl C).trans a = a := by
  obtain ⟨e, rfl⟩ := CatIsom.mk_surjective a
  exact CatIsom.mk_eq_mk.2 ⟨Functor.leftUnitor _⟩

lemma trans_refl (a : CatIsom C E) : a.trans (CatIsom.refl E) = a := by
  obtain ⟨e, rfl⟩ := CatIsom.mk_surjective a
  exact CatIsom.mk_eq_mk.2 ⟨Functor.rightUnitor _⟩

lemma trans_symm (a : CatIsom C E) : a.trans a.symm = CatIsom.refl C := by
  obtain ⟨e, rfl⟩ := CatIsom.mk_surjective a
  exact CatIsom.mk_eq_mk.2 ⟨e.unitIso.symm⟩

lemma symm_trans (a : CatIsom C E) : a.symm.trans a = CatIsom.refl E := by
  obtain ⟨e, rfl⟩ := CatIsom.mk_surjective a
  exact CatIsom.mk_eq_mk.2 ⟨e.counitIso⟩

/-- Conjugation `c ↦ x⁻¹ c y` is bijective. -/
lemma conj_bijective (x : CatIsom C E) (y : CatIsom F G) :
    Function.Bijective (fun c : CatIsom C F => x.symm.trans (c.trans y)) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun d => x.trans (d.trans y.symm), fun c => ?_,
    fun d => ?_⟩
  · change x.trans ((x.symm.trans (c.trans y)).trans y.symm) = c
    rw [trans_assoc x.symm (c.trans y) y.symm, trans_assoc c y y.symm, trans_symm y,
      trans_refl c, ← trans_assoc x x.symm c, trans_symm x, refl_trans]
  · change x.symm.trans ((x.trans (d.trans y.symm)).trans y) = d
    rw [trans_assoc x (d.trans y.symm) y, trans_assoc d y.symm y, symm_trans y, trans_refl d,
      ← trans_assoc x.symm x d, symm_trans x, refl_trans]

end CatIsom

/-! ### Divisor monoids on prime log-divisors (`P = components ⊕ cusps`) -/

namespace PrimeDivAut

open Iut.Frobenioid Iut.Frobenioid.PrimeDiv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pn Pc : Type} [MulAction G Pn] [MulAction G Pc]
  {Λ : Type} [CommRing Λ] [LinearOrder Λ] [IsStrictOrderedRing Λ] [Archimedean Λ]

/-- The cuspidal part `π_c` as an additive endomorphism of `Φ^gp(A)`. -/
noncomputable def cspHom (A : OrbitObj G) :
    (divMonoid G (Pn ⊕ Pc) Λ).obj A →+ (divMonoid G (Pn ⊕ Pc) Λ).obj A where
  toFun := cspPart
  map_zero' := Subtype.ext (funext fun z => by
    change (if IsCuspidal z then (0 : Λ) else 0) = 0; split_ifs <;> rfl)
  map_add' x y := Subtype.ext (funext fun z => by
    change (if IsCuspidal z then x.1 z + y.1 z else 0) =
      (if IsCuspidal z then x.1 z else 0) + (if IsCuspidal z then y.1 z else 0)
    split_ifs <;> simp)

/-- The non-cuspidal part `π_n` as an additive endomorphism of `Φ^gp(A)`. -/
noncomputable def ncspHom (A : OrbitObj G) :
    (divMonoid G (Pn ⊕ Pc) Λ).obj A →+ (divMonoid G (Pn ⊕ Pc) Λ).obj A where
  toFun := ncspPart
  map_zero' := Subtype.ext (funext fun z => by
    change (if IsCuspidal z then (0 : Λ) else 0) = 0; split_ifs <;> rfl)
  map_add' x y := Subtype.ext (funext fun z => by
    change (if IsCuspidal z then 0 else x.1 z + y.1 z) =
      (if IsCuspidal z then 0 else x.1 z) + (if IsCuspidal z then 0 else y.1 z)
    split_ifs <;> simp)

omit [Archimedean Λ] in
/-- **`Φ^gp` of prime log-divisors is torsion-free** (coefficients in an ordered ring). -/
theorem torsionFree_divMonoid : ModelAut.TorsionFree (divMonoid G (Pn ⊕ Pc) Λ) := by
  intro A n x hn hx
  refine Subtype.ext (funext fun z => ?_)
  have h := congrArg (fun y : (divMonoid G (Pn ⊕ Pc) Λ).obj A => y.1 z) hx
  change n • x.1 z = 0 at h
  rw [nsmul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left (Nat.cast_pos.2 hn).ne'

end PrimeDivAut

end PrimeStrip

end Multiradial

namespace HodgeTheater

open CategoryTheory Iut.Frobenioid Iut.Multiradial.PrimeStrip

variable {D : InitialThetaData.{0}}

/-! ### The tempered model Frobenioids over `D_v` -/

/-- **The tempered Frobenioid of the data `T v` over `D_v = B^temp(Π_v)⁰`** ([EtTh],
Definition 3.6: the model Frobenioid of `(D_v, Φ₀, B₀)`). -/
abbrev tempFrob (T : ∀ v : Vnon D, TemperedFrobenioidData (Piv D v).carrier) (v : Vnon D) :
    FrobCat :=
  modelFrob (T v).Φ₀ (T v).B₀ (T v).div₀

variable (T : ∀ v : Vnon D, TemperedFrobenioidData (Piv D v).carrier)

/-- **Named input (debt, MR18 T10): lifting automorphisms of `Π_v` to `F_v`** (IUT I,
Corollary 5.3 (iv), proof, l.9915–9917: automorphisms of `D_v` arise from automorphisms of the
scheme `X̲_v`, [AbsTopIII], Theorem 1.9, and `F_v` is constructed from `X̲_v`): every
automorphism `σ` of the topological group `Π_v` is the base of an automorphism of
`tempFrob T v` over `B^temp(σ)`. -/
def TempAutLift (v : Vnon D) : Prop :=
  ∀ σ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier,
    ∃ h : (tempFrob T v).Iso (tempFrob T v), Nonempty (h.D.functor ≅ OrbitObj.isoFunctor σ)

variable {T} in
/-- **Automorphisms of `D_v` lift to `tempFrob T v`**, from `OrbitIsoRecon Π_v` ([SemiAnbd],
Proposition 3.2) and `TempAutLift`. -/
theorem tempFrob_autLift {v : Vnon D} (hrec : OrbitIsoRecon (Piv D v).carrier)
    (hT : TempAutLift T v) : (tempFrob T v).AutLift := by
  intro e
  obtain ⟨σ, ⟨β⟩⟩ := hrec e
  obtain ⟨h, ⟨γ⟩⟩ := hT σ
  exact ⟨h, ⟨γ ≪≫ β.symm⟩⟩

/-- A constituent of the tempered slot: a Frobenioid isomorphic to `tempFrob T v`. -/
abbrev TempComp (v : Vnon D) : Type 1 := {X : FrobCat // Nonempty (X.Iso (tempFrob T v))}

variable {T}

/-- The chosen identification of a constituent with `tempFrob T v`. -/
def TempComp.iso {v : Vnon D} (X : TempComp T v) : X.1.Iso (tempFrob T v) :=
  Classical.choice X.2

/-- **The base equivalence of `a` transported to `D_v`** through the chosen identifications. -/
def tempBaseConj {v : Vnon D} {X Y : TempComp T v} (a : FrobCat.IsoClass X.1 Y.1) :
    CatIsom (cvFrob D v).D (cvFrob D v).D :=
  (CatIsom.mk X.iso.D).symm.trans (a.toD.trans (CatIsom.mk Y.iso.D))

/-- **The hull of an isomorphism class of tempered Frobenioids** (IUT I, Example 3.2 (iii),
(vi) (d)): the class of `C_v` with the same base equivalence (see the module docstring;
`tempHullClass_toD`). -/
def tempHullClass {v : Vnon D} {X Y : TempComp T v} (a : FrobCat.IsoClass X.1 Y.1) :
    FrobCat.IsoClass (cvFrob D v) (cvFrob D v) :=
  @Classical.epsilon _ ⟨FrobCat.IsoClass.refl _⟩ fun c => c.toD = tempBaseConj a

/-- The hull class induces the transported base equivalence, given that every self-equivalence
of `D_v` lifts to `C_v` (IUT I, Corollary 5.3 (ii), surjectivity at `v`). -/
theorem tempHullClass_toD {v : Vnon D} (hl : (cvFrob D v).AutLift) {X Y : TempComp T v}
    (a : FrobCat.IsoClass X.1 Y.1) : (tempHullClass a).toD = tempBaseConj a :=
  @Classical.epsilon_spec _ (fun c : FrobCat.IsoClass (cvFrob D v) (cvFrob D v) =>
    c.toD = tempBaseConj a) (FrobCat.IsoClass.toD_surjective hl (FrobCat.Iso.refl _) _)

variable (T) in
/-- **The tempered slot of model Frobenioids over `D_v`** (IUT I, Example 3.2 (i), (iii)):
constituents isomorphic to `tempFrob T v`, isomorphism classes of Frobenioids, hull `C_v`
(`cvFrob D v`) and `tempHullClass` on classes. -/
def tempSlot : TempSlot D where
  Comp v := TempComp T v
  IsoClass X Y := FrobCat.IsoClass X.1 Y.1
  hull {v} _ := ⟨cvFrob D v, ⟨FrobCat.Iso.refl _⟩⟩
  hullClass a := tempHullClass a

/-- **IUT I, Corollary 5.3 (iv)** for the tempered slot (`TempSlot.Cor53iv (tempSlot T)`):
from the inputs `ResInputs` at `V^bad` (Corollary 5.3 (ii) at `v`, `OrbitIsoRecon Π_v`), the
rigidity of `tempFrob T v` (injectivity) and `TempAutLift T v` (surjectivity). -/
theorem tempSlot_cor53iv (h : ∀ v : Vnon D, v ∈ D.VBad → ResInputs D v)
    (hrig : ∀ v : Vnon D, v ∈ D.VBad → (tempFrob T v).AutRigid)
    (hlift : ∀ v : Vnon D, v ∈ D.VBad → TempAutLift T v) : (tempSlot T).Cor53iv := by
  intro v hv X Y
  have hrec : OrbitIsoRecon (Piv D v).carrier := orbitIsoRecon_piv D v (h v hv).2.2.1
  have hcv : (cvFrob D v).AutLift :=
    cvFrob_autLift D v hrec (kummerLift D v (h v hv).1 (h v hv).2.1)
  have htoD : Function.Bijective
      (FrobCat.IsoClass.toD : FrobCat.IsoClass X.1 Y.1 → CatIsom X.1.D Y.1.D) :=
    ⟨FrobCat.IsoClass.toD_injective (FrobCat.autRigid_of_iso X.iso (hrig v hv)),
      FrobCat.IsoClass.toD_surjective
        (FrobCat.autLift_of_iso X.iso (tempFrob_autLift hrec (hlift v hv)))
        (X.iso.trans Y.iso.symm)⟩
  have e : (fun a : (tempSlot T).IsoClass X Y => ((tempSlot T).hullClass a).toD) =
      (fun c : CatIsom X.1.D Y.1.D => (CatIsom.mk X.iso.D).symm.trans
        (c.trans (CatIsom.mk Y.iso.D))) ∘ FrobCat.IsoClass.toD := by
    funext a
    exact tempHullClass_toD hcv a
  rw [e]
  exact (CatIsom.conj_bijective _ _).comp htoD

open ModelAut in
/-- **IUT I, Corollary 5.3 (iv)** for the tempered slot with the injectivity reduced to IUT's two
steps (`modelFrob_autRigid`): rational functions fixed by every automorphism over the identity
(`FixesRat`, the Kummer step), cuspidal compatibility (`CuspCompat`), generation of divisors by
parts of principal divisors (`DivGen`) and torsion-freeness of `Φ^gp`. -/
theorem tempSlot_cor53iv_of_fixes (h : ∀ v : Vnon D, v ∈ D.VBad → ResInputs D v)
    (πc πn : ∀ v : Vnon D, ∀ A, (T v).Φ₀.obj A →+ (T v).Φ₀.obj A)
    (hrat : ∀ v : Vnon D, v ∈ D.VBad → ∀ (h : (tempFrob T v).Iso (tempFrob T v))
      (β : h.D.functor ≅ 𝟭 (tempFrob T v).D), FixesRat h β)
    (hcc : ∀ v : Vnon D, v ∈ D.VBad → CuspCompat (T v).Φ₀ (T v).div₀ (πc v) (πn v))
    (hgen : ∀ v : Vnon D, v ∈ D.VBad → DivGen (T v).div₀ (πc v) (πn v))
    (htf : ∀ v : Vnon D, v ∈ D.VBad → TorsionFree (T v).Φ₀)
    (hlift : ∀ v : Vnon D, v ∈ D.VBad → TempAutLift T v) : (tempSlot T).Cor53iv :=
  tempSlot_cor53iv h
    (fun v hv => modelFrob_autRigid (hrat v hv) (hcc v hv) (hgen v hv) (htf v hv)) hlift

/-- **IUT I, Corollary 5.6 (i)** for Θ-Hodge theaters whose tempered constituents are in
`tempSlot T`, with the inputs of `tempSlot_cor53iv` in place of `TempSlot.Cor53iv`. -/
theorem ThetaHT.isoToD_bijective_tempSlot (h : ∀ v : Vnon D, ResInputs D v)
    (hrig : ∀ v : Vnon D, v ∈ D.VBad → (tempFrob T v).AutRigid)
    (hlift : ∀ v : Vnon D, v ∈ D.VBad → TempAutLift T v) (A B : ThetaHT D (tempSlot T)) :
    Function.Bijective (ThetaHT.Iso.toD : ThetaHT.Iso h A B → A.toD.IsoClass B.toD) :=
  ThetaHT.isoToD_bijective h (tempSlot_cor53iv (fun v _ => h v) hrig hlift) A B

end HodgeTheater

end Iut
