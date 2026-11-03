/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Strip
import Iut.Frobenioid.Tempered.BaseRecon
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Mono-analyticisation `†D ↦ †D^⊢` of abstract `D`-prime-strips (MR20, Remark 5.2.1 (ii))

IUT I, Examples 3.2 (i), (vi)(a), 3.3 (i), (iii)(a) (l.4483–4838, 5009–5189), Definition 4.1 (iv)
(l.6421–6450) and Remark 5.2.1 (l.9821–9850) of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`: `D^⊢_v = B(K_v)⁰` is a full
subcategory of `D_v = B^{(temp)}(Π_v)⁰` (pull-back of coverings along `X̲_v → Spec K_v`), which
"may be reconstructed category-theoretically from `D_v` [cf. [AbsAnab], Lemma 1.3.8]"; by
Remark 3.2.1 (i) (l.4824), "reconstructed category-theoretically" means "preserved by equivalences
of categories". This gives the mono-analyticisation `†D ↦ †D^⊢` of `D`-prime-strips.

## Formalisation

* `transportProp P X`: a property `P` of the objects of a model category `M`, transported to a
  category `X` admitting an equivalence with `M` (`A` has it iff some equivalence `X ≌ M` maps
  `A` into `P`). It is defined without choices, so an equivalence `X ≌ Y` restricts to the full
  subcategories (`transportEquiv`); if `P` is preserved by the self-equivalences of `M`
  (`AutoInvariant`, "reconstructed category-theoretically"), the full subcategory of `X` is
  equivalent to that of `M` (`transportModelEquiv`).
* `subProp N` on `B(Γ)⁰ = OrbitObj Γ`: the objects `Γ/H` with `N ⊆ H`; for normal `N` it is
  closed under all morphisms (`le_H_of_hom`). If every self-equivalence of `B(Γ)⁰` is induced on
  open normal subgroups by an automorphism of `Γ` (`OrbitRecon`: [Mzk2], Proposition 3.2 for
  profinite `Γ`, `OrbitObj.exists_continuousMulEquiv`; [SemiAnbd], Proposition 3.2 for tempered
  `Γ`, `OrbitObj.exists_continuousMulEquiv_temp`) and `N` is characteristic, then `subProp N` is
  `AutoInvariant` (`subProp_autoInvariant`).
* `pullFunctor p : B(G)⁰ ⥤ B(Γ)⁰`, `G/H ↦ Γ/p⁻¹(H)`, for a continuous surjection `p : Γ → G`; it
  is fully faithful with essential image `subProp (ker p)` when `p` maps open subgroups to open
  subgroups (`pullEquiv`). For `p = Π_v → G_v` (given debt H3, `PiToGQuotient`) this is
  **`D^⊢_v ⊆ D_v`** (`vdashModelEquiv`).
* **Named inputs.** `DeltaCharacteristic D v`: every automorphism of the topological group `Π_v`
  maps `Δ_v = ker(Π_v → G_v)` onto itself — [AbsAnab], Lemma 1.3.8 (`Absolute Anabelian
  Geometry.txt` l.977–985), the debt `ArithQuotientPreservedPadic` of MR13 (curves-jacobian
  `CuspChar/RigidityPadic.lean`), here for iut's `Π_v` (the cj statement is about `π₁ᵉᵗ` of
  `HypCurve`s, which are not identified with iut's `Orbicurve.genuinePi1` / tempered `Π_v`); at
  `v ∈ V^bad` in addition `TempRecon D v` (`Π_v` Hausdorff with a basis of open normal subgroups,
  complete for them, and with a countable cofinal chain — the hypotheses of [SemiAnbd],
  Proposition 3.2 in `BaseRecon.lean`; the first three are proved for tfg's `temperedPi1` in
  `PiTpONS.lean`, the chain is MR18's debt `hctbl`).
* **The mono-analyticisation** `DComp.toVdash`, `DStripNon.toVdash` (Definition 4.1 (iv)): the
  constituent `†D^⊢_v ⊆ †D_v` is the full subcategory `transportProp (D^⊢_v ⊆ D_v)`; on
  isomorphisms `DStripNon.isoToVdash` (no input needed); that it is a `D^⊢`-prime-strip uses the
  named inputs and H3. `FStripNon.toDVdash`: `F ↦ D ↦ D^⊢`.

**Not done here** (see `MR20-plan.md`): `F ↦ F^⊢` on abstract strips (needs the sub-Frobenioid
`Φ_{C^⊢_v} = ord(ℤ_p^▷) ⊆ Φ_{C_v}|_{D^⊢_v}` and the splitting `τ^⊢_v` reconstructed from `F_v`,
IUT I, Example 3.3 (iii)(d), (e): [AbsAnab] Proposition 1.2.1 (v), [AbsTopIII] Proposition 3.2 (iii)
— MR21 scope), hence `F ↦ F^⊩`; the archimedean `D_v ↦ D^⊢_v` (object of `TM^⊢` of `A_{D_v}`).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory Iut.Frobenioid

/-! ### Transport of a property of objects along equivalences -/

section Transport

variable {M : Type} [Category.{0} M] (P : ObjectProperty M)

/-- **The property `P` of objects of `M`, transported to a category `X`**: `A` has it iff some
equivalence `X ≌ M` maps `A` into `P`. -/
def transportProp (X : Type) [Category.{0} X] : ObjectProperty X :=
  fun A => ∃ e : X ≌ M, P (e.functor.obj A)

/-- **`P` is preserved by the self-equivalences of `M`** ("reconstructed category-theoretically",
IUT I, Remark 3.2.1 (i)). -/
def AutoInvariant : Prop := ∀ (σ : M ≌ M) (A : M), P A → P (σ.functor.obj A)

variable {P}

instance transportProp_isClosed [P.IsClosedUnderIsomorphisms] (X : Type) [Category.{0} X] :
    (transportProp P X).IsClosedUnderIsomorphisms where
  of_iso i := fun ⟨e, h⟩ => ⟨e, P.prop_of_iso (e.functor.mapIso i) h⟩

lemma transportProp_inverseImage [P.IsClosedUnderIsomorphisms] {X Y : Type} [Category.{0} X]
    [Category.{0} Y] (f : X ≌ Y) :
    (transportProp P Y).inverseImage f.functor = transportProp P X := by
  ext A
  refine ⟨fun ⟨e, h⟩ => ⟨f.trans e, h⟩, fun ⟨e, h⟩ => ⟨f.symm.trans e, ?_⟩⟩
  exact P.prop_of_iso (e.functor.mapIso (f.unitIso.app A)) h

lemma transportProp_iff [P.IsClosedUnderIsomorphisms] (hP : AutoInvariant P) {X : Type}
    [Category.{0} X] (e : X ≌ M) (A : X) : transportProp P X A ↔ P (e.functor.obj A) := by
  refine ⟨fun ⟨e', h⟩ => ?_, fun h => ⟨e, h⟩⟩
  have := hP (e'.symm.trans e) _ h
  exact P.prop_of_iso (e.functor.mapIso (e'.unitIso.app A).symm) this

/-- **An equivalence `X ≌ Y` restricts to the transported full subcategories.** -/
def transportEquiv [P.IsClosedUnderIsomorphisms] {X Y : Type} [Category.{0} X] [Category.{0} Y]
    (f : X ≌ Y) : (transportProp P X).FullSubcategory ≌ (transportProp P Y).FullSubcategory :=
  f.congrFullSubcategory (transportProp_inverseImage f)

/-- **The transported full subcategory is equivalent to that of the model** if `P` is preserved
by the self-equivalences of `M`. -/
def transportModelEquiv [P.IsClosedUnderIsomorphisms] (hP : AutoInvariant P) {X : Type}
    [Category.{0} X] (e : X ≌ M) : (transportProp P X).FullSubcategory ≌ P.FullSubcategory :=
  e.congrFullSubcategory (by ext A; exact (transportProp_iff hP e A).symm)

end Transport

/-! ### Objects `Γ/H` with `N ⊆ H` -/

section Orbit

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

/-- **The objects `Γ/H` of `B(Γ)⁰` with `N ⊆ H`** (for `N = ker(Γ ↠ G)`: the objects pulled back
from `B(G)⁰`). -/
def subProp (N : Subgroup Γ) : ObjectProperty (OrbitObj Γ) := fun A => N ≤ A.H

/-- **For normal `N`, `N ⊆ H` is inherited along every morphism `Γ/H → Γ/H'`.** -/
lemma le_H_of_hom {N : Subgroup Γ} [hN : N.Normal] {A B : OrbitObj Γ} (f : A ⟶ B)
    (h : N ≤ A.H) : N ≤ B.H := by
  intro δ hδ
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective (f.toFun (QuotientGroup.mk 1))
  have hδ' : g₀ * δ * g₀⁻¹ ∈ A.H := h (hN.conj_mem δ hδ g₀)
  have h1 : (g₀ * δ * g₀⁻¹) • (QuotientGroup.mk 1 : Γ ⧸ A.H) = QuotientGroup.mk 1 := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
    simpa using A.H.inv_mem hδ'
  have h2 := f.map_smul (g₀ * δ * g₀⁻¹) (QuotientGroup.mk 1)
  rw [h1, ← hg₀, MulAction.Quotient.smul_mk, smul_eq_mul] at h2
  have h3 := QuotientGroup.eq.mp h2
  rwa [show g₀⁻¹ * (g₀ * δ * g₀⁻¹ * g₀) = δ by group] at h3

instance subProp_isClosed (N : Subgroup Γ) [N.Normal] : (subProp N).IsClosedUnderIsomorphisms :=
  ⟨fun e h => le_H_of_hom e.hom h⟩

/-- **Self-equivalences of `B(Γ)⁰` act on open normal subgroups through automorphisms of `Γ`**
([Mzk2], Proposition 3.2; [SemiAnbd], Proposition 3.2). -/
def OrbitRecon (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] : Prop :=
  ∀ (F : OrbitObj Γ ⥤ OrbitObj Γ) [F.IsEquivalence], ∃ α : Γ ≃ₜ* Γ,
    ∀ N : OpenNormalSubgroup Γ, (F.obj (OrbitObj.ofONS N)).H = N.toSubgroup.map (α : Γ →* Γ)

/-- [Mzk2], Proposition 3.2 for profinite `Γ` (`OrbitObj.exists_continuousMulEquiv`). -/
theorem orbitRecon_of_profinite [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] [T2Space Γ] : OrbitRecon Γ := fun F _ => by
  obtain ⟨α, -, hα, -⟩ := OrbitObj.exists_continuousMulEquiv F
  exact ⟨α, hα⟩

/-- [SemiAnbd], Proposition 3.2 for tempered `Γ` (`OrbitObj.exists_continuousMulEquiv_temp`). -/
theorem orbitRecon_of_temp [IsTopologicalGroup Γ] [T2Space Γ] (hb : HasONSBasis Γ)
    (hs : HasONSChain Γ) (hc : IsONSComplete Γ) : OrbitRecon Γ := fun F _ => by
  obtain ⟨α, -, hα, -⟩ := OrbitObj.exists_continuousMulEquiv_temp hb hs hc hb hc F
  exact ⟨α, hα⟩

/-- **A characteristic normal subgroup `N` makes `subProp N` category-theoretic**: if the
self-equivalences of `B(Γ)⁰` come from automorphisms of `Γ` and every automorphism maps `N` onto
itself, every self-equivalence preserves the objects `Γ/H` with `N ⊆ H`. -/
theorem subProp_autoInvariant [IsTopologicalGroup Γ] (hb : HasONSBasis Γ) (hr : OrbitRecon Γ)
    {N : Subgroup Γ} [hN : N.Normal] (hchar : ∀ α : Γ ≃ₜ* Γ, N.map (α : Γ →* Γ) = N) :
    AutoInvariant (subProp N) := by
  intro σ A hA
  obtain ⟨α, hα⟩ := hr σ.functor
  obtain ⟨K, hK⟩ := hb A.isOpen A.H.one_mem
  haveI := K.isNormal'
  let K' : OpenNormalSubgroup Γ :=
    { toSubgroup := K.toSubgroup ⊔ N
      isOpen' := Subgroup.isOpen_mono le_sup_left K.isOpen
      isNormal' := inferInstance }
  have hle : (K'.toSubgroup : Subgroup Γ) ≤ A.H := sup_le (fun x hx => hK hx) hA
  refine le_H_of_hom (σ.functor.map (OrbitObj.proj A hle)) ?_
  rw [hα K']
  calc N = N.map (α : Γ →* Γ) := (hchar α).symm
    _ ≤ K'.toSubgroup.map (α : Γ →* Γ) := Subgroup.map_mono le_sup_right

end Orbit

/-! ### Pulling back orbits along a surjection -/

section Pull

variable {Γ G : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [TopologicalSpace G]
  (p : Γ →* G) (hs : Function.Surjective p)

/-- `Γ/p⁻¹(H) ≃ G/H` for a surjection `p`. -/
def comapQuot (H : Subgroup G) : Γ ⧸ H.comap p ≃ G ⧸ H where
  toFun := Quotient.map' p fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa using hab
  invFun := Quotient.lift (fun g => (QuotientGroup.mk (Function.surjInv hs g) : Γ ⧸ H.comap p))
    fun a b hab => by
      have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
      apply QuotientGroup.eq.mpr
      simpa [Subgroup.mem_comap, Function.surjInv_eq hs] using hab'
  left_inv x := by
    induction x using QuotientGroup.induction_on with
    | H γ =>
      change (QuotientGroup.mk (Function.surjInv hs (p γ)) : Γ ⧸ H.comap p) = QuotientGroup.mk γ
      apply QuotientGroup.eq.mpr
      simp [Subgroup.mem_comap, Function.surjInv_eq hs]
  right_inv y := by
    induction y using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk (p (Function.surjInv hs g)) : G ⧸ H) = QuotientGroup.mk g
      rw [Function.surjInv_eq hs]

omit [TopologicalSpace Γ] [TopologicalSpace G] in
lemma comapQuot_mk (H : Subgroup G) (γ : Γ) :
    comapQuot p hs H (QuotientGroup.mk γ) = QuotientGroup.mk (p γ) := rfl

omit [TopologicalSpace Γ] [TopologicalSpace G] in
lemma comapQuot_smul (H : Subgroup G) (γ : Γ) (x : Γ ⧸ H.comap p) :
    comapQuot p hs H (γ • x) = p γ • comapQuot p hs H x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, comapQuot_mk, comapQuot_mk,
      MulAction.Quotient.smul_mk, smul_eq_mul, map_mul]

omit [TopologicalSpace Γ] [TopologicalSpace G] in
lemma comapQuot_symm_smul (H : Subgroup G) (γ : Γ) (y : G ⧸ H) :
    (comapQuot p hs H).symm (p γ • y) = γ • (comapQuot p hs H).symm y := by
  apply (comapQuot p hs H).injective
  rw [Equiv.apply_symm_apply, comapQuot_smul, Equiv.apply_symm_apply]

omit [TopologicalSpace Γ] [TopologicalSpace G] in
/-- A `Γ`-equivariant map `Γ/p⁻¹(H) → Γ/p⁻¹(H')` induces a `G`-equivariant map `G/H → G/H'`. -/
lemma comapQuot_conj_smul {H H' : Subgroup G} (u : Γ ⧸ H.comap p → Γ ⧸ H'.comap p)
    (hu : ∀ (γ : Γ) x, u (γ • x) = γ • u x) (g : G) (y : G ⧸ H) :
    comapQuot p hs H' (u ((comapQuot p hs H).symm (g • y))) =
      g • comapQuot p hs H' (u ((comapQuot p hs H).symm y)) := by
  obtain ⟨γ, rfl⟩ := hs g
  rw [comapQuot_symm_smul, hu, comapQuot_smul]

variable (hp : Continuous p)

/-- **The pull-back `B(G)⁰ ⥤ B(Γ)⁰`**, `G/H ↦ Γ/p⁻¹(H)` (pulling back coverings along
`X̲_v → Spec K_v`). -/
def pullFunctor : OrbitObj G ⥤ OrbitObj Γ where
  obj B := ⟨B.H.comap p, B.isOpen.preimage hp⟩
  map {B B'} f :=
    ⟨(comapQuot p hs B'.H).symm ∘ f.toFun ∘ comapQuot p hs B.H, fun γ x => by
      simp only [Function.comp_apply, comapQuot_smul, f.map_smul, comapQuot_symm_smul]⟩
  map_id B := OrbitHom.hom_ext (funext fun x => by simp)
  map_comp f g := OrbitHom.hom_ext (funext fun x => by simp)

/-- The pull-back is fully faithful. -/
def pullFullyFaithful : (pullFunctor p hs hp).FullyFaithful where
  preimage {B B'} u :=
    ⟨comapQuot p hs B'.H ∘ u.toFun ∘ (comapQuot p hs B.H).symm, fun g y =>
      comapQuot_conj_smul p hs u.toFun u.map_smul g y⟩
  map_preimage u := OrbitHom.hom_ext (funext fun x => by
    change (comapQuot p hs _).symm (comapQuot p hs _ (u.toFun _)) = u.toFun x
    simp)
  preimage_map f := OrbitHom.hom_ext (funext fun y => by
    change comapQuot p hs _ ((comapQuot p hs _).symm (f.toFun _)) = f.toFun y
    simp)

lemma pullFunctor_prop (B : OrbitObj G) : subProp p.ker ((pullFunctor p hs hp).obj B) :=
  fun x hx => by
    change p x ∈ B.H
    rw [MonoidHom.mem_ker.mp hx]
    exact B.H.one_mem

/-- The pull-back, as a functor to the objects `Γ/H` with `ker p ⊆ H`. -/
abbrev pullLift : OrbitObj G ⥤ (subProp p.ker).FullSubcategory :=
  (subProp p.ker).lift (pullFunctor p hs hp) (pullFunctor_prop p hs hp)

/-- **`B(G)⁰ ≌ {Γ/H : ker p ⊆ H} ⊆ B(Γ)⁰`** when `p` maps open subgroups to open subgroups. -/
def pullEquiv (hopen : ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → IsOpen (U.map p : Set G)) :
    OrbitObj G ≌ (subProp p.ker).FullSubcategory :=
  haveI := (pullFullyFaithful p hs hp).full
  haveI := (pullFullyFaithful p hs hp).faithful
  haveI : (pullLift p hs hp).EssSurj := ⟨fun A => by
    refine ⟨⟨A.obj.H.map p, hopen _ A.obj.isOpen⟩, ⟨(subProp p.ker).isoMk (eqToIso ?_)⟩⟩
    obtain ⟨⟨H, hH⟩, hA⟩ := A
    change (⟨(H.map p).comap p, _⟩ : OrbitObj Γ) = ⟨H, hH⟩
    congr 1
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hA]⟩
  haveI : (pullLift p hs hp).IsEquivalence := { }
  (pullLift p hs hp).asEquivalence

end Pull

/-! ### `D^⊢_v ⊆ D_v` and its category-theoreticity -/

section Model

variable (D : InitialThetaData.{0}) (v : Vnon D)

/-- **`Δ_v = ker(Π_v → G_v)`** (IUT I, Definition 3.1 (e)). -/
def deltaV : Subgroup (Piv D v).carrier := (piToG D v).ker

instance : (deltaV D v).Normal := MonoidHom.normal_ker _

/-- **`D^⊢_v ⊆ D_v`** (IUT I, Examples 3.2 (i), 3.3 (i)): the objects `Π_v/H` with `Δ_v ⊆ H`,
i.e. the coverings pulled back from `Spec K_v`. -/
def isVdashObj : ObjectProperty (Dv D v) := subProp (deltaV D v)

instance : (isVdashObj D v).IsClosedUnderIsomorphisms := subProp_isClosed _

/-- **`D^⊢_v ≌ B(G_v)⁰`** (given debt H3): the pull-back along `Π_v ↠ G_v`. -/
def vdashModelEquiv (h3 : PiToGQuotient D v) : (isVdashObj D v).FullSubcategory ≌ DVdash D v :=
  (pullEquiv (p := piToG D v) (hs := h3.1) (hp := continuous_piToG D v) (hopen := h3.2)).symm

/-- **[AbsAnab], Lemma 1.3.8 for `Π_v` (named input)**: every automorphism of the topological
group `Π_v` maps `Δ_v` onto itself. This is MR13's debt `ArithQuotientPreservedPadic`
(curves-jacobian `CuspChar/RigidityPadic.lean`, `Absolute Anabelian Geometry.txt` l.977–985)
stated for iut's `Π_v` (the identification of iut's `Π_v` with the `π₁ᵉᵗ` of a curves-jacobian
`HypCurve` is not formalised); IUT I, Example 3.2 (vi)(a) applies the same lemma at `V^bad`. -/
def DeltaCharacteristic : Prop :=
  ∀ α : (Piv D v).carrier ≃ₜ* (Piv D v).carrier, (deltaV D v).map (α : _ →* _) = deltaV D v

/-- **The hypotheses of [SemiAnbd], Proposition 3.2 for the tempered `Π_v`** (`v ∈ V^bad`):
Hausdorff, a basis of open normal subgroups, completeness for them (proved for tfg's
`temperedPi1` in `Frobenioid/Tempered/PiTpONS.lean`, not yet instantiated at `X̲_v`) and a
countable cofinal chain (MR18's debt `hctbl`). -/
def TempRecon : Prop :=
  T2Space (Piv D v).carrier ∧ HasONSBasis (Piv D v).carrier ∧ HasONSChain (Piv D v).carrier ∧
    IsONSComplete (Piv D v).carrier

/-- **The named inputs of the mono-analyticisation at `v`**: Lemma 1.3.8 for `Π_v`, and at
`v ∈ V^bad` the reconstruction hypotheses for the tempered `Π_v`. -/
def VdashInputs : Prop := DeltaCharacteristic D v ∧ (v ∈ D.VBad → TempRecon D v)

/-- At `v ∉ V^bad`, `Π_v` is profinite. -/
theorem piv_profinite (hv : v ∉ D.VBad) :
    CompactSpace (Piv D v).carrier ∧ TotallyDisconnectedSpace (Piv D v).carrier ∧
      T2Space (Piv D v).carrier := by
  unfold Piv piData
  rw [if_neg hv]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- **`D^⊢_v ⊆ D_v` is preserved by every self-equivalence of `D_v`** (IUT I, Example 3.2 (vi)(a),
3.3 (iii)(a)), given the named inputs. -/
theorem isVdashObj_autoInvariant (h : VdashInputs D v) : AutoInvariant (isVdashObj D v) := by
  by_cases hv : v ∈ D.VBad
  · obtain ⟨h1, hb, hs, hc⟩ := h.2 hv
    exact subProp_autoInvariant hb (orbitRecon_of_temp hb hs hc) h.1
  · obtain ⟨h1, h2, h3⟩ := piv_profinite D v hv
    exact subProp_autoInvariant (hasONSBasis_of_profinite (G := (Piv D v).carrier))
      orbitRecon_of_profinite h.1

end Model

/-! ### The mono-analyticisation of abstract `D`-prime-strips -/

section Strips

variable {D : InitialThetaData.{0}} {v : Vnon D}

/-- **`†D^⊢_v ⊆ †D_v`**: the objects of `†D_v` mapped into `D^⊢_v` by some equivalence
`†D_v ≌ D_v` (a full subcategory defined without choices). -/
def DComp.vdashProp (X : DComp D v) : ObjectProperty X.C := transportProp (isVdashObj D v) X.C

/-- The category `†D^⊢_v`. -/
def DComp.vdashCat (X : DComp D v) : Cat.{0, 0} := Cat.of X.vdashProp.FullSubcategory

/-- **The mono-analyticisation of a constituent** `†D_v ↦ †D^⊢_v` (IUT I, Definition 4.1 (iv)):
a `D^⊢`-constituent, given the named inputs (Lemma 1.3.8 for `Π_v`, `TempRecon` at `V^bad`) and
debt H3. -/
def DComp.toVdash (X : DComp D v) (h : VdashInputs D v) (h3 : PiToGQuotient D v) :
    DVdashComp D v :=
  ⟨X.vdashCat, X.equiv_model.map fun e =>
    (transportModelEquiv (isVdashObj_autoInvariant D v h) e).trans (vdashModelEquiv D v h3)⟩

/-- **The mono-analyticisation on isomorphisms** (no input needed): an equivalence
`†D_v ≌ ‡D_v` restricts to `†D^⊢_v ≌ ‡D^⊢_v`. -/
def DComp.isoToVdash {X Y : DComp D v} (f : X.C ≌ Y.C) : X.vdashCat ≌ Y.vdashCat :=
  transportEquiv f

variable (D)

/-- **The mono-analyticisation `†D ↦ †D^⊢` of `D`-prime-strips** (IUT I, Definition 4.1 (iv);
Remark 5.2.1 (ii)), non-archimedean part. -/
def DStripNon.toVdash (P : DStripNon D) (h : ∀ v, VdashInputs D v)
    (h3 : ∀ v, PiToGQuotient D v) : DVdashStripNon D :=
  ⟨fun v => (P.comp v).toVdash (h v) (h3 v)⟩

variable {D}

/-- The mono-analyticisation on isomorphisms of `D`-prime-strips. -/
def DStripNon.isoToVdash {P Q : DStripNon D} (f : P.Iso Q) (h : ∀ v, VdashInputs D v)
    (h3 : ∀ v, PiToGQuotient D v) :
    (DStripNon.toVdash D P h h3).Iso (DStripNon.toVdash D Q h h3) :=
  fun v => DComp.isoToVdash (f v)

/-- **`F ↦ D^⊢`** (Remark 5.2.1 (i), (ii)): the mono-analyticisation of the associated
`D`-prime-strip. -/
def FStripNon.toDVdash (P : FStripNon D) (h : ∀ v, VdashInputs D v)
    (h3 : ∀ v, PiToGQuotient D v) : DVdashStripNon D :=
  DStripNon.toVdash D P.toD h h3

/-- `F ↦ D^⊢` on isomorphisms: through the base equivalences. -/
def FStripNon.isoToDVdash {P Q : FStripNon D} (f : P.Iso Q) (h : ∀ v, VdashInputs D v)
    (h3 : ∀ v, PiToGQuotient D v) : (P.toDVdash h h3).Iso (Q.toDVdash h h3) :=
  DStripNon.isoToVdash (FStripNon.isoToD f) h h3

end Strips

end PrimeStrip

end Multiradial

end Iut
