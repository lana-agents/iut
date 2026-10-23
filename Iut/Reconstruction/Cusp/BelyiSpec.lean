/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.Belyi
import CurvesJacobian.Cusp.BelyiCuspSpec

/-!
# Belyi cuspidalisation of `Π_X` (MR8.8): the genuine cusp data and `belyiCusp_spec`

`Belyi.lean` fills in cusps of a group with a *given* family of cuspidal inertia subgroups
(ROADMAP §5, item 34). Here the family is the genuine one, and the cuspidalisation itself is the
group-theoretic algorithm of [AbsTopII] Cor 3.7, 3.8 with its specification, both from
`curves-jacobian` (MR8.5/8.6):

* `CuspData.ofExt E`: the cusp data of a cuspidal extension `E = (Π ↠ G, {I})` (indexed by its
  cuspidal subgroups); `CuspData.Iso.ofExtIso`: every isomorphism of cuspidal extensions is an
  isomorphism of cusp data, so `filledEquiv` applies to it;
* `arithCuspData Ω C hc`: for an affine hyperbolic curve `C` over a number field, `Π_U` with
  the cuspidal inertia groups of its cusps (`CurvesJacobian.Cusp.arithCusps`: the `Π_U`-conjugates
  of the images of the inertia groups of the places of `K(X̄_Ω)^alg` over `X̄_Ω ∖ U_Ω`);
* **`ker_fillMap_eq_closure_kernel`**: filling in a closed point `x` (not necessarily rational),
  `ker(Π_U → Π_{U ∪ {x}})` is the closure of the `kernel` of `arithCuspData` for the single cusp
  `I` over `x` ([AbsTopI] Def 4.2 (iii)); so the group-theoretic filling of `Belyi.lean` is the
  geometric one, with `Π_{U'} = Π_U / cl(kernel)` (`fillMap_surjective`);
* `BelyiCuspSpec Ω C hc` (the statement of [AbsTopII] Cor 3.7 (a), (b), Cor 3.8 for
  `belyiCusp (Π_X)`) and **`belyiCuspSpec`** (`X` of strictly Belyi type with a Galois Belyi
  cover), **`belyiCuspSpec_oncePunctured`** (`X = E ∖ {O}` with rational `E[2]`, the case of
  IUT I, Def 3.1 (b)).

**Debt (explicit theorem argument).** The only input is `hDGC`, the rel-isom-DGC over all number
fields ([LocAn] Thm A, via [AbsTopI] Def 4.6; `Belyi.Anabelian.RelIsomDGC`), which is milestone
MR7 (the relative `p`-adic Grothendieck conjecture). It is recorded in `Plans/MR9Plan.md`.
Functoriality is in isomorphisms of cuspidal extensions, which preserve the cuspidal subgroups by
definition; that every `Π_X ≃ₜ* Π_{X'}` over `G_K ≃ₜ* G_{K'}` does so is [AbsTopI] Lemma 4.5 (v)
(not yet formalised).
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi.Anabelian CurvesJacobian.Cusp

noncomputable section

namespace Iut.Reconstruction

namespace CuspData

/-- **The cusp data of a cuspidal extension**: `Π` with its cuspidal inertia subgroups, indexed
by themselves. -/
def ofExt (E : CuspidalExt.{u}) : CuspData E.Pi E.cusps where
  inertia I := I.1

@[simp] lemma ofExt_inertia (E : CuspidalExt.{u}) (I : E.cusps) : (ofExt E).inertia I = I.1 :=
  rfl

lemma map_map_symm {G H : Type*} [Group G] [Group H] (e : G ≃* H) (J : Subgroup H) :
    (J.map e.symm.toMonoidHom).map e.toMonoidHom = J := by
  rw [Subgroup.map_map]
  ext x
  simp

/-- **An isomorphism of cuspidal extensions is an isomorphism of cusp data.** -/
def Iso.ofExtIso {E E' : CuspidalExt.{u}} (Φ : E.Iso E') : (ofExt E).Iso (ofExt E') where
  toMulEquiv := Φ.pi.toMulEquiv
  cusps :=
    { toFun I := ⟨I.1.map Φ.pi.toMulEquiv.toMonoidHom, (Φ.cusps_map I.1).1 I.2⟩
      invFun J := ⟨J.1.map Φ.pi.toMulEquiv.symm.toMonoidHom,
        (Φ.cusps_map _).2 (by rw [map_map_symm]; exact J.2)⟩
      left_inv I := Subtype.ext (by
        change (I.1.map Φ.pi.toMulEquiv.toMonoidHom).map Φ.pi.toMulEquiv.symm.toMonoidHom = I.1
        simpa using map_map_symm Φ.pi.toMulEquiv.symm I.1)
      right_inv J := Subtype.ext (map_map_symm Φ.pi.toMulEquiv J.1) }
  map_inertia _ := rfl

end CuspData

section Arith

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

/-- **The genuine cusp data of `Π_U`**: the arithmetic fundamental group of an affine
hyperbolic curve over a number field with its cuspidal inertia groups (`arithCusps`). -/
abbrev arithCuspData : CuspData (arithmeticExt Ω C hc).Pi (arithmeticExt Ω C hc).cusps :=
  CuspData.ofExt (arithmeticExt Ω C hc)

lemma kernel_compl_singleton (I : (arithmeticExt Ω C hc).cusps) :
    (arithCuspData Ω C hc).kernel ({I}ᶜ) = Subgroup.normalClosure (I.1 : Set _) := by
  simp [CuspData.kernel]

variable {Ω C hc} in
/-- **Filling in a closed point is the group-theoretic filling of the genuine cusp data**
([AbsTopI] Def 4.2 (iii)): for `U ⊆ U'` with `U' ∖ U ⊆ {x}`, `x ∈ U' ∖ U` a closed point (not
necessarily rational), the kernel of `Π_U ↠ Π_{U'}` is the closure of the `kernel` of
`arithCuspData` that fills in a single cusp `I` (over `x`). -/
theorem ker_fillMap_eq_closure_kernel {U' : C.Xbar.Opens} (h : C.U ≤ U')
    (hc' : (U' : Set C.Xbar)ᶜ.Nonempty) [Nonempty (baseChangeOpen K Ω U')]
    {x : C.Xbar} (hxU' : x ∈ U') (hxU : x ∉ C.U) (hx : (U' : Set C.Xbar) \ C.U ⊆ {x}) :
    ∃ I : (arithmeticExt Ω C hc).cusps, (fillMap Ω C hc h).toMonoidHom.ker =
      ((arithCuspData Ω C hc).kernel {I}ᶜ).topologicalClosure := by
  obtain ⟨I, hI, e⟩ := exists_ker_fillMap_eq_normalClosure Ω C hc h hc' hxU' hxU hx
  exact ⟨⟨I, hI⟩, by rw [e, kernel_compl_singleton]; rfl⟩

/-- **The specification of `belyiCusp (Π_X)`** ([AbsTopII] Cor 3.7 (a), (b), Cor 3.8,
`Topics in Absolute Anabelian Geometry II.txt` l.4735–4775, l.4794–4842), as in
`CurvesJacobian.Cusp.belyiCusp_spec`:
(a) every candidate `Π_U ↠ Π_V ↪ Π_X` is geometric;
(b) for every nonempty open `U_X ⊆ X` some candidate recovers `Π_V ×_{Π_X} Π_{U_X} ↠ Π_V`;
(c) `belyiCusp` is functorial in isomorphisms of cuspidal extensions;
(d) every isomorphism `Π_X ≅ Π_{X₂}` (`X₂` affine hyperbolic over a number field) lifts to
`Π_{U_X} ≅ Π_{U_{X₂}}` for some nonempty open `U_{X₂}` (Cor 3.8, existence);
(e) such lifts are unique up to inner automorphisms from `ker(Π_{U_X} ↠ Π_X)` (uniqueness). -/
def BelyiCuspSpec : Prop :=
  (∀ x ∈ belyiCusp (arithmeticExt Ω C hc), IsGeomCandidate₂ Ω C hc x) ∧
    (∀ (UX : C.Xbar.Opens) (hUX : UX ≤ C.U) (hne : (UX : Set C.Xbar).Nonempty)
      (α₀ : fiber (basePoint Ω C hc) ≅
        fiber (fillPoint Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) hUX)),
      ∃ x ∈ belyiCusp (arithmeticExt Ω C hc),
        x.emb.toMonoidHom.range.Normal ∧
        (∀ (B : x.PiV ≃ₜ* x.PiV) (g : (arithmeticExt Ω C hc).Pi),
          (∀ v, x.emb (B v) = g * x.emb v * g⁻¹) →
            ∃ ψ : x.PiU ≃ₜ* x.PiU, ∀ u, x.surj (ψ u) = B (x.surj u)) ∧
        ∃ (k : (arithmeticExt Ω C hc).Pi)
          (J : x.PiU ≃ₜ* x.emb.toMonoidHom.range.comap (cor38Fill Ω C hc UX hUX hne α₀)),
          ∀ u, cor38Fill Ω C hc UX hUX hne α₀ (J u) = k * x.emb (x.surj u) * k⁻¹) ∧
    (∀ {E' : CuspidalExt.{u + 1}} (Φ : (arithmeticExt Ω C hc).Iso E'),
      ∀ x ∈ belyiCusp (arithmeticExt Ω C hc), x.transport Φ ∈ belyiCusp E') ∧
    (∀ {K₂ : Type u} [Field K₂] [NumberField K₂] (Ω₂ : Type u) [Field Ω₂] [Algebra K₂ Ω₂]
      [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] (C₂ : HypCurve K₂)
      (hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty)
      (Φ : (arithmeticExt Ω C hc).Iso (arithmeticExt Ω₂ C₂ hc₂))
      (UX : C.Xbar.Opens) (hUX : UX ≤ C.U) (hne : (UX : Set C.Xbar).Nonempty)
      (α₀ : fiber (basePoint Ω C hc) ≅
        fiber (fillPoint Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) hUX)),
      ∃ (UX₂ : C₂.Xbar.Opens) (hUX₂ : UX₂ ≤ C₂.U) (hne₂ : (UX₂ : Set C₂.Xbar).Nonempty),
        ∀ α₂ : fiber (basePoint Ω₂ C₂ hc₂) ≅
            fiber (fillPoint Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hc₂)
              hUX₂),
          ∃ φU : (arithmeticExt Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc)).Pi ≃ₜ*
              (arithmeticExt Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hc₂)).Pi,
            ∀ e, cor38Fill Ω₂ C₂ hc₂ UX₂ hUX₂ hne₂ α₂ (φU e) =
              Φ.pi (cor38Fill Ω C hc UX hUX hne α₀ e)) ∧
    (∀ (UX : C.Xbar.Opens) (hUX : UX ≤ C.U) (hne : (UX : Set C.Xbar).Nonempty)
      (α₀ : fiber (basePoint Ω C hc) ≅
        fiber (fillPoint Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) hUX))
      {P : Type u} [Group P] [TopologicalSpace P]
      (φ₁ φ₂ : P ≃ₜ* (arithmeticExt Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc)).Pi),
      (∀ p, cor38Fill Ω C hc UX hUX hne α₀ (φ₂ p) = cor38Fill Ω C hc UX hUX hne α₀ (φ₁ p)) →
      ∃ n ∈ (cor38Fill Ω C hc UX hUX hne α₀).ker, ∀ p, φ₂ p = n * φ₁ p * n⁻¹)

/-- **[AbsTopII] Cor 3.7, 3.8 for `belyiCusp (Π_X)`**, `X` of strictly Belyi type with a Galois
Belyi cover (`S`). The only input is the rel-isom-DGC over number fields (`hDGC`, MR7). -/
theorem belyiCuspSpec (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω]
    [Algebra.IsAlgebraic M Ω] (S : GaloisBelyiInput C M) : BelyiCuspSpec Ω C hc :=
  belyiCusp_spec Ω C hc hDGC S

/-- **[AbsTopII] Cor 3.7, 3.8 for the once-punctured elliptic curve `X = E ∖ {O}`** with
`K`-rational `E[2]` (IUT I, Def 3.1 (b), assumes the `2·3`-torsion rational). The only input is
the rel-isom-DGC over number fields (`hDGC`, MR7). -/
theorem belyiCuspSpec_oncePunctured
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    {E : WeierstrassCurve K} [E.IsElliptic] (hE : E.Ψ₂Sq.Splits) :
    BelyiCuspSpec Ω (hypCurveX E) (compl_XE_nonempty E) := by
  obtain ⟨S⟩ := nonempty_galoisBelyiInput E hE
  exact belyiCuspSpec Ω (hypCurveX E) (compl_XE_nonempty E) hDGC (M := K) S

end Arith

end Iut.Reconstruction
