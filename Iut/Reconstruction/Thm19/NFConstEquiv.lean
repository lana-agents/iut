/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.GalEquiv

/-!
# `σ = nfRingEquiv|_{ℚ̄}` as a field isomorphism and `ψ = conj σ` (MR9, `CKSemiAbsConj` item 4)

[AbsTopIII] Thm 1.9 (`Topics in Absolute Anabelian Geometry III.txt` l.2109–2199) reconstructs
`k̄_NF` with its `G_k`-action functorially in `Π_U`. `Thm19/GalEquiv.lean` gives the restriction
`nfConst : k̄ → k̄'` of the field isomorphism `nfRingEquiv` (induced by `Φ : Π_U ≃ Π_{U'}`) and its
Galois equivariance `σ(g c) = ψ(g) σ(c)`, `ψ = gkIso Φ`. Here:

* `kbarRestrict` (generic): a ring isomorphism of NF-portions `F_NF ≃ F'_NF` of curves over number
  fields restricts to a ring isomorphism `k̄ ≃+* k̄'` of the fields of algebraic numbers;
* **`nfConstEquiv`**: `σ : k̄ ≃+* k̄'`, with `nfConstEquiv_apply` (it is `nfConst`) and
  `nfRingEquiv_constFnf` (`nfRingEquiv (c f) = σ(c) nfRingEquiv f` follows from this by
  multiplicativity);
* `ord_ringEquivOfIso` (generic), **`ord_nfRingEquiv`**: `nfRingEquiv` preserves the valuations
  along the bijection of points `nfPlaceEquiv`;
* **`gkIso_eq_conj`**: `ψ(g) = σ ∘ g ∘ σ⁻¹` on `k̄'`, i.e. `ψ` is conjugation by `σ`.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

/-! ### Generic: restriction to the algebraic numbers -/

section Generic

variable {k Ω : Type u} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [CharZero Ω]
  {k' Ω' : Type u} [Field k'] [NumberField k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : Pi1.Orbifold.GaloisData k' t'} [IsGalois (K₀ k' t') Ω'] [CharZero Ω']
  (M : NFModel D) (M' : NFModel D')

/-- A ring isomorphism of NF-portions maps algebraic numbers to algebraic numbers. -/
lemma mem_kbar_map_constFnf (e : fnf M ≃+* fnf M') (y : kbar k Ω) :
    ((e (constFnf M y) : fnf M') : Ω') ∈ kbar k' Ω' :=
  mem_kbar_of_isAlgebraic (isAlgebraic_rat_map (algebraMap (fnf M') Ω')
    (isAlgebraic_rat_map e.toRingHom ((isAlgebraic_algHom_iff ((fnf M).val.restrictScalars ℚ)
      (fnf M).val.injective).1
        (isAlgebraic_rat_of_isAlgebraic (mem_algebraicClosure_iff.1 y.2)))))

lemma constFnf_mul (y z : kbar k Ω) : constFnf M (y * z) = constFnf M y * constFnf M z := rfl

lemma constFnf_add (y z : kbar k Ω) : constFnf M (y + z) = constFnf M y + constFnf M z := rfl

/-- **A ring isomorphism of NF-portions restricts to the algebraic numbers**, `k̄ ≃+* k̄'`. -/
def kbarRestrict (e : fnf M ≃+* fnf M') : kbar k Ω ≃+* kbar k' Ω' where
  toFun y := ⟨(e (constFnf M y) : Ω'), mem_kbar_map_constFnf M M' e y⟩
  invFun y := ⟨(e.symm (constFnf M' y) : Ω), mem_kbar_map_constFnf M' M e.symm y⟩
  left_inv y := Subtype.ext (by
    change ((e.symm (constFnf M' ⟨(e (constFnf M y) : Ω'), _⟩) : fnf M) : Ω) = y
    rw [show constFnf M' ⟨(e (constFnf M y) : Ω'), mem_kbar_map_constFnf M M' e y⟩ =
      e (constFnf M y) from rfl, RingEquiv.symm_apply_apply]
    rfl)
  right_inv y := Subtype.ext (by
    change ((e (constFnf M ⟨(e.symm (constFnf M' y) : Ω), _⟩) : fnf M') : Ω') = y
    rw [show constFnf M ⟨(e.symm (constFnf M' y) : Ω), mem_kbar_map_constFnf M' M e.symm y⟩ =
      e.symm (constFnf M' y) from rfl, RingEquiv.apply_symm_apply]
    rfl)
  map_mul' y z := Subtype.ext (by
    change ((e (constFnf M (y * z)) : fnf M') : Ω') =
      ((e (constFnf M y) : fnf M') : Ω') * ((e (constFnf M z) : fnf M') : Ω')
    rw [constFnf_mul, map_mul]
    rfl)
  map_add' y z := Subtype.ext (by
    change ((e (constFnf M (y + z)) : fnf M') : Ω') =
      ((e (constFnf M y) : fnf M') : Ω') + ((e (constFnf M z) : fnf M') : Ω')
    rw [constFnf_add, map_add]
    rfl)

lemma coe_kbarRestrict (e : fnf M ≃+* fnf M') (y : kbar k Ω) :
    ((kbarRestrict M M' e y : kbar k' Ω') : Ω') = ((e (constFnf M y) : fnf M') : Ω') := rfl

/-- `e` on an algebraic number is its restriction. -/
lemma apply_constFnf (e : fnf M ≃+* fnf M') (y : kbar k Ω) :
    e (constFnf M y) = constFnf M' (kbarRestrict M M' e y) := rfl

end Generic

/-! ### The field isomorphism preserves the valuations -/

section Functorial

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [CharZero Ω] [Fact (D.H ≤ D.HL)] [NumberField k] (N : NFModel D)
  (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : Pi1.Orbifold.GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω']
  [CharZero Ω'] [Fact (D'.H ≤ D'.HL)] [NumberField k'] (N' : NFModel D')
  (hkF' : ∀ x : F D', IsAlgebraic k' x → x ∈ Set.range (algebraMap k' (F D')))

attribute [local instance] Thm19.isAlgClosed_algebraicClosure Thm19.isFunctionField_fnf

/-- `ord_P` on the reconstructed triple is `ord_P` of the NF-rational function. -/
lemma val_recTriple_kummerNFEquiv (P : Place (algebraicClosure ℚ Ω) (fnf N)) (f : (fnf N)ˣ) :
    (recTriple N hkF).val P (kummerNFEquiv N hkF f) = P.ord (f : fnf N) := by
  change Multiplicative.toAdd (Uchida.ordHom (algebraicClosure ℚ Ω) (fnf N) P
    ((kummerNFEquiv N hkF).symm (kummerNFEquiv N hkF f))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- **The field isomorphism of an isomorphism of triples preserves the valuations**:
`ord_{σ(P)}(ψ f) = ord_P f`, `σ` the bijection of points of the isomorphism. -/
theorem ord_ringEquivOfIso (e : (recTriple N hkF).Iso (recTriple N' hkF'))
    (P : Place (algebraicClosure ℚ Ω) (fnf N)) (f : (fnf N)ˣ) :
    (e.σ P).ord (ringEquivOfIso N hkF N' hkF' e (f : fnf N)) = P.ord (f : fnf N) := by
  have h1 := e.val_eq P (kummerNFEquiv N hkF f)
  have h2 : e.φ (kummerNFEquiv N hkF f) =
      kummerNFEquiv N' hkF' (Units.map (ringEquivOfIso N hkF N' hkF' e).toMonoidHom f) :=
    Subtype.ext ((kummerNF_ringEquivOfIso N hkF N' hkF' e f).symm.trans
      (coe_kummerNFEquiv N' hkF' _).symm)
  rw [h2, val_recTriple_kummerNFEquiv, val_recTriple_kummerNFEquiv] at h1
  exact h1

end Functorial

/-! ### `σ = nfRingEquiv|_{k̄}` and `ψ = conj σ` -/

section Lift

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}
  [hc₂ : Fact (C₂.U : Set C₂.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic

variable {τ : C.Xbar.functionField} {hτ : Transcendental K τ}
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] {hU : C.U = chartOne K C.Xbar τ}
  {τ₂ : C₂.Xbar.functionField} {hτ₂ : Transcendental K₂ τ₂}
  [IsGalois (K₀ K₂ (coordT τ₂)) (FFClosure C₂.Xbar)] {hU₂ : C₂.U = chartOne K₂ C₂.Xbar τ₂}
  {Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out)}

variable [Fact (0 < (CurvesJacobian.curveGenus K C.Xbar).toNat)]
  [Fact (0 < (CurvesJacobian.curveGenus K₂ C₂.Xbar).toNat)]
  [CharZero (FFClosure C.Xbar)] [CharZero (FFClosure C₂.Xbar)]

attribute [local instance] Thm19.isAlgClosed_algebraicClosure Thm19.isFunctionField_fnf

variable (hS : BelyiCuspSpec Ω C hc.out) (hS₂ : BelyiCuspSpec Ω₂ C₂ hc₂.out)
  (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
  (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
  (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
  (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
  (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
  (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0)
  (hDGC : RelIsomDGC.Exists K₂) (hDGC₁ : RelIsomDGC.Exists K)
  (N : NFModel (curveGaloisData K hτ)) (N₂ : NFModel (curveGaloisData K₂ hτ₂))

variable (hτ hU hτ₂ hU₂ Φ) in
/-- **`σ : k̄ ≃+* k̄'`**: `nfRingEquiv` on the algebraic numbers, as a field isomorphism
(MR9, `CKSemiAbsConj` item 4). -/
def nfConstEquiv : kbar K (FFClosure C.Xbar) ≃+* kbar K₂ (FFClosure C₂.Xbar) :=
  kbarRestrict N N₂ (nfRingEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂)

/-- `nfConstEquiv` is `nfConst`. -/
lemma nfConstEquiv_apply (y : kbar K (FFClosure C.Xbar)) :
    nfConstEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ y =
      nfConst hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ y := rfl

/-- **`nfRingEquiv` is `σ` on the algebraic numbers.** -/
lemma nfRingEquiv_constFnf (y : kbar K (FFClosure C.Xbar)) :
    nfRingEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ (constFnf N y) =
      constFnf N₂ (nfConstEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ y) :=
  rfl

variable (hτ hU hτ₂ hU₂ Φ) in
/-- The bijection of the points of `Z_NF` and `Z'_NF` underlying `nfRingEquiv`. -/
def nfPlaceEquiv : Place (algebraicClosure ℚ (FFClosure C.Xbar)) (fnf N) ≃
    Place (algebraicClosure ℚ (FFClosure C₂.Xbar)) (fnf N₂) :=
  (recTripleIso hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂).σ

/-- **`nfRingEquiv` preserves the valuations**: `ord_{σ(P)}(ψ f) = ord_P f` for `f ≠ 0`. -/
theorem ord_nfRingEquiv (P : Place (algebraicClosure ℚ (FFClosure C.Xbar)) (fnf N))
    (f : fnf N) (hf : f ≠ 0) :
    (nfPlaceEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ P).ord
      (nfRingEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ f) = P.ord f :=
  ord_ringEquivOfIso N (mem_range_of_isAlgebraic_F K hτ) N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)
    (recTripleIso hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂) P (Units.mk0 f hf)

/-- **`ψ = conj σ`** (MR9, `CKSemiAbsConj` item 4): the isomorphism `ψ = gkIso Φ : G_K ≃ G_{K'}`
induced by `Φ` is conjugation by `σ = nfConstEquiv`, `ψ(g) = σ ∘ g ∘ σ⁻¹` on `k̄'`
(`nfConst_galois` at `σ⁻¹ z`). -/
theorem gkIso_eq_conj (gal : Gk K (FFClosure C.Xbar)) (z : kbar K₂ (FFClosure C₂.Xbar)) :
    gkIso hτ hU hτ₂ hU₂ Φ gal z =
      nfConstEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂
        (gal ((nfConstEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂).symm
          z)) := by
  have h := nfConst_galois (hU := hU) (hU₂ := hU₂) (Φ := Φ) hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC
    hDGC₁ N N₂ gal
    ((nfConstEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂).symm z)
  rw [← nfConstEquiv_apply, ← nfConstEquiv_apply, RingEquiv.apply_symm_apply] at h
  exact h.symm

end Lift

end Iut.Reconstruction.Thm19
