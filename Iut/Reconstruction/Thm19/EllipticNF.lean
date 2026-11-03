/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.EllipticJ
import Iut.Reconstruction.Thm19.ConstExtThmC
import Iut.Reconstruction.Thm19.NFCanon
import CurvesJacobian.Galois.ChartOfOpen
import CurvesJacobian.Galois.FunctionFieldF
import CurvesJacobian.LocAn.GenusBaseChange

/-!
# The NF-portion of `E ∖ {O}` as an elliptic function field (MR9, `CKSemiAbsConj` item 5)

Let `E` be an elliptic curve over a number field `K`, `Ē = curveE E`, `X = E ∖ {O} = XE E` and
`D = curveGaloisData K hτ` the Galois model of `Ē` with coordinate `τ = x` (curves-jacobian
`hemiCurveData E`). This file provides the inputs of `EllipticJ.j_eq_of_semilinear` for the
NF-portion `F_NF = fnf N` of the function field (the field on which `nfRingEquiv` acts):

* `XE_eq_chartOne`: `E ∖ {O}` is the chart `x⁻¹(𝔸¹)` (the hypothesis `hU` of the Thm 1.9
  machinery for `hypCurveE E`, `τ = x`); `hypCurveE`: curves-jacobian's `hypCurveX E` with
  reducible fields;
* generic transport along semilinear isomorphisms of function fields over algebraically closed
  fields: `transcendental_tr`, `finrank_adjoin_tr` (`[F : k(x)]` via the degree of the divisor of
  poles), with weil-curves' `genus` handled by `genus_eq_of_tr` (`Thm19/ConstExtThmC.lean`);
* `finrank_tF_le_index`: `[F : k(t)] ≤ [Gal(Ω / k(t)) : H]` for a Galois model, and
  `index_baseChange_H_le`: base change to `k̄` does not increase the index;
* `kbarQbar`, `fbcEquiv`: over a number field `k̄ = k̄_NF` and `F k̄ = F_NF` (the identity of `Ω`);
* **`weq_fnf`**, `transcendental_xNF`, **`finrank_fnf_xNF`**, **`genus_fnf`**: in `F_NF` the
  coordinates `x, y` satisfy the Weierstrass equation of `E` (mapped to `k̄_NF`), `x` is
  transcendental, `[F_NF : k̄_NF(x)] = 2` and `g(F_NF) = 1`.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  Module Belyi Belyi.Anabelian
open scoped IntermediateField

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

/-! ### `E ∖ {O}` is the chart of `x` -/

section Chart

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- **`E ∖ {O} = x⁻¹(𝔸¹)`**: the points of `Ē` where `x` is regular. -/
theorem XE_eq_chartOne : XE E = chartOne K (curveE E) (xN E) := by
  haveI := nonempty_XE₂ E
  ext p
  by_cases hp : p = genericPoint (curveE E)
  · subst hp
    exact ⟨fun _ => genericPoint_mem_chartOne (k := K) _,
      fun _ => genericPoint_mem_of_nonempty (XE E)⟩
  · let Q := curvePlaceEquiv K (curveE E) ⟨p, hp⟩
    have hQ : pointOfPlace K (curveE E) Q = p := by
      change ((curvePlaceEquiv K (curveE E)).symm (curvePlaceEquiv K (curveE E) ⟨p, hp⟩)).1 = p
      rw [Equiv.symm_apply_apply]
    have hQv : (stalkVS K p : ValuationSubring (curveE E).functionField) = Q.1 :=
      (curvePlaceEquiv_apply K (curveE E) ⟨p, hp⟩).symm
    change p ∈ XE E ↔ p ∈ chartOne K (curveE E) (xN E)
    rw [mem_chartOne_iff K (transcendental_xN E), hQv]
    constructor
    · intro h
      exact xN_mem_of_mem_XE₂ E Q (hQ ▸ h)
    · intro h
      by_contra h'
      exact xN_not_mem_of_not_mem_XE₂ E Q (hQ ▸ h') h

/-- **`E ∖ {O}` as a hyperbolic curve** (curves-jacobian `hypCurveX E`, reducibly: its
compactification is `Ē = curveE E`, its open `XE E`). -/
@[reducible] def hypCurveE : HypCurve K where
  Xbar := curveE E
  over := (hypCurveX E).over
  isCurve := (hypCurveX E).isCurve
  U := XE E
  nonempty := (hypCurveX E).nonempty
  cusps_finite := (hypCurveX E).cusps_finite
  hyperbolic := (hypCurveX E).hyperbolic

/-- `g(Ē) ≠ 0`. -/
theorem curveGenus_hypCurveE_ne : CurvesJacobian.curveGenus K (hypCurveE E).Xbar ≠ 0 := by
  rw [curveGenus_curveE₂ E]
  norm_num

instance fact_curveGenus_hypCurveE :
    Fact (0 < (CurvesJacobian.curveGenus K (hypCurveE E).Xbar).toNat) :=
  ⟨by rw [curveGenus_curveE₂ E]; norm_num⟩

end Chart

/-! ### Transport along semilinear isomorphisms -/

section Transport

variable {κ L κ' L' : Type*} [Field κ] [Field L] [Algebra κ L] [Field κ'] [Field L']
  [Algebra κ' L'] (φ : L ≃+* L') (ψ : κ ≃+* κ')
  (hφ : ∀ c : κ, φ (algebraMap κ L c) = algebraMap κ' L' (ψ c))
  [IsAlgClosed κ] [IsFunctionField κ L] [IsAlgClosed κ'] [IsFunctionField κ' L']

include hφ in
/-- Transcendence transports along semilinear isomorphisms of function fields. -/
theorem transcendental_tr {x : L} (hx : Transcendental κ x) : Transcendental κ' (φ x) := by
  intro halg
  obtain ⟨P, hP⟩ := Place.exists_ord_neg (k := κ) hx
  have h1 := (Place.isAlgebraic_iff_forall_mem.1 halg) (placeTr φ ψ hφ P)
  rw [mem_placeTr_apply] at h1
  exact P.ord_neg_iff.1 hP h1

include hφ in
/-- The divisor of poles transports. -/
theorem polarDivisor_tr (x : L) :
    Divisor.polarDivisor κ' (φ x) = divTr φ ψ hφ (Divisor.polarDivisor κ x) := by
  ext Q
  rw [divTr_apply, Divisor.polarDivisor_apply, Divisor.polarDivisor_apply]
  conv_lhs => rw [← (placeTrEquiv φ ψ hφ).apply_symm_apply Q]
  rw [placeTrEquiv_apply, ord_placeTr]

include hφ in
/-- **`[L : κ(x)]` transports** (it is the degree of the divisor of poles of `x`). -/
theorem finrank_adjoin_tr {x : L} (hx : Transcendental κ x) :
    finrank κ'⟮φ x⟯ L' = finrank κ⟮x⟯ L := by
  have h1 := Divisor.deg_polarDivisor (k := κ') (transcendental_tr φ ψ hφ hx)
  have h2 := Divisor.deg_polarDivisor (k := κ) hx
  rw [polarDivisor_tr φ ψ hφ, deg_divTr] at h1
  exact_mod_cast h1.symm.trans h2

end Transport

/-! ### `[F : k(t)]` for a Galois model -/

section Galois

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] [CharZero k] [IsSepClosed Ω]

attribute [local instance] isFunctionField_F

omit [IsSepClosed Ω] in
/-- **`[F : k(t)] ≤ [Gal(Ω / k(t)) : H]`** (equality for `K₀ = k(t)`, by Galois theory). -/
theorem finrank_tF_le_index : finrank k⟮tF D⟯ (F D) ≤ D.H.index := by
  have hK₀ : finrank (K₀ k t) (F D) = D.H.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, fixingSubgroup_F]
  set E : IntermediateField k (F D) := IntermediateField.adjoin k {tF D}
  have hmem : ∀ x : K₀ k t, algebraMap (K₀ k t) (F D) x ∈ E := by
    intro x
    have hx : (x : Ω) ∈ (K₀ k t) := x.2
    have hle : (K₀ k t) ≤ (E.map (IntermediateField.val (F D) |>.restrictScalars k)) := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact ⟨tF D, IntermediateField.mem_adjoin_simple_self k _, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle hx
    have : y = algebraMap (K₀ k t) (F D) x := Subtype.ext hyx
    exact this ▸ hy
  letI : Algebra (K₀ k t) E :=
    ((algebraMap (K₀ k t) (F D)).codRestrict E.toSubalgebra hmem).toAlgebra
  haveI : IsScalarTower (K₀ k t) E (F D) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : FiniteDimensional (K₀ k t) (F D) := inferInstance
  haveI : FiniteDimensional (K₀ k t) E :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom (K₀ k t) E (F D)).toLinearMap
      (algebraMap E (F D)).injective
  have htower := Module.finrank_mul_finrank (K₀ k t) E (F D)
  have hpos : 0 < finrank (K₀ k t) E := Module.finrank_pos
  rw [← hK₀, ← htower]
  exact Nat.le_mul_of_pos_left _ hpos

omit [CharZero k] [IsSepClosed Ω] in
/-- **Base change to `k̄` does not increase the index of `H`.** -/
theorem index_baseChange_H_le (hD : D.H.index ≠ 0) :
    (Kummer.baseChange D).H.index ≤ D.H.index := by
  have e : (Kummer.baseChange D).H = D.H.comap (resK₀ k t) := by
    ext σ
    rw [mem_baseChange_H, Subgroup.mem_comap]
  rw [e, Subgroup.index_comap]
  calc D.H.relIndex (resK₀ k t).range ≤ D.H.relIndex ⊤ :=
        Subgroup.relIndex_le_of_le_right le_top (by rwa [Subgroup.relIndex_top_right])
    _ = D.H.index := Subgroup.relIndex_top_right _

end Galois

/-! ### The NF-portion of a curve over a number field is `F k̄` -/

section NF

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [CharZero k] [CharZero Ω]
  [NumberField k] (N : NFModel D)

variable (k Ω) in
/-- `k̄ = k̄_NF` over a number field, as a ring isomorphism. -/
def kbarQbar : kbar k Ω ≃+* algebraicClosure ℚ Ω where
  toFun c := ⟨c, mem_algebraicClosure_iff.2 (isAlgebraic_of_mem_kbar c.2)⟩
  invFun c := ⟨c, mem_kbar_of_isAlgebraic (mem_algebraicClosure_iff.1 c.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- **`F k̄ = F_NF`** over a number field, as a ring isomorphism (the identity of `Ω`). -/
def fbcEquiv : F (Kummer.baseChange D) ≃+* fnf N where
  toFun z := ⟨z, (NFModel.mem_FNF_iff_numberField N z).2 z.2⟩
  invFun w := ⟨w, (NFModel.mem_FNF_iff_numberField N w).1 w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp] lemma coe_fbcEquiv (z : F (Kummer.baseChange D)) : ((fbcEquiv N z : fnf N) : Ω) = z := rfl

lemma fbcEquiv_algebraMap (c : kbar k Ω) :
    fbcEquiv N (algebraMap (kbar k Ω) (F (Kummer.baseChange D)) c) =
      algebraMap (algebraicClosure ℚ Ω) (fnf N) (kbarQbar k Ω c) := rfl

end NF

/-! ### The NF-portion of `E ∖ {O}` -/

section Elliptic

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- `K(Ē)^alg` has characteristic zero. -/
instance charZero_FFClosure_curveE : CharZero (FFClosure (curveE E)) :=
  charZero_of_injective_algebraMap (algebraMap K (FFClosure (curveE E))).injective

attribute [local instance] isFunctionField_F Thm19.isAlgClosed_algebraicClosure
  Thm19.isFunctionField_fnf

/-- `x ∈ F k̄`. -/
abbrev xF : F (Kummer.baseChange (curveGaloisData K (transcendental_xN E))) :=
  tF (Kummer.baseChange (curveGaloisData K (transcendental_xN E)))

/-- `y ∈ F k̄`. -/
def yF : F (Kummer.baseChange (curveGaloisData K (transcendental_xN E))) :=
  ⟨algebraMap _ _ (yN E), algebraMap_mem_F K (transcendental_xN E) (yN E)⟩

/-- `K(Ē) → F k̄`. -/
def ffToF :
    (curveE E).functionField →+* F (Kummer.baseChange (curveGaloisData K (transcendental_xN E))) :=
  (algebraMap (curveE E).functionField (FFClosure (curveE E))).codRestrict
    (F (Kummer.baseChange (curveGaloisData K (transcendental_xN E))))
    (algebraMap_mem_F K (transcendental_xN E))

/-- **The Weierstrass equation in `F k̄`.** -/
theorem weq_F : WEq₂ (E.map (algebraMap K (kbar K (FFClosure (curveE E))))) (xF E) (yF E) := by
  have h := EllipticJ.weq_map (ffToF E) (algebraMap K (kbar K (FFClosure (curveE E)))) (fun c => by
    apply Subtype.ext
    change algebraMap (curveE E).functionField (FFClosure (curveE E))
      (algebraMap K (curveE E).functionField c) = algebraMap K (FFClosure (curveE E)) c
    rw [← IsScalarTower.algebraMap_apply]) (show WEq₂ E (xN E) (yN E) from wEq_curveE E)
  exact h

/-- `[F : K(x)] = 2` for the Galois model of `Ē` (curves-jacobian `finrank_hemiCurveData_L`). -/
theorem index_curveGaloisData_H :
    (curveGaloisData K (transcendental_xN E)).H.index = 2 := by
  rw [← fixingSubgroup_F, ← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact finrank_hemiCurveData_L E

/-- `[F k̄ : k̄(x)] = 2`. -/
theorem finrank_F_xF :
    finrank (kbar K (FFClosure (curveE E)))⟮xF E⟯
      (F (Kummer.baseChange (curveGaloisData K (transcendental_xN E)))) = 2 := by
  have h1 := finrank_tF_le_index (Kummer.baseChange (curveGaloisData K (transcendental_xN E)))
  have h2 := index_baseChange_H_le (curveGaloisData K (transcendental_xN E))
    (by rw [index_curveGaloisData_H]; norm_num)
  rw [index_curveGaloisData_H] at h2
  have h3 : finrank (kbar K (FFClosure (curveE E)))⟮xF E⟯
      (F (Kummer.baseChange (curveGaloisData K (transcendental_xN E)))) ≤ 2 :=
    h1.trans (by omega)
  exact EllipticJ.finrank_eq_two_of_le (weq_F E) (transcendental_tF _) h3

variable (N : NFModel (curveGaloisData K (transcendental_xN E)))

/-- `x ∈ F_NF`. -/
abbrev xNF : fnf N := fbcEquiv N (xF E)

/-- `y ∈ F_NF`. -/
abbrev yNF : fnf N := fbcEquiv N (yF E)

/-- `E` over `k̄_NF`. -/
abbrev eNF : WeierstrassCurve (algebraicClosure ℚ (FFClosure (curveE E))) :=
  (E.map (algebraMap K (kbar K (FFClosure (curveE E))))).map
    (kbarQbar K (FFClosure (curveE E))).toRingHom

/-- **The Weierstrass equation in `F_NF`.** -/
theorem weq_fnf : WEq₂ (eNF E) (xNF E N) (yNF E N) :=
  EllipticJ.weq_map (fbcEquiv N).toRingHom (kbarQbar K (FFClosure (curveE E))).toRingHom
    (fbcEquiv_algebraMap N) (weq_F E)

theorem transcendental_xNF : Transcendental (algebraicClosure ℚ (FFClosure (curveE E))) (xNF E N) :=
  transcendental_tr (fbcEquiv N) (kbarQbar K (FFClosure (curveE E))) (fbcEquiv_algebraMap N)
    (transcendental_tF _)

theorem finrank_fnf_xNF :
    finrank (algebraicClosure ℚ (FFClosure (curveE E)))⟮xNF E N⟯ (fnf N) = 2 := by
  rw [finrank_adjoin_tr (fbcEquiv N) (kbarQbar K (FFClosure (curveE E))) (fbcEquiv_algebraMap N)
    (transcendental_tF _)]
  exact finrank_F_xF E

/-- **`F_NF` has genus one.** -/
theorem genus_fnf : genus (algebraicClosure ℚ (FFClosure (curveE E))) (fnf N) = 1 := by
  rw [genus_eq_of_tr (fbcEquiv N) (kbarQbar K (FFClosure (curveE E))) (fbcEquiv_algebraMap N),
    Kummer.genus_baseChange_eq_curveGenus K (transcendental_xN E)]
  exact curveGenus_curveE₂ E

end Elliptic

end Iut.Reconstruction.Thm19
