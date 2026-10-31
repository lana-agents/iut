/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.StageNF
import CurvesJacobian.Cusp.CurveGaloisData
import CurvesJacobian.Galois.ChartOfOpen
import CurvesJacobian.Cusp.DupDecomp

/-!
# [AbsTopIII] Thm 1.9 (d): the stages `(U_X)_{K₁}` of the colimit

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178) takes
`lim→_V H¹(Π_V, μ_Ẑ(Π_U))`, "where `V` ranges over the open subschemes obtained by removing
finite collections of NF-points from `Z ×_{k_Z} k′`, for `k′` a finite extension of `k_Z`".
In the Galois model (`Thm19/NFDirectLimit.lean`) a stage is a finite extension `K₁ ⊇ k` and a
coordinate `t′` of `U_{K₁}`. For the functoriality of the colimit in `Π_U` (item 3 of
`Plans/MR9Plan.md`) the stages must be compared with the arithmetic fundamental groups of the
opens `U_X ⊆ U` defined over `k` (Belyi cuspidalization, [AbsTopII] Cor 3.8) and their extensions
of the field of constants `pr⁻¹(G_{K₁}) ⊆ Π_{U_X}` (curves-jacobian `piRes`). Here:

* (b) **`newData_curveGaloisData`**: changing the coordinate of the Galois model of a curve
  `X` from `τ` to `τ₀` gives the Galois model of `X` with coordinate `τ₀`
  (`newData (curveGaloisData k hτ) (coordT τ₀) = curveGaloisData k hτ₀`), and
  **`stage_eq_constExt_newData`**: a stage with a coordinate `t′ ∈ L` defined over `k` is the
  extension of the field of constants of the open of `t′`
  (`stage D K₁ t′ = constExt K₁ (newData D t′)`);
* `mem_chartRing_iff_of_isAlgebraic`: integrality over `K₁[t′]` and over `k[t′]` agree for
  algebraic `K₁` (every valuation ring of `Ω` containing `k` contains `k̄`);
* (a) **`exists_coord_regular`**, **`exists_stage_ge_coord`**: every stage is dominated by a
  stage with the same `K₁` and a coordinate in `L` (defined over `k`): the stages `(U_X)_{K₁}`
  with `U_X ⊆ U` over `k` are cofinal;
* (c) **`chartOne_le_iff`**: for a curve `X` over `k`, `chartOne τ₀ ⊆ chartOne τ` iff `τ` is
  integral over `k[τ₀]` in `K(X)^alg`, so the order of stages is the inclusion of the opens
  (curves-jacobian `mem_chartOne_iff`: `x ∈ chartOne τ ↔ τ ∈ 𝒪_{X,x}`).
-/

open CategoryTheory AlgebraicGeometry Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  Belyi

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

/-! ### Equality of Galois data -/

section Ext

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

/-- Galois data are determined by `H` and `H_L`. -/
lemma galoisData_ext {D₁ D₂ : GaloisData k t} (hH : D₁.H = D₂.H) (hHL : D₁.HL = D₂.HL) :
    D₁ = D₂ := by
  cases D₁
  cases D₂
  cases hH
  cases hHL
  rfl

end Ext

/-! ### (b) The Galois model of a curve under a change of coordinate -/

section Curve

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [IsFunctionField k X.functionField] {τ τ₀ : X.functionField}
  (hτ : Transcendental k τ) (hτ₀ : Transcendental k τ₀)

/-- Every rational function `τ₀` of `X` lies in the function field `L` of the Galois model. -/
lemma coordT_mem_curveGaloisData_L : coordT τ₀ ∈ (curveGaloisData k hτ).L := by
  rw [curveGaloisData_L]
  exact (mem_imageL_iff _).2 ⟨τ₀, rfl⟩

/-- **The Galois model of a curve does not depend on the coordinate**: changing the coordinate
`τ` of `curveGaloisData k hτ` to `τ₀` (curves-jacobian `newData`) gives `curveGaloisData k hτ₀`
(both have `H = H_L = Gal(K(X)^alg / K(X))`). -/
theorem newData_curveGaloisData [IsGalois (K₀ k (coordT τ)) (FFClosure X)] :
    newData (curveGaloisData k hτ) (coordT_mem_curveGaloisData_L k hτ)
        (transcendental_image hτ₀) = curveGaloisData k hτ₀ := by
  have key : ∀ x : FFClosure X, x ∈ extendK₀ (curveGaloisData k hτ).L
      (coordT_mem_curveGaloisData_L k hτ (τ₀ := τ₀)) ↔ x ∈ imageL (k := k) τ₀ := by
    intro x
    rw [mem_extendK₀, curveGaloisData_L, mem_imageL_iff, mem_imageL_iff]
  have hH : (newData (curveGaloisData k hτ) (coordT_mem_curveGaloisData_L k hτ)
      (transcendental_image hτ₀)).H = (curveGaloisData k hτ₀).H := by
    ext σ
    change σ ∈ (extendK₀ (curveGaloisData k hτ).L _).fixingSubgroup ↔
      σ ∈ (imageL (k := k) τ₀).fixingSubgroup
    simp only [IntermediateField.mem_fixingSubgroup_iff, key]
  exact galoisData_ext hH hH

end Curve

/-! ### (b) Stages with a coordinate over `k` are extensions of the field of constants -/

section StageConst

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K] {t' : Ω}

lemma t_mem_L : t ∈ D.L :=
  D.L.algebraMap_mem ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩

lemma L_le_L_constExt {x : Ω} (hx : x ∈ D.L) : x ∈ (constExt K D).L := by
  rw [mem_L_constExt_iff]
  exact fun σ hσ _ => (IntermediateField.mem_fixedField_iff _ _).1 hx σ hσ

/-- An automorphism of `Ω` over `K(t′)` fixes `L_K` iff it fixes `L` (the function field of
`U_K` is generated by `L` and `K`). -/
lemma fixes_L_constExt_iff (σ : Ω ≃ₐ[K₀ K t'] Ω) :
    (∀ x ∈ (constExt K D).L, σ x = x) ↔ ∀ x ∈ D.L, σ x = x := by
  constructor
  · exact fun h x hx => h x (L_le_L_constExt D K hx)
  · intro h x hx
    rw [mem_L_constExt_iff] at hx
    have hK : ∀ c : K, σ (algebraMap K Ω c) = algebraMap K Ω c := fun c =>
      σ.commutes ⟨_, (K₀ K t').algebraMap_mem c⟩
    obtain ⟨σ₀, hσ₀⟩ := exists_algEquiv_K₀ (E := k) (t' := t) σ.toRingEquiv
      (fun c => by
        change σ (algebraMap k Ω c) = algebraMap k Ω c
        rw [IsScalarTower.algebraMap_apply k K Ω]
        exact hK _)
      (h t (t_mem_L D))
    have hmem : σ₀ ∈ D.HL := by
      rw [← D.fixingSubgroup_L, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      rw [hσ₀]
      exact h y hy
    have := hx σ₀ hmem fun c => by rw [hσ₀]; exact hK c
    rwa [hσ₀] at this

variable (ht' : t' ∈ (constExt K D).L) (htr' : Transcendental K t') (ht'₀ : t' ∈ D.L)
  (htr'₀ : Transcendental k t')

/-- **A stage with a coordinate defined over `k` is an extension of the field of constants**:
for `t′ ∈ L`,
the open `V ⊆ U_K` of `t′` is `(U_X)_K` for the open `U_X ⊆ U` of `t′`
(`stage D K t′ = constExt K (newData D t′)`). -/
theorem stage_eq_constExt_newData [IsGalois (K₀ k t') Ω] :
    stage D K ht' htr' = constExt K (newData D ht'₀ htr'₀) := by
  have hH : (stage D K ht' htr').H = (constExt K (newData D ht'₀ htr'₀)).H := by
    ext σ
    rw [mem_constExt_H]
    change σ ∈ (extendK₀ (constExt K D).L ht').fixingSubgroup ↔
      resK k K t' σ ∈ (extendK₀ D.L ht'₀).fixingSubgroup
    simp only [IntermediateField.mem_fixingSubgroup_iff, mem_extendK₀, resK_apply]
    exact fixes_L_constExt_iff D K σ
  refine galoisData_ext hH ?_
  ext σ
  rw [mem_constExt_HL]
  exact (SetLike.ext_iff.1 hH σ).trans (mem_constExt_H _)

end StageConst

/-! ### Chart rings over algebraic extensions -/

section ChartRing

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

/-- A valuation subring of `Ω` containing `k` contains every algebraic extension `K ⊆ Ω`. -/
lemma algebraMap_mem_of_isAlgebraic (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K]
    {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W) (c : K) :
    algebraMap K Ω c ∈ W :=
  KummerTheory.Curve.mem_of_isIntegral hk
    ((Algebra.IsAlgebraic.isAlgebraic c).algebraMap (A := Ω)).isIntegral

/-- **Integrality over `K[t′]` and over `k[t′]` agree** for algebraic `K`. -/
lemma mem_chartRing_iff_of_isAlgebraic (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K]
    {x s : Ω} : x ∈ chartRing K s ↔ x ∈ chartRing k s := by
  constructor
  · intro hx
    exact mem_chartRing_of_forall fun W hk hs =>
      mem_of_mem_chartRing W (algebraMap_mem_of_isAlgebraic K hk) hs hx
  · intro hx
    exact mem_chartRing_of_forall fun W hK hs =>
      mem_of_mem_chartRing W (fun c => by
        rw [IsScalarTower.algebraMap_apply k K Ω]
        exact hK _) hs hx

end ChartRing

/-! ### (a) Cofinality of the stages with a coordinate over `k` -/

section Cofinal

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

/-- An element of `Ω` all of whose valuation rings `W ⊇ k` are integrally closed: an element
integral over `W` lies in `W`. -/
lemma mem_of_isIntegral_valuationSubring (W : ValuationSubring Ω) {x : Ω}
    (hx : IsIntegral W x) : x ∈ W := by
  have : IsIntegrallyClosedIn W.toSubring Ω := inferInstanceAs (IsIntegrallyClosedIn W Ω)
  obtain ⟨y, hy⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hx
  rw [← hy]
  exact y.2

/-- **A coordinate regular wherever finitely many functions are**: for a finite list of
elements of the function field there is a coordinate `z ∈ F`, transcendental over `k`, such
that `t` and all the elements of the list are regular on the open of `z`. -/
theorem exists_coord_regular (l : List (F D)) :
    ∃ z : F D, Transcendental k (z : Ω) ∧ ∀ W : ValuationSubring Ω,
      (∀ c : k, algebraMap k Ω c ∈ W) → (z : Ω) ∈ W → t ∈ W ∧ ∀ a ∈ l, (a : Ω) ∈ W := by
  induction l with
  | nil =>
    exact ⟨tF D, D.transcendental, fun W _ hz => ⟨hz, fun a ha => by simp at ha⟩⟩
  | cons a l ih =>
    obtain ⟨z, -, hz⟩ := ih
    obtain ⟨c, hc⟩ := exists_smul_add_mem_imp D z a
    set z' : F D := z + algebraMap k (F D) c * a
    have key : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → (z' : Ω) ∈ W →
        t ∈ W ∧ ∀ b ∈ a :: l, (b : Ω) ∈ W := by
      intro W hk hW
      obtain ⟨h1, h2⟩ := hc W hk hW
      obtain ⟨ht, hl⟩ := hz W hk h1
      refine ⟨ht, fun b hb => ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · exact h2
      · exact hl b hb
    refine ⟨z', fun halg => D.transcendental ?_, key⟩
    have hall : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → t ∈ W :=
      fun W hk => (key W hk (KummerTheory.Curve.mem_of_isIntegral hk halg.isIntegral)).1
    have hmem : t ∈ (integralClosure k Ω).toSubring := by
      rw [Subring.eq_iInf_of_isIntegrallyClosedIn (R := (integralClosure k Ω).toSubring),
        Subring.mem_iInf]
      intro V
      exact hall V.1 fun c => V.2 (Subalgebra.algebraMap_mem _ c)
    exact ((mem_integralClosure_iff k Ω).1 hmem).isAlgebraic

/-- An element `x ∈ Ω` lies in every valuation ring `W` containing the coefficients of its
minimal polynomial over `L` (valuation rings are integrally closed). -/
lemma mem_of_coeffs_mem (x : Ω) (W : ValuationSubring Ω)
    (hW : ∀ n, ((minpoly D.L x).coeff n : Ω) ∈ W) : x ∈ W := by
  have hint : IsIntegral D.L x := (Algebra.IsIntegral.isIntegral (R := K₀ k t) x).tower_top
  set p : Polynomial Ω := (minpoly D.L x).map (algebraMap D.L Ω)
  have hp : p.Monic := (minpoly.monic hint).map _
  have hcoeff : (p.coeffs : Set Ω) ⊆ W.toSubring := by
    intro c hc
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hc
    rw [Polynomial.coeff_map]
    exact hW n
  have hint' : IsIntegral W.toSubring x := by
    refine ⟨p.toSubring W.toSubring hcoeff, (p.monic_toSubring _ _).2 hp, ?_⟩
    rw [← Polynomial.eval_map]
    change ((p.toSubring W.toSubring hcoeff).map W.toSubring.subtype).eval x = 0
    rw [Polynomial.map_toSubring, Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval]
  have : IsIntegrallyClosedIn W.toSubring Ω := inferInstanceAs (IsIntegrallyClosedIn W Ω)
  obtain ⟨y, hy⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hint'
  rw [← hy]
  exact y.2

/-- **Cofinality of the stages with a coordinate over `k`** ((a) of item 3): every stage
`(K, t′)` is dominated by a stage `(K, z)` with `z ∈ L`, i.e. by the extension of the field of
constants
`(U_X)_K` of an open `U_X ⊆ U` defined over `k` (`stage_eq_constExt_newData`). The coordinate
`z` is chosen regular wherever `t` and the coefficients of the minimal polynomial of `t′` over
`L` are (`exists_coord_regular`). -/
theorem exists_stage_ge_coord [hH : Fact (D.H ≤ D.HL)] (s : StageIdx D) :
    ∃ s' : StageIdx D, s ≤ s' ∧ s'.K = s.K ∧ s'.t' ∈ D.L := by
  have hLF : ∀ x : Ω, x ∈ D.L → x ∈ F D := fun x hx => by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun σ hσ => (IntermediateField.mem_fixedField_iff _ _).1 hx σ (hH.out hσ)
  set q := minpoly D.L s.t'
  let l : List (F D) := (List.range (q.natDegree + 1)).map fun n =>
    ⟨((q.coeff n : D.L) : Ω), hLF _ (q.coeff n).2⟩
  obtain ⟨z, hztr, hz⟩ := exists_coord_regular D l
  have hreg : ∀ W : ValuationSubring Ω, (∀ c : s.K, algebraMap s.K Ω c ∈ W) → (z : Ω) ∈ W →
      t ∈ W ∧ s.t' ∈ W := by
    intro W hK hzW
    have hk : ∀ c : k, algebraMap k Ω c ∈ W := fun c => by
      rw [IsScalarTower.algebraMap_apply k s.K Ω]
      exact hK _
    obtain ⟨ht, hl⟩ := hz W hk hzW
    refine ⟨ht, mem_of_coeffs_mem D s.t' W fun n => ?_⟩
    by_cases hn : n ≤ q.natDegree
    · exact hl _ (List.mem_map.2 ⟨n, List.mem_range.2 (by omega), rfl⟩)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := q) (by omega)]
      exact W.zero_mem
  have hzL : (z : Ω) ∈ D.L := mem_L_of_mem_F_shrink D z.2
  exact ⟨⟨s.K, z, L_le_L_constExt D s.K hzL, Transcendental.extendScalars s.K hztr,
    mem_chartRing_of_forall fun W hK hW => (hreg W hK hW).1⟩,
    ⟨le_rfl, mem_chartRing_of_forall fun W hK hW => (hreg W hK hW).2⟩, rfl, hzL⟩

end Cofinal

/-! ### (c) The order of the stages is the inclusion of the opens -/

section ChartOne

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X]

/-- **`chartOne τ₀ ⊆ chartOne τ` iff `τ` is integral over `k[τ₀]`** (in `K(X)^alg`): the
order of the stages `t ∈ chartRing k t₀` is the inclusion of the opens of the coordinates
(curves-jacobian `mem_chartOne_iff`: `x ∈ chartOne τ ↔ τ ∈ 𝒪_{X,x}`; the points of `X` other
than the generic point are the places of `K(X)/k`, `curvePlaceEquiv`). -/
theorem chartOne_le_iff {τ τ₀ : X.functionField} (hτ : Transcendental k τ)
    (hτ₀ : Transcendental k τ₀) :
    chartOne k X τ₀ ≤ chartOne k X τ ↔ coordT τ ∈ chartRing k (coordT τ₀) := by
  constructor
  · intro hle
    refine mem_chartRing_of_forall fun W hk hW => ?_
    set O := W.comap (algebraMap X.functionField (FFClosure X))
    have hkO : ∀ c : k, algebraMap k X.functionField c ∈ O := fun c => by
      change algebraMap X.functionField (FFClosure X) (algebraMap k X.functionField c) ∈ W
      rw [← IsScalarTower.algebraMap_apply]
      exact hk c
    change τ ∈ O
    by_cases hO : O = ⊤
    · rw [hO]
      trivial
    · obtain ⟨x, hx⟩ := (curvePlaceEquiv k X).surjective ⟨O, hO, hkO⟩
      have h1 : (curvePlaceEquiv k X x).1 = O := congrArg Subtype.val hx
      rw [curvePlaceEquiv_apply] at h1
      have hτ₀x : τ₀ ∈ stalkVS k x.1 := by
        change τ₀ ∈ stalkValuationSubring (valuationRing_stalk_of_isCurveOver k X) x.1
        rw [h1]
        exact hW
      have := (mem_chartOne_iff k hτ x.1).1 (hle ((mem_chartOne_iff k hτ₀ x.1).2 hτ₀x))
      change τ ∈ stalkValuationSubring (valuationRing_stalk_of_isCurveOver k X) x.1 at this
      rwa [h1] at this
  · intro h x hx
    rw [mem_chartOne_iff k hτ₀] at hx
    rw [mem_chartOne_iff k hτ]
    obtain ⟨W, hW⟩ := exists_valuationSubring_comap_eq₂
      (algebraMap X.functionField (FFClosure X)) (stalkVS k x)
    have hk : ∀ c : k, algebraMap k (FFClosure X) c ∈ W := fun c => by
      rw [IsScalarTower.algebraMap_apply k X.functionField (FFClosure X)]
      change algebraMap k X.functionField c ∈ W.comap (algebraMap X.functionField (FFClosure X))
      rw [hW]
      exact algebraMap_mem_stalkValuationSubring k _ x c
    have h0 : coordT τ₀ ∈ W := by
      change τ₀ ∈ W.comap (algebraMap X.functionField (FFClosure X))
      rw [hW]
      exact hx
    have := mem_of_mem_chartRing W hk h0 h
    change τ ∈ W.comap (algebraMap X.functionField (FFClosure X)) at this
    rwa [hW] at this

end ChartOne

end Iut.Reconstruction.Thm19
