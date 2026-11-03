/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.GalConjStage
import Iut.Reconstruction.Thm19.RecTripleIso

/-!
# Galois equivariance of `nfRingEquiv` on the field of constants (MR9, `CKSemiAbsConj` item 3)

[AbsTopIII] Thm 1.9 (`Topics in Absolute Anabelian Geometry III.txt` l.2109–2199) reconstructs
`k̄_NF ⊆ K^×_{Z_NF} ↪ lim→_V H¹(Π_V, μ_Ẑ(Π_U))` together with the action of `Π_U` (through
`G_k`), functorially in `Π_U`. For the isomorphism `nfRingEquiv` induced by `Φ : Π_U ≃ Π_{U'}`
over `ψ = gkIso Φ : G_K ≃ G_{K'}` this means: on the algebraic numbers `σ := nfRingEquiv|_{ℚ̄}`
satisfies `σ(g c) = ψ(g) σ(c)`. Here:

* `exists_resG_eq_of_ofG_eq`: equal classes in the colimit agree at a common later stage;
* `GStage.exists_fieldOf`: every stage and algebraic number lie below a stage whose field of
  constants is `fieldOf N`, `N ⊆ G_k` open and normal (Galois over `k`);
* `kummerNF_eq_ofG_const`: the Kummer class of an algebraic number at a stage containing it;
* **`ofG_stageConj_eq`**: for `a` fixing `F` and restricting to an element of `G_k`, a class `w` at
  a stage `g` (`a(K₁) ⊆ K₁`) with `[g, w] = κ(c)`, `c` algebraic, has `[g, a_* w] = κ(a(c))`
  (go to a later Galois stage, `resT_conjPiH1`, `conjPiH1_kummerMapZHat`);
* `constFnf`: an algebraic number as an NF-rational function; **`nfConst`**: `nfRingEquiv` on the
  algebraic numbers `k̄ → k̄'`;
* **`nfConst_galois`**: `σ(g c) = ψ(g) σ(c)` for `g ∈ G_K` and `c ∈ k̄` (a lift of `g` to `Π_U`
  and its image under `Φ`; `h1Congr_stageConj` along the lift data of the stage).
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

open GStage

/-- Equal classes in a direct limit agree at a common later index. -/
lemma directLimit_exact {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {G : ι → Type*}
    {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ i j (h : i ≤ j), T h}
    [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)] {i j : ι}
    {x : G i} {y : G j} (h : (⟦⟨i, x⟩⟧ : DirectLimit G f) = ⟦⟨j, y⟩⟧) :
    ∃ (l : ι) (hi : i ≤ l) (hj : j ≤ l), f i l hi x = f j l hj y :=
  Quotient.exact h

/-! ### One curve: the colimit, Galois stages and constants -/

section One

variable {k : Type u} [Field k] [CharZero k] [NumberField k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X] {τ : X.functionField}
  {hτ : Transcendental k τ} [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)]
  [IsAlgClosed (FFClosure X)]

omit [NumberField k] [CharZero (FFClosure X)] in
lemma resT_three {s : StageIdx (curveGaloisData k hτ)} {g g'' : GStage k hτ}
    (h₁ : g.toStage ≤ s) (h₂ : s ≤ g''.toStage) (hg : g ≤ g'') (y : H1G g) :
    resT s.data g''.data (F_le_of_le_toStage h₂) (hW_le h₂) (stage_H_le _ s.K s.ht' s.htr')
      (resS h₁ (resT g.data g.toStage.data (F_toStage g) (fun _ hK ht => ⟨hK, ht⟩)
        g.data_H_le y)) = resG hg y := by
  have e1 : resS h₁ (resT g.data g.toStage.data (F_toStage g) (fun _ hK ht => ⟨hK, ht⟩)
      g.data_H_le y) = resT g.data s.data _ _ g.data_H_le y := resT_trans _ _ _ _ _ _ y
  have e2 : resT s.data g''.data (F_le_of_le_toStage h₂) (hW_le h₂)
      (stage_H_le _ s.K s.ht' s.htr') (resT g.data s.data (fun z hz =>
        Thm19.F_le h₁ z (F_toStage g z hz)) (fun W hK ht =>
          ⟨(hW_le h₁ W hK ht).1, (hW_le h₁ W hK ht).2⟩) g.data_H_le y) =
      resT g.data g''.data _ _ g.data_H_le y := resT_trans _ _ _ _ _ _ y
  exact (congrArg _ e1).trans e2

set_option maxHeartbeats 800000 in
-- the transition maps of three stages unify slowly
omit [NumberField k] [CharZero (FFClosure X)] in
/-- **Equal classes in the colimit agree at a common later stage.** -/
theorem exists_resG_eq_of_ofG_eq {g g' : GStage k hτ} {y : H1G g} {y' : H1G g'}
    (h : ofG g y = ofG g' y') :
    ∃ (g'' : GStage k hτ) (h₁ : g ≤ g'') (h₂ : g' ≤ g''), resG h₁ y = resG h₂ y' := by
  obtain ⟨s, hs₁, hs₂, e⟩ :=
    directLimit_exact (f := fun _ _ h => resS (D := curveGaloisData k hτ) h) h
  obtain ⟨g'', hg''⟩ := GStage.exists_ge_toStage s
  have h₁ : g ≤ g'' := toStage_le_iff.1 (hs₁.trans hg'')
  have h₂ : g' ≤ g'' := toStage_le_iff.1 (hs₂.trans hg'')
  exact ⟨g'', h₁, h₂, (resT_three hs₁ hg'' h₁ y).symm.trans
    ((congrArg _ e).trans (resT_three hs₂ hg'' h₂ y'))⟩

omit [NumberField k] [IsCurveOver k X] [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  [CharZero (FFClosure X)] in
/-- **Galois stages are cofinal**: `g` and an algebraic `x` lie below a stage with field of
constants `fieldOf N`, `N ⊆ G_k` open and normal. -/
theorem GStage.exists_fieldOf (g : GStage k hτ) (x : FFClosure X) (hx : IsAlgebraic k x) :
    ∃ N : Subgroup (Gk k (FFClosure X)), N.Normal ∧ IsOpen (N : Set (Gk k (FFClosure X))) ∧
      (∀ y ∈ g.K, y ∈ fieldOf N) ∧ x ∈ fieldOf N := by
  let x' : kbar k (FFClosure X) := ⟨x, mem_algebraicClosure_iff.2 hx⟩
  let O : Subgroup (Gk k (FFClosure X)) := gkFix g.K ⊓ MulAction.stabilizer _ x'
  have hO : IsOpen (O : Set (Gk k (FFClosure X))) :=
    (isOpen_gkFix g.K).inter (stabilizer_isOpen_of_isIntegral (x' : kbar k (FFClosure X)))
  obtain ⟨E, hEf, hEn, hEO⟩ := (krullTopology_mem_nhds_one_iff_of_normal k
    (kbar k (FFClosure X)) (O : Set (Gk k (FFClosure X)))).1 (hO.mem_nhds O.one_mem)
  haveI : IsGalois k E := isGalois_iff.2 ⟨inferInstance, hEn⟩
  refine ⟨E.fixingSubgroup, (InfiniteGalois.normal_iff_isGalois E).2 inferInstance,
    IntermediateField.fixingSubgroup_isOpen E, fun y hy => ?_, ?_⟩
  · have hya : IsAlgebraic k y := by
      have h1 : IsAlgebraic k (⟨y, hy⟩ : g.K) := Algebra.IsAlgebraic.isAlgebraic _
      exact (isAlgebraic_algHom_iff (g.K.val) g.K.val.injective).2 h1
    refine ⟨⟨y, mem_algebraicClosure_iff.2 hya⟩, fun n => ?_, rfl⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hEO n.2).1 _ hy
  · refine ⟨x', fun n => ?_, rfl⟩
    exact (hEO n.2).2

/-- The stage `(fieldOf N, τ₀)` above `g`. -/
abbrev GStage.ofField (g : GStage k hτ) (N : Subgroup (Gk k (FFClosure X)))
    (hN : IsOpen (N : Set (Gk k (FFClosure X)))) : GStage k hτ :=
  haveI := finiteDimensional_fieldOf hN
  ⟨fieldOf N, g.τ₀, g.hτ₀, g.htV⟩

omit [NumberField k] [IsCurveOver k X] [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  [CharZero (FFClosure X)] in
lemma GStage.le_ofField (g : GStage k hτ) (N : Subgroup (Gk k (FFClosure X)))
    (hN : IsOpen (N : Set (Gk k (FFClosure X)))) (hK : ∀ y ∈ g.K, y ∈ fieldOf N) :
    g ≤ g.ofField N hN :=
  ⟨fun y hy => hK y hy, self_mem_chartRing k _⟩

omit [NumberField k] [CharZero (FFClosure X)] in
lemma resG_kummerMapZHat {g g' : GStage k hτ} (h : g ≤ g') (u : units g.data) :
    resG h (kummerMapZHat g.data u) =
      kummerMapZHat g'.data (unitsT g.data g'.data (F_mono h) (hW_mono h) u) :=
  resT_kummerMapZHat _ _ _ _ _ u

omit [NumberField k] [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)]
  [IsAlgClosed (FFClosure X)] in
lemma resG_resG' {g₁ g₂ g₃ : GStage k hτ} (h₁₂ : g₁ ≤ g₂) (h₂₃ : g₂ ≤ g₃) (y : H1G g₁) :
    resG h₂₃ (resG h₁₂ y) = resG (h₁₂.trans h₂₃) y :=
  resT_resT y

/-- **The Kummer class of an algebraic number** at a stage containing it. -/
lemma kummerNF_eq_ofG_const (N : NFModel (curveGaloisData k hτ)) (g : GStage k hτ) (c : g.Kˣ)
    (f : (fnf N)ˣ) (hf : ((f : fnf N) : FFClosure X) = algebraMap g.K (FFClosure X) c) :
    kummerNF N (mem_range_of_isAlgebraic_F k hτ) f =
      ofG g (kummerMapZHat g.data (constUnit g.data c)) :=
  (ofG_kummerMapZHat N g _ f hf.symm).symm

variable (a : FFClosure X ≃+* FFClosure X) (hfix : ∀ x ∈ F (curveGaloisData k hτ), a x = x)

omit [NumberField k] [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)]
  [IsAlgClosed (FFClosure X)] in
include hfix in
lemma fix_of_fix (g : GStage k hτ) : ∀ x ∈ F (curveGaloisData k g.hτ₀), a x = x :=
  fun _ hx => hfix _ ((mem_F_curveGaloisData_iff hτ).2 ((mem_F_curveGaloisData_iff g.hτ₀).1 hx))

/-- Conjugation by `a` at a geometric stage with `a(K₁) ⊆ K₁`. -/
abbrev GStage.conj (g : GStage k hτ) (hgK : ∀ x ∈ g.K, a x ∈ g.K) : H1G g →* H1G g :=
  stageConj (curveGaloisData k g.hτ₀) g.K a (fix_of_fix a hfix g) hgK
    (curveGaloisData_H_le k g.hτ₀)

set_option maxHeartbeats 1600000 in
-- the transition maps and the conjugations at two stages unify slowly
omit [NumberField k] [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)]
  [IsAlgClosed (FFClosure X)] in
/-- Conjugation commutes with the transition maps of geometric stages. -/
lemma resG_conj {g g' : GStage k hτ} (h : g ≤ g') (hgK : ∀ x ∈ g.K, a x ∈ g.K)
    (hgK' : ∀ x ∈ g'.K, a x ∈ g'.K) (y : H1G g) :
    resG h (g.conj a hfix hgK y) = g'.conj a hfix hgK' (resG h y) :=
  resT_conjPiH1 a y

set_option maxHeartbeats 1600000 in
-- the Kummer classes at the stages unify slowly
/-- **Conjugation of a class equal to the Kummer class of an algebraic number.** For `a` fixing `F` and
restricting to `h ∈ G_k` on `k̄`, a class `w` at a stage `g` with `a(K₁) ⊆ K₁` and `[g, w] = κ(c)`
for an algebraic number `c` satisfies `[g, a_* w] = κ(a(c))`. -/
theorem ofG_stageConj_eq (N : NFModel (curveGaloisData k hτ)) (h : Gk k (FFClosure X))
    (hag : ∀ y : kbar k (FFClosure X), a y = h y) (g : GStage k hτ) (hgK : ∀ x ∈ g.K, a x ∈ g.K)
    (w : H1G g) (f f' : (fnf N)ˣ) (hc : IsAlgebraic k ((f : fnf N) : FFClosure X))
    (hf' : ((f' : fnf N) : FFClosure X) = a ((f : fnf N) : FFClosure X))
    (hw : ofG g w = kummerNF N (mem_range_of_isAlgebraic_F k hτ) f) :
    ofG g (g.conj a hfix hgK w) = kummerNF N (mem_range_of_isAlgebraic_F k hτ) f' := by
  obtain ⟨g₂, hle₂, hf₂⟩ : ∃ g₂ : GStage k hτ, g ≤ g₂ ∧ ((f : fnf N) : FFClosure X) ∈ g₂.K := by
    obtain ⟨N₂, -, hN₂o, hN₂K, hN₂f⟩ := g.exists_fieldOf _ hc
    exact ⟨g.ofField N₂ hN₂o, g.le_ofField N₂ hN₂o hN₂K, hN₂f⟩
  let c₂ : g₂.Kˣ := Units.mk0 ⟨_, hf₂⟩ (fun h0 => f.ne_zero (Subtype.ext
    (congrArg Subtype.val h0 :)))
  have hw₂ : ofG g w = ofG g₂ (kummerMapZHat g₂.data (constUnit _ c₂)) :=
    hw.trans (kummerNF_eq_ofG_const N _ c₂ f rfl)
  obtain ⟨g₃, h₁, h₂, e₃⟩ := exists_resG_eq_of_ofG_eq hw₂
  obtain ⟨g₄, hle₄, hg₄K⟩ : ∃ g₄ : GStage k hτ, g₃ ≤ g₄ ∧ ∀ x ∈ g₄.K, a x ∈ g₄.K := by
    obtain ⟨N₄, hN₄n, hN₄o, hN₄K, -⟩ := g₃.exists_fieldOf _ hc
    exact ⟨g₃.ofField N₄ hN₄o, g₃.le_ofField N₄ hN₄o hN₄K,
      fun x hx => mem_fieldOf_conj N₄ a h hag hx⟩
  -- at `g₄`, the class `w` is the Kummer class of `f`
  have e₄ : resG (h₁.trans hle₄) w =
      kummerMapZHat g₄.data (unitsT _ _ (F_mono (h₂.trans hle₄)) (hW_mono (h₂.trans hle₄))
        (constUnit _ c₂)) :=
    (resG_resG' h₁ hle₄ w).symm.trans ((congrArg (resG hle₄) e₃).trans
      ((resG_resG' h₂ hle₄ _).trans (resG_kummerMapZHat (h₂.trans hle₄) _)))
  have hfK : ((f : fnf N) : FFClosure X) ∈ g₄.K := hle₄.1 (h₂.1 hf₂)
  let c₄' : g₄.Kˣ := Units.mk0 ⟨_, hg₄K _ hfK⟩ (fun h0 => f'.ne_zero (Subtype.ext (by
    rw [hf']
    exact congrArg Subtype.val h0)))
  have hconj : g₄.conj a hfix hg₄K (resG (h₁.trans hle₄) w) =
      kummerMapZHat g₄.data (constUnit _ c₄') := by
    rw [e₄]
    exact conjPiH1_kummerMapZHat _ _ _ _ _ _ _ _ (by rw [coe_unitsT]; rfl)
  exact (ofG_compat g g₄ (h₁.trans hle₄) _).trans ((congrArg (ofG g₄)
    ((resG_conj a hfix _ hgK hg₄K w).trans hconj)).trans
      (kummerNF_eq_ofG_const N g₄ c₄' f' hf').symm)

end One

/-! ### The algebraic numbers along `nfRingEquiv` -/

/-- An element algebraic over a number field is algebraic over `ℚ`. -/
lemma isAlgebraic_rat_of_isAlgebraic {K L : Type*} [Field K] [NumberField K] [Field L]
    [Algebra K L] [CharZero L] {y : L} (hy : IsAlgebraic K y) : IsAlgebraic ℚ y :=
  hy.restrictScalars ℚ

end Iut.Reconstruction.Thm19

namespace Iut.Reconstruction

open Thm19

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

/-- An element of `k̄` as an NF-rational function (`k̄ = ℚ̄ ⊆ F_NF`, `k` a number field). -/
def constFnf {k : Type u} [Field k] [NumberField k] {Ω' : Type u} [Field Ω'] [Algebra k Ω']
    {t : Ω'} {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω'] [CharZero Ω']
    (M : NFModel D) (y : kbar k Ω') : fnf M :=
  ⟨y, M.algebraic_mem _ (isAlgebraic_rat_of_isAlgebraic (mem_algebraicClosure_iff.1 y.2))⟩

@[simp] lemma coe_constFnf {k : Type u} [Field k] [NumberField k] {Ω' : Type u} [Field Ω']
    [Algebra k Ω'] {t : Ω'} {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω']
    [CharZero Ω'] (M : NFModel D) (y : kbar k Ω') : ((constFnf M y : fnf M) : Ω') = y := rfl

/-- A ring homomorphism of fields of characteristic `0` maps algebraic numbers to algebraic
numbers. -/
lemma isAlgebraic_rat_map {A B : Type*} [Field A] [Field B] [CharZero A] [CharZero B]
    (φ : A →+* B) {x : A} (hx : IsAlgebraic ℚ x) : IsAlgebraic ℚ (φ x) :=
  hx.algHom φ.toRatAlgHom

variable (hτ hU hτ₂ hU₂ Φ) in
/-- **`σ`: `nfRingEquiv` on the algebraic numbers**, `k̄ → k̄'`. -/
def nfConst (y : kbar K (FFClosure C.Xbar)) : kbar K₂ (FFClosure C₂.Xbar) :=
  ⟨(nfRingEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ (constFnf N y) :
      FFClosure C₂.Xbar),
    mem_kbar_of_isAlgebraic (isAlgebraic_rat_map (algebraMap (fnf N₂) (FFClosure C₂.Xbar))
      (isAlgebraic_rat_map (nfRingEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N
        N₂).toRingHom ((isAlgebraic_algHom_iff ((fnf N).val.restrictScalars ℚ)
          (fnf N).val.injective).1
            (isAlgebraic_rat_of_isAlgebraic (mem_algebraicClosure_iff.1 y.2)))))⟩

lemma coe_nfConst (y : kbar K (FFClosure C.Xbar)) :
    ((nfConst hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ y :
      kbar K₂ (FFClosure C₂.Xbar)) : FFClosure C₂.Xbar) =
      (nfRingEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ (constFnf N y) :
        FFClosure C₂.Xbar) := rfl

lemma nfConst_zero :
    nfConst hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ 0 = 0 := by
  apply Subtype.ext
  rw [coe_nfConst, show constFnf N (0 : kbar K (FFClosure C.Xbar)) = 0 from rfl, map_zero]
  rfl

set_option maxHeartbeats 3200000 in
-- the lift data, the stages and the colimits unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- **Galois equivariance of `nfRingEquiv` on the algebraic numbers** (MR9, `CKSemiAbsConj`
items 3–4): `σ(g c) = ψ(g) σ(c)` for `g ∈ G_K`, `c ∈ k̄`, `σ = nfConst`, `ψ = gkIso Φ`. A lift
`a` of `g` to `Π_U` acts on the Kummer classes of the constants of a Galois stage `g₁ ∋ c`
(`ofG_stageConj_eq`); the stage isomorphism of the lift data of `g₁` intertwines it with
conjugation by a lift `a₂` of `Φ(a)` (`h1Congr_stageConj`), which acts on the constants of the
target as `ψ(g)` (`ofG_stageConj_eq` again); `kummerNF` is injective. -/
theorem nfConst_galois (gal : Gk K (FFClosure C.Xbar)) (y : kbar K (FFClosure C.Xbar)) :
    nfConst hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ (gal y) =
      gkIso hτ hU hτ₂ hU₂ Φ gal
        (nfConst hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ y) := by
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, nfConst_zero, map_zero]
  -- a lift `a` of `gal` to `Π_U`
  obtain ⟨γ, hγ⟩ := piToGk_surjective_curve hτ gal
  obtain ⟨ã, rfl⟩ := QuotientGroup.mk_surjective γ
  let a : FFClosure C.Xbar ≃+* FFClosure C.Xbar :=
    (ã : FFClosure C.Xbar ≃ₐ[K₀ K (coordT τ)] FFClosure C.Xbar).toRingEquiv
  have hfix : ∀ x ∈ F (curveGaloisData K hτ), a x = x := fun x hx => fixes_of_mem_F ã.2 ⟨x, hx⟩
  have hag : ∀ z : kbar K (FFClosure C.Xbar), a z = gal z := fun z => by
    rw [← hγ, piToGk_mk]
    exact (algebraMap_hToGk_apply _ ã z).symm
  -- the source stage `g₁ = (fieldOf N₁, τ)`, `y ∈ fieldOf N₁`
  have hya : IsAlgebraic K (y : FFClosure C.Xbar) := mem_algebraicClosure_iff.1 y.2
  obtain ⟨N₁, hN₁n, hN₁o, -, hyN₁⟩ :=
    (⟨⊥, τ, hτ, self_mem_chartRing K _⟩ : GStage K hτ).exists_fieldOf _ hya
  let g₁ : GStage K hτ := (⟨⊥, τ, hτ, self_mem_chartRing K _⟩ : GStage K hτ).ofField N₁ hN₁o
  haveI : FiniteDimensional K g₁.K := finiteDimensional_fieldOf hN₁o
  have hg₁K : ∀ x ∈ g₁.K, a x ∈ g₁.K := fun x hx => mem_fieldOf_conj N₁ a gal hag hx
  have hy0 : (y : FFClosure C.Xbar) ≠ 0 := fun h0 => hy (Subtype.ext h0)
  let c₁ : g₁.Kˣ := Units.mk0 ⟨y, hyN₁⟩ fun h0 => hy0 (congrArg Subtype.val h0 :)
  let f : (fnf N)ˣ := Units.mk0 (constFnf N y) fun h0 => hy0 (congrArg Subtype.val h0 :)
  let f' : (fnf N)ˣ := Units.mk0 (constFnf N (gal y)) fun h0 => hy0 (by
    have h1 : ((gal y : kbar K (FFClosure C.Xbar)) : FFClosure C.Xbar) = 0 :=
      congrArg Subtype.val h0
    have h2 : gal y = 0 := Subtype.ext h1
    rw [map_eq_zero_iff _ gal.injective] at h2
    exact congrArg Subtype.val h2)
  let w₁ : H1G g₁ := kummerMapZHat g₁.data (constUnit _ c₁)
  have hw₁ : ofG g₁ w₁ = kummerNF N (mem_range_of_isAlgebraic_F K hτ) f :=
    (kummerNF_eq_ofG_const N g₁ c₁ f rfl).symm
  have hsrc : ofG g₁ (g₁.conj a hfix hg₁K w₁) = kummerNF N (mem_range_of_isAlgebraic_F K hτ) f' :=
    ofG_stageConj_eq a hfix N gal hag g₁ hg₁K w₁ f f' hya (hag y).symm hw₁
  -- the lift data of `g₁` and a lift `a₂` of `Φ(a)`
  obtain ⟨L, hL⟩ : ∃ L : LiftData hτ hU hτ₂ hU₂ Φ g₁,
      L = LiftData.choose (hτ := hτ) (hU := hU) (hτ₂ := hτ₂) (hU₂ := hU₂) Φ hS g₁ := ⟨_, rfl⟩
  obtain ⟨ã₂, hã₂⟩ := QuotientGroup.mk_surjective
    (L.e ((ã : Pi (curveGaloisData K hτ))))
  let a₂ : FFClosure C₂.Xbar ≃+* FFClosure C₂.Xbar :=
    (ã₂ : FFClosure C₂.Xbar ≃ₐ[K₀ K₂ (coordT L.υ)] FFClosure C₂.Xbar).toRingEquiv
  have hfix₂ : ∀ x ∈ F (curveGaloisData K₂ L.hυ), a₂ x = x := fun x hx =>
    fixes_of_mem_F ã₂.2 ⟨x, hx⟩
  have hfix₂' : ∀ x ∈ F (curveGaloisData K₂ hτ₂), a₂ x = x := fun x hx =>
    hfix₂ x ((mem_F_curveGaloisData_iff L.hυ).2 ((mem_F_curveGaloisData_iff hτ₂).1 hx))
  have hag₂ : ∀ z : kbar K₂ (FFClosure C₂.Xbar), a₂ z = gkIso hτ hU hτ₂ hU₂ Φ gal z := fun z => by
    have e1 := L.he_gk (ã : Pi (curveGaloisData K hτ))
    rw [← hã₂, piToGk_mk, piToGk_mk] at e1
    have e2 : hToGk (curveGaloisData K hτ) ã = gal := by rw [← hγ, piToGk_mk]
    rw [e2] at e1
    rw [← e1]
    exact (algebraMap_hToGk_apply _ ã₂ z).symm
  haveI hnorm : ((gkFix g₁.K).map (gkIso hτ hU hτ₂ hU₂ Φ).toMonoidHom).Normal := by
    change ((gkFix (fieldOf N₁)).map (gkIso hτ hU hτ₂ hU₂ Φ).toMonoidHom).Normal
    rw [gkFix_fieldOf (Subgroup.isClosed_of_isOpen _ hN₁o)]
    exact hN₁n.map _ (gkIso hτ hU hτ₂ hU₂ Φ).surjective
  have hK₂ : ∀ x ∈ L.tgt.K, a₂ x ∈ L.tgt.K := fun x hx =>
    mem_fieldOf_conj ((gkFix g₁.K).map (gkIso hτ hU hτ₂ hU₂ Φ).toMonoidHom) a₂ _ hag₂ hx
  have hea : L.e (piOf (curveGaloisData K g₁.hτ₀) a (fix_of_fix a hfix g₁)) =
      piOf (curveGaloisData K₂ L.hυ) a₂ hfix₂ := by
    have e1 : piOf (curveGaloisData K g₁.hτ₀) a (fix_of_fix a hfix g₁) =
        (ã : Pi (curveGaloisData K hτ)) :=
      congrArg (fun σ : (curveGaloisData K hτ).H => (σ : Pi (curveGaloisData K hτ)))
        (Subtype.ext (AlgEquiv.ext fun _ => rfl))
    have e2 : piOf (curveGaloisData K₂ L.hυ) a₂ hfix₂ =
        (ã₂ : Pi (curveGaloisData K₂ L.hυ)) :=
      congrArg (fun σ : (curveGaloisData K₂ L.hυ).H => (σ : Pi (curveGaloisData K₂ L.hυ)))
        (Subtype.ext (AlgEquiv.ext fun _ => rfl))
    rw [e1, e2, hã₂]
  -- the stage isomorphism intertwines the conjugations
  have hS' : L.S (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ)
      (g₁.conj a hfix hg₁K w₁) =
      L.tgt.conj a₂ hfix₂' hK₂
        (L.S (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ) w₁) :=
    h1Congr_stageConj L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g₁.hτ₀)
      (cycloVχ (cycloIso hτ hU hτ₂ hU₂ Φ) g₁.hτ₀ L.hυ)
      (cycloVχ_smul (cycloIso hτ hU hτ₂ hU₂ Φ) _ (cycloIso_smul hτ hU hτ₂ hU₂ Φ) g₁.hτ₀ L.hυ L.he)
      g₁.K a (fix_of_fix a hfix g₁) hg₁K a₂ hfix₂ hK₂ (curveGaloisData_H_le K g₁.hτ₀)
      (curveGaloisData_H_le K₂ L.hυ) hea w₁
  -- assembly in the colimits
  have k1 : kummerNF N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)
      (Units.map (nfRingEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N
        N₂).toMonoidHom f') =
      ofG L.tgt (L.tgt.conj a₂ hfix₂' hK₂
        (L.S (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ) w₁)) := by
    rw [kummerNF_nfRingEquiv, ← hsrc, h1LimCycloEquiv_ofG, ← hL, hS']
  have k2 : ofG L.tgt (L.S (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ) w₁) =
      kummerNF N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)
        (Units.map (nfRingEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N
          N₂).toMonoidHom f) := by
    rw [kummerNF_nfRingEquiv, ← hw₁, h1LimCycloEquiv_ofG, ← hL]
  have hz0 : (gkIso hτ hU hτ₂ hU₂ Φ gal
      (nfConst hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ y) :
        FFClosure C₂.Xbar) ≠ 0 := by
    intro h0
    have h1 : gkIso hτ hU hτ₂ hU₂ Φ gal
        (nfConst hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ y) = 0 :=
      Subtype.ext h0
    rw [map_eq_zero_iff _ (gkIso hτ hU hτ₂ hU₂ Φ gal).injective] at h1
    have h2 := congrArg Subtype.val h1
    rw [coe_nfConst] at h2
    exact f.ne_zero ((map_eq_zero_iff _ (nfRingEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂
      hDGC hDGC₁ N N₂).injective).1 (Subtype.ext h2))
  let f₂' : (fnf N₂)ˣ := Units.mk0 (constFnf N₂ (gkIso hτ hU hτ₂ hU₂ Φ gal
    (nfConst hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ y)))
    fun h0 => hz0 (congrArg Subtype.val h0 :)
  have k3 := ofG_stageConj_eq a₂ hfix₂' N₂ (gkIso hτ hU hτ₂ hU₂ Φ gal) hag₂ L.tgt hK₂
    (L.S (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ) w₁)
    (Units.map (nfRingEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N
      N₂).toMonoidHom f) f₂'
    (mem_algebraicClosure_iff.1
      (nfConst hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ y).2)
    (hag₂ _).symm k2
  have hinj := kummerNF_injective N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂) (k1.trans k3)
  exact Subtype.ext (congrArg (fun u : (fnf N₂)ˣ => ((u : fnf N₂) : FFClosure C₂.Xbar)) hinj)

end Lift

end Iut.Reconstruction
