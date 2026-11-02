/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ClosedPtLift
import Iut.Reconstruction.Thm19.RestrictCongr
import Iut.Reconstruction.Thm19.NFCanon

/-!
# Kummer classes along the stage isomorphisms (MR9 item 4, step 4, "G")

[AbsTopIII] Prop 1.8 (i) (`Topics in Absolute Anabelian Geometry III.txt` l.2061–2106)
characterises the classes `η ∈ P_U` of which a positive multiple is the Kummer class of a
nonconstant NF-rational function by their restrictions to closed points. Along a stage isomorphism
`LiftData.S` (`Thm19/LimIso.lean`, cyclotome `cycloIso Φ`) these restrictions are matched
(`LiftData.exists_closedPoint_decomp`, `restrictClosed_h1Congr_eq_one_iff`), so the test passes on
both sides:

* generic: `exists_notMem_of_isIntegral` (a place with algebraic residue field over `k` is
  nontrivial on `F`);
* `LiftData.S_apply`, **`LiftData.exists_restrict_iff`**: every closed point of the stage has a
  closed point of the target stage at which the restrictions of `η` and `L.S η` vanish together;
* **`LiftData.isNFKummerTest_S`**: the test of Prop 1.8 (i) is carried along `L.S`;
* **`LiftData.S_kummer_pow`** (piece G): at a stage with rational cusps, some positive power of
  `L.S κ(w)` is a Kummer class (for `w` constant, `κ(w) = κ(w f₀) κ(f₀)⁻¹` with a unit `f₀` that is
  not an algebraic number).
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian IsLocalRing

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

/-- **A place whose residue field is algebraic over `k` is nontrivial on `F`**: otherwise the
residue of `p(t)`, `p` the minimal polynomial of the residue of `t`, would vanish although
`p(t) ≠ 0` is a unit of `A`. -/
lemma exists_notMem_of_isIntegral (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    [Algebra k (ResidueField A)]
    (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
    [Algebra.IsIntegral k (ResidueField A)] (ht : t ∈ A) : ∃ f : F D, (f : Ω) ∉ A := by
  by_contra h
  push Not at h
  obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := k) (residue A ⟨t, ht⟩)
  set ψ : k →+* A := (algebraMap k Ω).codRestrict A.toSubring hk
  set a : A := p.eval₂ ψ ⟨t, ht⟩
  have ha : (a : Ω) = Polynomial.aeval t p := by
    rw [Polynomial.aeval_def]
    exact Polynomial.hom_eval₂ p ψ A.subtype ⟨t, ht⟩
  have hcomp : (residue A).comp ψ = algebraMap k (ResidueField A) :=
    RingHom.ext fun c => hkres c
  have hres : residue A a = 0 := by
    rw [Polynomial.hom_eval₂, hcomp]
    exact hp
  set f : F D := Polynomial.aeval (tF D) p
  have hf : (f : Ω) = Polynomial.aeval t p := by
    exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k (F D) Ω) (tF D) p).symm
  have hf0 : f ≠ 0 := fun h0 => D.transcendental ⟨p, hpm.ne_zero, by
    rw [← hf, h0]
    rfl⟩
  have hinv : ((f⁻¹ : F D) : Ω) ∈ A := h _
  have hunit : IsUnit a := by
    refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
    change (a : Ω) * ((f⁻¹ : F D) : Ω) = 1
    rw [ha, ← hf, ← IntermediateField.coe_mul, mul_inv_cancel₀ hf0]
    rfl
  exact (residue_ne_zero_iff_isUnit a).2 hunit hres

/-- `x = a b⁻¹`, `a^m = c`, `b^n = d` ⇒ `x^{mn} = c^n (d^m)⁻¹` (commutative groups). -/
lemma pow_mul_eq_of_eq_mul_inv {G : Type*} [CommGroup G] {x a b c d : G} {m n : ℕ}
    (hx : x = a * b⁻¹) (ha : a ^ m = c) (hb : b ^ n = d) : x ^ (m * n) = c ^ n * (d ^ m)⁻¹ := by
  rw [hx, ← ha, ← hb, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm n m]

omit [CharZero k] in
/-- A nonzero algebraic number times a transcendental number is transcendental. -/
lemma not_isAlgebraic_mul [CharZero Ω] {x y : Ω} (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0)
    (hy : ¬ IsAlgebraic ℚ y) : ¬ IsAlgebraic ℚ (x * y) := by
  intro hxy
  apply hy
  have e : y = x * y / x := (mul_div_cancel_left₀ y hx0).symm
  rw [e]
  exact mem_algebraicClosure_iff.1 (div_mem (mem_algebraicClosure_iff.2 hxy)
    (mem_algebraicClosure_iff.2 hx))

end Generic

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
  [CharZero (FFClosure C.Xbar)] [CharZero (FFClosure C₂.Xbar)]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic

variable {τ : C.Xbar.functionField} {hτ : Transcendental K τ}
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] {hU : C.U = chartOne K C.Xbar τ}
  {τ₂ : C₂.Xbar.functionField} {hτ₂ : Transcendental K₂ τ₂}
  [IsGalois (K₀ K₂ (coordT τ₂)) (FFClosure C₂.Xbar)] {hU₂ : C₂.U = chartOne K₂ C₂.Xbar τ₂}
  {Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out)} {g : GStage K hτ}
  (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))
  (hχU : CycloEquivariant (bridgeIso hτ hU hτ₂ hU₂ Φ) χU)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
omit [CharZero (FFClosure C.Xbar)] [CharZero (FFClosure C₂.Xbar)] in
/-- `L.S` is `h1Congr` along `constIso` (the definition, in the form used by
`restrictClosed_h1Congr_eq_one_iff`). -/
lemma LiftData.S_apply (L : LiftData hτ hU hτ₂ hU₂ Φ g) (η : H1G g) :
    L.S χU hχU η = h1Congr
      (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K)
      (constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K)
      (constCyclo_smul L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
        (cycloVχ χU g.hτ₀ L.hυ) (cycloVχ_smul χU _ hχU g.hτ₀ L.hυ L.he) g.K) η := rfl

/-- The NF-model of a stage (over a number field, `F_NF = F k̄`). -/
abbrev Thm19.GStage.nfModel {k : Type u} [Field k] [CharZero k] [NumberField k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X] {τ' : X.functionField}
    {hτ' : Transcendental k τ'} [IsAlgClosed (FFClosure X)] [CharZero (FFClosure X)]
    (g : GStage k hτ') : NFModel g.data :=
  haveI : NumberField g.K := NumberField.of_module_finite k g.K
  nfModelNF g.data

variable (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
  (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
  (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
  (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
  (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
  (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0) (hDGC : RelIsomDGC.Exists K₂)

variable [Fact (0 < (CurvesJacobian.curveGenus K₂ C₂.Xbar).toNat)]

set_option maxHeartbeats 3200000 in
-- the restrictions to two closed points and the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the actions of `Gal(κ(A)/k_x)` and the group structures on `Π_V` are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC in
/-- **Closed points along the stage isomorphism, for the test of Prop 1.8**: every NF-point `A`
of the stage with the closed-point data of `RestrictTrivAt` has an NF-point `A''` of the target
stage with the same data such that `η|_A = 0 ↔ (L.S η)|_{A''} = 0` for all `η`
(`LiftData.exists_closedPoint_decomp`, `restrictClosed_h1Congr_eq_one_iff`). -/
theorem LiftData.exists_restrict_iff (hS : BelyiCuspSpec Ω C hc.out)
    (L : LiftData hτ hU hτ₂ hU₂ Φ g) (A : ValuationSubring (FFClosure C.Xbar))
    (hk : ∀ c : g.K, algebraMap g.K (FFClosure C.Xbar) c ∈ A) (ht : coordT g.τ₀ ∈ A)
    (hint : letI := Decomposition.residueAlgebra A hk
      Algebra.IsIntegral g.K (ResidueField A)) :
    ∃ (A'' : ValuationSubring (FFClosure C₂.Xbar))
      (hk'' : ∀ c : L.tgt.K, algebraMap L.tgt.K (FFClosure C₂.Xbar) c ∈ A'')
      (ht'' : coordT L.υ ∈ A''), L.tgt.nfModel.IsNFPoint A'' ∧
      letI := Decomposition.residueAlgebra A'' hk''
      ∃ (_ : Algebra.IsIntegral L.tgt.K (ResidueField A''))
        (_ : FiniteDimensional L.tgt.K (Decomposition.pointField (F L.tgt.data) A'' hk''
          (Decomposition.residue_algebraMap_residueAlgebra A'' hk''))),
        ∀ η : H1G g,
          (letI := Decomposition.residueAlgebra A hk; haveI := hint;
            restrictClosed g.data A hk (Decomposition.residue_algebraMap_residueAlgebra A hk)
              (constExt_HL_eq_curve K g.hτ₀ g.K) ht η = 1) ↔
            restrictClosed L.tgt.data A'' hk''
              (Decomposition.residue_algebraMap_residueAlgebra A'' hk'')
              (constExt_HL_eq_curve K₂ L.hυ L.tgt.K) ht'' (L.S χU hχU η) = 1 := by
  have hne : ∃ f : F g.data, (f : FFClosure C.Xbar) ∉ A := by
    letI := Decomposition.residueAlgebra A hk
    haveI := hint
    exact exists_notMem_of_isIntegral (D := g.data) A hk
      (Decomposition.residue_algebraMap_residueAlgebra A hk) ht
  have hD := L.exists_closedPoint_decomp σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hS A hk ht hne
  refine hD.elim fun A'' hD => hD.elim fun hk'' hD => hD.elim fun ht'' hD =>
    hD.elim fun hne'' hD => hD.elim fun M hdec => ?_
  letI := Decomposition.residueAlgebra A hk
  haveI := hint
  letI := Decomposition.residueAlgebra A'' hk''
  haveI hint'' : Algebra.IsIntegral L.tgt.K (ResidueField A'') :=
    isIntegral_residueField_of_ne A'' hk'' hne''
  refine ⟨A'', hk'', ht'', ?_, hint'', finiteDimensional_pointField A'' hk'' hne'',
    fun η => ?_⟩
  · obtain ⟨f, hf⟩ := hne''
    exact ⟨f, le_F_baseChange _ f.2, hf⟩
  · exact restrictClosed_h1Congr_eq_one_iff A hk
      (Decomposition.residue_algebraMap_residueAlgebra A hk) (constExt_HL_eq_curve K g.hτ₀ g.K)
      ht A'' hk'' (Decomposition.residue_algebraMap_residueAlgebra A'' hk'')
      (constExt_HL_eq_curve K₂ L.hυ L.tgt.K) ht''
      (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K)
      (constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K)
      (constCyclo_smul L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
        (cycloVχ χU g.hτ₀ L.hυ) (cycloVχ_smul χU _ hχU g.hτ₀ L.hυ L.he) g.K) M hdec η

set_option maxHeartbeats 3200000 in
-- the restrictions to two closed points and the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the actions of `Gal(κ(A)/k_x)` and the group structures on `Π_V` are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC in
/-- **The test of [AbsTopIII] Prop 1.8 (i) is carried along the stage isomorphism.** -/
theorem LiftData.isNFKummerTest_S (hS : BelyiCuspSpec Ω C hc.out)
    (L : LiftData hτ hU hτ₂ hU₂ Φ g) (η : H1G g)
    (h : IsNFKummerTest g.nfModel (constExt_HL_eq_curve K g.hτ₀ g.K) η) :
    IsNFKummerTest L.tgt.nfModel (constExt_HL_eq_curve K₂ L.hυ L.tgt.K) (L.S χU hχU η) := by
  obtain ⟨M, hM, hT1, hT2⟩ := h
  refine ⟨M, hM, ?_, ?_⟩
  · obtain ⟨A₁, hk₁, ht₁, -, hint₁, -, h₁⟩ := hT1
    have hR := L.exists_restrict_iff χU hχU σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hS A₁ hk₁ ht₁ hint₁
    have hT' : RestrictTrivAt L.tgt.nfModel (constExt_HL_eq_curve K₂ L.hυ L.tgt.K)
        (L.S χU hχU (η ^ M)) :=
      hR.elim fun A'' hR => hR.elim fun hk'' hR => hR.elim fun ht'' hR =>
        hR.2.elim fun hint'' hR' => hR'.elim fun hfin'' hiff =>
          ⟨A'', hk'', ht'', hR.1, hint'', hfin'', (hiff (η ^ M)).1 h₁⟩
    exact (map_pow (L.S χU hχU) η M) ▸ hT'
  · obtain ⟨A₂, hk₂, ht₂, -, hint₂, -, h₂⟩ := hT2
    have hR := L.exists_restrict_iff χU hχU σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hS A₂ hk₂ ht₂ hint₂
    have hT' : RestrictNontrivAt L.tgt.nfModel (constExt_HL_eq_curve K₂ L.hυ L.tgt.K)
        (L.S χU hχU (η ^ M)) :=
      hR.elim fun A'' hR => hR.elim fun hk'' hR => hR.elim fun ht'' hR =>
        hR.2.elim fun hint'' hR' => hR'.elim fun hfin'' hiff =>
          ⟨A'', hk'', ht'', hR.1, hint'', hfin'', fun h' => h₂ ((hiff (η ^ M)).2 h')⟩
    exact (map_pow (L.S χU hχU) η M) ▸ hT'

omit hc [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] in
include σ₀ hσ₀ in
/-- Prop 1.6 (iii) at a geometric stage (`⋂_N N · J(K₁) = 0`). -/
lemma Thm19.GStage.isKummerFaithfulJac (g : GStage K hτ) : IsKummerFaithfulJac g.data := by
  haveI : NumberField g.K := NumberField.of_module_finite K g.K
  exact isKummerFaithfulJac_constExt g.K
    (isDivFreeOver_curve K g.hτ₀ σ₀ hσ₀ g.K (jacDivFree_numberField' C.Xbar σ₀ hσ₀ g.K))

omit hc [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] in
/-- `K₁` is the field of constants of a geometric stage. -/
lemma Thm19.GStage.hkF (g : GStage K hτ) :
    ∀ x : F g.data, IsAlgebraic g.K x → x ∈ Set.range (algebraMap g.K (F g.data)) :=
  mem_range_of_isAlgebraic_F_constExt g.K (mem_range_of_isAlgebraic_F K g.hτ₀)

omit hc [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] in
/-- A unit whose value is not an algebraic number is not in the field of constants. -/
lemma Thm19.GStage.notMem_range_constUnit (g : GStage K hτ) {w : units g.data}
    (hw : ¬ IsAlgebraic ℚ (((w : (F g.data)ˣ) : F g.data) : FFClosure C.Xbar)) :
    w ∉ Set.range (constUnit g.data) := by
  haveI : NumberField g.K := NumberField.of_module_finite K g.K
  rintro ⟨b, rfl⟩
  exact hw (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b : g.K)).algebraMap

set_option maxHeartbeats 3200000 in
-- the restrictions to two closed points and the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the actions of `Gal(κ(A)/k_x)` and the group structures on `Π_V` are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC in
/-- **A nonconstant Kummer class along the stage isomorphism** (Prop 1.8 (i) on both sides, at a
stage with rational cusps). -/
theorem LiftData.S_kummer_pow_of_nonconst (hS : BelyiCuspSpec Ω C hc.out)
    (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (hrat : ∀ P : Place g.K (F g.data), IsCuspPlaceF P → ∃ x : RatPoint g.data, placeOfF x = P)
    (hT : L.TameCompat χU) (w : units g.data) (hw : w ∉ Set.range (constUnit g.data)) :
    ∃ M : ℕ, 0 < M ∧ ∃ w' : units L.tgt.data,
      L.S χU hχU (kummerMapZHat g.data w) ^ M = kummerMapZHat L.tgt.data w' := by
  haveI : NumberField g.K := NumberField.of_module_finite K g.K
  haveI : NumberField L.tgt.K := NumberField.of_module_finite K₂ L.tgt.K
  have htest : IsNFKummerTest g.nfModel (constExt_HL_eq_curve K g.hτ₀ g.K)
      (kummerMapZHat g.data w) :=
    (isNFKummerTest_iff (N := g.nfModel) (hHL := constExt_HL_eq_curve K g.hτ₀ g.K)
      (NumberField.isTorallyKummerFaithful g.K) (g.isKummerFaithfulJac σ₀ hσ₀) g.hkF
      (kummerMapZHat g.data w) ⟨w, rfl⟩).2 ⟨1, one_pos, w, pow_one _, hw,
        le_F_baseChange g.data ((w : (F g.data)ˣ) : F g.data).2⟩
  have hPU := L.S_mem_PU χU hχU σ₀ hσ₀ σ₂ hσ₂ hrat hT (kummerMapZHat g.data w) ⟨w, rfl⟩
  obtain ⟨M, hM, w', hw', -, -⟩ := (isNFKummerTest_iff (N := L.tgt.nfModel)
    (hHL := constExt_HL_eq_curve K₂ L.hυ L.tgt.K) (NumberField.isTorallyKummerFaithful L.tgt.K)
    (L.tgt.isKummerFaithfulJac σ₂ hσ₂) L.tgt.hkF _ hPU).1
    (L.isNFKummerTest_S χU hχU σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hS _ htest)
  exact ⟨M, hM, w', hw'⟩

set_option maxHeartbeats 3200000 in
-- the restrictions to two closed points and the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the actions of `Gal(κ(A)/k_x)` and the group structures on `Π_V` are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC in
/-- **Piece G: Kummer classes along the stage isomorphism.** At a stage with rational cusps
carrying a unit `f₀` that is not an algebraic number, some positive power of `L.S κ(w)` is a
Kummer class, for every unit `w` (for `w` constant: `κ(w) = κ(w f₀) κ(f₀)⁻¹`). -/
theorem LiftData.S_kummer_pow (hS : BelyiCuspSpec Ω C hc.out) (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (hrat : ∀ P : Place g.K (F g.data), IsCuspPlaceF P → ∃ x : RatPoint g.data, placeOfF x = P)
    (hT : L.TameCompat χU) (w f₀ : units g.data)
    (hf₀ : ¬ IsAlgebraic ℚ (((f₀ : (F g.data)ˣ) : F g.data) : FFClosure C.Xbar)) :
    ∃ M : ℕ, 0 < M ∧ ∃ w' : units L.tgt.data,
      L.S χU hχU (kummerMapZHat g.data w) ^ M = kummerMapZHat L.tgt.data w' := by
  haveI : NumberField g.K := NumberField.of_module_finite K g.K
  have nc := L.S_kummer_pow_of_nonconst χU hχU σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hS hrat hT
  by_cases hw : w ∈ Set.range (constUnit g.data)
  · obtain ⟨b, hb⟩ := hw
    have hbv : (((w : (F g.data)ˣ) : F g.data) : FFClosure C.Xbar) =
        algebraMap g.K (FFClosure C.Xbar) (b : g.K) :=
      (congrArg (fun u : units g.data => (((u : (F g.data)ˣ) : F g.data) : FFClosure C.Xbar))
        hb).symm
    have hwf : w * f₀ ∉ Set.range (constUnit g.data) :=
      g.notMem_range_constUnit (not_isAlgebraic_mul
        (hbv ▸ (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b : g.K)).algebraMap)
        (hbv ▸ (map_ne_zero_iff _ (algebraMap g.K (FFClosure C.Xbar)).injective).2 b.ne_zero)
        hf₀)
    obtain ⟨M₁, hM₁, w₁, h₁⟩ := nc (w * f₀) hwf
    obtain ⟨M₂, hM₂, w₂, h₂⟩ := nc f₀ (g.notMem_range_constUnit hf₀)
    refine ⟨M₁ * M₂, Nat.mul_pos hM₁ hM₂, w₁ ^ M₂ * (w₂ ^ M₁)⁻¹, ?_⟩
    have e : kummerMapZHat g.data w =
        kummerMapZHat g.data (w * f₀) * (kummerMapZHat g.data f₀)⁻¹ :=
      (mul_inv_cancel_right _ _).symm.trans (congrArg (· * _) (map_mul _ w f₀).symm)
    have hS : L.S χU hχU (kummerMapZHat g.data w) =
        L.S χU hχU (kummerMapZHat g.data (w * f₀)) *
          (L.S χU hχU (kummerMapZHat g.data f₀))⁻¹ :=
      (congrArg (L.S χU hχU) e).trans ((map_mul _ _ _).trans (congrArg (_ * ·) (map_inv _ _)))
    have hR : kummerMapZHat L.tgt.data (w₁ ^ M₂ * (w₂ ^ M₁)⁻¹) =
        kummerMapZHat L.tgt.data w₁ ^ M₂ * (kummerMapZHat L.tgt.data w₂ ^ M₁)⁻¹ :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (map_pow _ _ _)
        ((map_inv _ _).trans (congrArg _ (map_pow _ _ _))))
    exact (pow_mul_eq_of_eq_mul_inv hS h₁ h₂).trans hR.symm
  · exact nc w hw

end Lift

end Iut.Reconstruction
