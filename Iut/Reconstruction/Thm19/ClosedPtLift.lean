/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.SyncStageLift
import Iut.Reconstruction.Thm19.LimEquiv
import Iut.Reconstruction.Thm19.StageNF

/-!
# Decomposition groups of closed points along the stage isomorphisms (MR9 item 4, step 4, "D")

[AbsTopIII] Thm 1.9 (a) (`Topics in Absolute Anabelian Geometry III.txt` l.2140–2143) reconstructs
the decomposition groups of the closed points of `U` from `Π_U`; Prop 1.8 (l.2061–2106) tests
Kummer classes by their restrictions to them. For the functoriality of the test along a stage
isomorphism `LiftData.S` (`Thm19/LimIso.lean`) every closed point `x` of a geometric stage `V`
must have a closed point `x''` of the target stage whose decomposition group is the image of
that of `x` up to conjugation. Here `x` is made a cusp of a smaller open `V'' ⊆ V` (a coordinate
with a pole at `x`, `exists_coordinate_V_rev`), where the stage isomorphism matches the
decomposition groups of cusps (`LiftData.map_decompH_constIso`); the result is pushed down along
`V'' ⊆ V` (`LiftData.exists_conj_const`), and `x''` is not a cusp of the target stage because its
inertia group there is trivial (`inertiaPi_eq_bot_of_mem`, `mk_ne_one_of_cusp`):

* generic: `map_piT_decompH` (two charts of the same function field), `map_map_eq_conj`;
* `GStage.F_of_K_le`: the function field of a geometric stage depends only on its field of
  constants;
* `exists_coord_pole`: a coordinate `τ₀''` over `k` with `chartOne τ₀'' ⊆ chartOne τ₀` and a pole at
  a given place `A` nontrivial on `F`;
* **`LiftData.exists_closedPoint_decomp`**.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

/-! ### Generic Galois models -/

section Generic

variable {k k₂ Ω : Type u} [Field k] [Field k₂] [Field Ω] [Algebra k Ω] [Algebra k₂ Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [CharZero k₂] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {t₂ : Ω} {D₂ : GaloisData k₂ t₂} [IsGalois (K₀ k₂ t₂) Ω]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **Two Galois models with the same function field** (`F D = F D₂`): the transition
`Π_{U₂} → Π_U` maps the decomposition group of `W` onto that of `W`. -/
lemma map_piT_decompH (hF : ∀ x ∈ F D, x ∈ F D₂) (hF' : ∀ x ∈ F D₂, x ∈ F D)
    (hW : ∀ W : ValuationSubring Ω, (∀ c : k₂, algebraMap k₂ Ω c ∈ W) → t₂ ∈ W →
      (∀ c : k, algebraMap k Ω c ∈ W) ∧ t ∈ W) (hH : D.H ≤ D.HL) (W : ValuationSubring Ω) :
    ((Thm19.decompH D₂ W).map (QuotientGroup.mk' (GaloisPi1.kernel D₂.H D₂.S))).map
        (piT D D₂ hF hW hH) =
      (Thm19.decompH D W).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨hT D D₂ hF σ, fun a => hσ a, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    refine ⟨_, ⟨hT D₂ D hF' s, fun a => hs a, rfl⟩, ?_⟩
    exact congrArg (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S))
      (Subtype.ext (AlgEquiv.ext fun _ => rfl))

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- `map_piT_inertiaPi` for Galois models over two fields of constants (same function field). -/
lemma map_piT_inertiaPi' (hF : ∀ x ∈ F D, x ∈ F D₂) (hF' : ∀ x ∈ F D₂, x ∈ F D)
    (hW : ∀ W : ValuationSubring Ω, (∀ c : k₂, algebraMap k₂ Ω c ∈ W) → t₂ ∈ W →
      (∀ c : k, algebraMap k Ω c ∈ W) ∧ t ∈ W) (hH : D.H ≤ D.HL) (W : ValuationSubring Ω) :
    (inertiaPi D₂ W).map (piT D D₂ hF hW hH) = inertiaPi D W := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨hT D D₂ hF σ, fun a ha => hσ a ha, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    refine ⟨_, ⟨hT D₂ D hF' s, fun a ha => hs a ha, rfl⟩, ?_⟩
    exact congrArg (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S))
      (Subtype.ext (AlgEquiv.ext fun _ => rfl))

end Generic

/-- **Images along a square commuting up to conjugation.** If `d (c y) = m · b (a y) · m⁻¹`,
then `b (a S) = m⁻¹ (d (c S)) m`. -/
lemma map_map_eq_conj {G₁ G₂ G₃ G₄ : Type*} [Group G₁] [Group G₂] [Group G₃] [Group G₄]
    (a : G₁ →* G₂) (b : G₂ →* G₃) (c : G₁ →* G₄) (d : G₄ →* G₃) (m : G₃)
    (h : ∀ y, d (c y) = m * b (a y) * m⁻¹) (S : Subgroup G₁) :
    (S.map a).map b = ((S.map c).map d).map (MulAut.conj m⁻¹).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv, h y]
  group

/-- `map_map_eq_conj` with the images named: if `S₁ ↦ S₂` under `a`, `S₁ ↦ S₄ ↦ S₃` under `c`,
`d`, and `d ∘ c = m (b ∘ a) m⁻¹`, then `b (R₂) = m⁻¹ R₃ m` for `R₂ = S₂`, `R₃ = S₃`. -/
lemma map_eq_conj_of_square {G₁ G₂ G₃ G₄ : Type*} [Group G₁] [Group G₂] [Group G₃] [Group G₄]
    (a : G₁ →* G₂) (b : G₂ →* G₃) (c : G₁ →* G₄) (d : G₄ →* G₃) (m : G₃)
    (h : ∀ y, d (c y) = m * b (a y) * m⁻¹) {S₁ : Subgroup G₁} {S₂ R₂ : Subgroup G₂}
    {S₄ : Subgroup G₄} {S₃ R₃ : Subgroup G₃} (h₂ : S₁.map a = S₂) (h₄ : S₁.map c = S₄)
    (h₃ : S₄.map d = S₃) (hR₂ : R₂ = S₂) (hR₃ : R₃ = S₃) :
    R₂.map b = R₃.map (MulAut.conj m⁻¹).toMonoidHom := by
  subst h₂ h₄ h₃ hR₂ hR₃
  exact map_map_eq_conj a b c d m h S₁

/-! ### Geometric stages -/

section Geom

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [IsFunctionField k X.functionField] {τ : X.functionField}
  {hτ : Transcendental k τ} [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)]

/-- **The function field of a geometric stage depends only on its field of constants**
(`mem_F_stage_iff`: it is `(U_{K₁})`'s function field). -/
lemma GStage.F_of_K_le {g g' : GStage k hτ} (h : g'.K ≤ g.K) :
    ∀ x ∈ F g'.data, x ∈ F g.data := by
  intro x hx
  rw [← toStage_data g'] at hx
  rw [← toStage_data g]
  exact (mem_F_stage_iff _ _ _ _).2 (L_constExt_mono _ h ((mem_F_stage_iff _ _ _ _).1 hx))

variable [IsAlgClosed (FFClosure X)]

/-- **A coordinate with a pole at a given place**: if `A ⊇ K₁` contains `τ₀` and is nontrivial
on the function field of the stage, there is `τ₀''` over `k` with `coordT τ₀ ∈ k[τ₀'']^~` (i.e.
`chartOne τ₀'' ⊆ chartOne τ₀`) and `coordT τ₀'' ∉ A` (`exists_coordinate_V_rev` for a
coefficient `y ∉ A` of the minimal polynomial over `K(X)` of a function `f ∉ A`). -/
theorem exists_coord_pole (g : GStage k hτ) (A : ValuationSubring (FFClosure X))
    (hk : ∀ c : g.K, algebraMap g.K (FFClosure X) c ∈ A)
    (hne : ∃ f : F g.data, (f : FFClosure X) ∉ A) :
    ∃ τ₀'' : X.functionField, Transcendental k τ₀'' ∧
      coordT g.τ₀ ∈ chartRing k (coordT τ₀'') ∧ coordT τ₀'' ∉ A := by
  obtain ⟨f, hf⟩ := hne
  set D' := curveGaloisData k g.hτ₀
  have hkA : ∀ c : k, algebraMap k (FFClosure X) c ∈ A := fun c => by
    rw [IsScalarTower.algebraMap_apply k g.K (FFClosure X)]
    exact hk _
  -- a coefficient `y ∈ L` of the minimal polynomial of `f` over `L` with `y ∉ A`
  obtain ⟨n, hn⟩ : ∃ n, ((minpoly D'.L (f : FFClosure X)).coeff n : FFClosure X) ∉ A := by
    by_contra hall
    push Not at hall
    exact hf (mem_of_coeffs_mem D' _ A hall)
  set y : FFClosure X := ((minpoly D'.L (f : FFClosure X)).coeff n : FFClosure X)
  have hyL : y ∈ D'.L := ((minpoly D'.L (f : FFClosure X)).coeff n).2
  have hyF : y ∈ F D' := mem_F_of_mem_L D' (curveGaloisData_H_le k g.hτ₀) hyL
  have hy0 : (⟨y, hyF⟩ : F D') ≠ 0 := fun h => hn (by
    have : y = 0 := congrArg Subtype.val h
    rw [this]
    exact A.zero_mem)
  obtain ⟨t', ht'L, htr', ht₀, hy, -, -⟩ := exists_coordinate_V_rev D' (Units.mk0 _ hy0)
  rw [curveGaloisData_L] at ht'L
  obtain ⟨τ₀'', hτ₀''⟩ := (mem_imageL_iff _).1 ht'L
  have he : coordT τ₀'' = t' := hτ₀''
  refine ⟨τ₀'', ?_, he ▸ ht₀, fun h => hn ?_⟩
  · rw [← transcendental_algebraMap_iff (algebraMap X.functionField (FFClosure X)).injective]
    change Transcendental k (coordT τ₀'')
    rw [he]
    exact htr'
  · exact mem_of_mem_chartRing A hkA (he ▸ h) hy

end Geom

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
  {Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out)}
  (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
  (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
  (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
  (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
  (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
  (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0) (hDGC : RelIsomDGC.Exists K₂)

variable [Fact (0 < (CurvesJacobian.curveGenus K₂ C₂.Xbar).toNat)]

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
omit [CharZero (FFClosure C.Xbar)] in
/-- **A place of the target stage with trivial inertia group is not a cusp** (cuspidal inertia
injects into `Π_{V'}`, `mk_ne_one_of_cusp`, `map_piRes_inertiaH`). -/
theorem LiftData.coordT_mem_of_inertiaPi_eq_bot {g : GStage K hτ} (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (W'' : ValuationSubring (FFClosure C₂.Xbar))
    (hkW : ∀ c : L.tgt.K, algebraMap L.tgt.K (FFClosure C₂.Xbar) c ∈ W'')
    (hinert : inertiaPi L.tgt.data W'' = ⊥) : coordT L.υ ∈ W'' := by
  by_contra hυ
  have hk₂ : ∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W'' := fun c => by
    rw [IsScalarTower.algebraMap_apply K₂ L.tgt.K (FFClosure C₂.Xbar)]
    exact hkW _
  obtain ⟨σ, hσ, hσ1⟩ := exists_inertiaH_ne_one (D := curveGaloisData K₂ L.hυ) hk₂
    ⟨(coordT L.υ)⁻¹, inv_mem (coordT_mem_F _), inv_ne_zero (fun h => hυ (h ▸ W''.zero_mem)),
      by
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ (lt_of_not_ge fun h =>
          hυ ((W''.valuation_le_one_iff _).1 h))⟩
  have hbot : (inertiaH (curveGaloisData K₂ L.hυ) W'').map (QuotientGroup.mk'
      (GaloisPi1.kernel (curveGaloisData K₂ L.hυ).H (curveGaloisData K₂ L.hυ).S)) = ⊥ := by
    rw [← map_piRes_inertiaH L.tgt.K hk₂]
    exact (congrArg (fun S => S.map (piRes L.tgt.K (curveGaloisData K₂ L.hυ))) hinert).trans
      (Subgroup.map_bot _)
  have hmem : ((σ : (curveGaloisData K₂ L.hυ).H) : Pi (curveGaloisData K₂ L.hυ)) ∈
      (inertiaH (curveGaloisData K₂ L.hυ) W'').map (QuotientGroup.mk'
        (GaloisPi1.kernel (curveGaloisData K₂ L.hυ).H (curveGaloisData K₂ L.hυ).S)) :=
    ⟨σ, hσ, rfl⟩
  rw [hbot] at hmem
  exact mk_ne_one_of_cusp ⟨(W'', σ), hk₂, hσ⟩ hυ hσ1 (Subgroup.mem_bot.1 hmem)

set_option maxHeartbeats 3200000 in
-- the quotients `Π_V` of four stages unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
include σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC in
/-- **Piece D: closed points along the stage isomorphism.** For lift data `L` at a geometric
stage `g` and a place `A ⊇ K₁` with `τ₀ ∈ A`, nontrivial on the function field (a closed point
`x` of the stage), there are a place `A''` of the target stage with the same properties (a closed
point `x''`) and `M ∈ Π_{V'}` with `constIso (D_x) = M D_{x''} M⁻¹`. -/
theorem LiftData.exists_closedPoint_decomp (hS : BelyiCuspSpec Ω C hc.out) {g : GStage K hτ}
    (L : LiftData hτ hU hτ₂ hU₂ Φ g) (A : ValuationSubring (FFClosure C.Xbar))
    (hk : ∀ c : g.K, algebraMap g.K (FFClosure C.Xbar) c ∈ A) (ht : coordT g.τ₀ ∈ A)
    (hne : ∃ f : F g.data, (f : FFClosure C.Xbar) ∉ A) :
    ∃ (A'' : ValuationSubring (FFClosure C₂.Xbar))
      (_ : ∀ c : L.tgt.K, algebraMap L.tgt.K (FFClosure C₂.Xbar) c ∈ A'')
      (_ : coordT L.υ ∈ A'') (_ : ∃ f : F L.tgt.data, (f : FFClosure C₂.Xbar) ∉ A'')
      (M : Pi L.tgt.data),
      (decompToPi g.data A).range.map
          (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
            g.K).toMulEquiv.toMonoidHom =
        (decompToPi L.tgt.data A'').range.map (MulAut.conj M).toMonoidHom := by
  -- the stage `g''` on which `A` is a cusp
  obtain ⟨τ₀'', hτ₀'', h₀, hA⟩ := exists_coord_pole g A hk hne
  obtain ⟨g'', hle, hK, hAc⟩ : ∃ g'' : GStage K hτ, g ≤ g'' ∧ g''.K ≤ g.K ∧
      A ∈ CuspW (k := g''.K) (t := coordT g''.τ₀) :=
    ⟨⟨g.K, τ₀'', hτ₀'', GStage.mem_chartRing_trans' g.htV h₀⟩, ⟨le_rfl, h₀⟩, le_rfl, hk, hA⟩
  obtain ⟨L''⟩ := LiftData.nonempty (hτ₂ := hτ₂) (hU₂ := hU₂) (Φ := Φ) (hU := hU) hS g''
  obtain ⟨W'', hW'', hI⟩ := L''.exists_map_inertiaH_constIso A hAc
  have hD := L''.map_decompH_constIso A hAc W'' hW'' hI
  have hle' : L.tgt ≤ L''.tgt := L.le_tgt σ₂ hσ₂ hg₂ hle L''
  obtain ⟨m, -, hm⟩ := L.exists_conj_const σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hle L''
  -- the transitions along `g ≤ g''` and `L.tgt ≤ L''.tgt`
  have hF₁ : ∀ x ∈ F g''.data, x ∈ F g.data := GStage.F_of_K_le hK
  have hF₂ : ∀ x ∈ F L''.tgt.data, x ∈ F L.tgt.data :=
    GStage.F_of_K_le (constField_mono _ hK)
  -- `A''` is not a cusp of the target stage: its inertia group there is trivial
  have e1 := map_eq_conj_of_square
    (piT g.data g''.data (GStage.F_mono hle) (GStage.hW_mono hle) g.data_H_le)
    (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
      g.K).toMulEquiv.toMonoidHom
    (constIso L''.e (gkIso hτ hU hτ₂ hU₂ Φ) L''.he_gk (piToGk_surjective_curve g''.hτ₀)
      g''.K).toMulEquiv.toMonoidHom
    (piT L.tgt.data L''.tgt.data (GStage.F_mono hle') (GStage.hW_mono hle') L.tgt.data_H_le)
    m hm (S₁ := inertiaPi g''.data A) (R₂ := inertiaPi g.data A)
    (R₃ := inertiaPi L.tgt.data W'')
    (map_piT_inertiaPi' (D := g.data) (D₂ := g''.data) (GStage.F_mono hle) hF₁
      (GStage.hW_mono hle) g.data_H_le A) hI
    (map_piT_inertiaPi' (D := L.tgt.data) (D₂ := L''.tgt.data) (GStage.F_mono hle') hF₂
      (GStage.hW_mono hle') L.tgt.data_H_le W'') rfl rfl
  rw [inertiaPi_eq_bot_of_mem g.data_H_le hk ht, Subgroup.map_bot] at e1
  have hinert : inertiaPi L.tgt.data W'' = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h0 : (MulAut.conj m⁻¹).toMonoidHom x ∈
        (inertiaPi L.tgt.data W'').map (MulAut.conj m⁻¹).toMonoidHom := ⟨x, hx, rfl⟩
    rw [← e1, Subgroup.mem_bot] at h0
    exact Subgroup.mem_bot.2 ((MulAut.conj m⁻¹).injective (h0.trans (map_one _).symm))
  have hkW : ∀ c : L.tgt.K, algebraMap L.tgt.K (FFClosure C₂.Xbar) c ∈ W'' :=
    fun c => hW''.1 ⟨c, hle'.1 c.2⟩
  have ht'' : coordT L.υ ∈ W'' := L.coordT_mem_of_inertiaPi_eq_bot W'' hkW hinert
  have hne'' : ∃ f : F L.tgt.data, (f : FFClosure C₂.Xbar) ∉ W'' :=
    ⟨⟨_, hF₂ _ (tF L''.tgt.data).2⟩, hW''.2⟩
  refine ⟨W'', hkW, ht'', hne'', m⁻¹, ?_⟩
  -- the decomposition groups
  exact map_eq_conj_of_square
    (piT g.data g''.data (GStage.F_mono hle) (GStage.hW_mono hle) g.data_H_le)
    (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
      g.K).toMulEquiv.toMonoidHom
    (constIso L''.e (gkIso hτ hU hτ₂ hU₂ Φ) L''.he_gk (piToGk_surjective_curve g''.hτ₀)
      g''.K).toMulEquiv.toMonoidHom
    (piT L.tgt.data L''.tgt.data (GStage.F_mono hle') (GStage.hW_mono hle') L.tgt.data_H_le)
    m hm
    (map_piT_decompH (D := g.data) (D₂ := g''.data) (GStage.F_mono hle) hF₁
      (GStage.hW_mono hle) g.data_H_le A) hD
    (map_piT_decompH (D := L.tgt.data) (D₂ := L''.tgt.data) (GStage.F_mono hle') hF₂
      (GStage.hW_mono hle') L.tgt.data_H_le W'')
    (range_decompToPi_eq_map_decompH' (D := g.data) A)
    (range_decompToPi_eq_map_decompH' (D := L.tgt.data) W'')

end Lift

end Iut.Reconstruction
