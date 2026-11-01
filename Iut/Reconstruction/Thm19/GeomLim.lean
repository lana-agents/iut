/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.StageGeom
import Iut.Reconstruction.Thm19.LimCongr

/-!
# [AbsTopIII] Thm 1.9 (d): the colimit over geometric stages

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178) takes
`lim→_V H¹(Π_V, μ_Ẑ(Π_U))`, `V` ranging over the opens of `Z ×_{k_Z} k′` obtained by removing
NF-points, `k′ / k_Z` finite. In `Thm19/NFDirectLimit.lean` a stage is `(K₁, t′)` with an
arbitrary coordinate `t′` of `U_{K₁}`. For the functoriality in `Π_U` (MR9 item 3) only the
*geometric* stages are needed: `V = (U_X)_{K₁}` for an open `U_X = chartOne τ₀ ⊆ U` defined over
`k`, `τ₀ ∈ K(X)`. They are cofinal (`exists_stage_ge_coord`), and their Galois model is
`constExt K₁ (curveGaloisData k hτ₀)` on the nose, which avoids transports along
`stage_eq_constExt_newData`. Here:

* `limOf`, `limOf_f`: the class maps `F i →* lim→ F`;
* `resT_trans`, `piT_self`, `resT_self`: the transition maps of `Thm19/NFTransition.lean` compose
  and are the identity on equal data (all proof arguments are propositions);
* **`GStage k hτ`**: the geometric stages `(K₁, τ₀)` (`coordT τ` regular on `chartOne τ₀`),
  ordered by `K₁ ⊆ K₁′` and `chartOne τ₀′ ⊆ chartOne τ₀`; directed (through the stages of
  `NFDirectLimit` and `exists_stage_ge_coord`);
* `GStage.toStage`, `toStage_data` (`stage = constExt K₁ (curveGaloisData k hτ₀)`),
  `toStage_le_iff`;
* `H1G`, `resG`, **`GLim k hτ = lim→_{(K₁, τ₀)} H¹(Π_{(U_{τ₀})_{K₁}}, Ẑ(1))`**;
* **`h1LimEquivG : H1Lim (curveGaloisData k hτ) ≃* GLim k hτ`** (`mulEquivOfCocones`).
-/

open CategoryTheory AlgebraicGeometry Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  Belyi

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

/-! ### The class maps of a direct limit of groups -/

section Of

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {F : ι → Type*} [∀ i, Group (F i)] (f : ∀ i j, i ≤ j → F i →* F j)
  [DirectedSystem F (fun i j h ↦ f i j h)]

/-- The class map `F i →* lim→ F`. -/
def limOf (i : ι) : F i →* DirectLimit F (fun i j h ↦ f i j h) where
  toFun x := ⟦⟨i, x⟩⟧
  map_one' := (DirectLimit.one_def i).symm
  map_mul' x y := (DirectLimit.mul_def i x y).symm

lemma limOf_apply (i : ι) (x : F i) : limOf f i x = ⟦⟨i, x⟩⟧ := rfl

lemma limOf_f {i j : ι} (h : i ≤ j) (x : F i) : limOf f j (f i j h x) = limOf f i x :=
  DirectLimit.mk_apply (f := fun i j h ↦ f i j h) i j x h

lemma limLift_limOf {C : Type*} [Group C] (φ : ∀ i, F i →* C)
    (hφ : ∀ i j (h : i ≤ j) x, φ i x = φ j (f i j h x)) (i : ι) (x : F i) :
    limLift f φ hφ (limOf f i x) = φ i x := rfl

end Of

/-! ### The transition maps on equal and composed data -/

section Trans

variable {k₁ k₂ k₃ Ω : Type u} [Field k₁] [Field k₂] [Field k₃] [Field Ω] [Algebra k₁ Ω]
  [Algebra k₂ Ω] [Algebra k₃ Ω] {t₁ t₂ t₃ : Ω} {D₁ : GaloisData k₁ t₁}
  {D₂ : GaloisData k₂ t₂} {D₃ : GaloisData k₃ t₃}
  [IsGalois (K₀ k₁ t₁) Ω] [IsGalois (K₀ k₂ t₂) Ω] [IsGalois (K₀ k₃ t₃) Ω]
  [CharZero k₁] [CharZero k₂] [CharZero k₃]

/-- `resT_resT` with the composed proof arguments (usable by `rw`/`simp`). -/
lemma resT_trans (hF₁₂ : ∀ x ∈ F D₁, x ∈ F D₂) (hF₂₃ : ∀ x ∈ F D₂, x ∈ F D₃)
    (hW₁₂ : ∀ W : ValuationSubring Ω, (∀ c : k₂, algebraMap k₂ Ω c ∈ W) → t₂ ∈ W →
      (∀ c : k₁, algebraMap k₁ Ω c ∈ W) ∧ t₁ ∈ W)
    (hW₂₃ : ∀ W : ValuationSubring Ω, (∀ c : k₃, algebraMap k₃ Ω c ∈ W) → t₃ ∈ W →
      (∀ c : k₂, algebraMap k₂ Ω c ∈ W) ∧ t₂ ∈ W)
    (hH₁ : D₁.H ≤ D₁.HL) (hH₂ : D₂.H ≤ D₂.HL) (x : ContH1 (Pi D₁) (ZHatOne (F D₁) Ω)) :
    resT D₂ D₃ hF₂₃ hW₂₃ hH₂ (resT D₁ D₂ hF₁₂ hW₁₂ hH₁ x) =
      resT D₁ D₃ (fun y hy => hF₂₃ y (hF₁₂ y hy))
        (fun W hk ht => hW₁₂ W (hW₂₃ W hk ht).1 (hW₂₃ W hk ht).2) hH₁ x :=
  resT_resT x

lemma piT_self (hF : ∀ x ∈ F D₁, x ∈ F D₁)
    (hW : ∀ W : ValuationSubring Ω, (∀ c : k₁, algebraMap k₁ Ω c ∈ W) → t₁ ∈ W →
      (∀ c : k₁, algebraMap k₁ Ω c ∈ W) ∧ t₁ ∈ W) (hH : D₁.H ≤ D₁.HL) (p : Pi D₁) :
    piT D₁ D₁ hF hW hH p = p := by
  induction p using QuotientGroup.induction_on with
  | H σ => exact congrArg (fun h : D₁.H => (h : Pi D₁)) (Subtype.ext rfl)

lemma resT_self (hF : ∀ x ∈ F D₁, x ∈ F D₁)
    (hW : ∀ W : ValuationSubring Ω, (∀ c : k₁, algebraMap k₁ Ω c ∈ W) → t₁ ∈ W →
      (∀ c : k₁, algebraMap k₁ Ω c ∈ W) ∧ t₁ ∈ W) (hH : D₁.H ≤ D₁.HL)
    (x : ContH1 (Pi D₁) (ZHatOne (F D₁) Ω)) : resT D₁ D₁ hF hW hH x = x := by
  induction x using ContH1.induction_on with
  | h c =>
    simp only [resT, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext σ
    simp only [ContH1.cocyclesMap_apply]
    rw [piT_self hF hW hH σ]
    apply Subtype.ext
    funext i
    apply Mu.ext
    apply Units.ext
    rfl

end Trans

/-! ### Geometric stages -/

section Geom

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [IsFunctionField k X.functionField] {τ : X.functionField}

/-- **A geometric stage** of the colimit of [AbsTopIII] Thm 1.9 (d): a finite extension `K₁ / k`
and a coordinate `τ₀ ∈ K(X)` with `coordT τ` regular on `chartOne τ₀` (so
`chartOne τ₀ ⊆ chartOne τ`, `chartOne_le_iff`); the stage is `(chartOne τ₀)_{K₁}`. -/
structure GStage (hτ : Transcendental k τ) where
  /-- The field of constants `K₁`. -/
  K : IntermediateField k (FFClosure X)
  [fin : FiniteDimensional k K]
  /-- The coordinate of the open. -/
  τ₀ : X.functionField
  hτ₀ : Transcendental k τ₀
  htV : coordT τ ∈ chartRing k (coordT τ₀)

namespace GStage

attribute [instance] GStage.fin

variable {k} {hτ : Transcendental k τ}

instance isGalois (g : GStage k hτ) : IsGalois (K₀ k (coordT g.τ₀)) (FFClosure X) :=
  isGalois_K₀_algebraicClosure (k := k) g.τ₀ g.hτ₀

/-- The Galois model `(U_{τ₀})_{K₁}` of a geometric stage. -/
abbrev data (g : GStage k hτ) : GaloisData g.K (coordT g.τ₀) :=
  constExt g.K (curveGaloisData k g.hτ₀)

lemma data_H_le (g : GStage k hτ) : g.data.H ≤ g.data.HL := fun _ hσ =>
  (mem_constExt_HL _).2 ((mem_constExt_H _).1 hσ)

/-- `g ≤ g′`: `K₁ ⊆ K₁′` and `chartOne τ₀′ ⊆ chartOne τ₀`. -/
instance : LE (GStage k hτ) :=
  ⟨fun g g' => g.K ≤ g'.K ∧ coordT g.τ₀ ∈ chartRing k (coordT g'.τ₀)⟩

lemma le_def {g g' : GStage k hτ} :
    g ≤ g' ↔ g.K ≤ g'.K ∧ coordT g.τ₀ ∈ chartRing k (coordT g'.τ₀) := Iff.rfl

lemma mem_chartRing_trans' {x t₁ t₂ : FFClosure X} (h₁ : x ∈ chartRing k t₁)
    (h₂ : t₁ ∈ chartRing k t₂) : x ∈ chartRing k t₂ :=
  mem_chartRing_of_forall fun W hk hW =>
    mem_of_mem_chartRing W hk (mem_of_mem_chartRing W hk hW h₂) h₁

instance : Preorder (GStage k hτ) where
  le_refl g := ⟨le_rfl, self_mem_chartRing k _⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, mem_chartRing_trans' h₁.2 h₂.2⟩

instance : Nonempty (GStage k hτ) := ⟨⟨⊥, τ, hτ, self_mem_chartRing k _⟩⟩

lemma hW_mono {g g' : GStage k hτ} (h : g ≤ g') (W : ValuationSubring (FFClosure X))
    (hK : ∀ c : g'.K, algebraMap g'.K (FFClosure X) c ∈ W) (hW : coordT g'.τ₀ ∈ W) :
    (∀ c : g.K, algebraMap g.K (FFClosure X) c ∈ W) ∧ coordT g.τ₀ ∈ W := by
  have hk : ∀ c : k, algebraMap k (FFClosure X) c ∈ W := fun c => by
    rw [IsScalarTower.algebraMap_apply k g'.K (FFClosure X)]
    exact hK _
  exact ⟨fun c => hK ⟨c, h.1 c.2⟩, mem_of_mem_chartRing W hk hW h.2⟩

instance factH : Fact ((curveGaloisData k hτ).H ≤ (curveGaloisData k hτ).HL) :=
  ⟨curveGaloisData_H_le k hτ⟩

variable [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

/-- A geometric stage as a stage of `Thm19/NFDirectLimit.lean`. -/
def toStage (g : GStage k hτ) : StageIdx (curveGaloisData k hτ) where
  K := g.K
  t' := coordT g.τ₀
  ht' := L_le_L_constExt _ g.K (coordT_mem_curveGaloisData_L k hτ)
  htr' := Transcendental.extendScalars g.K (transcendental_image g.hτ₀)
  htV := (mem_chartRing_iff_of_isAlgebraic g.K).2 g.htV

/-- **The Galois model of a geometric stage** is `constExt K₁ (curveGaloisData k hτ₀)`
(`stage_eq_constExt_newData`, `newData_curveGaloisData`). -/
lemma toStage_data (g : GStage k hτ) : g.toStage.data = g.data := by
  change stage (curveGaloisData k hτ) g.K _ _ = constExt g.K (curveGaloisData k g.hτ₀)
  rw [stage_eq_constExt_newData (curveGaloisData k hτ) g.K _ _
    (coordT_mem_curveGaloisData_L k hτ) (transcendental_image g.hτ₀),
    newData_curveGaloisData k hτ g.hτ₀]

lemma toStage_le_iff {g g' : GStage k hτ} : g.toStage ≤ g'.toStage ↔ g ≤ g' := by
  change g.K ≤ g'.K ∧ coordT g.τ₀ ∈ chartRing g'.K (coordT g'.τ₀) ↔
    g.K ≤ g'.K ∧ coordT g.τ₀ ∈ chartRing k (coordT g'.τ₀)
  rw [mem_chartRing_iff_of_isAlgebraic g'.K]

lemma F_le_of_le_toStage {s : StageIdx (curveGaloisData k hτ)} {g : GStage k hτ}
    (h : s ≤ g.toStage) : ∀ x ∈ F s.data, x ∈ F g.data := by
  rw [← toStage_data g]
  exact Thm19.F_le h

lemma F_toStage (g : GStage k hτ) : ∀ x ∈ F g.data, x ∈ F g.toStage.data := by
  rw [toStage_data g]
  exact fun _ hx => hx

lemma F_mono {g g' : GStage k hτ} (h : g ≤ g') : ∀ x ∈ F g.data, x ∈ F g'.data := by
  rw [← toStage_data g]
  exact F_le_of_le_toStage (toStage_le_iff.2 h)

/-- **Cofinality of the geometric stages** (`exists_stage_ge_coord`). -/
theorem exists_ge_toStage (s : StageIdx (curveGaloisData k hτ)) :
    ∃ g : GStage k hτ, s ≤ g.toStage := by
  obtain ⟨s', hss', -, hL⟩ := exists_stage_ge_coord (curveGaloisData k hτ) s
  rw [curveGaloisData_L] at hL
  obtain ⟨τ₀, hτ₀⟩ := (mem_imageL_iff _).1 hL
  have h1 : Transcendental k s'.t' := fun ha =>
    s'.htr' (ha.extendScalars (algebraMap k s'.K).injective)
  have htr : Transcendental k τ₀ := by
    rw [← transcendental_algebraMap_iff (algebraMap X.functionField (FFClosure X)).injective]
    rw [hτ₀]
    exact h1
  have he : coordT τ₀ = s'.t' := hτ₀
  refine ⟨⟨s'.K, τ₀, htr, ?_⟩, hss'.1, ?_⟩
  · rw [he]
    exact (mem_chartRing_iff_of_isAlgebraic s'.K).1 s'.htV
  · change s.t' ∈ chartRing s'.K (coordT τ₀)
    rw [he]
    exact hss'.2

end GStage

open GStage

variable {k} {hτ : Transcendental k τ}

/-- **The geometric stages are directed** (through the stages of `NFDirectLimit`). -/
instance GStage.isDirectedOrder : IsDirectedOrder (GStage k hτ) where
  directed g₁ g₂ := by
    haveI := isGalois_K₀_algebraicClosure (k := k) τ hτ
    haveI : Fact ((curveGaloisData k hτ).H ≤ (curveGaloisData k hτ).HL) :=
      ⟨curveGaloisData_H_le k hτ⟩
    obtain ⟨s, h₁, h₂⟩ := exists_ge_ge g₁.toStage g₂.toStage
    obtain ⟨g, hg⟩ := exists_ge_toStage s
    exact ⟨g, toStage_le_iff.1 (h₁.trans hg), toStage_le_iff.1 (h₂.trans hg)⟩

/-- `H¹(Π_V, Ẑ(1))` at a geometric stage. -/
abbrev H1G (g : GStage k hτ) : Type u := ContH1 (Pi g.data) (ZHatOne (F g.data) (FFClosure X))

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure on `H¹` of the base change is found slowly
instance (g : GStage k hτ) : CommGroup (H1G g) := inferInstance

/-- The transition map at geometric stages. -/
def resG {g g' : GStage k hτ} (h : g ≤ g') : H1G g →* H1G g' :=
  haveI := isGalois_K₀_algebraicClosure (k := k) τ hτ
  resT g.data g'.data (F_mono h) (hW_mono h) g.data_H_le

instance : DirectedSystem (H1G (hτ := hτ)) (fun _ _ h => resG h) where
  map_self := fun _ x => resT_self _ _ _ x
  map_map := fun _ _ _ _ _ x => resT_resT x

variable (k hτ) in
/-- **`lim→ H¹(Π_V, Ẑ(1))` over the geometric stages.** -/
abbrev GLim : Type u := DirectLimit (H1G (hτ := hτ)) (fun _ _ h => resG h)

/-! ### Comparison with the colimit over all stages -/

variable [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

/-- A geometric stage above a stage. -/
def gsel (s : StageIdx (curveGaloisData k hτ)) : GStage k hτ := (exists_ge_toStage s).choose

lemma le_gsel (s : StageIdx (curveGaloisData k hτ)) : s ≤ (gsel s).toStage :=
  (exists_ge_toStage s).choose_spec

/-- `H¹(Π_V, Ẑ(1)) → GLim`, through a geometric stage above `V`. -/
def toG (s : StageIdx (curveGaloisData k hτ)) : H1S (curveGaloisData k hτ) s →* GLim k hτ :=
  (limOf (fun _ _ h => resG h) (gsel s)).comp
    (resT s.data (gsel s).data (F_le_of_le_toStage (le_gsel s)) (hW_le (le_gsel s))
      (stage_H_le _ s.K s.ht' s.htr'))

/-- `H¹(Π_V, Ẑ(1)) → H1Lim` at a geometric stage. -/
def ofG (g : GStage k hτ) : H1G g →* H1Lim (curveGaloisData k hτ) :=
  (limOf (fun _ _ h => resS h) g.toStage).comp
    (resT g.data g.toStage.data (F_toStage g) (fun _ hK ht => ⟨hK, ht⟩) g.data_H_le)

lemma toG_apply (s : StageIdx (curveGaloisData k hτ)) (x : H1S (curveGaloisData k hτ) s) :
    toG s x = limOf (fun _ _ h => resG h) (gsel s)
      (resT s.data (gsel s).data (F_le_of_le_toStage (le_gsel s)) (hW_le (le_gsel s))
        (stage_H_le _ s.K s.ht' s.htr') x) := rfl

lemma ofG_apply (g : GStage k hτ) (y : H1G g) :
    ofG g y = limOf (fun _ _ h => resS h) g.toStage
      (resT g.data g.toStage.data (F_toStage g) (fun _ hK ht => ⟨hK, ht⟩) g.data_H_le y) := rfl

lemma toG_compat (s s' : StageIdx (curveGaloisData k hτ)) (h : s ≤ s')
    (x : H1S (curveGaloisData k hτ) s) : toG s x = toG s' (resS h x) := by
  obtain ⟨g, h₁, h₂⟩ := exists_ge_ge (gsel s) (gsel s')
  have e1 : resG h₁ (resT s.data (gsel s).data (F_le_of_le_toStage (le_gsel s))
      (hW_le (le_gsel s)) (stage_H_le _ s.K s.ht' s.htr') x) =
      resT s.data g.data _ _ (stage_H_le _ s.K s.ht' s.htr') x := resT_trans _ _ _ _ _ _ x
  have e2 : resT s'.data (gsel s').data (F_le_of_le_toStage (le_gsel s')) (hW_le (le_gsel s'))
      (stage_H_le _ s'.K s'.ht' s'.htr') (resS h x) =
      resT s.data (gsel s').data _ _ (stage_H_le _ s.K s.ht' s.htr') x := resT_trans _ _ _ _ _ _ x
  have e3 : resG h₂ (resT s.data (gsel s').data (fun y hy => F_le_of_le_toStage (le_gsel s') y
      (Thm19.F_le h y hy)) (fun W hk ht => hW_le h W (hW_le (le_gsel s') W hk ht).1
        (hW_le (le_gsel s') W hk ht).2) (stage_H_le _ s.K s.ht' s.htr') x) =
      resT s.data g.data _ _ (stage_H_le _ s.K s.ht' s.htr') x := resT_trans _ _ _ _ _ _ x
  have e : resG h₁ (resT s.data (gsel s).data (F_le_of_le_toStage (le_gsel s))
      (hW_le (le_gsel s)) (stage_H_le _ s.K s.ht' s.htr') x) =
      resG h₂ (resT s'.data (gsel s').data (F_le_of_le_toStage (le_gsel s')) (hW_le (le_gsel s'))
        (stage_H_le _ s'.K s'.ht' s'.htr') (resS h x)) :=
    e1.trans ((congrArg (resG h₂) e2).trans e3).symm
  have l1 := limOf_f (fun _ _ h => resG (hτ := hτ) h) h₁ (resT s.data (gsel s).data
    (F_le_of_le_toStage (le_gsel s)) (hW_le (le_gsel s)) (stage_H_le _ s.K s.ht' s.htr') x)
  have l2 := limOf_f (fun _ _ h => resG (hτ := hτ) h) h₂ (resT s'.data (gsel s').data
    (F_le_of_le_toStage (le_gsel s')) (hW_le (le_gsel s')) (stage_H_le _ s'.K s'.ht' s'.htr')
    (resS h x))
  exact (toG_apply s x).trans (l1.symm.trans
    ((congrArg (limOf (F := H1G (hτ := hτ)) (fun _ _ h => resG h) g) e).trans
      (l2.trans (toG_apply s' (resS h x)).symm)))

lemma ofG_compat (g g' : GStage k hτ) (h : g ≤ g') (y : H1G g) : ofG g y = ofG g' (resG h y) := by
  have e1 : resS (toStage_le_iff.2 h) (resT g.data g.toStage.data (F_toStage g)
      (fun _ hK ht => ⟨hK, ht⟩) g.data_H_le y) =
      resT g.data g'.toStage.data _ _ g.data_H_le y := resT_trans _ _ _ _ _ _ y
  have e2 : resT g'.data g'.toStage.data (F_toStage g') (fun _ hK ht => ⟨hK, ht⟩) g'.data_H_le
      (resG h y) = resT g.data g'.toStage.data _ _ g.data_H_le y := resT_trans _ _ _ _ _ _ y
  have l1 := limOf_f (fun _ _ h => resS (D := curveGaloisData k hτ) h) (toStage_le_iff.2 h)
    (resT g.data g.toStage.data (F_toStage g) (fun _ hK ht => ⟨hK, ht⟩) g.data_H_le y)
  exact (ofG_apply g y).trans (l1.symm.trans
    ((congrArg (limOf (F := H1S (curveGaloisData k hτ)) (fun _ _ h => resS h) g'.toStage)
      (e1.trans e2.symm)).trans
      (ofG_apply g' (resG h y)).symm))

lemma ofG_toG (s : StageIdx (curveGaloisData k hτ)) (x : H1S (curveGaloisData k hτ) s) :
    limLift (fun _ _ h => resG h) ofG ofG_compat (toG s x) = ⟦⟨s, x⟩⟧ := by
  have e : resT (gsel s).data (gsel s).toStage.data (F_toStage (gsel s))
      (fun _ hK ht => ⟨hK, ht⟩) (gsel s).data_H_le (resT s.data (gsel s).data
        (F_le_of_le_toStage (le_gsel s)) (hW_le (le_gsel s)) (stage_H_le _ s.K s.ht' s.htr') x) =
      resS (le_gsel s) x := by
    have e₀ : resT (gsel s).data (gsel s).toStage.data (F_toStage (gsel s))
        (fun _ hK ht => ⟨hK, ht⟩) (gsel s).data_H_le (resT s.data (gsel s).data
          (F_le_of_le_toStage (le_gsel s)) (hW_le (le_gsel s)) (stage_H_le _ s.K s.ht' s.htr') x) =
        resT s.data (gsel s).toStage.data _ _ (stage_H_le _ s.K s.ht' s.htr') x :=
      resT_trans _ _ _ _ _ _ x
    exact e₀.trans rfl
  have l := limOf_f (fun _ _ h => resS (D := curveGaloisData k hτ) h) (le_gsel s) x
  exact (congrArg (limLift (F := H1G (hτ := hτ)) (fun _ _ h => resG h) ofG
    ofG_compat) (toG_apply s x)).trans
    ((limLift_limOf _ _ _ _ _).trans ((ofG_apply _ _).trans
      ((congrArg (limOf (F := H1S (curveGaloisData k hτ)) (fun _ _ h => resS h)
        (gsel s).toStage) e).trans l)))

lemma toG_ofG (g : GStage k hτ) (y : H1G g) :
    limLift (fun _ _ h => resS h) toG toG_compat (ofG g y) = ⟦⟨g, y⟩⟧ := by
  have e : resT g.toStage.data (gsel g.toStage).data (F_le_of_le_toStage (le_gsel g.toStage))
      (hW_le (le_gsel g.toStage)) (stage_H_le _ g.K _ _) (resT g.data g.toStage.data
        (F_toStage g) (fun _ hK ht => ⟨hK, ht⟩) g.data_H_le y) =
      resG (toStage_le_iff.1 (le_gsel g.toStage)) y := by
    have e₀ : resT g.toStage.data (gsel g.toStage).data (F_le_of_le_toStage (le_gsel g.toStage))
        (hW_le (le_gsel g.toStage)) (stage_H_le _ g.K _ _) (resT g.data g.toStage.data
          (F_toStage g) (fun _ hK ht => ⟨hK, ht⟩) g.data_H_le y) =
        resT g.data (gsel g.toStage).data _ _ g.data_H_le y := resT_trans _ _ _ _ _ _ y
    exact e₀.trans rfl
  have l := limOf_f (fun _ _ h => resG (hτ := hτ) h) (toStage_le_iff.1 (le_gsel g.toStage)) y
  exact (congrArg (limLift (F := H1S (curveGaloisData k hτ)) (fun _ _ h => resS h) toG toG_compat)
    (ofG_apply g y)).trans
    ((limLift_limOf _ _ _ _ _).trans ((toG_apply _ _).trans
      ((congrArg (limOf (F := H1G (hτ := hτ)) (fun _ _ h => resG h) (gsel g.toStage)) e).trans
        l)))

/-- **The colimit over all stages is the colimit over the geometric stages.** -/
def h1LimEquivG : H1Lim (curveGaloisData k hτ) ≃* GLim k hτ :=
  mulEquivOfCocones _ _ toG toG_compat ofG ofG_compat ofG_toG toG_ofG

@[simp] lemma h1LimEquivG_mk (s : StageIdx (curveGaloisData k hτ))
    (x : H1S (curveGaloisData k hτ) s) : h1LimEquivG ⟦⟨s, x⟩⟧ = toG s x := rfl

end Geom

end Iut.Reconstruction.Thm19
