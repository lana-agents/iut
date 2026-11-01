/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.StagePiJ
import Iut.Reconstruction.Thm19.PointDecomp
import Iut.Reconstruction.Thm19.ClosedPointDecomp

/-!
# Cuspidal decomposition groups along the stage isomorphisms (MR9 item 4, step 3 (a))

[AbsTopIII] Thm 1.9 (c) (`Topics in Absolute Anabelian Geometry III.txt` l.2153–2157) uses "the
decomposition groups of (a)" of the cusps; for a cusp, the decomposition group is the commensurator
of its inertia group ([AbsTopI] Lemma 4.5 (vi), curves-jacobian `commensurator_arithInertia`), so it
is carried along every isomorphism that carries cuspidal inertia groups to cuspidal inertia groups.
In the Galois models:

* `range_decompToPi_eq_map_decompH'` (any Galois model), `RatPoint.exists_piToGk_decompToPi`
  (the decomposition group of a rational point surjects onto `G_k`, cusps included);
* `map_piRes_inertiaH`, `map_piRes_decompH`, **`commensurator_inertiaH_constExt`**: inertia and
  decomposition groups of `U_{K₁}` inside `Π_U` (`piRes`), and the commensurator property descends
  to `U_{K₁}`;
* **`commensurator_inertiaH_curve`**: `Comm_{Π_U}(I_W) = D_W` for a cusp place `W` of the Galois
  model of a curve (transport of `commensurator_arithInertia` along `piBridge`);
* `map_conj_inertiaH`: `b I_W b⁻¹ = I_{τW}` for `b = [τ]`;
* **`LiftData.exists_map_inertiaH_e`**, **`LiftData.exists_map_inertiaH_constIso`**: the normalised
  lift `e` and the stage isomorphism `constIso e` map each cuspidal inertia group *onto* a
  cuspidal inertia group;
* **`LiftData.map_decompH_constIso`**: they map the decomposition group of the cusp onto that of
  the image cusp;
* `diffClass_sectionCongr_eq_one` (generic): rational points whose decomposition groups correspond
  (up to conjugation in `Π_{X'}`) have matching sections `t_x`; `eta_mapDomain'`
  (`eta_mapDomain` with the sections matched on the support only);
* `LiftData.gkLiftsTo`, `LiftData.cuspPoint`: the image of a `K₁`-rational cusp is
  `ψ(K₁)`-rational (`G_{ψ(K₁)}` lifts to its decomposition group, `ratPointConstExt`);
* **`LiftData.exists_cusp_tSection`** (the point map `β` on the rational cusps and its `hβ`) and
  **`LiftData.eta_mapDomain'`**: `η_{β_* f} = h1Congr (η_f)` for degree-`0` divisors `f` on the
  rational cusps of a stage.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp CurvesJacobian.LocAn
  Belyi Belyi.Anabelian

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

/-! ### Generic Galois models -/

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- **`D_A = image of D_A ∩ H`** for any Galois model. -/
lemma range_decompToPi_eq_map_decompH' (W : ValuationSubring Ω) :
    (decompToPi D W).range =
      (decompH D W).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)) := by
  apply le_antisymm
  · rintro _ ⟨σ, rfl⟩
    refine ⟨ofGalF D σ.1, fun x ↦ ?_, rfl⟩
    change ((ofGalF D σ.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω) x ∈ W ↔ x ∈ W
    rw [ofGalF_apply]
    exact (mem_decompositionSubgroup_iff' W σ.1).1 σ.2 x
  · rintro _ ⟨h, hh, rfl⟩
    refine ⟨⟨toGalF D h, (mem_decompositionSubgroup_iff' W _).2 fun x ↦ ?_⟩, ?_⟩
    · rw [toGalF_apply]
      exact hh x
    · change ((ofGalF D (toGalF D h) : D.H) : Pi D) = (h : Pi D)
      rw [ofGalF_toGalF]

lemma piXToGk_xSection_autCongr (x : RatPoint D) (g : Gk k Ω) :
    piXToGk D (xSection x (AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres) g)) = g := by
  rw [← piJ1ToGk_piXToPiJ1]
  exact (tSection x).piJ1ToGk_toHom g

/-- **The decomposition group of a rational point surjects onto `G_k`** (cusps included). -/
lemma ratPoint_exists_piToGk_decompToPi (x : RatPoint D) (g : Gk k Ω) :
    ∃ σ : x.A.decompositionSubgroup (F D), piToGk D (decompToPi D x.A σ) = g := by
  obtain ⟨σ, hσ⟩ := x.decompositionMap_surjective
    (AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres) g)
  refine ⟨σ, ?_⟩
  have h2 : piToGk D (decompToPi D x.A σ) =
      piXToGk D (xSection x (AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres) g)) := by
    rw [← hσ, xSection_decompositionMap, decompToPiX, MonoidHom.comp_apply, piXToGk_piUToPiX]
  rw [h2]
  exact piXToGk_xSection_autCongr x g

variable (K₁ : IntermediateField k Ω) [FiniteDimensional k K₁]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **`piRes` maps the inertia group of `U_{K₁}` onto that of `U`** (at a place `W ⊇ k`). -/
lemma map_piRes_inertiaH {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W) :
    ((inertiaH (constExt K₁ D) W).map
        (QuotientGroup.mk' (GaloisPi1.kernel (constExt K₁ D).H (constExt K₁ D).S))).map
        (piRes K₁ D) =
      (inertiaH D W).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)) := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact piRes_mem_map_inertiaH hy
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := exists_piRes_eq_of_mem_map_inertiaH (K₁ := K₁) hk hx
    exact ⟨y, hy, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **`D_W(U_{K₁}) = D_W(U) ∩ Π_{U_{K₁}}`** inside `Π_U`. -/
lemma map_piRes_decompH (W : ValuationSubring Ω) :
    ((decompH (constExt K₁ D) W).map
        (QuotientGroup.mk' (GaloisPi1.kernel (constExt K₁ D).H (constExt K₁ D).S))).map
        (piRes K₁ D) =
      (decompH D W).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)) ⊓ (piRes K₁ D).range := by
  apply le_antisymm
  · rintro _ ⟨y, ⟨σ, hσ, rfl⟩, rfl⟩
    refine ⟨⟨hRes K₁ D σ, fun z => ?_, rfl⟩, ⟨_, rfl⟩⟩
    change ((hRes K₁ D σ : D.H) : Ω ≃ₐ[K₀ k t] Ω) z ∈ W ↔ z ∈ W
    rw [coe_hRes, resK_apply]
    exact hσ z
  · rintro x ⟨⟨h, hh, rfl⟩, ⟨y, hy⟩⟩
    have hσ' : FixesK K₁ (piToGk D (h : Pi D)) := by
      have e : piToGk D (h : Pi D) = piToGk D (piRes K₁ D y) := by
        rw [hy]
        rfl
      rw [e]
      exact piToGk_piRes_fixesK K₁ y
    have hfix : ∀ c : K₁, (h : Ω ≃ₐ[K₀ k t] Ω) (algebraMap K₁ Ω c) = algebraMap K₁ Ω c := by
      intro c
      have h1 := algebraMap_hToGk_apply D h ⟨_, algebraMap_mem_kbar c⟩
      rw [← h1]
      change algebraMap (kbar k Ω) Ω (piToGk D (h : Pi D) _) = _
      rw [hσ' c]
      rfl
    obtain ⟨σ, hσ⟩ := exists_hRes_eq (K := K₁) D hfix
    refine ⟨(σ : Pi (constExt K₁ D)), ⟨σ, fun z => ?_, rfl⟩, ?_⟩
    · have hz : ((hRes K₁ D σ : D.H) : Ω ≃ₐ[K₀ k t] Ω) z ∈ W ↔ z ∈ W := by
        rw [hσ]
        exact hh z
      rw [coe_hRes, resK_apply] at hz
      exact hz
    · change ((hRes K₁ D σ : D.H) : Pi D) = (h : Pi D)
      rw [hσ]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **The commensurator property descends to `U_{K₁}`**: if `Comm_{Π_U}(I_W) = D_W`, then
`Comm_{Π_{U_{K₁}}}(I_W) = D_W` (at a place `W ⊇ k`). -/
theorem commensurator_inertiaH_constExt {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    (h : Subgroup.Commensurable.commensurator
        ((inertiaH D W).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S))) =
      (decompH D W).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S))) :
    Subgroup.Commensurable.commensurator ((inertiaH (constExt K₁ D) W).map
        (QuotientGroup.mk' (GaloisPi1.kernel (constExt K₁ D).H (constExt K₁ D).S))) =
      (decompH (constExt K₁ D) W).map
        (QuotientGroup.mk' (GaloisPi1.kernel (constExt K₁ D).H (constExt K₁ D).S)) := by
  apply Subgroup.map_injective (piRes_injective (K := K₁) D)
  rw [map_commensurator_of_injective _ (piRes_injective (K := K₁) D), map_piRes_inertiaH K₁ hk, h,
    map_piRes_decompH]

/-- Images along two composable squares agree. -/
lemma map_map_eq_of_comm {G₁ G₂ G₃ G₄ : Type*} [Group G₁] [Group G₂] [Group G₃] [Group G₄]
    (A : Subgroup G₁) (E : G₁ →* G₂) (r' : G₂ →* G₃) (r : G₁ →* G₄) (e : G₄ →* G₃)
    (h : ∀ p, r' (E p) = e (r p)) : (A.map E).map r' = (A.map r).map e := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext h

/-- `τ⁻¹(τW) = W`. -/
lemma transPlace_inv_transPlace {P : Type u} [Field P] [Algebra P Ω] (τ : Ω ≃ₐ[P] Ω)
    (W : ValuationSubring Ω) : transPlace τ⁻¹ (transPlace τ W) = W := by
  ext x
  rw [mem_transPlace, mem_transPlace]
  change τ.symm (τ.symm.symm x) ∈ W ↔ x ∈ W
  rw [AlgEquiv.symm_symm, AlgEquiv.symm_apply_apply]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **`b I_W b⁻¹ = I_{τW}`** for `b = [τ]`. -/
lemma map_conj_inertiaH (τ : D.H) (W : ValuationSubring Ω) :
    ((inertiaH D W).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S))).map
        (MulAut.conj (τ : Pi D)).toMonoidHom =
      (inertiaH D (transPlace (τ : Ω ≃ₐ[K₀ k t] Ω) W)).map
        (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_map_inertiaH τ hx
  · intro y hy
    have h := conj_mem_map_inertiaH τ⁻¹ hy
    have e : transPlace ((τ⁻¹ : D.H) : Ω ≃ₐ[K₀ k t] Ω) (transPlace (τ : Ω ≃ₐ[K₀ k t] Ω) W) = W :=
      transPlace_inv_transPlace (τ : Ω ≃ₐ[K₀ k t] Ω) W
    rw [e] at h
    refine ⟨_, h, ?_⟩
    change (τ : Pi D) * (((τ⁻¹ : D.H) : Pi D) * y * ((τ⁻¹ : D.H) : Pi D)⁻¹) * (τ : Pi D)⁻¹ = y
    rw [QuotientGroup.mk_inv]
    group

end Generic

/-! ### `Comm(I_W) = D_W` for the Galois model of a curve -/

section Curve

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
include Ω hU in
/-- **`Comm_{Π_U}(I_W) = D_W` at a cusp place** of the Galois model of a curve ([AbsTopI]
Lemma 4.5 (vi), `Topics in Absolute Anabelian Geometry I.txt` l.2840; curves-jacobian
`commensurator_arithInertia`, transported along `piBridge`). -/
theorem commensurator_inertiaH_curve (W : ValuationSubring (FFClosure C.Xbar))
    (hW : W ∈ CuspW (k := K) (t := coordT τ)) :
    Subgroup.Commensurable.commensurator ((inertiaH (curveGaloisData K hτ) W).map
        (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ).H
          (curveGaloisData K hτ).S))) =
      (decompH (curveGaloisData K hτ) W).map
        (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ).H
          (curveGaloisData K hτ).S)) := by
  apply Subgroup.map_injective (f := (piBridge (Ω := Ω) hτ hU).toMulEquiv.toMonoidHom)
    (piBridge (Ω := Ω) hτ hU).injective
  rw [map_commensurator_mulEquiv (piBridge (Ω := Ω) hτ hU).toMulEquiv,
    map_inertiaH_piBridge hτ hU,
    commensurator_arithInertia Ω C hc.out ((isCuspPlace_comap_iff (Ω := Ω) hτ hU W).2 hW),
    map_decompH_piBridge hτ hU]

end Curve


/-! ### Sections of rational points with matching decomposition groups -/

section Sections

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω']
  (X : PiX D ≃ₜ* PiX D') (ψ : Gk k Ω ≃ₜ* Gk k' Ω')
  (hX : ∀ y, piXToGk D' (X y) = ψ (piXToGk D y))
  [Fact (Function.Surjective (piJ1ToGk D))] [Fact (Function.Surjective (piJ1ToGk D'))]

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_X`, `Π_{J¹}` are found slowly
/-- **Rational points whose decomposition groups correspond have matching sections**: if the image
in `Π_{X'}` of `D_{y}` lies in `γ X(D_x) γ⁻¹`, then the transported section `t_x` and `t_y` have
trivial difference class (`exists_conj_of_forall_exists'`, `diffClass_eq_one_of_conj`). -/
theorem diffClass_sectionCongr_eq_one (x : RatPoint D) (y : RatPoint D') (γ : PiX D')
    (h : ∀ σ : y.A.decompositionSubgroup (F D'), ∃ σ' : x.A.decompositionSubgroup (F D),
      decompToPiX D' y.A σ = γ * X (decompToPiX D x.A σ') * γ⁻¹) :
    diffClass (sectionCongr X ψ hX (tSection x)) (tSection y) = 1 := by
  let s : Gk k' Ω' →* PiX D' := X.toMulEquiv.toMonoidHom.comp ((xSection x).comp
    ((AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres)).toMonoidHom.comp
      ψ.symm.toMulEquiv.toMonoidHom))
  let s' : Gk k' Ω' →* PiX D' := (xSection y).comp
    (AlgEquiv.autCongr (kbarEquiv y.A y.hk y.hkres)).toMonoidHom
  have hs : ∀ g, piXToGk D' (s g) = g := fun g => by
    change piXToGk D' (X (xSection x (AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres)
      (ψ.symm g)))) = g
    rw [hX, piXToGk_xSection_autCongr, ContinuousMulEquiv.apply_symm_apply]
  have hs' : ∀ g, piXToGk D' (s' g) = g := fun g => piXToGk_xSection_autCongr y g
  obtain ⟨δ, hδ, hconj⟩ := exists_conj_of_forall_exists' (piXToGk D') s s' hs hs' γ fun g => by
    obtain ⟨σ, hσ⟩ := y.decompositionMap_surjective
      (AlgEquiv.autCongr (kbarEquiv y.A y.hk y.hkres) g)
    obtain ⟨σ', hσ'⟩ := h σ
    refine ⟨ψ ((AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres)).symm
      (Decomposition.decompositionMap (F D) x.A x.hk x.hkres σ')), ?_⟩
    change xSection y (AlgEquiv.autCongr (kbarEquiv y.A y.hk y.hkres) g) =
      γ * X (xSection x (AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres) (ψ.symm (ψ
        ((AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres)).symm
          (Decomposition.decompositionMap (F D) x.A x.hk x.hkres σ')))))) * γ⁻¹
    rw [ContinuousMulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply, ← hσ,
      xSection_decompositionMap, xSection_decompositionMap]
    exact hσ'
  refine diffClass_eq_one_of_conj _ _ (q := piXToPiJ1 D' δ)
    (by rw [MonoidHom.mem_ker, piJ1ToGk_piXToPiJ1]; exact hδ) fun g => ?_
  change piXToPiJ1 D' (s' g) = piXToPiJ1 D' δ *
    piJ1Congr X ψ hX (piXToPiJ1 D (xSection x (AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres)
      (ψ.symm g)))) * (piXToPiJ1 D' δ)⁻¹
  rw [piJ1Congr_piXToPiJ1, hconj g, map_mul, map_mul, map_inv]
  rfl

variable (β : RatPoint D → RatPoint D')

set_option synthInstance.maxHeartbeats 400000 in
-- the action of `G_k` on `Δ_X^{ab}` is found slowly
/-- `etaDiv_mapDomain` with matching sections required only on the support. -/
theorem etaDiv_mapDomain' (f : RatPoint D →₀ ℤ) (x₀ : RatPoint D)
    (hβ : ∀ x ∈ f.support,
      diffClass (sectionCongr X ψ hX (tSection x)) (tSection (β x)) = 1)
    (hx₀ : x₀ ∈ f.support) :
    etaDiv (f.mapDomain β) (β x₀) =
      h1Congr ψ (deltaAbCongr X ψ hX) (deltaAbCongr_smul' X ψ hX) (etaDiv f x₀) := by
  rw [etaDiv, etaDiv, h1Congr_etaWith, etaWith, etaWith,
    Finsupp.prod_mapDomain_index (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)]
  refine Finsupp.prod_congr fun x hx => ?_
  rw [diffClass_eq_of_conj X ψ hX (hβ x hx) (hβ x₀ hx₀)]

set_option synthInstance.maxHeartbeats 400000 in
-- the action of `G_k` on `Δ_X^{ab}` is found slowly
/-- **`η_D` along the isomorphisms, sections matched on the support only** (e.g. a divisor on
the cusps and the map of rational cusps of `LiftData.exists_cusp_tSection`). -/
theorem eta_mapDomain' (f : RatPoint D →₀ ℤ)
    (hβ : ∀ x ∈ f.support,
      diffClass (sectionCongr X ψ hX (tSection x)) (tSection (β x)) = 1)
    (hf : (f.sum fun _ n => n) = 0) :
    eta (f.mapDomain β) =
      h1Congr ψ (deltaAbCongr X ψ hX) (deltaAbCongr_smul' X ψ hX) (eta f) := by
  rcases f.support.eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · rw [Finsupp.support_eq_empty.1 h, Finsupp.mapDomain_zero, eta_zero, eta_zero, map_one]
  · rw [eta_eq_etaDiv f hf x₀, eta_eq_etaDiv _ ((sum_mapDomain_deg β f).trans hf) (β x₀),
      etaDiv_mapDomain' X ψ hX β f x₀ hβ hx₀]

end Sections

end Iut.Reconstruction.Thm19

/-! ### Along lift data -/

namespace Iut.Reconstruction

open Thm19

/-! ### `Comm(I_W) = D_W` at the geometric stages -/

section GStageComm

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
omit [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] in
include Ω hU in
/-- **`Comm(I_W) = D_W` at a cusp of a geometric stage** `(V_{τ₀})_{K₁}`. -/
theorem GStage.commensurator_inertiaH (g' : GStage K hτ) (W : ValuationSubring (FFClosure C.Xbar))
    (hW : W ∈ CuspW (k := K) (t := coordT g'.τ₀)) :
    Subgroup.Commensurable.commensurator ((inertiaH g'.data W).map
        (QuotientGroup.mk' (GaloisPi1.kernel g'.data.H g'.data.S))) =
      (Thm19.decompH g'.data W).map (QuotientGroup.mk' (GaloisPi1.kernel g'.data.H g'.data.S)) :=
  commensurator_inertiaH_constExt g'.K hW.1
    (commensurator_inertiaH_curve Ω (C := subCurve C (chartOne K C.Xbar g'.τ₀)
      (chartOne_le_U hτ hU g'.hτ₀ g'.htV) (chartOne_ne g'.τ₀)) g'.hτ₀ rfl W hW)

end GStageComm

section Stage

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
  {Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out)} {g : GStage K hτ}

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **The normalised lift maps each cuspidal inertia group onto a cuspidal inertia group**
(`galLift φ`: `IsCor38Lift.exists_map_inertiaH_galLift`; the conjugation: `map_conj_inertiaH`). -/
theorem LiftData.exists_map_inertiaH_e (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (W : ValuationSubring (FFClosure C.Xbar)) (hW : W ∈ CuspW (k := K) (t := coordT g.τ₀)) :
    ∃ W'' ∈ CuspW (k := K₂) (t := coordT L.υ),
      ((inertiaH (curveGaloisData K g.hτ₀) W).map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K g.hτ₀).H
            (curveGaloisData K g.hτ₀).S))).map L.e.toMulEquiv.toMonoidHom =
        (inertiaH (curveGaloisData K₂ L.hυ) W'').map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K₂ L.hυ).H
            (curveGaloisData K₂ L.hυ).S)) := by
  obtain ⟨W', hW', hEq⟩ := L.hφ.exists_map_inertiaH_galLift Φ g.hτ₀ rfl L.hυ rfl L.φ W hW
  obtain ⟨b, hb⟩ := L.hb
  obtain ⟨τb, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨transPlace (τb : FFClosure C₂.Xbar ≃ₐ[K₀ K₂ (coordT L.υ)] FFClosure C₂.Xbar) W',
    transPlace_mem_CuspW hW' _, ?_⟩
  have hcomp : L.e.toMulEquiv.toMonoidHom =
      (MulAut.conj ((τb : (curveGaloisData K₂ L.hυ).H) :
        Pi (curveGaloisData K₂ L.hυ))).toMonoidHom.comp
        (galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ).toMulEquiv.toMonoidHom :=
    MonoidHom.ext fun x => hb x
  rw [hcomp, ← Subgroup.map_map, hEq]
  exact map_conj_inertiaH τb W'

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **The stage isomorphism maps each cuspidal inertia group onto a cuspidal inertia group**
(`exists_map_inertiaH_e`, `piRes_constIso`, `map_piRes_inertiaH`, `piRes` injective). -/
theorem LiftData.exists_map_inertiaH_constIso (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (W : ValuationSubring (FFClosure C.Xbar)) (hW : W ∈ CuspW (k := g.K) (t := coordT g.τ₀)) :
    ∃ W'' ∈ CuspW (k := L.tgt.K) (t := coordT L.υ),
      ((inertiaH g.data W).map (QuotientGroup.mk' (GaloisPi1.kernel g.data.H g.data.S))).map
          (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
            g.K).toMulEquiv.toMonoidHom =
        (inertiaH L.tgt.data W'').map
          (QuotientGroup.mk' (GaloisPi1.kernel L.tgt.data.H L.tgt.data.S)) := by
  have hW₀ := mem_CuspW_of_constExt g.K hW
  obtain ⟨W'', hW'', hEq⟩ := L.exists_map_inertiaH_e W hW₀
  refine ⟨W'', mem_CuspW_constExt _ hW'', ?_⟩
  apply Subgroup.map_injective (piRes_injective (K := L.tgt.K) (curveGaloisData K₂ L.hυ))
  refine (map_map_eq_of_comm _ _ _ (piRes g.K (curveGaloisData K g.hτ₀))
    L.e.toMulEquiv.toMonoidHom fun p => piRes_constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk
      (piToGk_surjective_curve g.hτ₀) g.K p).trans ?_
  refine (congrArg (fun S => S.map L.e.toMulEquiv.toMonoidHom)
    (map_piRes_inertiaH g.K hW₀.1)).trans ?_
  exact hEq.trans (map_piRes_inertiaH L.tgt.K hW''.1).symm

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **The stage isomorphism maps the decomposition group of a cusp onto that of the image cusp**
(`Comm(I_W) = D_W` on both sides, `map_commensurator_mulEquiv`). -/
theorem LiftData.map_decompH_constIso (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (W : ValuationSubring (FFClosure C.Xbar)) (hW : W ∈ CuspW (k := g.K) (t := coordT g.τ₀))
    (W'' : ValuationSubring (FFClosure C₂.Xbar))
    (hW'' : W'' ∈ CuspW (k := L.tgt.K) (t := coordT L.υ))
    (hEq : ((inertiaH g.data W).map
        (QuotientGroup.mk' (GaloisPi1.kernel g.data.H g.data.S))).map
          (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
            g.K).toMulEquiv.toMonoidHom =
        (inertiaH L.tgt.data W'').map
          (QuotientGroup.mk' (GaloisPi1.kernel L.tgt.data.H L.tgt.data.S))) :
    ((Thm19.decompH g.data W).map (QuotientGroup.mk' (GaloisPi1.kernel g.data.H g.data.S))).map
        (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
          g.K).toMulEquiv.toMonoidHom =
      (Thm19.decompH L.tgt.data W'').map
        (QuotientGroup.mk' (GaloisPi1.kernel L.tgt.data.H L.tgt.data.S)) := by
  rw [← GStage.commensurator_inertiaH Ω hτ hU g W (mem_CuspW_of_constExt g.K hW),
    ← GStage.commensurator_inertiaH Ω₂ hτ₂ hU₂ L.tgt W'' (mem_CuspW_of_constExt L.tgt.K hW''),
    map_commensurator_mulEquiv, hEq]

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **The image cusp is `ψ(K₁)`-rational** if the cusp is `K₁`-rational: `G_{ψ(K₁)}` lifts to
its decomposition group (`D_x ↠ G_{K₁}`, `LiftData.piToGk_e`, `piRes_decompToPi`). -/
theorem LiftData.gkLiftsTo (L : LiftData hτ hU hτ₂ hU₂ Φ g) (x : RatPoint g.data)
    (W'' : ValuationSubring (FFClosure C₂.Xbar))
    (hD : ((Thm19.decompH g.data x.A).map
        (QuotientGroup.mk' (GaloisPi1.kernel g.data.H g.data.S))).map
        (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
          g.K).toMulEquiv.toMonoidHom =
      (Thm19.decompH L.tgt.data W'').map
        (QuotientGroup.mk' (GaloisPi1.kernel L.tgt.data.H L.tgt.data.S))) :
    GkLiftsTo (curveGaloisData K₂ L.hυ) L.tgt.K W'' := by
  intro g' hg'
  obtain ⟨p, rfl⟩ := piToGk_surjective_curve L.hυ g'
  obtain ⟨q, rfl⟩ := (mem_range_piRes_iff (K := L.tgt.K) (curveGaloisData K₂ L.hυ) p).2 hg'
  obtain ⟨σ, hσ⟩ := ratPoint_exists_piToGk_decompToPi x (L.gk.symm (piToGk L.tgt.data q))
  have hmem : constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K
      (decompToPi g.data x.A σ) ∈ (decompToPi L.tgt.data W'').range := by
    rw [range_decompToPi_eq_map_decompH', ← hD]
    refine Subgroup.mem_map_of_mem _ ?_
    rw [← range_decompToPi_eq_map_decompH']
    exact ⟨σ, rfl⟩
  obtain ⟨σ₁, hσ₁⟩ := hmem
  refine ⟨⟨_, toGalF_hRes_mem_decomp L.tgt.K W'' σ₁⟩, ?_⟩
  rw [← piRes_decompToPi, hσ₁, piToGk_piRes, piToGk_piRes, L.piToGk_e, hσ,
    ContinuousMulEquiv.apply_symm_apply]

/-- **The image cusp as a `ψ(K₁)`-rational point** of the target stage. -/
def LiftData.cuspPoint (L : LiftData hτ hU hτ₂ hU₂ Φ g) (x : RatPoint g.data)
    (W'' : ValuationSubring (FFClosure C₂.Xbar))
    (hW'' : W'' ∈ CuspW (k := L.tgt.K) (t := coordT L.υ))
    (hD : ((Thm19.decompH g.data x.A).map
        (QuotientGroup.mk' (GaloisPi1.kernel g.data.H g.data.S))).map
        (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
          g.K).toMulEquiv.toMonoidHom =
      (Thm19.decompH L.tgt.data W'').map
        (QuotientGroup.mk' (GaloisPi1.kernel L.tgt.data.H L.tgt.data.S))) :
    RatPoint L.tgt.data :=
  ratPointConstExt L.tgt.K W'' (mem_CuspW_of_constExt L.tgt.K hW'').1
    (isIntegral_residueField_of_ne (D := curveGaloisData K₂ L.hυ) W''
      (mem_CuspW_of_constExt L.tgt.K hW'').1
      ⟨⟨coordT L.υ, coordT_mem_F (curveGaloisData K₂ L.hυ)⟩, hW''.2⟩)
    (L.gkLiftsTo x W'' hD)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
lemma LiftData.piX_piUToPiX (L : LiftData hτ hU hτ₂ hU₂ Φ g) (p : Pi g.data) :
    L.piX (piUToPiX g.data p) = piUToPiX L.tgt.data
      (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K p) :=
  piXCongr_piUToPiX _ _ p

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **[AbsTopIII] Thm 1.9 (c), the sections `t_x` of rational cusps along the stage
isomorphism**: for a `K₁`-rational cusp `x` of the stage there is a `ψ(K₁)`-rational cusp `y` of
the target stage whose inertia group is the image of that of `x`, and whose section `t_y` has
trivial difference class against the transported `t_x` (the input `hβ` of
`LiftData.eta_mapDomain`). -/
theorem LiftData.exists_cusp_tSection (L : LiftData hτ hU hτ₂ hU₂ Φ g) (x : RatPoint g.data)
    (hx : coordT g.τ₀ ∉ x.A) :
    ∃ y : RatPoint L.tgt.data, coordT L.υ ∉ y.A ∧
      ((inertiaH g.data x.A).map (QuotientGroup.mk' (GaloisPi1.kernel g.data.H g.data.S))).map
          (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
            g.K).toMulEquiv.toMonoidHom =
        (inertiaH L.tgt.data y.A).map
          (QuotientGroup.mk' (GaloisPi1.kernel L.tgt.data.H L.tgt.data.S)) ∧
      diffClass (sectionCongr L.piX L.gk L.piXToGk_piX (tSection x)) (tSection y) = 1 := by
  obtain ⟨W'', hW'', hEq⟩ := L.exists_map_inertiaH_constIso x.A ⟨x.hk, hx⟩
  have hD := L.map_decompH_constIso x.A ⟨x.hk, hx⟩ W'' hW'' hEq
  refine ⟨L.cuspPoint x W'' hW'' hD, hW''.2, hEq, ?_⟩
  refine diffClass_sectionCongr_eq_one L.piX L.gk L.piXToGk_piX x _ 1 fun σ => ?_
  have hmem : decompToPi L.tgt.data W'' σ ∈ ((decompToPi g.data x.A).range).map
      (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
        g.K).toMulEquiv.toMonoidHom := by
    rw [range_decompToPi_eq_map_decompH', hD, ← range_decompToPi_eq_map_decompH']
    exact ⟨σ, rfl⟩
  obtain ⟨d, ⟨σ', rfl⟩, hd⟩ := hmem
  refine ⟨σ', ?_⟩
  rw [one_mul, inv_one, mul_one]
  change piUToPiX L.tgt.data (decompToPi L.tgt.data W'' σ) =
    L.piX (piUToPiX g.data (decompToPi g.data x.A σ'))
  rw [L.piX_piUToPiX]
  exact congrArg (piUToPiX L.tgt.data) hd.symm

set_option synthInstance.maxHeartbeats 400000 in
-- the action of `G_{K₁}` on `Δ_X^{ab}` is found slowly
/-- **`η_D` at a stage along the lift data**, for a map `β` of `K₁`-rational points with
matching sections on the support of `f` (e.g. `f` on the rational cusps,
`LiftData.exists_cusp_tSection`). -/
theorem LiftData.eta_mapDomain' (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (β : RatPoint g.data → RatPoint L.tgt.data) (f : RatPoint g.data →₀ ℤ)
    (hβ : ∀ x ∈ f.support,
      diffClass (sectionCongr L.piX L.gk L.piXToGk_piX (tSection x)) (tSection (β x)) = 1)
    (hf : (f.sum fun _ n => n) = 0) :
    eta (f.mapDomain β) =
      h1Congr L.gk L.deltaAb (deltaAbCongr_smul' L.piX L.gk L.piXToGk_piX) (eta f) :=
  Thm19.eta_mapDomain' L.piX L.gk L.piXToGk_piX β f hβ hf

end Stage

end Iut.Reconstruction
