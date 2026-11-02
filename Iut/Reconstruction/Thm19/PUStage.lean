/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.CuspDecomp
import Iut.Reconstruction.Thm19.PlaceConj
import Iut.Reconstruction.Thm19.ConstExtThmC

/-!
# `P_V` along the stage isomorphisms (MR9 item 4, step 3 (c))

[AbsTopIII] Thm 1.9 (c) (`Topics in Absolute Anabelian Geometry III.txt` l.2153–2157) constructs
`P_U ⊆ H¹(Π_U, μ_Ẑ(Π_U))` from the cuspidal principal divisors, via the synchronizations of (b)
and the criterion of Prop 1.6 (ii) (l.1993–2000). For the functoriality of Thm 1.9 the subgroups
`P_V` of the stages must be carried along the stage isomorphisms `LiftData.S`:

* generic: `isCuspPlaceF_placeOfF_iff`, `idxVal_ne_top_of_cusp`, `divAt_ratDivF_eq_zero`
  (divisors on the cusps vanish at places over `U`), **`res_h1Congr_of_eq`** (the residue of a
  transported class at a transported inertia element), **`mem_PU_iff_eta_of`**
  (`mem_PU_iff_principal` with the criterion `η_f = 1 ↔ f principal` as an input);
* **`eta_eq_one_iff_principal_constExt`**: that criterion for `U_K`, `K` finite over a number
  field `k`, `X` with a `k`-rational point (Prop 1.6 (ii); the hypotheses of curves-jacobian
  `eta_eq_one_iff_principal` are transported along `fBcConstExt` as in
  `placeOfF_eq_of_ratSectionGk_conj_constExt`);
* `LiftData.TameCompat χU L`: the stage isomorphism and the coefficients `cycloVχ χU` carry the
  tame generator `θ_p` of a cusp to the tame generator of the image cusp (for `χU = cycloIso Φ`
  this is the functoriality of the synchronizations of Prop 1.4 (ii), l.1771–1802, which
  Thm 1.9 (b) uses; it is an explicit argument here, see `Plans/MR9Plan.md`, item 4 (b-i));
* **`LiftData.hrat_tgt`**: if every cusp of the stage is `K₁`-rational, every cusp of the target
  stage is `ψ(K₁)`-rational;
* **`LiftData.S_mem_PU`**: `LiftData.S` maps `P_V` into `P_{V'}` (at stages whose cusps are
  rational, given `TameCompat`).
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

/-! ### Generic Galois models -/

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

/-- The place of a rational point is a cusp iff `t ∉ A`. -/
lemma isCuspPlaceF_placeOfF_iff (x : RatPoint D) : IsCuspPlaceF (placeOfF x) ↔ t ∉ x.A :=
  Iff.rfl

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- At a cusp, the valuation subring of `F` below `p` is proper. -/
lemma idxVal_ne_top_of_cusp (p : InertiaIndex D) (hp : t ∉ p.1.1) : idxVal p ≠ ⊤ := by
  intro h
  have : CurvesJacobian.tF D ∈ idxVal p := h ▸ ValuationSubring.mem_top _
  exact hp this

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- The place below a cusp `p` is a cusp place. -/
lemma isCuspPlaceF_idxPlace (p : InertiaIndex D) (hp : t ∉ p.1.1) :
    IsCuspPlaceF (idxPlace p (idxVal_ne_top_of_cusp p hp)) :=
  hp

/-- **Divisors on the cusps vanish at places over `U`.** -/
lemma divAt_ratDivF_eq_zero (f : RatPoint D →₀ ℤ) (hf : ∀ x ∈ f.support, t ∉ x.A)
    (p : InertiaIndex D) (hp : t ∈ p.1.1) : divAt (ratDivF f) p = 0 := by
  classical
  unfold divAt
  split_ifs with h
  · refine Finsupp.notMem_support_iff.1 fun hP => ?_
    obtain ⟨x, hx, hxP⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hP)
    have h1 : CurvesJacobian.tF D ∉ (placeOfF x).1 := hf x hx
    rw [hxP] at h1
    exact h1 hp
  · rfl

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- The zero divisor has multiplicity `0` everywhere. -/
lemma divAt_zero (p : InertiaIndex D) : divAt (0 : Divisor k (F D)) p = 0 := by
  unfold divAt
  split_ifs <;> rfl

/-- Equality of places of `F` below a rational point and below an inertia index. -/
lemma placeOfF_eq_idxPlace_iff (x : RatPoint D) (p : InertiaIndex D) (hp : idxVal p ≠ ⊤) :
    placeOfF x = idxPlace p hp ↔
      x.A.comap (algebraMap (F D) Ω) = p.1.1.comap (algebraMap (F D) Ω) :=
  ⟨fun h => congrArg Subtype.val h, fun h => Place.ext h⟩

/-- **`mem_PU_iff_principal` with the criterion of Prop 1.6 (ii)** (`η_f = 1` iff `f` is
principal, for degree-`0` divisors on rational points) as an input. -/
theorem mem_PU_iff_eta_of [Fact (Function.Surjective (piJ1ToGk D))]
    (hEta : ∀ f : RatPoint D →₀ ℤ, (f.sum fun _ m => m) = 0 →
      (eta f = 1 ↔ ratDivF f ∈ principal k (F D)))
    (hrat : ∀ P : Place k (F D), IsCuspPlaceF P → ∃ x : RatPoint D, placeOfF x = P)
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    η ∈ PU D ↔ ∃ f : RatPoint D →₀ ℤ,
      (∀ x ∈ f.support, IsCuspPlaceF (placeOfF x)) ∧ (f.sum fun _ m => m) = 0 ∧ eta f = 1 ∧
        HasResidues η (ratDivF f) := by
  rw [mem_PU_iff_principal hrat]
  constructor
  · rintro ⟨f, hs, hp, hr⟩
    obtain ⟨g, hg, hd⟩ := mem_principal.1 hp
    have h0 := sum_eq_zero_of_div_eq f hg hd
    exact ⟨f, hs, h0, (hEta f h0).2 hp, hr⟩
  · rintro ⟨f, hs, h0, he, hr⟩
    exact ⟨f, hs, (hEta f h0).1 he, hr⟩

variable {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω']
  (e : Pi D ≃ₜ* Pi D') (χ : ZHatOne (F D) Ω ≃ₜ* ZHatOne (F D') Ω')
  (hχ : ∀ p z, χ (p • z) = e p • χ z)

/-- **The residue of a transported class at a transported inertia element.** -/
theorem res_h1Congr_of_eq (p : InertiaIndex D) (p' : InertiaIndex D')
    (heq : ((p'.1.2 : D'.H) : Pi D') = e ((p.1.2 : D.H) : Pi D))
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    res D' (h1Congr e χ hχ η) p' = χ (res D η p) :=
  (res_apply _ _ _).trans ((evalTriv_congr_elem heq
    (pi_inertia_smul_zHatOne p'.2.1 p'.2.2 _)
    (smul_eq_self_of_h1Congr _ χ hχ (pi_inertia_smul_zHatOne p.2.1 p.2.2 _)) _).trans
    ((evalTriv_h1Congr _ χ hχ (pi_inertia_smul_zHatOne p.2.1 p.2.2 _) η).trans
      (congrArg χ (res_apply _ η p).symm)))

/-- The inertia group of `W` in `Π_U`. -/
abbrev inertiaPi (D : GaloisData k t) (W : ValuationSubring Ω) : Subgroup (Pi D) :=
  (inertiaH D W).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S))

/-- **Every cusp of `U'` is rational** if those of `U` are and `e` matches the cusps
(`hsymm`: each cuspidal inertia group of `U'` is the image of one of `U`; `hpt`: the image of a
rational cusp is a rational cusp; `hcomap`: `e` matches "same place of `F`"). -/
theorem hrat_of
    (hsymm : ∀ p' : InertiaIndex D', t' ∉ p'.1.1 → ∃ p : InertiaIndex D, t ∉ p.1.1 ∧
      (inertiaPi D p.1.1).map e.toMulEquiv.toMonoidHom = inertiaPi D' p'.1.1 ∧
      ((p'.1.2 : D'.H) : Pi D') = e ((p.1.2 : D.H) : Pi D))
    (Q : RatPoint D → RatPoint D' → Prop)
    (hpt : ∀ x : RatPoint D, t ∉ x.A → ∃ y : RatPoint D', t' ∉ y.A ∧
      (inertiaPi D x.A).map e.toMulEquiv.toMonoidHom = inertiaPi D' y.A ∧ Q x y)
    (hcomap : ∀ W₁ W₂ : ValuationSubring Ω, W₁ ∈ CuspW (k := k) (t := t) →
      W₂ ∈ CuspW (k := k) (t := t) → ∀ W₁'' W₂'' : ValuationSubring Ω',
      W₁'' ∈ CuspW (k := k') (t := t') → W₂'' ∈ CuspW (k := k') (t := t') →
      (inertiaPi D W₁).map e.toMulEquiv.toMonoidHom = inertiaPi D' W₁'' →
      (inertiaPi D W₂).map e.toMulEquiv.toMonoidHom = inertiaPi D' W₂'' →
      (W₁.comap (algebraMap (F D) Ω) = W₂.comap (algebraMap (F D) Ω) ↔
        W₁''.comap (algebraMap (F D') Ω') = W₂''.comap (algebraMap (F D') Ω')))
    (hrat : ∀ P : Place k (F D), IsCuspPlaceF P → ∃ x : RatPoint D, placeOfF x = P)
    (P' : Place k' (F D')) (hP' : IsCuspPlaceF P') : ∃ y : RatPoint D', placeOfF y = P' := by
  obtain ⟨W'', hW''⟩ := CurvesJacobian.exists_valuationSubring_liesOver D' P'
  have hk'' : ∀ c : k', algebraMap k' Ω' c ∈ W'' := fun c => by
    have h : algebraMap (F D') Ω' (algebraMap k' (F D') c) ∈ W'' :=
      (hW'' (algebraMap k' (F D') c)).2 (P'.2.2 c)
    rwa [← IsScalarTower.algebraMap_apply] at h
  have ht'' : t' ∉ W'' := fun h => hP' ((hW'' (CurvesJacobian.tF D')).1 h)
  obtain ⟨p, hp, hEq, -⟩ := hsymm ⟨(W'', 1), hk'', (inertiaH D' W'').one_mem⟩ ht''
  have hne : idxVal p ≠ ⊤ := idxVal_ne_top_of_cusp p hp
  obtain ⟨x, hx⟩ := hrat (idxPlace p hne) (isCuspPlaceF_idxPlace p hp)
  have hxc : t ∉ x.A := by
    intro h
    have h1 : CurvesJacobian.tF D ∈ (placeOfF x).1 := h
    rw [hx] at h1
    exact hp h1
  obtain ⟨y, hy, hIy, -⟩ := hpt x hxc
  refine ⟨y, Place.ext ?_⟩
  have h2 := (hcomap x.A p.1.1 ⟨x.hk, hxc⟩ ⟨p.2.1, hp⟩ y.A W'' ⟨y.hk, hy⟩ ⟨hk'', ht''⟩ hIy
    hEq).1 ((placeOfF_eq_idxPlace_iff x p hne).1 hx)
  refine h2.trans ?_
  ext z
  exact hW'' z

set_option maxHeartbeats 1600000 in
-- the residues `ContH1.evalTriv` unify slowly
/-- **`h1Congr e χ` maps `P_U` into `P_{U'}`** ([AbsTopIII] Thm 1.9 (c), generic form): if the
cusps of `U` are rational, Prop 1.6 (ii) holds on both sides (`hEta`, `hEta'`), `e` matches the
cusps (`hsymm`, `hpt`, `hcomap`), the classes `η_f` (`heta`, for point maps with `Q` on the
support) and the tame generators (`hT`). -/
theorem h1Congr_mem_PU [Fact (Function.Surjective (piJ1ToGk D))]
    [Fact (Function.Surjective (piJ1ToGk D'))] (hH' : D'.H ≤ D'.HL)
    (hEta : ∀ f : RatPoint D →₀ ℤ, (f.sum fun _ m => m) = 0 →
      (eta f = 1 ↔ ratDivF f ∈ principal k (F D)))
    (hEta' : ∀ f : RatPoint D' →₀ ℤ, (f.sum fun _ m => m) = 0 →
      (eta f = 1 ↔ ratDivF f ∈ principal k' (F D')))
    (hsymm : ∀ p' : InertiaIndex D', t' ∉ p'.1.1 → ∃ p : InertiaIndex D, t ∉ p.1.1 ∧
      (inertiaPi D p.1.1).map e.toMulEquiv.toMonoidHom = inertiaPi D' p'.1.1 ∧
      ((p'.1.2 : D'.H) : Pi D') = e ((p.1.2 : D.H) : Pi D))
    (Q : RatPoint D → RatPoint D' → Prop)
    (hpt : ∀ x : RatPoint D, t ∉ x.A → ∃ y : RatPoint D', t' ∉ y.A ∧
      (inertiaPi D x.A).map e.toMulEquiv.toMonoidHom = inertiaPi D' y.A ∧ Q x y)
    (heta : ∀ (β : RatPoint D → RatPoint D') (f : RatPoint D →₀ ℤ),
      (∀ x ∈ f.support, Q x (β x)) → (f.sum fun _ m => m) = 0 → eta f = 1 →
        eta (f.mapDomain β) = 1)
    (hcomap : ∀ W₁ W₂ : ValuationSubring Ω, W₁ ∈ CuspW (k := k) (t := t) →
      W₂ ∈ CuspW (k := k) (t := t) → ∀ W₁'' W₂'' : ValuationSubring Ω',
      W₁'' ∈ CuspW (k := k') (t := t') → W₂'' ∈ CuspW (k := k') (t := t') →
      (inertiaPi D W₁).map e.toMulEquiv.toMonoidHom = inertiaPi D' W₁'' →
      (inertiaPi D W₂).map e.toMulEquiv.toMonoidHom = inertiaPi D' W₂'' →
      (W₁.comap (algebraMap (F D) Ω) = W₂.comap (algebraMap (F D) Ω) ↔
        W₁''.comap (algebraMap (F D') Ω') = W₂''.comap (algebraMap (F D') Ω')))
    (hT : ∀ (p : InertiaIndex D) (p' : InertiaIndex D'), t ∉ p.1.1 → t' ∉ p'.1.1 →
      ((p'.1.2 : D'.H) : Pi D') = e ((p.1.2 : D.H) : Pi D) → χ (tameGen p) = tameGen p')
    (hrat : ∀ P : Place k (F D), IsCuspPlaceF P → ∃ x : RatPoint D, placeOfF x = P)
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) (hη : η ∈ PU D) : h1Congr e χ hχ η ∈ PU D' := by
  classical
  obtain ⟨f, hfs, hf0, hfe, hfr⟩ := (mem_PU_iff_eta_of hEta hrat η).1 hη
  refine (mem_PU_iff_eta_of hEta' (hrat_of e hsymm Q hpt hcomap hrat) _).2 ?_
  have hcusp : ∀ x ∈ f.support, t ∉ x.A := hfs
  -- the residues at a cusp of `U'` (for any divisor `E'` with the matching multiplicity)
  have hres : ∀ (E' : Divisor k' (F D')) (hE'0 : ∀ p', t' ∈ p'.1.1 → divAt E' p' = 0)
      (hE' : ∀ (p : InertiaIndex D) (p' : InertiaIndex D'), t ∉ p.1.1 → t' ∉ p'.1.1 →
        (inertiaPi D p.1.1).map e.toMulEquiv.toMonoidHom = inertiaPi D' p'.1.1 →
        divAt E' p' = divAt (ratDivF f) p),
      HasResidues (h1Congr e χ hχ η) E' := by
    intro E' hE'0 hE' p'
    by_cases hp' : t' ∈ p'.1.1
    · refine (res_eq_one_of_mem hH' (h1Congr e χ hχ η) p' hp').trans ?_
      rw [hE'0 p' hp', zpow_zero]
    · obtain ⟨p, hp, hEq, hpp⟩ := hsymm p' hp'
      have h1 : res D η p = tameGen p ^ divAt (ratDivF f) p := hfr p
      have h2 : χ (tameGen p) = tameGen p' := hT p p' hp hp' hpp
      have h3 : divAt E' p' = divAt (ratDivF f) p := hE' p p' hp hp' hEq
      calc res D' (h1Congr e χ hχ η) p' = χ (res D η p) := res_h1Congr_of_eq e χ hχ p p' hpp η
        _ = χ (tameGen p ^ divAt (ratDivF f) p) := congrArg χ h1
        _ = χ (tameGen p) ^ divAt (ratDivF f) p := map_zpow χ _ _
        _ = tameGen p' ^ divAt E' p' := by rw [h2, h3]
  rcases f.support.eq_empty_or_nonempty with hf | ⟨x₀, hx₀⟩
  · have hf' : f = 0 := Finsupp.support_eq_empty.1 hf
    subst hf'
    refine ⟨0, by simp, by simp, eta_zero, hres _ (fun p' _ => ?_) fun p p' _ _ _ => ?_⟩
    · rw [ratDivF, Finsupp.mapDomain_zero, divAt_zero]
    · simp only [ratDivF, Finsupp.mapDomain_zero, divAt_zero]
  let β : RatPoint D → RatPoint D' := fun x =>
    if h : t ∉ x.A then (hpt x h).choose else (hpt x₀ (hcusp x₀ hx₀)).choose
  have hβspec : ∀ x ∈ f.support, t' ∉ (β x).A ∧
      (inertiaPi D x.A).map e.toMulEquiv.toMonoidHom = inertiaPi D' (β x).A ∧ Q x (β x) :=
    fun x hx => by
      have hb : β x = (hpt x (hcusp x hx)).choose := dif_pos (hcusp x hx)
      rw [hb]
      exact (hpt x (hcusp x hx)).choose_spec
  have hsupp : ∀ y ∈ (f.mapDomain β).support, t' ∉ y.A := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hy)
    exact (hβspec x hx).1
  refine ⟨f.mapDomain β, hsupp, (sum_mapDomain_deg β f).trans hf0,
    heta β f (fun x hx => (hβspec x hx).2.2) hf0 hfe,
    hres _ (divAt_ratDivF_eq_zero _ hsupp) fun p p' hp hp' hEq => ?_⟩
  refine divAt_ratDivF_eq_of_iff β f p p' (idxVal_ne_top_of_cusp p hp)
    (idxVal_ne_top_of_cusp p' hp') fun x hx => ?_
  rw [placeOfF_eq_idxPlace_iff, placeOfF_eq_idxPlace_iff]
  exact (hcomap x.A p.1.1 ⟨x.hk, hcusp x hx⟩ ⟨p.2.1, hp⟩ (β x).A p'.1.1
    ⟨(β x).hk, (hβspec x hx).1⟩ ⟨p'.2.1, hp'⟩ (hβspec x hx).2.1 hEq).symm

end Generic

/-! ### Prop 1.6 (ii) for `U_K` -/

section Curve

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  [CharZero (FFClosure X)] (K : IntermediateField k (FFClosure X)) [FiniteDimensional k K]

attribute [local instance] CurvesJacobian.isFunctionField_F

/-- **[AbsTopIII] Prop 1.6 (ii) for `U_K`** (`K` finite over a number field `k`, `X` with a
`k`-rational point): a degree-`0` divisor `∑ nᵢ xᵢ` on `K`-rational points is principal iff
`η_D = 1`. -/
theorem eta_eq_one_iff_principal_constExt [NumberField k]
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (f : RatPoint (constExt K (curveGaloisData k hτ)) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0) :
    eta f = 1 ↔ ratDivF f ∈ principal K (F (constExt K (curveGaloisData k hτ))) := by
  haveI : NumberField K := NumberField.of_module_finite k K
  set φ := fBcConstExt (curveGaloisData k hτ) K
  have hφ := fBcConstExt_tr k hτ K
  exact eta_eq_one_iff_principal
    (isKummerFaithfulJac_constExt K
      (isDivFreeOver_curve k hτ σ hσ K (jacDivFree_numberField' X σ hσ K)))
    (exists_nsmul_eq_of_tr φ (kbarConstExt K) hφ fun N hN y hy => by
      obtain ⟨w, hw⟩ := exists_nsmul_eq_jacPsi k hτ σ hσ hN.ne' ⟨y, hy⟩
      exact ⟨w, congrArg Subtype.val hw⟩)
    (fun N _ => weilDual_bijective_of_tr φ (kbarConstExt K) hφ
      (weilPairing_nondegenerate_baseChange k hτ))
    (fun N _ => finite_picTorsion_of_tr φ (kbarConstExt K) hφ N) f hf

end Curve

end Iut.Reconstruction.Thm19

/-! ### Along lift data -/

namespace Iut.Reconstruction

open Thm19

section Stage

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

variable (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))
  (hχU : CycloEquivariant (bridgeIso hτ hU hτ₂ hU₂ Φ) χU)

/-- **Tame generators along the stage isomorphism**: the coefficient isomorphism
`constCyclo (cycloVχ χU)` sends the tame generator `θ_p` at a cusp `p = (W, σ)` of the stage to
the tame generator at every cusp `p' = (W', σ')` of the target stage with `[σ'] = constIso e [σ]`.
For `χU = cycloIso Φ` this is the functoriality of the synchronizations of [AbsTopIII]
Prop 1.4 (ii) (`Topics in Absolute Anabelian Geometry III.txt` l.1771–1802), used by Thm 1.9 (b),
(c) (l.2144–2157); it enters the results below as an explicit argument (`Plans/MR9Plan.md`,
item 4 (b-i)). -/
def LiftData.TameCompat (L : LiftData hτ hU hτ₂ hU₂ Φ g) : Prop :=
  ∀ (p : InertiaIndex g.data) (p' : InertiaIndex L.tgt.data), coordT g.τ₀ ∉ p.1.1 →
    coordT L.υ ∉ p'.1.1 →
    ((p'.1.2 : L.tgt.data.H) : Pi L.tgt.data) =
      constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K
        ((p.1.2 : g.data.H) : Pi g.data) →
    constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K (tameGen p) = tameGen p'

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
omit [CharZero (FFClosure C.Xbar)] [CharZero (FFClosure C₂.Xbar)] in
/-- **Every cusp inertia element of the target stage is the image of a cusp inertia element of
the source stage** (`exists_map_inertiaH_constIso_symm`). -/
theorem LiftData.exists_inertiaIndex_symm (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (p' : InertiaIndex L.tgt.data) (hp' : coordT L.υ ∉ p'.1.1) :
    ∃ p : InertiaIndex g.data, coordT g.τ₀ ∉ p.1.1 ∧
      ((inertiaH g.data p.1.1).map (QuotientGroup.mk' (GaloisPi1.kernel g.data.H g.data.S))).map
          (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
            g.K).toMulEquiv.toMonoidHom =
        (inertiaH L.tgt.data p'.1.1).map
          (QuotientGroup.mk' (GaloisPi1.kernel L.tgt.data.H L.tgt.data.S)) ∧
      ((p'.1.2 : L.tgt.data.H) : Pi L.tgt.data) =
        constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K
          ((p.1.2 : g.data.H) : Pi g.data) := by
  obtain ⟨W, hW, hEq⟩ := L.exists_map_inertiaH_constIso_symm p'.1.1 ⟨p'.2.1, hp'⟩
  have hmem : ((p'.1.2 : L.tgt.data.H) : Pi L.tgt.data) ∈ (inertiaH L.tgt.data p'.1.1).map
      (QuotientGroup.mk' (GaloisPi1.kernel L.tgt.data.H L.tgt.data.S)) :=
    ⟨p'.1.2, p'.2.2, rfl⟩
  rw [← hEq] at hmem
  obtain ⟨y, ⟨σ, hσ, rfl⟩, hy⟩ := hmem
  exact ⟨⟨(W, σ), hW.1, hσ⟩, hW.2, hEq, hy.symm⟩

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V`, the coefficients and the sections unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **[AbsTopIII] Thm 1.9 (c) along the stage isomorphisms: `LiftData.S (P_V) ⊆ P_{V'}`** at a
stage whose cusps are `K₁`-rational, given the tame generators along the stage isomorphism
(`TameCompat`) and rational points of both compactifications (Prop 1.6 (ii) on both sides;
`h1Congr_mem_PU` with `exists_inertiaIndex_symm`, `exists_cusp_tSection`, `eta_mapDomain'`,
`comap_eq_iff`). -/
theorem LiftData.S_mem_PU (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
    (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
    (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
    (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
    (hrat : ∀ P : Place g.K (F g.data), IsCuspPlaceF P → ∃ x : RatPoint g.data, placeOfF x = P)
    (hT : L.TameCompat χU) (η : H1G g) (hη : η ∈ PU g.data) :
    L.S χU hχU η ∈ PU L.tgt.data :=
  h1Congr_mem_PU
    (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K)
    (constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K)
    (constCyclo_smul L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
      (cycloVχ χU g.hτ₀ L.hυ) (cycloVχ_smul χU _ hχU g.hτ₀ L.hυ L.he) g.K)
    L.tgt.data_H_le
    (eta_eq_one_iff_principal_constExt K g.hτ₀ g.K σ₀ hσ₀)
    (eta_eq_one_iff_principal_constExt K₂ L.hυ L.tgt.K σ₂ hσ₂)
    L.exists_inertiaIndex_symm
    (fun x y => diffClass (sectionCongr L.piX L.gk L.piXToGk_piX (tSection x)) (tSection y) = 1)
    L.exists_cusp_tSection
    (fun β f hβ hf he => by rw [L.eta_mapDomain' β f hβ hf, he, map_one])
    (fun W₁ W₂ hW₁ hW₂ W₁'' W₂'' hW₁'' hW₂'' h₁ h₂ =>
      L.comap_eq_iff W₁ W₂ hW₁ hW₂ W₁'' W₂'' hW₁'' hW₂'' h₁ h₂)
    hT hrat η hη

end Stage

end Iut.Reconstruction
