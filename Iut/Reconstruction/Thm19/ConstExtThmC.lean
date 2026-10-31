/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.PointDecomp
import Iut.Reconstruction.Thm19.StageJac

/-!
# [LocAn] Theorem C over a finite extension of the field of constants

[GalSect] Thm 1.3 (i) (`Galois Sections.txt` l.265–266) for *closed* points `x` of `U` is reduced
to rational points of `U_K` for a finite extension `K ⊇ κ(x)` of the field of constants `k`.
curves-jacobian proves [LocAn] Thm C (profinite) for a generic Galois model `D′`
(`LocAn.placeOfF_eq_of_ratSectionGk_conj`) under hypotheses on `J(k̄)`: divisibility,
perfectness of the Weil pairing, finiteness of `J[N]` and genus `≠ 0` of `F(baseChange D′)`,
known for `D′ = curveGaloisData k hτ`. Here they are transported to
`D′ = constExt K (curveGaloisData k hτ)`, whose geometric function field `F K̄` is that of `U`
(inside `Ω`), along a ring isomorphism which is semilinear for `K̄ ≅ k̄` (both the algebraic
closure of `k` in `Ω`):

* semilinear transport along curves-jacobian's `picTr`: `deg_divTr`, `deg_picTr`,
  `exists_nsmul_eq_of_tr` (divisibility), `picTorsionTr_bijective`, `finite_picTorsion_of_tr`,
  `weilPairing_nondegenerate_of_tr`, `weilDual_bijective_of_tr` (via `weilPairing_tr`),
  `mem_L_divTr`, `ell_divTr`, **`genus_eq_of_tr`** (the genus is invariant under semilinear
  isomorphisms of function fields);
* `mem_F_baseChange_constExt_iff`, **`fBcConstExt`** `: F(baseChange (constExt K D)) ≃+*
  F(baseChange D)` (the identity of `Ω`) over `kbarConstExt : K̄ ≃+* k̄`;
* **`isKummerFaithfulJac_constExt`**: `⋂_N N · Pic(F k̄)^{H_K} = 0` gives Kummer-faithfulness of the
  Jacobian of `U_K` (as `isKummerFaithfulJac_stage`);
* `mem_range_of_isAlgebraic_F_constExt`: `K` is the field of constants of `U_K` when `k` is that
  of `U`;
* **`placeOfF_eq_of_ratSectionGk_conj_constExt`**: [LocAn] Thm C (profinite) for rational points of
  `U_K`, `K` finite over a number field `k`, `X` of genus `≠ 0` with a rational point.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

/-! ### Semilinear transport of the hypotheses of Theorem C -/

section Semilinear

variable {κ K κ' K' : Type*} [Field κ] [Field K] [Algebra κ K] [Field κ'] [Field K']
  [Algebra κ' K'] (φ : K ≃+* K') (ψ : κ ≃+* κ')
  (hφ : ∀ c : κ, φ (algebraMap κ K c) = algebraMap κ' K' (ψ c))
  [IsAlgClosed κ] [IsFunctionField κ K] [IsAlgClosed κ'] [IsFunctionField κ' K']

/-- `φ` preserves degrees of divisors (all places have degree `1`). -/
theorem deg_divTr (A : Divisor κ K) : (divTr φ ψ hφ A).deg = A.deg := by
  induction A using Finsupp.induction_linear with
  | zero => rw [map_zero, Divisor.deg_zero, Divisor.deg_zero]
  | add A B hA hB => rw [map_add, Divisor.deg_add, Divisor.deg_add, hA, hB]
  | single P n =>
    change Divisor.deg (Finsupp.equivMapDomain (placeTrEquiv φ ψ hφ) (Finsupp.single P n)) = _
    rw [Finsupp.equivMapDomain_single, Divisor.deg_single, Divisor.deg_single,
      Place.deg_eq_one_of_isAlgClosed, Place.deg_eq_one_of_isAlgClosed]

theorem deg_picTr (x : Pic κ K) : Pic.deg κ' K' (picTr φ ψ hφ x) = Pic.deg κ K x := by
  induction x using QuotientAddGroup.induction_on with
  | H A => rw [picTr_mk, Pic.deg_mk, Pic.deg_mk, deg_divTr]

include hφ in
/-- **Divisibility of `J` transports.** -/
theorem exists_nsmul_eq_of_tr
    (h : ∀ N : ℕ, 0 < N → ∀ y : Pic κ' K', Pic.deg κ' K' y = 0 → ∃ w, N • w = y) :
    ∀ N : ℕ, 0 < N → ∀ y : Pic κ K, Pic.deg κ K y = 0 → ∃ w, N • w = y := by
  intro N hN y hy
  obtain ⟨w, hw⟩ := h N hN (picTr φ ψ hφ y) (by rw [deg_picTr, hy])
  refine ⟨(picTr φ ψ hφ).symm w, (picTr φ ψ hφ).injective ?_⟩
  rw [map_nsmul, AddEquiv.apply_symm_apply, hw]

lemma picTorsionTr_bijective (n : ℕ) : Function.Bijective (picTorsionTr φ ψ hφ n) := by
  refine ⟨fun a b h => Subtype.ext ((picTr φ ψ hφ).injective (congrArg Subtype.val h)),
    fun b => ?_⟩
  refine ⟨⟨(picTr φ ψ hφ).symm b, ?_⟩, Subtype.ext ?_⟩
  · change n • (picTr φ ψ hφ).symm b = 0
    rw [← map_nsmul, show n • (b : Pic κ' K') = 0 from b.2, map_zero]
  · exact (picTr φ ψ hφ).apply_symm_apply _

include hφ in
/-- **Finiteness of `J[n]` transports.** -/
lemma finite_picTorsion_of_tr (n : ℕ) [Finite (picTorsion κ' K' n)] :
    Finite (picTorsion κ K n) :=
  Finite.of_injective _ (picTorsionTr_bijective φ ψ hφ n).1

include hφ in
/-- **Nondegeneracy of the Weil pairing transports** (`e_n(φ a, φ b) = ψ(e_n(a, b))`). -/
theorem weilPairing_nondegenerate_of_tr {n : ℕ} [NeZero n]
    (h : ∀ a : picTorsion κ' K' n, (∀ b, weilPairing n a b = 1) → a = 0)
    (a : picTorsion κ K n) (ha : ∀ b, weilPairing n a b = 1) : a = 0 := by
  have h0 := h (picTorsionTr φ ψ hφ n a) fun b' ↦ by
    obtain ⟨b, rfl⟩ := (picTorsionTr_bijective φ ψ hφ n).2 b'
    rw [weilPairing_tr, ha b, map_one]
  exact (picTorsionTr_bijective φ ψ hφ n).1 (h0.trans (map_zero _).symm)

include hφ in
/-- **Perfectness of the Weil pairing transports.** -/
theorem weilDual_bijective_of_tr {n : ℕ} [NeZero n] [CharZero κ] [Finite (picTorsion κ' K' n)]
    (h : ∀ a : picTorsion κ' K' n, (∀ b, weilPairing n a b = 1) → a = 0) :
    Function.Bijective (weilDual (κ := κ) (K := K) (n := n)) :=
  haveI := finite_picTorsion_of_tr φ ψ hφ n
  weilDual_bijective (weilPairing_nondegenerate_of_tr φ ψ hφ h)

theorem mem_L_divTr (A : Divisor κ K) (f : K) :
    φ f ∈ Divisor.L (divTr φ ψ hφ A) ↔ f ∈ Divisor.L A := by
  rw [Divisor.mem_L, Divisor.mem_L, map_eq_zero_iff φ φ.injective]
  refine or_congr Iff.rfl ?_
  rw [← (placeTrEquiv φ ψ hφ).forall_congr_right]
  refine forall_congr' fun P ↦ ?_
  rw [placeTrEquiv_apply, divTr_apply_placeTr, ord_placeTr]

/-- `φ : L(A) ≃ L(φ A)` (additively; semilinear along `ψ`). -/
def lTr (A : Divisor κ K) : Divisor.L A ≃+ Divisor.L (divTr φ ψ hφ A) where
  toFun m := ⟨φ (m : K), (mem_L_divTr φ ψ hφ A m).2 m.2⟩
  invFun y := ⟨φ.symm y, (mem_L_divTr φ ψ hφ A _).1 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv m := Subtype.ext (φ.symm_apply_apply _)
  right_inv y := Subtype.ext (φ.apply_symm_apply _)
  map_add' a b := Subtype.ext (map_add φ (a : K) b)

theorem ell_divTr (A : Divisor κ K) : (divTr φ ψ hφ A).ell = A.ell := by
  have h := lift_rank_eq_of_equiv_equiv ψ (lTr φ ψ hφ A) ψ.bijective fun r m => Subtype.ext (by
    change φ (r • (m : K)) = ψ r • φ (m : K)
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ])
  unfold Divisor.ell Module.finrank
  rw [← Cardinal.toNat_lift.{u_2}, ← h, Cardinal.toNat_lift]

include hφ in
/-- **The genus is invariant under semilinear isomorphisms of function fields.** -/
theorem genus_eq_of_tr : genus κ' K' = genus κ K := by
  unfold genus Divisor.riemannConst
  congr 2
  rw [← (divTr φ ψ hφ).surjective.range_comp]
  congr 1
  funext A
  simp only [Function.comp_apply, deg_divTr, ell_divTr]

end Semilinear

/-! ### `F K̄` of `U_K` is `F k̄` of `U` -/

section ConstExt

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [CharZero Ω] (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K]

attribute [local instance] CurvesJacobian.isFunctionField_F

variable (D) in
/-- **`F K̄` of `U_K` is `F k̄` of `U`** inside `Ω`. -/
theorem mem_F_baseChange_constExt_iff {x : Ω} :
    x ∈ F (baseChange (constExt K D)) ↔ x ∈ F (baseChange D) := by
  constructor
  · intro hx
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    intro σ hσ
    have hσ' : resK₀ k t σ ∈ D.H := (mem_baseChange_H D).1 hσ
    obtain ⟨σ', hσ'e⟩ := exists_algEquiv_K₀ (E := kbar K Ω) (t' := t)
      (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω).toRingEquiv (fun c => by
        have hc : (c : Ω) ∈ kbar k Ω := (mem_kbar_stage_iff K).1 c.2
        exact σ.commutes ⟨_, (K₀ (kbar k Ω) t).algebraMap_mem ⟨_, hc⟩⟩)
      (σ.commutes ⟨t, IntermediateField.mem_adjoin_simple_self _ t⟩)
    have hmem : σ' ∈ (baseChange (constExt K D)).H := by
      rw [mem_baseChange_H, mem_constExt_H]
      have e : resK k K t (resK₀ K t σ') = resK₀ k t σ := AlgEquiv.ext fun y => by
        rw [resK_apply, resK₀_apply, resK₀_apply, hσ'e]
        rfl
      rw [e]
      exact hσ'
    have := hx σ' hmem
    rw [hσ'e] at this
    exact this
  · intro hx
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    intro σ hσ
    have hσ' : resK k K t (resK₀ K t σ) ∈ D.H :=
      (mem_constExt_H D).1 ((mem_baseChange_H (constExt K D)).1 hσ)
    obtain ⟨σ₀, hσ₀e⟩ := exists_algEquiv_K₀ (E := kbar k Ω) (t' := t)
      (σ : Ω ≃ₐ[K₀ (kbar K Ω) t] Ω).toRingEquiv (fun c => by
        have hc : (c : Ω) ∈ kbar K Ω := (mem_kbar_stage_iff K).2 c.2
        exact σ.commutes ⟨_, (K₀ (kbar K Ω) t).algebraMap_mem ⟨_, hc⟩⟩)
      (σ.commutes ⟨t, IntermediateField.mem_adjoin_simple_self _ t⟩)
    have hmem : σ₀ ∈ (baseChange D).H := by
      rw [mem_baseChange_H]
      have e : resK₀ k t σ₀ = resK k K t (resK₀ K t σ) := AlgEquiv.ext fun y => by
        rw [resK_apply, resK₀_apply, resK₀_apply, hσ₀e]
        rfl
      rw [e]
      exact hσ'
    have := hx σ₀ hmem
    rw [hσ₀e] at this
    exact this

/-- `K̄ = k̄` inside `Ω`. -/
def kbarConstExt : kbar K Ω ≃+* kbar k Ω where
  toFun c := ⟨c, (mem_kbar_stage_iff K).1 c.2⟩
  invFun c := ⟨c, (mem_kbar_stage_iff K).2 c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

variable (D) in
/-- **`F K̄` of `U_K` is `F k̄` of `U`** (the identity of `Ω`). -/
def fBcConstExt : F (baseChange (constExt K D)) ≃+* F (baseChange D) where
  toFun x := ⟨x, (mem_F_baseChange_constExt_iff D K).1 x.2⟩
  invFun y := ⟨y, (mem_F_baseChange_constExt_iff D K).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[simp] lemma coe_fBcConstExt (x : F (baseChange (constExt K D))) :
    ((fBcConstExt D K x : F (baseChange D)) : Ω) = x :=
  Subtype.coe_mk _ _

lemma mapsConst_fBcConstExt :
    MapsConst (fBcConstExt D K) (kbar K Ω) (kbar k Ω) := fun c =>
  ⟨kbarConstExt K c, rfl⟩

lemma mapsConst_fBcConstExt_symm :
    MapsConst (fBcConstExt D K).symm (kbar k Ω) (kbar K Ω) := fun c =>
  ⟨(kbarConstExt K).symm c, rfl⟩

/-! ### Kummer-faithfulness of the Jacobian of `U_K` -/

variable (D) in
/-- **`Pic(F K̄)` of `U_K` is `Pic(F k̄)` of `U`.** -/
def picConstExtEquiv :
    Pic (kbar K Ω) (F (baseChange (constExt K D))) ≃+ Pic (kbar k Ω) (F (baseChange D)) :=
  picEquivS (mapsConst_fBcConstExt K) (mapsConst_fBcConstExt_symm K)

/-- `picConstExtEquiv` maps `Pic^{G_K}` of `U_K` into the `H_K`-invariant classes. -/
theorem picConstExtEquiv_mem_inv {y : Pic (kbar K Ω) (F (baseChange (constExt K D)))}
    (hy : y ∈ Kummer.picInv (constExt K D)) : picConstExtEquiv D K y ∈ picInvOver D K := by
  intro h hK
  obtain ⟨g, rfl⟩ := exists_hRes_eq (K := K) D hK
  have e := picEquivS_picMap (mapsConst_fBcConstExt K) (mapsConst_fBcConstExt_symm K)
    (autF (constExt K D) g) (autF D (hRes K D g)) (fun x => Subtype.ext (by
      simp only [coe_fBcConstExt, coe_autF_apply, coe_hRes, resK_apply])) y
  change picConstExtEquiv D K (picAct (constExt K D) g y) =
    picAct D (hRes K D g) (picConstExtEquiv D K y) at e
  rw [← e, hy g]

/-- **Kummer-faithfulness of the Jacobian of `U_K`** from `⋂_N N · Pic(F k̄)^{H_K} = 0`. -/
theorem isKummerFaithfulJac_constExt (hJ : IsDivFreeOver D K) :
    IsKummerFaithfulJac (constExt K D) := by
  intro x hx
  apply (picConstExtEquiv D K).injective
  rw [map_zero]
  refine hJ _ fun N hN => ?_
  obtain ⟨y, hy, hyx⟩ := hx N hN
  exact ⟨picConstExtEquiv D K y, picConstExtEquiv_mem_inv K hy, by rw [← map_nsmul, hyx]⟩

/-! ### The field of constants of `U_K` -/

/-- **`K` is the field of constants of `U_K`** if `k` is that of `U`. -/
theorem mem_range_of_isAlgebraic_F_constExt
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (x : F (constExt K D)) (hx : IsAlgebraic K x) :
    x ∈ Set.range (algebraMap K (F (constExt K D))) := by
  have hxΩ : IsAlgebraic K (x : Ω) :=
    (isAlgebraic_algHom_iff ((F (constExt K D)).val.restrictScalars K)
      (F (constExt K D)).val.injective).2 hx
  have hxk : (x : Ω) ∈ kbar k Ω := (mem_kbar_stage_iff K).1 (mem_algebraicClosure_iff.2 hxΩ)
  obtain ⟨c, hc⟩ := exists_eq_of_forall_fix_constExt (K := K) ⟨_, hxk⟩ fun g hg => by
    obtain ⟨h, rfl⟩ := hToGk_surjective D hk g
    have hfix : ∀ c : K, (h : Ω ≃ₐ[K₀ k t] Ω) (algebraMap K Ω c) = algebraMap K Ω c := by
      intro c
      have := congrArg (algebraMap (kbar k Ω) Ω) (hg c)
      rwa [algebraMap_hToGk_apply] at this
    obtain ⟨σ, rfl⟩ := exists_hRes_eq (K := K) D hfix
    apply Subtype.ext
    change algebraMap (kbar k Ω) Ω (hToGk D (hRes K D σ) _) = _
    rw [algebraMap_hToGk_apply, coe_hRes, resK_apply]
    exact (IntermediateField.mem_fixedField_iff _ _).1 x.2 _ σ.2
  exact ⟨c, Subtype.ext hc⟩

end ConstExt

/-! ### Theorem C for rational points of `U_K` -/

section Curve

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  [CharZero (FFClosure X)] (K : IntermediateField k (FFClosure X)) [FiniteDimensional k K]

attribute [local instance] CurvesJacobian.isFunctionField_F

/-- `K̄`-semilinearity of `fBcConstExt`. -/
lemma fBcConstExt_tr (c : kbar K (FFClosure X)) :
    fBcConstExt (curveGaloisData k hτ) K
        (algebraMap (kbar K (FFClosure X))
          (F (baseChange (constExt K (curveGaloisData k hτ)))) c) =
      algebraMap (kbar k (FFClosure X)) (F (baseChange (curveGaloisData k hτ)))
        (kbarConstExt K c) := rfl

/-- **The field of constants of `U_K` is `K`.** -/
instance fact_piJ1ToGk_surjective_constExt :
    Fact (Function.Surjective (piJ1ToGk (constExt K (curveGaloisData k hτ)))) :=
  fact_piJ1ToGk_surjective _
    (mem_range_of_isAlgebraic_F_constExt K (mem_range_of_isAlgebraic_F k hτ))

lemma constExt_HL_eq_curve :
    (constExt K (curveGaloisData k hτ)).HL = (constExt K (curveGaloisData k hτ)).H :=
  constExt_HL_eq _ rfl

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_{U_K}` is found slowly
/-- **[LocAn] Thm C (profinite) for rational points of `U_K`**, `K` finite over a number field
`k`, `X` proper of genus `≠ 0` with a rational point: rational points of `U_K` with
`Δ_{U_K}`-conjugate sections of `Π_{U_K} → G_K` are equal. -/
theorem placeOfF_eq_of_ratSectionGk_conj_constExt [NumberField k]
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hg : CurvesJacobian.curveGenus k X ≠ 0)
    {x y : RatPoint (constExt K (curveGaloisData k hτ))} (hx : coordT τ ∈ x.A)
    (hy : coordT τ ∈ y.A) {δ : Pi (constExt K (curveGaloisData k hτ))}
    (hδ : δ ∈ (piToGk (constExt K (curveGaloisData k hτ))).ker)
    (h : ∀ g, ratSectionGk y (constExt_HL_eq_curve k hτ K) hy g =
      δ * ratSectionGk x (constExt_HL_eq_curve k hτ K) hx g * δ⁻¹) :
    placeOfF x = placeOfF y := by
  haveI : NumberField K := NumberField.of_module_finite k K
  set φ := fBcConstExt (curveGaloisData k hτ) K
  have hφ := fBcConstExt_tr k hτ K
  refine placeOfF_eq_of_ratSectionGk_conj
    (isKummerFaithfulJac_constExt K
      (isDivFreeOver_curve k hτ σ hσ K (jacDivFree_numberField' X σ hσ K)))
    (exists_nsmul_eq_of_tr φ (kbarConstExt K) hφ fun N hN y hy => by
      obtain ⟨w, hw⟩ := exists_nsmul_eq_jacPsi k hτ σ hσ hN.ne' ⟨y, hy⟩
      exact ⟨w, congrArg Subtype.val hw⟩)
    (fun N _ => weilDual_bijective_of_tr φ (kbarConstExt K) hφ
      (weilPairing_nondegenerate_baseChange k hτ))
    (fun N _ => finite_picTorsion_of_tr φ (kbarConstExt K) hφ N)
    (by
      rw [← genus_eq_of_tr φ (kbarConstExt K) hφ]
      exact genus_baseChange_ne_zero_of_curveGenus k hτ hg)
    (constExt_HL_eq_curve k hτ K) hx hy hδ h

end Curve

end Iut.Reconstruction.Thm19
