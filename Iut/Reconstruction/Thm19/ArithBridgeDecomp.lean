/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ArithBridge
import CurvesJacobian.Cusp.ArithDecomp
import CurvesJacobian.Cusp.FillElemOp
import CurvesJacobian.Kummer.ConstantExtension

/-!
# [AbsTopIII] Thm 1.9 (a): decomposition groups and `Δ_U` under the Galois-model bridge

[AbsTopIII] Thm 1.9 (a) (`Topics in Absolute Anabelian Geometry III.txt` l.2131–2143) equips
`Π_U` with "the collection of subgroups that arise as decomposition groups of NF-points"; on the
étale side these are curves-jacobian's `arithDecomp W = (decompGal L₀ W).map arithAction` (and
[AbsTopII] Cor 3.7 (c), `Reconstruction/Cusp/Cor37c.lean`). Here `Thm19/ArithBridge.lean`'s
`piBridge` is shown to carry the image in `Π_U` (Galois model of the Kummer side) of the
decomposition group `D_W ∩ H = {h ∈ H | h(W) = W}` of a place `W ⊆ K(X̄)^alg` to `arithDecomp`
of the transported place:

* `decompH D W`: `D_W ∩ H` as a subgroup of `H`;
* `arithAut_mem_decompGal_iff`: `h(W) = W` iff `σ h σ⁻¹ (σ W) = σ W`;
* **`map_decompH_piBridge`**: `piBridge (image of D_W ∩ H) = arithDecomp (σ W)`;
* **`projGk_piBridge_eq_one_iff`**: `piBridge` carries `Δ_U = ker(Π_U → G_K)` of the Galois model
  (`piToGk`, restriction to `k̄`) onto `ker(projGk)` of `arithmeticExt` (the transport of `h ∈ Δ`
  fixes `Ω` and `L₀`, hence `K(X̄_Ω)`, and is an element of the geometric Galois group
  (`geomOf`, `toArithAut_geomOf`); conversely `ker(projGk) = range geomToPi`).
So `piBridge` is an isomorphism of the extensions `1 → Δ_U → Π_U → G_K → 1` (on `Δ_U`), with
the cuspidal inertia and decomposition groups matched.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian CurvesJacobian.Cusp AffOrbicurve KummerTheory
  KummerTheory.Curve CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section Decomp

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

/-- **The decomposition group `D_W ∩ H`** of a place `W` of `Ω`, as a subgroup of `H`. -/
def decompH (D : Pi1.Orbifold.GaloisData k t) (W : ValuationSubring Ω) : Subgroup D.H :=
  (decompGal (K₀ k t) W).comap D.H.subtype

lemma mem_decompH {D : Pi1.Orbifold.GaloisData k t} {W : ValuationSubring Ω} {h : D.H} :
    h ∈ decompH D W ↔ ∀ x, (h : Ω ≃ₐ[K₀ k t] Ω) x ∈ W ↔ x ∈ W := Iff.rfl

end Decomp

section Bridge

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar algFF algFFL₀

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)

attribute [local instance] nonempty_U

/-- **Decomposition groups under the bridge**: `h(W) = W` iff the transport of `h` fixes
`σ(W)`. -/
lemma arithAut_mem_decompGal_iff (h : (curveGaloisData K hτ).H)
    (W : ValuationSubring (FFClosure C.Xbar)) :
    arithAut (Ω := Ω) hτ h ∈ decompGal (arithFF Ω C hc.out)
        (W.comap ((σc (Ω := Ω) (C := C)).symm :
          FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) ↔
      h ∈ decompH (curveGaloisData K hτ) W := by
  rw [mem_decompH]
  change (∀ x, _ ∈ W.comap _ ↔ x ∈ W.comap _) ↔ _
  simp only [ValuationSubring.mem_comap, RingHom.coe_coe, arithAut_apply,
    RingEquiv.symm_apply_apply]
  constructor
  · intro H y
    simpa using H (σc y)
  · intro H x
    exact H _

/-- **[AbsTopIII] Thm 1.9 (a), decomposition groups under the bridge**: the image in `Π_U`
(Galois model) of `D_W ∩ H` is carried by `piBridge` to `arithDecomp (σ W)`. -/
theorem map_decompH_piBridge (W : ValuationSubring (FFClosure C.Xbar)) :
    ((decompH (curveGaloisData K hτ) W).map
        (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ).H
          (curveGaloisData K hτ).S))).map
        (piBridge (Ω := Ω) hτ hU).toMulEquiv.toMonoidHom =
      arithDecomp Ω C hc.out
        (W.comap ((σc (Ω := Ω) (C := C)).symm :
          FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) := by
  rw [Subgroup.map_map, arithDecomp]
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    rw [piBridge_comp_mk]
    exact ⟨arithAut hτ h, (arithAut_mem_decompGal_iff hτ h W).2 hh, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨⟨hOf g, hOf_mem hτ g⟩, ?_, ?_⟩
    · exact (arithAut_mem_decompGal_iff (Ω := Ω) hτ ⟨hOf g, hOf_mem hτ g⟩ W).1
        (by rw [arithAut_hOf]; exact hg)
    · rw [piBridge_comp_mk, arithAut_hOf]

/-! ### The geometric fundamental group `Δ_U` -/

/-- Elements of `K(X̄_Ω)^alg` coming from `Ω` are moved by `σ⁻¹` into `k̄ ⊆ K(X̄)^alg`. -/
lemma σc_symm_algebraMap_mem_kbar (c : Ω) :
    (σc (Ω := Ω) (C := C)).symm (algebraMap Ω (FFClosure (geomCurve Ω C)) c) ∈
      kbar K (FFClosure C.Xbar) := by
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ K Ω
  have h1 : IsAlgebraic ℚ (algebraMap Ω (FFClosure (geomCurve Ω C)) c) :=
    (Algebra.IsAlgebraic.isAlgebraic c).algHom (algebraMap Ω _).toRatAlgHom
  have h2 : IsAlgebraic ℚ
      ((σc (Ω := Ω) (C := C)).symm (algebraMap Ω (FFClosure (geomCurve Ω C)) c)) :=
    h1.algHom (σc (Ω := Ω) (C := C)).symm.toRingHom.toRatAlgHom
  exact mem_algebraicClosure_iff.2 (h2.tower_top K)

/-- **`h ∈ Δ` transports into the geometric Galois group**: if `h` fixes `k̄`, its transport fixes
`K(X̄_Ω)` (it fixes `Ω` and `L₀ ⊇ Γ(U)`, which generate `K(X̄_Ω)`). -/
lemma arithAut_fix_geom (h : (curveGaloisData K hτ).H)
    (hh : hToGk (curveGaloisData K hτ) h = 1) (z : (geomCurve Ω C).functionField) :
    arithAut hτ h (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C)) z) =
      algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C)) z := by
  have hfix := (hToGk_eq_one_iff (curveGaloisData K hτ) h).1 hh
  refine algebraMap_mem_of_le Ω C hc.out
    (RingHom.eqLocusField (arithAut (Ω := Ω) hτ h : FFClosure (geomCurve Ω C) →+* _)
      (RingHom.id _)) (fun c => ?_) (fun a => ?_) z
  · change arithAut hτ h _ = _
    rw [arithAut_apply, hfix _ (σc_symm_algebraMap_mem_kbar c), RingEquiv.apply_symm_apply]
    rfl
  · exact (arithAut hτ h).commutes ⟨_, secEmb_mem_arithFF Ω C hc.out a⟩

/-- The transport of `h ∈ Δ` as an element of the geometric `H` of `X̄_Ω`. -/
def geomOf (h : (curveGaloisData K hτ).H) (hh : hToGk (curveGaloisData K hτ) h = 1) :
    (geomData Ω C).H :=
  ⟨AlgEquiv.ofRingEquiv (f := (arithAut (Ω := Ω) hτ h).toRingEquiv) fun c => by
      obtain ⟨z, hz⟩ : (c : FFClosure (geomCurve Ω C)) ∈
          Set.range (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C))) :=
        K₀_le_imageK (k := Ω) (geomCoord Ω C) c.2
      change arithAut hτ h (c : FFClosure (geomCurve Ω C)) = c
      rw [← hz, arithAut_fix_geom hτ h hh],
    by
      change _ ∈ (imageL (k := Ω) (geomCoord Ω C)).fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      obtain ⟨z, rfl⟩ := (mem_imageL_iff _).1 hy
      exact arithAut_fix_geom hτ h hh z⟩

lemma toArithAut_geomOf (h : (curveGaloisData K hτ).H)
    (hh : hToGk (curveGaloisData K hτ) h = 1) :
    toArithAut Ω C hc.out (geomOf hτ h hh) = arithAut hτ h := by
  ext y
  rfl

/-- **[AbsTopIII] Thm 1.9, the geometric subgroups correspond**: `piBridge` carries
`Δ_U = ker(Π_U → G_K)` of the Galois model onto `ker(projGk)` of `arithmeticExt`. -/
theorem projGk_piBridge_eq_one_iff (p : Pi (curveGaloisData K hτ)) :
    projGk Ω C hc.out (piBridge hτ hU p) = 1 ↔ piToGk (curveGaloisData K hτ) p = 1 := by
  induction p using QuotientGroup.induction_on with
  | H h =>
    rw [piToGk_mk]
    constructor
    · intro h1
      have hmem : piBridge hτ hU (h : Pi (curveGaloisData K hτ)) ∈
          (geomToPi Ω C hc.out).range := by
        rw [range_geomToPi]
        exact h1
      obtain ⟨δ, hδ⟩ := hmem
      obtain ⟨σ, rfl⟩ := (genericL_spec (geomData Ω C) (geomCurve Ω C)
        (curveEquivL Ω (transcendental_geomCoord Ω C))
        (curveEquivL_algebraMap Ω (transcendental_geomCoord Ω C))
        (curveGaloisData_H_le Ω (transcendental_geomCoord Ω C))
        (curveEquivL_τ Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C)
        (compl_finite_baseChangeOpen K Ω C.nonempty)).2 δ
      rw [geomToPi_chartHom, ← arithAut_hOf hτ (toArithAut Ω C hc.out σ),
        ← piBridge_mk hτ hU] at hδ
      have heq := congrArg (piToGk (curveGaloisData K hτ)) ((piBridge hτ hU).injective hδ)
      rw [piToGk_mk, piToGk_mk] at heq
      rw [← heq]
      refine (hToGk_eq_one_iff _ _).2 fun y hy => ?_
      have hyQ : IsAlgebraic ℚ y := (mem_algebraicClosure_iff.1 hy).restrictScalars ℚ
      obtain ⟨c, hc'⟩ := exists_algebraMap_eq_of_isAlgebraic Ω C (σc (Ω := Ω) (C := C) y)
        (hyQ.algHom (σc (Ω := Ω) (C := C)).toRingHom.toRatAlgHom)
      change (σc (Ω := Ω) (C := C)).symm
        ((σ : FFClosure (geomCurve Ω C) ≃ₐ[K₀ Ω (coordT (geomCoord Ω C))]
          FFClosure (geomCurve Ω C)) (σc (Ω := Ω) (C := C) y)) = y
      have hσc : (σ : FFClosure (geomCurve Ω C) ≃ₐ[K₀ Ω (coordT (geomCoord Ω C))]
          FFClosure (geomCurve Ω C)) (algebraMap Ω (FFClosure (geomCurve Ω C)) c) =
            algebraMap Ω (FFClosure (geomCurve Ω C)) c :=
        (σ : FFClosure (geomCurve Ω C) ≃ₐ[K₀ Ω (coordT (geomCoord Ω C))]
          FFClosure (geomCurve Ω C)).commutes
          ⟨algebraMap Ω (FFClosure (geomCurve Ω C)) c,
            (K₀ Ω (coordT (geomCoord Ω C))).algebraMap_mem c⟩
      rw [← hc', hσc, hc', RingEquiv.symm_apply_apply]
    · intro h1
      rw [piBridge_mk, ← toArithAut_geomOf hτ h h1, ← geomToPi_chartHom]
      exact geomToPi_mem_ker Ω C hc.out _

end Bridge

end Iut.Reconstruction.Thm19
