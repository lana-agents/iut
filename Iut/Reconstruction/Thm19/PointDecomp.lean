/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ArithBridgeDecomp
import CurvesJacobian.LocAn.ThmC
import CurvesJacobian.LocAn.GenusBaseChange
import CurvesJacobian.Kummer.JacobianLocalField
import CurvesJacobian.LocAn.ThmCConstExt

/-!
# [AbsTopIII] Thm 1.9 (a): rational points of `U` are determined by their decomposition groups

[AbsTopIII] Thm 1.9 (a) (`Topics in Absolute Anabelian Geometry III.txt` l.2131–2143) equips
`Π_U` with the decomposition groups of the NF-points, and the algorithm of [AbsTopIII] Thm 3.5
(l.3547) treats "NF-points [i.e., conjugacy classes of decomposition groups of NF-points in
`Π_X`]": a point is identified with the conjugacy class of its decomposition group. That this
identification is injective is [GalSect] Thm 1.3 (i) (`Galois Sections.txt` l.265–266: "the closed
point `x` is completely determined by the conjugacy class of the closed subgroup `D_x`"), which
"follows … formally from [Mzk1], Theorem C" (l.280–281), the profinite form of [LocAn] Thm C
(curves-jacobian `LocAn/ThmC.lean`: rational points with `Δ_U`-conjugate sections are equal,
by the Kummer sequence of the Jacobian). Here, for rational points of the affine curve `U` over a
number field, in the Galois model `Π_U = Pi (curveGaloisData k hτ)`:

* `ratSectionGk_mem_range`, `exists_ratSectionGk_eq`, `piToGk_ratSectionGk`: the image of the
  section `s_x : G_k → Π_U` of a rational point `x ∈ U(k)` is the image `D_x` of its
  decomposition group (`decompToPi`);
* **`placeOfF_eq_of_range_decompToPi_le_conj`**: if `D_y ⊆ γ D_x γ⁻¹` for some `γ ∈ Π_U`, then
  `x = y` (as places of `K(X)`), for a proper compactification of genus `≠ 0` with a rational
  point (`exists_conj_of_forall_exists'` and
  `placeOfF_eq_of_ratSectionGk_conj_curve` with `jacDivFree_numberField`);
* `range_decompToPi_eq_map_decompH`: `D_x` is the image of `D_W ∩ H` (`decompH`, the form used by
  `Thm19/ArithBridgeDecomp.lean`);
* **`placeOfF_eq_of_arithDecomp_le_conj`**: the same for the decomposition groups `arithDecomp` of
  curves-jacobian's `arithmeticExt` (through `piBridge`, `map_decompH_piBridge`).
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp CurvesJacobian.LocAn
  Belyi Belyi.Anabelian

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

/-! ### Sections and decomposition groups of rational points -/

/-- If the image of a section `s'` of `p : G → Q` lies in a conjugate `γ · s(Q) · γ⁻¹` of the image
of another section `s`, then `s' = δ s δ⁻¹` for `δ = γ · s(p γ)⁻¹ ∈ ker p` (the group theory of
curves-jacobian's `SectionBridge.exists_conj_of_forall_exists`, whose module is not in the import
closure here). -/
theorem exists_conj_of_forall_exists' {G Q : Type*} [Group G] [Group Q] (p : G →* Q)
    (s s' : Q →* G) (hs : ∀ g, p (s g) = g) (hs' : ∀ g, p (s' g) = g) (γ : G)
    (h : ∀ g, ∃ g', s' g = γ * s g' * γ⁻¹) :
    ∃ δ, p δ = 1 ∧ ∀ g, s' g = δ * s g * δ⁻¹ := by
  refine ⟨γ * (s (p γ))⁻¹, by rw [map_mul, map_inv, hs, mul_inv_cancel], fun g ↦ ?_⟩
  obtain ⟨g', hg'⟩ := h g
  have hp : g = p γ * g' * (p γ)⁻¹ := by
    have := congrArg p hg'
    rwa [hs', map_mul, map_mul, map_inv, hs] at this
  have hg'' : g' = (p γ)⁻¹ * g * p γ := by
    rw [hp]
    group
  rw [hg', hg'', map_mul, map_mul, map_inv]
  group

section Galois

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

variable {k hτ}

lemma piToGk_ratSectionGk (x : RatPoint (curveGaloisData k hτ)) (hx : coordT τ ∈ x.A)
    (g : Gk k (FFClosure X)) :
    piToGk (curveGaloisData k hτ) (ratSectionGk x rfl hx g) = g := by
  rw [ratSectionGk, MonoidHom.comp_apply, piToGk_ratSectionMap]
  refine AlgEquiv.ext fun y => ?_
  simp

lemma ratSectionGk_mem_range (x : RatPoint (curveGaloisData k hτ)) (hx : coordT τ ∈ x.A)
    (g : Gk k (FFClosure X)) :
    ratSectionGk x rfl hx g ∈ (decompToPi (curveGaloisData k hτ) x.A).range := by
  obtain ⟨σ, hσ⟩ := x.decompositionMap_surjective
    (AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres) g)
  refine ⟨σ, ?_⟩
  rw [ratSectionGk, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hσ,
    ratSectionMap_decompositionMap]

lemma exists_ratSectionGk_eq (x : RatPoint (curveGaloisData k hτ)) (hx : coordT τ ∈ x.A)
    {d : Pi (curveGaloisData k hτ)} (hd : d ∈ (decompToPi (curveGaloisData k hτ) x.A).range) :
    ∃ g, ratSectionGk x rfl hx g = d := by
  obtain ⟨σ, rfl⟩ := hd
  refine ⟨(AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres)).symm
    (Decomposition.decompositionMap (F (curveGaloisData k hτ)) x.A x.hk x.hkres σ), ?_⟩
  rw [ratSectionGk, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    ratSectionMap_decompositionMap]

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
/-- **[GalSect] Thm 1.3 (i) for rational points of `U`** (Galois model, number field `k`, proper
compactification of genus `≠ 0` with a rational point `σ`): if the decomposition group `D_y` of
`y ∈ U(k)` lies in a conjugate `γ D_x γ⁻¹` of that of `x ∈ U(k)`, then `x = y`. -/
theorem placeOfF_eq_of_range_decompToPi_le_conj [NumberField k]
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hg : CurvesJacobian.curveGenus k X ≠ 0)
    {x y : RatPoint (curveGaloisData k hτ)} (hx : coordT τ ∈ x.A) (hy : coordT τ ∈ y.A)
    (γ : Pi (curveGaloisData k hτ))
    (h : ∀ d ∈ (decompToPi (curveGaloisData k hτ) y.A).range,
      ∃ d' ∈ (decompToPi (curveGaloisData k hτ) x.A).range, d = γ * d' * γ⁻¹) :
    placeOfF x = placeOfF y := by
  obtain ⟨δ, hδ, hconj⟩ := exists_conj_of_forall_exists'
    (piToGk (curveGaloisData k hτ)) (ratSectionGk x rfl hx) (ratSectionGk y rfl hy)
    (piToGk_ratSectionGk x hx) (piToGk_ratSectionGk y hy) γ (fun g ↦ by
      obtain ⟨d', hd', he⟩ := h _ (ratSectionGk_mem_range y hy g)
      obtain ⟨g', rfl⟩ := exists_ratSectionGk_eq x hx hd'
      exact ⟨g', he⟩)
  exact placeOfF_eq_of_ratSectionGk_conj_curve k hτ σ hσ (jacDivFree_numberField X σ hσ)
    (genus_baseChange_ne_zero_of_curveGenus k hτ hg) rfl hx hy hδ hconj

/-! ### `D_x` as the image of `D_W ∩ H`, and the arithmetic form -/

open scoped Pointwise in
lemma mem_decompositionSubgroup_iff' {L Ω : Type*} [Field L] [Field Ω] [Algebra L Ω]
    (W : ValuationSubring Ω) (σ : Ω ≃ₐ[L] Ω) :
    σ ∈ W.decompositionSubgroup L ↔ ∀ x, σ x ∈ W ↔ x ∈ W := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hσ x
    have := ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := W) (x := x)
    rw [hσ] at this
    exact this
  · intro h
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simpa using (h (σ⁻¹ • y)).symm

/-- **`D_x = image of D_W ∩ H`**: the image of the decomposition group of `W` (over `F`) in `Π_U`
is the image of `decompH` (the form of `Thm19/ArithBridgeDecomp.lean`). -/
lemma range_decompToPi_eq_map_decompH (W : ValuationSubring (FFClosure X)) :
    (decompToPi (curveGaloisData k hτ) W).range =
      (decompH (curveGaloisData k hτ) W).map (QuotientGroup.mk' (GaloisPi1.kernel
        (curveGaloisData k hτ).H (curveGaloisData k hτ).S)) := by
  apply le_antisymm
  · rintro _ ⟨σ, rfl⟩
    refine ⟨ofGalF (curveGaloisData k hτ) σ.1, fun x ↦ ?_, rfl⟩
    change ((ofGalF (curveGaloisData k hτ) σ.1 : (curveGaloisData k hτ).H) :
      FFClosure X ≃ₐ[K₀ k (coordT τ)] FFClosure X) x ∈ W ↔ x ∈ W
    rw [ofGalF_apply]
    exact (mem_decompositionSubgroup_iff' W σ.1).1 σ.2 x
  · rintro _ ⟨h, hh, rfl⟩
    refine ⟨⟨toGalF (curveGaloisData k hτ) h,
      (mem_decompositionSubgroup_iff' W _).2 fun x ↦ ?_⟩, ?_⟩
    · rw [toGalF_apply]
      exact hh x
    · change ((ofGalF (curveGaloisData k hτ) (toGalF (curveGaloisData k hτ) h) :
        (curveGaloisData k hτ).H) : Pi (curveGaloisData k hτ)) = (h : Pi (curveGaloisData k hτ))
      rw [ofGalF_toGalF]

end Galois

section Arith

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)

include hU in
lemma piBridge_mem_arithDecomp_iff (W : ValuationSubring (FFClosure C.Xbar))
    (d : Pi (curveGaloisData K hτ)) :
    piBridge (Ω := Ω) hτ hU d ∈ arithDecomp Ω C hc.out
        (W.comap ((σc (Ω := Ω) (C := C)).symm :
          FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) ↔
      d ∈ (decompToPi (curveGaloisData K hτ) W).range := by
  rw [← map_decompH_piBridge hτ hU, range_decompToPi_eq_map_decompH]
  constructor
  · rintro ⟨d', hd', he⟩
    rwa [(piBridge (Ω := Ω) hτ hU).injective he] at hd'
  · intro hd
    exact ⟨d, hd, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
include hU in
/-- **[GalSect] Thm 1.3 (i) for rational points of `U`, arithmetic form**: for an affine
hyperbolic curve over a number field whose compactification has genus `≠ 0` and a rational point,
if the decomposition group (curves-jacobian `arithDecomp`) of `y ∈ U(K)` lies in a
`Π_U`-conjugate of that of `x ∈ U(K)`, then `x = y`. -/
theorem placeOfF_eq_of_arithDecomp_le_conj (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
    (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
    (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
    {x y : RatPoint (curveGaloisData K hτ)} (hx : coordT τ ∈ x.A) (hy : coordT τ ∈ y.A)
    (g : (arithmeticExt Ω C hc.out).Pi)
    (h : ∀ e : (arithmeticExt Ω C hc.out).Pi, e ∈ arithDecomp Ω C hc.out
        (y.A.comap ((σc (Ω := Ω) (C := C)).symm :
          FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) →
      ∃ e' : (arithmeticExt Ω C hc.out).Pi, e' ∈ arithDecomp Ω C hc.out
        (x.A.comap ((σc (Ω := Ω) (C := C)).symm :
          FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) ∧ e = g * e' * g⁻¹) :
    placeOfF x = placeOfF y := by
  refine placeOfF_eq_of_range_decompToPi_le_conj σ₀ hσ₀ hg hx hy
    ((piBridge (Ω := Ω) hτ hU).symm g) fun d hd ↦ ?_
  obtain ⟨e', he', he⟩ := h _ ((piBridge_mem_arithDecomp_iff hτ hU y.A d).2 hd)
  obtain ⟨d', rfl⟩ := (piBridge (Ω := Ω) hτ hU).surjective e'
  refine ⟨d', (piBridge_mem_arithDecomp_iff hτ hU x.A d').1 he', ?_⟩
  apply (piBridge (Ω := Ω) hτ hU).injective
  rw [he, map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]

end Arith

end Iut.Reconstruction.Thm19
