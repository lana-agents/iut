/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.Cor37c
import Iut.Reconstruction.Cusp.CuspDataIso
import CurvesJacobian.Cusp.FillCuspClasses
import CurvesJacobian.Cusp.DupFillMatch
import CurvesJacobian.Cusp.ArithDecompPi

/-!
# Functoriality of [AbsTopIII] Thm 1.9 (a): isomorphisms preserve the decomposition groups of points

[AbsTopIII] Thm 1.9 (`Topics in Absolute Anabelian Geometry III.txt` l.2109–2199) is a
"functorial "group-theoretic" algorithm"; its step (a) (l.2131–2143) is "a "group-theoretic"
construction of `Π_U` equipped with the collection of subgroups that arise as decomposition groups
of NF-points", by Belyi cuspidalization ([AbsTopII] Cor 3.7 (a)–(c)). The functoriality of step
(a) is that every isomorphism of the input groups maps this collection onto the corresponding one.

For an affine hyperbolic curve `U` over a number field, every closed point `x ∈ U` is an NF-point,
and a place `W` of `K(X̄_Ω)^alg` over `x` is a cusp place of `U_X = U ∖ {x}` centred on `U`. Here:

* `ptDecomps Ω C hc`: the decomposition groups `D_W ⊆ Π_U` (all `Π_U`-conjugates of `arithDecomp`)
  of the places `W` that are cusp places of some nonempty open `U_X ⊆ U` and are centred on `U`
  (i.e. lie over a closed point of `U ∖ U_X`);
* `exists_map_cor38Fill_commensurator`: [AbsTopII] Cor 3.7 (c) along `cor38Fill`: up to one
  conjugation, the image of `Comm_{Π_{U_X}}(I_W)` in `Π_U` is `D_W`;
* **`map_mem_ptDecomps`**: an isomorphism of cuspidal extensions `Π_U ≅ Π_{U'}` (`U'` over a
  possibly different number field) maps `ptDecomps` into `ptDecomps`. Proof: the lift
  `Π_{U_X} ≃ Π_{U'_X}` of [AbsTopII] Cor 3.8 (`BelyiCuspSpec` (d), debt `hDGC`), which lies over
  `G_K ≃ G_{K'}` up to conjugation (`exists_pr_cor38Fill₃`), preserves the cuspidal inertia groups
  ([AbsTopI] Lemma 4.5 (v), `arithmeticExtIso'`) and commensurators; the cusp `I_W` is killed in
  `Π_U`, so its image is killed in `Π_{U'}` and is the inertia of a place centred on `U'`
  (`false_of_le_ker`); then Cor 3.7 (c) for `U'`;
* **`map_ptDecomps_eq`**: for two curves with `BelyiCuspSpec` (e.g. of strictly Belyi type,
  `belyiCuspSpec`), `Φ(ptDecomps U) = ptDecomps U'`; **`map_ptDecomps_eq'`**: the same for any
  pair of compatible isomorphisms `Π_U ≃ₜ* Π_{U'}`, `G_K ≃ₜ* G_{K'}` (no cusp hypothesis:
  [AbsTopI] Lemma 4.5 (v)).

The only debt is `hDGC` (inside `BelyiCuspSpec`, MR7).
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian.Cusp

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction

section Generic

variable {G H : Type*} [Group G] [Group H]

lemma map_conj_map_symm (e : H ≃* G) (t : G) (D : Subgroup H) :
    ((D.map e.toMonoidHom).map (MulAut.conj t).toMonoidHom).map e.symm.toMonoidHom =
      D.map (MulAut.conj (e.symm t)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

lemma map_conj_map (f : H →* G) (a : H) (D : Subgroup H) :
    (D.map (MulAut.conj a).toMonoidHom).map f = (D.map f).map (MulAut.conj (f a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

lemma map_conj_conj (a b : G) (D : Subgroup G) :
    (D.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      D.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

lemma map_conj_inv (a : G) (D E : Subgroup G) (h : E = D.map (MulAut.conj a).toMonoidHom) :
    D = E.map (MulAut.conj a⁻¹).toMonoidHom := by
  rw [h, map_conj_conj, inv_mul_cancel]
  ext x
  simp

/-- Commensurators are transported by isomorphisms. -/
lemma map_commensurator_mulEquiv (e : H ≃* G) (I : Subgroup H) :
    (Subgroup.Commensurable.commensurator I).map e.toMonoidHom =
      Subgroup.Commensurable.commensurator (I.map e.toMonoidHom) := by
  rw [map_commensurator_of_injective e.toMonoidHom e.injective,
    MonoidHom.range_eq_top.2 e.surjective, inf_top_eq]

/-- **The algebra of the functoriality of Cor 3.7 (c)**: if `F₂ ∘ φ = Φ ∘ F`, `φ(I) = I₂`, and
`F(Comm I)`, `F₂(Comm I₂)` are conjugates of `D`, `D₂`, then `Φ` maps every conjugate of `D` to a
conjugate of `D₂`. -/
theorem map_conj_eq_of_commensurator {P P₂ Q Q₂ : Type*} [Group P] [Group P₂] [Group Q] [Group Q₂]
    (F : P →* Q) (F₂ : P₂ →* Q₂) (φ : P ≃* P₂) (Φ : Q ≃* Q₂)
    (hφ : ∀ e, F₂ (φ e) = Φ (F e)) {I : Subgroup P} {I₂ : Subgroup P₂}
    (hI : I.map φ.toMonoidHom = I₂) {D : Subgroup Q} {D₂ : Subgroup Q₂} {s : Q} {s₂ : Q₂}
    (hs : (Subgroup.Commensurable.commensurator I).map F = D.map (MulAut.conj s).toMonoidHom)
    (hs₂ : (Subgroup.Commensurable.commensurator I₂).map F₂ =
      D₂.map (MulAut.conj s₂).toMonoidHom) (g : Q) :
    (D.map (MulAut.conj g).toMonoidHom).map Φ.toMonoidHom =
      D₂.map (MulAut.conj (Φ g * Φ s⁻¹ * s₂)).toMonoidHom := by
  have hcomp : Φ.toMonoidHom.comp F = F₂.comp φ.toMonoidHom := by
    ext e
    exact (hφ e).symm
  have hD : D = ((Subgroup.Commensurable.commensurator I).map F).map
      (MulAut.conj s⁻¹).toMonoidHom := map_conj_inv s _ _ hs
  have hmid : ((Subgroup.Commensurable.commensurator I).map F).map Φ.toMonoidHom =
      D₂.map (MulAut.conj s₂).toMonoidHom := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, map_commensurator_mulEquiv, hI, hs₂]
  rw [map_conj_map, hD, map_conj_map, hmid, map_conj_conj, map_conj_conj]
  simp only [mul_assoc]
  rfl

end Generic

/-- Conjugation as a continuous automorphism. -/
def conjCME {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (t : G) :
    G ≃ₜ* G where
  toMulEquiv := MulAut.conj t
  continuous_toFun := by
    change Continuous fun x => t * x * t⁻¹
    fun_prop
  continuous_invFun := by
    change Continuous fun x => t⁻¹ * x * t
    fun_prop

@[simp] lemma conjCME_apply {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (t x : G) : conjCME t x = t * x * t⁻¹ := rfl

section Arith

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- `W` is centred on `U_Ω`. -/
abbrev IsCentredOnU (W : ValuationSubring (FFClosure (geomCurve Ω C))) : Prop :=
  IsCentredOn (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
    (baseChangeOpen K Ω C.U) W

/-- **The decomposition groups of the closed points of `U` in `Π_U`** ([AbsTopIII] Thm 1.9 (a),
the NF-points of a curve over a number field): the `Π_U`-conjugates of the decomposition groups
`D_W` of the places `W` centred on `U_Ω` which are cusp places of some nonempty open `U_X ⊆ U`
(i.e. lie over a closed point of `U ∖ U_X`). -/
def ptDecomps : Set (Subgroup (arithmeticExt Ω C hc).Pi) :=
  {D | ∃ (UX : C.Xbar.Opens) (hUX : UX ≤ C.U) (hne : (UX : Set C.Xbar).Nonempty)
      (W : ValuationSubring (FFClosure (geomCurve Ω C))),
      IsCuspPlace Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) W ∧
        IsCentredOnU Ω C W ∧ ∃ g, D = (arithDecomp Ω C hc W).map (MulAut.conj g).toMonoidHom}

/-- **[AbsTopII] Cor 3.7 (c) along `cor38Fill`**: up to one conjugation `s ∈ Π_X`, the image of
the cuspidal decomposition group `Comm_{Π_{U_X}}(I_W)` under `Π_{U_X} ↠ Π_X` is `D_W`, for every
place `W` over a cusp of `U_X`. -/
theorem exists_map_cor38Fill_commensurator (UX : C.Xbar.Opens) (hUX : UX ≤ C.U)
    (hne : (UX : Set C.Xbar).Nonempty)
    (α₀ : fiber (basePoint Ω C hc) ≅
      fiber (fillPoint Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) hUX)) :
    ∃ s : (arithmeticExt Ω C hc).Pi, ∀ W : ValuationSubring (FFClosure (geomCurve Ω C)),
      IsCuspPlace Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) W →
      (Subgroup.Commensurable.commensurator (arithInertia Ω (subCurve C UX hUX hne)
          (compl_nonempty_of_le hUX hc) W)).map (cor38Fill Ω C hc UX hUX hne α₀) =
        (arithDecomp Ω C hc W).map (MulAut.conj s).toMonoidHom := by
  obtain ⟨t, ht⟩ := cor37c Ω C hc UX hUX hne α₀
  let A := autContinuousMulEquivOfIso (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, C.U)) rfl rfl α₀)
  refine ⟨A.symm t, fun W hW => ?_⟩
  have h1 := ht W hW
  have h2 := congrArg (fun S => S.map A.toMulEquiv.symm.toMonoidHom) h1
  have h3 := map_conj_map_symm A.toMulEquiv t (arithDecomp Ω C hc W)
  calc (Subgroup.Commensurable.commensurator (arithInertia Ω (subCurve C UX hUX hne)
          (compl_nonempty_of_le hUX hc) W)).map (cor38Fill Ω C hc UX hUX hne α₀)
      = ((Subgroup.Commensurable.commensurator (arithInertia Ω (subCurve C UX hUX hne)
          (compl_nonempty_of_le hUX hc) W)).map
            (fillMap Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) hUX).toMonoidHom).map
            A.toMulEquiv.symm.toMonoidHom := (Subgroup.map_map _ _ _).symm
    _ = (((arithDecomp Ω C hc W).map A.toMulEquiv.toMonoidHom).map
          (MulAut.conj t).toMonoidHom).map A.toMulEquiv.symm.toMonoidHom := h2
    _ = (arithDecomp Ω C hc W).map (MulAut.conj (A.symm t)).toMonoidHom := h3

end Arith

section Functorial

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}
  {hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty}

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **Functoriality of [AbsTopIII] Thm 1.9 (a)**: an isomorphism of cuspidal extensions
`Π_U ≅ Π_{U'}` maps the decomposition groups of the closed points of `U` to decomposition groups of
closed points of `U'`. The input is [AbsTopII] Cor 3.8 for `U` (`BelyiCuspSpec` (d), debt
`hDGC`). -/
theorem map_mem_ptDecomps (hS : BelyiCuspSpec Ω C hc)
    (Φ : (arithmeticExt Ω C hc).Iso (arithmeticExt Ω₂ C₂ hc₂))
    {D : Subgroup (arithmeticExt Ω C hc).Pi} (hD : D ∈ ptDecomps Ω C hc) :
    D.map Φ.pi.toMulEquiv.toMonoidHom ∈ ptDecomps Ω₂ C₂ hc₂ := by
  obtain ⟨UX, hUX, hne, W, hW, hWU, g, rfl⟩ := hD
  obtain ⟨α₀⟩ : Nonempty (fiber (basePoint Ω C hc) ≅
      fiber (fillPoint Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) hUX)) := by
    haveI := isIntegral_specTensor Ω C hc
    exact nonempty_iso_of_fiberFunctor _ _
  have hlift := hS.2.2.2.1 Ω₂ C₂ hc₂ Φ UX hUX hne α₀
  obtain ⟨UX₂, hUX₂, hne₂, hlift⟩ := hlift
  obtain ⟨α₂⟩ : Nonempty (fiber (basePoint Ω₂ C₂ hc₂) ≅
      fiber (fillPoint Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hc₂) hUX₂)) := by
    haveI := isIntegral_specTensor Ω₂ C₂ hc₂
    exact nonempty_iso_of_fiberFunctor _ _
  obtain ⟨φU, hφU⟩ := hlift α₂
  -- `φU` lies over `G_K ≃ G_{K₂}` up to conjugations
  obtain ⟨t, ht⟩ := exists_pr_cor38Fill₃ Ω C hc UX hUX hne α₀
  obtain ⟨t₂, ht₂⟩ := exists_pr_cor38Fill₃ Ω₂ C₂ hc₂ UX₂ hUX₂ hne₂ α₂
  let g' : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ≃ₜ*
      π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K₂ Ω₂))) := Φ.g
  let ψU : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ≃ₜ*
      π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K₂ Ω₂))) :=
    ((conjCME t).trans g').trans (conjCME t₂⁻¹)
  have hprU : ∀ e, projGk Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hc₂) (φU e) =
      ψU (projGk Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) e) := by
    intro e
    have a1 := ht₂ (φU e)
    have a2 := ht e
    have a3 : projGk Ω₂ C₂ hc₂ (Φ.pi (cor38Fill Ω C hc UX hUX hne α₀ e)) =
        g' (projGk Ω C hc (cor38Fill Ω C hc UX hUX hne α₀ e)) :=
      Φ.pr_comm _
    rw [hφU e, a3, a2] at a1
    change projGk Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hc₂) (φU e) =
      t₂⁻¹ * g' (t * projGk Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) e * t⁻¹) *
        t₂⁻¹⁻¹
    rw [a1]
    group
  let ΦU := CurvesJacobian.CuspChar.arithmeticExtIso' φU ψU hprU
  -- the cusp `I_W` of `Π_{U_X}` goes to a cusp `I_{W₂}` of `Π_{U'_X}`
  have hI : arithInertia Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) W ∈
      arithCusps Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) :=
    (mem_arithCusps_iff Ω _ _).2 ⟨W, hW, rfl⟩
  have hI₂ := (ΦU.cusps_map _).1 hI
  obtain ⟨W₂, hW₂, hIW₂⟩ := (mem_arithCusps_iff Ω₂ _ _).1 hI₂
  -- `I_W` is killed in `Π_U`, so `I_{W₂}` is killed in `Π_{U'}`
  haveI : Nonempty (baseChangeOpen K Ω C.U) := inferInstanceAs (Nonempty (geomOpen Ω C))
  haveI : Nonempty (baseChangeOpen K₂ Ω₂ C₂.U) := inferInstanceAs (Nonempty (geomOpen Ω₂ C₂))
  have hker : arithInertia Ω (subCurve C UX hUX hne) (compl_nonempty_of_le hUX hc) W ≤
      (cor38Fill Ω C hc UX hUX hne α₀).ker := by
    rw [ker_cor38Fill₂]
    exact arithInertia_le_ker_fillMap_of_isCentredOn₂ Ω (subCurve C UX hUX hne)
      (compl_nonempty_of_le hUX hc) hUX hc hW hWU
  have hker₂ : arithInertia Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hc₂) W₂ ≤
      (fillMap Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hc₂)
        hUX₂).toMonoidHom.ker := by
    rw [← ker_cor38Fill₂ Ω₂ C₂ hc₂ UX₂ hUX₂ hne₂ α₂, ← hIW₂]
    rintro _ ⟨e, he, rfl⟩
    rw [MonoidHom.mem_ker]
    change cor38Fill Ω₂ C₂ hc₂ UX₂ hUX₂ hne₂ α₂ (φU e) = 1
    rw [hφU e]
    exact (congrArg Φ.pi (hker he)).trans (map_one _)
  have hW₂U : IsCentredOnU Ω₂ C₂ W₂ := by
    by_contra hnc
    have hhyp := isHyperbolic_baseChange Ω₂ (fillCurve (subCurve C₂ UX₂ hUX₂ hne₂) hUX₂
      C₂.hyperbolic)
    have e : (geomCuspInertia Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) W₂).map
        (geomToPi Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hc₂)) =
        arithInertia Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hc₂) W₂ :=
      map_geomCuspInertia Ω₂ _ _ hW₂.1
    have hle' : (geomCuspInertia Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) W₂).map
        (geomToPi Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hc₂)) ≤
        (fillMap Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hc₂)
          hUX₂).toMonoidHom.ker := by
      rw [e]
      exact hker₂
    exact false_of_le_ker Ω₂ (subCurve C₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hc₂) hUX₂
      hc₂ hhyp hW₂.1 hnc 1 (by rw [Subgroup.relIndex_self]; exact one_ne_zero)
      (map_conj_le_of_le_normal 1 hle')
  -- Cor 3.7 (c) on both sides
  obtain ⟨s, hs⟩ := exists_map_cor38Fill_commensurator Ω C hc UX hUX hne α₀
  obtain ⟨s₂, hs₂⟩ := exists_map_cor38Fill_commensurator Ω₂ C₂ hc₂ UX₂ hUX₂ hne₂ α₂
  refine ⟨UX₂, hUX₂, hne₂, W₂, hW₂, hW₂U, Φ.pi g * Φ.pi s⁻¹ * s₂, ?_⟩
  exact map_conj_eq_of_commensurator (cor38Fill Ω C hc UX hUX hne α₀)
    (cor38Fill Ω₂ C₂ hc₂ UX₂ hUX₂ hne₂ α₂) φU.toMulEquiv Φ.pi.toMulEquiv hφU hIW₂ (hs W hW)
    (hs₂ W₂ hW₂) g

/-- **`Φ(ptDecomps U) = ptDecomps U'`** for an isomorphism of cuspidal extensions between two
curves satisfying [AbsTopII] Cor 3.7, 3.8 (`BelyiCuspSpec`, e.g. of strictly Belyi type,
`belyiCuspSpec`; debt `hDGC`). -/
theorem map_ptDecomps_eq (hS : BelyiCuspSpec Ω C hc) (hS₂ : BelyiCuspSpec Ω₂ C₂ hc₂)
    (Φ : (arithmeticExt Ω C hc).Iso (arithmeticExt Ω₂ C₂ hc₂)) :
    (fun D => D.map Φ.pi.toMulEquiv.toMonoidHom) '' ptDecomps Ω C hc = ptDecomps Ω₂ C₂ hc₂ := by
  ext D₂
  constructor
  · rintro ⟨D, hD, rfl⟩
    exact map_mem_ptDecomps hS Φ hD
  · intro hD₂
    refine ⟨D₂.map Φ.symm.pi.toMulEquiv.toMonoidHom, map_mem_ptDecomps hS₂ Φ.symm hD₂, ?_⟩
    change (D₂.map Φ.pi.toMulEquiv.symm.toMonoidHom).map Φ.pi.toMulEquiv.toMonoidHom = D₂
    exact CuspData.map_map_symm Φ.pi.toMulEquiv D₂

/-- **`Φ(ptDecomps U) = ptDecomps U'`** for compatible continuous isomorphisms
`Π_U ≃ₜ* Π_{U'}`, `G_K ≃ₜ* G_{K'}` (the cusps are preserved by [AbsTopI] Lemma 4.5 (v),
`arithmeticExtIso'`). -/
theorem map_ptDecomps_eq' (hS : BelyiCuspSpec Ω C hc) (hS₂ : BelyiCuspSpec Ω₂ C₂ hc₂)
    (Φ : (arithmeticExt Ω C hc).Pi ≃ₜ* (arithmeticExt Ω₂ C₂ hc₂).Pi)
    (ψ : (arithmeticExt Ω C hc).G ≃ₜ* (arithmeticExt Ω₂ C₂ hc₂).G)
    (hpr : ∀ x, (arithmeticExt Ω₂ C₂ hc₂).pr (Φ x) = ψ ((arithmeticExt Ω C hc).pr x)) :
    (fun D => D.map Φ.toMulEquiv.toMonoidHom) '' ptDecomps Ω C hc = ptDecomps Ω₂ C₂ hc₂ :=
  map_ptDecomps_eq hS hS₂ (CurvesJacobian.CuspChar.arithmeticExtIso' Φ ψ hpr)

/-- **Thm 1.9 (a) functoriality for curves of strictly Belyi type** (with a Galois Belyi cover,
`GaloisBelyiInput`): every pair of compatible isomorphisms `Π_U ≃ₜ* Π_{U'}`, `G_K ≃ₜ* G_{K'}`
maps the decomposition groups of the closed points of `U` onto those of `U'`. The only input is
the existence half of the rel-isom-DGC over number fields (`hDGC`, MR7). -/
theorem map_ptDecomps_eq_of_belyi
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω]
    [Algebra.IsAlgebraic M Ω] (S : GaloisBelyiInput C M)
    {M₂ : Type u} [Field M₂] [NumberField M₂] [Algebra K₂ M₂] [Algebra M₂ Ω₂]
    [IsScalarTower K₂ M₂ Ω₂] [Algebra.IsAlgebraic M₂ Ω₂] (S₂ : GaloisBelyiInput C₂ M₂)
    (Φ : (arithmeticExt Ω C hc).Pi ≃ₜ* (arithmeticExt Ω₂ C₂ hc₂).Pi)
    (ψ : (arithmeticExt Ω C hc).G ≃ₜ* (arithmeticExt Ω₂ C₂ hc₂).G)
    (hpr : ∀ x, (arithmeticExt Ω₂ C₂ hc₂).pr (Φ x) = ψ ((arithmeticExt Ω C hc).pr x)) :
    (fun D => D.map Φ.toMulEquiv.toMonoidHom) '' ptDecomps Ω C hc = ptDecomps Ω₂ C₂ hc₂ :=
  map_ptDecomps_eq' (belyiCuspSpec Ω C hc hDGC S) (belyiCuspSpec Ω₂ C₂ hc₂ hDGC S₂) Φ ψ hpr

end Functorial

end Iut.Reconstruction
