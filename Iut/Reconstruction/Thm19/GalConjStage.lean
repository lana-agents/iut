/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.GalConjPi

/-!
# Conjugation on the stages `U_{K'}` and the stage isomorphisms (MR9, `CKSemiAbsConj` item 3)

The stages of [AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt`
l.2158–2178) are base changes `U_{K'}` (Galois models `constExt K' D₀`). A ring automorphism `a`
of `Ω` fixing the function field `F₀` of `U` and mapping `K'` into itself (e.g. a lift of an
element of `Π_U`, for `K'` Galois over `k`) normalises the stage. Here:

* `stage_hK₀`, `stage_hH`, `stage_hHL`, `stage_hW`: the hypotheses of `conjPiH1` for
  `constExt K' D₀`, and **`stageConj`**: conjugation by `a` on `H¹(Π_{U_{K'}}, Ẑ(1))`;
* `algOf`, `piOf`: `a` as an element of `H₀` and of `Π_U`;
* `piRes_conjPiInv`: on `Π_{U_{K'}} ⊆ Π_U` (`piRes`) conjugation by `a` is conjugation by `piOf a`;
* `smul_eq_zConj`: `piOf a` acts on `Ẑ(1)` as `a`;
* **`constIso_stageConjPi`**, **`constCyclo_zConj`**, **`h1Congr_stageConj`**: for
  `e : Π_U ≃ Π_{U'}` over `ψ` with `e (piOf a) = piOf a'`, the stage isomorphisms `constH1Iso`
  intertwine conjugation by `a` and by `a'`;
* **`mem_fieldOf_conj`**: the fixed field `fieldOf H` of a normal subgroup `H ⊆ G_k` is stable
  under every automorphism of `Ω` restricting to an element of `G_k` on `k̄`.
-/

open KummerTheory Curve AffOrbicurve CurvesJacobian CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

/-! ### The hypotheses of `conjPiH1` at a stage -/

section Stage

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D₀ : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω]
  (K' : IntermediateField k Ω) [Algebra.IsAlgebraic k K']
  (a : Ω ≃+* Ω) (hfix : ∀ x ∈ F D₀, a x = x) (hK' : ∀ x ∈ K', a x ∈ K')

include hfix in
omit [IsGalois (K₀ k t) Ω] in
lemma fix_t : a t = t :=
  hfix t ((F D₀).algebraMap_mem ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩)

include hfix hK' in
omit [IsGalois (K₀ k t) Ω] [Algebra.IsAlgebraic k K'] in
/-- `a` maps `K'(t)` into itself. -/
lemma stage_hK₀ : ∀ x ∈ K₀ K' t, a x ∈ K₀ K' t := by
  let E : IntermediateField K' Ω :=
    Subfield.toIntermediateField ((K₀ K' t).toSubfield.comap (a : Ω →+* Ω)) fun c => by
      change a (algebraMap K' Ω c) ∈ K₀ K' t
      exact (K₀ K' t).algebraMap_mem ⟨a c, hK' c c.2⟩
  have hle : K₀ K' t ≤ E := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    change a t ∈ K₀ K' t
    rw [fix_t D₀ a hfix]
    exact IntermediateField.mem_adjoin_simple_self K' t
  exact fun x hx => hle hx

include hfix in
lemma stage_resK_mem {σ : Ω ≃ₐ[K₀ K' t] Ω} (hσ : σ ∈ (constExt K' D₀).H)
    (hK₀ : ∀ x ∈ K₀ K' t, a x ∈ K₀ K' t) :
    resK k K' t (galConjInv (K₀ K' t) a hK₀ σ) ∈ D₀.H := by
  have e : (IntermediateField.fixedField D₀.H).fixingSubgroup = D₀.H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨D₀.H, D₀.isClosed_H⟩
  rw [← e]
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
  have h1 : σ x = x := fixes_of_mem_F ((mem_constExt_H D₀).1 hσ) ⟨x, hx⟩
  rw [resK_apply, galConjInv_apply, hfix x hx, h1]
  have h2 := congrArg a.symm (hfix x hx)
  rwa [RingEquiv.symm_apply_apply, eq_comm] at h2

include hfix in
lemma stage_hH (hK₀ : ∀ x ∈ K₀ K' t, a x ∈ K₀ K' t) :
    ∀ σ ∈ (constExt K' D₀).H, galConjInv (K₀ K' t) a hK₀ σ ∈ (constExt K' D₀).H :=
  fun _ hσ => (mem_constExt_H D₀).2 (stage_resK_mem D₀ K' a hfix hσ hK₀)

include hfix in
lemma stage_hHL (hH₀ : D₀.H ≤ D₀.HL) (hK₀ : ∀ x ∈ K₀ K' t, a x ∈ K₀ K' t) :
    ∀ σ ∈ (constExt K' D₀).HL, galConjInv (K₀ K' t) a hK₀ σ ∈ (constExt K' D₀).HL :=
  fun _ hσ => (mem_constExt_HL D₀).2 (hH₀ (stage_resK_mem D₀ K' a hfix
    ((mem_constExt_H D₀).2 (D₀.le ((mem_constExt_HL D₀).1 hσ))) hK₀))

include hfix hK' in
omit [IsGalois (K₀ k t) Ω] [Algebra.IsAlgebraic k K'] in
lemma stage_hW : ∀ W : ValuationSubring Ω, (∀ c : K', algebraMap K' Ω c ∈ W) → t ∈ W →
    (∀ c : K', a (algebraMap K' Ω c) ∈ W) ∧ a t ∈ W :=
  fun W hk ht => ⟨fun c => hk ⟨a c, hK' c c.2⟩, by rw [fix_t D₀ a hfix]; exact ht⟩

variable [CharZero k]

/-- **Conjugation by `a` on `H¹(Π_{U_{K'}}, Ẑ(1))`** for `a` fixing `F₀` and mapping `K'` into
itself. -/
abbrev stageConj (hH₀ : D₀.H ≤ D₀.HL) :
    ContH1 (Pi (constExt K' D₀)) (ZHatOne (F (constExt K' D₀)) Ω) →*
      ContH1 (Pi (constExt K' D₀)) (ZHatOne (F (constExt K' D₀)) Ω) :=
  conjPiH1 (constExt K' D₀) a (stage_hK₀ D₀ K' a hfix hK')
    (stage_hH D₀ K' a hfix (stage_hK₀ D₀ K' a hfix hK'))
    (stage_hHL D₀ K' a hfix hH₀ (stage_hK₀ D₀ K' a hfix hK')) (stage_hW D₀ K' a hfix hK')

/-- `p ↦ a⁻¹ p a` on `Π_{U_{K'}}`. -/
abbrev stageConjPi (hH₀ : D₀.H ≤ D₀.HL) : Pi (constExt K' D₀) →* Pi (constExt K' D₀) :=
  conjPiInv (constExt K' D₀) a (stage_hK₀ D₀ K' a hfix hK')
    (stage_hH D₀ K' a hfix (stage_hK₀ D₀ K' a hfix hK'))
    (stage_hHL D₀ K' a hfix hH₀ (stage_hK₀ D₀ K' a hfix hK')) (stage_hW D₀ K' a hfix hK')

end Stage

/-! ### `a` as an element of `Π_U` -/

section Elt

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D₀ : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω]
  (a : Ω ≃+* Ω) (hfix : ∀ x ∈ F D₀, a x = x)

/-- `a` as an automorphism of `Ω` over `k(t)`. -/
def algOf : Ω ≃ₐ[K₀ k t] Ω :=
  AlgEquiv.ofRingEquiv (f := a) fun c => hfix _ ((F D₀).algebraMap_mem c)

omit [IsGalois (K₀ k t) Ω] in
@[simp] lemma algOf_apply (x : Ω) : algOf D₀ a hfix x = a x := rfl

lemma algOf_mem : algOf D₀ a hfix ∈ D₀.H := by
  have e : (IntermediateField.fixedField D₀.H).fixingSubgroup = D₀.H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨D₀.H, D₀.isClosed_H⟩
  rw [← e]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => hfix x hx

/-- `a` as an element of `Π_U`. -/
def piOf : Pi D₀ := ((⟨algOf D₀ a hfix, algOf_mem D₀ a hfix⟩ : D₀.H) : Pi D₀)

variable [CharZero k]

/-- `piOf a` acts on `Ẑ(1)` as `a`. -/
lemma smul_eq_zConj (L : Type*) [Field L] (w : ZHatOne L Ω) :
    piOf D₀ a hfix • w = zConj a L w := by
  apply Subtype.ext
  funext i
  apply Mu.ext
  apply Units.ext
  rfl

variable (K' : IntermediateField k Ω) [Algebra.IsAlgebraic k K'] (hK' : ∀ x ∈ K', a x ∈ K')
  (hH₀ : D₀.H ≤ D₀.HL)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure on the quotient `Π_U` is found slowly
omit [CharZero k] in
/-- **On `Π_{U_{K'}} ⊆ Π_U` conjugation by `a` is conjugation by `piOf a`.** -/
lemma piRes_stageConjPi (p : Pi (constExt K' D₀)) :
    piRes K' D₀ (stageConjPi D₀ K' a hfix hK' hH₀ p) =
      (piOf D₀ a hfix)⁻¹ * piRes K' D₀ p * piOf D₀ a hfix := by
  induction p using QuotientGroup.induction_on with
  | H σ =>
    change ((hRes K' D₀ (conjHInv (constExt K' D₀) a _ _ σ) : D₀.H) : Pi D₀) =
      (((⟨algOf D₀ a hfix, algOf_mem D₀ a hfix⟩ : D₀.H)⁻¹ * hRes K' D₀ σ *
        ⟨algOf D₀ a hfix, algOf_mem D₀ a hfix⟩ : D₀.H) : Pi D₀)
    congr 1

end Elt

/-! ### The stage isomorphisms intertwine the conjugations -/

section Iso

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : Pi1.Orbifold.GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω']
  (e : Pi D ≃ₜ* Pi D') (ψ : Gk k Ω ≃* Gk k' Ω')
  (he : ∀ p, piToGk D' (e p) = ψ (piToGk D p)) (hs : Function.Surjective (piToGk D))
  (χ : ZHatOne (F D) Ω ≃ₜ* ZHatOne (F D') Ω') (hχ : ∀ p z, χ (p • z) = e p • χ z)
  (K : IntermediateField k Ω) [FiniteDimensional k K] [FiniteDimensional k' (constField ψ K)]
  (a : Ω ≃+* Ω) (hfix : ∀ x ∈ F D, a x = x) (hK : ∀ x ∈ K, a x ∈ K)
  (a' : Ω' ≃+* Ω') (hfix' : ∀ x ∈ F D', a' x = x)
  (hK' : ∀ x ∈ constField ψ K, a' x ∈ constField ψ K)
  (hH : D.H ≤ D.HL) (hH' : D'.H ≤ D'.HL)
  (hea : e (piOf D a hfix) = piOf D' a' hfix')

set_option maxHeartbeats 800000 in
-- the quotients `Π_{U_K}` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
include hea in
/-- **`constIso e` intertwines the conjugations by `a` and `a'`** (through `piRes`, injective). -/
lemma constIso_stageConjPi (p : Pi (constExt K D)) :
    constIso e ψ he hs K (stageConjPi D K a hfix hK hH p) =
      stageConjPi D' (constField ψ K) a' hfix' hK' hH' (constIso e ψ he hs K p) := by
  apply piRes_injective (K := constField ψ K) D'
  rw [piRes_constIso, piRes_stageConjPi, piRes_stageConjPi, piRes_constIso, map_mul, map_mul,
    map_inv, hea]

omit [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω'] in
lemma zK_zConj (L₁ L₂ : Type*) [Field L₁] [Field L₂] [CharZero L₁] [CharZero L₂]
    (m : ZHatOne L₁ Ω) :
    zHatRes L₁ L₂ Ω Ω (zConj a L₁ m) = zConj a L₂ (zHatRes L₁ L₂ Ω Ω m) := by
  apply Subtype.ext
  funext i
  apply Mu.ext
  apply Units.ext
  rfl

set_option maxHeartbeats 800000 in
-- the coefficients of the base change are unified slowly
omit [IsAlgClosed Ω] [IsAlgClosed Ω'] in
include hχ hea in
/-- **`constCyclo` intertwines `a` and `a'` on `Ẑ(1)`.** -/
lemma constCyclo_zConj (z : ZHatOne (F (constExt K D)) Ω) :
    constCyclo ψ χ K (zConj a _ z) = zConj a' _ (constCyclo ψ χ K z) := by
  simp only [constCyclo, ContinuousMulEquiv.trans_apply, zKEquiv, zHatResEquiv_symm_apply,
    zHatResEquiv_apply]
  rw [zK_zConj, ← smul_eq_zConj D a hfix, hχ, hea, smul_eq_zConj D' a' hfix', zK_zConj]

set_option maxHeartbeats 1600000 in
-- the coefficients of the base change are unified slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the action of `Π_{U_K}` on `Ẑ(1)` is found slowly
include hχ hea in
/-- **The stage isomorphisms intertwine conjugation by `a` and by `a'`.** -/
theorem h1Congr_stageConj (x : ContH1 (Pi (constExt K D)) (ZHatOne (F (constExt K D)) Ω)) :
    h1Congr (constIso e ψ he hs K) (constCyclo ψ χ K) (constCyclo_smul e ψ he hs χ hχ K)
        (stageConj D K a hfix hK hH x) =
      stageConj D' (constField ψ K) a' hfix' hK' hH'
        (h1Congr (constIso e ψ he hs K) (constCyclo ψ χ K) (constCyclo_smul e ψ he hs χ hχ K) x) :=
  h1Congr_map_comm _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun p => constIso_stageConjPi (e := e) (ψ := ψ) (he := he) (hs := hs) (K := K) (a := a)
      (hfix := hfix) (hK := hK) (a' := a') (hfix' := hfix') (hK' := hK') (hH := hH) (hH' := hH')
      (hea := hea) p)
    (fun z => constCyclo_zConj (e := e) (ψ := ψ) (χ := χ) (hχ := hχ) (K := K) (a := a)
      (hfix := hfix) (a' := a') (hfix' := hfix') (hea := hea) z) x

end Iso

/-! ### Stability of fixed fields of normal subgroups -/

section FieldOf

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

/-- **`fieldOf H` is stable under automorphisms of `Ω` restricting to elements of `G_k`**, for `H`
normal. -/
lemma mem_fieldOf_conj (H : Subgroup (Gk k Ω)) [hN : H.Normal] (a : Ω ≃+* Ω) (g : Gk k Ω)
    (hag : ∀ y : kbar k Ω, a y = g y) {x : Ω} (hx : x ∈ fieldOf H) : a x ∈ fieldOf H := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y ∈ IntermediateField.fixedField H := hy
  rw [IntermediateField.mem_fixedField_iff] at hy'
  refine ⟨g y, (IntermediateField.mem_fixedField_iff _ _).2 fun h hh => ?_, (hag y).symm⟩
  have h1 : g⁻¹ * h * g ∈ H := by
    have := hN.conj_mem _ hh g⁻¹
    rwa [inv_inv] at this
  have h2 : g⁻¹ (h (g y)) = y := hy' _ h1
  have h3 : g (g⁻¹ (h (g y))) = g y := congrArg g h2
  exact (AlgEquiv.apply_symm_apply g _).symm.trans h3

end FieldOf

end Iut.Reconstruction.Thm19
