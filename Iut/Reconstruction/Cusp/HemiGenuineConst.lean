/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.HemiGenuineField

/-!
# `Π_{C_F} ↪ Π_{C_K}` on the field of constants (MR9, `CKSemiAbsConj` assembly)

`genuine_CM_emb` and `genuine_CF_emb` embed iut's genuine `π₁` of `C_F = (E ∖ {O}) / ±1` into
that of `C_K = (E' ∖ {O}) / ±1` (`K ⊆ F` number fields, `j(E) = j(E') ∉ {0, 1728}`), through
curves-jacobian's twist (`twOmegaEquiv`). This file records, for the same embeddings, how they act
on the field of constants: the embedding is induced by a ring isomorphism
`ψ : k(E)^alg ≃ K(Ē')^alg` extending a `K`-embedding of `F` into `K̄`, i.e. the class of
`σ ∈ Gal(k(E)^alg / k(x))` acts on the algebraic closure of `K` in `K(Ē')^alg` as `ψ σ ψ⁻¹`:

* `mkC E σ`: the class of `σ` in the genuine `π₁` of `C` (`mkC_surjective`);
* **`genuine_CM_emb_const`**, **`genuine_CF_emb_const`**: `genuine_CM_emb`, `genuine_CF_emb` with
  this additional conclusion.
-/

open CategoryTheory AlgebraicGeometry CurvesJacobian CurvesJacobian.Cusp Belyi Belyi.Anabelian
  Pi1.Orbifold AffOrbicurve Topology Polynomial

noncomputable section

namespace Iut.Reconstruction.HemiGenuine

universe u

open Iut.Anabelian Iut.Anabelian.Genuine WeierstrassCurve

section Mk

attribute [local instance low] Classical.propDecidable

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- The class of `σ ∈ Gal(k(E)^alg / k(x))` in the genuine `π₁` of `C = (E ∖ {O}) / ±1`. -/
def mkC (σ : Gal E) : (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).genuinePi1 :=
  (QuotientGroup.mk ⟨σ, mem_Hgp_one_bot_true E σ⟩ :
    Hgp E 1 ⊥ true ⧸ GaloisPi1.kernel (Hgp E 1 ⊥ true) (SgenC E 1 ⊥))

lemma mkC_surjective : Function.Surjective (mkC E) := by
  intro y
  obtain ⟨⟨σ, hσ⟩, rfl⟩ := QuotientGroup.mk_surjective
    (s := GaloisPi1.kernel (Hgp E 1 ⊥ true) (SgenC E 1 ⊥)) y
  exact ⟨σ, rfl⟩

end Mk

/-! ### `Π_{C_M} ↪ Π_{C_K}` on the field of constants -/

section Emb

attribute [local instance low] Classical.propDecidable

variable {K : Type u} [Field K] [NumberField K] (E' : WeierstrassCurve K) [E'.IsElliptic]
  (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E')))) [FiniteDimensional K M]
  [IsGalois K M] (E : WeierstrassCurve M) [E.IsElliptic]

attribute [local instance high] decEqM

/-- The class of `σ` in `Π_{C_M}`, mapped to `Π_{C_K}` through the twist, acts on `K̄` as
`φ σ φ⁻¹` (`φ = twOmegaEquiv`). -/
lemma twInclC_const (u2 r : M) (hu2 : u2 ≠ 0) (hS : (hemiTwData E' M E u2 r).S = (hemiData E').S)
    (σ : Gal E) (z : ConstField₂ K (FFClosure (curveE E'))) :
    ((piConstC (hemiData E') (twInclC (hemiTwData E' M E u2 r) (hemiData E') le_top hS
        (genuinePi1TwEquiv E' M E u2 r hu2 (mkC E σ))) z :
        ConstField₂ K (FFClosure (curveE E'))) : FFClosure (curveE E')) =
      twOmegaEquiv E' M E u2 r hu2 (σ ((twOmegaEquiv E' M E u2 r hu2).symm z)) := by
  have h₁ : genuinePi1TwEquiv E' M E u2 r hu2 (mkC E σ) =
      (QuotientGroup.mk ⟨twGalHom E' M E u2 r hu2 σ, twGalHom_mem_H E' M E u2 r hu2 σ⟩ :
        (hemiTwData E' M E u2 r).H ⧸
          GaloisPi1.kernel (hemiTwData E' M E u2 r).H (hemiTwData E' M E u2 r).S) := rfl
  have h₃ : twInclC (hemiTwData E' M E u2 r) (hemiData E') le_top hS
      (QuotientGroup.mk ⟨twGalHom E' M E u2 r hu2 σ, twGalHom_mem_H E' M E u2 r hu2 σ⟩ :
        (hemiTwData E' M E u2 r).H ⧸
          GaloisPi1.kernel (hemiTwData E' M E u2 r).H (hemiTwData E' M E u2 r).S) =
      (QuotientGroup.mk ⟨twGalHom E' M E u2 r hu2 σ, Subgroup.mem_top _⟩ :
        (hemiData E').H ⧸ GaloisPi1.kernel (hemiData E').H (hemiData E').S) := rfl
  rw [h₁, h₃]
  rfl

set_option maxHeartbeats 1000000 in
-- the unifications over `M ⊆ K̄ ⊆ K(Ē')^alg` exceed the default budget
/-- **`genuine_CM_emb` on the field of constants**: the embedding
`Π_{C_M} ↪ Π_{C_K}` is induced by a ring isomorphism `φ : k(E)^alg ≃ K(Ē')^alg` extending
`M ⊆ K̄`: the class of `σ` acts on `K̄` as `φ σ φ⁻¹`. -/
theorem genuine_CM_emb_const (hj : E.j = algebraMap K M E'.j) (h0 : E'.j ≠ 0)
    (h1728 : E'.j ≠ 1728) :
    ∃ f : (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).genuinePi1 →ₜ*
        (Orbicurve.pmQuotient (Orbicurve.oncePunctured E')).genuinePi1,
      IsOpenEmbedding f ∧ f.toMonoidHom.range.Normal ∧
        f.toMonoidHom.range.index = Module.finrank K M ∧
        (∀ y, y ∈ f.toMonoidHom.range ↔
          piConstC (hemiData E') (genuinePi1HemiEquiv E' y) ∈ M.fixingSubgroup) ∧
        ∃ φ : Genuine.Ω E ≃+* FFClosure (curveE E'),
          (∀ m : M, φ (algebraMap M (Genuine.Ω E) m) = constι₃ M m) ∧
          ∀ (σ : Gal E) (z : ConstField₂ K (FFClosure (curveE E'))),
            ((piConstC (hemiData E') (genuinePi1HemiEquiv E' (f (mkC E σ))) z :
              ConstField₂ K (FFClosure (curveE E'))) : FFClosure (curveE E')) =
              φ (σ (φ.symm z)) := by
  have hj' : E.j = (E'.baseChange M).j := by
    rw [hj]
    change _ = (E'.map (algebraMap K M)).j
    rw [WeierstrassCurve.map_j]
  have hE0 : E.j ≠ 0 := by
    rw [hj]; exact (_root_.map_ne_zero _).2 h0
  have hE1728 : E.j ≠ 1728 := by
    rw [hj]; intro h
    exact h1728 ((algebraMap K M).injective (by rw [h, map_ofNat]))
  obtain ⟨u2, r, hu2, hΨ⟩ := exists_Ψ₂Sq_comp_xrat₃ E (E'.baseChange M) hj' hE0 hE1728
  obtain ⟨ho, hn, hi, -⟩ := hemiTw_constExt E' M E r hu2 hΨ
  let ι := twInclC (hemiTwData E' M E u2 r) (hemiData E') le_top (hemiTwData_S E' M E r hu2 hΨ)
  let e₁ := genuinePi1TwEquiv E' M E u2 r hu2
  let e₂ := (genuinePi1HemiEquiv E').symm
  let f := ((ContinuousMonoidHom.toContinuousMonoidHom e₂).comp ι).comp
    (ContinuousMonoidHom.toContinuousMonoidHom e₁)
  have hrange : f.toMonoidHom.range = ι.toMonoidHom.range.map (e₂.toMulEquiv : _ →* _) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨ι (e₁ y), ⟨e₁ y, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine ⟨e₁.symm z, ?_⟩
      change e₂ (ι (e₁ (e₁.symm z))) = e₂ (ι z)
      rw [ContinuousMulEquiv.apply_symm_apply]
  have hconst : ∀ (σ : Gal E) (z : ConstField₂ K (FFClosure (curveE E'))),
      ((piConstC (hemiData E') (genuinePi1HemiEquiv E' (f (mkC E σ))) z :
        ConstField₂ K (FFClosure (curveE E'))) : FFClosure (curveE E')) =
        twOmegaEquiv E' M E u2 r hu2 (σ ((twOmegaEquiv E' M E u2 r hu2).symm z)) := by
    intro σ z
    have h₂ : genuinePi1HemiEquiv E' (f (mkC E σ)) = ι (e₁ (mkC E σ)) :=
      (genuinePi1HemiEquiv E').apply_symm_apply _
    rw [h₂]
    exact twInclC_const E' M E u2 r hu2 _ σ z
  refine ⟨f, e₂.toHomeomorph.isOpenEmbedding.comp (ho.comp e₁.toHomeomorph.isOpenEmbedding),
    ?_, ?_, fun y => ?_, twOmegaEquiv E' M E u2 r hu2, twOmegaEquiv_C E' M E u2 r hu2, hconst⟩
  · rw [hrange]
    exact hn.map _ e₂.toMulEquiv.surjective
  · rw [hrange, Subgroup.index_map_equiv]
    exact hi
  · rw [hrange]
    exact Subgroup.mem_map_equiv.trans (mem_range_twInclC_iff E' M E _ _)

end Emb

/-! ### `Π_{C_F} ↪ Π_{C_K}` on the field of constants, `F` abstract -/

section NF

attribute [local instance low] Classical.propDecidable

variable {K F : Type u} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F] (E' : WeierstrassCurve K) [E'.IsElliptic] (E : WeierstrassCurve F) [E.IsElliptic]

attribute [local instance high] decEqM

set_option maxHeartbeats 1000000 in
-- the unifications over `M ⊆ K̄ ⊆ K(Ē')^alg` exceed the default budget
/-- **`genuine_CF_emb` on the field of constants**: the embedding `Π_{C_F} ↪ Π_{C_K}` is induced
by a ring isomorphism `ψ : k(E)^alg ≃ K(Ē')^alg` extending the `K`-embedding `embConst` of `F`
into `K̄`: the class of `σ` acts on `K̄` as `ψ σ ψ⁻¹`. -/
theorem genuine_CF_emb_const (hj : E.j = algebraMap K F E'.j) (h0 : E'.j ≠ 0)
    (h1728 : E'.j ≠ 1728) :
    ∃ f : (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).genuinePi1 →ₜ*
        (Orbicurve.pmQuotient (Orbicurve.oncePunctured E')).genuinePi1,
      IsOpenEmbedding f ∧ f.toMonoidHom.range.Normal ∧
        f.toMonoidHom.range.index = Module.finrank K F ∧
        (∀ y, y ∈ f.toMonoidHom.range ↔ piConstC (hemiData E') (genuinePi1HemiEquiv E' y) ∈
          (fieldM E' (F := F)).fixingSubgroup) ∧
        ∃ ψ : Genuine.Ω E ≃+* FFClosure (curveE E'),
          (∀ c : F, ψ (algebraMap F (Genuine.Ω E) c) =
            ((embConst E' c : ConstField₂ K (FFClosure (curveE E'))) : FFClosure (curveE E'))) ∧
          ∀ (σ : Gal E) (z : ConstField₂ K (FFClosure (curveE E'))),
            ((piConstC (hemiData E') (genuinePi1HemiEquiv E' (f (mkC E σ))) z :
              ConstField₂ K (FFClosure (curveE E'))) : FFClosure (curveE E')) =
              ψ (σ (ψ.symm z)) := by
  set e := (equivM E' (F := F)).toRingEquiv
  have hjM : (mapE e E).j = algebraMap K (fieldM E' (F := F)) E'.j := by
    rw [map_j, hj]
    exact (equivM E' (F := F)).commutes _
  obtain ⟨g, hg, hn, hi, hgal, φ, hφC, hφ⟩ :=
    genuine_CM_emb_const E' (fieldM E' (F := F)) (mapE e E) hjM h0 h1728
  let t := genuinePi1MapEquiv e E
  let f := g.comp (ContinuousMonoidHom.toContinuousMonoidHom t)
  have hrange : f.toMonoidHom.range = g.toMonoidHom.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨t y, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨t.symm y, ?_⟩
      change g (t (t.symm y)) = g y
      rw [ContinuousMulEquiv.apply_symm_apply]
  have ht : ∀ σ : Gal E, t (mkC E σ) = mkC (mapE e E) (mapGalEquiv e E σ) := fun _ => rfl
  refine ⟨f, ?_, ?_, ?_, fun y => ?_, (mapOmegaEquiv e E).trans φ, fun c => ?_,
    fun σ z => ?_⟩
  · have hf : (f : _ → _) = g ∘ t := rfl
    rw [hf]
    exact hg.comp t.toHomeomorph.isOpenEmbedding
  · rw [hrange]; exact hn
  · rw [hrange, hi]
    exact (equivM E' (F := F)).toLinearEquiv.finrank_eq.symm
  · rw [hrange]; exact hgal y
  · rw [RingEquiv.trans_apply, mapOmegaEquiv_algebraMap, hφC]
    rfl
  · have h := hφ (mapGalEquiv e E σ) z
    have hf : f (mkC E σ) = g (t (mkC E σ)) := rfl
    rw [hf, ht σ, h]
    rfl

end NF

end Iut.Reconstruction.HemiGenuine
