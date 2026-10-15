/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Plane
import Iut.AutHolomorphic.Reconstruct

/-!
# Reconstruction of the complex field from the Aut-holomorphic plane

For an Aut-holomorphic space `(X, A)` **isomorphic to the Aut-holomorphic plane** (`IsPlane A`:
there is a homeomorphism `X ≃ₜ ℂ` which is an isomorphism of Aut-holomorphic spaces, e.g. the
underlying Aut-holomorphic space of a complex archimedean field `k`, [AbsTopIII], Definition
4.1(i)), the model-implicit data of `Reconstruct.lean`, built from `A_X(X)` and a point `p ∈ X`
only, form a **field** `RecField A p` (the set `A_p ∪ {0}` with pointwise `+_p` and composition),
and every isomorphism `ψ : (X, A) ≅ ℂ` yields an isomorphism of topological fields
`recEquiv ψ p : RecField A p ≃+* ℂ` (`recEquiv_continuous`, `recEquiv_symm_continuous`; the
topology is that of pointwise convergence on `X`).

This is the "direct approach" of [AbsTopIII], Remark 2.7.1 (the additive structure from the
identity component of the holomorphic automorphism group — here: the fixed-point-free
automorphisms) combined with the construction of the local linear holomorphic structure
`A_p ∪ {0}` of [AbsTopIII], Proposition 2.6(a) and Corollary 2.7(e); `A_p ≅ ℂ^×`
(`stabEquivUnits`).

## The plane

* `isTransl_plane`: the translations of `A_ℂ(ℂ)` are the maps `z ↦ z + b`;
* `translSimplyTransitive_plane`, `transl_plane`;
* `mem_Kset_plane`: `A_q ∪ {0} = {z ↦ q + c (z − q)}` (`linAt q c`), and the operations are those of
  `ℂ` on the coefficient `c` (`kAdd_linAt`, `kMul_linAt`, `kNeg_linAt`, `kInv_linAt`).
-/

namespace Iut

namespace AutHol

open Set

/-! ### Translations and stabilisers of the plane -/

theorem isTransl_plane {g : ℂ ≃ₜ ℂ} : IsTransl plane.global g ↔ ∃ b, ∀ z, g z = z + b := by
  constructor
  · rintro ⟨hg, h⟩
    obtain ⟨a, b, ha, hab⟩ := mem_global_plane.1 hg
    rcases h with rfl | hfix
    · exact ⟨0, fun z => by simp⟩
    · refine ⟨b, fun z => ?_⟩
      by_cases ha1 : a = 1
      · rw [hab, ha1, one_mul]
      · exfalso
        have h1 : (1 : ℂ) - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha1)
        apply hfix (b / (1 - a))
        rw [hab]
        field_simp
        ring
  · rintro ⟨b, hb⟩
    refine ⟨mem_global_plane.2 ⟨1, b, one_ne_zero, fun z => by rw [hb, one_mul]⟩, ?_⟩
    by_cases hb0 : b = 0
    · left
      ext z
      simp [hb, hb0]
    · right
      intro x hx
      rw [hb] at hx
      exact hb0 (by simpa using hx)

theorem translSimplyTransitive_plane : TranslSimplyTransitive plane.global := by
  intro p a
  refine ⟨affine 1 (a - p) one_ne_zero, ⟨isTransl_plane.2 ⟨a - p, fun z => by simp⟩, by simp⟩,
    ?_⟩
  rintro g ⟨hg, hgp⟩
  obtain ⟨b, hb⟩ := isTransl_plane.1 hg
  have : b = a - p := by
    rw [hb] at hgp
    rw [← hgp]
    ring
  ext z
  simp [hb, this]

theorem transl_plane (p a : ℂ) : transl plane.global p a = affine 1 (a - p) one_ne_zero :=
  transl_eq translSimplyTransitive_plane (isTransl_plane.2 ⟨a - p, fun z => by simp⟩) (by simp)

/-- The linear map `z ↦ q + c (z − q)` centred at `q`. -/
def linAt (q c : ℂ) : ℂ → ℂ := fun z => q + c * (z - q)

@[simp]
theorem linAt_apply (q c z : ℂ) : linAt q c z = q + c * (z - q) := rfl

theorem linAt_injective (q : ℂ) : Function.Injective (linAt q) := by
  intro c c' h
  have := congrFun h (q + 1)
  simpa using this

theorem linAt_eq_affine (q : ℂ) {c : ℂ} (hc : c ≠ 0) : linAt q c = ⇑(affine c (q - c * q) hc) := by
  ext z
  simp only [linAt_apply, affine_apply]
  ring

theorem linAt_zero (q : ℂ) : linAt q 0 = kZero q := by
  ext z
  simp [kZero]

theorem linAt_one (q : ℂ) : linAt q 1 = kOne := by
  ext z
  simp [kOne]

theorem mem_Kset_plane {q : ℂ} {f : ℂ → ℂ} : f ∈ Kset plane.global q ↔ ∃ c, f = linAt q c := by
  constructor
  · rintro (⟨g, hg, hgq, rfl⟩ | rfl)
    · obtain ⟨a, b, -, hab⟩ := mem_global_plane.1 hg
      refine ⟨a, ?_⟩
      have hb : b = q - a * q := by
        rw [hab] at hgq
        linear_combination hgq
      ext z
      rw [hab, hb, linAt_apply]
      ring
    · exact ⟨0, (linAt_zero q).symm⟩
  · rintro ⟨c, rfl⟩
    by_cases hc : c = 0
    · subst hc
      exact Or.inr (linAt_zero q)
    · refine Or.inl ⟨affine c (q - c * q) hc, affine_mem_global _ _ hc, ?_, ?_⟩
      · simp only [affine_apply]
        ring
      · exact (linAt_eq_affine q hc).symm

theorem linAt_mem_Kset (q c : ℂ) : linAt q c ∈ Kset plane.global q := mem_Kset_plane.2 ⟨c, rfl⟩

theorem kAdd_linAt (q c c' : ℂ) :
    kAdd plane.global q (linAt q c) (linAt q c') = linAt q (c + c') := by
  ext z
  simp only [kAdd, addAt, transl_plane, affine_apply, linAt_apply]
  ring

theorem kNeg_linAt (q c : ℂ) : kNeg plane.global q (linAt q c) = linAt q (-c) := by
  ext z
  simp only [kNeg, negAt, transl_plane, affine_symm_apply, linAt_apply]
  ring

theorem kMul_linAt (q c c' : ℂ) : kMul (linAt q c) (linAt q c') = linAt q (c * c') := by
  ext z
  simp only [kMul, Function.comp_apply, linAt_apply]
  ring

theorem kInv_linAt (q c : ℂ) : kInv plane.global q (linAt q c) = linAt q c⁻¹ := by
  by_cases hc : c = 0
  · subst hc
    rw [inv_zero, linAt_zero, kInv_zero _ ⟨q + 1, by simp⟩]
  · rw [linAt_eq_affine q hc, kInv_of_mem (affine_mem_global _ _ hc) (by simp)]
    ext z
    simp only [affine_symm_apply, linAt_apply]
    field_simp
    ring

/-! ### Aut-holomorphic spaces isomorphic to the plane -/

variable {X : Type*} [TopologicalSpace X]

/-- `(X, A)` is **isomorphic to the Aut-holomorphic plane**. -/
def IsPlane (A : AutHolStr X) : Prop := ∃ ψ : X ≃ₜ ℂ, IsIso A plane ψ

theorem global_eq_of_isIso {A : AutHolStr X} {ψ : X ≃ₜ ℂ} (hψ : IsIso A plane ψ) :
    plane.global = A.global.map (conj ψ).toMonoidHom := by
  haveI : ConnectedSpace X := ψ.symm.surjective.connectedSpace ψ.symm.continuous
  exact hψ.global_eq isConnected_univ

theorem translSimplyTransitive_of_isIso {A : AutHolStr X} {ψ : X ≃ₜ ℂ}
    (hψ : IsIso A plane ψ) : TranslSimplyTransitive A.global :=
  translSimplyTransitive_of_conj (global_eq_of_isIso hψ) translSimplyTransitive_plane

/-- **The coefficient** of `f` with respect to `ψ : X ≃ₜ ℂ`: `ψ (f (ψ⁻¹ (ψ p + 1))) − ψ p`. -/
noncomputable def coeff (ψ : X ≃ₜ ℂ) (p : X) (f : X → X) : ℂ := transportFun ψ f (ψ p + 1) - ψ p

/-- The element of `A_p ∪ {0}` with coefficient `c`. -/
noncomputable def ofCoeff (ψ : X ≃ₜ ℂ) (p : X) (c : ℂ) : X → X :=
  fun x => ψ.symm (linAt (ψ p) c (ψ x))

theorem transportFun_ofCoeff (ψ : X ≃ₜ ℂ) (p : X) (c : ℂ) :
    transportFun ψ (ofCoeff ψ p c) = linAt (ψ p) c := by
  ext z
  simp [transportFun, ofCoeff]

theorem coeff_ofCoeff (ψ : X ≃ₜ ℂ) (p : X) (c : ℂ) : coeff ψ p (ofCoeff ψ p c) = c := by
  rw [coeff, transportFun_ofCoeff, linAt_apply]
  ring

theorem coeff_kZero (ψ : X ≃ₜ ℂ) (p : X) : coeff ψ p (kZero p) = 0 := by
  simp [coeff, transportFun, kZero]

theorem coeff_kOne (ψ : X ≃ₜ ℂ) (p : X) : coeff ψ p kOne = 1 := by
  simp [coeff, transportFun, kOne]

theorem kZero_mem (A : AutHolStr X) (p : X) : kZero p ∈ Kset A.global p := Or.inr rfl

theorem kOne_mem (A : AutHolStr X) (p : X) : kOne ∈ Kset A.global p :=
  Or.inl ⟨1, one_mem _, rfl, rfl⟩

section Iso

variable {A : AutHolStr X} {ψ : X ≃ₜ ℂ} (hψ : IsIso A plane ψ) (p : X)
include hψ

theorem transportFun_eq_linAt {f : X → X} (hf : f ∈ Kset A.global p) :
    transportFun ψ f = linAt (ψ p) (coeff ψ p f) := by
  obtain ⟨c, hc⟩ := mem_Kset_plane.1 ((mem_Kset_transport (global_eq_of_isIso hψ)).2 hf)
  rw [hc]
  congr 1
  rw [coeff, hc, linAt_apply]
  ring

theorem ofCoeff_mem (c : ℂ) : ofCoeff ψ p c ∈ Kset A.global p := by
  rw [← mem_Kset_transport (global_eq_of_isIso hψ), transportFun_ofCoeff]
  exact linAt_mem_Kset _ _

theorem ofCoeff_coeff {f : X → X} (hf : f ∈ Kset A.global p) : ofCoeff ψ p (coeff ψ p f) = f := by
  apply transportFun_injective ψ
  rw [transportFun_ofCoeff, transportFun_eq_linAt hψ p hf]

theorem coeff_injOn : InjOn (coeff ψ p) (Kset A.global p) := by
  intro f hf f' hf' h
  rw [← ofCoeff_coeff hψ p hf, ← ofCoeff_coeff hψ p hf', h]

theorem coeff_kAdd {f f' : X → X} (hf : f ∈ Kset A.global p) (hf' : f' ∈ Kset A.global p) :
    coeff ψ p (kAdd A.global p f f') = coeff ψ p f + coeff ψ p f' := by
  have h := kAdd_transport (global_eq_of_isIso hψ) translSimplyTransitive_plane p f f'
  rw [transportFun_eq_linAt hψ p hf, transportFun_eq_linAt hψ p hf', kAdd_linAt] at h
  rw [coeff, ← h, linAt_apply]
  ring

theorem coeff_kNeg {f : X → X} (hf : f ∈ Kset A.global p) :
    coeff ψ p (kNeg A.global p f) = -coeff ψ p f := by
  have h := kNeg_transport (global_eq_of_isIso hψ) translSimplyTransitive_plane p f
  rw [transportFun_eq_linAt hψ p hf, kNeg_linAt] at h
  rw [coeff, ← h, linAt_apply]
  ring

theorem coeff_kMul {f f' : X → X} (hf : f ∈ Kset A.global p) (hf' : f' ∈ Kset A.global p) :
    coeff ψ p (kMul f f') = coeff ψ p f * coeff ψ p f' := by
  have h := kMul_transport (φ := ψ) f f'
  rw [transportFun_eq_linAt hψ p hf, transportFun_eq_linAt hψ p hf', kMul_linAt] at h
  rw [coeff, ← h, linAt_apply]
  ring

theorem coeff_kInv {f : X → X} (hf : f ∈ Kset A.global p) :
    coeff ψ p (kInv A.global p f) = (coeff ψ p f)⁻¹ := by
  have hX : ∃ x : X, x ≠ p := ⟨ψ.symm (ψ p + 1), fun h => by
    have := congrArg ψ h
    simp at this⟩
  have h := kInv_transport (global_eq_of_isIso hψ) hX hf
  rw [transportFun_eq_linAt hψ p hf, kInv_linAt] at h
  rw [coeff, ← h, linAt_apply]
  ring

theorem kAdd_mem {f f' : X → X} (hf : f ∈ Kset A.global p) (hf' : f' ∈ Kset A.global p) :
    kAdd A.global p f f' ∈ Kset A.global p := by
  rw [← mem_Kset_transport (global_eq_of_isIso hψ),
    ← kAdd_transport (global_eq_of_isIso hψ) translSimplyTransitive_plane,
    transportFun_eq_linAt hψ p hf, transportFun_eq_linAt hψ p hf', kAdd_linAt]
  exact linAt_mem_Kset _ _

theorem kNeg_mem {f : X → X} (hf : f ∈ Kset A.global p) : kNeg A.global p f ∈ Kset A.global p := by
  rw [← mem_Kset_transport (global_eq_of_isIso hψ),
    ← kNeg_transport (global_eq_of_isIso hψ) translSimplyTransitive_plane,
    transportFun_eq_linAt hψ p hf, kNeg_linAt]
  exact linAt_mem_Kset _ _

theorem kMul_mem {f f' : X → X} (hf : f ∈ Kset A.global p) (hf' : f' ∈ Kset A.global p) :
    kMul f f' ∈ Kset A.global p := by
  rw [← mem_Kset_transport (global_eq_of_isIso hψ), ← kMul_transport,
    transportFun_eq_linAt hψ p hf, transportFun_eq_linAt hψ p hf', kMul_linAt]
  exact linAt_mem_Kset _ _

theorem kInv_mem {f : X → X} (hf : f ∈ Kset A.global p) : kInv A.global p f ∈ Kset A.global p := by
  have hX : ∃ x : X, x ≠ p := ⟨ψ.symm (ψ p + 1), fun h => by
    have := congrArg ψ h
    simp at this⟩
  rw [← mem_Kset_transport (global_eq_of_isIso hψ), ← kInv_transport (global_eq_of_isIso hψ) hX hf,
    transportFun_eq_linAt hψ p hf, kInv_linAt]
  exact linAt_mem_Kset _ _

end Iso

end AutHol

end Iut
