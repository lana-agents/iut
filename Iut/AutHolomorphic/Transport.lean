/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.RecField

/-!
# Functoriality of the reconstructed field; the Galois indeterminacy

* `transportEquiv hφ p : RecField A p ≃+* RecField B (φ p)`: an isomorphism `φ : (X, A) ≅ (Y, B)`
  of Aut-holomorphic spaces isomorphic to the plane induces, by `f ↦ φ ∘ f ∘ φ⁻¹`, an isomorphism
  of the reconstructed fields; it is continuous (`transportEquiv_continuous`), compatible with
  composition (`transportEquiv_trans`) and trivial for the identity (`transportEquiv_refl`). This
  is the **functoriality** of the algorithm ([AbsTopIII], Proposition 2.6, Corollary 2.7: "the
  asserted functoriality").
* `induced_eq_id_or_conj`: read through any two isomorphisms with the plane, the induced
  automorphism of `ℂ` is the identity or complex conjugation.
* `recEquiv_trans_eq`: **two isomorphisms `ψ, ψ' : (X, A) ≅ ℂ` ("Kummer structures") induce
  identifications `RecField A p ≅ ℂ` which differ by an element of `Gal(ℂ/ℝ)`** — the archimedean
  Kummer indeterminacy is exactly `{id, conj}` (cf. [AbsTopIII], Corollary 2.3(i): precisely two
  co-holomorphicizations; Definition 4.1(iv); `FullGalKummer.gal` of `Iut/LogLink/GalKummerAll.lean`).
-/

namespace Iut

namespace AutHol

open Set

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem isConnected_univ_of_isPlane {A : AutHolStr X} (h : IsPlane A) :
    IsConnected (univ : Set X) := by
  obtain ⟨ψ, -⟩ := h
  haveI : ConnectedSpace X := ψ.symm.surjective.connectedSpace ψ.symm.continuous
  exact isConnected_univ

theorem transportFun_symm (φ : X ≃ₜ Y) (g : Y → Y) :
    transportFun φ (transportFun φ.symm g) = g := by
  ext y
  simp [transportFun]

theorem transportFun_trans (φ : X ≃ₜ Y) (φ' : Y ≃ₜ Z) (f : X → X) :
    transportFun (φ.trans φ') f = transportFun φ' (transportFun φ f) := by
  ext z
  simp [transportFun]

section Transport

variable {A : AutHolStr X} {B : AutHolStr Y} [hA : Fact (IsPlane A)] [hB : Fact (IsPlane B)]

omit [Fact (IsPlane B)] in
theorem global_eq_of_isIso' {φ : X ≃ₜ Y} (hφ : IsIso A B φ) :
    B.global = A.global.map (conj φ).toMonoidHom :=
  hφ.global_eq (isConnected_univ_of_isPlane hA.out)

omit [Fact (IsPlane A)] in
theorem translSimplyTransitive_of_fact : TranslSimplyTransitive B.global := by
  obtain ⟨ψ, hψ⟩ := hB.out
  exact translSimplyTransitive_of_isIso hψ

omit [Fact (IsPlane B)] in
/-- The transport of an element of `RecField A p` along `φ`. -/
def transportElem {φ : X ≃ₜ Y} (hφ : IsIso A B φ) (p : X) (a : RecField A p) :
    RecField B (φ p) :=
  ⟨transportFun φ a.val, (mem_Kset_transport (global_eq_of_isIso' hφ)).2 a.val_mem⟩

omit [Fact (IsPlane B)] in
theorem transportElem_val {φ : X ≃ₜ Y} (hφ : IsIso A B φ) (p : X) (a : RecField A p) :
    (transportElem hφ p a).val = transportFun φ a.val := rfl

/-- The transport as a ring homomorphism. -/
def transportHom {φ : X ≃ₜ Y} (hφ : IsIso A B φ) (p : X) : RecField A p →+* RecField B (φ p) where
  toFun := transportElem hφ p
  map_one' := by
    apply RecField.val_injective
    rw [transportElem_val, one_val, one_val]
    exact (kOne_transport (φ := φ)).symm
  map_mul' a b := by
    apply RecField.val_injective
    rw [transportElem_val, mul_val, mul_val, transportElem_val, transportElem_val, kMul_transport]
  map_zero' := by
    apply RecField.val_injective
    rw [transportElem_val, zero_val, zero_val]
    rfl
  map_add' a b := by
    apply RecField.val_injective
    rw [transportElem_val, add_val, add_val, transportElem_val, transportElem_val,
      kAdd_transport (global_eq_of_isIso' hφ) translSimplyTransitive_of_fact]

theorem transportHom_bijective {φ : X ≃ₜ Y} (hφ : IsIso A B φ) (p : X) :
    Function.Bijective (transportHom hφ p) := by
  constructor
  · intro a b h
    apply RecField.val_injective
    exact transportFun_injective φ (congrArg RecField.val h)
  · intro b
    have hmem : transportFun φ.symm b.val ∈ Kset A.global p := by
      rw [← mem_Kset_transport (global_eq_of_isIso' hφ), transportFun_symm]
      exact b.val_mem
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply RecField.val_injective
    change transportFun φ (transportFun φ.symm b.val) = b.val
    rw [transportFun_symm]

/-- **The isomorphism of reconstructed fields induced by an isomorphism of Aut-holomorphic
spaces.** -/
noncomputable def transportEquiv {φ : X ≃ₜ Y} (hφ : IsIso A B φ) (p : X) :
    RecField A p ≃+* RecField B (φ p) :=
  RingEquiv.ofBijective (transportHom hφ p) (transportHom_bijective hφ p)

theorem transportEquiv_val {φ : X ≃ₜ Y} (hφ : IsIso A B φ) (p : X) (a : RecField A p) :
    (transportEquiv hφ p a).val = transportFun φ a.val := rfl

theorem transportEquiv_continuous {φ : X ≃ₜ Y} (hφ : IsIso A B φ) (p : X) :
    Continuous (transportEquiv hφ p) := by
  have : Continuous fun a : RecField A p => (transportEquiv hφ p a).val := by
    refine continuous_pi fun y => ?_
    simp only [transportEquiv_val, transportFun]
    exact φ.continuous.comp ((continuous_apply _).comp RecField.continuous_val)
  exact this.subtype_mk _

theorem transportEquiv_refl (p : X) (a : RecField A p) :
    (transportEquiv (IsIso.refl A) p a).val = a.val := by
  rw [transportEquiv_val]
  rfl

theorem transportEquiv_trans {C : AutHolStr Z} [Fact (IsPlane C)] {φ : X ≃ₜ Y} {φ' : Y ≃ₜ Z}
    (hφ : IsIso A B φ) (hφ' : IsIso B C φ') (p : X) (a : RecField A p) :
    (transportEquiv (hφ.trans hφ') p a).val =
      (transportEquiv hφ' (φ p) (transportEquiv hφ p a)).val := by
  rw [transportEquiv_val, transportEquiv_val, transportEquiv_val, transportFun_trans]

/-- **Through any two isomorphisms with the plane, an isomorphism of Aut-holomorphic spaces
induces the identity or the complex conjugation of `ℂ`.** -/
theorem induced_eq_id_or_conj {φ : X ≃ₜ Y} (hφ : IsIso A B φ) (p : X) {ψA : X ≃ₜ ℂ}
    {ψB : Y ≃ₜ ℂ} (hψA : IsIso A plane ψA) (hψB : IsIso B plane ψB) :
    (((recEquiv hψA p).symm.trans (transportEquiv hφ p)).trans (recEquiv hψB (φ p)) :
      ℂ →+* ℂ) = RingHom.id ℂ ∨
    (((recEquiv hψA p).symm.trans (transportEquiv hφ p)).trans (recEquiv hψB (φ p)) :
      ℂ →+* ℂ) = starRingEnd ℂ := by
  apply Complex.ringHom_eq_id_or_conj_of_continuous
  exact (recEquiv_continuous hψB).comp
    ((transportEquiv_continuous hφ p).comp (recEquiv_symm_continuous hψA))

end Transport

/-- **Two "Kummer structures" `ψ, ψ' : (X, A) ≅ ℂ` identify the reconstructed field with `ℂ` up to
an element of `Gal(ℂ/ℝ)`.** -/
theorem recEquiv_trans_eq {A : AutHolStr X} [Fact (IsPlane A)] (p : X) {ψ ψ' : X ≃ₜ ℂ}
    (hψ : IsIso A plane ψ) (hψ' : IsIso A plane ψ') :
    (((recEquiv hψ p).symm.trans (recEquiv hψ' p)) : ℂ →+* ℂ) = RingHom.id ℂ ∨
    (((recEquiv hψ p).symm.trans (recEquiv hψ' p)) : ℂ →+* ℂ) = starRingEnd ℂ := by
  apply Complex.ringHom_eq_id_or_conj_of_continuous
  exact (recEquiv_continuous hψ').comp (recEquiv_symm_continuous hψ)

end AutHol

end Iut
