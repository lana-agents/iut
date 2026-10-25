/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Angular.Props
import Iut.AutHolomorphic.Transport
import Iut.AutHolomorphic.Elliptic.EllField

/-!
# The Kummer structure on the archimedean Frobenioid (IUT I, Example 3.4(i))

IUT I, Example 3.4(i): "there is a natural topological isomorphism `K_v ≅ A_{D_v}`, which may be
restricted to `O^▷_{K_v}` to obtain an inclusion of topological monoids
`κ_v : O^▷(C_v) → A_{D_v}` — which we shall refer to as the Kummer structure on `C_v`".

Here `C_v` is the archimedean Frobenioid of angular regions (`Angular.Obj`, a Frobenioid by
`Angular.isFrobenioid`), `O^▷(C_v) = O^▷(A)` for an isotropic object `A` with
`O^▷(A) ≅ O^▷_ℂ` (`Angular.orhdEquiv`), and `A_{D_v}` is the field reconstructed from an
Aut-holomorphic space by MR10 (`AutHol.RecField D p`, a topological field isomorphic to `ℂ` via
`recEquiv hψ p` for any isomorphism `ψ : (X, D) ≅ ℂ`).

Two versions of `A_D`:

* `D` an Aut-holomorphic plane: `A_D = AutHol.RecField D p` (`kummer`);
* `D` an Aut-holomorphic space isomorphic to a once-punctured complex torus `E_Λ` (the output
  `E` of [AbsTopIII] Cor 2.7 (a) for `D_v = X→_v`): `A_D = A_p ∪ {0} = Ell.EllField D p`, built by
  elliptic cuspidalisation (Cor 2.7 (b)–(e)), a topological field isomorphic to `ℂ` via
  `Ell.ellEquiv hψ p` for any isomorphism `ψ : (X, D) ≅ E_Λ` (`kummerEll`).

**Simplification.** Cor 2.7 (a) (the core `D_v → \underline{D}_v` and its double cover by a
once-punctured elliptic curve, via [AbsTopIII] Cor 2.4) is not formalised: `D` is assumed
isomorphic to some `E_Λ`.

Proved (for both versions; the elliptic statements carry the suffix `Ell`):
`kummer hψ p hA : O^▷(A) → A_D` is injective (`kummer_injective`), multiplicative
(`kummer_comp`), continuous for the topology of `O^▷_ℂ` (`continuous_kummer`), with image the
elements of norm `≤ 1` of `A_D^×` (`range_kummer`); it is compatible with the isomorphisms
`O^▷(A) ≅ O^▷(B)` induced by co-angular pre-steps (`kummer_transport`); and the Kummer structures
obtained from two isomorphisms `ψ, ψ'` differ by the identity or complex conjugation
(`kummer_indet`, from `AutHol.recEquiv_trans_eq`; cf. IUT I, Remark 3.4.2).
-/

namespace Iut

namespace Frobenioid

namespace Angular

open CategoryTheory Set AutHol

noncomputable section

variable {X : Type*} [TopologicalSpace X] {D : AutHolStr X} [Fact (IsPlane D)] {ψ : X ≃ₜ ℂ}
  (hψ : IsIso D plane ψ) (p : X)

/-- **The Kummer structure** `κ : O^▷(A) → A_D`, `(1, μ) ↦ μ` (IUT I, Example 3.4(i)). -/
def kummer {A : Obj} (_hA : IsIsotropic P A) (e : Orhd P A) : RecField D p :=
  (recEquiv hψ p).symm (val e.1)

lemma recEquiv_kummer {A : Obj} (hA : IsIsotropic P A) (e : Orhd P A) :
    recEquiv hψ p (kummer hψ p hA e) = val e.1 := by
  simp [kummer]

theorem kummer_injective {A : Obj} (hA : IsIsotropic P A) :
    Function.Injective (kummer hψ p hA) := fun e₁ e₂ h => by
  have h' : (orhdEquiv hA e₁ : ℂ) = orhdEquiv hA e₂ := by
    have := congrArg (recEquiv hψ p) h
    rwa [recEquiv_kummer, recEquiv_kummer] at this
  exact (orhdEquiv hA).injective (Subtype.ext h')

/-- `κ` is multiplicative: `κ(e₂ ∘ e₁) = κ(e₂)·κ(e₁)`. -/
theorem kummer_comp {A : Obj} (hA : IsIsotropic P A) (e₁ e₂ e : Orhd P A)
    (he : e.1 = e₁.1 ≫ e₂.1) :
    kummer hψ p hA e = kummer hψ p hA e₂ * kummer hψ p hA e₁ := by
  have := orhdEquiv_comp hA e₁ e₂ e he
  simp only [kummer]
  rw [← map_mul]
  exact congrArg _ this

/-- `κ ∘ (O^▷(A) ≅ O^▷_ℂ)⁻¹` is the restriction of the topological isomorphism `ℂ ≅ A_D`, hence
continuous. -/
theorem continuous_kummer {A : Obj} (hA : IsIsotropic P A) :
    Continuous fun z : orhdC => kummer hψ p hA ((orhdEquiv hA).symm z) := by
  have : (fun z : orhdC => kummer hψ p hA ((orhdEquiv hA).symm z)) =
      fun z : orhdC => (recEquiv hψ p).symm z := by
    funext z
    simp only [kummer]
    congr 1
    exact congrArg Subtype.val ((orhdEquiv hA).apply_symm_apply z)
  rw [this]
  exact (recEquiv_symm_continuous hψ).comp continuous_subtype_val

/-- The image of `κ` is `{x ∈ A_D^× : |x| ≤ 1}`. -/
theorem range_kummer {A : Obj} (hA : IsIsotropic P A) :
    range (kummer hψ p hA) = {x | recEquiv hψ p x ∈ orhdC} := by
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    simp only [mem_setOf_eq, recEquiv_kummer]
    exact (orhdEquiv hA e).2
  · intro hx
    refine ⟨(orhdEquiv hA).symm ⟨_, hx⟩, ?_⟩
    apply (recEquiv hψ p).injective
    rw [recEquiv_kummer]
    exact congrArg Subtype.val ((orhdEquiv hA).apply_symm_apply ⟨_, hx⟩)

/-- Compatibility with the isomorphisms `O^▷(A) ≅ O^▷(B)` induced by pre-steps ([FrdI],
Definition 1.3(iii)(c); IUT I, Example 3.4(i): "the linear morphisms among the pseudo-terminal
objects of `C` determine unique isomorphisms among the respective topological monoids
`O^▷(−)`"). -/
theorem kummer_transport {A B : Obj} (hA : IsIsotropic P A) (hB : IsIsotropic P B) (φ : A ⟶ B)
    (hφ : IsPreStep P φ) (e : Orhd P A) (e' : Orhd P B) (h : φ ≫ e'.1 = e.1 ≫ φ) :
    kummer hψ p hB e' = kummer hψ p hA e := by
  simp only [kummer]
  rw [val_transport φ hφ ((mem_orhd _).mp e.2) ((mem_orhd _).mp e'.2) h]

/-- **The Kummer indeterminacy**: Kummer structures defined via two isomorphisms `ψ, ψ'` with the
plane agree up to `Gal(ℂ/ℝ)`. -/
theorem kummer_indet {ψ' : X ≃ₜ ℂ} (hψ' : IsIso D plane ψ') {A : Obj} (hA : IsIsotropic P A) :
    (∀ e, recEquiv hψ' p (kummer hψ p hA e) = val e.1) ∨
      ∀ e, recEquiv hψ' p (kummer hψ p hA e) = starRingEnd ℂ (val e.1) := by
  rcases recEquiv_trans_eq p hψ hψ' with h | h
  · left
    intro e
    exact congrArg (fun f : ℂ →+* ℂ => f (val e.1)) h
  · right
    intro e
    exact congrArg (fun f : ℂ →+* ℂ => f (val e.1)) h

/-! ### `A_D` for an Aut-holomorphic once-punctured elliptic curve ([AbsTopIII] Cor 2.7) -/

section Ell

variable {X : Type*} [TopologicalSpace X] {D : AutHolStr X} [Fact (Ell.IsEllModel D)]
  {L : PeriodPair} {ψ : X ≃ₜ Ell.punct L} (hψ : IsIso D (Ell.ellStr L) ψ) (p : X)

/-- **The Kummer structure** `κ : O^▷(A) → A_D` for `D ≅ E_Λ` (IUT I, Example 3.4(i), with
`A_D = A_p ∪ {0}` of [AbsTopIII] Corollary 2.7 (e)). -/
def kummerEll {A : Obj} (_hA : IsIsotropic P A) (e : Orhd P A) : Ell.EllField D p :=
  (Ell.ellEquiv hψ p).symm (val e.1)

lemma ellEquiv_kummerEll {A : Obj} (hA : IsIsotropic P A) (e : Orhd P A) :
    Ell.ellEquiv hψ p (kummerEll hψ p hA e) = val e.1 := by
  simp [kummerEll]

theorem kummerEll_injective {A : Obj} (hA : IsIsotropic P A) :
    Function.Injective (kummerEll hψ p hA) := fun e₁ e₂ h => by
  have h' : (orhdEquiv hA e₁ : ℂ) = orhdEquiv hA e₂ := by
    have := congrArg (Ell.ellEquiv hψ p) h
    rwa [ellEquiv_kummerEll, ellEquiv_kummerEll] at this
  exact (orhdEquiv hA).injective (Subtype.ext h')

/-- `κ` is multiplicative. -/
theorem kummerEll_comp {A : Obj} (hA : IsIsotropic P A) (e₁ e₂ e : Orhd P A)
    (he : e.1 = e₁.1 ≫ e₂.1) :
    kummerEll hψ p hA e = kummerEll hψ p hA e₂ * kummerEll hψ p hA e₁ := by
  have := orhdEquiv_comp hA e₁ e₂ e he
  simp only [kummerEll]
  rw [← map_mul]
  exact congrArg _ this

/-- `κ ∘ (O^▷(A) ≅ O^▷_ℂ)⁻¹` is the restriction of the topological isomorphism `ℂ ≅ A_D`. -/
theorem continuous_kummerEll {A : Obj} (hA : IsIsotropic P A) :
    Continuous fun z : orhdC => kummerEll hψ p hA ((orhdEquiv hA).symm z) := by
  have : (fun z : orhdC => kummerEll hψ p hA ((orhdEquiv hA).symm z)) =
      fun z : orhdC => (Ell.ellEquiv hψ p).symm z := by
    funext z
    simp only [kummerEll]
    congr 1
    exact congrArg Subtype.val ((orhdEquiv hA).apply_symm_apply z)
  rw [this]
  exact (Ell.continuous_ellEquiv_symm hψ p).comp continuous_subtype_val

/-- The image of `κ` is `{x ∈ A_D^× : |x| ≤ 1}`. -/
theorem range_kummerEll {A : Obj} (hA : IsIsotropic P A) :
    range (kummerEll hψ p hA) = {x | Ell.ellEquiv hψ p x ∈ orhdC} := by
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    simp only [mem_setOf_eq, ellEquiv_kummerEll]
    exact (orhdEquiv hA e).2
  · intro hx
    refine ⟨(orhdEquiv hA).symm ⟨_, hx⟩, ?_⟩
    apply (Ell.ellEquiv hψ p).injective
    rw [ellEquiv_kummerEll]
    exact congrArg Subtype.val ((orhdEquiv hA).apply_symm_apply ⟨_, hx⟩)

/-- Compatibility with the isomorphisms `O^▷(A) ≅ O^▷(B)` induced by pre-steps. -/
theorem kummerEll_transport {A B : Obj} (hA : IsIsotropic P A) (hB : IsIsotropic P B)
    (φ : A ⟶ B) (hφ : IsPreStep P φ) (e : Orhd P A) (e' : Orhd P B) (h : φ ≫ e'.1 = e.1 ≫ φ) :
    kummerEll hψ p hB e' = kummerEll hψ p hA e := by
  simp only [kummerEll]
  rw [val_transport φ hφ ((mem_orhd _).mp e.2) ((mem_orhd _).mp e'.2) h]

/-- **The Kummer indeterminacy**: Kummer structures defined via two isomorphisms `ψ, ψ'` of `D`
with once-punctured complex tori agree up to `Gal(ℂ/ℝ)`. -/
theorem kummerEll_indet {L' : PeriodPair} {ψ' : X ≃ₜ Ell.punct L'}
    (hψ' : IsIso D (Ell.ellStr L') ψ') {A : Obj} (hA : IsIsotropic P A) :
    (∀ e, Ell.ellEquiv hψ' p (kummerEll hψ p hA e) = val e.1) ∨
      ∀ e, Ell.ellEquiv hψ' p (kummerEll hψ p hA e) = starRingEnd ℂ (val e.1) := by
  rcases Ell.ellEquiv_trans_eq hψ p hψ' with h | h
  · left
    intro e
    exact congrArg (fun f : ℂ →+* ℂ => f (val e.1)) h
  · right
    intro e
    exact congrArg (fun f : ℂ →+* ℂ => f (val e.1)) h

end Ell

end

end Angular

end Frobenioid

end Iut
