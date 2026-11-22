/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.Theater.Semilinear

/-!
# Semilinear automorphisms on cuspidal places (MR22 T6: `χ` and the cusps)

IUT I, Example 4.3 (i) (l.6545–6600 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller
Theory I.txt`): `Aut_ϵ(C̲_K)` is the stabiliser of the cusp `ϵ`, and `χ` is the action on the
cusps `Q ≅ F_ℓ` of `X̲_K`. For the semilinear automorphisms `τ` of `Ω = K(E)^alg` of
`Semilinear.lean` (over `θ ∈ Aut(K)` with action `f` on `E(K)` and `τ(Q_ℓ) = Q_ℓ + T₀`):

* **`isCuspPlace_tau`**: `τ` maps a place over the cusp of `T` to a place over `f(T) − T₀`;
* **`cusp_label_tau`**: on labels `Q ≅ F_ℓ` this is the affine map `z ↦ s z − [T₀]` whose linear
  part `s` is the scalar of `rhoGal_psi` (the value of `χ` in `exists_normCK_chiN`);
* **`galDecomp_betaC`**: the induced automorphism `betaC` of `π₁(C)` maps the decomposition group
  of `W` onto that of `τ(W)`.
-/

noncomputable section

namespace Iut.Multiradial.Theater

open WeierstrassCurve Iut.Anabelian Iut.Anabelian.Genuine Iut.HodgeTheater
  Iut.Reconstruction.HemiGenuine Iut.Reconstruction.HemiCusp CurvesJacobian.Cusp

universe u

attribute [local instance low] Classical.propDecidable

set_option linter.unusedSectionVars false

section Tie

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]
  {θ : k ≃+* k} {τ : Ω E ≃+* Ω E} (hτ : IsSemilin E θ τ) (hE : E.map (θ : k →+* k) = E)
  (f : E.toAffine.Point →+ E.toAffine.Point)
  (hf : ∀ (x y : k) (h : E.toAffine.Nonsingular x y), ∃ h',
      f (.some x y h) = .some (θ x) (θ y) h')

include hf in
/-- **`τ` maps a place over the cusp of `T` to a place over `f(T) − T₀`.** -/
theorem isCuspPlace_tau {ℓ : ℕ} {T T₀ : E.toAffine.Point}
    (hT₀ : tauPt hτ hE (Qpt E ℓ) = Qpt E ℓ + base E T₀) {W : ValuationSubring (Ω E)}
    (h : IsCuspPlace E ℓ T W) :
    IsCuspPlace E ℓ (f T - T₀) (W.comap (τ.symm : Ω E →+* Ω E)) := by
  refine ⟨fun c => ?_, ?_⟩
  · change τ.symm (algebraMap k (Ω E) c) ∈ W
    rw [tau_symm_algebraMap hτ]
    exact h.1 _
  · have e : Qpt E ℓ - base E (f T - T₀) = tauPt hτ hE (Qpt E ℓ - base E T) := by
      rw [map_sub, map_sub, tauPt_base hτ hE f hf, hT₀]
      abel
    rw [e]
    have hp := h.2
    rcases hP : Qpt E ℓ - base E T with _ | ⟨x, y, hxy⟩
    · rw [hP] at hp
      exact absurd hp id
    rw [hP] at hp
    rw [tauPt_some]
    change τ.symm (τ x) ∉ W
    rw [RingEquiv.symm_apply_apply]
    exact hp

include hf in
/-- **The action of `τ` on the cusp labels** is `z ↦ s z − [T₀]` (`s` the scalar of `f` on
`E(k)[ℓ]/M`, as in `rhoGal_psi`). -/
theorem cusp_label_tau {ℓ : ℕ} [OddPrime ℓ] (M : AddSubgroup E.toAffine.Point)
    (e : Tor E ℓ ⧸ M.addSubgroupOf (Tor E ℓ) ≃+ ZMod ℓ) (s : (ZMod ℓ)ˣ)
    (hM : ∀ S : E.toAffine.Point, ℓ • S = 0 → f S - (s : ZMod ℓ).val • S ∈ M) {T₀ T : Tor E ℓ}
    (hT₀ : tauPt hτ hE (Qpt E ℓ) = Qpt E ℓ + base E T₀) {W : ValuationSubring (Ω E)}
    (h : IsCuspPlace E ℓ T W) : ∃ T' : Tor E ℓ,
      IsCuspPlace E ℓ T' (W.comap (τ.symm : Ω E →+* Ω E)) ∧
        qOf M e T' = s * qOf M e T - qOf M e T₀ := by
  refine ⟨fTor f T - T₀, ?_, by rw [qOf_sub, qOf_fTor f M e s hM]⟩
  have := isCuspPlace_tau hτ hE f hf hT₀ h
  rwa [AddSubgroup.coe_sub, coe_fTor]

/-- `τ σ τ⁻¹` stabilises `τ(W)` iff `σ` stabilises `W`. -/
lemma psi_mem_decompGal_iff (σ : Gal E) (W : ValuationSubring (Ω E)) :
    psi hτ σ ∈ decompGal (baseField E) (W.comap (τ.symm : Ω E →+* Ω E)) ↔
      σ ∈ decompGal (baseField E) W := by
  rw [mem_decompGal, mem_decompGal]
  have key : ∀ y, psi hτ σ (τ y) ∈ W.comap (τ.symm : Ω E →+* Ω E) ↔ σ y ∈ W := fun y => by
    rw [psi_apply']
    change τ.symm (τ (σ y)) ∈ W ↔ _
    rw [RingEquiv.symm_apply_apply]
  have key' : ∀ y, τ y ∈ W.comap (τ.symm : Ω E →+* Ω E) ↔ y ∈ W := fun y => by
    change τ.symm (τ y) ∈ W ↔ _
    rw [RingEquiv.symm_apply_apply]
  constructor
  · intro h y
    rw [← key, ← key']
    exact h (τ y)
  · intro h x
    obtain ⟨y, rfl⟩ := τ.surjective x
    rw [key, key']
    exact h y

/-- **`betaC` maps the decomposition group of `W` onto that of `τ(W)`.** -/
theorem galDecomp_betaC (W : ValuationSubring (Ω E)) :
    (galDecomp (Hgp E 1 ⊥ true) (SgenC E 1 ⊥) (isClosed_Hgp E 1 ⊥ true) W).map
        (betaC hτ).toMulEquiv.toMonoidHom =
      galDecomp (Hgp E 1 ⊥ true) (SgenC E 1 ⊥) (isClosed_Hgp E 1 ⊥ true)
        (W.comap (τ.symm : Ω E →+* Ω E)) := by
  ext y
  constructor
  · rintro ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨⟨psi hτ σ, mem_Hgp_one_bot_true E _⟩,
      Subgroup.mem_subgroupOf.2 ((psi_mem_decompGal_iff hτ σ W).2 (Subgroup.mem_subgroupOf.1 hσ)),
      rfl⟩
  · rintro ⟨σ', hσ', rfl⟩
    let σ : Hgp E 1 ⊥ true := ⟨(psi hτ).symm σ', mem_Hgp_one_bot_true E _⟩
    have hσ : (σ : Gal E) ∈ decompGal (baseField E) W := by
      rw [← psi_mem_decompGal_iff hτ]
      change psi hτ ((psi hτ).symm σ') ∈ _
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact Subgroup.mem_subgroupOf.1 hσ'
    refine ⟨galProj _ _ _ σ, ⟨σ, Subgroup.mem_subgroupOf.2 hσ, rfl⟩, ?_⟩
    change (QuotientGroup.mk ⟨psi hτ σ, mem_Hgp_one_bot_true E _⟩ :
      Hgp E 1 ⊥ true ⧸ GaloisPi1.kernel _ _) = QuotientGroup.mk σ'
    congr 1
    exact Subtype.ext (ContinuousMulEquiv.apply_symm_apply _ _)

end Tie

end Iut.Multiradial.Theater
