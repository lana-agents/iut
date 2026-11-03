/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.GalConj
import Iut.Reconstruction.Thm19.StageIso

/-!
# Conjugation on the Galois models and the Kummer map of a curve (MR9, `CKSemiAbsConj` item 3)

For a Galois model `D` of an affine curve `U` (`Π_U = H ⧸ ⟨⟨S⟩⟩`) and a ring automorphism `a` of
`Ω` normalising it (`a` maps `k(t)` into itself, `σ ↦ a⁻¹ σ a` preserves `H` and `H_L`, and `a`
maps the places centred on `U` to such places), conjugation by `a` acts on `Π_U` and on
`H¹(Π_U, Ẑ(1))`; for `a ∈ H` this is the conjugation action of `Π_U` on its own `H¹` (trivial),
for the stages `U_{K'}` of [AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry
III.txt` l.2158–2178) with `K' / k` Galois it is the action of `Π_U` on `H¹(Π_{U_{K'}}, Ẑ(1))`.
Here:

* `conjHInv`, **`conjPiInv`**: `σ ↦ a⁻¹ σ a` on `H` and on `Π_U` (inertia at `W` goes to inertia
  at `a⁻¹ W`, `galConjInv_mem_inertia`);
* **`conjPiH1`**: `H¹(Π_U, Ẑ(1)) → H¹(Π_U, Ẑ(1))`, cocycles `c ↦ a ∘ c ∘ conjPiInv`;
* `mem_F_conj`: `a` maps `F = Ω^H` into itself;
* **`conjPiH1_kummerMapZHat`**: `a_*(κ_U(u)) = κ_U(u')` for units with `u' = a(u)` (inflation to
  `H`, restriction from `Gal(Ω/F)`, `conjH1_kummerZHat`);
* **`resT_conjPiH1`**: conjugation commutes with the transition maps of the colimit;
* **`h1Congr_map_comm`** (generic): `h1Congr e χ` intertwines `ContH1.map φ f` and
  `ContH1.map φ' f'` if `e ∘ φ = φ' ∘ e` and `χ ∘ f = f' ∘ χ`.
-/

open KummerTheory Curve AffOrbicurve

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

/-! ### `h1Congr` and maps of cohomology -/

section Generic

variable {P P' M M' : Type*} [Group P] [TopologicalSpace P] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction P M]
  [Group P'] [TopologicalSpace P'] [CommGroup M'] [TopologicalSpace M']
  [IsTopologicalGroup M'] [MulDistribMulAction P' M']

/-- **`h1Congr e χ` intertwines maps of cohomology** compatible with `e` and `χ`. -/
theorem h1Congr_map_comm (e : P ≃ₜ* P') (χ : M ≃ₜ* M') (hχ : ∀ p m, χ (p • m) = e p • χ m)
    (φ : P →* P) (hφ : Continuous φ) (f : M →* M) (hf : Continuous f)
    (hcomp : ∀ p m, f (φ p • m) = p • f m)
    (φ' : P' →* P') (hφ' : Continuous φ') (f' : M' →* M') (hf' : Continuous f')
    (hcomp' : ∀ p m, f' (φ' p • m) = p • f' m)
    (he : ∀ p, e (φ p) = φ' (e p)) (hfχ : ∀ m, χ (f m) = f' (χ m)) (x : ContH1 P M) :
    h1Congr e χ hχ (ContH1.map φ hφ f hf hcomp x) =
      ContH1.map φ' hφ' f' hf' hcomp' (h1Congr e χ hχ x) := by
  induction x using ContH1.induction_on with
  | h c =>
    rw [h1Congr_apply, h1Congr_apply]
    simp only [ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext p'
    simp only [ContH1.cocyclesMap_apply]
    have h1 : φ (e.symm p') = e.symm (φ' p') := by
      rw [ContinuousMulEquiv.eq_symm_apply, he, ContinuousMulEquiv.apply_symm_apply]
    change χ (f (c (φ (e.symm p')))) = f' (χ (c (e.symm (φ' p'))))
    rw [h1, hfχ]

end Generic

/-! ### Conjugation on a Galois model -/

section Model

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω]
  (a : Ω ≃+* Ω) (hK₀ : ∀ x ∈ K₀ k t, a x ∈ K₀ k t)
  (hH : ∀ σ ∈ D.H, galConjInv (K₀ k t) a hK₀ σ ∈ D.H)

/-- **`σ ↦ a⁻¹ σ a` on `H`.** -/
def conjHInv : D.H →* D.H :=
  ((galConjInv (K₀ k t) a hK₀).comp D.H.subtype).codRestrict D.H fun σ => hH σ σ.2

omit [IsGalois (K₀ k t) Ω] in
@[simp]
lemma conjHInv_apply (σ : D.H) (x : Ω) :
    ((conjHInv D a hK₀ hH σ : D.H) : Ω ≃ₐ[K₀ k t] Ω) x = a.symm ((σ : Ω ≃ₐ[K₀ k t] Ω) (a x)) :=
  rfl

lemma continuous_conjHInv : Continuous (conjHInv D a hK₀ hH) :=
  ((continuous_galConjInv (K₀ k t) a hK₀).comp continuous_subtype_val).subtype_mk _

omit [IsGalois (K₀ k t) Ω] in
include hH in
/-- `a` maps the function field `F = Ω^H` into itself. -/
lemma mem_F_conj {x : Ω} (hx : x ∈ F D) : a x ∈ F D := by
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro τ hτ
  have h := hx _ (hH τ hτ)
  rw [galConjInv_apply] at h
  have h' := congrArg a h
  rwa [RingEquiv.apply_symm_apply] at h'

omit [IsGalois (K₀ k t) Ω] in
lemma toGalF_conjHInv (σ : D.H) :
    toGalF D (conjHInv D a hK₀ hH σ) =
      galConjInv (F D) a (fun _ hx => mem_F_conj D a hK₀ hH hx) (toGalF D σ) :=
  AlgEquiv.ext fun _ => rfl

/-- `v_{a⁻¹W}(a⁻¹ y) < 1 ↔ v_W(y) < 1`. -/
lemma valuation_comap_symm_lt_one_iff (W : ValuationSubring Ω) (y : Ω) :
    (W.comap (a : Ω →+* Ω)).valuation (a.symm y) < 1 ↔ W.valuation y < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply,
    map_eq_zero_iff _ a.symm.injective]

omit [IsGalois (K₀ k t) Ω] in
/-- **Inertia at `W` goes to inertia at `a⁻¹ W`.** -/
lemma galConjInv_mem_inertia {W : ValuationSubring Ω} {σ : Ω ≃ₐ[K₀ k t] Ω}
    (hσ : σ ∈ GaloisPi1.inertia W) :
    galConjInv (K₀ k t) a hK₀ σ ∈ GaloisPi1.inertia (W.comap (a : Ω →+* Ω)) := by
  intro y hy
  have h1 : galConjInv (K₀ k t) a hK₀ σ y - y = a.symm (σ (a y) - a y) := by
    rw [galConjInv_apply, map_sub, RingEquiv.symm_apply_apply]
  rw [h1, valuation_comap_symm_lt_one_iff]
  exact hσ _ (ValuationSubring.mem_comap.1 hy)

variable (hHL : ∀ σ ∈ D.HL, galConjInv (K₀ k t) a hK₀ σ ∈ D.HL)
  (hW : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → t ∈ W →
    (∀ c : k, a (algebraMap k Ω c) ∈ W) ∧ a t ∈ W)

omit [IsGalois (K₀ k t) Ω] in
include hHL hW in
lemma conjHInv_mem_S {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S) :
    ((conjHInv D a hK₀ hH σ : D.H) : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S := by
  obtain ⟨hσL, W, hk, htW, hI⟩ := hσ
  obtain ⟨hk', ht'⟩ := hW W hk htW
  exact ⟨hHL _ hσL, W.comap (a : Ω →+* Ω), fun c => ValuationSubring.mem_comap.2 (hk' c),
    ValuationSubring.mem_comap.2 ht', galConjInv_mem_inertia a hK₀ hI⟩

include hHL hW in
lemma kernel_le_comap_conjHInv :
    GaloisPi1.kernel D.H D.S ≤ (GaloisPi1.kernel D.H D.S).comap (conjHInv D a hK₀ hH) := by
  have hS : D.S ⊆ D.H := fun _ h => D.le h.1
  refine le_trans (le_of_eq (GaloisPi1.kernel_eq_topologicalClosure _ D.isClosed_H _ hS)) ?_
  haveI : (GaloisPi1.kernel D.H D.S).Normal := inferInstance
  haveI : ((GaloisPi1.kernel D.H D.S).comap (conjHInv D a hK₀ hH)).Normal :=
    Subgroup.Normal.comap inferInstance _
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
    ((GaloisPi1.isClosed_kernel D.H D.S).preimage (continuous_conjHInv D a hK₀ hH))
  intro s hs
  change conjHInv D a hK₀ hH s ∈ GaloisPi1.kernel D.H D.S
  rw [GaloisPi1.kernel_eq_topologicalClosure _ D.isClosed_H _ hS]
  exact Subgroup.le_topologicalClosure _
    (Subgroup.subset_normalClosure (conjHInv_mem_S D a hK₀ hH hHL hW hs))

/-- **`p ↦ a⁻¹ p a` on `Π_U`.** -/
def conjPiInv : Pi D →* Pi D :=
  QuotientGroup.map _ _ (conjHInv D a hK₀ hH) (kernel_le_comap_conjHInv D a hK₀ hH hHL hW)

@[simp]
lemma conjPiInv_mk (σ : D.H) :
    conjPiInv D a hK₀ hH hHL hW (σ : Pi D) = (conjHInv D a hK₀ hH σ : Pi D) := rfl

lemma continuous_conjPiInv : Continuous (conjPiInv D a hK₀ hH hHL hW) := by
  change Continuous (QuotientGroup.map _ _ (conjHInv D a hK₀ hH)
    (kernel_le_comap_conjHInv D a hK₀ hH hHL hW))
  rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
  exact QuotientGroup.continuous_mk.comp (continuous_conjHInv D a hK₀ hH)

variable [CharZero k]

omit [IsGalois (K₀ k t) Ω] [CharZero k] in
lemma zConj_conjHInv_smul (K : Type*) [Field K] (σ : D.H) (m : ZHatOne K Ω) :
    zConj a K (conjHInv D a hK₀ hH σ • m) = σ • zConj a K m :=
  zConj_galConjInv_smul (K₀ k t) a hK₀ K (σ : Ω ≃ₐ[K₀ k t] Ω) m

lemma zConj_conjPiInv_smul (K : Type*) [Field K] (p : Pi D) (m : ZHatOne K Ω) :
    zConj a K (conjPiInv D a hK₀ hH hHL hW p • m) = p • zConj a K m := by
  induction p using QuotientGroup.induction_on with
  | H σ => exact zConj_conjHInv_smul D a hK₀ hH K σ m

/-- **Conjugation by `a` on `H¹(Π_U, Ẑ(1))`**, cocycles `c ↦ a ∘ c ∘ (p ↦ a⁻¹ p a)`. -/
def conjPiH1 : ContH1 (Pi D) (ZHatOne (F D) Ω) →* ContH1 (Pi D) (ZHatOne (F D) Ω) :=
  ContH1.map (conjPiInv D a hK₀ hH hHL hW) (continuous_conjPiInv D a hK₀ hH hHL hW)
    (zConj a (F D)) (continuous_zConj a (F D)) (zConj_conjPiInv_smul D a hK₀ hH hHL hW (F D))

/-- The same on `H¹(H, Ẑ(1))`. -/
def conjHH1 : ContH1 D.H (ZHatOne (F D) Ω) →* ContH1 D.H (ZHatOne (F D) Ω) :=
  ContH1.map (conjHInv D a hK₀ hH) (continuous_conjHInv D a hK₀ hH)
    (zConj a (F D)) (continuous_zConj a (F D)) (zConj_conjHInv_smul D a hK₀ hH (F D))

lemma inflZHat_conjPiH1 (x : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    inflZHat D (F D) (conjPiH1 D a hK₀ hH hHL hW x) = conjHH1 D a hK₀ hH (inflZHat D (F D) x) := by
  induction x using ContH1.induction_on with
  | h c => rfl

omit [CharZero k] in
lemma conjHH1_resZHat (X : ContH1 (Ω ≃ₐ[F D] Ω) (ZHatOne (F D) Ω)) :
    conjHH1 D a hK₀ hH (resZHat D (F D) X) =
      resZHat D (F D) (conjH1 (F D) a (fun _ hx => mem_F_conj D a hK₀ hH hx) X) := by
  induction X using ContH1.induction_on with
  | h c =>
    simp only [conjHH1, resZHat, Curve.res, conjH1, ContH1.map_mk]
    rfl

variable [IsSepClosed Ω]

set_option maxHeartbeats 1600000 in
-- the action instances of `inflation_injective` and of `inflZHat` are unified slowly
/-- **Conjugation of Kummer classes**: `a_*(κ_U(u)) = κ_U(u')` for units `u, u'` of `U` with
`u' = a(u)`. -/
theorem conjPiH1_kummerMapZHat (u u' : units D)
    (hu : (((u' : (F D)ˣ) : F D) : Ω) = a (((u : (F D)ˣ) : F D) : Ω)) :
    conjPiH1 D a hK₀ hH hHL hW (kummerMapZHat D u) = kummerMapZHat D u' := by
  apply ContH1.inflation_injective (N := GaloisPi1.kernel D.H D.S) (fun _ _ => rfl)
  rw [inflZHat_conjPiH1, inflation_kummerMapZHat, inflation_kummerMapZHat, conjHH1_resZHat,
    conjH1_kummerZHat]
  congr 2
  ext
  exact hu.symm

end Model

/-! ### Conjugation and the transition maps -/

section Transition

variable {k₁ k₂ Ω : Type u} [Field k₁] [Field k₂] [Field Ω] [Algebra k₁ Ω] [Algebra k₂ Ω]
  {t₁ t₂ : Ω} {D₁ : Pi1.Orbifold.GaloisData k₁ t₁} {D₂ : Pi1.Orbifold.GaloisData k₂ t₂}
  [IsGalois (K₀ k₁ t₁) Ω] [IsGalois (K₀ k₂ t₂) Ω]
  {hF : ∀ x ∈ F D₁, x ∈ F D₂}
  {hW : ∀ W : ValuationSubring Ω, (∀ c : k₂, algebraMap k₂ Ω c ∈ W) → t₂ ∈ W →
    (∀ c : k₁, algebraMap k₁ Ω c ∈ W) ∧ t₁ ∈ W} {hH₁ : D₁.H ≤ D₁.HL}
  (a : Ω ≃+* Ω)
  {hK₁ : ∀ x ∈ K₀ k₁ t₁, a x ∈ K₀ k₁ t₁}
  {hH₁' : ∀ σ ∈ D₁.H, galConjInv (K₀ k₁ t₁) a hK₁ σ ∈ D₁.H}
  {hHL₁ : ∀ σ ∈ D₁.HL, galConjInv (K₀ k₁ t₁) a hK₁ σ ∈ D₁.HL}
  {hW₁ : ∀ W : ValuationSubring Ω, (∀ c : k₁, algebraMap k₁ Ω c ∈ W) → t₁ ∈ W →
    (∀ c : k₁, a (algebraMap k₁ Ω c) ∈ W) ∧ a t₁ ∈ W}
  {hK₂ : ∀ x ∈ K₀ k₂ t₂, a x ∈ K₀ k₂ t₂}
  {hH₂ : ∀ σ ∈ D₂.H, galConjInv (K₀ k₂ t₂) a hK₂ σ ∈ D₂.H}
  {hHL₂ : ∀ σ ∈ D₂.HL, galConjInv (K₀ k₂ t₂) a hK₂ σ ∈ D₂.HL}
  {hW₂ : ∀ W : ValuationSubring Ω, (∀ c : k₂, algebraMap k₂ Ω c ∈ W) → t₂ ∈ W →
    (∀ c : k₂, a (algebraMap k₂ Ω c) ∈ W) ∧ a t₂ ∈ W}

lemma piT_conjPiInv (p : Pi D₂) :
    piT D₁ D₂ hF hW hH₁ (conjPiInv D₂ a hK₂ hH₂ hHL₂ hW₂ p) =
      conjPiInv D₁ a hK₁ hH₁' hHL₁ hW₁ (piT D₁ D₂ hF hW hH₁ p) := by
  induction p using QuotientGroup.induction_on with
  | H σ => exact congrArg (fun τ : D₁.H => (τ : Pi D₁)) (Subtype.ext (AlgEquiv.ext fun _ => rfl))

variable [CharZero k₁] [CharZero k₂]

omit [IsGalois (K₀ k₁ t₁) Ω] [IsGalois (K₀ k₂ t₂) Ω] [CharZero k₂] in
lemma zT_zConj (m : ZHatOne (F D₁) Ω) :
    zT D₁ D₂ (zConj a (F D₁) m) = zConj a (F D₂) (zT D₁ D₂ m) := by
  apply Subtype.ext
  funext i
  apply Mu.ext
  apply Units.ext
  rfl

/-- **Conjugation commutes with the transition maps** `resT`. -/
theorem resT_conjPiH1 (x : ContH1 (Pi D₁) (ZHatOne (F D₁) Ω)) :
    resT D₁ D₂ hF hW hH₁ (conjPiH1 D₁ a hK₁ hH₁' hHL₁ hW₁ x) =
      conjPiH1 D₂ a hK₂ hH₂ hHL₂ hW₂ (resT D₁ D₂ hF hW hH₁ x) := by
  induction x using ContH1.induction_on with
  | h c =>
    simp only [resT, conjPiH1, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext p
    simp only [ContH1.cocyclesMap_apply]
    rw [piT_conjPiInv, zT_zConj]

end Transition

end Iut.Reconstruction.Thm19
