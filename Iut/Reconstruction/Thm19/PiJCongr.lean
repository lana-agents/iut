/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ResKer

/-!
# `Π_{J¹}`, `Δ_X^{ab}`, the sections `t_x` and `η_D` along isomorphisms (MR9 item 4, step 3)

[AbsTopIII] Thm 1.9 (c) (`Topics in Absolute Anabelian Geometry III.txt` l.2153–2157) builds
`P_U` from the characterisation of principal divisors in Prop 1.6 (ii) (l.1993–2000): the
sections `t_x : G_k → Π_{J¹}` of rational points (`Π_X ↠ Π_{J¹}` with kernel the commutator
subgroup of `Δ_X`, l.1979–1982) and the class `η_D` of `t_D` against the identity section. For
its functoriality in isomorphisms, generically in the Galois models (curves-jacobian
`Kummer/JacobianPi1.lean`):

* **`piUToPiX_eq_one_iff_of_maps`**: an isomorphism `E : Π_U ≃ₜ* Π_{U'}` such that `E` and `E⁻¹`
  preserve cuspidal inertia (`MapsCuspInertia`) matches the kernels of `Π_U ↠ Π_X` (the input
  `hfill` of `piXCongr`);
* for `X : Π_X ≃ₜ* Π_{X'}` over `ψ : G_k ≃ₜ* G_{k'}`: `mem_deltaX_iff_of_piX`,
  **`mem_commClosure_iff_of_piX`** (`X` matches `\overline{[Δ_X, Δ_X]}`), **`piJ1Congr`**
  (`Π_{J¹} ≃ₜ* Π_{J¹'}`), `deltaXIso`, **`deltaAbCongr`** (`Δ_X^{ab} ≃ₜ* Δ_{X'}^{ab}`, equivariant
  along `ψ`: `deltaAbCongr_smul`);
* `sectionCongr` (sections `J ∘ s ∘ ψ⁻¹`), **`h1Congr_diffClass`** (difference classes are
  carried to difference classes), `h1Congr_etaWith`;
* **`eta_mapDomain`**: for a map `β` of rational points whose sections `t_{β x}` are
  `Δ_{X'}^{ab}`-conjugate to the transported `t_x`, `η_{β_* f} = h1Congr (η_f)` for `deg f = 0`.
-/

open KummerTheory Curve AffOrbicurve CurvesJacobian CurvesJacobian.Kummer Pi1.Orbifold

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

/-- Shortcut instance. -/
local instance mulOneClass_piX' {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
    (D : GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] :
    MulOneClass (PiX D) :=
  @Monoid.toMulOneClass _ (@DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _ (group_piX D)))

/-- Shortcut instance. -/
local instance one_piX' {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
    (D : GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] : One (PiX D) :=
  (mulOneClass_piX' D).toOne

/-- Shortcut instance. -/
local instance mul_piX' {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
    (D : GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] : Mul (PiX D) :=
  (mulOneClass_piX' D).toMul

/-- Shortcut instance. -/
local instance bracket_piX' {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
    (D : GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] :
    Bracket (PiX D) (PiX D) :=
  @commutatorElement _ (group_piX D)

/-- Shortcut instance. -/
local instance inv_piX' {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
    (D : GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] : Inv (PiX D) :=
  (group_piX D).toInv

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω']

/-! ### The filling `Π_U ↠ Π_X` -/

section Fill

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotient `Π_X` are found slowly
/-- **An isomorphism preserving cuspidal inertia in both directions matches the kernels of the
fillings** `Π_U ↠ Π_X` (`piUToPiX_eq_one_iff`, `mem_closure_iff_of_image`). -/
theorem piUToPiX_eq_one_iff_of_maps (hH : D.H ≤ D.HL) (hH' : D'.H ≤ D'.HL)
    (E : Pi D ≃ₜ* Pi D') (hE : MapsCuspInertia ⇑E) (hE' : MapsCuspInertia ⇑E.symm) (x : Pi D) :
    piUToPiX D' (E x) = 1 ↔ piUToPiX D x = 1 := by
  rw [piUToPiX_eq_one_iff D' hH', piUToPiX_eq_one_iff D hH]
  refine mem_closure_iff_of_image E (fun y => ⟨?_, ?_⟩) x
  · rintro ⟨W, hW, σ, hσ, rfl⟩
    obtain ⟨W', hW', σ', hσ', h⟩ := hE W hW σ hσ
    exact ⟨W', hW', σ', hσ', h⟩
  · rintro ⟨W', hW', σ', hσ', h⟩
    obtain ⟨W, hW, σ, hσ, h2⟩ := hE' W' hW' σ' hσ'
    refine ⟨W, hW, σ, hσ, ?_⟩
    rw [← h2, ← h, ContinuousMulEquiv.symm_apply_apply]

end Fill

/-! ### `Δ_X`, its closed commutator subgroup, `Π_{J¹}` and `Δ_X^{ab}` -/

section PiJ

variable (X : PiX D ≃ₜ* PiX D') (ψ : Gk k Ω ≃ₜ* Gk k' Ω')
  (hX : ∀ y, piXToGk D' (X y) = ψ (piXToGk D y))

include hX in
lemma mem_deltaX_iff_of_piX (y : PiX D) : X y ∈ DeltaX D' ↔ y ∈ DeltaX D := by
  change piXToGk D' _ = 1 ↔ piXToGk D y = 1
  rw [hX, map_eq_one_iff _ ψ.injective]

include hX in
lemma mem_deltaX_iff_of_piX_symm (y : PiX D') : X.symm y ∈ DeltaX D ↔ y ∈ DeltaX D' := by
  rw [← mem_deltaX_iff_of_piX X ψ hX, ContinuousMulEquiv.apply_symm_apply]

include hX in
lemma mem_commSet_iff_of_piX (x : PiX D) :
    x ∈ {g | ∃ g₁ ∈ DeltaX D, ∃ g₂ ∈ DeltaX D, ⁅g₁, g₂⁆ = g} ↔
      X x ∈ {g | ∃ g₁ ∈ DeltaX D', ∃ g₂ ∈ DeltaX D', ⁅g₁, g₂⁆ = g} := by
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨X a, (mem_deltaX_iff_of_piX X ψ hX a).2 ha, X b, (mem_deltaX_iff_of_piX X ψ hX b).2 hb,
      (map_commutatorElement X a b).symm⟩
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨X.symm a, (mem_deltaX_iff_of_piX_symm X ψ hX a).2 ha, X.symm b,
      (mem_deltaX_iff_of_piX_symm X ψ hX b).2 hb, ?_⟩
    rw [← map_commutatorElement, h, ContinuousMulEquiv.symm_apply_apply]

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotient `Π_X` are found slowly
include hX in
/-- **`X` matches the closed commutator subgroups `\overline{[Δ_X, Δ_X]}`.** -/
theorem mem_commClosure_iff_of_piX (x : PiX D) :
    X x ∈ commClosure D' ↔ x ∈ commClosure D := by
  change X x ∈ (⁅DeltaX D', DeltaX D'⁆).topologicalClosure ↔
    x ∈ (⁅DeltaX D, DeltaX D⁆).topologicalClosure
  rw [Subgroup.commutator_def, Subgroup.commutator_def]
  exact mem_closure_iff_of_image X (mem_commSet_iff_of_piX X ψ hX) x

/-- **`Π_{J¹} ≃ₜ* Π_{J¹'}`** from `X : Π_X ≃ₜ* Π_{X'}` over `ψ`. -/
def piJ1Congr : PiJ1 D ≃ₜ* PiJ1 D' :=
  descendCongr (piXToPiJ1 D) (piXToPiJ1 D') (continuous_piXToPiJ1 D) (continuous_piXToPiJ1 D')
    (piXToPiJ1_surjective D) (piXToPiJ1_surjective D') X fun x => by
      rw [piXToPiJ1_eq_one_iff, piXToPiJ1_eq_one_iff]
      exact mem_commClosure_iff_of_piX X ψ hX x

lemma piJ1Congr_piXToPiJ1 (x : PiX D) :
    piJ1Congr X ψ hX (piXToPiJ1 D x) = piXToPiJ1 D' (X x) :=
  descendCongr_apply _ _ _ _ _ _ _ _ x

lemma piJ1ToGk_piJ1Congr (y : PiJ1 D) :
    piJ1ToGk D' (piJ1Congr X ψ hX y) = ψ (piJ1ToGk D y) := by
  obtain ⟨x, rfl⟩ := piXToPiJ1_surjective D y
  rw [piJ1Congr_piXToPiJ1, piJ1ToGk_piXToPiJ1, piJ1ToGk_piXToPiJ1, hX]

/-- **`Δ_X ≃ₜ* Δ_{X'}`**, the restriction of `X`. -/
def deltaXIso : DeltaX D ≃ₜ* DeltaX D' where
  toFun δ := ⟨X (δ : PiX D), (mem_deltaX_iff_of_piX X ψ hX _).2 δ.2⟩
  invFun δ := ⟨X.symm (δ : PiX D'), (mem_deltaX_iff_of_piX_symm X ψ hX _).2 δ.2⟩
  left_inv δ := Subtype.ext (X.symm_apply_apply (δ : PiX D))
  right_inv δ := Subtype.ext (X.apply_symm_apply (δ : PiX D'))
  map_mul' a b := Subtype.ext (map_mul X (a : PiX D) b)
  continuous_toFun := (X.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (X.symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] lemma coe_deltaXIso (δ : DeltaX D) : (deltaXIso X ψ hX δ : PiX D') = X (δ : PiX D) := rfl

lemma continuous_deltaAbMk : Continuous (deltaAbMk D) :=
  QuotientGroup.continuous_mk

/-- **`Δ_X^{ab} ≃ₜ* Δ_{X'}^{ab}`** from `X : Π_X ≃ₜ* Π_{X'}` over `ψ`. -/
def deltaAbCongr : DeltaAb D ≃ₜ* DeltaAb D' :=
  descendCongr (deltaAbMk D) (deltaAbMk D') continuous_deltaAbMk continuous_deltaAbMk
    (deltaAbMk_surjective D) (deltaAbMk_surjective D') (deltaXIso X ψ hX) fun x => by
      rw [deltaAbMk_eq_one_iff, deltaAbMk_eq_one_iff, coe_deltaXIso]
      exact mem_commClosure_iff_of_piX X ψ hX x

lemma deltaAbCongr_deltaAbMk (x : DeltaX D) :
    deltaAbCongr X ψ hX (deltaAbMk D x) = deltaAbMk D' (deltaXIso X ψ hX x) :=
  descendCongr_apply _ _ _ _ _ _ _ _ x

lemma deltaAbToPiJ1_deltaAbCongr (m : DeltaAb D) :
    deltaAbToPiJ1 D' (deltaAbCongr X ψ hX m) = piJ1Congr X ψ hX (deltaAbToPiJ1 D m) := by
  obtain ⟨x, rfl⟩ := deltaAbMk_surjective D m
  rw [deltaAbCongr_deltaAbMk, deltaAbToPiJ1_deltaAbMk, deltaAbToPiJ1_deltaAbMk,
    piJ1Congr_piXToPiJ1, coe_deltaXIso]

variable [Fact (Function.Surjective (piJ1ToGk D))] [Fact (Function.Surjective (piJ1ToGk D'))]

/-- **`deltaAbCongr` is equivariant along `ψ`.** -/
theorem deltaAbCongr_smul (g : Gk k Ω) (m : DeltaAb D) :
    deltaAbCongr X ψ hX (g • m) = ψ g • deltaAbCongr X ψ hX m := by
  apply deltaAbToPiJ1_injective D'
  have hp := piJ1ToGk_liftGk D g
  have hq : piJ1ToGk D' (piJ1Congr X ψ hX (liftGk D g)) = ψ g := by
    rw [piJ1ToGk_piJ1Congr, hp]
  rw [deltaAbToPiJ1_deltaAbCongr, deltaAbToPiJ1_smul D g m hp, deltaAbToPiJ1_smul D' _ _ hq,
    deltaAbToPiJ1_deltaAbCongr, map_mul, map_mul, map_inv]

/-! ### Sections and difference classes -/

/-- **The transported section** `J ∘ s ∘ ψ⁻¹`. -/
def sectionCongr (s : J1Section D) : J1Section D' where
  toHom := (piJ1Congr X ψ hX).toMulEquiv.toMonoidHom.comp
    (s.toHom.comp ψ.symm.toMulEquiv.toMonoidHom)
  continuous_toHom := (piJ1Congr X ψ hX).continuous.comp
    (s.continuous_toHom.comp ψ.symm.continuous)
  piJ1ToGk_toHom g := by
    change piJ1ToGk D' (piJ1Congr X ψ hX (s.toHom (ψ.symm g))) = g
    rw [piJ1ToGk_piJ1Congr, s.piJ1ToGk_toHom, ContinuousMulEquiv.apply_symm_apply]

lemma sectionCongr_toHom (s : J1Section D) (g : Gk k' Ω') :
    (sectionCongr X ψ hX s).toHom g = piJ1Congr X ψ hX (s.toHom (ψ.symm g)) := rfl

/-- The coefficients `deltaAbCongr`, in the form used by `h1Congr`. -/
lemma deltaAbCongr_smul' (g : Gk k Ω) (m : DeltaAb D) :
    deltaAbCongr X ψ hX (g • m) = ψ g • deltaAbCongr X ψ hX m :=
  deltaAbCongr_smul X ψ hX g m

set_option synthInstance.maxHeartbeats 400000 in
-- the action of `G_k` on `Δ_X^{ab}` is found slowly
/-- **Difference classes are carried to difference classes**:
`h1Congr ψ (deltaAbCongr) [s − s'] = [J s − J s']`. -/
theorem h1Congr_diffClass (s s' : J1Section D) :
    h1Congr ψ (deltaAbCongr X ψ hX) (deltaAbCongr_smul' X ψ hX) (diffClass s s') =
      diffClass (sectionCongr X ψ hX s) (sectionCongr X ψ hX s') := by
  rw [h1Congr_apply, diffClass, diffClass, ContH1.map_mk]
  congr 1
  apply Subtype.ext
  funext g
  simp only [ContH1.cocyclesMap_apply]
  apply deltaAbToPiJ1_injective D'
  change deltaAbToPiJ1 D' (deltaAbCongr X ψ hX (diffFun s s' (ψ.symm g))) =
    deltaAbToPiJ1 D' (diffFun (sectionCongr X ψ hX s) (sectionCongr X ψ hX s') g)
  rw [deltaAbToPiJ1_deltaAbCongr, deltaAbToPiJ1_diffFun, deltaAbToPiJ1_diffFun, map_mul, map_inv,
    sectionCongr_toHom, sectionCongr_toHom]

/-- `etaWith` along the isomorphisms. -/
theorem h1Congr_etaWith {ι : Type*} (s : ι → J1Section D) (f : ι →₀ ℤ) (i₀ : ι) :
    h1Congr ψ (deltaAbCongr X ψ hX) (deltaAbCongr_smul' X ψ hX) (etaWith s f i₀) =
      etaWith (fun i => sectionCongr X ψ hX (s i)) f i₀ := by
  rw [etaWith, etaWith, map_finsuppProd]
  refine Finsupp.prod_congr fun i _ => ?_
  rw [map_zpow, h1Congr_diffClass]

/-! ### `η_D` along a map of rational points -/

/-- Two sections with trivial difference class against the transported ones have the same
difference class as the transported ones. -/
lemma diffClass_eq_of_conj {s₁ s₂ : J1Section D} {r₁ r₂ : J1Section D'}
    (h₁ : diffClass (sectionCongr X ψ hX s₁) r₁ = 1)
    (h₂ : diffClass (sectionCongr X ψ hX s₂) r₂ = 1) :
    diffClass r₁ r₂ = diffClass (sectionCongr X ψ hX s₁) (sectionCongr X ψ hX s₂) := by
  calc diffClass r₁ r₂ = diffClass r₁ (sectionCongr X ψ hX s₁) *
        (diffClass (sectionCongr X ψ hX s₁) (sectionCongr X ψ hX s₂) *
          diffClass (sectionCongr X ψ hX s₂) r₂) := by
        rw [diffClass_mul, diffClass_mul]
    _ = diffClass (sectionCongr X ψ hX s₁) (sectionCongr X ψ hX s₂) := by
        rw [diffClass_swap (sectionCongr X ψ hX s₁) r₁, h₁, h₂, inv_one, one_mul, mul_one]

lemma eta_zero : eta (0 : RatPoint D →₀ ℤ) = 1 := by
  unfold eta
  rw [dif_neg (by simp)]

lemma sum_mapDomain_deg {α β : Type*} (g : α → β) (f : α →₀ ℤ) :
    ((f.mapDomain g).sum fun _ n => n) = f.sum fun _ n => n :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

variable (β : RatPoint D → RatPoint D')
  (hβ : ∀ x, diffClass (sectionCongr X ψ hX (tSection x)) (tSection (β x)) = 1)

include hβ in
/-- `etaDiv` along a map of rational points with matching sections. -/
theorem etaDiv_mapDomain (f : RatPoint D →₀ ℤ) (x₀ : RatPoint D) :
    etaDiv (f.mapDomain β) (β x₀) =
      h1Congr ψ (deltaAbCongr X ψ hX) (deltaAbCongr_smul' X ψ hX) (etaDiv f x₀) := by
  rw [etaDiv, etaDiv, h1Congr_etaWith, etaWith, etaWith,
    Finsupp.prod_mapDomain_index (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)]
  refine Finsupp.prod_congr fun x _ => ?_
  rw [diffClass_eq_of_conj X ψ hX (hβ x) (hβ x₀)]

include hβ in
/-- **`η_D` along the isomorphisms**: for a map `β` of rational points whose sections `t_{β x}`
have trivial difference class against the transported `t_x` (e.g. `Δ_{X'}^{ab}`-conjugate ones,
`diffClass_eq_one_of_conj`), `η_{β_* f} = h1Congr (η_f)` for `deg f = 0`. -/
theorem eta_mapDomain (f : RatPoint D →₀ ℤ) (hf : (f.sum fun _ n => n) = 0) :
    eta (f.mapDomain β) =
      h1Congr ψ (deltaAbCongr X ψ hX) (deltaAbCongr_smul' X ψ hX) (eta f) := by
  rcases f.support.eq_empty_or_nonempty with h | ⟨x₀, -⟩
  · rw [Finsupp.support_eq_empty.1 h, Finsupp.mapDomain_zero, eta_zero, eta_zero, map_one]
  · rw [eta_eq_etaDiv f hf x₀, eta_eq_etaDiv _ ((sum_mapDomain_deg β f).trans hf) (β x₀),
      etaDiv_mapDomain X ψ hX β hβ]

end PiJ

end Iut.Reconstruction.Thm19
