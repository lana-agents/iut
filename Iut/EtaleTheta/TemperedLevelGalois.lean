/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaProp13

/-!
# The tempered Galois correspondence for a finite étale level (MR15, obligation 13b)

For an étale level `L_X ≤ L'` (`fieldData`, `muL`), the image of `Π^tp_{L'} → Π^tp_X` is the
preimage of `Gal(Ω/L') · ⟨⟨S_X⟩⟩ / ⟨⟨S_X⟩⟩ ⊆ Π_X` under `tempToPi`:

* `fibreAct_eq_fibreSmul`: on the tempered covering of a finite étale cover, `γ ∈ Π^tp_X` acts
  on the fibre through any lift `σ ∈ H_X` of its image in `Π_X` (`f ↦ σ ∘ f`).
* **`mem_range_muL_iff`** (tempered Galois correspondence): `γ` lies in the image iff some lift
  `σ ∈ H_X` of `tempToPi γ` fixes `L'`; **`mem_range_muL_iff_forall`**: iff every lift does
  (the ambient kernel fixes `L'`, `ambientKernel_le_level`).
* **`normal_range_muL`**: if `Gal(Ω/L_X)` maps `L'` into itself, the image is normal.
* **`normal_piYddotX`**: under that hypothesis for `L' = L 0`, `Π^tp_Ÿ` is normal in `Π^tp_X`
  (MR15 obligation 13b, normality; the hypothesis holds for the levels of
  `exists_etaleThetaSystem`, whose last conjunct contains `σ(L_j) ⊆ L_j`, `level_stable`).
* `galoisToTempered_mem_range_muL_iff`, `piY_not_le_range_muL`: a decomposition-group element
  moving an element of `L'` shows `Π^tp_Y ⊄ Π^tp_{L'}` (the lower bound in
  `[Π^tp_Y : Π^tp_Ÿ] = 2`). The upper bound `≤ 2` needs `Π^tp_Y ≤ Π^tp_{E_{q²}}` (the `ℤ`-cover
  `Y → X` factors through the 2-gon cover `E_{q²} → E_q`), a tempered input of the same kind as
  debt C1 (`MR14-plan.md`, run 17).
-/

open CategoryTheory Pi1.Orbifold AffOrbicurve KummerTheory KummerTheory.Curve
open CurvesJacobian.Cusp TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta

section Fibre

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω]
  (O : ValuationSubring k) (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)

/-- `temperedToEtale γ` is the action of any lift `σ ∈ H` of `tempToPi γ`. -/
theorem temperedToEtale_eq_toEtalePi1 (γ : TempPi D O V hV) (σ : D.H)
    (hσ : (σ : Pi D) = tempToPi D O V hV γ) :
    temperedToEtale O D.R D.A V hV γ = D.toEtalePi1 σ := by
  apply D.equivPi1.injective
  change etaleToPi D (temperedToEtale O D.R D.A V hV γ) = etaleToPi D (D.toEtalePi1 σ)
  rw [etaleToPi_toEtalePi1, hσ]
  rfl

/-- **The action of `γ ∈ Π^tp` on the fibre of a finite étale cover** is the action
`f ↦ σ ∘ f ∘ (X.act σ̄)⁻¹` of any lift `σ ∈ H` of `tempToPi γ`. -/
theorem fibreAct_eq_fibreSmul (γ : TempPi D O V hV) (σ : D.H)
    (hσ : (σ : Pi D) = tempToPi D O V hV γ) (X : EquivEtale D.R D.A)
    (x : TempObj.Fibre Ω V hV ((etaleToTemp O D.R D.A).obj X)) :
    etaleToTempFibreEquiv O D.R D.A V hV X (γ.app ((etaleToTemp O D.R D.A).obj X) x) =
      D.fibreSmul σ X (etaleToTempFibreEquiv O D.R D.A V hV X x) := by
  set e := etaleToTempFibreEquiv O D.R D.A V hV X
  calc e (γ.app ((etaleToTemp O D.R D.A).obj X) x)
      = e (γ.app ((etaleToTemp O D.R D.A).obj X) (e.symm (e x))) := by
        rw [Equiv.symm_apply_apply]
    _ = (temperedToEtale O D.R D.A V hV γ).app X (e x) := rfl
    _ = (D.toEtalePi1 σ).app X (e x) := by rw [temperedToEtale_eq_toEtalePi1 D O V hV γ σ hσ]
    _ = D.fibreSmul σ X (e x) := rfl

end Fibre

section Correspondence

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (ht : Transcendental k t)
  [IsGalois (K₀ k t) Ω] [CharZero k]
  {LX : IntermediateField (K₀ k t) Ω} (hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
  (L' : IntermediateField (K₀ k t) Ω)
  (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))) [hX : Fact (LX ≤ L')]
  [het : Algebra.Etale (fieldData ht LX hLX).R (fieldData ht L' hL').R]
  (O : ValuationSubring k) (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)

/-- **The tempered Galois correspondence for a finite étale level** `L_X ≤ L'`:
`γ ∈ Π^tp_X` comes from `Π^tp_{L'}` iff some lift `σ ∈ H_X = Gal(Ω/L_X)` of its image in
`Π_X` fixes `L'`. -/
theorem mem_range_muL_iff (γ : TempPi (fieldData ht LX hLX) O V hV) :
    γ ∈ (temperedPi1Map (muL ht hLX L' hL') V hV).range ↔
      ∃ σ : (fieldData ht LX hLX).H, (σ : Pi (fieldData ht LX hLX)) =
        tempToPi (fieldData ht LX hLX) O V hV γ ∧
        (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ L'.fixingSubgroup := by
  constructor
  · rintro ⟨γ', rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective
      (tempToPi (fieldData ht L' hL') O V hV γ')
    refine ⟨Subgroup.inclusion (fieldData_H_antitone ht hLX hL' hX.out) h, ?_, h.2⟩
    rw [tempToPi_temperedPi1Map ht hLX hL' hX.out O V hV, ← hh]
    rfl
  · rintro ⟨σ, hσ, hσL⟩
    rw [mem_range_temperedPi1Map]
    apply (etaleToTempFibreEquiv O (fieldData ht LX hLX).R (fieldData ht LX hLX).A V hV
      (coverEt (fieldData ht LX hLX).R (fieldData ht LX hLX).A (fieldData ht L' hL').R)).injective
    rw [fibreAct_eq_fibreSmul _ O V hV γ σ hσ]
    have hpt : etaleToTempFibreEquiv O (fieldData ht LX hLX).R (fieldData ht LX hLX).A V hV
        (coverEt (fieldData ht LX hLX).R (fieldData ht LX hLX).A (fieldData ht L' hL').R)
          (coverFibrePt V hV) =
        coverPt (fieldData ht LX hLX).R (fieldData ht LX hLX).A (fieldData ht L' hL').R Ω :=
      Equiv.apply_symm_apply _ _
    rw [hpt]
    refine AlgHom.ext fun b => ?_
    rw [GaloisData.fibreSmul_of_mem _ σ.2]
    exact (IntermediateField.mem_fixedField_iff _ _).1
      (CoordRing.algebraMap_mem (F := (fieldData ht L' hL').L) _) _ hσL

/-- **The tempered Galois correspondence, every lift**: `γ` comes from `Π^tp_{L'}` iff every
lift `σ ∈ H_X` of its image in `Π_X` fixes `L'` (the ambient kernel `⟨⟨S_X⟩⟩` fixes `L'`). -/
theorem mem_range_muL_iff_forall (γ : TempPi (fieldData ht LX hLX) O V hV) :
    γ ∈ (temperedPi1Map (muL ht hLX L' hL') V hV).range ↔
      ∀ σ : (fieldData ht LX hLX).H, (σ : Pi (fieldData ht LX hLX)) =
        tempToPi (fieldData ht LX hLX) O V hV γ →
        (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ L'.fixingSubgroup := by
  rw [mem_range_muL_iff]
  constructor
  · rintro ⟨σ₀, hσ₀, hσ₀L⟩ σ hσ
    have e : (σ₀ : Pi (fieldData ht LX hLX)) = (σ : Pi (fieldData ht LX hLX)) := hσ₀.trans hσ.symm
    rw [QuotientGroup.eq] at e
    have hker := ambientKernel_le_level ht hLX L' hL' hX.out het e
    have := mul_mem hσ₀L hker
    simpa using this
  · intro h
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (tempToPi (fieldData ht LX hLX) O V hV γ)
    exact ⟨σ, hσ, h σ hσ⟩

set_option synthInstance.maxHeartbeats 200000 in
-- `DivisionMonoid (Pi _)` is slow to synthesize
/-- **Normality**: if `Gal(Ω/L_X)` maps `L'` into itself (`L'/L_X` Galois), the image of
`Π^tp_{L'}` in `Π^tp_X` is normal. -/
theorem normal_range_muL (hstab : ∀ σ ∈ LX.fixingSubgroup, ∀ x ∈ L', σ x ∈ L') :
    (temperedPi1Map (muL ht hLX L' hL') V hV).range.Normal := by
  refine ⟨fun γ hγ δ => ?_⟩
  obtain ⟨σ, hσ, hσL⟩ := (mem_range_muL_iff ht hLX L' hL' O V hV γ).1 hγ
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (tempToPi (fieldData ht LX hLX) O V hV δ)
  refine (mem_range_muL_iff ht hLX L' hL' O V hV _).2 ⟨τ * σ * τ⁻¹, ?_, ?_⟩
  · rw [(tempToPi (fieldData ht LX hLX) O V hV).map_mul,
      (tempToPi (fieldData ht LX hLX) O V hV).map_mul,
      (tempToPi (fieldData ht LX hLX) O V hV).map_inv, ← hτ, ← hσ]
    rfl
  · rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hx' : ((τ⁻¹ : (fieldData ht LX hLX).H) : Ω ≃ₐ[K₀ k t] Ω) x ∈ L' :=
      hstab _ (τ⁻¹).2 x hx
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσL _ hx'
    change (τ : Ω ≃ₐ[K₀ k t] Ω) ((σ : Ω ≃ₐ[K₀ k t] Ω)
      (((τ⁻¹ : (fieldData ht LX hLX).H) : Ω ≃ₐ[K₀ k t] Ω) x)) = x
    rw [hfix]
    exact (τ : Ω ≃ₐ[K₀ k t] Ω).apply_symm_apply x

/-- **Galois elements and the image of a level**: `σ ∈ D_V` lies in the image of `Π^tp_{L'}`
iff it fixes `L'` (the converse of `galoisToTempered_level`). -/
theorem galoisToTempered_mem_range_muL_iff (σ : decompositionGroup (fieldData ht LX hLX).R V) :
    galoisToTempered O _ _ hV σ ∈ (temperedPi1Map (muL ht hLX L' hL') V hV).range ↔
      ∀ x ∈ L', (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x := by
  rw [mem_range_muL_iff_forall]
  constructor
  · intro h
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1
      (h (galoisToH (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω))
        (tempToPi_galoisToTempered _ O V hV σ).symm)
  · intro h τ hτ
    rw [tempToPi_galoisToTempered] at hτ
    have e := hτ.symm
    rw [QuotientGroup.eq] at e
    have hker := ambientKernel_le_level ht hLX L' hL' hX.out het e
    have hσL : ((galoisToH (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) :
        (fieldData ht LX hLX).H) : Ω ≃ₐ[K₀ k t] Ω) ∈ L'.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 h
    have := mul_mem hσL hker
    simpa using this

/-- **(G4a) from a Galois element**: if some `σ` in the decomposition group of `V` moves an
element of `L'`, then `Π^tp_Y ⊄ Π^tp_{L'}`. -/
theorem piY_not_le_range_muL (T : TemperedFundamentalGroups.TateObject.Data O
      (fieldData ht LX hLX).R)
    (σ : decompositionGroup (fieldData ht LX hLX).R V) {x : Ω} (hx : x ∈ L')
    (hσx : (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x ≠ x) :
    ¬ TateObject.piY (A := (fieldData ht LX hLX).A) T V hV ≤
      (temperedPi1Map (muL ht hLX L' hL') V hV).range := fun h =>
  hσx ((galoisToTempered_mem_range_muL_iff ht hLX L' hL' O V hV σ).1
    (h (galoisToTempered_mem_piY hV T σ)) x hx)

end Correspondence

section PiYddot

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsSepClosed Ω]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  (T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R)
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
  [hX : ∀ j, Fact (LX ≤ L j)]
  [het : ∀ j, Algebra.Etale (fieldData ht LX hLX).R (fieldData ht (L j) (hL j)).R]

omit [IsSepClosed Ω] in
/-- **`Π^tp_Ÿ` is normal in `Π^tp_X`** if `Gal(Ω/L_X)` maps `L 0` into itself
(`Π^tp_Y = ker χ_Y` is normal). -/
theorem normal_piYddotX (hstab : ∀ σ ∈ LX.fixingSubgroup, ∀ x ∈ L 0, σ x ∈ L 0) :
    (piYddotX V hV T hL).Normal := by
  haveI := normal_range_muL ht hLX (L 0) (hL 0) O V hV hstab
  exact Subgroup.normal_inf_normal _ _

end PiYddot

end Iut.EtaleTheta
