/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Env.ThetaConjTemp
import Iut.EtaleTheta.Env.ThetaConjModL
import Iut.EtaleTheta.TemperedLevelTrans

/-!
# The theta class mod `l` is invariant under `Π^tp_X̿`: obligation 13 (MR15, 13c(iii))

The tempered transport of the étale invariance `conjH1_kummerMap_of_pow`
(`Env/ThetaConjModL.lean`) to `Π^tp_Ÿ`, and the splitting cocycle `cX` of [EtTh] Prop. 2.2(ii)
(text l.2938–2945) for the étale theta system of the Tate curve, from MR14's tempered
translation formula (run 18, `TemperedLevelTrans.lean`, `of_mem_piXdd`; [EtTh] Prop. 1.5(iii)
mod `l`).

* `piRes_level_injective`: for an étale level `L_X ≤ L'`, `Π_{L'} → Π_X` is injective
  (`⟨⟨S_X⟩⟩ ⊆ ⟨⟨S_{L'}⟩⟩`, MR14 `ambientKernel_le_ambientKernel_level`); `piRes_conjPi`.
* `tempToPi_toLevel_conjSub`, **`conjH1Sub_resLevel`**: for `γ ∈ Π^tp_X` normalising `Π^tp_Ÿ`
  and a lift `σ ∈ H_X = Gal(Ω/L_X)` of its image in `Π_X` (with `σ⁻¹ H_j σ ⊆ H_j`), conjugation by
  `γ` on `H¹(Π^tp_Ÿ, μ_n)` (`conjH1Sub`) of the restriction of a class `x` of `Π_{L_j}` is the
  restriction of `conjH1 σ x` (`KummerConj.lean`).
* **`conjH1Sub_classAt_of_pow`**: if moreover `σ(L_j) ⊆ L_j` and `σ(η_j) = z^l·η_j` with
  `z ∈ L_j`, then `κ^tp_l(η_j)|_{Π^tp_Ÿ}` is `γ`-invariant (`z` is a unit: `z^l = σ(η_j)/η_j`).
* **`exists_cX_of_moves`** (generic): with C1, the transitions, the stability `σ(L_j) ⊆ L_j`,
  the translation formula at a level `j` with `l ∣ N_j` (every lift of every `γ` with
  `l ∣ χ(γ)` moves `η_j` by an `l`-th power), MR14's debt Z at `j = 0` (`PiYIndexTwoAt`,
  `[Π^tp_Y : Π^tp_Ÿ] ≤ 2`) and `g₁` with `χ(g₁) = 1` (13a), for odd `l` and a representative `r`
  of the theta class mod `l·N`: a splitting cocycle `cX : Π^tp_X̿ → μ_l` with `hcXr` exists.
  Both cases of the index are covered: `[Π^tp_Y : Π^tp_Ÿ] = 2` (`exists_cX_of_classInvariant`
  with `e ∈ Π^tp_Y ∖ Π^tp_Ÿ` and MR14's `piYddotX_index`) and `Π^tp_Y ⊆ Π^tp_Ÿ`
  (`exists_cX_of_invariant_ker`); the `lℤ`-direction is `g = g₁^l`.
* **`exists_thetaEnvU_rigidity_cX`** (concrete): `exists_thetaEnvU_rigidity` with `cX` produced
  instead of assumed, for the theta system of `exists_thetaRep_inputs`, under C1 (debt Z at
  `j = 0` from (Z_2) = `zM_zero`, `Π^tp_Y ≤ Π^tp_{K(E_{q²})}`; TFGD runs 2, 4, 6); 13a (`g₁`
  with `χ̂(g₁) = 1` for the normalised character `χ̂ = TateObject.charN`) from Theorem B.
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer
open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta.Env

/-! ### Injectivity of `Π_{L_j} → Π_X` for an étale level -/

section Inj

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (ht : Transcendental k t)
  [IsGalois (K₀ k t) Ω] [CharZero k]
  {LX : IntermediateField (K₀ k t) Ω} (hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
  (L' : IntermediateField (K₀ k t) Ω)
  (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))) [hX : Fact (LX ≤ L')]
  [het : Algebra.Etale (fieldData ht LX hLX).R (fieldData ht L' hL').R]

/-- **`Π_{L'} → Π_X` is injective for an étale level** `L_X ≤ L'`: `⟨⟨S_X⟩⟩ ⊆ ⟨⟨S_{L'}⟩⟩`
(`ambientKernel_le_ambientKernel_level`). -/
theorem piRes_level_injective :
    Function.Injective (piRes (fieldData_H_antitone ht hLX hL' hX.out)
      (fieldData_S_antitone ht hLX hL' hX.out)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [piRes, QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at hx
    rw [QuotientGroup.eq_one_iff]
    simp only [GaloisPi1.kernel, Subgroup.mem_subgroupOf] at hx ⊢
    exact ambientKernel_le_ambientKernel_level ht hLX L' hL' hX.out het hx

omit [IsGalois (K₀ k t) Ω] [CharZero k] het in
/-- `piRes` intertwines the conjugations by `σ ∈ H_X`. -/
theorem piRes_conjPi (σ : (fieldData ht LX hLX).H)
    (hH : ∀ h ∈ (fieldData ht L' hL').H,
      (σ : Ω ≃ₐ[K₀ k t] Ω)⁻¹ * h * σ ∈ (fieldData ht L' hL').H)
    (x : Pi (fieldData ht L' hL')) :
    piRes (fieldData_H_antitone ht hLX hL' hX.out) (fieldData_S_antitone ht hLX hL' hX.out)
        (conjPi hH hH x) =
      (σ : Pi (fieldData ht LX hLX))⁻¹ *
        piRes (fieldData_H_antitone ht hLX hL' hX.out) (fieldData_S_antitone ht hLX hL' hX.out) x *
          (σ : Pi (fieldData ht LX hLX)) := by
  induction x using QuotientGroup.induction_on with
  | H h => rfl

end Inj

/-! ### Conjugation of the tempered classes of a level -/

section Transport

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsSepClosed Ω]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  {T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R}
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  [hX : ∀ j, Fact (LX ≤ L j)]
  [het : ∀ j, Algebra.Etale (fieldData ht LX hLX).R (fieldData ht (L j) (hL j)).R]

set_option synthInstance.maxHeartbeats 200000 in
-- `DivisionMonoid (Pi _)` is slow to synthesize
omit [IsSepClosed Ω] in
/-- **Tempered conjugation at a level**: for `γ ∈ Π^tp_X` normalising `Π^tp_Ÿ` and a lift
`σ ∈ H_X` of its image in `Π_X` with `σ⁻¹ H_j σ ⊆ H_j`, the image of `γ⁻¹ h γ` in `Π_{L_j}` is
the conjugate by `σ` of the image of `h` (`piRes_level_injective`). -/
theorem tempToPi_toLevel_conjSub (hC1 : LevelsDominated V hV T hL) (j : ℕ)
    (γ : TempPi (fieldData ht LX hLX) O V hV)
    (hHn : ∀ h ∈ piYddotX V hV T hL, γ⁻¹ * h * γ ∈ piYddotX V hV T hL)
    (σ : (fieldData ht LX hLX).H)
    (hσ : (σ : Pi (fieldData ht LX hLX)) = tempToPi (fieldData ht LX hLX) O V hV γ)
    (hH : ∀ h ∈ (fieldData ht (L j) (hL j)).H,
      (σ : Ω ≃ₐ[K₀ k t] Ω)⁻¹ * h * σ ∈ (fieldData ht (L j) (hL j)).H)
    (h : piYddotX V hV T hL) :
    tempToPi (fieldData ht (L j) (hL j)) O V hV (toLevel hC1 j (conjSub _ γ hHn h)) =
      conjPi hH hH (tempToPi (fieldData ht (L j) (hL j)) O V hV (toLevel hC1 j h)) := by
  apply piRes_level_injective ht hLX (L j) (hL j)
  rw [piRes_conjPi, ← tempToPi_temperedPi1Map ht hLX (hL j) (hX j).out O V hV,
    ← tempToPi_temperedPi1Map ht hLX (hL j) (hX j).out O V hV, temperedPi1Map_toLevel,
    temperedPi1Map_toLevel, coe_conjSub, map_mul, map_mul, map_inv, hσ]

omit [IsSepClosed Ω] in
/-- **Conjugation of pulled-back classes**: `conjH1Sub γ` of the restriction to `Π^tp_Ÿ` of
(the tempered pull-back of) a class `x` of `Π_{L_j}` is the restriction of `conjH1 σ x`. -/
theorem conjH1Sub_resLevel (hC1 : LevelsDominated V hV T hL) (j n : ℕ) [NeZero n]
    (γ : TempPi (fieldData ht LX hLX) O V hV)
    (hHn : ∀ h ∈ piYddotX V hV T hL, γ⁻¹ * h * γ ∈ piYddotX V hV T hL)
    (σ : (fieldData ht LX hLX).H)
    (hσ : (σ : Pi (fieldData ht LX hLX)) = tempToPi (fieldData ht LX hLX) O V hV γ)
    (hH : ∀ h ∈ (fieldData ht (L j) (hL j)).H,
      (σ : Ω ≃ₐ[K₀ k t] Ω)⁻¹ * h * σ ∈ (fieldData ht (L j) (hL j)).H)
    (x : ContH1 (Pi (fieldData ht (L j) (hL j))) (Mu n Ω)) :
    conjH1Sub (piYddotX V hV T hL) γ hHn
        (resLevel hC1 j n (toTempMu (fieldData ht (L j) (hL j)) O V hV n x)) =
      resLevel hC1 j n (toTempMu (fieldData ht (L j) (hL j)) O V hV n (conjH1 hH hH n x)) := by
  induction x using ContH1.induction_on with
  | h c =>
    simp only [resLevel, conjH1Sub, conjH1, ContH1.map_mk]
    refine congrArg ContH1.mk (Subtype.ext (funext fun h => ?_))
    simp only [ContH1.cocyclesMap_apply, MonoidHom.id_apply]
    rw [tempToPi_toLevel_conjSub hC1 j γ hHn σ hσ hH h]
    change tempToPi (fieldData ht LX hLX) O V hV γ • _ = muConj (σ : Ω ≃ₐ[K₀ k t] Ω) n _
    rw [← hσ]
    rfl

end Transport

/-! ### Invariance of the theta class mod `l` and the splitting cocycle -/

section Invariance

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  {T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R}
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  [hX : ∀ j, Fact (LX ≤ L j)]
  [het : ∀ j, Algebra.Etale (fieldData ht LX hLX).R (fieldData ht (L j) (hL j)).R]

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] in
/-- `σ(L') ⊆ L'` gives `σ⁻¹ Gal(Ω/L') σ ⊆ Gal(Ω/L')`. -/
theorem conj_mem_fieldData_H {L' : IntermediateField (K₀ k t) Ω}
    {hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))} {σ : Ω ≃ₐ[K₀ k t] Ω}
    (hstab : ∀ x ∈ L', σ x ∈ L') :
    ∀ h ∈ (fieldData ht L' hL').H, σ⁻¹ * h * σ ∈ (fieldData ht L' hL').H := by
  intro h hh
  change h ∈ L'.fixingSubgroup at hh
  change _ ∈ L'.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff] at hh ⊢
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hh _ (hstab x hx), AlgEquiv.aut_inv]
  exact σ.symm_apply_apply x

/-- **Invariance of the theta class mod `l` at a level** (13c(iii)): for `γ ∈ Π^tp_X`
normalising `Π^tp_Ÿ` and a lift `σ ∈ H_X` of its image in `Π_X` with `σ(L_j) ⊆ L_j` and
`σ(η_j) = z^l·η_j`, `z ∈ L_j` ([EtTh] Prop. 1.5(iii) mod `l`), the class `κ^tp_l(η_j)|_{Π^tp_Ÿ}`
is invariant under conjugation by `γ`. (`z` is a unit of the level: `z^l = σ(η_j)/η_j`.) -/
theorem conjH1Sub_classAt_of_pow (η : ∀ j, units (fieldData ht (L j) (hL j)))
    (hC1 : LevelsDominated V hV T hL) (j l : ℕ) [NeZero l]
    (γ : TempPi (fieldData ht LX hLX) O V hV)
    (hHn : ∀ h ∈ piYddotX V hV T hL, γ⁻¹ * h * γ ∈ piYddotX V hV T hL)
    (σ : (fieldData ht LX hLX).H)
    (hσ : (σ : Pi (fieldData ht LX hLX)) = tempToPi (fieldData ht LX hLX) O V hV γ)
    (hstab : ∀ x ∈ L j, (σ : Ω ≃ₐ[K₀ k t] Ω) x ∈ L j) {z : Ω} (hz : z ∈ L j)
    (hη : (σ : Ω ≃ₐ[K₀ k t] Ω)
        ((((η j : (F (fieldData ht (L j) (hL j)))ˣ) : F (fieldData ht (L j) (hL j))) : Ω)) =
      z ^ l * ((((η j : (F (fieldData ht (L j) (hL j)))ˣ) : F (fieldData ht (L j) (hL j))) : Ω))) :
    conjH1Sub (piYddotX V hV T hL) γ hHn (classAt η hC1 j l) = classAt η hC1 j l := by
  have hH := conj_mem_fieldData_H (ht := ht) (hL' := hL j) hstab
  set v : Ω := (((η j : (F (fieldData ht (L j) (hL j)))ˣ) : F (fieldData ht (L j) (hL j))) : Ω)
    with hvdef
  have hv0 : v ≠ 0 := fun h0 =>
    (η j : (F (fieldData ht (L j) (hL j)))ˣ).ne_zero (Subtype.ext h0)
  have hvi : IsIntegral (A₀ k t) v := (CoordRing.isIntegral_coe_iff _).2 (η j).2.1
  have hvi' : IsIntegral (A₀ k t) v⁻¹ := by
    have h := (CoordRing.isIntegral_coe_iff _).2 (η j).2.2
    rwa [Units.val_inv_eq_inv_val, IntermediateField.coe_inv] at h
  have hσv0 : (σ : Ω ≃ₐ[K₀ k t] Ω) v ≠ 0 := (_root_.map_ne_zero _).2 hv0
  have hzl : z ^ l = (σ : Ω ≃ₐ[K₀ k t] Ω) v * v⁻¹ := by
    rw [hη]; field_simp
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne l), zero_mul] at hη
    exact hσv0 hη
  have hzl' : z⁻¹ ^ l = (σ : Ω ≃ₐ[K₀ k t] Ω) v⁻¹ * v := by
    rw [inv_pow, hzl, map_inv₀, mul_inv, inv_inv]
  have hzi : IsIntegral (A₀ k t) z :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne l))
      (by rw [hzl]; exact (isIntegral_aut _ hvi).mul hvi')
  have hzi' : IsIntegral (A₀ k t) z⁻¹ :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne l))
      (by rw [hzl']; exact (isIntegral_aut _ hvi').mul hvi)
  obtain ⟨zu, hzu⟩ := Iut.EtaleTheta.exists_unit_fieldData ht (L j) (hL j) hz hz0 hzi hzi'
  rw [classAt, kummerMapTempered, MonoidHom.comp_apply,
    conjH1Sub_resLevel hC1 j l γ hHn σ hσ hH]
  refine congrArg _ (congrArg _ (conjH1_kummerMap_of_pow hH hH l (η j) zu ?_))
  rw [← hvdef, hη]
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
    IntermediateField.coe_mul, IntermediateField.coe_pow, hzu]
  rfl

/-- **Obligation 13 from the tempered translation formula** ([EtTh] Prop. 2.2(ii), l.2938–2945,
with Prop. 1.5(iii) mod `l` on `lℤ`): for a theta system with C1, its transitions, the stability
`σ(L_j) ⊆ L_j` and the translation formula at a level `j` with `l ∣ N_j` (`hmove`: every lift
`σ ∈ H_X` of every `γ ∈ Π^tp_X` with `l ∣ χ(γ)` moves `η_j` by an `l`-th power; MR14 run 18),
MR14's debt Z at `j = 0` and `g₁` with `χ(g₁) = 1` (13a), for odd `l` and a representative `r`
of the theta class mod `l·N`: a splitting cocycle `cX : Π^tp_X̿ → μ_l` with `hcXr` exists.
The class `θ mod l` (`= classAt η j l`) is invariant under conjugation by every `γ` with
`l ∣ χ(γ)` (`conjH1Sub_classAt_of_pow`); `g = g₁^l`; if `Π^tp_Y ⊄ Π^tp_Ÿ`, any
`e ∈ Π^tp_Y ∖ Π^tp_Ÿ` has `e² ∈ Π^tp_Ÿ`, `Π^tp_Y = Π^tp_Ÿ ∪ Π^tp_Ÿ·e` (`piYddotX_index`) and
`exists_cX_of_classInvariant` applies, otherwise `exists_cX_of_invariant_ker`. -/
theorem exists_cX_of_moves {η : ∀ j, units (fieldData ht (L j) (hL j))}
    (hC1 : LevelsDominated V hV T hL) (htr : ThetaTransitions ht hL η)
    (hstab : ∀ j, ∀ σ ∈ LX.fixingSubgroup, ∀ x ∈ L j, σ x ∈ L j)
    {l : ℕ} [NeZero l] (hl : Odd l) {N : ℕ} [NeZero N] {j : ℕ} (hlj : l ∣ 2 * (j + 1))
    (hmove : ∀ (γ : TempPi (fieldData ht LX hLX) O V hV) (m : ℤ),
      Iut.EtaleTheta.TateObject.charN (A := (fieldData ht LX hLX).A) T V hV γ =
        Multiplicative.ofAdd ((l : ℤ) * m) →
      ∀ σ : (fieldData ht LX hLX).H,
        (σ : Pi (fieldData ht LX hLX)) = tempToPi (fieldData ht LX hLX) O V hV γ →
        ∃ z ∈ L j, (σ : Ω ≃ₐ[K₀ k t] Ω)
            ((((η j : (F (fieldData ht (L j) (hL j)))ˣ) : F (fieldData ht (L j) (hL j))) : Ω)) =
          z ^ l * ((((η j : (F (fieldData ht (L j) (hL j)))ˣ) :
            F (fieldData ht (L j) (hL j))) : Ω)))
    (hZ : PiYIndexTwoAt V hV T hL 0)
    {g₁ : TempPi (fieldData ht LX hLX) O V hV}
    (hg₁ : Iut.EtaleTheta.TateObject.charN (A := (fieldData ht LX hLX).A) T V hV g₁ =
      Multiplicative.ofAdd 1)
    (r : ContH1.cocycles (piYddotX V hV T hL) (Mu (l * N) Ω))
    (hr : ContH1.mk r = thetaClassTemp η hC1 (l * N)) :
    ∃ (cX : piXdd V hV T l → Mu l Ω)
      (_ : IsCocycle (actDD (augT (fieldData ht LX hLX) O V hV) (psiMu (k := k) (Ω := Ω) l)
        (piXdd V hV T l)) cX),
      ∀ (γ : piYddotX V hV T hL) (h : (γ : TempPi (fieldData ht LX hLX) O V hV) ∈ piXdd V hV T l),
        cX ⟨γ, h⟩ = Mu.transition (Dvd.intro N rfl : l ∣ l * N) (r γ) := by
  have hnorm : (piYddotX V hV T hL).Normal := normal_piYddotX T hL (hstab 0)
  have hHn : ∀ x ∈ piXdd V hV T l, ∀ h ∈ piYddotX V hV T hL,
      x * h * x⁻¹ ∈ piYddotX V hV T hL := fun x _ h hh => hnorm.conj_mem h hh x
  have hconj : ∀ γ : TempPi (fieldData ht LX hLX) O V hV, ∀ h ∈ piYddotX V hV T hL,
      γ⁻¹ * h * γ ∈ piYddotX V hV T hL := fun γ h hh => by
    simpa using hnorm.conj_mem h hh γ⁻¹
  have hcl : transTemp T hL (Dvd.intro N rfl : l ∣ l * N) (ContH1.mk r) = classAt η hC1 j l := by
    rw [hr, transTemp_thetaClassTemp hC1 htr, thetaClassTemp_eq hC1 htr l j hlj]
  have key : ∀ (γ : TempPi (fieldData ht LX hLX) O V hV) (m : ℤ),
      Iut.EtaleTheta.TateObject.charN (A := (fieldData ht LX hLX).A) T V hV γ =
        Multiplicative.ofAdd ((l : ℤ) * m) →
      conjH1Sub _ γ (hconj γ) (classAt η hC1 j l) = classAt η hC1 j l := by
    intro γ m hγ
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (tempToPi (fieldData ht LX hLX) O V hV γ)
    obtain ⟨z, hz, hzη⟩ := hmove γ m hγ σ hσ
    exact conjH1Sub_classAt_of_pow η hC1 j l γ (hconj γ) σ hσ (hstab j σ σ.2) hz hzη
  -- the `lℤ`-direction `g = g₁^l`
  have hg : Iut.EtaleTheta.TateObject.charN (A := (fieldData ht LX hLX).A) T V hV
      (g₁ ^ l) = Multiplicative.ofAdd (l : ℤ) := by
    rw [map_pow, hg₁, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]
  have hclg : conjH1Sub _ (g₁ ^ l) (hconj (g₁ ^ l))
      (transTemp T hL (Dvd.intro N rfl : l ∣ l * N) (ContH1.mk r)) =
      transTemp T hL (Dvd.intro N rfl : l ∣ l * N) (ContH1.mk r) := by
    rw [hcl]; exact key (g₁ ^ l) 1 (by rw [hg, mul_one])
  by_cases hex : ∃ e ∈ Iut.EtaleTheta.TateObject.piY (A := (fieldData ht LX hLX).A) T V hV,
      e ∉ piYddotX V hV T hL
  · -- `[Π^tp_Y : Π^tp_Ÿ] = 2`
    obtain ⟨e, heY, he⟩ := hex
    obtain ⟨he2, hidx⟩ := piYddotX_index hZ heY he
    have hχe : Iut.EtaleTheta.TateObject.charN (A := (fieldData ht LX hLX).A) T V hV
        e = Multiplicative.ofAdd ((l : ℤ) * 0) := by
      rw [mul_zero, ofAdd_zero]; exact (Iut.EtaleTheta.TateObject.charN_eq_one_iff _ _ _ _).2 heY
    refine exists_cX_of_classInvariant r hl hHn heY he he2 hidx hg (hconj e) (hconj (g₁ ^ l))
      ?_ hclg
    rw [hcl]; exact key e 0 hχe
  · -- `Π^tp_Y ⊆ Π^tp_Ÿ`
    simp only [not_exists, not_and, not_not] at hex
    have hgdd : g₁ ^ l ∈ piXdd V hV T l := by
      change _ ∈ Subgroup.zpowers _; rw [hg]; exact Subgroup.mem_zpowers _
    obtain ⟨mg, hmg⟩ := exists_hce_of_invariant r (g₁ ^ l) (hconj (g₁ ^ l))
      (hHn _ hgdd) hclg
    exact exists_cX_of_invariant_ker r hHn hex hg mg hmg

end Invariance

/-! ### The Tate curve: `cX` for the étale theta system -/

section Concrete

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)
set_option quotPrecheck false in
local notation "DXc" => fieldData (transcendental_tau t.tateCurve) (hemiData t.tateCurve).L
  (hemiL_open t)

variable [t.tateCurve.IsElliptic] (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ}
  (hs : s ^ 2 = t.q) (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)

set_option maxHeartbeats 1000000 in
-- unifying with `exists_thetaRep_inputs` (concrete Tate-curve levels) is slow
variable [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [PerfectField (IsLocalRing.ResidueField O)] in
include h2 in
/-- **[EtTh] §2 for `X̲`, with the splitting cocycle constructed** (obligation 13 discharged
modulo C1): `exists_thetaEnvU_rigidity` with `∃ cX` in place of `∀ cX`.
For the theta system of `exists_thetaRep_inputs`, `O` a complete discrete valuation ring of mixed
characteristic `(0, p)` with perfect residue field, every base point `V` over `O`, under C1
(debt Z at `j = 0`, `[Π^tp_Y : Π^tp_Ÿ] ≤ 2`, is discharged by (Z_2) = `zM_zero`,
`Π^tp_Y ≤ Π^tp_{K(E_{q²})}`), every odd `l`, every `N ≥ 1` and every
representative `r` of the theta class mod `lN` on `Π^tp_Ÿ`, there is a splitting cocycle
`cX : Π^tp_X̿ → μ_l` with `hcXr` (`exists_cX_of_moves`, at the level `j = 2l − 1`), and
`EnvUConclusions` hold for the curve `X̲` it defines. Debt 13a is discharged (TFGD run 2):
`Π^tp_X̿ = χ̂⁻¹(lℤ)` for the normalised character `χ̂` (`TateObject.charN`), and `g₁` with
`χ̂(g₁) = 1` comes from Theorem B (`exists_charN_eq_one_tateDataX`). C1 holds for the system
(second conjunct; TFGD run 8: (Z_{N_j}) for all `j`, `zM`). -/
theorem exists_thetaEnvU_rigidity_cX (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) :
    ∃ (L : ℕ → IntermediateField (K₀ K τ) Ω)
      (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
      (_ : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j))
      (_ : ∀ j, Algebra.Etale (Iut.EtaleTheta.DX t).R
        (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R)
      (η : ∀ j, units (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))),
      ThetaTransitions (transcendental_tau t.tateCurve) hL η ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O),
        LevelsDominated V hV (tateDataX O hO hs h12) hL) ∧
      ∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
        (hC1 : LevelsDominated V hV (tateDataX O hO hs h12) hL),
        ∀ (l N : ℕ) [NeZero l] [NeZero N], Odd l →
        ∀ (r : ContH1.cocycles (piYddotX V hV (tateDataX O hO hs h12) hL) (Mu (l * N) Ω)),
        ContH1.mk r = thetaClassTemp η hC1 (l * N) →
        ∃ (cX : piXdd V hV (tateDataX O hO hs h12) l → Mu l Ω)
          (hcX : IsCocycle (actDD (augT DXc O V hV) (psiMu l)
            (piXdd V hV (tateDataX O hO hs h12) l)) cX)
          (hcXr : ∀ (γ : piYddotX V hV (tateDataX O hO hs h12) hL)
            (h : (γ : TempPi DXc O V hV) ∈ piXdd V hV (tateDataX O hO hs h12) l),
            cX ⟨γ, h⟩ = Mu.transition (Dvd.intro N rfl : l ∣ l * N) (r γ)),
          EnvUConclusions hcX r hcXr (thetaClassTemp η hC1 N)
            (∃ (W : ValuationSubring Ω) (_ : ∀ c : K, algebraMap K Ω c ∈ W), τ ∉ W ∧ V ≤ W ∧
              CuspInertiaWeil (DXc)) := by
  refine (exists_thetaRep_inputs h2 h12 hs O hO).imp fun L => Exists.imp fun hL =>
    Exists.imp fun hX => Exists.imp fun het => Exists.imp fun η h =>
      ⟨h.1, h.2.2.2.2.1, fun V hV hC1 l N _ _ hl r hr => ?_⟩
  obtain ⟨hZ, hmv⟩ := h.2.2.1 V hV
  obtain ⟨g₁, hg₁⟩ := exists_charN_eq_one_tateDataX h12 O hO hs p hp hpm V hV
  have hlj : 2 * l ∣ 2 * (2 * l - 1 + 1) := by
    rw [Nat.sub_add_cancel (by have := NeZero.ne l; omega)]
    exact Dvd.intro_left 2 rfl
  obtain ⟨cX, hcX, hcXr⟩ := exists_cX_of_moves hC1 h.1 h.2.1 hl
    ((Dvd.intro_left 2 rfl).trans hlj)
    (fun γ m hγ σ hσ => by
      obtain ⟨d, y, hy, e⟩ := hmv (2 * l - 1) l hl hlj hC1 g₁ hg₁ γ m hγ σ hσ
      refine ⟨algebraMap K Ω d * y, mul_mem ?_ hy, e⟩
      rw [IsScalarTower.algebraMap_apply K (K₀ K τ) Ω]
      exact (L (2 * l - 1)).algebraMap_mem _)
    hZ hg₁ r hr
  obtain ⟨hr13, hrL⟩ := h.2.2.2.2.2 V hV hC1 (l * N) r hr
  exact ⟨cX, hcX, hcXr, envUConclusions_of hcX r hcXr
    ((congrArg (transTemp (tateDataX O hO hs h12) hL (Dvd.intro_left l rfl : N ∣ l * N)) hr).trans
      ((h.2.2.2.1 V hV hC1).2 N (l * N) (Dvd.intro_left l rfl)))
    hr13 (fun ⟨W, hk, hτ, hVW, _⟩ => surj_augT_of_ratPoint (tateDataX O hO hs h12)
      (cuspRatPoint hk hτ) hVW) fun ⟨W, hk, hτ, hVW, hG5⟩ => hrL W hk hτ hVW hG5⟩

end Concrete

end Iut.EtaleTheta.Env
