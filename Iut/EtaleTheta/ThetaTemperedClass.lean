/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaTempered
import Iut.EtaleTheta.TemperedCovering

/-!
# The étale theta class on `Π^tp_Ÿ` as a compatible system (MR14, run 7)

Let `q` be a Tate parameter over a complete nonarchimedean field `K` of characteristic `0` with
`‖2‖ = 1`, `s² = q`, `X = E_q ∖ {O}`, `Ω = K(Ē)^alg`, `O ⊆ K` the unit ball, `V ⊆ Ω` a valuation
subring over `O`. `exists_etaleThetaSystem` gives the levels `Ÿ'_{N_j}` (`N_j = 2(j+1)`; function
fields `L j ⊆ Ω`, étale over `X`) with the theta level units `η_j` (the Kummer classes of their
values are those of `Θ̈`, [EtTh] Prop. 1.4(iii)) forming a projective system. This file turns them
into **one class on the tempered fundamental group of `Ÿ`**.

* Generic part (any Galois data `fieldData L_X` of a curve `X` with Tate data `T` of
  `tempered-fundamental-groups`, and levels `L j ⊇ L_X`, étale and finite over `X`):
  - `piYddotX T (L 0)`: **`Π^tp_Ÿ := Π^tp_Y ∩ Π^tp_{Ÿ'_2} ⊆ Π^tp_X`**, `Π^tp_Y = TateObject.piY T`
    (the stabilizer of a point of the fibre of `Y ×_X Ÿ'_2`; `Ÿ` is the component through the base
    point, [EtTh] §1: `Ü² = U`, `Ÿ'_2 = E_q` in the coordinate `Ü`);
  - **hypothesis C1** `LevelsDominated`: `Π^tp_Ÿ ≤ Π^tp_{Ÿ'_{N_j}}` for all `j` (a debt of
    `MR14-plan.md`: `Ÿ'_{N_j} → Ÿ'_2` is a quotient of the `ℤ`-covering `Ÿ → Ÿ'_2`; it needs
    `2N`-gon Tate models in `tempered-fundamental-groups`);
  - `toLevel j : Π^tp_Ÿ → Π^tp_{Ÿ'_{N_j}}`, `classAt η j n` (the restriction of the tempered Kummer
    class `κ^tp_n(η_j)`), **`thetaClassTemp η n ∈ H¹(Π^tp_Ÿ, μ_n)`**;
  - `classAt_eq_of_res`, **`thetaClassTemp_eq`**: independence of the level (from the tempered
    naturality of `ThetaTempered.lean`); **`transTemp_thetaClassTemp`**: compatibility in `n`
    (`μ_m → μ_n`), so `(thetaClassTemp η n)_n ∈ lim_n H¹(Π^tp_Ÿ, μ_n)`
    (`Δ_Θ ⊗ ℤ/n ≅ μ_n`, [EtTh] Prop. 1.3).
* Concrete part: the coordinates `xX`, `yX` of `X` and **the Tate data `tateDataX` of `E_q`**
  (`π = s`); **`exists_thetaClassTemp`**: the system of `exists_etaleThetaSystem` with its class.
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer
open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta

/-! ### Generic part: levels over a curve `X` with Tate data -/

section Transport

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω)

theorem etale_ringMap_of_eq {M₁ M₂ L₁ L₂ : IntermediateField (K₀ k t) Ω} (e₁ : M₁ = L₁)
    (e₂ : M₂ = L₂) (h : L₁ ≤ L₂) (h' : M₁ ≤ M₂) (H : (ringMap t h).toRingHom.Etale) :
    (ringMap t h').toRingHom.Etale := by
  subst e₁ e₂
  exact H

/-- The inclusion of coordinate rings for `L₁ ≤ L₂`. -/
def coordRingCast {L₁ L₂ : IntermediateField (K₀ k t) Ω} (h : L₁ ≤ L₂) :
    CoordRing k t L₁ →+* CoordRing k t L₂ :=
  (ringMap t h).toRingHom

theorem algebraMap_coordRingCast {L₁ L₂ : IntermediateField (K₀ k t) Ω} (h : L₁ ≤ L₂)
    (x : CoordRing k t L₁) :
    algebraMap (CoordRing k t L₂) Ω (coordRingCast t h x) = algebraMap (CoordRing k t L₁) Ω x :=
  rfl

end Transport

section Levels

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (ht : Transcendental k t)
  {LX : IntermediateField (K₀ k t) Ω} (hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
  (L' : IntermediateField (K₀ k t) Ω)
  (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))) [hX : Fact (LX ≤ L')]

instance algXL : Algebra (fieldData ht LX hLX).R (fieldData ht L' hL').R :=
  levelAlgebra ht hLX hL' hX.out

instance : IsScalarTower k (fieldData ht LX hLX).R (fieldData ht L' hL').R :=
  IsScalarTower.of_algebraMap_eq fun _ => CoordRing.ext rfl

instance : IsScalarTower (fieldData ht LX hLX).R (fieldData ht L' hL').R Ω :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance [IsGalois (K₀ k t) Ω] [CharZero k] :
    Module.Finite (fieldData ht LX hLX).R (fieldData ht L' hL').R :=
  module_finite_of_charZero ht (fieldData_L_le ht hLX hL' hX.out)

/-- Étaleness of `Spec R' → X` from the étaleness of `coordRing L_X → coordRing L'`. -/
theorem etale_fieldData [IsGalois (K₀ k t) Ω] (H : (ringMap t hX.out).toRingHom.Etale) :
    Algebra.Etale (fieldData ht LX hLX).R (fieldData ht L' hL').R :=
  etale_ringMap_of_eq t (fieldData_L ht LX hLX) (fieldData_L ht L' hL') hX.out _ H

/-- The map of orbifolds `Spec R' → X`. -/
abbrev muL : OrbMap (fieldData ht LX hLX).R (fieldData ht LX hLX).A (fieldData ht L' hL').R
    (fieldData ht L' hL').A :=
  levelOrbMap ht hLX hL'

omit hX in
theorem orbMap_ext [Algebra (fieldData ht LX hLX).R (fieldData ht L' hL').R]
    {μ₁ μ₂ : OrbMap (fieldData ht LX hLX).R (fieldData ht LX hLX).A (fieldData ht L' hL').R
      (fieldData ht L' hL').A} (h : μ₁.α = μ₂.α) : μ₁ = μ₂ := by
  cases μ₁
  cases μ₂
  cases h
  rfl

/-- The transition property of a system of theta levels (`exists_etaleThetaSystem`). -/
abbrev ThetaTransitions [IsGalois (K₀ k t) Ω] [CharZero k] [IsSepClosed Ω]
    {L : ℕ → IntermediateField (K₀ k t) Ω}
    (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
    (η : ∀ j, units (fieldData ht (L j) (hL j))) : Prop :=
  ∀ j j' M : ℕ, 2 * (j' + 1) = 2 * (j + 1) * M → Even M →
    LevelTransition ht (hL j) (hL j') (η j) (η j') (2 * (j + 1))

end Levels

/-! ### `Π^tp_Ÿ` and the étale theta class on it (generic) -/

section Class

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsSepClosed Ω]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  (T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R)
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
  [hX : ∀ j, Fact (LX ≤ L j)]
  [het : ∀ j, Algebra.Etale (fieldData ht LX hLX).R (fieldData ht (L j) (hL j)).R]

variable (V hV) in
/-- **`Π^tp_Ÿ ⊆ Π^tp_X`**: the stabilizer of a point of the fibre of `Y ×_X Ÿ'_2`, i.e.
`Π^tp_Y ∩ Π^tp_{Ÿ'_2}` (`Y → X` the `ℤ`-covering of the special fibre of the Tate model of `T`,
`TateObject.piY`; `Ÿ` is the component of `Y ×_X Ÿ'_2` through the base point: [EtTh] §1,
`Ü² = U`, `Ÿ'_2 = E_q` in the coordinate `Ü`). -/
def piYddotX : Subgroup (TempPi (fieldData ht LX hLX) O V hV) :=
  TateObject.piY (A := (fieldData ht LX hLX).A) T V hV ⊓
    (temperedPi1Map (muL ht hLX (L 0) (hL 0)) V hV).range

variable (V hV) in
/-- **Hypothesis C1** (`MR14-plan.md`, debt): `Ÿ` dominates every level,
`Π^tp_Ÿ ≤ Π^tp_{Ÿ'_{N_j}}`. -/
abbrev LevelsDominated : Prop :=
  ∀ j, piYddotX V hV T hL ≤ (temperedPi1Map (muL ht hLX (L j) (hL j)) V hV).range

variable {T hL}

/-- `Π^tp_Ÿ → Π^tp_{Ÿ'_{N_j}}` under C1 (the inverse of the open embedding on its image). -/
def toLevel (hC1 : LevelsDominated V hV T hL) (j : ℕ) :
    piYddotX V hV T hL →* TempPi (fieldData ht (L j) (hL j)) O V hV :=
  (MonoidHom.ofInjective
      (temperedPi1Map_injective V hV (muL ht hLX (L j) (hL j)))).symm.toMonoidHom.comp
    (Subgroup.inclusion (hC1 j))

omit [IsSepClosed Ω] in
theorem temperedPi1Map_toLevel (hC1 : LevelsDominated V hV T hL) (j : ℕ)
    (γ : piYddotX V hV T hL) :
    temperedPi1Map (muL ht hLX (L j) (hL j)) V hV (toLevel hC1 j γ) = γ :=
  MonoidHom.apply_ofInjective_symm (temperedPi1Map_injective V hV _) _

omit [IsSepClosed Ω] in
theorem continuous_toLevel (hC1 : LevelsDominated V hV T hL) (j : ℕ) :
    Continuous (toLevel hC1 j) := by
  rw [(isOpenEmbedding_temperedPi1Map (O := O) V hV
    (muL ht hLX (L j) (hL j))).isEmbedding.continuous_iff]
  have : temperedPi1Map (muL ht hLX (L j) (hL j)) V hV ∘ toLevel hC1 j = Subtype.val :=
    funext (temperedPi1Map_toLevel hC1 j)
  rw [this]
  exact continuous_subtype_val

omit [IsSepClosed Ω] in
theorem toLevel_smul (hC1 : LevelsDominated V hV T hL) (j n : ℕ) [NeZero n]
    (γ : piYddotX V hV T hL) (x : Mu n Ω) :
    MonoidHom.id (Mu n Ω) (toLevel hC1 j γ • x) = γ • MonoidHom.id (Mu n Ω) x := by
  change _ = tempToPi (fieldData ht LX hLX) O V hV
    (γ : TempPi (fieldData ht LX hLX) O V hV) • x
  conv_rhs => rw [← temperedPi1Map_toLevel hC1 j γ]
  exact (tempToPi_smul_level ht hLX (hL j) (hX j).out O V hV n _ x).symm

/-- The pull-back `H¹(Π^tp_{Ÿ'_{N_j}}, μ_n) → H¹(Π^tp_Ÿ, μ_n)`. -/
def resLevel (hC1 : LevelsDominated V hV T hL) (j n : ℕ) [NeZero n] :
    ContH1 (TempPi (fieldData ht (L j) (hL j)) O V hV) (Mu n Ω) →*
      ContH1 (piYddotX V hV T hL) (Mu n Ω) :=
  ContH1.map (toLevel hC1 j) (continuous_toLevel hC1 j) (MonoidHom.id _) continuous_id
    (toLevel_smul hC1 j n)

variable (η : ∀ j, units (fieldData ht (L j) (hL j)))

/-- The class `κ^tp_n(η_j)|_{Π^tp_Ÿ}` at the level `j`. -/
def classAt (hC1 : LevelsDominated V hV T hL) (j n : ℕ) [NeZero n] :
    ContH1 (piYddotX V hV T hL) (Mu n Ω) :=
  resLevel hC1 j n (kummerMapTempered (fieldData ht (L j) (hL j)) O V hV n (η j))

/-- **Independence of the level**: if `L j ≤ L j'` and `κ_n(η_j)` restricts to `κ_n(η_{j'})`,
the two classes on `Π^tp_Ÿ` agree. -/
theorem classAt_eq_of_res (hC1 : LevelsDominated V hV T hL) (n : ℕ) [NeZero n]
    {j j' : ℕ} (hle : L j ≤ L j')
    (hres : resPi (fieldData_H_antitone ht (hL j) (hL j') hle)
      (fieldData_S_antitone ht (hL j) (hL j') hle) n
      (kummerMap (fieldData ht (L j) (hL j)) n (η j)) =
        kummerMap (fieldData ht (L j') (hL j')) n (η j')) :
    classAt η hC1 j n = classAt η hC1 j' n := by
  letI : Algebra (fieldData ht (L j) (hL j)).R (fieldData ht (L j') (hL j')).R :=
    levelAlgebra ht (hL j) (hL j') hle
  haveI : IsScalarTower k (fieldData ht (L j) (hL j)).R (fieldData ht (L j') (hL j')).R :=
    IsScalarTower.of_algebraMap_eq fun _ => CoordRing.ext rfl
  haveI : IsScalarTower (fieldData ht (L j) (hL j)).R (fieldData ht (L j') (hL j')).R Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (fieldData ht LX hLX).R (fieldData ht (L j) (hL j)).R
      (fieldData ht (L j') (hL j')).R :=
    IsScalarTower.of_algebraMap_eq fun _ => CoordRing.ext rfl
  set μ := levelOrbMap ht (hL j) (hL j')
  have hμ : (muL ht hLX (L j) (hL j)).comp μ = muL ht hLX (L j') (hL j') :=
    orbMap_ext ht hLX (L j') (hL j') (MonoidHom.one_comp _)
  have hcomp : ∀ γ, temperedPi1Map μ V hV (toLevel hC1 j' γ) = toLevel hC1 j γ := by
    intro γ
    apply temperedPi1Map_injective V hV (muL ht hLX (L j) (hL j))
    rw [← temperedPi1Map_comp, hμ, temperedPi1Map_toLevel, temperedPi1Map_toLevel]
  rw [classAt, classAt, kummerMapTempered, kummerMapTempered, MonoidHom.comp_apply,
    MonoidHom.comp_apply, ← hres, ← map_toTempMu_level ht (hL j) (hL j') hle O V hV n]
  induction kummerMap (fieldData ht (L j) (hL j)) n (η j) using ContH1.induction_on with
  | h c =>
    simp only [resLevel, ContH1.map_mk]
    refine congrArg ContH1.mk (Subtype.ext (funext fun γ => ?_))
    simp only [ContH1.cocyclesMap_apply, MonoidHom.id_apply]
    rw [hcomp]

/-- **The étale theta class mod `n` on `Π^tp_Ÿ`**: `κ^tp_n(η_j)|_{Π^tp_Ÿ}` at the level
`N_j = 2n` (`j = n - 1`); by `thetaClassTemp_eq` every level with `n ∣ N_j` gives the same
class. -/
def thetaClassTemp (hC1 : LevelsDominated V hV T hL) (n : ℕ) [NeZero n] :
    ContH1 (piYddotX V hV T hL) (Mu n Ω) :=
  classAt η hC1 (n - 1) n

variable {η}

/-- **The étale theta classes form a compatible system in the level**: for every level `j` with
`n ∣ N_j`, `κ^tp_n(η_j)` restricted to `Π^tp_Ÿ` is the theta class mod `n`. -/
theorem thetaClassTemp_eq (hC1 : LevelsDominated V hV T hL) (htr : ThetaTransitions ht hL η)
    (n : ℕ) [NeZero n] (j : ℕ) (hn : n ∣ 2 * (j + 1)) :
    thetaClassTemp η hC1 n = classAt η hC1 j n := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have ha : n - 1 + 1 = n := Nat.sub_add_cancel hn0
  have hj'' : 4 * n * (j + 1) - 1 + 1 = 4 * n * (j + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.mul_pos (by norm_num) hn0) (Nat.succ_pos j))
  have e1 : classAt η hC1 (n - 1) n = classAt η hC1 (4 * n * (j + 1) - 1) n := by
    obtain ⟨hle, h⟩ := htr (n - 1) (4 * n * (j + 1) - 1) (4 * (j + 1))
      (by rw [hj'', ha]; ring) ⟨2 * (j + 1), by ring⟩
    exact classAt_eq_of_res η hC1 n hle (h n (by rw [ha]; exact Dvd.intro_left 2 rfl))
  have e2 : classAt η hC1 j n = classAt η hC1 (4 * n * (j + 1) - 1) n := by
    obtain ⟨hle, h⟩ := htr j (4 * n * (j + 1) - 1) (4 * n) (by rw [hj'']; ring)
      ⟨2 * n, by ring⟩
    exact classAt_eq_of_res η hC1 n hle (h n hn)
  rw [thetaClassTemp, e1, e2]

/-! ### Compatibility in `n` -/

variable (T hL) in
/-- The transition `H¹(Π^tp_Ÿ, μ_m) → H¹(Π^tp_Ÿ, μ_n)` for `n ∣ m` (`ζ ↦ ζ^{m/n}`). -/
def transTemp {n m : ℕ} (h : n ∣ m) [NeZero n] [NeZero m] :
    ContH1 (piYddotX V hV T hL) (Mu m Ω) →* ContH1 (piYddotX V hV T hL) (Mu n Ω) :=
  ContH1.map (MonoidHom.id _) continuous_id (Mu.transition h) continuous_of_discreteTopology
    (fun γ ζ => by
      change Mu.transition h (tempToPi (fieldData ht LX hLX) O V hV
          (γ : TempPi (fieldData ht LX hLX) O V hV) • ζ) =
        tempToPi (fieldData ht LX hLX) O V hV (γ : TempPi (fieldData ht LX hLX) O V hV) •
          Mu.transition h ζ
      induction tempToPi (fieldData ht LX hLX) O V hV
          (γ : TempPi (fieldData ht LX hLX) O V hV) using QuotientGroup.induction_on with
      | H g => exact Mu.transition_smul (K := K₀ k t) h (g : Ω ≃ₐ[K₀ k t] Ω) ζ)

/-- On `Π_U`, the transitions map Kummer classes to Kummer classes. -/
theorem transition_kummerMap (D : GaloisData k t) {n m : ℕ} (h : n ∣ m)
    [NeZero n] [NeZero m] (u : units D) :
    ContH1.map (MonoidHom.id (Pi D)) continuous_id (Mu.transition h)
        continuous_of_discreteTopology
        (fun g ζ => by
          induction g using QuotientGroup.induction_on with
          | H g => exact Mu.transition_smul (K := K₀ k t) h (g : Ω ≃ₐ[K₀ k t] Ω) ζ)
        (kummerMap D m u) = kummerMap D n u := by
  have hm : ((m : ℕ) : F D) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have hn : ((n : ℕ) : F D) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  rw [← map_proj_kummerMapZHat (D := D) ⟨m, hm⟩ u, ← map_proj_kummerMapZHat (D := D) ⟨n, hn⟩ u]
  induction kummerMapZHat D u using ContH1.induction_on with
  | h c =>
    simp only [ContH1.map_mk]
    refine congrArg ContH1.mk (Subtype.ext (funext fun g => ?_))
    simp only [ContH1.cocyclesMap_apply, MonoidHom.id_apply]
    exact ZHatOne.transition_proj (i := ⟨n, hn⟩) (j := ⟨m, hm⟩) h _

theorem transTemp_classAt (hC1 : LevelsDominated V hV T hL) (j : ℕ) {n m : ℕ} (h : n ∣ m)
    [NeZero n] [NeZero m] :
    transTemp T hL h (classAt η hC1 j m) = classAt η hC1 j n := by
  simp only [classAt, kummerMapTempered, MonoidHom.comp_apply]
  rw [← transition_kummerMap (fieldData ht (L j) (hL j)) h (η j)]
  generalize kummerMap (fieldData ht (L j) (hL j)) m (η j) = x
  induction x using ContH1.induction_on with
  | h c =>
    simp only [transTemp, resLevel, ContH1.map_mk]
    refine congrArg ContH1.mk (Subtype.ext (funext fun γ => ?_))
    simp only [ContH1.cocyclesMap_apply, MonoidHom.id_apply]

/-- **Compatibility in `n`**: the theta classes mod `m` and mod `n ∣ m` correspond under
`μ_m → μ_n`; so `(thetaClassTemp η n)_n` is an element of `lim_n H¹(Π^tp_Ÿ, μ_n)`. -/
theorem transTemp_thetaClassTemp (hC1 : LevelsDominated V hV T hL)
    (htr : ThetaTransitions ht hL η) {n m : ℕ} (h : n ∣ m) [NeZero n] [NeZero m] :
    transTemp T hL h (thetaClassTemp η hC1 m) = thetaClassTemp η hC1 n := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hdm : m ∣ 2 * (m - 1 + 1) := by rw [Nat.sub_add_cancel hm0]; exact Dvd.intro_left 2 rfl
  rw [thetaClassTemp_eq hC1 htr m (m - 1) hdm, thetaClassTemp_eq hC1 htr n (m - 1) (h.trans hdm)]
  exact transTemp_classAt hC1 (m - 1) h

variable (V hV T η) in
/-- **The compatible system** (a `Prop` def used only as a conclusion, like
`EtaleThetaAtPoint`): under C1, the classes `thetaClassTemp η n` are independent of the level and
compatible in `n`. -/
def ThetaClassCompatible : Prop :=
  ∀ hC1 : LevelsDominated V hV T hL,
    (∀ (n : ℕ) [NeZero n] (j : ℕ), n ∣ 2 * (j + 1) →
      thetaClassTemp η hC1 n = classAt η hC1 j n) ∧
    ∀ (n m : ℕ) [NeZero n] [NeZero m] (h : n ∣ m),
      transTemp T hL h (thetaClassTemp η hC1 m) = thetaClassTemp η hC1 n

theorem thetaClassCompatible (htr : ThetaTransitions ht hL η) :
    ThetaClassCompatible V hV T η := fun hC1 =>
  ⟨fun n _ j hn => thetaClassTemp_eq hC1 htr n j hn,
    fun _ _ _ _ h => transTemp_thetaClassTemp hC1 htr h⟩

end Class

/-! ### The concrete base `X = E_q ∖ {O}` and its Tate data -/

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

section Base

variable (t) [t.tateCurve.IsElliptic]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem hemiL_open :
    IsOpen ((hemiData t.tateCurve).L.fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)) := by
  rw [GaloisData.fixingSubgroup_L]
  exact (hemiData t.tateCurve).isOpen_HL

/-- The Galois data of `X = E_q ∖ {O}` (no orbifold structure). -/
abbrev DX : GaloisData K τ :=
  fieldData (transcendental_tau t.tateCurve) (hemiData t.tateCurve).L (hemiL_open t)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem hemiL_le_DX : (hemiData t.tateCurve).L ≤ (DX t).L :=
  (fieldData_L (transcendental_tau t.tateCurve) (hemiData t.tateCurve).L (hemiL_open t)).symm.le

/-- The coordinate `x` on `X`. -/
def xX : (DX t).R :=
  coordRingCast τ (hemiL_le_DX t)
    (hemiREquiv t.tateCurve (AdjoinRoot.of t.tateCurve.toAffine.polynomial X))

/-- The coordinate `y` on `X`. -/
def yX : (DX t).R :=
  coordRingCast τ (hemiL_le_DX t)
    (hemiREquiv t.tateCurve (AdjoinRoot.root t.tateCurve.toAffine.polynomial))

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem algebraMap_xX : algebraMap (DX t).R Ω (xX t) = τ :=
  hemiRho_of_X t.tateCurve

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem algebraMap_yX :
    algebraMap (DX t).R Ω (yX t) = hemiRho t.tateCurve
      (AdjoinRoot.root t.tateCurve.toAffine.polynomial) :=
  rfl

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The Weierstrass equation of `E_q` on `X`. -/
theorem yX_equation : yX t ^ 2 + xX t * yX t =
    xX t ^ 3 + algebraMap K (DX t).R t.a₄ * xX t + algebraMap K (DX t).R t.a₆ := by
  apply CoordRing.algebraMap_injective
  simp only [map_add, map_mul, map_pow, algebraMap_xX, algebraMap_yX,
    ← IsScalarTower.algebraMap_apply K (DX t).R Ω]
  have h := hemiRho_root_eq t.tateCurve
  rw [hemiRho_of, hemiRho_of] at h
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, tateCurve_a₁, tateCurve_a₂,
    tateCurve_a₃, tateCurve_a₄, tateCurve_a₆, map_one, map_zero, one_mul, zero_mul,
    add_zero] at h
  linear_combination h

variable {t} (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) {s : Kˣ}
  (hs : s ^ 2 = t.q)

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] [t.tateCurve.IsElliptic] in
include hs in
theorem norm_sq_s : ‖(s : K)‖ ^ 2 = ‖(t.q : K)‖ := by
  rw [← norm_pow, ← hs, Units.val_pow_eq_pow_val]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] [t.tateCurve.IsElliptic] in
include hs in
theorem norm_s_lt_one : ‖(s : K)‖ < 1 := by
  have h := norm_sq_s hs
  have h1 := t.norm_lt_one
  nlinarith [norm_nonneg (s : K)]

omit [CharZero K] [t.tateCurve.IsElliptic] in
theorem norm_a₆_le (h12 : (12 : K) ≠ 0) : ‖t.a₆‖ ≤ ‖(t.q : K)‖ := by
  have hq1 := t.norm_lt_one
  calc ‖t.a₆‖ = ‖(t.a₆ + t.q) + (-(t.q : K))‖ := by ring_nf
    _ ≤ max ‖t.a₆ + t.q‖ ‖-(t.q : K)‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ ‖(t.q : K)‖ := by
      rw [norm_neg]
      refine max_le ((t.norm_a₆_add_q_le h12).trans ?_) le_rfl
      nlinarith [norm_nonneg (t.q : K)]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] [t.tateCurve.IsElliptic] in
include hO hs in
theorem mem_O_div {a : K} (ha : ‖a‖ ≤ ‖(t.q : K)‖) : a / ((s : K) ^ 2) ∈ O := by
  rw [hO, norm_div, norm_pow, norm_sq_s hs]
  rcases eq_or_ne ‖(t.q : K)‖ 0 with h | h
  · rw [h, div_zero]; exact zero_le_one
  · exact (div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))).2 ha

/-- **The Tate data of `E_q` on `X`** for `tempered-fundamental-groups` (`π = s`, `s² = q`:
`a₄ = s²·(a₄/q)`, `a₆ = s²·(a₆/q)`). -/
def tateDataX (h12 : (12 : K) ≠ 0) :
    TemperedFundamentalGroups.TateObject.Data O (DX t).R where
  π := ⟨s, (hO _).2 (norm_s_lt_one hs).le⟩
  b₄ := ⟨t.a₄ / (s : K) ^ 2, mem_O_div O hO hs t.norm_a₄_le⟩
  b₆ := ⟨t.a₆ / (s : K) ^ 2, mem_O_div O hO hs (norm_a₆_le h12)⟩
  π_ne_zero h := s.ne_zero (congrArg Subtype.val h)
  π_mem := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h1 : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := u.inv_mul
    rw [hu] at h1
    have h2 := congrArg (fun z : O => ‖(z : K)‖) h1
    simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h2
    have h3 : ‖(((u⁻¹ : Oˣ) : O) : K)‖ ≤ 1 := (hO _).1 ((u⁻¹ : Oˣ) : O).2
    have h4 := norm_s_lt_one hs
    change ‖(((u⁻¹ : Oˣ) : O) : K)‖ * ‖(s : K)‖ = 1 at h2
    nlinarith [norm_nonneg (((u⁻¹ : Oˣ) : O) : K), norm_nonneg (s : K)]
  x := xX t
  y := yX t
  equation := by
    have hs0 : ((s : K) ^ 2) ≠ 0 := pow_ne_zero _ s.ne_zero
    simp only
    rw [mul_div_cancel₀ _ hs0, mul_div_cancel₀ _ hs0]
    exact yX_equation t

end Base

/-! ### The étale theta class of [EtTh] §1 -/

section Main

variable [t.tateCurve.IsElliptic] (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ}
  (hs : s ^ 2 = t.q) (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)

/-- The compatible system for the Tate data `tateDataX` of `E_q`, for any system of levels with
the transition property. -/
theorem thetaClassCompatible_tate (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
    {L : ℕ → IntermediateField (K₀ K τ) Ω}
    {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω))}
    [∀ j, Fact ((hemiData t.tateCurve).L ≤ L j)]
    [∀ j, Algebra.Etale (DX t).R (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R]
    {η : ∀ j, units (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))}
    (htr : ThetaTransitions (transcendental_tau t.tateCurve) hL η) :
    ThetaClassCompatible (ht := transcendental_tau t.tateCurve) (LX := (hemiData t.tateCurve).L)
      (hLX := hemiL_open t) V hV (tateDataX O hO hs h12) η :=
  thetaClassCompatible htr

include h2 in
/-- **The étale theta class on `Π^tp_Ÿ`** ([EtTh] Prop. 1.3, 1.4(iii)): there is a system of
levels `Ÿ'_{N_j}` (`N_j = 2(j+1)`), étale over `X = E_q ∖ {O}`, with theta level units `η_j`
whose Kummer classes are those of the values of `Θ̈` at points (`EtaleThetaAtPoint`) and which
form a projective system (`ThetaTransitions`); for the Tate data `tateDataX` of `E_q` and under
C1, their tempered Kummer classes restrict to one class `thetaClassTemp η n ∈ H¹(Π^tp_Ÿ, μ_n)`
for each `n`, independent of the level and compatible in `n` (`ThetaClassCompatible`). -/
theorem exists_thetaClassTemp (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) :
    ∃ (L : ℕ → IntermediateField (K₀ K τ) Ω)
      (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
      (_ : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j))
      (_ : ∀ j, Algebra.Etale (DX t).R (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R)
      (η : ∀ j, units (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))),
      (∀ (j : ℕ) (u : Kˣ) (hu : OffOrbit t u)
        (hψ : evalTate t h12 hu (psiN t.tateCurve (2 * (2 * (j + 1)))) ≠ 0),
        EtaleThetaAtPoint h12 (2 * (j + 1)) (L j) (hL j) (η j) u hu hψ) ∧
      ThetaTransitions (transcendental_tau t.tateCurve) hL η ∧
      ThetaClassCompatible (ht := transcendental_tau t.tateCurve) (LX := (hemiData t.tateCurve).L)
        (hLX := hemiL_open t) V hV (tateDataX O hO hs h12) η := by
  obtain ⟨L, hL, h₁, η, het, hpt, -, htr⟩ := exists_etaleThetaSystem h2 h12 hs
  haveI hX : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j) := fun j => ⟨h₁ j⟩
  haveI het' : ∀ j, Algebra.Etale (DX t).R
      (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R := fun j =>
    etale_fieldData (transcendental_tau t.tateCurve) (hemiL_open t) (L j) (hL j) (het j)
  exact ⟨L, hL, hX, het', η, hpt, htr, thetaClassCompatible_tate h12 hs O hO V hV htr⟩

end Main

end Iut.EtaleTheta
