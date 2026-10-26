/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaLevelSystem

/-!
# The étale theta classes `κ_n(η_N)` as a projective system (MR14, run 5)

Let `q` be a Tate parameter over a complete nonarchimedean field `K` of characteristic `0` with
`‖2‖ = 1`, `s² = q`, `E = E_q`, `Ω = K(Ē)^alg`, `τ = x`. For `j ∈ ℕ` let `N_j = 2(j+1)`.

**Main theorem** (`exists_etaleThetaSystem`). There are intermediate fields `L'_j ⊆ Ω` (the
function fields of the levels `Ÿ'_{N_j}` of [EtTh], §1, route R-alg of `MR14-plan.md`) and units
`η_j` of `Ÿ'_{N_j}` (the theta level functions `F_{N_j}`) such that

* `coordRing L_X → coordRing L'_j` is étale (`L_X = K(E)`, `X = E ∖ {O}`);
* at every Tate point `u` with `ψ_{2N_j}(u) ≠ 0` there is a `K`-rational point of `Ÿ'_{N_j}` over
  `u` at which `s_x^* κ_n(η_j) = κ_n(Θ̈(u^{N_j}))` for `n ∣ N_j` ([EtTh] Prop. 1.4(iii) at points,
  `EtaleThetaAtPoint`);
* **compatibility in `N`**: if `N_{j'} = N_j·M` with `M` even, then `L'_j ≤ L'_{j'}`, so
  `Π_{Ÿ'_{N_{j'}}} ≤ Π_{Ÿ'_{N_j}}`, and for `n ∣ N_j` the restriction of `κ_n(η_j)` to
  `Π_{Ÿ'_{N_{j'}}}` is `κ_n(η_{j'})`.

So for each `n` the classes `κ_n(η_j)` (`n ∣ N_j`) define one class on `Π_Ÿ = ⋂_j Π_{Ÿ'_{N_j}}`:
this is the étale theta class `η̈^Θ` mod `n` of [EtTh], Prop. 1.3 (as the Kummer class of `Θ̈`,
Prop. 1.4(iii)). The index set `{N_j}` with the relation "`N_{j'}/N_j` even" is directed and
cofinal for divisibility.
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta

open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

section Transition

variable {k Ω' : Type u} [Field k] [Field Ω'] [Algebra k Ω'] {t' : Ω'} [CharZero k]
  [IsGalois (K₀ k t') Ω'] [IsSepClosed Ω'] (ht : Transcendental k t')

omit [CharZero k] [IsGalois (K₀ k t') Ω'] [IsSepClosed Ω'] in
theorem fieldData_H_antitone {L L' : IntermediateField (K₀ k t') Ω'}
    (hL : IsOpen (L.fixingSubgroup : Set (Ω' ≃ₐ[K₀ k t'] Ω')))
    (hL' : IsOpen (L'.fixingSubgroup : Set (Ω' ≃ₐ[K₀ k t'] Ω'))) (hle : L ≤ L') :
    (fieldData ht L' hL').H ≤ (fieldData ht L hL).H :=
  IntermediateField.fixingSubgroup_antitone hle

omit [CharZero k] [IsGalois (K₀ k t') Ω'] [IsSepClosed Ω'] in
theorem fieldData_S_antitone {L L' : IntermediateField (K₀ k t') Ω'}
    (hL : IsOpen (L.fixingSubgroup : Set (Ω' ≃ₐ[K₀ k t'] Ω')))
    (hL' : IsOpen (L'.fixingSubgroup : Set (Ω' ≃ₐ[K₀ k t'] Ω'))) (hle : L ≤ L') :
    (fieldData ht L' hL').S ⊆ (fieldData ht L hL).S :=
  fun _ hσ => ⟨IntermediateField.fixingSubgroup_antitone hle hσ.1, hσ.2⟩

/-- **The transition statement between two levels** `L ≤ L'` with units `η`, `η'`: for every
`n ∣ N`, the restriction of `κ_n(η)` to `Π_{L'}` is `κ_n(η')`. -/
def LevelTransition {L L' : IntermediateField (K₀ k t') Ω'}
    (hL : IsOpen (L.fixingSubgroup : Set (Ω' ≃ₐ[K₀ k t'] Ω')))
    (hL' : IsOpen (L'.fixingSubgroup : Set (Ω' ≃ₐ[K₀ k t'] Ω')))
    (η : units (fieldData ht L hL)) (η' : units (fieldData ht L' hL')) (N : ℕ) : Prop :=
  ∃ hle : L ≤ L', ∀ (n : ℕ) [NeZero n], n ∣ N →
    resPi (fieldData_H_antitone ht hL hL' hle) (fieldData_S_antitone ht hL hL' hle) n
        (kummerMap (fieldData ht L hL) n η) =
      kummerMap (fieldData ht L' hL') n η'

/-- **A transition from a factorisation of units**: if `η'` is the image of `η` times an `N`-th
power of a unit of `L'`, the classes `κ_n(η)`, `κ_n(η')` (`n ∣ N`) are compatible. -/
theorem levelTransition_of_eq {L L' : IntermediateField (K₀ k t') Ω'}
    (hL : IsOpen (L.fixingSubgroup : Set (Ω' ≃ₐ[K₀ k t'] Ω')))
    (hL' : IsOpen (L'.fixingSubgroup : Set (Ω' ≃ₐ[K₀ k t'] Ω'))) (hle : L ≤ L')
    (η : units (fieldData ht L hL)) (η' : units (fieldData ht L' hL')) (N : ℕ)
    (v' γ : units (fieldData ht L' hL'))
    (hv' : ((((v' : (F (fieldData ht L' hL'))ˣ) : F (fieldData ht L' hL')) : Ω')) =
      ((((η : (F (fieldData ht L hL))ˣ) : F (fieldData ht L hL)) : Ω')))
    (hη' : η' = v' * γ ^ N) : LevelTransition ht hL hL' η η' N := by
  refine ⟨hle, fun n _ hn => ?_⟩
  obtain ⟨c, hc⟩ := hn
  rw [hη', map_mul, map_pow, hc, pow_mul, pow_eq_one_of_mu, one_pow, mul_one]
  exact resPi_kummerMap _ _ n η v' hv'.symm

end Transition

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- A unit of a level `L' ≤ L_m` from an element of `K[E][1/ψ_m]` whose inverse is also in
`K[E][1/ψ_m]`. -/
theorem exists_unit_of_cover [t.tateCurve.IsElliptic] (m : ℕ) [NeZero m]
    (L' : IntermediateField (K₀ K τ) Ω) (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
    {g : TateField t} (hg : mulByNEmb t.tateCurve m g ∈ L') (hg0 : g ≠ 0)
    {b b' : coverRingN t.tateCurve m} (hb : algebraMap _ _ b = g) (hb' : algebraMap _ _ b' = g⁻¹) :
    ∃ η : units (fieldData (transcendental_tau t.tateCurve) L' hL'),
      ((((η : (F (fieldData (transcendental_tau t.tateCurve) L' hL'))ˣ) :
        F (fieldData (transcendental_tau t.tateCurve) L' hL')) : Ω)) =
        mulByNEmb t.tateCurve m g := by
  refine exists_unit_fieldData (transcendental_tau t.tateCurve) L' hL' hg
    ((_root_.map_ne_zero _).mpr hg0) ?_ ?_
  · rw [← hb]; exact isIntegral_mulByNEmb _ _ b
  · rw [← map_inv₀, ← hb']; exact isIntegral_mulByNEmb _ _ b'

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **The transition between two levels, from the function-field data** (`2N' = M·2N`):
`L'_N ≤ L'_{N'}` and `η_{N'} = η_N · γ^N` (`F_{N'} = [M]^*F_N · G^N`). -/
theorem levelTransition_of_data [t.tateCurve.IsElliptic] {N M N' : ℕ} (hN : 0 < N)
    [NeZero (2 * N)] [NeZero (2 * N')] [NeZero M] (hrel : M * (2 * N) = 2 * N')
    {gX gY Fθ gX' gY' Fθ' G : TateField t}
    (hF : Fθ ∈ IntermediateField.adjoin K ({gX, gY} : Set (TateField t)))
    (hgX : pb t.tateCurve M gX ∈ IntermediateField.adjoin K ({gX', gY'} : Set (TateField t)))
    (hgY : pb t.tateCurve M gY ∈ IntermediateField.adjoin K ({gX', gY'} : Set (TateField t)))
    (hGmem : G ∈ IntermediateField.adjoin K ({gX', gY'} : Set (TateField t)))
    (hFG : Fθ' = pb t.tateCurve M Fθ * G ^ N) (hF0 : Fθ ≠ 0) (hF0' : Fθ' ≠ 0)
    {b b₁ : coverRingN t.tateCurve (2 * N)} (hb : algebraMap _ _ b = Fθ)
    (hb₁ : algebraMap _ _ b₁ = Fθ⁻¹)
    {b' b₁' : coverRingN t.tateCurve (2 * N')} (hb' : algebraMap _ _ b' = Fθ')
    (hb₁' : algebraMap _ _ b₁' = Fθ'⁻¹)
    {L L' : IntermediateField (K₀ K τ) Ω}
    (hLd : L = IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}))
    (hL'd : L' =
      IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N') '' {gX', gY'}))
    (hL : IsOpen (L.fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
    (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
    (η : units (fieldData (transcendental_tau t.tateCurve) L hL))
    (hη : ((((η : (F (fieldData (transcendental_tau t.tateCurve) L hL))ˣ) :
        F (fieldData (transcendental_tau t.tateCurve) L hL)) : Ω)) =
      mulByNEmb t.tateCurve (2 * N) Fθ)
    (η' : units (fieldData (transcendental_tau t.tateCurve) L' hL'))
    (hη' : ((((η' : (F (fieldData (transcendental_tau t.tateCurve) L' hL'))ˣ) :
        F (fieldData (transcendental_tau t.tateCurve) L' hL')) : Ω)) =
      mulByNEmb t.tateCurve (2 * N') Fθ') :
    LevelTransition (transcendental_tau t.tateCurve) hL hL' η η' N := by
  have hle : L ≤ L' := by
    rw [hLd, hL'd]
    refine levelField_mono hrel fun g hg => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    exacts [hgX, hgY]
  have hFL : mulByNEmb t.tateCurve (2 * N) Fθ ∈ L := by rw [hLd]; exact mem_adjoin_image _ _ hF
  have hGL : mulByNEmb t.tateCurve (2 * N') G ∈ L' := by
    rw [hL'd]; exact mem_adjoin_image _ _ hGmem
  have hφ : ∀ x, mulByNEmb t.tateCurve (2 * N') (pb t.tateCurve M x) =
      mulByNEmb t.tateCurve (2 * N) x := fun x => by
    rw [← AlgHom.comp_apply, mulByNEmb_comp_pb_eq hrel]
  have hval : mulByNEmb t.tateCurve (2 * N') Fθ' =
      mulByNEmb t.tateCurve (2 * N) Fθ * mulByNEmb t.tateCurve (2 * N') G ^ N := by
    rw [hFG, map_mul, map_pow, hφ]
  obtain ⟨v', hv'⟩ := exists_unit_of_cover (2 * N) L' hL' (hle hFL) hF0 hb hb₁
  have hG0 : G ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), mul_zero] at hFG
    exact hF0' hFG
  have hφF0 : mulByNEmb t.tateCurve (2 * N) Fθ ≠ 0 := (_root_.map_ne_zero _).mpr hF0
  have hφG0 : mulByNEmb t.tateCurve (2 * N') G ≠ 0 := (_root_.map_ne_zero _).mpr hG0
  have hpowG : mulByNEmb t.tateCurve (2 * N') G ^ N =
      mulByNEmb t.tateCurve (2 * N') Fθ' * (mulByNEmb t.tateCurve (2 * N) Fθ)⁻¹ := by
    rw [hval]; field_simp
  have hpowG' : (mulByNEmb t.tateCurve (2 * N') G)⁻¹ ^ N =
      (mulByNEmb t.tateCurve (2 * N') Fθ')⁻¹ * mulByNEmb t.tateCurve (2 * N) Fθ := by
    rw [inv_pow, hpowG, mul_inv, inv_inv]
  have i1 : IsIntegral (A₀ K τ) (mulByNEmb t.tateCurve (2 * N) Fθ) := by
    rw [← hb]; exact isIntegral_mulByNEmb _ _ b
  have i2 : IsIntegral (A₀ K τ) (mulByNEmb t.tateCurve (2 * N) Fθ)⁻¹ := by
    rw [← map_inv₀, ← hb₁]; exact isIntegral_mulByNEmb _ _ b₁
  have i3 : IsIntegral (A₀ K τ) (mulByNEmb t.tateCurve (2 * N') Fθ') := by
    rw [← hb']; exact isIntegral_mulByNEmb _ _ b'
  have i4 : IsIntegral (A₀ K τ) (mulByNEmb t.tateCurve (2 * N') Fθ')⁻¹ := by
    rw [← map_inv₀, ← hb₁']; exact isIntegral_mulByNEmb _ _ b₁'
  obtain ⟨γ, hγ⟩ := exists_unit_fieldData (transcendental_tau t.tateCurve) L' hL' hGL hφG0
    (IsIntegral.of_pow hN (by rw [hpowG]; exact i3.mul i2))
    (IsIntegral.of_pow hN (by rw [hpowG']; exact i4.mul i1))
  refine levelTransition_of_eq _ hL hL' hle η η' N v' γ (hv'.trans hη.symm) ?_
  apply Subtype.ext; apply Units.ext; apply Subtype.ext
  change ((((η' : (F (fieldData (transcendental_tau t.tateCurve) L' hL'))ˣ) :
      F (fieldData (transcendental_tau t.tateCurve) L' hL')) : Ω)) =
    ((((v' : (F (fieldData (transcendental_tau t.tateCurve) L' hL'))ˣ) :
      F (fieldData (transcendental_tau t.tateCurve) L' hL')) : Ω)) *
    ((((γ : (F (fieldData (transcendental_tau t.tateCurve) L' hL'))ˣ) :
      F (fieldData (transcendental_tau t.tateCurve) L' hL')) : Ω)) ^ N
  rw [hη', hv', hγ, hval]

/-- **The étale theta classes form a projective system** (see the module docstring). -/
theorem exists_etaleThetaSystem (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ}
    (hs : s ^ 2 = t.q) :
    haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
    ∃ (L : ℕ → IntermediateField (K₀ K τ) Ω)
      (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
      (h₁ : ∀ j, (hemiData t.tateCurve).L ≤ L j)
      (η : ∀ j, units (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))),
      (∀ j, (ringMap τ (h₁ j)).toRingHom.Etale) ∧
      (∀ (j : ℕ) (u : Kˣ) (hu : OffOrbit t u)
        (hψ : evalTate t h12 hu (psiN t.tateCurve (2 * (2 * (j + 1)))) ≠ 0),
        EtaleThetaAtPoint h12 (2 * (j + 1)) (L j) (hL j) (η j) u hu hψ) ∧
      ∀ j j' M : ℕ, 2 * (j' + 1) = 2 * (j + 1) * M → Even M →
        LevelTransition (transcendental_tau t.tateCurve) (hL j) (hL j') (η j) (η j')
          (2 * (j + 1)) := by
  haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
  choose gX gY F hF hmul hunit hval using fun j : ℕ =>
    exists_levelData (t := t) h12 h2 hs (N := 2 * (j + 1)) (by omega) ⟨j + 1, by ring⟩
  choose b b' hb hb' using hunit
  -- the levels
  set L : ℕ → IntermediateField (K₀ K τ) Ω := fun j => IntermediateField.adjoin (K₀ K τ)
    (mulByNEmb t.tateCurve (2 * (2 * (j + 1))) '' {gX j, gY j}) with hLdef
  have hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)) := fun j =>
    IntermediateField.fixingSubgroup_isOpen _
  have hFL : ∀ j, mulByNEmb t.tateCurve (2 * (2 * (j + 1))) (F j) ∈ L j := fun j =>
    mem_adjoin_image _ _ (hF j)
  -- `F_N ≠ 0`, and the values of `F_N` at points
  have hpt : ∀ (j : ℕ) (u : Kˣ) (hu : OffOrbit t u)
      (hψ : evalTate t h12 hu (psiN t.tateCurve (2 * (2 * (j + 1)))) ≠ 0),
      etaleTheta t (u ^ (2 * (j + 1))) ≠ 0 ∧
      evalCover (2 * (2 * (j + 1))) hu hψ (b j) =
        thetaLevel t (2 * (j + 1)) (by omega) (u ^ (2 * (j + 1))) := by
    intro j u hu hψ
    obtain ⟨hum, -⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * (2 * (j + 1))) h2 hu hψ
    have h := hasTateValue_cover (2 * (2 * (j + 1))) hu hψ (b j)
    rw [hb j] at h
    exact ⟨etaleTheta_pow_ne_zero hum, h.unique (hval j u hu hum).2.2⟩
  have hF0 : ∀ j, F j ≠ 0 := by
    intro j h0
    apply psiN_ne_zero_of_neZero t.tateCurve (2 * (2 * (j + 1)))
    refine eq_zero_of_evalTate (h12 := h12) _ fun u hu => ?_
    by_contra hψ
    obtain ⟨hum, -⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * (2 * (j + 1))) h2 hu hψ
    exact (hval j u hu hum).2.2.ne_zero
      (thetaLevel_ne_zero t _ (by omega) (etaleTheta_pow_ne_zero hum)) h0
  -- the units `η_N`
  choose η hη using fun j => exists_unit_of_cover (2 * (2 * (j + 1))) (L j) (hL j) (hFL j)
    (hF0 j) (hb j) (hb' j)
  refine ⟨L, hL, fun j => hemiL_le_adjoin _ _ (hmul j), η,
    fun j => etale_adjoin_image _ _ (hmul j), fun j => ?_, fun j j' M hjM hevM => ?_⟩
  · exact etaleThetaClass_points (by omega) (L j) (hL j) (adjoin_image_le_mulByNField _ _ _)
      (η j) ((hη j).trans (congrArg _ (hb j).symm)) (hpt j)
  -- the transition `j → j'`
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h, mul_zero] at hjM; omega
    · exact h
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hgX, hgY, G, hGmem, hFG⟩ := levelData_transition h12 h2 hs (by omega) hM (by omega)
    hjM hevM (hval j) (hval j')
  exact levelTransition_of_data (by omega) (by rw [hjM]; ring) (hF j) hgX hgY hGmem hFG (hF0 j)
    (hF0 j') (hb j) (hb' j) (hb j') (hb' j') rfl rfl (hL j) (hL j') (η j) (hη j) (η j') (hη j')

end Iut.EtaleTheta
