/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.LogVolumeLCFT
import Iut.Reconstruction.Local.MonoAnalytic

/-!
# The mono-analytic log-shell `𝓘(G_k)` is `Iut.logShell` (roadmap P17, M3f)

[AbsTopIII], Proposition 5.8 (ii): the logarithm identifies `𝒪_kˣ ⊗ ℚ` with `k`, and under this
identification the group-theoretic log-shell `𝓘(G_k) = (p*)⁻¹ · 𝒪^×(G_k)`
(`Iut.Reconstruction.monoLogShell`) becomes the log-shell `(2p)⁻¹ log(1 + 𝔪_k)` of IUT III,
Definition 1.1 (`Iut.logShell k p`).

The field `k` carries both structures (valuation and `local-class-field-theory`, with the same
unit ball `hball`, e.g. by `hball_of_continuous`). We define

* `logU : 𝒪_kˣ → k`, `u ↦ (q − 1)⁻¹ log(u^{q−1})` (a homomorphism; on principal units it is
  `log`, `logU_of_principal`), whose image is `log(1 + 𝔪_k)` (`exists_logU_eq_iff`: a unit is a
  Teichmüller representative times a principal unit);
* `logTensor : ℚ ⊗ 𝒪_kˣ → k`, `c ⊗ u ↦ c · logU(u)`;

and prove `logShell_eq_range_logU` (`(2p)⁻¹ log(1 + 𝔪) = (p*)⁻¹ log 𝒪ˣ`, using square roots of
principal units for odd `p`), `image_logTensor` and **`image_logTensor_monoLogShell`**: for
`G_k = Gal(Ω/k)`, `logTensor ∘ (ℚ ⊗ 𝒪_kˣ ≅ ℚ ⊗ 𝒪^×(G_k))⁻¹` maps `𝓘(G_k)` onto
`Iut.logShell k p`.
-/

namespace Iut.Reconstruction

open PadicLogVolume PadicField IsLocalRing
open scoped Valued TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type*} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k] [CompleteSpace k] [CharZero k]
  (hball : ∀ x : k, ‖x‖ ≤ 1 ↔ nrm p k x ≤ 1)
include hball

theorem norm_eq_one_iff_nrm (x : k) : ‖x‖ = 1 ↔ nrm p k x = 1 := by
  have h1 := norm_le_norm_iff hball x 1
  have h2 := norm_le_norm_iff hball 1 x
  rw [norm_one, nrm_one] at h1 h2
  constructor
  · intro h
    exact le_antisymm (h1.1 h.le) (h2.1 h.ge)
  · intro h
    exact le_antisymm (h1.2 h.le) (h2.2 h.ge)

omit hball in
/-- A unit of `𝒪` (in the sense of `unitGroup`) as an element of `(𝒪 p k)ˣ`. -/
def unitGroupToInt (u : unitGroup p k) : (𝒪 p k)ˣ := unitOfNrm ((u : kˣ) : k) u.2

omit hball in
theorem coe_unitGroupToInt (u : unitGroup p k) :
    (((unitGroupToInt u : (𝒪 p k)ˣ) : 𝒪 p k) : k) = ((u : kˣ) : k) := rfl

theorem pow_q_sub_one_principal (u : unitGroup p k) :
    ‖((u : kˣ) : k) ^ (q p k - 1) - 1‖ < 1 := by
  have h := pow_q_sub_one_mem_unitFilt (unitGroupToInt u)
  rw [mem_unitFilt_one_iff hball] at h
  simpa [coe_unitGroupToInt] using h

omit hball in
theorem q_sub_one_ne_zero : ((q p k - 1 : ℕ) : k) ≠ 0 := by
  have := one_lt_q p k
  exact Nat.cast_ne_zero.2 (by omega)

/-- **The logarithm on `𝒪_kˣ`**: `u ↦ (q − 1)⁻¹ log(u^{q−1})`. -/
def logU : unitGroup p k →* Multiplicative k where
  toFun u := Multiplicative.ofAdd
    (((q p k - 1 : ℕ) : k)⁻¹ * padicLog (((u : kˣ) : k) ^ (q p k - 1)))
  map_one' := by simp
  map_mul' x y := by
    simp only [Subgroup.coe_mul, Units.val_mul, mul_pow]
    rw [padicLog_mul hp.out (norm_p_lt_one hball) (pow_q_sub_one_principal hball x)
      (pow_q_sub_one_principal hball y), mul_add, ofAdd_add]

theorem logU_apply (u : unitGroup p k) :
    (logU hball u).toAdd = ((q p k - 1 : ℕ) : k)⁻¹ * padicLog (((u : kˣ) : k) ^ (q p k - 1)) :=
  rfl

/-- On principal units, `logU` is the logarithm. -/
theorem logU_of_principal (u : unitGroup p k) (hu : ‖((u : kˣ) : k) - 1‖ < 1) :
    (logU hball u).toAdd = padicLog ((u : kˣ) : k) := by
  rw [logU_apply, padicLog_pow hp.out (norm_p_lt_one hball) hu, ← mul_assoc,
    inv_mul_cancel₀ (q_sub_one_ne_zero (p := p)), one_mul]

/-- A principal unit as an element of `unitGroup`. -/
def principalToUnitGroup {w : k} (hw : ‖w - 1‖ < 1) : unitGroup p k :=
  ⟨Units.mk0 w (ne_zero_of_norm_sub_one_lt hw),
    (norm_eq_one_iff_nrm hball w).1 (norm_eq_one_of_norm_sub_one_lt hw)⟩

theorem logU_principalToUnitGroup {w : k} (hw : ‖w - 1‖ < 1) :
    (logU hball (principalToUnitGroup hball hw)).toAdd = padicLog w :=
  logU_of_principal hball _ hw

/-- **The image of `logU` is `log(1 + 𝔪)`**: a unit is a Teichmüller representative times a
principal unit. -/
theorem exists_logU_eq_iff (y : k) :
    (∃ u : unitGroup p k, (logU hball u).toAdd = y) ↔
      ∃ w : k, ‖w - 1‖ < 1 ∧ padicLog w = y := by
  constructor
  · rintro ⟨u, rfl⟩
    set u' := unitGroupToInt u
    set ζ : 𝒪 p k := Teichmuller.teichmuller (𝒪 p k) (residue (𝒪 p k) (u' : 𝒪 p k))
    have hres : residue (𝒪 p k) ζ = residue (𝒪 p k) (u' : 𝒪 p k) :=
      Teichmuller.residue_teichmuller _
    have hζ0 : (ζ : k) ≠ 0 := by
      intro h0
      have : ζ = 0 := Integers.ext (by rw [h0]; rfl)
      rw [this, map_zero] at hres
      exact (residue_ne_zero_iff_isUnit _).2 u'.isUnit hres.symm
    have hζpow : (ζ : k) ^ (q p k - 1) = 1 := by
      have h1 : ζ ^ q p k = ζ := Teichmuller.teichmuller_pow_Q _
      have h2 : (ζ : k) ^ q p k = ζ := by
        have := congrArg (fun z : 𝒪 p k => (z : k)) h1
        simpa using this
      have hq := one_lt_q p k
      rw [show q p k = (q p k - 1) + 1 by omega, pow_succ] at h2
      exact (mul_eq_right₀ hζ0).1 h2
    set w : k := ((u : kˣ) : k) / ζ
    have hw : ‖w - 1‖ < 1 := by
      rw [norm_lt_one_iff' hball]
      have hdiff : (u' : 𝒪 p k) - ζ ∈ maximalIdeal (𝒪 p k) := by
        rw [← residue_eq_zero_iff, map_sub, hres, sub_self]
      rw [Integers.mem_maximalIdeal_iff] at hdiff
      have hζn : nrm p k (ζ : k) = 1 := by
        have : IsUnit ζ := by
          rw [← residue_ne_zero_iff_isUnit, hres]
          exact (residue_ne_zero_iff_isUnit _).2 u'.isUnit
        exact Integers.isUnit_iff_nrm_eq_one.1 this
      have : w - 1 = (((u' : 𝒪 p k) : k) - ζ) / ζ := by
        simp only [w, coe_unitGroupToInt, u']
        field_simp
      rw [this, nrm_div, hζn, div_one]
      simpa using hdiff
    refine ⟨w, hw, ?_⟩
    have hww : w ^ (q p k - 1) = ((u : kˣ) : k) ^ (q p k - 1) := by
      simp only [w, div_pow, hζpow, div_one]
    rw [← logU_principalToUnitGroup hball hw, logU_apply, logU_apply]
    change _ * padicLog (w ^ (q p k - 1)) = _
    rw [hww]
  · rintro ⟨w, hw, rfl⟩
    exact ⟨principalToUnitGroup hball hw, logU_principalToUnitGroup hball hw⟩

/-- **`(2p)⁻¹ log(1 + 𝔪) = (p*)⁻¹ log 𝒪ˣ`**. -/
theorem logShell_eq_range_logU :
    logShell k p = {y | ∃ u : unitGroup p k, y = (pStar p : k)⁻¹ * (logU hball u).toAdd} := by
  ext y
  rw [mem_logShell, Set.mem_setOf_eq]
  have hp0 : (p : k) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have h20 : (2 : k) ≠ 0 := two_ne_zero
  by_cases h2 : p = 2
  · subst h2
    have hstar : ((pStar 2 : ℕ) : k) = 2 * ((2 : ℕ) : k) := by
      simp only [pStar]; push_cast; ring
    rw [hstar]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, hu⟩ := (exists_logU_eq_iff hball _).2 ⟨w, hw, rfl⟩
      exact ⟨u, by rw [hu]⟩
    · rintro ⟨u, rfl⟩
      obtain ⟨w, hw, hwu⟩ := (exists_logU_eq_iff hball _).1 ⟨u, rfl⟩
      exact ⟨w, hw, by rw [hwu]⟩
  · have hstar : ((pStar p : ℕ) : k) = p := by simp [pStar, h2]
    rw [hstar]
    constructor
    · rintro ⟨w, hw, rfl⟩
      -- a square root of the principal unit `w`
      set w' := unitGroupToInt (principalToUnitGroup hball hw)
      have hker : w' ∈ (resUnits p k).ker := by
        rw [MonoidHom.mem_ker]
        apply Units.ext
        change residue (𝒪 p k) (w' : 𝒪 p k) = residue (𝒪 p k) 1
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, Integers.mem_maximalIdeal_iff]
        rw [← norm_lt_one_iff' hball]
        simpa [w', coe_unitGroupToInt, principalToUnitGroup] using hw
      have hcop : p.Coprime 2 := (Nat.coprime_primes hp.out Nat.prime_two).2 h2
      obtain ⟨v', hv'⟩ := ker_resUnits_le_powRange hcop two_ne_zero hker
      set v : unitGroup p k := ⟨Units.mk0 ((v' : 𝒪 p k) : k) (by
          intro h0
          exact v'.ne_zero (Integers.ext (by rw [h0]; rfl))),
        Integers.isUnit_iff_nrm_eq_one.1 v'.isUnit⟩
      have hv2 : v ^ 2 = principalToUnitGroup hball hw := by
        apply Subtype.ext
        apply Units.ext
        have := congrArg (fun z : (𝒪 p k)ˣ => ((z : 𝒪 p k) : k)) hv'
        simpa [v, w', coe_unitGroupToInt, principalToUnitGroup] using this
      refine ⟨v, ?_⟩
      have h3 : 2 * (logU hball v).toAdd = padicLog w := by
        rw [← logU_principalToUnitGroup hball hw, ← hv2, map_pow, toAdd_pow, nsmul_eq_mul]
        norm_num
      rw [← h3]
      field_simp
    · rintro ⟨u, rfl⟩
      obtain ⟨w, hw, hwu⟩ := (exists_logU_eq_iff hball _).1 ⟨u, rfl⟩
      refine ⟨w ^ 2, norm_pow_sub_one_lt hw 2, ?_⟩
      rw [padicLog_pow hp.out (norm_p_lt_one hball) hw, hwu]
      push_cast
      field_simp

omit hball in
/-- `(c, a) ↦ c · L(a)`, `ℤ`-bilinear. -/
def scaleMul (L : Additive (unitGroup p k) →+ k) :
    ℚ →ₗ[ℤ] Additive (unitGroup p k) →ₗ[ℤ] k :=
  LinearMap.mk₂ ℤ (fun (c : ℚ) a => (c : k) * L a)
    (fun c c' a => by push_cast; ring)
    (fun n c a => by
      rw [zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring)
    (fun c a a' => by rw [map_add, mul_add])
    (fun n c a => by rw [map_zsmul, zsmul_eq_mul, zsmul_eq_mul]; ring)

/-- **The logarithm `ℚ ⊗ 𝒪_kˣ → k`**, `c ⊗ u ↦ c · logU(u)`. -/
def logTensor : ℚ ⊗[ℤ] Additive (unitGroup p k) →+ k :=
  (TensorProduct.lift (scaleMul (logU hball).toAdditive)).toAddMonoidHom

theorem logTensor_tmul (c : ℚ) (u : unitGroup p k) :
    logTensor hball (c ⊗ₜ Additive.ofMul u) = (c : k) * (logU hball u).toAdd := by
  simp only [logTensor, LinearMap.toAddMonoidHom_coe, TensorProduct.lift.tmul]
  rfl

/-- **`log((p*)⁻¹ ⊗ 𝒪ˣ) = 𝓘_k`.** -/
theorem image_logTensor :
    logTensor hball '' {x | ∃ u : unitGroup p k, x = ((pStar p : ℚ)⁻¹) ⊗ₜ Additive.ofMul u} =
      logShell k p := by
  rw [logShell_eq_range_logU hball]
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    refine ⟨u, ?_⟩
    rw [logTensor_tmul]
    push_cast
    rfl
  · rintro ⟨u, rfl⟩
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    rw [logTensor_tmul]
    push_cast
    rfl

variable {Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

variable (Ω) in
/-- **[AbsTopIII], Proposition 5.8 (ii)**: the group-theoretic log-shell `𝓘(G_k)` of
`G_k = Gal(Ω/k)` is mapped onto the log-shell `Iut.logShell k p` of IUT III, Definition 1.1, by
the logarithm `ℚ ⊗ 𝒪^×(G_k) ≅ ℚ ⊗ 𝒪_kˣ → k`. -/
theorem image_logTensor_monoLogShell :
    (fun x => logTensor hball ((unitsQGalEquiv p k Ω).symm x)) ''
        monoLogShell (Ω ≃ₐ[k] Ω) = logShell k p := by
  rw [← image_monoLogShell_gal p k Ω, Set.image_image]
  simp only [LinearEquiv.symm_apply_apply]
  exact image_logTensor hball

end

end Iut.Reconstruction
