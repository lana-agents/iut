/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.KummerClass
import ContinuousKummerTheory.Kummer.Equiv

/-!
# The theta level functions `f_N = Θ̈_q / (Θ̈_{q^N})^N` (MR14, task G2a)

MR14 plan (route R-alg, `~/iut-scratch/multiradial/MR14-plan.md`): the étale theta class
`η̈^Θ_N ∈ H¹(Π^tp_Ÿ, μ_N)` is the restriction of the Kummer class of a function on the *finite*
level `Ÿ'_N = Ÿ / ⟨N-th power of the generator of Gal(Ÿ/X)⟩`, the Tate curve `E_{Q}` with
`Q = q^{N/2}` (coordinate `Ü`). By [EtTh], Prop. 1.4(ii) (`etaleTheta_zpow_sqrt_mul`),
`Θ̈_q(Q·Ü) = (-1)^N Q^{-N} Ü^{-2N} Θ̈_q(Ü)`, and the étale theta function `Θ̈_{q^N}` of the
parameter `q^N` (whose square root is `Q`) has automorphy factor `-Q^{-1} Ü^{-2}`; hence

`f_N(Ü) := Θ̈_q(Ü) / Θ̈_{q^N}(Ü)^N`

is `Q`-periodic (`thetaLevel_sqrt_pow_mul`): an elliptic function on `E_Q`, regular and
invertible off the cusps `Ü² ∈ q^ℤ` (`thetaLevel_ne_zero`). Its Kummer classes in
`H¹(G_K, μ_n)`, `n ∣ N`, are those of `Θ̈_q` (`kummer_thetaLevel`): the `N`-th power
`Θ̈_{q^N}^N` is invisible mod `n`. The `f_N` are compatible in `N`
(`thetaLevel_mul`: `f_{N·M} = f_N · (f^{(q^N)}_M)^N`, with `f^{(q^N)}_M` again periodic for the
lattice of `f_{N·M}`).
-/

namespace Iut.EtaleTheta

open TateCurvesTheta

variable {K : Type*} [NormedField K]

/-- The Tate parameter `q^N` (`N ≥ 1`). -/
def tatePow (t : TateParameter K) (N : ℕ) (hN : 0 < N) : TateParameter K where
  q := t.q ^ N
  norm_lt_one := by
    rw [Units.val_pow_eq_pow_val, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) t.norm_lt_one hN.ne'

@[simp]
theorem tatePow_q (t : TateParameter K) (N : ℕ) (hN : 0 < N) : (tatePow t N hN).q = t.q ^ N :=
  rfl

theorem tatePow_tatePow (t : TateParameter K) (N M : ℕ) (hN : 0 < N) (hM : 0 < M) :
    tatePow (tatePow t N hN) M hM = tatePow t (N * M) (Nat.mul_pos hN hM) := by
  cases t
  simp only [tatePow, pow_mul]

variable (t : TateParameter K) (N : ℕ) (hN : 0 < N)

/-- **The theta level function** `f_N(Ü) = Θ̈_q(Ü) / Θ̈_{q^N}(Ü)^N`. -/
noncomputable def thetaLevel (U : Kˣ) : K :=
  etaleTheta t U / etaleTheta (tatePow t N hN) U ^ N

/-- `Θ̈_{q^N}` has automorphy factor `-Q^{-1}Ü^{-2}` for `Q = s^N`, `s² = q`
([EtTh], Prop. 1.4(ii) for the parameter `q^N`, `a = 1`). -/
theorem etaleTheta_tatePow_mul {s : Kˣ} (hs : s ^ 2 = t.q) (U : Kˣ) :
    etaleTheta (tatePow t N hN) (s ^ N * U) =
      thetaFactor (s ^ N) 1 U * etaleTheta (tatePow t N hN) U := by
  have hS : (s ^ N) ^ 2 = (tatePow t N hN).q := by
    rw [tatePow_q, ← hs, ← pow_mul, ← pow_mul, mul_comm]
  simpa using etaleTheta_zpow_sqrt_mul (tatePow t N hN) hS 1 U

/-- The two automorphy factors agree: `j_q(N, Ü) = j_{q^N}(1, Ü)^N`. -/
theorem thetaFactor_pow (s : Kˣ) (U : Kˣ) :
    thetaFactor s (N : ℤ) U = thetaFactor (s ^ N) 1 U ^ N := by
  have hs : (s : K) ≠ 0 := s.ne_zero
  have hU : (U : K) ≠ 0 := U.ne_zero
  simp only [thetaFactor, Units.val_pow_eq_pow_val]
  rw [show (-(N : ℤ) ^ 2) = -((N * N : ℕ) : ℤ) by push_cast; ring,
    show (-2 * (N : ℤ)) = -((2 * N : ℕ) : ℤ) by push_cast; ring,
    show (-(1 : ℤ) ^ 2) = -1 by norm_num, show (-2 * (1 : ℤ)) = -((2 : ℕ) : ℤ) by norm_num]
  simp only [zpow_neg, zpow_natCast, zpow_one]
  ring

/-- **`f_N` is `Q`-periodic**, `Q = s^N`, `s² = q`: an elliptic function for the lattice `Q^ℤ`
(the level `Ÿ'_N` of [EtTh], §1). -/
theorem thetaLevel_sqrt_pow_mul {s : Kˣ} (hs : s ^ 2 = t.q) (U : Kˣ) :
    thetaLevel t N hN (s ^ N * U) = thetaLevel t N hN U := by
  have hpow : s ^ N * U = s ^ (N : ℤ) * U := by rw [zpow_natCast]
  unfold thetaLevel
  rw [etaleTheta_tatePow_mul t N hN hs U, mul_pow, hpow, etaleTheta_zpow_sqrt_mul t hs (N : ℤ) U,
    thetaFactor_pow, mul_div_mul_left _ _ (pow_ne_zero _ (thetaFactor_ne_zero _ _ _))]

/-- The cusps of `Ÿ` for `q^N` are cusps for `q`. -/
theorem etaleTheta_tatePow_ne_zero [CompleteSpace K] [IsUltrametricDist K] {U : Kˣ}
    (hU : etaleTheta t U ≠ 0) : etaleTheta (tatePow t N hN) U ≠ 0 := by
  intro h
  rw [etaleTheta_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  apply hU
  rw [etaleTheta_eq_zero_iff]
  exact ⟨N * k, by rw [hk, tatePow_q, Units.val_pow_eq_pow_val, zpow_mul, zpow_natCast]⟩

/-- `f_N` is regular and invertible off the cusps `Ü² ∈ q^ℤ`. -/
theorem thetaLevel_ne_zero [CompleteSpace K] [IsUltrametricDist K] {U : Kˣ}
    (hU : etaleTheta t U ≠ 0) : thetaLevel t N hN U ≠ 0 :=
  div_ne_zero hU (pow_ne_zero _ (etaleTheta_tatePow_ne_zero t N hN hU))

/-- **Compatibility in `N`**: `f_{N·M} = f_N · (f^{(q^N)}_M)^N`. -/
theorem thetaLevel_mul [CompleteSpace K] [IsUltrametricDist K] (M : ℕ) (hM : 0 < M) {U : Kˣ}
    (hU : etaleTheta t U ≠ 0) :
    thetaLevel t (N * M) (Nat.mul_pos hN hM) U =
      thetaLevel t N hN U * thetaLevel (tatePow t N hN) M hM U ^ N := by
  have h1 := etaleTheta_tatePow_ne_zero t N hN hU
  have h2 := etaleTheta_tatePow_ne_zero (tatePow t N hN) M hM h1
  unfold thetaLevel
  rw [tatePow_tatePow, div_pow, ← pow_mul, mul_comm M N]
  field_simp

section Kummer

variable [CompleteSpace K] [IsUltrametricDist K]

/-- `f_N(Ü)` as a unit, off the cusps. -/
noncomputable def thetaLevelUnit {U : Kˣ} (hU : etaleTheta t U ≠ 0) : Kˣ :=
  Units.mk0 _ (thetaLevel_ne_zero t N hN hU)

theorem thetaLevelUnit_eq {U : Kˣ} (hU : etaleTheta t U ≠ 0) :
    thetaLevelUnit t N hN hU = etaleThetaUnit t U hU *
      (etaleThetaUnit (tatePow t N hN) U (etaleTheta_tatePow_ne_zero t N hN hU) ^ N)⁻¹ := by
  ext
  simp [thetaLevelUnit, thetaLevel, div_eq_mul_inv]

variable (n : ℕ) (Ω : Type*) [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [KummerTheory.HasKummerRoots n K Ω]

/-- **The Kummer classes of `f_N` and `Θ̈` agree mod `n` for `n ∣ N`** ([EtTh], Prop. 1.4(iii)
on points, for the finite-level function `f_N`): `κ_n(f_N(Ü)) = κ_n(Θ̈(Ü))`. -/
theorem kummer_thetaLevel (hn : n ∣ N) {U : Kˣ} (hU : etaleTheta t U ≠ 0) :
    KummerTheory.kummer n K Ω (thetaLevelUnit t N hN hU) =
      KummerTheory.kummer n K Ω (etaleThetaUnit t U hU) := by
  obtain ⟨m, rfl⟩ := hn
  rw [thetaLevelUnit_eq, map_mul, map_inv]
  have : KummerTheory.kummer n K Ω
      (etaleThetaUnit (tatePow t (n * m) hN) U (etaleTheta_tatePow_ne_zero t _ hN hU) ^ (n * m))
      = 1 := by
    rw [← MonoidHom.mem_ker, KummerTheory.ker_kummer]
    exact ⟨_ ^ m, by rw [powMonoidHom_apply, ← pow_mul, mul_comm m n]⟩
  rw [this, inv_one, mul_one]

end Kummer

end Iut.EtaleTheta
