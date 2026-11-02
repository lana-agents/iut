/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaLevelHeisenberg
import Iut.EtaleTheta.ThetaLevelQuot

/-!
# [EtTh] Prop. 1.5(iii) mod `l` at the levels, and the translation homomorphism (MR14, run 17)

MR15 obligation 13c(i), (ii) (`MR15-plan.md`, phase 2 run 6). Let `s² = q`, `Q = s^N`, `N` even.

* **Prop. 1.5(iii) mod `l` on `E_Q` itself** ((ii)): for `w = (-1)^e s^a` with `a = l b`
  (`l` odd, `N = k l`, so `k` is even) the `l`-th root of the translation factor is on the level:
  `exists_transFactorLevel` (`H ∈ K(E_Q)` with values `U^{-2b}(Θ̈_{q^N}(U)/Θ̈_{q^N}(wU))^k`, by the
  weight-family engine: `isWeightFamily_shiftCoef`), `thetaLevel_cuspElt_mul_pow` (the identity on
  values, `d = (-1)^e(-1)^b s^{-lb²}`), **`transT_level_pow`** (`t_w f = d^l H^l f` in `K(E_Q)`).
  Checked numerically before formalising (`MR14-plan.md`, run 17, D24); [EtTh] Prop. 1.5(iii):
  `a ∈ ℤ` acts by `η̈^Θ ↦ η̈^Θ − 2a log(Ü) − (a²/2) log(q) + log(O^×)`, whose `log(Ü)`- and
  `log(q)`-terms vanish mod `l` for `l ∣ a`.
* **The translation homomorphism** ((i)): for an embedding `ι : K(E_Q) → Ω'` and a group `G` of
  automorphisms each of which acts as `σ ∘ ι = ι ∘ t_w` (`exists_levelEmb`), `transHom : G →*
  K^×/Q^ℤ`, `σ ↦ w` (`transIdx`; multiplicative by `genPointHom` on the generic point and the Tate
  point homomorphism `tatePoint_mul`, `basePt_eq_map`), trivial on `Gal(Ω/L_j)`
  (`transHom_eq_one_of`); `dvd_of_mk_cuspElt_eq`: `w(σ) = w(ρ)^l ⇒ l ∣ a(σ)` for `l ∣ N`.
* At the levels: `level_stable` (`σ(L_j) ⊆ L_j`), `transHom_level_eq_one`,
  **`transHom_level_pow`** (`w(σ) = w(ρ)^l ⇒
  σ(η) = (d·y)^l·η`, `d ∈ K`, `y ∈ L_j`).
* **`exists_etaleThetaSystem`** (moved here from `ThetaLevelHeisenberg.lean`) has the new last
  conjunct: homomorphisms `w_j : Gal(Ω/L_X) →* K^×/Q_j^ℤ`, trivial on `Gal(Ω/L_j)`, the
  stability `σ(L_j) ⊆ L_j`, and
  `w_j(σ) = w_j(ρ)^l ⇒ σ(η_j) = (d·y)^l·η_j`, `d ∈ K`, `y ∈ L_j` (`l` odd, `l ∣ N_j`).
-/

open Polynomial

noncomputable section

universe u

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter

section Tate

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **Shifting a theta family**: if `c` is a weight-`k` family with multiplier `A`, then the
family of `U ↦ U^{-j}·G(U)` has weight `k` and multiplier `A·q^{-j}`. -/
theorem isWeightFamily_shiftCoef {T : TateParameter K} {k : ℕ} {A : Kˣ} {c : ℤ → K}
    (hc : T.IsWeightFamily k A c) (j : ℤ) :
    T.IsWeightFamily k (A * (T.q ^ j)⁻¹) (shiftCoef c j) := by
  refine ⟨fun u => (hasSum_shiftCoef j u (hc.summable u).hasSum).summable, fun n => ?_⟩
  have h := hc.step (n + j)
  have hq : (T.q : K) ≠ 0 := T.q.ne_zero
  simp only [shiftCoef, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
  rw [show n + (k : ℤ) + j = n + j + k by ring, mul_comm (A : K), mul_assoc, h,
    zpow_add₀ hq]
  field_simp

variable (t : TateParameter K) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ}
  (hN : 0 < N) (T : TateParameter K) (hT : T.q = s ^ N)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem transValueLevel_eq {w U : Kˣ} (k b : ℕ) {Θ₁ Θ₂ : K} (hΘ : Θ₂ ≠ 0) :
    ((w : K) ^ k)⁻¹ * (((U : K) ^ (-(k : ℤ)) * Θ₁ ^ k) /
        ((U : K) ^ (-(-((2 * b : ℕ) : ℤ))) * (((w * U : Kˣ) : K) ^ (-(k : ℤ)) * Θ₂ ^ k))) =
      (U : K) ^ (-((2 * b : ℕ) : ℤ)) * Θ₁ ^ k / Θ₂ ^ k := by
  have hU : (U : K) ≠ 0 := U.ne_zero
  have hw : (w : K) ≠ 0 := w.ne_zero
  simp only [Units.val_mul, zpow_neg, neg_neg, zpow_natCast]
  field_simp
  ring

include hs hT in
/-- **The `l`-th root of the translation factor on the level `E_Q` itself** ([EtTh] Prop. 1.5(iii)
mod `l` at the level; MR15 obligation 13c(ii)). For `w = ε·s^a` (`ε² = 1`) and `a·k = b·N`
(`a = l b`, `N = l k`) with `k` even, there are `H ∈ K(E_Q)` (`Q = s^N`) and `0 ≠ D ∈ K[E_Q]` such
that wherever `D(U) ≠ 0`, `Θ̈_{q^N}(wU) ≠ 0` and `H(U) = U^{-2b}·Θ̈_{q^N}(U)^k/Θ̈_{q^N}(wU)^k`.
(Numerically checked before formalising, `MR14-plan.md`, run 17.) -/
theorem exists_transFactorLevel (k : ℕ) (hk : 0 < k) (hke : Even k) {ε : Kˣ}
    (hε : (ε : K) ^ 2 = 1) (a b : ℕ) (hab : a * k = b * N) :
    ∃ (H : TateField T) (D : TateRing T), D ≠ 0 ∧ ∀ (U : Kˣ) (hU : OffOrbit T U),
      evalTate T h12 hU D ≠ 0 →
        etaleTheta (tatePow t N hN) (ε * s ^ a * U) ≠ 0 ∧
        HasTateValue T h12 H hU ((U : K) ^ (-((2 * b : ℕ) : ℤ)) *
          etaleTheta (tatePow t N hN) U ^ k / etaleTheta (tatePow t N hN) (ε * s ^ a * U) ^ k) := by
  have hc := isWeightFamily_thetaPow t hs hN T hT k
  have hM : multθ T ^ (2 * k) = (T.q ^ 2 * (-1))⁻¹ ^ k := multθ_pow_two_mul hke T
  have hw2 : (ε * s ^ a) ^ (2 * k) = T.q ^ ((2 * b : ℕ) : ℤ) := by
    have hε' : ε ^ 2 = 1 := Units.ext (by simpa using hε)
    rw [mul_pow, pow_mul ε 2 k, hε', one_pow, one_mul, ← pow_mul, hT, zpow_natCast, ← pow_mul]
    congr 1
    calc a * (2 * k) = 2 * (a * k) := by ring
      _ = N * (2 * b) := by rw [hab]; ring
  have h₁ : T.IsWeightFamily (2 * k) (multθ T ^ (2 * k))
      (cpow (oddShift (tatePow t N hN) 1) k) := by
    rw [hM]; exact hc
  have h₂ : T.IsWeightFamily (2 * k) (multθ T ^ (2 * k))
      (shiftCoef (scaleCoef (cpow (oddShift (tatePow t N hN) 1) k) (ε * s ^ a))
        (-((2 * b : ℕ) : ℤ))) := by
    have := isWeightFamily_shiftCoef (isWeightFamily_scaleCoef hc (ε * s ^ a)) (-((2 * b : ℕ) : ℤ))
    rwa [hw2, zpow_neg, inv_inv, inv_mul_cancel_right, ← hM] at this
  have tden : ∀ U : Kˣ, (∑' m : ℤ, shiftCoef (scaleCoef (cpow (oddShift (tatePow t N hN) 1) k)
      (ε * s ^ a)) (-((2 * b : ℕ) : ℤ)) m *
      (U : K) ^ m) = (U : K) ^ (-(-((2 * b : ℕ) : ℤ))) *
        (((ε * s ^ a * U : Kˣ) : K) ^ (-(k : ℤ)) *
          etaleTheta (tatePow t N hN) (ε * s ^ a * U) ^ k) := by
    intro U
    rw [(hasSum_shiftCoef _ U
      ((isWeightFamily_scaleCoef hc (ε * s ^ a)).summable U).hasSum).tsum_eq,
      tsum_scaleCoef, tsum_thetaPow t hs hN T hT k]
  obtain ⟨n, d, h⟩ := exists_hasTateValue_of_weight (h12 := h12)
    (Nat.mul_pos two_pos hk) h₁ h₂
  refine ⟨algebraMap K (TateField T) (((ε * s ^ a : Kˣ) : K) ^ k)⁻¹ *
      (algebraMap _ (TateField T) n / algebraMap _ (TateField T) d), d, ?_, fun U hU hD => ?_⟩
  · obtain ⟨u₀, hn₀, h1₀⟩ := exists_good_unit t hN
    have hU₀n : ‖((u₀ ^ N : Kˣ) : K)‖ = 1 := by
      rw [Units.val_pow_eq_pow_val, norm_pow, hn₀, one_pow]
    have hU₀ : OffOrbit T (u₀ ^ N) := offOrbit_of_norm hU₀n fun h => h1₀ (by
      rw [pow_mul', ← Units.val_pow_eq_pow_val, h, one_pow])
    have hΘ₀ := etaleTheta_trans_ne_zero t hs hN hε a hn₀ h1₀
    obtain ⟨-, e₂, -⟩ := h (u₀ ^ N) hU₀
    intro hd0
    rw [hd0, map_zero, zero_mul, tden] at e₂
    exact hΘ₀ ((pow_eq_zero_iff hk.ne').mp ((mul_eq_zero.mp ((mul_eq_zero.mp e₂).resolve_left
      (zpow_ne_zero _ (Units.ne_zero _)))).resolve_left (zpow_ne_zero _ (Units.ne_zero _))))
  · obtain ⟨-, e₂, hv⟩ := h U hU
    have hθ : T.theta (-U) ^ (2 * k) ≠ 0 := pow_ne_zero _ (theta_neg_ne_zero T hU)
    have hF₂ : (∑' m : ℤ, shiftCoef (scaleCoef (cpow (oddShift (tatePow t N hN) 1) k)
        (ε * s ^ a)) (-((2 * b : ℕ) : ℤ)) m * (U : K) ^ m) ≠ 0 := by
      rw [e₂]; exact mul_ne_zero hD hθ
    have hΘ : etaleTheta (tatePow t N hN) (ε * s ^ a * U) ≠ 0 := by
      intro h0
      apply hF₂
      rw [tden, h0, zero_pow hk.ne', mul_zero, mul_zero]
    refine ⟨hΘ, ((HasTateValue.const hU _).mul (hv hF₂)).congr ?_⟩
    rw [tsum_thetaPow t hs hN T hT k, tden]
    exact transValueLevel_eq k b hΘ

end Tate

section Value

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem neg_one_pow_odd_pow {l : ℕ} (hl : Odd l) (e : ℕ) :
    ((-1 : K) ^ e) ^ l = (-1) ^ e := by
  rw [← pow_mul, mul_comm, pow_mul, hl.neg_one_pow]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **The translation identity of the theta level function mod `l`-th powers, on values**:
for `a = l b`, `N = k l` (`l` odd) and `w = (-1)^e s^a`,
`f_N(U w) = d^l · (U^{-2b} Θ̈_{q^N}(U)^k / Θ̈_{q^N}(wU)^k)^l · f_N(U)` with
`d = (-1)^e (-1)^b s^{-l b²} ∈ K`. -/
theorem thetaLevel_cuspElt_mul_pow (t : TateParameter K) {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ}
    (hN : 0 < N) {l k b : ℕ} (hl : Odd l) (hkl : k * l = N) (e : Fin 2) {a : ℕ} (hab : a = l * b)
    (U : Kˣ) (h0 : etaleTheta (tatePow t N hN) U ≠ 0)
    (h1 : etaleTheta (tatePow t N hN) ((-1) ^ (e : ℕ) * s ^ a * U) ≠ 0) :
    thetaLevel t N hN (U * cuspElt s e a) =
      ((-1 : K) ^ (e : ℕ) * (-1) ^ b * (s : K) ^ (-((l * b ^ 2 : ℕ) : ℤ))) ^ l *
        ((U : K) ^ (-((2 * b : ℕ) : ℤ)) * etaleTheta (tatePow t N hN) U ^ k /
          etaleTheta (tatePow t N hN) ((-1) ^ (e : ℕ) * s ^ a * U) ^ k) ^ l *
        thetaLevel t N hN U := by
  have hw : U * cuspElt s e a = (-1) ^ (e : ℕ) * (s ^ (a : ℤ) * U) := by
    rw [cuspElt, zpow_natCast, mul_comm, mul_assoc]
  have hw' : (-1) ^ (e : ℕ) * s ^ a * U = (-1) ^ (e : ℕ) * (s ^ (a : ℤ) * U) := by
    rw [zpow_natCast, mul_assoc]
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have e1 : ((-1 : K) ^ b) ^ l = (-1) ^ (a : ℤ) := by
    rw [← pow_mul, hab, mul_comm, zpow_natCast]
  have e2 : ((s : K) ^ (-((l * b ^ 2 : ℕ) : ℤ))) ^ l = (s : K) ^ (-(a : ℤ) ^ 2) := by
    rw [← zpow_natCast _ l, ← zpow_mul, hab]
    congr 1
    push_cast
    ring
  have hd : ((-1 : K) ^ (e : ℕ) * (-1) ^ b * (s : K) ^ (-((l * b ^ 2 : ℕ) : ℤ))) ^ l =
      (-1 : K) ^ (e : ℕ) * ((-1 : K) ^ (a : ℤ) * (s : K) ^ (-(a : ℤ) ^ 2)) := by
    rw [mul_pow, mul_pow, neg_one_pow_odd_pow hl, e1, e2, mul_assoc]
  have hU : ((U : K) ^ (-((2 * b : ℕ) : ℤ))) ^ l = (U : K) ^ (-2 * (a : ℤ)) := by
    rw [← zpow_natCast _ l, ← zpow_mul, hab]
    congr 1
    push_cast
    ring
  rw [hw'] at h1 ⊢
  rw [hw, thetaLevel, thetaLevel, etaleTheta_sign_pow, etaleTheta_zpow_sqrt_mul t hs, thetaFactor,
    hd, div_pow, mul_pow, hU, ← pow_mul, ← pow_mul, hkl]
  have hu : (U : K) ^ (-2 * (a : ℤ)) ≠ 0 := zpow_ne_zero _ U.ne_zero
  field_simp

end Value

section LevelIdentity

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K} {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ} (hN : 0 < N)

omit [CharZero K] in
theorem etaleTheta_ne_zero_of_offOrbit_sq {U : Kˣ} (hU2 : OffOrbit t (U ^ 2)) :
    etaleTheta (tatePow t N hN) U ≠ 0 := by
  rw [Ne, etaleTheta_eq_zero_iff]
  rintro ⟨m, hm⟩
  apply hU2 (-(N * m))
  simp only [tatePow_q, Units.val_pow_eq_pow_val] at hm
  rw [Units.val_pow_eq_pow_val, hm, ← zpow_natCast (t.q : K) N, ← zpow_mul,
    ← zpow_add₀ t.q.ne_zero, neg_add_cancel,
    zpow_zero]

omit [CharZero K] in
include hs in
theorem good_level (h12 : (12 : K) ≠ 0) {w : Kˣ} {U : Kˣ} (hU : OffOrbit (sqrtPow hs N hN) U)
    (h0 : evalTate (sqrtPow hs N hN) h12 hU (mkT (sqrtPow hs N hN)
      (C (badPoly (sqrtPow hs N hN) s N * (Polynomial.X - C ((sqrtPow hs N hN).X w))))) ≠ 0) :
    OffOrbit t (U ^ 2) ∧ (sqrtPow hs N hN).X U ≠ (sqrtPow hs N hN).X w := by
  rw [evalTate_mk_C, eval_mul, eval_sub, eval_X, eval_C] at h0
  obtain ⟨h0a, h0b⟩ := mul_ne_zero_iff.mp h0
  refine ⟨?_, sub_ne_zero.mp h0b⟩
  by_contra h
  exact h0a (badPoly_eval_eq_zero hs hN rfl h)

set_option maxHeartbeats 1000000 in
-- `eq_of_hasTateValue` with translated values
/-- **[EtTh] Prop. 1.5(iii) mod `l` at the level `E_Q`** (MR15 obligation 13c(ii), the identity):
for the theta level function `f ∈ K(E_Q)` (`Q = s^N`, values `f_N`), a kernel point
`w = (-1)^e s^a ≠ 1` with `a = l b` (`l` odd, `N = k l`, `k` even):
`t_w f = d^l · H^l · f` with `d ∈ K` and `H ∈ K(E_Q)` — the `l`-th root of the translation
factor lives on the level itself (unlike `pullbackT_transT_level`, where `H ∈ L_{2N}`). -/
theorem transT_level_pow (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0)
    [(sqrtPow hs N hN).tateCurve.IsElliptic] {f : TateField (sqrtPow hs N hN)}
    (hfv : ∀ (u : Kˣ) (hu : OffOrbit (sqrtPow hs N hN) u), etaleTheta (tatePow t N hN) u ≠ 0 →
      HasTateValue (sqrtPow hs N hN) h12 f hu (thetaLevel t N hN u))
    {l k b : ℕ} (hl : Odd l) (hkl : k * l = N) (hke : Even k) (e : Fin 2) (a : Fin N)
    (hab : (a : ℕ) = l * b) (h00 : (e, (a : ℕ)) ≠ (0, 0)) :
    ∃ (d : K) (H : TateField (sqrtPow hs N hN)),
      transT h12 (offOrbit_cuspElt rfl hN a.2 h00) f = algebraMap K _ (d ^ l) * H ^ l * f := by
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, zero_mul] at hkl; omega
    · exact h
  have hε : (((-1 : Kˣ) ^ (e : ℕ) : Kˣ) : K) ^ 2 = 1 := by
    rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul]; simp
  have hab' : (a : ℕ) * k = b * N := by rw [hab, ← hkl]; ring
  obtain ⟨H, DH, hDH, hHv⟩ :=
    exists_transFactorLevel t h12 hs hN (sqrtPow hs N hN) rfl k hk0 hke hε a b hab'
  set w := cuspElt s e (a : ℕ) with hwdef
  have hw : OffOrbit (sqrtPow hs N hN) w := offOrbit_cuspElt rfl hN a.2 h00
  have hDb : badPoly (sqrtPow hs N hN) s N * (Polynomial.X - C ((sqrtPow hs N hN).X w)) ≠ 0 :=
    mul_ne_zero badPoly_ne_zero (X_sub_C_ne_zero _)
  have hwU : ∀ U : Kˣ, U * w = (-1) ^ (e : ℕ) * s ^ (a : ℕ) * U := fun U => by
    rw [hwdef, cuspElt, mul_comm]
  refine ⟨(-1 : K) ^ (e : ℕ) * (-1) ^ b * (s : K) ^ (-((l * b ^ 2 : ℕ) : ℤ)), H,
    eq_of_hasTateValue (h12 := h12) (mul_ne_zero (mkT_C_ne_zero h12 hDb) hDH)
      (G := fun U => thetaLevel t N hN (U * w)) (fun U hU h0 => ?_) (fun U hU h0 => ?_)⟩
  · rw [map_mul] at h0
    obtain ⟨hb, hD⟩ := mul_ne_zero_iff.mp h0
    obtain ⟨hU2, hx⟩ := good_level hs hN h12 hU hb
    have hUw : OffOrbit (sqrtPow hs N hN) (U * w) := by
      intro n hn
      apply hx
      have e' : U = (sqrtPow hs N hN).q ^ (-n) * w⁻¹ := by
        apply Units.ext
        push_cast at hn ⊢
        have hw0 : (w : K) ≠ 0 := w.ne_zero
        have hT0 : ((sqrtPow hs N hN).q : K) ≠ 0 := (sqrtPow hs N hN).q.ne_zero
        rw [zpow_neg]
        field_simp
        linear_combination hn
      rw [e', X_zpow_mul, (sqrtPow hs N hN).X_inv hw]
    have hΘ : etaleTheta (tatePow t N hN) (U * w) ≠ 0 := by
      rw [hwU]; exact (hHv U hU hD).1
    exact hasTateValue_trans h2 hU hw hUw hx f _ (hfv _ hUw hΘ)
  · rw [map_mul] at h0
    obtain ⟨hb, hD⟩ := mul_ne_zero_iff.mp h0
    obtain ⟨hU2, -⟩ := good_level hs hN h12 hU hb
    obtain ⟨h1, hH⟩ := hHv U hU hD
    have hΘU := etaleTheta_ne_zero_of_offOrbit_sq hN hU2
    refine (((HasTateValue.const hU _).mul (hH.pow l)).mul (hfv U hU hΘU)).congr ?_
    exact (thetaLevel_cuspElt_mul_pow t hs hN hl hkl e hab U hΘU h1).symm

end LevelIdentity

section Index

open WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing CurvesJacobian.Cusp

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {s : Kˣ} {N : ℕ} {T : TateParameter K} (hT : T.q = s ^ N) (hN : 0 < N)
  (h12 : (12 : K) ≠ 0) (h2 : ‖(2 : K)‖ = 1)

local notation "𝒫" => genericPoint (W := T.tateCurve.toAffine)

section Points

/-- The Tate point of `u ∈ K^×` in `E_T(K)` (`tatePoint`, a homomorphism with kernel `T.q^ℤ`). -/
def tatePt (u : Kˣ) : T.tateCurve.toAffine.Point :=
  T.tatePoint (fun _ hu => tateEquation h12 hu) ⟨h2, h12⟩ u

omit [CharZero K] in
theorem tatePt_def (u : Kˣ) :
    tatePt (T := T) h12 h2 u = T.tatePoint (fun _ hu => tateEquation h12 hu) ⟨h2, h12⟩ u := rfl

omit [CharZero K] in
/-- Equal Tate points are equal in `K^×/T.q^ℤ`. -/
theorem mk_eq_of_tatePt_eq {u v : Kˣ} (h : tatePt (T := T) h12 h2 u = tatePt (T := T) h12 h2 v) :
    (u : Kˣ ⧸ T.qpowers) = v := by
  classical
  rw [QuotientGroup.eq, ← T.tatePoint_eq_zero_iff (fun _ hu => tateEquation h12 hu) ⟨h2, h12⟩,
    T.tatePoint_mul, T.tatePoint_inv]
  rw [tatePt_def, tatePt_def] at h
  rw [h, neg_add_cancel]

include h2 in
/-- The translation point of `t_w` is the image of the Tate point of `w`. -/
theorem basePt_eq_map [T.tateCurve.IsElliptic] [DecidableEq K] [DecidableEq (TateField T)]
    (e : Fin 2) (a : Fin N) :
    basePt hT hN h12 e a =
      Point.map (W' := T.tateCurve) (Algebra.ofId K (TateField T))
        (tatePt (T := T) h12 h2 (cuspElt s e a)) := by
  unfold basePt
  split_ifs with h
  · have h0 : tatePt (T := T) h12 h2 (cuspElt s e a) = 0 := by
      rw [tatePt_def, T.tatePoint_eq_zero_iff, T.mem_qpowers_iff]
      refine ⟨0, ?_⟩
      simp only [Prod.mk.injEq] at h
      obtain ⟨he, ha⟩ := h
      simp [cuspElt, he, ha]
    rw [h0]
    rfl
  · have hw := offOrbit_cuspElt hT hN a.2 h
    have hnm : cuspElt s e a ∉ T.qpowers := fun hm => by
      obtain ⟨n, hn⟩ := (T.mem_qpowers_iff _).mp hm
      exact hw n hn
    rw [tatePt_def, T.tatePoint_of_notMem _ _ hnm]
    rfl

end Points

variable [T.tateCurve.IsElliptic]

include h2 in
theorem mk_eq_of_basePt_eq {e e' : Fin 2} {a a' : Fin N}
    (h : basePt hT hN h12 e a = basePt hT hN h12 e' a') :
    (cuspElt s e a : Kˣ ⧸ T.qpowers) = cuspElt s e' a' := by
  classical
  rw [basePt_eq_map hT hN h12 h2, basePt_eq_map hT hN h12 h2] at h
  exact mk_eq_of_tatePt_eq h12 h2 (Point.map_injective _ h)

variable {P Ω' : Type*} [Field P] [Field Ω'] [Algebra K P] [Algebra P Ω'] [Algebra K Ω']
  [IsScalarTower K P Ω'] (ι : TateField T →ₐ[K] Ω') (G : Subgroup (Ω' ≃ₐ[P] Ω'))
  (hι : ∀ σ ∈ G, ∃ p : Fin 2 × Fin N, ((σ : Ω' →ₐ[P] Ω').restrictScalars K).comp ι =
    ι.comp (baseAut hT hN h12 p.1 p.2 : TateField T →ₐ[K] TateField T))

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] [T.tateCurve.IsElliptic] in
theorem baseAut_eq_of_comp_eq {φ ψ : TateField T →ₐ[K] TateField T} (h : ι.comp φ = ι.comp ψ) :
    φ = ψ :=
  AlgHom.ext fun g => ι.toRingHom.injective (AlgHom.congr_fun h g)

theorem basePt_eq_of_comp_eq {p p' : Fin 2 × Fin N}
    (h : ι.comp (baseAut hT hN h12 p.1 p.2 : TateField T →ₐ[K] TateField T) =
      ι.comp (baseAut hT hN h12 p'.1 p'.2 : TateField T →ₐ[K] TateField T)) :
    basePt hT hN h12 p.1 p.2 = basePt hT hN h12 p'.1 p'.2 := by
  have h'' := congrArg (fun φ => genPointHom φ 𝒫) (baseAut_eq_of_comp_eq ι h)
  simp only [genPointHom_baseAut] at h''
  exact add_left_cancel h''

omit [T.tateCurve.IsElliptic] in
theorem baseAut_zero : (baseAut hT hN h12 0 ⟨0, hN⟩ : TateField T →ₐ[K] TateField T) =
    AlgHom.id K _ := by
  rw [baseAut, dif_pos rfl]; rfl

/-- The translation index of `σ ∈ G`: the kernel point `(e, a)` with `σ ∘ ι = ι ∘ t_w`. -/
def transIdx (σ : G) : Fin 2 × Fin N := (hι σ σ.2).choose

omit [T.tateCurve.IsElliptic] in
theorem transIdx_spec (σ : G) :
    (((σ : Ω' ≃ₐ[P] Ω') : Ω' →ₐ[P] Ω').restrictScalars K).comp ι =
      ι.comp (baseAut hT hN h12 (transIdx hT hN h12 ι G hι σ).1
        (transIdx hT hN h12 ι G hι σ).2 : TateField T →ₐ[K] TateField T) :=
  (hι σ σ.2).choose_spec

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem restrictScalars_mul (σ τ : Ω' ≃ₐ[P] Ω') :
    (((σ * τ : Ω' ≃ₐ[P] Ω') : Ω' →ₐ[P] Ω').restrictScalars K) =
      ((σ : Ω' →ₐ[P] Ω').restrictScalars K).comp ((τ : Ω' →ₐ[P] Ω').restrictScalars K) :=
  AlgHom.ext fun _ => rfl

include h2 in
theorem mk_transIdx_eq_one_of (σ : G)
    (hσ : (((σ : Ω' ≃ₐ[P] Ω') : Ω' →ₐ[P] Ω').restrictScalars K).comp ι = ι) :
    (cuspElt s (transIdx hT hN h12 ι G hι σ).1 (transIdx hT hN h12 ι G hι σ).2 :
      Kˣ ⧸ T.qpowers) = 1 := by
  have h1 := (transIdx_spec hT hN h12 ι G hι σ).symm.trans
    (hσ.trans (by rw [baseAut_zero hT hN h12, AlgHom.comp_id] :
      ι = ι.comp (baseAut hT hN h12 0 ⟨0, hN⟩ : TateField T →ₐ[K] TateField T)))
  have h1' := basePt_eq_of_comp_eq hT hN h12 ι (p' := (0, ⟨0, hN⟩)) h1
  rw [mk_eq_of_basePt_eq hT hN h12 h2 h1']
  simp [cuspElt]

/-- **The translation homomorphism** `w : G → K^×/Q^ℤ` (`G ⊆ Gal(Ω/L_X)`, `Q = T.q`):
`σ ∘ ι = ι ∘ t_w` with `w = (-1)^e s^a` (MR15 obligation 13c(i): `Π^tp_X → Gal(L_j/L_X)`, the
latter identified with the kernel `{±s^a}` of `E_Q → E_q` inside `K^×/Q^ℤ`). -/
def transHom : G →* Kˣ ⧸ T.qpowers where
  toFun σ := (cuspElt s (transIdx hT hN h12 ι G hι σ).1 (transIdx hT hN h12 ι G hι σ).2 :
    Kˣ ⧸ T.qpowers)
  map_one' := mk_transIdx_eq_one_of hT hN h12 h2 ι G hι 1 (AlgHom.ext fun _ => rfl)
  map_mul' σ τ := by
    classical
    have h3 := transIdx_spec hT hN h12 ι G hι (σ * τ)
    have h1 := transIdx_spec hT hN h12 ι G hι σ
    have h2' := transIdx_spec hT hN h12 ι G hι τ
    rw [Subgroup.coe_mul, restrictScalars_mul, AlgHom.comp_assoc, h2', ← AlgHom.comp_assoc, h1,
      AlgHom.comp_assoc] at h3
    have e := baseAut_eq_of_comp_eq ι h3.symm
    have hP := congrArg (fun φ => genPointHom φ 𝒫) e
    rw [← genPointHom_comp, genPointHom_baseAut, genPointHom_baseAut, map_add,
      genPointHom_baseAut, genPointHom_basePt, add_assoc] at hP
    have hb := add_left_cancel hP
    rw [basePt_eq_map hT hN h12 h2, basePt_eq_map hT hN h12 h2, basePt_eq_map hT hN h12 h2] at hb
    rw [← QuotientGroup.mk_mul]
    refine (mk_eq_of_tatePt_eq h12 h2 ?_).symm
    rw [tatePt_def, T.tatePoint_mul, ← tatePt_def h12 h2, ← tatePt_def h12 h2]
    apply Point.map_injective (W' := T.tateCurve) (Algebra.ofId K (TateField T))
    refine Eq.trans ?_ hb.symm
    exact map_add _ _ _

theorem transHom_apply (σ : G) : transHom hT hN h12 h2 ι G hι σ =
    (cuspElt s (transIdx hT hN h12 ι G hι σ).1 (transIdx hT hN h12 ι G hι σ).2 :
      Kˣ ⧸ T.qpowers) := rfl

theorem transHom_eq_one_of (σ : G)
    (hσ : (((σ : Ω' ≃ₐ[P] Ω') : Ω' →ₐ[P] Ω').restrictScalars K).comp ι = ι) :
    transHom hT hN h12 h2 ι G hι σ = 1 :=
  mk_transIdx_eq_one_of hT hN h12 h2 ι G hι σ hσ

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] [T.tateCurve.IsElliptic] in
include hT hN in
/-- If `(-1)^e s^a ≡ ((-1)^{e'} s^{a'})^l` mod `Q^ℤ` (`Q = s^N`) and `l ∣ N`, then `l ∣ a`. -/
theorem dvd_of_mk_cuspElt_eq {l : ℕ} (hlN : l ∣ N) {e e' : Fin 2} {a a' : ℕ}
    (h : (cuspElt s e a : Kˣ ⧸ T.qpowers) = (cuspElt s e' a' : Kˣ ⧸ T.qpowers) ^ l) :
    l ∣ a := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq, T.mem_qpowers_iff] at h
  obtain ⟨n, hn⟩ := h
  have hs1 := norm_s_lt_one_of_q hT hN
  have hs0 : 0 < ‖(s : K)‖ := norm_pos_iff.mpr s.ne_zero
  have hnorm := congrArg norm hn
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_mul,
    norm_inv, norm_pow, norm_zpow, norm_cuspElt, hT, norm_one] at hnorm
  have hr0 : ‖(s : K)‖ ≠ 0 := hs0.ne'
  have e : ‖(s : K)‖ ^ ((N : ℤ) * n - a + l * a') =
      (‖(s : K)‖ ^ N) ^ n * (‖(s : K)‖ ^ a)⁻¹ * (‖(s : K)‖ ^ a') ^ l := by
    rw [zpow_add₀ hr0, zpow_sub₀ hr0, zpow_mul, zpow_natCast, zpow_natCast, mul_comm (l : ℤ),
      zpow_mul, zpow_natCast, zpow_natCast, div_eq_mul_inv]
  have key : ‖(s : K)‖ ^ ((N : ℤ) * n - a + l * a') = ‖(s : K)‖ ^ (0 : ℤ) := by
    rw [e, zpow_zero]
    linear_combination hnorm
  have h0 := zpow_right_injective₀ hs0 (ne_of_lt hs1) key
  obtain ⟨c, hc⟩ := hlN
  have hz : (l : ℤ) ∣ (a : ℤ) := ⟨c * n + a', by
    have : (a : ℤ) = N * n + l * a' := by linarith
    rw [this, hc]; push_cast; ring⟩
  exact_mod_cast hz

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] [T.tateCurve.IsElliptic] in
include hT hN in
/-- The exponent of `s` in a kernel point is determined modulo `N` by its class mod `Q^ℤ`
(`Q = s^N`): if `(-1)^e s^a ≡ x` then `a = A + N n` whenever `‖x‖ = ‖s‖^A`. -/
theorem exp_eq_of_mk_cuspElt_eq {e : Fin 2} {a : ℕ} {x : Kˣ} {A : ℤ}
    (hx : ‖(x : K)‖ = ‖(s : K)‖ ^ A) (h : (cuspElt s e a : Kˣ ⧸ T.qpowers) = x) :
    ∃ n : ℤ, (a : ℤ) = A + N * n := by
  rw [QuotientGroup.eq, T.mem_qpowers_iff] at h
  obtain ⟨n, hn⟩ := h
  have hs1 := norm_s_lt_one_of_q hT hN
  have hs0 : 0 < ‖(s : K)‖ := norm_pos_iff.mpr s.ne_zero
  have hr0 : ‖(s : K)‖ ≠ 0 := hs0.ne'
  have hnorm := congrArg norm hn
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, norm_zpow,
    norm_cuspElt, hT, Units.val_pow_eq_pow_val, norm_pow, norm_one, hx] at hnorm
  have ha : ‖(s : K)‖ ^ a ≠ 0 := pow_ne_zero _ hr0
  have key : ‖(s : K)‖ ^ a = (‖(s : K)‖ ^ N) ^ n * ‖(s : K)‖ ^ A :=
    calc ‖(s : K)‖ ^ a = ‖(s : K)‖ ^ a * ((‖(s : K)‖ ^ N) ^ n * ((‖(s : K)‖ ^ a)⁻¹ *
          ‖(s : K)‖ ^ A)) := by rw [hnorm, mul_one]
      _ = (‖(s : K)‖ ^ N) ^ n * ‖(s : K)‖ ^ A := by field_simp
  refine ⟨n, zpow_right_injective₀ hs0 (ne_of_lt hs1) ?_⟩
  change ‖(s : K)‖ ^ (a : ℤ) = ‖(s : K)‖ ^ (A + N * n)
  rw [zpow_add₀ hr0, zpow_mul, zpow_natCast, zpow_natCast, key, mul_comm]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] [T.tateCurve.IsElliptic] in
include hT hN in
/-- If `(-1)^e s^a ≡ ((-1)^{e'} s^{a'})^l · (-1)^{e''} s^{a''}` mod `Q^ℤ`, `l ∣ N` and `l ∣ a''`,
then `l ∣ a`. -/
theorem dvd_of_mk_cuspElt_eq_mul {l : ℕ} (hlN : l ∣ N) {e e' e'' : Fin 2} {a a' a'' : ℕ}
    (hla : l ∣ a'')
    (h : (cuspElt s e a : Kˣ ⧸ T.qpowers) =
      (cuspElt s e' a' : Kˣ ⧸ T.qpowers) ^ l * (cuspElt s e'' a'' : Kˣ ⧸ T.qpowers)) :
    l ∣ a := by
  rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul] at h
  have hx : ‖((cuspElt s e' a' ^ l * cuspElt s e'' a'' : Kˣ) : K)‖ =
      ‖(s : K)‖ ^ ((l * a' + a'' : ℕ) : ℤ) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, norm_cuspElt, norm_cuspElt,
      zpow_natCast]
    ring
  obtain ⟨n, hn⟩ := exp_eq_of_mk_cuspElt_eq hT hN hx h
  obtain ⟨c, hc⟩ := hlN
  obtain ⟨c', hc'⟩ := hla
  have hz : (l : ℤ) ∣ (a : ℤ) := ⟨a' + c' + c * n, by rw [hn, hc, hc']; push_cast; ring⟩
  exact_mod_cast hz

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] [T.tateCurve.IsElliptic] in
include hT hN in
/-- A kernel point of order `≤ 2` mod `Q^ℤ` has `a ∈ {0, N/2}` (mod `N`): if `2l ∣ N` then
`l ∣ a`. -/
theorem dvd_of_mk_cuspElt_sq {l : ℕ} (hlN : 2 * l ∣ N) {e : Fin 2} {a : ℕ}
    (h : (cuspElt s e a : Kˣ ⧸ T.qpowers) ^ 2 = 1) : l ∣ a := by
  rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one] at h
  have hc2 : ((cuspElt s e a ^ 2 : Kˣ) : Kˣ ⧸ T.qpowers) = cuspElt s 0 (2 * a) := by
    congr 1
    apply Units.ext
    simp only [cuspElt, Units.val_pow_eq_pow_val, Units.val_mul, Fin.val_zero, pow_zero, one_mul]
    rw [mul_pow, ← pow_mul, mul_comm (e : ℕ) 2, pow_mul]
    simp only [Units.val_neg, Units.val_one, neg_one_sq, one_pow, one_mul]
    ring
  rw [hc2] at h
  have hx : ‖((1 : Kˣ) : K)‖ = ‖(s : K)‖ ^ (0 : ℤ) := by simp
  obtain ⟨n, hn⟩ := exp_eq_of_mk_cuspElt_eq hT hN hx h
  obtain ⟨c, hc⟩ := hlN
  have hz : (l : ℤ) ∣ (a : ℤ) := ⟨c * n, by
    have : (2 : ℤ) * a = 2 * (l * (c * n)) := by
      have h' : ((2 * a : ℕ) : ℤ) = 0 + N * n := hn
      rw [hc] at h'; push_cast at h'; linarith
    linarith⟩
  exact_mod_cast hz

end Index

section Level

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer
open CurvesJacobian.Cusp WeierstrassCurve.Affine

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

variable (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ}
  (hN : 0 < N) [t.tateCurve.IsElliptic] [NeZero (2 * N)] [(sqrtPow hs N hN).tateCurve.IsElliptic]
  {gX gY : TateField t} (hpt : IsTPoint (sqrtPow hs N hN) gX gY) (htr : Transcendental K gX)
  (hidx : ∀ σ : FFClosure (curveE t.tateCurve) ≃ₐ[K₀ K (coordT (xN t.tateCurve))]
      FFClosure (curveE t.tateCurve), σ ∈ (hemiData t.tateCurve).L.fixingSubgroup →
    ∃ p : Fin 2 × Fin N,
      ((σ : FFClosure (curveE t.tateCurve) →ₐ[K₀ K (coordT (xN t.tateCurve))]
          FFClosure (curveE t.tateCurve)).restrictScalars K).comp
        ((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr)) =
      ((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr)).comp
        (baseAut (rfl : (sqrtPow hs N hN).q = s ^ N) hN h12 p.1 p.2 :
          TateField (sqrtPow hs N hN) →ₐ[K] TateField (sqrtPow hs N hN)))

omit [CompleteSpace K] [IsUltrametricDist K] [(sqrtPow hs N hN).tateCurve.IsElliptic] in
theorem levelEmb_mem (g : TateField (sqrtPow hs N hN)) :
    ((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr)) g ∈
      IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}) := by
  rw [AlgHom.comp_apply]
  exact mem_adjoin_image _ _ (pullbackT_mem_adjoin gX gY hpt htr g)

omit [(sqrtPow hs N hN).tateCurve.IsElliptic] in
include h12 hs hN hpt htr hidx in
/-- **The level is stable under `Gal(Ω/L_X)`** (`L_j/L_X` is Galois; input of
`normal_piYddotX` for MR15 obligation 13b). -/
theorem level_stable (σ : Ω ≃ₐ[K₀ K τ] Ω) (hσ : σ ∈ (hemiData t.tateCurve).L.fixingSubgroup)
    {x : Ω}
    (hx : x ∈ IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY})) :
    σ x ∈ IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}) := by
  set ι := (mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr) with hιdef
  obtain ⟨p, hp⟩ := hidx σ hσ
  have hι : ∀ g, σ (ι g) ∈
      IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}) := by
    intro g
    have e : σ (ι g) = ι (baseAut (rfl : (sqrtPow hs N hN).q = s ^ N) hN h12 p.1 p.2 g) :=
      DFunLike.congr_fun hp g
    rw [e]
    exact levelEmb_mem hs hN hpt htr _
  have hle : (IntermediateField.adjoin (K₀ K τ)
      (mulByNEmb t.tateCurve (2 * N) '' {gX, gY})).map (σ : Ω →ₐ[K₀ K τ] Ω) ≤
        IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}) := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    rcases hg with hg | hg
    · rw [hg]
      have h := hι (algebraMap _ _ (mkT (sqrtPow hs N hN) (C Polynomial.X)))
      have e2 : ι (algebraMap _ _ (mkT (sqrtPow hs N hN) (C Polynomial.X))) =
          mulByNEmb t.tateCurve (2 * N) gX := by
        rw [hιdef, AlgHom.comp_apply, pullbackT_genX]
      rw [e2] at h
      exact h
    · rw [show g = gY from hg]
      have h := hι (algebraMap _ _ (mkT (sqrtPow hs N hN) Polynomial.X))
      have e2 : ι (algebraMap _ _ (mkT (sqrtPow hs N hN) Polynomial.X)) =
          mulByNEmb t.tateCurve (2 * N) gY := by
        rw [hιdef, AlgHom.comp_apply, pullbackT_genY]
      rw [e2] at h
      exact h
  exact hle ⟨x, hx, rfl⟩

/-- **The translation homomorphism is trivial on `Gal(Ω/L_j)`** (MR15 13c(i)). -/
theorem transHom_level_eq_one (σ : (hemiData t.tateCurve).L.fixingSubgroup)
    (hσ : ∀ z ∈ IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}),
      (σ : Ω ≃ₐ[K₀ K τ] Ω) z = z) :
    transHom rfl hN h12 h2 ((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr))
      (hemiData t.tateCurve).L.fixingSubgroup hidx σ = 1 :=
  transHom_eq_one_of rfl hN h12 h2 _ _ hidx σ
    (AlgHom.ext fun g => hσ _ (levelEmb_mem hs hN hpt htr g))

include h2 in
/-- The core of `transHom_level_pow`: if `l` divides the exponent `a` of the translation
index `(e, a)` of `σ`, then `σ(η) = (d·y)^l·η` with `d ∈ K`, `y ∈ L`. -/
theorem level_pow_of_dvd (hev : Even N)
    {f : TateField (sqrtPow hs N hN)}
    (hfv : ∀ (U : Kˣ) (hU : OffOrbit (sqrtPow hs N hN) U), etaleTheta (tatePow t N hN) U ≠ 0 →
      HasTateValue (sqrtPow hs N hN) h12 f hU (thetaLevel t N hN U))
    {l : ℕ} (hl : Odd l) (hlN : l ∣ N) (σ : (hemiData t.tateCurve).L.fixingSubgroup)
    (hla : l ∣ ((transIdx rfl hN h12 ((mulByNEmb t.tateCurve (2 * N)).comp
      (pullbackT gX gY hpt htr)) (hemiData t.tateCurve).L.fixingSubgroup hidx σ).2 : ℕ)) :
    ∃ (d : K), ∃ y ∈ IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}),
      (σ : Ω ≃ₐ[K₀ K τ] Ω) (((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr)) f) =
        (algebraMap K Ω d * y) ^ l *
          ((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr)) f := by
  set ι := (mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr) with hιdef
  have hspec := transIdx_spec rfl hN h12 ι (hemiData t.tateCurve).L.fixingSubgroup hidx σ
  set p := transIdx rfl hN h12 ι (hemiData t.tateCurve).L.fixingSubgroup hidx σ with hpdef
  have key : (σ : Ω ≃ₐ[K₀ K τ] Ω) (ι f) =
      ι (baseAut (rfl : (sqrtPow hs N hN).q = s ^ N) hN h12 p.1 p.2 f) := by
    have := congrArg (fun g : TateField (sqrtPow hs N hN) →ₐ[K] Ω => g f) hspec
    simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgHom.coe_coe,
      AlgEquiv.coe_toAlgHom] using this
  rw [key]
  by_cases h00 : (p.1, (p.2 : ℕ)) = (0, 0)
  · refine ⟨1, 1, one_mem _, ?_⟩
    rw [baseAut, dif_pos h00]
    simp
  · obtain ⟨b, hb⟩ := hla
    obtain ⟨k, hk⟩ := hlN
    have hkl : k * l = N := by rw [hk, mul_comm]
    have hke : Even k := by
      rw [hk] at hev
      exact (Nat.even_mul.mp hev).resolve_left (Nat.not_even_iff_odd.mpr hl)
    obtain ⟨d, H, hH⟩ := transT_level_pow hs hN h2 h12 hfv hl hkl hke p.1 p.2 hb h00
    refine ⟨d, ι H, levelEmb_mem hs hN hpt htr H, ?_⟩
    rw [baseAut, dif_neg h00, hH]
    simp only [map_mul, map_pow, AlgHom.commutes, mul_pow]


/-- **[EtTh] Prop. 1.5(iii) mod `l` at the level `Ÿ'_N`** (MR15 obligation 13c(ii)): if the
translation of `σ ∈ Gal(Ω/L_X)` on the level is an `l`-th power of a translation
(`w(σ) = w(ρ)^l`, `l` odd, `l ∣ N`, `N` even), then `σ(η) = (d·y)^l·η` with `d ∈ K` and `y` in
the level `L = K(τ)(φ x_Q∘ψ, φ y_Q∘ψ)` itself, where `η = φ(F_N)`. -/
theorem transHom_level_pow (hev : Even N)
    {f : TateField (sqrtPow hs N hN)}
    (hfv : ∀ (U : Kˣ) (hU : OffOrbit (sqrtPow hs N hN) U), etaleTheta (tatePow t N hN) U ≠ 0 →
      HasTateValue (sqrtPow hs N hN) h12 f hU (thetaLevel t N hN U))
    {l : ℕ} (hl : Odd l) (hlN : l ∣ N) (σ ρ : (hemiData t.tateCurve).L.fixingSubgroup)
    (h : transHom rfl hN h12 h2 ((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr))
        (hemiData t.tateCurve).L.fixingSubgroup hidx σ =
      transHom rfl hN h12 h2 ((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr))
        (hemiData t.tateCurve).L.fixingSubgroup hidx ρ ^ l) :
    ∃ (d : K), ∃ y ∈ IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}),
      (σ : Ω ≃ₐ[K₀ K τ] Ω) (((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr)) f) =
        (algebraMap K Ω d * y) ^ l *
          ((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr)) f := by
  rw [transHom_apply, transHom_apply] at h
  exact level_pow_of_dvd h2 h12 hs hN hpt htr hidx hev hfv hl hlN σ
    (dvd_of_mk_cuspElt_eq rfl hN hlN h)

/-- **[EtTh] Prop. 1.5(iii) mod `l` at the level, general form** (MR15 obligation 13c(i)+(ii)):
if `w(σ) = w(ρ)^l·w(τ)` with `w(τ)² = 1` (`l` odd, `2l ∣ N`), then `σ(η) = (d·y)^l·η` with
`d ∈ K`, `y ∈ L`. (`w(τ) ∈ {±1, ±s^{N/2}}`, all `l`-th powers of kernel points as `l ∣ N/2`.) -/
theorem transHom_level_pow_mul (hev : Even N)
    {f : TateField (sqrtPow hs N hN)}
    (hfv : ∀ (U : Kˣ) (hU : OffOrbit (sqrtPow hs N hN) U), etaleTheta (tatePow t N hN) U ≠ 0 →
      HasTateValue (sqrtPow hs N hN) h12 f hU (thetaLevel t N hN U))
    {l : ℕ} (hl : Odd l) (hlN : 2 * l ∣ N) (σ ρ τ' : (hemiData t.tateCurve).L.fixingSubgroup)
    (h : transHom rfl hN h12 h2 ((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr))
        (hemiData t.tateCurve).L.fixingSubgroup hidx σ =
      transHom rfl hN h12 h2 ((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr))
        (hemiData t.tateCurve).L.fixingSubgroup hidx ρ ^ l *
      transHom rfl hN h12 h2 ((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr))
        (hemiData t.tateCurve).L.fixingSubgroup hidx τ')
    (hτ : transHom rfl hN h12 h2 ((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr))
        (hemiData t.tateCurve).L.fixingSubgroup hidx τ' ^ 2 = 1) :
    ∃ (d : K), ∃ y ∈ IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}),
      (σ : Ω ≃ₐ[K₀ K τ] Ω) (((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr)) f) =
        (algebraMap K Ω d * y) ^ l *
          ((mulByNEmb t.tateCurve (2 * N)).comp (pullbackT gX gY hpt htr)) f := by
  have hlN' : l ∣ N := Dvd.dvd.trans (Dvd.intro_left 2 rfl) hlN
  rw [transHom_apply, transHom_apply, transHom_apply] at h
  rw [transHom_apply] at hτ
  exact level_pow_of_dvd h2 h12 hs hN hpt htr hidx hev hfv hl hlN' σ
    (dvd_of_mk_cuspElt_eq_mul rfl hN hlN' (dvd_of_mk_cuspElt_sq rfl hN hlN hτ) h)

end Level

section SystemVars

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]

open CurvesJacobian.Cusp WeierstrassCurve.Affine

section System

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer

variable {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
/-- The Tate parameter `s^N` of the level `N = 2` is `q` itself. -/
theorem sqrtPow_eq_self {t : TateParameter K} {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ} (hN : 0 < N)
    (h : N = 2) : sqrtPow hs N hN = t := by
  subst h
  cases t
  simp only [sqrtPow, TateParameter.mk.injEq]
  exact hs

/-- **The level `Ÿ'_2` is the source of `[2]`**: the coordinates `x_Q∘ψ`, `y_Q∘ψ` of the level
`N = 2` (`Q = s² = q`) of `exists_levelData` are `[2]^*x`, `[2]^*y`. -/
theorem levelData_two_eq_pb (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) [t.tateCurve.IsElliptic]
    {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ} (hN : 0 < N) (hN2 : N = 2) {gX gY F : TateField t}
    (hval : ∀ (u : Kˣ) (hu : OffOrbit t u), OffOrbit t (u ^ (2 * N)) →
      HasTateValue t h12 gX hu ((sqrtPow hs N hN).X (u ^ N)) ∧
      HasTateValue t h12 gY hu ((sqrtPow hs N hN).Y (u ^ N)) ∧
      HasTateValue t h12 F hu (thetaLevel t N hN (u ^ N))) :
    gX = pb t.tateCurve 2 (algebraMap (TateRing t) (TateField t) (xE t.tateCurve)) ∧
      gY = pb t.tateCurve 2 (algebraMap (TateRing t) (TateField t) (yE t.tateCurve)) := by
  subst hN2
  rw [sqrtPow_eq_self hs hN rfl] at hval
  have hD₀ : psiN t.tateCurve 4 * psiN t.tateCurve 2 ≠ 0 :=
    mul_ne_zero (psiN_ne_zero_of_neZero _ _) (psiN_ne_zero_of_neZero _ _)
  have good : ∀ (u : Kˣ) (hu : OffOrbit t u),
      evalTate t h12 hu (psiN t.tateCurve 4 * psiN t.tateCurve 2) ≠ 0 →
      OffOrbit t (u ^ (2 * 2)) ∧ ∃ hum : OffOrbit t (u ^ 2), ∀ a : TateRing t,
        HasTateValue t h12 (algebraMap _ (TateField t) (mulByNHom t.tateCurve 2 a)) hu
          (evalTate t h12 hum a) := by
    intro u hu h0
    rw [map_mul] at h0
    exact ⟨(hasTateValue_mulByNHom (h12 := h12) 4 h2 hu (left_ne_zero_of_mul h0)).1,
      hasTateValue_mulByNHom (h12 := h12) 2 h2 hu (right_ne_zero_of_mul h0)⟩
  refine ⟨eq_of_hasTateValue (h12 := h12) hD₀ (G := fun u => t.X (u ^ 2))
      (fun u hu h0 => (hval u hu (good u hu h0).1).1) (fun u hu h0 => ?_),
    eq_of_hasTateValue (h12 := h12) hD₀ (G := fun u => t.Y (u ^ 2))
      (fun u hu h0 => (hval u hu (good u hu h0).1).2.1) (fun u hu h0 => ?_)⟩
  · obtain ⟨hum, hv⟩ := (good u hu h0).2
    rw [← algebraMap_mulByNHom_eq_pb]
    refine (hv _).congr ?_
    change evalTate t h12 hum (mkT t (C X)) = _
    rw [evalTate_mk_C, eval_X]
  · obtain ⟨hum, hv⟩ := (good u hu h0).2
    rw [← algebraMap_mulByNHom_eq_pb]
    refine (hv _).congr ?_
    change evalTate t h12 hum (mkT t X) = _
    rw [evalTate_mk_Y]

/-- `σ` moves `x` by an `l`-th power of `d·y`, `d ∈ K` (the field of constants), `y ∈ L'`:
`σ x = (d·y)^l·x` ([EtTh] Prop. 1.5(iii) mod `l`, the conclusion of `transHom_level_pow_mul`). -/
def MovesByPow {B : Type*} [Field B] [Algebra B Ω] (L' : IntermediateField B Ω) (σ : Ω → Ω)
    (x : Ω) (l : ℕ) : Prop :=
  ∃ (d : K), ∃ y ∈ L', σ x = (algebraMap K Ω d * y) ^ l * x

set_option maxHeartbeats 1000000 in
-- the system now carries the translation homomorphisms of all levels (run 17)
/-- **The étale theta classes form a projective system** (module docstring of
`ThetaClassSystem.lean`), **with cusp inertia and the translation formula**: at every level `j`,
every place `W ⊇ K` of `Ω`
with `τ ∉ W` (a cusp of `Ÿ'_{N_j}`) and every `n ∣ N_j`, `κ_n(η_j)` restricted to `I_W ∩ H` is
the tame character of `W` (`CuspTameAt`, `cuspTameAt_level`); and every `σ ∈ Gal(Ω/L_X)`
multiplies `η_j` by `c·h^n` with `c ∈ K`, `h ∈ L_{2N_j}` (`translation_level`, (F2) of
`ThetaKerTheta.lean`). -/
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
      (∀ (j : ℕ) (u : Kˣ) (hu : OffOrbit t u)
        (hψ : evalTate t h12 hu (psiN t.tateCurve (2 * (2 * (j + 1)))) ≠ 0),
        ThetaValueAt h12 (2 * (j + 1)) (by omega) (L j) (hL j) (η j) u hu hψ) ∧
      (∀ j, ∃ σ : Ω ≃ₐ[K₀ K τ] Ω,
        (∀ g : TateField t, σ (mulByNEmb t.tateCurve (2 * (2 * (j + 1))) g) =
          mulByNEmb t.tateCurve (2 * (2 * (j + 1))) (negE t.tateCurve g)) ∧
        InversionAt (transcendental_tau t.tateCurve) (hL j) (η j) σ) ∧
      (∀ j j' M : ℕ, 2 * (j' + 1) = 2 * (j + 1) * M → Even M →
        LevelTransition (transcendental_tau t.tateCurve) (hL j) (hL j') (η j) (η j')
          (2 * (j + 1))) ∧
      (∀ (j : ℕ) (W : ValuationSubring Ω) (hk : ∀ c : K, algebraMap K Ω c ∈ W), τ ∉ W →
        ∀ (n : ℕ) [NeZero n], n ∣ 2 * (j + 1) →
          CuspTameAt (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)) (η j) W hk n) ∧
      (∀ (j n : ℕ), n ∣ 2 * (j + 1) →
        L j ≤ mulByNField t.tateCurve (2 * (2 * (j + 1))) ∧
        ∀ σ : Ω ≃ₐ[K₀ K τ] Ω, (∀ z ∈ (hemiData t.tateCurve).L, σ z = z) →
          ∃ (c : K), ∃ h ∈ mulByNField t.tateCurve (2 * (2 * (j + 1))),
            σ ((((η j : (F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
                F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))) : Ω)) =
              algebraMap K Ω c * h ^ n *
                (((η j : (F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
                  F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))) : Ω)) ∧
      L 0 ≤ mulByNField t.tateCurve 2 ∧
      (∀ j, L j ≤ L 0 ⊔ levelQN h2 h12 hs j) ∧
      ∃ w : ∀ j, (hemiData t.tateCurve).L.fixingSubgroup →*
          Kˣ ⧸ (sqrtPow hs (2 * (j + 1)) (by omega)).qpowers,
        (∀ j (σ : (hemiData t.tateCurve).L.fixingSubgroup),
          (∀ z ∈ L j, (σ : Ω ≃ₐ[K₀ K τ] Ω) z = z) → w j σ = 1) ∧
        (∀ j, ∀ σ ∈ (hemiData t.tateCurve).L.fixingSubgroup, ∀ x ∈ L j, σ x ∈ L j) ∧
        (∀ (j l : ℕ), Odd l → l ∣ 2 * (j + 1) →
          ∀ σ ρ : (hemiData t.tateCurve).L.fixingSubgroup, w j σ = w j ρ ^ l →
            ∃ (d : K), ∃ y ∈ L j,
              (σ : Ω ≃ₐ[K₀ K τ] Ω)
                  (((η j : (F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
                    F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))) : Ω) =
                (algebraMap K Ω d * y) ^ l *
                  (((η j : (F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
                    F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))) : Ω)) ∧
        ∀ (j l : ℕ), Odd l → 2 * l ∣ 2 * (j + 1) →
          ∀ σ ρ τ' : (hemiData t.tateCurve).L.fixingSubgroup, w j σ = w j ρ ^ l * w j τ' →
            w j τ' ^ 2 = 1 →
            MovesByPow (L j) (σ : Ω ≃ₐ[K₀ K τ] Ω)
              (((η j : (F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
                F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))) : Ω) l := by
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
  -- the translation homomorphisms and [EtTh] Prop. 1.5(iii) mod `l` (run 17)
  have hW : ∃ w : ∀ j, (hemiData t.tateCurve).L.fixingSubgroup →*
        Kˣ ⧸ (sqrtPow hs (2 * (j + 1)) (by omega)).qpowers,
      (∀ j (σ : (hemiData t.tateCurve).L.fixingSubgroup),
        (∀ z ∈ L j, (σ : Ω ≃ₐ[K₀ K τ] Ω) z = z) → w j σ = 1) ∧
      (∀ j, ∀ σ ∈ (hemiData t.tateCurve).L.fixingSubgroup, ∀ x ∈ L j, σ x ∈ L j) ∧
      (∀ (j l : ℕ), Odd l → l ∣ 2 * (j + 1) →
        ∀ σ ρ : (hemiData t.tateCurve).L.fixingSubgroup, w j σ = w j ρ ^ l →
          ∃ (d : K), ∃ y ∈ L j,
            (σ : Ω ≃ₐ[K₀ K τ] Ω)
                (((η j : (KummerTheory.Curve.F
                  (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
                  KummerTheory.Curve.F (fieldData (transcendental_tau t.tateCurve) (L j)
                    (hL j))) : Ω) =
              (algebraMap K Ω d * y) ^ l *
                (((η j : (KummerTheory.Curve.F
                  (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
                  KummerTheory.Curve.F (fieldData (transcendental_tau t.tateCurve) (L j)
                    (hL j))) : Ω)) ∧
      ∀ (j l : ℕ), Odd l → 2 * l ∣ 2 * (j + 1) →
        ∀ σ ρ τ' : (hemiData t.tateCurve).L.fixingSubgroup, w j σ = w j ρ ^ l * w j τ' →
          w j τ' ^ 2 = 1 →
          MovesByPow (L j) (σ : Ω ≃ₐ[K₀ K τ] Ω)
            (((η j : (KummerTheory.Curve.F
              (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
              KummerTheory.Curve.F (fieldData (transcendental_tau t.tateCurve) (L j)
                (hL j))) : Ω) l := by
    have hW' : ∀ j, ∃ w : (hemiData t.tateCurve).L.fixingSubgroup →*
          Kˣ ⧸ (sqrtPow hs (2 * (j + 1)) (by omega)).qpowers,
        (∀ σ : (hemiData t.tateCurve).L.fixingSubgroup,
          (∀ z ∈ L j, (σ : Ω ≃ₐ[K₀ K τ] Ω) z = z) → w σ = 1) ∧
        (∀ σ ∈ (hemiData t.tateCurve).L.fixingSubgroup, ∀ x ∈ L j, σ x ∈ L j) ∧
        (∀ l : ℕ, Odd l → l ∣ 2 * (j + 1) →
          ∀ σ ρ : (hemiData t.tateCurve).L.fixingSubgroup, w σ = w ρ ^ l →
            ∃ (d : K), ∃ y ∈ L j,
              (σ : Ω ≃ₐ[K₀ K τ] Ω)
                  (((η j : (KummerTheory.Curve.F
                    (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
                    KummerTheory.Curve.F (fieldData (transcendental_tau t.tateCurve) (L j)
                      (hL j))) : Ω) =
                (algebraMap K Ω d * y) ^ l *
                  (((η j : (KummerTheory.Curve.F
                    (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
                    KummerTheory.Curve.F (fieldData (transcendental_tau t.tateCurve) (L j)
                      (hL j))) : Ω)) ∧
        ∀ l : ℕ, Odd l → 2 * l ∣ 2 * (j + 1) →
          ∀ σ ρ τ' : (hemiData t.tateCurve).L.fixingSubgroup, w σ = w ρ ^ l * w τ' →
            w τ' ^ 2 = 1 →
            MovesByPow (L j) (σ : Ω ≃ₐ[K₀ K τ] Ω)
              (((η j : (KummerTheory.Curve.F
                (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
                KummerTheory.Curve.F (fieldData (transcendental_tau t.tateCurve) (L j)
                  (hL j))) : Ω) l := by
      intro j
      have hNj : 0 < 2 * (j + 1) := by omega
      have hev : Even (2 * (j + 1)) := ⟨j + 1, by ring⟩
      haveI : (sqrtPow hs (2 * (j + 1)) hNj).tateCurve.IsElliptic :=
        (sqrtPow hs (2 * (j + 1)) hNj).tateCurve_isElliptic h12
      haveI : NeZero (2 * (2 * (j + 1))) := ⟨by omega⟩
      obtain ⟨hpt', htr, f, hfv, hjf, hidx⟩ := exists_levelEmb (N := 2 * (j + 1)) h2 h12 hs
        hNj hev (hmul j) (hval j)
      have hidx' := fun σ hσ => hidx σ ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ)
      refine ⟨transHom rfl hNj h12 h2 _ _ hidx', fun σ hσ => ?_, fun σ hσ x hx => ?_,
        fun l hl hlN σ ρ h => ?_, fun l hl hlN σ ρ τ' h hτ' => ?_⟩
      · exact transHom_level_eq_one h2 h12 hs hNj hpt' htr _ σ hσ
      · exact level_stable h12 hs hNj hpt' htr hidx' σ hσ hx
      · obtain ⟨d, y, hy, e⟩ := transHom_level_pow h2 h12 hs hNj hpt' htr _
          hev hfv hl hlN σ ρ h
        refine ⟨d, y, hy, ?_⟩
        have hιf : ((mulByNEmb t.tateCurve (2 * (2 * (j + 1)))).comp
            (pullbackT (gX j) (gY j) hpt' htr)) f =
              mulByNEmb t.tateCurve (2 * (2 * (j + 1))) (F j) := by
          rw [AlgHom.comp_apply, hjf]
        rw [hη j, ← hιf]
        exact e
      · unfold MovesByPow
        obtain ⟨d, y, hy, e⟩ := transHom_level_pow_mul h2 h12 hs hNj hpt' htr _
          hev hfv hl hlN σ ρ τ' h hτ'
        refine ⟨d, y, hy, ?_⟩
        have hιf : ((mulByNEmb t.tateCurve (2 * (2 * (j + 1)))).comp
            (pullbackT (gX j) (gY j) hpt' htr)) f =
              mulByNEmb t.tateCurve (2 * (2 * (j + 1))) (F j) := by
          rw [AlgHom.comp_apply, hjf]
        rw [hη j, ← hιf]
        exact e
    choose w hw1 hw2 hw3 hw4 using hW'
    exact ⟨w, hw1, hw2, hw3, hw4⟩
  -- `L_j ≤ L_0 ⊔ K(E_{q^{N_j}})` (TFGD run 3, `adjoin_levelCoords_le`)
  have hsup : ∀ j, L j ≤ L 0 ⊔ levelQN h2 h12 hs j := by
    intro j
    obtain ⟨e1, e2⟩ := eq_levelCoords h2 h12 hs j (gX := gX j) (gY := gY j)
      (fun u hu hum => ⟨(hval j u hu hum).1, (hval j u hu hum).2.1⟩)
    have hx0 : mulByNEmb t.tateCurve 2
        (algebraMap (TateRing t) (TateField t) (xE t.tateCurve)) ∈ L 0 := by
      obtain ⟨hgX, -⟩ := levelData_two_eq_pb h2 h12 hs (N := 2 * (0 + 1)) (by omega) rfl (hval 0)
      have hc : ∀ f, mulByNEmb t.tateCurve (2 * (2 * (0 + 1))) (pb t.tateCurve 2 f) =
          mulByNEmb t.tateCurve 2 f := fun f =>
        AlgHom.congr_fun (mulByNEmb_comp_pb_mul t.tateCurve 2 2) f
      have hm : mulByNEmb t.tateCurve (2 * (2 * (0 + 1))) (gX 0) ∈ L 0 :=
        IntermediateField.subset_adjoin _ _ ⟨gX 0, by simp, rfl⟩
      rwa [hgX, hc] at hm
    have h := adjoin_levelCoords_le h2 h12 hs j hx0
    rw [← e1, ← e2] at h
    exact h
  refine ⟨L, hL, fun j => hemiL_le_adjoin _ _ (hmul j), η,
    fun j => etale_adjoin_image _ _ (hmul j), fun j => ?_, fun j => ?_, fun j => ?_,
    fun j j' M hjM hevM => ?_, fun j W hk hτ n _ hn => ?_, fun j n hn =>
      ⟨adjoin_image_le_mulByNField _ _ _, fun σ hσ => ?_⟩, ?_, hsup, hW⟩
  · exact etaleThetaClass_points (by omega) (L j) (hL j) (adjoin_image_le_mulByNField _ _ _)
      (η j) ((hη j).trans (congrArg _ (hb j).symm)) (hpt j)
  · exact thetaValueAt_points (by omega) (L j) (hL j) (adjoin_image_le_mulByNField _ _ _)
      (η j) ((hη j).trans (congrArg _ (hb j).symm)) (hpt j)
  -- the inversion `ι` at the level `j` ([EtTh] Prop. 1.5(iii))
  · obtain ⟨σ, hσ⟩ := exists_negAut t.tateCurve (2 * (2 * (j + 1)))
    obtain ⟨hX, hY, hFneg⟩ := levelData_inv (h12 := h12) h2 hs (N := 2 * (j + 1)) (by omega)
      ⟨j + 1, by ring⟩ (hval j)
    have hσ' : ∀ g : TateField t, σ (mulByNEmb t.tateCurve (2 * (2 * (j + 1))) g) =
        mulByNEmb t.tateCurve (2 * (2 * (j + 1))) (negT t g) := hσ
    refine ⟨σ, hσ, inversionAt_of _ (hL j) (η j) σ (fun x hx => ?_) ?_⟩
    · have hle : (IntermediateField.adjoin (K₀ K τ)
          (mulByNEmb t.tateCurve (2 * (2 * (j + 1))) '' {gX j, gY j})).map
            (σ : Ω →ₐ[K₀ K τ] Ω) ≤ L j := by
        rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
        have hmX : mulByNEmb t.tateCurve (2 * (2 * (j + 1))) (gX j) ∈ L j :=
          IntermediateField.subset_adjoin _ _ ⟨gX j, by simp, rfl⟩
        have hmY : mulByNEmb t.tateCurve (2 * (2 * (j + 1))) (gY j) ∈ L j :=
          IntermediateField.subset_adjoin _ _ ⟨gY j, by simp, rfl⟩
        rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
        rcases hg with rfl | rfl
        · change σ _ ∈ L j
          rw [hσ', hX]
          exact hmX
        · change σ _ ∈ L j
          rw [hσ', hY, map_sub, map_neg]
          exact sub_mem (neg_mem hmY) hmX
      exact hle ⟨x, hx, rfl⟩
    · rw [hη j, hσ', hFneg, map_neg]
  rotate_left
  -- the cusps
  · haveI : NeZero (2 * (2 * (j + 1))) := ⟨by omega⟩
    exact cuspTameAt_level h2 h12 hs (by omega) ⟨j + 1, by ring⟩ (hmul j) (hval j) rfl (hL j)
      (η j) (hη j) W hk hτ n hn
  -- (F2), the translation formula ([EtTh] Prop. 1.4(ii) at the level)
  · haveI : NeZero (2 * (2 * (j + 1))) := ⟨by omega⟩
    rw [hη j]
    exact translation_level h2 h12 hs (by omega) ⟨j + 1, by ring⟩ (hmul j) (hval j) hn σ hσ
  -- `L 0` is the source of `[2]`
  · obtain ⟨hgX, hgY⟩ := levelData_two_eq_pb h2 h12 hs (N := 2 * (0 + 1)) (by omega) rfl (hval 0)
    have hc : ∀ f, mulByNEmb t.tateCurve (2 * (2 * (0 + 1))) (pb t.tateCurve 2 f) =
        mulByNEmb t.tateCurve 2 f := fun f =>
      AlgHom.congr_fun (mulByNEmb_comp_pb_mul t.tateCurve 2 2) f
    change IntermediateField.adjoin _ _ ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨g, hg, rfl⟩
    rcases hg with rfl | rfl
    · rw [hgX, hc]; exact ⟨_, rfl⟩
    · rw [hgY, hc]; exact ⟨_, rfl⟩
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

end System

end SystemVars

end Iut.EtaleTheta
