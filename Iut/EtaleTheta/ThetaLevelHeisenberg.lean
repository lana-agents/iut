/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaLevelEmbed
import Iut.EtaleTheta.ThetaTransFactor
import Iut.EtaleTheta.MulByNTorsion

/-!
# The translation formula (F2) at the levels `Ÿ'_N` (MR14, run 15)

For the level data of `exists_levelData` (`N` even, `Q = s^N`, `x_Q∘ψ, y_Q∘ψ, F_N ∈ K(E_q)`,
`ψ(u) = u^N`), the level `L = K(τ)(φ(x_Q∘ψ), φ(y_Q∘ψ)) ⊆ L_{2N}` (`φ = mulByNEmb (2N)`) and
the unit `η = φ(F_N)`:

* **`pullbackT_transT_level`** (the identity, by Tate values): for a kernel point
  `w = (-1)^e s^a ≠ 1` of `E_Q → E_q` and `n ∣ N`, `k = N/n`,
  `j(t_w^* f_N) = c_w · H_w^n · F_N` in `K(E_q)`, with `c_w = (-1)^e (-1)^a s^{-a²} ∈ K` and
  `H_w ∈ K(E_q)` of `exists_transFactor` (values `u^{-2ak}Θ̈_{q^N}(u^N)^k/Θ̈_{q^N}(w u^N)^k`);
  this is `Θ̈_q(wU) = (-1)^e(-1)^a s^{-a²} U^{-2a} Θ̈_q(U)` (`etaleTheta_zpow_sqrt_mul`,
  `etaleTheta_neg`) at `U = u^N`. Checked numerically before formalising (`MR14-plan.md`, run 15).
* **`translation_level`** ((F2) at one level): every `σ ∈ Gal(Ω/L_X)` acts on the level as one
  of the `2N` translations (`eq_baseAut_of_eq`, with `ι(R) = τ`, `ι(R_y) = y_X`), hence
  `σ(η) = c·h^n·η` with `c ∈ K` and `h = φ(H_w) ∈ L_{2N}`.
-/

open Polynomial

noncomputable section

universe u

namespace Iut.EtaleTheta

open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem etaleTheta_sign_pow (t : TateParameter K) (e : ℕ) (U : Kˣ) :
    etaleTheta t ((-1) ^ e * U) = (-1 : K) ^ e * etaleTheta t U := by
  induction e generalizing U with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, mul_assoc, ih, neg_one_mul, etaleTheta_neg, pow_succ]
    ring

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **The translation identity of the theta level function, on values.** -/
theorem thetaLevel_cuspElt_mul (t : TateParameter K) {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ}
    (hN : 0 < N) {n k : ℕ} (hkn : k * n = N) (e : Fin 2) (a : ℕ) (u : Kˣ)
    (h0 : etaleTheta (tatePow t N hN) (u ^ N) ≠ 0)
    (h1 : etaleTheta (tatePow t N hN) ((-1) ^ (e : ℕ) * s ^ a * u ^ N) ≠ 0) :
    thetaLevel t N hN (u ^ N * cuspElt s e a) =
      ((-1 : K) ^ (e : ℕ) * (-1) ^ a * (s : K) ^ (-((a : ℤ) ^ 2))) *
        ((u : K) ^ (-((2 * a * k : ℕ) : ℤ)) * etaleTheta (tatePow t N hN) (u ^ N) ^ k /
          etaleTheta (tatePow t N hN) ((-1) ^ (e : ℕ) * s ^ a * u ^ N) ^ k) ^ n *
        thetaLevel t N hN (u ^ N) := by
  have hw : u ^ N * cuspElt s e a = (-1) ^ (e : ℕ) * (s ^ (a : ℤ) * u ^ N) := by
    rw [cuspElt, zpow_natCast, mul_comm, mul_assoc]
  have hw' : (-1) ^ (e : ℕ) * s ^ a * u ^ N = (-1) ^ (e : ℕ) * (s ^ (a : ℤ) * u ^ N) := by
    rw [zpow_natCast, mul_assoc]
  have hU : ((u ^ N : Kˣ) : K) ^ (-2 * (a : ℤ)) =
      ((u : K) ^ (-((2 * a * k : ℕ) : ℤ))) ^ n := by
    rw [← zpow_natCast _ n, ← zpow_mul, Units.val_pow_eq_pow_val, ← zpow_natCast _ N,
      ← zpow_mul, ← hkn]
    congr 1
    push_cast
    ring
  rw [hw'] at h1 ⊢
  rw [hw, thetaLevel, thetaLevel, etaleTheta_sign_pow, etaleTheta_zpow_sqrt_mul t hs, thetaFactor,
    hU, div_pow, mul_pow, ← pow_mul, ← pow_mul, hkn, zpow_natCast]
  have hu : (u : K) ^ (-((2 * a * k : ℕ) : ℤ)) ≠ 0 := zpow_ne_zero _ u.ne_zero
  field_simp

/-! ### Off-orbit consequences of `u^{2N} ∉ qᶻ` at the kernel points -/

section OffOrbit

variable {t : TateParameter K} {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ} {u : Kˣ}
  (hum : OffOrbit t (u ^ (2 * N)))

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hum in
theorem pow_ne_q_zpow (z : ℤ) : ((u : K)) ^ (2 * N) ≠ (t.q : K) ^ z := by
  intro h
  apply hum (-z)
  rw [Units.val_pow_eq_pow_val, h, ← zpow_add₀ t.q.ne_zero, neg_add_cancel, zpow_zero]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs in
theorem sq_pow_mul_cuspElt (T : TateParameter K) (hT : T.q = s ^ N) (m : ℤ) (e : Fin 2) (a : ℕ)
    (σ : ℤ) :
    (((T.q : K) ^ m * (cuspElt s e a : K) ^ σ)) ^ 2 = (t.q : K) ^ (N * m + σ * a) := by
  obtain ⟨k, hk⟩ := cuspElt_sq (t := t) hs e a
  have hka : (t.q : K) ^ k = (t.q : K) ^ (a : ℤ) := by
    rw [← hk]
    have hsq : ((-1 : K) ^ (e : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    simp only [cuspElt, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      mul_pow, hsq, one_mul, zpow_natCast]
    rw [← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, hs]
  have hq : (t.q : K) ≠ 0 := t.q.ne_zero
  have hw : (cuspElt s e a : K) ^ 2 = (t.q : K) ^ (a : ℤ) := hk.trans hka
  have hT' : (T.q : K) ^ 2 = (t.q : K) ^ (N : ℤ) := by
    rw [hT, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, hs,
      zpow_natCast]
  have key : ∀ x y : K, (x ^ m * y ^ σ) ^ 2 = (x ^ 2) ^ m * (y ^ 2) ^ σ := fun x y => by
    rw [mul_pow, ← zpow_natCast (x ^ m) 2, ← zpow_natCast (y ^ σ) 2, ← zpow_mul x m,
      ← zpow_mul y σ, ← zpow_natCast x 2, ← zpow_natCast y 2, ← zpow_mul x, ← zpow_mul y,
      mul_comm m, mul_comm σ]
  rw [key, hT', hw, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hq]
  congr 1
  ring

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
include hs hum in
theorem offOrbit_pow_mul_cuspElt (T : TateParameter K) (hT : T.q = s ^ N) (e : Fin 2) (a : ℕ) :
    OffOrbit T (u ^ N * cuspElt s e a) := by
  intro m hm
  apply pow_ne_q_zpow hum (-(N * m + 1 * a))
  have h := sq_pow_mul_cuspElt hs T hT m e a 1
  have h1 : ((T.q : K) ^ m * ((u ^ N * cuspElt s e a : Kˣ) : K)) ^ 2 = 1 := by
    rw [hm, one_pow]
  have hu2 : ((u : K)) ^ (2 * N) * ((T.q : K) ^ m * (cuspElt s e a : K) ^ (1 : ℤ)) ^ 2 = 1 := by
    rw [zpow_one, ← h1]
    push_cast
    ring
  rw [h] at hu2
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_left hu2

omit [CharZero K] in
include hs hum in
theorem etaleTheta_pow_mul_cuspElt_ne_zero {N' : ℕ} (hN' : 0 < N') (hNN : N' = N) (e : Fin 2)
    (a : ℕ) : etaleTheta (tatePow t N' hN') (u ^ N * cuspElt s e a) ≠ 0 := by
  subst hNN
  rw [Ne, etaleTheta_eq_zero_iff]
  rintro ⟨m, hm⟩
  apply pow_ne_q_zpow hum (N' * m - a)
  obtain ⟨k, hk⟩ := cuspElt_sq (t := t) hs e a
  have hw : (cuspElt s e a : K) ^ 2 = (t.q : K) ^ (a : ℤ) := by
    rw [hk]
    have hsq : ((-1 : K) ^ (e : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    simp only [cuspElt, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      mul_pow, hsq, one_mul, zpow_natCast] at hk ⊢
    rw [← hk, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, hs]
  have hq : (t.q : K) ≠ 0 := t.q.ne_zero
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, tatePow_q] at hm
  rw [mul_pow, hw, ← pow_mul, mul_comm N' 2, ← zpow_natCast (t.q : K) N', ← zpow_mul] at hm
  rw [zpow_sub₀ hq, ← hm, mul_comm (2 : ℕ) N']
  field_simp

omit [CharZero K] in
include hs hum in
theorem X_pow_ne_X_cuspElt (h12 : (12 : K) ≠ 0) (h2 : ‖(2 : K)‖ = 1) (T : TateParameter K)
    (hT : T.q = s ^ N) (hv : OffOrbit T (u ^ N)) {e : Fin 2} {a : ℕ}
    (hw : OffOrbit T (cuspElt s e a)) : T.X (u ^ N) ≠ T.X (cuspElt s e a) := by
  intro hX
  have E1 := (WeierstrassCurve.Affine.equation_iff _ _).mp (tateEquation h12 hv)
  have E2 := (WeierstrassCurve.Affine.equation_iff _ _).mp (tateEquation h12 hw)
  simp only [tateCurve_a₁, tateCurve_a₂, tateCurve_a₃] at E1 E2
  rw [hX] at E1
  have hfac : (T.Y (u ^ N) - T.Y (cuspElt s e a)) *
      (T.Y (u ^ N) + T.Y (cuspElt s e a) + T.X (cuspElt s e a)) = 0 := by
    linear_combination E1 - E2
  have key : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∃ m : ℤ,
      ((u ^ N : Kˣ) : K) = (T.q : K) ^ m * (cuspElt s e a : K) ^ σ := by
    rcases mul_eq_zero.mp hfac with h | h
    · obtain ⟨m, hm⟩ := exists_zpow_of_coords_eq h12 h2 hv hw hX (sub_eq_zero.mp h)
      exact ⟨1, Or.inl rfl, m, by rw [zpow_one]; exact hm⟩
    · have hwi := offOrbit_inv T hw
      obtain ⟨m, hm⟩ := exists_zpow_of_coords_eq h12 h2 hv hwi (by rw [T.X_inv hw, hX])
        (by rw [T.Y_inv hw]; linear_combination h)
      exact ⟨-1, Or.inr rfl, m, by rw [hm, zpow_neg_one, Units.val_inv_eq_inv_val]⟩
  obtain ⟨σ, -, m, hm⟩ := key
  apply pow_ne_q_zpow hum (N * m + σ * a)
  rw [← sq_pow_mul_cuspElt hs T hT m e a σ, ← hm, Units.val_pow_eq_pow_val, ← pow_mul,
    mul_comm]

end OffOrbit

section Level

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer

variable {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

set_option maxHeartbeats 1000000 in
-- `eq_of_hasTateValue` with the pulled-back values of the level data is slow to elaborate
/-- **The translation identity in `K(E_q)`** (the source of `[2N]`): for the level data, the
pullback `j : K(E_Q) → K(E_q)` along `ψ(u) = u^N` (`j(x_Q) = x_Q∘ψ`), an element `f ∈ K(E_Q)`
with the values of `f_N`, a kernel point `w = (-1)^e s^a ≠ 1` and `n ∣ N`:
`j(t_w f) = c · H^n · F_N` with `c ∈ K`, `H ∈ K(E_q)`. -/
theorem pullbackT_transT_level (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ}
    (hs : s ^ 2 = t.q) {N : ℕ} (hN : 0 < N) [t.tateCurve.IsElliptic] [NeZero (2 * N)]
    {gX gY Fθ : TateField t}
    (hval : ∀ (u : Kˣ) (hu : OffOrbit t u), OffOrbit t (u ^ (2 * N)) →
      HasTateValue t h12 gX hu ((sqrtPow hs N hN).X (u ^ N)) ∧
      HasTateValue t h12 gY hu ((sqrtPow hs N hN).Y (u ^ N)) ∧
      HasTateValue t h12 Fθ hu (thetaLevel t N hN (u ^ N)))
    (hpt : IsTPoint (sqrtPow hs N hN) gX gY) (htr : Transcendental K gX)
    {f : TateField (sqrtPow hs N hN)}
    (hfv : ∀ (u : Kˣ) (hu : OffOrbit (sqrtPow hs N hN) u), etaleTheta (tatePow t N hN) u ≠ 0 →
      HasTateValue (sqrtPow hs N hN) h12 f hu (thetaLevel t N hN u))
    {n : ℕ} (hn : n ∣ N) (e : Fin 2) (a : Fin N) (h00 : (e, (a : ℕ)) ≠ (0, 0)) :
    ∃ (c : K) (H : TateField t),
      pullbackT gX gY hpt htr (transT h12 (offOrbit_cuspElt rfl hN a.2 h00) f) =
        algebraMap K _ c * H ^ n * Fθ := by
  obtain ⟨k, hk⟩ := hn
  have hkn : k * n = N := by rw [hk, mul_comm]
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk; omega
    · exact h
  have hε : (((-1 : Kˣ) ^ (e : ℕ) : Kˣ) : K) ^ 2 = 1 := by
    rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul]; simp
  obtain ⟨H, DH, hDH, hHv⟩ := exists_transFactor t h12 hs hN (sqrtPow hs N hN) rfl k hk0 hε a
  have hψ0 := psiN_ne_zero_of_neZero t.tateCurve (2 * N)
  set w := cuspElt s e (a : ℕ) with hwdef
  have hw : OffOrbit (sqrtPow hs N hN) w := offOrbit_cuspElt rfl hN a.2 h00
  refine ⟨(-1 : K) ^ (e : ℕ) * (-1) ^ (a : ℕ) * (s : K) ^ (-((a : ℤ) ^ 2)), H,
    eq_of_hasTateValue (h12 := h12) (mul_ne_zero hψ0 hDH)
      (G := fun u => thetaLevel t N hN (u ^ N * w)) (fun u hu h0 => ?_) (fun u hu h0 => ?_)⟩
  · rw [map_mul] at h0
    obtain ⟨hψ, -⟩ := mul_ne_zero_iff.mp h0
    obtain ⟨hum, -⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu hψ
    have hv : OffOrbit (sqrtPow hs N hN) (u ^ N) := offOrbit_sqrt_pow hs _ rfl hum
    obtain ⟨hX, hY, -⟩ := hval u hu hum
    have huw := offOrbit_pow_mul_cuspElt hs hum (sqrtPow hs N hN) rfl e a
    have hx := X_pow_ne_X_cuspElt hs hum h12 h2 (sqrtPow hs N hN) rfl hv hw
    exact hasTateValue_pullbackT hpt htr hv hX hY (hasTateValue_trans h2 hv hw huw hx f _
      (hfv _ huw (etaleTheta_pow_mul_cuspElt_ne_zero hs hum hN rfl e a)))
  · rw [map_mul] at h0
    obtain ⟨hψ, hD⟩ := mul_ne_zero_iff.mp h0
    obtain ⟨hum, -⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu hψ
    obtain ⟨-, -, hF⟩ := hval u hu hum
    obtain ⟨h1, hH⟩ := hHv u hu hD
    refine (((HasTateValue.const hu _).mul (hH.pow n)).mul hF).congr ?_
    exact (thetaLevel_cuspElt_mul t hs hN hkn e a u
      (etaleTheta_pow_ne_zero (offOrbit_tatePow hN hum))
      h1).symm

/-- **(F2) at one level**: every `σ ∈ Gal(Ω/L_X)` multiplies the theta level unit `η = φ(F_N)`
by `c·h^n` with `c ∈ K` and `h ∈ L_{2N}` (`n ∣ N`). -/
theorem translation_level (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)
    {N : ℕ} (hN : 0 < N) (hev : Even N) [t.tateCurve.IsElliptic] [NeZero (2 * N)]
    {gX gY Fθ : TateField t}
    (hmul : ∀ a : TateRing t, algebraMap _ (TateField t) (mulByNHom t.tateCurve (2 * N) a) ∈
      IntermediateField.adjoin K ({gX, gY} : Set (TateField t)))
    (hval : ∀ (u : Kˣ) (hu : OffOrbit t u), OffOrbit t (u ^ (2 * N)) →
      HasTateValue t h12 gX hu ((sqrtPow hs N hN).X (u ^ N)) ∧
      HasTateValue t h12 gY hu ((sqrtPow hs N hN).Y (u ^ N)) ∧
      HasTateValue t h12 Fθ hu (thetaLevel t N hN (u ^ N)))
    {n : ℕ} (hn : n ∣ N) (σ : Ω ≃ₐ[K₀ K τ] Ω)
    (hσ : ∀ z ∈ (hemiData t.tateCurve).L, σ z = z) :
    ∃ (c : K), ∃ h ∈ mulByNField t.tateCurve (2 * N),
      σ (mulByNEmb t.tateCurve (2 * N) Fθ) =
        algebraMap K Ω c * h ^ n * mulByNEmb t.tateCurve (2 * N) Fθ := by
  set T := sqrtPow hs N hN with hTdef
  haveI : T.tateCurve.IsElliptic := T.tateCurve_isElliptic h12
  have hN2 : 2 ≤ N := by obtain ⟨r, hr⟩ := hev; omega
  have hψ0 := psiN_ne_zero_of_neZero t.tateCurve (2 * N)
  have hpts : ∀ (u : Kˣ) (hu : OffOrbit t u),
      evalTate t h12 hu (psiN t.tateCurve (2 * N)) ≠ 0 → OffOrbit t (u ^ (2 * N)) :=
    fun u hu hψ => (hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu hψ).1
  have hpt : IsTPoint T gX gY := isTPoint_of_values (h12 := h12) hψ0 (fun u => u ^ N)
    fun u hu hψ => ⟨offOrbit_sqrt_pow hs T rfl (hpts u hu hψ), (hval u hu (hpts u hu hψ)).1,
      (hval u hu (hpts u hu hψ)).2.1⟩
  set Rt : TateField t := algebraMap (coverRingN t.tateCurve (2 * N)) (TateField t)
    (mulByNHom t.tateCurve (2 * N) (xE t.tateCurve)) with hRtdef
  have hRt : mulByNEmb t.tateCurve (2 * N) Rt = τ := tau_eq t.tateCurve (2 * N)
  have htrR : Transcendental K Rt := fun h =>
    transcendental_tau t.tateCurve (hRt ▸ h.algHom (mulByNEmb t.tateCurve (2 * N)))
  have htr : Transcendental K gX := transcendental_of_mem_adjoin gX gY hpt (hmul _) htrR
  set j := pullbackT gX gY hpt htr with hjdef
  set ι : TateField T →ₐ[K] Ω := (mulByNEmb t.tateCurve (2 * N)).comp j with hιdef
  obtain ⟨f, -, hfv, -, -⟩ := thetaLevel_cusp_orders t h12 h2 hs hN hN2 hev T rfl
  have htrans : ∀ (u : Kˣ) (hu : OffOrbit t u) (hum : OffOrbit t (u ^ (2 * N)))
      {g : TateField T} {c : K}, HasTateValue T h12 g (offOrbit_sqrt_pow hs T rfl hum) c →
      HasTateValue t h12 (j g) hu c := fun u hu hum _ _ hg =>
    hasTateValue_pullbackT hpt htr _ (hval u hu hum).1 (hval u hu hum).2.1 hg
  have hjf : j f = Fθ := eq_of_hasTateValue (h12 := h12) hψ0
    (G := fun u => thetaLevel t N hN (u ^ N))
    (fun u hu hψ => htrans u hu (hpts u hu hψ)
      (hfv _ _ (etaleTheta_pow_ne_zero (offOrbit_tatePow hN (hpts u hu hψ)))))
    (fun u hu hψ => (hval u hu (hpts u hu hψ)).2.2)
  obtain ⟨A₁, B₁, A₂, B₂, e₁, e₁', e₂, e₂', hR⟩ := exists_poly_isogenyX_deg t h12 hs hN T rfl
  obtain ⟨C₁, E₁, C₂, E₂, hRy⟩ := exists_poly_isogenyY t hs hN T rfl h12 hev
  set R := algebraMap _ (TateField T) (polyXY T A₁ B₁) /
    algebraMap _ (TateField T) (polyXY T A₂ B₂) with hRdef
  set Ry := algebraMap _ (TateField T) (polyXY T C₁ E₁) /
    algebraMap _ (TateField T) (polyXY T C₂ E₂) with hRydef
  have hjR : j R = Rt := by
    refine eq_of_hasTateValue (h12 := h12) hψ0 (G := fun u => t.X (u ^ (2 * N)))
      (fun u hu hψ => ?_) (fun u hu hψ => ?_)
    · have hum := hpts u hu hψ
      have e : (u ^ N) ^ 2 = u ^ (2 * N) := by rw [← pow_mul, mul_comm]
      have hum2 : OffOrbit t ((u ^ N) ^ 2) := by rw [e]; exact hum
      exact (htrans u hu hum (hasTateValue_R hR _ hum2)).congr (by rw [e])
    · obtain ⟨hum, hv⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu hψ
      exact (hv (xE t.tateCurve)).congr (by
        rw [show xE t.tateCurve = mkT t (C X) from rfl, evalTate_mk_C, eval_X])
  set Ryt : TateField t := algebraMap (coverRingN t.tateCurve (2 * N)) (TateField t)
    (mulByNHom t.tateCurve (2 * N) (yE t.tateCurve)) with hRytdef
  have hjRy : j Ry = Ryt := by
    refine eq_of_hasTateValue (h12 := h12) hψ0 (G := fun u => t.Y (u ^ (2 * N)))
      (fun u hu hψ => ?_) (fun u hu hψ => ?_)
    · have hum := hpts u hu hψ
      have e : (u ^ N) ^ 2 = u ^ (2 * N) := by rw [← pow_mul, mul_comm]
      have hum2 : OffOrbit t ((u ^ N) ^ 2) := by rw [e]; exact hum
      exact (htrans u hu hum (hasTateValue_Ry h12 hRy _ hum2)).congr (by rw [e])
    · obtain ⟨hum, hv⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu hψ
      exact (hv (yE t.tateCurve)).congr (by
        rw [show yE t.tateCurve = mkT t Polynomial.X from rfl, evalTate_mk_Y])
  have hιR : ι R = τ := by rw [hιdef, AlgHom.comp_apply, hjR, hRt]
  have hιRy : ι Ry = embE t.tateCurve (CoordinateRing.genY _) := by
    rw [hιdef, AlgHom.comp_apply, hjRy, hRytdef, mulByNEmb_mulByNHom]
    rfl
  have hτL : τ ∈ (hemiData t.tateCurve).L :=
    (mem_hemiL_iff _ _).mpr ⟨CoordinateRing.genX _, embE_genX t.tateCurve⟩
  have hyL : ι Ry ∈ (hemiData t.tateCurve).L := (mem_hemiL_iff _ _).mpr ⟨_, hιRy.symm⟩
  have hψ : 2 * ι Ry + ι R ≠ 0 := by
    rw [hιRy, hιR, ← embE_genX t.tateCurve]
    have h := psiTwo_gen_ne_zero (W := t.tateCurve.toAffine) (two_ne_zero_of_norm h2)
    simp only [tateCurve_a₁, tateCurve_a₃, map_one, map_zero, one_mul, add_zero] at h
    intro h0
    apply h
    apply (map_eq_zero_iff (embE t.tateCurve) (embE t.tateCurve).toRingHom.injective).mp
    simpa only [map_add, map_mul, map_ofNat] using h0
  set ρ : TateField T →ₐ[K] Ω := ((σ : Ω →ₐ[K₀ K τ] Ω).restrictScalars K).comp ι with hρdef
  have hρR : ρ R = ι R := by
    rw [hρdef, AlgHom.comp_apply, hιR]
    exact hσ _ hτL
  have hρRy : ρ Ry = ι Ry := by
    rw [hρdef, AlgHom.comp_apply]
    exact hσ _ hyL
  obtain ⟨e, a, hρ⟩ := eq_baseAut_of_eq (rfl : T.q = s ^ N) hN h12 hs hR hRy h2 e₁ e₁' e₂ e₂'
    ι ρ (by rw [hιR]; exact transcendental_tau t.tateCurve) hρR hρRy hψ
  have hιf : mulByNEmb t.tateCurve (2 * N) Fθ = ι f := by
    rw [hιdef, AlgHom.comp_apply, hjf]
  have key : σ (ι f) = ι (baseAut (rfl : T.q = s ^ N) hN h12 e a f) := by
    have := congrArg (fun g : TateField T →ₐ[K] Ω => g f) hρ
    simpa only [hρdef, AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgHom.coe_coe,
      AlgEquiv.coe_toAlgHom] using this
  rw [hιf, key]
  by_cases h00 : (e, (a : ℕ)) = (0, 0)
  · refine ⟨1, 1, one_mem _, ?_⟩
    rw [baseAut, dif_pos h00]
    simp
  · obtain ⟨c, H, hH⟩ := pullbackT_transT_level h2 h12 hs hN hval hpt htr hfv hn e a h00
    refine ⟨c, mulByNEmb t.tateCurve (2 * N) H, ⟨H, rfl⟩, ?_⟩
    rw [baseAut, dif_neg h00]
    rw [hιdef, AlgHom.comp_apply, AlgHom.comp_apply, hH, hjf, map_mul, map_mul, map_pow,
      AlgHom.commutes]

end Level

section System

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer

variable {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

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
      ∀ (j n : ℕ), n ∣ 2 * (j + 1) →
        L j ≤ mulByNField t.tateCurve (2 * (2 * (j + 1))) ∧
        ∀ σ : Ω ≃ₐ[K₀ K τ] Ω, (∀ z ∈ (hemiData t.tateCurve).L, σ z = z) →
          ∃ (c : K), ∃ h ∈ mulByNField t.tateCurve (2 * (2 * (j + 1))),
            σ ((((η j : (F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
                F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))) : Ω)) =
              algebraMap K Ω c * h ^ n *
                (((η j : (F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
                  F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))) : Ω) := by
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
    fun j => etale_adjoin_image _ _ (hmul j), fun j => ?_, fun j => ?_, fun j => ?_,
    fun j j' M hjM hevM => ?_, fun j W hk hτ n _ hn => ?_, fun j n hn =>
      ⟨adjoin_image_le_mulByNField _ _ _, fun σ hσ => ?_⟩⟩
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

end Iut.EtaleTheta
