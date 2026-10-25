/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaPullback

/-!
# The isogeny `φ : E_Q → E_q`, `Ü ↦ Ü²`, in Tate coordinates (MR14, task G1a)

Let `s² = q`, `N` even, `Q = s^N`. The level `Ÿ'_N = E_Q ∖ C_N` maps to `X = E_q ∖ {O}` by
`φ(Ü) = Ü²` ([EtTh], §1: `Ü² = U`). Here we show that `φ` is algebraic: the coordinates
`X_q(Ü²)`, `Y_q(Ü²)` are rational functions of `X_Q(Ü)`, `Y_Q(Ü)`
(`exists_poly_isogenyX`, `exists_poly_isogenyY`), by the same engine as for the theta level
functions: `Ü^{-a}·(X_q θ_q(-·)²)(Ü²)` and `Ü^{-a}·θ_q(-Ü²)²` are weight-`4N` theta families for the
lattice `Q^ℤ` with the multiplier of `θ_Q(-Ü)^{4N}` (`isWeightFamily_pullIter`: pulling back along
`Ü ↦ Ü^m` from a lattice `q₁^ℤ` to a lattice `q₂^ℤ` with `q₂^m = q₁^r`).

Composed with `ψ(u) = u^N` (`ThetaPullback.lean`) this gives the inclusion
`[2N]^* K(E_q) ⊆ ψ^* K(E_Q)` of function fields, `φ ∘ ψ = [2N]`.
-/

open Polynomial

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **Iterated functional equation**: `G(q^r w) = A^r q^{-k·C(r,2)} w^{-kr} G(w)`. -/
theorem tsum_iter_q_smul {T : TateParameter K} {k : ℕ} {A : Kˣ} {c : ℤ → K}
    (hc : T.IsWeightFamily k A c) (w : Kˣ) :
    ∀ r : ℕ, (∑' n : ℤ, c n * ((T.q ^ r * w : Kˣ) : K) ^ n) =
      (A : K) ^ r * ((T.q : K) ^ (k * r.choose 2))⁻¹ * ((w : K) ^ (k * r))⁻¹ *
        ∑' n : ℤ, c n * (w : K) ^ n
  | 0 => by simp
  | r + 1 => by
    have hq : (T.q : K) ≠ 0 := T.q.ne_zero
    have hw : (w : K) ≠ 0 := w.ne_zero
    have e : ((T.q ^ (r + 1) * w : Kˣ) : K) = (T.q : K) * ((T.q ^ r * w : Kˣ) : K) := by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]; ring
    rw [e, hc.tsum_q_smul, tsum_iter_q_smul hc w r, Nat.choose_succ_succ, Nat.choose_one_right]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, zpow_neg, zpow_natCast]
    field_simp
    ring

/-- **Pulling back theta families along `u ↦ u^m`** from the lattice `q₁^ℤ` to the lattice
`q₂^ℤ`, where `q₂^m = q₁^r`: `u ↦ u^{-a}·G(u^m)` is a weight-`krm` family with multiplier
`q₂^{-a}·A^r·q₁^{-k·C(r,2)}`. -/
theorem isWeightFamily_pullIter {T₁ T₂ : TateParameter K} {m r : ℕ} (hm : 0 < m)
    (hmr : T₂.q ^ m = T₁.q ^ r) {k : ℕ} {A : Kˣ} {c : ℤ → K} (hc : T₁.IsWeightFamily k A c)
    (a : ℤ) :
    T₂.IsWeightFamily (k * r * m) ((T₂.q ^ a)⁻¹ * A ^ r * (T₁.q ^ (k * r.choose 2))⁻¹)
      (pullCoef c m a) := by
  refine IsWeightFamily.of_tsum_q_smul (fun u => (hasSum_pullCoef hc hm a u).summable)
    fun u => ?_
  have hu : (u : K) ≠ 0 := u.ne_zero
  have hq₁ : (T₁.q : K) ≠ 0 := T₁.q.ne_zero
  have hq₂ : (T₂.q : K) ≠ 0 := T₂.q.ne_zero
  have hpow : (T₂.q * u) ^ m = T₁.q ^ r * u ^ m := by rw [mul_pow, hmr]
  have hqu : (T₂.q : K) * (u : K) = ((T₂.q * u : Kˣ) : K) := by rw [Units.val_mul]
  rw [hqu, (hasSum_pullCoef hc hm a _).tsum_eq, (hasSum_pullCoef hc hm a u).tsum_eq, hpow,
    tsum_iter_q_smul hc]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
    Units.val_zpow_eq_zpow_val, zpow_neg, zpow_natCast, mul_zpow, mul_inv]
  rw [show (u : K) ^ (k * r * m) = ((u : K) ^ m) ^ (k * r) by
    rw [← pow_mul]; ring_nf]
  field_simp

variable (t : TateParameter K) {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ} (hN : 0 < N)
  (T : TateParameter K) (hT : T.q = s ^ N)

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs hT in
theorem isogeny_lattice : T.q ^ 2 = t.q ^ N := by
  rw [hT, ← hs, ← pow_mul, ← pow_mul, mul_comm]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem two_mul_choose_two (M : ℕ) : 2 * (M + 1).choose 2 = (M + 1) * M := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  exact Nat.two_mul_div_two_of_even (by simpa using Nat.even_mul_pred_self (M + 1))

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs hN hT in
theorem isogenyMult_X :
    (T.q ^ ((2 * N - 2 : ℕ) : ℤ))⁻¹ * ((t.q * (-1))⁻¹ ^ 2) ^ N * (t.q ^ (2 * N.choose 2))⁻¹ =
      multθ T ^ (2 * N * 2) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [two_mul_choose_two, show 2 * (M + 1) - 2 = 2 * M by omega, hT, ← hs]
  ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, zpow_natCast]
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hQ : (T.q : K) = (s : K) ^ (M + 1) := by rw [hT, Units.val_pow_eq_pow_val]
  rw [inv_pow, inv_pow, mul_pow (_ : K) (-1) 2, neg_one_sq, mul_one, inv_pow,
    mul_pow (_ : K) (-1), Even.neg_one_pow ⟨(M + 1) * 2, by ring⟩, mul_one]
  rw [hQ]
  field_simp
  ring

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs hN hT in
theorem isogenyMult_Y (hev : Even N) :
    (T.q ^ ((3 * N - 3 : ℕ) : ℤ))⁻¹ * ((t.q * (-1))⁻¹ ^ 3) ^ N * (t.q ^ (3 * N.choose 2))⁻¹ =
      multθ T ^ (3 * N * 2) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [show 3 * (M + 1) - 3 = 3 * M by omega, hT, ← hs]
  ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, zpow_natCast]
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hQ : (T.q : K) = (s : K) ^ (M + 1) := by rw [hT, Units.val_pow_eq_pow_val]
  have hC : ((s : K) ^ 2) ^ (3 * (M + 1).choose 2) = (s : K) ^ (3 * ((M + 1) * M)) := by
    rw [← pow_mul, ← two_mul_choose_two]; ring_nf
  rw [hC, inv_pow, inv_pow, mul_pow (_ : K) (-1) 3,
    show ((-1 : K)) ^ 3 = -1 by norm_num, mul_neg_one, Even.neg_pow hev, inv_pow,
    mul_pow (_ : K) (-1), Even.neg_one_pow ⟨3 * (M + 1), by ring⟩, mul_one, hQ]
  field_simp
  ring

variable (h12 : (12 : K) ≠ 0)

include hs hN hT h12 in
/-- **The isogeny `φ(Ü) = Ü²` in Tate coordinates, `x`-coordinate**: `X_q(Ü²)` is a rational
function of `X_Q(Ü)`, `Y_Q(Ü)` (wherever `θ_q(-Ü²) ≠ 0`, i.e. `Ü ∉ C_N`). -/
theorem exists_poly_isogenyX :
    ∃ P₁ Q₁ P₂ Q₂ : K[X], ∀ v : Kˣ, OffOrbit T v → t.theta (-(v ^ 2)) ≠ 0 →
      P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v) ≠ 0 ∧
      t.X (v ^ 2) = (P₁.eval (T.X v) + T.Y v * Q₁.eval (T.X v)) /
        (P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v)) := by
  have hlat := isogeny_lattice t hs T hT
  have h1 := isWeightFamily_pullIter (m := 2) two_pos hlat (isWeightFamily_XThetaSq t)
    ((2 * N - 2 : ℕ) : ℤ)
  rw [isogenyMult_X t hs hN T hT] at h1
  have h2 := isWeightFamily_pullIter (m := 2) two_pos hlat
    (isWeightFamily_cpow t (isWeightFamily_thetaBlock (t := t) (-1)) 2) ((2 * N - 2 : ℕ) : ℤ)
  rw [one_mul, isogenyMult_X t hs hN T hT] at h2
  obtain ⟨P₁, Q₁, e₁⟩ := exists_poly_of_isWeightFamily T h12 (by positivity) h1
  obtain ⟨P₂, Q₂, e₂⟩ := exists_poly_of_isWeightFamily T h12 (by positivity) h2
  refine ⟨P₁, Q₁, P₂, Q₂, fun v hv hθ => ?_⟩
  have f₁ := e₁ v hv
  have f₂ := e₂ v hv
  rw [(hasSum_pullCoef (isWeightFamily_XThetaSq t) two_pos _ v).tsum_eq,
    (t.hasSum_XThetaSqCoeff (offOrbit_of_theta_ne_zero hθ)).tsum_eq] at f₁
  rw [tsum_pull_theta two_pos 2 v] at f₂
  have hv0 : (v : K) ^ (-((2 * N - 2 : ℕ) : ℤ)) ≠ 0 := zpow_ne_zero _ v.ne_zero
  have hθT : T.theta (-v) ^ (2 * N * 2) ≠ 0 := pow_ne_zero _ (theta_neg_ne_zero T hv)
  have hden : P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at f₂
    exact mul_ne_zero hv0 (pow_ne_zero _ hθ) f₂
  refine ⟨hden, ?_⟩
  rw [eq_div_iff hden]
  apply mul_left_cancel₀ (mul_ne_zero hv0 (mul_ne_zero (pow_ne_zero 2 hθ) hθT))
  linear_combination
    (T.theta (-v) ^ (2 * N * 2) * (P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v))) * f₁ -
    ((P₁.eval (T.X v) + T.Y v * Q₁.eval (T.X v)) * T.theta (-v) ^ (2 * N * 2)) * f₂

include hs hN hT h12 in
/-- **The isogeny `φ(Ü) = Ü²` in Tate coordinates, `y`-coordinate** (`N` even). -/
theorem exists_poly_isogenyY (hev : Even N) :
    ∃ P₁ Q₁ P₂ Q₂ : K[X], ∀ v : Kˣ, OffOrbit T v → t.theta (-(v ^ 2)) ≠ 0 →
      P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v) ≠ 0 ∧
      t.Y (v ^ 2) = (P₁.eval (T.X v) + T.Y v * Q₁.eval (T.X v)) /
        (P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v)) := by
  have hlat := isogeny_lattice t hs T hT
  have h1 := isWeightFamily_pullIter (m := 2) two_pos hlat (isWeightFamily_YThetaCube t)
    ((3 * N - 3 : ℕ) : ℤ)
  rw [isogenyMult_Y t hs hN T hT hev] at h1
  have h2 := isWeightFamily_pullIter (m := 2) two_pos hlat
    (isWeightFamily_cpow t (isWeightFamily_thetaBlock (t := t) (-1)) 3) ((3 * N - 3 : ℕ) : ℤ)
  rw [one_mul, isogenyMult_Y t hs hN T hT hev] at h2
  obtain ⟨P₁, Q₁, e₁⟩ := exists_poly_of_isWeightFamily T h12 (by positivity) h1
  obtain ⟨P₂, Q₂, e₂⟩ := exists_poly_of_isWeightFamily T h12 (by positivity) h2
  refine ⟨P₁, Q₁, P₂, Q₂, fun v hv hθ => ?_⟩
  have f₁ := e₁ v hv
  have f₂ := e₂ v hv
  rw [(hasSum_pullCoef (isWeightFamily_YThetaCube t) two_pos _ v).tsum_eq,
    (t.hasSum_YThetaCubeCoeff (offOrbit_of_theta_ne_zero hθ)).tsum_eq] at f₁
  rw [tsum_pull_theta two_pos 3 v] at f₂
  have hv0 : (v : K) ^ (-((3 * N - 3 : ℕ) : ℤ)) ≠ 0 := zpow_ne_zero _ v.ne_zero
  have hθT : T.theta (-v) ^ (3 * N * 2) ≠ 0 := pow_ne_zero _ (theta_neg_ne_zero T hv)
  have hden : P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at f₂
    exact mul_ne_zero hv0 (pow_ne_zero _ hθ) f₂
  refine ⟨hden, ?_⟩
  rw [eq_div_iff hden]
  apply mul_left_cancel₀ (mul_ne_zero hv0 (mul_ne_zero (pow_ne_zero 3 hθ) hθT))
  linear_combination
    (T.theta (-v) ^ (3 * N * 2) * (P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v))) * f₁ -
    ((P₁.eval (T.X v) + T.Y v * Q₁.eval (T.X v)) * T.theta (-v) ^ (3 * N * 2)) * f₂

include hs hN hT in
/-- **G1 (ψ-route), function fields**: for `N` even there are `x_Q ∘ ψ, y_Q ∘ ψ ∈ K(E_q)`
(`ψ(u) = u^N`) such that the subfield `ψ^* K(E_Q) = K(x_Q ∘ ψ, y_Q ∘ ψ)` contains

* `F_N = f_N ∘ ψ`, with values `Θ̈_q(u^N)/Θ̈_{q^N}(u^N)^N` (the theta level function), and
* `[2N]^* x_q`, `[2N]^* y_q`, with values `X_q(u^{2N})`, `Y_q(u^{2N})` (`φ ∘ ψ = [2N]`),

all values taken at the Tate points `u` with `θ_Q(-u^N) ≠ 0` (and `Θ̈_{q^N}(u^N) ≠ 0`,
resp. `θ_q(-u^{2N}) ≠ 0`); `D ≠ 0` cuts out the first condition. -/
theorem exists_levelField (hev : Even N) :
    ∃ (gX gY F x₂ y₂ : TateField t) (D : TateRing t), D ≠ 0 ∧
      F ∈ IntermediateField.adjoin K ({gX, gY} : Set (TateField t)) ∧
      x₂ ∈ IntermediateField.adjoin K ({gX, gY} : Set (TateField t)) ∧
      y₂ ∈ IntermediateField.adjoin K ({gX, gY} : Set (TateField t)) ∧
      ∀ (u : Kˣ) (hu : OffOrbit t u),
        (evalTate t h12 hu D ≠ 0 ↔ T.theta (-(u ^ N)) ≠ 0) ∧
        (T.theta (-(u ^ N)) ≠ 0 →
          HasTateValue t h12 gX hu (T.X (u ^ N)) ∧ HasTateValue t h12 gY hu (T.Y (u ^ N)) ∧
          (etaleTheta (tatePow t N hN) (u ^ N) ≠ 0 →
            HasTateValue t h12 F hu (thetaLevel t N hN (u ^ N))) ∧
          (t.theta (-(u ^ (2 * N))) ≠ 0 →
            HasTateValue t h12 x₂ hu (t.X (u ^ (2 * N))) ∧
            HasTateValue t h12 y₂ hu (t.Y (u ^ (2 * N))))) := by
  obtain ⟨gX, gY, F, D, hD, hF, hspec⟩ := exists_pullTheta t h12 hs hN T hT hev
  obtain ⟨A₁, B₁, A₂, B₂, hx⟩ := exists_poly_isogenyX t hs hN T hT h12
  obtain ⟨C₁, E₁, C₂, E₂, hy⟩ := exists_poly_isogenyY t hs hN T hT h12 hev
  have hgX : gX ∈ IntermediateField.adjoin K ({gX, gY} : Set (TateField t)) :=
    IntermediateField.subset_adjoin _ _ (by simp)
  have hgY : gY ∈ IntermediateField.adjoin K ({gX, gY} : Set (TateField t)) :=
    IntermediateField.subset_adjoin _ _ (by simp)
  have mem : ∀ P₁ Q₁ P₂ Q₂ : K[X],
      (Polynomial.aeval gX P₁ + gY * Polynomial.aeval gX Q₁) /
        (Polynomial.aeval gX P₂ + gY * Polynomial.aeval gX Q₂) ∈
        IntermediateField.adjoin K ({gX, gY} : Set (TateField t)) := fun P₁ Q₁ P₂ Q₂ =>
    div_mem (add_mem (aeval_mem_adjoin hgX P₁) (mul_mem hgY (aeval_mem_adjoin hgX Q₁)))
      (add_mem (aeval_mem_adjoin hgX P₂) (mul_mem hgY (aeval_mem_adjoin hgX Q₂)))
  refine ⟨gX, gY, F, _, _, D, hD, hF, mem A₁ B₁ A₂ B₂, mem C₁ E₁ C₂ E₂, fun u hu => ?_⟩
  obtain ⟨hDiff, hval⟩ := hspec u hu
  refine ⟨hDiff, fun h0 => ?_⟩
  obtain ⟨vX, vY, vF⟩ := hval h0
  refine ⟨vX, vY, vF, fun hθ => ?_⟩
  have hvv : u ^ (2 * N) = (u ^ N) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hvv] at hθ ⊢
  have hv := offOrbit_of_theta_ne_zero h0
  obtain ⟨hdx, ex⟩ := hx (u ^ N) hv hθ
  obtain ⟨hdy, ey⟩ := hy (u ^ N) hv hθ
  exact ⟨((vX.aeval A₁).add (vY.mul (vX.aeval B₁))).div
      ((vX.aeval A₂).add (vY.mul (vX.aeval B₂))) hdx |>.congr ex.symm,
    ((vX.aeval C₁).add (vY.mul (vX.aeval E₁))).div
      ((vX.aeval C₂).add (vY.mul (vX.aeval E₂))) hdy |>.congr ey.symm⟩

end Iut.EtaleTheta
