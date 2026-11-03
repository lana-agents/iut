/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.TateElliptic

/-!
# The cyclic quadric `Γ_d` takes a single value on Tate points (TFGD, D-T11)

Let `t` be a Tate parameter with period `q = t.q`, let `T'` be the Tate parameter with period
`Q = q^n`, write `X' = T'.X` and `x_D = X'(q^d)` for `0 < d < n`. The cyclic quadric

`Γ_d(v) = ∑_{k < n} (X'(v q^k) - x_D)·(X'(v q^{k+d}) - x_D)`

takes the same value at every `v` off the period orbit `q^ℤ`
(`exists_gammaQuadric_eq`, `gammaQuadric_eq_neg_one`).

Proof, inside the theta-family engine of tate-curves-theta (`Theta/WeightSpace.lean`):

* `H(v) = ∏_{i<n} θ'(-v q^i)²` and `F(v) = ∑_k ∏_{i<n} f_{k,i}(v)`, where `f_{k,i}` is
  `(X'(v q^i) - x_D)·θ'(-v q^i)²` for the two marked indices `i ∈ {k, k + d mod n}` and
  `θ'(-v q^i)²` otherwise, are values of explicit everywhere-summable Laurent families
  (iterated convolutions `prodCoef` of rescaled families `gamScaleCoef`).
* Off the orbit, `F = Γ_d·H`; `Γ_d(q v) = Γ_d(v)` and `H(q v) = Aθ'²·v⁻²·H(v)`, so both
  families are weight-two families for `t` with multiplier `Aθ'² = ((Q·(-1))⁻¹)²`
  (`isWeightFamily_of_tsum_q_smul_off_orbit`).
* Both vanish at `v = 1`: each summand of `F` contains `θ'(-1)² = 0` or a factor
  `X'(q^d) - x_D = 0` resp. `X'(q^{n-d}) - x_D = 0`.
* A weight-two family vanishing at `1` is `a·θ(-u)·θ(e u)` for one fixed `e` depending only on
  the multiplier (`exists_lval_eq_of_weightTwo`: division by the theta block `θ(-u)`,
  `exists_convBlock_eq'`, and weight-one classification, `w1_eq_smul_thetaBlock`).
  Hence `F = a₁ φ`, `H = a₂ φ`, `H(v) ≠ 0` off the orbit, and `Γ_d = a₁/a₂`.
-/

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! ### Everywhere summable Laurent families -/

/-- The value `∑' n, cₙ xⁿ` of a Laurent coefficient family at `x`. -/
def lval (c : ℤ → K) (x : K) : K := ∑' n : ℤ, c n * x ^ n

/-- A Laurent coefficient family whose series is summable at every unit. -/
def LaurentSummable (c : ℤ → K) : Prop := ∀ u : Kˣ, Summable fun n : ℤ => c n * (u : K) ^ n

theorem LaurentSummable.conv {c d : ℤ → K} (hc : LaurentSummable c) (hd : LaurentSummable d) :
    LaurentSummable (lconv c d) := fun u =>
  (hasSum_laurentConvolution u (hc u).hasSum (hd u).hasSum).summable

theorem lval_lconv {c d : ℤ → K} (hc : LaurentSummable c) (hd : LaurentSummable d) (u : Kˣ) :
    lval (lconv c d) u = lval c u * lval d u :=
  (hasSum_laurentConvolution u (hc u).hasSum (hd u).hasSum).tsum_eq

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem laurentSummable_single : LaurentSummable (Pi.single 0 1 : ℤ → K) := fun _ =>
  summable_of_ne_finset_zero (s := {0}) fun n hn => by
    rw [Finset.mem_singleton] at hn
    simp [hn]

/-- The family of `u ↦ F(u·s)`: the `n`-th coefficient is multiplied by `sⁿ`. -/
def gamScaleCoef (c : ℤ → K) (s : K) : ℤ → K := fun n => c n * s ^ n

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem LaurentSummable.scale {c : ℤ → K} (hc : LaurentSummable c) (s : Kˣ) :
    LaurentSummable (gamScaleCoef c s) := fun u =>
  (hc (u * s)).congr fun n => by
    simp only [gamScaleCoef, Units.val_mul, mul_zpow]
    ring

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem lval_scaleCoef (c : ℤ → K) (s u : Kˣ) :
    lval (gamScaleCoef c s) u = lval c ((u * s : Kˣ) : K) := by
  unfold lval gamScaleCoef
  refine tsum_congr fun n => ?_
  rw [Units.val_mul, mul_zpow]
  ring

/-- Iterated convolution `f_{m-1} ⋆ ⋯ ⋆ f₀` (the family of the product of the values). -/
def prodCoef (f : ℕ → ℤ → K) : ℕ → ℤ → K
  | 0 => Pi.single 0 1
  | m + 1 => lconv (f m) (prodCoef f m)

theorem laurentSummable_prodCoef {f : ℕ → ℤ → K} (hf : ∀ i, LaurentSummable (f i)) :
    ∀ m, LaurentSummable (prodCoef f m)
  | 0 => laurentSummable_single
  | m + 1 => (hf m).conv (laurentSummable_prodCoef hf m)

theorem lval_prodCoef {f : ℕ → ℤ → K} (hf : ∀ i, LaurentSummable (f i)) (u : Kˣ) :
    ∀ m, lval (prodCoef f m) u = ∏ i ∈ Finset.range m, lval (f i) u
  | 0 => by
    rw [Finset.prod_range_zero]
    exact tsum_single u
  | m + 1 => by
    rw [Finset.prod_range_succ, ← lval_prodCoef hf u m, mul_comm]
    exact lval_lconv (hf m) (laurentSummable_prodCoef hf m) u

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem laurentSummable_sum {ι : Type*} (s : Finset ι) {f : ι → ℤ → K}
    (hf : ∀ i ∈ s, LaurentSummable (f i)) : LaurentSummable (∑ i ∈ s, f i) := fun u =>
  (summable_sum fun i hi => hf i hi u).congr fun n => by simp [Finset.sum_mul]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem lval_sum {ι : Type*} (s : Finset ι) {f : ι → ℤ → K}
    (hf : ∀ i ∈ s, LaurentSummable (f i)) (u : Kˣ) :
    lval (∑ i ∈ s, f i) u = ∑ i ∈ s, lval (f i) u := by
  unfold lval
  rw [← Summable.tsum_finsetSum fun i hi => hf i hi u]
  exact tsum_congr fun n => by simp [Finset.sum_mul]

/-! ### Weight-two families vanishing at `1` -/

/-- **A weight-two family vanishing at `u = 1` is a multiple of one fixed product of theta
functions**: `F(u) = a·θ(-u)·θ(e u)` with `e = (q·(q·(-1))·M)⁻¹` depending only on the
multiplier `M`. Division by the theta block `θ(-u)` (`exists_convBlock_eq'`, with a witness
`θ(s u)·θ(P s⁻¹ u)` not vanishing at `1`) and the weight-one classification
(`w1_eq_smul_thetaBlock`). -/
theorem exists_lval_eq_of_weightTwo (t : TateParameter K) {M : Kˣ} {c : ℤ → K}
    (hc : t.IsWeightFamily 2 M c) (h1 : lval c ((1 : Kˣ) : K) = 0) :
    ∃ a : K, ∀ u : Kˣ, lval c u =
      a * (t.theta (-u) * t.theta ((t.q * (t.q * (-1) * M))⁻¹ * u)) := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Kˣ, P = (t.q * t.q * M)⁻¹ := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ := t.exists_unit_avoiding {-1, -P}
  have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
  have hs1 : t.theta s ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff s).mp h0
    exact hs (-1) (by simp) k (by rw [hk]; simp)
  have hs2 : t.theta (P * s⁻¹) ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff _).mp h0
    refine hs (-P) (by simp) (-k) ?_
    rw [Units.val_mul] at hk
    have hP' : (P : K) = -(t.q : K) ^ k * s := by
      rw [← hk, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    rw [Units.val_neg, hP', zpow_neg, neg_mul, neg_neg, ← mul_assoc,
      inv_mul_cancel₀ (zpow_ne_zero _ hq0), one_mul]
  have hmult : (t.q * s)⁻¹ * (t.q * (P * s⁻¹))⁻¹ = M := by
    rw [hP]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hgw := (isWeightFamily_thetaBlock (t := t) s).conv
    (isWeightFamily_thetaBlock (t := t) (P * s⁻¹))
  rw [hmult] at hgw
  obtain ⟨C, hC⟩ := exists_convBlock_eq' (t := t) (k := 1) one_pos (-1)
    (A := t.q * (-1) * M) (M := M) (by group) (x₀ := 1)
    (by rw [mul_one]; exact t.theta_neg_one) ⟨_, hgw⟩ (by
      rw [evalAt_apply]
      change (∑' n : ℤ, (∑' m : ℤ, t.thetaBlock s (n - m) * t.thetaBlock (P * s⁻¹) m) *
        ((1 : Kˣ) : K) ^ n) ≠ 0
      rw [((isWeightFamily_thetaBlock (t := t) s).conv_hasSum
        (isWeightFamily_thetaBlock (t := t) (P * s⁻¹)) 1).tsum_eq, tsum_thetaBlock,
        tsum_thetaBlock, mul_one, mul_one]
      exact mul_ne_zero hs1 hs2) ⟨c, hc⟩ (by rw [evalAt_apply]; exact h1)
  refine ⟨(C : ℤ → K) 0, fun u => ?_⟩
  have h := t.tsum_eq_theta_mul_of_forall_conv_eq C hC u
  have hw := w1_eq_smul_thetaBlock (t := t) C.2
  have hCv : (∑' n : ℤ, (C : ℤ → K) n * (u : K) ^ n) =
      (C : ℤ → K) 0 * t.theta ((t.q * (t.q * (-1) * M))⁻¹ * u) := by
    calc (∑' n : ℤ, (C : ℤ → K) n * (u : K) ^ n)
        = ∑' n : ℤ, (C : ℤ → K) 0 *
            (t.thetaBlock ((t.q * (t.q * (-1) * M))⁻¹) n * (u : K) ^ n) :=
          tsum_congr fun n => by rw [congrFun hw n, Pi.smul_apply, smul_eq_mul, mul_assoc]
      _ = _ := by rw [tsum_mul_left, tsum_thetaBlock]
  unfold lval
  rw [h, hCv, neg_one_mul]
  ring

/-! ### Orbit bookkeeping -/

section Orbit

variable (t T' : TateParameter K) {n : ℕ}

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem offOrbit_q_mul {v : Kˣ} (hv : OffOrbit t v) : OffOrbit t (t.q * v) := by
  intro j hj
  apply hv (j + 1)
  rw [Units.val_mul] at hj
  rw [zpow_add_one₀ t.q.ne_zero]
  linear_combination hj

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem offOrbit_mul_pow (hT : T'.q = t.q ^ n) {v : Kˣ} (hv : OffOrbit t v) (i : ℕ) :
    OffOrbit T' (v * t.q ^ i) := by
  intro j hj
  apply hv ((n : ℤ) * j + i)
  rw [hT, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_pow_eq_pow_val] at hj
  rw [zpow_add₀ t.q.ne_zero, zpow_mul, zpow_natCast, zpow_natCast, ← hj]
  ring

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem eq_zero_of_q_zpow_eq_one {m : ℤ} (h : (t.q : K) ^ m = 1) : m = 0 := by
  have hn := congrArg norm h
  rwa [norm_one, norm_zpow, zpow_eq_one_iff_right₀ (norm_nonneg _) t.norm_lt_one.ne] at hn

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem offOrbit_q_pow (hT : T'.q = t.q ^ n) {i : ℕ} (hi0 : 0 < i) (hin : i < n) :
    OffOrbit T' (t.q ^ i) := by
  intro j hj
  rw [hT, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← zpow_natCast (t.q : K) n,
    ← zpow_mul, ← zpow_natCast (t.q : K) i, ← zpow_add₀ t.q.ne_zero] at hj
  have h := eq_zero_of_q_zpow_eq_one t hj
  rcases le_or_gt 0 j with hj0 | hj0
  · have : (0 : ℤ) ≤ (n : ℤ) * j := mul_nonneg (by positivity) hj0
    omega
  · have : (n : ℤ) * j ≤ -(n : ℤ) := by nlinarith
    omega

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem offOrbit_neg_one_of_ne (h2 : (2 : K) ≠ 0) : OffOrbit t (-1) := by
  intro j hj
  have hj' : (t.q : K) ^ j = -1 := by
    rw [Units.val_neg, Units.val_one] at hj
    linear_combination -hj
  have h0 : (t.q : K) ^ (j + j) = 1 := by rw [zpow_add₀ t.q.ne_zero, hj']; ring
  have hj0 : j = 0 := by have := eq_zero_of_q_zpow_eq_one t h0; omega
  rw [hj0, zpow_zero] at hj'
  exact h2 (by linear_combination hj')

end Orbit

/-! ### Finite index bookkeeping -/

theorem sum_range_shift_of_eq {M : Type*} [AddCommMonoid M] {φ : ℕ → M} {n : ℕ} (hn : 0 < n)
    (h : φ n = φ 0) : ∑ k ∈ Finset.range n, φ (k + 1) = ∑ k ∈ Finset.range n, φ k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ', h]

theorem prod_range_shift_of_eq {M : Type*} [CommMonoid M] {ψ : ℕ → M} {n : ℕ} {c : M}
    (hn : 0 < n) (h : ψ n = c * ψ 0) :
    ∏ k ∈ Finset.range n, ψ (k + 1) = c * ∏ k ∈ Finset.range n, ψ k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.prod_range_succ, Finset.prod_range_succ', h, mul_left_comm]

theorem prod_ite_two {M : Type*} [CommMonoid M] {n k k' : ℕ} (hk : k < n) (hk' : k' < n)
    (hne : k ≠ k') (a : ℕ → M) :
    ∏ i ∈ Finset.range n, (if i = k ∨ i = k' then a i else 1) = a k * a k' := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
  have : (Finset.range n).filter (fun i => i = k ∨ i = k') = {k, k'} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [this, Finset.prod_pair hne]

/-- The second marked index `k + d mod n` (for `k, d < n`). -/
def wrapIdx (n d k : ℕ) : ℕ := if k + d < n then k + d else k + d - n

theorem wrapIdx_lt {n d k : ℕ} (hk : k < n) (hd : d < n) : wrapIdx n d k < n := by
  unfold wrapIdx
  split_ifs <;> omega

theorem ne_wrapIdx {n d k : ℕ} (hd0 : 0 < d) (hd : d < n) : k ≠ wrapIdx n d k := by
  unfold wrapIdx
  split_ifs <;> omega

/-! ### The theta families of the cyclic quadric -/

section Gamma

variable (t T' : TateParameter K) {n d : ℕ}

theorem laurentSummable_thetaBlock (e : Kˣ) : LaurentSummable (T'.thetaBlock e) :=
  (isWeightFamily_thetaBlock (t := T') e).summable

/-- The family of `w ↦ θ'(-w)²`. -/
def thetaSqCoef : ℤ → K := lconv (T'.thetaBlock (-1)) (T'.thetaBlock (-1))

theorem laurentSummable_thetaSqCoef : LaurentSummable (thetaSqCoef T') :=
  (laurentSummable_thetaBlock T' (-1)).conv (laurentSummable_thetaBlock T' (-1))

theorem lval_thetaSqCoef (w : Kˣ) : lval (thetaSqCoef T') w = T'.theta (-w) ^ 2 := by
  rw [thetaSqCoef, lval_lconv (laurentSummable_thetaBlock T' (-1))
    (laurentSummable_thetaBlock T' (-1)), lval, tsum_thetaBlock, neg_one_mul, sq]

/-- The functional equation of `θ'(-w)²` under `w ↦ Q w`. -/
theorem theta_neg_q_mul_sq (w : Kˣ) :
    T'.theta (-(T'.q * w)) ^ 2 =
      (((T'.q * (-1))⁻¹ ^ 2 : Kˣ) : K) * (w : K) ^ (-((2 : ℕ) : ℤ)) * T'.theta (-w) ^ 2 := by
  have h := (isWeightFamily_thetaBlock (t := T') (-1)).tsum_q_smul w
  have h1 := tsum_thetaBlock (t := T') (-1) (T'.q * w)
  rw [Units.val_mul] at h1
  rw [h1, tsum_thetaBlock, neg_one_mul, neg_one_mul] at h
  rw [h, Units.val_pow_eq_pow_val]
  have hw : (w : K) ^ (-((2 : ℕ) : ℤ)) = ((w : K) ^ (-((1 : ℕ) : ℤ))) ^ 2 := by
    rw [← zpow_natCast _ 2, ← zpow_mul]
    norm_num
  rw [hw]
  ring

/-- The family of `w ↦ (X'(w) - x)·θ'(-w)²`. -/
def markCoef (x : K) : ℤ → K := T'.XThetaSqCoeff - x • thetaSqCoef T'

theorem laurentSummable_markCoef (x : K) : LaurentSummable (markCoef T' x) := fun u =>
  ((T'.summable_XThetaSqCoeff_mul_zpow u).sub
    ((laurentSummable_thetaSqCoef T' u).mul_left x)).congr fun n => by
      simp only [markCoef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring

theorem lval_markCoef (x : K) {w : Kˣ} (hw : OffOrbit T' w) :
    lval (markCoef T' x) w = (T'.X w - x) * T'.theta (-w) ^ 2 := by
  have hth := lval_thetaSqCoef T' w
  unfold lval at hth ⊢
  calc (∑' n : ℤ, markCoef T' x n * (w : K) ^ n)
      = ∑' n : ℤ, (T'.XThetaSqCoeff n * (w : K) ^ n - x * (thetaSqCoef T' n * (w : K) ^ n)) :=
        tsum_congr fun n => by
          simp only [markCoef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
    _ = _ := by
        rw [Summable.tsum_sub (T'.summable_XThetaSqCoeff_mul_zpow w)
          ((laurentSummable_thetaSqCoef T' w).mul_left x), tsum_mul_left,
          (T'.hasSum_XThetaSqCoeff hw).tsum_eq, hth]
        ring

/-- The `i`-th factor of the `k`-th summand of the numerator family: `(X' - x)·θ'(-·)²` at
the marked indices `k`, `k + d mod n` and `θ'(-·)²` otherwise, rescaled by `q^i`. -/
def gammaFactor (n d : ℕ) (x : K) (k i : ℕ) : ℤ → K :=
  gamScaleCoef (if i = k ∨ i = wrapIdx n d k then markCoef T' x else thetaSqCoef T')
    ((t.q ^ i : Kˣ) : K)

/-- The numerator family `F(v) = ∑_k ∏_i f_{k,i}(v)`. -/
def gammaNumCoef (n d : ℕ) : ℤ → K :=
  ∑ k ∈ Finset.range n, prodCoef (gammaFactor t T' n d (T'.X (t.q ^ d)) k) n

/-- The denominator family `H(v) = ∏_{i<n} θ'(-v q^i)²`. -/
def gammaDenCoef (n : ℕ) : ℤ → K :=
  prodCoef (fun i => gamScaleCoef (thetaSqCoef T') ((t.q ^ i : Kˣ) : K)) n

/-- The cyclic quadric `Γ_d(v) = ∑_{k<n} (X'(v q^k) - x_D)·(X'(v q^{k+d}) - x_D)`. -/
def gammaSum (n d : ℕ) (v : Kˣ) : K :=
  ∑ k ∈ Finset.range n,
    (T'.X (v * t.q ^ k) - T'.X (t.q ^ d)) * (T'.X (v * t.q ^ (k + d)) - T'.X (t.q ^ d))

theorem laurentSummable_gammaFactor (n d : ℕ) (x : K) (k i : ℕ) :
    LaurentSummable (gammaFactor t T' n d x k i) := by
  unfold gammaFactor
  split_ifs
  · exact (laurentSummable_markCoef T' x).scale _
  · exact (laurentSummable_thetaSqCoef T').scale _

theorem laurentSummable_gammaNumCoef (n d : ℕ) : LaurentSummable (gammaNumCoef t T' n d) :=
  laurentSummable_sum _ fun k _ =>
    laurentSummable_prodCoef (laurentSummable_gammaFactor t T' n d _ k) n

theorem laurentSummable_gammaDenCoef (n : ℕ) : LaurentSummable (gammaDenCoef t T' n) :=
  laurentSummable_prodCoef (fun _ => (laurentSummable_thetaSqCoef T').scale _) n

theorem lval_gammaFactor (n d : ℕ) (x : K) (k i : ℕ) (v : Kˣ)
    (hv : OffOrbit T' (v * t.q ^ i)) :
    lval (gammaFactor t T' n d x k i) v =
      (if i = k ∨ i = wrapIdx n d k then T'.X (v * t.q ^ i) - x else 1) *
        T'.theta (-(v * t.q ^ i)) ^ 2 := by
  unfold gammaFactor
  split_ifs
  · rw [lval_scaleCoef, lval_markCoef T' x hv]
  · rw [lval_scaleCoef, lval_thetaSqCoef, one_mul]

theorem lval_gammaFactor_of_not (n d : ℕ) (x : K) (k i : ℕ)
    (h : ¬(i = k ∨ i = wrapIdx n d k)) (v : Kˣ) :
    lval (gammaFactor t T' n d x k i) v = T'.theta (-(v * t.q ^ i)) ^ 2 := by
  unfold gammaFactor
  rw [if_neg h, lval_scaleCoef, lval_thetaSqCoef]

theorem lval_gammaDenCoef (n : ℕ) (v : Kˣ) :
    lval (gammaDenCoef t T' n) v = ∏ i ∈ Finset.range n, T'.theta (-(v * t.q ^ i)) ^ 2 := by
  rw [gammaDenCoef, lval_prodCoef (fun _ => (laurentSummable_thetaSqCoef T').scale _)]
  exact Finset.prod_congr rfl fun i _ => by rw [lval_scaleCoef, lval_thetaSqCoef]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem X_mul_q_pow_wrapIdx (hT : T'.q = t.q ^ n) {k : ℕ} (v : Kˣ) :
    T'.X (v * t.q ^ wrapIdx n d k) = T'.X (v * t.q ^ (k + d)) := by
  unfold wrapIdx
  split_ifs with h
  · rfl
  · have : v * t.q ^ (k + d) = T'.q * (v * t.q ^ (k + d - n)) := by
      rw [hT, mul_left_comm, ← pow_add]
      congr 2
      omega
    rw [this, X_q_smul]

/-- Off the orbit, the numerator is the cyclic quadric times the denominator. -/
theorem lval_gammaNumCoef (hT : T'.q = t.q ^ n) (hd0 : 0 < d) (hdn : d < n) {v : Kˣ}
    (hv : ∀ i, OffOrbit T' (v * t.q ^ i)) :
    lval (gammaNumCoef t T' n d) v = gammaSum t T' n d v * lval (gammaDenCoef t T' n) v := by
  rw [gammaNumCoef, lval_sum _ (fun k _ =>
    laurentSummable_prodCoef (laurentSummable_gammaFactor t T' n d _ k) n), gammaSum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [lval_prodCoef (laurentSummable_gammaFactor t T' n d _ k), lval_gammaDenCoef,
    Finset.prod_congr rfl fun i _ => lval_gammaFactor t T' n d _ k i v (hv i),
    Finset.prod_mul_distrib, prod_ite_two hk (wrapIdx_lt hk hdn) (ne_wrapIdx hd0 hdn),
    X_mul_q_pow_wrapIdx t T' hT]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem gammaSum_q_mul (hT : T'.q = t.q ^ n) (hn : 0 < n) (v : Kˣ) :
    gammaSum t T' n d (t.q * v) = gammaSum t T' n d v := by
  unfold gammaSum
  rw [← sum_range_shift_of_eq (φ := fun j => (T'.X (v * t.q ^ j) - T'.X (t.q ^ d)) *
      (T'.X (v * t.q ^ (j + d)) - T'.X (t.q ^ d))) hn (by
    simp only [pow_zero, mul_one, zero_add]
    rw [show v * t.q ^ n = T'.q * v by rw [hT, mul_comm],
      show v * t.q ^ (n + d) = T'.q * (v * t.q ^ d) by rw [hT, pow_add, mul_left_comm],
      X_q_smul, X_q_smul])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show t.q * v * t.q ^ k = v * t.q ^ (k + 1) by rw [pow_succ]; ac_rfl,
    show t.q * v * t.q ^ (k + d) = v * t.q ^ (k + 1 + d) by
      rw [show k + 1 + d = k + d + 1 by omega, pow_succ]; ac_rfl]

theorem lval_gammaDen_q_mul (hT : T'.q = t.q ^ n) (hn : 0 < n) (v : Kˣ) :
    lval (gammaDenCoef t T' n) ((t.q * v : Kˣ) : K) =
      (((T'.q * (-1))⁻¹ ^ 2 : Kˣ) : K) * (v : K) ^ (-((2 : ℕ) : ℤ)) *
        lval (gammaDenCoef t T' n) v := by
  rw [lval_gammaDenCoef, lval_gammaDenCoef,
    ← prod_range_shift_of_eq (ψ := fun j => T'.theta (-(v * t.q ^ j)) ^ 2) hn (by
      simp only [pow_zero, mul_one]
      rw [show v * t.q ^ n = T'.q * v by rw [hT, mul_comm], theta_neg_q_mul_sq])]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [show t.q * v * t.q ^ k = v * t.q ^ (k + 1) by rw [pow_succ]; ac_rfl]

theorem isWeightFamily_gammaDen (hT : T'.q = t.q ^ n) (hn : 0 < n) :
    t.IsWeightFamily 2 ((T'.q * (-1))⁻¹ ^ 2) (gammaDenCoef t T' n) :=
  isWeightFamily_of_tsum_q_smul_off_orbit (t := t) (laurentSummable_gammaDenCoef t T' n)
    fun u _ => lval_gammaDen_q_mul t T' hT hn u

theorem isWeightFamily_gammaNum (hT : T'.q = t.q ^ n) (hd0 : 0 < d) (hdn : d < n) :
    t.IsWeightFamily 2 ((T'.q * (-1))⁻¹ ^ 2) (gammaNumCoef t T' n d) :=
  isWeightFamily_of_tsum_q_smul_off_orbit (t := t) (laurentSummable_gammaNumCoef t T' n d)
    fun u hu => by
      have hu' : OffOrbit t u := hu
      change lval (gammaNumCoef t T' n d) ((t.q * u : Kˣ) : K) =
        _ * _ * lval (gammaNumCoef t T' n d) u
      rw [lval_gammaNumCoef t T' hT hd0 hdn (offOrbit_mul_pow t T' hT (offOrbit_q_mul t hu')),
        lval_gammaNumCoef t T' hT hd0 hdn (offOrbit_mul_pow t T' hT hu'),
        lval_gammaDen_q_mul t T' hT (by omega), gammaSum_q_mul t T' hT (by omega)]
      ring

theorem lval_gammaDen_one (hn : 0 < n) : lval (gammaDenCoef t T' n) ((1 : Kˣ) : K) = 0 := by
  rw [lval_gammaDenCoef]
  refine Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr hn) ?_
  rw [pow_zero, mul_one, T'.theta_neg_one]
  ring

theorem lval_gammaNum_one (hT : T'.q = t.q ^ n) (hd0 : 0 < d) (hdn : d < n) :
    lval (gammaNumCoef t T' n d) ((1 : Kˣ) : K) = 0 := by
  rw [gammaNumCoef, lval_sum _ (fun k _ =>
    laurentSummable_prodCoef (laurentSummable_gammaFactor t T' n d _ k) n)]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [lval_prodCoef (laurentSummable_gammaFactor t T' n d _ k)]
  have hD : OffOrbit T' (t.q ^ d) := offOrbit_q_pow t T' hT hd0 hdn
  by_cases hk0 : k = 0
  · subst hk0
    refine Finset.prod_eq_zero (i := d) (Finset.mem_range.mpr hdn) ?_
    have hm : d = 0 ∨ d = wrapIdx n d 0 := Or.inr (by unfold wrapIdx; rw [if_pos (by omega)]; omega)
    rw [lval_gammaFactor t T' n d _ 0 d 1 (by rw [one_mul]; exact hD), if_pos hm, one_mul,
      sub_self, zero_mul]
  · by_cases hw : wrapIdx n d k = 0
    · have hkd : k + d = n := by
        unfold wrapIdx at hw
        split_ifs at hw <;> omega
      refine Finset.prod_eq_zero (i := k) (Finset.mem_range.mpr hk) ?_
      have hX : T'.X (t.q ^ k) = T'.X (t.q ^ d) := by
        have : t.q ^ k = T'.q * (t.q ^ d)⁻¹ := by rw [hT, ← hkd, pow_add, mul_inv_cancel_right]
        rw [this, X_q_smul, T'.X_inv hD]
      have hk' : OffOrbit T' (t.q ^ k) := offOrbit_q_pow t T' hT (by omega) hk
      rw [lval_gammaFactor t T' n d _ k k 1 (by rw [one_mul]; exact hk'), if_pos (Or.inl rfl),
        one_mul, hX, sub_self, zero_mul]
    · refine Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr (by omega)) ?_
      rw [lval_gammaFactor_of_not t T' n d _ k 0 (by omega) 1, pow_zero, mul_one,
        T'.theta_neg_one]
      ring

theorem lval_gammaDen_ne_zero (hT : T'.q = t.q ^ n) {v : Kˣ} (hv : OffOrbit t v) :
    lval (gammaDenCoef t T' n) v ≠ 0 := by
  rw [lval_gammaDenCoef]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    pow_ne_zero _ (Iut.EtaleTheta.theta_neg_ne_zero T' (offOrbit_mul_pow t T' hT hv i))

/-- **The cyclic quadric `Γ_d` takes one value on Tate points** (TFGD, D-T11): for
`T'.q = q^n` and `0 < d < n`, `∑_{k<n} (X'(v q^k) - x_D)(X'(v q^{k+d}) - x_D)` with
`X' = T'.X`, `x_D = X'(q^d)` is the same for all `v` off the orbit `q^ℤ`. -/
theorem exists_gammaQuadric_eq (hT : T'.q = t.q ^ n) (hd0 : 0 < d) (hdn : d < n) :
    ∃ c : K, ∀ v : Kˣ, OffOrbit t v →
      ∑ k ∈ Finset.range n, (T'.X (v * t.q ^ k) - T'.X (t.q ^ d)) *
        (T'.X (v * t.q ^ (k + d)) - T'.X (t.q ^ d)) = c := by
  obtain ⟨a₁, h₁⟩ := exists_lval_eq_of_weightTwo t (isWeightFamily_gammaNum t T' hT hd0 hdn)
    (lval_gammaNum_one t T' hT hd0 hdn)
  obtain ⟨a₂, h₂⟩ := exists_lval_eq_of_weightTwo t (isWeightFamily_gammaDen t T' hT (by omega))
    (lval_gammaDen_one t T' (by omega))
  refine ⟨a₁ / a₂, fun v hv => ?_⟩
  have hH := lval_gammaDen_ne_zero t T' hT hv
  have hF := lval_gammaNumCoef t T' hT hd0 hdn (offOrbit_mul_pow t T' hT hv)
  rw [h₁, h₂] at hF
  rw [h₂] at hH
  have ha₂ : a₂ ≠ 0 := left_ne_zero_of_mul hH
  have hφ := right_ne_zero_of_mul hH
  change gammaSum t T' n d v = a₁ / a₂
  rw [eq_div_iff ha₂]
  apply mul_right_cancel₀ hφ
  linear_combination -hF

/-- The value of the cyclic quadric is its value at `v = -1` (where it can be estimated). -/
theorem gammaQuadric_eq_neg_one (h2 : (2 : K) ≠ 0) (hT : T'.q = t.q ^ n) (hd0 : 0 < d)
    (hdn : d < n) {v : Kˣ} (hv : OffOrbit t v) :
    ∑ k ∈ Finset.range n, (T'.X (v * t.q ^ k) - T'.X (t.q ^ d)) *
        (T'.X (v * t.q ^ (k + d)) - T'.X (t.q ^ d)) =
      ∑ k ∈ Finset.range n, (T'.X (-1 * t.q ^ k) - T'.X (t.q ^ d)) *
        (T'.X (-1 * t.q ^ (k + d)) - T'.X (t.q ^ d)) := by
  obtain ⟨c, hc⟩ := exists_gammaQuadric_eq t T' hT hd0 hdn
  rw [hc v hv, hc (-1) (offOrbit_neg_one_of_ne t h2)]

end Gamma

end Iut.EtaleTheta
