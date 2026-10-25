/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TateCurvesTheta.TateCurve.AbelStep
import TateCurvesTheta.TateCurve.CoordinateInversion
import TateCurvesTheta.TateCurve.TatePointOnCurve

/-!
# Theta functions of weight `k` are polynomials in `X, Y` times `θ(-u)^k` (MR14, task G2b)

For a Tate parameter `q` over a complete nonarchimedean field `K` with `12 ≠ 0`, every weight-`k`
theta family (`TateParameter.IsWeightFamily`, `F(qu) = A·u⁻ᵏ·F(u)`) with the multiplier
`Aθᵏ = ((q·(-1))⁻¹)ᵏ` of `θ(-u)ᵏ` has values

`F(u) = (P(X(u)) + Y(u)·Q(X(u))) · θ(-u)ᵏ`, `deg P ≤ k/2`, `deg Q ≤ (k-3)/2`,

(`exists_poly_of_isWeightFamily`): a `q`-periodic function `F/θ(-u)^k` with poles of order `≤ k`
at the origin only is a polynomial in the Tate coordinates — the dimension count
`dim L(k·O) = k = dim W(k, Aθᵏ)` (tate-curves-theta: `finrank_weightSpace`) together with the
linear independence of the monomials `Xⁱ`, `XⁱY` as functions (`poly_eq_zero_of_eval`, from
`X(u⁻¹) = X(u)`, `Y(u⁻¹) = -Y(u) - X(u)`, the Weierstrass equation of the Tate point and the
infinitude of the values of `X`, `infinite_range_X`).

This is the engine of route R-alg of MR14 (`~/iut-scratch/multiradial/MR14-plan.md`): the theta
level functions `f_N = Θ̈_q/Θ̈_{q^N}^N` (`ThetaLevel.lean`) and the isogeny coordinates are
rational functions on the Tate curve `E_{q^{N/2}}`.
-/

open Filter Topology

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-! ### Convolution powers -/

/-- The `m`-fold convolution power of a coefficient family. -/
def cpow (c : ℤ → K) : ℕ → ℤ → K
  | 0 => Pi.single 0 1
  | m + 1 => fun n => ∑' l : ℤ, c (n - l) * cpow c m l

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The unit family `δ₀` is a weight-`0` family with multiplier `1`. -/
theorem isWeightFamily_single : t.IsWeightFamily 0 1 (Pi.single 0 1 : ℤ → K) := by
  refine ⟨fun u => ?_, fun n => ?_⟩
  · apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    rw [Finset.mem_singleton] at hn
    simp [hn]
  · by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem tsum_single (u : Kˣ) : (∑' n : ℤ, (Pi.single 0 1 : ℤ → K) n * (u : K) ^ n) = 1 := by
  rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp

theorem isWeightFamily_cpow {k : ℕ} {A : Kˣ} {c : ℤ → K} (hc : t.IsWeightFamily k A c) :
    ∀ m : ℕ, t.IsWeightFamily (k * m) (A ^ m) (cpow c m)
  | 0 => by rw [mul_zero, pow_zero]; exact isWeightFamily_single t
  | m + 1 => by
    have h := hc.conv (isWeightFamily_cpow hc m)
    rw [show k + k * m = k * (m + 1) by ring, ← pow_succ'] at h
    exact h

theorem tsum_cpow {k : ℕ} {A : Kˣ} {c : ℤ → K} (hc : t.IsWeightFamily k A c) (u : Kˣ) :
    ∀ m : ℕ, (∑' n : ℤ, cpow c m n * (u : K) ^ n) = (∑' n : ℤ, c n * (u : K) ^ n) ^ m
  | 0 => by
    rw [pow_zero]
    exact tsum_single u
  | m + 1 => by
    change (∑' n : ℤ, (∑' l : ℤ, c (n - l) * cpow c m l) * (u : K) ^ n) = _
    rw [(hc.conv_hasSum (isWeightFamily_cpow t hc m) u).tsum_eq, tsum_cpow hc u m, pow_succ']

/-! ### The monomial families `Xⁱ θ(-u)ᵏ` and `Xⁱ Y θ(-u)ᵏ` -/

/-- The multiplier `Aθ = (q·(-1))⁻¹` of `θ(-u)`. -/
abbrev multθ : Kˣ := (t.q * (-1))⁻¹

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Changing the weight along an equality of naturals. -/
theorem weightFamily_of_eq {k l : ℕ} {A : Kˣ} {c : ℤ → K} (h : t.IsWeightFamily k A c)
    (hkl : k = l) : t.IsWeightFamily l A c := hkl ▸ h

/-- The family of `Xⁱ θ(-u)ᵏ` (for `2i ≤ k`). -/
def monoX (k i : ℕ) : ℤ → K :=
  fun n => ∑' l : ℤ, cpow t.XThetaSqCoeff i (n - l) * cpow (t.thetaBlock (-1)) (k - 2 * i) l

/-- The family of `Xⁱ Y θ(-u)ᵏ` (for `2i + 3 ≤ k`). -/
def monoXY (k i : ℕ) : ℤ → K :=
  fun n => ∑' l : ℤ, t.YThetaCubeCoeff (n - l) * monoX t (k - 3) i l

theorem isWeightFamily_monoX {k i : ℕ} (hi : 2 * i ≤ k) :
    t.IsWeightFamily k (multθ t ^ k) (monoX t k i) := by
  have h := (isWeightFamily_cpow t t.isWeightFamily_XThetaSq i).conv
    (isWeightFamily_cpow t (isWeightFamily_thetaBlock (t := t) (-1)) (k - 2 * i))
  rw [← pow_mul, ← pow_add, show 2 * i + (k - 2 * i) = k by omega] at h
  exact weightFamily_of_eq t h (by omega)

theorem isWeightFamily_monoXY {k i : ℕ} (hi : 2 * i + 3 ≤ k) :
    t.IsWeightFamily k (multθ t ^ k) (monoXY t k i) := by
  have h := t.isWeightFamily_YThetaCube.conv (isWeightFamily_monoX t (k := k - 3) (i := i)
    (by omega))
  rw [← pow_add, show 3 + (k - 3) = k by omega] at h
  exact weightFamily_of_eq t h (by omega)

/-- Points off the period orbit. -/
def OffOrbit (u : Kˣ) : Prop := ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1

theorem tsum_monoX {k i : ℕ} (hi : 2 * i ≤ k) {u : Kˣ} (hu : OffOrbit t u) :
    (∑' n : ℤ, monoX t k i n * (u : K) ^ n) = t.X u ^ i * t.theta (-u) ^ k := by
  have hc := isWeightFamily_cpow t t.isWeightFamily_XThetaSq i
  have hd := isWeightFamily_cpow t (isWeightFamily_thetaBlock (t := t) (-1)) (k - 2 * i)
  unfold monoX
  rw [(hc.conv_hasSum hd u).tsum_eq, tsum_cpow t t.isWeightFamily_XThetaSq u,
    tsum_cpow t (isWeightFamily_thetaBlock (t := t) (-1)) u, (t.hasSum_XThetaSqCoeff hu).tsum_eq,
    tsum_thetaBlock, neg_one_mul, mul_pow, mul_assoc, ← pow_mul, ← pow_add,
    show 2 * i + (k - 2 * i) = k by omega]

theorem tsum_monoXY {k i : ℕ} (hi : 2 * i + 3 ≤ k) {u : Kˣ} (hu : OffOrbit t u) :
    (∑' n : ℤ, monoXY t k i n * (u : K) ^ n) = t.X u ^ i * t.Y u * t.theta (-u) ^ k := by
  have hd := isWeightFamily_monoX t (k := k - 3) (i := i) (by omega)
  unfold monoXY
  rw [(t.isWeightFamily_YThetaCube.conv_hasSum hd u).tsum_eq,
    (t.hasSum_YThetaCubeCoeff hu).tsum_eq, tsum_monoX t (by omega) hu]
  have : t.theta (-u) ^ k = t.theta (-u) ^ 3 * t.theta (-u) ^ (k - 3) := by
    rw [← pow_add]; congr 1; omega
  rw [this]; ring

/-! ### Linear independence of the monomials as functions -/

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem offOrbit_inv {u : Kˣ} (hu : OffOrbit t u) : OffOrbit t u⁻¹ := by
  intro n hn
  apply hu (-n)
  have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  rw [Units.val_inv_eq_inv_val] at hn
  rw [zpow_neg]
  field_simp at hn ⊢
  rw [hn]

omit [CompleteSpace K] in
theorem norm_one_add_q_pow (n : ℕ) : ‖(1 : K) + (t.q : K) ^ (n + 1)‖ = 1 := by
  have hlt : ‖(t.q : K) ^ (n + 1)‖ < ‖(1 : K)‖ := by
    rw [norm_one, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) t.norm_lt_one (Nat.succ_ne_zero n)
  rw [add_comm, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le,
    norm_one]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- For units of norm one, `a = qᵏ b` forces `k = 0`. -/
theorem eq_of_eq_q_zpow_mul {a b : K} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {k : ℤ}
    (h : a = (t.q : K) ^ k * b) : a = b := by
  have hq : 0 < ‖(t.q : K)‖ := norm_pos_iff.mpr t.q.ne_zero
  have hn : ‖(t.q : K)‖ ^ k = 1 := by
    have := congrArg norm h
    rwa [norm_mul, norm_zpow, ha, hb, mul_one, eq_comm] at this
  have hk : k = 0 := by
    rcases lt_trichotomy k 0 with hk | hk | hk
    · exact absurd hn (one_lt_zpow_of_neg₀ hq t.norm_lt_one hk).ne'
    · exact hk
    · exact absurd hn (zpow_lt_one₀ hq t.norm_lt_one hk).ne
  rw [h, hk, zpow_zero, one_mul]

/-- The units `uₙ = 1 + q^{n+1}`. -/
def unitSeq (n : ℕ) : Kˣ :=
  Units.mk0 (1 + (t.q : K) ^ (n + 1)) fun h => by
    have := norm_one_add_q_pow t n
    rw [h, norm_zero] at this
    exact zero_ne_one this

omit [CompleteSpace K] in
theorem offOrbit_unitSeq (n : ℕ) : OffOrbit t (unitSeq t n) := by
  intro k hk
  have h1 : (unitSeq t n : K) = (t.q : K) ^ (-k) * 1 := by
    rw [zpow_neg, mul_one]
    field_simp
    rw [mul_comm]; exact hk
  have := eq_of_eq_q_zpow_mul t (norm_one_add_q_pow t n) norm_one h1
  simp only [add_eq_left] at this
  exact pow_ne_zero _ t.q.ne_zero this

omit [CompleteSpace K] in
theorem unitSeq_injective : Function.Injective (unitSeq t) := by
  intro a b h
  have h' : (t.q : K) ^ (a + 1) = (t.q : K) ^ (b + 1) := by
    have := congrArg Units.val h
    simpa [unitSeq] using this
  have hn := congrArg norm h'
  rw [norm_pow, norm_pow] at hn
  have := (pow_right_strictAnti₀ (norm_pos_iff.mpr t.q.ne_zero) t.norm_lt_one).injective hn
  omega

/-- The values of `X` off the period orbit are infinite in number. -/
theorem infinite_range_X :
    Set.Infinite (Set.range fun u : {u : Kˣ // OffOrbit t u} => t.X u) := by
  intro hfin
  let f : ℕ → Set.range (fun u : {u : Kˣ // OffOrbit t u} => t.X u) :=
    fun n => ⟨t.X (unitSeq t n), ⟨⟨_, offOrbit_unitSeq t n⟩, rfl⟩⟩
  haveI : Finite (Set.range fun u : {u : Kˣ // OffOrbit t u} => t.X u) := hfin.to_subtype
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  have hS : Set.Infinite (f ⁻¹' {y}) := Set.infinite_coe_iff.mp hy
  obtain ⟨a, ha, -⟩ := hS.exists_gt 0
  obtain ⟨b, hb, hab⟩ := hS.exists_gt a
  obtain ⟨c, hc, hbc⟩ := hS.exists_gt b
  -- equal `X` forces `u_m = u_n⁻¹` for `m ≠ n`
  have key : ∀ m n : ℕ, m ≠ n → f m = f n → (unitSeq t m : K) = ((unitSeq t n)⁻¹ : Kˣ) := by
    intro m n hmn hf
    have hX : t.X (unitSeq t m) = t.X (unitSeq t n) := congrArg Subtype.val hf
    have hnorm : ∀ l, ‖(unitSeq t l : K)‖ = 1 := fun l => norm_one_add_q_pow t l
    have hninv : ∀ l, ‖((unitSeq t l)⁻¹ : Kˣ).val‖ = 1 := fun l => by
      rw [Units.val_inv_eq_inv_val, norm_inv, hnorm, inv_one]
    rcases t.class_eq_or_inv_of_X_eq (offOrbit_unitSeq t m) (offOrbit_unitSeq t n) hX with
      ⟨k, hk⟩ | ⟨k, hk⟩
    · exact absurd (unitSeq_injective t (Units.ext (eq_of_eq_q_zpow_mul t (hnorm m) (hnorm n) hk)))
        hmn
    · exact eq_of_eq_q_zpow_mul t (hnorm m) (hninv n) hk
  have e1 := key a b hab.ne (by rw [show f a = y from ha, show f b = y from hb])
  have e2 := key a c (hab.trans hbc).ne (by rw [show f a = y from ha, show f c = y from hc])
  have : unitSeq t b = unitSeq t c := by
    have h' : ((unitSeq t b)⁻¹ : Kˣ) = (unitSeq t c)⁻¹ := Units.ext (e1.symm.trans e2)
    exact inv_injective h'
  exact hbc.ne (unitSeq_injective t this)

/-- **Independence of `Xⁱ`, `XⁱY` as functions on the Tate curve**: if
`P(X(u)) + Y(u)·Q(X(u)) = 0` off the period orbit, then `P = Q = 0`. -/
theorem poly_eq_zero_of_eval (h12 : (12 : K) ≠ 0) (P Q : Polynomial K)
    (h : ∀ u : Kˣ, OffOrbit t u → P.eval (t.X u) + t.Y u * Q.eval (t.X u) = 0) :
    P = 0 ∧ Q = 0 := by
  have hinv : ∀ u, OffOrbit t u → (2 * t.Y u + t.X u) * Q.eval (t.X u) = 0 := by
    intro u hu
    have h1 := h u hu
    have h2 := h u⁻¹ (offOrbit_inv t hu)
    rw [t.X_inv hu, t.Y_inv hu] at h2
    linear_combination h1 - h2
  set C : Polynomial K := Polynomial.C (4 : K) * Polynomial.X ^ 3 + Polynomial.X ^ 2 +
    Polynomial.C (4 * t.a₄) * Polynomial.X + Polynomial.C (4 * t.a₆) with hCdef
  have hC : C ≠ 0 := by
    intro h0
    have := congrArg (fun p : Polynomial K => p.coeff 2) h0
    simp [hCdef, Polynomial.coeff_X_pow] at this
  have hroot : ∀ u, OffOrbit t u → (Q * C).eval (t.X u) = 0 := by
    intro u hu
    rw [Polynomial.eval_mul]
    by_cases hQ : Q.eval (t.X u) = 0
    · rw [hQ, zero_mul]
    · have hY : 2 * t.Y u + t.X u = 0 := (mul_eq_zero.mp (hinv u hu)).resolve_right hQ
      have hdef := t.tateDefect_eq_zero h12 hu
      rw [tateDefect_apply] at hdef
      have : C.eval (t.X u) = 0 := by
        simp only [hCdef, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C]
        linear_combination (-4 : K) * hdef + (2 * t.Y u + t.X u) * hY
      rw [this, mul_zero]
  have hinf : ∀ R : Polynomial K, (∀ u, OffOrbit t u → R.eval (t.X u) = 0) → R = 0 := by
    intro R hR
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine (infinite_range_X t).mono ?_
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    exact hR u hu
  have hQ0 : Q = 0 := by
    by_contra hQ
    exact mul_ne_zero hQ hC (hinf _ hroot)
  refine ⟨hinf P fun u hu => ?_, hQ0⟩
  have := h u hu
  rwa [hQ0, Polynomial.eval_zero, mul_zero, add_zero] at this

/-! ### The dimension count -/

theorem theta_neg_ne_zero {u : Kˣ} (hu : OffOrbit t u) : t.theta (-u) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff (-u)).mp h
  apply hu (-k)
  rw [Units.val_neg, neg_inj] at hk
  rw [hk, ← zpow_add₀ t.q.ne_zero, neg_add_cancel, zpow_zero]

/-- Index set of the monomials `Xⁱ` (`2i ≤ k`) and `XⁱY` (`2i + 3 ≤ k`). -/
abbrev MonoIdx (k : ℕ) : Type := Fin (k / 2 + 1) ⊕ Fin ((k - 1) / 2)

theorem card_monoIdx {k : ℕ} (hk : 0 < k) : Fintype.card (MonoIdx k) = k := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- The monomial families, as elements of the weight space `W(k, Aθᵏ)`. -/
def monoBasis (k : ℕ) : MonoIdx k → t.weightSpace k (multθ t ^ k)
  | Sum.inl i => ⟨monoX t k i, isWeightFamily_monoX t (by omega)⟩
  | Sum.inr i => ⟨monoXY t k i, isWeightFamily_monoXY t (by have := i.2; omega)⟩

/-- The polynomial `∑ aᵢ xⁱ` with coefficients indexed by `Fin m`. -/
def polyOf {m : ℕ} (a : Fin m → K) : Polynomial K :=
  ∑ i : Fin m, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem coeff_polyOf {m : ℕ} (a : Fin m → K) (i : Fin m) : (polyOf a).coeff i = a i := by
  simp only [polyOf, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have : (i : ℕ) ≠ j := fun h => hj (Fin.ext h.symm)
    simp [this]
  · simp

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem eval_polyOf {m : ℕ} (a : Fin m → K) (x : K) :
    (polyOf a).eval x = ∑ i : Fin m, a i * x ^ (i : ℕ) := by
  simp [polyOf, Polynomial.eval_finsetSum]

/-- **The value of a linear combination of monomial families**:
`∑ g_s (mono_s)(u) = (P_g(X(u)) + Y(u)·Q_g(X(u)))·θ(-u)ᵏ`. -/
theorem tsum_monoBasis_comb {k : ℕ} (g : MonoIdx k → K) {u : Kˣ} (hu : OffOrbit t u) :
    (∑' n : ℤ, ((∑ s, g s • monoBasis t k s : t.weightSpace k (multθ t ^ k)) : ℤ → K) n *
        (u : K) ^ n) =
      ((polyOf fun i => g (Sum.inl i)).eval (t.X u) +
        t.Y u * (polyOf fun i => g (Sum.inr i)).eval (t.X u)) * t.theta (-u) ^ k := by
  have hsum : ∀ s, Summable fun n : ℤ => (monoBasis t k s : ℤ → K) n * (u : K) ^ n :=
    fun s => (monoBasis t k s).2.summable u
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [Summable.tsum_finsetSum fun s _ => ((hsum s).mul_left (g s)).congr fun n => by ring]
  · simp only [mul_assoc]
    simp_rw [tsum_mul_left]
    rw [Fintype.sum_sum_type, eval_polyOf, eval_polyOf]
    simp only [monoBasis]
    have e1 : ∀ i : Fin (k / 2 + 1), (∑' n : ℤ, monoX t k i n * (u : K) ^ n) =
        t.X u ^ (i : ℕ) * t.theta (-u) ^ k := fun i => tsum_monoX t (by omega) hu
    have e2 : ∀ i : Fin ((k - 1) / 2), (∑' n : ℤ, monoXY t k i n * (u : K) ^ n) =
        t.X u ^ (i : ℕ) * t.Y u * t.theta (-u) ^ k :=
      fun i => tsum_monoXY t (by have := i.2; omega) hu
    simp only [e1, e2, add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring

theorem linearIndependent_monoBasis (h12 : (12 : K) ≠ 0) (k : ℕ) :
    LinearIndependent K (monoBasis t k) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hval : ∀ u : Kˣ, OffOrbit t u →
      (polyOf fun i => g (Sum.inl i)).eval (t.X u) +
        t.Y u * (polyOf fun i => g (Sum.inr i)).eval (t.X u) = 0 := by
    intro u hu
    have := tsum_monoBasis_comb t g hu
    rw [hg] at this
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply, zero_mul, tsum_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right (pow_ne_zero _ (theta_neg_ne_zero t hu))
  obtain ⟨hP, hQ⟩ := poly_eq_zero_of_eval t h12 _ _ hval
  rintro (i | i)
  · have := coeff_polyOf (fun i => g (Sum.inl i)) i
    rw [hP, Polynomial.coeff_zero] at this
    exact this.symm
  · have := coeff_polyOf (fun i => g (Sum.inr i)) i
    rw [hQ, Polynomial.coeff_zero] at this
    exact this.symm

/-- **Tate's theorem for theta functions** (weight `k ≥ 1`, multiplier of `θ(-u)ᵏ`): every
weight family has values `(P(X(u)) + Y(u)·Q(X(u)))·θ(-u)ᵏ` off the period orbit. -/
theorem exists_poly_of_isWeightFamily (h12 : (12 : K) ≠ 0) {k : ℕ} (hk : 0 < k) {F : ℤ → K}
    (hF : t.IsWeightFamily k (multθ t ^ k) F) :
    ∃ P Q : Polynomial K, ∀ u : Kˣ, OffOrbit t u →
      (∑' n : ℤ, F n * (u : K) ^ n) =
        (P.eval (t.X u) + t.Y u * Q.eval (t.X u)) * t.theta (-u) ^ k := by
  haveI := finiteDimensional_weightSpace (t := t) (A := multθ t ^ k) hk
  have hli := linearIndependent_monoBasis t h12 k
  have hspan : Submodule.span K (Set.range (monoBasis t k)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by
      rw [card_monoIdx hk, finrank_weightSpace hk])
  have hmem : (⟨F, hF⟩ : t.weightSpace k (multθ t ^ k)) ∈
      Submodule.span K (Set.range (monoBasis t k)) := hspan ▸ Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
  refine ⟨polyOf fun i => g (Sum.inl i), polyOf fun i => g (Sum.inr i), fun u hu => ?_⟩
  rw [← tsum_monoBasis_comb t g hu, hg]

end Iut.EtaleTheta
