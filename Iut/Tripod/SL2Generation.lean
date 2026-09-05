/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib

/-!
# Subgroups of `GL₂(𝔽_ℓ)` containing a transvection and stabilizing no line

The group theory behind [GenEll], Lemma 3.1(iii) (Serre, *Abelian ℓ-adic representations*,
IV-3.2, Lemma 2): a subgroup `G ≤ GL₂(𝔽_ℓ)` (`ℓ` prime) that contains a transvection `T ≠ 1`
(`(T − 1)² = 0`) and stabilizes no line contains `SL₂(𝔽_ℓ)`
(`Iut.SL2.toGL_mem_of_transvection`).

The proof: `N = T − 1` has `N² = 0`, `N ≠ 0`, so `N` has a nonzero vector `v` with `Nv = 0`.
Some `g ∈ G` has `w = gv ∉ 𝔽_ℓ·v`, and in the basis `(v, w)` the elements `T` and `gTg⁻¹`
become the elementary matrices `E₁₂(b)`, `E₂₁(c)` with `b, c ≠ 0`. Their powers give all
`E₁₂(x)`, `E₂₁(y)` (`𝔽_ℓ` is a prime field), and the elementary matrices generate `SL₂`
(`Matrix.SpecialLinearGroup.SL2.transvection_induction`).

An element of order `ℓ` of `GL₂(𝔽_ℓ)` is such a transvection (`Iut.SL2.transvection_of_orderOf`):
`(M − 1)^ℓ = M^ℓ − 1 = 0`, and a nilpotent `2 × 2` matrix squares to zero.
-/

namespace Iut.SL2

open Matrix Polynomial
open scoped MatrixGroups

/-! ### Nilpotent `2 × 2` matrices -/

/-- A nilpotent `2 × 2` matrix over a field squares to zero. -/
lemma sq_eq_zero_of_isNilpotent {F : Type*} [Field F] {N : Matrix (Fin 2) (Fin 2) F}
    (hN : IsNilpotent N) : N ^ 2 = 0 := by
  have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
  rw [Fintype.card_fin] at h
  have h0 : N.charpoly = X ^ 2 := sub_eq_zero.mp h.eq_zero
  have := Matrix.aeval_self_charpoly N
  rwa [h0, aeval_X_pow] at this

/-- An element of order `ℓ` of `GL₂(𝔽_ℓ)` is a transvection `≠ 1`. -/
lemma transvection_of_orderOf {ℓ : ℕ} [Fact ℓ.Prime] (M : GL (Fin 2) (ZMod ℓ))
    (hM : orderOf M = ℓ) :
    M ≠ 1 ∧ ((M : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) - 1) ^ 2 = 0 := by
  have hℓ : ℓ.Prime := Fact.out
  refine ⟨fun h => ?_, ?_⟩
  · rw [h, orderOf_one] at hM
    exact hℓ.one_lt.ne hM
  have hpow : (M : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ^ ℓ = 1 := by
    have := pow_orderOf_eq_one M
    rw [hM] at this
    have := congrArg Units.val this
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  apply sq_eq_zero_of_isNilpotent
  refine ⟨ℓ, ?_⟩
  rw [sub_pow_char_of_commute ℓ (Commute.one_right _), hpow, one_pow, sub_self]

/-! ### The generation lemma -/

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- A nonzero vector `v` with `N v = 0` and `v = N w₀`, for `N ≠ 0` with `N² = 0`. -/
lemma exists_vec_of_sq_eq_zero {N : Matrix (Fin 2) (Fin 2) (ZMod ℓ)} (hN : N ≠ 0)
    (hN2 : N ^ 2 = 0) : ∃ v : Fin 2 → ZMod ℓ, v ≠ 0 ∧ N *ᵥ v = 0 := by
  have : ∃ j, N.col j ≠ 0 := by
    by_contra h
    apply hN
    ext i j
    have hj : N.col j = 0 := by
      by_contra hj
      exact h ⟨j, hj⟩
    simpa using congrFun hj i
  obtain ⟨j, hj⟩ := this
  refine ⟨N *ᵥ Pi.single j 1, by rwa [mulVec_single_one], ?_⟩
  rw [mulVec_mulVec, ← sq, hN2, zero_mulVec]

/-- The matrix with columns `v`, `w`. -/
def colMat (v w : Fin 2 → ZMod ℓ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := !![v 0, w 0; v 1, w 1]

lemma colMat_mulVec_zero (v w : Fin 2 → ZMod ℓ) : colMat v w *ᵥ Pi.single 0 1 = v := by
  ext i
  fin_cases i <;> simp [colMat, mulVec, dotProduct, Fin.sum_univ_two]

lemma colMat_mulVec_one (v w : Fin 2 → ZMod ℓ) : colMat v w *ᵥ Pi.single 1 1 = w := by
  ext i
  fin_cases i <;> simp [colMat, mulVec, dotProduct, Fin.sum_univ_two]

/-- If `w` is not a multiple of `v ≠ 0`, the matrix with columns `v`, `w` is invertible. -/
lemma det_colMat_ne_zero {v w : Fin 2 → ZMod ℓ} (hv : v ≠ 0) (hw : ∀ c : ZMod ℓ, w ≠ c • v) :
    (colMat v w).det ≠ 0 := by
  intro hdet
  rw [colMat, det_fin_two_of] at hdet
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp [h0, h1]
    rw [h0, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero] at hdet
    have hw0 : w 0 = 0 := hdet.resolve_right h1
    apply hw (w 1 / v 1)
    ext i
    fin_cases i
    · simp [hw0, h0]
    · simp [div_mul_cancel₀ _ h1]
  · apply hw (w 0 / v 0)
    ext i
    fin_cases i
    · simp [div_mul_cancel₀ _ h0]
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination hdet

/-- A `2 × 2` matrix `N` with `N² = 0` whose first column vanishes is `b · E₁₂`. -/
lemma eq_single_zero_one_of_col_zero {N : Matrix (Fin 2) (Fin 2) (ZMod ℓ)} (hN2 : N ^ 2 = 0)
    (h00 : N 0 0 = 0) (h10 : N 1 0 = 0) : N = Matrix.single 0 1 (N 0 1) := by
  have h11 : N 1 1 = 0 := by
    have := congrFun (congrFun hN2 1) 1
    simp only [sq, mul_apply, Fin.sum_univ_two, h10, zero_mul, zero_add, Matrix.zero_apply] at this
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [sq]; exact this)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

/-- A `2 × 2` matrix `N` with `N² = 0` whose second column vanishes is `c · E₂₁`. -/
lemma eq_single_one_zero_of_col_zero {N : Matrix (Fin 2) (Fin 2) (ZMod ℓ)} (hN2 : N ^ 2 = 0)
    (h01 : N 0 1 = 0) (h11 : N 1 1 = 0) : N = Matrix.single 1 0 (N 1 0) := by
  have h00 : N 0 0 = 0 := by
    have := congrFun (congrFun hN2 0) 0
    simp only [sq, mul_apply, Fin.sum_univ_two, h01, zero_mul, add_zero, Matrix.zero_apply] at this
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [sq]; exact this)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h11]

open Matrix.SpecialLinearGroup in
/-- Powers of a transvection. -/
lemma transvection_pow {i j : Fin 2} (hij : i ≠ j) (b : ZMod ℓ) (k : ℕ) :
    (SpecialLinearGroup.transvection hij b) ^ k = SpecialLinearGroup.transvection hij (k • b) := by
  induction k with
  | zero => rw [pow_zero, zero_smul, transvection_coeff_zero]
  | succ k ih => rw [pow_succ, ih, succ_nsmul, transvection_add]

open Matrix.SpecialLinearGroup in
/-- Every transvection `E_{ij}(c)` is a power of `E_{ij}(b)` for `b ≠ 0` (`𝔽_ℓ` is a prime
field). -/
lemma transvection_eq_pow {i j : Fin 2} (hij : i ≠ j) {b : ZMod ℓ} (hb : b ≠ 0) (c : ZMod ℓ) :
    SpecialLinearGroup.transvection hij c =
      (SpecialLinearGroup.transvection hij b) ^ (c * b⁻¹).val := by
  rw [transvection_pow]
  congr 1
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val, inv_mul_cancel_right₀ hb]

open Matrix.SpecialLinearGroup in
/-- **A subgroup of `GL₂(𝔽_ℓ)` containing a transvection and stabilizing no line contains
`SL₂(𝔽_ℓ)`** (Serre, *Abelian ℓ-adic representations*, IV-3.2, Lemma 2). -/
theorem toGL_mem_of_transvection (G : Subgroup (GL (Fin 2) (ZMod ℓ))) {T : GL (Fin 2) (ZMod ℓ)}
    (hTG : T ∈ G) (hT1 : T ≠ 1) (hT2 : ((T : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) - 1) ^ 2 = 0)
    (hline : ∀ v : Fin 2 → ZMod ℓ, v ≠ 0 →
      ∃ g ∈ G, ∀ c : ZMod ℓ, (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ v ≠ c • v)
    (A : SL(2, ZMod ℓ)) : A.toGL ∈ G := by
  set N : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := (T : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) - 1 with hN
  have hN0 : N ≠ 0 := by
    intro h
    apply hT1
    ext i j
    have := congrFun (congrFun h i) j
    simpa [hN, sub_eq_zero] using this
  obtain ⟨v, hv, hNv⟩ := exists_vec_of_sq_eq_zero hN0 hT2
  obtain ⟨g, hgG, hgv⟩ := hline v hv
  set w := (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ v with hw
  set P := colMat v w with hPdef
  have hdet : P.det ≠ 0 := det_colMat_ne_zero hv hgv
  have hdetU : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  have hPQ : P * P⁻¹ = 1 := mul_nonsing_inv P hdetU
  have hQP : P⁻¹ * P = 1 := nonsing_inv_mul P hdetU
  have hcP : ∀ X : Matrix (Fin 2) (Fin 2) (ZMod ℓ), P * (P⁻¹ * X) = X :=
    fun X => mul_nonsing_inv_cancel_left P X hdetU
  have hcQ : ∀ X : Matrix (Fin 2) (Fin 2) (ZMod ℓ), P⁻¹ * (P * X) = X :=
    fun X => nonsing_inv_mul_cancel_left P X hdetU
  have hgg : (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) * ((g⁻¹ : GL (Fin 2) (ZMod ℓ)) :
      Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgg' : ((g⁻¹ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *
      (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcg : ∀ X : Matrix (Fin 2) (Fin 2) (ZMod ℓ), (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *
      (((g⁻¹ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) * X) = X :=
    fun X => Units.mul_inv_cancel_left g X
  have hcg' : ∀ X : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      ((g⁻¹ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *
        ((g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) * X) = X :=
    fun X => Units.inv_mul_cancel_left g X
  -- the conjugate of `N` by `P` is `b · E₁₂` with `b ≠ 0`
  set N₁ := P⁻¹ * N * P with hN₁
  have hN₁sq : N₁ ^ 2 = 0 := by
    have : N₁ ^ 2 = P⁻¹ * (N ^ 2) * P := by
      simp only [hN₁, sq, mul_assoc, hcP]
    rw [this, hT2, mul_zero, zero_mul]
  have hN₁col : N₁ *ᵥ Pi.single 0 1 = 0 := by
    rw [hN₁, ← mulVec_mulVec, ← mulVec_mulVec, hPdef, colMat_mulVec_zero, hNv, mulVec_zero]
  have hN₁eq : N₁ = Matrix.single 0 1 (N₁ 0 1) := by
    refine eq_single_zero_one_of_col_zero hN₁sq ?_ ?_
    · have := congrFun hN₁col 0
      rwa [mulVec_single_one] at this
    · have := congrFun hN₁col 1
      rwa [mulVec_single_one] at this
  have hNconj : N = P * N₁ * P⁻¹ := by
    simp only [hN₁, mul_assoc, hcP, hPQ, mul_one]
  have hb : N₁ 0 1 ≠ 0 := by
    intro hb
    apply hN0
    have h1 : N₁ = 0 := by rw [hN₁eq, hb, Matrix.single_zero]
    rw [hNconj, h1, mul_zero, zero_mul]
  -- the conjugate of `gNg⁻¹` by `P` is `c · E₂₁` with `c ≠ 0`
  set N' : Matrix (Fin 2) (Fin 2) (ZMod ℓ) :=
    (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) * N * ((g⁻¹ : GL (Fin 2) (ZMod ℓ)) :
      Matrix (Fin 2) (Fin 2) (ZMod ℓ)) with hN'
  have hN'sq : N' ^ 2 = 0 := by
    have : N' ^ 2 = (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) * (N ^ 2) *
        ((g⁻¹ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := by
      simp only [hN', sq, mul_assoc, hcg']
    rw [this, hT2, mul_zero, zero_mul]
  have hN'w : N' *ᵥ w = 0 := by
    rw [hN', hw, mulVec_mulVec, Units.inv_mul_cancel_right, ← mulVec_mulVec, hNv, mulVec_zero]
  set N₂ := P⁻¹ * N' * P with hN₂
  have hN₂sq : N₂ ^ 2 = 0 := by
    have : N₂ ^ 2 = P⁻¹ * (N' ^ 2) * P := by
      simp only [hN₂, sq, mul_assoc, hcP]
    rw [this, hN'sq, mul_zero, zero_mul]
  have hN₂col : N₂ *ᵥ Pi.single 1 1 = 0 := by
    rw [hN₂, ← mulVec_mulVec, ← mulVec_mulVec, hPdef, colMat_mulVec_one, hN'w, mulVec_zero]
  have hN₂eq : N₂ = Matrix.single 1 0 (N₂ 1 0) := by
    refine eq_single_one_zero_of_col_zero hN₂sq ?_ ?_
    · have := congrFun hN₂col 0
      rwa [mulVec_single_one] at this
    · have := congrFun hN₂col 1
      rwa [mulVec_single_one] at this
  have hN'conj : N' = P * N₂ * P⁻¹ := by
    simp only [hN₂, mul_assoc, hcP, hPQ, mul_one]
  have hc : N₂ 1 0 ≠ 0 := by
    intro hc
    apply hN0
    have h1 : N₂ = 0 := by rw [hN₂eq, hc, Matrix.single_zero]
    have h3 : N = ((g⁻¹ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) * N' *
        (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := by
      simp only [hN', mul_assoc, hcg', hgg', mul_one]
    rw [h3, hN'conj, h1]
    simp
  -- the subgroup of elements whose conjugate by `P` lies in `G`
  let Pu : GL (Fin 2) (ZMod ℓ) := Matrix.GeneralLinearGroup.mkOfDetNeZero P hdet
  have hPu : (Pu : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = P := rfl
  have hPuinv : ((Pu⁻¹ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = P⁻¹ := by
    rw [Matrix.coe_units_inv, hPu]
  let H : Subgroup (GL (Fin 2) (ZMod ℓ)) := G.comap (MulAut.conj Pu).toMonoidHom
  have hH : ∀ M : GL (Fin 2) (ZMod ℓ), M ∈ H ↔ Pu * M * Pu⁻¹ ∈ G := fun M => Iff.rfl
  -- `E₁₂(b) ∈ H`
  have hE₁₂ : (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1)
      (N₁ 0 1)).toGL ∈ H := by
    rw [hH]
    convert hTG using 1
    apply Units.ext
    simp only [Units.val_mul, hPuinv, hPu]
    have : (((SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1)
        (N₁ 0 1)).toGL : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = 1 + N₁ := by
      change 1 + Matrix.single 0 1 (N₁ 0 1) = 1 + N₁
      exact congrArg _ hN₁eq.symm
    rw [this, mul_add, add_mul, mul_one, hPQ, ← hNconj, hN, add_sub_cancel]
  -- `E₂₁(c) ∈ H`
  have hE₂₁ : (SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0)
      (N₂ 1 0)).toGL ∈ H := by
    rw [hH]
    convert G.mul_mem (G.mul_mem hgG hTG) (G.inv_mem hgG) using 1
    apply Units.ext
    simp only [Units.val_mul, hPuinv, hPu]
    have : (((SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0)
        (N₂ 1 0)).toGL : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = 1 + N₂ := by
      change 1 + Matrix.single 1 0 (N₂ 1 0) = 1 + N₂
      exact congrArg _ hN₂eq.symm
    rw [this, mul_add, add_mul, mul_one, hPQ, ← hN'conj, hN', hN]
    simp only [mul_sub, sub_mul, mul_one, hgg]
    abel
  -- all transvections lie in `H`, hence `SL₂`
  have hSL : ∀ B : SL(2, ZMod ℓ), B.toGL ∈ H := by
    intro B
    refine SL2.transvection_induction (fun B => B.toGL ∈ H) ?_ ?_ B
    · intro i j hij c
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · rw [transvection_eq_pow _ hb c, map_pow]
        exact H.pow_mem hE₁₂ _
      · rw [transvection_eq_pow _ hc c, map_pow]
        exact H.pow_mem hE₂₁ _
      · exact absurd rfl hij
    · intro A B hA hB
      rw [map_mul]
      exact H.mul_mem hA hB
  -- conclude
  have hdetB : (P⁻¹ * (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) * P).det = 1 := by
    rw [det_mul, det_mul, A.det_coe, mul_one, mul_comm, ← det_mul, hPQ, det_one]
  have hB := hSL ⟨P⁻¹ * (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) * P, hdetB⟩
  rw [hH] at hB
  convert hB using 1
  apply Units.ext
  simp only [Units.val_mul, hPuinv, hPu]
  have hval : ((SpecialLinearGroup.toGL (⟨P⁻¹ * (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) * P,
      hdetB⟩ : SL(2, ZMod ℓ)) : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) =
      P⁻¹ * (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) * P := rfl
  rw [hval]
  simp only [mul_assoc, hcP, hPQ, mul_one]
  rfl

end Iut.SL2
