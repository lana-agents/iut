/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.TorsionDegree
import Iut.Cor312.ThetaData.VariableChangePoint

/-!
# `F_λ/ℚ(j)` is Galois of degree prime to `ℓ ≥ 7`

For a point `λ` of the tripod with `E_λ[3](ℚ̄)`, `E_λ[5](ℚ̄)` finite, the field of definition
`F_λ = ℚ(λ, √−1, √λ, √(1 − λ), E_λ[3], E_λ[5]) ⊆ ℚ̄` of the Legendre curve is Galois over the
field of moduli `F_mod = ℚ(j(E_λ))`, of degree prime to every prime `ℓ ≥ 7`
(`Iut.Tripod.galois_deg_prime_of_torsion_basis`, the field `galois_deg_prime` of
`Iut.EllipticCurveData.CurveArithmetic` for `curveOf x h3 h5`).

## The Galois property

`ℚ̄/ℚ(j)` is Galois, so `F_λ/ℚ(j)` is normal iff `σ(F_λ) ⊆ F_λ` for every
`σ ∈ Gal(ℚ̄/ℚ(j))` (`IntermediateField.normal_iff_forall_map_le'`). Such a `σ` fixes
`j = 256(λ² − λ + 1)³/(λ²(λ − 1)²)`, so `μ = σ(λ)` is a root of
`256(T² − T + 1)³ − j·T²(T − 1)²`, whose six roots are the **conjugates**
`λ, 1 − λ, 1/λ, 1/(1 − λ), 1 − 1/λ, 1 − 1/(1 − λ)` of `λ` (`Iut.Tripod.Conj`, from the
factorisation `Iut.Tripod.conj_of_j_eq`). Then

* `μ ∈ ℚ(λ) ⊆ F_λ`;
* `σ(√−1) = ±√−1`, `σ(√λ)² = μ` and `σ(√(1 − λ))² = 1 − μ`, and `F_λ` contains square
  roots of all the conjugates (`Iut.Tripod.conj_exists_sq`: e.g.
  `√(1 − 1/λ) = √−1·√(1 − λ)/√λ`), so `σ(√λ), σ(√(1 − λ)) ∈ F_λ`;
* `σ` maps `E_λ[n](ℚ̄)` onto `E_μ[n](ℚ̄)` (`Iut.Anabelian.pointMap`), and `E_μ[n] ⊆ F_λ` since
  `E_μ ≅ E_λ` over `F_λ`: `E_{1−λ} = ⟨√−1, 1, 0, 0⟩ • E_λ` and `E_{1/λ} = ⟨√λ, 0, 0, 0⟩ • E_λ`
  (`Iut.Tripod.legendre_vc_one_sub`, `legendre_vc_inv`), and a change of variables
  `(u, r, s, t)` with `u, r, s, t ∈ F_λ` identifies the points of the two curves as groups
  (`Iut.Anabelian.vcEquiv`), preserving `n`-torsion (`Iut.Tripod.torsionCoords_subset_of_vc`).

## The degree

`[F_λ : ℚ(j)]` is the product of the relative degrees of the tower
`ℚ(j) ⊆ ℚ(λ) ⊆ ℚ(λ, √−1) ⊆ ℚ(λ, √−1, √λ) ⊆ ℚ(λ, √−1, √λ, √(1 − λ)) ⊆ …(E_λ[3]) ⊆ F_λ`,
of degrees `≤ 6` (`λ` is a root of the degree-`6` polynomial above), `≤ 2`, `≤ 2`, `≤ 2`,
`∣ |GL₂(𝔽_3)| = 48` and `∣ |GL₂(𝔽_5)| = 480` (the torsion field `K(E_λ[n])` is the fixed
field of the kernel of the mod-`n` representation `Gal(ℚ̄/K) → GL₂(ℤ/n)`, so its degree is
the order of the image, `Iut/Tripod/TorsionDegree.lean`); each factor is prime to `ℓ ≥ 7`.

The statements about `F_mod = ℚ(j) ⊆ F_λ` as an intermediate field of `F_λ` are transferred
to `ℚ(j) ⊆ ℚ̄` (`Iut.Tripod.isGalois_of_lift_eq`, `finrank_eq_relfinrank_of_lift_eq`).
-/

namespace Iut.Tripod

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

open scoped Classical IntermediateField

/-! ### The Legendre curves of `1 − λ` and `1/λ` as changes of variables of `E_λ` -/

/-- `E_{1−λ} = ⟨√−1, 1, 0, 0⟩ • E_λ`: the change of variables `(x, y) ↦ (1 − x, √−1·y)`. -/
theorem legendre_vc_one_sub {i : Qbar} (hi : i ^ 2 = -1) (hi0 : i ≠ 0) (l : Qbar) :
    (⟨Units.mk0 i hi0, 1, 0, 0⟩ : VariableChange Qbar) • legendre l = legendre (1 - l) := by
  have h4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hi]; norm_num
  have h6 : i ^ 6 = -1 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hi]; norm_num
  ext
  · simp [variableChange_a₁]
  · simp only [variableChange_a₂, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hi,
      legendre_a₂, legendre_a₁]
    ring
  · simp [variableChange_a₃]
  · simp only [variableChange_a₄, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, h4,
      legendre_a₄, legendre_a₃, legendre_a₂, legendre_a₁]
    ring
  · simp only [variableChange_a₆, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, h6,
      legendre_a₆, legendre_a₄, legendre_a₃, legendre_a₂, legendre_a₁]
    ring

/-- `E_{1/λ} = ⟨√λ, 0, 0, 0⟩ • E_λ`: the change of variables `(x, y) ↦ (λx, λ√λ·y)`. -/
theorem legendre_vc_inv {u l : Qbar} (hu : u ^ 2 = l) (hu0 : u ≠ 0) :
    (⟨Units.mk0 u hu0, 0, 0, 0⟩ : VariableChange Qbar) • legendre l = legendre l⁻¹ := by
  have hl : l ≠ 0 := by rw [← hu]; exact pow_ne_zero _ hu0
  have h4 : u ^ 4 = l ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hu]
  ext
  · simp [variableChange_a₁]
  · simp only [variableChange_a₂, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hu,
      legendre_a₂, legendre_a₁]
    field_simp
    ring
  · simp [variableChange_a₃]
  · simp only [variableChange_a₄, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, h4,
      legendre_a₄, legendre_a₃, legendre_a₂, legendre_a₁]
    field_simp
    ring
  · simp only [variableChange_a₆, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow,
      legendre_a₆, legendre_a₄, legendre_a₃, legendre_a₂, legendre_a₁]
    ring

/-! ### Transport of the torsion coordinates along a change of variables -/

/-- Torsion is transported along an equality of curves. -/
theorem nsmul_some_eq_zero_of_eq {W W' : WeierstrassCurve Qbar} (h : W = W') {x y : Qbar}
    (hW : W.toAffine.Nonsingular x y) (hW' : W'.toAffine.Nonsingular x y) (n : ℕ)
    (hP : n • Affine.Point.some x y hW = 0) : n • Affine.Point.some x y hW' = 0 := by
  subst h
  exact hP

/-- **The torsion coordinates of `E_μ` lie in `F` if those of `E_λ` do**, when
`E_μ = C • E_λ` for a change of variables `C = (u, r, s, t)` with `u, r, s, t ∈ F`: the
isomorphism `E_λ(ℚ̄) ≅ E_μ(ℚ̄)` maps `E_λ[n]` onto `E_μ[n]`, and the coordinates
`((x − r)/u², (y − t − s(x − r))/u³)` of the image of `(x, y)` lie in `F`. -/
theorem torsionCoords_subset_of_vc {l m : Qbar} {C : VariableChange Qbar}
    (h : C • legendre l = legendre m) (F : IntermediateField ℚ Qbar)
    (huF : (C.u : Qbar) ∈ F) (hrF : C.r ∈ F) (hsF : C.s ∈ F) (htF : C.t ∈ F) {n : ℕ}
    (hl : torsionCoords l n ⊆ F) : torsionCoords m n ⊆ F := by
  intro c hc
  obtain ⟨P, hP, hcP⟩ := Set.mem_iUnion₂.mp hc
  cases P with
  | zero => exact absurd hcP id
  | some x' y' hxy' =>
    have hxy'' : (C • legendre l).toAffine.Nonsingular x' y' := h ▸ hxy'
    have hP' : n • Affine.Point.some x' y' hxy'' = 0 :=
      nsmul_some_eq_zero_of_eq h.symm hxy' hxy'' n hP
    obtain ⟨Q, hQP⟩ := Anabelian.vcPoint_surjective C (legendre l) (Affine.Point.some x' y' hxy'')
    have hQn : n • Q = 0 := by
      apply Anabelian.vcPoint_injective C (legendre l)
      change Anabelian.vcHom C (legendre l) (n • Q) = Anabelian.vcHom C (legendre l) 0
      rw [map_nsmul, map_zero, Anabelian.vcHom_apply, hQP]
      exact hP'
    cases Q with
    | zero => exact absurd hQP.symm (Affine.Point.some_ne_zero hxy'')
    | some x y hxy =>
      rw [Anabelian.vcPoint_some, Affine.Point.some.injEq] at hQP
      have hx : x ∈ F := hl (mem_torsionCoords hQn (Set.mem_insert _ _))
      have hy : y ∈ F := hl (mem_torsionCoords hQn (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      rcases hcP with rfl | rfl
      · rw [← hQP.1]
        exact div_mem (sub_mem hx hrF) (pow_mem huF 2)
      · rw [← hQP.2]
        exact div_mem (sub_mem (sub_mem hy htF) (mul_mem hsF (sub_mem hx hrF))) (pow_mem huF 3)

/-! ### The six conjugates of `λ` over `ℚ(j)` -/

/-- **The conjugates of `λ` over `ℚ(j)`**: `μ ∈ {λ, 1 − λ, 1/λ, 1/(1 − λ), 1 − 1/λ,
1 − 1/(1 − λ)}`. -/
def Conj (l m : Qbar) : Prop :=
  m = l ∨ m = 1 - l ∨ m = l⁻¹ ∨ m = (1 - l)⁻¹ ∨ m = 1 - l⁻¹ ∨ m = 1 - (1 - l)⁻¹

/-- The factorisation
`(μ² − μ + 1)³·λ²(λ − 1)² − (λ² − λ + 1)³·μ²(μ − 1)² = ∏ (μ − μᵢ)` (up to the leading
coefficient), for the six conjugates `μᵢ` of `λ`. -/
theorem j_poly_factor (l m : Qbar) :
    (m ^ 2 - m + 1) ^ 3 * (l ^ 2 * (l - 1) ^ 2) - (l ^ 2 - l + 1) ^ 3 * (m ^ 2 * (m - 1) ^ 2) =
      (m - l) * (m - (1 - l)) * (l * m - 1) * ((1 - l) * m - 1) * (l * m - l + 1) *
        ((1 - l) * m + l) := by
  ring

/-- **`j(μ) = j(λ)` implies that `μ` is a conjugate of `λ`.** -/
theorem conj_of_j_eq {l m : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    (h : (m ^ 2 - m + 1) ^ 3 * (l ^ 2 * (l - 1) ^ 2) =
      (l ^ 2 - l + 1) ^ 3 * (m ^ 2 * (m - 1) ^ 2)) :
    Conj l m := by
  have h1 : (1 : Qbar) - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl1)
  have hprod : (m - l) * (m - (1 - l)) * (l * m - 1) * ((1 - l) * m - 1) * (l * m - l + 1) *
      ((1 - l) * m + l) = 0 := by
    rw [← j_poly_factor, h, sub_self]
  simp only [mul_eq_zero, sub_eq_zero] at hprod
  rcases hprod with ((((h | h) | h) | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (eq_inv_of_mul_eq_one_right h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_inv_of_mul_eq_one_right h))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    field_simp
    linear_combination h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    field_simp
    linear_combination h

/-- The conjugates of `λ` are closed under `μ ↦ 1 − μ`. -/
theorem conj_one_sub {l m : Qbar} (h : Conj l m) : Conj l (1 - m) := by
  rcases h with h | h | h | h | h | h <;> subst m
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (sub_sub_cancel 1 l)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · exact Or.inr (Or.inr (Or.inl (sub_sub_cancel 1 l⁻¹)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (sub_sub_cancel 1 (1 - l)⁻¹))))

/-- The conjugates of `λ` lie in every subfield containing `λ`. -/
theorem conj_mem {l m : Qbar} (h : Conj l m) {F : IntermediateField ℚ Qbar} (hl : l ∈ F) :
    m ∈ F := by
  rcases h with h | h | h | h | h | h <;> subst m
  · exact hl
  · exact sub_mem (one_mem _) hl
  · exact inv_mem hl
  · exact inv_mem (sub_mem (one_mem _) hl)
  · exact sub_mem (one_mem _) (inv_mem hl)
  · exact sub_mem (one_mem _) (inv_mem (sub_mem (one_mem _) hl))

/-- **`F_λ` contains a square root of every conjugate of `λ`**: `√(1/λ) = 1/√λ`,
`√(1/(1 − λ)) = 1/√(1 − λ)`, `√(1 − 1/λ) = √−1·√(1 − λ)/√λ`,
`√(1 − 1/(1 − λ)) = √−1·√λ/√(1 − λ)`. -/
theorem conj_exists_sq {l m : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1) (h : Conj l m) :
    ∃ s ∈ fieldOf' l, s ^ 2 = m := by
  have h1 : (1 : Qbar) - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl1)
  have hs0 : sqrtLam l ≠ 0 := fun h0 ↦ hl0 (by rw [← sqrtLam_sq l, h0]; ring)
  have hs1 : sqrtOneSubLam l ≠ 0 := fun h0 ↦ h1 (by rw [← sqrtOneSubLam_sq l, h0]; ring)
  have hi := sqrtNegOne_mem_fieldOf' l
  have hs := sqrtLam_mem_fieldOf' l
  have hs' := sqrtOneSubLam_mem_fieldOf' l
  rcases h with h | h | h | h | h | h <;> subst m
  · exact ⟨sqrtLam l, hs, sqrtLam_sq l⟩
  · exact ⟨sqrtOneSubLam l, hs', sqrtOneSubLam_sq l⟩
  · exact ⟨(sqrtLam l)⁻¹, inv_mem hs, by rw [inv_pow, sqrtLam_sq]⟩
  · exact ⟨(sqrtOneSubLam l)⁻¹, inv_mem hs', by rw [inv_pow, sqrtOneSubLam_sq]⟩
  · refine ⟨sqrtNegOne * sqrtOneSubLam l / sqrtLam l, div_mem (mul_mem hi hs') hs, ?_⟩
    rw [div_pow, mul_pow, sqrtNegOne_sq, sqrtOneSubLam_sq, sqrtLam_sq]
    field_simp
    ring
  · refine ⟨sqrtNegOne * sqrtLam l / sqrtOneSubLam l, div_mem (mul_mem hi hs) hs', ?_⟩
    rw [div_pow, mul_pow, sqrtNegOne_sq, sqrtOneSubLam_sq, sqrtLam_sq]
    field_simp
    ring

/-- **The torsion coordinates of the conjugate curves lie in `F_λ`**: `E_μ ≅ E_λ` over
`F_λ` for every conjugate `μ` of `λ`, by the changes of variables `legendre_vc_one_sub` and
`legendre_vc_inv` with `u ∈ {√−1, √λ, √(1 − λ)}`, `r ∈ {0, 1}`. -/
theorem conj_torsionCoords_subset {l m : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1) (h : Conj l m)
    {n : ℕ} (hn : torsionCoords l n ⊆ fieldOf' l) : torsionCoords m n ⊆ fieldOf' l := by
  have h1 : (1 : Qbar) - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl1)
  have hi0 : sqrtNegOne ≠ 0 := fun h0 ↦ by
    have := sqrtNegOne_sq
    rw [h0, zero_pow two_ne_zero] at this
    exact one_ne_zero (neg_eq_zero.mp this.symm)
  have hs0 : sqrtLam l ≠ 0 := fun h0 ↦ hl0 (by rw [← sqrtLam_sq l, h0]; ring)
  have hs1 : sqrtOneSubLam l ≠ 0 := fun h0 ↦ h1 (by rw [← sqrtOneSubLam_sq l, h0]; ring)
  have hi := sqrtNegOne_mem_fieldOf' l
  have hs := sqrtLam_mem_fieldOf' l
  have hs' := sqrtOneSubLam_mem_fieldOf' l
  -- the chain `λ → 1 − λ → 1/(1 − λ) → 1 − 1/(1 − λ)` and `λ → 1/λ → 1 − 1/λ`
  have h2 : torsionCoords (1 - l) n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_one_sub sqrtNegOne_sq hi0 l) _ hi (one_mem _)
      (zero_mem _) (zero_mem _) hn
  have h3 : torsionCoords l⁻¹ n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_inv (sqrtLam_sq l) hs0) _ hs (zero_mem _)
      (zero_mem _) (zero_mem _) hn
  have h4 : torsionCoords (1 - l)⁻¹ n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_inv (sqrtOneSubLam_sq l) hs1) _ hs' (zero_mem _)
      (zero_mem _) (zero_mem _) h2
  have h5 : torsionCoords (1 - l⁻¹) n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_one_sub sqrtNegOne_sq hi0 l⁻¹) _ hi (one_mem _)
      (zero_mem _) (zero_mem _) h3
  have h6 : torsionCoords (1 - (1 - l)⁻¹) n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_one_sub sqrtNegOne_sq hi0 (1 - l)⁻¹) _ hi
      (one_mem _) (zero_mem _) (zero_mem _) h4
  rcases h with h | h | h | h | h | h <;> subst m
  · exact hn
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

/-! ### The Galois group of `ℚ̄/ℚ(j)` -/

/-- `j(E_λ) = 256(λ² − λ + 1)³/(λ²(λ − 1)²)` as an element of `ℚ̄`. -/
noncomputable def jQ (l : Qbar) : Qbar := 256 * (l ^ 2 - l + 1) ^ 3 / (l ^ 2 * (l - 1) ^ 2)

/-- The field of moduli `ℚ(j) ⊆ ℚ̄`. -/
noncomputable abbrev fieldOfJ (l : Qbar) : IntermediateField ℚ Qbar := ℚ⟮jQ l⟯

theorem jQ_mem_fieldOf (l : Qbar) : jQ l ∈ fieldOf l := by
  have hl : l ∈ fieldOf l := IntermediateField.mem_adjoin_simple_self ℚ l
  have h256 : (256 : Qbar) ∈ fieldOf l := by
    have : (256 : Qbar) = ((256 : ℕ) : Qbar) := by norm_num
    rw [this]
    exact IntermediateField.natCast_mem _ _
  exact div_mem (mul_mem h256 (pow_mem (add_mem (sub_mem (pow_mem hl 2) hl) (one_mem _)) 3))
    (mul_mem (pow_mem hl 2) (pow_mem (sub_mem hl (one_mem _)) 2))

/-- `ℚ(j) ⊆ ℚ(λ)`. -/
theorem fieldOfJ_le_fieldOf (l : Qbar) : fieldOfJ l ≤ fieldOf l :=
  IntermediateField.adjoin_simple_le_iff.mpr (jQ_mem_fieldOf l)

/-- `ℚ(j) ⊆ F_λ`. -/
theorem fieldOfJ_le_fieldOf' (l : Qbar) : fieldOfJ l ≤ fieldOf' l :=
  (fieldOfJ_le_fieldOf l).trans (fieldOf_le_fieldOf' l)

/-- `σ ∈ Gal(ℚ̄/ℚ(j))` fixes `j`. -/
theorem gal_jQ {l : Qbar} (σ : Qbar ≃ₐ[fieldOfJ l] Qbar) : σ (jQ l) = jQ l :=
  σ.commutes ⟨jQ l, IntermediateField.mem_adjoin_simple_self ℚ _⟩

/-- **`σ(λ)` is a conjugate of `λ`** for `σ ∈ Gal(ℚ̄/ℚ(j))`. -/
theorem conj_of_gal {l : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1) (σ : Qbar ≃ₐ[fieldOfJ l] Qbar) :
    Conj l (σ l) := by
  have hj := gal_jQ σ
  have hm0 : σ l ≠ 0 := fun h ↦ hl0 (σ.injective (by rw [h, map_zero]))
  have hm1 : σ l ≠ 1 := fun h ↦ hl1 (σ.injective (by rw [h, map_one]))
  have hd : l ^ 2 * (l - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ (sub_ne_zero.mpr hl1))
  have hd' : σ l ^ 2 * (σ l - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hm0) (pow_ne_zero _ (sub_ne_zero.mpr hm1))
  apply conj_of_j_eq hl0 hl1
  have key : jQ (σ l) = jQ l := by
    rw [← hj]
    unfold jQ
    simp only [map_div₀, map_mul, map_pow, map_sub, map_add, map_one, map_ofNat]
  unfold jQ at key
  rw [div_eq_div_iff hd' hd] at key
  have h256 : (256 : Qbar) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h256
  linear_combination key

/-- `σ` maps the coordinates of `E_λ[n]` to coordinates of `E_{σ(λ)}[n]`. -/
theorem torsionCoords_map_subset {l : Qbar} (σ : Qbar ≃ₐ[fieldOfJ l] Qbar) {n : ℕ} {c : Qbar}
    (hc : c ∈ torsionCoords l n) : σ c ∈ torsionCoords (σ l) n := by
  obtain ⟨P, hP, hcP⟩ := Set.mem_iUnion₂.mp hc
  cases P with
  | zero => exact absurd hcP id
  | some x y hxy =>
    have hQ : n • Anabelian.pointMap (legendre l) σ.toAlgHom.toRingHom
        (Point.some x y hxy) = 0 := by
      rw [← map_nsmul, hP, map_zero]
    rw [Anabelian.pointMap_some] at hQ
    have hxy' : (legendre (σ l)).toAffine.Nonsingular (σ x) (σ y) :=
      legendre_map l σ.toAlgHom.toRingHom ▸
        (Affine.map_nonsingular (legendre l) σ.injective x y).mpr hxy
    have hQ' : n • Point.some (σ x) (σ y) hxy' = 0 :=
      nsmul_some_eq_zero_of_eq (legendre_map l σ.toAlgHom.toRingHom) _ hxy' n hQ
    rcases hcP with rfl | rfl
    · exact mem_torsionCoords hQ' (Set.mem_insert _ _)
    · exact mem_torsionCoords hQ' (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- **`F_λ` is stable under `Gal(ℚ̄/ℚ(j))`.** -/
theorem gal_map_mem_fieldOf' {l : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    (σ : Qbar ≃ₐ[fieldOfJ l] Qbar) {a : Qbar} (ha : a ∈ fieldOf' l) : σ a ∈ fieldOf' l := by
  have hconj := conj_of_gal hl0 hl1 σ
  have hsq : ∀ {s t : Qbar}, s ^ 2 = t ^ 2 → t ∈ fieldOf' l → s ∈ fieldOf' l := by
    intro s t h ht
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
    · rw [h']; exact ht
    · rw [h']; exact neg_mem ht
  unfold fieldOf' at ha
  induction ha using IntermediateField.adjoin_induction with
  | mem c hc =>
    rcases hc with (hc | hc) | hc
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with hc | hc | hc | hc <;> subst c
      · exact conj_mem hconj (mem_fieldOf'_self l)
      · refine hsq (t := sqrtNegOne) ?_ (sqrtNegOne_mem_fieldOf' l)
        rw [← map_pow, sqrtNegOne_sq, map_neg, map_one]
      · obtain ⟨s, hs, hs2⟩ := conj_exists_sq hl0 hl1 hconj
        refine hsq (t := s) ?_ hs
        rw [← map_pow, sqrtLam_sq, hs2]
      · obtain ⟨s, hs, hs2⟩ := conj_exists_sq hl0 hl1 (conj_one_sub hconj)
        refine hsq (t := s) ?_ hs
        rw [← map_pow, sqrtOneSubLam_sq, hs2, map_sub, map_one]
    · exact conj_torsionCoords_subset hl0 hl1 hconj (torsionCoords_three_subset_fieldOf' l)
        (torsionCoords_map_subset σ hc)
    · exact conj_torsionCoords_subset hl0 hl1 hconj (torsionCoords_five_subset_fieldOf' l)
        (torsionCoords_map_subset σ hc)
  | algebraMap r =>
    have h := (σ.toAlgHom.restrictScalars ℚ).commutes r
    change σ (algebraMap ℚ Qbar r) = _ at h
    rw [h]
    exact IntermediateField.algebraMap_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-- **`F_λ/ℚ(j)` is normal.** -/
theorem fieldOf'_normal {l : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    Normal (fieldOfJ l) (IntermediateField.extendScalars (fieldOfJ_le_fieldOf' l)) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  rintro σ _ ⟨a, ha, rfl⟩
  exact gal_map_mem_fieldOf' hl0 hl1 σ ha

/-- **`F_λ/ℚ(j)` is Galois.** -/
theorem fieldOf'_isGalois {l : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    IsGalois (fieldOfJ l) (IntermediateField.extendScalars (fieldOfJ_le_fieldOf' l)) where
  to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable (fieldOfJ l) _ Qbar
  to_normal := fieldOf'_normal hl0 hl1

/-! ### Transfer between intermediate fields of `F` and of `ℚ̄` -/

/-- The identification of `L ⊆ ℚ̄` with itself as an extension of `M' ≤ L`. -/
def extendScalarsEquiv {L M' : IntermediateField ℚ Qbar} (h : M' ≤ L) :
    IntermediateField.extendScalars h ≃+* L where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- `L/M` is Galois for `M ⊆ L ⊆ ℚ̄` if `L` is Galois over the lift `M' ⊆ ℚ̄` of `M`. -/
theorem isGalois_of_lift_eq {L : IntermediateField ℚ Qbar} {M : IntermediateField ℚ L}
    {M' : IntermediateField ℚ Qbar} (hM : IntermediateField.lift M = M') (h : M' ≤ L)
    [IsGalois M' (IntermediateField.extendScalars h)] : IsGalois M L := by
  subst hM
  exact IsGalois.of_equiv_equiv (f := (IntermediateField.liftAlgEquiv M).symm.toRingEquiv)
    (g := extendScalarsEquiv h) (RingHom.ext fun _ ↦ rfl)

/-- `[L : M] = [L : M']` for the lift `M' ⊆ ℚ̄` of `M ⊆ L`. -/
theorem finrank_eq_relfinrank_of_lift_eq {L : IntermediateField ℚ Qbar}
    {M : IntermediateField ℚ L} {M' : IntermediateField ℚ Qbar}
    (hM : IntermediateField.lift M = M') (h : M' ≤ L) :
    Module.finrank M L = IntermediateField.relfinrank M' L := by
  subst hM
  rw [IntermediateField.relfinrank_eq_finrank_of_le h]
  exact Algebra.finrank_eq_of_equiv_equiv (IntermediateField.liftAlgEquiv M).toRingEquiv
    (extendScalarsEquiv h).symm (RingHom.ext fun _ ↦ rfl)

/-- The lift of the field of moduli `ℚ(j(E_λ)) ⊆ F_λ` to `ℚ̄` is `ℚ(j) ⊆ ℚ̄`. -/
theorem lift_fieldOfModuli (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    IntermediateField.lift (fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E) =
      fieldOfJ x.1 := by
  haveI : (legendre (genC x h3 h5)).IsElliptic := (curveOf x h3 h5).isElliptic
  have hj : (curveOf x h3 h5).E.j = 256 * (genC x h3 h5 ^ 2 - genC x h3 h5 + 1) ^ 3 /
      (genC x h3 h5 ^ 2 * (genC x h3 h5 - 1) ^ 2) := legendre_j (l := genC x h3 h5)
  have hemb : IntermediateField.lift (fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E) =
      (fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E).map (embC x h3 h5) := rfl
  rw [hemb]
  change IntermediateField.map (embC x h3 h5) ℚ⟮(curveOf x h3 h5).E.j⟯ = _
  rw [IntermediateField.adjoin_map, Set.image_singleton, hj,
    map_div₀, map_mul, map_pow, map_add, map_sub, map_pow, map_one, map_mul, map_pow,
    map_pow, map_sub, map_one, map_ofNat]
  rfl

/-! ### The degree -/

/-- A positive integer `d < ℓ` is prime to the prime `ℓ`. -/
theorem coprime_of_pos_of_lt {d ℓ : ℕ} (hℓ : ℓ.Prime) (hd : 0 < d) (h : d < ℓ) :
    Nat.Coprime d ℓ :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr fun hdvd ↦
    absurd (Nat.le_of_dvd hd hdvd) (not_le.mpr h))

/-- `|GL₂(𝔽_3)| = 48` and `|GL₂(𝔽_5)| = 480` are prime to every prime `ℓ ≥ 7`. -/
theorem coprime_gl_card {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) :
    Nat.Coprime 48 ℓ ∧ Nat.Coprime 480 ℓ := by
  have h2 : Nat.Coprime 2 ℓ := (Nat.coprime_primes Nat.prime_two hℓ).mpr (by omega)
  have h3 : Nat.Coprime 3 ℓ := (Nat.coprime_primes Nat.prime_three hℓ).mpr (by omega)
  have h5 : Nat.Coprime 5 ℓ := (Nat.coprime_primes Nat.prime_five hℓ).mpr (by omega)
  constructor
  · rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num]
    exact Nat.Coprime.mul_left (Nat.Coprime.pow_left 4 h2) h3
  · rw [show (480 : ℕ) = 2 ^ 5 * 3 * 5 by norm_num]
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.pow_left 5 h2) h3) h5

/-- `K ⊆ K ⊔ ℚ(S)` viewed over `K` is `K(S)`. -/
theorem extendScalars_sup_adjoin (K : IntermediateField ℚ Qbar) (S : Set Qbar) :
    IntermediateField.extendScalars (le_sup_left : K ≤ K ⊔ IntermediateField.adjoin ℚ S) =
      IntermediateField.adjoin K S :=
  le_antisymm
    ((IntermediateField.extendScalars_le_iff _ _).mpr (sup_le
      (fun a ha ↦ IntermediateField.algebraMap_mem (IntermediateField.adjoin K S) ⟨a, ha⟩)
      (IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin K S))))
    (IntermediateField.adjoin_le_iff.mpr fun _ ha ↦
      (le_sup_right : IntermediateField.adjoin ℚ S ≤ K ⊔ IntermediateField.adjoin ℚ S)
        (IntermediateField.subset_adjoin ℚ S ha))

/-- `[K(s) : K] ≤ 2` for `s² ∈ K`. -/
theorem relfinrank_sup_adjoin_sq_le (K : IntermediateField ℚ Qbar) {s : Qbar} (hs : s ^ 2 ∈ K) :
    IntermediateField.relfinrank K (K ⊔ ℚ⟮s⟯) ≤ 2 := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le le_sup_left, extendScalars_sup_adjoin]
  have hint : IsIntegral K s := (isIntegral s).tower_top
  rw [IntermediateField.adjoin.finrank hint]
  have hmin := minpoly.min K s (monic_X_pow_sub_C (⟨s ^ 2, hs⟩ : K) two_ne_zero) (by simp)
  have := natDegree_le_natDegree hmin
  rwa [natDegree_X_pow_sub_C] at this

/-- **`[K(E_λ[n]) : K]` divides `|GL₂(𝔽_n)| = (n² − 1)(n² − n)`**: it is the index of the
kernel of the mod-`n` representation, the order of its image. -/
theorem relfinrank_sup_torsion_dvd (K : IntermediateField ℚ Qbar) {l : Qbar} (hl : l ∈ K)
    (n : ℕ) [Fact n.Prime]
    (b : AddSubgroup.torsionBy (legendre l).toAffine.Point n ≃+ (Fin 2 → ZMod n)) :
    IntermediateField.relfinrank K (K ⊔ IntermediateField.adjoin ℚ (torsionCoords l n)) ∣
      (n ^ 2 - 1) * (n ^ 2 - n) := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le le_sup_left, extendScalars_sup_adjoin,
    IntermediateField.finrank_eq_fixingSubgroup_index, ← torsionRep_ker K hl n b,
    Subgroup.index_ker, ← card_GL_two n]
  exact Subgroup.card_subgroup_dvd_card _

/-- `j/256` as an element of `ℚ(j)`. -/
noncomputable def jC (l : Qbar) : fieldOfJ l :=
  ⟨jQ l / 256, div_mem (IntermediateField.mem_adjoin_simple_self ℚ _) (by
    have : (256 : Qbar) = ((256 : ℕ) : Qbar) := by norm_num
    rw [this]
    exact IntermediateField.natCast_mem _ _)⟩

/-- The polynomial `(T² − T + 1)³ − (j/256)·T²(T − 1)²` over `ℚ(j)`, of degree `6`, of which
`λ` is a root. -/
noncomputable def jPoly (l : Qbar) : Polynomial (fieldOfJ l) :=
  (X ^ 2 - X + 1) ^ 3 - C (jC l) * (X ^ 2 * (X - 1) ^ 2)

theorem jPoly_monic (l : Qbar) : (jPoly l).Monic := by
  unfold jPoly
  monicity!

theorem jPoly_natDegree_le (l : Qbar) : (jPoly l).natDegree ≤ 6 := by
  unfold jPoly
  compute_degree!

theorem jPoly_aeval {l : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1) : aeval l (jPoly l) = 0 := by
  have h1 : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  simp only [jPoly, map_sub, map_pow, map_add, map_mul, aeval_X, aeval_C, map_one]
  change (l ^ 2 - l + 1) ^ 3 - jQ l / 256 * (l ^ 2 * (l - 1) ^ 2) = 0
  unfold jQ
  field_simp
  ring

/-- `[ℚ(λ) : ℚ(j)] ≤ 6`. -/
theorem relfinrank_fieldOfJ_fieldOf_le {l : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    IntermediateField.relfinrank (fieldOfJ l) (fieldOf l) ≤ 6 := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le (fieldOfJ_le_fieldOf l),
    IntermediateField.extendScalars_adjoin]
  have hint : IsIntegral (fieldOfJ l) l := (isIntegral l).tower_top
  rw [IntermediateField.adjoin.finrank hint]
  exact (natDegree_le_of_dvd (minpoly.dvd _ l (jPoly_aeval hl0 hl1))
    (jPoly_monic l).ne_zero).trans (jPoly_natDegree_le l)

/-- **`[F_λ : ℚ(j)]` is prime to every prime `ℓ ≥ 7`**, given bases of `E_λ[3]`, `E_λ[5]`
and `[F_λ : ℚ(j)] ≠ 0`: it is the product of the relative degrees of the tower
`ℚ(j) ⊆ ℚ(λ) ⊆ ℚ(λ, √−1) ⊆ ℚ(λ, √−1, √λ) ⊆ ℚ(λ, √−1, √λ, √(1 − λ)) ⊆ …(E_λ[3]) ⊆ F_λ`, of
degrees `≤ 6`, `≤ 2`, `≤ 2`, `≤ 2`, `∣ 48`, `∣ 480`. -/
theorem coprime_relfinrank_fieldOfJ {l : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    (b3 : AddSubgroup.torsionBy (legendre l).toAffine.Point 3 ≃+ (Fin 2 → ZMod 3))
    (b5 : AddSubgroup.torsionBy (legendre l).toAffine.Point 5 ≃+ (Fin 2 → ZMod 5))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    (hpos : IntermediateField.relfinrank (fieldOfJ l) (fieldOf' l) ≠ 0) :
    Nat.Coprime (IntermediateField.relfinrank (fieldOfJ l) (fieldOf' l)) ℓ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hF : fieldOf' l = fieldOf l ⊔ ℚ⟮sqrtNegOne⟯ ⊔ ℚ⟮sqrtLam l⟯ ⊔ ℚ⟮sqrtOneSubLam l⟯ ⊔
      IntermediateField.adjoin ℚ (torsionCoords l 3) ⊔
      IntermediateField.adjoin ℚ (torsionCoords l 5) := by
    have hset : ({l, sqrtNegOne, sqrtLam l, sqrtOneSubLam l} : Set Qbar) =
        (({l} ∪ {sqrtNegOne}) ∪ {sqrtLam l}) ∪ {sqrtOneSubLam l} := by
      ext a
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, or_assoc]
    rw [fieldOf', IntermediateField.adjoin_union, IntermediateField.adjoin_union, hset,
      IntermediateField.adjoin_union, IntermediateField.adjoin_union,
      IntermediateField.adjoin_union]
  set K₁ : IntermediateField ℚ Qbar := fieldOf l with hK₁
  set K₂ : IntermediateField ℚ Qbar := K₁ ⊔ ℚ⟮sqrtNegOne⟯ with hK₂
  set K₃ : IntermediateField ℚ Qbar := K₂ ⊔ ℚ⟮sqrtLam l⟯ with hK₃
  set K₄ : IntermediateField ℚ Qbar := K₃ ⊔ ℚ⟮sqrtOneSubLam l⟯ with hK₄
  set K₅ : IntermediateField ℚ Qbar := K₄ ⊔ IntermediateField.adjoin ℚ (torsionCoords l 3)
    with hK₅
  set K₆ : IntermediateField ℚ Qbar := K₅ ⊔ IntermediateField.adjoin ℚ (torsionCoords l 5)
    with hK₆
  have hl₁ : l ∈ K₁ := IntermediateField.mem_adjoin_simple_self ℚ l
  have hl₂ : l ∈ K₂ := le_sup_left (a := K₁) hl₁
  have hl₃ : l ∈ K₃ := le_sup_left (a := K₂) hl₂
  have hl₄ : l ∈ K₄ := le_sup_left (a := K₃) hl₃
  have h01 : fieldOfJ l ≤ K₁ := fieldOfJ_le_fieldOf l
  have h12 : K₁ ≤ K₂ := le_sup_left
  have h23 : K₂ ≤ K₃ := le_sup_left
  have h34 : K₃ ≤ K₄ := le_sup_left
  have h45 : K₄ ≤ K₅ := le_sup_left
  have h56 : K₅ ≤ K₆ := le_sup_left
  have h02 : fieldOfJ l ≤ K₂ := h01.trans h12
  have h03 : fieldOfJ l ≤ K₃ := h02.trans h23
  have h04 : fieldOfJ l ≤ K₄ := h03.trans h34
  have h05 : fieldOfJ l ≤ K₅ := h04.trans h45
  have hprod : IntermediateField.relfinrank (fieldOfJ l) (fieldOf' l) =
      IntermediateField.relfinrank (fieldOfJ l) K₁ * IntermediateField.relfinrank K₁ K₂ *
        IntermediateField.relfinrank K₂ K₃ * IntermediateField.relfinrank K₃ K₄ *
        IntermediateField.relfinrank K₄ K₅ * IntermediateField.relfinrank K₅ K₆ := by
    rw [hF, IntermediateField.relfinrank_mul_relfinrank h01 h12,
      IntermediateField.relfinrank_mul_relfinrank h02 h23,
      IntermediateField.relfinrank_mul_relfinrank h03 h34,
      IntermediateField.relfinrank_mul_relfinrank h04 h45,
      IntermediateField.relfinrank_mul_relfinrank h05 h56]
  rw [hprod] at hpos ⊢
  simp only [ne_eq, mul_eq_zero, not_or] at hpos
  obtain ⟨⟨⟨⟨⟨n1, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩ := hpos
  have d1 : IntermediateField.relfinrank (fieldOfJ l) K₁ ≤ 6 :=
    relfinrank_fieldOfJ_fieldOf_le hl0 hl1
  have d2 : IntermediateField.relfinrank K₁ K₂ ≤ 2 :=
    relfinrank_sup_adjoin_sq_le K₁ (s := sqrtNegOne)
      (by rw [sqrtNegOne_sq]; exact neg_mem (one_mem _))
  have d3 : IntermediateField.relfinrank K₂ K₃ ≤ 2 :=
    relfinrank_sup_adjoin_sq_le K₂ (s := sqrtLam l) (by rw [sqrtLam_sq]; exact hl₂)
  have d4 : IntermediateField.relfinrank K₃ K₄ ≤ 2 :=
    relfinrank_sup_adjoin_sq_le K₃ (s := sqrtOneSubLam l)
      (by rw [sqrtOneSubLam_sq]; exact sub_mem (one_mem _) hl₃)
  have d5 : IntermediateField.relfinrank K₄ K₅ ∣ (3 ^ 2 - 1) * (3 ^ 2 - 3) :=
    relfinrank_sup_torsion_dvd K₄ hl₄ 3 b3
  have d6 : IntermediateField.relfinrank K₅ K₆ ∣ (5 ^ 2 - 1) * (5 ^ 2 - 5) :=
    relfinrank_sup_torsion_dvd K₅ (le_sup_left (a := K₄) hl₄) 5 b5
  norm_num at d5 d6
  obtain ⟨c48, c480⟩ := coprime_gl_card hℓ h7
  refine Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left
    (Nat.Coprime.mul_left (Nat.Coprime.mul_left ?_ ?_) ?_) ?_) ?_) ?_
  · exact coprime_of_pos_of_lt hℓ (Nat.pos_of_ne_zero n1) (by omega)
  · exact coprime_of_pos_of_lt hℓ (Nat.pos_of_ne_zero n2) (by omega)
  · exact coprime_of_pos_of_lt hℓ (Nat.pos_of_ne_zero n3) (by omega)
  · exact coprime_of_pos_of_lt hℓ (Nat.pos_of_ne_zero n4) (by omega)
  · exact Nat.Coprime.coprime_dvd_left d5 c48
  · exact Nat.Coprime.coprime_dvd_left d6 c480

/-! ### The main theorem -/

/-- **`F_λ/F_mod` is Galois of degree prime to `ℓ` for every prime `ℓ ≥ 7`** (the field
`galois_deg_prime` of `Iut.EllipticCurveData.CurveArithmetic` for the curve of a point of the
tripod), given that `E_μ[n](ℚ̄) ≅ (ℤ/n)²` for all `μ` and `n ≠ 0` (used for `n = 3, 5`). -/
theorem galois_deg_prime_of_torsion_basis
    (hb : ∀ (l : Qbar) (n : ℕ), n ≠ 0 →
      Nonempty (AddSubgroup.torsionBy (legendre l).toAffine.Point n ≃+ (Fin 2 → ZMod n)))
    (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (h7 : 7 ≤ ℓ) : IsGaloisOfDegreePrimeTo (curveOf x h3 h5).F (curveOf x h3 h5).E ℓ := by
  have hlift := lift_fieldOfModuli x h3 h5
  have hle := fieldOfJ_le_fieldOf' x.1
  haveI := fieldOf'_isGalois x.2.1 x.2.2
  refine ⟨isGalois_of_lift_eq hlift hle, ?_⟩
  haveI : Module.Finite (fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E)
      (curveOf x h3 h5).F :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  have hpos : Module.finrank (fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E)
      (curveOf x h3 h5).F ≠ 0 := Module.finrank_pos.ne'
  have key : Module.finrank (fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E)
      (curveOf x h3 h5).F = IntermediateField.relfinrank (fieldOfJ x.1) (fieldOf' x.1) :=
    finrank_eq_relfinrank_of_lift_eq hlift hle
  rw [key] at hpos ⊢
  exact coprime_relfinrank_fieldOfJ x.2.1 x.2.2 (hb x.1 3 (by norm_num)).some
    (hb x.1 5 (by norm_num)).some hℓ h7 hpos

end Iut.Tripod
