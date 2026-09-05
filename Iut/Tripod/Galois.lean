/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.TorsionDegree
import Iut.Tripod.PointMap

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
* `σ` maps `E_λ[n](ℚ̄)` onto `E_μ[n](ℚ̄)` (`Iut.Tripod.mapPoint`), and `E_μ[n] ⊆ F_λ` since
  `E_μ ≅ E_λ` over `F_λ`: `E_{1−λ} = ⟨√−1, 1, 0, 0⟩ • E_λ` and `E_{1/λ} = ⟨√λ, 0, 0, 0⟩ • E_λ`
  (`Iut.Tripod.legendre_vc_one_sub`, `legendre_vc_inv`), and the change of variables
  `(x, y) ↦ (u²x + r, u³y)` is a group homomorphism (`Iut.Tripod.vcPoint`) preserving
  `n`-torsion, with `u, r ∈ F_λ` (`Iut.Tripod.torsionCoords_subset_of_vc`).

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
    vc (Units.mk0 i hi0) 1 • legendre l = legendre (1 - l) := by
  ext
  · rw [vc_a₁]; simp
  · rw [vc_a₂]
    simp only [Units.val_mk0, legendre_a₂, inv_pow, hi]
    ring
  · rw [vc_a₃]; simp
  · rw [vc_a₄]
    simp only [Units.val_mk0, legendre_a₄, legendre_a₂, inv_pow]
    have : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hi]; norm_num
    rw [this]
    ring
  · rw [vc_a₆]
    simp only [Units.val_mk0, legendre_a₆, legendre_a₄, legendre_a₂]
    ring

/-- `E_{1/λ} = ⟨√λ, 0, 0, 0⟩ • E_λ`: the change of variables `(x, y) ↦ (λx, λ√λ·y)`. -/
theorem legendre_vc_inv {u l : Qbar} (hu : u ^ 2 = l) (hu0 : u ≠ 0) :
    vc (Units.mk0 u hu0) 0 • legendre l = legendre l⁻¹ := by
  have hl : l ≠ 0 := by rw [← hu]; exact pow_ne_zero _ hu0
  ext
  · rw [vc_a₁]; simp
  · rw [vc_a₂]
    simp only [Units.val_mk0, legendre_a₂, inv_pow, hu]
    field_simp
    ring
  · rw [vc_a₃]; simp
  · rw [vc_a₄]
    simp only [Units.val_mk0, legendre_a₄, legendre_a₂, inv_pow]
    have : u ^ 4 = l ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hu]
    rw [this]
    field_simp
    ring
  · rw [vc_a₆]
    simp only [Units.val_mk0, legendre_a₆, legendre_a₄, legendre_a₂]
    ring

/-! ### Transport of the torsion coordinates along a change of variables -/

/-- **The torsion coordinates of `E_μ` lie in `F` if those of `E_λ` do**, when
`E_μ = ⟨u, r, 0, 0⟩ • E_λ` with `u, r ∈ F`: the change of variables `(x, y) ↦ (u²x + r, u³y)`
maps `E_μ[n]` into `E_λ[n]`, and `x = ((u²x + r) − r)/u²`, `y = u³y/u³`. -/
theorem torsionCoords_subset_of_vc {l m : Qbar} {u : Qbarˣ} {r : Qbar}
    (h : vc u r • legendre l = legendre m) (F : IntermediateField ℚ Qbar)
    (huF : (u : Qbar) ∈ F) (hrF : r ∈ F) {n : ℕ} (hl : torsionCoords l n ⊆ F) :
    torsionCoords m n ⊆ F := by
  intro c hc
  obtain ⟨P, hP, hcP⟩ := Set.mem_iUnion₂.mp hc
  cases P with
  | zero => exact absurd hcP id
  | some x y hxy =>
    have hxy' : (vc u r • legendre l).toAffine.Nonsingular x y := h ▸ hxy
    have hP' : n • Point.some x y hxy' = 0 := nsmul_some_eq_zero_of_eq h.symm hxy hxy' n hP
    have hQ : n • vcPoint u r (Point.some x y hxy') = 0 := by
      rw [← map_nsmul, hP', map_zero]
    rw [vcPoint_some] at hQ
    have hx : u ^ 2 * x + r ∈ F := hl (mem_torsionCoords hQ (by simp))
    have hy : u ^ 3 * y ∈ F := hl (mem_torsionCoords hQ (by simp))
    have hu : (u : Qbar) ≠ 0 := u.ne_zero
    rcases hcP with rfl | rfl
    · have : c = (u ^ 2 * c + r - r) / u ^ 2 := by
        field_simp
        ring
      rw [this]
      exact div_mem (sub_mem hx hrF) (pow_mem huF 2)
    · have : c = u ^ 3 * c / u ^ 3 := by
        field_simp
      rw [this]
      exact div_mem hy (pow_mem huF 3)

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
    torsionCoords_subset_of_vc (legendre_vc_one_sub sqrtNegOne_sq hi0 l) _ hi (one_mem _) hn
  have h3 : torsionCoords l⁻¹ n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_inv (sqrtLam_sq l) hs0) _ hs (zero_mem _) hn
  have h4 : torsionCoords (1 - l)⁻¹ n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_inv (sqrtOneSubLam_sq l) hs1) _ hs' (zero_mem _) h2
  have h5 : torsionCoords (1 - l⁻¹) n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_one_sub sqrtNegOne_sq hi0 l⁻¹) _ hi (one_mem _) h3
  have h6 : torsionCoords (1 - (1 - l)⁻¹) n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_one_sub sqrtNegOne_sq hi0 (1 - l)⁻¹) _ hi
      (one_mem _) h4
  rcases h with h | h | h | h | h | h <;> subst m
  · exact hn
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

end Iut.Tripod
