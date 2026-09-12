/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.MultiplicativeKernel
import Iut.Tripod.TpdRamIdx
import Iut.Cor312.ThetaData.VariableChangePoint

/-!
# Bounding the inertia group by its action on the torsion

* `Iut.card_le_of_forall_pow_eq_one`: a subgroup `H` of a finite group `G` with `Nat.card G ∣ p·m`,
  `p ∤ m`, all of whose elements satisfy `σ^p = 1`, has order at most `p` (it is a `p`-group);
* `Iut.valuation_map_eq_of_mem_inertia`: an element of the inertia group of `w` preserves the
  `w`-adic valuation (it stabilizes the prime `𝔓_w`);
* the transport of the Galois action on points along a change of variables with invariant
  coefficients (`Iut.vcX_map`, `Iut.vcY_map`, `Iut.exists_vcEquiv_map_eq`), the iterates of a
  conjugate (`Iut.iterate_vcEquiv`), and the Legendre coefficients of the models
  `E_{1−μ} = ⟨√−1, 1, 0, 0⟩ • E_μ`, `E_{1/μ} = ⟨√μ, 0, 0, 0⟩ • E_μ`
  (`Iut.legendreCoeffs_vc_one_sub`, `Iut.legendreCoeffs_vc_inv`);
* `Iut.Affine.Point.map_pow`: `Point.map (σ^m) = (Point.map σ)^[m]`.
-/

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WeierstrassCurve
  WeierstrassCurve.Affine

open scoped Pointwise

/-! ### `p`-subgroups of small order -/

/-- A subgroup all of whose elements satisfy `σ^p = 1`, of a finite group of order dividing
`p·m` with `p ∤ m`, has order at most `p`. -/
theorem card_le_of_forall_pow_eq_one {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (p m : ℕ) [hp : Fact p.Prime] (hG : Nat.card G ∣ p * m) (hpm : ¬ p ∣ m)
    (hH : ∀ σ ∈ H, σ ^ p = 1) : Nat.card H ≤ p := by
  have hP : IsPGroup p H := fun σ => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hH σ.1 σ.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd : p ^ k ∣ p * m := hk ▸ (H.card_subgroup_dvd_card.trans hG)
  rw [hk]
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · rw [pow_zero]; exact hp.out.one_lt.le
    · rw [pow_one]
  · exfalso
    have : p ^ 2 ∣ p * m := (pow_dvd_pow p hk2).trans hdvd
    rw [sq] at this
    exact hpm ((Nat.mul_dvd_mul_iff_left hp.out.pos).mp this)

/-- A subgroup all of whose elements satisfy `σ^p = 1` is a `p`-group: its order is prime
to every prime `q ≠ p`. -/
theorem not_dvd_card_of_forall_pow_eq_one {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (p : ℕ) [hp : Fact p.Prime] (hH : ∀ σ ∈ H, σ ^ p = 1) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    ¬ q ∣ Nat.card H := by
  have hP : IsPGroup p H := fun σ => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hH σ.1 σ.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk]
  intro h
  exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp.out).mp (hq.dvd_of_dvd_pow h))

/-- `ℓ ∤ (ℓ² − 1)(ℓ − 1)` for a prime `ℓ`. -/
lemma not_dvd_gl_cofactor {ℓ : ℕ} (hℓ : ℓ.Prime) : ¬ ℓ ∣ (ℓ ^ 2 - 1) * (ℓ - 1) := by
  intro h
  have h2 := hℓ.two_le
  rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
  · have h1 : ℓ ∣ ℓ ^ 2 := dvd_pow_self ℓ two_ne_zero
    have : ℓ ∣ 1 := by
      have := Nat.dvd_sub h1 h
      rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at this
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp this)
  · have := Nat.le_of_dvd (by omega) h
    omega

/-- `|GL₂(𝔽_ℓ)| = ℓ·((ℓ² − 1)(ℓ − 1))`. -/
lemma card_GL_two_eq_mul (ℓ : ℕ) :
    (ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ) = ℓ * ((ℓ ^ 2 - 1) * (ℓ - 1)) := by
  have : ℓ ^ 2 - ℓ = ℓ * (ℓ - 1) := by
    rw [Nat.mul_sub, mul_one, sq]
  rw [this]; ring

/-! ### Inertia elements preserve the valuation -/

section Valuation

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The prime of `σ·w` is `σ • 𝔓_w` (Mathlib's pointwise action). -/
lemma galPlace_maximalIdeal_eq_smul (σ : K ≃ₐ[k] K) (w : FinitePlace K) :
    (galPlace σ w).maximalIdeal.asIdeal = σ • w.maximalIdeal.asIdeal := by
  rw [galPlace_maximalIdeal, Ideal.pointwise_smul_eq_comap]
  have : ((galRestrictInt σ⁻¹ : 𝓞 K ≃ₐ[𝓞 k] 𝓞 K) : 𝓞 K →+* 𝓞 K) =
      ((MulSemiringAction.toRingAut (K ≃ₐ[k] K) (𝓞 K) σ).symm : 𝓞 K →+* 𝓞 K) := by
    refine RingHom.ext fun x => RingOfIntegers.coe_injective ?_
    change ((galRestrictInt σ⁻¹ x : 𝓞 K) : K) = ((σ⁻¹ • x : 𝓞 K) : K)
    rw [coe_galRestrictInt]
    rfl
  rw [this]
  rfl

/-- **An inertia element preserves the valuation**: `w(σ x) = w(x)` for
`σ ∈ I_w ⊆ D_w`. -/
lemma valuation_map_eq_of_mem_inertia {w : FinitePlace K} {σ : K ≃ₐ[k] K}
    (hσ : σ ∈ w.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K)) (x : K) :
    w.maximalIdeal.valuation K (σ x) = w.maximalIdeal.valuation K x := by
  have hst : σ ∈ MulAction.stabilizer (K ≃ₐ[k] K) w.maximalIdeal.asIdeal :=
    Ideal.inertia_le_stabilizer _ hσ
  rw [MulAction.mem_stabilizer_iff] at hst
  have hw : galPlace σ w = w := by
    apply (FinitePlace.maximalIdeal_inj _ _).mp
    apply HeightOneSpectrum.ext
    rw [galPlace_maximalIdeal_eq_smul, hst]
  rw [← galPlace_valuation σ w x, hw]

end Valuation

/-! ### Transport along a change of variables -/

section VariableChange

variable {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K) (σ : K →+* K)
  (hu : σ C.u = C.u) (hr : σ C.r = C.r) (hs : σ C.s = C.s) (ht : σ C.t = C.t)
include hu hr hs ht

omit hs ht in
/-- `vcX` commutes with `σ` when `σ` fixes the coefficients of `C`. -/
lemma vcX_map (x : K) : Anabelian.vcX C (σ x) = σ (Anabelian.vcX C x) := by
  unfold Anabelian.vcX
  rw [map_div₀, map_sub, map_pow, hu, hr]

/-- `vcY` commutes with `σ` when `σ` fixes the coefficients of `C`. -/
lemma vcY_map (x y : K) : Anabelian.vcY C (σ x) (σ y) = σ (Anabelian.vcY C x y) := by
  unfold Anabelian.vcY
  rw [map_div₀, map_sub, map_sub, map_mul, map_sub, map_pow, hu, hr, hs, ht]

open scoped Classical in
/-- **The conjugate of a coordinatewise action** by `vcEquiv C W` acts coordinatewise on
`C • W`. -/
lemma exists_vcEquiv_map_eq (φ : W.toAffine.Point →+ W.toAffine.Point)
    (hφ : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      ∃ h' : W.toAffine.Nonsingular (σ x) (σ y), φ (Point.some x y h) = Point.some (σ x) (σ y) h')
    (x' y' : K) (h' : (C • W).toAffine.Nonsingular x' y') :
    ∃ h'' : (C • W).toAffine.Nonsingular (σ x') (σ y'),
      Anabelian.vcEquiv C W (φ ((Anabelian.vcEquiv C W).symm (Point.some x' y' h'))) =
        Point.some (σ x') (σ y') h'' := by
  obtain ⟨Q, hQ⟩ := Anabelian.vcPoint_surjective C W (Point.some x' y' h')
  cases Q with
  | zero =>
    exact absurd (hQ.symm.trans (Anabelian.vcPoint_zero C W)) (Point.some_ne_zero h')
  | some x y h =>
    have hsymm : (Anabelian.vcEquiv C W).symm (Point.some x' y' h') = Point.some x y h := by
      rw [← hQ]
      exact (Anabelian.vcEquiv C W).symm_apply_apply (Point.some x y h)
    rw [Anabelian.vcPoint_some] at hQ
    obtain ⟨hσ, hφ'⟩ := hφ x y h
    obtain ⟨hx', hy'⟩ := Point.some.inj hQ
    subst hx' hy'
    refine ⟨?_, ?_⟩
    · rw [← vcX_map C σ hu hr, ← vcY_map C σ hu hr hs ht]
      exact (Anabelian.nonsingular_vc C W _ _).mp hσ
    · rw [hsymm, hφ', Anabelian.vcEquiv_apply, Anabelian.vcPoint_some]
      exact Anabelian.some_ext (vcX_map C σ hu hr x) (vcY_map C σ hu hr hs ht x y)

end VariableChange

/-- The iterates of a conjugate `e ∘ φ ∘ e⁻¹`. -/
lemma iterate_conj {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (e : G ≃+ G') (φ : G →+ G)
    (m : ℕ) (Q : G) :
    (⇑(e.toAddMonoidHom.comp (φ.comp e.symm.toAddMonoidHom)))^[m] (e Q) = e ((⇑φ)^[m] Q) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp

/-! ### The Legendre coefficients of the twisted models -/

section Legendre

variable {K : Type*} [Field K] {μ : K} {W : Affine K} (hW₁ : W.a₁ = 0) (hW₂ : W.a₂ = -(1 + μ))
  (hW₃ : W.a₃ = 0) (hW₄ : W.a₄ = μ) (hW₆ : W.a₆ = 0)
include hW₁ hW₂ hW₃ hW₄ hW₆

/-- `⟨√−1, 1, 0, 0⟩ • E_μ` is the Legendre model of `1 − μ`. -/
lemma legendreCoeffs_vc_one_sub {i : K} (hi : i ^ 2 = -1) (hi0 : i ≠ 0) :
    let C : VariableChange K := ⟨Units.mk0 i hi0, 1, 0, 0⟩
    (C • W).a₁ = 0 ∧ (C • W).a₂ = -(1 + (1 - μ)) ∧ (C • W).a₃ = 0 ∧ (C • W).a₄ = 1 - μ ∧
      (C • W).a₆ = 0 := by
  intro C
  have h4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hi]; norm_num
  have h6 : i ^ 6 = -1 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hi]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [C, variableChange_a₁, hW₁]
  · simp only [C, variableChange_a₂, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hi, hW₁,
      hW₂]
    ring
  · simp [C, variableChange_a₃, hW₁, hW₃]
  · simp only [C, variableChange_a₄, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, h4, hW₁,
      hW₂, hW₃, hW₄]
    ring
  · simp only [C, variableChange_a₆, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, h6, hW₁,
      hW₂, hW₃, hW₄, hW₆]
    ring

/-- `⟨√μ, 0, 0, 0⟩ • E_μ` is the Legendre model of `1/μ`. -/
lemma legendreCoeffs_vc_inv {u : K} (hu : u ^ 2 = μ) (hu0 : u ≠ 0) :
    let C : VariableChange K := ⟨Units.mk0 u hu0, 0, 0, 0⟩
    (C • W).a₁ = 0 ∧ (C • W).a₂ = -(1 + μ⁻¹) ∧ (C • W).a₃ = 0 ∧ (C • W).a₄ = μ⁻¹ ∧
      (C • W).a₆ = 0 := by
  intro C
  have hμ : μ ≠ 0 := by rw [← hu]; exact pow_ne_zero _ hu0
  have h4 : u ^ 4 = μ ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hu]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [C, variableChange_a₁, hW₁]
  · simp only [C, variableChange_a₂, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hu, hW₁,
      hW₂]
    field_simp
    ring
  · simp [C, variableChange_a₃, hW₁, hW₃]
  · simp only [C, variableChange_a₄, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, h4, hW₁,
      hW₂, hW₃, hW₄]
    field_simp
    ring
  · simp only [C, variableChange_a₆, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hW₁, hW₂,
      hW₃, hW₄, hW₆]
    ring

/-- A model with the Legendre coefficients of `μ` is the Legendre curve of `μ`. -/
lemma eq_legendre_of_coeffs : W = Tripod.legendre μ := by
  ext <;> simp [Tripod.legendre, hW₁, hW₂, hW₃, hW₄, hW₆]

end Legendre

/-! ### Powers of the Galois action on points -/

section PointMap

variable {k K : Type*} [Field k] [Field K] [DecidableEq K] [Algebra k K] (W : WeierstrassCurve k)

/-- `Point.map (σ^m) = (Point.map σ)^[m]`. -/
lemma Affine.Point.map_pow (σ : K ≃ₐ[k] K) (m : ℕ) (Q : (Affine.baseChange W K).Point) :
    Point.map (W' := W) (S := k) ((σ ^ m : K ≃ₐ[k] K) : K →ₐ[k] K) Q =
      (⇑(Point.map (W' := W) (S := k) (σ : K →ₐ[k] K)))^[m] Q := by
  induction m with
  | zero =>
    rw [pow_zero, Function.iterate_zero_apply]
    cases Q <;> rfl
  | succ m ih =>
    have : ((σ ^ (m + 1) : K ≃ₐ[k] K) : K →ₐ[k] K) =
        (σ : K →ₐ[k] K).comp ((σ ^ m : K ≃ₐ[k] K) : K →ₐ[k] K) :=
      AlgHom.ext fun x => by rw [pow_succ']; rfl
    rw [Function.iterate_succ_apply', ← ih, this, ← Point.map_map]

end PointMap

end Iut
