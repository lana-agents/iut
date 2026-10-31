/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.FunctionField.ProjectiveDivisor
import EllipticCurves.FunctionField.DivisorDegree
import EllipticCurves.FunctionField.NegYInvolution

/-!
# Auxiliary degree, pole and parity bounds on a Weierstrass curve

* `deg_smul_basis`: the degree formula `deg (p • 1 + q • y) = max (2 deg p) (2 deg q + 3)`
  (with the `q`-term dropped when `q = 0`), and the bounds `deg_smul_basis_le`,
  `deg_smul_basis_le_of_degree_lt`, `two_le_deg`.
* `sum_pole_le`: the weighted pole count of `n / d` is at most `k` when `deg n, deg d ≤ k`.
* `ordInfty_even_of_negY`, `ordInfty_odd_of_negY`: the parity of the order at infinity of a
  function that is even or odd under the hyperelliptic involution.
-/

open Polynomial
open scoped Polynomial.Bivariate nonZeroDivisors

namespace Iut.EtaleTheta

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}

/-! ### The degree formula in the basis `{1, y}` -/

private lemma two_nsmul_coe (m : ℕ) : (2 • (m : WithBot ℕ)) = ((2 * m : ℕ) : WithBot ℕ) := by
  rw [two_nsmul, two_mul]; norm_cast

open scoped Classical in
/-- **The degree formula** in the basis `{1, y}`. -/
theorem deg_smul_basis (p q : F[X]) :
    deg W (p • (1 : W.CoordinateRing) + q • mk W Y) =
      max (2 * p.natDegree) (if q = 0 then 0 else 2 * q.natDegree + 3) := by
  by_cases hq : q = 0
  · subst hq
    rw [if_pos rfl, max_eq_left (Nat.zero_le _), deg, norm_smul_basis]
    simp [natDegree_pow]
  · rw [if_neg hq]
    refine natDegree_eq_of_degree_eq_some ?_
    rw [degree_norm_smul_basis, degree_eq_natDegree hq, two_nsmul_coe]
    by_cases hp : p = 0
    · subst hp
      rw [degree_zero, natDegree_zero, mul_zero, max_eq_right (Nat.zero_le _)]
      rw [show (2 • (⊥ : WithBot ℕ)) = ⊥ from rfl, max_eq_right bot_le]
      norm_cast
    · rw [degree_eq_natDegree hp, two_nsmul_coe]
      norm_cast

/-- **Degree bound in the basis `{1, y}`.** -/
theorem deg_smul_basis_le {p q : F[X]} {k : ℕ} (hp : 2 * p.natDegree ≤ k)
    (hq : q ≠ 0 → 2 * q.natDegree + 3 ≤ k) :
    deg W (p • (1 : W.CoordinateRing) + q • mk W Y) ≤ k := by
  classical
  rw [deg_smul_basis]
  refine max_le hp ?_
  split_ifs with h
  · exact Nat.zero_le _
  · exact hq h

/-- **Degree bound in the basis `{1, y}`**, from the degree bounds produced by
`exists_poly_of_isWeightFamily_deg`. -/
theorem deg_smul_basis_le_of_degree_lt {p q : F[X]} {k : ℕ}
    (hp : p.degree < ((k / 2 + 1 : ℕ) : WithBot ℕ))
    (hq : q.degree < (((k - 1) / 2 : ℕ) : WithBot ℕ)) :
    deg W (p • (1 : W.CoordinateRing) + q • mk W Y) ≤ k := by
  refine deg_smul_basis_le ?_ ?_
  · by_cases hp0 : p = 0
    · subst hp0; simp
    · have := (natDegree_lt_iff_degree_lt hp0).mpr hp
      omega
  · intro hq0
    have := (natDegree_lt_iff_degree_lt hq0).mpr hq
    omega

/-- **A function on the affine chart outside the field of constants has a pole of order at least
`2` at infinity.** -/
theorem two_le_deg {a : W.CoordinateRing} (ha : a ∉ Set.range (algebraMap F W.CoordinateRing)) :
    2 ≤ deg W a := by
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by rw [h, map_zero]⟩
  have h1 := deg_ne_one a
  have h0 : deg W a ≠ 0 := fun h => by
    obtain ⟨c, -, hc⟩ := exists_eq_algebraMap_of_deg_eq_zero ha0 h
    exact ha ⟨c, hc.symm⟩
  omega

/-! ### The pole-sum bound -/

section Pole

variable [IsDedekindDomain W.CoordinateRing]

open scoped Classical in
/-- On the affine chart, the projective divisor of an element of the coordinate ring is
nonnegative, and its weighted sum over any finite set of affine points is at most the degree. -/
private lemma sum_erase_none_le {d : W.CoordinateRing} (hd : d ≠ 0) (S : Finset (ProjPoint W)) :
    ∑ p ∈ S.erase none,
        divisorProj W (algebraMap W.CoordinateRing W.FunctionField d) p * (degProjPt W p : ℤ)
      ≤ deg W d := by
  set D := divisorProj W (algebraMap W.CoordinateRing W.FunctionField d) with hD
  have hd' : algebraMap W.CoordinateRing W.FunctionField d ≠ 0 :=
    fun h => hd ((IsFractionRing.injective W.CoordinateRing W.FunctionField) (by rw [h, map_zero]))
  set g : ProjPoint W → ℤ := fun p => D p * (degProjPt W p : ℤ) with hg
  have hnn : ∀ p ∈ (S ∪ D.support).erase none, 0 ≤ g p := by
    intro p hp
    obtain ⟨v, rfl⟩ := Option.ne_none_iff_exists'.mp (Finset.ne_of_mem_erase hp)
    simp only [hg, hD, divisorProj_apply_some]
    exact mul_nonneg (ord_algebraMap_nonneg v d) (Nat.cast_nonneg _)
  have h1 : ∑ p ∈ S.erase none, g p ≤ ∑ p ∈ (S ∪ D.support).erase none, g p :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset_erase _ Finset.subset_union_left) (fun p hp _ => hnn p hp)
  have h2 : ∑ p ∈ (S ∪ D.support), g p = degProj W D := by
    rw [degProj, Finsupp.sum]
    symm
    refine Finset.sum_subset Finset.subset_union_right ?_
    intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp, zero_mul]
  have h3 : ∑ p ∈ (S ∪ D.support), g p
      = ∑ p ∈ (S ∪ D.support).erase none, g p + g none := by
    by_cases hn : none ∈ S ∪ D.support
    · rw [← Finset.sum_erase_add _ _ hn]
    · rw [Finset.erase_eq_of_notMem hn]
      have : D none = 0 := by
        by_contra h
        exact hn (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr h))
      simp [hg, this]
  have h4 : g none = -(deg W d : ℤ) := by
    simp [hg, hD, divisorProj_apply_none, ordInfty_algebraMap hd]
  have h5 := degProj_divisorProj hd'
  rw [← hD] at h5
  change ∑ p ∈ S.erase none, g p ≤ _
  linarith

/-- **The pole-sum bound.**  If `R = n / d` with `deg n, deg d ≤ k`, then the weighted number of
poles of `R` on any finite set of points is at most `k`.  (No sign hypothesis on `S` is needed:
points where `R` has no pole only contribute nonpositive terms.) -/
theorem sum_pole_le {n d : W.CoordinateRing} (hn : n ≠ 0) (hd : d ≠ 0) {k : ℕ}
    (hnk : deg W n ≤ k) (hdk : deg W d ≤ k) {R : W.FunctionField}
    (hR : R = algebraMap W.CoordinateRing W.FunctionField n
      / algebraMap W.CoordinateRing W.FunctionField d)
    (S : Finset (ProjPoint W)) :
    ∑ p ∈ S, (-divisorProj W R p) * (degProjPt W p : ℤ) ≤ k := by
  classical
  have hinj := IsFractionRing.injective W.CoordinateRing W.FunctionField
  have hn' : algebraMap W.CoordinateRing W.FunctionField n ≠ 0 :=
    fun h => hn (hinj (by rw [h, map_zero]))
  have hd' : algebraMap W.CoordinateRing W.FunctionField d ≠ 0 :=
    fun h => hd (hinj (by rw [h, map_zero]))
  have hR0 : R ≠ 0 := by rw [hR]; exact div_ne_zero hn' hd'
  set D := divisorProj W (algebraMap W.CoordinateRing W.FunctionField d) with hD
  -- the affine terms are bounded by the divisor of `d`
  have haff : ∀ p ∈ S.erase none,
      (-divisorProj W R p) * (degProjPt W p : ℤ) ≤ D p * (degProjPt W p : ℤ) := by
    intro p hp
    obtain ⟨v, rfl⟩ := Option.ne_none_iff_exists'.mp (Finset.ne_of_mem_erase hp)
    refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
    rw [hD, divisorProj_apply_some, divisorProj_apply_some, hR, ord_div v hn' hd']
    linarith [ord_algebraMap_nonneg v n]
  have hS' : ∑ p ∈ S.erase none, (-divisorProj W R p) * (degProjPt W p : ℤ) ≤ deg W d :=
    (Finset.sum_le_sum haff).trans (sum_erase_none_le hd S)
  have hinf : -divisorProj W R none = (deg W n : ℤ) - deg W d := by
    rw [divisorProj_apply_none, ordInfty_eq_sub hR0 hd (a := n)
      (by rw [hR, div_mul_cancel₀ _ hd'])]
    ring
  by_cases hnS : none ∈ S
  · rw [← Finset.sum_erase_add _ _ hnS, hinf, degProjPt_none, Nat.cast_one, mul_one]
    linarith
  · rw [Finset.erase_eq_of_notMem hnS] at hS'
    linarith

end Pole

/-! ### Parity at infinity under the hyperelliptic involution -/

private lemma negYCoordHom_smul_basis (p q : F[X]) :
    negYCoordHom W (p • (1 : W.CoordinateRing) + q • mk W Y) =
      (p - q * (C W.a₁ * X + C W.a₃)) • (1 : W.CoordinateRing) + (-q) • mk W Y := by
  rw [map_add, map_smul, map_smul, map_one, negYCoordHom_mk, X_comp, negPolynomial]
  have hL : (mk W (C (C W.a₁ * X + C W.a₃)) : W.CoordinateRing)
      = (C W.a₁ * X + C W.a₃) • (1 : W.CoordinateRing) := by
    rw [CoordinateRing.smul, mul_one]
  rw [map_sub, map_neg, hL, sub_smul, mul_smul, neg_smul]
  rw [smul_sub, smul_neg]
  abel

private lemma smul_basis_inj {p q p' q' : F[X]}
    (h : p • (1 : W.CoordinateRing) + q • mk W Y = p' • (1 : W.CoordinateRing) + q' • mk W Y) :
    p = p' ∧ q = q' := by
  have h0 : (p - p') • (1 : W.CoordinateRing) + (q - q') • mk W Y = 0 := by
    rw [sub_smul, sub_smul]; linear_combination h
  obtain ⟨h1, h2⟩ := smul_basis_eq_zero h0
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

/-- An element of the coordinate ring fixed by the hyperelliptic involution has even degree. -/
theorem even_deg_of_negYCoordHom_eq (h2 : (2 : F) ≠ 0) {x : W.CoordinateRing}
    (hx : negYCoordHom W x = x) : Even (deg W x) := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq x
  rw [negYCoordHom_smul_basis] at hx
  have hq : q = 0 := by
    have h := (smul_basis_inj hx).2
    have h' : C (2 : F) * q = 0 := by
      rw [map_ofNat C 2, two_mul]
      linear_combination -h
    exact (mul_eq_zero.mp h').resolve_left (by simpa using h2)
  rw [deg_smul_basis, if_pos hq, max_eq_left (Nat.zero_le _)]
  exact even_two_mul _

/-- An element of the coordinate ring negated by the hyperelliptic involution, and nonzero, has
odd degree. -/
theorem odd_deg_of_negYCoordHom_eq_neg (h2 : (2 : F) ≠ 0) {x : W.CoordinateRing} (hx0 : x ≠ 0)
    (hx : negYCoordHom W x = -x) : Odd (deg W x) := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq x
  rw [negYCoordHom_smul_basis, neg_add, ← neg_smul, ← neg_smul] at hx
  have h := (smul_basis_inj hx).1
  have hp : p = C (2 : F)⁻¹ * (q * (C W.a₁ * X + C W.a₃)) := by
    have h' : C (2 : F) * p = q * (C W.a₁ * X + C W.a₃) := by
      rw [map_ofNat C 2, two_mul]
      linear_combination h
    rw [← h', ← mul_assoc, ← C_mul, inv_mul_cancel₀ h2, C_1, one_mul]
  have hq : q ≠ 0 := by
    rintro rfl
    apply hx0
    rw [hp]; simp
  have hpd : p.natDegree ≤ q.natDegree + 1 := by
    rw [hp]
    refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
    have := natDegree_linear_le (a := W.a₁) (b := W.a₃)
    omega
  rw [deg_smul_basis, if_neg hq, max_eq_right (by omega)]
  exact ⟨q.natDegree + 1, by ring⟩

/-- Writing `f` as a quotient `c / D` of an `ε`-eigenvector `c` and an invariant `D`. -/
private lemma exists_eigen_quotient {f : W.FunctionField} (hf : f ≠ 0) {ε : F}
    (hε : negYAlgEquiv W f = algebraMap F W.FunctionField ε * f) :
    ∃ c D : W.CoordinateRing, c ≠ 0 ∧ D ≠ 0 ∧ negYCoordHom W D = D ∧
      negYCoordHom W c = algebraMap F W.CoordinateRing ε * c ∧
      ordInfty W f = (deg W D : ℤ) - deg W c := by
  have hinj := IsFractionRing.injective W.CoordinateRing W.FunctionField
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hf
  set b' := negYCoordHom W b with hb'
  have hb'0 : b' ≠ 0 := by
    intro h
    apply hb0
    rw [← negYCoordHom_negYCoordHom W b, ← hb', h, map_zero]
  have hψ : ∀ {z : W.CoordinateRing}, z ≠ 0 → genPsi W z ≠ 0 :=
    fun hz h => hz (hinj (by rw [h, map_zero]))
  refine ⟨a * b', b * b', mul_ne_zero ha0 hb'0, mul_ne_zero hb0 hb'0, ?_, ?_, ?_⟩
  · rw [map_mul, hb', negYCoordHom_negYCoordHom, mul_comm]
  · rw [map_mul, hb', negYCoordHom_negYCoordHom, ← hb']
    apply hinj
    change genPsi W _ = genPsi W _
    have hε' := hε
    change negYAlgEquiv W (genPsi W a / genPsi W b) = _ at hε'
    rw [map_div₀, negYAlgEquiv_genPsi, negYAlgEquiv_genPsi, ← hb'] at hε'
    rw [div_eq_iff (hψ hb'0)] at hε'
    have hεc : genPsi W (algebraMap F W.CoordinateRing ε) = algebraMap F W.FunctionField ε :=
      (IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField ε).symm
    rw [map_mul, map_mul, map_mul, hεc, hε']
    field_simp [hψ hb0]
  · refine ordInfty_eq_sub hf (mul_ne_zero hb0 hb'0) ?_
    rw [map_mul, map_mul]
    field_simp [hψ hb0]

/-- **A function invariant under the hyperelliptic involution has even order at infinity.** -/
theorem ordInfty_even_of_negY (h2 : (2 : F) ≠ 0) {f : W.FunctionField} (hf : f ≠ 0)
    (hι : negYAlgEquiv W f = f) : Even (ordInfty W f) := by
  obtain ⟨c, D, -, -, hD, hc, hord⟩ :=
    exists_eigen_quotient hf (ε := 1) (by rw [map_one, one_mul, hι])
  rw [map_one, one_mul] at hc
  obtain ⟨m, hm⟩ := even_deg_of_negYCoordHom_eq h2 hD
  obtain ⟨m', hm'⟩ := even_deg_of_negYCoordHom_eq h2 hc
  rw [hord, hm, hm']
  exact ⟨(m : ℤ) - m', by push_cast; ring⟩

/-- **A nonzero function negated by the hyperelliptic involution has odd order at infinity.** -/
theorem ordInfty_odd_of_negY (h2 : (2 : F) ≠ 0) {f : W.FunctionField} (hf : f ≠ 0)
    (hι : negYAlgEquiv W f = -f) : Odd (ordInfty W f) := by
  obtain ⟨c, D, hc0, -, hD, hc, hord⟩ :=
    exists_eigen_quotient hf (ε := -1) (by rw [map_neg, map_one, neg_one_mul, hι])
  rw [map_neg, map_one, neg_one_mul] at hc
  obtain ⟨m, hm⟩ := even_deg_of_negYCoordHom_eq h2 hD
  obtain ⟨m', hm'⟩ := odd_deg_of_negYCoordHom_eq_neg h2 hc0 hc
  rw [hord, hm, hm']
  exact ⟨(m : ℤ) - m' - 1, by push_cast; ring⟩

end Iut.EtaleTheta
