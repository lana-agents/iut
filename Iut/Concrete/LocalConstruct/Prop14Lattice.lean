/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.IndAut
import Iut.Concrete.LocalConstruct.LatticeSandwich
import Iut.Concrete.LocalConstruct.ScaleVolume
import Iut.Concrete.LocalConstruct.LocalDifferent

/-!
# IUT IV, Proposition 1.4(iii),(iv) for the lattice automorphisms

Let all places of the packet lie over `p`, and let `x ∈ K_{w_j}` with `ord_p x = λ ≥ 0`. For every
indeterminacy automorphism `φ` (a `ℚ_p`-linear automorphism preserving `⊗_i 𝓘_i`,
`IndAut.lean`) we have, following the proof of IUT IV, Proposition 1.2(ii):

`x·(R_I)^∼ ⊆ p^m·α·δ·(R_I)^∼ ⊆ p^m·α·R_I ⊆ p^m·⊗_i 𝓘_i`,  so
`φ(x·(R_I)^∼) ⊆ p^m·⊗_i 𝓘_i ⊆ p^m·β·R_I ⊆ p^m·β·(R_I)^∼`,

where `δ = ⊗_i δ_i` with `ord_p δ_i = d_i` and `δ·(R_I)^∼ ⊆ R_I` (Proposition 1.1:
`PacketDifferent.lean`, `LocalDifferent.lean`), `α = ⊗_i (2p)⁻¹ϖ_{a,i}` and
`β = ⊗_i (2p)⁻¹ϖ_{b,i}` (Proposition 1.2(i): `LatticeSandwich.lean`), and
`m = ⌊λ − ord_p(α) − d_I⌋`. Then (`ScaleVolume.lean`)

`μ^log(p^m·β·(R_I)^∼) = −(m + ord_p β)·log p ≤ (−λ + d_I + 1)·log p + ∑_i (a_i + b_i)·log p`,

and `(a_i + b_i)·log p ≤ 3 + log e_i`, with `a_i + b_i = 0` when `p` is odd and `e_i ≤ p − 2`
(`LogLattice.lean`): this is `prop14iii_lattice`. At an odd prime unramified in every factor,
`(R_I)^∼ = R_I = ⊗_i 𝓘_i` is preserved by every `φ` (`latticeAut_integral_subset`,
Proposition 1.4(iv)).
-/

namespace Iut

namespace LocalConstruct

open NumberField
open scoped TensorProduct Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (p : Nat.Primes) (c : ι → Place K)

/-! ### Elementary scalings along the canonical finite places -/

section Canonical

variable {p c} (hc : ∀ j, IsOver K p (c j))
include hc

omit [Fintype ι] in
/-- The canonical finite place of the factor `j`. -/
lemma hW (j : ι) : c j = Place.finite (finPart K (c j)) := (hc j).eq_finite_finPart

omit [Fintype ι] in
lemma hres (j : ι) : residueChar (finPart K (c j)) = p := (hc j).residueChar_finPart

/-- An elementary scaling along the canonical places is an elementary tensor. -/
lemma prod_incl_eq_tprod (y : ∀ j, completionAt K (finPart K (c j))) :
    (∏ j, incl p c j (finPart K (c j)) (hW hc j) (y j)) =
      PiTensorProduct.tprod ℚ_[p] fun j => factorMk p (c j) (y j) := by
  rw [tprod_eq_prod_inclFactor]
  rfl

/-- `incl_j` of the image of `t ∈ ℚ_p` is the scalar `t`. -/
lemma incl_padicEmb (j : ι) (t : ℚ_[p]) :
    incl p c j (finPart K (c j)) (hW hc j) (padicEmb (hres hc j) t) =
      algebraMap ℚ_[p] (Tensor K (.finite p) c) t := by
  rw [incl_apply]
  change inclFactor p c j (factorMk p (c j) (padicEmb (hc j).residueChar_finPart t)) = _
  rw [← algebraMap_factor_apply_of_isOver p (c j) (hc j), AlgHom.commutes]

end Canonical

/-! ### Updating one coordinate of an elementary scaling -/

section Update

variable {p c}
variable [DecidableEq ι] (w : ι → FinitePlace K) (h : ∀ j, c j = Place.finite (w j))

lemma prod_incl_update (g : ∀ i, completionAt K (w i)) (j : ι) (v : completionAt K (w j)) :
    (∏ i, incl p c i (w i) (h i) (Function.update g j v i)) =
      incl p c j (w j) (h j) v * ∏ i ∈ Finset.univ.erase j, incl p c i (w i) (h i) (g i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

lemma prod_incl_eq_mul_erase (g : ∀ i, completionAt K (w i)) (j : ι) :
    (∏ i, incl p c i (w i) (h i) (g i)) =
      incl p c j (w j) (h j) (g j) * ∏ i ∈ Finset.univ.erase j, incl p c i (w i) (h i) (g i) :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

lemma sum_ordp_update (g : ∀ i, completionAt K (w i)) (j : ι) (v : completionAt K (w j)) :
    (∑ i, ordp K (w i) (Function.update g j v i)) =
      ∑ i, ordp K (w i) (g i) - ordp K (w j) (g j) + ordp K (w j) v := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _
    (Finset.mem_univ j), Function.update_self]
  have : ∑ i ∈ Finset.univ.erase j, ordp K (w i) (Function.update g j v i) =
      ∑ i ∈ Finset.univ.erase j, ordp K (w i) (g i) :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [this]
  ring

omit [Fintype ι] in
lemma update_ne_zero (g : ∀ i, completionAt K (w i)) (hg : ∀ i, g i ≠ 0) (j : ι)
    (v : completionAt K (w j)) (hv : v ≠ 0) (i : ι) : Function.update g j v i ≠ 0 := by
  by_cases hij : i = j
  · subst hij; rw [Function.update_self]; exact hv
  · rw [Function.update_of_ne hij]; exact hg i

end Update

/-! ### `ord_p` of powers of `p` -/

lemma ordp_zpow_residueChar (w : FinitePlace K) (m : ℤ) :
    ordp K w (((residueChar w : ℕ) : completionAt K w) ^ m) = m := by
  have h1 := ordp_residueChar w
  unfold ordp at h1 ⊢
  rw [norm_zpow, Real.log_zpow, neg_mul_eq_mul_neg, mul_div_assoc, h1, mul_one]

/-! ### Proposition 1.4(iii) -/

/-- The ramification term of a factor is bounded by `3 + log e` (resp. vanishes) as in IUT IV,
Proposition 1.4(iii). -/
lemma logLattice_term_le (w : FinitePlace K) (hw : residueChar w = p) :
    (logLatticeA (residueChar w) (ramIdx K w) + logLatticeB (residueChar w) (ramIdx K w)) *
        Real.log p ≤
      if (p : ℕ) - 2 < ramIdx K w then 3 + Real.log (ramIdx K w) else 0 := by
  have he := ramIdx_pos' w
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  split_ifs with hlt
  · rw [hw]
    exact logLatticeA_add_B_le hp2 he
  · have hne : (p : ℕ) ≠ 2 := by
      intro h2; rw [h2] at hlt; exact hlt (by simpa using he)
    rw [hw, logLatticeA_add_B_eq_zero hne he (by omega), zero_mul]

/-- **IUT IV, Proposition 1.4(iii)** for the lattice automorphisms (`LocalTheory.prop14_iii`). -/
theorem prop14iii_lattice (hc : ∀ j, ∃ w : FinitePlace K, c j = Place.finite w ∧ residueChar w = p)
    (d : ι → ℝ) (j : ι) (w : FinitePlace K) (h : c j = Place.finite w)
    (x : completionAt K w) (hx : x ≠ 0) (hord : 0 ≤ ordp K w x)
    (hd : ∀ i w', c i = Place.finite w' → d i = differentExponent K w') :
    ∃ a : Tensor K (.finite p) c, IsUnit a ∧
      (∀ φ ∈ indAut (.finite p) c,
        φ '' (incl p c j w h x • integral p c) ⊆ a • integral p c) ∧
      componentVol (.finite p) c (a • integral p c) ≤
        (-ordp K w x + ∑ i, d i + 1) * Real.log p +
          ∑ i, if (p : ℕ) - 2 < ramIdxAt K (c i) then 3 + Real.log (ramIdxAt K (c i)) else 0 := by
  classical
  have hc' : ∀ j, IsOver K p (c j) := hc
  obtain rfl : w = finPart K (c j) := eq_finPart h
  set W : ι → FinitePlace K := fun i => finPart K (c i)
  have hWi : ∀ i, c i = Place.finite (W i) := hW hc'
  -- the different elements
  have hδ := fun i => exists_local_different_elt (p := (p : ℕ)) (hres hc' i)
  choose δ hδ0 hδord hδdual using hδ
  -- the scalars
  set A : ∀ i, completionAt K (W i) := fun i => scalA c i * δ i
  have hA0 : ∀ i, A i ≠ 0 := fun i => mul_ne_zero (scalA_ne_zero c i) (hδ0 i)
  set σA : ℝ := ∑ i, ordp K (W i) (A i)
  set lam : ℝ := ordp K (W j) x
  set m : ℤ := ⌊lam - σA⌋
  set t : ℚ_[p] := ((p : ℕ) : ℚ_[p]) ^ m
  have ht0 : t ≠ 0 := zpow_ne_zero _ (by exact_mod_cast p.2.ne_zero)
  set e : completionAt K (W j) := padicEmb (hres hc' j) t
  have he0 : e ≠ 0 := (map_ne_zero _).mpr ht0
  have hepow : e = ((residueChar (W j) : ℕ) : completionAt K (W j)) ^ m := by
    change padicEmb (hres hc' j) t = _
    rw [map_zpow₀, map_natCast, hres hc' j]
  have heord : ordp K (W j) e = m := by rw [hepow, ordp_zpow_residueChar]
  -- the integral element `Z = x·p^{-m}·A⁻¹`
  set g : ∀ i, completionAt K (W i) := fun i => (A i)⁻¹
  set y := Function.update g j (x * e⁻¹ * (A j)⁻¹)
  have hy0 : ∀ i, y i ≠ 0 := update_ne_zero W g (fun i => inv_ne_zero (hA0 i)) j _
    (mul_ne_zero (mul_ne_zero hx (inv_ne_zero he0)) (inv_ne_zero (hA0 j)))
  have hyord : 0 ≤ ∑ i, ordp K (W i) (y i) := by
    rw [sum_ordp_update]
    have hg : ∀ i, ordp K (W i) (g i) = -ordp K (W i) (A i) := fun i => ordp_inv _ _
    simp only [g, ordp_inv, Finset.sum_neg_distrib]
    rw [ordp_mul _ _ _ (mul_ne_zero hx (inv_ne_zero he0)) (inv_ne_zero (hA0 j)),
      ordp_mul _ _ _ hx (inv_ne_zero he0), ordp_inv, ordp_inv, heord]
    have := Int.floor_le (lam - σA)
    change 0 ≤ -σA - -ordp K (W j) (A j) + (lam + -↑m + -ordp K (W j) (A j))
    linarith
  set Z := ∏ i, incl p c i (W i) (hWi i) (y i)
  have hZ : Z ∈ integral p c := prod_incl_mem_integral hc' W hWi y hy0 hyord
  have hinc : incl p c j (W j) (hWi j) e = algebraMap ℚ_[p] (Tensor K (.finite p) c) t :=
    incl_padicEmb hc' j t
  have hAinv : (∏ i, incl p c i (W i) (hWi i) (A i)) *
      ∏ i, incl p c i (W i) (hWi i) (g i) = 1 := prod_incl_mul_prod_incl_inv W hWi A hA0
  have hAprod : (∏ i, incl p c i (W i) (hWi i) (A i)) =
      (∏ i, incl p c i (W i) (hWi i) (scalA c i)) * ∏ i, incl p c i (W i) (hWi i) (δ i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => map_mul _ _ _
  have hZ' : Z = incl p c j (W j) (hWi j) (x * e⁻¹) * ∏ i, incl p c i (W i) (hWi i) (g i) := by
    change (∏ i, incl p c i (W i) (hWi i) (Function.update g j _ i)) = _
    rw [prod_incl_update, prod_incl_eq_mul_erase W hWi g j, ← mul_assoc, ← map_mul]
  have hxZ : incl p c j (W j) (hWi j) x =
      algebraMap ℚ_[p] (Tensor K (.finite p) c) t *
        ((∏ i, incl p c i (W i) (hWi i) (scalA c i)) *
          ((∏ i, incl p c i (W i) (hWi i) (δ i)) * Z)) := by
    rw [← hinc, hZ']
    calc incl p c j (W j) (hWi j) x =
        incl p c j (W j) (hWi j) (e * (x * e⁻¹)) *
          ((∏ i, incl p c i (W i) (hWi i) (A i)) * ∏ i, incl p c i (W i) (hWi i) (g i)) := by
          rw [hAinv, mul_one]
          congr 1
          field_simp
      _ = _ := by rw [map_mul, hAprod]; ring
  -- the containing scalar `a = p^m·β`
  set a : Tensor K (.finite p) c :=
    algebraMap ℚ_[p] (Tensor K (.finite p) c) t * ∏ i, incl p c i (W i) (hWi i) (scalB c i)
  have ha : a = ∏ i, incl p c i (W i) (hWi i)
      (Function.update (fun i => scalB c i) j (e * scalB c j) i) := by
    rw [prod_incl_update, map_mul, hinc]
    change algebraMap ℚ_[p] _ t * ∏ i, incl p c i (W i) (hWi i) (scalB c i) = _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), mul_assoc]
  have hB0 : ∀ i, Function.update (fun i => scalB c i) j (e * scalB c j) i ≠ 0 :=
    update_ne_zero W _ (scalB_ne_zero c) j _ (mul_ne_zero he0 (scalB_ne_zero c j))
  refine ⟨a, ha ▸ isUnit_prod_incl W hWi _ hB0, ?_, ?_⟩
  · -- containment
    intro φ hφ
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    have hδr : (∏ i, incl p c i (W i) (hWi i) (δ i)) * (Z * r) ∈ order p c :=
      prod_incl_mul_mem_order_of_mem_integral p c hc' W hWi δ
        (fun i yy hyy => hδdual i yy hyy) (Z * r) (mul_mem_integral p c hZ hr)
    have hL : (∏ i, incl p c i (W i) (hWi i) (scalA c i)) *
        ((∏ i, incl p c i (W i) (hWi i) (δ i)) * (Z * r)) ∈ tensorLogShell p c := by
      rw [prod_incl_eq_tprod hc']
      exact tprod_scalA_mul_mem_tensorLogShell hc' hδr
    obtain ⟨e', rfl, he'⟩ := hφ
    have hφL : e' ((∏ i, incl p c i (W i) (hWi i) (scalA c i)) *
        ((∏ i, incl p c i (W i) (hWi i) (δ i)) * (Z * r))) ∈ tensorLogShell p c :=
      he' ▸ ⟨_, hL, rfl⟩
    obtain ⟨r', hr', hr'eq⟩ := exists_mem_order_of_mem_tensorLogShell hc' hφL
    refine ⟨r', order_subset_integral p c hr', ?_⟩
    have key : incl p c j (W j) (hWi j) x * r =
        t • ((∏ i, incl p c i (W i) (hWi i) (scalA c i)) *
          ((∏ i, incl p c i (W i) (hWi i) (δ i)) * (Z * r))) := by
      rw [hxZ, Algebra.smul_def]; ring
    change a * r' = e' (incl p c j (W j) (hWi j) x * r)
    rw [key, map_smul, hr'eq, ← prod_incl_eq_tprod hc', Algebra.smul_def]
    change algebraMap ℚ_[p] _ t * (∏ i, incl p c i (W i) (hWi i) (scalB c i)) * r' = _
    ring
  · -- the volume bound
    rw [ha, componentVol_prod_incl_smul_integral hc' W hWi _ hB0, sum_ordp_update,
      ordp_mul _ _ _ he0 (scalB_ne_zero c j), heord]
    have hfl := Int.sub_one_lt_floor (lam - σA)
    have hσA : σA = ∑ i, ordp K (W i) (scalA c i) + ∑ i, d i := by
      change ∑ i, ordp K (W i) (scalA c i * δ i) = _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ordp_mul _ _ _ (scalA_ne_zero c i) (hδ0 i), hδord i, hd i (W i) (hWi i)]
    have hterm : ∀ i, (ordp K (W i) (scalA c i) - ordp K (W i) (scalB c i)) * Real.log p ≤
        if (p : ℕ) - 2 < ramIdxAt K (c i) then 3 + Real.log (ramIdxAt K (c i)) else 0 := by
      intro i
      rw [ordp_scalA_sub_scalB]
      have hr : ramIdxAt K (c i) = ramIdx K (W i) := by rw [hWi i]; rfl
      rw [hr]
      exact logLattice_term_le p (W i) (hres hc' i)
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
    rw [← Finset.sum_mul, Finset.sum_sub_distrib] at hsum
    have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast p.2.one_lt)
    change -(∑ i, ordp K (W i) (scalB c i) - ordp K (W j) (scalB c j) +
      (↑m + ordp K (W j) (scalB c j))) * Real.log ↑↑p ≤ _
    nlinarith

/-! ### Proposition 1.4(iv) -/

/-- At an odd prime unramified in every factor, `(R_I)^∼ = R_I`. -/
theorem integral_eq_order_of_unramified
    (hc : ∀ j, ∃ w : FinitePlace K, c j = Place.finite w ∧ residueChar w = p)
    (hunr : ∀ j w, c j = Place.finite w → ramIdx K w = 1) : integral p c = order p c := by
  classical
  have hc' : ∀ j, IsOver K p (c j) := hc
  set W : ι → FinitePlace K := fun i => finPart K (c i)
  have hWi : ∀ i, c i = Place.finite (W i) := hW hc'
  have hδ := fun i => exists_local_different_elt (p := (p : ℕ)) (hres hc' i)
  choose δ hδ0 hδord hδdual using hδ
  have hd0 : ∀ i, ordp K (W i) (δ i) = 0 := fun i => by
    rw [hδord, differentExponent, ordDifferent_eq_zero _ (hunr i _ (hWi i)), Nat.cast_zero,
      zero_div]
  refine Set.Subset.antisymm (fun r hr => ?_) (order_subset_integral p c)
  have hδr := prod_incl_mul_mem_order_of_mem_integral p c hc' W hWi δ
    (fun i yy hyy => hδdual i yy hyy) r hr
  have hinv : (∏ i, incl p c i (W i) (hWi i) (δ i)⁻¹) ∈ order p c := by
    refine Finset.prod_induction _ (· ∈ order p c) (fun _ _ => mul_mem_order p c)
      (one_mem_order p c) fun i _ => incl_mem_order p c i (W i) (hWi i) _ ?_
    rw [norm_inv, norm_eq_rpow_ordp _ (hδ0 i), hd0, Real.rpow_zero, inv_one]
  have := mul_mem_order p c hinv hδr
  rwa [← mul_assoc, mul_comm (∏ i, incl p c i (W i) (hWi i) (δ i)⁻¹),
    prod_incl_mul_prod_incl_inv W hWi δ hδ0, one_mul] at this

/-- **IUT IV, Proposition 1.4(iv)** (`LocalTheory.prop14_iv`): at an odd prime unramified in
every factor, the lattice automorphisms preserve `(R_I)^∼`. -/
theorem latticeAut_integral_subset
    (hc : ∀ j, ∃ w : FinitePlace K, c j = Place.finite w ∧ residueChar w = p)
    (hp : Odd (p : ℕ)) (hunr : ∀ j w, c j = Place.finite w → ramIdx K w = 1) :
    ∀ φ ∈ indAut (.finite p) c, φ '' integral p c ⊆ integral p c := by
  rintro φ ⟨e, rfl, he⟩
  have hL : tensorLogShell p c = integral p c := by
    rw [tensorLogShell_eq_order_of_unramified p c hp hunr,
      integral_eq_order_of_unramified p c hc hunr]
  rw [← hL, he]

end LocalConstruct

end Iut
