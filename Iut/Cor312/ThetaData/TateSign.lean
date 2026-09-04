/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.TateTorsion
import Iut.Cor312.ThetaData.TateFamilyGalois
import Iut.Cor312.ThetaData.UltrametricSqrt

/-!
# The local sign theorem: `−c₄c₆` is a square fixed by an isometry

Let `E` be an elliptic curve over a complete rank-one valued field `k` carrying a Tate
structure `S` (`Iut.TateStructure`), and let `σ : k ≃+* k` be an isometric automorphism fixing
the coefficients of `E`. If, for an odd prime `ℓ`, the ℓ-torsion `E(k)[ℓ]` has `ℓ²` elements
all of which are fixed by `σ`, then `−c₄(E)c₆(E)` has a **`σ`-fixed square root** in `k`
(`Iut.exists_sqrt_neg_c₄_mul_c₆_fixed`).

The proof transports the Tate structure along `σ` (`Iut.TateStructure.baseChange` on the type
synonym `Iut.Twist k`, whose `k`-algebra structure is `σ`), obtaining a second Tate structure
`S'` on `E` with `S'.C = S.C.map σ` and `S'.ofUnit (σ u) = σ (S.ofUnit u)`. By the uniqueness
of Tate structures (`Iut.eq_one_or_negChange_of_smul_tateCurve`) the changes of variables `S'.C`
and `S.C` differ by `1` or by the negation of `E_q`; the negation would make `σ` act as `−1`
on the class of an ℓ-th root of `q`, forcing `ℓ ∣ 2`. Hence `S.C.map σ = S.C`, so `σ` fixes
`E_q = S.C • E` and its invariants; Hensel's lemma (`Iut.exists_sq_eq_of_norm_sq_sub_lt`) gives a
square root `s` of `−c₄(E_q)c₆(E_q) ≡ 1` with `‖s − 1‖ < 1`, which is `σ`-fixed since `−s` is
not close to `1`, and `r = u⁵ s` is the required root for `E`.
-/

namespace Iut

open WeierstrassCurve TateCurvesTheta Iut.Anabelian
open scoped Classical Valued

universe u

noncomputable section

/-! ### Transport lemmas -/

section Congr

variable {k : Type u} [Field k]

lemma pointCongr_pointCongr_symm {W W' : WeierstrassCurve k} (h : W = W') (P : W'.toAffine.Point) :
    pointCongr h (pointCongr h.symm P) = P := by
  subst h
  rfl

variable [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

namespace TateStructure

omit [CompleteSpace k] in
lemma congr_t {W W' : WeierstrassCurve k} (h : W = W') (S : TateStructure W) :
    (S.congr h).t = S.t := by
  subst h
  rfl

omit [CompleteSpace k] in
lemma congr_C {W W' : WeierstrassCurve k} (h : W = W') (S : TateStructure W) :
    (S.congr h).C = S.C := by
  subst h
  rfl

omit [CompleteSpace k] in
lemma ofUnit_congr {W W' : WeierstrassCurve k} (h : W = W') (S : TateStructure W) (u : kˣ) :
    (S.congr h).ofUnit u = pointCongr h (S.ofUnit u) := by
  subst h
  rfl

end TateStructure

end Congr

/-! ### The negation of the Tate curve acts as `−1` on points -/

section Neg

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
variable {E : WeierstrassCurve k} [E.IsElliptic]

namespace TateStructure

/-- If the changes of variables of two Tate structures differ by the negation of `E_q`, their
point maps differ by the sign `−1` (the second branch of `ofUnit_eq_or_neg`). -/
lemma ofUnit_eq_neg_of_C (S S' : TateStructure E) (h12 : (12 : k) ≠ 0)
    (hC' : S'.C = negChange k * S.C) (u : kˣ) : S'.ofUnit u = -S.ofUnit u := by
  have ht := S.t_eq S' h12
  by_cases hu : u ∈ Subgroup.zpowers S.t.q
  · rw [S'.ofUnit_eq_zero_of_mem (by rw [ht]; exact hu), S.ofUnit_eq_zero_of_mem hu, neg_zero]
  · have hu' : ∀ n : ℤ, (S'.t.q : k) ^ n * (u : k) ≠ 1 := by
      rw [ht]
      exact (S.notMem_zpowers_iff u).mp hu
    have hx : xCoord S'.C (S'.ofUnit u) = S.t.X u := by
      rw [← ht]
      exact S'.iso_x u hu'
    have hy : yCoord S'.C (S'.ofUnit u) = S.t.Y u := by
      rw [← ht]
      exact S'.iso_y u hu'
    have hx' : xCoord S.C (S.ofUnit u) = S.t.X u :=
      S.iso_x u ((S.notMem_zpowers_iff u).mp hu)
    have hy' : yCoord S.C (S.ofUnit u) = S.t.Y u :=
      S.iso_y u ((S.notMem_zpowers_iff u).mp hu)
    have hne' : S'.ofUnit u ≠ 0 := S'.ofUnit_ne_zero (by rw [ht]; exact hu)
    have hne : S.ofUnit u ≠ 0 := S.ofUnit_ne_zero hu
    rw [hC', xCoord_mul _ _ hne', vcX_negChange] at hx
    rw [hC', yCoord_mul _ _ hne', vcY_negChange, hx] at hy
    refine eq_of_coords S.C hne' (neg_ne_zero.mpr hne) ?_ ?_
    · rw [xCoord_neg, hx, hx']
    · rw [yCoord_neg _ hne, hx', hy']
      have hnegY : (S.C • E).toAffine.negY (S.t.X u) (S.t.Y u) = -S.t.Y u - S.t.X u := by
        unfold Affine.negY
        rw [S.hC, S.t.tateCurve_a₁, S.t.tateCurve_a₃]
        ring
      rw [hnegY]
      linear_combination -hy

end TateStructure

end Neg

/-! ### The core argument over `k` -/

section Core

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
variable {E : WeierstrassCurve k} [E.IsElliptic]

/-- An odd prime does not divide `2`. -/
lemma not_dvd_two_of_odd_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) : ¬ ℓ ∣ 2 := fun h =>
  hodd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h)

/-- **The change of variables is fixed.** Given a second Tate structure `S'` on `E` obtained by
transporting `S` along an endomorphism `f` of `k` fixing `E`, if the ℓ-torsion is `f`-fixed
and has `ℓ²` elements (`ℓ` an odd prime), then `f` fixes the Tate parameter and the change of
variables of `S`. -/
theorem TateStructure.map_eq_of_fixed (f : k →+* k) (hE : E.map f = E) (h12 : (12 : k) ≠ 0)
    (S S' : TateStructure E) (hq : S'.t.q = Units.map f.toMonoidHom S.t.q)
    (hC : S'.C = S.C.map f)
    (hS' : ∀ u : kˣ, S'.ofUnit (Units.map f.toMonoidHom u) =
      pointCongr hE (pointMap E f (S.ofUnit u)))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (htors : ∀ P ∈ TateStructure.torsion ℓ E, pointMap E f P = pointCongr hE.symm P)
    (hcard : ℓ * ℓ ≤ Nat.card ↥(TateStructure.torsion ℓ E)) :
    Units.map f.toMonoidHom S.t.q = S.t.q ∧ S.C.map f = S.C := by
  have ht := S.t_eq S' h12
  have hqfix : Units.map f.toMonoidHom S.t.q = S.t.q := by rw [← hq, ht]
  refine ⟨hqfix, ?_⟩
  -- the change of variables of `S'` differs from that of `S` by an automorphism of `E_q`
  set D := S'.C * S.C⁻¹ with hDdef
  have hC' : S'.C = D * S.C := by rw [hDdef, inv_mul_cancel_right]
  have hD : D • S.t.tateCurve = S.t.tateCurve := by
    rw [← S.hC, hDdef, mul_smul, inv_smul_smul, S'.hC, ht, S.hC]
  rcases eq_one_or_negChange_of_smul_tateCurve S.t h12 hD with hD1 | hDn
  · rw [hD1, one_mul] at hC'
    rw [← hC, hC']
  · exfalso
    rw [hDn] at hC'
    have hneg := S.ofUnit_eq_neg_of_C S' h12 hC'
    -- a root class of `q`
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨u, m, hu⟩ := S.exists_root_class ℓ hcard
    have hP : S.ofUnit u ∈ TateStructure.torsion ℓ E := S.ofUnit_mem_torsion ℓ hu
    -- its point is `f`-fixed
    have hfix : S'.ofUnit (Units.map f.toMonoidHom u) = S.ofUnit u := by
      rw [hS', htors _ hP, pointCongr_pointCongr_symm]
    rw [hneg, ← TateStructure.ofUnit_inv, TateStructure.ofUnit_eq_iff] at hfix
    obtain ⟨n, hn⟩ := hfix
    -- `f` fixes `u ^ ℓ`
    have hfu : Units.map f.toMonoidHom u ^ ℓ = S.t.q ^ (1 + ℓ * m) := by
      rw [← map_pow, hu, map_zpow, hqfix]
    have hpow : S.t.q ^ (1 + (ℓ : ℤ) * m) = S.t.q ^ ((n * ℓ : ℤ) + -(1 + ℓ * m)) := by
      rw [← hu, hn, mul_pow, inv_pow, hfu, zpow_add S.t.q (n * ℓ) (-(1 + ℓ * m)),
        zpow_mul, zpow_natCast, zpow_neg]
    have hexp := S.q_zpow_injective hpow
    have hdvd : (ℓ : ℤ) ∣ 2 := ⟨n - 2 * m, by linear_combination hexp⟩
    exact not_dvd_two_of_odd_prime hℓ hodd (Int.natCast_dvd_ofNat.mp hdvd)

omit [E.IsElliptic] in
/-- **The square root, given that `f` fixes the change of variables.** -/
theorem TateStructure.exists_sqrt_of_map_C_eq (f : k →+* k) (hf : ∀ x, ‖f x‖ = ‖x‖)
    (hE : E.map f = E) (h12 : TameResidueChar k) (S : TateStructure E) (hC : S.C.map f = S.C) :
    ∃ r : k, f r = r ∧ r ^ 2 = -(E.c₄ * E.c₆) := by
  have h2 : ‖(2 : k)‖ = 1 := h12.1
  have h12' : (12 : k) ≠ 0 := h12.2
  -- `f` fixes the Tate curve `E_q = S.C • E`
  have hEq : S.t.tateCurve.map f = S.t.tateCurve := by
    rw [← S.hC, ← map_variableChange, hC, hE]
  have hc4 : f S.t.tateCurve.c₄ = S.t.tateCurve.c₄ := by rw [← map_c₄, hEq]
  have hc6 : f S.t.tateCurve.c₆ = S.t.tateCurve.c₆ := by rw [← map_c₆, hEq]
  set a := -(S.t.tateCurve.c₄ * S.t.tateCurve.c₆) with ha
  have hfa : f a = a := by rw [ha, map_neg, map_mul, hc4, hc6]
  have hlt : ‖(1 : k) ^ 2 - a‖ < 1 := by
    rw [one_pow, ha, sub_neg_eq_add, add_comm]
    exact norm_tateCurve_c₄_mul_c₆_add_one_lt S.t h12'
  obtain ⟨s, hs, hs1⟩ := exists_sq_eq_of_norm_sq_sub_lt h2 norm_one hlt
  have hs_norm : ‖s‖ = 1 := norm_eq_one_of_norm_sub_lt_one norm_one hs1
  -- the square root is `f`-fixed
  have hfs : f s = s := by
    have h1 : (f s) ^ 2 = s ^ 2 := by rw [← map_pow, hs, hfa]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact h
    · exfalso
      have hfs1 : ‖f s - 1‖ < 1 := by
        rw [← map_one f, ← map_sub, hf]
        exact hs1
      have hdiff : ‖(f s - 1) - (s - 1)‖ = 1 := by
        rw [h, show (-s - 1) - (s - 1) = -(2 * s) by ring, norm_neg, norm_mul, h2, hs_norm,
          one_mul]
      have hle : ‖(f s - 1) - (s - 1)‖ < 1 := by
        rw [sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hfs1 ?_)
        rw [norm_neg]
        exact hs1
      rw [hdiff] at hle
      exact lt_irrefl _ hle
  -- `f` fixes the scaling unit of `S.C`
  have hCu : f (S.C.u : k) = S.C.u := by
    have := congrArg (fun C : VariableChange k => (C.u : k)) hC
    exact this
  have hc4' : S.t.tateCurve.c₄ = (S.C.u : k)⁻¹ ^ 4 * E.c₄ := by
    rw [← S.hC, variableChange_c₄, Units.val_inv_eq_inv_val]
  have hc6' : S.t.tateCurve.c₆ = (S.C.u : k)⁻¹ ^ 6 * E.c₆ := by
    rw [← S.hC, variableChange_c₆, Units.val_inv_eq_inv_val]
  refine ⟨(S.C.u : k) ^ 5 * s, by rw [map_mul, map_pow, hCu, hfs], ?_⟩
  rw [mul_pow, ← pow_mul, hs, ha, hc4', hc6']
  have hu0 : (S.C.u : k) ≠ 0 := S.C.u.ne_zero
  field_simp

end Core

/-! ### The twisted field -/

section Twist

variable (k : Type u) [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

/-- A type synonym for `k`, to be made a normed `k`-algebra through an isometric automorphism
`σ` of `k` (so that `algebraMap k (Twist k) = σ`). -/
def Twist : Type u := k

instance : Field (Twist k) := inferInstanceAs (Field k)

instance : Valued (Twist k) (WithZero (Multiplicative ℤ)) :=
  inferInstanceAs (Valued k (WithZero (Multiplicative ℤ)))

instance : Valuation.RankOne (Valued.v : Valuation (Twist k) (WithZero (Multiplicative ℤ))) :=
  inferInstanceAs (Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ))))

instance : CompleteSpace (Twist k) := inferInstanceAs (CompleteSpace k)

variable {k}

/-- The `k`-algebra structure on `Twist k` through `σ`. -/
@[reducible] def twistAlgebra (σ : k ≃+* k) : Algebra k (Twist k) :=
  ((σ : k →+* k) : k →+* Twist k).toAlgebra

/-- The normed `k`-algebra structure on `Twist k` through an isometric `σ`. -/
@[reducible] def twistNormedAlgebra (σ : k ≃+* k) (hσ : ∀ x, ‖σ x‖ = ‖x‖) : NormedAlgebra k (Twist k) :=
  @NormedAlgebra.mk _ _ _ _ (twistAlgebra σ) fun r x => by
    letI := twistAlgebra σ
    rw [Algebra.smul_def, norm_mul]
    have h : ‖algebraMap k (Twist k) r‖ = ‖r‖ := hσ r
    rw [h]

end Twist

/-! ### The local sign theorem -/

section Main

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

/-- **The local sign theorem.** Let `σ` be an isometric automorphism of `k` fixing the
coefficients of an elliptic curve `E` with a Tate structure `S`, and let `ℓ` be an odd prime
such that `E(k)[ℓ]` has at least `ℓ²` elements, all fixed by `σ`. Then `−c₄(E)c₆(E)` has a
`σ`-fixed square root. -/
theorem exists_sqrt_neg_c₄_mul_c₆_fixed (σ : k ≃+* k) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (E : WeierstrassCurve k) [E.IsElliptic] (hE : E.map (σ : k →+* k) = E)
    (h12 : TameResidueChar k) (S : TateStructure E) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (htors : ∀ P ∈ TateStructure.torsion ℓ E,
      pointMap E (σ : k →+* k) P = pointCongr hE.symm P)
    (hcard : ℓ * ℓ ≤ Nat.card ↥(TateStructure.torsion ℓ E)) :
    ∃ r : k, σ r = r ∧ r ^ 2 = -(E.c₄ * E.c₆) := by
  letI := twistNormedAlgebra σ hσ
  have hbij : Function.Bijective (algebraMap k (Twist k)) := σ.bijective
  have hE' : E.map (algebraMap k (Twist k)) = E := hE
  -- the transported Tate structure, read as a Tate structure on `E` over `k`
  have hq : ((S.baseChange hbij).congr hE').t.q =
      Units.map (σ : k →+* k).toMonoidHom S.t.q := by
    rw [TateStructure.congr_t]
    rfl
  have hC : ((S.baseChange hbij).congr hE').C = S.C.map (σ : k →+* k) := by
    rw [TateStructure.congr_C]
    rfl
  have hS' : ∀ u : kˣ, ((S.baseChange hbij).congr hE').ofUnit
      (Units.map (σ : k →+* k).toMonoidHom u) =
      pointCongr hE (pointMap E (σ : k →+* k) (S.ofUnit u)) := fun u => by
    have h := (TateStructure.ofUnit_congr hE' (S.baseChange hbij) (unitsEquiv hbij u)).trans
      (congrArg _ (S.baseChange_ofUnit hbij u))
    exact h
  obtain ⟨-, hCfix⟩ := TateStructure.map_eq_of_fixed (σ : k →+* k) hE h12.2 S
    ((S.baseChange hbij).congr hE') hq hC hS' hℓ hodd htors hcard
  obtain ⟨r, hr, hr2⟩ := TateStructure.exists_sqrt_of_map_C_eq (σ : k →+* k) hσ hE h12 S hCfix
  exact ⟨r, hr, hr2⟩

end Main

end

end Iut
