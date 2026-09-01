/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.ThetaRegion
import Iut.Implication.Theorem110

/-!
# Concrete arithmetic invariants of Theorem 1.10 (taxis #1453)

For the concrete variant data `concreteVariantData D LT TL QI`, the invariants of
`Theorem110Invariants` that live on the `ℓ`-torsion field `K` are defined here from the
local theory:

* the **distinguished primes** `V_ℚ^dst`: the primes dividing `2·3·5·ℓ`, the residue
  characteristics of the bad places, and the primes ramified in `K` (conditions (D6)/(D7)
  in the proof of Theorem 1.10, taken as the definition);
* the **local different contributions** `log(d^K_p) = ∑_{v ∣ p} w_v·d_v·log p`, from the
  different exponents `d_v = ord_𝔭(𝔡_{K/ℚ})/e_v` (`Iut.differentExponent`) and the weights
  `w_v = [K_v : ℚ_p]/[K : ℚ]`.

The invariants of the tripodal field `F_tpd = F_mod(E[2])` and of `F_mod` —
`log(d_{F_tpd})`, `log(f_{F_tpd})`, `e_mod` — together with the ramification bound (R4) of
the proof of Theorem 1.10 are supplied by `ArithmeticInputs` (standard algebraic number
theory of the tower `F_mod ⊆ F_tpd ⊆ F ⊆ K`; IUT IV, Propositions 1.3 and 1.8).

The file also proves the weighted-average identities of IUT IV, Proposition 1.7 in the
form used by Step (v): for weights summing to `1`, the weighted sum over tuples of a
quantity depending on one coordinate is the weighted sum over places.
-/

namespace Iut

universe u v

open NumberField
open scoped Pointwise

/-! ### Weighted averages over tuples (IUT IV, Proposition 1.7) -/

section Average

variable {ι E : Type*} [Fintype ι] [Fintype E] [DecidableEq ι] (w : E → ℝ)

/-- The tuple weights sum to `(∑ w)^{|ι|}`. -/
lemma sum_prod_tuple : ∑ c : ι → E, ∏ i, w (c i) = (∑ e, w e) ^ Fintype.card ι := by
  rw [← Fintype.prod_sum (fun _ : ι => w)]
  simp

/-- Proposition 1.7, one coordinate: `∑_c (∏_i w(c i))·f(c i₀) = (∑_e w e f e)·(∑ w)^{|ι|−1}`;
with `∑ w = 1` the right-hand side is `∑_e w e f e`. -/
lemma sum_prod_tuple_mul_coord (hw : ∑ e, w e = 1) (f : E → ℝ) (i₀ : ι) :
    ∑ c : ι → E, (∏ i, w (c i)) * f (c i₀) = ∑ e, w e * f e := by
  let g : ι → E → ℝ := fun i e => if i = i₀ then w e * f e else w e
  have hg : ∀ c : ι → E, (∏ i, w (c i)) * f (c i₀) = ∏ i, g i (c i) := by
    intro c
    rw [← Finset.mul_prod_erase Finset.univ (fun i => g i (c i)) (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase Finset.univ (fun i => w (c i)) (Finset.mem_univ i₀)]
    have : ∏ i ∈ Finset.univ.erase i₀, g i (c i) = ∏ i ∈ Finset.univ.erase i₀, w (c i) :=
      Finset.prod_congr rfl fun i hi => by simp [g, (Finset.mem_erase.mp hi).1]
    rw [this]
    simp only [g, if_true]
    ring
  simp_rw [hg]
  rw [← Fintype.prod_sum g,
    ← Finset.mul_prod_erase Finset.univ (fun i => ∑ e, g i e) (Finset.mem_univ i₀)]
  have : ∏ i ∈ Finset.univ.erase i₀, ∑ e, g i e = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    simp [g, (Finset.mem_erase.mp hi).1, hw]
  rw [this, mul_one]
  simp [g]

/-- Proposition 1.7, summed over the coordinates:
`∑_c (∏_i w(c i))·∑_i f(c i) = |ι|·∑_e w e f e`. -/
lemma sum_prod_tuple_mul_sum (hw : ∑ e, w e = 1) (f : E → ℝ) :
    ∑ c : ι → E, (∏ i, w (c i)) * ∑ i, f (c i) = Fintype.card ι * ∑ e, w e * f e := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_prod_tuple_mul_coord w hw f]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

omit [DecidableEq ι] in
/-- The tuple weights sum to `1` when the weights do (for any `Fintype` instance on the
tuples). -/
lemma sum_prod_tuple_eq_one (hw : ∑ e, w e = 1) [inst : Fintype (ι → E)] :
    ∑ c : ι → E, ∏ i, w (c i) = 1 := by
  classical
  rw [Subsingleton.elim inst Pi.instFintype]
  clear inst
  rw [sum_prod_tuple, hw, one_pow]

end Average

/-! ### The concrete invariants -/

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}

namespace LocalTheory

variable (LT)

/-- The residue characteristics of the primes ramified in `K`, as a finite set. -/
noncomputable def ramifiedChars : Finset ℕ :=
  (LT.ramified_finite.toFinset).image residueChar

/-- `log(d^K_p) = ∑_{v ∣ p} w_v·d_v·log p` (the contribution of `p` to the normalized
degree of the different of `K`), and `0` at non-primes. -/
noncomputable def logDK (p : ℕ) : ℝ :=
  if hp : p.Prime then
    ∑ v : LT.Fiber (.finite ⟨p, hp⟩),
      LT.weight _ v * differentExponent D.Kt (LT.fiberPlace v) * Real.log p
  else 0

lemma differentExponent_nonneg (w : FinitePlace D.Kt) : 0 ≤ differentExponent D.Kt w :=
  div_nonneg (by positivity) (by positivity)

lemma logDK_nonneg (p : ℕ) : 0 ≤ LT.logDK p := by
  unfold LocalTheory.logDK
  split_ifs with hp
  · exact Finset.sum_nonneg fun v _ => mul_nonneg
      (mul_nonneg (LT.weight_pos _ v).le (differentExponent_nonneg _))
      (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
  · exact le_rfl

end LocalTheory

namespace ThetaLocalData

variable (TL : ThetaLocalData D LT)

/-- **The distinguished primes** `V_ℚ^dst`: `2, 3, 5, ℓ`, the bad residue characteristics,
and the primes ramified in `K` ((D6)/(D7), as the definition). -/
noncomputable def dst : Finset ℕ :=
  {2, 3, 5, D.ℓ} ∪ TL.badChars ∪ LT.ramifiedChars

lemma dst_prime (p : ℕ) (hp : p ∈ TL.dst) : p.Prime := by
  simp only [dst, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    LocalTheory.ramifiedChars, Finset.mem_image, Set.Finite.mem_toFinset] at hp
  rcases hp with ((rfl | rfl | rfl | rfl) | hb) | ⟨w, _, rfl⟩
  · exact Nat.prime_two
  · exact Nat.prime_three
  · exact Nat.prime_five
  · exact D.prime.ℓ_prime
  · exact TL.badChars_prime _ hb
  · exact LT.residueChar_prime w

lemma mem_dst_of_ramified (w : FinitePlace D.Kt) (hw : ramIdx D.Kt w ≠ 1) :
    residueChar w ∈ TL.dst := by
  refine Finset.mem_union_right _ ?_
  simp only [LocalTheory.ramifiedChars, Finset.mem_image, Set.Finite.mem_toFinset]
  exact ⟨w, hw, rfl⟩

lemma mem_dst_of_badChars (p : ℕ) (hp : p ∈ TL.badChars) : p ∈ TL.dst :=
  Finset.mem_union_left _ (Finset.mem_union_right _ hp)

lemma two_mem_dst : 2 ∈ TL.dst := by
  refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
  simp

lemma logDK_eq_zero (p : ℕ) (hp : p ∉ TL.dst) : LT.logDK p = 0 := by
  unfold LocalTheory.logDK
  split_ifs with hpp
  · refine Finset.sum_eq_zero fun v _ => ?_
    have hunr : ramIdx D.Kt (LT.fiberPlace v) = 1 := by
      by_contra hne
      apply hp
      have := TL.mem_dst_of_ramified _ hne
      rwa [LT.residueChar_fiberPlace] at this
    simp [differentExponent, LT.ordDifferent_eq_zero _ hunr]
  · rfl

end ThetaLocalData

variable (D LT) (TL : ThetaLocalData D LT) (QI : QPilotInputs D)

/-- **The arithmetic inputs of the tripodal tower** (IUT IV, Theorem 1.10): the maximal
ramification index `e_mod` of `F_mod`, the different and conductor degrees of
`F_tpd = F_mod(E[2])`, and the ramification bound (R4) on the places of `K`
(from (R1)–(R3): the structure of the tower `F_mod ⊆ F_tpd ⊆ F ⊆ K` through
Proposition 1.8 and IUT I, Definition 3.1(c)). Standard algebraic number theory of
the specific tower; delegated (taxis #5, #1453). -/
structure ArithmeticInputs where
  /-- The maximal ramification index `e_mod` of `F_mod` over `ℚ`. -/
  emod : ℕ
  /-- `1 ≤ e_mod`. -/
  one_le_emod : 1 ≤ emod
  /-- `e_mod ≤ d_mod`. -/
  emod_le_dmod : emod ≤ Module.finrank ℚ ↥(fieldOfModuli D.F D.E)
  /-- `log(d_{F_tpd})`, the normalized degree of the different of `F_tpd`. -/
  logDtpd : ℝ
  /-- `log(d_{F_tpd}) ≥ 0`. -/
  logDtpd_nonneg : 0 ≤ logDtpd
  /-- `log(f_{F_tpd})`, the normalized degree of the conductor of `F_tpd`. -/
  logFtpd : ℝ
  /-- `log(f_{F_tpd}) ≥ 0`. -/
  logFtpd_nonneg : 0 ≤ logFtpd
  /-- **(R4)**: if `e_v > p_v − 2` then `p_v ≤ e*_mod·ℓ` and
  `log e_v ≤ −3 + 4·log(e*_mod·ℓ)`, with `e*_mod = 552960·e_mod`. -/
  ramIdx_bound : ∀ v : FinitePlace D.Kt, residueChar v - 2 < ramIdx D.Kt v →
    residueChar v ≤ 552960 * emod * D.ℓ ∧
      Real.log (ramIdx D.Kt v) ≤ -3 + 4 * Real.log (((552960 * emod : ℕ) : ℝ) * D.ℓ)

variable {D LT TL QI}

namespace ArithmeticInputs

variable (AI : ArithmeticInputs D)

/-- **The concrete invariants of Theorem 1.10** for the concrete variant data. -/
noncomputable def invariants : Theorem110Invariants (concreteVariantData D LT TL QI) where
  emod := AI.emod
  one_le_emod := AI.one_le_emod
  emod_le_dmod := AI.emod_le_dmod
  logDtpd := AI.logDtpd
  logDtpd_nonneg := AI.logDtpd_nonneg
  logFtpd := AI.logFtpd
  logFtpd_nonneg := AI.logFtpd_nonneg
  dst := TL.dst
  dst_prime := TL.dst_prime
  logDK := LT.logDK
  logDK_nonneg := LT.logDK_nonneg
  logDK_eq_zero := TL.logDK_eq_zero

/-- The residue characteristics of the bad places of `F` are distinguished ((D2)). -/
lemma bad_mem_dst (w : FinitePlace D.F)
    (hw : w ∈ (concreteVariantData D LT TL QI).qPilot.badFinset) : residueChar w ∈ TL.dst :=
  TL.mem_dst_of_badChars _ (TL.bad_residueChar_mem w
    ((concreteVariantData D LT TL QI).qPilot.mem_bad hw))

/-- The arithmetic certificate of Theorem 1.10 for the concrete invariants, from `ℓ ≥ 7`
and Steps (ii) and (iii) (the two inputs of the tower's number theory that remain
explicit; IUT IV, Propositions 1.3, 1.8 and (D1)–(D7)). -/
theorem certificate (h7 : 7 ≤ D.ℓ)
    (step_ii : (AI.invariants (LT := LT) (TL := TL) (QI := QI)).logDKtot ≤
      AI.logDtpd + AI.logFtpd + 2 * Real.log D.ℓ + 21)
    (step_iii : (AI.invariants (LT := LT) (TL := TL) (QI := QI)).logSQ ≤
      2 * Module.finrank ℚ ↥(fieldOfModuli D.F D.E) * (AI.logDtpd + AI.logFtpd) + 5 +
        Real.log D.ℓ) :
    Theorem110Certificate (AI.invariants (LT := LT) (TL := TL) (QI := QI)) where
  seven_le := h7
  bad_mem_dst := bad_mem_dst (LT := LT) (TL := TL) (QI := QI)
  step_ii := step_ii
  step_iii := step_iii

end ArithmeticInputs

end Iut
