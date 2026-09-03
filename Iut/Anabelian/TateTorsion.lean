/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.TateStructure
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The ℓ-torsion of a Tate curve (taxis #1529)

For a Tate structure `S` on `E` over `k` (`Iut.TateStructure`), the ℓ-torsion of `E(k)` is
computed in `k^×/q^ℤ`: a point `[u]` is ℓ-torsion iff `u^ℓ = q^n` for some `n ∈ ℤ`, and
`n mod ℓ` is a homomorphism `E(k)[ℓ] → ℤ/ℓℤ` (`TateStructure.resid`) whose kernel is the
graph line `μ_ℓ` (`resid_eq_zero_iff`). Hence `E(k)[ℓ]` is finite of order
`|μ_ℓ(k)| · |im| ≤ ℓ²` (`card_torsion_le`), and if `E(k)[ℓ]` has `ℓ²` elements then the
graph line has exactly `ℓ` elements and `q` has an ℓ-th root class: the canonical
generators exist (`exists_canonical`) and form the two cosets `±g + μ_ℓ`
(`isCanonical_iff`).
-/

namespace Iut.TateStructure

open WeierstrassCurve TateCurvesTheta
open scoped Classical Valued

universe u

noncomputable section

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
variable {E : WeierstrassCurve k} (S : TateStructure E)

/-! ### Powers of the Tate parameter -/

lemma norm_q_lt_one : ‖(S.t.q : k)‖ < 1 := S.t.norm_lt_one

lemma norm_q_pos : 0 < ‖(S.t.q : k)‖ := S.t.norm_q_pos

lemma q_zpow_injective : Function.Injective (fun n : ℤ => S.t.q ^ n) := by
  intro a b h
  have h' : ‖((S.t.q ^ a : kˣ) : k)‖ = ‖((S.t.q ^ b : kˣ) : k)‖ := by
    simp only at h
    rw [h]
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, norm_zpow, norm_zpow] at h'
  exact zpow_right_injective₀ S.norm_q_pos S.norm_q_lt_one.ne h'

lemma ofUnit_eq_zero_iff (u : kˣ) : S.ofUnit u = 0 ↔ ∃ n : ℤ, u = S.t.q ^ n := by
  rw [← S.ofUnit_one, S.ofUnit_eq_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_right hn.symm
  · rintro ⟨n, rfl⟩
    exact ⟨-n, by rw [zpow_neg, inv_mul_cancel]⟩

lemma nsmul_ofUnit (n : ℕ) (u : kˣ) : n • S.ofUnit u = S.ofUnit (u ^ n) := by
  unfold ofUnit
  rw [← map_nsmul]
  rfl

lemma ofUnit_mem_torsionBy_iff (ℓ : ℕ) (u : kˣ) :
    S.ofUnit u ∈ AddSubgroup.torsionBy E.toAffine.Point ℓ ↔ ∃ n : ℤ, u ^ ℓ = S.t.q ^ n := by
  rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_ofUnit, ofUnit_eq_zero_iff]

/-- The exponent of `q` in `u^ℓ` is determined modulo `ℓ` by the point of `u`. -/
lemma expo_congr (ℓ : ℕ) {u v : kˣ} {n m : ℤ} (huv : S.ofUnit u = S.ofUnit v)
    (hu : u ^ ℓ = S.t.q ^ n) (hv : v ^ ℓ = S.t.q ^ m) : (m : ZMod ℓ) = n := by
  obtain ⟨j, hj⟩ := (S.ofUnit_eq_iff u v).mp huv
  have h : S.t.q ^ m = S.t.q ^ (j * ℓ + n) := by
    rw [← hv, hj, mul_pow, hu, ← zpow_natCast, ← zpow_mul, ← zpow_add]
  have hm := S.q_zpow_injective h
  rw [hm]
  push_cast
  simp

/-! ### The residue homomorphism -/

variable (ℓ : ℕ)

/-- The ℓ-torsion of `E(k)`. -/
abbrev torsion (E : WeierstrassCurve k) : AddSubgroup E.toAffine.Point :=
  AddSubgroup.torsionBy E.toAffine.Point ℓ

lemma exists_rep (P : ↥(torsion ℓ E)) :
    ∃ u : kˣ, S.ofUnit u = P ∧ ∃ n : ℤ, u ^ ℓ = S.t.q ^ n := by
  obtain ⟨u, hu⟩ := S.ofUnit_surjective P.1
  exact ⟨u, hu, (S.ofUnit_mem_torsionBy_iff ℓ u).mp (hu ▸ P.2)⟩

/-- A chosen unit representing an ℓ-torsion point. -/
def rep (P : ↥(torsion ℓ E)) : kˣ := (S.exists_rep ℓ P).choose

lemma ofUnit_rep (P : ↥(torsion ℓ E)) : S.ofUnit (S.rep ℓ P) = P :=
  (S.exists_rep ℓ P).choose_spec.1

/-- The exponent of `q` in the ℓ-th power of the chosen representative. -/
def expo (P : ↥(torsion ℓ E)) : ℤ := (S.exists_rep ℓ P).choose_spec.2.choose

lemma rep_pow (P : ↥(torsion ℓ E)) : S.rep ℓ P ^ ℓ = S.t.q ^ S.expo ℓ P :=
  (S.exists_rep ℓ P).choose_spec.2.choose_spec

/-- **The residue homomorphism** `E(k)[ℓ] → ℤ/ℓℤ`, `[u] ↦ n mod ℓ` where `u^ℓ = q^n`. -/
def resid : ↥(torsion ℓ E) →+ ZMod ℓ where
  toFun P := (S.expo ℓ P : ZMod ℓ)
  map_zero' := by
    obtain ⟨j, hj⟩ := (S.ofUnit_eq_zero_iff _).mp (S.ofUnit_rep ℓ 0)
    have h : S.t.q ^ S.expo ℓ 0 = S.t.q ^ (j * ℓ) := by
      rw [← S.rep_pow, hj, ← zpow_natCast, ← zpow_mul]
    have := S.q_zpow_injective h
    simp [this]
  map_add' P Q := by
    have h : S.ofUnit (S.rep ℓ (P + Q)) = S.ofUnit (S.rep ℓ P * S.rep ℓ Q) := by
      rw [ofUnit_mul, ofUnit_rep, ofUnit_rep, ofUnit_rep]
      rfl
    have := S.expo_congr ℓ h (S.rep_pow ℓ (P + Q))
      (by rw [mul_pow, rep_pow, rep_pow, ← zpow_add])
    simp only [Int.cast_add] at this
    exact this.symm

lemma resid_apply (P : ↥(torsion ℓ E)) : S.resid ℓ P = (S.expo ℓ P : ZMod ℓ) := rfl

lemma resid_ofUnit {u : kˣ} {n : ℤ} (hu : u ^ ℓ = S.t.q ^ n) (hP : S.ofUnit u ∈ torsion ℓ E) :
    S.resid ℓ ⟨S.ofUnit u, hP⟩ = (n : ZMod ℓ) := by
  rw [resid_apply]
  exact S.expo_congr ℓ (S.ofUnit_rep ℓ ⟨S.ofUnit u, hP⟩).symm hu (S.rep_pow ℓ _)

/-- The kernel of the residue homomorphism is the graph line. -/
lemma resid_eq_zero_iff (P : ↥(torsion ℓ E)) :
    S.resid ℓ P = 0 ↔ (P : E.toAffine.Point) ∈ S.graphLine ℓ := by
  constructor
  · intro h
    rw [resid_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨j, hj⟩ := h
    refine ⟨S.rep ℓ P * (S.t.q ^ j)⁻¹, ?_, ?_⟩
    · rw [mul_pow, rep_pow, hj, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm (j : ℤ),
        mul_inv_cancel]
    · rw [ofUnit_mul, ofUnit_rep, (S.ofUnit_eq_zero_iff (S.t.q ^ j)⁻¹).mpr ⟨-j, by rw [zpow_neg]⟩,
        add_zero]
  · rintro ⟨ζ, hζ, hζP⟩
    have := S.expo_congr ℓ (hζP.trans (S.ofUnit_rep ℓ P).symm) (by rw [hζ, zpow_zero])
      (S.rep_pow ℓ P)
    rw [resid_apply, this]
    simp

/-! ### Cardinalities -/

variable [NeZero ℓ]

lemma graphLine_le_torsion : S.graphLine ℓ ≤ torsion ℓ E := by
  rintro _ ⟨ζ, hζ, rfl⟩
  rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_ofUnit, hζ, ofUnit_one]

/-- The roots of unity map onto the graph line. -/
lemma ofUnit_rootsOfUnity_surjective :
    Function.Surjective (fun ζ : rootsOfUnity ℓ k =>
      (⟨S.ofUnit ζ.1, ⟨ζ.1, (mem_rootsOfUnity ℓ ζ.1).mp ζ.2, rfl⟩⟩ : ↥(S.graphLine ℓ))) := by
  rintro ⟨P, ζ, hζ, rfl⟩
  exact ⟨⟨ζ, (mem_rootsOfUnity ℓ ζ).mpr hζ⟩, rfl⟩

instance finite_graphLine : Finite ↥(S.graphLine ℓ) :=
  Finite.of_surjective _ (S.ofUnit_rootsOfUnity_surjective ℓ)

lemma card_graphLine_le : Nat.card ↥(S.graphLine ℓ) ≤ ℓ :=
  (Nat.card_le_card_of_surjective _ (S.ofUnit_rootsOfUnity_surjective ℓ)).trans
    (card_rootsOfUnity (R := k) (k := ℓ))

lemma resid_ker : (S.resid ℓ).ker = (S.graphLine ℓ).addSubgroupOf (torsion ℓ E) := by
  ext P
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, resid_eq_zero_iff]

lemma card_torsion_eq :
    Nat.card ↥(torsion ℓ E) = Nat.card ↥(S.graphLine ℓ) * Nat.card ↥(S.resid ℓ).range := by
  rw [← AddSubgroup.card_mul_index (S.resid ℓ).ker, AddSubgroup.index_eq_card, resid_ker]
  congr 1
  · exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (S.graphLine_le_torsion ℓ)).toEquiv
  · rw [← resid_ker]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (S.resid ℓ)).toEquiv

lemma card_range_le : Nat.card ↥(S.resid ℓ).range ≤ ℓ :=
  (Nat.card_le_card_of_injective _ Subtype.val_injective).trans (by rw [Nat.card_zmod])

include S in
/-- **The ℓ-torsion of a Tate curve has at most `ℓ²` elements.** -/
lemma card_torsion_le : Nat.card ↥(torsion ℓ E) ≤ ℓ * ℓ := by
  rw [S.card_torsion_eq ℓ]
  exact Nat.mul_le_mul (S.card_graphLine_le ℓ) (S.card_range_le ℓ)

include S in
theorem finite_torsion : Finite ↥(torsion ℓ E) := by
  apply Nat.finite_of_card_ne_zero
  rw [S.card_torsion_eq ℓ]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

/-! ### Curves with `ℓ²` rational ℓ-torsion points -/

lemma eq_of_mul_ge {a b : ℕ} (ha : a ≤ ℓ) (hb : b ≤ ℓ) (h : ℓ * ℓ ≤ a * b) :
    a = ℓ ∧ b = ℓ := by
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (NeZero.ne ℓ)
  have hab : a * b ≤ ℓ * ℓ := Nat.mul_le_mul ha hb
  constructor
  · by_contra hne
    have : a < ℓ := lt_of_le_of_ne ha hne
    have : a * b ≤ a * ℓ := Nat.mul_le_mul_left a hb
    nlinarith
  · by_contra hne
    have : b < ℓ := lt_of_le_of_ne hb hne
    have : a * b ≤ ℓ * b := Nat.mul_le_mul_right b ha
    nlinarith

variable (h2 : ℓ * ℓ ≤ Nat.card ↥(torsion ℓ E))
include h2

/-- If the ℓ-torsion has `ℓ²` elements, the graph line has `ℓ` elements. -/
lemma card_graphLine_eq : Nat.card ↥(S.graphLine ℓ) = ℓ :=
  (eq_of_mul_ge ℓ (S.card_graphLine_le ℓ) (S.card_range_le ℓ) (by rwa [← S.card_torsion_eq])).1

/-- If the ℓ-torsion has `ℓ²` elements, the residue homomorphism is surjective. -/
lemma resid_range_eq_top : (S.resid ℓ).range = ⊤ := by
  apply AddSubgroup.eq_top_of_card_eq
  rw [Nat.card_zmod]
  exact (eq_of_mul_ge ℓ (S.card_graphLine_le ℓ) (S.card_range_le ℓ)
    (by rwa [← S.card_torsion_eq])).2

/-- If the ℓ-torsion has `ℓ²` elements, `q` has an ℓ-th root modulo `q^{ℓℤ}`. -/
lemma exists_root_class : ∃ u : kˣ, ∃ m : ℤ, u ^ ℓ = S.t.q ^ (1 + ℓ * m) := by
  have h1 : (1 : ZMod ℓ) ∈ (S.resid ℓ).range := by rw [S.resid_range_eq_top ℓ h2]; trivial
  obtain ⟨P, hP⟩ := h1
  rw [resid_apply, ← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub,
    ZMod.intCast_zmod_eq_zero_iff_dvd] at hP
  obtain ⟨m, hm⟩ := hP
  refine ⟨S.rep ℓ P, m, ?_⟩
  rw [rep_pow]
  congr 1
  linarith

end

/-! ### The canonical generators -/

section Canonical

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
variable {E : WeierstrassCurve k} (S : TateStructure E) (ℓ : ℕ)

lemma mem_graphLine_of_pow_eq {u : kˣ} {j : ℤ} (h : u ^ ℓ = S.t.q ^ (ℓ * j)) :
    S.ofUnit u ∈ S.graphLine ℓ := by
  refine ⟨u * (S.t.q ^ j)⁻¹, ?_, ?_⟩
  · rw [mul_pow, h, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm (j : ℤ), mul_inv_cancel]
  · rw [ofUnit_mul, (S.ofUnit_eq_zero_iff (S.t.q ^ j)⁻¹).mpr ⟨-j, by rw [zpow_neg]⟩, add_zero]

variable {u₁ : kˣ} {m₁ : ℤ} (hu₁ : u₁ ^ ℓ = S.t.q ^ (1 + ℓ * m₁))
include hu₁

lemma isCanonical_ofUnit : S.IsCanonical ℓ (S.ofUnit u₁) := ⟨u₁, rfl, m₁, Or.inl hu₁⟩

lemma ofUnit_mem_torsion : S.ofUnit u₁ ∈ torsion ℓ E :=
  (S.ofUnit_mem_torsionBy_iff ℓ u₁).mpr ⟨_, hu₁⟩

lemma ofUnit_not_mem_graphLine [Fact (1 < ℓ)] : S.ofUnit u₁ ∉ S.graphLine ℓ := by
  intro h
  have := (S.resid_eq_zero_iff ℓ ⟨_, S.ofUnit_mem_torsion ℓ hu₁⟩).mpr h
  rw [S.resid_ofUnit ℓ hu₁] at this
  simp at this

/-- **The canonical generators are the two cosets `±g + μ_ℓ`** of a root class `g`. -/
lemma isCanonical_iff (P : E.toAffine.Point) :
    S.IsCanonical ℓ P ↔
      P - S.ofUnit u₁ ∈ S.graphLine ℓ ∨ P + S.ofUnit u₁ ∈ S.graphLine ℓ := by
  constructor
  · rintro ⟨u, rfl, m, hu | hu⟩
    · left
      rw [sub_eq_add_neg, ← ofUnit_inv, ← ofUnit_mul]
      apply S.mem_graphLine_of_pow_eq ℓ (j := m - m₁)
      rw [mul_pow, inv_pow, hu, hu₁, ← zpow_neg, ← zpow_add]
      congr 1
      ring
    · right
      rw [← ofUnit_mul]
      apply S.mem_graphLine_of_pow_eq ℓ (j := m + m₁)
      rw [mul_pow, hu, hu₁, ← zpow_add]
      congr 1
      ring
  · rintro (⟨ζ, hζ, hζP⟩ | ⟨ζ, hζ, hζP⟩)
    · refine ⟨ζ * u₁, ?_, m₁, Or.inl ?_⟩
      · rw [ofUnit_mul, hζP, sub_add_cancel]
      · rw [mul_pow, hζ, one_mul, hu₁]
    · refine ⟨ζ * u₁⁻¹, ?_, -m₁, Or.inr ?_⟩
      · rw [ofUnit_mul, ofUnit_inv, hζP, add_neg_cancel_right]
      · rw [mul_pow, hζ, one_mul, inv_pow, hu₁, ← zpow_neg]
        congr 1
        ring

end Canonical

end Iut.TateStructure
