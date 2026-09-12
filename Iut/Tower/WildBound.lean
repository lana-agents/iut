/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.RamIdx

/-!
# The wild ramification bound from the degree divisibilities and tameness

`Iut.padicValNat_mul_le_wildConst`: for a prime `ℓ ≥ 7` and a prime `p`, if
`e₁ ∣ |GL₂(𝔽_ℓ)| = (ℓ² − 1)(ℓ² − ℓ)`, `e₂ ∣ 2¹²·3²·5` and `p ∤ e₁` for `p ≠ ℓ`, then
`v_p(e₁·e₂) ≤ c_p = wildConst ℓ p`. This is the arithmetic behind the wild ramification
bound `v_p(e(v/u)) ≤ c_p` of `Iut.TowerLocalFacts`: `e(v/u) = e(v/w)·e(w/u)` with
`e(v/w) ∣ [K : F] ∣ |GL₂(𝔽_ℓ)|` (and `K/F` tame away from `ℓ`) and
`e(w/u) ∣ [F : F_tpd] ∣ 2¹²·3²·5`.
-/

namespace Iut

open NumberField

/-- `v_ℓ((ℓ² − 1)(ℓ² − ℓ)) = 1` for a prime `ℓ`: `ℓ ∤ ℓ² − 1` and `ℓ² − ℓ = ℓ(ℓ − 1)`. -/
lemma padicValNat_card_GL_two {ℓ : ℕ} (hℓ : ℓ.Prime) :
    padicValNat ℓ ((ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ)) = 1 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have h2 := hℓ.two_le
  have h1 : ℓ ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ ℓ ^ 2 := by nlinarith
    omega
  have h1' : ¬ ℓ ∣ ℓ ^ 2 - 1 := by
    intro h
    have h3 : ℓ ∣ ℓ ^ 2 := dvd_pow_self ℓ two_ne_zero
    have h4 : ℓ ∣ ℓ ^ 2 - (ℓ ^ 2 - 1) := Nat.dvd_sub h3 h
    have h5 : ℓ ^ 2 - (ℓ ^ 2 - 1) = 1 := by
      have : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    rw [h5] at h4
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h4)
  have h6 : ℓ ^ 2 - ℓ = ℓ * (ℓ - 1) := by
    rw [Nat.mul_sub_one, ← pow_two]
  have h7 : ¬ ℓ ∣ ℓ - 1 := by
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  rw [h6, padicValNat.mul h1 (Nat.mul_ne_zero hℓ.ne_zero (by omega)),
    padicValNat.mul hℓ.ne_zero (by omega),
    padicValNat.eq_zero_of_not_dvd h1', padicValNat.eq_zero_of_not_dvd h7, padicValNat_self]

/-- `v_p(2¹²·3²·5) ≤ c_p − [p = ℓ]`: the wild factor at `p ≠ ℓ`. -/
lemma padicValNat_184320_le {ℓ p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ) :
    padicValNat p 184320 ≤ wildConst ℓ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h184320 : (184320 : ℕ) = 2 ^ 12 * 3 ^ 2 * 5 := by norm_num
  have hle : ∀ c : ℕ, ¬ p ^ (c + 1) ∣ 184320 → padicValNat p 184320 ≤ c := by
    intro c hc
    by_contra h
    exact hc ((pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd)
  unfold wildConst
  rw [if_neg hpℓ, add_zero]
  by_cases h2 : p = 2
  · subst h2
    rw [if_pos rfl]
    exact hle 12 (by decide)
  by_cases h3 : p = 3
  · subst h3
    rw [if_neg (by decide), if_pos rfl]
    exact hle 2 (by decide)
  by_cases h5 : p = 5
  · subst h5
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact hle 1 (by decide)
  rw [if_neg h2, if_neg h3, if_neg h5]
  refine hle 0 fun h => ?_
  rw [pow_one, h184320] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
  · exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)

/-- **The wild ramification bound from the degree divisibilities**: `v_p(e₁·e₂) ≤ c_p` for
`e₁ ∣ (ℓ² − 1)(ℓ² − ℓ)`, `e₂ ∣ 2¹²·3²·5` and `p ∤ e₁` when `p ≠ ℓ`, for primes `p` and
`ℓ ≥ 7`. -/
theorem padicValNat_mul_le_wildConst {ℓ p e₁ e₂ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) (hp : p.Prime)
    (h₁ : e₁ ∣ (ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ)) (h₂ : e₂ ∣ 184320) (htame : p ≠ ℓ → ¬ p ∣ e₁) :
    padicValNat p (e₁ * e₂) ≤ wildConst ℓ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hGL : (ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ) ≠ 0 := by
    have h2 := hℓ.two_le
    exact Nat.mul_ne_zero (Nat.sub_ne_zero_of_lt (by nlinarith))
      (Nat.sub_ne_zero_of_lt (by nlinarith))
  have he₁ : e₁ ≠ 0 := ne_zero_of_dvd_ne_zero hGL h₁
  have he₂ : e₂ ≠ 0 := ne_zero_of_dvd_ne_zero (by norm_num) h₂
  have hv₁ : padicValNat p e₁ ≤ padicValNat p ((ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ)) :=
    (padicValNat_dvd_iff_le hGL).mp (pow_padicValNat_dvd.trans h₁)
  have hv₂ : padicValNat p e₂ ≤ padicValNat p 184320 :=
    (padicValNat_dvd_iff_le (by norm_num)).mp (pow_padicValNat_dvd.trans h₂)
  rw [padicValNat.mul he₁ he₂]
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    rw [padicValNat_card_GL_two hℓ] at hv₁
    have hv₂' : padicValNat p 184320 = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h
      have h184320 : (184320 : ℕ) = 2 ^ 12 * 3 ^ 2 * 5 := by norm_num
      rw [h184320] at h
      rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
          omega
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
          omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h
        omega
    have hw : wildConst p p = (if p = 2 then 12 else if p = 3 then 2 else if p = 5 then 1
        else 0) + 1 := by
      simp [wildConst]
    rw [hw]
    omega
  · rw [padicValNat.eq_zero_of_not_dvd (htame hpℓ), zero_add]
    exact hv₂.trans (padicValNat_184320_le hp hpℓ)

section Torsion

universe u

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

/-- **`[K : F] ∣ |GL₂(𝔽_ℓ)|`**: the torsion field is the fixed field of the kernel of the
mod-`ℓ` representation, whose index is the order of the image, a subgroup of `GL₂(𝔽_ℓ)`. -/
theorem finrank_torsionField_dvd (Pr : AdmissiblePrimeData F E Fbar VBad) :
    Module.finrank F ↥Pr.torsionField ∣ (Pr.ℓ ^ 2 - 1) * (Pr.ℓ ^ 2 - Pr.ℓ) := by
  let H : ClosedSubgroup (Fbar ≃ₐ[F] Fbar) :=
    ⟨Pr.rep.ker, Subgroup.isClosed_of_isOpen _ Pr.ker_isOpen⟩
  have h1 : Module.finrank F ↥Pr.torsionField = Pr.rep.ker.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index]
    change (IntermediateField.fixedField H.1).fixingSubgroup.index = H.1.index
    rw [InfiniteGalois.fixingSubgroup_fixedField H]
  haveI : NeZero Pr.ℓ := ⟨Pr.ℓ_prime.ne_zero⟩
  rw [h1, Subgroup.index_ker, ← card_GL_two_of_prime Pr.ℓ Pr.ℓ_prime]
  exact Subgroup.card_subgroup_dvd_card _

end Torsion

end Iut
