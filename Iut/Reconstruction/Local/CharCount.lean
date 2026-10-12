/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.ArtinPairing
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Iut.Reconstruction.GroupTheoretic
import Iut.Reconstruction.Local.UnitIndex

/-!
# Counting characters of `G_K` by local duality (roadmap P17, M1b)

For a finite extension `K/ℚ_p` with algebraic closure `Ω`, the number of continuous characters
`Gal(Ω/K) → ℤ/n` equals `[Kˣ : (Kˣ)ⁿ]` (`Iut.Reconstruction.charCount_gal`). This is the bridge
from the topological group `G_K` to the arithmetic of `K`: by `charCount_congr` the function
`n ↦ [Kˣ : (Kˣ)ⁿ]` is a group-theoretic invariant of `G_K`.

Proof: the local duality pairing `H¹(K, ℤ/n) × Kˣ/(Kˣ)ⁿ → ℤ/n` of roadmap P9
(`PadicField.pairing`, `χ ∪ κ(a)` followed by the invariant `H²(K, μ_n) ≃ ℤ/n`) is
non-degenerate on both sides (`PadicField.eq_one_of_forall_pairing_eq_zero`,
`PadicField.exists_pairing_ne_zero_of_not_mem_pow`), and a finite abelian group `B` has at
most `#B` homomorphisms to `ℤ/n` (`Iut.Reconstruction.card_monoidHom_zmod_le`, via the
`ℂˣ`-valued dual of `Mathlib.GroupTheory.FiniteAbelian.Duality`).
-/

open PadicField Brauer

namespace Iut.Reconstruction

section Dual

/-- An injective homomorphism `ℤ/n → ℂˣ`. -/
theorem exists_injective_zmod_units_complex (n : ℕ) [NeZero n] :
    ∃ φ : Multiplicative (ZMod n) →* ℂˣ, Function.Injective φ := by
  haveI : NeZero ((n : ℂ)) := ⟨Nat.cast_ne_zero.2 (NeZero.ne n)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ n
  set ζu : ℂˣ := (hζ.isUnit (NeZero.ne n)).unit
  have hζu : IsPrimitiveRoot ζu n := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    simpa [ζu] using hζ
  let e := hζu.zmodEquivZPowers
  refine ⟨(Subgroup.zpowers ζu).subtype.comp
    (AddMonoidHom.toMultiplicativeLeft e.toAddMonoidHom), ?_⟩
  intro a b h
  have h' : (AddMonoidHom.toMultiplicativeLeft e.toAddMonoidHom) a =
      (AddMonoidHom.toMultiplicativeLeft e.toAddMonoidHom) b := Subtype.ext h
  exact Multiplicative.toAdd.injective (e.injective (congrArg Additive.ofMul h'))

/-- A finite commutative group has at most `#B` homomorphisms to `ℤ/n`. -/
theorem card_monoidHom_zmod_le (B : Type*) [CommGroup B] [Finite B] (n : ℕ) [NeZero n] :
    Nat.card (B →* Multiplicative (ZMod n)) ≤ Nat.card B := by
  obtain ⟨φ, hφ⟩ := exists_injective_zmod_units_complex n
  haveI : NeZero ((Monoid.exponent B : ℂ)) :=
    ⟨Nat.cast_ne_zero.2 (Monoid.exponent_ne_zero_of_finite)⟩
  have hcard := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity B ℂ
  haveI : Finite (B →* ℂˣ) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  rw [← hcard]
  refine Nat.card_le_card_of_injective (fun χ => φ.comp χ) fun χ χ' h => ?_
  ext b
  exact congrArg Multiplicative.toAdd (hφ (DFunLike.congr_fun h b))

end Dual

section Duality

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
variable (n : ℕ) [NeZero n]

/-- The pairing with a fixed character, as a homomorphism `Kˣ → ℤ/n`. -/
noncomputable def pairingHom (χ : LocChar K Ω n) : Kˣ →* Multiplicative (ZMod n) where
  toFun a := Multiplicative.ofAdd (pairing (p := p) n χ a)
  map_one' := by rw [pairing_one]; rfl
  map_mul' a b := by rw [pairing_mul_right, ofAdd_add]

/-- The pairing with a fixed character, on `Kˣ/(Kˣ)ⁿ`. -/
noncomputable def pairingQuot (χ : LocChar K Ω n) :
    Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range →* Multiplicative (ZMod n) :=
  QuotientGroup.lift _ (pairingHom (p := p) n χ) fun a ha => by
    change Multiplicative.ofAdd (pairing (p := p) n χ a) = 1
    rw [pairing_eq_zero_of_mem_pow n χ ha]; rfl

theorem pairingQuot_injective :
    Function.Injective (fun χ : LocChar K Ω n => pairingQuot (p := p) n χ) := by
  intro χ χ' h
  have h1 : ∀ a : Kˣ, pairing (p := p) n (χ * χ'⁻¹) a = 0 := by
    intro a
    have ha := DFunLike.congr_fun h (QuotientGroup.mk a)
    change Multiplicative.ofAdd (pairing (p := p) n χ a) =
      Multiplicative.ofAdd (pairing (p := p) n χ' a) at ha
    have hinv : pairing (p := p) n χ'⁻¹ a = -pairing (p := p) n χ' a := by
      have := pairing_mul_left (p := p) n χ'⁻¹ χ' a
      rw [inv_mul_cancel] at this
      have h0 : pairing (p := p) n (1 : LocChar K Ω n) a = 0 := by
        have := pairing_mul_left (p := p) n (1 : LocChar K Ω n) 1 a
        rw [mul_one] at this
        linear_combination -this
      rw [h0] at this
      linear_combination -this
    rw [pairing_mul_left, hinv, Multiplicative.ofAdd.injective ha, add_neg_cancel]
  have := eq_one_of_forall_pairing_eq_zero (p := p) n (χ * χ'⁻¹) h1
  exact mul_inv_eq_one.1 this

/-- The pairing with a fixed class of `Kˣ/(Kˣ)ⁿ`, on characters. -/
noncomputable def pairingChar (a : Kˣ) : LocChar K Ω n →* Multiplicative (ZMod n) where
  toFun χ := Multiplicative.ofAdd (pairing (p := p) n χ a)
  map_one' := by
    have := pairing_mul_left (p := p) n (1 : LocChar K Ω n) 1 a
    rw [mul_one] at this
    have h0 : pairing (p := p) n (1 : LocChar K Ω n) a = 0 := by linear_combination -this
    rw [h0]; rfl
  map_mul' χ χ' := by rw [pairing_mul_left, ofAdd_add]

variable (p) in
include hp in
theorem card_locChar_le [Finite (LocChar K Ω n)] :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ≤ Nat.card (LocChar K Ω n) := by
  set P := (powMonoidHom n : Kˣ →* Kˣ).range
  let F : Kˣ ⧸ P → (LocChar K Ω n →* Multiplicative (ZMod n)) :=
    Quotient.lift (fun a => pairingChar (p := p) (Ω := Ω) n a) (by
      intro a b hab
      ext χ
      have hmem : a⁻¹ * b ∈ P := QuotientGroup.leftRel_apply.1 hab
      have h0 := pairing_eq_zero_of_mem_pow (p := p) n χ hmem
      rw [pairing_mul_right] at h0
      have hinv : pairing (p := p) n χ a⁻¹ = -pairing (p := p) n χ a := by
        have := pairing_mul_right (p := p) n χ a⁻¹ a
        rw [inv_mul_cancel, pairing_one] at this
        linear_combination -this
      change Multiplicative.ofAdd (pairing (p := p) n χ a) =
        Multiplicative.ofAdd (pairing (p := p) n χ b)
      congr 1
      linear_combination -h0 + hinv)
  have hF : Function.Injective F := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    rw [QuotientGroup.eq]
    by_contra hnot
    obtain ⟨χ, hχ⟩ := exists_pairing_ne_zero_of_not_mem_pow (p := p) (Ω := Ω) n hnot
    apply hχ
    have h1 := DFunLike.congr_fun hxy χ
    change Multiplicative.ofAdd (pairing (p := p) n χ a) =
      Multiplicative.ofAdd (pairing (p := p) n χ b) at h1
    have hinv : pairing (p := p) n χ a⁻¹ = -pairing (p := p) n χ a := by
      have := pairing_mul_right (p := p) n χ a⁻¹ a
      rw [inv_mul_cancel, pairing_one] at this
      linear_combination -this
    rw [pairing_mul_right, hinv, Multiplicative.ofAdd.injective h1, neg_add_cancel]
  haveI : Finite (LocChar K Ω n →* Multiplicative (ZMod n)) :=
    Finite.of_injective _ DFunLike.coe_injective
  exact (Nat.card_le_card_of_injective F hF).trans (card_monoidHom_zmod_le _ n)

variable (p) in
include hp in
/-- **Local duality count**: `#H¹(K, ℤ/n) = [Kˣ : (Kˣ)ⁿ]`. -/
theorem card_locChar : Nat.card (LocChar K Ω n) = powIndex Kˣ n := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  haveI := KummerTheory.finiteIndex_powRange_of_isDiscreteValuationRing (𝒪 p K) K n
    (Nat.cast_ne_zero.2 (NeZero.ne n))
  set P := (powMonoidHom n : Kˣ →* Kˣ).range
  haveI : Finite (Kˣ ⧸ P) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Finite (Kˣ ⧸ P →* Multiplicative (ZMod n)) :=
    Finite.of_injective _ DFunLike.coe_injective
  have h1 : Nat.card (LocChar K Ω n) ≤ Nat.card (Kˣ ⧸ P) :=
    (Nat.card_le_card_of_injective _ (pairingQuot_injective (p := p) n)).trans
      (card_monoidHom_zmod_le _ n)
  haveI : Finite (LocChar K Ω n) := Finite.of_injective _ (pairingQuot_injective (p := p) n)
  exact le_antisymm h1 (card_locChar_le p n)

variable (K Ω) in
/-- Continuous characters of `Gal(Ω/K)` are `LocChar K Ω n`. -/
def contCharEquivLocChar : ContChar (Ω ≃ₐ[K] Ω) n ≃ LocChar K Ω n :=
  Equiv.refl _

variable (p) in
include hp in
/-- **The character count of `G_K`**: `#Hom_cont(Gal(Ω/K), ℤ/n) = [Kˣ : (Kˣ)ⁿ]` for `n ≥ 1`. -/
theorem charCount_gal : charCount (Ω ≃ₐ[K] Ω) n = powIndex Kˣ n := by
  rw [charCount, Nat.card_congr (contCharEquivLocChar K Ω n), card_locChar p]

end Duality

end Iut.Reconstruction
