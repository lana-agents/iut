/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Module.LinearMap.End

/-!
# Weights of characters and quasi-trivial twists ([AbsTopI], Lemma 4.5 (ii), (iii))

The group-theoretic characterisation of the cuspidal decomposition groups of a hyperbolic
curve ([AbsTopI], Lemma 4.5, after [Mzk12], §2) uses *weights*: for the cyclotomic character
`χ_cyc : G → ℤ_ℓˣ` (of infinite order), a character `χ` is **`ℚ`-cyclotomic of weight `w`** if
`χ^b = χ_cyc^a` with `b > 0` and `w = 2a/b`; two characters are **power-equivalent** if some
positive powers agree; a representation is **quasi-trivial** if it factors through a finite
quotient. This file proves the formal parts of Lemma 4.5 (ii), (iii):

* `powEquiv_equivalence`: power-equivalence is an equivalence relation;
* `IsQCyclotomic.weight_eq`: the weight is well defined (`χ_cyc` of infinite order);
  `IsQCyclotomic.of_powEquiv`: it depends only on the power-equivalence class;
  `IsQCyclotomic.mul`: weights add; `isQCyclotomic_self` (`χ_cyc` has weight `2`),
  `isQCyclotomic_one` (the trivial character has weight `0`);
* `powEquiv_iff_isQCyclotomic_two`: the power-equivalence class of `χ_cyc` consists of the
  `ℚ`-cyclotomic characters of weight `2`; hence **`powEquiv_mul_of_weights`** (Lemma 4.5 (iii)):
  if the weights occurring range from `0` to `2` (for `H^ab ⊗ ℚ_ℓ ⊕ ℚ_ℓ` these are `0, 1, 2`, a
  deep input from the weight filtration of the Tate module), then `χ^* · χ_*` is
  power-equivalent to `χ_cyc` for any `χ^*` of maximal and `χ_*` of minimal weight;
* `IsQuasiTrivial.twist`, `isQuasiTrivial_twist_iff`: twisting by power-equivalent characters
  does not change quasi-triviality — the reason why `d_χ(M) = τ(M(χ⁻¹)) − τ(M^∨)` depends only
  on the power-equivalence class of `χ` (Lemma 4.5 (ii)).
-/

namespace Iut.Reconstruction

section Weights

variable {G A : Type*} [Group G] [CommGroup A]

/-- Two characters are **power-equivalent** if some positive powers agree. -/
def PowEquiv (χ ψ : G →* A) : Prop := ∃ n : ℕ, 0 < n ∧ χ ^ n = ψ ^ n

theorem powEquiv_equivalence : Equivalence (PowEquiv (G := G) (A := A)) where
  refl χ := ⟨1, one_pos, rfl⟩
  symm := fun ⟨n, hn, h⟩ => ⟨n, hn, h.symm⟩
  trans := fun ⟨n, hn, h⟩ ⟨m, hm, h'⟩ =>
    ⟨n * m, Nat.mul_pos hn hm, by rw [pow_mul, h, ← pow_mul, mul_comm, pow_mul, h', ← pow_mul,
      mul_comm]⟩

/-- `χ` is **`ℚ`-cyclotomic of weight `w`** (relative to `c = χ_cyc`): `χ^b = c^a`, `b > 0`,
`w = 2a/b`. -/
def IsQCyclotomic (c χ : G →* A) (w : ℚ) : Prop :=
  ∃ (a : ℤ) (b : ℕ), 0 < b ∧ χ ^ b = c ^ a ∧ w = 2 * a / b

variable {c χ ψ : G →* A} {w w' : ℚ}

theorem isQCyclotomic_self : IsQCyclotomic c c 2 :=
  ⟨1, 1, one_pos, by simp, by norm_num⟩

theorem isQCyclotomic_one : IsQCyclotomic c 1 0 :=
  ⟨0, 1, one_pos, by simp, by norm_num⟩

/-- **The weight is well defined** when `c` has infinite order. -/
theorem IsQCyclotomic.weight_eq (hc : ∀ n : ℤ, c ^ n = 1 → n = 0) (h : IsQCyclotomic c χ w)
    (h' : IsQCyclotomic c χ w') : w = w' := by
  obtain ⟨a, b, hb, hχ, rfl⟩ := h
  obtain ⟨a', b', hb', hχ', rfl⟩ := h'
  have h1 : c ^ (a * b' - a' * b) = 1 := by
    rw [zpow_sub, zpow_mul, zpow_mul, ← hχ, ← hχ', zpow_natCast, zpow_natCast, ← pow_mul,
      ← pow_mul, mul_comm b b', mul_inv_cancel]
  have h2 := hc _ h1
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  have hb0' : (b' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb'.ne'
  have h3 : (a : ℚ) * b' = a' * b := by exact_mod_cast sub_eq_zero.1 h2
  field_simp
  rw [h3, mul_comm]

/-- **The weight depends only on the power-equivalence class.** -/
theorem IsQCyclotomic.of_powEquiv (h : IsQCyclotomic c χ w) (hψ : PowEquiv χ ψ) :
    IsQCyclotomic c ψ w := by
  obtain ⟨a, b, hb, hχ, rfl⟩ := h
  obtain ⟨n, hn, hn'⟩ := hψ
  refine ⟨n * a, n * b, Nat.mul_pos hn hb, ?_, ?_⟩
  · rw [pow_mul, ← hn', ← pow_mul, mul_comm, pow_mul, hχ, ← zpow_natCast, ← zpow_mul,
      mul_comm]
  · have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    push_cast
    field_simp

/-- **Weights add.** -/
theorem IsQCyclotomic.mul (h : IsQCyclotomic c χ w) (h' : IsQCyclotomic c ψ w') :
    IsQCyclotomic c (χ * ψ) (w + w') := by
  obtain ⟨a, b, hb, hχ, rfl⟩ := h
  obtain ⟨a', b', hb', hψ, rfl⟩ := h'
  refine ⟨a * b' + a' * b, b * b', Nat.mul_pos hb hb', ?_, ?_⟩
  · rw [mul_pow, pow_mul, hχ, mul_comm b b', pow_mul, hψ, zpow_add, ← zpow_natCast,
      ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  · have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
    have hb0' : (b' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb'.ne'
    push_cast
    field_simp

/-- **The power-equivalence class of `χ_cyc`** consists of the characters of weight `2`. -/
theorem powEquiv_iff_isQCyclotomic_two : PowEquiv χ c ↔ IsQCyclotomic c χ 2 := by
  constructor
  · intro h
    exact isQCyclotomic_self.of_powEquiv (powEquiv_equivalence.symm h)
  · rintro ⟨a, b, hb, hχ, hw⟩
    have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
    have hab : (a : ℚ) = b := by
      field_simp at hw
      linarith
    have hab' : a = b := by exact_mod_cast hab
    refine ⟨b, hb, ?_⟩
    rw [hχ, hab', zpow_natCast]

/-- **[AbsTopI], Lemma 4.5 (iii)** (formal part): if `χ^*` is `ℚ`-cyclotomic of weight `2` (the
maximal weight occurring) and `χ_*` of weight `0` (the minimal one), then `χ^* · χ_*` is
power-equivalent to `χ_cyc`. -/
theorem powEquiv_mul_of_weights {χu χl : G →* A} (hu : IsQCyclotomic c χu 2)
    (hl : IsQCyclotomic c χl 0) : PowEquiv (χu * χl) c := by
  rw [powEquiv_iff_isQCyclotomic_two]
  simpa using hu.mul hl

end Weights

section QuasiTrivial

variable {G R M : Type*} [Group G] [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

/-- A representation is **quasi-trivial** if it factors through a finite quotient. -/
def IsQuasiTrivial (ρ : G →* Module.End R M) : Prop := ρ.ker.FiniteIndex

/-- The twist `ρ(χ)` of a representation by a character. -/
def twist (ρ : G →* Module.End R M) (χ : G →* Rˣ) : G →* Module.End R M where
  toFun g := ((χ g : Rˣ) : R) • ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, Units.val_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    ext m
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul, mul_comm]

omit [IsDomain R] in
theorem twist_apply (ρ : G →* Module.End R M) (χ : G →* Rˣ) (g : G) :
    twist ρ χ g = ((χ g : Rˣ) : R) • ρ g := rfl

omit [IsDomain R] in
theorem twist_twist (ρ : G →* Module.End R M) (χ ψ : G →* Rˣ) :
    twist (twist ρ χ) ψ = twist ρ (χ * ψ) := by
  ext g m
  simp [twist_apply, smul_smul, mul_comm]

/-- A character of finite order has a kernel of finite index. -/
theorem finiteIndex_ker_of_pow_eq_one {χ : G →* Rˣ} {n : ℕ} (hn : 0 < n) (h : χ ^ n = 1) :
    χ.ker.FiniteIndex := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hle : χ.range ≤ rootsOfUnity n R := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity, ← MonoidHom.pow_apply, h, MonoidHom.one_apply]
  haveI : Finite χ.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  refine ⟨?_⟩
  rw [Subgroup.index_ker]
  exact Nat.card_pos.ne'

/-- **Twisting a quasi-trivial representation by a character of finite order keeps it
quasi-trivial.** -/
theorem IsQuasiTrivial.twist {ρ : G →* Module.End R M} (hρ : IsQuasiTrivial ρ) {χ : G →* Rˣ}
    {n : ℕ} (hn : 0 < n) (h : χ ^ n = 1) : IsQuasiTrivial (Iut.Reconstruction.twist ρ χ) := by
  haveI : ρ.ker.FiniteIndex := hρ
  haveI := finiteIndex_ker_of_pow_eq_one hn h
  refine Subgroup.finiteIndex_of_le (H := ρ.ker ⊓ χ.ker) ?_
  intro g hgg
  have hg : ρ g = 1 := (MonoidHom.mem_ker).1 (Subgroup.mem_inf.1 hgg).1
  have hg' : χ g = 1 := (MonoidHom.mem_ker).1 (Subgroup.mem_inf.1 hgg).2
  rw [MonoidHom.mem_ker]
  rw [twist_apply, hg, hg', Units.val_one, one_smul]

/-- **[AbsTopI], Lemma 4.5 (ii)** (the key point): quasi-triviality of the twist `M(χ⁻¹)`
depends only on the power-equivalence class of `χ`. -/
theorem isQuasiTrivial_twist_iff {ρ : G →* Module.End R M} {χ ψ : G →* Rˣ}
    (h : PowEquiv χ ψ) :
    IsQuasiTrivial (twist ρ χ⁻¹) ↔ IsQuasiTrivial (twist ρ ψ⁻¹) := by
  obtain ⟨n, hn, hχψ⟩ := h
  constructor
  · intro hq
    have := hq.twist hn (χ := χ * ψ⁻¹) (by rw [mul_pow, hχψ, inv_pow, mul_inv_cancel])
    rwa [twist_twist, inv_mul_cancel_left] at this
  · intro hq
    have := hq.twist hn (χ := ψ * χ⁻¹) (by rw [mul_pow, ← hχψ, inv_pow, mul_inv_cancel])
    rwa [twist_twist, inv_mul_cancel_left] at this

end QuasiTrivial

end Iut.Reconstruction
