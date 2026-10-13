/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.UnramifiedZHat

/-!
# `Ẑ` and `Gal(K^ur/K)` (roadmap P17, auxiliary)

Consequences of `Gal(K^ur/K) ≃ₜ* Ẑ` (`PadicField.galMaxUnramifiedEquiv` of
`local-class-field-theory`, Frobenius `↦ 1`) used by the reconstruction files. They replace
earlier finite-level arguments (orders of the Frobenius of the unramified extensions `K_n`).

* `zhat_hom_ext`: continuous homomorphisms out of `Ẑ` into a Hausdorff group are determined by
  the image of `1` (`ℤ` is dense in `Ẑ`);
* `zhat_eq_zero_of_nsmul_eq_zero`: `Ẑ` is torsion-free;
* `frobUr_zpow_eq_one_iff`: the Frobenius of `K^ur` has infinite order;
* `eq_one_of_pow_eq_one_unr`: `Gal(K^ur/K)` is torsion-free.
-/

open PadicField Brauer

set_option linter.unusedSectionVars false

namespace Iut.Reconstruction

theorem ofAdd_intToZHat_eq_zpow (k : ℤ) :
    Multiplicative.ofAdd (intToZHat k) = Multiplicative.ofAdd (intToZHat 1) ^ k := by
  rw [← ofAdd_zsmul, ← map_zsmul, zsmul_one]
  rfl

/-- Continuous homomorphisms `Ẑ → X` (`X` Hausdorff) agreeing on `1` are equal. -/
theorem zhat_hom_ext {X : Type*} [Group X] [TopologicalSpace X] [T2Space X]
    {f g : Multiplicative ZHat →* X} (hf : Continuous f) (hg : Continuous g)
    (h : f (Multiplicative.ofAdd (intToZHat 1)) = g (Multiplicative.ofAdd (intToZHat 1))) :
    f = g := by
  have := denseRange_ofAdd_intToZHat.equalizer hf hg (funext fun k => by
    change f (Multiplicative.ofAdd (intToZHat k)) = g (Multiplicative.ofAdd (intToZHat k))
    rw [ofAdd_intToZHat_eq_zpow, map_zpow, map_zpow, h])
  exact MonoidHom.ext (congrFun this)

/-- **`Ẑ` is torsion-free.** -/
theorem zhat_eq_zero_of_nsmul_eq_zero {a : ZHat} {n : ℕ} (hn : 0 < n) (h : n • a = 0) :
    a = 0 := by
  refine ZHat.ext fun m => ?_
  set N : ℕ+ := ⟨n * m, Nat.mul_pos hn m.pos⟩
  have hmN : (m : ℕ) ∣ (N : ℕ) := Dvd.intro_left n rfl
  have h1 : (n : ZMod N) * (a : ∀ n : ℕ+, ZMod n) N = 0 := by
    have := congrArg (fun x : ZHat => (x : ∀ n : ℕ+, ZMod n) N) h
    simpa [nsmul_eq_mul] using this
  rw [← ZMod.natCast_zmod_val ((a : ∀ n : ℕ+, ZMod n) N), ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff] at h1
  have h2 : (m : ℕ) ∣ ((a : ∀ n : ℕ+, ZMod n) N).val :=
    Nat.dvd_of_mul_dvd_mul_left hn h1
  rw [← ZHat.castHom_apply a hmN, ZMod.castHom_apply, ← ZMod.natCast_zmod_val
    ((a : ∀ n : ℕ+, ZMod n) N), ZMod.cast_natCast hmN]
  change (((a : ∀ n : ℕ+, ZMod n) N).val : ZMod m) = 0
  rw [ZMod.natCast_eq_zero_iff]
  exact h2

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

/-- `frobUr ^ n = 1` only for `n = 0`. -/
theorem frobUr_zpow_eq_one_iff (n : ℤ) : frobUr p K Ω ^ n = 1 ↔ n = 0 := by
  rw [← EmbeddingLike.map_eq_one_iff (f := galMaxUnramifiedEquiv p K Ω),
    galMaxUnramifiedEquiv_frobUr_zpow,
    ofAdd_eq_one, map_eq_zero_iff _ intToZHat_injective]

/-- **`Gal(K^ur/K) ≅ Ẑ` is torsion-free.** -/
theorem eq_one_of_pow_eq_one_unr (τ : maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω) {n : ℕ}
    (hn : 0 < n) (h : τ ^ n = 1) : τ = 1 := by
  rw [← EmbeddingLike.map_eq_one_iff (f := galMaxUnramifiedEquiv p K Ω)] at h ⊢
  rw [map_pow, ← toAdd_eq_zero, toAdd_pow] at h
  rw [← toAdd_eq_zero]
  exact zhat_eq_zero_of_nsmul_eq_zero hn h

end Iut.Reconstruction
