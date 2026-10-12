/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.PAdic

/-!
# The archimedean Frobenioid of a number field at an infinite place (IUT I, Example 3.4)

A minimal **archimedean Frobenioid** ([FrdII], Example 3.3(ii); IUT I, Example 3.4(i), (ii),
where it is the Frobenioid `C_v` of an `F`-prime-strip at `v ∈ V^arc`): for an infinite place `v`
of a number field `K` with completion `K_v` (`≅ ℝ` or `ℂ`), the model Frobenioid with

* base category `Pt` (the trivial Galois extension, as for the `p`-adic Frobenioid of
  `PAdic.lean`);
* divisor monoid `ℝ_{≥0}` (`Φ^gp = ℝ`, `realCone`): the divisor of `λ ∈ O^▷(K_v)` is `−log|λ|`;
* rational functions `K_v^×` with `Div_B = −log|·| : K_v^× → ℝ` (`logHom`).

Proved: it is a Frobenioid (`Arch.isFrobenioid`, [FrdI], Theorem 5.2(ii)); `O^▷(A)` is the set
`{u ∈ K_v^× : |u| ≤ 1}` (`Arch.orhd_iff`) and `O^×(A)` the unit circle `{|u| = 1}`
(`Arch.ounits_iff`), via the description of base-identity linear endomorphisms.

**Simplification.** IUT I, Example 3.4 uses the Aut-holomorphic orbispace `D_v` and a Kummer
structure `κ_v` as further data of `F_v`; they are not part of this Frobenioid (see
`Iut/HodgeTheater/PrimeStrip.lean` for how `F_v` is recorded).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField

universe u

/-- `ℝ_{≥0} ⊆ ℝ` (lifted to the universe of the local field). -/
def realCone : AddSubmonoid (ULift.{u} ℝ) where
  carrier := {x | 0 ≤ x.down}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, ULift.add_down] at ha hb ⊢
    exact add_nonneg ha hb
  zero_mem' := le_refl (0 : ℝ)

lemma mem_realCone {x : ULift.{u} ℝ} : x ∈ realCone ↔ 0 ≤ x.down := Iff.rfl

/-- The divisor monoid `ℝ_{≥0}` on `Pt`. -/
abbrev phiReal : DivMonoid.{u} Pt :=
  constDivMonoid (ULift.{u} ℝ) realCone
    (fun {x} h h' => by
      rw [mem_realCone] at h h'
      ext
      simp only [ULift.neg_down, Left.nonneg_neg_iff] at h'
      exact le_antisymm h' h)
    (fun {x} n hn h => by
      rw [mem_realCone] at h ⊢
      rw [ULift.smul_down, nsmul_eq_mul] at h
      exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hn))
    (fun x => ⟨⟨max x.down 0⟩, by simp [mem_realCone], ⟨max (-x.down) 0⟩, by
      simp [mem_realCone], by
      ext
      simp⟩)

variable {K : Type u} [Field K] (v : InfinitePlace K)

/-- `−log|·| : K_v^× → ℝ`, as a homomorphism of additive groups. -/
noncomputable def logHom : Additive (v.Completion)ˣ →+ ULift.{u} ℝ where
  toFun x := ⟨-Real.log ‖((x.toMul : (v.Completion)ˣ) : v.Completion)‖⟩
  map_zero' := by ext; simp
  map_add' x y := by
    ext
    simp only [toMul_add, Units.val_mul, norm_mul, ULift.add_down]
    rw [Real.log_mul (norm_ne_zero_iff.mpr x.toMul.ne_zero)
      (norm_ne_zero_iff.mpr y.toMul.ne_zero)]
    ring

/-- The rational functions `K_v^×`. -/
noncomputable abbrev bArch : GrpOn.{u} Pt := constGrpOn (Additive (v.Completion)ˣ)

/-- `Div_B = −log|·|`. -/
noncomputable abbrev divArch : DivHom (bArch v) (phiReal).toGrpOn := constDivHom (logHom v)

/-- **The archimedean Frobenioid of `K_v`** (over the trivial Galois extension). -/
abbrev Arch : Type u := Model phiReal (bArch v) (divArch v)

namespace Arch

/-- **The archimedean Frobenioid is a Frobenioid** ([FrdI], Theorem 5.2(ii)). -/
theorem isFrobenioid : IsFrobenioid (Model.toElem phiReal (bArch v) (divArch v)) :=
  Model.isFrobenioid

/-- `O^▷`: `−log|u| ≥ 0` iff `|u| ≤ 1`. -/
theorem orhd_iff (x : (v.Completion)ˣ) :
    logHom v (Additive.ofMul x) ∈ realCone ↔ ‖(x : v.Completion)‖ ≤ 1 := by
  rw [mem_realCone]
  change 0 ≤ -Real.log ‖(x : v.Completion)‖ ↔ _
  rw [neg_nonneg]
  exact Real.log_nonpos_iff (norm_nonneg _)

/-- `O^×`: `−log|u| = 0` iff `|u| = 1`. -/
theorem ounits_iff (x : (v.Completion)ˣ) :
    (logHom v (Additive.ofMul x)).down = 0 ↔ ‖(x : v.Completion)‖ = 1 := by
  change -Real.log ‖(x : v.Completion)‖ = 0 ↔ _
  rw [neg_eq_zero]
  constructor
  · intro h
    exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr x.ne_zero) h
  · intro h
    rw [h, Real.log_one]

end Arch

end Frobenioid

end Iut
