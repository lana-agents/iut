/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered
import Iut.EtaleTheta.TemperedCovering

/-!
# `Y = Π^tp_Y` for the tempered Frobenioid of the Tate curve (step 2, milestone (14))

**The object `Y` of the tempered Frobenioid of the Tate curve is the `ℤ`-covering of
`tempered-fundamental-groups`**: `tateY_H` (its subgroup is `Π^tp_Y = TateObject.piY`,
`TemperedCovering.lean`) and `mem_tateY_H_iff` (it is the stabilizer of the base point of the
fibre of `Y = X₀`).

(The former unit part `B₀ = U × {theta-monomial divisors}` with an arbitrary group `U` is
replaced by the genuine `B₀` of log-meromorphic functions, `Tempered/EllTheta.lean`, whose
divisor map has kernel `O_K^×`: `BAn.radDiv_eq_zero_iff`.)
-/

noncomputable section

namespace Iut

namespace Frobenioid

open CategoryTheory

universe u

/-! ### `Y` is the `ℤ`-covering of the Tate curve -/

section Tate

open TemperedFundamentalGroups

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A] (T : TateObject.Data O R)
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **The subgroup of the object `Y` of the tempered Frobenioid of the Tate curve is
`Π^tp_Y`** (`EtaleTheta.TateObject.piY`). -/
theorem tateY_H : (tateY (A := A) T V hV).H = EtaleTheta.TateObject.piY (A := A) T V hV := rfl

/-- **`Y` is the stabilizer of the base point of the fibre of the `ℤ`-covering `X₀`.** -/
theorem mem_tateY_H_iff (α : temperedPi1 O R A V hV) :
    α ∈ (tateY (A := A) T V hV).H ↔
      α.app (TateObject.X₀ T) (TateObject.basePoint T V hV) = TateObject.basePoint T V hV := by
  rw [tateY_H]
  exact EtaleTheta.TateObject.mem_piY_iff T V hV α

end Tate

end Frobenioid

end Iut
