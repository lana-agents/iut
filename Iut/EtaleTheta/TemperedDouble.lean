/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.TemperedCovering
import TemperedFundamentalGroups.Andre.TateObjectDouble

/-!
# The double covering `Ÿ → Y` and `Π^tp_Ÿ ⊆ Π^tp_Y` (step 2, milestone (15))

[EtTh] §1: `Ÿ → Y → X`, with `Ÿ = Y ×_X X'` for the `2`-isogeny covering
`X' = E_{√q} ∖ {±1} → X = E_q ∖ {0}`. `tempered-fundamental-groups`
(`Andre/TateObjectDouble.lean`) constructs `Ÿ` as a tempered object for Tate data with an element
`e` (the `x`-coordinate of the `2`-torsion point `√q`) such that `2` and `x − e` are units
(`DoubleData`: then `X'` is the Kummer covering `R[t]/(t² − (x − e))`, finite étale over
`Spec R`). Here:

* `piYddot`: **`Π^tp_Ÿ`**, the stabilizer of the base point of the fibre of `Ÿ`
  (`mem_piYddot_iff`), an open (`isOpen_piYddot`) normal subgroup of `Π^tp_X`;
* `piYddot_le_piY`: **`Π^tp_Ÿ ⊆ Π^tp_Y`** (`piY` of `TemperedCovering.lean`);
* `relIndex_piYddot_le_two`: **`[Π^tp_Y : Π^tp_Ÿ] ≤ 2`**, and `relIndex_piYddot_eq_two`: it is
  `2` as soon as some element of the decomposition group of the valuation `V` of the geometric
  point moves `√(x − e)`.
-/

namespace Iut.EtaleTheta

namespace TateObject

open TemperedFundamentalGroups

universe u

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A] (D : TemperedFundamentalGroups.TateObject.DoubleData O R)
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c)

/-- **`Π^tp_Ÿ`**: the stabilizer of the base point of the fibre of `Ÿ`. -/
noncomputable abbrev piYddot : Subgroup (temperedPi1 O R A V hV) :=
  TemperedFundamentalGroups.TateObject.piYddot (A := A) D V hV s hs

theorem mem_piYddot_iff (α : temperedPi1 O R A V hV) :
    α ∈ piYddot (A := A) D V hV s hs ↔
      α.app (TemperedFundamentalGroups.TateObject.Yddot (A := A) D)
          (TemperedFundamentalGroups.TateObject.basePoint₂ (A := A) D V hV s hs) =
        TemperedFundamentalGroups.TateObject.basePoint₂ (A := A) D V hV s hs :=
  TemperedFundamentalGroups.TateObject.mem_piYddot_iff D V hV s hs α

theorem isOpen_piYddot :
    IsOpen (piYddot (A := A) D V hV s hs : Set (temperedPi1 O R A V hV)) :=
  TemperedFundamentalGroups.TateObject.isOpen_piYddot D V hV s hs

/-- **`Π^tp_Ÿ ⊆ Π^tp_Y`.** -/
theorem piYddot_le_piY : piYddot (A := A) D V hV s hs ≤ piY (A := A) D.toData V hV :=
  TemperedFundamentalGroups.TateObject.piYddot_le_ker_character D V hV s hs

/-- **`[Π^tp_Y : Π^tp_Ÿ] ≤ 2`.** -/
theorem relIndex_piYddot_le_two :
    (piYddot (A := A) D V hV s hs).relIndex (piY (A := A) D.toData V hV) ≤ 2 :=
  TemperedFundamentalGroups.TateObject.relIndex_le_two D V hV s hs

/-- **`[Π^tp_Y : Π^tp_Ÿ] = 2`** if some element of the decomposition group moves `√(x − e)`. -/
theorem relIndex_piYddot_eq_two
    (h : ∃ σ : decompositionGroup R V, (σ : Ω ≃ₐ[R] Ω) s = -s) :
    (piYddot (A := A) D V hV s hs).relIndex (piY (A := A) D.toData V hV) = 2 :=
  TemperedFundamentalGroups.TateObject.relIndex_eq_two_of_galois D V hV s hs h

end TateObject

end Iut.EtaleTheta
