/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.CyclotomicEnvelope
import Iut.EtaleTheta.Env.Envelope
import Iut.EtaleTheta.TemperedCovering
import TemperedFundamentalGroups.Andre.TempSlim

/-!
# Temp-slimness of `Π^tp_Y` and [EtTh] Cor. 2.19(i) for `Π^tp_Y[μ]`

`CyclotomicEnvelope.lean` proves [EtTh], Prop. 2.11(ii) / Cor. 2.19(i) (first step) for a
temp-slim `P`. Here `P` is the actual tempered fundamental group `Π^tp_Y = TateObject.piY` of the
`ℤ`-covering of the Tate curve: by `tempered-fundamental-groups` (`Andre/TempSlim.lean`,
[Mzk14], Example 3.10) `Π^tp_Y` is temp-slim given **`VerticialTempSlim`** — some verticial
subgroup of André's tower satisfies `HI` (the specialization theorem M2) and is temp-slim
(slimness of the decomposition group of a component). That is the only remaining input; the
argument from it is proved.

* **`tempSlim_piY`**: `VerticialTempSlim → TempSlim Π^tp_Y`;
* **`mem_range_inl_iff_piY`**: in `Π^tp_Y[μ] = μ ⋊ Π^tp_Y` (`μ` finite) the subgroup `μ` is the
  union of the centralizers of the finite-index subgroups, given **`FISlim Π^tp_Y`**;
* **`apply_mem_range_inl_iff_piY`**: group isomorphisms of such envelopes preserve `μ`
  ([EtTh], Cor. 2.19(i), first step), given `FISlim`.

**Shell #29 (lead decision 2026-10-26):** the consumers of [EtTh], Prop. 2.11(ii) for `Π^tp_Y`
use the finite-index form (`Env/Envelope.lean`, `Envelope.mem_range_inl_iff_finiteIndex`), so the
remaining debt is `FISlim Π^tp_Y` (every finite-index subgroup has trivial centralizer) instead of
`VerticialTempSlim`. Discharge path: `TempSlim.centralizer_eq_bot_of_denseRange`
(`tempered-fundamental-groups`, `SemiAnbd/DenseSlim.lean`, MR13 decision D4; not yet at iut's
pin) applied to the dense embedding `Π^tp_Y ↪ Π̂_Y` (M2-GEA) and the slimness of the profinite
`Π̂_Y` (MR2). `tempSlim_piY` stays as the (open-subgroup) temp-slimness statement of the
`VerticialTempSlim` route.
-/

universe u

namespace Iut.EtaleTheta

open TemperedFundamentalGroups SemidirectProduct
open scoped Envelope

namespace TateObject

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A] [Finite A] [SMulCommClass A K R]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
  (T : TemperedFundamentalGroups.TateObject.Data O R)

/-- **`Π^tp_Y` is temp-slim**, given `VerticialTempSlim` (`tempered-fundamental-groups`,
`tempSlim_ker_character`). -/
theorem tempSlim_piY (h : VerticialTempSlim (R := R) (A := A) V hV hp hR) :
    TempSlim (piY (A := A) T V hV) :=
  fun H hH => tempSlim_ker_character V hV hp hR T h H hH

variable {μ : Type*} [CommGroup μ] [Finite μ]

omit [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [PerfectField (IsLocalRing.ResidueField O)] [Algebra.Smooth K R] [Finite A] [SMulCommClass A K R]
  [IsAlgClosed Ω] in
/-- **[EtTh], Prop. 2.11(ii) for `Π^tp_Y[μ]`** (`μ` finite), given `FISlim Π^tp_Y`. -/
theorem mem_range_inl_iff_piY (hFI : Envelope.FISlim (piY (A := A) T V hV))
    {φ : piY (A := A) T V hV →* MulAut μ} (x : μ ⋊[φ] piY (A := A) T V hV) :
    x ∈ (inl : μ →* μ ⋊[φ] piY (A := A) T V hV).range ↔
      ∃ W : Subgroup (μ ⋊[φ] piY (A := A) T V hV), W.FiniteIndex ∧
        x ∈ Subgroup.centralizer (W : Set (μ ⋊[φ] piY (A := A) T V hV)) :=
  Envelope.mem_range_inl_iff_finiteIndex hFI x

omit [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [PerfectField (IsLocalRing.ResidueField O)] [Algebra.Smooth K R] [Finite A] [SMulCommClass A K R]
  [IsAlgClosed Ω] in
/-- **[EtTh], Cor. 2.19(i) (first step) for `Π^tp_Y[μ]`**: a group isomorphism of cyclotomic
envelopes of `Π^tp_Y` (for two Tate data, `μ`, `μ'` finite) preserves the cyclotomic subgroups,
given `FISlim` for both tempered groups. -/
theorem apply_mem_range_inl_iff_piY (T' : TemperedFundamentalGroups.TateObject.Data O R)
    (hFI : Envelope.FISlim (piY (A := A) T V hV)) (hFI' : Envelope.FISlim (piY (A := A) T' V hV))
    {μ' : Type*} [CommGroup μ'] [Finite μ']
    {φ : piY (A := A) T V hV →* MulAut μ} {φ' : piY (A := A) T' V hV →* MulAut μ'}
    (e : (μ ⋊[φ] piY (A := A) T V hV) ≃* (μ' ⋊[φ'] piY (A := A) T' V hV))
    (x : μ ⋊[φ] piY (A := A) T V hV) :
    e x ∈ (inl : μ' →* μ' ⋊[φ'] piY (A := A) T' V hV).range ↔
      x ∈ (inl : μ →* μ ⋊[φ] piY (A := A) T V hV).range :=
  Envelope.apply_mem_range_inl_iff_finiteIndex hFI hFI' e x

end TateObject

end Iut.EtaleTheta
