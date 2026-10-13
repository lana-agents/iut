/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.CyclotomicEnvelope
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
* **`mem_range_inl_iff_piY`**: in `Π^tp_Y[μ] = μ ⋊ Π^tp_Y` (`μ` discrete, the action with open
  kernel) the subgroup `μ` is the union of the centralizers of the open subgroups;
* **`apply_mem_range_inl_iff_piY`**: isomorphisms of such envelopes preserve `μ`
  ([EtTh], Cor. 2.19(i), first step).
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

variable {μ : Type*} [CommGroup μ] [TopologicalSpace μ] [DiscreteTopology μ]

/-- **[EtTh], Prop. 2.11(ii) for `Π^tp_Y[μ]`**, given `VerticialTempSlim`. -/
theorem mem_range_inl_iff_piY (h : VerticialTempSlim (R := R) (A := A) V hV hp hR)
    {φ : piY (A := A) T V hV →* MulAut μ} (hφ : IsOpen (φ.ker : Set (piY (A := A) T V hV)))
    (x : μ ⋊[φ] piY (A := A) T V hV) :
    x ∈ (inl : μ →* μ ⋊[φ] piY (A := A) T V hV).range ↔
      ∃ W : Subgroup (μ ⋊[φ] piY (A := A) T V hV), IsOpen (W : Set (μ ⋊[φ] _)) ∧
        x ∈ Subgroup.centralizer (W : Set (μ ⋊[φ] piY (A := A) T V hV)) :=
  Envelope.mem_range_inl_iff (tempSlim_piY V hV hp hR T h) hφ x

/-- **[EtTh], Cor. 2.19(i) (first step) for `Π^tp_Y[μ]`**: an isomorphism of cyclotomic
envelopes of `Π^tp_Y` (for two Tate data) preserves the cyclotomic subgroups, given
`VerticialTempSlim`. -/
theorem apply_mem_range_inl_iff_piY (h : VerticialTempSlim (R := R) (A := A) V hV hp hR)
    (T' : TemperedFundamentalGroups.TateObject.Data O R)
    {μ' : Type*} [CommGroup μ'] [TopologicalSpace μ'] [DiscreteTopology μ']
    {φ : piY (A := A) T V hV →* MulAut μ} {φ' : piY (A := A) T' V hV →* MulAut μ'}
    (hφ : IsOpen (φ.ker : Set (piY (A := A) T V hV)))
    (hφ' : IsOpen (φ'.ker : Set (piY (A := A) T' V hV)))
    (e : (μ ⋊[φ] piY (A := A) T V hV) ≃ₜ* (μ' ⋊[φ'] piY (A := A) T' V hV))
    (x : μ ⋊[φ] piY (A := A) T V hV) :
    e x ∈ (inl : μ' →* μ' ⋊[φ'] piY (A := A) T' V hV).range ↔
      x ∈ (inl : μ →* μ ⋊[φ] piY (A := A) T V hV).range :=
  Envelope.apply_mem_range_inl_iff (tempSlim_piY V hV hp hR T h) (tempSlim_piY V hV hp hR T' h)
    hφ hφ' e x

end TateObject

end Iut.EtaleTheta
