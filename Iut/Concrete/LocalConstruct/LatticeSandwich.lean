/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.FactorShell
import Iut.Concrete.LocalConstruct.PacketDifferent

/-!
# The tensor product of the log-shells between two scaled orders (IUT IV, Prop. 1.2)

For a packet all of whose places lie over `p`, with `α = ⊗_j (2p)⁻¹ϖ_{a,j}` and
`β = ⊗_j (2p)⁻¹ϖ_{b,j}` (`FactorShell.lean`):

`α · R_I ⊆ ⊗_j 𝓘_{c j} ⊆ β · R_I`

(`tprod_scalA_mul_mem_tensorLogShell`, `mem_tensorLogShell_iff_exists`), the tensor-product form
of IUT IV, Proposition 1.2(i), used in the proof of Proposition 1.2(ii).
-/

namespace Iut

open PadicLogVolume

namespace LocalConstruct

open NumberField
open scoped TensorProduct Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K] {ι : Type}
  (p : Nat.Primes) (c : ι → Place K)

/-- The scalar `(2p)⁻¹ϖ_a` of the factor `j`. -/
noncomputable def scalA (j : ι) : completionAt K (finPart K (c j)) :=
  (2 * ((residueChar (finPart K (c j)) : ℕ) : completionAt K (finPart K (c j))))⁻¹ *
    varpiA (finPart K (c j))

/-- The scalar `(2p)⁻¹ϖ_b` of the factor `j`. -/
noncomputable def scalB (j : ι) : completionAt K (finPart K (c j)) :=
  (2 * ((residueChar (finPart K (c j)) : ℕ) : completionAt K (finPart K (c j))))⁻¹ *
    varpiB (finPart K (c j))

lemma scalA_ne_zero (j : ι) : scalA c j ≠ 0 :=
  mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero (residueChar_ne_zero' _)))
    (varpiA_ne_zero _)

lemma scalB_ne_zero (j : ι) : scalB c j ≠ 0 :=
  mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero (residueChar_ne_zero' _)))
    (varpiB_ne_zero _)

/-- `ord_p(scalA) − ord_p(scalB) = a + b`. -/
lemma ordp_scalA_sub_scalB (j : ι) :
    ordp K _ (scalA c j) - ordp K _ (scalB c j) =
      logLatticeA (residueChar (finPart K (c j))) (ramIdx K (finPart K (c j))) +
        logLatticeB (residueChar (finPart K (c j))) (ramIdx K (finPart K (c j))) := by
  have h2p := inv_ne_zero (mul_ne_zero two_ne_zero (residueChar_ne_zero' (finPart K (c j))))
  unfold scalA scalB
  rw [ordp_mul _ _ _ h2p (varpiA_ne_zero _), ordp_mul _ _ _ h2p (varpiB_ne_zero _),
    ordp_varpiA, ordp_varpiB]
  ring

variable {p c} [Fintype ι]

/-- **`α · R_I ⊆ ⊗_j 𝓘_{c j}`.** -/
theorem tprod_scalA_mul_mem_tensorLogShell (hc : ∀ j, IsOver K p (c j))
    {r : Tensor K (.finite p) c} (hr : r ∈ order p c) :
    PiTensorProduct.tprod ℚ_[p] (fun j => factorMk p (c j) (scalA c j)) * r ∈
      tensorLogShell p c := by
  rw [mem_order] at hr
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    unfold tprodIntegral
    rw [PiTensorProduct.tprod_mul_tprod]
    refine Submodule.subset_span ⟨fun j => ⟨_, ?_⟩, rfl⟩
    have hres := (hc j).residueChar_finPart
    rw [Pi.mul_apply, ← map_mul]
    refine ⟨_, ?_, rfl⟩
    have := mul_mem_logShell_of_norm_le_one (finPart K (c j)) (a j).2
    rw [hres] at this
    unfold scalA
    rw [hres, mul_assoc]
    exact this
  | zero => rw [mul_zero]; exact (Submodule.span ℤ_[p] _).zero_mem
  | add x y _ _ hx hy => rw [mul_add]; exact (Submodule.span ℤ_[p] _).add_mem hx hy
  | smul r x _ hx =>
    have : PiTensorProduct.tprod ℚ_[p] (fun j => factorMk p (c j) (scalA c j)) * (r • x) =
        r • (PiTensorProduct.tprod ℚ_[p] (fun j => factorMk p (c j) (scalA c j)) * x) :=
      mul_smul_comm (r : ℚ_[p]) _ x
    rw [this]
    exact (Submodule.span ℤ_[p] _).smul_mem r hx

/-- **`⊗_j 𝓘_{c j} ⊆ β · R_I`.** -/
theorem exists_mem_order_of_mem_tensorLogShell (hc : ∀ j, IsOver K p (c j))
    {x : Tensor K (.finite p) c} (hx : x ∈ tensorLogShell p c) :
    ∃ r ∈ order p c,
      x = PiTensorProduct.tprod ℚ_[p] (fun j => factorMk p (c j) (scalB c j)) * r := by
  set s := PiTensorProduct.tprod ℚ_[p] (fun j => factorMk p (c j) (scalB c j))
  let N : Submodule ℤ_[p] (Tensor K (.finite p) c) :=
    { carrier := {x | ∃ r ∈ order p c, x = s * r}
      add_mem' := by
        rintro _ _ ⟨r, hr, rfl⟩ ⟨r', hr', rfl⟩
        exact ⟨r + r', (orderSubmodule p c).add_mem hr hr', (mul_add _ _ _).symm⟩
      zero_mem' := ⟨0, (orderSubmodule p c).zero_mem, (mul_zero _).symm⟩
      smul_mem' := by
        rintro t _ ⟨r, hr, rfl⟩
        exact ⟨t • r, (orderSubmodule p c).smul_mem t hr, (mul_smul_comm (t : ℚ_[p]) s r).symm⟩ }
  have hle : tensorLogShell p c ⊆ (N : Set (Tensor K (.finite p) c)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    have hy : ∀ j, ∃ y ∈ Iut.logShell (completionAt K (finPart K (c j))) p,
        factorMk p (c j) y = b j := fun j => (b j).2
    choose y hy hyb using hy
    have hr : ∀ j, ‖y j / scalB c j‖ ≤ 1 := by
      intro j
      have hres := (hc j).residueChar_finPart
      have := hy j
      rw [← hres] at this
      exact norm_div_le_one_of_mem_logShell (finPart K (c j)) this
    refine ⟨tprodIntegral p c fun j => ⟨_, hr j⟩, tprodIntegral_mem p c _, ?_⟩
    unfold tprodIntegral
    rw [PiTensorProduct.tprod_mul_tprod]
    change (PiTensorProduct.tprod ℚ_[p] fun j => (b j : Factor K p (c j))) = _
    congr 1
    funext j
    rw [Pi.mul_apply, ← hyb j, ← map_mul, mul_div_cancel₀ _ (scalB_ne_zero c j)]
  exact hle hx

end LocalConstruct

end Iut
