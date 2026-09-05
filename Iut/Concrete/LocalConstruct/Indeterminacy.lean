/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.Integral

/-!
# The indeterminacy automorphisms of the tensor packets (taxis #4, #278)

The automorphisms `φ` of IUT IV, Proposition 1.2, through which the indeterminacies (Ind1),
(Ind2) act on a packet `⊗_j K_{c j}`, are the automorphisms `⊗_j σ_j` induced by
automorphisms `σ_j` of the factors over the base field (`mapAlgHom`); their class is
`indAut` (the field `LocalTheory.indAut`). This file proves `id_mem_indAut` and the general
transport principle `mapAlgHom_image_span_subset`: such an automorphism maps the
`ℤ_p`-span of the elementary tensors of a family of subsets of the factors into itself as
soon as each `σ_j` preserves the corresponding subset — the tool for `indAut_logShell`
(applied to the log-shells of the factors) and for the analogous statement about `R_I`
(`mapAlgHom_image_integral_subset`).
-/

namespace Iut

namespace LocalConstruct

open NumberField
open scoped TensorProduct Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]

variable (vQ : RationalPlace) (c : ι → Place K)

/-- **The automorphism `⊗_j σ_j` of the packet** induced by automorphisms `σ_j` of the
factors over the base field. -/
noncomputable def mapAlgHom
    (σ : ∀ j, Factor' K vQ (c j) ≃ₐ[baseField vQ] Factor' K vQ (c j)) :
    Tensor K vQ c →ₐ[baseField vQ] Tensor K vQ c :=
  PiTensorProduct.liftAlgHom
    ((PiTensorProduct.tprod (baseField vQ)).compLinearMap fun j => (σ j).toLinearMap)
    (by
      rw [MultilinearMap.compLinearMap_apply, PiTensorProduct.one_def]
      congr 1
      funext j
      exact map_one (σ j))
    (by
      intro x y
      simp only [MultilinearMap.compLinearMap_apply, AlgEquiv.toLinearMap_apply,
        PiTensorProduct.tprod_mul_tprod]
      congr 1
      funext i
      exact map_mul (σ i) (x i) (y i))

lemma mapAlgHom_tprod (σ : ∀ j, Factor' K vQ (c j) ≃ₐ[baseField vQ] Factor' K vQ (c j))
    (m : ∀ j, Factor' K vQ (c j)) :
    mapAlgHom vQ c σ (PiTensorProduct.tprod (baseField vQ) m) =
      PiTensorProduct.tprod (baseField vQ) fun j => σ j (m j) := by
  unfold mapAlgHom
  rw [PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply]
  rfl

/-- **The indeterminacy automorphisms** (`LocalTheory.indAut`): the maps `⊗_j σ_j` induced
by automorphisms of the factors over the base field. -/
def indAut : Set (Tensor K vQ c → Tensor K vQ c) :=
  {φ | ∃ σ : ∀ j, Factor' K vQ (c j) ≃ₐ[baseField vQ] Factor' K vQ (c j), φ = ⇑(mapAlgHom vQ c σ)}

lemma mapAlgHom_refl : mapAlgHom vQ c (fun _ => AlgEquiv.refl) = AlgHom.id _ _ := by
  classical
  refine PiTensorProduct.algHom_ext fun j => ?_
  ext a
  simp only [AlgHom.comp_apply, PiTensorProduct.singleAlgHom_apply, mapAlgHom_tprod,
    AlgHom.id_apply, AlgEquiv.coe_refl, id_eq]

/-- The identity is an indeterminacy automorphism (`LocalTheory.id_mem_indAut`). -/
lemma id_mem_indAut : id ∈ indAut vQ c :=
  ⟨fun _ => AlgEquiv.refl, by rw [mapAlgHom_refl]; rfl⟩

variable {vQ c}

/-- Indeterminacy automorphisms are ring homomorphisms. -/
lemma indAut_map_mul {φ : Tensor K vQ c → Tensor K vQ c} (hφ : φ ∈ indAut vQ c) (x y) :
    φ (x * y) = φ x * φ y := by
  obtain ⟨σ, rfl⟩ := hφ
  exact map_mul _ _ _

/-! ### Transport of elementary-tensor spans -/

section Prime

variable (p : Nat.Primes)

/-- **Transport principle**: `⊗_j σ_j` maps the `ℤ_p`-span of the elementary tensors of a
family `S_j` of subsets of the factors into itself as soon as each `σ_j` preserves `S_j`. -/
theorem mapAlgHom_image_span_subset
    (σ : ∀ j, Factor K p (c j) ≃ₐ[ℚ_[p]] Factor K p (c j))
    (S : ∀ j, Set (Factor K p (c j))) (hσ : ∀ j, σ j '' S j ⊆ S j) :
    mapAlgHom (.finite p) c σ ''
        (Submodule.span ℤ_[p] (Set.range fun a : ∀ j, S j =>
          PiTensorProduct.tprod ℚ_[p] fun j => (a j : Factor K p (c j))) :
            Set (Tensor K (.finite p) c)) ⊆
      Submodule.span ℤ_[p] (Set.range fun a : ∀ j, S j =>
          PiTensorProduct.tprod ℚ_[p] fun j => (a j : Factor K p (c j))) := by
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [mapAlgHom_tprod]
    exact Submodule.subset_span ⟨fun j => ⟨σ j (a j), hσ j ⟨_, (a j).2, rfl⟩⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx =>
    change mapAlgHom (.finite p) c σ ((r : ℚ_[p]) • x) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ r hx

/-- `⊗_j σ_j` preserves `R_I` as soon as each `σ_j` preserves the ring of integers of its
factor. -/
theorem mapAlgHom_image_integral_subset
    (σ : ∀ j, Factor K p (c j) ≃ₐ[ℚ_[p]] Factor K p (c j))
    (hσ : ∀ j (a : completionAt K (finPart K (c j))), ‖a‖ ≤ 1 →
      ∃ b : completionAt K (finPart K (c j)),
        ‖b‖ ≤ 1 ∧ σ j (factorMk p (c j) a) = factorMk p (c j) b) :
    mapAlgHom (.finite p) c σ '' integral p c ⊆ integral p c := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_integral] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    unfold tprodIntegral
    rw [mapAlgHom_tprod]
    choose b hb hb' using fun j => hσ j (a j).1 (a j).2
    have : (PiTensorProduct.tprod ℚ_[p] fun j => σ j (factorMk p (c j) (a j).1)) =
        tprodIntegral p c fun j => ⟨b j, hb j⟩ := by
      unfold tprodIntegral
      exact congrArg _ (funext fun j => hb' j)
    rw [this]
    exact tprodIntegral_mem p c _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx =>
    change mapAlgHom (.finite p) c σ ((r : ℚ_[p]) • x) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ r hx

end Prime

end LocalConstruct

end Iut
