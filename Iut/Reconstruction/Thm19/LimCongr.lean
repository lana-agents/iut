/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Colimit.DirectLimit
import ContinuousKummerTheory.ContH1.Basic

/-!
# Isomorphisms of direct limits of groups from compatible cocones

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178) works in
`lim→_V H¹(Π_V, μ_Ẑ(Π_U))`, `V` ranging over the stages. Its functoriality in `Π_U ≃ Π_{U'}`
compares two such colimits over *different* index sets (the stages of `U` and of `U'`), the
stagewise isomorphisms coming from Belyi cuspidalization. The generic tool is here: two families
of homomorphisms `φ_i : F i → lim→ G`, `ψ_j : G j → lim→ F`, each compatible with the transition
maps, which are mutually inverse on generators, give `lim→ F ≃* lim→ G`
(`mulEquivOfCocones`), with `mulEquivOfCocones_mk`.

The stagewise isomorphisms are only determined up to inner automorphisms ([AbsTopII] Cor 3.8,
uniqueness: lifts differ by conjugation by an element of the kernel of the filling), which act
trivially on `H¹`: **`ContH1.map_conj_eq_self`** (`h ↦ a⁻¹ · c(a h a⁻¹)` is cohomologous to `c`).
-/

noncomputable section

namespace Iut.Reconstruction.Thm19

variable {ι κ : Type*} [Preorder ι] [Preorder κ] [IsDirectedOrder ι] [IsDirectedOrder κ]
  [Nonempty ι] [Nonempty κ]
  {F : ι → Type*} [∀ i, Group (F i)] (f : ∀ i j, i ≤ j → F i →* F j)
  [DirectedSystem F (fun i j h ↦ f i j h)]
  {G : κ → Type*} [∀ j, Group (G j)] (g : ∀ i j, i ≤ j → G i →* G j)
  [DirectedSystem G (fun i j h ↦ g i j h)]

/-- The homomorphism `lim→ F → C` induced by a compatible family `φ_i : F i →* C`. -/
def limLift {C : Type*} [Group C] (φ : ∀ i, F i →* C)
    (hφ : ∀ i j (h : i ≤ j) x, φ i x = φ j (f i j h x)) :
    DirectLimit F (fun i j h ↦ f i j h) →* C where
  toFun := DirectLimit.lift _ (fun i x ↦ φ i x) hφ
  map_one' := by
    rw [DirectLimit.one_def (Classical.arbitrary ι)]
    exact map_one (φ _)
  map_mul' x y := DirectLimit.induction₂ _ (fun i x y ↦ by
    rw [DirectLimit.mul_def]
    exact map_mul (φ i) x y) x y

@[simp] lemma limLift_mk {C : Type*} [Group C] (φ : ∀ i, F i →* C)
    (hφ : ∀ i j (h : i ≤ j) x, φ i x = φ j (f i j h x)) (i : ι) (x : F i) :
    limLift f φ hφ ⟦⟨i, x⟩⟧ = φ i x := rfl

/-- **`lim→ F ≃* lim→ G` from mutually inverse compatible cocones.** -/
def mulEquivOfCocones
    (φ : ∀ i, F i →* DirectLimit G (fun i j h ↦ g i j h))
    (hφ : ∀ i j (h : i ≤ j) x, φ i x = φ j (f i j h x))
    (ψ : ∀ j, G j →* DirectLimit F (fun i j h ↦ f i j h))
    (hψ : ∀ i j (h : i ≤ j) x, ψ i x = ψ j (g i j h x))
    (hψφ : ∀ i x, limLift g ψ hψ (φ i x) = ⟦⟨i, x⟩⟧)
    (hφψ : ∀ j y, limLift f φ hφ (ψ j y) = ⟦⟨j, y⟩⟧) :
    DirectLimit F (fun i j h ↦ f i j h) ≃* DirectLimit G (fun i j h ↦ g i j h) where
  toFun := limLift f φ hφ
  invFun := limLift g ψ hψ
  left_inv z := by
    induction z using DirectLimit.induction with
    | ih i x => exact hψφ i x
  right_inv z := by
    induction z using DirectLimit.induction with
    | ih j y => exact hφψ j y
  map_mul' := map_mul _

@[simp] lemma mulEquivOfCocones_mk
    (φ : ∀ i, F i →* DirectLimit G (fun i j h ↦ g i j h))
    (hφ : ∀ i j (h : i ≤ j) x, φ i x = φ j (f i j h x))
    (ψ : ∀ j, G j →* DirectLimit F (fun i j h ↦ f i j h))
    (hψ : ∀ i j (h : i ≤ j) x, ψ i x = ψ j (g i j h x)) (hψφ hφψ) (i : ι) (x : F i) :
    mulEquivOfCocones f g φ hφ ψ hψ hψφ hφψ ⟦⟨i, x⟩⟧ = φ i x := rfl

section Inner

open groupCohomology

variable {P M : Type*} [Group P] [TopologicalSpace P] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction P M]

/-- **Inner automorphisms act trivially on `H¹`**: for `a ∈ P`, the map induced by `h ↦ a h a⁻¹`
and `m ↦ a⁻¹ • m` is the identity of `H¹(P, M)` (the cocycle `h ↦ a⁻¹ • c(a h a⁻¹)` differs
from `c` by the coboundary of `(a⁻¹ • c(a))⁻¹`). -/
theorem ContH1.map_conj_eq_self (a : P) (hφ : Continuous (MulAut.conj a).toMonoidHom)
    (hf : Continuous (MulDistribMulAction.toMonoidHom M a⁻¹))
    (hcomp : ∀ h m, MulDistribMulAction.toMonoidHom M a⁻¹ ((MulAut.conj a).toMonoidHom h • m) =
      h • MulDistribMulAction.toMonoidHom M a⁻¹ m) (x : ContH1 P M) :
    ContH1.map (MulAut.conj a).toMonoidHom hφ (MulDistribMulAction.toMonoidHom M a⁻¹) hf hcomp x =
      x := by
  induction x using ContH1.induction_on with
  | h c =>
    rw [ContH1.map_mk, ContH1.mk_eq_mk_iff]
    have hc := ContH1.isMulCocycle₁ c
    refine ⟨(a⁻¹ • c a)⁻¹, fun h ↦ ?_⟩
    simp only [ContH1.cocyclesMap_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MulDistribMulAction.toMonoidHom_apply]
    have h1 : (c : P → M) (a * h * a⁻¹) =
        (a * h) • (c : P → M) a⁻¹ * (a • (c : P → M) h * c a) := by
      rw [hc, hc]
    have h2 : (c : P → M) a⁻¹ = (a⁻¹ • (c : P → M) a)⁻¹ := by
      rw [← smul_inv', ← map_inv_of_isMulCocycle₁ hc a, smul_smul, inv_mul_cancel, one_smul]
    rw [h1, smul_mul', smul_mul', smul_smul, smul_smul, inv_mul_cancel_left, inv_mul_cancel,
      one_smul, h2, div_inv_eq_mul, ← mul_assoc, mul_right_comm _ ((c : P → M) h),
      mul_div_cancel_right]

end Inner

end Iut.Reconstruction.Thm19
