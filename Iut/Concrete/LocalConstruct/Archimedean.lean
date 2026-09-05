/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.Packet

/-!
# The archimedean integral structure `B_I` (taxis #4, #278)

The archimedean packet `⊗_j K_{c j}` (over `ℝ`, each factor `ℝ` or `ℂ`) carries the
**projective tensor norm** `‖·‖_π` of Mathlib (`PiTensorProduct.projectiveSeminorm`): the
largest norm with `‖⊗_j a_j‖ ≤ ∏_j ‖a_j‖`; its closed unit ball is the closed absolutely
convex hull of the elementary tensors of unit vectors, the natural "product of the unit
balls" `B_I` in the tensor product presentation (IUT IV, Proposition 1.5). We take this ball
as the archimedean integral structure (`archIntegral`, the field `LocalTheory.integral` at
`∞`).

Since the packet is finite-dimensional, the projective norm is equivalent to the coordinate
sup norm `‖·‖` of `Packet.lean` (`archNorm_le`, `norm_le_archNorm`); hence `B_I` is
closed, bounded, and a neighbourhood of `0`.
-/

namespace Iut

namespace LocalConstruct

open NumberField
open scoped TensorProduct

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type} [Fintype ι] (c : ι → Place K)

/-- The archimedean factor at `v` as a normed space (the normed subfield `ℝ` or `ℂ` of `ℂ`,
lifted to the universe of `K`): definitionally `ArchFactor K v`, but carrying only the
norm structure, so that Mathlib's projective seminorm applies to the tensor product. -/
def ArchNormedFactor (v : Place K) : Type u := ULift.{u} (archField K (archPlace K v))

noncomputable instance (v : Place K) : NormedAddCommGroup (ArchNormedFactor v) :=
  inferInstanceAs (NormedAddCommGroup (ULift (archField K (archPlace K v))))

noncomputable instance (v : Place K) : NormedSpace ℝ (ArchNormedFactor v) :=
  inferInstanceAs (NormedSpace ℝ (ULift (archField K (archPlace K v))))

instance (v : Place K) : Module.Finite ℝ (ArchNormedFactor v) :=
  inferInstanceAs (Module.Finite ℝ (ULift (archField K (archPlace K v))))

noncomputable instance (v : Place K) : One (ArchNormedFactor v) :=
  inferInstanceAs (One (ULift (archField K (archPlace K v))))

/-- The archimedean packet presented over the normed factors, carrying Mathlib's projective
seminorm. This type is definitionally `Tensor K .infinite c`. -/
abbrev ArchModel : Type u := ⨂[ℝ] j, ArchNormedFactor (c j)

/-- The identity map from the packet to its normed model. -/
def toArchModel : Tensor K .infinite c → ArchModel c := id

/-- **The projective tensor norm** of the archimedean packet. -/
noncomputable def archNorm (x : Tensor K .infinite c) : ℝ := ‖toArchModel c x‖

/-- **The archimedean integral structure `B_I`**: the closed unit ball of the projective
tensor norm (`LocalTheory.integral` at `∞`). -/
def archIntegral : Set (Tensor K .infinite c) := {x | archNorm c x ≤ 1}

lemma mem_archIntegral {x : Tensor K .infinite c} : x ∈ archIntegral c ↔ archNorm c x ≤ 1 :=
  Iff.rfl

lemma archNorm_nonneg (x : Tensor K .infinite c) : 0 ≤ archNorm c x := norm_nonneg _

lemma archNorm_add_le (x y : Tensor K .infinite c) :
    archNorm c (x + y) ≤ archNorm c x + archNorm c y := norm_add_le (E := ArchModel c) _ _

lemma archNorm_smul_le (t : ℝ) (x : Tensor K .infinite c) :
    archNorm c (t • x) ≤ |t| * archNorm c x := by
  change ‖(t • toArchModel c x : ArchModel c)‖ ≤ |t| * ‖toArchModel c x‖
  rw [← Real.norm_eq_abs]
  exact norm_smul_le t (toArchModel c x)

lemma archNorm_sub_le (x y : Tensor K .infinite c) :
    |archNorm c x - archNorm c y| ≤ archNorm c (x - y) :=
  abs_norm_sub_norm_le (E := ArchModel c) _ _

lemma archNorm_tprod_le (m : ∀ j, ArchNormedFactor (c j)) :
    archNorm c (PiTensorProduct.tprod ℝ m) ≤ ∏ j, ‖m j‖ :=
  PiTensorProduct.projectiveSeminorm_tprod_le (𝕜 := ℝ) m

lemma archNorm_one : archNorm c 1 ≤ 1 := by
  have h1 : ∀ j, ‖(1 : ArchNormedFactor (c j))‖ = 1 := by
    intro j
    change ‖(1 : ULift.{u} (archField K (archPlace K (c j))))‖ = 1
    rw [ULift.norm_def, ULift.one_down]
    change ‖((1 : archField K (archPlace K (c j))) : ℂ)‖ = 1
    rw [Subalgebra.coe_one, norm_one]
  have : (1 : Tensor K .infinite c) = PiTensorProduct.tprod ℝ
      (fun j => (1 : ArchNormedFactor (c j))) := rfl
  rw [this]
  refine (archNorm_tprod_le c _).trans ?_
  simp [h1]

/-- `1 ∈ B_I` (`LocalTheory.one_mem_integral` at `∞`). -/
lemma one_mem_archIntegral : (1 : Tensor K .infinite c) ∈ archIntegral c := archNorm_one c

/-! ### Comparison with the coordinate norm -/

/-- The projective norm is bounded by a multiple of the coordinate norm. -/
lemma exists_archNorm_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Tensor K .infinite c, archNorm c x ≤ C * ‖x‖ := by
  set b := packetBasis .infinite c
  refine ⟨∑ k, archNorm c (b k), Finset.sum_nonneg fun k _ => archNorm_nonneg c _, fun x => ?_⟩
  conv_lhs => rw [← b.sum_equivFun x]
  calc archNorm c (∑ k, b.equivFun x k • b k)
      ≤ ∑ k, archNorm c (b.equivFun x k • b k) := norm_sum_le (E := ArchModel c) _ _
    _ ≤ ∑ k, ‖x‖ * archNorm c (b k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine (archNorm_smul_le c _ _).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (archNorm_nonneg c _)
        rw [← Real.norm_eq_abs, norm_def]
        exact norm_le_pi_norm _ k
    _ = (∑ k, archNorm c (b k)) * ‖x‖ := by rw [Finset.sum_mul]; simp [mul_comm]

/-- The projective norm is continuous. -/
lemma continuous_archNorm : Continuous (archNorm c) := by
  obtain ⟨C, hC0, hC⟩ := exists_archNorm_le c
  refine (LipschitzWith.of_dist_le_mul (K := ⟨C, hC0⟩) fun x y => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact (archNorm_sub_le c x y).trans (hC _)

/-- The chosen basis of a factor, as a basis of the normed model of the factor. -/
noncomputable def factorBasis (j : ι) :
    Module.Basis (Fin (Module.finrank (baseField .infinite) (Factor' K .infinite (c j)))) ℝ
      (ArchNormedFactor (c j)) :=
  (Module.finBasis (baseField .infinite) (Factor' K .infinite (c j))).map (LinearEquiv.refl ℝ _)

omit [Fintype ι] in
lemma factorBasis_apply (j : ι) (i) :
    factorBasis c j i = Module.finBasis (baseField .infinite) (Factor' K .infinite (c j)) i := rfl

/-- The coordinate functional of the basis of elementary tensors, as a continuous multilinear
functional on the factors: `a ↦ ∏_j (coordinate `k j` of `a j`)`. -/
noncomputable def coordMultilinear (k : PacketIndex .infinite c) :
    ContinuousMultilinearMap ℝ (fun j => ArchNormedFactor (c j)) ℝ where
  toMultilinearMap := (MultilinearMap.mkPiAlgebra ℝ ι ℝ).compLinearMap fun j =>
    (factorBasis c j).coord (k j)
  cont := by
    have : ⇑((MultilinearMap.mkPiAlgebra ℝ ι ℝ).compLinearMap fun j =>
        (factorBasis c j).coord (k j)) =
        fun m => ∏ j, (factorBasis c j).coord (k j) (m j) := by
      funext m
      rw [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
    change Continuous ⇑((MultilinearMap.mkPiAlgebra ℝ ι ℝ).compLinearMap fun j =>
      (factorBasis c j).coord (k j))
    rw [this]
    refine continuous_finsetProd _ fun j _ => ?_
    exact ((factorBasis c j).coord (k j)).continuous_of_finiteDimensional.comp (continuous_apply j)

lemma coordMultilinear_apply (k : PacketIndex .infinite c)
    (m : ∀ j, ArchNormedFactor (c j)) :
    (coordMultilinear c k).toMultilinearMap m = ∏ j, (factorBasis c j).coord (k j) (m j) := by
  change ((MultilinearMap.mkPiAlgebra ℝ ι ℝ).compLinearMap _) m = _
  rw [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-- The lift of `coordMultilinear k` to the packet, as a linear functional on the packet. -/
noncomputable def coordLift (k : PacketIndex .infinite c) : Tensor K .infinite c →ₗ[ℝ] ℝ :=
  PiTensorProduct.lift (coordMultilinear c k).toMultilinearMap

lemma coordLift_apply (k : PacketIndex .infinite c) (x : Tensor K .infinite c) :
    coordLift c k x =
      PiTensorProduct.lift (coordMultilinear c k).toMultilinearMap (toArchModel c x) :=
  rfl

/-- The lift of `coordMultilinear k` to the packet is the `k`-th coordinate functional. -/
lemma coordLift_eq_coord (k : PacketIndex .infinite c) :
    coordLift c k = (packetBasis .infinite c).coord k := by
  classical
  refine (packetBasis .infinite c).ext fun l => ?_
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, coordLift_apply]
  have hbl : toArchModel c (packetBasis .infinite c l) =
      PiTensorProduct.tprod ℝ fun j => factorBasis c j (l j) :=
    Basis.piTensorProduct_apply _ l
  rw [hbl, PiTensorProduct.lift.tprod, coordMultilinear_apply]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hl : l = k
  · subst hl
    simp
  · rw [if_neg hl]
    obtain ⟨j, hj⟩ : ∃ j, l j ≠ k j := by
      by_contra h
      push Not at h
      exact hl (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg hj])

lemma lift_coordMultilinear (k : PacketIndex .infinite c) (x : Tensor K .infinite c) :
    PiTensorProduct.lift (coordMultilinear c k).toMultilinearMap (toArchModel c x) =
      (packetBasis .infinite c).equivFun x k := by
  rw [← coordLift_apply, coordLift_eq_coord, Module.Basis.coord_apply, Module.Basis.equivFun_apply]

/-- The coordinate norm is bounded by a multiple of the projective norm. -/
lemma exists_norm_le_archNorm :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Tensor K .infinite c, ‖x‖ ≤ C * archNorm c x := by
  refine ⟨∑ k, ‖coordMultilinear c k‖, Finset.sum_nonneg fun k _ => norm_nonneg _, fun x => ?_⟩
  rw [norm_def, pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)
    (archNorm_nonneg c x))]
  intro k
  rw [← lift_coordMultilinear]
  calc ‖PiTensorProduct.lift (coordMultilinear c k).toMultilinearMap (toArchModel c x)‖
      ≤ ‖coordMultilinear c k‖ * ‖toArchModel c x‖ :=
        PiTensorProduct.norm_eval_le_projectiveSeminorm _ _
    _ ≤ (∑ k, ‖coordMultilinear c k‖) * archNorm c x :=
        mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun k _ => norm_nonneg (coordMultilinear c k)) (Finset.mem_univ k))
          (archNorm_nonneg c x)

/-! ### Properties of `B_I` -/

/-- **`B_I` is closed.** -/
lemma isClosed_archIntegral : IsClosed (archIntegral c) :=
  isClosed_le (continuous_archNorm c) continuous_const

/-- **`B_I` is bounded.** -/
lemma exists_archIntegral_subset_closedBall :
    ∃ M : ℝ, archIntegral c ⊆ Metric.closedBall 0 M := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_archNorm c
  refine ⟨C, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (hC x).trans (mul_le_of_le_one_right hC0 hx)

lemma isBounded_archIntegral : Bornology.IsBounded (archIntegral c) := by
  obtain ⟨M, hM⟩ := exists_archIntegral_subset_closedBall c
  exact (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨M, hM⟩

/-- **`B_I` is compact.** -/
lemma isCompact_archIntegral : IsCompact (archIntegral c) :=
  (isClosed_archIntegral c).closure_eq ▸ (isBounded_archIntegral c).isCompact_closure

/-- **`B_I` is a neighbourhood of `0`.** -/
lemma exists_ball_subset_archIntegral :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : Tensor K .infinite c) r ⊆ archIntegral c := by
  obtain ⟨C, hC0, hC⟩ := exists_archNorm_le c
  refine ⟨1 / (C + 1), by positivity, fun x hx => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hx
  rw [mem_archIntegral]
  calc archNorm c x ≤ C * ‖x‖ := hC x
    _ ≤ C * (1 / (C + 1)) := mul_le_mul_of_nonneg_left hx.le hC0
    _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        linarith

lemma archIntegral_nonempty : (archIntegral c).Nonempty := ⟨1, one_mem_archIntegral c⟩

end LocalConstruct

end Iut
