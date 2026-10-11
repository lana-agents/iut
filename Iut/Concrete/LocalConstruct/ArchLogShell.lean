/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.ThetaAdmissible

/-!
# The archimedean log-shell and IUT IV, Proposition 1.5 (taxis #4, #278)

At the archimedean place the log-shell of a factor `ℝ` or `ℂ` is the closed disc of radius
`π` (the image of the units under the logarithm; IUT III, Proposition 1.2(vii)). Following
IUT III, Proposition 3.2(ii) (pp. 98–99), this disc is regarded as the closed unit ball of a
Hermitian metric on the factor (the standard metric `|·|`, rescaled by `π`), the packet
`⊗_j K_{c j}` (tensor product over `ℝ`) is equipped with the **induced tensor-product
Hermitian metric**, and the log-shell of the packet is the **closed unit ball** of that
metric (`archLogShell`, `Iut.LocalTheory.logShell` at `∞`).

Concretely, each factor carries the real inner product `⟨a, b⟩ = Re(a·conj b)` of `ℂ`
(`archInner`, whose norm is the absolute value `archAbs`), and the packet carries the tensor
product of these inner products, the symmetric bilinear form with
`⟨⊗_j a_j, ⊗_j b_j⟩_T = ∏_j ⟨a_j, b_j⟩` (`archTensorInner`, `archTensorInner_tprod`). Rescaling
each factor metric by `π` rescales the tensor-product metric by `π^{|I|}`, so

`archLogShell = {x | ⟨x, x⟩_T ≤ (π^{|I|})²}`,

the closed ball of radius `π^{|I|}` for the tensor-product metric. The tensor product of
orthonormal bases of the factors (`archFactorBasis`) is an orthonormal basis of the packet
(`archTensorBasis`, `archTensorInner_basis`), so `⟨x, x⟩_T` is the sum of the squares of the
coordinates of `x` (`archTensorInner_self`) and the log-shell is a Euclidean ball in these
coordinates (`archLogShell_eq_preimage`): it is closed, absolutely convex, compact and of
positive Haar measure (`isClosed_archLogShell`, `absConvex_archLogShell`,
`isCompact_archLogShell`, `haar_archLogShell_pos`). The elementary tensors `⊗_j y_j` of
log-shell elements `|y_j| ≤ π` lie in it, with `‖⊗_j y_j‖_T = ∏_j |y_j|`
(`archTensorInner_self_tprod`, `archLogShellSet_subset_archLogShell`); hence so does the closed
absolutely convex hull of these elementary tensors
(`closure_absConvexHull_archLogShellSet_subset`).

**IUT IV, Proposition 1.5** (`archLogShell_subset`): every component `χ_𝔪(x)` of `x` in the
direct sum decomposition of the packet satisfies `|χ_𝔪(x)| ≤ ∑_b |x_b| ≤ √N·‖x‖_T`, where the
`x_b` are the coordinates in the product orthonormal basis, `N ≤ 2^{|I|}` is its cardinality,
and `|χ_𝔪(b)| = 1` for every basis element `b` (`norm_archChar_basis`, `norm_archChar_sq_le`).
Hence `archLogShell ⊆ (√2·π)^{|I|}·B_I` (`archHullRadius`). This is the comparison between the
tensor-product metric and the direct-sum metric of IUT IV, Proposition 1.5(i),(iii) (which
differ by a factor depending only on `|I|`, governed by `2^{|I|−1}` there); only an upper bound
is needed, since the proof of Theorem 1.10 only uses an upper bound on the holomorphic hull.
The elementary tensors themselves lie in the smaller polydisc `π^{|I|}·B_I`
(`archLogShellSet_subset`; IUT IV, Proposition 1.5(iv)).

The Galois automorphisms `⊗_j σ_j` of the packet preserve `B_I` and its real multiples
(`mapAlgHom_image_archIntegral_subset`, `galAut_image_smul_archIntegral_subset`): they permute
the components up to absolute value (`norm_archChar_algHom`).
-/

namespace Iut

namespace LocalConstruct

open NumberField MeasureTheory
open scoped TensorProduct Pointwise InnerProductSpace

universe u

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι] (c : ι → Place K)

/-! ### The Galois automorphisms of the packet preserve `B_I` -/

/-- **IUT IV, Proposition 1.5(iii)**: the Galois automorphisms of the packet preserve `B_I`. -/
theorem mapAlgHom_image_archIntegral_subset
    (σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j)) :
    mapAlgHom .infinite c σ '' archIntegral c ⊆ archIntegral c := by
  rintro _ ⟨x, hx, rfl⟩ m
  rw [norm_archChar_algHom]
  exact hx _

/-- The Galois automorphisms of the packet preserve every real multiple of `B_I`. -/
theorem galAut_image_smul_archIntegral_subset (t : ℝ) :
    ∀ φ ∈ galAut .infinite c, φ '' (algebraMap ℝ (Tensor K .infinite c) t • archIntegral c) ⊆
      algebraMap ℝ (Tensor K .infinite c) t • archIntegral c := by
  rintro _ ⟨σ, rfl⟩ _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨mapAlgHom .infinite c σ x, mapAlgHom_image_archIntegral_subset c σ ⟨x, hx, rfl⟩, ?_⟩
  change algebraMap ℝ _ t * mapAlgHom .infinite c σ x =
    mapAlgHom .infinite c σ (algebraMap ℝ _ t * x)
  rw [map_mul, AlgHom.commutes]

/-! ### The real multiples of `B_I` are absolutely convex -/

/-- For `t > 0`, the polydisc `t·B_I` is absolutely convex. -/
theorem absConvex_algebraMap_smul_archIntegral {t : ℝ} (ht : 0 < t) :
    AbsConvex ℝ (algebraMap ℝ (Tensor K .infinite c) t • archIntegral c) := by
  refine ⟨fun a ha => ?_, fun x hx y hy a b ha hb hab => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_algebraMap_smul_archIntegral ht] at hx ⊢
    intro m
    rw [map_smul, norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (hx m)
  · rw [mem_algebraMap_smul_archIntegral ht] at hx hy ⊢
    intro m
    rw [map_add, map_smul, map_smul]
    calc ‖a • archChar c m x + b • archChar c m y‖
        ≤ ‖a • archChar c m x‖ + ‖b • archChar c m y‖ := norm_add_le _ _
      _ = a * ‖archChar c m x‖ + b * ‖archChar c m y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * t + b * t := add_le_add (mul_le_mul_of_nonneg_left (hx m) ha)
          (mul_le_mul_of_nonneg_left (hy m) hb)
      _ = t := by rw [← add_mul, hab, one_mul]

/-! ### The archimedean log-shell -/

/-- **The tensor products of elements of the log-shells** `⊗_j y_j` with `|y_j| ≤ π`
(IUT III, Proposition 3.2(ii); IUT IV, Proposition 1.5(iv)). -/
def archLogShellSet : Set (Tensor K .infinite c) :=
  {x | ∃ y : ∀ j, ArchFactor K (c j), (∀ j, archAbs (c j) (y j) ≤ Real.pi) ∧
    PiTensorProduct.tprod ℝ y = x}

lemma one_mem_archLogShellSet : (1 : Tensor K .infinite c) ∈ archLogShellSet c :=
  ⟨1, fun j => by rw [Pi.one_apply, archAbs_one]; linarith [Real.pi_gt_three], rfl⟩

/-- **IUT IV, Proposition 1.5(iv)**: the tensor products of elements of the log-shells lie in
`π^{|I|}·B_I`. -/
theorem archLogShellSet_subset :
    archLogShellSet c ⊆
      algebraMap ℝ (Tensor K .infinite c) (Real.pi ^ Fintype.card ι) • archIntegral c := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_algebraMap_smul_archIntegral (pow_pos Real.pi_pos _)]
  intro m
  rw [norm_archChar_tprod, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun j _ => archAbs_nonneg _ _) fun j _ => hy j

/-! ### The Hermitian metrics of the factors -/

section Factor

variable (v : Place K)

/-- An archimedean factor as a real subspace (`ℝ` or `ℂ`) of the real inner product space
`ℂ`. -/
noncomputable abbrev archFactorSub : Submodule ℝ ℂ :=
  Subalgebra.toSubmodule (archField K (archPlace K v))

/-- The identification of an archimedean factor with the real subspace `ℝ` or `ℂ` of `ℂ`. -/
noncomputable def archFactorLin : ArchFactor K v ≃ₗ[ℝ] archFactorSub v :=
  (archFactorEquiv v).toLinearEquiv.trans (Subalgebra.toSubmoduleEquiv _).symm

lemma norm_archFactorLin (a : ArchFactor K v) : ‖archFactorLin v a‖ = archAbs v a := rfl

/-- **The Hermitian metric of a factor** (as a real inner product): `⟨a, b⟩ = Re(a·conj b)`,
whose norm is the absolute value of the factor (`archInner_self`). The log-shell of the
factor, the closed disc of radius `π` (IUT III, Proposition 1.2(vii)), is the closed unit ball
of the rescaled metric `π⁻²·⟨·, ·⟩`. -/
noncomputable def archInner : ArchFactor K v →ₗ[ℝ] ArchFactor K v →ₗ[ℝ] ℝ :=
  (innerₗ (archFactorSub v)).compl₁₂ (archFactorLin v).toLinearMap (archFactorLin v).toLinearMap

lemma archInner_apply (a b : ArchFactor K v) :
    archInner v a b = ⟪archFactorLin v a, archFactorLin v b⟫_ℝ := rfl

lemma archInner_self (a : ArchFactor K v) : archInner v a a = archAbs v a ^ 2 := by
  rw [archInner_apply, real_inner_self_eq_norm_sq, norm_archFactorLin]

/-- The inner product of a factor is determined by its absolute value (polarization). -/
lemma archInner_eq_polarization (a b : ArchFactor K v) :
    archInner v a b = (archAbs v (a + b) * archAbs v (a + b) - archAbs v a * archAbs v a -
      archAbs v b * archAbs v b) / 2 := by
  rw [archInner_apply,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add,
    norm_archFactorLin, norm_archFactorLin, norm_archFactorLin]

/-- A chosen orthonormal basis of the factor as a subspace of `ℂ` (any orthonormal basis
induces the same tensor-product metric). -/
noncomputable def archFactorONB :
    OrthonormalBasis (Fin (Module.finrank ℝ (archFactorSub v))) ℝ (archFactorSub v) :=
  stdOrthonormalBasis ℝ _

/-- **An orthonormal basis of a factor** (for `archInner`). -/
noncomputable def archFactorBasis :
    Module.Basis (Fin (Module.finrank ℝ (archFactorSub v))) ℝ (ArchFactor K v) :=
  (archFactorONB v).toBasis.map (archFactorLin v).symm

lemma archFactorLin_basis (k : Fin (Module.finrank ℝ (archFactorSub v))) :
    archFactorLin v (archFactorBasis v k) = archFactorONB v k := by
  simp [archFactorBasis]

lemma archInner_basis (k l : Fin (Module.finrank ℝ (archFactorSub v))) :
    archInner v (archFactorBasis v k) (archFactorBasis v l) = if k = l then 1 else 0 := by
  rw [archInner_apply, archFactorLin_basis, archFactorLin_basis]
  exact orthonormal_iff_ite.mp (archFactorONB v).orthonormal k l

lemma archAbs_basis (k : Fin (Module.finrank ℝ (archFactorSub v))) :
    archAbs v (archFactorBasis v k) = 1 := by
  rw [← norm_archFactorLin, archFactorLin_basis]
  exact (archFactorONB v).orthonormal.1 k

/-- A factor has real dimension at most `2`. -/
lemma finrank_archFactorSub_le : Module.finrank ℝ (archFactorSub v) ≤ 2 :=
  (Submodule.finrank_le _).trans Complex.finrank_real_complex.le

end Factor

/-! ### The tensor-product Hermitian metric of the packet -/

/-- **The tensor-product Hermitian metric** of the archimedean packet (IUT III,
Proposition 3.2(ii)), as a real bilinear form: the tensor product of the metrics of the
factors, `⟨⊗_j a_j, ⊗_j b_j⟩_T = ∏_j ⟨a_j, b_j⟩` (`archTensorInner_tprod`). -/
noncomputable def archTensorInner :
    Tensor K .infinite c →ₗ[ℝ] Tensor K .infinite c →ₗ[ℝ] ℝ :=
  (PiTensorProduct.dualDistrib (R := ℝ) (M := fun j => ArchFactor K (c j))).comp
    (PiTensorProduct.map fun j => archInner (c j))

lemma archTensorInner_tprod (a b : ∀ j, ArchFactor K (c j)) :
    archTensorInner c (PiTensorProduct.tprod ℝ a) (PiTensorProduct.tprod ℝ b) =
      ∏ j, archInner (c j) (a j) (b j) := by
  simp [archTensorInner, PiTensorProduct.map_tprod, PiTensorProduct.dualDistrib_apply]

/-- `‖⊗_j y_j‖_T² = ∏_j |y_j|²`. -/
lemma archTensorInner_self_tprod (y : ∀ j, ArchFactor K (c j)) :
    archTensorInner c (PiTensorProduct.tprod ℝ y) (PiTensorProduct.tprod ℝ y) =
      (∏ j, archAbs (c j) (y j)) ^ 2 := by
  rw [archTensorInner_tprod, ← Finset.prod_pow]
  simp_rw [archInner_self]

/-- The index type of the product basis. -/
abbrev ArchTensorIdx : Type := ∀ j, Fin (Module.finrank ℝ (archFactorSub (c j)))

noncomputable instance : Fintype (ArchTensorIdx c) := Fintype.ofFinite _

/-- **The product of the orthonormal bases of the factors**, a basis of the packet. -/
noncomputable def archTensorBasis : Module.Basis (ArchTensorIdx c) ℝ (Tensor K .infinite c) :=
  Basis.piTensorProduct fun j => archFactorBasis (c j)

/-- **The product basis is orthonormal** for the tensor-product metric. -/
lemma archTensorInner_basis (p q : ArchTensorIdx c) :
    archTensorInner c (archTensorBasis c p) (archTensorBasis c q) = if p = q then 1 else 0 := by
  rw [archTensorBasis, Basis.piTensorProduct_apply, Basis.piTensorProduct_apply,
    archTensorInner_tprod]
  simp_rw [archInner_basis]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

/-- `‖x‖_T²` is the sum of the squares of the coordinates of `x` in the product basis. -/
lemma archTensorInner_self (x : Tensor K .infinite c) :
    archTensorInner c x x = ∑ p, (archTensorBasis c).repr x p ^ 2 := by
  conv_lhs => rw [← (archTensorBasis c).sum_repr x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single p (fun q _ hq => by rw [archTensorInner_basis, if_neg hq, mul_zero])
    (by simp), archTensorInner_basis, if_pos rfl]
  ring

/-- The coordinates in the product basis, as a point of a Euclidean space. -/
noncomputable def archTensorCoord :
    Tensor K .infinite c →ₗ[ℝ] EuclideanSpace ℝ (ArchTensorIdx c) :=
  (WithLp.linearEquiv 2 ℝ (ArchTensorIdx c → ℝ)).symm.toLinearMap ∘ₗ
    (archTensorBasis c).equivFun.toLinearMap

/-- The coordinates are an isometry from the tensor-product metric to the Euclidean metric. -/
lemma norm_archTensorCoord_sq (x : Tensor K .infinite c) :
    ‖archTensorCoord c x‖ ^ 2 = archTensorInner c x x := by
  rw [EuclideanSpace.norm_sq_eq, archTensorInner_self]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [archTensorCoord]

lemma archTensorInner_self_nonneg (x : Tensor K .infinite c) : 0 ≤ archTensorInner c x x := by
  rw [← norm_archTensorCoord_sq]
  positivity

lemma continuous_archTensorCoord : Continuous (archTensorCoord c) :=
  LinearMap.continuous_of_finiteDimensional _

/-! ### The archimedean log-shell -/

/-- **The archimedean log-shell** of the packet (`LocalTheory.logShell` at `∞`;
IUT III, Proposition 3.2(ii), pp. 98–99): the closed unit ball of the tensor-product Hermitian
metric for which the log-shell of each factor (the closed disc of radius `π`) is the closed
unit ball, i.e. the closed ball of radius `π^{|I|}` for `archTensorInner`. Since the product
of orthonormal bases of the factors is orthonormal for the tensor-product metric
(`archTensorInner_basis`), this is the Euclidean ball of radius `π^{|I|}` in the coordinates
of the product basis (`archLogShell_eq_preimage`). -/
def archLogShell : Set (Tensor K .infinite c) :=
  {x | archTensorInner c x x ≤ (Real.pi ^ Fintype.card ι) ^ 2}

lemma mem_archLogShell {x : Tensor K .infinite c} :
    x ∈ archLogShell c ↔ archTensorInner c x x ≤ (Real.pi ^ Fintype.card ι) ^ 2 :=
  Iff.rfl

lemma archLogShell_eq_preimage :
    archLogShell c = archTensorCoord c ⁻¹' Metric.closedBall 0 (Real.pi ^ Fintype.card ι) := by
  ext x
  rw [Set.mem_preimage, mem_closedBall_zero_iff, mem_archLogShell, ← norm_archTensorCoord_sq,
    pow_le_pow_iff_left₀ (norm_nonneg _) (pow_pos Real.pi_pos _).le two_ne_zero]

/-- The archimedean log-shell is closed. -/
lemma isClosed_archLogShell : IsClosed (archLogShell c) := by
  rw [archLogShell_eq_preimage]
  exact Metric.isClosed_closedBall.preimage (continuous_archTensorCoord c)

/-- The archimedean log-shell is absolutely convex. -/
lemma absConvex_archLogShell : AbsConvex ℝ (archLogShell c) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_archLogShell] at hx ⊢
    change archTensorInner c (a • x) (a • x) ≤ _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc]
    have ha2 : a * a ≤ 1 := by
      rw [Real.norm_eq_abs] at ha
      nlinarith [abs_mul_abs_self a, abs_nonneg a]
    exact (mul_le_of_le_one_left (archTensorInner_self_nonneg c x) ha2).trans hx
  · rw [archLogShell_eq_preimage]
    exact (convex_closedBall _ _).linear_preimage _

/-- **The elementary tensors of log-shell elements lie in the archimedean log-shell**:
`‖⊗_j y_j‖_T = ∏_j |y_j| ≤ π^{|I|}`. -/
lemma archLogShellSet_subset_archLogShell : archLogShellSet c ⊆ archLogShell c := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_archLogShell, archTensorInner_self_tprod, ← Finset.card_univ, ← Finset.prod_const]
  exact pow_le_pow_left₀ (Finset.prod_nonneg fun j _ => archAbs_nonneg _ _)
    (Finset.prod_le_prod (fun j _ => archAbs_nonneg _ _) fun j _ => hy j) 2

/-- The closed absolutely convex hull of the elementary tensors of log-shell elements lies in
the archimedean log-shell. -/
theorem closure_absConvexHull_archLogShellSet_subset :
    closure (absConvexHull ℝ (archLogShellSet c)) ⊆ archLogShell c :=
  closure_minimal (absConvexHull_min (archLogShellSet_subset_archLogShell c)
    (absConvex_archLogShell c)) (isClosed_archLogShell c)

/-! ### IUT IV, Proposition 1.5: the hull bound -/

/-- Every component of an element of the product basis has absolute value `1`. -/
lemma norm_archChar_basis (m : MaximalSpectrum (Tensor K .infinite c)) (p : ArchTensorIdx c) :
    ‖archChar c m (archTensorBasis c p)‖ = 1 := by
  rw [archTensorBasis, Basis.piTensorProduct_apply, norm_archChar_tprod]
  exact Finset.prod_eq_one fun j _ => archAbs_basis _ _

/-- The product basis has at most `2^{|I|}` elements. -/
lemma card_archTensorIdx : Fintype.card (ArchTensorIdx c) ≤ 2 ^ Fintype.card ι := by
  classical
  rw [Fintype.card_eq_nat_card, Nat.card_pi, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod' fun j _ => by
    simpa [Nat.card_eq_fintype_card] using finrank_archFactorSub_le (c j)

/-- **Comparison of the tensor-product and direct-sum metrics** (IUT IV, Proposition
1.5(i),(iii)): every component satisfies `|χ_𝔪(x)| ≤ ∑_b |x_b|`, hence
`|χ_𝔪(x)|² ≤ N·‖x‖_T² ≤ 2^{|I|}·‖x‖_T²` (Cauchy–Schwarz). -/
theorem norm_archChar_sq_le (m : MaximalSpectrum (Tensor K .infinite c))
    (x : Tensor K .infinite c) :
    ‖archChar c m x‖ ^ 2 ≤ 2 ^ Fintype.card ι * archTensorInner c x x := by
  have h1 : ‖archChar c m x‖ ≤ ∑ p, |(archTensorBasis c).repr x p| := by
    conv_lhs => rw [← (archTensorBasis c).sum_repr x]
    rw [map_sum]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
    rw [map_smul, norm_smul, norm_archChar_basis, mul_one, Real.norm_eq_abs]
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun p => |(archTensorBasis c).repr x p|)
  simp only [sq_abs, Finset.card_univ] at h2
  rw [archTensorInner_self]
  calc ‖archChar c m x‖ ^ 2 ≤ (∑ p, |(archTensorBasis c).repr x p|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_archTensorIdx c)
        (Finset.sum_nonneg fun p _ => sq_nonneg _)

/-- The radius `√2·π` of the archimedean hull bound: the log-shell lies in
`(√2·π)^{|I|}·B_I` (`archLogShell_subset`). -/
noncomputable def archHullRadius : ℝ := Real.sqrt 2 * Real.pi

lemma archHullRadius_pos : 0 < archHullRadius := mul_pos (by positivity) Real.pi_pos

lemma isUnit_archScalar :
    IsUnit (algebraMap ℝ (Tensor K .infinite c) (archHullRadius ^ Fintype.card ι)) :=
  (isUnit_iff_ne_zero.mpr (pow_ne_zero _ archHullRadius_pos.ne')).map (algebraMap ℝ _)

/-- **IUT IV, Proposition 1.5** for the archimedean log-shell: it lies in
`(√2·π)^{|I|}·B_I` (`norm_archChar_sq_le`). -/
theorem archLogShell_subset :
    archLogShell c ⊆
      algebraMap ℝ (Tensor K .infinite c) (archHullRadius ^ Fintype.card ι) • archIntegral c := by
  intro x hx
  rw [mem_algebraMap_smul_archIntegral (pow_pos archHullRadius_pos _)]
  intro m
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (pow_pos archHullRadius_pos _).le two_ne_zero]
  refine (norm_archChar_sq_le c m x).trans ?_
  calc (2 : ℝ) ^ Fintype.card ι * archTensorInner c x x
      ≤ 2 ^ Fintype.card ι * (Real.pi ^ Fintype.card ι) ^ 2 :=
        mul_le_mul_of_nonneg_left hx (by positivity)
    _ = (archHullRadius ^ Fintype.card ι) ^ 2 := by
        rw [archHullRadius, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
          mul_comm (Fintype.card ι) 2, pow_mul, pow_mul, Real.sq_sqrt zero_le_two]

/-- The archimedean log-shell is compact. -/
lemma isCompact_archLogShell : IsCompact (archLogShell c) :=
  (isCompact_smul _ (isCompact_archIntegral c)).of_isClosed_subset (isClosed_archLogShell c)
    (archLogShell_subset c)

/-- The archimedean log-shell is relatively compact (`LocalTheory.logShell_relCompact` at `∞`). -/
lemma isCompact_closure_archLogShell : IsCompact (closure (archLogShell c)) := by
  rw [(isClosed_archLogShell c).closure_eq]
  exact isCompact_archLogShell c

/-- **The archimedean log-shell has positive Haar measure**: it contains the open ball of
radius `π^{|I|}`. -/
theorem haar_archLogShell_pos : 0 < haar .infinite c (archLogShell c) := by
  have hopen : IsOpen (archTensorCoord c ⁻¹' Metric.ball 0 (Real.pi ^ Fintype.card ι)) :=
    Metric.isOpen_ball.preimage (continuous_archTensorCoord c)
  have h0 : (0 : Tensor K .infinite c) ∈
      archTensorCoord c ⁻¹' Metric.ball 0 (Real.pi ^ Fintype.card ι) := by
    rw [Set.mem_preimage, map_zero]
    exact Metric.mem_ball_self (pow_pos Real.pi_pos _)
  refine lt_of_lt_of_le (hopen.measure_pos (haar .infinite c) ⟨0, h0⟩) (measure_mono ?_)
  rw [archLogShell_eq_preimage]
  exact Set.preimage_mono Metric.ball_subset_closedBall

end LocalConstruct

end Iut
