/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.ArchLogShell

/-!
# The archimedean indeterminacy automorphisms (IUT III, Theorem 3.11 (Ind1), (Ind2))

At an archimedean rational place the indeterminacies of the log-shells are, by
IUT III, Theorem 3.11, (Ind2), "the action of copies of each of the automorphisms of order `2`
whose orbit constitutes the poly-automorphism of Proposition 1.2(vii) on each of the direct
summands of the factors", where the poly-isomorphism of IUT III, Proposition 1.2(vii) is the
orbit under "the **independent actions of `{±1}` on each of the direct factors**" `ℝ` and `ℝ·i`
of a factor `ℂ = ℝ ⊕ ℝ·i` (on a factor `ℝ`: the action of `{±1}`). On a factor `ℂ` these are the
four `ℝ`-linear maps `x ↦ ε₁·Re(x) + ε₂·i·Im(x)` (`ε₁, ε₂ ∈ {±1}`), i.e. the identity, complex
conjugation, `−1` and `−conj`; on a factor `ℝ` they are `±1`. Together with the indeterminacy
(Ind1) (automorphisms of the factors, i.e. complex conjugation, already among them), they act on
the packet `⊗_j K_{c j}` by `x ↦ (⊗_j ψ_j)(x)`.

We write these factor maps uniformly as `ψ_j = ε_j·σ_j` with `ε_j ∈ {±1}` and `σ_j` an
`ℝ`-algebra automorphism of the factor (identity or conjugation; `archFactorMap`), and the class
of induced maps of the packet is `archIndAut` (`LocalTheory.indAut` at `∞`). Since
`⊗_j (ε_j·σ_j) = (∏_j ε_j)·⊗_j σ_j` (`archIndMap_apply`), a member is a sign times a Galois
automorphism of the packet; hence it permutes the components of the direct sum decomposition
up to absolute value (`norm_archChar_archIndMap`) and preserves `B_I` and its real multiples
(`archIndAut_image_smul_archIntegral_subset`; IUT IV, Proposition 1.5(iii)). The class is
finite (`archIndAut_finite`), its members are continuous (`continuous_of_mem_archIndAut`), it
contains the Galois automorphisms (`galAut_subset_archIndAut`), and it preserves the
tensor products of log-shell elements (`archIndAut_image_archLogShellSet`). Since each factor
map `ψ_j` is an isometry of the Hermitian metric of its factor (`archInner_archFactorMap`),
`⊗_j ψ_j` is an isometry of the tensor-product Hermitian metric (`archTensorInner_archIndMap`),
so the class preserves the archimedean log-shell, the closed unit ball of that metric
(`archIndAut_image_archLogShell`; IUT III, Proposition 3.2(ii)). This gives IUT IV,
Proposition 1.5 for the archimedean theta region (`archIndAut_prop15`: it lies in
`(√2·π)^{|I|}·B_I`) and the admissibility of the corresponding regions
(`archIndAut_theta_admissible`, `archIndAut_thetaShell_admissible`).
-/

namespace Iut

namespace LocalConstruct

open NumberField MeasureTheory
open scoped TensorProduct Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- **The indeterminacy of a factor** (IUT III, Proposition 1.2(vii), Theorem 3.11 (Ind1),
(Ind2)): the `ℝ`-linear map `ε·σ` of the factor, with `ε ∈ {±1}` and `σ` an automorphism of the
factor. On a factor `ℂ` these are `x ↦ ε₁·Re(x) + ε₂·i·Im(x)` (`id`, `conj`, `−1`, `−conj`); on a
factor `ℝ`, `±1`. -/
noncomputable def archFactorMap {v : Place K} (σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v)
    (ε : ℤˣ) : ArchFactor K v →ₗ[ℝ] ArchFactor K v :=
  ((ε : ℤ) : ℝ) • σ.toLinearMap

lemma archFactorMap_apply {v : Place K} (σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v) (ε : ℤˣ)
    (a : ArchFactor K v) : archFactorMap σ ε a = ((ε : ℤ) : ℝ) • σ a := rfl

lemma abs_intCast_units (ε : ℤˣ) : |((ε : ℤ) : ℝ)| = 1 := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

/-- The factor indeterminacies preserve the absolute value, hence the log-shells. -/
lemma archAbs_archFactorMap {v : Place K} (σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v) (ε : ℤˣ)
    (a : ArchFactor K v) : archAbs v (archFactorMap σ ε a) = archAbs v a := by
  rw [archFactorMap_apply, archAbs_smul, abs_intCast_units, one_mul, archAbs_algEquiv]

variable {ι : Type} [Fintype ι] (c : ι → Place K)

/-- The map `⊗_j ψ_j` of the packet induced by the factor indeterminacies `ψ_j = ε_j·σ_j`. -/
noncomputable def archIndMap (σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j))
    (ε : ι → ℤˣ) : Tensor K .infinite c →ₗ[ℝ] Tensor K .infinite c :=
  PiTensorProduct.map fun j => archFactorMap (σ j) (ε j)

/-- **The archimedean indeterminacy automorphisms** (`LocalTheory.indAut` at `∞`; IUT III,
Theorem 3.11 (Ind1), (Ind2), Proposition 1.2(vii)): the maps `⊗_j ψ_j` of the packet induced by
independent factor indeterminacies `ψ_j = ε_j·σ_j` (`archFactorMap`). -/
def archIndAut : Set (Tensor K .infinite c → Tensor K .infinite c) :=
  {φ | ∃ σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j), ∃ ε : ι → ℤˣ,
    φ = ⇑(archIndMap c σ ε)}

lemma archIndMap_tprod (σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j)) (ε : ι → ℤˣ)
    (y : ∀ j, ArchFactor K (c j)) :
    archIndMap c σ ε (PiTensorProduct.tprod ℝ y) =
      PiTensorProduct.tprod ℝ fun j => archFactorMap (σ j) (ε j) (y j) :=
  PiTensorProduct.map_tprod _ _

/-- **`⊗_j (ε_j·σ_j) = (∏_j ε_j)·⊗_j σ_j`**: an indeterminacy automorphism is a sign times a
Galois automorphism of the packet. -/
theorem archIndMap_apply (σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j))
    (ε : ι → ℤˣ) (x : Tensor K .infinite c) :
    archIndMap c σ ε x = (((∏ j, ε j : ℤˣ) : ℤ) : ℝ) • mapAlgHom .infinite c σ x := by
  have h : archIndMap c σ ε =
      (((∏ j, ε j : ℤˣ) : ℤ) : ℝ) • (mapAlgHom .infinite c σ).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun y => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    change PiTensorProduct.map _ (PiTensorProduct.tprod ℝ y) = _
    rw [PiTensorProduct.map_tprod]
    simp only [archFactorMap_apply]
    rw [MultilinearMap.map_smul_univ, mapAlgHom_tprod]
    push_cast
    rfl
  rw [h]
  rfl

/-- **The indeterminacy automorphisms permute the components up to absolute value.** -/
theorem norm_archChar_archIndMap (σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j))
    (ε : ι → ℤˣ) (m : MaximalSpectrum (Tensor K .infinite c)) (x : Tensor K .infinite c) :
    ‖archChar c m (archIndMap c σ ε x)‖ =
      ‖archChar c (kerSpec ((archChar c m).comp (mapAlgHom .infinite c σ))) x‖ := by
  rw [archIndMap_apply, map_smul, norm_smul, Real.norm_eq_abs, abs_intCast_units, one_mul,
    norm_archChar_algHom]

/-- The Galois automorphisms are indeterminacy automorphisms (`ε = 1`). -/
theorem galAut_subset_archIndAut : galAut .infinite c ⊆ archIndAut c := by
  rintro _ ⟨σ, rfl⟩
  refine ⟨σ, fun _ => 1, ?_⟩
  funext x
  rw [archIndMap_apply]
  simp

/-- The identity is an indeterminacy automorphism. -/
lemma id_mem_archIndAut : id ∈ archIndAut c :=
  galAut_subset_archIndAut c (id_mem_galAut .infinite c)

/-- **The class of archimedean indeterminacy automorphisms is finite.** -/
theorem archIndAut_finite : (archIndAut c).Finite := by
  refine (Set.finite_range fun p : (∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j)) ×
      (ι → ℤˣ) => ⇑(archIndMap c p.1 p.2)).subset ?_
  rintro _ ⟨σ, ε, rfl⟩
  exact ⟨(σ, ε), rfl⟩

/-- Indeterminacy automorphisms are continuous (linear maps of finite-dimensional spaces). -/
lemma continuous_of_mem_archIndAut {φ : Tensor K .infinite c → Tensor K .infinite c}
    (hφ : φ ∈ archIndAut c) : Continuous φ := by
  obtain ⟨σ, ε, rfl⟩ := hφ
  exact LinearMap.continuous_of_finiteDimensional _

/-! ### The indeterminacy automorphisms preserve `B_I` and the log-shells -/

/-- **IUT IV, Proposition 1.5(iii)**: the indeterminacy automorphisms preserve `B_I`. -/
theorem archIndAut_image_archIntegral_subset :
    ∀ φ ∈ archIndAut c, φ '' archIntegral c ⊆ archIntegral c := by
  rintro _ ⟨σ, ε, rfl⟩ _ ⟨x, hx, rfl⟩ m
  rw [norm_archChar_archIndMap]
  exact hx _

/-- **IUT IV, Proposition 1.5(iii)**: the indeterminacy automorphisms preserve every real
multiple of `B_I`. -/
theorem archIndAut_image_smul_archIntegral_subset (t : ℝ) :
    ∀ φ ∈ archIndAut c, φ '' (algebraMap ℝ (Tensor K .infinite c) t • archIntegral c) ⊆
      algebraMap ℝ (Tensor K .infinite c) t • archIntegral c := by
  rintro φ hφ _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨σ, ε, rfl⟩ := hφ
  refine ⟨archIndMap c σ ε x, archIndAut_image_archIntegral_subset c _ ⟨σ, ε, rfl⟩ ⟨x, hx, rfl⟩,
    ?_⟩
  change algebraMap ℝ _ t * archIndMap c σ ε x = archIndMap c σ ε (algebraMap ℝ _ t * x)
  rw [archIndMap_apply, archIndMap_apply, map_mul, AlgHom.commutes, mul_smul_comm]

/-- The indeterminacy automorphisms preserve the tensor products of elements of the
log-shells. -/
theorem archIndAut_image_archLogShellSet :
    ∀ φ ∈ archIndAut c, φ '' archLogShellSet c ⊆ archLogShellSet c := by
  rintro _ ⟨σ, ε, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨fun j => archFactorMap (σ j) (ε j) (y j),
    fun j => (archAbs_archFactorMap _ _ _).trans_le (hy j), (archIndMap_tprod c σ ε y).symm⟩

/-! ### The indeterminacy automorphisms preserve the tensor-product metric -/

/-- The factor indeterminacies `ε·σ` are isometries of the Hermitian metric of the factor
(they preserve the absolute value, hence, by polarization, the inner product). -/
lemma archInner_archFactorMap {v : Place K} (σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v) (ε : ℤˣ)
    (a b : ArchFactor K v) :
    archInner v (archFactorMap σ ε a) (archFactorMap σ ε b) = archInner v a b := by
  rw [archInner_eq_polarization, archInner_eq_polarization, ← map_add, archAbs_archFactorMap,
    archAbs_archFactorMap, archAbs_archFactorMap]

/-- **The indeterminacy automorphisms are isometries of the tensor-product metric**: on
elementary tensors, `⟨⊗ψ_j(a_j), ⊗ψ_j(b_j)⟩_T = ∏_j ⟨ψ_j(a_j), ψ_j(b_j)⟩ = ∏_j ⟨a_j, b_j⟩`. -/
theorem archTensorInner_archIndMap (σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j))
    (ε : ι → ℤˣ) (x y : Tensor K .infinite c) :
    archTensorInner c (archIndMap c σ ε x) (archIndMap c σ ε y) = archTensorInner c x y := by
  have h : (archTensorInner c).compl₁₂ (archIndMap c σ ε) (archIndMap c σ ε) =
      archTensorInner c := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun a => ?_)
    refine PiTensorProduct.ext (MultilinearMap.ext fun b => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.compl₁₂_apply]
    rw [archIndMap_tprod, archIndMap_tprod, archTensorInner_tprod, archTensorInner_tprod]
    simp_rw [archInner_archFactorMap]
  exact LinearMap.congr_fun₂ h x y

/-- **The indeterminacy automorphisms preserve the archimedean log-shell** (the closed unit
ball of the tensor-product metric). -/
theorem archIndAut_image_archLogShell :
    ∀ φ ∈ archIndAut c, φ '' archLogShell c ⊆ archLogShell c := by
  rintro _ ⟨σ, ε, rfl⟩ _ ⟨x, hx, rfl⟩
  rw [mem_archLogShell, archTensorInner_archIndMap]
  exact hx

/-- **IUT IV, Proposition 1.5** for the archimedean theta region: the images of the
archimedean log-shell under the indeterminacy automorphisms lie in `(√2·π)^{|I|}·B_I`. -/
theorem archIndAut_prop15 : ∀ φ ∈ archIndAut c, φ '' archLogShell c ⊆
    algebraMap ℝ (Tensor K .infinite c) (archHullRadius ^ Fintype.card ι) •
      integralAt .infinite c :=
  fun φ hφ => (archIndAut_image_archLogShell c φ hφ).trans (archLogShell_subset c)

/-! ### Admissibility -/

/-- **The union of the images of a compact set of positive Haar measure under the
indeterminacy automorphisms is admissible.** -/
theorem iUnion_archIndAut_admissible {S : Set (Tensor K .infinite c)} (hS : IsCompact S)
    (hpos : 0 < haar .infinite c S) : (⋃ φ ∈ archIndAut c, φ '' S) ∈ admissible .infinite c := by
  have hsub : S ⊆ ⋃ φ ∈ archIndAut c, φ '' S := fun x hx =>
    Set.mem_iUnion₂.mpr ⟨id, id_mem_archIndAut c, ⟨x, hx, rfl⟩⟩
  have hcpt : IsCompact (⋃ φ ∈ archIndAut c, φ '' S) :=
    (archIndAut_finite c).isCompact_biUnion fun φ hφ =>
      hS.image (continuous_of_mem_archIndAut c hφ)
  refine ⟨?_, ?_, hcpt.isClosed.measurableSet, lt_of_lt_of_le hpos (measure_mono hsub),
    hcpt.measure_lt_top⟩
  · obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
    exact ⟨x, hsub hx⟩
  · rw [hcpt.isClosed.closure_eq]
    exact hcpt

/-- The union of the images of a scaled integral structure under the indeterminacy
automorphisms is admissible. -/
theorem archIndAut_theta_admissible (s : Tensor K .infinite c) (hs : IsUnit s) :
    (⋃ φ ∈ archIndAut c, φ '' (s • integralAt .infinite c)) ∈ admissible .infinite c :=
  iUnion_archIndAut_admissible c (isCompact_smul_integralAt s) (haar_smul_integralAt_pos hs)

/-- **The archimedean theta region is admissible**: the union of the images of the archimedean
log-shell under the indeterminacy automorphisms. -/
theorem archIndAut_thetaShell_admissible :
    (⋃ φ ∈ archIndAut c, φ '' archLogShell c) ∈ admissible .infinite c :=
  iUnion_archIndAut_admissible c (isCompact_archLogShell c) (haar_archLogShell_pos c)

end LocalConstruct

end Iut
