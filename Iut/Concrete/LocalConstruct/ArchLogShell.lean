/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.ThetaAdmissible

/-!
# The archimedean log-shell and IUT IV, Proposition 1.5 (taxis #4, #278)

At the archimedean place the log-shell of a factor `ℝ` or `ℂ` is the closed disc of radius
`π` (the image of the units under the logarithm; IUT III, Proposition 1.2(ii)), and the
archimedean packet region of IUT IV, Proposition 1.5 is `π^{|I|}·B_I`, the closed ball of
radius `π^{|I|}` of the projective tensor norm — the closed absolutely convex hull of the
elementary tensors of the discs of radius `π`. We take this ball as the archimedean log-shell
(`archLogShell`, the field `LocalTheory.logShell` at `∞`), so that Proposition 1.5(iii),(iv)
(`prop15`) reduces to the statement that the indeterminacy automorphisms preserve `B_I`
(`mapAlgHom_image_archIntegral_subset`): the automorphisms `σ_j` of the factors `ℝ`, `ℂ`
over `ℝ` are isometries (`norm_archAut_apply`: an `ℝ`-algebra automorphism of `ℂ` is the
identity or complex conjugation), and the projective norm is contractive under tensor
products of contractions (`PiTensorProduct.opNorm_mapL`).
-/

namespace Iut

namespace LocalConstruct

open NumberField MeasureTheory
open scoped TensorProduct Pointwise ComplexConjugate

universe u

/-! ### Automorphisms of `ℝ` and `ℂ` over `ℝ` are isometries -/

/-- An `ℝ`-algebra endomorphism of a subalgebra `S` of `ℂ` which is either real (all its
elements are real) or contains `i` preserves the absolute value. -/
theorem norm_algHom_apply_subalgebra (S : Subalgebra ℝ ℂ)
    (hS : Complex.I ∈ S ∨ ∀ x : S, ∃ r : ℝ, (x : ℂ) = r) (σ : S →ₐ[ℝ] S) (x : S) :
    ‖(σ x : ℂ)‖ = ‖(x : ℂ)‖ := by
  rcases hS with hI | hreal
  · set i : S := ⟨Complex.I, hI⟩ with hi
    have hii : i * i = -1 := Subtype.ext (by simp [hi, Complex.I_mul_I])
    have hσi : (σ i : ℂ) ^ 2 = Complex.I ^ 2 := by
      rw [Complex.I_sq, sq, ← Subalgebra.coe_mul, ← map_mul, hii, map_neg, map_one]
      rfl
    have hx : x = algebraMap ℝ S x.1.re + algebraMap ℝ S x.1.im * i := by
      apply Subtype.ext
      simp [hi, Complex.re_add_im]
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hσi
    conv_lhs => rw [hx, map_add, map_mul, σ.commutes, σ.commutes]
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_algebraMap,
      Complex.coe_algebraMap]
    rcases hσi with h | h
    · rw [h, Complex.re_add_im]
    · rw [h]
      have : (x.1.re : ℂ) + x.1.im * -Complex.I = conj (x.1 : ℂ) := by
        conv_rhs => rw [← Complex.re_add_im (x.1 : ℂ)]
        simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
      rw [this, RCLike.norm_conj]
  · obtain ⟨r, hr⟩ := hreal x
    have hx : x = algebraMap ℝ S r := Subtype.ext (by simpa using hr)
    rw [hx, σ.commutes]

variable {K : Type u} [Field K] [NumberField K]

omit [NumberField K] in
/-- The archimedean factor of a real place is real; that of a complex place contains `i`. -/
lemma archField_cases (w : InfinitePlace K) :
    Complex.I ∈ archField K w ∨ ∀ x : archField K w, ∃ r : ℝ, (x : ℂ) = r := by
  by_cases h : w.IsReal
  · right
    intro x
    have hx : (x : ℂ) ∈ (⊥ : Subalgebra ℝ ℂ) := archField_of_isReal K h ▸ x.2
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hx
    exact ⟨r, hr.symm⟩
  · left
    rw [archField_of_isComplex K (InfinitePlace.not_isReal_iff_isComplex.mp h)]
    exact Algebra.mem_top

variable (v : Place K)

/-- The identity map from an archimedean factor to its normed model. -/
def toNormedFactor : ArchFactor K v → ArchNormedFactor v := id

/-- **Automorphisms of the archimedean factors are isometries.** -/
theorem norm_archAut_apply (σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v) (x : ArchNormedFactor v) :
    ‖toNormedFactor v (σ x)‖ = ‖x‖ := by
  let σ' : archField K (archPlace K v) →ₐ[ℝ] archField K (archPlace K v) :=
    ULift.algEquiv.toAlgHom.comp (σ.toAlgHom.comp ULift.algEquiv.symm.toAlgHom)
  have h := norm_algHom_apply_subalgebra _ (archField_cases (archPlace K v)) σ' x.down
  exact h

/-- The automorphism of a factor as a continuous linear map of the normed factor, of norm at
most `1`. -/
noncomputable def archAutCLM (σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v) :
    ArchNormedFactor v →L[ℝ] ArchNormedFactor v :=
  LinearMap.mkContinuous
    { toFun := fun x => toNormedFactor v (σ x)
      map_add' := fun x y => map_add σ x y
      map_smul' := fun r x => map_smul σ r x } 1
    fun x => by rw [one_mul]; exact (norm_archAut_apply v σ x).le

lemma archAutCLM_apply (σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v) (x : ArchNormedFactor v) :
    archAutCLM v σ x = toNormedFactor v (σ x) := rfl

lemma norm_archAutCLM_le (σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v) : ‖archAutCLM v σ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ### The indeterminacy automorphisms preserve `B_I` -/

variable {ι : Type} [Fintype ι] (c : ι → Place K)

/-- `⊗_j σ_j` on the normed model is the tensor product of the continuous linear maps. -/
lemma toArchModel_mapAlgHom (σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j))
    (x : Tensor K .infinite c) :
    toArchModel c (mapAlgHom .infinite c σ x) =
      PiTensorProduct.mapL (fun j => archAutCLM (c j) (σ j)) (toArchModel c x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, mapAlgHom_tprod]
    change (r • PiTensorProduct.tprod ℝ (fun j => toNormedFactor (c j) (σ j (m j))) :
        ArchModel c) =
      PiTensorProduct.mapL (fun j => archAutCLM (c j) (σ j))
        (r • PiTensorProduct.tprod ℝ (fun j => toNormedFactor (c j) (m j)) : ArchModel c)
    rw [map_smul, PiTensorProduct.mapL_apply, PiTensorProduct.map_tprod]
    rfl
  | add x y hx hy =>
    rw [map_add]
    change (toArchModel c (mapAlgHom .infinite c σ x) + toArchModel c (mapAlgHom .infinite c σ y) :
        ArchModel c) =
      PiTensorProduct.mapL (fun j => archAutCLM (c j) (σ j))
        (toArchModel c x + toArchModel c y : ArchModel c)
    rw [map_add, hx, hy]

/-- **The projective norm is contractive under the indeterminacy automorphisms.** -/
theorem archNorm_mapAlgHom_le (σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j))
    (x : Tensor K .infinite c) : archNorm c (mapAlgHom .infinite c σ x) ≤ archNorm c x := by
  unfold archNorm
  rw [toArchModel_mapAlgHom]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine (PiTensorProduct.opNorm_mapL _).trans ?_
  exact Finset.prod_le_one (fun j _ => norm_nonneg _) fun j _ => norm_archAutCLM_le (c j) (σ j)

/-- **IUT IV, Proposition 1.5(iii)**: the indeterminacy automorphisms preserve `B_I`. -/
theorem mapAlgHom_image_archIntegral_subset
    (σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j)) :
    mapAlgHom .infinite c σ '' archIntegral c ⊆ archIntegral c := by
  rintro _ ⟨x, hx, rfl⟩
  exact (archNorm_mapAlgHom_le c σ x).trans hx

/-- The indeterminacy automorphisms preserve every real multiple of `B_I`. -/
theorem indAut_image_smul_archIntegral_subset (t : ℝ) :
    ∀ φ ∈ indAut .infinite c, φ '' (algebraMap ℝ (Tensor K .infinite c) t • archIntegral c) ⊆
      algebraMap ℝ (Tensor K .infinite c) t • archIntegral c := by
  rintro _ ⟨σ, rfl⟩ _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨mapAlgHom .infinite c σ x, mapAlgHom_image_archIntegral_subset c σ ⟨x, hx, rfl⟩, ?_⟩
  change algebraMap ℝ _ t * mapAlgHom .infinite c σ x =
    mapAlgHom .infinite c σ (algebraMap ℝ _ t * x)
  rw [map_mul, AlgHom.commutes]

/-! ### The archimedean log-shell -/

/-- **The archimedean log-shell** `π^{|I|}·B_I` (`LocalTheory.logShell` at `∞`; IUT IV,
Proposition 1.5). -/
def archLogShell : Set (Tensor K .infinite c) :=
  algebraMap ℝ (Tensor K .infinite c) (Real.pi ^ Fintype.card ι) • archIntegral c

lemma isUnit_archScalar : IsUnit (algebraMap ℝ (Tensor K .infinite c) (Real.pi ^ Fintype.card ι)) :=
  (isUnit_iff_ne_zero.mpr (pow_ne_zero _ Real.pi_ne_zero)).map (algebraMap ℝ _)

/-- The archimedean log-shell is compact. -/
lemma isCompact_archLogShell : IsCompact (archLogShell c) :=
  isCompact_smul _ (isCompact_archIntegral c)

/-- The archimedean log-shell is relatively compact (`LocalTheory.logShell_relCompact` at `∞`). -/
lemma isCompact_closure_archLogShell : IsCompact (closure (archLogShell c)) := by
  rw [(isCompact_archLogShell c).isClosed.closure_eq]
  exact isCompact_archLogShell c

/-- **IUT IV, Proposition 1.5(iii),(iv)** (`LocalTheory.prop15`): the images of the
archimedean log-shell under the indeterminacy automorphisms lie in `π^{|I|}·B_I`. -/
theorem prop15 : ∀ φ ∈ indAut .infinite c, φ '' archLogShell c ⊆
    algebraMap ℝ (Tensor K .infinite c) (Real.pi ^ Fintype.card ι) • integralAt .infinite c :=
  indAut_image_smul_archIntegral_subset c _

/-- The indeterminacy automorphisms preserve the archimedean log-shell
(`LocalTheory.indAut_logShell` at `∞`). -/
theorem indAut_archLogShell : ∀ φ ∈ indAut .infinite c, φ '' archLogShell c ⊆ archLogShell c :=
  indAut_image_smul_archIntegral_subset c _

/-- **`LocalTheory.thetaShell_admissible`** at `∞`. -/
theorem thetaShell_admissible_infinite :
    (⋃ φ ∈ indAut .infinite c, φ '' archLogShell c) ∈ admissible .infinite c :=
  iUnion_indAut_admissible .infinite c (isCompact_archLogShell c)
    (haar_smul_integralAt_pos (isUnit_archScalar c))

end LocalConstruct

end Iut
