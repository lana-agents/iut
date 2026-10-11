/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.MaximalOrder

/-!
# The archimedean integral structure `B_I` (taxis #4, #278, #44)

The archimedean packet `T = ⊗_j K_{c j}` (over `ℝ`, each factor `ℝ` or `ℂ`) is a reduced
finite-dimensional commutative `ℝ`-algebra: it is formally unramified over `ℝ`, being a tensor
product of the formally unramified factors (`PiTensorProduct.formallyUnramified`), hence
reduced (`Algebra.FormallyUnramified.isReduced_of_field`). Being Artinian, it is the product of
its residue fields `T ⧸ 𝔪` over its finitely many maximal ideals `𝔪`
(`IsArtinianRing.equivPi`, `archResidueEquiv`): this is the **direct sum decomposition of the
packet into copies of `ℝ` and `ℂ`** of IUT IV, Proposition 1.5(iii) (cf. IUT III,
Proposition 3.1(i)). Each residue field is a finite extension of `ℝ`, which we embed in `ℂ`
(`archEmb`, a choice; the absolute value it induces does not depend on the choice,
`norm_algHom_eq_of_field`). The composite `archChar 𝔪 : T →ₐ[ℝ] ℂ` is the **`𝔪`-component** of
an element, with its canonical absolute value `‖archChar 𝔪 x‖`.

**The archimedean integral structure** (IUT IV, Proposition 1.5(iii)) is then

`B_I = {x | ‖archChar 𝔪 x‖ ≤ 1 for every 𝔪}` (`archIntegral`),

the direct product of the unit balls of the copies of `ℂ` (and `ℝ`) in the direct sum
decomposition of the packet. It is compact and a neighbourhood of `0`
(`isCompact_archIntegral`, `exists_ball_subset_archIntegral`), the units of `T` are the
elements all of whose components are nonzero (`isUnit_iff_forall_archChar_ne_zero`), and the
regions `a·B_I` (`a` a unit) are the polydiscs with radii `‖archChar 𝔪 a‖`
(`mem_smul_archIntegral_iff`; IUT III, Remark 3.9.5(i)). Every family of real radii is
realized by some `a` (`exists_forall_archChar_eq`), by the Chinese remainder theorem.

The absolute values of the components are intrinsic: every `ℝ`-algebra homomorphism
`χ : T → ℂ` has the absolute value of the component at its kernel
(`norm_algHom_eq_archChar`), since two `ℝ`-embeddings of a field into `ℂ` differ by complex
conjugation at most (`norm_algHom_subalgebra`).
-/

namespace Iut

namespace LocalConstruct

open NumberField
open scoped TensorProduct Pointwise ComplexConjugate

universe u

/-! ### `ℝ`-algebra homomorphisms into `ℂ` preserve the absolute value -/

/-- **An `ℝ`-algebra homomorphism from a real subalgebra of `ℂ` into `ℂ` preserves the absolute
value**: it is the identity or complex conjugation. -/
theorem norm_algHom_subalgebra (S : Subalgebra ℝ ℂ) (h : S →ₐ[ℝ] ℂ) (s : S) :
    ‖h s‖ = ‖(s : ℂ)‖ := by
  by_cases him : (s : ℂ).im = 0
  · have hs : s = algebraMap ℝ S (s : ℂ).re := by
      apply Subtype.ext
      apply Complex.ext <;> simp [him]
    rw [hs, AlgHom.commutes]
    simp
  · set i : S := ((s : ℂ).im)⁻¹ • (s - algebraMap ℝ S (s : ℂ).re) with hi
    have hiI : (i : ℂ) = Complex.I := by
      rw [hi]
      apply Complex.ext <;> simp [him]
    have hs : s = algebraMap ℝ S (s : ℂ).re + (s : ℂ).im • i := by
      apply Subtype.ext
      rw [Subalgebra.coe_add, Subalgebra.coe_smul, hiI]
      apply Complex.ext <;> simp
    have hhs : h s = algebraMap ℝ ℂ (s : ℂ).re + (s : ℂ).im • h i := by
      conv_lhs => rw [hs]
      rw [map_add, map_smul, AlgHom.commutes]
    have hii : i * i = -1 := Subtype.ext (by simp [hiI])
    have hsq : h i ^ 2 = Complex.I ^ 2 := by
      rw [Complex.I_sq, sq, ← map_mul, hii, map_neg, map_one]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
    · rw [hhs, h1]
      conv_rhs => rw [← Complex.re_add_im (s : ℂ)]
      simp [Complex.real_smul]
    · rw [hhs, h1]
      have : (algebraMap ℝ ℂ (s : ℂ).re + (s : ℂ).im • -Complex.I) = conj (s : ℂ) := by
        apply Complex.ext <;> simp
      rw [this, RCLike.norm_conj]

/-- **Two `ℝ`-embeddings of a field into `ℂ` induce the same absolute value.** -/
theorem norm_algHom_eq_of_field {F : Type*} [Field F] [Algebra ℝ F] (f g : F →ₐ[ℝ] ℂ) (y : F) :
    ‖g y‖ = ‖f y‖ := by
  let e := AlgEquiv.ofInjective f f.toRingHom.injective
  have : g y = (g.comp e.symm.toAlgHom) (e y) := by simp
  rw [this, norm_algHom_subalgebra]
  rfl

variable {K : Type u} [Field K] [NumberField K]

/-! ### The archimedean factors -/

section Factor

variable (v : Place K)

/-- An archimedean factor, as an `ℝ`-algebra, is the subalgebra `ℝ` or `ℂ` of `ℂ`. -/
noncomputable def archFactorEquiv : ArchFactor K v ≃ₐ[ℝ] archField K (archPlace K v) :=
  ULift.algEquiv

/-- **The absolute value** of an archimedean factor (the factor `ℝ` or `ℂ` with its canonical
absolute value). -/
noncomputable def archAbs (a : ArchFactor K v) : ℝ := ‖(archFactorEquiv v a : ℂ)‖

lemma archAbs_nonneg (a : ArchFactor K v) : 0 ≤ archAbs v a := norm_nonneg _

lemma archAbs_one : archAbs v 1 = 1 := by
  simp [archAbs]

lemma archAbs_smul (r : ℝ) (a : ArchFactor K v) : archAbs v (r • a) = |r| * archAbs v a := by
  simp only [archAbs, map_smul, Subalgebra.coe_smul, norm_smul, Real.norm_eq_abs]

lemma archAbs_neg (a : ArchFactor K v) : archAbs v (-a) = archAbs v a := by
  simp only [archAbs, map_neg, Subalgebra.coe_neg, norm_neg]

/-- **Automorphisms of the archimedean factors preserve the absolute value** (they are the
identity or complex conjugation). -/
lemma archAbs_algEquiv (σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v) (a : ArchFactor K v) :
    archAbs v (σ a) = archAbs v a := by
  unfold archAbs
  have h := norm_algHom_subalgebra _ ((Subalgebra.val _).comp ((archFactorEquiv v).toAlgHom.comp
    (σ.toAlgHom.comp (archFactorEquiv v).symm.toAlgHom))) (archFactorEquiv v a)
  simpa using h

/-- An archimedean factor is formally unramified over `ℝ` (it is `ℝ` or `ℂ`). -/
instance formallyUnramified_archFactor : Algebra.FormallyUnramified ℝ (ArchFactor K v) := by
  by_cases h : (archPlace K v).IsReal
  · exact Algebra.FormallyUnramified.of_equiv ((archFactorEquiv v).trans
      ((Subalgebra.equivOfEq _ _ (archField_of_isReal K h)).trans (Algebra.botEquiv ℝ ℂ))).symm
  · have h' : (archPlace K v).IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp h
    haveI : Algebra.FormallyUnramified ℝ ℂ := Algebra.FormallyUnramified.of_isSeparable ℝ ℂ
    exact Algebra.FormallyUnramified.of_equiv ((archFactorEquiv v).trans
      ((Subalgebra.equivOfEq _ _ (archField_of_isComplex K h')).trans Subalgebra.topEquiv)).symm

end Factor

/-! ### The residue fields of the archimedean packet -/

variable {ι : Type} [Fintype ι] (c : ι → Place K)

/-- The archimedean packets are formally unramified over `ℝ`. -/
instance formallyUnramified_tensor_infinite :
    Algebra.FormallyUnramified ℝ (Tensor K .infinite c) :=
  PiTensorProduct.formallyUnramified (R := ℝ) (fun j => ArchFactor K (c j))

/-- **The archimedean packets are reduced.** -/
instance isReduced_tensor_infinite : IsReduced (Tensor K .infinite c) :=
  Algebra.FormallyUnramified.isReduced_of_field ℝ _

instance isArtinianRing_tensor_infinite : IsArtinianRing (Tensor K .infinite c) :=
  IsArtinianRing.of_finite ℝ _

/-- The maximal ideals of an archimedean packet (finitely many: the packet is Artinian). -/
noncomputable instance : Fintype (MaximalSpectrum (Tensor K .infinite c)) := Fintype.ofFinite _

/-- **The residue field** `T ⧸ 𝔪` of the archimedean packet at a maximal ideal `𝔪`: a copy of `ℝ`
or `ℂ` in the direct sum decomposition of the packet. -/
abbrev ArchResidueField (m : MaximalSpectrum (Tensor K .infinite c)) : Type u :=
  Tensor K .infinite c ⧸ m.asIdeal

variable (m : MaximalSpectrum (Tensor K .infinite c))

noncomputable instance : Field (ArchResidueField c m) := Ideal.Quotient.field m.asIdeal

instance : Module.Finite ℝ (ArchResidueField c m) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℝ m.asIdeal).toLinearMap
    Ideal.Quotient.mk_surjective

instance : Module.Free ℝ (ArchResidueField c m) := Module.Free.of_divisionRing _ _

instance : Module.IsTorsionFree ℝ (ArchResidueField c m) := Module.Free.instIsTorsionFree ℝ _

instance : Algebra.IsAlgebraic ℝ (ArchResidueField c m) := Algebra.IsAlgebraic.of_finite ℝ _

/-- The projection of the packet onto its residue field at `𝔪`. -/
noncomputable def archProj : Tensor K .infinite c →ₐ[ℝ] ArchResidueField c m :=
  Ideal.Quotient.mkₐ ℝ m.asIdeal

/-- **The direct sum decomposition** of the archimedean packet into its residue fields (a
reduced Artinian ring is the product of its residue fields). -/
noncomputable def archResidueEquiv :
    Tensor K .infinite c ≃ₐ[Tensor K .infinite c] ∀ m, ArchResidueField c m :=
  IsArtinianRing.equivPi _

lemma archResidueEquiv_apply (x : Tensor K .infinite c) :
    archResidueEquiv c x m = archProj c m x := rfl

/-- A chosen embedding of the residue field at `𝔪` into `ℂ` (the residue field is a finite
extension of `ℝ`). The induced absolute value does not depend on the choice
(`norm_algHom_eq_of_field`). -/
noncomputable def archEmb : ArchResidueField c m →ₐ[ℝ] ℂ := IsAlgClosed.lift

/-- **The `𝔪`-component** `T → T ⧸ 𝔪 ↪ ℂ` of the archimedean packet. -/
noncomputable def archChar : Tensor K .infinite c →ₐ[ℝ] ℂ :=
  (archEmb c m).comp (archProj c m)

lemma archChar_apply (x : Tensor K .infinite c) :
    archChar c m x = archEmb c m (archProj c m x) := rfl

lemma archChar_algebraMap (r : ℝ) :
    archChar c m (algebraMap ℝ (Tensor K .infinite c) r) = (r : ℂ) :=
  (archChar c m).commutes r

lemma norm_archChar_algebraMap (r : ℝ) :
    ‖archChar c m (algebraMap ℝ (Tensor K .infinite c) r)‖ = |r| := by
  rw [archChar_algebraMap, Complex.norm_real, Real.norm_eq_abs]

lemma archChar_eq_zero_iff {x : Tensor K .infinite c} :
    archChar c m x = 0 ↔ archProj c m x = 0 := by
  rw [archChar_apply, map_eq_zero_iff (archEmb c m) (RingHom.injective (archEmb c m).toRingHom)]

/-- The components are continuous (linear maps of finite-dimensional spaces). -/
lemma continuous_archChar : Continuous (archChar c m) :=
  LinearMap.continuous_of_finiteDimensional (archChar c m).toLinearMap

/-! ### The components are intrinsic -/

variable {c}

/-- The kernel of an `ℝ`-algebra homomorphism `T → ℂ`, as a maximal ideal of the packet. -/
noncomputable def kerSpec (χ : Tensor K .infinite c →ₐ[ℝ] ℂ) :
    MaximalSpectrum (Tensor K .infinite c) :=
  haveI := RingHom.ker_isPrime χ
  ⟨RingHom.ker χ, IsArtinianRing.isMaximal_of_isPrime _⟩

/-- An `ℝ`-algebra homomorphism `χ : T → ℂ` killing `𝔪` has the absolute value of the
`𝔪`-component. -/
theorem norm_algHom_eq_archChar_of_le (χ : Tensor K .infinite c →ₐ[ℝ] ℂ)
    (h : m.asIdeal ≤ RingHom.ker χ) (x : Tensor K .infinite c) :
    ‖χ x‖ = ‖archChar c m x‖ := by
  have hχ : χ x = Ideal.Quotient.liftₐ m.asIdeal χ (fun a ha => h ha) (archProj c m x) := rfl
  rw [hχ, archChar_apply, norm_algHom_eq_of_field (archEmb c m)]

/-- **Every `ℝ`-algebra homomorphism `T → ℂ` has the absolute value of the component at its
kernel.** -/
theorem norm_algHom_eq_archChar (χ : Tensor K .infinite c →ₐ[ℝ] ℂ) (x : Tensor K .infinite c) :
    ‖χ x‖ = ‖archChar c (kerSpec χ) x‖ :=
  norm_algHom_eq_archChar_of_le _ χ le_rfl x

/-- **Algebra endomorphisms of the packet permute the components up to absolute value.** -/
theorem norm_archChar_algHom (σ : Tensor K .infinite c →ₐ[ℝ] Tensor K .infinite c)
    (x : Tensor K .infinite c) :
    ‖archChar c m (σ x)‖ = ‖archChar c (kerSpec ((archChar c m).comp σ)) x‖ :=
  norm_algHom_eq_archChar ((archChar c m).comp σ) x

/-! ### The components of elementary tensors -/

/-- An elementary tensor is the product of its factors `1 ⊗ ⋯ ⊗ a_j ⊗ ⋯ ⊗ 1`. -/
lemma tprod_eq_prod_singleAlgHom [DecidableEq ι] (y : ∀ j, ArchFactor K (c j)) :
    (PiTensorProduct.tprod ℝ y : Tensor K .infinite c) =
      ∏ j, PiTensorProduct.singleAlgHom (R := ℝ) (A := fun j => ArchFactor K (c j)) j (y j) := by
  calc (PiTensorProduct.tprod ℝ y : Tensor K .infinite c)
      = PiTensorProduct.tprodMonoidHom ℝ (∏ j, Pi.mulSingle j (y j)) := by
        rw [Finset.univ_prod_mulSingle]; rfl
    _ = _ := map_prod _ _ _

/-- The component of a factor `1 ⊗ ⋯ ⊗ a ⊗ ⋯ ⊗ 1` has the absolute value of `a`. -/
lemma norm_archChar_singleAlgHom [DecidableEq ι] (j : ι) (a : ArchFactor K (c j)) :
    ‖archChar c m (PiTensorProduct.singleAlgHom (R := ℝ) (A := fun j => ArchFactor K (c j)) j a)‖ =
      archAbs (c j) a := by
  have h := norm_algHom_subalgebra _ (((archChar c m).comp
    (PiTensorProduct.singleAlgHom (R := ℝ) (A := fun j => ArchFactor K (c j)) j)).comp
      (archFactorEquiv (c j)).symm.toAlgHom) (archFactorEquiv (c j) a)
  simpa [archAbs] using h

/-- **IUT IV, Proposition 1.5(iv)**: every component of an elementary tensor `⊗_j y_j` has
absolute value `∏_j |y_j|`. -/
theorem norm_archChar_tprod (y : ∀ j, ArchFactor K (c j)) :
    ‖archChar c m (PiTensorProduct.tprod ℝ y)‖ = ∏ j, archAbs (c j) (y j) := by
  classical
  rw [tprod_eq_prod_singleAlgHom, map_prod, norm_prod]
  exact Finset.prod_congr rfl fun j _ => norm_archChar_singleAlgHom m j (y j)

variable (c)

/-! ### The direct sum decomposition -/

/-- Every family of real numbers is the family of components of an element of the packet
(Chinese remainder theorem). -/
lemma exists_forall_archChar_eq (r : MaximalSpectrum (Tensor K .infinite c) → ℝ) :
    ∃ a : Tensor K .infinite c, ∀ m, archChar c m a = (r m : ℂ) := by
  refine ⟨(archResidueEquiv c).symm fun m => algebraMap ℝ (ArchResidueField c m) (r m),
    fun m => ?_⟩
  have h : archProj c m ((archResidueEquiv c).symm
      fun m => algebraMap ℝ (ArchResidueField c m) (r m)) =
      algebraMap ℝ (ArchResidueField c m) (r m) :=
    congrFun ((archResidueEquiv c).apply_symm_apply _) m
  rw [archChar_apply, h, AlgHom.commutes, Complex.coe_algebraMap]

/-- An element of the packet is determined by its components. -/
lemma eq_of_forall_archChar_eq {x y : Tensor K .infinite c}
    (h : ∀ m, archChar c m x = archChar c m y) : x = y := by
  refine (archResidueEquiv c).injective (funext fun m => ?_)
  rw [archResidueEquiv_apply, archResidueEquiv_apply]
  exact (archEmb c m).toRingHom.injective (h m)

/-- **The units of the packet** are the elements all of whose components are nonzero. -/
theorem isUnit_iff_forall_archChar_ne_zero {a : Tensor K .infinite c} :
    IsUnit a ↔ ∀ m, archChar c m a ≠ 0 := by
  constructor
  · intro ha m
    exact (ha.map (archChar c m)).ne_zero
  · intro h
    have : IsUnit (archResidueEquiv c a) := Pi.isUnit_iff.mpr fun m =>
      isUnit_iff_ne_zero.mpr fun h0 => h m ((archChar_eq_zero_iff c m).mpr h0)
    simpa using this.map (archResidueEquiv c).symm

/-- The components, jointly, as an `ℝ`-linear map to `ℂ^{Spm T}`. -/
noncomputable def archCharLin :
    Tensor K .infinite c →ₗ[ℝ] (MaximalSpectrum (Tensor K .infinite c) → ℂ) :=
  LinearMap.pi fun m => (archChar c m).toLinearMap

lemma ker_archCharLin : LinearMap.ker (archCharLin c) = ⊥ := by
  refine LinearMap.ker_eq_bot'.mpr fun x hx => eq_of_forall_archChar_eq c fun m => ?_
  rw [map_zero]
  exact congrFun hx m

/-! ### The integral structure `B_I` -/

/-- **The archimedean integral structure `B_I`** (IUT IV, Proposition 1.5(iii);
`LocalTheory.integral` at `∞`): the direct product of the unit balls of the copies of `ℂ`
(and `ℝ`) in the direct sum decomposition of the packet, i.e. the elements all of whose
components have absolute value at most `1`. -/
def archIntegral : Set (Tensor K .infinite c) := {x | ∀ m, ‖archChar c m x‖ ≤ 1}

lemma mem_archIntegral {x : Tensor K .infinite c} :
    x ∈ archIntegral c ↔ ∀ m, ‖archChar c m x‖ ≤ 1 :=
  Iff.rfl

lemma archIntegral_eq_preimage :
    archIntegral c = archCharLin c ⁻¹' Metric.closedBall 0 1 := by
  ext x
  rw [Set.mem_preimage, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  rfl

/-- `1 ∈ B_I` (`LocalTheory.one_mem_integral` at `∞`). -/
lemma one_mem_archIntegral : (1 : Tensor K .infinite c) ∈ archIntegral c := fun m => by
  rw [map_one, norm_one]

lemma archIntegral_nonempty : (archIntegral c).Nonempty := ⟨1, one_mem_archIntegral c⟩

/-- **`B_I` is compact.** -/
lemma isCompact_archIntegral : IsCompact (archIntegral c) := by
  rw [archIntegral_eq_preimage]
  exact (LinearMap.isClosedEmbedding_of_injective (ker_archCharLin c)).isCompact_preimage
    (isCompact_closedBall 0 1)

/-- **`B_I` is closed.** -/
lemma isClosed_archIntegral : IsClosed (archIntegral c) := (isCompact_archIntegral c).isClosed

/-- **`B_I` is a neighbourhood of `0`.** -/
lemma exists_ball_subset_archIntegral :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : Tensor K .infinite c) r ⊆ archIntegral c := by
  have hopen : IsOpen (archCharLin c ⁻¹' Metric.ball 0 1) :=
    Metric.isOpen_ball.preimage (LinearMap.continuous_of_finiteDimensional _)
  have h0 : (0 : Tensor K .infinite c) ∈ archCharLin c ⁻¹' Metric.ball 0 1 := by
    rw [Set.mem_preimage, map_zero]
    exact Metric.mem_ball_self one_pos
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
  refine ⟨r, hr, hball.trans ?_⟩
  rw [archIntegral_eq_preimage]
  exact Set.preimage_mono Metric.ball_subset_closedBall

/-! ### The hull regions `a·B_I` -/

variable {c}

/-- **The hull regions `a·B_I` are polydiscs**: for a unit `a`, `x ∈ a·B_I` iff every component
of `x` has absolute value at most that of the corresponding component of `a`
(IUT III, Remark 3.9.5(i)). -/
theorem mem_smul_archIntegral_iff {a : Tensor K .infinite c} (ha : IsUnit a)
    {x : Tensor K .infinite c} :
    x ∈ a • archIntegral c ↔ ∀ m, ‖archChar c m x‖ ≤ ‖archChar c m a‖ := by
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩ m
    rw [smul_eq_mul, map_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hy m)
  · intro h
    refine ⟨↑ha.unit⁻¹ * x, fun m => ?_, ?_⟩
    · have hne : archChar c m a ≠ 0 := (isUnit_iff_forall_archChar_ne_zero c).mp ha m
      have hinv : archChar c m ↑ha.unit⁻¹ = (archChar c m a)⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← map_mul, ha.val_inv_mul, map_one]
      rw [map_mul, norm_mul, hinv, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr hne), mul_one]
      exact h m
    · rw [smul_eq_mul, ← mul_assoc, ha.mul_val_inv, one_mul]

/-- For real `t > 0`, `x ∈ t·B_I` iff every component of `x` has absolute value at most `t`. -/
theorem mem_algebraMap_smul_archIntegral {t : ℝ} (ht : 0 < t) {x : Tensor K .infinite c} :
    x ∈ algebraMap ℝ (Tensor K .infinite c) t • archIntegral c ↔
      ∀ m, ‖archChar c m x‖ ≤ t := by
  rw [mem_smul_archIntegral_iff ((isUnit_iff_ne_zero.mpr ht.ne').map _)]
  refine forall_congr' fun m => ?_
  rw [norm_archChar_algebraMap, abs_of_pos ht]

end LocalConstruct

end Iut
