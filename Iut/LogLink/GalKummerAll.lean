/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.GalKummer
import Iut.LogLink.GaloisArch
import Iut.Concrete.LocalConstruct.ArchIndAut

/-!
# Unit-induced Kummer data at all places (`V^non ∪ V^arc`)

`Iut/LogLink/GalKummer.lean` gives the Kummer identifications of the log-shell containers at the
nonarchimedean places (`Wall.Scaling`, which acts trivially at `∞`) by their anabelian origin, and
proves them unit-induced, log-shell compatible and volume neutral. Here the archimedean places are
added.

## The archimedean factors and packets

* **Factors.** An archimedean factor `K_v` (`ℝ` or `ℂ`, `LocalConstruct.ArchFactor`) embeds in
  `ℂ` (`factorEmb`). An `ℝ`-linear map `ψ` of the factor is **unit-induced**
  (`FactorArchUnitInduced`) if it is the restriction of an `ℝ`-linear automorphism of `ℂ` which
  is unit-induced in the sense of `Iut/LogLink/GaloisArch.lean` (`ArchUnitInduced`: induced by an
  automorphism of the angular units `S¹` and a map of the radial part `ℝ_{>0}`).
  **`factorArchUnitInduced_iff`**: `ψ` is unit-induced and preserves the log-shell of the factor
  (the elements of absolute value `≤ π`) **iff** `ψ = ε·σ` with `ε = ±1` and `σ` an automorphism
  of the factor (`archFactorMap σ ε`), i.e. iff `ψ` belongs to the poly-isomorphism of IUT III,
  Proposition 1.2(vii) (the indeterminacy (Ind2) at `V^arc`).
* **Packets.** Hence the class `LocalConstruct.archIndAut` of maps `⊗_j (ε_j·σ_j)` of an
  archimedean packet is exactly the class of tensor products of unit-induced, log-shell
  preserving factor maps (**`mem_archIndAut_iff`**). These maps are injective
  (`archIndMap_injective`), map the archimedean log-shell **onto** itself
  (`image_archLogShell_archIndMap`), have determinant `±1` (`abs_det_archIndMap`), and therefore
  preserve the Haar measure and the log-volume of every region (**`haar_image_archIndMap`,
  `componentVol_image_archIndMap`**) and admissibility (`image_mem_admissible_archIndMap`).

## All places

* `ArcScaling D`: an archimedean Kummer identification of the container (a factor datum
  `(σ_j, ε_j)` for every capsule, tuple of archimedean places and label), a group;
  `FullScaling D = Scaling D × ArcScaling D`: Kummer identifications at **all** places;
  `fullAct`: the action on regions, with `fullAct_mul`, `fullAct_one`, `isAdelic_fullAct`.
* **`logVol_fullAct`**: `log-vol(W·S) = log-vol(W_non·S)`: the archimedean components do not
  change log-volumes; so `log-vol(W·S) = shift(W_non) + log-vol(S)` (`logVol_fullAct_adelic`).
* `FullKummer L` (resp. `FullGalKummer L`): Kummer data at every vertex of a log-theta-lattice and
  every place, with the nonarchimedean components arising from automorphisms of the unit groups
  (resp. Galois groups) and the archimedean components from `{±1} × Aut` (resp. `Gal(ℂ/ℝ)`).
  **`FullKummer.logVol_transport`**: the transport between any two vertices, over all places,
  preserves log-volumes of adelic regions (the distortion is `0` at `V^non ∪ V^arc`);
  `FullKummer.xi_iff_ss`, `classicalABC_of_thm311_full`, `classicalABC_of_xi_full`.

## Scope

* The model's wall (`XiPrinciple`, `Thm311`) is formulated with the nonarchimedean Kummer
  scalings of `LatticeKummer`; the restatements over all places use `FullKummer.toLatticeKummer`
  and are justified by `logVol_fullAct`: adding the archimedean Kummer identifications changes no
  log-volume, so the wall is the same. This is a statement about the model's log-volumes; the
  angular log-volumes and Aut-holomorphic orbispaces of IUT at `V^arc` are not formalised.
* As at `V^non`, that the archimedean Kummer identifications are of this form (here: in the
  poly-isomorphism) is the datum; `factorArchUnitInduced_iff` shows that this is equivalent to
  unit-inducedness together with log-shell compatibility. Unlike at `V^non`, unit-inducedness
  alone does not imply log-shell compatibility at `V^arc` (`not_archPolyIso_radialScale`): the
  radial normalization is an extra input (IUT III, Remark 1.2.1(ii)).
-/

namespace Iut

namespace LogLink

open LocalConstruct NumberField Wall ThetaLink HodgeTheater MeasureTheory Metric
open scoped ComplexConjugate

noncomputable section

/-! ### Archimedean factors -/

section Factor

universe u

variable {K : Type u} [Field K] [NumberField K] {v : Place K}

/-- **An `ℝ`-algebra homomorphism from a real subalgebra of `ℂ` to `ℂ` is the inclusion or its
conjugate.** -/
theorem subalgebra_algHom_eq_or_conj (S : Subalgebra ℝ ℂ) (h : S →ₐ[ℝ] ℂ) :
    (∀ s, h s = s) ∨ (∀ s, h s = conj (s : ℂ)) := by
  by_cases hI : ∃ i : S, (i : ℂ) = Complex.I
  · obtain ⟨i, hi⟩ := hI
    have hdec : ∀ s : S, s = algebraMap ℝ S (s : ℂ).re + (s : ℂ).im • i := fun s => by
      apply Subtype.ext
      rw [Subalgebra.coe_add, Subalgebra.coe_smul, hi]
      apply Complex.ext <;> simp
    have hhs : ∀ s : S, h s = ((s : ℂ).re : ℂ) + (s : ℂ).im • h i := fun s => by
      conv_lhs => rw [hdec s]
      rw [map_add, map_smul, AlgHom.commutes]
      rfl
    have hii : i * i = -1 := Subtype.ext (by simp [hi])
    have hsq : h i ^ 2 = Complex.I ^ 2 := by
      rw [Complex.I_sq, sq, ← map_mul, hii, map_neg, map_one]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
    · left
      intro s
      rw [hhs, h1]
      apply Complex.ext <;> simp
    · right
      intro s
      rw [hhs, h1]
      apply Complex.ext <;> simp
  · left
    intro s
    have him : (s : ℂ).im = 0 := by
      by_contra hne
      refine hI ⟨((s : ℂ).im)⁻¹ • (s - algebraMap ℝ S (s : ℂ).re), ?_⟩
      apply Complex.ext <;> simp [hne]
    have hs : s = algebraMap ℝ S (s : ℂ).re := by
      apply Subtype.ext
      apply Complex.ext <;> simp [him]
    rw [hs, AlgHom.commutes]
    rfl

variable (v) in
/-- **The embedding of an archimedean factor into `ℂ`.** -/
def factorEmb : ArchFactor K v →ₐ[ℝ] ℂ :=
  (archField K (archPlace K v)).val.comp (archFactorEquiv v).toAlgHom

theorem factorEmb_apply (a : ArchFactor K v) :
    factorEmb v a = ((archFactorEquiv v a : archField K (archPlace K v)) : ℂ) := rfl

theorem factorEmb_injective : Function.Injective (factorEmb v : ArchFactor K v → ℂ) :=
  fun _ _ h => (archFactorEquiv v).injective (Subtype.ext h)

theorem archAbs_eq_norm (a : ArchFactor K v) : archAbs v a = ‖factorEmb v a‖ := rfl

theorem factorEmb_algebraMap (r : ℝ) : factorEmb v (algebraMap ℝ (ArchFactor K v) r) = r :=
  (factorEmb v).commutes r

/-- An automorphism of a factor is the identity or the conjugation, read in `ℂ`. -/
theorem factorEmb_algEquiv (σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v) :
    ∃ τ : ℂ ≃ₐ[ℝ] ℂ, ∀ a, factorEmb v (σ a) = τ (factorEmb v a) := by
  rcases subalgebra_algHom_eq_or_conj _ ((factorEmb v).comp
      (σ.toAlgHom.comp (archFactorEquiv v).symm.toAlgHom)) with h | h
  · refine ⟨AlgEquiv.refl, fun a => ?_⟩
    have := h (archFactorEquiv v a)
    simpa [factorEmb_apply] using this
  · refine ⟨Complex.conjAe, fun a => ?_⟩
    have := h (archFactorEquiv v a)
    simpa [factorEmb_apply] using this

/-- **A unit-induced map of an archimedean factor**: the restriction of a unit-induced
`ℝ`-linear automorphism of `ℂ` (`ArchUnitInduced`). -/
def FactorArchUnitInduced (ψ : ArchFactor K v →ₗ[ℝ] ArchFactor K v) : Prop :=
  ∃ ψ' : ℂ ≃ₗ[ℝ] ℂ, ArchUnitInduced ψ' ∧ ∀ a, factorEmb v (ψ a) = ψ' (factorEmb v a)

variable (v) in
/-- **The log-shell of an archimedean factor**: the elements of absolute value `≤ π`. -/
def factorArchLogShell : Set (ArchFactor K v) := {a | archAbs v a ≤ Real.pi}

/-- **The factor indeterminacies `ε·σ` are unit-induced.** -/
theorem factorArchUnitInduced_archFactorMap (σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v)
    (ε : ℤˣ) : FactorArchUnitInduced (archFactorMap σ ε) := by
  obtain ⟨τ, hτ⟩ := factorEmb_algEquiv σ
  refine ⟨signAlgEquiv ε τ, (archPolyIso_signAlgEquiv ε τ).archUnitInduced, fun a => ?_⟩
  rw [archFactorMap_apply, map_smul, hτ, signAlgEquiv_apply, Complex.real_smul]
  push_cast
  rfl

/-- The factor indeterminacies preserve the factor log-shell. -/
theorem image_factorArchLogShell_archFactorMap (σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v)
    (ε : ℤˣ) : archFactorMap σ ε '' factorArchLogShell v = factorArchLogShell v := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    change archAbs v _ ≤ _
    rw [archAbs_archFactorMap]
    exact ha
  · intro hb
    refine ⟨archFactorMap σ.symm ε b, ?_, ?_⟩
    · change archAbs v _ ≤ _
      rw [archAbs_archFactorMap]
      exact hb
    · rw [archFactorMap_apply, archFactorMap_apply, map_smul, AlgEquiv.apply_symm_apply,
        smul_smul]
      rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

/-- **Converse**: a unit-induced map of a factor preserving the factor log-shell is a factor
indeterminacy `ε·σ`. -/
theorem exists_archFactorMap_of_factorArchUnitInduced {ψ : ArchFactor K v →ₗ[ℝ] ArchFactor K v}
    (h : FactorArchUnitInduced ψ) (hls : ψ '' factorArchLogShell v = factorArchLogShell v) :
    ∃ σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v, ∃ ε : ℤˣ, ψ = archFactorMap σ ε := by
  obtain ⟨ψ', hu, hψ⟩ := h
  have hre := re_apply_of_archUnitInduced hu
  -- `|λ| = 1` from the log-shell of the factor
  have hpi := Real.pi_pos
  set a₀ := algebraMap ℝ (ArchFactor K v) Real.pi
  have he₀ : factorEmb v a₀ = Real.pi := factorEmb_algebraMap _
  have hmem : a₀ ∈ factorArchLogShell v := by
    change archAbs v a₀ ≤ _
    rw [archAbs_eq_norm, he₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  have habs : |(ψ' 1).re| = 1 := by
    have h1 : ψ a₀ ∈ factorArchLogShell v := by
      rw [← hls]
      exact ⟨_, hmem, rfl⟩
    have h1' : |(ψ' 1).re| * Real.pi ≤ Real.pi := by
      change archAbs v _ ≤ _ at h1
      rw [archAbs_eq_norm, hψ, he₀] at h1
      have := (Complex.abs_re_le_norm _).trans h1
      rwa [hre, Complex.ofReal_re, abs_mul, abs_of_pos hpi] at this
    rw [← hls] at hmem
    obtain ⟨z, hz, hz'⟩ := hmem
    have hre' : (ψ' 1).re * (factorEmb v z).re = Real.pi := by
      rw [← hre, ← hψ, hz', he₀, Complex.ofReal_re]
    have hzre : |(factorEmb v z).re| ≤ Real.pi := by
      change archAbs v z ≤ _ at hz
      rw [archAbs_eq_norm] at hz
      exact (Complex.abs_re_le_norm _).trans hz
    have h2 : Real.pi ≤ |(ψ' 1).re| * Real.pi := by
      calc Real.pi = |(ψ' 1).re * (factorEmb v z).re| := by rw [hre', abs_of_pos hpi]
        _ = |(ψ' 1).re| * |(factorEmb v z).re| := abs_mul _ _
        _ ≤ |(ψ' 1).re| * Real.pi := mul_le_mul_of_nonneg_left hzre (abs_nonneg _)
    have h3 : |(ψ' 1).re| ≤ 1 := le_of_mul_le_mul_right (by linarith) hpi
    have h4 : 1 ≤ |(ψ' 1).re| := le_of_mul_le_mul_right (by linarith) hpi
    linarith
  obtain ⟨ε, τ, hετ⟩ := (archPolyIso_iff_sign_algEquiv ψ').1 (archPolyIso_of_abs hu habs)
  have hττ : ∀ z, τ (τ z) = z := by
    intro z
    rcases Complex.real_algHom_eq_id_or_conj τ.toAlgHom with e | e
    · have h1 : ∀ w, τ w = w := fun w => by simpa using AlgHom.congr_fun e w
      rw [h1, h1]
    · have h1 : ∀ w, τ w = conj w := fun w => by simpa using AlgHom.congr_fun e w
      rw [h1, h1, Complex.conj_conj]
  have hεε := intCast_units_mul_self ε
  -- `σ = ε·ψ`, read in `ℂ` as `τ`
  set σl : ArchFactor K v →ₗ[ℝ] ArchFactor K v := ((ε : ℤ) : ℝ) • ψ with hσl
  have hσe : ∀ a, factorEmb v (σl a) = τ (factorEmb v a) := fun a => by
    rw [hσl, LinearMap.smul_apply, map_smul, hψ, hετ, Complex.real_smul]
    push_cast
    rw [← mul_assoc, hεε, one_mul]
  have hinv : Function.Involutive σl := fun a =>
    factorEmb_injective (by rw [hσe, hσe, hττ])
  let σe : ArchFactor K v ≃ₗ[ℝ] ArchFactor K v := LinearEquiv.ofInvolutive σl hinv
  have hσe' : ∀ a, σe a = σl a := fun _ => rfl
  let σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v := AlgEquiv.ofLinearEquiv σe
    (factorEmb_injective (by rw [hσe', hσe, map_one, map_one]))
    (fun a b => factorEmb_injective (by
      rw [hσe' (a * b), hσe, map_mul (factorEmb v) a b, map_mul τ,
        map_mul (factorEmb v) (σe a) (σe b), hσe' a, hσe' b, hσe, hσe]))
  refine ⟨σ, ε, LinearMap.ext fun a => ?_⟩
  rw [archFactorMap_apply]
  change ψ a = ((ε : ℤ) : ℝ) • σl a
  rw [hσl, LinearMap.smul_apply, smul_smul]
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

/-- **Precise characterization at an archimedean factor**: a map of the factor is unit-induced
and preserves the factor log-shell iff it is a factor indeterminacy `ε·σ` (IUT III,
Proposition 1.2(vii), Theorem 3.11 (Ind2) at `V^arc`). -/
theorem factorArchUnitInduced_iff (ψ : ArchFactor K v →ₗ[ℝ] ArchFactor K v) :
    (FactorArchUnitInduced ψ ∧ ψ '' factorArchLogShell v = factorArchLogShell v) ↔
      ∃ σ : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v, ∃ ε : ℤˣ, ψ = archFactorMap σ ε := by
  constructor
  · rintro ⟨h, hls⟩
    exact exists_archFactorMap_of_factorArchUnitInduced h hls
  · rintro ⟨σ, ε, rfl⟩
    exact ⟨factorArchUnitInduced_archFactorMap σ ε, image_factorArchLogShell_archFactorMap σ ε⟩

end Factor

/-! ### Archimedean packets -/

section Packet

universe u

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι] (c : ι → Place K)

/-- **The archimedean indeterminacy class is the class of tensor products of unit-induced,
log-shell preserving factor maps.** -/
theorem mem_archIndAut_iff (f : Tensor K .infinite c → Tensor K .infinite c) :
    f ∈ archIndAut c ↔ ∃ ψ : ∀ j, ArchFactor K (c j) →ₗ[ℝ] ArchFactor K (c j),
      f = ⇑(PiTensorProduct.map ψ) ∧ ∀ j, FactorArchUnitInduced (ψ j) ∧
        ψ j '' factorArchLogShell (c j) = factorArchLogShell (c j) := by
  constructor
  · rintro ⟨σ, ε, rfl⟩
    exact ⟨fun j => archFactorMap (σ j) (ε j), rfl,
      fun j => (factorArchUnitInduced_iff _).2 ⟨σ j, ε j, rfl⟩⟩
  · rintro ⟨ψ, rfl, hψ⟩
    choose σ ε hσε using fun j => (factorArchUnitInduced_iff (ψ j)).1 (hψ j)
    refine ⟨σ, ε, ?_⟩
    have : ψ = fun j => archFactorMap (σ j) (ε j) := funext hσε
    subst this
    rfl

/-- The tensor-product metric is definite. -/
theorem eq_zero_of_archTensorInner_self {x : Tensor K .infinite c}
    (h : archTensorInner c x x = 0) : x = 0 := by
  rw [archTensorInner_self] at h
  have hp : ∀ p, (archTensorBasis c).repr x p = 0 := fun p => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => sq_nonneg _)).1 h p
      (Finset.mem_univ _)
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  exact (archTensorBasis c).repr.injective (by ext p; simp [hp])

variable (σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j)) (ε : ι → ℤˣ)

/-- **The indeterminacy automorphisms are injective** (isometries of a definite metric). -/
theorem archIndMap_injective : Function.Injective (archIndMap c σ ε) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply eq_zero_of_archTensorInner_self c
  rw [← archTensorInner_archIndMap c σ ε, hx, map_zero]

/-- `⊗_j (ε_j·σ_j)` as a linear automorphism of the packet. -/
def archIndEquiv : Tensor K .infinite c ≃ₗ[ℝ] Tensor K .infinite c :=
  LinearEquiv.ofInjectiveEndo (archIndMap c σ ε) (archIndMap_injective c σ ε)

theorem coe_archIndEquiv : ⇑(archIndEquiv c σ ε) = archIndMap c σ ε := rfl

/-- **The indeterminacy automorphisms map the archimedean log-shell onto itself.** -/
theorem image_archLogShell_archIndMap :
    archIndMap c σ ε '' archLogShell c = archLogShell c := by
  refine (archIndAut_image_archLogShell c _ ⟨σ, ε, rfl⟩).antisymm fun y hy => ?_
  refine ⟨(archIndEquiv c σ ε).symm y, ?_, (archIndEquiv c σ ε).apply_symm_apply y⟩
  rw [mem_archLogShell, ← archTensorInner_archIndMap c σ ε, ← coe_archIndEquiv,
    LinearEquiv.apply_symm_apply]
  exact hy

/-- **The indeterminacy automorphisms have determinant `±1`.** -/
theorem abs_det_archIndMap : |LinearMap.det (archIndMap c σ ε)| = 1 := by
  have h := Measure.addHaar_image_linearMap (haar .infinite c) (archIndMap c σ ε)
    (archLogShell c)
  rw [image_archLogShell_archIndMap] at h
  have hpos := haar_archLogShell_pos c
  have hfin := (isCompact_archLogShell c).measure_lt_top (μ := haar .infinite c)
  have h1 : ENNReal.ofReal |LinearMap.det (archIndMap c σ ε)| = 1 := by
    refine (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 ?_
    rw [← h, one_mul]
  exact ENNReal.ofReal_eq_one.1 h1

/-- **The indeterminacy automorphisms preserve the Haar measure.** -/
theorem haar_image_archIndMap (S : Set (Tensor K .infinite c)) :
    haar .infinite c (archIndMap c σ ε '' S) = haar .infinite c S := by
  rw [Measure.addHaar_image_linearMap, abs_det_archIndMap, ENNReal.ofReal_one, one_mul]

/-- **The indeterminacy automorphisms preserve log-volumes.** -/
theorem componentVol_image_archIndMap (S : Set (Tensor K .infinite c)) :
    componentVol .infinite c (archIndMap c σ ε '' S) = componentVol .infinite c S := by
  unfold componentVol
  rw [haar_image_archIndMap]

/-- **The indeterminacy automorphisms preserve admissibility.** -/
theorem image_mem_admissible_archIndMap {S : Set (Tensor K .infinite c)}
    (hS : S ∈ admissible .infinite c) : archIndMap c σ ε '' S ∈ admissible .infinite c := by
  let e := (archIndEquiv c σ ε).toContinuousLinearEquiv
  have he : ⇑e = archIndMap c σ ε := rfl
  obtain ⟨hne, hcl, hms, hpos, hfin⟩ := hS
  refine ⟨hne.image _, ?_, ?_, ?_, ?_⟩
  · rw [← he]
    have h : e '' closure S = closure (e '' S) := e.toHomeomorph.image_closure S
    rw [← h]
    exact hcl.image e.continuous
  · rw [← he]
    exact e.toHomeomorph.toMeasurableEquiv.measurableSet_image.2 hms
  · rwa [haar_image_archIndMap]
  · rwa [haar_image_archIndMap]

theorem archFactorMap_mul {v : Place K} (σ σ' : ArchFactor K v ≃ₐ[ℝ] ArchFactor K v)
    (ε ε' : ℤˣ) :
    archFactorMap (σ * σ') (ε * ε') = (archFactorMap σ ε).comp (archFactorMap σ' ε') := by
  refine LinearMap.ext fun a => ?_
  rw [LinearMap.comp_apply, archFactorMap_apply, archFactorMap_apply, archFactorMap_apply,
    map_smul, AlgEquiv.mul_apply, smul_smul, Units.val_mul, Int.cast_mul]

theorem archIndMap_mul (σ' : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j))
    (ε' : ι → ℤˣ) :
    archIndMap c (σ * σ') (ε * ε') = (archIndMap c σ ε).comp (archIndMap c σ' ε') := by
  unfold archIndMap
  rw [← PiTensorProduct.map_comp]
  congr 1
  funext j
  exact archFactorMap_mul _ _ _ _

theorem archIndMap_one : archIndMap c (1 : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j))
    (1 : ι → ℤˣ) = LinearMap.id := by
  unfold archIndMap
  rw [← PiTensorProduct.map_id]
  congr 1
  funext j
  refine LinearMap.ext fun a => ?_
  simp [archFactorMap_apply]

end Packet


/-! ### All places: Kummer identifications at `V^non ∪ V^arc` -/

variable (D : InitialThetaData.{0})

/-- The factor data `(σ_j, ε_j)` of an archimedean Kummer identification of the component of
capsule `i` at the tuple `c` of archimedean places. -/
abbrev ArcDatum (i : Fin (nC D))
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod .infinite) : Type :=
  (∀ j, ArchFactor D.Kt (LocalTheory.tuple D.placeSect _ c j) ≃ₐ[ℝ]
      ArchFactor D.Kt (LocalTheory.tuple D.placeSect _ c j)) ×
    (InitialThetaData.Lab (nC D) i → ℤˣ)

/-- **An archimedean Kummer identification of the container**: on every archimedean tensor
component, the factor indeterminacies `ε_j·σ_j` (by `factorArchUnitInduced_iff`, exactly the
unit-induced, log-shell preserving factor maps), acting by `⊗_j (ε_j·σ_j)`. -/
abbrev ArcScaling : Type :=
  ∀ (i : Fin (nC D)) (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod .infinite),
    ArcDatum D i c

/-- **Kummer identifications at all places** `V^non ∪ V^arc`. -/
abbrev FullScaling : Type := Scaling D × ArcScaling D

/-- The archimedean action on the packet of capsule `i`. -/
def arcMap (W : ArcScaling D) (i : Fin (nC D)) :
    (LocalTheory.packet D.placeSect (InitialThetaData.Lab (nC D) i) .infinite).Total →
      (LocalTheory.packet D.placeSect (InitialThetaData.Lab (nC D) i) .infinite).Total :=
  fun x c => archIndMap (LocalTheory.tuple D.placeSect _ c) (W i c).1 (W i c).2 (x c)

theorem arcMap_mul (a b : ArcScaling D) (i : Fin (nC D)) :
    arcMap D (a * b) i = arcMap D a i ∘ arcMap D b i := by
  funext x c
  change archIndMap _ ((a i c).1 * (b i c).1) ((a i c).2 * (b i c).2) (x c) = _
  rw [archIndMap_mul]
  rfl

theorem arcMap_one (i : Fin (nC D)) : arcMap D 1 i = id := by
  funext x c
  change archIndMap _ 1 1 (x c) = _
  rw [archIndMap_one]
  rfl

/-- The packet regions of `W·R`. -/
def fullActRegion (W : FullScaling D) (i : Fin (VC D).proc.length)
    (R : (VC D).AdmissibleRegion i) : ∀ vQ : RationalPlace, Set ((VC D).packet i vQ).Total
  | .finite p => actMap D W.1 i p '' R.region (.finite p)
  | .infinite => arcMap D W.2 i '' R.region .infinite

/-- `W·R` at capsule `i`. -/
def fullActAt (W : FullScaling D) (i : Fin (VC D).proc.length) (R : (VC D).AdmissibleRegion i) :
    (VC D).AdmissibleRegion i where
  region := fullActRegion D W i R
  finiteSupport := by
    refine ((actAt D W.1 i R).finiteSupport.union (Set.finite_singleton .infinite)).subset
      fun vQ hvQ => ?_
    rcases vQ with p | _
    · exact Or.inl hvQ
    · exact Or.inr rfl

/-- **The region `S` transformed by the Kummer identification `W` at all places.** -/
def fullAct (W : FullScaling D) (S : Region D) : Region D := fun i => fullActAt D W i (S i)

theorem fullAct_region_finite (W : FullScaling D) (S : Region D) (i : Fin (nC D))
    (p : Nat.Primes) : (fullAct D W S i).region (.finite p) = (act D W.1 S i).region (.finite p) :=
  rfl

theorem fullAct_mul (a b : FullScaling D) (S : Region D) :
    fullAct D (a * b) S = fullAct D a (fullAct D b S) := by
  funext i
  refine admissibleRegion_ext D (funext fun vQ => ?_)
  rcases vQ with p | _
  · change actMap D (a.1 * b.1) i p '' _ = actMap D a.1 i p '' (actMap D b.1 i p '' _)
    rw [actMap_mul, Set.image_comp]
  · change arcMap D (a.2 * b.2) i '' _ = arcMap D a.2 i '' (arcMap D b.2 i '' _)
    rw [arcMap_mul, Set.image_comp]

theorem fullAct_one (S : Region D) : fullAct D 1 S = S := by
  funext i
  refine admissibleRegion_ext D (funext fun vQ => ?_)
  rcases vQ with p | _
  · change actMap D 1 i p '' _ = _
    rw [actMap_one, Set.image_id]
  · change arcMap D 1 i '' _ = _
    rw [arcMap_one, Set.image_id]

/-- **`W·S` is adelic for adelic `S`.** -/
theorem isAdelic_fullAct (W : FullScaling D) {S : Region D} (hS : IsAdelic D S) :
    IsAdelic D (fullAct D W S) := by
  intro i vQ
  rcases vQ with p | _
  · exact isAdelic_act D W.1 hS i (.finite p)
  · obtain ⟨fam, hfam, hR⟩ := hS i .infinite
    refine ⟨fun c => archIndMap _ (W.2 i c).1 (W.2 i c).2 '' fam c,
      fun c => image_mem_admissible_archIndMap _ _ _ (hfam c), ?_⟩
    change arcMap D W.2 i '' (S i).region .infinite = _
    rw [hR]
    ext x
    simp only [DirectSumPresentation.mem_productRegion, Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩ c
      exact ⟨y c, hy c, rfl⟩
    · intro hx
      choose y hy hxy using hx
      exact ⟨y, hy, funext hxy⟩

/-- **The archimedean components do not change log-volumes**: `log-vol(W·S) = log-vol(W_non·S)`
for every region `S`. -/
theorem logVol_fullAct (W : FullScaling D) (S : Region D) :
    logVol D (fullAct D W S) = logVol D (act D W.1 S) := by
  unfold logVol LogVolumeData.processionVol
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold LogVolumeData.globalVol
  refine finsum_congr fun vQ => ?_
  rcases vQ with p | _
  · rfl
  · change (LocalTheory.vol D.placeSect (nC D)).packetVol i .infinite
        (arcMap D W.2 i '' (S i).region .infinite) =
      (LocalTheory.vol D.placeSect (nC D)).packetVol i .infinite ((S i).region .infinite)
    rw [LocalTheory.packetVol_eq, LocalTheory.packetVol_eq]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    have h : LocalTheory.proj D.placeSect .infinite c (arcMap D W.2 i '' (S i).region .infinite) =
        archIndMap _ (W.2 i c).1 (W.2 i c).2 ''
          LocalTheory.proj D.placeSect .infinite c ((S i).region .infinite) := by
      unfold LocalTheory.proj
      rw [Set.image_image, Set.image_image]
      rfl
    exact (congrArg (LocalTheory.componentVol D.Kt .infinite _) h).trans
      (componentVol_image_archIndMap _ _ _ _)

/-- **`log-vol(W·S) = shift(W_non) + log-vol(S)`** for adelic `S`. -/
theorem logVol_fullAct_adelic (W : FullScaling D) {S : Region D} (hS : IsAdelic D S) :
    logVol D (fullAct D W S) = shift D W.1 + logVol D S := by
  rw [logVol_fullAct, logVol_act D _ hS]

/-! ### Kummer data at all places on the log-theta-lattice -/

variable {D}

/-- **Kummer data at every vertex and every place**: nonarchimedean components arising from
automorphisms of the unit groups (`AnabelianKummer`), archimedean components given by the factor
indeterminacies (the unit-induced, log-shell preserving factor maps). -/
structure FullKummer (L : LogThetaLattice D) where
  /-- The Kummer data at `V^non`. -/
  non : AnabelianKummer L
  /-- The Kummer identifications at `V^arc`. -/
  arc : ℤ × ℤ → ArcScaling D

/-- **Galois-induced Kummer data at every vertex and every place**: at `V^non` induced by
automorphisms of the local Galois groups (`GalKummer`); at `V^arc` by `Gal(ℂ/ℝ)` on the factors
(all signs `ε_j = 1`). -/
structure FullGalKummer (L : LogThetaLattice D) where
  /-- The Kummer data at `V^non`. -/
  non : GalKummer L
  /-- The Kummer identifications at `V^arc`. -/
  arc : ℤ × ℤ → ArcScaling D
  /-- They are Galois automorphisms of the factors. -/
  gal : ∀ a i c j, (arc a i c).2 j = 1

namespace FullKummer

variable {L : LogThetaLattice D} (K : FullKummer L)

/-- The Kummer identification of the vertex `a`, at all places. -/
def kum (a : ℤ × ℤ) : FullScaling D := (K.non.kum a, K.arc a)

/-- The `LatticeKummer` data at `V^non` (unit-inducedness discharged). -/
def toLatticeKummer : LatticeKummer L := K.non.toLatticeKummer

/-- **The archimedean factor maps are unit-induced and log-shell preserving.** -/
theorem arc_factor (a : ℤ × ℤ) (i : Fin (nC D))
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod .infinite) (j) :
    FactorArchUnitInduced (archFactorMap ((K.arc a i c).1 j) ((K.arc a i c).2 j)) ∧
      archFactorMap ((K.arc a i c).1 j) ((K.arc a i c).2 j) ''
        factorArchLogShell (LocalTheory.tuple D.placeSect _ c j) =
          factorArchLogShell (LocalTheory.tuple D.placeSect _ c j) :=
  (factorArchUnitInduced_iff _).2 ⟨_, _, rfl⟩

/-- The archimedean Kummer identifications preserve the archimedean log-shells. -/
theorem arc_image_archLogShell (a : ℤ × ℤ) (i : Fin (nC D))
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod .infinite) :
    archIndMap _ (K.arc a i c).1 (K.arc a i c).2 '' archLogShell (LocalTheory.tuple D.placeSect _ c)
      = archLogShell (LocalTheory.tuple D.placeSect _ c) :=
  image_archLogShell_archIndMap _ _ _

/-- **The transport `κ_b ∘ κ_a⁻¹` at all places.** -/
def transport (a b : ℤ × ℤ) (U : Region D) : Region D := fullAct D (K.kum b * (K.kum a)⁻¹) U

theorem transport_trans (a b c : ℤ × ℤ) (U : Region D) :
    K.transport b c (K.transport a b U) = K.transport a c U := by
  rw [transport, transport, transport, ← fullAct_mul]
  congr 1
  group

theorem transport_self (a : ℤ × ℤ) (U : Region D) : K.transport a a U = U := by
  rw [transport, mul_inv_cancel, fullAct_one]

theorem isAdelic_transport (a b : ℤ × ℤ) {U : Region D} (hU : IsAdelic D U) :
    IsAdelic D (K.transport a b U) :=
  isAdelic_fullAct D _ hU

/-- The transport at all places shifts log-volumes by the distortion of the `V^non` model. -/
theorem logVol_transport_distortion (a b : ℤ × ℤ) {U : Region D} (hU : IsAdelic D U) :
    logVol D (K.transport a b U) = logVol D U + K.toLatticeKummer.model.distortion a b := by
  rw [transport, logVol_fullAct_adelic D _ hU]
  change shift D (K.non.kum b * (K.non.kum a)⁻¹) + _ = _
  rw [shift_mul, shift_inv]
  change _ = _ + (shift D (K.non.kum b) - shift D (K.non.kum a))
  ring

/-- **The distortion vanishes at all places**: the transport between any two vertices of the
lattice, at `V^non ∪ V^arc`, preserves the log-volume of every adelic region. -/
theorem logVol_transport (a b : ℤ × ℤ) {U : Region D} (hU : IsAdelic D U) :
    logVol D (K.transport a b U) = logVol D U := by
  rw [K.logVol_transport_distortion a b hU, toLatticeKummer, K.non.distortion_eq_zero, add_zero]

theorem distortion_eq_zero (a b : ℤ × ℤ) : K.toLatticeKummer.model.distortion a b = 0 :=
  K.non.distortion_eq_zero a b

/-- **Step (xi) is the Scholze–Stix inequality** for Kummer data at all places. -/
theorem xi_iff_ss : XiPrinciple K.toLatticeKummer ↔ SSIneq D :=
  K.non.xi_iff_ss

variable (L) in
/-- The trivial Kummer data at all places. -/
def trivial : FullKummer L := ⟨(GalKummer.trivial L).toAnabelianKummer, 1⟩

variable (L) in
/-- **Alien Kummer data at all places**: P20's alien data at `V^non` (`AnabelianKummer.alt`) and
the inversion of the units (`ε = −1` at the label `1`, i.e. `x ↦ −x`) at `V^arc` at the vertices
with `n + m` odd. -/
def alt : FullKummer L where
  non := AnabelianKummer.alt L
  arc a := fun i _ => (1, if Even (a.1 + a.2) then 1 else Pi.mulSingle (labOne D i) (-1))

end FullKummer

namespace FullGalKummer

variable {L : LogThetaLattice D} (K : FullGalKummer L)

/-- Galois-induced Kummer data at all places are Kummer data at all places. -/
def toFullKummer : FullKummer L := ⟨K.non.toAnabelianKummer, K.arc⟩

/-- **The archimedean components are Galois automorphisms of the packets.** -/
theorem arc_mem_galAut (a : ℤ × ℤ) (i : Fin (nC D))
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod .infinite) :
    ⇑(archIndMap _ (K.arc a i c).1 (K.arc a i c).2) ∈
      galAut .infinite (LocalTheory.tuple D.placeSect _ c) := by
  refine ⟨(K.arc a i c).1, funext fun x => ?_⟩
  rw [archIndMap_apply]
  have h : ∏ j, (K.arc a i c).2 j = 1 := Finset.prod_eq_one fun j _ => K.gal a i c j
  rw [h]
  simp

theorem xi_iff_ss : XiPrinciple K.toFullKummer.toLatticeKummer ↔ SSIneq D :=
  K.toFullKummer.xi_iff_ss

variable (L) in
/-- The trivial Galois-induced Kummer data at all places. -/
def trivial : FullGalKummer L := ⟨GalKummer.trivial L, 1, fun _ _ _ _ => rfl⟩

end FullGalKummer

/-- **`classicalABC_of_thm311` for Kummer data at all places.** -/
theorem classicalABC_of_thm311_full (L : ∀ D : InitialThetaData.{0}, LogThetaLattice D)
    (K : ∀ D, FullKummer (L D)) (h : ∀ D, Thm311 (L D) (K D).toLatticeKummer)
    (hx : ∀ D, XiPrinciple (K D).toLatticeKummer) : ClassicalABC :=
  classicalABC_of_thm311_anabelian L (fun D => (K D).non) h hx

/-- Step (xi) for lattices with Galois-induced Kummer data at all places implies
`ClassicalABC`; by `FullGalKummer.xi_iff_ss` this hypothesis is `SSIneq`. -/
theorem classicalABC_of_xi_full
    (hx : ∀ D : InitialThetaData.{0}, ∃ (L : LogThetaLattice D) (K : FullGalKummer L),
      XiPrinciple K.toFullKummer.toLatticeKummer) : ClassicalABC :=
  classicalABC_of_xi_gal fun D => by
    obtain ⟨L, K, h⟩ := hx D
    exact ⟨L, K.non, h⟩

end

end LogLink

end Iut
