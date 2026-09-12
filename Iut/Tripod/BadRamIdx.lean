/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.Unramified
import Iut.Tower.InertiaBound

/-!
# The ramification of `K = F(E[ℓ])` over `F` at the places away from `2·ℓ`

For a point `λ` of the tripod, a prime `ℓ ≥ 7` and a place `v` of `K = F_λ(E_λ[ℓ])` of residue
characteristic `p ∉ {2, ℓ}` over the place `w` of `F = F_λ`:

* at a bad place (`w(λ) ≠ 1` or `w(λ − 1) ≠ 1`), the inertia group `I_v ⊆ Gal(K/F)` acts
  unipotently on `E(K)[ℓ]` (`Iut.MultKernel.iterate_map_eq_self`, for the model
  `E_μ`, `μ ∈ {λ, 1 − λ, 1/λ}`, with `v(μ) < 1`, transported along the changes of variables
  `⟨√−1, 1, 0, 0⟩`, `⟨√λ, 0, 0, 0⟩` whose coefficients lie in `F`), so `σ^ℓ = 1` for
  `σ ∈ I_v` (`Iut.Tripod.inertia_pow_eq_one`); as `|I_v|` divides
  `[K : F] ∣ |GL₂(𝔽_ℓ)| = ℓ(ℓ² − 1)(ℓ − 1)`, `e(v/w) = |I_v| ≤ ℓ`;
* at a good place `e(v/w) = 1` (`Iut.Tripod.relRamIdx_torsionField_eq_one`).

Hence `e(v/w) ≤ ℓ` (`Iut.Tripod.relRamIdx_torsionField_le`).
-/

namespace Iut.Tripod

open Iut Iut.EllipticCurveData NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  WeierstrassCurve WeierstrassCurve.Affine

open scoped Classical

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK

variable (P : CurveProviders) (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
  (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw)

set_option quotPrecheck false in
/-- The torsion field `K` of the datum of `x` and `ℓ`. -/
local notation "KF" => ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField

/-- `[K : F]` divides `|GL₂(𝔽_ℓ)|`. -/
theorem finrank_torsionField_dvd :
    Module.finrank (P.curve x).F ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField ∣
      (ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ) := by
  set Pr := primeDataOf P x hℓ h7 hsl hP2
  let H : ClosedSubgroup ((P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar) :=
    ⟨Pr.rep.ker, Subgroup.isClosed_of_isOpen _ Pr.ker_isOpen⟩
  have h1 : Module.finrank (P.curve x).F ↥Pr.torsionField = Pr.rep.ker.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index]
    change (IntermediateField.fixedField H.1).fixingSubgroup.index = H.1.index
    rw [InfiniteGalois.fixingSubgroup_fixedField H]
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rw [h1, Subgroup.index_ker, ← card_GL_two_of_prime ℓ hℓ]
  exact Subgroup.card_subgroup_dvd_card _

section Bad

variable [NumberField ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField]
  (v : FinitePlace ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField)

omit [NumberField ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField] in
/-- The Legendre coefficients of `E_λ` base changed to `K`. -/
lemma legendreCoeffs_EK :
    (Affine.baseChange (P.curve x).E ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField).a₁ = 0 ∧
    (Affine.baseChange (P.curve x).E ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField).a₂ =
      -(1 + algebraMap (P.curve x).F _ (genC' P x)) ∧
    (Affine.baseChange (P.curve x).E ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField).a₃ = 0 ∧
    (Affine.baseChange (P.curve x).E ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField).a₄ =
      algebraMap (P.curve x).F _ (genC' P x) ∧
    (Affine.baseChange (P.curve x).E ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField).a₆ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change algebraMap (P.curve x).F _ (legendre (genC' P x)).a₁ = 0
    simp [legendre]
  · change algebraMap (P.curve x).F _ (legendre (genC' P x)).a₂ = _
    simp [legendre]
  · change algebraMap (P.curve x).F _ (legendre (genC' P x)).a₃ = 0
    simp [legendre]
  · change algebraMap (P.curve x).F _ (legendre (genC' P x)).a₄ = _
    simp [legendre]
  · change algebraMap (P.curve x).F _ (legendre (genC' P x)).a₆ = 0
    simp [legendre]

set_option maxHeartbeats 1000000 in
/-- **The inertia group at a bad place acts unipotently on `E(K)[ℓ]`**: `σ^ℓ = 1` for every
`σ` in the inertia group of a place `v` of residue characteristic `∉ {2, ℓ}` over a bad place
of `F`. -/
theorem inertia_pow_eq_one (h2 : residueChar v ≠ 2) (hpℓ : residueChar v ≠ ℓ)
    (hbad : (placeUnder (k := (P.curve x).F) v).maximalIdeal.valuation _ (genC' P x) ≠ 1 ∨
      (placeUnder (k := (P.curve x).F) v).maximalIdeal.valuation _ (genC' P x - 1) ≠ 1)
    (σ : ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField ≃ₐ[(P.curve x).F]
      ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField)
    (hσ : σ ∈ v.maximalIdeal.asIdeal.inertia
      (↥(primeDataOf P x hℓ h7 hsl hP2).torsionField ≃ₐ[(P.curve x).F]
        ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField)) :
    σ ^ ℓ = 1 := by
  have hvw : FinitePlace.LiesOver v (placeUnder (k := (P.curve x).F) v) := liesOver_placeUnder v
  set vK := v.maximalIdeal.valuation KF with hvK
  set μ : KF := algebraMap (P.curve x).F KF (genC' P x) with hμ_def
  have h2' : vK 2 = 1 := valuation_two_eq_one v h2
  have hℓ' : vK (ℓ : KF) = 1 := (valuation_natCast_eq_one_iff v hℓ).2 hpℓ
  have hodd : Odd ℓ := hℓ.odd_of_ne_two (by omega)
  have hσ' : ∀ z : KF, vK z ≤ 1 → vK (σ z - z) < 1 := fun z hz =>
    valuation_sub_lt_one_of_mem_inertia hσ hz
  have hvσ : ∀ z : KF, vK (σ z) = vK z := fun z => valuation_map_eq_of_mem_inertia hσ z
  obtain ⟨hE₁, hE₂, hE₃, hE₄, hE₆⟩ := legendreCoeffs_EK P x hℓ h7 hsl hP2
  -- the model `E_μ'` with `v(μ') < 1`, `μ' ∈ {λ, 1 − λ, 1/λ}`, and the conjugate action on it
  suffices key : ∀ Q : (Affine.baseChange (P.curve x).E KF).Point, ℓ • Q = 0 →
      (⇑(Point.map (W' := (P.curve x).E) (S := (P.curve x).F)
        (σ : KF →ₐ[(P.curve x).F] KF)))^[ℓ] Q = Q by
    refine (primeDataOf P x hℓ h7 hsl hP2).eq_one_of_forall_torsion (σ ^ ℓ) fun Q hQ => ?_
    change Point.map (W' := (P.curve x).E) (S := (P.curve x).F)
      ((σ ^ ℓ : KF ≃ₐ[(P.curve x).F] KF) : KF →ₐ[(P.curve x).F] KF) Q = Q
    rw [Affine.Point.map_pow]
    exact key Q hQ
  have hφ : ∀ (a b : KF) (h : (Affine.baseChange (P.curve x).E KF).Nonsingular a b),
      ∃ h' : (Affine.baseChange (P.curve x).E KF).Nonsingular (σ a) (σ b),
        Point.map (W' := (P.curve x).E) (S := (P.curve x).F) (σ : KF →ₐ[(P.curve x).F] KF)
          (Point.some a b h) = Point.some (σ a) (σ b) h' :=
    fun a b h => ⟨_, Point.map_some _ h⟩
  have hψ : ReductionKernel.DivPolyHyp (Affine.baseChange (P.curve x).E KF) := by
    rw [eq_legendre_of_coeffs hE₁ hE₂ hE₃ hE₄ hE₆]
    exact divPolyLegendreHyp _ _
  -- the three cases
  rcases lt_trichotomy (vK μ) 1 with hμ | hμ | hμ
  · -- `v(λ) < 1`: the Legendre model itself
    intro Q hQ
    exact MultKernel.iterate_map_eq_self vK hE₁ hE₂ hE₃ hE₄ hE₆ (σ : KF →+* KF) hμ h2'
      (σ.commutes _) hσ' hvσ hψ hodd hℓ' _ hφ Q hQ
  · -- `v(λ) = 1`, so `v(λ − 1) < 1`: the model `E_{1−λ} = ⟨√−1, 1, 0, 0⟩ • E_λ`
    have hμ1 : vK (1 - μ) < 1 := by
      have hl1 : (placeUnder (k := (P.curve x).F) v).maximalIdeal.valuation _ (genC' P x) = 1 :=
        (valuation_algebraMap_eq_one_iff hvw _).mp hμ
      have hne : (placeUnder (k := (P.curve x).F) v).maximalIdeal.valuation _
          (genC' P x - 1) ≠ 1 := by
        rcases hbad with hb | hb
        · exact absurd hl1 hb
        · exact hb
      have hle : (placeUnder (k := (P.curve x).F) v).maximalIdeal.valuation _
          (genC' P x - 1) ≤ 1 :=
        (Valuation.map_sub _ _ _).trans (max_le hl1.le (by rw [map_one]))
      have hlt := (valuation_algebraMap_lt_one_iff hvw _).mpr (lt_of_le_of_ne hle hne)
      rw [map_sub, map_one] at hlt
      rw [Valuation.map_sub_swap]
      exact hlt
    set i : KF := algebraMap (P.curve x).F KF (sqrtNegOne' x.1) with hi_def
    have hi : i ^ 2 = -1 := by
      have hsq : (sqrtNegOne' x.1 : (P.curve x).F) ^ 2 = -1 := sqrtNegOne'_sq x.1
      rw [hi_def, ← map_pow]
      exact (congrArg _ hsq).trans ((map_neg _ _).trans (congrArg Neg.neg (map_one _)))
    have hi0 : i ≠ 0 := fun h0 => by
      rw [h0, zero_pow two_ne_zero, eq_comm, neg_eq_zero] at hi
      exact one_ne_zero hi
    set C : VariableChange KF := ⟨Units.mk0 i hi0, 1, 0, 0⟩ with hC
    obtain ⟨hC₁, hC₂, hC₃, hC₄, hC₆⟩ := legendreCoeffs_vc_one_sub hE₁ hE₂ hE₃ hE₄ hE₆ hi hi0
    set e := Anabelian.vcEquiv C (Affine.baseChange (P.curve x).E KF) with he
    set φ' := e.toAddMonoidHom.comp
      ((Point.map (W' := (P.curve x).E) (S := (P.curve x).F)
        (σ : KF →ₐ[(P.curve x).F] KF)).comp e.symm.toAddMonoidHom) with hφ'
    have hφ'' := exists_vcEquiv_map_eq C (Affine.baseChange (P.curve x).E KF) (σ : KF →+* KF)
      (by rw [hC]; exact σ.commutes _) (by rw [hC]; exact map_one _)
      (by rw [hC]; exact map_zero _) (by rw [hC]; exact map_zero _) _ hφ
    have hψ' : ReductionKernel.DivPolyHyp (C • Affine.baseChange (P.curve x).E KF) := by
      rw [eq_legendre_of_coeffs hC₁ hC₂ hC₃ hC₄ hC₆]
      exact divPolyLegendreHyp _ _
    intro Q hQ
    have hQ' : ℓ • e Q = 0 := by rw [← map_nsmul, hQ, map_zero]
    have := MultKernel.iterate_map_eq_self vK hC₁ hC₂ hC₃ hC₄ hC₆ (σ : KF →+* KF) hμ1 h2'
      (by change σ (1 - μ) = 1 - μ; rw [map_sub, map_one, hμ_def, σ.commutes]) hσ' hvσ hψ' hodd
      hℓ' φ' hφ'' (e Q) hQ'
    rw [hφ', iterate_conj] at this
    exact e.injective this
  · -- `v(λ) > 1`: the model `E_{1/λ} = ⟨√λ, 0, 0, 0⟩ • E_λ`
    have hμ0 : μ ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hμ
      exact absurd hμ (not_lt.mpr zero_le_one)
    have hμ1 : vK μ⁻¹ < 1 := by
      rw [map_inv₀, inv_lt_one₀ (lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr
        hμ0)))]
      exact hμ
    set u : KF := algebraMap (P.curve x).F KF (sqrtLam' x.1) with hu_def
    have hu : u ^ 2 = μ := by
      have hsq : (sqrtLam' x.1 : (P.curve x).F) ^ 2 = genC' P x := sqrtLam'_sq x.1
      rw [hu_def, ← map_pow]
      exact congrArg _ hsq
    have hu0 : u ≠ 0 := fun h0 => hμ0 (by rw [← hu, h0, zero_pow two_ne_zero])
    set C : VariableChange KF := ⟨Units.mk0 u hu0, 0, 0, 0⟩ with hC
    obtain ⟨hC₁, hC₂, hC₃, hC₄, hC₆⟩ := legendreCoeffs_vc_inv hE₁ hE₂ hE₃ hE₄ hE₆ hu hu0
    set e := Anabelian.vcEquiv C (Affine.baseChange (P.curve x).E KF) with he
    set φ' := e.toAddMonoidHom.comp
      ((Point.map (W' := (P.curve x).E) (S := (P.curve x).F)
        (σ : KF →ₐ[(P.curve x).F] KF)).comp e.symm.toAddMonoidHom) with hφ'
    have hφ'' := exists_vcEquiv_map_eq C (Affine.baseChange (P.curve x).E KF) (σ : KF →+* KF)
      (by rw [hC]; exact σ.commutes _) (by rw [hC]; exact map_zero _)
      (by rw [hC]; exact map_zero _) (by rw [hC]; exact map_zero _) _ hφ
    have hψ' : ReductionKernel.DivPolyHyp (C • Affine.baseChange (P.curve x).E KF) := by
      rw [eq_legendre_of_coeffs hC₁ hC₂ hC₃ hC₄ hC₆]
      exact divPolyLegendreHyp _ _
    intro Q hQ
    have hQ' : ℓ • e Q = 0 := by rw [← map_nsmul, hQ, map_zero]
    have := MultKernel.iterate_map_eq_self vK hC₁ hC₂ hC₃ hC₄ hC₆ (σ : KF →+* KF) hμ1 h2'
      (by change σ μ⁻¹ = μ⁻¹; rw [map_inv₀, hμ_def, σ.commutes]) hσ' hvσ hψ' hodd hℓ' φ' hφ''
      (e Q) hQ'
    rw [hφ', iterate_conj] at this
    exact e.injective this

/-- **`e(v/w) ≤ ℓ` at a bad place**: the inertia group is an `ℓ`-group whose order divides
`[K : F] ∣ ℓ(ℓ² − 1)(ℓ − 1)`. -/
theorem relRamIdx_torsionField_le_of_bad (h2 : residueChar v ≠ 2) (hpℓ : residueChar v ≠ ℓ)
    (hbad : (placeUnder (k := (P.curve x).F) v).maximalIdeal.valuation _ (genC' P x) ≠ 1 ∨
      (placeUnder (k := (P.curve x).F) v).maximalIdeal.valuation _ (genC' P x - 1) ≠ 1) :
    relRamIdx v (placeUnder (k := (P.curve x).F) v) ≤ ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  rw [relRamIdx_eq_card_inertia (liesOver_placeUnder v)]
  refine card_le_of_forall_pow_eq_one _ ℓ ((ℓ ^ 2 - 1) * (ℓ - 1)) ?_ (not_dvd_gl_cofactor hℓ)
    fun σ hσ => inertia_pow_eq_one P x hℓ h7 hsl hP2 v h2 hpℓ hbad σ hσ
  rw [IsGalois.card_aut_eq_finrank, ← card_GL_two_eq_mul]
  exact finrank_torsionField_dvd P x hℓ h7 hsl hP2

/-- **`e(v/w) ≤ ℓ` away from `2·ℓ`**, for `v` a place of `K = F(E[ℓ])` over `w` of `F`. -/
theorem relRamIdx_torsionField_le (h2 : residueChar v ≠ 2) (hpℓ : residueChar v ≠ ℓ) :
    relRamIdx v (placeUnder (k := (P.curve x).F) v) ≤ ℓ := by
  by_cases hgood : (placeUnder (k := (P.curve x).F) v).maximalIdeal.valuation _ (genC' P x) = 1 ∧
      (placeUnder (k := (P.curve x).F) v).maximalIdeal.valuation _ (genC' P x - 1) = 1
  · rw [relRamIdx_torsionField_eq_one hℓ h7 hsl hP2 divPolyLegendreHyp v h2 hpℓ hgood.1 hgood.2]
    exact hℓ.one_lt.le
  · exact relRamIdx_torsionField_le_of_bad P x hℓ h7 hsl hP2 v h2 hpℓ (not_and_or.mp hgood)

end Bad

end Iut.Tripod
