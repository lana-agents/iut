/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.CurveFacts

/-!
# The torsion degree bound

We prove `Iut.Tripod.TorsionDegreeBound l n` for prime `n`: for every number field
`K ⊆ ℚ̄` containing `λ`, adjoining the coordinates of the `n`-torsion points of the Legendre
curve `E_λ` multiplies the degree by at most `|GL₂(𝔽_n)| = (n² − 1)(n² − n)`, provided
`E_λ[n](ℚ̄) ≅ (ℤ/n)²`.

The proof is the Galois-theoretic one. The Legendre curve `E_λ` is defined over `K`
(`Iut.Tripod.legendreOver`), so `Gal(ℚ̄/K)` acts on `E_λ(ℚ̄)` (`Iut.Tripod.galAct`) preserving
the `n`-torsion `T = E_λ[n]`. Through a basis `b : T ≃+ (ℤ/n)²` this gives the mod-`n`
representation `ρ : Gal(ℚ̄/K) →* GL₂(ℤ/n)` (`Iut.Tripod.torsionRep`). Its kernel is the fixing
subgroup of the torsion field `L = K(E_λ[n])` (`Iut.Tripod.torsionRep_ker`), so by the Galois
correspondence for the Galois extension `ℚ̄/K` (`IntermediateField.finrank_eq_fixingSubgroup_index`)

  `[L : K] = [Gal(ℚ̄/K) : ker ρ] = |ρ(Gal(ℚ̄/K))| ≤ |GL₂(𝔽_n)| = (n² − 1)(n² − n)`,

and `[L : ℚ] = [K : ℚ]·[L : K]`.
-/

namespace Iut.Tripod

open WeierstrassCurve

open scoped Classical IntermediateField

/-! ### The Galois action on the points of the Legendre curve -/

section GaloisAction

variable (K : IntermediateField ℚ Qbar) {l : Qbar} (hl : l ∈ K)

/-- The Legendre curve `E_λ` as a curve over a subfield `K ∋ λ` of `ℚ̄`. -/
noncomputable def legendreOver : WeierstrassCurve K := legendre (⟨l, hl⟩ : K)

/-- The base change of `E_λ/K` to `ℚ̄` is `E_λ/ℚ̄` (definitionally). -/
theorem legendreOver_baseChange : Affine.baseChange (legendreOver K hl) Qbar = legendre l := rfl

/-- The action of `σ ∈ Gal(ℚ̄/K)` on `E_λ(ℚ̄)`: the functorial map of nonsingular points along
`σ : ℚ̄ →ₐ[K] ℚ̄`, for the model `E_λ/K`. -/
noncomputable def galAct (σ : Qbar ≃ₐ[K] Qbar) :
    (legendre l).toAffine.Point →+ (legendre l).toAffine.Point :=
  Affine.Point.map (W' := legendreOver K hl) (S := K) σ.toAlgHom

theorem galAct_zero (σ : Qbar ≃ₐ[K] Qbar) : galAct K hl σ 0 = 0 := rfl

theorem galAct_some (σ : Qbar ≃ₐ[K] Qbar) {x y : Qbar} (h : (legendre l).toAffine.Nonsingular x y) :
    galAct K hl σ (Affine.Point.some x y h) =
      Affine.Point.some (σ x) (σ y)
        ((Affine.baseChange_nonsingular (legendreOver K hl) σ.toAlgHom.injective ..).mpr h) :=
  rfl

theorem galAct_one (P : (legendre l).toAffine.Point) : galAct K hl 1 P = P := by
  cases P <;> rfl

theorem galAct_mul (σ τ : Qbar ≃ₐ[K] Qbar) (P : (legendre l).toAffine.Point) :
    galAct K hl (σ * τ) P = galAct K hl σ (galAct K hl τ P) := by
  cases P <;> rfl

/-- The Galois action preserves the `n`-torsion. -/
theorem galAct_torsionBy (σ : Qbar ≃ₐ[K] Qbar) {n : ℕ} {P : (legendre l).toAffine.Point}
    (hP : P ∈ AddSubgroup.torsionBy (legendre l).toAffine.Point n) :
    galAct K hl σ P ∈ AddSubgroup.torsionBy (legendre l).toAffine.Point n := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

/-- The action of `σ ∈ Gal(ℚ̄/K)` on the `n`-torsion `E_λ(ℚ̄)[n]`. -/
noncomputable def galTorsion (n : ℕ) (σ : Qbar ≃ₐ[K] Qbar) :
    AddSubgroup.torsionBy (legendre l).toAffine.Point n →+
      AddSubgroup.torsionBy (legendre l).toAffine.Point n :=
  ((galAct K hl σ).restrict (AddSubgroup.torsionBy (legendre l).toAffine.Point n)).codRestrict
    (AddSubgroup.torsionBy (legendre l).toAffine.Point n)
    (fun P => galAct_torsionBy K hl σ P.2)

@[simp] theorem coe_galTorsion (n : ℕ) (σ : Qbar ≃ₐ[K] Qbar)
    (P : AddSubgroup.torsionBy (legendre l).toAffine.Point n) :
    (galTorsion K hl n σ P : (legendre l).toAffine.Point) = galAct K hl σ P :=
  rfl

/-- **`σ` fixes the `n`-torsion points iff it fixes their coordinates.** -/
theorem galAct_torsion_fixed_iff (σ : Qbar ≃ₐ[K] Qbar) (n : ℕ) :
    (∀ P : AddSubgroup.torsionBy (legendre l).toAffine.Point n, galAct K hl σ P = P) ↔
      ∀ c ∈ torsionCoords l n, σ c = c := by
  constructor
  · intro h c hc
    obtain ⟨P, hP, hcP⟩ := Set.mem_iUnion₂.mp hc
    have hP' : P ∈ AddSubgroup.torsionBy (legendre l).toAffine.Point n :=
      AddSubgroup.torsionBy.nsmul_iff.mpr hP
    have hfix := h ⟨P, hP'⟩
    cases P with
    | zero => exact absurd hcP id
    | some x y hxy =>
      replace hfix := Affine.Point.some.inj
        (show Affine.Point.some (σ x) (σ y) _ = Affine.Point.some x y hxy from hfix)
      rcases hcP with rfl | rfl
      · exact hfix.1
      · exact hfix.2
  · rintro h ⟨P, hP⟩
    cases P with
    | zero => rfl
    | some x y hxy =>
      have hP' : n • Affine.Point.some x y hxy = 0 := AddSubgroup.torsionBy.nsmul_iff.mp hP
      show Affine.Point.some (σ x) (σ y) _ = Affine.Point.some x y hxy
      rw [Affine.Point.some.injEq]
      exact ⟨h x (mem_torsionCoords hP' (by simp)), h y (mem_torsionCoords hP' (by simp))⟩

end GaloisAction

/-! ### The mod-`n` representation in a basis -/

section Representation

variable (K : IntermediateField ℚ Qbar) {l : Qbar} (hl : l ∈ K) (n : ℕ)
variable (b : AddSubgroup.torsionBy (legendre l).toAffine.Point n ≃+ (Fin 2 → ZMod n))

/-- The `ℤ/n`-linear endomorphism `b ∘ σ ∘ b⁻¹` of `(ℤ/n)²` induced by `σ ∈ Gal(ℚ̄/K)`. -/
noncomputable def repLin (σ : Qbar ≃ₐ[K] Qbar) : Module.End (ZMod n) (Fin 2 → ZMod n) :=
  (b.toAddMonoidHom.comp ((galTorsion K hl n σ).comp b.symm.toAddMonoidHom)).toZModLinearMap n

theorem repLin_apply (σ : Qbar ≃ₐ[K] Qbar) (v : Fin 2 → ZMod n) :
    repLin K hl n b σ v = b (galTorsion K hl n σ (b.symm v)) :=
  rfl

/-- `σ ↦ b ∘ σ ∘ b⁻¹` as a monoid homomorphism to the endomorphisms of `(ℤ/n)²`. -/
noncomputable def repEnd : (Qbar ≃ₐ[K] Qbar) →* Module.End (ZMod n) (Fin 2 → ZMod n) where
  toFun := repLin K hl n b
  map_one' := by
    refine LinearMap.ext fun v => ?_
    rw [repLin_apply, Module.End.one_apply]
    have h : galTorsion K hl n 1 (b.symm v) = b.symm v := Subtype.ext (galAct_one K hl _)
    rw [h, b.apply_symm_apply]
  map_mul' σ τ := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, repLin_apply, repLin_apply, repLin_apply, b.symm_apply_apply]
    congr 1
    exact Subtype.ext (galAct_mul K hl σ τ _)

/-- **The mod-`n` representation** `ρ : Gal(ℚ̄/K) →* GL₂(ℤ/n)` of the Legendre curve in the
basis `b` of `E_λ(ℚ̄)[n]`. -/
noncomputable def torsionRep : (Qbar ≃ₐ[K] Qbar) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod n) :=
  (Units.mapEquiv (LinearMap.toMatrixAlgEquiv' :
    Module.End (ZMod n) (Fin 2 → ZMod n) ≃ₐ[ZMod n] Matrix (Fin 2) (Fin 2) (ZMod n)).toMulEquiv
    ).toMonoidHom.comp (repEnd K hl n b).toHomUnits

/-- `σ ∈ ker ρ` iff `σ` fixes every `n`-torsion point. -/
theorem mem_torsionRep_ker_iff (σ : Qbar ≃ₐ[K] Qbar) :
    σ ∈ (torsionRep K hl n b).ker ↔
      ∀ P : AddSubgroup.torsionBy (legendre l).toAffine.Point n, galAct K hl σ P = P := by
  rw [MonoidHom.mem_ker, torsionRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one]
  change repLin K hl n b σ = 1 ↔ _
  constructor
  · intro h P
    have hv := LinearMap.congr_fun h (b P)
    rw [repLin_apply, b.symm_apply_apply, Module.End.one_apply] at hv
    exact congrArg Subtype.val (b.injective hv)
  · intro h
    refine LinearMap.ext fun v => ?_
    have hv : galTorsion K hl n σ (b.symm v) = b.symm v := Subtype.ext (h (b.symm v))
    rw [repLin_apply, Module.End.one_apply, hv, b.apply_symm_apply]

/-- **The kernel of `ρ` is the fixing subgroup of the torsion field** `K(E_λ[n])`. -/
theorem torsionRep_ker :
    (torsionRep K hl n b).ker =
      (IntermediateField.adjoin K (torsionCoords l n)).fixingSubgroup := by
  ext σ
  rw [mem_torsionRep_ker_iff, galAct_torsion_fixed_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem c hc => exact h c hc
    | algebraMap r => exact σ.commutes r
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  · intro h c hc
    exact h c (IntermediateField.subset_adjoin K _ hc)

end Representation

/-! ### The degree bound -/

section Bound

/-- `|GL₂(𝔽_n)| = (n² − 1)(n² − n)` for `n` prime. -/
theorem card_GL_two (n : ℕ) [Fact n.Prime] :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod n)) = (n ^ 2 - 1) * (n ^ 2 - n) := by
  rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
  simp

variable (K : IntermediateField ℚ Qbar) {l : Qbar} (hl : l ∈ K) (n : ℕ) [Fact n.Prime]
variable (b : AddSubgroup.torsionBy (legendre l).toAffine.Point n ≃+ (Fin 2 → ZMod n))

/-- The index of `ker ρ` is at most `|GL₂(𝔽_n)|`. -/
theorem torsionRep_ker_index_le :
    (torsionRep K hl n b).ker.index ≤ (n ^ 2 - 1) * (n ^ 2 - n) := by
  rw [Subgroup.index_ker, ← card_GL_two n]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-- `ℚ̄/K` is Galois for every subfield `K ⊆ ℚ̄`. -/
instance isGalois_qbar : IsGalois K Qbar := ⟨⟩

include hl b in
/-- **The relative torsion degree bound**: `[K(E_λ[n]) : K] ≤ (n² − 1)(n² − n)`. -/
theorem finrank_adjoin_torsionCoords_le :
    Module.finrank K (IntermediateField.adjoin K (torsionCoords l n)) ≤
      (n ^ 2 - 1) * (n ^ 2 - n) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← torsionRep_ker K hl n b]
  exact torsionRep_ker_index_le K hl n b

end Bound

/-- **The torsion degree bound** (`Iut.Tripod.TorsionDegreeBound`) for prime `n`, given a basis
`E_λ(ℚ̄)[n] ≅ (ℤ/n)²`. -/
theorem torsionDegreeBound (l : Qbar) (n : ℕ) [Fact n.Prime]
    (hbasis : Nonempty (AddSubgroup.torsionBy (legendre l).toAffine.Point n ≃+ (Fin 2 → ZMod n))) :
    TorsionDegreeBound l n := by
  intro K hK hl
  obtain ⟨b⟩ := hbasis
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup]
  calc Module.finrank ℚ ↥(IntermediateField.restrictScalars ℚ
        (IntermediateField.adjoin K (torsionCoords l n)))
      = Module.finrank ℚ K * Module.finrank K (IntermediateField.adjoin K (torsionCoords l n)) :=
        (Module.finrank_mul_finrank ℚ K (IntermediateField.adjoin K (torsionCoords l n))).symm
    _ ≤ Module.finrank ℚ K * ((n ^ 2 - 1) * (n ^ 2 - n)) :=
        Nat.mul_le_mul_left _ (finrank_adjoin_torsionCoords_le K hl n b)
    _ = (n ^ 2 - 1) * (n ^ 2 - n) * Module.finrank ℚ K := mul_comm _ _

/-- The torsion degree bound for `n = 3`. -/
theorem torsionDegreeBound_three (l : Qbar)
    (hbasis : Nonempty (AddSubgroup.torsionBy (legendre l).toAffine.Point 3 ≃+ (Fin 2 → ZMod 3))) :
    TorsionDegreeBound l 3 :=
  torsionDegreeBound l 3 hbasis

/-- The torsion degree bound for `n = 5`. -/
theorem torsionDegreeBound_five (l : Qbar)
    (hbasis : Nonempty (AddSubgroup.torsionBy (legendre l).toAffine.Point 5 ≃+ (Fin 2 → ZMod 5))) :
    TorsionDegreeBound l 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  torsionDegreeBound l 5 hbasis

end Iut.Tripod
