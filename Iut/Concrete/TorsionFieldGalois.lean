/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Cor312.ThetaData.Basic
import Iut.Cor312.ThetaData.TwoTorsion
import Iut.Cor312.ThetaData.VariableChangePoint

/-!
# The `ℓ`-torsion field is Galois over the field of moduli (IUT I, Remark 3.1.5)

For initial Θ-data, `F/F_mod` is Galois (IUT I, Definition 3.1(b)) and the `6`-torsion of `E` is
rational over `F`; IUT I, Remark 3.1.5 deduces that the `ℓ`-torsion field `K = F(E[ℓ])` is
Galois over `F_mod`. This file proves it (`Iut.InitialThetaData.isGalois_Kt`):

* **rigidity along the `3`-torsion** (`Iut.variableChange_eq_of_three_torsion`): over an
  algebraically closed field of characteristic `0`, two changes of variables of an elliptic
  curve agreeing on the `3`-torsion points are equal (the `3`-torsion contains two points with
  distinct `x`-coordinates, the first not of order `2`; `|E[3]| = 9`,
  `Iut.card_torsionBy_eq_sq'`); hence a field automorphism `τ` fixing the `3`-torsion of `W`
  and of `C • W` fixes `C` (`Iut.variableChange_map_eq_of_three_torsion`);
* for `σ ∈ Gal(F̄/F_mod)`: `σ(F) = F`, and `E` and `E^σ` have the same `j`-invariant
  `j(E) ∈ F_mod`, so `C • E = E^σ` over `F̄` (Mathlib's
  `WeierstrassCurve.exists_variableChange_of_j_eq`); as the `3`-torsion of both is rational
  over `F`, `C` is fixed by `Gal(F̄/F)`;
* so for `τ ∈ ker ρ` the conjugate `σ⁻¹τσ` fixes `E[ℓ]` (`σ(E[ℓ]) = E^σ[ℓ] = C(E[ℓ])`), hence
  lies in `ker ρ`, and `σ(K) ⊆ K`: `K/F_mod` is normal, hence Galois.
-/

namespace Iut

universe u

open NumberField WeierstrassCurve Iut.Anabelian

section Rigidity

variable {L : Type*} [Field L]

open scoped Classical in
/-- Three-torsion points: two of distinct `x`-coordinates, the first not of order `2`. -/
theorem exists_three_torsion_points [IsAlgClosed L] [CharZero L] (W : WeierstrassCurve L)
    [W.IsElliptic] :
    ∃ (x₁ y₁ x₂ y₂ : L) (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂),
      x₁ ≠ x₂ ∧ y₁ ≠ W.toAffine.negY x₁ y₁ ∧
      Affine.Point.some x₁ y₁ h₁ ∈ AddSubgroup.torsionBy W.toAffine.Point ((3 : ℕ) : ℤ) ∧
      Affine.Point.some x₂ y₂ h₂ ∈ AddSubgroup.torsionBy W.toAffine.Point ((3 : ℕ) : ℤ) := by
  set T := AddSubgroup.torsionBy W.toAffine.Point ((3 : ℕ) : ℤ) with hT
  have hcard : Nat.card T = 3 ^ 2 := card_torsionBy_eq_sq' W 3 (by norm_num)
  have hcard' : (T : Set W.toAffine.Point).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]; exact hcard
  -- small subsets do not exhaust `T`
  have hbig : ∀ s : Finset W.toAffine.Point, s.card ≤ 3 → ∃ Q ∈ T, Q ∉ s := by
    intro s hs
    by_contra h
    push Not at h
    have : (T : Set W.toAffine.Point).ncard ≤ s.card := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard (fun Q hQ => h Q hQ) (Finset.finite_toSet s)
    omega
  have h3 : ∀ Q : W.toAffine.Point, Q ∈ T ↔ (3 : ℤ) • Q = 0 := fun Q => mem_torsionBy_iff' _ _
  obtain ⟨P, hP, hP0⟩ := hbig {0} (by simp)
  rw [Finset.mem_singleton] at hP0
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd rfl hP0
  have hy : y₁ ≠ W.toAffine.negY x₁ y₁ := by
    intro hy
    apply hP0
    have hneg : -(Affine.Point.some x₁ y₁ h₁) = Affine.Point.some x₁ y₁ h₁ := by
      rw [Affine.Point.neg_some]; exact some_ext rfl hy.symm
    have h3P := (h3 _).mp hP
    have h2 : (2 : ℤ) • Affine.Point.some x₁ y₁ h₁ = 0 := by
      rw [two_zsmul]; nth_rewrite 2 [← hneg]; exact add_neg_cancel _
    have : (3 : ℤ) • Affine.Point.some x₁ y₁ h₁ = (2 : ℤ) • Affine.Point.some x₁ y₁ h₁ +
        Affine.Point.some x₁ y₁ h₁ := by
      rw [show (3 : ℤ) = 2 + 1 by norm_num, add_zsmul, one_zsmul]
    rw [this, h2, zero_add] at h3P
    exact h3P
  obtain ⟨Q, hQ, hQs⟩ := hbig {0, Affine.Point.some x₁ y₁ h₁, -(Affine.Point.some x₁ y₁ h₁)}
    (Finset.card_le_three)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQs
  obtain ⟨hQ0, hQP, hQN⟩ := hQs
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hQ0
  refine ⟨x₁, y₁, x₂, y₂, h₁, h₂, ?_, hy, hP, hQ⟩
  intro hx
  rcases Affine.Y_eq_of_X_eq h₂.1 h₁.1 hx.symm with h | h
  · exact hQP (some_ext hx.symm h)
  · apply hQN
    rw [Affine.Point.neg_some]
    exact some_ext hx.symm h



open scoped Classical in
/-- **Rigidity of changes of variables along the `3`-torsion**: two changes of variables of an
elliptic curve over an algebraically closed field of characteristic `0` which agree on the
coordinates of every `3`-torsion point are equal. -/
theorem variableChange_eq_of_three_torsion [IsAlgClosed L] [CharZero L] (W : WeierstrassCurve L)
    [W.IsElliptic] (C₀ C₁ : VariableChange L)
    (h : ∀ (x y : L) (hxy : W.toAffine.Nonsingular x y),
      Affine.Point.some x y hxy ∈ AddSubgroup.torsionBy W.toAffine.Point ((3 : ℕ) : ℤ) →
        vcX C₀ x = vcX C₁ x ∧ vcY C₀ x y = vcY C₁ x y) : C₀ = C₁ := by
  obtain ⟨x₁, y₁, x₂, y₂, h₁, h₂, hx, hy, hP, hQ⟩ := exists_three_torsion_points W
  have hN : Affine.Point.some x₁ (W.toAffine.negY x₁ y₁) ((Affine.nonsingular_neg ..).mpr h₁) ∈
      AddSubgroup.torsionBy W.toAffine.Point ((3 : ℕ) : ℤ) := by
    have := neg_mem hP
    rwa [Affine.Point.neg_some] at this
  obtain ⟨hX1, hY1⟩ := h _ _ _ hP
  obtain ⟨hX2, hY2⟩ := h _ _ _ hQ
  obtain ⟨-, hY3⟩ := h _ _ _ hN
  unfold vcX at hX1 hX2
  unfold vcY at hY1 hY2 hY3
  set z := W.toAffine.negY x₁ y₁
  have hu0 := u_ne_zero C₀
  have hu1 := u_ne_zero C₁
  field_simp at hX1 hX2 hY1 hY2 hY3
  have ha : (C₀.u : L) ^ 2 = (C₁.u : L) ^ 2 := by
    have : (x₁ - x₂) * (C₁.u : L) ^ 2 = (x₁ - x₂) * (C₀.u : L) ^ 2 := by
      linear_combination hX1 - hX2
    exact (mul_left_cancel₀ (sub_ne_zero.mpr hx) this).symm
  have hr : C₀.r = C₁.r := by
    have : (C₀.u : L) ^ 2 * (C₀.r - C₁.r) = 0 := by linear_combination -hX1 - (x₁ - C₀.r) * ha
    have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hu0)
    linear_combination this
  have hb : (C₀.u : L) ^ 3 = (C₁.u : L) ^ 3 := by
    have : (y₁ - z) * (C₁.u : L) ^ 3 = (y₁ - z) * (C₀.u : L) ^ 3 := by
      linear_combination hY1 - hY3
    exact (mul_left_cancel₀ (sub_ne_zero.mpr hy) this).symm
  have hu : (C₀.u : L) = C₁.u := by
    have e1 : (C₀.u : L) = (C₀.u : L) ^ 3 / (C₀.u : L) ^ 2 := by field_simp
    have e2 : (C₁.u : L) = (C₁.u : L) ^ 3 / (C₁.u : L) ^ 2 := by field_simp
    rw [e1, e2, ha, hb]
  rw [hr, hu] at hY1 hY2
  have hs : C₀.s = C₁.s := by
    have : (x₁ - x₂) * ((C₁.u : L) ^ 3 * (C₀.s - C₁.s)) = 0 := by
      linear_combination -hY1 + hY2
    have := ((mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hx))
    have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hu1)
    linear_combination this
  have ht : C₀.t = C₁.t := by
    rw [hs] at hY1
    have : (C₁.u : L) ^ 3 * (C₀.t - C₁.t) = 0 := by linear_combination -hY1
    have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hu1)
    linear_combination this
  ext
  · exact hu
  · exact hr
  · exact hs
  · exact ht



open scoped Classical in
/-- A ring endomorphism moves the `X`-coordinate in `C • W` to that in `C.map τ • W.map τ`. -/
lemma map_vcX (C : VariableChange L) (τ : L →+* L) (x : L) :
    τ (vcX C x) = vcX (C.map τ) (τ x) := by
  simp [vcX, map_div₀]

open scoped Classical in
/-- A ring endomorphism moves the `Y`-coordinate in `C • W` to that in `C.map τ • W.map τ`. -/
lemma map_vcY (C : VariableChange L) (τ : L →+* L) (x y : L) :
    τ (vcY C x y) = vcY (C.map τ) (τ x) (τ y) := by
  simp [vcY, map_div₀]

open scoped Classical in
/-- **Fixed changes of variables**: if a field automorphism `τ` fixes the coordinates of the
`3`-torsion points of `W` and of `C • W`, then it fixes the coefficients of `C`. -/
theorem variableChange_map_eq_of_three_torsion [IsAlgClosed L] [CharZero L]
    (W : WeierstrassCurve L) [W.IsElliptic] (C : VariableChange L) (τ : L →+* L)
    (hW : ∀ (x y : L) (hxy : W.toAffine.Nonsingular x y),
      Affine.Point.some x y hxy ∈ AddSubgroup.torsionBy W.toAffine.Point ((3 : ℕ) : ℤ) →
        τ x = x ∧ τ y = y)
    (hCW : ∀ (x y : L) (hxy : (C • W).toAffine.Nonsingular x y),
      Affine.Point.some x y hxy ∈ AddSubgroup.torsionBy (C • W).toAffine.Point ((3 : ℕ) : ℤ) →
        τ x = x ∧ τ y = y) :
    C.map τ = C := by
  refine variableChange_eq_of_three_torsion W _ _ fun x y hxy hP => ?_
  have hP' : vcHom C W (Affine.Point.some x y hxy) ∈
      AddSubgroup.torsionBy (C • W).toAffine.Point ((3 : ℕ) : ℤ) := by
    rw [mem_torsionBy_iff'] at hP ⊢
    rw [← map_zsmul, hP, map_zero]
  rw [vcHom_apply, vcPoint_some] at hP'
  obtain ⟨hx, hy⟩ := hW x y hxy hP
  obtain ⟨hX, hY⟩ := hCW _ _ _ hP'
  constructor
  · rw [← hx, ← map_vcX, hx, hX]
  · rw [← hx, ← hy, ← map_vcY, hx, hy, hY]

end Rigidity


section Galois

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]

omit [NumberField F] [E.IsElliptic] [IsAlgClosure F Fbar] in
open scoped Classical in
/-- The coordinates of the `3`-torsion points of `E(F̄)` are rational, if the `6`-torsion is. -/
lemma coords_rational_of_three_torsion (h6 : SixTorsionRational F E Fbar) (x y : Fbar)
    (hxy : (E.baseChange Fbar).toAffine.Nonsingular x y)
    (hP : Affine.Point.some x y hxy ∈
      AddSubgroup.torsionBy (E.baseChange Fbar).toAffine.Point ((3 : ℕ) : ℤ)) :
    x ∈ (algebraMap F Fbar).range ∧ y ∈ (algebraMap F Fbar).range := by
  have hP6 : Affine.Point.some x y hxy ∈
      AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) 6 := by
    rw [mem_torsionBy_iff'] at hP ⊢
    rw [show (6 : ℤ) = 2 * ((3 : ℕ) : ℤ) by norm_num, mul_zsmul, hP, smul_zero]
  obtain ⟨Q, hQ⟩ := h6 _ hP6
  rcases Q with _ | ⟨a, b, hab⟩
  · exact absurd hQ (fun h => by cases h)
  · simp only [Affine.Point.baseChange, Affine.Point.map_some] at hQ
    obtain ⟨rfl, rfl⟩ := Affine.Point.some.inj hQ
    exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩

/-- `F̄` is normal over `F_mod`. -/
lemma normal_fieldOfModuli_algClosure : Normal ↥(fieldOfModuli F E) Fbar := by
  haveI : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic F Fbar := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ↥(fieldOfModuli F E) Fbar :=
    Algebra.IsAlgebraic.trans ↥(fieldOfModuli F E) F Fbar
  haveI : IsAlgClosure ↥(fieldOfModuli F E) Fbar := ⟨inferInstance, inferInstance⟩
  exact IsAlgClosure.normal _ _

/-- **`σ(F) = F`**: an `F_mod`-embedding `F̄ → F̄` maps `F` into `F`, as `F/F_mod` is normal. -/
lemma map_algebraMap_mem_range [Normal ↥(fieldOfModuli F E) F]
    (σ : Fbar →ₐ[↥(fieldOfModuli F E)] Fbar) (a : F) :
    σ (algebraMap F Fbar a) ∈ (algebraMap F Fbar).range := by
  haveI := normal_fieldOfModuli_algClosure (F := F) (E := E) (Fbar := Fbar)
  set Fr := (IsScalarTower.toAlgHom ↥(fieldOfModuli F E) F Fbar).fieldRange
  have hFr : Normal ↥(fieldOfModuli F E) Fr :=
    Normal.of_algEquiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom _ F Fbar))
  have hle := IntermediateField.normal_iff_forall_map_le.mp hFr σ
  have hmem : σ (algebraMap F Fbar a) ∈ Fr.map σ :=
    ⟨algebraMap F Fbar a, ⟨a, rfl⟩, rfl⟩
  obtain ⟨b, hb⟩ := hle hmem
  exact ⟨b, hb⟩

/-- The conjugate `σ⁻¹ τ σ` of `τ ∈ Gal(F̄/F)` by `σ ∈ Gal(F̄/F_mod)`, an element of
`Gal(F̄/F)` since `σ(F) = F`. -/
noncomputable def conjAut [Normal ↥(fieldOfModuli F E) F]
    (σ : Fbar ≃ₐ[↥(fieldOfModuli F E)] Fbar) (τ : Fbar ≃ₐ[F] Fbar) : Fbar ≃ₐ[F] Fbar :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv.trans (τ.toRingEquiv.trans σ.symm.toRingEquiv))
    (fun a => by
      obtain ⟨b, hb⟩ := map_algebraMap_mem_range (E := E) σ.toAlgHom a
      change σ.symm (τ (σ (algebraMap F Fbar a))) = algebraMap F Fbar a
      change algebraMap F Fbar b = σ (algebraMap F Fbar a) at hb
      rw [← hb, τ.commutes, hb, AlgEquiv.symm_apply_apply])

/-- `σ⁻¹ τ σ` applied to `x`. -/
lemma conjAut_apply [Normal ↥(fieldOfModuli F E) F]
    (σ : Fbar ≃ₐ[↥(fieldOfModuli F E)] Fbar) (τ : Fbar ≃ₐ[F] Fbar) (x : Fbar) :
    conjAut (E := E) σ τ x = σ.symm (τ (σ x)) := rfl

variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))} (P : AdmissiblePrimeData F E Fbar VBad)

omit [IsAlgClosure F Fbar] in
open scoped Classical in
/-- An element of `Gal(F̄/F)` fixing the `ℓ`-torsion pointwise lies in the kernel of the mod-`ℓ`
representation. -/
lemma mem_ker_rep_of_fixes (τ : Fbar ≃ₐ[F] Fbar)
    (h : ∀ Q ∈ AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) P.ℓ,
      galPointMap F E Fbar τ Q = Q) : τ ∈ P.rep.ker := by
  have hA : ∀ v : Fin 2 → ZMod P.ℓ, (P.rep τ : Matrix (Fin 2) (Fin 2) (ZMod P.ℓ)).mulVec v = v := by
    intro v
    obtain ⟨Q, rfl⟩ := P.torsionBasis.surjective v
    rw [← P.rep_spec τ Q]
    congr 1
    exact Subtype.ext (h Q.1 Q.2)
  rw [MonoidHom.mem_ker]
  refine Units.ext ?_
  ext i j
  have := congrFun (hA (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

omit [IsAlgClosure F Fbar] in
open scoped Classical in
/-- If `C • E_{F̄} = W'` with `C` fixed by `τ ∈ ker ρ`, then `τ` fixes the coordinates of the
`ℓ`-torsion points of `W'` (they are the images under `C` of `ℓ`-torsion points of `E`). -/
lemma coords_fixed_of_variableChange {W' : WeierstrassCurve Fbar} (C : VariableChange Fbar)
    (hC : C • E.baseChange Fbar = W') {τ : Fbar ≃ₐ[F] Fbar} (hτ : τ ∈ P.rep.ker)
    (hCτ : C.map (τ : Fbar →+* Fbar) = C) (x y : Fbar) (hxy : W'.toAffine.Nonsingular x y)
    (hR : Affine.Point.some x y hxy ∈ AddSubgroup.torsionBy W'.toAffine.Point (P.ℓ : ℤ)) :
    τ x = x ∧ τ y = y := by
  subst hC
  obtain ⟨R, hvc⟩ := (vcEquiv C (E.baseChange Fbar)).surjective (Affine.Point.some x y hxy)
  have hRT : R ∈ AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) P.ℓ := by
    rw [mem_torsionBy_iff'] at hR ⊢
    apply (vcEquiv C (E.baseChange Fbar)).injective
    rw [map_zsmul, hvc, hR, map_zero]
  rw [vcEquiv_apply] at hvc
  have hfix := P.galPointMap_eq_of_mem_ker hτ ⟨R, hRT⟩
  rcases R with _ | ⟨xR, yR, hR'⟩
  · exact absurd hvc (fun h => by cases h)
  · rw [vcPoint_some] at hvc
    obtain ⟨rfl, rfl⟩ := Affine.Point.some.inj hvc
    simp only [galPointMap, Affine.Point.map_some] at hfix
    obtain ⟨hx, hy⟩ := Affine.Point.some.inj hfix
    change τ xR = xR at hx
    change τ yR = yR at hy
    constructor
    · change (τ : Fbar →+* Fbar) (vcX C xR) = _
      rw [map_vcX, hCτ]; congr 1
    · change (τ : Fbar →+* Fbar) (vcY C xR yR) = _
      rw [map_vcY, hCτ]; congr 1

open scoped Classical in
/-- **IUT I, Remark 3.1.5** (as an intermediate field of `F̄/F_mod`): every `F_mod`-embedding
`σ : F̄ → F̄` maps the `ℓ`-torsion field `K` into itself. -/
theorem normal_restrictScalars_torsionField [hGal : IsGalois ↥(fieldOfModuli F E) F]
    (h6 : SixTorsionRational F E Fbar) :
    Normal ↥(fieldOfModuli F E) (P.torsionField.restrictScalars ↥(fieldOfModuli F E)) := by
  haveI := normal_fieldOfModuli_algClosure (F := F) (E := E) (Fbar := Fbar)
  haveI : Normal ↥(fieldOfModuli F E) F := hGal.to_normal
  haveI : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed F
  haveI : CharZero Fbar := charZero_of_injective_algebraMap (algebraMap F Fbar).injective
  haveI : Algebra.IsAlgebraic F Fbar := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ↥(fieldOfModuli F E) Fbar :=
    Algebra.IsAlgebraic.trans ↥(fieldOfModuli F E) F Fbar
  rw [IntermediateField.normal_iff_forall_map_le]
  rintro σ0 _ ⟨x, hx, rfl⟩
  set σ : Fbar ≃ₐ[↥(fieldOfModuli F E)] Fbar :=
    AlgEquiv.ofBijective σ0 (Algebra.IsAlgebraic.algHom_bijective σ0) with hσ
  change σ x ∈ _
  set W := E.baseChange Fbar with hW
  -- `E` and `E^σ` have the same `j`-invariant
  have hjmem : E.j ∈ fieldOfModuli F E := IntermediateField.mem_adjoin_simple_self ℚ E.j
  have hj : W.j = (W.map (σ : Fbar →+* Fbar)).j := by
    rw [map_j]
    have hWj : W.j = algebraMap F Fbar E.j := map_j E (algebraMap F Fbar)
    rw [hWj]
    change _ = σ (algebraMap F Fbar ((⟨E.j, hjmem⟩ : ↥(fieldOfModuli F E)) : F))
    have hsc : algebraMap F Fbar ((⟨E.j, hjmem⟩ : ↥(fieldOfModuli F E)) : F) =
        algebraMap ↥(fieldOfModuli F E) Fbar ⟨E.j, hjmem⟩ :=
      (IsScalarTower.algebraMap_apply ↥(fieldOfModuli F E) F Fbar
        (⟨E.j, hjmem⟩ : ↥(fieldOfModuli F E))).symm
    rw [hsc, σ.commutes, ← hsc]
  obtain ⟨C, hC⟩ := exists_variableChange_of_j_eq W (W.map (σ : Fbar →+* Fbar)) hj
  -- `C` is defined over `F`
  have hCτ : ∀ τ : Fbar ≃ₐ[F] Fbar, C.map (τ : Fbar →+* Fbar) = C := by
    intro τ
    have hfixF : ∀ a ∈ (algebraMap F Fbar).range, (τ : Fbar →+* Fbar) a = a := by
      rintro _ ⟨a, rfl⟩
      exact τ.commutes a
    refine variableChange_map_eq_of_three_torsion W C _ (fun x y hxy hP => ?_) ?_
    · obtain ⟨hx, hy⟩ := coords_rational_of_three_torsion h6 x y hxy hP
      exact ⟨hfixF x hx, hfixF y hy⟩
    · rw [hC]
      intro x' y' hxy' hP'
      have hn : W.toAffine.Nonsingular (σ.symm x') (σ.symm y') := by
        rw [← W.toAffine.map_nonsingular (f := (σ : Fbar →+* Fbar)) σ.injective]
        convert hxy' <;> exact σ.apply_symm_apply _
      have hpm : pointMap W (σ : Fbar →+* Fbar) (Affine.Point.some _ _ hn) =
          Affine.Point.some x' y' hxy' :=
        (pointMap_some W _ hn).trans (some_ext (σ.apply_symm_apply _) (σ.apply_symm_apply _))
      have hP : Affine.Point.some _ _ hn ∈
          AddSubgroup.torsionBy W.toAffine.Point ((3 : ℕ) : ℤ) := by
        rw [mem_torsionBy_iff'] at hP' ⊢
        apply pointMap_injective W (σ : Fbar →+* Fbar)
        rw [map_zsmul, hpm, hP', map_zero]
      obtain ⟨hx, hy⟩ := coords_rational_of_three_torsion h6 _ _ hn hP
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      have hx' : x' ∈ (algebraMap F Fbar).range := by
        rw [← σ.apply_symm_apply x', ← ha]
        exact map_algebraMap_mem_range (E := E) σ.toAlgHom a
      have hy' : y' ∈ (algebraMap F Fbar).range := by
        rw [← σ.apply_symm_apply y', ← hb]
        exact map_algebraMap_mem_range (E := E) σ.toAlgHom b
      exact ⟨hfixF x' hx', hfixF y' hy'⟩
  -- `σ x` is fixed by the kernel of `ρ`
  have hx' : x ∈ P.torsionField := hx
  change σ x ∈ P.torsionField
  rw [AdmissiblePrimeData.torsionField, IntermediateField.mem_fixedField_iff] at hx' ⊢
  intro τ hτ
  have hτ' : conjAut (E := E) σ τ ∈ P.rep.ker := by
    refine mem_ker_rep_of_fixes P _ fun Q hQ => ?_
    rcases Q with _ | ⟨qx, qy, hq⟩
    · rfl
    · have hn : (W.map (σ : Fbar →+* Fbar)).toAffine.Nonsingular (σ qx) (σ qy) :=
        (W.toAffine.map_nonsingular (f := (σ : Fbar →+* Fbar)) σ.injective qx qy).mpr hq
      have hR : Affine.Point.some _ _ hn ∈
          AddSubgroup.torsionBy (W.map (σ : Fbar →+* Fbar)).toAffine.Point (P.ℓ : ℤ) := by
        rw [mem_torsionBy_iff'] at hQ ⊢
        have : Affine.Point.some _ _ hn =
            pointMap W (σ : Fbar →+* Fbar) (Affine.Point.some _ _ hq) := rfl
        rw [this, ← map_zsmul, hQ, map_zero]
      obtain ⟨hx1, hy1⟩ := coords_fixed_of_variableChange P C hC hτ (hCτ τ) _ _ hn hR
      simp only [galPointMap, Affine.Point.map_some]
      refine some_ext ?_ ?_
      · change σ.symm (τ (σ qx)) = qx
        rw [hx1, σ.symm_apply_apply]
      · change σ.symm (τ (σ qy)) = qy
        rw [hy1, σ.symm_apply_apply]
  have := hx' _ hτ'
  rw [conjAut_apply] at this
  calc τ (σ x) = σ (σ.symm (τ (σ x))) := (σ.apply_symm_apply _).symm
    _ = σ x := by rw [this]

/-- **IUT I, Remark 3.1.5**: the `ℓ`-torsion field `K` is Galois over `F_mod`, if `F/F_mod` is
Galois and the `6`-torsion of `E` is rational over `F`. -/
theorem isGalois_fieldOfModuli_torsionField [IsGalois ↥(fieldOfModuli F E) F]
    (h6 : SixTorsionRational F E Fbar) :
    IsGalois ↥(fieldOfModuli F E) ↥P.torsionField := by
  have hN := normal_restrictScalars_torsionField P h6
  let e : ↥(P.torsionField.restrictScalars ↥(fieldOfModuli F E)) ≃ₐ[↥(fieldOfModuli F E)]
      ↥P.torsionField :=
    { Equiv.refl _ with
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  haveI : Normal ↥(fieldOfModuli F E) ↥P.torsionField := Normal.of_algEquiv e
  haveI : FiniteDimensional F ↥P.torsionField := P.finiteDimensional_torsionField
  haveI : FiniteDimensional ↥(fieldOfModuli F E) ↥P.torsionField :=
    Module.Finite.trans F ↥P.torsionField
  haveI : Algebra.IsSeparable ↥(fieldOfModuli F E) ↥P.torsionField :=
    Algebra.IsSeparable.of_integral _ _
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

end Galois

/-- **IUT I, Remark 3.1.5**: the `ℓ`-torsion field `K` of initial Θ-data is Galois over the field
of moduli `F_mod` (from `F/F_mod` Galois and `E[6] ⊆ E(F)`, IUT I, Definition 3.1(b)). -/
theorem InitialThetaData.isGalois_Kt (D : InitialThetaData.{u}) :
    IsGalois ↥(fieldOfModuli D.F D.E) D.Kt :=
  haveI := D.prime.galois_deg_prime.1
  isGalois_fieldOfModuli_torsionField D.prime D.global.six_torsion_rational

/-- `K/F_mod` is Galois (`Iut.InitialThetaData.isGalois_Kt`). -/
instance InitialThetaData.instIsGaloisKt (D : InitialThetaData.{u}) :
    IsGalois ↥(fieldOfModuli D.F D.E) D.Kt :=
  D.isGalois_Kt

end Iut
