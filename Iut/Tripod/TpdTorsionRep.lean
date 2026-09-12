/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.Unramified

/-!
# The mod-`n` representations of `Gal(F_λ/ℚ(λ))` on `E_λ(F_λ)[n]`, `n ∈ {3, 5}`

For a point `λ` of the tripod, the `n`-torsion of `E_λ(F_λ)` is identified with the `n`-torsion
of `E_λ(ℚ̄)` (the coordinates of the `n`-torsion lie in `F_λ` for `n = 3, 5`,
`Iut.Tripod.torsionEquivF`), hence with `(ℤ/n)²` (`Iut.Tripod.basisF`, from the bases
`Iut.Tripod.legendre_torsionBasis`). The Galois group `Gal(F_λ/ℚ(λ))` acts on `E_λ(F_λ)`
(`Iut.Tripod.galF`), and `Iut.Tripod.repF n : Gal(F_λ/ℚ(λ)) →* GL₂(ℤ/n)` is the matrix of this
action in the chosen basis; its kernel consists of the automorphisms fixing the `n`-torsion
pointwise (`Iut.Tripod.mem_repF_ker_iff`), which then fix the `n`-torsion coordinates
(`Iut.Tripod.torsionCoord_fixed_of_galF`).
-/

namespace Iut.Tripod

open Iut Iut.EllipticCurveData NumberField WeierstrassCurve WeierstrassCurve.Affine

open scoped Classical

/-! ### Points along an equality of curves -/

/-- The identification of the points of two equal curves. -/
noncomputable def castPoint {K : Type*} [Field K] {W W' : WeierstrassCurve K} (h : W = W') :
    W.toAffine.Point ≃+ W'.toAffine.Point := h ▸ AddEquiv.refl _

lemma castPoint_some {K : Type*} [Field K] {W W' : WeierstrassCurve K} (h : W = W') {a b : K}
    (hab : W.toAffine.Nonsingular a b) :
    castPoint h (Point.some a b hab) = Point.some a b (h ▸ hab) := by
  subst h; rfl

variable (P : CurveProviders) (x : Pt)

set_option quotPrecheck false in
/-- The Legendre curve `E_λ` over `F = F_λ`, as the base change of the Legendre curve of
`λ ∈ F_tpd`. -/
local notation "EF" => Affine.baseChange (legendre (genT P x)) (P.curve x).F

/-! ### The base change `E_λ(F_λ) → E_λ(ℚ̄)` -/

/-- The base change of points `E_λ(F_λ) → E_λ(ℚ̄)`. -/
noncomputable def toQbar : (EF).Point →+ (legendre x.1).toAffine.Point :=
  (castPoint (baseChange_legendre_genT_Fbar P x)).toAddMonoidHom.comp
    (Point.map (W' := legendre (genT P x)) (S := tpd P x)
      (IsScalarTower.toAlgHom (tpd P x) (P.curve x).F (P.curve x).Fbar))

lemma toQbar_injective : Function.Injective (toQbar P x) := by
  intro a b h
  exact Point.map_injective _ ((castPoint (baseChange_legendre_genT_Fbar P x)).injective h)

lemma toQbar_some {a b : (P.curve x).F} (h : (EF).Nonsingular a b) :
    toQbar P x (Point.some a b h) =
      Point.some (algebraMap (P.curve x).F (P.curve x).Fbar a)
        (algebraMap (P.curve x).F (P.curve x).Fbar b)
        ((baseChange_legendre_genT_Fbar P x) ▸
          (Affine.baseChange_nonsingular (W := legendre (genT P x))
            (IsScalarTower.toAlgHom (tpd P x) (P.curve x).F (P.curve x).Fbar).injective a b).mpr
            h) := by
  rfl

/-- **The `n`-torsion of `E_λ(ℚ̄)` comes from `E_λ(F_λ)`** when its coordinates lie in
`F_λ`. -/
theorem exists_toQbar_eq {n : ℕ} (hsub : torsionCoords x.1 n ⊆ (fieldOf' x.1 : Set Qbar))
    (Q : (legendre x.1).toAffine.Point) (hQ : n • Q = 0) : ∃ R : (EF).Point, toQbar P x R = Q := by
  cases Q with
  | zero => exact ⟨0, map_zero _⟩
  | some x₀ y₀ h₀ =>
    have hx₀ : x₀ ∈ fieldOf' x.1 := hsub (mem_torsionCoords hQ (by rw [coords_some]; simp))
    have hy₀ : y₀ ∈ fieldOf' x.1 := hsub (mem_torsionCoords hQ (by rw [coords_some]; simp))
    obtain ⟨xF, hxF⟩ : ∃ xF : (P.curve x).F, algebraMap (P.curve x).F (P.curve x).Fbar xF = x₀ :=
      ⟨⟨x₀, hx₀⟩, rfl⟩
    obtain ⟨yF, hyF⟩ : ∃ yF : (P.curve x).F, algebraMap (P.curve x).F (P.curve x).Fbar yF = y₀ :=
      ⟨⟨y₀, hy₀⟩, rfl⟩
    subst hxF hyF
    have hns' : (Affine.baseChange (legendre (genT P x)) (P.curve x).Fbar).Nonsingular
        (algebraMap (P.curve x).F (P.curve x).Fbar xF)
        (algebraMap (P.curve x).F (P.curve x).Fbar yF) := by
      rw [baseChange_legendre_genT_Fbar]; exact h₀
    have hnsF : (EF).Nonsingular xF yF :=
      (Affine.baseChange_nonsingular (W := legendre (genT P x))
        (IsScalarTower.toAlgHom (tpd P x) (P.curve x).F (P.curve x).Fbar).injective _ _).mp hns'
    exact ⟨Point.some xF yF hnsF, by rw [toQbar_some]; rfl⟩

/-! ### The torsion basis over `F_λ` -/

variable (n : ℕ) [Fact n.Prime] (hsub : torsionCoords x.1 n ⊆ (fieldOf' x.1 : Set Qbar))

omit [Fact n.Prime] in
lemma toQbar_mem_torsionBy {R : (EF).Point} (hR : R ∈ AddSubgroup.torsionBy (EF).Point n) :
    toQbar P x R ∈ AddSubgroup.torsionBy (legendre x.1).toAffine.Point n := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hR ⊢
  rw [← map_nsmul, hR, map_zero]

/-- **`E_λ(F_λ)[n] ≃ E_λ(ℚ̄)[n]`.** -/
noncomputable def torsionEquivF :
    ↥(AddSubgroup.torsionBy (EF).Point n) ≃+
      ↥(AddSubgroup.torsionBy (legendre x.1).toAffine.Point n) :=
  AddEquiv.ofBijective ((toQbar P x).restrict (AddSubgroup.torsionBy (EF).Point n) |>.codRestrict
    _ fun R => toQbar_mem_torsionBy P x n R.2)
    ⟨fun R R' h => Subtype.ext (toQbar_injective P x (congrArg Subtype.val h)),
     fun Q => by
      obtain ⟨R, hR⟩ := exists_toQbar_eq P x hsub Q.1 (AddSubgroup.torsionBy.nsmul_iff.mp Q.2)
      refine ⟨⟨R, ?_⟩, Subtype.ext hR⟩
      rw [AddSubgroup.torsionBy.nsmul_iff]
      apply toQbar_injective P x
      rw [map_nsmul, hR, map_zero]
      exact AddSubgroup.torsionBy.nsmul_iff.mp Q.2⟩

@[simp] lemma coe_torsionEquivF (R : ↥(AddSubgroup.torsionBy (EF).Point n)) :
    (torsionEquivF P x n hsub R : (legendre x.1).toAffine.Point) = toQbar P x R := rfl

/-- **A basis `E_λ(F_λ)[n] ≃ (ℤ/n)²`.** -/
noncomputable def basisF : ↥(AddSubgroup.torsionBy (EF).Point n) ≃+ (Fin 2 → ZMod n) :=
  (torsionEquivF P x n hsub).trans (legendre_torsionBasis x n).some

/-! ### The Galois action and the mod-`n` representation -/

/-- The action of `σ ∈ Gal(F_λ/ℚ(λ))` on `E_λ(F_λ)`. -/
noncomputable def galF (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) : (EF).Point →+ (EF).Point :=
  Point.map (W' := legendre (genT P x)) (S := tpd P x) (σ : (P.curve x).F →ₐ[tpd P x] (P.curve x).F)

lemma galF_one (Q : (EF).Point) : galF P x 1 Q = Q := by
  cases Q <;> rfl

lemma galF_mul (σ τ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) (Q : (EF).Point) :
    galF P x (σ * τ) Q = galF P x σ (galF P x τ Q) := by
  unfold galF
  rw [Point.map_map]
  rfl

omit [Fact n.Prime] in
lemma galF_mem_torsionBy (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) {R : (EF).Point}
    (hR : R ∈ AddSubgroup.torsionBy (EF).Point n) :
    galF P x σ R ∈ AddSubgroup.torsionBy (EF).Point n := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hR ⊢
  rw [← map_nsmul, hR, map_zero]

/-- The action on the `n`-torsion. -/
noncomputable def galTorsionF (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) :
    ↥(AddSubgroup.torsionBy (EF).Point n) →+ ↥(AddSubgroup.torsionBy (EF).Point n) :=
  (galF P x σ).restrict _ |>.codRestrict _ fun R => galF_mem_torsionBy P x n σ R.2

@[simp] lemma coe_galTorsionF (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F)
    (R : ↥(AddSubgroup.torsionBy (EF).Point n)) :
    (galTorsionF P x n σ R : (EF).Point) = galF P x σ R := rfl

/-- The linear endomorphism `b ∘ σ ∘ b⁻¹` of `(ℤ/n)²`. -/
noncomputable def repLinF (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) :
    Module.End (ZMod n) (Fin 2 → ZMod n) :=
  ((basisF P x n hsub).toAddMonoidHom.comp
    ((galTorsionF P x n σ).comp (basisF P x n hsub).symm.toAddMonoidHom)).toZModLinearMap n

lemma repLinF_apply (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) (w : Fin 2 → ZMod n) :
    repLinF P x n hsub σ w = basisF P x n hsub (galTorsionF P x n σ ((basisF P x n hsub).symm w)) :=
  rfl

/-- `σ ↦ b ∘ σ ∘ b⁻¹` as a monoid homomorphism. -/
noncomputable def repEndF :
    ((P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) →* Module.End (ZMod n) (Fin 2 → ZMod n) where
  toFun := repLinF P x n hsub
  map_one' := by
    refine LinearMap.ext fun w => ?_
    rw [repLinF_apply, Module.End.one_apply]
    have h : galTorsionF P x n 1 ((basisF P x n hsub).symm w) = (basisF P x n hsub).symm w :=
      Subtype.ext (galF_one P x _)
    rw [h, (basisF P x n hsub).apply_symm_apply]
  map_mul' σ τ := by
    refine LinearMap.ext fun w => ?_
    rw [Module.End.mul_apply, repLinF_apply, repLinF_apply, repLinF_apply,
      (basisF P x n hsub).symm_apply_apply]
    congr 1
    exact Subtype.ext (galF_mul P x σ τ _)

/-- **The mod-`n` representation** `Gal(F_λ/ℚ(λ)) →* GL₂(ℤ/n)` in the basis `b`. -/
noncomputable def repF : ((P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) →*
    Matrix.GeneralLinearGroup (Fin 2) (ZMod n) :=
  (Units.mapEquiv (LinearMap.toMatrixAlgEquiv' :
    Module.End (ZMod n) (Fin 2 → ZMod n) ≃ₐ[ZMod n] Matrix (Fin 2) (Fin 2) (ZMod n)).toMulEquiv
    ).toMonoidHom.comp (repEndF P x n hsub).toHomUnits

/-- `σ ∈ ker ρₙ` iff `σ` fixes every `n`-torsion point of `E_λ(F_λ)`. -/
theorem mem_repF_ker_iff (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) :
    σ ∈ (repF P x n hsub).ker ↔ ∀ Q : (EF).Point, n • Q = 0 → galF P x σ Q = Q := by
  rw [MonoidHom.mem_ker, repF, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one]
  change repLinF P x n hsub σ = 1 ↔ _
  constructor
  · intro h Q hQ
    have hv := LinearMap.congr_fun h (basisF P x n hsub ⟨Q, AddSubgroup.torsionBy.nsmul_iff.mpr hQ⟩)
    rw [repLinF_apply, (basisF P x n hsub).symm_apply_apply, Module.End.one_apply] at hv
    exact congrArg Subtype.val ((basisF P x n hsub).injective hv)
  · intro h
    refine LinearMap.ext fun w => ?_
    have hv : galTorsionF P x n σ ((basisF P x n hsub).symm w) = (basisF P x n hsub).symm w :=
      Subtype.ext (h _ (AddSubgroup.torsionBy.nsmul_iff.mp ((basisF P x n hsub).symm w).2))
    rw [repLinF_apply, Module.End.one_apply, hv, (basisF P x n hsub).apply_symm_apply]

/-! ### The torsion coordinates are fixed by the kernel -/

include hsub in
/-- An automorphism fixing the `n`-torsion of `E_λ(F_λ)` pointwise fixes its coordinates. -/
theorem torsionCoord_fixed_of_galF (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F)
    (hσ : ∀ Q : (EF).Point, n • Q = 0 → galF P x σ Q = Q) {c : Qbar}
    (hc : c ∈ torsionCoords x.1 n) (hcF : c ∈ fieldOf' x.1) : σ ⟨c, hcF⟩ = ⟨c, hcF⟩ := by
  obtain ⟨Q, hQ, hcQ⟩ := Set.mem_iUnion₂.mp hc
  have hQ' : n • Q = 0 := hQ
  obtain ⟨R, hR⟩ := exists_toQbar_eq P x hsub Q hQ'
  have hRn : n • R = 0 := by
    apply toQbar_injective P x
    rw [map_nsmul, hR, map_zero]
    exact hQ'
  cases R with
  | zero =>
    change toQbar P x 0 = Q at hR
    rw [map_zero] at hR
    subst hR
    exact absurd hcQ (Set.notMem_empty c)
  | some xF yF hF =>
    have hfix := hσ _ hRn
    unfold galF at hfix
    rw [Point.map_some] at hfix
    obtain ⟨hfx, hfy⟩ := Point.some.inj hfix
    rw [toQbar_some] at hR
    subst hR
    change c ∈ ({algebraMap (P.curve x).F (P.curve x).Fbar xF,
      algebraMap (P.curve x).F (P.curve x).Fbar yF} : Set Qbar) at hcQ
    rcases hcQ with rfl | rfl
    · have hc : (⟨_, hcF⟩ : (P.curve x).F) = xF := Subtype.ext rfl
      rw [hc]; exact hfx
    · have hc : (⟨_, hcF⟩ : (P.curve x).F) = yF := Subtype.ext rfl
      rw [hc]; exact hfy

end Iut.Tripod
