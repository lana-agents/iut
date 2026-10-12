/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Inertia
import LocalClassFieldTheory.Brauer.LocalGalois

/-!
# Tame inertia and the group-theoretic Frobenius (roadmap P17, M1e)

[AbsAnab], Proposition 1.2.1 (iv) (and [AbsTopIII], Proposition 5.8 (i)): the Frobenius element
of `G_K / I_K` is determined by the topological group `G_K`. It is characterised by its
conjugation action on the tame inertia group `I_K / P_K ≅ ∏_{ℓ ≠ p} ℤ_ℓ(1)`: a lift `φ ∈ G_K`
of the Frobenius acts on `I_K / P_K` by the `q`-th power. We use the finite-level form: for every
`n` prime to `p` and every continuous character `χ : I_K → ℤ/n` (these factor through
`I_K / P_K`),

`χ(φ τ φ⁻¹) = q · χ(τ)`  for all `τ ∈ I_K`.

* **Lifts of Frobenius satisfy this** (`char_conj_of_frob`): `χ` factors through a finite Galois
  level `L/K`; at that level the tame character `σ ↦ σ(π_L)/π_L mod 𝔪_L` of
  `local-class-field-theory` (whose kernel, the wild inertia group, is a `p`-group) satisfies
  `θ(φ τ φ⁻¹) = θ(τ)^q` (`tameChar_conj`), so `χ(φ τ φ⁻¹ τ^{-q})` has `p`-power order in
  `ℤ/n`, hence vanishes.
* **Only lifts of Frobenius satisfy this** (`mk_eq_arithFrob_of_char_conj`): for
  `n = q^m − 1` and `α^n = π_K`, the Kummer character `τ ↦ τ(α)/α` of `I_K` is onto `μ_n`
  (`kummerChar_surjective`; otherwise `α^d ∈ K^ur` for a proper divisor `d` of `n`, contradicting
  `v(π_K) = 1` in the unramified `K_m`), and `θ(σ τ σ⁻¹) = σ(θ(τ))` (`kummerRatio_conj`). So an
  element satisfying the identity acts on `μ_{q^m − 1}` as `ζ ↦ ζ^q`, i.e. as the Frobenius on
  every `K_m`, hence on `K^ur`.

## Main definitions and results

* `Iut.Reconstruction.IsFrobLift G φ` — group-theoretic in `G` (`IsFrobLift.map`);
* `Iut.Reconstruction.isFrobLift_gal_iff`: for `G = Gal(Ω/K)`, `IsFrobLift G σ` iff
  `σ ≡ Frob (mod I_K)`;
* `Iut.Reconstruction.galEquiv_arithFrob`: every isomorphism of topological groups
  `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` maps lifts of the Frobenius to lifts of the Frobenius.
-/

open PadicField IsLocalRing IntermediateField

set_option linter.unusedSectionVars false

namespace Iut.Reconstruction

section Tame

variable {p : ℕ} [hp : Fact p.Prime]
variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L]

omit [FiniteDimensional ℚ_[p] K] in
theorem residue_smul_of_mem_inertia {τ : L ≃ₐ[K] L} (hτ : τ ∈ inertia p K L) (x : 𝒪 p L) :
    residue (𝒪 p L) (τ • x) = residue (𝒪 p L) x := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact hτ x

theorem coe_unitOfNrm_inv (x : L) (hx : nrm p L x = 1) :
    ((((unitOfNrm x hx)⁻¹ : (𝒪 p L)ˣ) : 𝒪 p L) : L) = x⁻¹ := rfl

/-- **Tame inertia and Frobenius** (finite level): if `σ` acts on residues as `x ↦ x ^ Q`, then
`θ(σ τ σ⁻¹) = θ(τ) ^ Q` for the tame character `θ`. -/
theorem tameChar_conj {σ : L ≃ₐ[K] L} {Q : ℕ}
    (hσ : ∀ w : 𝒪 p L, σ • w - w ^ Q ∈ maximalIdeal (𝒪 p L)) (τ c : inertia p K L)
    (hc : (c : L ≃ₐ[K] L) = σ * τ * σ⁻¹) : tameChar c = tameChar τ ^ Q := by
  set π := uniformizer p L with hπdef
  have hπ : π ≠ 0 := (uniformizer_spec (p := p) (K := L)).ne_zero
  set y := σ⁻¹ π with hydef
  have hy : y ≠ 0 := by
    rw [hydef]; exact (map_ne_zero_iff _ (σ⁻¹).injective).2 hπ
  have hσy : σ y = π := by
    rw [hydef, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have hu : nrm p L (y / π) = 1 := by
    rw [nrm_div, hydef, nrm_algEquiv_tower, div_self]
    exact (nrm_pos_iff.2 hπ).ne'
  set u := unitOfNrm (y / π) hu
  set W : 𝒪 p L := (τ : L ≃ₐ[K] L) • (u : 𝒪 p L) * ((u⁻¹ : (𝒪 p L)ˣ) : 𝒪 p L) *
    (ratioUnit (p := p) (τ : L ≃ₐ[K] L) : 𝒪 p L)
  have key : (ratioUnit (p := p) (c : L ≃ₐ[K] L) : 𝒪 p L) = σ • W := by
    apply Integers.ext
    rw [Integers.coe_smul]
    simp only [W, Integers.coe_mul, Integers.coe_smul, coe_ratioUnit, coe_unitOfNrm_inv, u,
      coe_unitOfNrm, hc, AlgEquiv.mul_apply]
    have h1 : σ⁻¹ π = y := rfl
    have hτy : (τ : L ≃ₐ[K] L) y ≠ 0 := (map_ne_zero_iff _ (τ : L ≃ₐ[K] L).injective).2 hy
    have hτπ : (τ : L ≃ₐ[K] L) π ≠ 0 := (map_ne_zero_iff _ (τ : L ≃ₐ[K] L).injective).2 hπ
    have : (τ : L ≃ₐ[K] L) y / (τ : L ≃ₐ[K] L) π * (y / π)⁻¹ *
        ((τ : L ≃ₐ[K] L) π / π) = (τ : L ≃ₐ[K] L) y / y := by
      field_simp
    rw [← hπdef, h1, map_div₀ (τ : L ≃ₐ[K] L) y π, this, map_div₀, hσy]
  have hres : residue (𝒪 p L) W =
      residue (𝒪 p L) (ratioUnit (p := p) (τ : L ≃ₐ[K] L) : 𝒪 p L) := by
    simp only [W, map_mul, residue_smul_of_mem_inertia τ.2]
    rw [← map_mul, Units.mul_inv, map_one, one_mul]
  ext
  change residue (𝒪 p L) (ratioUnit (p := p) (c : L ≃ₐ[K] L) : 𝒪 p L) =
    (residue (𝒪 p L) (ratioUnit (p := p) (τ : L ≃ₐ[K] L) : 𝒪 p L)) ^ Q
  rw [key, ← hres, ← map_pow]
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact hσ W

end Tame

/-- In `ℤ/n` with `p ∤ n`, an element killed by a power of `p` is zero. -/
theorem eq_one_of_pow_p_pow {p n : ℕ} (hn : p.Coprime n) {x : Multiplicative (ZMod n)} {k : ℕ}
    (hx : x ^ p ^ k = 1) : x = 1 := by
  have hu : IsUnit ((p ^ k : ℕ) : ZMod n) :=
    (ZMod.unitOfCoprime (p ^ k) (Nat.Coprime.pow_left k hn)).isUnit
  have h : ((p ^ k : ℕ) : ZMod n) * x.toAdd = 0 := by
    rw [← nsmul_eq_mul, ← toAdd_pow, hx, toAdd_one]
  rw [hu.mul_right_eq_zero] at h
  exact toAdd_eq_zero.1 h

section Absolute

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

omit [IsAlgClosed Ω] [IsGalois K Ω] in
theorem nrm_coe_intermediate (L : IntermediateField K Ω) [FiniteDimensional K L] (x : L) :
    nrm p Ω (x : Ω) = nrm p L x :=
  nrm_algebraMap_tower (K := L) (L := Ω) x

omit [IsAlgClosed Ω] [IsGalois K Ω] in
/-- Restriction maps the absolute inertia group into the inertia group of a finite Galois
level. -/
theorem restrict_mem_inertia (L : IntermediateField K Ω) [FiniteDimensional K L] [Normal K L]
    {τ : Ω ≃ₐ[K] Ω} (hτ : τ ∈ absInertia p K Ω) :
    AlgEquiv.restrictNormalHom L τ ∈ inertia p K L := by
  intro x
  change _ ∈ maximalIdeal (𝒪 p L)
  rw [Integers.mem_maximalIdeal_iff, ← nrm_coe_intermediate L]
  have h1 : (((AlgEquiv.restrictNormalHom L τ • x - x : 𝒪 p L) : L) : Ω) =
      τ ((x : L) : Ω) - ((x : L) : Ω) := by
    rw [Integers.coe_sub, Integers.coe_smul]
    push_cast
    rw [AlgEquiv.restrictNormalHom_apply]
  rw [h1]
  refine hτ _ ?_
  rw [nrm_coe_intermediate L]
  exact Integers.nrm_coe_le_one x

omit [IsGalois K Ω] in
/-- A lift of the Frobenius acts on the residues of a finite Galois level as `x ↦ x ^ q`. -/
theorem restrict_frob_spec (L : IntermediateField K Ω) [FiniteDimensional K L] [Normal K L]
    {σ : Ω ≃ₐ[K] Ω} (hσ : QuotientGroup.mk σ = arithFrob p K Ω) (w : 𝒪 p L) :
    AlgEquiv.restrictNormalHom L σ • w - w ^ q p K ∈ maximalIdeal (𝒪 p L) := by
  rw [Integers.mem_maximalIdeal_iff, ← nrm_coe_intermediate L]
  have h1 : (((AlgEquiv.restrictNormalHom L σ • w - w ^ q p K : 𝒪 p L) : L) : Ω) =
      σ ((w : L) : Ω) - ((w : L) : Ω) ^ q p K := by
    rw [Integers.coe_sub, Integers.coe_smul, Integers.coe_pow]
    push_cast
    rw [AlgEquiv.restrictNormalHom_apply]
  rw [h1]
  refine arithFrob_spec hσ ?_
  rw [nrm_coe_intermediate L]
  exact Integers.nrm_coe_le_one w

/-- **Lifts of the Frobenius act on tame characters by `q`** ([AbsAnab], 1.2.1 (iv)): for
`p ∤ n`, a continuous character `χ : I_K → ℤ/n` and `τ ∈ I_K`, `χ(σ τ σ⁻¹) = q · χ(τ)`. -/
theorem char_conj_of_frob {σ : Ω ≃ₐ[K] Ω} (hσ : QuotientGroup.mk σ = arithFrob p K Ω)
    {n : ℕ} (hn : p.Coprime n) (χ : absInertia p K Ω →* Multiplicative (ZMod n))
    (hχ : IsLocallyConstant χ) (τ τ' : absInertia p K Ω)
    (h : (τ' : Ω ≃ₐ[K] Ω) = σ * τ * σ⁻¹) : χ τ' = χ τ ^ q p K := by
  -- a finite Galois level `E` with `Gal(Ω/E) ∩ I_K ⊆ ker χ`
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.1 (hχ.isOpen_fiber 1)
  have h1V : (1 : Ω ≃ₐ[K] Ω) ∈ V := by
    have : (1 : absInertia p K Ω) ∈ Subtype.val ⁻¹' V := by
      rw [hVeq]; exact map_one χ
    exact this
  haveI : Normal K Ω := IsGalois.to_normal
  obtain ⟨E, hEfin, hEnorm, hEV⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K Ω V).1 (hV.mem_nhds h1V)
  haveI := hEfin
  haveI := hEnorm
  set ρ : absInertia p K Ω := τ' * (τ ^ q p K)⁻¹ with hρ
  have hker : ∀ x : absInertia p K Ω, (x : Ω ≃ₐ[K] Ω) ∈ E.fixingSubgroup → χ x = 1 := by
    intro x hx
    have : x ∈ Subtype.val ⁻¹' V := hEV hx
    rw [hVeq] at this
    exact this
  -- the tame character of the restriction of `ρ` is trivial
  set r : E ≃ₐ[K] E := AlgEquiv.restrictNormalHom E (ρ : Ω ≃ₐ[K] Ω)
  have hr : r ∈ inertia p K E := restrict_mem_inertia E ρ.2
  set t : inertia p K E := ⟨AlgEquiv.restrictNormalHom E (τ : Ω ≃ₐ[K] Ω),
    restrict_mem_inertia E τ.2⟩
  set c : inertia p K E := ⟨AlgEquiv.restrictNormalHom E (τ' : Ω ≃ₐ[K] Ω),
    restrict_mem_inertia E τ'.2⟩
  have hc : (c : E ≃ₐ[K] E) = AlgEquiv.restrictNormalHom E σ * t *
      (AlgEquiv.restrictNormalHom E σ)⁻¹ := by
    simp only [c, t, h, map_mul, map_inv]
  have htc := tameChar_conj (restrict_frob_spec E hσ) t c hc
  have hrtc : (⟨r, hr⟩ : inertia p K E) = c * (t ^ q p K)⁻¹ := by
    apply Subtype.ext
    simp only [r, c, t, hρ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, map_mul,
      map_inv, map_pow]
  have hrk : tameChar (⟨r, hr⟩ : inertia p K E) = 1 := by
    rw [hrtc, map_mul, map_inv, map_pow, htc, mul_inv_cancel]
  obtain ⟨k, hk⟩ := isPGroup_ker_tameChar (p := p) (K := K) (L := E) ⟨⟨r, hr⟩, hrk⟩
  have hrk' : r ^ p ^ k = 1 := by
    have := congrArg Subtype.val (congrArg Subtype.val hk)
    simpa using this
  have hmem : ((ρ ^ p ^ k : absInertia p K Ω) : Ω ≃ₐ[K] Ω) ∈ E.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, Subgroup.coe_pow,
      map_pow]
    exact hrk'
  have hχρ : χ ρ = 1 := eq_one_of_pow_p_pow hn (by rw [← map_pow]; exact hker _ hmem)
  rw [hρ, map_mul, map_inv, map_pow, mul_inv_eq_one] at hχρ
  exact hχρ

/-! ### The tame Kummer character `τ ↦ τ(α)/α`, `α ^ (q ^ m - 1) = π_K` -/

section Kummer

variable {m : ℕ} {α : Ω}

omit [IsGalois K Ω] in
theorem one_lt_q_pow' (hm : 0 < m) : 1 < q p K ^ m := Nat.one_lt_pow hm.ne' (one_lt_q p K)

theorem pow_eq_self_of_pow_eq_one {N : ℕ} (hN : 1 ≤ N) {ζ : Ω} (hζ : ζ ^ (N - 1) = 1) :
    ζ ^ N = ζ := by
  rw [show N = (N - 1) + 1 by omega, pow_succ, hζ, one_mul]

omit [IsGalois K Ω] in
/-- Inertia fixes the `(q ^ m - 1)`-th roots of unity. -/
theorem absInertia_fix_root (hm : 0 < m) {τ : Ω ≃ₐ[K] Ω} (hτ : τ ∈ absInertia p K Ω) {ζ : Ω}
    (hζ : ζ ^ (q p K ^ m - 1) = 1) : τ ζ = ζ :=
  absInertia_apply_eq_of_pow_eq hτ hm (pow_eq_self_of_pow_eq_one (one_lt_q_pow' hm).le hζ)

omit [IsGalois K Ω] in
/-- `p ∤ q ^ m - 1`. -/
theorem coprime_q_pow_sub_one (hm : 0 < m) : p.Coprime (q p K ^ m - 1) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp.out]
  intro h
  have h1 : p ∣ q p K ^ m := by
    rw [q_eq_p_pow_f, ← pow_mul]
    exact dvd_pow_self p (Nat.mul_ne_zero (f_pos (p := p)).ne' hm.ne')
  have h2 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self (one_lt_q_pow' hm).le] at h2
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h2)

/-- The Kummer ratio `τ(α)/α`. -/
noncomputable def kummerRatio (α : Ω) (τ : Ω ≃ₐ[K] Ω) : Ω := τ α / α

variable (hm : 0 < m) (hα : α ^ (q p K ^ m - 1) = algebraMap K Ω (uniformizer p K))
include hm hα

omit [IsGalois K Ω] in
theorem ne_zero_of_kummer : α ≠ 0 := by
  rintro rfl
  rw [zero_pow (by have := one_lt_q_pow' (p := p) (K := K) hm; omega)] at hα
  exact (uniformizer_spec (p := p) (K := K)).ne_zero
    ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hα.symm)

omit [IsGalois K Ω] in
theorem kummerRatio_pow (τ : Ω ≃ₐ[K] Ω) : kummerRatio α τ ^ (q p K ^ m - 1) = 1 := by
  rw [kummerRatio, div_pow, ← map_pow, hα, AlgEquiv.commutes, div_self]
  exact (map_ne_zero_iff _ (algebraMap K Ω).injective).2
    (uniformizer_spec (p := p) (K := K)).ne_zero

omit [IsGalois K Ω] in
theorem kummerRatio_ne_zero (τ : Ω ≃ₐ[K] Ω) : kummerRatio α τ ≠ 0 := by
  have h0 := ne_zero_of_kummer hm hα
  exact div_ne_zero ((map_ne_zero_iff _ τ.injective).2 h0) h0

omit [IsGalois K Ω] in
/-- An element of inertia multiplies every root of `X ^ (q ^ m - 1) - π` by the same root of
unity. -/
theorem apply_root_eq {τ : Ω ≃ₐ[K] Ω} (hτ : τ ∈ absInertia p K Ω) {β : Ω}
    (hβ : β ^ (q p K ^ m - 1) = algebraMap K Ω (uniformizer p K)) :
    τ β = kummerRatio α τ * β := by
  have h0 := ne_zero_of_kummer hm hα
  have hc : (β / α) ^ (q p K ^ m - 1) = 1 := by
    rw [div_pow, hβ, hα, div_self]
    exact (map_ne_zero_iff _ (algebraMap K Ω).injective).2
      (uniformizer_spec (p := p) (K := K)).ne_zero
  have hfix := absInertia_fix_root hm hτ hc
  have hβα : β = β / α * α := by field_simp
  rw [hβα, map_mul, hfix, kummerRatio]
  field_simp

omit [IsGalois K Ω] in
theorem kummerRatio_mul {τ₁ : Ω ≃ₐ[K] Ω} (h₁ : τ₁ ∈ absInertia p K Ω) (τ₂ : Ω ≃ₐ[K] Ω) :
    kummerRatio α (τ₁ * τ₂) = kummerRatio α τ₁ * kummerRatio α τ₂ := by
  have h0 := ne_zero_of_kummer hm hα
  have hfix := absInertia_fix_root hm h₁ (kummerRatio_pow hm hα τ₂)
  have h2 : τ₂ α = kummerRatio α τ₂ * α := by rw [kummerRatio]; field_simp
  rw [kummerRatio, AlgEquiv.mul_apply, h2, map_mul, hfix, kummerRatio]
  field_simp
  rw [kummerRatio]
  field_simp

omit [IsGalois K Ω] in
/-- **Conjugation and the Kummer character**: `θ(σ τ σ⁻¹) = σ(θ(τ))`. -/
theorem kummerRatio_conj (σ : Ω ≃ₐ[K] Ω) {τ : Ω ≃ₐ[K] Ω} (hτ : τ ∈ absInertia p K Ω) :
    kummerRatio α (σ * τ * σ⁻¹) = σ (kummerRatio α τ) := by
  have h0 := ne_zero_of_kummer hm hα
  have hβ : (σ⁻¹ α) ^ (q p K ^ m - 1) = algebraMap K Ω (uniformizer p K) := by
    rw [← map_pow, hα, AlgEquiv.commutes]
  have h1 := apply_root_eq hm hα hτ hβ
  rw [kummerRatio, AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, map_mul]
  rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  field_simp

/-- **The tame Kummer character** `I_K → μ_{q^m - 1}`, `τ ↦ τ(α)/α`. -/
noncomputable def kummerChar : absInertia p K Ω →* rootsOfUnity (q p K ^ m - 1) Ω where
  toFun τ := ⟨Units.mk0 (kummerRatio α (τ : Ω ≃ₐ[K] Ω)) (kummerRatio_ne_zero hm hα τ), by
    rw [mem_rootsOfUnity]
    ext
    simp [kummerRatio_pow hm hα]⟩
  map_one' := by
    ext
    simp [kummerRatio, ne_zero_of_kummer hm hα]
  map_mul' τ₁ τ₂ := by
    ext
    simp [kummerRatio_mul hm hα τ₁.2]

theorem coe_kummerChar (τ : absInertia p K Ω) :
    (((kummerChar hm hα τ : rootsOfUnity (q p K ^ m - 1) Ω) : Ωˣ) : Ω) =
      kummerRatio α (τ : Ω ≃ₐ[K] Ω) := rfl

theorem isLocallyConstant_kummerChar : IsLocallyConstant (kummerChar hm hα) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro τ
  haveI := isAlgebraic_tower_top p K Ω
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  haveI : FiniteDimensional K K⟮α⟯ := IntermediateField.adjoin.finiteDimensional hint
  have hopen := (K⟮α⟯).fixingSubgroup_isOpen
  refine ⟨(fun τ' : absInertia p K Ω => (τ : Ω ≃ₐ[K] Ω)⁻¹ * τ') ⁻¹'
    ((K⟮α⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)),
    hopen.preimage (continuous_const.mul continuous_subtype_val), ?_, ?_⟩
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact one_mem _
  · intro τ' hτ'
    have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ' α
      (IntermediateField.mem_adjoin_simple_self K α)
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at h1
    apply Subtype.ext
    apply Units.ext
    rw [coe_kummerChar, coe_kummerChar, kummerRatio, kummerRatio, h1]

/-- **The tame Kummer character is onto `μ_{q^m - 1}`**: otherwise its image is `μ_d` for a
proper divisor `d` of `q^m - 1`, so `α^d` is fixed by inertia, i.e. lies in some unramified
`K_k`, where `v(π_K) = 1` forbids `(α^d)^{(q^m - 1)/d} = π_K`. -/
theorem kummerChar_surjective : Function.Surjective (kummerChar hm hα) := by
  set N := q p K ^ m - 1 with hN
  have hN0 : 0 < N := by have := one_lt_q_pow' (p := p) (K := K) hm; omega
  haveI : NeZero N := ⟨hN0.ne'⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ_[p] Ω).injective
  haveI : NeZero (N : Ω) := ⟨Nat.cast_ne_zero.2 hN0.ne'⟩
  have hcard : Nat.card (rootsOfUnity N Ω) = N :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω N
  set H := (kummerChar hm hα).range
  set d := Nat.card H
  have hdN : d ∣ N := hcard ▸ Subgroup.card_subgroup_dvd_card H
  have hd0 : 0 < d := Nat.pos_of_ne_zero (fun h => by
    rw [h, zero_dvd_iff] at hdN; exact hN0.ne' hdN)
  -- `α ^ d` is fixed by inertia
  have hfix : ∀ τ ∈ absInertia p K Ω, τ (α ^ d) = α ^ d := by
    intro τ hτ
    have h1 : (⟨kummerChar hm hα ⟨τ, hτ⟩, ⟨τ, hτ⟩, rfl⟩ : H) ^ d = 1 := pow_card_eq_one'
    have h2 : kummerRatio α τ ^ d = 1 := by
      have := congrArg (fun x : H => (((x : rootsOfUnity N Ω) : Ωˣ) : Ω)) h1
      simpa [coe_kummerChar] using this
    have h0 := ne_zero_of_kummer hm hα
    have h3 : τ α = kummerRatio α τ * α := by rw [kummerRatio]; field_simp
    rw [map_pow, h3, mul_pow, h2, one_mul]
  have hmem : α ^ d ∈ maxUnramified p K Ω := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (maxUnramified p K Ω), ← absInertia_eq]
    exact fun τ => hfix τ τ.2
  obtain ⟨k, hk, hkmem⟩ := (mem_maxUnramified_iff (p := p)).1 hmem
  set E := unramifiedOfDegree p K Ω k
  set β : E := ⟨α ^ d, hkmem⟩
  have hβ0 : β ≠ 0 := by
    intro h
    have : α ^ d = 0 := congrArg Subtype.val h
    exact ne_zero_of_kummer hm hα (pow_eq_zero_iff hd0.ne' |>.1 this)
  obtain ⟨c, hc⟩ := hdN
  have hβc : β ^ c = algebraMap K E (uniformizer p K) := by
    apply Subtype.ext
    change (α ^ d) ^ c = algebraMap K Ω (uniformizer p K)
    rw [← pow_mul, ← hc, hα]
  have hv := congrArg (v p) hβc
  rw [v_pow hβ0, v_algebraMap, isUnramified_unramifiedOfDegree (p := p) (K := K) (Ω := Ω) k,
    (uniformizer_spec (p := p) (K := K))] at hv
  norm_num at hv
  have hc1 : (c : ℤ) = 1 :=
    Int.eq_one_of_mul_eq_one_right (Int.natCast_nonneg c) hv
  have hc1' : c = 1 := by exact_mod_cast hc1
  rw [hc1', mul_one] at hc
  have htop : H = ⊤ := Subgroup.eq_top_of_card_eq H (by rw [hcard]; exact hc.symm)
  exact MonoidHom.range_eq_top.1 htop

end Kummer

/-- The Frobenius condition: `σ` acts on the prime-to-`p` characters of `I_K` by `q`. -/
def FrobCond (σ : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ n : ℕ, p.Coprime n → ∀ χ : absInertia p K Ω →* Multiplicative (ZMod n),
    IsLocallyConstant χ → ∀ τ τ' : absInertia p K Ω, (τ' : Ω ≃ₐ[K] Ω) = σ * τ * σ⁻¹ →
      χ τ' = χ τ ^ q p K

theorem frobCond_of_mk_eq {σ : Ω ≃ₐ[K] Ω} (hσ : QuotientGroup.mk σ = arithFrob p K Ω) :
    FrobCond (p := p) σ :=
  fun _ hn χ hχ τ τ' h => char_conj_of_frob hσ hn χ hχ τ τ' h

/-- An element satisfying the Frobenius condition acts on the roots of `X ^ (q ^ m) - X` as
`y ↦ y ^ q`. -/
theorem apply_root_of_frobCond {σ : Ω ≃ₐ[K] Ω} (h : FrobCond (p := p) σ) {m : ℕ} (hm : 0 < m)
    {y : Ω} (hy : y ^ q p K ^ m = y) : σ y = y ^ q p K := by
  by_cases hy0 : y = 0
  · subst hy0
    rw [map_zero, zero_pow (by have := one_lt_q p K; omega)]
  set N := q p K ^ m - 1 with hN
  have hN0 : 0 < N := by have := one_lt_q_pow' (p := p) (K := K) hm; omega
  haveI : NeZero N := ⟨hN0.ne'⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ_[p] Ω).injective
  haveI : NeZero (N : Ω) := ⟨Nat.cast_ne_zero.2 hN0.ne'⟩
  have hyN : y ^ N = 1 := by
    have h1 : y ^ N * y = 1 * y := by
      rw [← pow_succ, one_mul, hN, Nat.sub_add_cancel (one_lt_q_pow' hm).le, hy]
    exact mul_right_cancel₀ hy0 h1
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (uniformizer p K)) hN0
  set ζ : rootsOfUnity N Ω := ⟨Units.mk0 y hy0, by
    rw [mem_rootsOfUnity]; ext; simp [hyN]⟩
  obtain ⟨τ, hτ⟩ := kummerChar_surjective hm hα ζ
  have hcard : Nat.card (rootsOfUnity N Ω) = Nat.card (Multiplicative (ZMod N)) := by
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω N]
    simp
  set e : rootsOfUnity N Ω ≃* Multiplicative (ZMod N) := mulEquivOfCyclicCardEq hcard
  set χ : absInertia p K Ω →* Multiplicative (ZMod N) :=
    e.toMonoidHom.comp (kummerChar hm hα)
  have hχ : IsLocallyConstant χ := (isLocallyConstant_kummerChar hm hα).comp e
  set τ' : absInertia p K Ω :=
    ⟨σ * τ * σ⁻¹, (absInertia_normal (p := p) (K := K) (Ω := Ω)).conj_mem _ τ.2 σ⟩
  have h1 := h N (coprime_q_pow_sub_one hm) χ hχ τ τ' rfl
  change e (kummerChar hm hα τ') = e (kummerChar hm hα τ) ^ q p K at h1
  rw [← map_pow] at h1
  have h2 := congrArg (fun x : rootsOfUnity N Ω => ((x : Ωˣ) : Ω)) (e.injective h1)
  simp only [coe_kummerChar, Subgroup.coe_pow, Units.val_pow_eq_pow_val] at h2
  rw [kummerRatio_conj hm hα σ τ.2] at h2
  have h3 : kummerRatio α (τ : Ω ≃ₐ[K] Ω) = y := by
    have := congrArg (fun x : rootsOfUnity N Ω => ((x : Ωˣ) : Ω)) hτ
    simpa [coe_kummerChar, ζ] using this
  rwa [h3] at h2

/-- **Only lifts of the Frobenius satisfy the Frobenius condition.** -/
theorem mk_eq_arithFrob_of_frobCond {σ : Ω ≃ₐ[K] Ω} (h : FrobCond (p := p) σ) :
    QuotientGroup.mk σ = arithFrob p K Ω := by
  obtain ⟨φ, hφ⟩ := QuotientGroup.mk_surjective (arithFrob p K Ω)
  rw [← hφ, QuotientGroup.eq, absInertia_eq, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  obtain ⟨k, hk, hxk⟩ := (mem_maxUnramified_iff (p := p)).1 hx
  have hle : unramifiedOfDegree p K Ω k ≤
      IntermediateField.fixedField (Subgroup.zpowers (σ⁻¹ * φ)) := by
    rw [unramifiedOfDegree_def, IntermediateField.adjoin_le_iff]
    intro y hy
    have hy' : y ^ q p K ^ k = y := (mem_rootSet_X_pow_sub_X (one_lt_q_pow hk)).1 hy
    have hagree : (σ⁻¹ * φ) y = y := by
      rw [AlgEquiv.mul_apply, arithFrob_apply_of_pow_eq hφ hk hy',
        ← apply_root_of_frobCond h hk hy', AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have hst : σ⁻¹ * φ ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) y := hagree
    exact (Subgroup.zpowers_le.2 hst) hf
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hxk) _ (Subgroup.mem_zpowers _)

/-- **The Frobenius condition characterises the lifts of the Frobenius.** -/
theorem frobCond_iff (σ : Ω ≃ₐ[K] Ω) :
    FrobCond (p := p) σ ↔ QuotientGroup.mk σ = arithFrob p K Ω :=
  ⟨mk_eq_arithFrob_of_frobCond, frobCond_of_mk_eq⟩

end Absolute

/-! ### The group-theoretic Frobenius -/

section GroupTheoretic

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

/-- **Lifts of the Frobenius, group-theoretically**: `φ ∈ G` acts by the `recQ G`-th power on
every continuous character `recInertia G → ℤ/n` with `n` prime to `recPrime G`. -/
def IsFrobLift (G : Type*) [Group G] [TopologicalSpace G] (φ : G) : Prop :=
  ∀ n : ℕ, (recPrime G).Coprime n → ∀ χ : recInertia G →* Multiplicative (ZMod n),
    IsLocallyConstant χ → ∀ τ τ' : recInertia G, (τ' : G) = φ * τ * φ⁻¹ →
      χ τ' = χ τ ^ recQ G

theorem mem_recInertia_iff_map (ψ : G ≃ₜ* G') {x : G} :
    ψ x ∈ recInertia G' ↔ x ∈ recInertia G := by
  rw [← comap_recInertia ψ]
  rfl

/-- An isomorphism of topological groups restricted to the reconstructed inertia subgroups. -/
noncomputable def inertiaHom (ψ : G ≃ₜ* G') : recInertia G →* recInertia G' :=
  MonoidHom.codRestrict (ψ.toMulEquiv.toMonoidHom.comp (recInertia G).subtype) _
    (fun x => (mem_recInertia_iff_map ψ).2 x.2)

theorem continuous_inertiaHom (ψ : G ≃ₜ* G') : Continuous (inertiaHom ψ) :=
  Continuous.subtype_mk (ψ.continuous.comp continuous_subtype_val) _

/-- **The Frobenius condition is group-theoretic.** -/
theorem IsFrobLift.map (ψ : G ≃ₜ* G') {φ : G} (h : IsFrobLift G φ) : IsFrobLift G' (ψ φ) := by
  intro n hn χ hχ τ τ' hτ'
  have hp : recPrime G = recPrime G' := by simp only [recPrime, charCountFun_congr ψ]
  have hq : recQ G = recQ G' := by simp only [recQ, hp, charCountFun_congr ψ]
  have hσ : ψ.symm τ ∈ recInertia G := by
    rw [← mem_recInertia_iff_map ψ, ψ.apply_symm_apply]; exact τ.2
  have hσ' : ψ.symm τ' ∈ recInertia G := by
    rw [← mem_recInertia_iff_map ψ, ψ.apply_symm_apply]; exact τ'.2
  have hconj : ((⟨ψ.symm τ', hσ'⟩ : recInertia G) : G) = φ * ψ.symm τ * φ⁻¹ := by
    apply ψ.injective
    simp [hτ']
  have := h n (hp ▸ hn) (χ.comp (inertiaHom ψ)) (hχ.comp_continuous (continuous_inertiaHom ψ))
    ⟨ψ.symm τ, hσ⟩ ⟨ψ.symm τ', hσ'⟩ hconj
  have e1 : inertiaHom ψ ⟨ψ.symm τ, hσ⟩ = τ := Subtype.ext (ψ.apply_symm_apply _)
  have e2 : inertiaHom ψ ⟨ψ.symm τ', hσ'⟩ = τ' := Subtype.ext (ψ.apply_symm_apply _)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e1, e2, hq] at this
  exact this

theorem isFrobLift_map_iff (ψ : G ≃ₜ* G') {φ : G} : IsFrobLift G' (ψ φ) ↔ IsFrobLift G φ :=
  ⟨fun h => by simpa using h.map ψ.symm, fun h => h.map ψ⟩

/-- **The reconstructed Weil group**: generated by the lifts of the Frobenius and inertia. -/
def recWeil (G : Type*) [Group G] [TopologicalSpace G] : Subgroup G :=
  Subgroup.closure ({φ | IsFrobLift G φ} ∪ recInertia G)

/-- **The reconstructed Weil group is group-theoretic.** -/
theorem map_recWeil (ψ : G ≃ₜ* G') :
    (recWeil G).map ψ.toMulEquiv.toMonoidHom = recWeil G' := by
  rw [recWeil, recWeil, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_union, Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy | hy, rfl⟩
    · exact Or.inl (hy.map ψ)
    · exact Or.inr ((mem_recInertia_iff_map ψ).2 hy)
  · intro hx
    refine ⟨ψ.symm x, ?_, ψ.apply_symm_apply x⟩
    rcases hx with hx | hx
    · exact Or.inl (by rw [← isFrobLift_map_iff ψ, ψ.apply_symm_apply]; exact hx)
    · exact Or.inr (by rw [← mem_recInertia_iff_map ψ, ψ.apply_symm_apply]; exact hx)

end GroupTheoretic

section Galois

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

variable (p) in
/-- **[AbsAnab], Proposition 1.2.1 (iv)**: the group-theoretic Frobenius condition on
`Gal(Ω/K)` characterises the lifts of the arithmetic Frobenius. -/
theorem isFrobLift_gal_iff (σ : Ω ≃ₐ[K] Ω) :
    IsFrobLift (Ω ≃ₐ[K] Ω) σ ↔ QuotientGroup.mk σ = arithFrob p K Ω := by
  rw [← frobCond_iff, IsFrobLift, FrobCond, recInertia_gal p, recPrime_gal p, recQ_gal p]

variable (p) in
/-- The reconstructed Weil group of `Gal(Ω/K)`: the preimage of `Frob^ℤ ⊆ Gal(Ω/K)/I_K`. -/
theorem mem_recWeil_gal_iff (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ recWeil (Ω ≃ₐ[K] Ω) ↔
      ∃ k : ℤ, (QuotientGroup.mk σ : (Ω ≃ₐ[K] Ω) ⧸ absInertia p K Ω) = arithFrob p K Ω ^ k := by
  set W : Subgroup (Ω ≃ₐ[K] Ω) :=
    (Subgroup.zpowers (arithFrob p K Ω)).comap (QuotientGroup.mk' (absInertia p K Ω))
  have hW : ∀ x, x ∈ W ↔ ∃ k : ℤ,
      (QuotientGroup.mk x : (Ω ≃ₐ[K] Ω) ⧸ absInertia p K Ω) = arithFrob p K Ω ^ k := by
    intro x
    simp only [W, Subgroup.mem_comap, QuotientGroup.mk'_apply, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩
  rw [← hW]
  constructor
  · intro h
    refine (Subgroup.closure_le W).2 ?_ h
    rintro x (hx | hx)
    · exact (hW x).2 ⟨1, by rw [zpow_one]; exact (isFrobLift_gal_iff p x).1 hx⟩
    · refine (hW x).2 ⟨0, ?_⟩
      rw [zpow_zero, QuotientGroup.eq_one_iff, ← recInertia_gal p]
      exact hx
  · intro h
    obtain ⟨k, hk⟩ := (hW σ).1 h
    obtain ⟨φ, hφ⟩ := QuotientGroup.mk_surjective (arithFrob p K Ω)
    have hφW : φ ∈ recWeil (Ω ≃ₐ[K] Ω) :=
      Subgroup.subset_closure (Or.inl ((isFrobLift_gal_iff p φ).2 hφ))
    have hτ : (φ ^ k)⁻¹ * σ ∈ recWeil (Ω ≃ₐ[K] Ω) := by
      refine Subgroup.subset_closure (Or.inr ?_)
      change _ ∈ recInertia (Ω ≃ₐ[K] Ω)
      rw [recInertia_gal p, ← QuotientGroup.eq, QuotientGroup.mk_zpow, hφ, hk]
    have := mul_mem (zpow_mem hφW k) hτ
    rwa [mul_inv_cancel_left] at this

variable {p' : ℕ} [Fact p'.Prime]
variable {K' : Type*} [Field K'] [Algebra ℚ_[p'] K'] [FiniteDimensional ℚ_[p'] K']
variable {Ω' : Type*} [Field Ω'] [Algebra K' Ω'] [Algebra ℚ_[p'] Ω'] [IsScalarTower ℚ_[p'] K' Ω']
  [IsAlgClosed Ω'] [IsGalois K' Ω'] [Algebra.IsAlgebraic ℚ_[p'] Ω']

variable (p p') in
/-- **The Frobenius is group-theoretic** (invariance form): every isomorphism of topological
groups `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` maps lifts of the Frobenius of `K` to lifts of the Frobenius
of `K'`. -/
theorem galEquiv_arithFrob (φ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) (σ : Ω ≃ₐ[K] Ω) :
    (QuotientGroup.mk (φ σ) : (Ω' ≃ₐ[K'] Ω') ⧸ absInertia p' K' Ω') = arithFrob p' K' Ω' ↔
      (QuotientGroup.mk σ : (Ω ≃ₐ[K] Ω) ⧸ absInertia p K Ω) = arithFrob p K Ω := by
  rw [← isFrobLift_gal_iff p, ← isFrobLift_gal_iff p', isFrobLift_map_iff]

end Galois

end Iut.Reconstruction
