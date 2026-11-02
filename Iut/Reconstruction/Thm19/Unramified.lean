/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.CuspSync
import Iut.Reconstruction.Thm19.RecOrd
import Iut.Reconstruction.Thm19.NFColimit

/-!
# [AbsTopIII] Thm 1.9 (b): the extension of the field of constants is unramified everywhere

`Thm19/CuspSync.lean` compares the tame characters of a Galois model `D` and of its base change
`D_{k̄}` at inertia indices over `k`-rational points (curves-jacobian `ord_placeOf_ιF`). Here the
rational point is removed: the extension `F ⊆ F k̄` of the field of constants is unramified at
every place `W ⊇ k` of `Ω`, by the argument of curves-jacobian `ord_placeOf_ιF_of_ord_eq_one`
(a ramified uniformiser would have an `e`-th root moved by a root of unity under an inertia
element fixing `F k̄`, `exists_inertia_tameChar`, `eq_of_mem_inertia`).

* `placeBarOf`: the place `W ∩ F k̄` of `F k̄` below `W`, as soon as `W ∩ F ≠ F`;
* **`ord_placeBarOf_ιF`**, **`isUnif_baseChange`**: a uniformiser of `W ∩ F` stays a
  uniformiser of `W ∩ F k̄`;
* **`proj_tameChar_inertiaBar'`**: the tame characters of `D` and `D_{k̄}` agree on `I_W ∩ H` at
  every inertia index `p = (W, σ)` with `W ∩ F ≠ F` (no rational point needed);
* **`zHatRes_tameGen_eq`**: the tame generators of two Galois models at the same place and the
  same inertia element agree, as soon as the two uniformisers have the same value;
  `valuation_unif_eq_of_le`, `valuation_unif_eq_of_eq` provide that hypothesis;
* **`exists_inertiaH_ne_one`**: the inertia group `I_W ∩ H` is nontrivial when `W ∩ F ≠ F`.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer

universe u

namespace Iut.Reconstruction.Thm19

/-- An element of value `< 1` has no inverse in the valuation subring. -/
lemma inv_notMem_of_valuation_lt_one {K : Type*} [Field K] {W : ValuationSubring K} {x : K}
    (hx0 : x ≠ 0) (hx : W.valuation x < 1) : x⁻¹ ∉ W := fun h => by
  have h1 := (W.valuation_le_one_iff _).2 h
  rw [map_inv₀] at h1
  have h2 : W.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  exact absurd ((inv_le_one₀ (zero_lt_iff.2 h2)).1 h1) (not_le.2 hx)

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- The place `W ∩ F k̄` of `F k̄` below a place `W ⊇ k` of `Ω` with `W ∩ F ≠ F`. -/
noncomputable def placeBarOf {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    {π : F D} (hπ0 : π ≠ 0) (hπW : W.valuation ((π : F D) : Ω) < 1) :
    Place (kbar k Ω) (F (baseChange D)) :=
  ⟨W.comap (algebraMap (F (baseChange D)) Ω), fun htop => by
    have h : ((ιF D π)⁻¹ : F (baseChange D)) ∈ W.comap (algebraMap (F (baseChange D)) Ω) :=
      htop ▸ ValuationSubring.mem_top _
    change (((ιF D π)⁻¹ : F (baseChange D)) : Ω) ∈ W at h
    rw [IntermediateField.coe_inv, coe_ιF] at h
    exact inv_notMem_of_valuation_lt_one (fun h0 => hπ0 (Subtype.ext h0)) hπW h,
    kbar_mem W hkW⟩

/-- **A uniformiser of `W ∩ F` has order `1` at `W ∩ F k̄`** (the extension of the field of
constants is unramified at every place `W ⊇ k`). -/
theorem ord_placeBarOf_ιF {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    {π : F D} (hπ0 : π ≠ 0) (hπW : W.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω)) :
    (placeBarOf hkW hπ0 hπW).ord (ιF D π) = 1 := by
  set Q := placeBarOf hkW hπ0 hπW with hQdef
  have hQ : ∀ y : F (baseChange D), y ∈ Q.1 ↔ ((y : F (baseChange D)) : Ω) ∈ W :=
    fun _ => Iff.rfl
  have hπΩ0 : ((π : F D) : Ω) ≠ 0 := fun h ↦ hπ0 (Subtype.ext h)
  have hπWm : ((π : F D) : Ω) ∈ W := (W.valuation_le_one_iff _).1 hπW.le
  have hπWi : ((π : F D) : Ω)⁻¹ ∉ W := inv_notMem_of_valuation_lt_one hπΩ0 hπW
  have hιπ0 : ιF D π ≠ 0 := (map_ne_zero _).2 hπ0
  have hmem : ιF D π ∈ Q.1 := (hQ _).2 (by rw [coe_ιF]; exact hπWm)
  have hninv : (ιF D π)⁻¹ ∉ Q.1 := fun h => hπWi (by
    have := (hQ _).1 h
    rwa [IntermediateField.coe_inv, coe_ιF] at this)
  have hpos : 0 < Q.ord (ιF D π) := by
    have h0 := Q.ord_nonneg_of_mem hmem
    rcases h0.lt_or_eq with h | h
    · exact h
    · exact absurd ((Q.ord_eq_zero_iff hιπ0).1 h.symm).2 hninv
  by_contra hne
  set n : ℕ := (Q.ord (ιF D π)).toNat with hn
  have hnZ : (n : ℤ) = Q.ord (ιF D π) := Int.toNat_of_nonneg hpos.le
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨hn0.ne'⟩
  -- a uniformiser `ρ` of `Q` and the unit `w = π / ρⁿ`
  obtain ⟨ρ, hρ⟩ := Q.exists_ord_eq_one
  have hρ0 : ρ ≠ 0 := by rintro rfl; simp at hρ
  set w : F (baseChange D) := ιF D π / ρ ^ n with hw
  have hw0 : w ≠ 0 := div_ne_zero hιπ0 (pow_ne_zero _ hρ0)
  have hword : Q.ord w = 0 := by
    rw [hw, Q.ord_div hιπ0 (pow_ne_zero _ hρ0), Q.ord_pow, hρ, ← hnZ]
    ring
  obtain ⟨hw1, hw2⟩ := (Q.ord_eq_zero_iff hw0).1 hword
  have hwA : (w : Ω) ∈ W := (hQ _).1 hw1
  have hwA' : ((w : Ω))⁻¹ ∈ W := by
    have := (hQ _).1 hw2
    rwa [IntermediateField.coe_inv] at this
  have hwΩ : (w : Ω) = (π : Ω) / (ρ : Ω) ^ n := by
    rw [hw, IntermediateField.coe_div, IntermediateField.coe_pow, coe_ιF]
  -- an `n`-th root `α` of `π` and a primitive `n`-th root of unity `ζ`
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : NeZero (n : Ω) := NeZero.charZero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (π : Ω) hn0
  -- the tame character: `σ ∈ I_W ∩ H` with `σ α = ζ α`
  obtain ⟨σ, hσI, hσα⟩ := exists_inertia_tameChar (D := D) hkW π.2 hπΩ0 hπW hπ hn0 hα
    (hζ.pow_eq_one)
  have hσk : ∀ z ∈ kbar k Ω, (σ : Ω ≃ₐ[K₀ k t] Ω) z = z := fun z hz =>
    inertia_fix_algebraic hkW hσI (mem_algebraicClosure_iff.mp hz)
  have hσρ : (σ : Ω ≃ₐ[K₀ k t] Ω) ρ = ρ := fixes_F_baseChange D σ.2 hσk ρ.2
  -- `β = α / ρ` is a unit of `W` multiplied by `ζ` under `σ`
  have hρΩ0 : (ρ : Ω) ≠ 0 := fun h ↦ hρ0 (Subtype.ext h)
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0.ne'] at hα
    exact hπΩ0 hα.symm
  set β : Ω := α / ρ with hβ
  have hβ0 : β ≠ 0 := div_ne_zero hα0 hρΩ0
  have hβn : β ^ n = (w : Ω) := by rw [hβ, div_pow, hα, hwΩ]
  have hβA : β ∈ W := KummerTheory.Curve.mem_of_pow_mem hn0 (by rw [hβn]; exact hwA)
  have hβA' : β⁻¹ ∈ W :=
    KummerTheory.Curve.mem_of_pow_mem hn0 (by rw [inv_pow, hβn]; exact hwA')
  have hv := KummerTheory.Curve.valuation_eq_one_of_mem hβA hβA' hβ0
  have hσβ : (σ : Ω ≃ₐ[K₀ k t] Ω) β = ζ * β := by
    rw [hβ, map_div₀, hσα, hσρ, mul_div_assoc]
  have hfix := KummerTheory.Curve.eq_of_mem_inertia (k := k) hkW hσI hβA hv hn0
    hζ.pow_eq_one hσβ
  rw [hσβ] at hfix
  have hζ1 : ζ = 1 := mul_right_cancel₀ hβ0 (hfix.trans (one_mul β).symm)
  rw [hζ1, IsPrimitiveRoot.one_left_iff] at hζ
  omega

/-- **The extension `F ⊆ F k̄` of the field of constants is unramified at every place `W ⊇ k`**:
a uniformiser of `W ∩ F` (the largest value `< 1` on `F`) stays a uniformiser of `W ∩ F k̄`. -/
theorem isUnif_baseChange {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    {π : F D} (hπW : W.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω)) :
    ∀ f ∈ F (baseChange D), W.valuation f < 1 →
      W.valuation f ≤ W.valuation ((π : F D) : Ω) := by
  intro f hf hlt
  rcases eq_or_ne π 0 with rfl | hπ0
  · -- `π = 0`: then `F ⊆ W`, hence `W = Ω` (`Ω / F` is algebraic) and `f = 0`
    have hF : ∀ y : F D, ((y : F D) : Ω) ∈ W := fun y => by
      by_contra hy
      have hy0 : ((y : F D) : Ω) ≠ 0 := fun h => hy (h ▸ zero_mem W)
      have hyi : ((y : F D) : Ω)⁻¹ ∈ W := (W.mem_or_inv_mem _).resolve_left hy
      have hlt' : W.valuation ((y : F D) : Ω)⁻¹ < 1 := by
        rcases lt_or_eq_of_le ((W.valuation_le_one_iff _).2 hyi) with h | h
        · exact h
        · exfalso
          apply hy
          rw [map_inv₀, inv_eq_one] at h
          exact (W.valuation_le_one_iff _).1 h.le
      have := hπ _ (inv_mem y.2) hlt'
      simp [hy0] at this
    haveI : Algebra.IsAlgebraic (F D) Ω := Algebra.IsAlgebraic.tower_top (K := K₀ k t) (F D)
    have hall : ∀ z : Ω, z ∈ W := fun z ↦ by
      obtain ⟨p, hpm, hp⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := F D) z).isIntegral
      let φ : F D →+* W := (algebraMap (F D) Ω).codRestrict W.toSubring hF
      have hφ : (algebraMap W Ω).comp φ = algebraMap (F D) Ω := RingHom.ext fun _ ↦ rfl
      have hint : IsIntegral W z :=
        ⟨p.map φ, hpm.map φ, by rw [Polynomial.eval₂_map, hφ]; exact hp⟩
      obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
      rw [← hw]
      exact w.2
    rcases eq_or_ne f 0 with rfl | hf0
    · simp
    · exact absurd (hall f⁻¹) (inv_notMem_of_valuation_lt_one hf0 hlt)
  have h1 := ord_placeBarOf_ιF hkW hπ0 hπW hπ
  have h := valuation_le_of_ord_eq_one (placeBarOf hkW hπ0 hπW)
    (algebraMap (F (baseChange D)) Ω) rfl h1 ⟨f, hf⟩ hlt
  have e : algebraMap (F (baseChange D)) Ω (ιF D π) = ((π : F D) : Ω) := coe_ιF π
  exact h.trans_eq (congrArg W.valuation e)

set_option maxHeartbeats 1600000 in
-- `ContH1.evalTriv` terms unify slowly
/-- **The tame characters of `D` and of its base change `D_{k̄}` agree on `I_W ∩ H`** at every
inertia index `p = (W, σ)` with `W ∩ F ≠ F` (no rational point below `W` is needed): for any
uniformiser `π` of `W ∩ F k̄`, `θ_π(σ) = θ_p` at every level `n`. The extension of the field of
constants is unramified at `W` (`ord_placeBarOf_ιF`), so `unif p` and `π` differ by a unit,
whose `n`-th roots are fixed by inertia (`smul_eq_of_ord_eq_zero`). -/
theorem proj_tameChar_inertiaBar' (p : InertiaIndex D) (hne : idxVal p ≠ ⊤)
    {π : (F (baseChange D))ˣ}
    (hπW : p.1.1.valuation ((π : F (baseChange D)) : Ω) < 1)
    (hπ : ∀ f ∈ F (baseChange D), p.1.1.valuation f < 1 →
      p.1.1.valuation f ≤ p.1.1.valuation ((π : F (baseChange D)) : Ω))
    (n : ℕ) [NeZero n] :
    ZHatOne.proj (CurvesJacobian.ChernClass.kIdx (baseChange D) n)
        (tameChar (kbar_mem_idx p) π (inertiaBar p)) =
      ZHatOne.proj (CurvesJacobian.ChernClass.kIdx D n) (tameGen p) := by
  set Q := placeBarOf p.2.1 (unif p).ne_zero (unif_valuation_lt_one p hne)
  have hQ : ∀ y : F (baseChange D), ((y : F (baseChange D)) : Ω) ∈ p.1.1 ↔ y ∈ Q.1 :=
    fun _ => Iff.rfl
  have hπ1 : Q.ord (π : F (baseChange D)) = 1 :=
    CurvesJacobian.ChernClass.ord_eq_one_of_valuation hQ hπW hπ
  have hu1 : Q.ord (ιF D ((unif p : (F D)ˣ) : F D)) = 1 :=
    ord_placeBarOf_ιF p.2.1 (unif p).ne_zero (unif_valuation_lt_one p hne)
      (valuation_le_unif p hne)
  set u : F (baseChange D) := ιF D ((unif p : (F D)ˣ) : F D) / (π : F (baseChange D))
  have hι0 : ιF D ((unif p : (F D)ˣ) : F D) ≠ 0 := (map_ne_zero _).2 (unif p).ne_zero
  have hu0 : u ≠ 0 := div_ne_zero hι0 π.ne_zero
  have hu : Q.ord u = 0 := by
    rw [Q.ord_div hι0 π.ne_zero, hu1, hπ1, sub_self]
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq ((π : F (baseChange D)) : Ω)
    (Nat.pos_of_ne_zero (NeZero.ne n))
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq ((u : F (baseChange D)) : Ω)
    (Nat.pos_of_ne_zero (NeZero.ne n))
  have hπΩ : ((π : F (baseChange D)) : Ω) ≠ 0 := fun h => π.ne_zero (Subtype.ext h)
  have huΩ : ((u : F (baseChange D)) : Ω) ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hα0 : α ≠ 0 := fun h => hπΩ (by rw [← hα, h, zero_pow (NeZero.ne n)])
  have hγ0 : γ ≠ 0 := fun h => huΩ (by rw [← hγ, h, zero_pow (NeZero.ne n)])
  have hσγ : (inertiaBar p : (baseChange D).H) • γ = γ :=
    CurvesJacobian.ChernClass.smul_eq_of_ord_eq_zero hQ hu0 hu (inertiaBar p).2 hγ
  have hβ : (γ * α) ^ n = (((unif p : (F D)ˣ) : F D) : Ω) := by
    rw [mul_pow, hγ, hα]
    simp only [u, IntermediateField.coe_div, coe_ιF]
    field_simp
  have hL := val_proj_tameChar (kbar_mem_idx p) π (inertiaBar p)
    (CurvesJacobian.ChernClass.kIdx (baseChange D) n) (Units.mk0 α hα0)
    (Units.ext (by
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map, MonoidHom.coe_coe]
      exact hα))
  have hR := val_proj_tameChar p.2.1 (unif p) ⟨p.1.2, p.2.2⟩
    (CurvesJacobian.ChernClass.kIdx D n) (Units.mk0 (γ * α) (mul_ne_zero hγ0 hα0))
    (Units.ext (by
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map, MonoidHom.coe_coe]
      exact hβ))
  have hσγ' : ((p.1.2 : D.H) : Ω ≃ₐ[K₀ k t] Ω) γ = γ := by
    rw [← inertiaBar_apply]
    exact hσγ
  apply Mu.ext
  apply Units.ext
  refine hL.trans (Eq.trans ?_ hR.symm)
  simp only [Units.val_mk0]
  rw [map_mul, hσγ', inertiaBar_apply]
  field_simp

/-- **The inertia group `I_W ∩ H` is nontrivial** at every place `W ⊇ k` with `W ∩ F ≠ F`: the
tame character of a uniformiser of `W ∩ F` takes the value `-1` on `μ_2`
(`exists_inertia_tameChar`). -/
theorem exists_inertiaH_ne_one {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hW : ∃ f ∈ F D, f ≠ 0 ∧ W.valuation f < 1) : ∃ σ ∈ inertiaH D W, σ ≠ 1 := by
  obtain ⟨f, hf, hf0, hfW⟩ := hW
  let P : Place k (F D) := ⟨W.comap (algebraMap (F D) Ω), fun htop => by
      have h : (⟨f, hf⟩ : F D)⁻¹ ∈ W.comap (algebraMap (F D) Ω) :=
        htop ▸ ValuationSubring.mem_top _
      change (((⟨f, hf⟩ : F D)⁻¹ : F D) : Ω) ∈ W at h
      rw [IntermediateField.coe_inv] at h
      exact inv_notMem_of_valuation_lt_one hf0 hfW h, fun c => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact hkW c⟩
  obtain ⟨π, -, hπW, hπ⟩ :=
    CurvesJacobian.ChernClass.exists_uniformiser (P := P) (W := W) fun _ => Iff.rfl
  have hπ0 : ((π : F D) : Ω) ≠ 0 := fun h => π.ne_zero (Subtype.ext h)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq ((π : F D) : Ω) two_pos
  obtain ⟨σ, hσI, hσα⟩ := exists_inertia_tameChar (D := D) hkW (π : F D).2 hπ0 hπW hπ
    two_pos hα (ζ := -1) (by norm_num)
  refine ⟨σ, hσI, fun h1 => ?_⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have h2 : α = -1 * α := by
    rw [← hσα, h1]
    rfl
  have h3 : (2 : Ω) * α = 0 := by linear_combination h2
  have hα0 : α = 0 := (mul_eq_zero.1 h3).resolve_left two_ne_zero
  apply hπ0
  rw [← hα, hα0]
  norm_num

end Generic

/-! ### Tame generators of two Galois models at the same place -/

section Compare

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

set_option maxHeartbeats 1600000 in
-- `ContH1.evalTriv` terms unify slowly
/-- **The tame generators of two Galois models agree** at inertia indices `p₁ = (W₁, σ₁)`,
`p₂ = (W₂, σ₂)` with the same inertia element (`σ₁ = σ₂` on `Ω`) as soon as the two
uniformisers have the same value at `W₂` (`valuation_unif_eq_of_le`): `unif p₁ / unif p₂` is a
unit of `W₂` fixed by `σ₂`, whose `n`-th roots are fixed by inertia (`eq_of_mem_inertia`).
Applies to a Galois model and its extension of the field of constants (`constExt`), or to two
coordinates of the same curve. -/
theorem zHatRes_tameGen_eq {k₁ k₂ : Type u} [Field k₁] [Field k₂] [Algebra k₁ Ω] [Algebra k₂ Ω]
    [CharZero k₁] [CharZero k₂] {t₁ t₂ : Ω} [IsGalois (K₀ k₁ t₁) Ω] [IsGalois (K₀ k₂ t₂) Ω]
    {D₁ : Pi1.Orbifold.GaloisData k₁ t₁} {D₂ : Pi1.Orbifold.GaloisData k₂ t₂}
    (p₁ : InertiaIndex D₁) (p₂ : InertiaIndex D₂)
    (hσ : ∀ x : Ω, ((p₁.1.2 : D₁.H) : Ω ≃ₐ[K₀ k₁ t₁] Ω) x =
      ((p₂.1.2 : D₂.H) : Ω ≃ₐ[K₀ k₂ t₂] Ω) x)
    (hv : p₂.1.1.valuation (((unif p₁ : (F D₁)ˣ) : F D₁) : Ω) =
      p₂.1.1.valuation (((unif p₂ : (F D₂)ˣ) : F D₂) : Ω)) :
    zHatRes (F D₁) (F D₂) Ω Ω (tameGen p₁) = tameGen p₂ := by
  apply Subtype.ext
  funext i
  have hn : 0 < i.n := Nat.pos_of_ne_zero (NeZero.ne i.n)
  have h₁0 : (((unif p₁ : (F D₁)ˣ) : F D₁) : Ω) ≠ 0 := fun h =>
    (unif p₁).ne_zero (Subtype.ext h)
  have h₂0 : (((unif p₂ : (F D₂)ˣ) : F D₂) : Ω) ≠ 0 := fun h =>
    (unif p₂).ne_zero (Subtype.ext h)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (((unif p₂ : (F D₂)ˣ) : F D₂) : Ω) hn
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq
    ((((unif p₁ : (F D₁)ˣ) : F D₁) : Ω) / (((unif p₂ : (F D₂)ˣ) : F D₂) : Ω)) hn
  have hα0 : α ≠ 0 := fun h => h₂0 (by rw [← hα, h, zero_pow hn.ne'])
  have hγ0 : γ ≠ 0 := fun h => div_ne_zero h₁0 h₂0 (by rw [← hγ, h, zero_pow hn.ne'])
  have hσ₂ : ((p₂.1.2 : D₂.H) : Ω ≃ₐ[K₀ k₂ t₂] Ω) (((unif p₂ : (F D₂)ˣ) : F D₂) : Ω) =
      (((unif p₂ : (F D₂)ˣ) : F D₂) : Ω) :=
    (IntermediateField.mem_fixedField_iff _ _).1 ((unif p₂ : (F D₂)ˣ) : F D₂).2 _ p₂.1.2.2
  have hσ₁ : ((p₂.1.2 : D₂.H) : Ω ≃ₐ[K₀ k₂ t₂] Ω) (((unif p₁ : (F D₁)ˣ) : F D₁) : Ω) =
      (((unif p₁ : (F D₁)ˣ) : F D₁) : Ω) :=
    (hσ _).symm.trans
      ((IntermediateField.mem_fixedField_iff _ _).1 ((unif p₁ : (F D₁)ˣ) : F D₁).2 _ p₁.1.2.2)
  have hu : p₂.1.1.valuation
      ((((unif p₁ : (F D₁)ˣ) : F D₁) : Ω) / (((unif p₂ : (F D₂)ˣ) : F D₂) : Ω)) = 1 := by
    rw [map_div₀, hv, div_self ((Valuation.ne_zero_iff _).2 h₂0)]
  have hγW : γ ∈ p₂.1.1 := KummerTheory.Curve.mem_of_pow_mem hn (by
    rw [hγ]
    exact (p₂.1.1.valuation_le_one_iff _).1 hu.le)
  have hγW' : γ⁻¹ ∈ p₂.1.1 := KummerTheory.Curve.mem_of_pow_mem hn (by
    rw [inv_pow, hγ]
    exact (p₂.1.1.valuation_le_one_iff _).1 (by rw [map_inv₀, hu, inv_one]))
  have hvγ := KummerTheory.Curve.valuation_eq_one_of_mem hγW hγW' hγ0
  have hζ : (((p₂.1.2 : D₂.H) : Ω ≃ₐ[K₀ k₂ t₂] Ω) γ / γ) ^ i.n = 1 := by
    rw [div_pow, ← map_pow, hγ, map_div₀, hσ₁, hσ₂, div_self (div_ne_zero h₁0 h₂0)]
  have hσγ := KummerTheory.Curve.eq_of_mem_inertia (k := k₂) p₂.2.1 p₂.2.2 hγW hvγ hn hζ
    (div_mul_cancel₀ _ hγ0).symm
  have hβ : (γ * α) ^ i.n = (((unif p₁ : (F D₁)ˣ) : F D₁) : Ω) := by
    rw [mul_pow, hγ, hα, div_mul_cancel₀ _ h₂0]
  have hL := val_proj_tameChar p₁.2.1 (unif p₁) ⟨p₁.1.2, p₁.2.2⟩ (reindex (k := F D₁) i)
    (Units.mk0 (γ * α) (mul_ne_zero hγ0 hα0))
    (Units.ext (by
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map, MonoidHom.coe_coe]
      exact hβ))
  have hR := val_proj_tameChar p₂.2.1 (unif p₂) ⟨p₂.1.2, p₂.2.2⟩ i (Units.mk0 α hα0)
    (Units.ext (by
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map, MonoidHom.coe_coe]
      exact hα))
  apply Mu.ext
  apply Units.ext
  refine hL.trans (Eq.trans ?_ hR.symm)
  simp only [Units.val_mk0]
  rw [hσ, map_mul, hσγ]
  field_simp

/-- The uniformisers of two Galois models at the same place have the same value if
`F₁ ⊆ F₂` and the uniformiser of `F₁` stays a uniformiser of `F₂` (e.g. `isUnif_baseChange`). -/
lemma valuation_unif_eq_of_le {k₁ k₂ : Type u} [Field k₁] [Field k₂] [Algebra k₁ Ω]
    [Algebra k₂ Ω] [CharZero k₁] [CharZero k₂] {t₁ t₂ : Ω} [IsGalois (K₀ k₁ t₁) Ω]
    [IsGalois (K₀ k₂ t₂) Ω] {D₁ : Pi1.Orbifold.GaloisData k₁ t₁}
    {D₂ : Pi1.Orbifold.GaloisData k₂ t₂} (p₁ : InertiaIndex D₁) (p₂ : InertiaIndex D₂)
    (hF : ∀ x ∈ F D₁, x ∈ F D₂) (hW : p₁.1.1 = p₂.1.1) (hne₁ : idxVal p₁ ≠ ⊤)
    (hne₂ : idxVal p₂ ≠ ⊤)
    (hmax : ∀ f ∈ F D₂, p₂.1.1.valuation f < 1 →
      p₂.1.1.valuation f ≤ p₂.1.1.valuation (((unif p₁ : (F D₁)ˣ) : F D₁) : Ω)) :
    p₂.1.1.valuation (((unif p₁ : (F D₁)ˣ) : F D₁) : Ω) =
      p₂.1.1.valuation (((unif p₂ : (F D₂)ˣ) : F D₂) : Ω) := by
  have h1 := unif_valuation_lt_one p₁ hne₁
  rw [hW] at h1
  exact le_antisymm
    (valuation_le_unif p₂ hne₂ _ (hF _ ((unif p₁ : (F D₁)ˣ) : F D₁).2) h1)
    (hmax _ ((unif p₂ : (F D₂)ˣ) : F D₂).2 (unif_valuation_lt_one p₂ hne₂))

/-- **Same function field**: the uniformisers of two Galois models with `F₁ = F₂` at the same
place have the same value. -/
lemma valuation_unif_eq_of_eq {k₁ k₂ : Type u} [Field k₁] [Field k₂] [Algebra k₁ Ω]
    [Algebra k₂ Ω] [CharZero k₁] [CharZero k₂] {t₁ t₂ : Ω} [IsGalois (K₀ k₁ t₁) Ω]
    [IsGalois (K₀ k₂ t₂) Ω] {D₁ : Pi1.Orbifold.GaloisData k₁ t₁}
    {D₂ : Pi1.Orbifold.GaloisData k₂ t₂} (p₁ : InertiaIndex D₁) (p₂ : InertiaIndex D₂)
    (hF : ∀ x : Ω, x ∈ F D₁ ↔ x ∈ F D₂) (hW : p₁.1.1 = p₂.1.1) (hne₁ : idxVal p₁ ≠ ⊤)
    (hne₂ : idxVal p₂ ≠ ⊤) :
    p₂.1.1.valuation (((unif p₁ : (F D₁)ˣ) : F D₁) : Ω) =
      p₂.1.1.valuation (((unif p₂ : (F D₂)ˣ) : F D₂) : Ω) := by
  refine valuation_unif_eq_of_le p₁ p₂ (fun x hx => (hF x).1 hx) hW hne₁ hne₂
    fun f hf hlt => ?_
  have h := valuation_le_unif p₁ hne₁
  rw [hW] at h
  exact h f ((hF f).2 hf) hlt

end Compare

end Iut.Reconstruction.Thm19
