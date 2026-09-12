/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.TpdTorsionRep
import Iut.Tripod.InertiaUnipotent
import Iut.Tripod.WildRamIdx

/-!
# The ramification of `F_λ` over `ℚ(λ)` at the bad places away from `2·3·5`

For a point `λ` of the tripod and a place `w` of `F = F_λ` of residue characteristic
`p ∉ {2, 3, 5}` over a bad place `u` of `F_tpd = ℚ(λ)`, the inertia group `I ⊆ Gal(F/F_tpd)` at
`w` has order `≤ 30` (`Iut.Tripod.relRamIdx_tpd_le_thirty`):

* `I⁺ := {σ ∈ I | σ√λ = √λ, σ√(1 − λ) = √(1 − λ)}` has index `≤ 2` in `I`
  (`Iut.Tripod.card_inertia_le_two_mul`): `√−1` and one of `√λ`, `√(1 − λ)`, `√(1 − λ)/√λ` is a
  square root of a unit, hence fixed by `I` (`Iut.sqrt_fixed_of_valuation_sub_lt`), and the sign
  of `I` on the remaining root is a homomorphism `I →* ℤˣ` with kernel `I⁺`;
* `I⁺` acts unipotently on `E_λ(F)[3]` and `E_λ(F)[5]` (`Iut.iterate_map_eq_self_of_inertia`),
  so its images under the mod-`3` and mod-`5` representations are a `3`-subgroup of
  `GL₂(𝔽_3)` (order `48 = 3·16`) and a `5`-subgroup of `GL₂(𝔽_5)` (order `480 = 5·96`), of
  orders `≤ 3` and `≤ 5`; as `I⁺` acts faithfully on `E_λ(F)[3] × E_λ(F)[5]` (`F` is generated
  over `F_tpd` by the torsion coordinates and the square roots), `|I⁺| ≤ 15`
  (`Iut.Tripod.card_inertiaPlus_le`).
-/

namespace Iut

open NumberField WeierstrassCurve WeierstrassCurve.Affine

open scoped Classical

/-! ### The sign of an automorphism on a square root -/

section Sign

variable {k L : Type*} [Field k] [Field L] [CharZero L] [Algebra k L]

/-- The sign `±1` of `σ ∈ Aut(L/k)` on a square root `s` of an element of `k`. -/
noncomputable def signHom (s : L) (hs : ∃ a : k, s ^ 2 = algebraMap k L a) (hs0 : s ≠ 0) :
    (L ≃ₐ[k] L) →* ℤˣ where
  toFun σ := if σ s = s then 1 else -1
  map_one' := by simp
  map_mul' σ τ := by
    have key : ∀ ρ : L ≃ₐ[k] L, ρ s = s ∨ ρ s = -s := fun ρ => by
      obtain ⟨a, ha⟩ := hs
      have : (ρ s) ^ 2 = s ^ 2 := by rw [← map_pow, ha, ρ.commutes]
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
    have hne : -s ≠ s := fun h => hs0 (by
      have h2 : (2 : L) * s = 0 := by linear_combination -h
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero)
    simp only [AlgEquiv.mul_apply]
    rcases key τ with hτ | hτ
    · simp [hτ]
    · rcases key σ with hσ | hσ
      · simp [hτ, hσ, hne]
      · simp [hτ, hσ, hne]

lemma signHom_eq_one_iff {s : L} (hs : ∃ a : k, s ^ 2 = algebraMap k L a) (hs0 : s ≠ 0)
    (σ : L ≃ₐ[k] L) : signHom s hs hs0 σ = 1 ↔ σ s = s := by
  change (if σ s = s then (1 : ℤˣ) else -1) = 1 ↔ σ s = s
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h1 => absurd h1 (by decide), fun h1 => absurd h1 h⟩

end Sign

end Iut

namespace Iut.Tripod

open Iut Iut.EllipticCurveData NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  WeierstrassCurve WeierstrassCurve.Affine

open scoped Classical

variable (P : CurveProviders) (x : Pt)

set_option quotPrecheck false in
/-- The Legendre curve `E_λ` over `F = F_λ`. -/
local notation "EF" => Affine.baseChange (legendre (genT P x)) (P.curve x).F

/-- `√λ ∈ F`, as a square root of an element of `F_tpd`. -/
lemma sqrtLam'_sq_mem : ∃ a : tpd P x, (sqrtLam' x.1 : (P.curve x).F) ^ 2 =
    algebraMap (tpd P x) (P.curve x).F a :=
  ⟨genT P x, by rw [algebraMap_genT]; exact sqrtLam'_sq x.1⟩

/-- `√(1 − λ) ∈ F`, as a square root of an element of `F_tpd`. -/
lemma sqrtOneSubLam'_sq_mem : ∃ a : tpd P x, (sqrtOneSubLam' x.1 : (P.curve x).F) ^ 2 =
    algebraMap (tpd P x) (P.curve x).F a :=
  ⟨1 - genT P x, by rw [map_sub, map_one, algebraMap_genT]; exact sqrtOneSubLam'_sq x.1⟩

lemma sqrtLam'_ne_zero : sqrtLam' x.1 ≠ 0 := by
  intro h
  have hsq := sqrtLam'_sq x.1
  rw [h, zero_pow two_ne_zero] at hsq
  exact gen'_ne_zero x.2.1 hsq.symm

lemma sqrtOneSubLam'_ne_zero : sqrtOneSubLam' x.1 ≠ 0 := by
  intro h
  have hsq := sqrtOneSubLam'_sq x.1
  rw [h, zero_pow two_ne_zero, eq_comm, sub_eq_zero] at hsq
  exact gen'_ne_one x.2.2 hsq.symm

/-- **The subgroup `I⁺`** of the automorphisms of `F/F_tpd` in the inertia group of `w` fixing
`√λ` and `√(1 − λ)`. -/
noncomputable def inertiaPlus (w : FinitePlace (P.curve x).F) :
    Subgroup ((P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) :=
  w.maximalIdeal.asIdeal.inertia _ ⊓
    ((signHom _ (sqrtLam'_sq_mem P x) (sqrtLam'_ne_zero x)).ker ⊓
      (signHom _ (sqrtOneSubLam'_sq_mem P x) (sqrtOneSubLam'_ne_zero x)).ker)

lemma mem_inertiaPlus_iff (w : FinitePlace (P.curve x).F)
    (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) :
    σ ∈ inertiaPlus P x w ↔ σ ∈ w.maximalIdeal.asIdeal.inertia _ ∧
      σ (sqrtLam' x.1) = sqrtLam' x.1 ∧ σ (sqrtOneSubLam' x.1) = sqrtOneSubLam' x.1 := by
  simp only [inertiaPlus, Subgroup.mem_inf, MonoidHom.mem_ker, signHom_eq_one_iff]

/-! ### `[I : I⁺] ≤ 2` -/

/-- **The index of `I⁺` in `I` is at most `2`**: if `I` fixes an element `r` and fixing a
square root `f` of an element of `F_tpd` together with `r` forces fixing `√λ` and `√(1 − λ)`,
then the sign of `I` on `f` is a homomorphism `I →* ℤˣ` with kernel `I⁺`. -/
theorem card_inertia_le_two_mul (w : FinitePlace (P.curve x).F) (f : (P.curve x).F)
    (hf : ∃ a : tpd P x, f ^ 2 = algebraMap (tpd P x) (P.curve x).F a) (hf0 : f ≠ 0)
    (hplus : ∀ σ ∈ w.maximalIdeal.asIdeal.inertia ((P.curve x).F ≃ₐ[tpd P x] (P.curve x).F),
      σ f = f → σ (sqrtLam' x.1) = sqrtLam' x.1 ∧ σ (sqrtOneSubLam' x.1) = sqrtOneSubLam' x.1) :
    Nat.card (w.maximalIdeal.asIdeal.inertia ((P.curve x).F ≃ₐ[tpd P x] (P.curve x).F)) ≤
      2 * Nat.card (inertiaPlus P x w) := by
  haveI : IsGalois (tpd P x) (P.curve x).F := isGalois_tpd_curve' (P := P) (x := x)
  set I := w.maximalIdeal.asIdeal.inertia ((P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) with hI
  set ε := (signHom f hf hf0).restrict I with hε
  have h1 := Subgroup.card_mul_index ε.ker
  have hidx : ε.ker.index ≤ 2 := by
    rw [Subgroup.index_ker]
    calc Nat.card ε.range ≤ Nat.card ℤˣ := Subgroup.card_le_card_group _
      _ = 2 := by simp
  have hker : Nat.card ε.ker ≤ Nat.card (inertiaPlus P x w) := by
    refine Nat.card_le_card_of_injective (fun σ => ⟨σ.1.1, ?_⟩) ?_
    · rw [mem_inertiaPlus_iff]
      have hσf : σ.1.1 f = f :=
        (signHom_eq_one_iff hf hf0 σ.1.1).mp (MonoidHom.mem_ker.mp σ.2)
      exact ⟨σ.1.2, hplus σ.1.1 σ.1.2 hσf⟩
    · intro σ τ h
      have h' := congrArg Subtype.val h
      simp only at h'
      exact Subtype.ext (Subtype.ext h')
  calc Nat.card I = Nat.card ε.ker * ε.ker.index := h1.symm
    _ ≤ Nat.card (inertiaPlus P x w) * 2 := Nat.mul_le_mul hker hidx
    _ = 2 * Nat.card (inertiaPlus P x w) := mul_comm _ _

/-! ### `I⁺` acts unipotently on the `3`- and `5`-torsion -/

/-- **`I⁺` acts unipotently on `E_λ(F)[n]` at a bad place** (`n` odd, `w(n) = 1`, `w(2) = 1`):
`σ^n` fixes the `n`-torsion pointwise for `σ ∈ I⁺`. -/
theorem galF_pow_eq_self_of_mem_inertiaPlus (w : FinitePlace (P.curve x).F)
    (h2 : residueChar w ≠ 2) {n : ℕ} (hodd : Odd n)
    (hn : w.maximalIdeal.valuation _ (n : (P.curve x).F) = 1)
    (hbad : w.maximalIdeal.valuation _ (genC' P x) ≠ 1 ∨
      w.maximalIdeal.valuation _ (genC' P x - 1) ≠ 1)
    (σ : (P.curve x).F ≃ₐ[tpd P x] (P.curve x).F) (hσ : σ ∈ inertiaPlus P x w)
    (Q : (EF).Point) (hQ : n • Q = 0) : galF P x (σ ^ n) Q = Q := by
  rw [mem_inertiaPlus_iff] at hσ
  obtain ⟨hσI, hσa, hσb⟩ := hσ
  have h2' := valuation_two_eq_one w h2
  -- `√−1` is fixed by the inertia group
  have hi : (sqrtNegOne' x.1 : (P.curve x).F) ^ 2 = -1 := sqrtNegOne'_sq x.1
  have hσi : σ (sqrtNegOne' x.1) = sqrtNegOne' x.1 := by
    have ha : w.maximalIdeal.valuation _ (algebraMap (tpd P x) (P.curve x).F (-1)) = 1 := by
      rw [map_neg, map_one, Valuation.map_neg, map_one]
    have hsq : (sqrtNegOne' x.1 : (P.curve x).F) ^ 2 =
        algebraMap (tpd P x) (P.curve x).F (-1) := by
      rw [map_neg, map_one]; exact hi
    exact sqrt_fixed_of_valuation_sub_lt _ (σ : (P.curve x).F →+* (P.curve x).F) hsq
      (σ.commutes _) ha h2' (valuation_sub_lt_one_of_mem_inertia hσI
        (valuation_eq_one_of_sq _ ((congrArg _ hsq).trans ha)).le)
  have hu : (sqrtLam' x.1 : (P.curve x).F) ^ 2 = algebraMap (tpd P x) (P.curve x).F (genT P x) := by
    rw [algebraMap_genT]; exact sqrtLam'_sq x.1
  have hbad' : w.maximalIdeal.valuation _ (algebraMap (tpd P x) (P.curve x).F (genT P x)) ≠ 1 ∨
      w.maximalIdeal.valuation _ (algebraMap (tpd P x) (P.curve x).F (genT P x) - 1) ≠ 1 := by
    rw [algebraMap_genT]; exact hbad
  have := iterate_map_eq_self_of_inertia (genT P x) w h2 hodd hn hbad' σ hσI hi hu hσi hσa Q hQ
  unfold galF
  rw [Affine.Point.map_pow]
  exact this

/-! ### `|I⁺| ≤ 15` -/

/-- **`|I⁺| ≤ 15`** at a bad place of residue characteristic `∉ {2, 3, 5}`. -/
theorem card_inertiaPlus_le (w : FinitePlace (P.curve x).F) (h2 : residueChar w ≠ 2)
    (h3 : residueChar w ≠ 3) (h5 : residueChar w ≠ 5)
    (hbad : w.maximalIdeal.valuation _ (genC' P x) ≠ 1 ∨
      w.maximalIdeal.valuation _ (genC' P x - 1) ≠ 1) :
    Nat.card (inertiaPlus P x w) ≤ 15 := by
  haveI : IsGalois (tpd P x) (P.curve x).F := isGalois_tpd_curve' (P := P) (x := x)
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsub3 := torsionCoords_three_subset_fieldOf' x.1
  have hsub5 := torsionCoords_five_subset_fieldOf' x.1
  set ρ₃ := (repF P x 3 hsub3).restrict (inertiaPlus P x w) with hρ₃
  set ρ₅ := (repF P x 5 hsub5).restrict (inertiaPlus P x w) with hρ₅
  have hn3 : w.maximalIdeal.valuation _ ((3 : ℕ) : (P.curve x).F) = 1 :=
    (valuation_natCast_eq_one_iff w Nat.prime_three).2 h3
  have hn5 : w.maximalIdeal.valuation _ ((5 : ℕ) : (P.curve x).F) = 1 :=
    (valuation_natCast_eq_one_iff w Nat.prime_five).2 h5
  -- unipotence: `ρₙ(σ)^n = 1`
  have hpow3 : ∀ σ : inertiaPlus P x w, ρ₃ σ ^ 3 = 1 := fun σ => by
    rw [hρ₃, MonoidHom.restrict_apply, ← map_pow, ← MonoidHom.mem_ker, mem_repF_ker_iff]
    exact galF_pow_eq_self_of_mem_inertiaPlus P x w h2 (by decide) hn3 hbad σ.1 σ.2
  have hpow5 : ∀ σ : inertiaPlus P x w, ρ₅ σ ^ 5 = 1 := fun σ => by
    rw [hρ₅, MonoidHom.restrict_apply, ← map_pow, ← MonoidHom.mem_ker, mem_repF_ker_iff]
    exact galF_pow_eq_self_of_mem_inertiaPlus P x w h2 (by decide) hn5 hbad σ.1 σ.2
  -- faithfulness: `ρ₃ σ = 1`, `ρ₅ σ = 1` force `σ = 1`
  have hinj : ∀ σ : inertiaPlus P x w, ρ₃ σ = 1 → ρ₅ σ = 1 → σ = 1 := by
    intro σ h3' h5'
    rw [hρ₃, MonoidHom.restrict_apply, ← MonoidHom.mem_ker, mem_repF_ker_iff] at h3'
    rw [hρ₅, MonoidHom.restrict_apply, ← MonoidHom.mem_ker, mem_repF_ker_iff] at h5'
    obtain ⟨hσI, hσa, hσb⟩ := (mem_inertiaPlus_iff P x w σ.1).mp σ.2
    have h2' := valuation_two_eq_one w h2
    have hσi : σ.1 (sqrtNegOne' x.1) = sqrtNegOne' x.1 := by
      have ha : w.maximalIdeal.valuation _ (algebraMap (tpd P x) (P.curve x).F (-1)) = 1 := by
        rw [map_neg, map_one, Valuation.map_neg, map_one]
      have hsq : (sqrtNegOne' x.1 : (P.curve x).F) ^ 2 =
          algebraMap (tpd P x) (P.curve x).F (-1) := by
        rw [map_neg, map_one]; exact sqrtNegOne'_sq x.1
      exact sqrt_fixed_of_valuation_sub_lt _ (σ.1 : (P.curve x).F →+* (P.curve x).F) hsq
        (σ.1.commutes _) ha h2' (valuation_sub_lt_one_of_mem_inertia hσI
          (valuation_eq_one_of_sq _ ((congrArg _ hsq).trans ha)).le)
    apply Subtype.ext
    refine algEquiv_eq_one_of_fixed (adjoin_tpdGens P x) σ.1 fun s hs => ?_
    rcases hs with (hs | hs) | hs
    · rcases hs with rfl | rfl | rfl
      · exact hσi
      · exact hσa
      · exact hσb
    · exact torsionCoord_fixed_of_galF P x 3 hsub3 σ.1 h3' hs s.2
    · exact torsionCoord_fixed_of_galF P x 5 hsub5 σ.1 h5' hs s.2
  -- counting
  have hGL3 : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) ∣ 3 * 16 := by
    rw [card_GL_two 3]; norm_num
  have hGL5 : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) ∣ 5 * 96 := by
    rw [card_GL_two 5]; norm_num
  have hrange3 : Nat.card ρ₃.range ≤ 3 :=
    card_le_of_forall_pow_eq_one ρ₃.range 3 16 hGL3 (by norm_num) fun τ hτ => by
      obtain ⟨σ, rfl⟩ := hτ
      exact hpow3 σ
  set ρ₅' := ρ₅.restrict ρ₃.ker with hρ₅'
  have hinj' : Function.Injective ρ₅' := by
    intro σ τ h
    have h' : ρ₅ σ.1 = ρ₅ τ.1 := h
    have hστ : ρ₅ (σ.1 * τ.1⁻¹) = 1 := by rw [map_mul, map_inv, h', mul_inv_cancel]
    have h3' : ρ₃ (σ.1 * τ.1⁻¹) = 1 := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp σ.2, MonoidHom.mem_ker.mp τ.2, one_mul, inv_one]
    have := hinj _ h3' hστ
    exact Subtype.ext (mul_inv_eq_one.mp this)
  have hker3 : Nat.card ρ₃.ker ≤ 5 := by
    calc Nat.card ρ₃.ker ≤ Nat.card ρ₅'.range :=
          Nat.card_le_card_of_injective ρ₅'.rangeRestrict
            (MonoidHom.rangeRestrict_injective_iff.mpr hinj')
      _ ≤ 5 := card_le_of_forall_pow_eq_one ρ₅'.range 5 96 hGL5 (by norm_num) fun τ hτ => by
          obtain ⟨σ, rfl⟩ := hτ
          rw [hρ₅', MonoidHom.restrict_apply]
          exact hpow5 σ.1
  calc Nat.card (inertiaPlus P x w) = Nat.card ρ₃.ker * ρ₃.ker.index :=
        (Subgroup.card_mul_index ρ₃.ker).symm
    _ = Nat.card ρ₃.ker * Nat.card ρ₃.range := by rw [Subgroup.index_ker]
    _ ≤ 5 * 3 := Nat.mul_le_mul hker3 hrange3
    _ = 15 := by norm_num

/-! ### `e(w/u) ≤ 30` -/

/-- **`F_λ/ℚ(λ)` has ramification index `≤ 30` at the bad places of residue characteristic
`∉ {2, 3, 5}`.** -/
theorem relRamIdx_tpd_le_thirty {w : FinitePlace (P.curve x).F} {𝔭 : FinitePlace (tpd P x)}
    (hw𝔭 : FinitePlace.LiesOver w 𝔭) (h2 : residueChar w ≠ 2) (h3 : residueChar w ≠ 3)
    (h5 : residueChar w ≠ 5) (h𝔭 : 𝔭 ∈ badT P x) : relRamIdx w 𝔭 ≤ 30 := by
  haveI : IsGalois (tpd P x) (P.curve x).F := isGalois_tpd_curve' (P := P) (x := x)
  set v := w.maximalIdeal.valuation (P.curve x).F with hv
  have h2' : v 2 = 1 := valuation_two_eq_one w h2
  have hbad : v (genC' P x) ≠ 1 ∨ v (genC' P x - 1) ≠ 1 := by
    rw [mem_badT] at h𝔭
    rcases h𝔭 with h | h
    · exact Or.inl fun h' => h ((FinitePlace.apply_eq_one_iff _ _).mpr
        ((valuation_genC_eq_one_iff P x hw𝔭).mp h'))
    · exact Or.inr fun h' => h ((FinitePlace.apply_eq_one_iff _ _).mpr
        ((valuation_genC_sub_one_eq_one_iff P x hw𝔭).mp h'))
  rw [relRamIdx_eq_card_inertia hw𝔭]
  refine le_trans ?_ (Nat.mul_le_mul_left 2 (card_inertiaPlus_le P x w h2 h3 h5 hbad))
  -- the inertia condition and the rigidity of square roots of units
  have hrigid : ∀ (s : (P.curve x).F) (a : tpd P x), s ^ 2 = algebraMap (tpd P x) (P.curve x).F a →
      v (algebraMap (tpd P x) (P.curve x).F a) = 1 →
      ∀ σ ∈ w.maximalIdeal.asIdeal.inertia ((P.curve x).F ≃ₐ[tpd P x] (P.curve x).F),
        σ s = s := fun s a hs ha σ hσ =>
    sqrt_fixed_of_valuation_sub_lt _ (σ : (P.curve x).F →+* (P.curve x).F) hs (σ.commutes _) ha
      h2' (valuation_sub_lt_one_of_mem_inertia hσ
        (valuation_eq_one_of_sq _ ((congrArg _ hs).trans ha)).le)
  have hu : (sqrtLam' x.1 : (P.curve x).F) ^ 2 = algebraMap (tpd P x) (P.curve x).F (genT P x) := by
    rw [algebraMap_genT]; exact sqrtLam'_sq x.1
  have hb : (sqrtOneSubLam' x.1 : (P.curve x).F) ^ 2 =
      algebraMap (tpd P x) (P.curve x).F (1 - genT P x) := by
    rw [map_sub, map_one, algebraMap_genT]; exact sqrtOneSubLam'_sq x.1
  rcases lt_trichotomy (v (genC' P x)) 1 with hl | hl | hl
  · -- `v(λ) < 1`: `√(1 − λ)` is fixed by `I`; the sign on `√λ` cuts out `I⁺`
    have hunit : v (algebraMap (tpd P x) (P.curve x).F (1 - genT P x)) = 1 := by
      rw [map_sub, map_one, algebraMap_genT, Valuation.map_sub_eq_of_lt_left _ (by
        rw [map_one]; exact hl), map_one]
    exact card_inertia_le_two_mul P x w _ (sqrtLam'_sq_mem P x) (sqrtLam'_ne_zero x)
      fun σ hσ hf => ⟨hf, hrigid _ _ hb hunit σ hσ⟩
  · -- `v(λ) = 1`, so `v(λ − 1) < 1`: `√λ` is fixed by `I`; the sign on `√(1 − λ)` cuts out `I⁺`
    have hunit : v (algebraMap (tpd P x) (P.curve x).F (genT P x)) = 1 := by
      rw [algebraMap_genT]; exact hl
    exact card_inertia_le_two_mul P x w _ (sqrtOneSubLam'_sq_mem P x) (sqrtOneSubLam'_ne_zero x)
      fun σ hσ hf => ⟨hrigid _ _ hu hunit σ hσ, hf⟩
  · -- `v(λ) > 1`: `√(1 − λ)/√λ` is fixed by `I`; the sign on `√λ` cuts out `I⁺`
    have hl0 : genC' P x ≠ 0 := gen'_ne_zero x.2.1
    set a : (P.curve x).F := sqrtLam' x.1 with ha
    set b : (P.curve x).F := sqrtOneSubLam' x.1 with hb'
    have ha0 : a ≠ 0 := sqrtLam'_ne_zero x
    have hr : (b / a) ^ 2 = algebraMap (tpd P x) (P.curve x).F ((1 - genT P x) / genT P x) := by
      rw [map_div₀, div_pow]
      exact congrArg₂ (· / ·) hb hu
    have hunit : v (algebraMap (tpd P x) (P.curve x).F ((1 - genT P x) / genT P x)) = 1 := by
      rw [map_div₀, map_sub, map_one, algebraMap_genT, map_div₀, Valuation.map_sub_swap,
        Valuation.map_sub_eq_of_lt_left _ (by rw [map_one]; exact hl),
        div_self ((Valuation.ne_zero_iff _).mpr hl0)]
    refine card_inertia_le_two_mul P x w a (sqrtLam'_sq_mem P x) ha0 fun σ hσ hf => ⟨hf, ?_⟩
    have hσr : σ (b / a) = b / a := hrigid _ _ hr hunit σ hσ
    have h1 : σ b / σ a = b / a := (map_div₀ σ b a).symm.trans hσr
    have h2 : σ b / a = b / a :=
      (congrArg (fun t : (P.curve x).F => σ b / t) hf).symm.trans h1
    exact (div_left_inj' ha0).mp h2

end Iut.Tripod
