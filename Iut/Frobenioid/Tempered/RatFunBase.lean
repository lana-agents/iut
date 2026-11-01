/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.RatFunMero
import Iut.Frobenioid.Tempered.RatFunConst
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Field of definition and Galois action: `E(L) ⊆ E(Ω)` (MR18 T8, route B-an)

In [EtTh] §3 the stable curve `Z` and its universal combinatorial covering `Z_∞` are defined over
a finite extension `L` of `ℚ_p`, and the meromorphic functions are those defined over `L`; the
divisors (zeros and poles at points) only become visible over an algebraically closed complete
extension `Ω` of `L` (e.g. `ℂ_p`, Mathlib's `ℂ_[p]`). This file transports entire Laurent series
and meromorphic functions along an **isometric field homomorphism** `φ : L → Ω`, which covers both

* the **base change** `E(L) → E(Ω)` along `algebraMap L Ω` for a normed algebra `Ω/L`, and
* the **Galois action** of an isometric automorphism `σ` of `Ω` on coefficients
  (`Entire.gal`), which fixes the image of `E(L)` when `σ` fixes `L`.

The transport preserves Gauss norms and orders at points (`Entire.gn_map`, `Entire.ord_map`), so
the divisor of a function over `L` is that of its image over `Ω`, Galois-equivariantly.
Elements of the kernel descend to `L` by comparing one nonzero coefficient
(`Mero.exists_eq_ofE_mono_of_map_eq`), with no Ax–Sen–Tate argument.

## Main results

* `Entire.map φ hφ : E(L) →+* E(Ω)`, `coeff_map`, `map_apply`, `map_injective`, `gn_map`,
  `ord_map`, `map_map`; `Entire.gal`, `gal_map_of_fix`; `Mero.map`, `Mero.ord_map`, `Mero.gn_map`.
* `Mero.ker_iff_of_map`: **[EtTh] Proposition 3.4(ii) over `L`**: `x ∈ Frac E(L)` has trivial
  divisor over `Ω` iff `x ∈ O_L^×`; `Mero.eff_iff_of_map`: effective iff `x ∈ O_L ∖ {0}`.
* `Mero.eq_one_of_forall_pow`: **[EtTh] Proposition 3.2(iii) for meromorphic functions**: over a
  locally compact `L`, a nonzero meromorphic function with an `N`-th root for every `N ≥ 1` is `1`.
* `properSpace_of_isNonarchimedeanLocalField`: a nonarchimedean local field in the sense of
  Mathlib's `IsNonarchimedeanLocalField` is a proper space (the hypothesis of `RatFunConst.lean`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open Polynomial TateCurvesTheta Filter Topology

/-- A nonarchimedean local field (Mathlib's `IsNonarchimedeanLocalField`, with the norm topology)
is proper, hence satisfies the hypothesis `ProperSpace L` of `RatFunConst.lean`. -/
theorem properSpace_of_isNonarchimedeanLocalField (L : Type*) [NontriviallyNormedField L]
    [ValuativeRel L] [IsNonarchimedeanLocalField L] : ProperSpace L :=
  ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace L

variable {L Ω : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  [NontriviallyNormedField Ω] [CompleteSpace Ω] [IsUltrametricDist Ω]

/-! ### Transport of coefficient families -/

section Coeff

variable (φ : L →+* Ω) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
include hφ

lemma tnorm_comp (c : ℤ → L) (r : ℝ) : tnorm (fun n => φ (c n)) r = tnorm c r := by
  funext n; simp [tnorm, hφ]

lemma gnorm_comp (c : ℤ → L) (r : ℝ) : gnorm (fun n => φ (c n)) r = gnorm c r := by
  simp only [gnorm, tnorm_comp φ hφ]

lemma lo_comp (c : ℤ → L) (r : ℝ) : lo (fun n => φ (c n)) r = lo c r := by
  simp only [lo, domSet, tnorm_comp φ hφ, gnorm_comp φ hφ]

lemma hi_comp (c : ℤ → L) (r : ℝ) : hi (fun n => φ (c n)) r = hi c r := by
  simp only [hi, domSet, tnorm_comp φ hφ, gnorm_comp φ hφ]

lemma continuous_of_isometric : Continuous φ :=
  AddMonoidHomClass.continuous_of_bound φ 1 fun x => by rw [hφ, one_mul]

lemma isEntire_comp {c : ℤ → L} (hc : IsEntire c) : IsEntire fun n => φ (c n) :=
  isEntire_of_convAt fun r hr => by
    change Tendsto _ _ _
    rw [tnorm_comp φ hφ]; exact hc.convAt hr

lemma conv_comp {c d : ℤ → L} (hc : IsEntire c) (hd : IsEntire d) :
    conv (fun n => φ (c n)) (fun n => φ (d n)) = fun n => φ (conv c d n) := by
  funext l
  have h := ((summable_conv_family hc hd l).hasSum.map φ (continuous_of_isometric φ hφ)).tsum_eq
  rw [conv, conv, ← h]
  congr 1; funext m; simp

end Coeff

/-! ### Transport of entire series -/

namespace Entire

variable (φ : L →+* Ω) (hφ : ∀ x, ‖φ x‖ = ‖x‖)

/-- **Transport of an entire series along an isometric field homomorphism** (coefficientwise). -/
def map : Entire L →+* Entire Ω where
  toFun f := ofCoeff (fun n => φ (coeff f n)) (isEntire_comp φ hφ (isEntire_coeff f))
  map_one' := ext_coeff (by
    rw [coeff_ofCoeff, coeff_one, coeff_one]; funext n
    by_cases hn : n = 0 <;> simp [hn])
  map_mul' f g := ext_coeff (by
    rw [coeff_ofCoeff, coeff_mul, coeff_mul, coeff_ofCoeff, coeff_ofCoeff,
      conv_comp φ hφ (isEntire_coeff f) (isEntire_coeff g)])
  map_zero' := ext_coeff (by rw [coeff_ofCoeff, coeff_zero, coeff_zero]; funext n; simp)
  map_add' f g := ext_coeff (by
    rw [coeff_ofCoeff, coeff_add, coeff_add, coeff_ofCoeff, coeff_ofCoeff]; funext n; simp)

lemma coeff_map (f : Entire L) : coeff (map φ hφ f) = fun n => φ (coeff f n) :=
  coeff_ofCoeff _ (isEntire_comp φ hφ (isEntire_coeff f))

lemma map_injective : Function.Injective (map φ hφ) := fun f g h => by
  refine ext_coeff (funext fun n => φ.injective ?_)
  have := congrFun (congrArg coeff h) n
  rwa [coeff_map, coeff_map] at this

/-- Values at points of `L`: `(φ f)(φ u) = φ (f u)`. -/
lemma map_apply (f : Entire L) (u : Lˣ) :
    ((map φ hφ f : Entire Ω) : Ωˣ → Ω) (Units.map φ.toMonoidHom u) = φ ((f : Lˣ → L) u) := by
  have h := ((coeff_spec f u).map φ (continuous_of_isometric φ hφ)).tsum_eq
  rw [← h, coe_eq_lsum, coeff_map, lsum]
  congr 1; funext n
  simp [map_zpow₀]

lemma gn_map (f : Entire L) (r : ℝ) : gn (map φ hφ f) r = gn f r := by
  rw [gn, coeff_map, gnorm_comp φ hφ]

lemma lo_map (f : Entire L) (r : ℝ) : lo (coeff (map φ hφ f)) r = lo (coeff f) r := by
  rw [coeff_map, lo_comp φ hφ]

lemma hi_map (f : Entire L) (r : ℝ) : hi (coeff (map φ hφ f)) r = hi (coeff f) r := by
  rw [coeff_map, hi_comp φ hφ]

lemma map_algebraMap (a : L) : map φ hφ (algebraMap L (Entire L) a) = algebraMap Ω _ (φ a) :=
  ext_coeff (by
    rw [coeff_map, coeff_algebraMap, coeff_algebraMap]; funext n
    by_cases hn : n = 0 <;> simp [hn])

lemma map_mono (k : ℤ) : map φ hφ (mono k) = mono k :=
  ext_coeff (by
    rw [coeff_map, coeff_mono, coeff_mono]; funext n
    by_cases hn : n = k <;> simp [hn])

lemma map_polyE_lin (a : L) : map φ hφ (polyE (lin a)) = polyE (lin (φ a)) :=
  ext_coeff (by
    rw [coeff_map, coeff_polyE, coeff_polyE]; funext n
    rw [polyCoeff_lin, polyCoeff_lin]
    split_ifs <;> simp)

/-- **Orders at points are preserved**: `ord_{φ α} (φ f) = ord_α f`. -/
theorem ord_map (f : Entire L) (α : Lˣ) :
    ord (map φ hφ f) (Units.map φ.toMonoidHom α) = ord f α := by
  by_cases hf : f = 0
  · subst hf
    rw [map_zero]
    simp [ord]
  obtain ⟨g, hg, hgα⟩ := hasOrderAt_ord hf α
  refine ord_eq_of_hasOrderAt ⟨map φ hφ g, ?_, ?_⟩
  · conv_lhs => rw [hg]
    rw [map_mul, map_pow, map_polyE_lin]
    rfl
  · rw [map_apply]
    exact fun h => hgα (φ.injective (h.trans (map_zero φ).symm))

lemma map_map {Ω' : Type*} [NontriviallyNormedField Ω'] [CompleteSpace Ω'] [IsUltrametricDist Ω']
    (ψ : Ω →+* Ω') (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (f : Entire L) :
    map ψ hψ (map φ hφ f) = map (ψ.comp φ) (fun x => by simp [hψ, hφ]) f :=
  ext_coeff (by rw [coeff_map, coeff_map, coeff_map]; rfl)

/-- **The Galois action** of an isometric automorphism `σ` of `Ω` on `E(Ω)` (on coefficients). -/
abbrev gal (σ : Ω ≃+* Ω) (hσ : ∀ x, ‖σ x‖ = ‖x‖) : Entire Ω →+* Entire Ω :=
  map (σ : Ω →+* Ω) hσ

lemma gal_mul_gal (σ τ : Ω ≃+* Ω) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (hτ : ∀ x, ‖τ x‖ = ‖x‖)
    (f : Entire Ω) : gal σ hσ (gal τ hτ f) = gal (τ.trans σ) (fun x => by simp [hσ, hτ]) f :=
  ext_coeff (by simp only [coeff_map]; rfl)

lemma gal_refl (f : Entire Ω) : gal (RingEquiv.refl Ω) (fun _ => rfl) f = f :=
  ext_coeff (by rw [coeff_map]; rfl)

/-- Series defined over `L` are fixed by the automorphisms of `Ω` fixing `L`. -/
lemma gal_map_of_fix (σ : Ω ≃+* Ω) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (hfix : ∀ a, σ (φ a) = φ a)
    (f : Entire L) : gal σ hσ (map φ hφ f) = map φ hφ f :=
  ext_coeff (funext fun n => by rw [coeff_map, coeff_map]; exact hfix _)

end Entire

/-! ### Meromorphic functions -/

namespace Mero

variable (φ : L →+* Ω) (hφ : ∀ x, ‖φ x‖ = ‖x‖)

/-- **Transport of meromorphic functions** `Frac E(L) → Frac E(Ω)`. -/
def map : Mero L →+* Mero Ω :=
  IsFractionRing.lift (K := Mero L) (g := (algebraMap (Entire Ω) (Mero Ω)).comp (Entire.map φ hφ))
    (ofE_injective.comp (Entire.map_injective φ hφ))

lemma map_ofE (f : Entire L) : map φ hφ (ofE f) = ofE (Entire.map φ hφ f) :=
  IsFractionRing.lift_algebraMap _ _

lemma map_div (g h : Entire L) :
    map φ hφ (ofE g / ofE h) = ofE (Entire.map φ hφ g) / ofE (Entire.map φ hφ h) := by
  rw [map_div₀, map_ofE, map_ofE]

lemma map_injective : Function.Injective (map φ hφ) := (map φ hφ).injective

lemma map_const (c : L) : map φ hφ (const c) = const (φ c) := by
  rw [map_ofE, Entire.map_algebraMap]

lemma ord_map {x : Mero L} (hx : x ≠ 0) (α : Lˣ) :
    ord (map φ hφ x) (Units.map φ.toMonoidHom α) = ord x α := by
  have hn := num_ne_zero hx
  have hd := den_ne_zero x
  conv_lhs => rw [eq_num_div_den x]
  rw [map_div, ord_div ((map_ne_zero_iff _ (Entire.map_injective φ hφ)).mpr hn)
    ((map_ne_zero_iff _ (Entire.map_injective φ hφ)).mpr hd), Entire.ord_map, Entire.ord_map, ord]

lemma gn_map (x : Mero L) {r : ℝ} (hr : 0 < r) : gn (map φ hφ x) r = gn x r := by
  have hd := den_ne_zero x
  conv_lhs => rw [eq_num_div_den x]
  rw [map_div, gn_div ((map_ne_zero_iff _ (Entire.map_injective φ hφ)).mpr hd) hr,
    Entire.gn_map, Entire.gn_map, gn]

/-- **Descent of monomials**: if the image of `x ∈ Frac E(L)` is `a·Uᵏ`, then `a = φ c` with
`c ∈ L` and `x = c·Uᵏ` (compare one nonzero coefficient). -/
theorem exists_eq_ofE_mono_of_map_eq {x : Mero L} {a : Ω} {k : ℤ}
    (h : map φ hφ x = ofE (a • Entire.mono k)) :
    ∃ c : L, φ c = a ∧ x = ofE (c • Entire.mono k) := by
  set g := num x
  set d := den x
  have hd := den_ne_zero x
  have hd' : Entire.map φ hφ d ≠ 0 := (map_ne_zero_iff _ (Entire.map_injective φ hφ)).mpr hd
  have e : Entire.map φ hφ g = a • Entire.mono k * Entire.map φ hφ d := by
    have h' := h
    rw [eq_num_div_den x, map_div, div_eq_iff (ofE_ne_zero hd'), ← ofE_mul] at h'
    exact ofE_injective h'
  have hc : ∀ n, φ (Entire.coeff g n) = a * φ (Entire.coeff d (n - k)) := fun n => by
    have := congrFun (congrArg Entire.coeff e) n
    rwa [Entire.coeff_map, smul_mul_assoc, Entire.coeff_smul, Pi.smul_apply, smul_eq_mul,
      Entire.coeff_mono_mul, Entire.coeff_map] at this
  obtain ⟨n₀, hn₀⟩ := Function.ne_iff.mp (Entire.coeff_ne_zero hd)
  set c := Entire.coeff g (n₀ + k) / Entire.coeff d n₀
  have hφc : φ c = a := by
    rw [map_div₀, hc, add_sub_cancel_right, mul_div_assoc,
      div_self ((map_ne_zero φ).mpr hn₀), mul_one]
  refine ⟨c, hφc, ?_⟩
  have hgd : g = c • Entire.mono k * d := Entire.ext_coeff (funext fun n => φ.injective (by
    rw [hc, smul_mul_assoc, Entire.coeff_smul, Pi.smul_apply, smul_eq_mul, Entire.coeff_mono_mul,
      map_mul, hφc]))
  rw [eq_num_div_den x]
  change ofE g / ofE d = _
  rw [hgd, ofE_mul, mul_div_cancel_right₀ _ (ofE_ne_zero hd)]

/-- Descent of constants. -/
theorem exists_eq_const_of_map_eq {x : Mero L} {a : Ω} (h : map φ hφ x = const a) :
    ∃ c : L, φ c = a ∧ x = const c := by
  have h' : map φ hφ x = ofE (a • Entire.mono 0) := by
    rw [h, Entire.mono_zero, Algebra.smul_def, mul_one]
  obtain ⟨c, hc, hx⟩ := exists_eq_ofE_mono_of_map_eq φ hφ h'
  exact ⟨c, hc, by rw [hx, Entire.mono_zero, Algebra.smul_def, mul_one]⟩

variable [IsAlgClosed Ω]

/-- **[EtTh] Proposition 3.4(ii) over `L`, the kernel**: `x ∈ Frac E(L)` has trivial divisor over
`Ω` (no zeros or poles at the points of `Ωˣ`, Gauss norm `1` on the component circles) iff
`x ∈ O_L^×`. -/
theorem ker_iff_of_map {x : Mero L} (hx : x ≠ 0) {q : L} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ((∀ α : Ωˣ, ord (map φ hφ x) α = 0) ∧ ∀ a : ℤ, gn x (‖q‖ ^ a) = 1) ↔
      ∃ c : L, ‖c‖ = 1 ∧ x = const c := by
  have hx' : map φ hφ x ≠ 0 := (map_ne_zero_iff _ (map_injective φ hφ)).mpr hx
  have hq0' : 0 < ‖φ q‖ := by rwa [hφ]
  have hq1' : ‖φ q‖ < 1 := by rwa [hφ]
  have key := ker_iff hx' hq0' hq1'
  have key2 : ∀ a : ℤ, gn (map φ hφ x) (‖q‖ ^ a) = gn x (‖q‖ ^ a) := fun a =>
    gn_map φ hφ x (zpow_pos hq0 a)
  simp only [hφ, key2] at key
  rw [key]
  constructor
  · rintro ⟨a, ha, he⟩
    obtain ⟨c, hc, rfl⟩ := exists_eq_const_of_map_eq φ hφ he
    exact ⟨c, by rw [← hφ, hc, ha], rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨φ c, by rw [hφ, hc], map_const φ hφ c⟩

/-- **[EtTh] Proposition 3.4(ii) over `L`, the effective part** `O^⊿_L ≅ B ×_{Φ^gp} Φ`. -/
theorem eff_iff_of_map {x : Mero L} (hx : x ≠ 0) {q : L} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ((∀ α : Ωˣ, 0 ≤ ord (map φ hφ x) α) ∧ ∀ a : ℤ, gn x (‖q‖ ^ a) ≤ 1) ↔
      ∃ c : L, c ≠ 0 ∧ ‖c‖ ≤ 1 ∧ x = const c := by
  have hx' : map φ hφ x ≠ 0 := (map_ne_zero_iff _ (map_injective φ hφ)).mpr hx
  have hq0' : 0 < ‖φ q‖ := by rwa [hφ]
  have hq1' : ‖φ q‖ < 1 := by rwa [hφ]
  have key := eff_iff hx' hq0' hq1'
  have key2 : ∀ a : ℤ, gn (map φ hφ x) (‖q‖ ^ a) = gn x (‖q‖ ^ a) := fun a =>
    gn_map φ hφ x (zpow_pos hq0 a)
  simp only [hφ, key2] at key
  rw [key]
  constructor
  · rintro ⟨a, ha0, ha, he⟩
    obtain ⟨c, hc, rfl⟩ := exists_eq_const_of_map_eq φ hφ he
    exact ⟨c, fun h0 => ha0 (by rw [← hc, h0, map_zero]), by rw [← hφ, hc]; exact ha, rfl⟩
  · rintro ⟨c, hc0, hc, rfl⟩
    exact ⟨φ c, (map_ne_zero φ).mpr hc0, by rw [hφ]; exact hc, map_const φ hφ c⟩

/-- A meromorphic function over `L` without zeros or poles over `Ω` is `c·Uᵏ`, `c ∈ L^×`. -/
theorem exists_eq_mono_of_ord_eq_zero {x : Mero L} (hx : x ≠ 0)
    (h : ∀ α : Ωˣ, ord (map φ hφ x) α = 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ k : ℤ, x = ofE (c • Entire.mono k) := by
  have hx' : map φ hφ x ≠ 0 := (map_ne_zero_iff _ (map_injective φ hφ)).mpr hx
  obtain ⟨F, hF, hFe⟩ := exists_entire_of_ord_nonneg hx' fun α => (h α).symm.le
  have hz : ∀ u : Ωˣ, (F : Ωˣ → Ω) u ≠ 0 := fun u => by
    have := h u
    rw [hFe, ord_ofE hF, Nat.cast_eq_zero] at this
    exact (ord_eq_zero_iff hF u).mp this
  obtain ⟨a, ha, k, rfl⟩ := eq_smul_mono_of_ne_zero hF hz
  obtain ⟨c, hc, hxc⟩ := exists_eq_ofE_mono_of_map_eq φ hφ hFe
  exact ⟨c, fun h0 => ha (by rw [← hc, h0, map_zero]), k, hxc⟩

include φ hφ in
/-- **[EtTh] Proposition 3.2(iii) for meromorphic functions on `𝔾_m^an`**: over a locally compact
ultrametric field `L` (finite over `ℚ_p`), a nonzero meromorphic function with an `N`-th root in
`Frac E(L)` for every `N ≥ 1` is `1`. (The divisor is computed over `Ω`.) -/
theorem eq_one_of_forall_pow [ProperSpace L] {x : Mero L} (hx : x ≠ 0)
    (h : ∀ N : ℕ, 0 < N → ∃ y : Mero L, y ^ N = x) : x = 1 := by
  have hroot0 : ∀ {N : ℕ} {y : Mero L}, 0 < N → y ^ N = x → y ≠ 0 := fun hN hy h0 => by
    rw [h0, zero_pow hN.ne'] at hy; exact hx hy.symm
  have hpow : ∀ {N : ℕ} {y : Mero L}, y ≠ 0 → ∀ α : Ωˣ,
      ord (map φ hφ (y ^ N)) α = N * ord (map φ hφ y) α := fun {N} {y} hy α => by
    rw [map_pow, ord_pow ((map_ne_zero_iff _ (map_injective φ hφ)).mpr hy)]
  -- the divisor of `x` vanishes
  have hord : ∀ α : Ωˣ, ord (map φ hφ x) α = 0 := fun α => by
    set M := (ord (map φ hφ x) α).natAbs + 1 with hM
    obtain ⟨y, hy⟩ := h M (Nat.succ_pos _)
    have := hpow (N := M) (hroot0 (Nat.succ_pos _) hy) α
    rw [hy] at this
    rcases eq_or_ne (ord (map φ hφ y) α) 0 with h0 | h0
    · rw [this, h0, mul_zero]
    · exfalso
      have e := congrArg Int.natAbs this
      rw [Int.natAbs_mul, Int.natAbs_natCast] at e
      have h1 : M ≤ M * (ord (map φ hφ y) α).natAbs :=
        Nat.le_mul_of_pos_right M (Int.natAbs_pos.mpr h0)
      rw [← e] at h1
      omega
  obtain ⟨c, hc0, k, hxk⟩ := exists_eq_mono_of_ord_eq_zero φ hφ hx hord
  -- each root is a monomial, which forces `k = 0` and `c ∈ ⋂ (L^×)^N`
  have hroots : ∀ N : ℕ, 0 < N → (N : ℤ) ∣ k ∧ ∃ b : L, b ^ N = c := fun N hN => by
    obtain ⟨y, hy⟩ := h N hN
    have hy0 := hroot0 hN hy
    have hordy : ∀ α : Ωˣ, ord (map φ hφ y) α = 0 := fun α => by
      have := hpow (N := N) hy0 α
      rw [hy, hord α] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (by exact_mod_cast hN.ne')
    obtain ⟨b, hb0, j, rfl⟩ := exists_eq_mono_of_ord_eq_zero φ hφ hy0 hordy
    rw [← ofE_pow, smul_pow, Entire.mono_pow, hxk] at hy
    have e := ofE_injective hy
    have e2 := congrFun (congrArg Entire.coeff e) k
    simp only [Entire.coeff_smul, Entire.coeff_mono, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, if_true, mul_one] at e2
    by_cases hk : k = N * j
    · exact ⟨⟨j, hk⟩, b, by rw [if_pos hk, mul_one] at e2; exact e2⟩
    · rw [if_neg hk, mul_zero] at e2
      exact absurd e2.symm hc0
  have hk : k = 0 := by
    obtain ⟨⟨m, hm⟩, -⟩ := hroots (k.natAbs + 1) (Nat.succ_pos _)
    rcases eq_or_ne m 0 with h0 | h0
    · rw [hm, h0, mul_zero]
    · exfalso
      have e := congrArg Int.natAbs hm
      rw [Int.natAbs_mul, Int.natAbs_natCast] at e
      have h1 : k.natAbs + 1 ≤ (k.natAbs + 1) * m.natAbs :=
        Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr h0)
      rw [← e] at h1
      omega
  have hc1 : c = 1 := eq_one_of_forall_pow_eq hc0 fun N hN => (hroots N hN).2
  rw [hxk, hk, hc1, one_smul, Entire.mono_zero, ofE_one]

end Mero

end Iut.Frobenioid.BAn
