/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GlobalNonRlf

/-!
# The fractional-ideal version of the global Frobenioid (IUT III, Example 3.6(ii))

IUT III, Example 3.6(ii) (l.7148–7202 of `~/iut-scratch/papers/txt/`): "An object `J = {J_v}_{v∈V}`
[…] consists of a collection of "fractional ideals" `J_v ⊆ K_v` for each `v ∈ V` — i.e., a finitely
generated nonzero `O_{K_v}`-submodule of `K_v` when `v ∈ V^non`; a positive real multiple of
`O_{K_v} = {λ ∈ K_v | |λ| ≤ 1}` when `v ∈ V^arc` — such that `J_v = O_{K_v}` for all but finitely
many `v`. […] An elementary morphism `J_1 → J_2` […] is defined to be an element `f ∈ F_mod^×`
that is integral with respect to `J_1` and `J_2` in the sense that
`f · J_{1,v} ⊆ J_{2,v}` for each `v ∈ V`.
[…] A morphism `J_1 → J_2` […] is defined to consist of a positive integer `n` and an elementary
morphism `(J_1)^{⊗n} → J_2`. […] there exists a natural isomorphism of Frobenioids
`F^⊛_mod ≅ F^⊛_mod` [the fractional-ideal version] that induces the identity morphism
`F_mod^× → F_mod^×` on the associated rational function monoids."

## Formalisation

We work over an arbitrary number field `K` (in IUT, `K = F_mod`) and its own places.

* At the finite places, a family `{J_v}` of local fractional ideals, almost all equal to `O_v`, is
  the same as one nonzero fractional ideal `I` of `𝓞_K` (`J_v = I·O_v`; `ord_v(J_v) = count_v(I)`),
  so the finite part of an object is a nonzero `FractionalIdeal (𝓞 K)⁰ K`. At an archimedean
  place, `J_v = r_v·O_{K_v}` is recorded by `r_v > 0`, and `f·J_{1,v}^{⊗n} ⊆ J_{2,v}` reads
  `|f|_v·r_{1,v}^n ≤ r_{2,v}`.
* **The fractional-ideal lemma** (not in Mathlib, which only has `FractionalIdeal.count_mono` and
  the integral-ideal version): for nonzero fractional ideals of a Dedekind domain,
  **`FracIdeal.le_iff_count_le`**: `I ≤ J ↔ ∀ v, count_v J ≤ count_v I`; also
  `FracIdeal.eq_of_count_eq` and `FracIdeal.count_ofCounts` (every finitely supported family of
  exponents is realised).
* **`FracIdealFrob K`**: the category of IUT III, Example 3.6(ii) (`FracIdealObj`, `FracIdealHom`,
  composition `(m, g) ∘ (n, f) = (mn, g·f^m)`).
* **`FracIdealFrob.toModel : FracIdealFrob K ⥤ GlobalFrobenioid K`** (`J ↦ (−count(I), log r)`),
  which is an **isomorphism of categories**: `toModel_obj_bijective`, `Full`, `Faithful`
  (`FracIdealFrob.equivModel` is the induced equivalence); it preserves Frobenius degrees
  (`toModel_map_deg`), so elementary morphisms are the linear morphisms, and it **induces the
  identity on `K^×`** (`toModel_map_u`). The key computation is **`integral_iff`**:
  `f·J_1^n ⊆ J_2` at all places iff `α(J_2) + div(f) − n·α(J_1)` is effective.

**Remark (ramification).** The text takes `J_v ⊆ K_v` for the field `K ⊇ F_mod` of IUT I,
Definition 3.1, and `f ∈ F_mod^×`. If `e = e(K_v|(F_mod)_v) > 1`, then `f·π_{K_v}^{n a_1} O ⊆
π_{K_v}^{a_2} O` iff `e·ord_v(f) + n a_1 ≥ a_2`, and for `a_1, a_2 ∉ eℤ` this condition is not of
the form `ord_v(f) + n b_1 ≥ b_2`, so such a category is not isomorphic to the [FrdI] Example 6.3
Frobenioid of `F_mod` compatibly with the identity on `F_mod^×`. Taking the local fields of
`F_mod` itself (as here, `K = F_mod`) gives the isomorphism; cf. IUT III, Remark 3.6.1, which
reads the `β_v` as subquotients of the *perfection* `(F_mod^×)^pf`, where the factor `e` disappears.
-/

namespace Iut

open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors

namespace Arakelov

namespace FracIdeal

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

omit [IsDedekindDomain R] [IsFractionRing R K] in
variable (K) in
/-- A finite product of nonnegative powers of primes is an integral ideal. -/
lemma exists_coeIdeal_finprod (f : HeightOneSpectrum R → ℕ) :
    ∃ J : Ideal R, (∏ᶠ v, (v.asIdeal : FractionalIdeal R⁰ K) ^ f v) = J := by
  refine finprod_induction
    (fun I : FractionalIdeal R⁰ K => ∃ J : Ideal R, I = (J : FractionalIdeal R⁰ K))
    ⟨⊤, by simp⟩ ?_ ?_
  · rintro _ _ ⟨J₁, rfl⟩ ⟨J₂, rfl⟩
    exact ⟨J₁ * J₂, (coeIdeal_mul _ _).symm⟩
  · intro v
    exact ⟨v.asIdeal ^ f v, by rw [coeIdeal_pow]⟩

/-- **A nonzero fractional ideal with nonnegative valuations is integral**: `I ≤ 1`. -/
theorem le_one_of_count_nonneg {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, 0 ≤ count K v I) : I ≤ 1 := by
  rw [← finprod_heightOneSpectrum_factorization' K hI]
  have hc : ∀ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v I =
      (v.asIdeal : FractionalIdeal R⁰ K) ^ (count K v I).toNat := fun v => by
    rw [← zpow_natCast, Int.toNat_of_nonneg (h v)]
  rw [finprod_congr hc]
  obtain ⟨J, hJ⟩ := exists_coeIdeal_finprod K fun v => (count K v I).toNat
  rw [hJ]
  exact coeIdeal_le_one

/-- **The fractional-ideal lemma**: for nonzero fractional ideals of a Dedekind domain,
`I ≤ J ↔ ∀ v, count_v J ≤ count_v I`. -/
theorem le_iff_count_le {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ v : HeightOneSpectrum R, count K v J ≤ count K v I := by
  refine ⟨fun h v => count_mono K v hI h, fun h => ?_⟩
  have hJ' : J⁻¹ ≠ 0 := inv_ne_zero hJ
  have h1 : I * J⁻¹ ≤ 1 := le_one_of_count_nonneg (mul_ne_zero hI hJ') fun v => by
    rw [count_mul K v hI hJ', count_inv]
    linarith [h v]
  calc I = I * J⁻¹ * J := by rw [mul_assoc, inv_mul_cancel₀ hJ, mul_one]
    _ ≤ 1 * J := mul_le_mul_left h1 J
    _ = J := one_mul J

/-- Nonzero fractional ideals are determined by their valuations. -/
theorem eq_of_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, count K v I = count K v J) : I = J :=
  le_antisymm ((le_iff_count_le hI hJ).2 fun v => (h v).ge)
    ((le_iff_count_le hJ hI).2 fun v => (h v).le)

variable (K) in
/-- The fractional ideal `∏_v 𝔭_v^{c_v}` with prescribed valuations. -/
noncomputable def ofCounts (c : HeightOneSpectrum R →₀ ℤ) : FractionalIdeal R⁰ K :=
  ∏ᶠ v, (v.asIdeal : FractionalIdeal R⁰ K) ^ c v

lemma ofCounts_ne_zero (c : HeightOneSpectrum R →₀ ℤ) : ofCounts K c ≠ 0 :=
  finprod_induction (fun I : FractionalIdeal R⁰ K => I ≠ 0) one_ne_zero
    (fun _ _ => mul_ne_zero) fun v => zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

/-- **Every finitely supported family of exponents is realised**: `count_v(∏ 𝔭^{c}) = c_v`. -/
theorem count_ofCounts (c : HeightOneSpectrum R →₀ ℤ) (v : HeightOneSpectrum R) :
    count K v (ofCounts K c) = c v := by
  refine count_finprod K v c ?_
  rw [Filter.eventually_cofinite]
  exact c.hasFiniteSupport.subset fun w hw => by simpa using hw

end FracIdeal

end Arakelov

namespace Frobenioid

open CategoryTheory NumberField Arakelov

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- **An object of the fractional-ideal Frobenioid** (IUT III, Example 3.6(ii)): a nonzero
fractional ideal `I` of `𝓞_K` (the local fractional ideals `J_v = I·O_v` at the finite places) and
radii `r_v > 0` (`J_v = r_v·O_{K_v}` at the archimedean places). -/
structure FracIdealObj where
  /-- The finite part. -/
  I : FractionalIdeal (𝓞 K)⁰ K
  ne_zero : I ≠ 0
  /-- The archimedean radii. -/
  r : InfinitePlace K → ℝ
  r_pos : ∀ v, 0 < r v

variable {K}

namespace FracIdealObj

/-- **Integrality of `f` with respect to `J_1^{⊗n}` and `J_2`**: `f·J_{1,v}^{⊗n} ⊆ J_{2,v}` at all
places. -/
def Integral (J₁ J₂ : FracIdealObj K) (n : ℕ) (f : Kˣ) : Prop :=
  spanSingleton (𝓞 K)⁰ (f : K) * J₁.I ^ n ≤ J₂.I ∧ ∀ v, v (f : K) * J₁.r v ^ n ≤ J₂.r v

end FracIdealObj

/-- **A morphism of the fractional-ideal Frobenioid**: a positive integer `n` (the Frobenius
degree) and an elementary morphism `f : J_1^{⊗n} → J_2`. -/
@[ext]
structure FracIdealHom (J₁ J₂ : FracIdealObj K) where
  /-- The Frobenius degree. -/
  deg : ℕ+
  /-- The rational function. -/
  f : Kˣ
  integral : J₁.Integral J₂ deg f

variable (K) in
/-- **The fractional-ideal Frobenioid** of IUT III, Example 3.6(ii) (base category: one arrow). -/
def FracIdealFrob : Type u := FracIdealObj K

namespace FracIdealFrob

lemma integral_id (J : FracIdealObj K) : J.Integral J 1 1 :=
  ⟨by simp, fun v => by simp⟩

lemma integral_comp {J₁ J₂ J₃ : FracIdealObj K} {n m : ℕ} {f g : Kˣ}
    (hf : J₁.Integral J₂ n f) (hg : J₂.Integral J₃ m g) : J₁.Integral J₃ (m * n) (g * f ^ m) := by
  refine ⟨?_, fun v => ?_⟩
  · calc spanSingleton (𝓞 K)⁰ ((g * f ^ m : Kˣ) : K) * J₁.I ^ (m * n)
          = spanSingleton (𝓞 K)⁰ (g : K) * (spanSingleton (𝓞 K)⁰ (f : K) * J₁.I ^ n) ^ m := by
            rw [mul_pow, spanSingleton_pow, ← pow_mul, ← mul_assoc, spanSingleton_mul_spanSingleton,
              mul_comm n m, Units.val_mul, Units.val_pow_eq_pow_val]
      _ ≤ spanSingleton (𝓞 K)⁰ (g : K) * J₂.I ^ m := by gcongr; exact hf.1
      _ ≤ J₃.I := hg.1
  · have h0 : 0 ≤ v (f : K) * J₁.r v ^ n :=
      mul_nonneg (v.pos_iff.mpr f.ne_zero).le (pow_nonneg (J₁.r_pos v).le _)
    calc v ((g * f ^ m : Kˣ) : K) * J₁.r v ^ (m * n)
          = v (g : K) * (v (f : K) * J₁.r v ^ n) ^ m := by
            rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, mul_pow, ← pow_mul,
              mul_comm n m, mul_assoc]
      _ ≤ v (g : K) * J₂.r v ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (hf.2 v) m) (v.pos_iff.mpr g.ne_zero).le
      _ ≤ J₃.r v := hg.2 v

instance : Category (FracIdealFrob K) where
  Hom := FracIdealHom
  id J := ⟨1, 1, integral_id J⟩
  comp φ ψ := ⟨ψ.deg * φ.deg, ψ.f * φ.f ^ (ψ.deg : ℕ), by
    rw [PNat.mul_coe]; exact integral_comp φ.integral ψ.integral⟩
  id_comp φ := FracIdealHom.ext (mul_one _) (by simp)
  comp_id φ := FracIdealHom.ext (one_mul _) (by simp)
  assoc φ ψ χ := FracIdealHom.ext (mul_assoc _ _ _).symm (by
    simp only [PNat.mul_coe, mul_pow, ← pow_mul, mul_assoc, mul_comm (ψ.deg : ℕ)])

@[ext] lemma hom_ext {J₁ J₂ : FracIdealFrob K} {φ ψ : J₁ ⟶ J₂} (h₁ : φ.deg = ψ.deg)
    (h₂ : φ.f = ψ.f) : φ = ψ :=
  FracIdealHom.ext h₁ h₂

@[simp] lemma id_deg (J : FracIdealFrob K) : FracIdealHom.deg (𝟙 J) = 1 := rfl
@[simp] lemma id_f (J : FracIdealFrob K) : FracIdealHom.f (𝟙 J) = 1 := rfl
@[simp] lemma comp_deg {J₁ J₂ J₃ : FracIdealFrob K} (φ : J₁ ⟶ J₂) (ψ : J₂ ⟶ J₃) :
    FracIdealHom.deg (φ ≫ ψ) = ψ.deg * φ.deg := rfl
@[simp] lemma comp_f {J₁ J₂ J₃ : FracIdealFrob K} (φ : J₁ ⟶ J₂) (ψ : J₂ ⟶ J₃) :
    FracIdealHom.f (φ ≫ ψ) = ψ.f * φ.f ^ (ψ.deg : ℕ) := rfl

/-! ### The comparison with the [FrdI] Example 6.3 Frobenioid -/

/-- `count_w(I)` at a finite place `w`. -/
noncomputable abbrev cnt (I : FractionalIdeal (𝓞 K)⁰ K) (w : FinitePlace K) : ℤ :=
  count K w.maximalIdeal I

lemma finite_support_cnt (I : FractionalIdeal (𝓞 K)⁰ K) : (Function.support (cnt I)).Finite := by
  have h := FractionalIdeal.finite_factors (K := K) I
  rw [Filter.eventually_cofinite] at h
  refine (h.preimage (FinitePlace.equivHeightOneSpectrum.injective.injOn)).subset fun w hw => ?_
  exact hw

/-- **The arithmetic divisor of `J`**: `α(J) = (−count_w(I), log r_v)`. -/
noncomputable def alpha (J : FracIdealObj K) : ArithDivZ K :=
  (Finsupp.ofSupportFinite (fun w => -cnt J.I w)
      ((finite_support_cnt J.I).subset fun w hw => by simpa using hw),
    fun v => Real.log (J.r v))

@[simp] lemma alpha_fst (J : FracIdealObj K) (w : FinitePlace K) :
    (alpha J).1 w = -cnt J.I w := rfl

@[simp] lemma alpha_snd (J : FracIdealObj K) (v : InfinitePlace K) :
    (alpha J).2 v = Real.log (J.r v) := rfl

/-- `count_w((x)) = ord_w(x)`. -/
lemma cnt_spanSingleton (x : Kˣ) (w : FinitePlace K) :
    cnt (spanSingleton (𝓞 K)⁰ (x : K)) w = ordZ x w := by
  rw [cnt, ← ArithLineBundle.fracIdeal_principal _ x.ne_zero, ArithLineBundle.count_fracIdeal,
    FinitePlace.mk_maximalIdeal, ordZ_apply]

/-- **Integrality is effectivity of `α(J_2) + div(f) − n·α(J_1)`.** -/
theorem integral_iff (J₁ J₂ : FracIdealObj K) (n : ℕ) (f : Kˣ) :
    J₁.Integral J₂ n f ↔ alpha J₂ + divZ K (Additive.ofMul f) - n • alpha J₁ ∈ effConeZ K := by
  have hs : spanSingleton (𝓞 K)⁰ (f : K) ≠ 0 := spanSingleton_ne_zero_iff.mpr f.ne_zero
  have hp : spanSingleton (𝓞 K)⁰ (f : K) * J₁.I ^ n ≠ 0 := mul_ne_zero hs (pow_ne_zero _ J₁.ne_zero)
  rw [FracIdealObj.Integral, Arakelov.FracIdeal.le_iff_count_le hp J₂.ne_zero, mem_effConeZ]
  refine and_congr ?_ (forall_congr' fun v => ?_)
  · rw [← FinitePlace.equivHeightOneSpectrum.forall_congr_right]
    refine forall_congr' fun w => ?_
    have hc : count K (FinitePlace.equivHeightOneSpectrum w) (spanSingleton (𝓞 K)⁰ (f : K) *
        J₁.I ^ n) = ordZ f w + n * cnt J₁.I w := by
      rw [count_mul K _ hs (pow_ne_zero _ J₁.ne_zero), count_pow]
      exact congrArg₂ (· + ·) (cnt_spanSingleton f w) rfl
    rw [hc]
    change cnt J₂.I w ≤ _ ↔
      0 ≤ (alpha J₂).1 w + (divZ K (Additive.ofMul f)).1 w - n • (alpha J₁).1 w
    simp only [alpha_fst, nsmul_eq_mul]
    change _ ↔ 0 ≤ -cnt J₂.I w + ordZ f w - n * -cnt J₁.I w
    constructor <;> intro h <;> linarith
  · have h1 := J₁.r_pos v
    have h2 := J₂.r_pos v
    have hf : 0 < v (f : K) := v.pos_iff.mpr f.ne_zero
    change _ ↔ 0 ≤ Real.log (J₂.r v) + -Real.log (v (f : K)) - n • Real.log (J₁.r v)
    rw [← Real.log_le_log_iff (mul_pos hf (pow_pos h1 n)) h2, Real.log_mul hf.ne' (by positivity),
      Real.log_pow, nsmul_eq_mul]
    constructor <;> intro h <;> linarith

lemma integral_of_hom {J₁ J₂ : FracIdealObj K} (ψ : (⟨pt, alpha J₁⟩ : GlobalFrobenioid K) ⟶
    ⟨pt, alpha J₂⟩) : J₁.Integral J₂ ψ.deg (Additive.toMul ψ.u) := by
  rw [integral_iff, ofMul_toMul]
  have h : ψ.div = alpha J₂ + divZ K ψ.u - (ψ.deg : ℕ) • alpha J₁ := by
    have r := ψ.rel
    change (ψ.deg : ℕ) • alpha J₁ + ψ.div = alpha J₂ + divZ K ψ.u at r
    rw [← r]
    abel
  rw [← h]
  exact ψ.div_mem

variable (K) in
/-- **The isomorphism `F^⊛_mod (fractional ideals) → F^⊛_mod ([FrdI] Ex 6.3)`**:
`J ↦ α(J) = (−count(I), log r)`, `(n, f) ↦ (n, id, α(J_2) + div(f) − n·α(J_1), f)`. -/
noncomputable def toModel : FracIdealFrob K ⥤ GlobalFrobenioid K where
  obj J := ⟨pt, alpha J⟩
  map {J₁ J₂} φ := Model.mk' φ.deg (𝟙 _) (alpha J₂ + divZ K (Additive.ofMul φ.f) -
      (φ.deg : ℕ) • alpha J₁) ((integral_iff J₁ J₂ _ φ.f).mp φ.integral) (Additive.ofMul φ.f) (by
    change (φ.deg : ℕ) • alpha J₁ + (alpha J₂ + divZ K (Additive.ofMul φ.f) -
      (φ.deg : ℕ) • alpha J₁) = alpha J₂ + divZ K (Additive.ofMul φ.f)
    abel)
  map_id J := by
    refine Model.hom_ext rfl (Subsingleton.elim _ _) ?_ rfl
    change alpha J + divZ K (Additive.ofMul (1 : Kˣ)) - (1 : ℕ) • alpha J = 0
    rw [ofMul_one, map_zero, one_smul]
    abel
  map_comp {J₁ J₂ J₃} φ ψ := by
    refine Model.hom_ext rfl (Subsingleton.elim _ _) ?_ ?_
    · change alpha J₃ + divZ K (Additive.ofMul (ψ.f * φ.f ^ (ψ.deg : ℕ))) -
        ((ψ.deg * φ.deg : ℕ+) : ℕ) • alpha J₁ = (alpha J₃ + divZ K (Additive.ofMul ψ.f) -
        (ψ.deg : ℕ) • alpha J₂) + (ψ.deg : ℕ) • (alpha J₂ + divZ K (Additive.ofMul φ.f) -
        (φ.deg : ℕ) • alpha J₁)
      rw [ofMul_mul, ofMul_pow, map_add, map_nsmul, PNat.mul_coe, mul_smul]
      module
    · change Additive.ofMul (ψ.f * φ.f ^ (ψ.deg : ℕ)) =
        Additive.ofMul ψ.f + (ψ.deg : ℕ) • Additive.ofMul φ.f
      rw [ofMul_mul, ofMul_pow]

@[simp] lemma toModel_obj_α (J : FracIdealFrob K) : ((toModel K).obj J).α = alpha J := rfl

/-- **The isomorphism preserves Frobenius degrees** (so elementary morphisms are the linear
morphisms). -/
@[simp] lemma toModel_map_deg {J₁ J₂ : FracIdealFrob K} (φ : J₁ ⟶ J₂) :
    ((toModel K).map φ).deg = φ.deg := rfl

/-- **The isomorphism induces the identity on the rational function monoids `K^×`.** -/
@[simp] lemma toModel_map_u {J₁ J₂ : FracIdealFrob K} (φ : J₁ ⟶ J₂) :
    ((toModel K).map φ).u = Additive.ofMul φ.f := rfl

instance : (toModel K).Faithful where
  map_injective {_ _} φ ψ h :=
    hom_ext (congrArg Model.Hom.deg h) (by simpa using congrArg Model.Hom.u h)

instance : (toModel K).Full where
  map_surjective {J₁ J₂} ψ := ⟨⟨ψ.deg, Additive.toMul ψ.u, integral_of_hom ψ⟩, by
    refine Model.hom_ext rfl (Subsingleton.elim _ _) ?_ rfl
    have r := ψ.rel
    change (ψ.deg : ℕ) • alpha J₁ + ψ.div = alpha J₂ + divZ K ψ.u at r
    change alpha J₂ + divZ K ψ.u - (ψ.deg : ℕ) • alpha J₁ = ψ.div
    rw [← r]
    abel⟩

/-- The object with prescribed arithmetic divisor. -/
noncomputable def ofDiv (x : ArithDivZ K) : FracIdealObj K where
  I := FracIdeal.ofCounts K ((-x.1).equivMapDomain FinitePlace.equivHeightOneSpectrum)
  ne_zero := FracIdeal.ofCounts_ne_zero _
  r v := Real.exp (x.2 v)
  r_pos _ := Real.exp_pos _

lemma alpha_ofDiv (x : ArithDivZ K) : alpha (ofDiv x) = x := by
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · rw [alpha_fst, cnt, ofDiv]
    dsimp only
    rw [FracIdeal.count_ofCounts]
    change -(-x.1) (FinitePlace.equivHeightOneSpectrum.symm (FinitePlace.equivHeightOneSpectrum w))
      = x.1 w
    simp only [Finsupp.coe_neg, Pi.neg_apply, neg_neg]
    exact congrArg x.1 (FinitePlace.equivHeightOneSpectrum.symm_apply_apply w)
  · exact Real.log_exp _

/-- **`toModel` is bijective on objects** (an isomorphism of categories, with `Full`,
`Faithful`). -/
theorem toModel_obj_bijective : Function.Bijective (toModel K).obj := by
  refine ⟨fun J₁ J₂ h => ?_, fun X => ⟨ofDiv X.α, ?_⟩⟩
  · have hα : alpha J₁ = alpha J₂ := congrArg Model.α h
    obtain ⟨I₁, h₁, r₁, hr₁⟩ := J₁
    obtain ⟨I₂, h₂, r₂, hr₂⟩ := J₂
    have hI : I₁ = I₂ := FracIdeal.eq_of_count_eq h₁ h₂ fun v => by
      have := congrArg (fun x => x.1 (FinitePlace.mk v)) hα
      simpa [cnt, FinitePlace.maximalIdeal_mk] using this
    have hr : r₁ = r₂ := funext fun v => by
      have := congrArg (fun x => x.2 v) hα
      exact Real.log_injOn_pos (hr₁ v) (hr₂ v) this
    subst hI hr
    rfl
  · change (⟨pt, alpha (ofDiv X.α)⟩ : GlobalFrobenioid K) = X
    rw [alpha_ofDiv]

instance : (toModel K).EssSurj where
  mem_essImage X := by
    obtain ⟨J, hJ⟩ := toModel_obj_bijective.2 X
    exact ⟨J, ⟨eqToIso hJ⟩⟩

instance : (toModel K).IsEquivalence where

variable (K) in
/-- **IUT III, Example 3.6(ii)**: the fractional-ideal Frobenioid is equivalent (indeed
isomorphic, `toModel_obj_bijective`) to the [FrdI] Example 6.3 Frobenioid, compatibly with
Frobenius degrees and with the identity on `K^×`. -/
noncomputable def equivModel : FracIdealFrob K ≌ GlobalFrobenioid K := (toModel K).asEquivalence

end FracIdealFrob

end Frobenioid

end Iut
