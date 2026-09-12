/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.SerreCore

/-!
# Serre's bound on the different of a Dedekind extension (IUT IV, Proposition 1.3)

For Dedekind domains `A ⊆ B` with `B` finite over `A` and separable fraction fields, a
maximal ideal `𝔓` of `B` over `𝔭` of `A` with finite residue field, `e = e(𝔓/𝔭)` and `κ`
with `e ∉ 𝔭^{κ+1}`:

  `𝔓^{e(κ+1)} ∤ 𝔇_{B/A}`  (`Iut.Serre.not_pow_dvd_differentIdeal`),

i.e. `ord_𝔓(𝔇_{B/A}) ≤ e − 1 + e·κ`; with `κ = ord_𝔭(e)` this is Serre's
`ord_𝔓(𝔇) ≤ e − 1 + ord_𝔓(e)` (*Local Fields*, III §6, Remark after Proposition 13).

The proof: by Mathlib's `not_dvd_differentIdeal_of_intTrace_not_mem` it suffices to find
`x ∈ J^{κ+1}` (`𝔭B = 𝔓^e·J`) with `Tr_{B/A}(x) ∉ 𝔭^{κ+1}`. After localizing at `𝔭`
(`Bₚ` is free over the discrete valuation ring `Aₚ`) the trace modulo `𝔭^{κ+1}` is the
trace of `Bₚ/𝔭^{κ+1}Bₚ = Bₚ/𝔓^{e(κ+1)} × Bₚ/J^{κ+1}` over `Aₚ/𝔭^{κ+1}`, and the trace of
the first factor is not identically zero (`Iut.Serre.free_and_exists_trace_ne_zero`).
-/

namespace Iut.Serre

open IsLocalRing nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Elementary

variable {A : Type*} [CommRing A] (𝔭 : Ideal A) [𝔭.IsMaximal]

/-- `𝔭 + (s) = 1` for `s ∉ 𝔭`. -/
lemma sup_span_singleton_eq_top {s : A} (hs : s ∉ 𝔭) : 𝔭 ⊔ Ideal.span {s} = ⊤ := by
  by_contra h
  have := Ideal.IsMaximal.eq_of_le ‹𝔭.IsMaximal› h le_sup_left
  exact hs (this ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))

/-- `s ∉ 𝔭`, `s·a ∈ 𝔭^n` ⟹ `a ∈ 𝔭^n`. -/
lemma mem_pow_of_mul_mem_pow {s a : A} (hs : s ∉ 𝔭) (n : ℕ) (h : s * a ∈ 𝔭 ^ n) :
    a ∈ 𝔭 ^ n := by
  have hcop : IsCoprime (𝔭 ^ n) (Ideal.span {s}) :=
    (Ideal.isCoprime_iff_sup_eq.mpr (sup_span_singleton_eq_top 𝔭 hs)).pow_left
  obtain ⟨x, hx, y, hy, hxy⟩ := hcop.exists
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have : a = a * x + c * (s * a) := by
    calc a = a * (x + c * s) := by rw [hxy, mul_one]
      _ = a * x + c * (s * a) := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_left _ _ h)

/-- For coprime ideals `I`, `J` there is `w ∈ J` with `1 − w ∈ I`. -/
lemma exists_mem_and_one_sub_mem {R : Type*} [CommRing R] {I J : Ideal R} (h : IsCoprime I J) :
    ∃ w ∈ J, 1 - w ∈ I := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists
  exact ⟨y, hy, by rw [← hxy, add_sub_cancel_right]; exact hx⟩

end Elementary

section Localized

variable {A B : Type*} [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
variable (𝔭 : Ideal A) [𝔭.IsMaximal] [Finite (A ⧸ 𝔭)] (𝔓 : Ideal B) [𝔓.IsMaximal] [𝔓.LiesOver 𝔭]
variable (Rₚ Sₚ : Type*) [CommRing Rₚ] [CommRing Sₚ] [Algebra A Rₚ] [IsLocalization.AtPrime Rₚ 𝔭]
  [IsLocalRing Rₚ] [Algebra B Sₚ] [Algebra A Sₚ] [Algebra Rₚ Sₚ]
  [IsLocalization (Algebra.algebraMapSubmonoid B 𝔭.primeCompl) Sₚ]
  [IsScalarTower A B Sₚ] [IsScalarTower A Rₚ Sₚ]
  [IsDedekindDomain Rₚ] [IsDedekindDomain Sₚ] [Module.Finite Rₚ Sₚ] [Module.Free Rₚ Sₚ]
  [Module.IsTorsionFree Rₚ Sₚ]

include Rₚ Sₚ in
/-- **The trace of an element supported at `𝔓` is not divisible by `𝔭^{κ+1}`**: for
`𝔭B = 𝔓^e·J`, `𝔓 + J = 1` and `e ∉ 𝔭^{κ+1}` there is `x ∈ J^{κ+1}` with
`Tr_{B/A}(x) ∉ 𝔭^{κ+1}`, computed in the localization `Sₚ/Rₚ` at `𝔭`. -/
theorem exists_mem_pow_intTrace_notMem (h𝔭 : 𝔭 ≠ ⊥) (e κ : ℕ) (J : Ideal B) (he : e ≠ 0)
    (hpB : 𝔭.map (algebraMap A B) = 𝔓 ^ e * J) (hJ : 𝔓 ⊔ J = ⊤)
    (hκ : ((e : ℕ) : A) ∉ 𝔭 ^ (κ + 1)) :
    ∃ x ∈ J ^ (κ + 1), Algebra.intTrace A B x ∉ 𝔭 ^ (κ + 1) := by
  classical
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have h𝔓 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 𝔓
  set N := e * (κ + 1) with hN
  have hM : Algebra.algebraMapSubmonoid B 𝔭.primeCompl ≤ B⁰ :=
    Submonoid.map_le_of_le_comap _ <| 𝔭.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  have hinjA : Function.Injective (algebraMap A Rₚ) :=
    IsLocalization.injective Rₚ 𝔭.primeCompl_le_nonZeroDivisors
  have hinjB : Function.Injective (algebraMap B Sₚ) := IsLocalization.injective Sₚ hM
  -- the ideals `𝔪 = 𝔭Rₚ`, `𝔓ₚ`, `Jₚ`
  have h𝔪 : 𝔭.map (algebraMap A Rₚ) = maximalIdeal Rₚ :=
    IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 Rₚ
  have h𝔪0 : maximalIdeal Rₚ ≠ ⊥ := by
    rw [← h𝔪]
    exact (Ideal.map_eq_bot_iff_of_injective hinjA).not.mpr h𝔭
  set 𝔓ₚ : Ideal Sₚ := 𝔓.map (algebraMap B Sₚ) with h𝔓ₚ
  set Jₚ : Ideal Sₚ := J.map (algebraMap B Sₚ) with hJₚ
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid B 𝔭.primeCompl : Set B) (𝔓 : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hs𝔓
    exact hs (by rw [𝔓.over_def 𝔭]; exact hs𝔓)
  haveI : 𝔓ₚ.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Sₚ 𝔓 inferInstance hdisj
  have h𝔓ₚ0 : 𝔓ₚ ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective hinjB).not.mpr h𝔓
  haveI : 𝔓ₚ.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔓ₚ0
  have hpSₚ : (maximalIdeal Rₚ).map (algebraMap Rₚ Sₚ) = 𝔓ₚ ^ e * Jₚ := by
    rw [← h𝔪, Ideal.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A B Sₚ,
      ← Ideal.map_map, hpB, Ideal.map_mul, Ideal.map_pow]
  have hJₚ' : 𝔓ₚ ⊔ Jₚ = ⊤ := by
    rw [h𝔓ₚ, hJₚ, ← Ideal.map_sup, hJ, Ideal.map_top]
  haveI : 𝔓ₚ.LiesOver (maximalIdeal Rₚ) := by
    constructor
    refine Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance) ?_
    change maximalIdeal Rₚ ≤ 𝔓ₚ.comap (algebraMap Rₚ Sₚ)
    rw [← Ideal.map_le_iff_le_comap, hpSₚ]
    exact Ideal.mul_le_right.trans (Ideal.pow_le_self he)
  haveI : Finite (Rₚ ⧸ maximalIdeal Rₚ) :=
    Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔭 Rₚ).toEquiv
  -- the contraction of `𝔪^n` to `A` is `𝔭^n`
  have hcontr : ∀ (n : ℕ) (a : A), algebraMap A Rₚ a ∈ maximalIdeal Rₚ ^ n → a ∈ 𝔭 ^ n := by
    intro n a ha
    rw [← h𝔪, ← Ideal.map_pow, IsLocalization.mem_map_algebraMap_iff 𝔭.primeCompl] at ha
    obtain ⟨⟨x, s⟩, hx⟩ := ha
    rw [← map_mul] at hx
    have hx' := hinjA hx
    exact mem_pow_of_mul_mem_pow 𝔭 s.2 n (by rw [mul_comm, hx']; exact x.2)
  have hκ' : ((e : ℕ) : Rₚ) ∉ maximalIdeal Rₚ ^ (κ + 1) := by
    rw [← map_natCast (algebraMap A Rₚ)]
    exact fun h => hκ (hcontr _ _ h)
  -- the core: the trace of `Sₚ/𝔓ₚ^N` over `Rₚ/𝔪^{κ+1}` is nonzero
  letI := quotAlgebra (maximalIdeal Rₚ) 𝔓ₚ e κ Jₚ hpSₚ
  haveI := quotAlgebra_isScalarTower (maximalIdeal Rₚ) 𝔓ₚ e κ Jₚ hpSₚ
  obtain ⟨hfree1, y, hy⟩ := free_and_exists_trace_ne_zero (maximalIdeal Rₚ) 𝔓ₚ e κ Jₚ he h𝔪0
    h𝔓ₚ0 hpSₚ hJₚ' hκ'
  -- `B → Sₚ/𝔓ₚ^N` is surjective
  have hsurjB : ∀ z : Sₚ ⧸ 𝔓ₚ ^ N, ∃ b : B,
      Ideal.Quotient.mk (𝔓ₚ ^ N) (algebraMap B Sₚ b) = z := by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨b, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B 𝔭.primeCompl) z
    obtain ⟨s₀, hs₀, hs₀s⟩ := s.2
    have hs𝔓 : (s : B) ∉ 𝔓 := by
      rw [← hs₀s]
      intro h
      exact hs₀ (by rw [𝔓.over_def 𝔭]; exact h)
    have hcop : IsCoprime (𝔓 ^ N) (Ideal.span {(s : B)}) :=
      (Ideal.isCoprime_iff_sup_eq.mpr (sup_span_singleton_eq_top 𝔓 hs𝔓)).pow_left
    obtain ⟨w, hw, hw1⟩ := exists_mem_and_one_sub_mem hcop
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    refine ⟨b * c, ?_⟩
    rw [Ideal.Quotient.eq]
    have hspec := IsLocalization.mk'_spec Sₚ b s
    have hrel : algebraMap B Sₚ (b * c) - IsLocalization.mk' Sₚ b s =
        -(IsLocalization.mk' Sₚ b s * algebraMap B Sₚ (1 - c * s)) := by
      simp only [map_mul, map_sub, map_one]
      linear_combination (-(algebraMap B Sₚ c)) * hspec
    rw [hrel, Ideal.neg_mem_iff]
    refine Ideal.mul_mem_left _ _ ?_
    rw [h𝔓ₚ, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hw1
  obtain ⟨b, hb⟩ := hsurjB y
  -- `x ≡ b mod 𝔓^N`, `x ∈ J^{κ+1}`
  have hcopB : IsCoprime (𝔓 ^ N) (J ^ (κ + 1)) :=
    ((Ideal.isCoprime_iff_sup_eq.mpr hJ).pow_left).pow_right
  obtain ⟨w, hw, hw1⟩ := exists_mem_and_one_sub_mem hcopB
  set x := b * w with hx
  have hxQ : x ∈ J ^ (κ + 1) := Ideal.mul_mem_left _ _ hw
  have hxb : x - b ∈ 𝔓 ^ N := by
    have : x - b = -(b * (1 - w)) := by rw [hx]; ring
    rw [this, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_left _ _ hw1
  have hx1 : Ideal.Quotient.mk (𝔓ₚ ^ N) (algebraMap B Sₚ x) = y := by
    rw [← hb, Ideal.Quotient.eq, ← map_sub, h𝔓ₚ, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hxb
  have hx2 : Ideal.Quotient.mk (Jₚ ^ (κ + 1)) (algebraMap B Sₚ x) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, hJₚ, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hxQ
  -- the Chinese remainder decomposition of `Sₚ/𝔪^{κ+1}Sₚ`
  have hprod : (maximalIdeal Rₚ ^ (κ + 1)).map (algebraMap Rₚ Sₚ) = 𝔓ₚ ^ N * Jₚ ^ (κ + 1) := by
    rw [Ideal.map_pow, hpSₚ, mul_pow, ← pow_mul, hN]
  have hcopₚ : IsCoprime (𝔓ₚ ^ N) (Jₚ ^ (κ + 1)) :=
    ((Ideal.isCoprime_iff_sup_eq.mpr hJₚ').pow_left).pow_right
  letI : Algebra (Rₚ ⧸ maximalIdeal Rₚ ^ (κ + 1)) (Sₚ ⧸ Jₚ ^ (κ + 1)) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (by rw [← Ideal.map_le_iff_le_comap, hprod]; exact Ideal.mul_le_left)
  haveI : IsScalarTower Rₚ (Rₚ ⧸ maximalIdeal Rₚ ^ (κ + 1)) (Sₚ ⧸ Jₚ ^ (κ + 1)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Rₚ (Rₚ ⧸ maximalIdeal Rₚ ^ (κ + 1))
      (Sₚ ⧸ (maximalIdeal Rₚ ^ (κ + 1)).map (algebraMap Rₚ Sₚ)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let E : (Sₚ ⧸ (maximalIdeal Rₚ ^ (κ + 1)).map (algebraMap Rₚ Sₚ)) ≃ₐ[Rₚ ⧸
      maximalIdeal Rₚ ^ (κ + 1)] ((Sₚ ⧸ 𝔓ₚ ^ N) × Sₚ ⧸ Jₚ ^ (κ + 1)) :=
    { __ := (Ideal.quotEquivOfEq hprod).trans (Ideal.quotientMulEquivQuotientProd _ _ hcopₚ),
      commutes' := Quotient.ind fun _ ↦ rfl }
  -- finiteness and freeness of the factors
  have hfin : ∀ (I : Ideal Sₚ) [Algebra (Rₚ ⧸ maximalIdeal Rₚ ^ (κ + 1)) (Sₚ ⧸ I)]
      [IsScalarTower Rₚ (Rₚ ⧸ maximalIdeal Rₚ ^ (κ + 1)) (Sₚ ⧸ I)],
      Module.Finite (Rₚ ⧸ maximalIdeal Rₚ ^ (κ + 1)) (Sₚ ⧸ I) := by
    intro I _ _
    haveI : Module.Finite Rₚ (Sₚ ⧸ I) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ Rₚ I).toLinearMap
        Ideal.Quotient.mk_surjective
    exact Module.Finite.of_restrictScalars_finite Rₚ _ _
  haveI := hfin ((maximalIdeal Rₚ ^ (κ + 1)).map (algebraMap Rₚ Sₚ))
  haveI := hfin (𝔓ₚ ^ N)
  haveI := hfin (Jₚ ^ (κ + 1))
  haveI : Nontrivial (Rₚ ⧸ maximalIdeal Rₚ ^ (κ + 1)) := Ideal.Quotient.nontrivial_iff.mpr
    (fun h => Ideal.IsMaximal.ne_top (inferInstance : (maximalIdeal Rₚ).IsMaximal)
      (top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero κ))))
  haveI : IsLocalRing (Rₚ ⧸ maximalIdeal Rₚ ^ (κ + 1)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : Module.Projective (Rₚ ⧸ maximalIdeal Rₚ ^ (κ + 1)) (Sₚ ⧸ Jₚ ^ (κ + 1)) :=
    Module.Projective.of_split (E.symm.toLinearMap ∘ₗ LinearMap.inr _ _ _)
      (LinearMap.snd _ _ _ ∘ₗ E.toLinearMap) (LinearMap.ext fun z => by
        simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.snd_apply,
          AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply, LinearMap.id_apply])
  haveI : Module.Free (Rₚ ⧸ maximalIdeal Rₚ ^ (κ + 1)) (Sₚ ⧸ Jₚ ^ (κ + 1)) :=
    Module.free_of_flat_of_isLocalRing
  -- the trace of `x` modulo `𝔪^{κ+1}` is nonzero
  have hkey : Ideal.Quotient.mk (maximalIdeal Rₚ ^ (κ + 1))
      (Algebra.trace Rₚ Sₚ (algebraMap B Sₚ x)) ≠ 0 := by
    rw [← trace_quotient_mk_map, ← Algebra.trace_eq_of_algEquiv E, Algebra.trace_prod_apply]
    have hE : E (Ideal.Quotient.mk _ (algebraMap B Sₚ x)) = (y, 0) := by
      ext
      · rw [← hx1]
        exact Ideal.quotientMulEquivQuotientProd_fst _ _ hcopₚ _
      · rw [← hx2]
        exact Ideal.quotientMulEquivQuotientProd_snd _ _ hcopₚ _
    rw [hE, map_zero, add_zero]
    exact hy
  refine ⟨x, hxQ, fun hmem => hkey ?_⟩
  rw [Ideal.Quotient.eq_zero_iff_mem, ← Algebra.intTrace_eq_trace,
    ← Algebra.intTrace_eq_of_isLocalization A B 𝔭.primeCompl (Aₘ := Rₚ) (Bₘ := Sₚ) x, ← h𝔪,
    ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hmem

end Localized

section Main

variable {A B : Type*} [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
variable (𝔭 : Ideal A) [𝔭.IsMaximal] [Finite (A ⧸ 𝔭)] (𝔓 : Ideal B) [𝔓.IsMaximal] [𝔓.LiesOver 𝔭]

/-- **Serre's bound**: `𝔓^{e(κ+1)} ∤ 𝔇_{B/A}` for `e = e(𝔓/𝔭)` and `e ∉ 𝔭^{κ+1}`. -/
theorem not_pow_dvd_differentIdeal (h𝔭 : 𝔭 ≠ ⊥) (κ : ℕ)
    (hκ : ((𝔭.ramificationIdx' 𝔓 : ℕ) : A) ∉ 𝔭 ^ (κ + 1)) :
    ¬ 𝔓 ^ (𝔭.ramificationIdx' 𝔓 * (κ + 1)) ∣ differentIdeal A B := by
  classical
  -- the factorization `𝔭B = 𝔓^e·J`
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hpB0 : 𝔭.map (algebraMap A B) ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective hinj).not.mpr h𝔭
  have h𝔓 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 𝔓
  set e := 𝔭.ramificationIdx' 𝔓 with he_def
  obtain ⟨J, hJ, hpB⟩ := Ideal.eq_prime_pow_mul_coprime hpB0 𝔓
  rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hpB0 inferInstance h𝔓,
    ← he_def] at hpB
  have he : e ≠ 0 := by
    intro he0
    rw [he0, pow_zero, one_mul] at hpB
    have h1 : 𝔭.map (algebraMap A B) ≤ 𝔓 := Ideal.map_le_iff_le_comap.mpr (𝔓.over_def 𝔭).le
    rw [hpB] at h1
    rw [sup_eq_left.mpr h1] at hJ
    exact Ideal.IsMaximal.ne_top ‹𝔓.IsMaximal› hJ
  -- the localization at `𝔭`
  let Rₚ := Localization.AtPrime 𝔭
  let Sₚ := Localization (Algebra.algebraMapSubmonoid B 𝔭.primeCompl)
  letI : Algebra Rₚ Sₚ := localizationAlgebra 𝔭.primeCompl B
  haveI : IsScalarTower A Rₚ Sₚ := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  haveI : IsLocalization (Submonoid.map (algebraMap A B) (Ideal.primeCompl 𝔭)) Sₚ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid B 𝔭.primeCompl) Sₚ)
  have hM : Algebra.algebraMapSubmonoid B 𝔭.primeCompl ≤ B⁰ :=
    Submonoid.map_le_of_le_comap _ <| 𝔭.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  haveI : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  haveI : Module.IsTorsionFree Rₚ Sₚ := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot,
      RingHom.ker_eq_bot_iff_eq_zero]
    simp
  haveI : Module.Finite Rₚ Sₚ := .of_isLocalization A B 𝔭.primeCompl
  haveI : IsIntegrallyClosed Sₚ := isIntegrallyClosed_of_isLocalization _ _ hM
  haveI : IsDiscreteValuationRing Rₚ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A h𝔭 Rₚ
  haveI : Module.Free Rₚ Sₚ := Module.free_of_finite_type_torsion_free'
  haveI : IsDedekindDomain Sₚ := IsLocalization.isDedekindDomain B hM Sₚ
  obtain ⟨x, hxQ, hint⟩ := exists_mem_pow_intTrace_notMem 𝔭 𝔓 Rₚ Sₚ h𝔭 e κ J he hpB hJ hκ
  have hPQ : 𝔓 ^ (e * (κ + 1)) * J ^ (κ + 1) = (𝔭 ^ (κ + 1)).map (algebraMap A B) := by
    rw [Ideal.map_pow, hpB, mul_pow, ← pow_mul]
  exact not_dvd_differentIdeal_of_intTrace_not_mem A (𝔓 ^ (e * (κ + 1))) (J ^ (κ + 1)) hPQ x hxQ
    hint

end Main

end Iut.Serre
