/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.QuotientBasis

/-!
# The trace of `B/𝔓^{e(κ+1)}` over `A/𝔭^{κ+1}` is nonzero (the core of Serre's bound)

Let `A ⊆ B` be Dedekind domains with `B` finite over `A`, `𝔓` a maximal ideal of `B` over
the maximal ideal `𝔭` of `A`, with finite residue fields, `𝔭B = 𝔓^e·J` with `J` prime to
`𝔓`, and `κ` with `e ∉ 𝔭^{κ+1}`. Put `R = A/𝔭^{κ+1}`, `C = B/𝔓^{e(κ+1)}`. Then
`C` is a free `R`-module and the trace `Tr_{C/R}` is not identically zero
(`Iut.Serre.exists_trace_ne_zero`): by Hensel's lemma the (separable) residue extension
`l/k` lifts to a finite free `R`-algebra `R' = R[X]/(g) ⊆ C` with `R'/𝔭R' ≅ l`, over which
`C` is free of rank `e` (spanned by the powers of a uniformizer, by Nakayama, and free by
counting), so `Tr_{C/R}(y) = e·Tr_{R'/R}(y)` for `y ∈ R'`, and `Tr_{R'/R}` takes a value
prime to `𝔭` because the trace of the separable extension `l/k` is nonzero.

This is the wild half of IUT IV, Proposition 1.3 (Serre, *Local Fields*, III §6, Remark
after Proposition 13): `ord_𝔓(𝔇_{B/A}) ≤ e − 1 + ord_𝔓(e)`.
-/

namespace Iut.Serre

open Polynomial

attribute [local instance] Ideal.Quotient.field

variable {A B : Type*} [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B]
variable (𝔭 : Ideal A) [𝔭.IsMaximal] (𝔓 : Ideal B) [𝔓.IsMaximal] [𝔓.LiesOver 𝔭]
variable (e κ : ℕ) (J : Ideal B)

/-- `𝔭^{κ+1}B ⊆ 𝔓^{e(κ+1)}`. -/
lemma pow_le_comap (hpB : 𝔭.map (algebraMap A B) = 𝔓 ^ e * J) :
    𝔭 ^ (κ + 1) ≤ (𝔓 ^ (e * (κ + 1))).comap (algebraMap A B) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, hpB, mul_pow, ← pow_mul]
  exact Ideal.mul_le_right

/-- The `A/𝔭^{κ+1}`-algebra structure of `B/𝔓^{e(κ+1)}`. -/
noncomputable def quotAlgebra (hpB : 𝔭.map (algebraMap A B) = 𝔓 ^ e * J) :
    Algebra (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1))) :=
  Ideal.Quotient.algebraQuotientOfLEComap (pow_le_comap 𝔭 𝔓 e κ J hpB)

lemma quotAlgebra_isScalarTower (hpB : 𝔭.map (algebraMap A B) = 𝔓 ^ e * J) :
    letI := quotAlgebra 𝔭 𝔓 e κ J hpB
    IsScalarTower A (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1))) :=
  letI := quotAlgebra 𝔭 𝔓 e κ J hpB
  IsScalarTower.of_algebraMap_eq' rfl

/-- The residue field `B/𝔓` is finite over `A/𝔭`. -/
lemma finite_quotient_of_liesOver [Finite (A ⧸ 𝔭)] : Finite (B ⧸ 𝔓) := by
  haveI : Module.Finite A (B ⧸ 𝔓) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A 𝔓).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (A ⧸ 𝔭) (B ⧸ 𝔓) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ 𝔭) (B ⧸ 𝔓)
  exact Module.finite_of_finite (A ⧸ 𝔭)

/-- `𝔓^e ⊆ 𝔭B + 𝔓^{e(κ+1)}`, so `𝔓^e/𝔓^{e(κ+1)} ⊆ 𝔭·(B/𝔓^{e(κ+1)})`. -/
lemma mk_mem_map_of_mem_pow (hpB : 𝔭.map (algebraMap A B) = 𝔓 ^ e * J) (hJ : 𝔓 ⊔ J = ⊤)
    {b : B} (hb : b ∈ 𝔓 ^ e) :
    Ideal.Quotient.mk (𝔓 ^ (e * (κ + 1))) b ∈
      𝔭.map (algebraMap A (B ⧸ 𝔓 ^ (e * (κ + 1)))) := by
  have hcop : IsCoprime (𝔓 ^ (e * κ)) J :=
    (Ideal.isCoprime_iff_sup_eq.mpr hJ).pow_left
  have h1 : 𝔓 ^ e = 𝔓 ^ (e * (κ + 1)) ⊔ 𝔭.map (algebraMap A B) := by
    rw [hpB, show e * (κ + 1) = e + e * κ by ring, pow_add, ← Ideal.mul_sup, hcop.sup_eq,
      Ideal.mul_top]
  rw [h1] at hb
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hb
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hx, zero_add,
    IsScalarTower.algebraMap_eq A B (B ⧸ 𝔓 ^ (e * (κ + 1))), ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hy

section Hensel

variable [Finite (A ⧸ 𝔭)]
variable [Algebra (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1)))]
  [IsScalarTower A (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1)))]

/-- The reduction map `A/𝔭^{κ+1} → A/𝔭`. -/
noncomputable abbrev redA : A ⧸ 𝔭 ^ (κ + 1) →+* A ⧸ 𝔭 :=
  Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero κ))

/-- The reduction map `B/𝔓^{e(κ+1)} → B/𝔓`. -/
noncomputable abbrev redB (𝔓 : Ideal B) (e κ : ℕ) (he : e ≠ 0) :
    B ⧸ 𝔓 ^ (e * (κ + 1)) →+* B ⧸ 𝔓 :=
  Ideal.Quotient.factor (Ideal.pow_le_self (Nat.mul_ne_zero he (Nat.succ_ne_zero κ)))

lemma redB_comp_algebraMap (he : e ≠ 0) :
    (redB 𝔓 e κ he).comp (algebraMap (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1)))) =
      (algebraMap (A ⧸ 𝔭) (B ⧸ 𝔓)).comp (redA 𝔭 κ) := by
  refine RingHom.ext fun r => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  simp only [RingHom.comp_apply, Ideal.Quotient.factor_mk, Ideal.Quotient.algebraMap_mk_of_liesOver]
  have h : Ideal.Quotient.mk (𝔭 ^ (κ + 1)) a = algebraMap A (A ⧸ 𝔭 ^ (κ + 1)) a := rfl
  rw [h, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.factor_mk]

lemma redB_aeval (he : e ≠ 0) (x : B ⧸ 𝔓 ^ (e * (κ + 1))) (q : (A ⧸ 𝔭 ^ (κ + 1))[X]) :
    redB 𝔓 e κ he (aeval x q) = aeval (redB 𝔓 e κ he x) (q.map (redA 𝔭 κ)) := by
  rw [aeval_def, aeval_def, hom_eval₂, eval₂_map, redB_comp_algebraMap]

/-- **Hensel's lemma for the residue extension**: a monic polynomial `g` over `A/𝔭^{κ+1}`
lifting the minimal polynomial of a primitive element of `(B/𝔓)/(A/𝔭)`, with a root `α`
in `B/𝔓^{e(κ+1)}` such that `A/𝔭^{κ+1}[α] → B/𝔓` is surjective. -/
lemma exists_monic_root (he : e ≠ 0) (h𝔓 : 𝔓 ≠ ⊥) :
    ∃ (g : (A ⧸ 𝔭 ^ (κ + 1))[X]) (α : B ⧸ 𝔓 ^ (e * (κ + 1))), g.Monic ∧
      g.natDegree = Module.finrank (A ⧸ 𝔭) (B ⧸ 𝔓) ∧ aeval α g = 0 ∧
      ∀ y : B ⧸ 𝔓, ∃ q : (A ⧸ 𝔭 ^ (κ + 1))[X], redB 𝔓 e κ he (aeval α q) = y := by
  classical
  haveI : Finite (B ⧸ 𝔓) := finite_quotient_of_liesOver 𝔭 𝔓
  haveI : Module.Finite (A ⧸ 𝔭) (B ⧸ 𝔓) := Module.Finite.of_finite
  haveI : Algebra.IsSeparable (A ⧸ 𝔭) (B ⧸ 𝔓) := inferInstance
  obtain ⟨a₁, ha₁⟩ := Field.exists_primitive_element (A ⧸ 𝔭) (B ⧸ 𝔓)
  have hint : IsIntegral (A ⧸ 𝔭) a₁ := IsIntegral.of_finite _ _
  set g₀ := minpoly (A ⧸ 𝔭) a₁ with hg₀
  have hg₀m : g₀.Monic := minpoly.monic hint
  have hg₀s : g₀.Separable := Algebra.IsSeparable.isSeparable (A ⧸ 𝔭) a₁
  have hg₀deg : g₀.natDegree = Module.finrank (A ⧸ 𝔭) (B ⧸ 𝔓) := by
    rw [← IntermediateField.adjoin.finrank hint, ha₁, IntermediateField.finrank_top']
  have hθ : Function.Surjective (redA 𝔭 κ) := Ideal.Quotient.factor_surjective _
  obtain ⟨g, hg, hgdeg, hgm⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts _).mpr (map_surjective _ hθ g₀)) hg₀m
  -- the ideal `𝔓/𝔓^{e(κ+1)}` is nilpotent, so `B/𝔓^{e(κ+1)}` is Henselian at it
  set I : Ideal (B ⧸ 𝔓 ^ (e * (κ + 1))) := 𝔓.map (Ideal.Quotient.mk (𝔓 ^ (e * (κ + 1))))
    with hI
  have hIN : I ^ (e * (κ + 1)) = ⊥ := by
    rw [hI, ← Ideal.map_pow, Ideal.map_quotient_self]
  haveI := isAdicComplete_of_pow_eq_bot I (e * (κ + 1)) hIN
  have hmemI : ∀ x : B ⧸ 𝔓 ^ (e * (κ + 1)), x ∈ I ↔ redB 𝔓 e κ he x = 0 := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hI, Ideal.mem_quotient_iff_mem_sup, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem, sup_eq_left.mpr (Ideal.pow_le_self (Nat.mul_ne_zero he
        (Nat.succ_ne_zero κ)))]
  obtain ⟨α₀, hα₀⟩ := Ideal.Quotient.mk_surjective a₁
  set a₀ : B ⧸ 𝔓 ^ (e * (κ + 1)) := Ideal.Quotient.mk (𝔓 ^ (e * (κ + 1))) α₀ with ha₀
  have hred₀ : redB 𝔓 e κ he a₀ = a₁ := by rw [ha₀, Ideal.Quotient.factor_mk, hα₀]
  have hGmonic : (g.map (algebraMap (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1))))).Monic := hgm.map _
  have h1 : (g.map (algebraMap (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1))))).eval a₀ ∈ I := by
    rw [hmemI, eval_map, ← aeval_def, redB_aeval, hred₀, hg, hg₀, minpoly.aeval]
  have h2 : IsUnit (Ideal.Quotient.mk I
      ((derivative (g.map (algebraMap (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1)))))).eval a₀)) := by
    rw [derivative_map, eval_map, ← aeval_def]
    set d := aeval a₀ (derivative g) with hd
    have hne : redB 𝔓 e κ he d ≠ 0 := by
      rw [hd, redB_aeval, hred₀, ← derivative_map, hg, hg₀]
      exact hg₀s.aeval_derivative_ne_zero (minpoly.aeval _ _)
    let E := DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self (R := B) (I := 𝔓)
      (Nat.mul_ne_zero he (Nat.succ_ne_zero κ)))
    obtain ⟨d', hd'⟩ := Ideal.Quotient.mk_surjective d
    have hE : E (Ideal.Quotient.mk I d) = redB 𝔓 e κ he d := by
      rw [← hd', Ideal.Quotient.factor_mk]
      exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk d' _
    have hunit : IsUnit (E (Ideal.Quotient.mk I d)) := by
      rw [hE]
      exact isUnit_iff_ne_zero.mpr hne
    have := hunit.map E.symm.toRingHom
    simpa using this
  obtain ⟨α, hα, hαa₀⟩ := HenselianRing.is_henselian (I := I) _ hGmonic a₀ h1 h2
  have hαg : aeval α g = 0 := by
    rw [aeval_def, ← eval_map]
    exact hα
  have hredα : redB 𝔓 e κ he α = a₁ := by
    rw [← hred₀, ← sub_eq_zero, ← map_sub]
    exact (hmemI _).mp hαa₀
  refine ⟨g, α, hgm, hgdeg.trans hg₀deg, hαg, fun y => ?_⟩
  have hy : y ∈ Algebra.adjoin (A ⧸ 𝔭) ({a₁} : Set (B ⧸ 𝔓)) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral hint, ha₁]
    exact trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨q', hq'⟩ := hy
  obtain ⟨q, rfl⟩ := map_surjective _ hθ q'
  exact ⟨q, by rw [redB_aeval, hredα]; exact hq'⟩

end Hensel

section Span

/-- `π^i ∉ 𝔓^{i+1}` for a uniformizer `π ∈ 𝔓 ∖ 𝔓²`. -/
lemma pow_notMem_pow_succ (h𝔓 : 𝔓 ≠ ⊥) {π : B} (hπ : π ∈ 𝔓) (hπ2 : π ∉ 𝔓 ^ 2) (i : ℕ) :
    π ^ i ∉ 𝔓 ^ (i + 1) := by
  intro h
  have hprime : Prime 𝔓 := Ideal.prime_of_isPrime h𝔓 inferInstance
  obtain ⟨𝔞, h𝔞⟩ : 𝔓 ∣ Ideal.span {π} := Ideal.dvd_span_singleton.mpr hπ
  have h1 : 𝔓 ^ (i + 1) ∣ Ideal.span {π} ^ i := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_span_singleton.mpr h
  rw [h𝔞, mul_pow, pow_succ] at h1
  have h2 : 𝔓 ∣ 𝔞 ^ i := (mul_dvd_mul_iff_left (pow_ne_zero i h𝔓)).mp h1
  have h3 : 𝔓 ∣ 𝔞 := hprime.dvd_of_dvd_pow h2
  apply hπ2
  rw [← Ideal.dvd_span_singleton, h𝔞, pow_two]
  exact mul_dvd_mul_left 𝔓 h3

variable [Algebra (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1)))]
  [IsScalarTower A (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1)))]

/-- **`B/𝔓^{e(κ+1)}` is spanned over `R' = R[X]/(g)` by `1, π, …, π^{e−1}`**, for `π` a
uniformizer at `𝔓` and `R'[α] → B/𝔓` surjective: the images of `R'` and the powers of
`π` span `B/𝔓^e`, and `𝔓^e/𝔓^{e(κ+1)} ⊆ 𝔭·(B/𝔓^{e(κ+1)})` is killed by Nakayama. -/
lemma span_pow_eq_top (he : e ≠ 0) (h𝔓 : 𝔓 ≠ ⊥) (hpB : 𝔭.map (algebraMap A B) = 𝔓 ^ e * J)
    (hJ : 𝔓 ⊔ J = ⊤) {g : (A ⧸ 𝔭 ^ (κ + 1))[X]} {α : B ⧸ 𝔓 ^ (e * (κ + 1))}
    [Algebra (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1)))]
    (halg : ∀ q : (A ⧸ 𝔭 ^ (κ + 1))[X],
      algebraMap (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1))) (AdjoinRoot.mk g q) = aeval α q)
    (hsurj : ∀ y : B ⧸ 𝔓, ∃ q : (A ⧸ 𝔭 ^ (κ + 1))[X], redB 𝔓 e κ he (aeval α q) = y)
    {π : B} (hπ : π ∈ 𝔓) (hπ2 : π ∉ 𝔓 ^ 2) :
    Submodule.span (AdjoinRoot g) (Set.range fun i : Fin e =>
      Ideal.Quotient.mk (𝔓 ^ (e * (κ + 1))) (π ^ (i : ℕ))) = ⊤ := by
  classical
  set M := Submodule.span (AdjoinRoot g) (Set.range fun i : Fin e =>
    Ideal.Quotient.mk (𝔓 ^ (e * (κ + 1))) (π ^ (i : ℕ))) with hM
  -- the algebra map `A → R' → B/𝔓^{e(κ+1)}` is the algebra map `A → B/𝔓^{e(κ+1)}`
  have hcomp : (algebraMap (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1)))).comp
      (algebraMap A (AdjoinRoot g)) = algebraMap A (B ⧸ 𝔓 ^ (e * (κ + 1))) := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A (A ⧸ 𝔭 ^ (κ + 1)) (AdjoinRoot g),
      AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, halg, aeval_C, ← IsScalarTower.algebraMap_apply]
  set J₁ : Ideal (AdjoinRoot g) := 𝔭.map (algebraMap A (AdjoinRoot g)) with hJ₁def
  have hJ₁ : J₁ • (⊤ : Submodule (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1)))) =
      (𝔭.map (algebraMap A (B ⧸ 𝔓 ^ (e * (κ + 1))))).restrictScalars (AdjoinRoot g) := by
    rw [Ideal.smul_top_eq_map, hJ₁def, Ideal.map_map, hcomp]
  have hbase : ∀ b ∈ 𝔓 ^ e, Ideal.Quotient.mk (𝔓 ^ (e * (κ + 1))) b ∈ M ⊔ J₁ • ⊤ := by
    intro b hb
    refine Submodule.mem_sup_right ?_
    rw [hJ₁]
    exact mk_mem_map_of_mem_pow 𝔭 𝔓 e κ J hpB hJ hb
  have hstep : ∀ j, j ≤ e → ∀ b ∈ 𝔓 ^ (e - j),
      Ideal.Quotient.mk (𝔓 ^ (e * (κ + 1))) b ∈ M ⊔ J₁ • ⊤ := by
    intro j
    induction j with
    | zero =>
      intro _ b hb
      exact hbase b (by simpa using hb)
    | succ j ih =>
      intro hj b hb
      have hi : e - (j + 1) + 1 = e - j := by omega
      obtain ⟨d, e', he', hde⟩ := Ideal.exists_mul_add_mem_pow_succ h𝔓 (π ^ (e - (j + 1))) b
        (Ideal.pow_mem_pow hπ _) (pow_notMem_pow_succ 𝔓 h𝔓 hπ hπ2 _) hb
      obtain ⟨q, hq⟩ := hsurj (Ideal.Quotient.mk 𝔓 d)
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (aeval α q)
      have hdz : d - z ∈ 𝔓 := by
        have h' : Ideal.Quotient.mk 𝔓 d = Ideal.Quotient.mk 𝔓 z := by
          rw [← hq, ← hz, Ideal.Quotient.factor_mk]
        exact Ideal.Quotient.eq.mp h'
      have hrest : π ^ (e - (j + 1)) * (d - z) + e' ∈ 𝔓 ^ (e - j) := by
        rw [← hi]
        refine Ideal.add_mem _ ?_ he'
        rw [pow_succ]
        exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ _) hdz
      have hb' : b = π ^ (e - (j + 1)) * z + (π ^ (e - (j + 1)) * (d - z) + e') := by
        rw [← hde]
        ring
      rw [hb', map_add]
      refine Submodule.add_mem _ ?_ (ih (by omega) _ hrest)
      refine Submodule.mem_sup_left ?_
      have hsm : Ideal.Quotient.mk (𝔓 ^ (e * (κ + 1))) (π ^ (e - (j + 1)) * z) =
          AdjoinRoot.mk g q • Ideal.Quotient.mk (𝔓 ^ (e * (κ + 1))) (π ^ (e - (j + 1))) := by
        rw [Algebra.smul_def, halg, ← hz, ← map_mul]
        exact congrArg _ (mul_comm _ _)
      rw [hsm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨e - (j + 1), by omega⟩, rfl⟩)
  have hall : (⊤ : Submodule (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1)))) ≤ M ⊔ J₁ • ⊤ := by
    intro x _
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hstep e le_rfl b (by simp)
  -- Nakayama: `J₁^{κ+1} = 0`
  have hnak : ∀ n : ℕ, (⊤ : Submodule (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1)))) ≤ M ⊔ J₁ ^ n • ⊤ := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact le_sup_right
    | succ n ih =>
      calc (⊤ : Submodule (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1)))) ≤ M ⊔ J₁ ^ n • ⊤ := ih
        _ ≤ M ⊔ J₁ ^ n • (M ⊔ J₁ • ⊤) := sup_le_sup_left (Submodule.smul_mono le_rfl hall) _
        _ ≤ M ⊔ J₁ ^ (n + 1) • ⊤ := by
          have hpow : J₁ ^ (n + 1) • (⊤ : Submodule (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1)))) =
              J₁ ^ n • J₁ • ⊤ := by
            rw [pow_succ J₁ n, Submodule.mul_smul]
          rw [Submodule.smul_sup, hpow]
          exact sup_le le_sup_left
            (sup_le (Submodule.smul_le_right.trans le_sup_left) le_sup_right)
  have hJ₁pow : J₁ ^ (κ + 1) = ⊥ := by
    rw [hJ₁def, ← Ideal.map_pow, IsScalarTower.algebraMap_eq A (A ⧸ 𝔭 ^ (κ + 1)) (AdjoinRoot g),
      ← Ideal.map_map, Ideal.Quotient.algebraMap_eq, Ideal.map_quotient_self, Ideal.map_bot]
  have := hnak (κ + 1)
  rwa [hJ₁pow, Submodule.bot_smul, sup_bot_eq, top_le_iff] at this

end Span

section Main

variable [Finite (A ⧸ 𝔭)]
variable [Algebra (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1)))]
  [IsScalarTower A (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1)))]

/-- **The core of Serre's bound**: `B/𝔓^{e(κ+1)}` is a free `A/𝔭^{κ+1}`-module whose trace
is not identically zero, provided `e ∉ 𝔭^{κ+1}`. -/
theorem free_and_exists_trace_ne_zero (he : e ≠ 0) (h𝔭 : 𝔭 ≠ ⊥) (h𝔓 : 𝔓 ≠ ⊥)
    (hpB : 𝔭.map (algebraMap A B) = 𝔓 ^ e * J) (hJ : 𝔓 ⊔ J = ⊤)
    (hκ : ((e : ℕ) : A) ∉ 𝔭 ^ (κ + 1)) :
    Module.Free (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1))) ∧
      ∃ y : B ⧸ 𝔓 ^ (e * (κ + 1)),
        Algebra.trace (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1))) y ≠ 0 := by
  classical
  obtain ⟨g, α, hgm, hgdeg, hαg, hsurj⟩ := exists_monic_root 𝔭 𝔓 e κ he h𝔓
  haveI : Finite (B ⧸ 𝔓) := finite_quotient_of_liesOver 𝔭 𝔓
  haveI : Module.Finite (A ⧸ 𝔭) (B ⧸ 𝔓) := Module.Finite.of_finite
  -- the algebra `R' = R[X]/(g) → B/𝔓^{e(κ+1)}`, `X ↦ α`
  have hev : g.eval₂ ((Algebra.ofId (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1))) :
      (A ⧸ 𝔭 ^ (κ + 1)) →ₐ[A ⧸ 𝔭 ^ (κ + 1)] (B ⧸ 𝔓 ^ (e * (κ + 1)))) :
      (A ⧸ 𝔭 ^ (κ + 1)) →+* (B ⧸ 𝔓 ^ (e * (κ + 1)))) α = 0 := hαg
  let φ : AdjoinRoot g →ₐ[A ⧸ 𝔭 ^ (κ + 1)] (B ⧸ 𝔓 ^ (e * (κ + 1))) :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId _ _) α hev
  letI : Algebra (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1))) := φ.toRingHom.toAlgebra
  have halg : ∀ q : (A ⧸ 𝔭 ^ (κ + 1))[X],
      algebraMap (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1))) (AdjoinRoot.mk g q) = aeval α q :=
    fun q => AdjoinRoot.liftAlgHom_mk _ _ _ _ q
  haveI : IsScalarTower (A ⧸ 𝔭 ^ (κ + 1)) (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1))) :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  haveI : Nontrivial (AdjoinRoot g) := ((redB 𝔓 e κ he).comp φ.toRingHom).domain_nontrivial
  let pb := AdjoinRoot.powerBasis' hgm
  haveI : Module.Free (A ⧸ 𝔭 ^ (κ + 1)) (AdjoinRoot g) := Module.Free.of_basis pb.basis
  haveI : Module.Finite (A ⧸ 𝔭 ^ (κ + 1)) (AdjoinRoot g) := Module.Finite.of_basis pb.basis
  -- a uniformizer
  obtain ⟨π, hπ, hπ2⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow h𝔓 1)
  rw [pow_one] at hπ
  have hspan := span_pow_eq_top 𝔭 𝔓 e κ J he h𝔓 hpB hJ halg hsurj hπ hπ2
  -- cardinalities
  have hq0 : Nat.card (A ⧸ 𝔭) ≠ 0 := Nat.card_pos.ne'
  have hcardR : Nat.card (A ⧸ 𝔭 ^ (κ + 1)) = Nat.card (A ⧸ 𝔭) ^ (κ + 1) := by
    rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime h𝔭]
  have hcardC : Nat.card (B ⧸ 𝔓 ^ (e * (κ + 1))) = Nat.card (B ⧸ 𝔓) ^ (e * (κ + 1)) := by
    rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime h𝔓]
  have hcardl : Nat.card (B ⧸ 𝔓) = Nat.card (A ⧸ 𝔭) ^ Module.finrank (A ⧸ 𝔭) (B ⧸ 𝔓) :=
    Module.natCard_eq_pow_finrank
  haveI : Finite (A ⧸ 𝔭 ^ (κ + 1)) := Nat.finite_of_card_ne_zero (by rw [hcardR]; positivity)
  have hcardR' : Nat.card (AdjoinRoot g) = Nat.card (A ⧸ 𝔭 ^ (κ + 1)) ^ g.natDegree := by
    rw [Nat.card_congr pb.basis.equivFun.toEquiv, Nat.card_fun, Nat.card_fin,
      AdjoinRoot.powerBasis'_dim]
  haveI : Finite (AdjoinRoot g) := Nat.finite_of_card_ne_zero (by
    rw [hcardR', hcardR]; positivity)
  haveI : Finite (B ⧸ 𝔓 ^ (e * (κ + 1))) := Nat.finite_of_card_ne_zero (by
    rw [hcardC, hcardl]; positivity)
  -- the powers of `π` form a basis over `R'`
  let f : (Fin e →₀ AdjoinRoot g) →ₗ[AdjoinRoot g] (B ⧸ 𝔓 ^ (e * (κ + 1))) :=
    Finsupp.linearCombination (AdjoinRoot g) fun i : Fin e =>
      Ideal.Quotient.mk (𝔓 ^ (e * (κ + 1))) (π ^ (i : ℕ))
  have hfsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hspan]
  haveI : Finite (Fin e →₀ AdjoinRoot g) := Finite.of_equiv _ Finsupp.equivFunOnFinite.symm
  have hcard_le : Nat.card (Fin e →₀ AdjoinRoot g) ≤ Nat.card (B ⧸ 𝔓 ^ (e * (κ + 1))) := by
    rw [Nat.card_congr (Finsupp.equivFunOnFinite), Nat.card_fun, Nat.card_fin, hcardR', hcardR,
      hcardC, hcardl, ← hgdeg, ← pow_mul, ← pow_mul, ← pow_mul]
    exact le_of_eq (by ring_nf)
  have hfbij : Function.Bijective f := hfsurj.bijective_of_nat_card_le hcard_le
  let fe := (LinearEquiv.ofBijective f hfbij).symm.trans
    (Finsupp.linearEquivFunOnFinite (AdjoinRoot g) (AdjoinRoot g) (Fin e))
  let be : Module.Basis (Fin e) (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1))) :=
    Module.Basis.ofEquivFun fe
  haveI : Module.Free (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1))) := Module.Free.of_basis be
  haveI : Module.Finite (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1))) := Module.Finite.of_basis be
  have hrank : Module.finrank (AdjoinRoot g) (B ⧸ 𝔓 ^ (e * (κ + 1))) = e := by
    rw [Module.finrank_eq_card_basis be, Fintype.card_fin]
  haveI hfreeC : Module.Free (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1))) :=
    Module.Free.of_basis (pb.basis.smulTower be)
  haveI : Module.Finite (A ⧸ 𝔭 ^ (κ + 1)) (B ⧸ 𝔓 ^ (e * (κ + 1))) :=
    Module.Finite.of_basis (pb.basis.smulTower be)
  refine ⟨hfreeC, ?_⟩
  -- the trace of `R'/R` takes a value prime to `𝔭`: `R'/𝔭R' ≅ B/𝔓`
  set pR : Ideal (A ⧸ 𝔭 ^ (κ + 1)) := 𝔭.map (Ideal.Quotient.mk (𝔭 ^ (κ + 1))) with hpR
  set pR' : Ideal (AdjoinRoot g) := pR.map (algebraMap (A ⧸ 𝔭 ^ (κ + 1)) (AdjoinRoot g))
    with hpR'
  let E₁ : (A ⧸ 𝔭 ^ (κ + 1)) ⧸ pR ≃+* A ⧸ 𝔭 :=
    DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self (Nat.succ_ne_zero κ))
  let χ₀ : AdjoinRoot g →+* B ⧸ 𝔓 := (redB 𝔓 e κ he).comp φ.toRingHom
  have hχ₀ : ∀ r : A ⧸ 𝔭 ^ (κ + 1), χ₀ (algebraMap _ (AdjoinRoot g) r) =
      algebraMap (A ⧸ 𝔭) (B ⧸ 𝔓) (redA 𝔭 κ r) := by
    intro r
    have := congrArg (fun h => h r) (redB_comp_algebraMap 𝔭 𝔓 e κ he)
    simp only [RingHom.comp_apply] at this
    rw [← this]
    change redB 𝔓 e κ he (φ (algebraMap _ (AdjoinRoot g) r)) = _
    rw [φ.commutes]
  have hker : ∀ x ∈ pR', χ₀ x = 0 := by
    intro x hx
    rw [← RingHom.mem_ker]
    refine Ideal.map_le_iff_le_comap.mpr ?_ hx
    rw [hpR]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, hχ₀, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  let χ : (AdjoinRoot g ⧸ pR') →+* B ⧸ 𝔓 := Ideal.Quotient.lift pR' χ₀ hker
  have hχsurj : Function.Surjective χ := by
    intro y
    obtain ⟨q, hq⟩ := hsurj y
    refine ⟨Ideal.Quotient.mk pR' (AdjoinRoot.mk g q), ?_⟩
    rw [Ideal.Quotient.lift_mk]
    change redB 𝔓 e κ he (φ (AdjoinRoot.mk g q)) = y
    have hφq : φ (AdjoinRoot.mk g q) = aeval α q := halg q
    rw [hφq]
    exact hq
  haveI : Finite (AdjoinRoot g ⧸ pR') := Quotient.finite _
  have hcardQ : Nat.card (AdjoinRoot g ⧸ pR') ≤ Nat.card (B ⧸ 𝔓) := by
    rw [Nat.card_congr (basisQuotientMap pb.basis pR).equivFun.toEquiv, Nat.card_fun,
      Nat.card_fin, AdjoinRoot.powerBasis'_dim, Nat.card_congr E₁.toEquiv, hcardl, hgdeg]
  have hχbij : Function.Bijective χ := hχsurj.bijective_of_nat_card_le hcardQ
  let E₂ : (AdjoinRoot g ⧸ pR') ≃+* B ⧸ 𝔓 := RingEquiv.ofBijective χ hχbij
  have hcompat : (algebraMap (A ⧸ 𝔭) (B ⧸ 𝔓)).comp (E₁ : (A ⧸ 𝔭 ^ (κ + 1)) ⧸ pR →+* A ⧸ 𝔭) =
      (E₂ : (AdjoinRoot g ⧸ pR') →+* B ⧸ 𝔓).comp
        (algebraMap ((A ⧸ 𝔭 ^ (κ + 1)) ⧸ pR) (AdjoinRoot g ⧸ pR')) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
    have h1 : E₁ (Ideal.Quotient.mk pR (Ideal.Quotient.mk (𝔭 ^ (κ + 1)) a)) =
        Ideal.Quotient.mk 𝔭 a := DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk a _
    have h2 : E₂ (Ideal.Quotient.mk pR' (algebraMap _ (AdjoinRoot g)
        (Ideal.Quotient.mk (𝔭 ^ (κ + 1)) a))) =
        χ₀ (algebraMap _ (AdjoinRoot g) (Ideal.Quotient.mk (𝔭 ^ (κ + 1)) a)) :=
      Ideal.Quotient.lift_mk pR' χ₀ hker
    rw [h1, h2, hχ₀, Ideal.Quotient.factor_mk]
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : B ⧸ 𝔓, Algebra.trace (A ⧸ 𝔭) (B ⧸ 𝔓) z₁ ≠ 0 := by
    by_contra h
    exact Algebra.trace_ne_zero (A ⧸ 𝔭) (B ⧸ 𝔓)
      (LinearMap.ext fun z => not_not.mp (not_exists.mp h z))
  obtain ⟨y₀, hy₀⟩ := Ideal.Quotient.mk_surjective (E₂.symm z₁)
  have htr : Ideal.Quotient.mk pR (Algebra.trace (A ⧸ 𝔭 ^ (κ + 1)) (AdjoinRoot g) y₀) ≠ 0 := by
    rw [← trace_quotient_mk_map, hy₀, Algebra.trace_eq_of_equiv_equiv E₁ E₂ hcompat,
      RingEquiv.apply_symm_apply]
    exact (map_ne_zero_iff _ E₁.symm.injective).mpr hz₁
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective
    (Algebra.trace (A ⧸ 𝔭 ^ (κ + 1)) (AdjoinRoot g) y₀)
  have htp : t ∉ 𝔭 := by
    intro htp
    apply htr
    rw [← ht, Ideal.Quotient.eq_zero_iff_mem, hpR, Ideal.mem_quotient_iff_mem_sup]
    exact Ideal.mem_sup_left htp
  refine ⟨algebraMap (AdjoinRoot g) _ y₀, ?_⟩
  rw [← Algebra.trace_trace (S := AdjoinRoot g), Algebra.trace_algebraMap, hrank, map_nsmul,
    ← ht, ← map_nsmul, nsmul_eq_mul, Ne, Ideal.Quotient.eq_zero_iff_mem]
  intro hmem
  exact htp (Ideal.mem_prime_of_mul_mem_pow h𝔭 hκ hmem)

end Main

end Iut.Serre
