/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.AndreLocal
import Iut.Cor312.ThetaData.BadPlaceNorm
import Iut.Cor312.ThetaData.Basic

/-!
# Theorem B for the Tate curves of the Θ-data

Theorem B of lana-agents/tempered-fundamental-groups
(`TemperedFundamentalGroups.TateOrbicurve.nondegenerate_of_normalForm`) says: for a Tate curve
in normal form `y² + xy = x³ + a₄x + a₆` over a complete discrete valuation ring of mixed
characteristic `(0, p)` with perfect residue field, with `ϖ^m ∣ a₄`, `a₆ = ϖ^m ε` (`ε` a unit,
`m ≥ 1`), the tempered fundamental group of the orbifold `[Y / A]`, `Y = E ∖ (E[ℓ] + M)`
(`ℓ ≥ 1`, `M` finite), has an open normal subgroup with infinite quotient.

This module supplies the normal form for every Tate curve `E_q` of lana-agents/tate-curves-theta
over a complete ultrametric field whose unit ball is a discrete valuation ring
(`Iut.TateParameter.exists_normalForm`: `m = v(q)`, `a₄(q) = q · (a₄/q)` with `‖a₄‖ ≤ ‖q‖`, and
`a₆(q) = q · unit` from `‖a₆ + q‖ ≤ ‖q‖²`), and deduces Theorem B

* for the Tate curve `E_q` over the completion `F_w` of a number field at a finite place
  (`Iut.tateOrbicurve_nondegenerate`), and
* for the Tate curves of initial Θ-data: at every bad place `w` of the torsion field `K`, the
  Tate curve `E_{q_w}` of the Θ-data's Tate uniformization `D.tate.S w hw`
  (`Iut.InitialThetaData.tate_nondegenerate`).

**Which group.** The group is the tempered fundamental group
`canonicalTemperedPi1` of the *geometric* presentation `Orbicurve.affineOrbifold` of the model
orbicurve `(E_q, ℓ, M, ±)` (`[(E_q ∖ (E_q[ℓ] + M)) / A]` at the generic point,
`TemperedFundamentalGroups.Orbicurve.orbicurveOrbifold`), over the canonical valuation of `F_w`.
It is **not** literally `LocalThetaData.PivBad`: `Π_v` at a bad place is the tempered group of
the local model `X̲_v` (whose elliptic curve is `E ×_F K_w`, isomorphic to `E_{q_w}` by the change
of variables `(D.tate.S w hw).C` but not equal to it) in its Galois presentation
`Genuine.orbifold` (the characteristic-`0` branch of `Orbicurve.temperedPresentation`). Relating
the two would need (i) invariance of the tempered group under a change of Weierstrass model and
(ii) a comparison of the geometric and the Galois presentation of the same orbicurve; neither is
formalized here. No Θ-data definition is changed.
-/

namespace Iut

universe u

open NumberField IsDedekindDomain TateCurvesTheta TemperedFundamentalGroups IsLocalRing

section NormalForm

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {O : ValuationSubring K} (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)

omit [IsUltrametricDist K] [CompleteSpace K] in
include hO in
/-- A unit of the unit ball has norm `1`. -/
lemma norm_coe_unit_eq_one (u : Oˣ) : ‖((u : O) : K)‖ = 1 := by
  have h1 : ‖((u : O) : K)‖ ≤ 1 := (hO _).1 (u : O).2
  have h2 : ‖(((u⁻¹ : Oˣ) : O) : K)‖ ≤ 1 := (hO _).1 ((u⁻¹ : Oˣ) : O).2
  have hmul : ‖((u : O) : K)‖ * ‖(((u⁻¹ : Oˣ) : O) : K)‖ = 1 := by
    have h : ((u : O) : K) * (((u⁻¹ : Oˣ) : O) : K) = 1 := congrArg Subtype.val u.mul_inv
    rw [← norm_mul, h, norm_one]
  nlinarith [norm_nonneg ((u : O) : K), norm_nonneg (((u⁻¹ : Oˣ) : O) : K)]

include hO in
/-- **The Tate curve is in normal form** (`m = v(q)`): for a uniformizer `ϖ` of the unit ball `O`
(a discrete valuation ring), `a₄(q) = ϖ^m u₄` and `a₆(q) = ϖ^m ε` with `u₄ ∈ O`, `ε ∈ O^×` and
`m ≥ 1`. -/
theorem TateParameter.exists_normalForm [IsDiscreteValuationRing O] (t : TateParameter K)
    (h12 : (12 : K) ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ u₄ : O, t.a₄ = ((ϖ ^ m * u₄ : O) : K) ∧
      ∃ ε : Oˣ, t.a₆ = ((ϖ ^ m * ε : O) : K) := by
  set q : K := (t.q : K) with hqdef
  have hq0 : q ≠ 0 := t.q.ne_zero
  have hqpos : 0 < ‖q‖ := norm_pos_iff.2 hq0
  have hq1 : ‖q‖ < 1 := t.norm_lt_one
  let qO : O := ⟨q, (hO q).2 hq1.le⟩
  have hqO0 : qO ≠ 0 := fun h => hq0 (congrArg Subtype.val h)
  obtain ⟨m, u, hqu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hqO0 hϖ
  have hqK : q = ((u : O) : K) * ((ϖ : K)) ^ m := by
    have := congrArg Subtype.val hqu
    simpa using this
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [hqK, pow_zero, mul_one, norm_coe_unit_eq_one hO] at hq1
      exact absurd hq1 (lt_irrefl _)
    · exact hm
  -- `a₄ = q · b` with `b ∈ O`
  have hb : ‖t.a₄ / q‖ ≤ 1 := by
    rw [norm_div, div_le_one hqpos]
    exact t.norm_a₄_le
  let b : O := ⟨t.a₄ / q, (hO _).2 hb⟩
  -- `‖a₆‖ = ‖q‖`
  have ha₆q : ‖t.a₆ + q‖ < ‖q‖ :=
    (t.norm_a₆_add_q_le h12).trans_lt (by nlinarith)
  have ha₆ : ‖t.a₆‖ = ‖q‖ := by
    apply le_antisymm
    · calc ‖t.a₆‖ = ‖(t.a₆ + q) + (-q)‖ := by ring_nf
        _ ≤ max ‖t.a₆ + q‖ ‖-q‖ := IsUltrametricDist.norm_add_le_max _ _
        _ = ‖q‖ := by rw [norm_neg]; exact max_eq_right ha₆q.le
    · have : ‖q‖ ≤ max ‖t.a₆ + q‖ ‖-t.a₆‖ := by
        calc ‖q‖ = ‖(t.a₆ + q) + (-t.a₆)‖ := by ring_nf
          _ ≤ _ := IsUltrametricDist.norm_add_le_max _ _
      rw [norm_neg] at this
      rcases le_max_iff.1 this with h | h
      · exact absurd h (not_le.2 ha₆q)
      · exact h
  have hc : ‖t.a₆ / q‖ = 1 := by rw [norm_div, ha₆, div_self hqpos.ne']
  have hc' : ‖(t.a₆ / q)⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
  have hc0 : t.a₆ / q ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  let c : Oˣ := Units.mkOfMulEqOne (⟨t.a₆ / q, (hO _).2 hc.le⟩ : O)
    ⟨(t.a₆ / q)⁻¹, (hO _).2 hc'.le⟩ (Subtype.ext (mul_inv_cancel₀ hc0))
  refine ⟨m, hm, u * b, ?_, u * c, ?_⟩
  · change t.a₄ = (ϖ : K) ^ m * (((u : O) : K) * (t.a₄ / q))
    rw [← mul_assoc, mul_comm ((ϖ : K) ^ m), ← hqK, mul_div_cancel₀ _ hq0]
  · change t.a₆ = (ϖ : K) ^ m * (((u : O) : K) * (t.a₆ / q))
    rw [← mul_assoc, mul_comm ((ϖ : K) ^ m), ← hqK, mul_div_cancel₀ _ hq0]

end NormalForm

section Completion

attribute [local instance low] Classical.propDecidable

variable {k : Type u} [Field k] [NumberField k] (w : FinitePlace k)

/-- The canonical valuation subring of `F_w` is its unit ball. -/
lemma mem_canonicalValuationSubring_iff (x : localCompletion w) :
    x ∈ canonicalValuationSubring (localCompletion w) ↔ ‖x‖ ≤ 1 := by
  rw [Anabelian.AdicCompletion.canonicalValuationSubring_eq, norm_le_one_iff_valued]
  exact Iff.rfl

/-- `affGroup W M ±` is finite for finite `M` (it embeds in `ℤˣ × M`). -/
lemma finite_affGroup {K : Type*} [Field K] [DecidableEq K] {W : WeierstrassCurve K}
    {M : AddSubgroup W.toAffine.Point} (hM : (M : Set W.toAffine.Point).Finite) {pm : Bool} :
    Finite (Orbicurve.affGroup W M pm) := by
  haveI : Finite M := hM.to_subtype
  refine Finite.of_injective (β := ℤˣ × M)
    (fun g => ((g : Orbicurve.AffAut W).ε, ⟨(g : Orbicurve.AffAut W).m, g.2.1⟩)) ?_
  intro g h hgh
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hgh
  exact Subtype.ext (Orbicurve.AffAut.ext hgh.1 hgh.2)

/-- The model orbicurve `(E_q, ℓ, M, ±)` over `F_w` of a Tate curve `E_q`. -/
noncomputable abbrev tateOrbicurve (t : TateParameter (localCompletion w)) (ℓ : ℕ)
    (M : AddSubgroup t.tateCurve.toAffine.Point) (pm : Bool) :
    Anabelian.Orbicurve (localCompletion w) :=
  haveI := t.tateCurve_isElliptic (twelve_ne_zero w)
  ⟨t.tateCurve, ℓ, M, pm⟩

/-- **Theorem B for the Tate curves over `F_w`** (`TateOrbicurve.nondegenerate_of_normalForm` of
lana-agents/tempered-fundamental-groups, with the normal form `TateParameter.exists_normalForm`):
for a Tate parameter `q` over the completion `F_w` of a number field at a finite place, a level
`ℓ ≥ 1`, a finite subgroup `M ≤ E_q(F_w)` and a sign flag, the tempered fundamental group of
the geometric presentation `[(E_q ∖ (E_q[ℓ] + M)) / A]` of the model orbicurve
`(E_q, ℓ, M, ±)` over the canonical valuation of `F_w` has an open normal subgroup with infinite
quotient. -/
theorem tateOrbicurve_nondegenerate (t : TateParameter (localCompletion w)) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (M : AddSubgroup t.tateCurve.toAffine.Point)
    (hM : (M : Set t.tateCurve.toAffine.Point).Finite)
    (pm : Bool) :
    ∃ N : Subgroup (tateOrbicurve w t ℓ M pm).affineOrbifold.canonicalTemperedPi1,
      IsOpen (N : Set (tateOrbicurve w t ℓ M pm).affineOrbifold.canonicalTemperedPi1) ∧
        N.Normal ∧
          Infinite ((tateOrbicurve w t ℓ M pm).affineOrbifold.canonicalTemperedPi1 ⧸ N) := by
  haveI := t.tateCurve_isElliptic (twelve_ne_zero w)
  let O := canonicalValuationSubring (localCompletion w)
  let X := Orbicurve.orbicurveOrbifold t.tateCurve ℓ M pm
  letI : Algebra (Orbicurve.geomOrbicurveRing t.tateCurve ℓ M) X.Ω := X.algebraRΩ
  haveI : IsScalarTower (localCompletion w) (Orbicurve.geomOrbicurveRing t.tateCurve ℓ M) X.Ω :=
    X.tower
  haveI : Finite (Orbicurve.affGroup t.tateCurve M pm) := finite_affGroup hM
  haveI : IsAlgClosed X.Ω :=
    inferInstanceAs (IsAlgClosed (AlgebraicClosure (Orbicurve.funField t.tateCurve)))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, hm, u₄, ha₄, ε, ha₆⟩ :=
    TateParameter.exists_normalForm (mem_canonicalValuationSubring_iff w) t (twelve_ne_zero w) hϖ
  obtain ⟨p, hp, hpm⟩ := Anabelian.AdicCompletion.exists_prime_canonical w.maximalIdeal
  exact TateOrbicurve.nondegenerate_of_normalForm (W := t.tateCurve) (ℓ := ℓ) (M := M)
    (Orbicurve.affGroup t.tateCurve M pm)
    ↥(⊥ : Subgroup (Orbicurve.affGroup t.tateCurve M pm)) (X.V O) (X.V_comap O) p hp hpm hℓ hM hϖ
    rfl rfl rfl hm u₄ ha₄ ε ha₆

/-- **Theorem B for the Tate curves of initial Θ-data**: at a place `w` of the torsion field `K`
over `V_mod^bad`, let `E_{q_w}` be the Tate curve of the Θ-data's Tate uniformization
`D.tate.S w hw` (so `E ×_F K_w` is `E_{q_w}` after the change of variables `(D.tate.S w hw).C`).
For every finite subgroup `M ≤ E_{q_w}(K_w)` and sign flag, the tempered fundamental group of the
geometric presentation of the model orbicurve `(E_{q_w}, ℓ, M, ±)` (`ℓ` the prime of `D`) over
the canonical valuation `O_w` of `K_w` has an open normal subgroup with infinite quotient.

This is a statement about the geometric presentation `Orbicurve.affineOrbifold`, not about
`LocalThetaData.PivBad` (the Galois presentation of `E ×_F K_w`); see the module docstring. -/
theorem InitialThetaData.tate_nondegenerate (D : InitialThetaData.{u}) (w : FinitePlace D.Kt)
    (hw : IsBadPlace D.E D.prime.torsionField D.VBad w)
    (M : AddSubgroup (D.tate.S w hw).t.tateCurve.toAffine.Point)
    (hM : (M : Set (D.tate.S w hw).t.tateCurve.toAffine.Point).Finite)
    (pm : Bool) :
    ∃ N : Subgroup
        (tateOrbicurve w (D.tate.S w hw).t D.ℓ M pm).affineOrbifold.canonicalTemperedPi1,
      IsOpen (N : Set
        (tateOrbicurve w (D.tate.S w hw).t D.ℓ M pm).affineOrbifold.canonicalTemperedPi1) ∧
        N.Normal ∧ Infinite
          ((tateOrbicurve w (D.tate.S w hw).t D.ℓ M pm).affineOrbifold.canonicalTemperedPi1 ⧸ N) :=
  tateOrbicurve_nondegenerate w _ D.ℓ D.prime.ℓ_prime.one_lt.le M hM pm

end Completion

end Iut
