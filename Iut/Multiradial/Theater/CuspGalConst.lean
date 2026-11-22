/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.Theater.CuspConj

/-!
# Geometric transitivity on cuspidal places, and `π₁(X) ↠ G_k` at every level

For a model orbicurve `(E, ℓ, M, ±)` over a field `k` of characteristic `0` with all of `E[ℓ]`
rational, the genuine `π₁` is `Hgp E ℓ M ± ⧸ ⟨⟨inertia⟩⟩` with `Hgp ⊆ Gal(Ω / k(x))`
(`Iut.Anabelian.Genuine`). This file shows that `Hgp E ℓ M true` has the same image in the
automorphisms of the algebraic closure of `k` in `Ω` as all of `Gal(Ω / k(x))`:

* `mem_of_isIntegral`: a place `W ⊇ k` contains every element integral over `k`;
* `kbarX`: the field `k̄(x) ⊆ Ω`; **`exists_fixAlg_placeSmul`**: any two cuspidal places are
  conjugate under `Aut(Ω / k̄(x))`, i.e. by an element of `Gal(Ω / k(x))` fixing every element of
  `Ω` algebraic over `k` (the argument of `exists_gal_placeSmul` with `k̄` in place of `k`: all
  places containing `k̄` at which `x` has a pole agree on `k̄(x)`);
* **`exists_fixAlg_mul_mem_Hgp`**: for every `σ ∈ Gal(Ω / k(x))` there is `δ` fixing the algebraic
  elements with `δσ ∈ Hgp E ℓ M true`: move the place `σ(W₀)` back to the cuspidal place `W₀` over
  the origin; then `δσ(Q_ℓ) = ±Q_ℓ` (`act_Qpt_eq`, `isCuspPlace_smul`, `isCuspPlace_unique`).

Geometrically: `C̲ = (E/M ∖ E[ℓ]/M) / ±1` is geometrically connected over `k` (its zero cusp is
`k`-rational), so `π₁(C̲) ↠ G_k`. Used for `π₁(C̲_K) ↠ G_K` in `HodgeTheater/DStarCKu.lean`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Multiradial.Theater

open WeierstrassCurve Iut.Anabelian Iut.Anabelian.Genuine Polynomial

universe u

section Const

attribute [local instance low] Classical.propDecidable

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- **A place containing `k` contains every element integral over `k`** (valuation subrings are
integrally closed). -/
lemma mem_of_isIntegral {W : ValuationSubring (Ω E)} (hW : ContainsBase E W) {z : Ω E}
    (hz : IsIntegral k z) : z ∈ W := by
  let φ : k →+* W := (algebraMap k (Ω E)).codRestrict W.toSubring hW
  have hx : IsIntegral W z := by
    obtain ⟨p, hp, hpz⟩ := hz
    refine ⟨p.map φ, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap W (Ω E)).comp φ = algebraMap k (Ω E) := RingHom.ext fun _ => rfl
    rw [e]
    exact hpz
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx
  rw [← hy]
  exact y.2

/-- `k(x) ⊆ k̄(x)` inside `Ω` (`k̄` the algebraic closure of `k` in `Ω`). -/
lemma baseField_le_kbarX :
    baseField E ≤ (IntermediateField.adjoin (algebraicClosure k (Ω E)) {xG E}).restrictScalars k :=
  fun z hz => by
    have hz' : z ∈ IntermediateField.adjoin k {xG E} := (SetLike.ext_iff.1 (hbase E) z).1 hz
    have hle : IntermediateField.adjoin k {xG E} ≤
        (IntermediateField.adjoin (algebraicClosure k (Ω E)) {xG E}).restrictScalars k :=
      IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2
        (IntermediateField.subset_adjoin (algebraicClosure k (Ω E)) {xG E} rfl))
    exact hle hz'

/-- **`k̄(x) ⊆ Ω`** as an intermediate field over the base field `k(x)`. -/
def kbarX : IntermediateField (baseField E) (Ω E) :=
  IntermediateField.extendScalars (baseField_le_kbarX E)

lemma mem_kbarX {z : Ω E} :
    z ∈ kbarX E ↔ z ∈ IntermediateField.adjoin (algebraicClosure k (Ω E)) {xG E} :=
  IntermediateField.mem_extendScalars _

instance : IsGalois (kbarX E) (Ω E) := IsGalois.tower_top_of_isGalois (baseField E) (kbarX E) (Ω E)

/-- **Any two cuspidal places are conjugate under `Aut(Ω / k̄(x))`**: by an element of
`Gal(Ω / k(x))` fixing every element of `Ω` algebraic over `k`. -/
theorem exists_fixAlg_placeSmul {ℓ : ℕ} (hℓ : ℓ ≠ 0) {T T' : E.toAffine.Point} (hT : ℓ • T = 0)
    (hT' : ℓ • T' = 0) {W W' : ValuationSubring (Ω E)} (h : IsCuspPlace E ℓ T W)
    (h' : IsCuspPlace E ℓ T' W') :
    ∃ δ : Gal E, (∀ z : Ω E, IsAlgebraic k z → δ z = z) ∧ W' = placeSmul E δ W := by
  have hx := xG_notMem_of_isCuspPlace E hℓ hT h
  have hx' := xG_notMem_of_isCuspPlace E hℓ hT' h'
  have hk : ∀ c : algebraicClosure k (Ω E), algebraMap (algebraicClosure k (Ω E)) (Ω E) c ∈ W :=
    fun c => mem_of_isIntegral E h.1 (mem_algebraicClosure_iff.1 c.2).isIntegral
  have hk' : ∀ c : algebraicClosure k (Ω E), algebraMap (algebraicClosure k (Ω E)) (Ω E) c ∈ W' :=
    fun c => mem_of_isIntegral E h'.1 (mem_algebraicClosure_iff.1 c.2).isIntegral
  have hcomap : W.comap (algebraMap (kbarX E) (Ω E)) = W'.comap (algebraMap (kbarX E) (Ω E)) := by
    ext z
    exact mem_iff_of_mem_adjoin hk hx hk' hx' ((mem_kbarX E).1 z.2)
  obtain ⟨δ, hδ⟩ := CurvesJacobian.Cusp.exists_algEquiv_comap_eq W W' hcomap
  refine ⟨δ.restrictScalars (baseField E), fun z hz => ?_, hδ⟩
  have hzL : z ∈ kbarX E := (mem_kbarX E).2 (by
    have hmem : z ∈ algebraicClosure k (Ω E) := mem_algebraicClosure_iff.2 hz
    exact IntermediateField.algebraMap_mem _ (⟨z, hmem⟩ : algebraicClosure k (Ω E)))
  exact δ.commutes ⟨z, hzL⟩

/-- **`Hgp E ℓ M true` surjects onto the automorphisms of the algebraic elements**: for every
`σ ∈ Gal(Ω / k(x))` some `δ` fixing every element algebraic over `k` has `δσ ∈ Hgp E ℓ M true`
(`π₁(C̲) ↠ G_k`, `C̲ = (E, ℓ, M, ±)`). -/
theorem exists_fixAlg_mul_mem_Hgp {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point (ℓ : ℤ)) = ℓ ^ 2)
    (M : AddSubgroup E.toAffine.Point) (σ : Gal E) :
    ∃ δ : Gal E, (∀ z : Ω E, IsAlgebraic k z → δ z = z) ∧ δ * σ ∈ Hgp E ℓ M true := by
  have h0 : ℓ • (0 : E.toAffine.Point) = 0 := smul_zero ℓ
  obtain ⟨W, hW⟩ := exists_isCuspPlace hℓ h0
  obtain ⟨ε, hε, S, hS, hσ⟩ := act_Qpt_eq E hℓ hcard σ
  have hσW := isCuspPlace_smul hε hσ hW
  have hT1 : ℓ • (ε • (0 - S)) = 0 := by
    rw [smul_comm, zero_sub, smul_neg, hS, neg_zero, smul_zero]
  obtain ⟨δ, hδalg, hδ⟩ := exists_fixAlg_placeSmul E hℓ hT1 h0 hσW hW
  refine ⟨δ, hδalg, ?_⟩
  obtain ⟨ε', hε', S', -, hδσ⟩ := act_Qpt_eq E hℓ hcard (δ * σ)
  have h2 := isCuspPlace_smul hε' hδσ hW
  have hfix : placeSmul E (δ * σ) W = W :=
    calc placeSmul E (δ * σ) W = placeSmul E δ (placeSmul E σ W) :=
          ValuationSubring.ext _ _ fun _ => Iff.rfl
      _ = W := hδ.symm
  rw [hfix] at h2
  have h3 := isCuspPlace_unique hW h2
  have hS0 : S' = 0 := by
    rcases hε' with rfl | rfl
    · rw [one_smul, zero_sub, eq_comm, neg_eq_zero] at h3
      exact h3
    · rw [neg_one_zsmul, zero_sub, neg_neg] at h3
      exact h3.symm
  refine ⟨ε', ?_, ?_⟩
  · rcases hε' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, rfl⟩
  · rw [hδσ, hS0, map_zero, add_zero, sub_self]
    exact zero_mem _

end Const

end Iut.Multiradial.Theater
