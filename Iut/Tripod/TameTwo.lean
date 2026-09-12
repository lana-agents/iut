/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.InertiaInvolution
import Iut.Tripod.TowerFacts

/-!
# The tameness of `K = F_λ(E_λ[ℓ])` over `F_λ` at the places over `2`

For a point `λ` of the tripod, a prime `ℓ ≥ 7` and a place `v` of `K = F_λ(E_λ[ℓ])` of residue
characteristic `2` over the place `w` of `F = F_λ`, `2 ∤ e(v/w)`
(`Iut.Tripod.not_two_dvd_relRamIdx_torsionField`), so `Iut.Tripod.TameTwoHyp P` holds for every
curve provider (`Iut.Tripod.tameTwoHyp`), in particular for `Iut.Tripod.tripodProviders`:

* `E_λ/F_λ` has stable reduction at `w` (`Iut.EllipticCurveData.CurveArithmetic.stable_reduction`,
  from the rational `3`-torsion, `Iut/Tripod/StableTwo.lean`), so some model `C • E_λ` is a
  `w`-integral good or multiplicative model (`Iut.exists_isStableModel_of_hasStableReductionAt`),
  which stays good or multiplicative for `v` (`Iut.isStableModel_baseChange`);
* the ramification index `e(v/w)` is the order of the inertia group `I_v ⊆ Gal(K/F)`
  (`Iut.relRamIdx_eq_card_inertia`); if it were even, `I_v` would contain an element `σ` of
  order `2` (Cauchy), acting on `E(K)[ℓ]` as an involution satisfying the inertia condition;
* such an involution fixes the `ℓ`-torsion of the stable model
  (`Iut.InertiaInvolution.map_eq_self`, the tangent-slope argument of
  `Iut/Tower/InertiaInvolution.lean`, transported to `E_λ` along the change of variables
  `Iut.exists_vcEquiv_map_eq`), and `Gal(K/F)` acts faithfully on `E(K)[ℓ]`
  (`Iut.AdmissiblePrimeData.eq_one_of_forall_torsion`), so `σ = 1`: a contradiction.

With `Iut.Tripod.towerLocalHyp_of_tameTwo`, the residual local facts of the tower are a theorem
(`Iut.Tripod.towerLocalHyp`).
-/

namespace Iut

open NumberField WeierstrassCurve

/-! ### Stable models at a place from stable reduction -/

section Models

variable {F : Type*} [Field F] [NumberField F] (E : WeierstrassCurve F) (w : FinitePlace F)

/-- A model whose base change to `F_w` is integral over `𝒪_w` is `w`-integral. -/
lemma isIntegralModel_of_baseChange
    [(E.baseChange (localCompletion w)).IsIntegral (w.maximalIdeal.adicCompletionIntegers F)] :
    IsIntegralModel (w.maximalIdeal.valuation F) E := by
  have h₁ := norm_a₁_le_one (E.baseChange (localCompletion w))
  have h₂ := norm_a₂_le_one (E.baseChange (localCompletion w))
  have h₃ := norm_a₃_le_one (E.baseChange (localCompletion w))
  have h₄ := norm_a₄_le_one (E.baseChange (localCompletion w))
  have h₆ := norm_a₆_le_one (E.baseChange (localCompletion w))
  rw [baseChange_adicCompletion_eq, map_a₁, norm_emb_le_one_iff] at h₁
  rw [baseChange_adicCompletion_eq, map_a₂, norm_emb_le_one_iff] at h₂
  rw [baseChange_adicCompletion_eq, map_a₃, norm_emb_le_one_iff] at h₃
  rw [baseChange_adicCompletion_eq, map_a₄, norm_emb_le_one_iff] at h₄
  rw [baseChange_adicCompletion_eq, map_a₆, norm_emb_le_one_iff] at h₆
  exact ⟨h₁, h₂, h₃, h₄, h₆⟩

/-- **A `w`-integral good or multiplicative model at a place of stable reduction.** -/
theorem exists_isStableModel_of_hasStableReductionAt (h : HasStableReductionAt E w) :
    ∃ C : VariableChange F, IsStableModel (w.maximalIdeal.valuation F) (C • E) := by
  rcases h with ⟨C, hC⟩ | hm
  · haveI := hC
    refine ⟨C, Or.inl ⟨isIntegralModel_of_baseChange (C • E) w, ?_⟩⟩
    have hΔ : ‖((C • E).baseChange (localCompletion w)).Δ‖ = 1 :=
      (valuation_eq_one_iff w _).1 HasGoodReduction.goodReduction
    rwa [baseChange_adicCompletion_eq, map_Δ, norm_emb_eq_one_iff] at hΔ
  · obtain ⟨C, hC, hc₄, hΔ⟩ := exists_variableChange_of_mult E w hm
    haveI := hC
    exact ⟨C, Or.inr ⟨isIntegralModel_of_baseChange (C • E) w, hΔ, hc₄⟩⟩

end Models

/-! ### Base change of stable models along an extension of places -/

section BaseChange

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {v : FinitePlace K} {u : FinitePlace k} (hvu : FinitePlace.LiesOver v u)
include hvu

/-- A `u`-integral model is `v`-integral after base change, for `v ∣ u`. -/
lemma isIntegralModel_baseChange {W : WeierstrassCurve k}
    (h : IsIntegralModel (u.maximalIdeal.valuation k) W) :
    IsIntegralModel (v.maximalIdeal.valuation K) (W.baseChange K) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := h
  exact ⟨(valuation_algebraMap_le_one_iff hvu _).2 h₁, (valuation_algebraMap_le_one_iff hvu _).2 h₂,
    (valuation_algebraMap_le_one_iff hvu _).2 h₃, (valuation_algebraMap_le_one_iff hvu _).2 h₄,
    (valuation_algebraMap_le_one_iff hvu _).2 h₆⟩

/-- A `u`-stable model is `v`-stable after base change, for `v ∣ u`. -/
lemma isStableModel_baseChange {W : WeierstrassCurve k}
    (h : IsStableModel (u.maximalIdeal.valuation k) W) :
    IsStableModel (v.maximalIdeal.valuation K) (W.baseChange K) := by
  have hΔ : (W.baseChange K).Δ = algebraMap k K W.Δ := map_Δ W _
  have hc₄ : (W.baseChange K).c₄ = algebraMap k K W.c₄ := map_c₄ W _
  rcases h with ⟨hi, hΔ'⟩ | ⟨hi, hΔ', hc₄'⟩
  · exact Or.inl ⟨isIntegralModel_baseChange hvu hi,
      by rw [hΔ]; exact (valuation_algebraMap_eq_one_iff hvu _).2 hΔ'⟩
  · exact Or.inr ⟨isIntegralModel_baseChange hvu hi,
      by rw [hΔ]; exact (valuation_algebraMap_lt_one_iff hvu _).2 hΔ',
      by rw [hc₄]; exact (valuation_algebraMap_eq_one_iff hvu _).2 hc₄'⟩

end BaseChange

end Iut

namespace Iut.Tripod

open Iut Iut.EllipticCurveData NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  WeierstrassCurve WeierstrassCurve.Affine

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK

variable (P : CurveProviders) (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
  (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw)

set_option quotPrecheck false in
/-- The torsion field `K` of the datum of `x` and `ℓ`. -/
local notation "KF" => ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField

variable [NumberField ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField]
  (v : FinitePlace ↥(primeDataOf P x hℓ h7 hsl hP2).torsionField)

set_option maxHeartbeats 1000000 in
-- the conjugate action on the points of the stable model elaborates slowly
/-- **An involution in the inertia group of a place over `2` is trivial**: it fixes the
`ℓ`-torsion of a stable model of `E_λ` at the place (`Iut.InertiaInvolution.map_eq_self`), and
`Gal(K/F)` acts faithfully on `E(K)[ℓ]`. -/
theorem eq_one_of_mul_self_eq_one_of_mem_inertia (h2 : residueChar v = 2)
    (σ : KF ≃ₐ[(P.curve x).F] KF)
    (hσ : σ ∈ v.maximalIdeal.asIdeal.inertia (KF ≃ₐ[(P.curve x).F] KF)) (hσ2 : σ * σ = 1) :
    σ = 1 := by
  set w := placeUnder (k := (P.curve x).F) v with hw_def
  have hvw : FinitePlace.LiesOver v w := liesOver_placeUnder v
  set vK := v.maximalIdeal.valuation KF with hvK
  have hℓ' : vK (ℓ : KF) = 1 := (valuation_natCast_eq_one_iff v hℓ).2 (by rw [h2]; omega)
  have hodd : Odd ℓ := hℓ.odd_of_ne_two (by omega)
  have h2' : vK 2 < 1 := by
    refine lt_of_le_of_ne (valuation_ofNat_le_one vK 2) fun h => ?_
    have := (valuation_natCast_eq_one_iff v Nat.prime_two).1 (by rw [Nat.cast_ofNat]; exact h)
    exact this h2
  have hσ' : ∀ z : KF, vK z ≤ 1 → vK (σ z - z) < 1 := fun z hz =>
    valuation_sub_lt_one_of_mem_inertia hσ hz
  have hσσ : ∀ z : KF, σ (σ z) = z := fun z => by
    have := congrArg (fun τ : KF ≃ₐ[(P.curve x).F] KF => τ z) hσ2
    simpa using this
  -- the stable model `C • E` at `w`, base changed to `K`
  obtain ⟨C, hC⟩ := exists_isStableModel_of_hasStableReductionAt (P.curve x).E w
    ((P.arith x).stable_reduction w)
  have hCK : IsStableModel vK ((C • (P.curve x).E).baseChange KF) := isStableModel_baseChange hvw hC
  set C' : VariableChange KF := C.map (algebraMap (P.curve x).F KF) with hC'
  have hCE : C' • Affine.baseChange (P.curve x).E KF = (C • (P.curve x).E).baseChange KF :=
    map_variableChange _ _ _
  have hW : IsStableModel vK (C' • Affine.baseChange (P.curve x).E KF) := by
    rw [hCE]; exact hCK
  have hfix₁ : σ (C' • Affine.baseChange (P.curve x).E KF).a₁ =
      (C' • Affine.baseChange (P.curve x).E KF).a₁ := by
    rw [hCE]; exact σ.commutes _
  have hfix₂ : σ (C' • Affine.baseChange (P.curve x).E KF).a₂ =
      (C' • Affine.baseChange (P.curve x).E KF).a₂ := by
    rw [hCE]; exact σ.commutes _
  have hfix₃ : σ (C' • Affine.baseChange (P.curve x).E KF).a₃ =
      (C' • Affine.baseChange (P.curve x).E KF).a₃ := by
    rw [hCE]; exact σ.commutes _
  have hfix₄ : σ (C' • Affine.baseChange (P.curve x).E KF).a₄ =
      (C' • Affine.baseChange (P.curve x).E KF).a₄ := by
    rw [hCE]; exact σ.commutes _
  have hcase : (vK (C' • Affine.baseChange (P.curve x).E KF).a₁ = 1 ∧ vK 2 < 1) ∨
      vK (C' • Affine.baseChange (P.curve x).E KF).Δ = 1 := by
    rcases hW with ⟨_, hΔ⟩ | ⟨hi, _, hc₄⟩
    · exact Or.inr hΔ
    · exact Or.inl ⟨InertiaInvolution.valuation_a₁_eq_one_of_c₄ vK hi hc₄ h2', h2'⟩
  have hint : IsIntegralModel vK (C' • Affine.baseChange (P.curve x).E KF) := by
    rcases hW with ⟨hi, _⟩ | ⟨hi, _, _⟩ <;> exact hi
  -- the action of `σ` on the points, conjugated to the stable model
  refine (primeDataOf P x hℓ h7 hsl hP2).eq_one_of_forall_torsion σ fun Q hQ => ?_
  change Point.map (W' := (P.curve x).E) (S := (P.curve x).F)
    (σ : KF →ₐ[(P.curve x).F] KF) Q = Q
  have hφ : ∀ (a b : KF) (h : (Affine.baseChange (P.curve x).E KF).Nonsingular a b),
      ∃ h' : (Affine.baseChange (P.curve x).E KF).Nonsingular (σ a) (σ b),
        Point.map (W' := (P.curve x).E) (S := (P.curve x).F) (σ : KF →ₐ[(P.curve x).F] KF)
          (Point.some a b h) = Point.some (σ a) (σ b) h' :=
    fun a b h => ⟨_, Point.map_some _ h⟩
  set e := Anabelian.vcEquiv C' (Affine.baseChange (P.curve x).E KF) with he
  set φ' := e.toAddMonoidHom.comp
    ((Point.map (W' := (P.curve x).E) (S := (P.curve x).F)
      (σ : KF →ₐ[(P.curve x).F] KF)).comp e.symm.toAddMonoidHom) with hφ'
  have hφ'' := exists_vcEquiv_map_eq C' (Affine.baseChange (P.curve x).E KF) (σ : KF →+* KF)
    (σ.commutes _) (σ.commutes _) (σ.commutes _) (σ.commutes _) _ hφ
  have hQ' : ℓ • e Q = 0 := by
    rw [← map_nsmul]
    exact (congrArg e hQ).trans (map_zero e)
  have key := InertiaInvolution.map_eq_self vK hint (σ : KF →+* KF) hσσ hσ' hfix₁ hfix₂ hfix₃
    hfix₄ hcase hodd hℓ' φ' hφ'' (e Q) hQ'
  rw [hφ'] at key
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
    at key
  exact e.injective key

/-- **`K/F` is tamely ramified at the places over `2`**: `2 ∤ e(v/w)` for a place `v` of
`K = F_λ(E_λ[ℓ])` of residue characteristic `2` over the place `w` of `F_λ` (the inertia group
contains no element of order `2`). -/
theorem not_two_dvd_relRamIdx_torsionField (h2 : residueChar v = 2) :
    ¬ 2 ∣ relRamIdx v (placeUnder (k := (P.curve x).F) v) := by
  rw [relRamIdx_eq_card_inertia (liesOver_placeUnder v)]
  intro hdvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hτ2 : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have hτ1 : τ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  apply hτ1
  apply Subtype.ext
  refine eq_one_of_mul_self_eq_one_of_mem_inertia P x hℓ h7 hsl hP2 v h2 τ.1 τ.2 ?_
  have := congrArg Subtype.val hτ2
  rw [Subgroup.coe_pow, pow_two] at this
  exact this

end Iut.Tripod

namespace Iut.Tripod

open Iut Iut.EllipticCurveData NumberField

/-- **The residual tameness of `K = F_λ(E_λ[ℓ])` over `F_λ` at the places over `2` holds** for
every curve provider: `2 ∤ e(v/w)` for the places `v` of residue characteristic `2`. -/
theorem tameTwoHyp (P : CurveProviders) : TameTwoHyp P := by
  intro x ℓ hℓ h7 hsl hP2
  haveI := ((P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ) hsl
    hP2).numberField_torsionField
  intro v h2
  exact not_two_dvd_relRamIdx_torsionField P x hℓ h7 hsl hP2 v h2

/-- **The residual local facts of the tower hold for the curves of the tripod**: the tameness
at `2` (`Iut.Tripod.tameTwoHyp`), Néron–Ogg–Shafarevich and the ramification bound away from
`2·3·5·ℓ` are theorems. -/
theorem towerLocalHyp (P : CurveProviders) : TowerLocalHyp P :=
  towerLocalHyp_of_tameTwo P (tameTwoHyp P)

end Iut.Tripod
