/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.QuadraticExtension
import Iut.Cor312.ThetaData.ValuationTransfer
import Iut.Cor312.ThetaData.PlaceUnder
import Iut.Cor312.ThetaData.LocalAut
import Iut.Cor312.ThetaData.TateSign
import Iut.Cor312.ThetaData.TateFamilyOfSplit

/-!
# Split multiplicative reduction over the torsion field

Let `E/F` have multiplicative reduction at the places of `F` over `V_mod^bad` (of odd residue
characteristic), and let `K ⊇ F` be a number field over which `E` has `ℓ²` rational ℓ-torsion
points (`ℓ` an odd prime). Then at every finite place `w` of `K` over `V_mod^bad` the
discriminant `d = −c₄c₆` of the tangent quadratic at the node is a **square in `K_w`**
(`Iut.exists_sq_eq_neg_c₄_mul_c₆`), i.e. the reduction is split multiplicative:

* if `d` is a square in `K`, there is nothing to prove;
* otherwise, in `K' = K(√d)` choose a place `w'` over `w`. Over `L = K'_{w'}` the curve is a Tate
  curve (`Iut.exists_variableChange_tateCurve`). If the conjugation `σ` of `K'/K` fixes `w'`, it
  acts on `L` fixing `E` and all its ℓ-torsion (which is `K`-rational), so by the sign theorem
  (`Iut.exists_sqrt_neg_c₄_mul_c₆_fixed`) `d` has a `σ`-fixed square root in `L`; but the square
  roots of `d` in `L` are `±√d`, which `σ` negates — a contradiction (`d ≠ 0`).
* If `σ` moves `w'`, the place `w` splits in the quadratic extension `K'`, so the residue degree
  of `w'/w` is `1` (`Iut.inertiaDeg'_eq_one_of_ne`), `√d` is congruent modulo `w'` to an element
  of `𝓞_K`, hence `d` is a square modulo `w`, and Hensel's lemma gives a square root in `K_w`.

The tangent root at `w` follows (`Iut.exists_tangent_root_of_sq`), and with it the Tate
structures at all bad places (`Iut.tateFamilyOfTorsion`).
-/

namespace Iut

open NumberField WeierstrassCurve Iut.Anabelian TateCurvesTheta
open IsDedekindDomain.HeightOneSpectrum
open scoped Classical Valued

universe u

noncomputable section

/-! ## The tangent root from a square root of `−c₄c₆` -/

section Root

variable {k : Type*} [NormedField k]

/-- A square root of `−c₄c₆` gives a root of the tangent quadratic. -/
lemma exists_tangent_root_of_sq (W : WeierstrassCurve k) (h2 : (2 : k) ≠ 0) (hc₄ : W.c₄ ≠ 0)
    {s : k} (hs : s ^ 2 = -(W.c₄ * W.c₆)) :
    ∃ r : k, ‖W.c₄ * r ^ 2 + W.a₁ * W.c₄ * r - (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)‖ < 1 := by
  set r := (s - W.a₁ * W.c₄) / (2 * W.c₄) with hr
  refine ⟨r, ?_⟩
  have h := tangent_sq_eq W r
  have hs' : 2 * W.c₄ * r + W.a₁ * W.c₄ = s := by
    rw [hr]
    field_simp
    ring
  rw [hs', hs] at h
  have h4 : (4 : k) * W.c₄ ≠ 0 := by
    refine mul_ne_zero ?_ hc₄
    have : (4 : k) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hf : W.c₄ * r ^ 2 + W.a₁ * W.c₄ * r - (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄) = 0 := by
    have : (4 : k) * W.c₄ * (W.c₄ * r ^ 2 + W.a₁ * W.c₄ * r -
        (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left h4
  rw [hf, norm_zero]
  exact zero_lt_one

end Root

/-! ## Transitivity of lying over -/

section Trans

variable {A B C : Type*} [Field A] [NumberField A] [Field B] [NumberField B] [Field C]
  [NumberField C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

lemma FinitePlace.liesOver_trans {w₃ : FinitePlace C} {w₂ : FinitePlace B} {w₁ : FinitePlace A}
    (h₁ : FinitePlace.LiesOver w₃ w₂) (h₂ : FinitePlace.LiesOver w₂ w₁) :
    FinitePlace.LiesOver w₃ w₁ := by
  haveI : w₃.maximalIdeal.asIdeal.LiesOver w₂.maximalIdeal.asIdeal := h₁
  haveI : w₂.maximalIdeal.asIdeal.LiesOver w₁.maximalIdeal.asIdeal := h₂
  exact Ideal.LiesOver.trans w₃.maximalIdeal.asIdeal w₂.maximalIdeal.asIdeal
    w₁.maximalIdeal.asIdeal

end Trans

/-! ## The setting -/

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

/-- The classical decidable equality on `K`, as used by the model orbicurves. -/
local instance (priority := 1100) instDecidableEqIntermediateField''' : DecidableEq ↥K :=
  fun a b => Classical.propDecidable (a = b)

/-- The place of `F` below a bad place of `K` is a place of multiplicative reduction. -/
lemma mult_placeUnder
    (hmult : ∀ v ∈ VBad, ∀ w : FinitePlace F, FinitePlace.LiesOver w v →
      HasMultiplicativeReductionAt E w)
    {w : FinitePlace ↥K} (hw : IsBadPlace E K VBad w) :
    HasMultiplicativeReductionAt E (placeUnder w : FinitePlace F) := by
  obtain ⟨v, hv, hwv⟩ := hw
  refine hmult v hv _ ⟨?_⟩
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  rw [hwv.over, placeUnder_maximalIdeal, Ideal.under_def, Ideal.under_def, Ideal.comap_comap,
    ← IsScalarTower.algebraMap_eq]

section NormsAt

variable {K' : Type u} [Field K'] [NumberField K'] [Algebra F K'] {w : FinitePlace K'}
  {w₀ : FinitePlace F} (hww₀ : FinitePlace.LiesOver w w₀) (hw₀ : HasMultiplicativeReductionAt E w₀)
include hww₀ hw₀

lemma norm_c₄_curveLoc : ‖(curveLoc E K' w).c₄‖ = 1 := by
  rw [curveLoc, map_c₄, map_c₄, norm_emb_eq_one_iff, valuation_algebraMap_eq_one_iff hww₀]
  exact valuation_c₄_eq_one_of_mult E w₀ hw₀

lemma norm_Δ_curveLoc : ‖(curveLoc E K' w).Δ‖ < 1 := by
  rw [curveLoc, map_Δ, map_Δ, norm_emb_lt_one_iff, valuation_algebraMap_lt_one_iff hww₀]
  exact valuation_Δ_lt_one_of_mult E w₀ hw₀

lemma norm_c₆_curveLoc : ‖(curveLoc E K' w).c₆‖ = 1 :=
  norm_c₆_eq_one _ (norm_c₄_curveLoc E hww₀ hw₀) (norm_Δ_curveLoc E hww₀ hw₀)

lemma norm_d_curveLoc : ‖-((curveLoc E K' w).c₄ * (curveLoc E K' w).c₆)‖ = 1 := by
  rw [norm_neg, norm_mul, norm_c₄_curveLoc E hww₀ hw₀, norm_c₆_curveLoc E hww₀ hw₀, one_mul]

end NormsAt

/-- `-(c₄c₆)` of `E` over `K'_w` is the image of the global `-(c₄c₆)`. -/
lemma neg_c₄_mul_c₆_curveLoc {K' : Type u} [Field K'] [NumberField K'] [Algebra F K']
    (w : FinitePlace K') :
    -((curveLoc E K' w).c₄ * (curveLoc E K' w).c₆) =
      FinitePlace.embedding w.maximalIdeal (algebraMap F K' (-(E.c₄ * E.c₆))) := by
  rw [curveLoc, map_c₄, map_c₄, map_c₆, map_c₆, map_neg, map_neg, map_mul, map_mul]

/-! ## The square root of `−c₄c₆` at a bad place -/

variable (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
  (hmult : ∀ v ∈ VBad, ∀ w : FinitePlace F, FinitePlace.LiesOver w v →
    HasMultiplicativeReductionAt E w)
  {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
  (TK : AddSubgroup (E.map (algebraMap F ↥K)).toAffine.Point)
  (hTK : TK ≤ AddSubgroup.torsionBy (E.map (algebraMap F ↥K)).toAffine.Point ℓ)
  (hcard : ℓ * ℓ ≤ Nat.card ↥TK)

include hVBad hmult hℓ hodd hTK hcard in
set_option maxHeartbeats 1000000 in
/-- **`−c₄c₆` is a square in `K_w`** at every bad place `w` of a field `K` over which `E` has
`ℓ²` rational ℓ-torsion points. -/
theorem exists_sq_eq_neg_c₄_mul_c₆ {w : FinitePlace ↥K} (hw : IsBadPlace E K VBad w) :
    ∃ s : localCompletion w,
      s ^ 2 = FinitePlace.embedding w.maximalIdeal (algebraMap F ↥K (-(E.c₄ * E.c₆))) := by
  set dK : ↥K := algebraMap F ↥K (-(E.c₄ * E.c₆)) with hdK
  by_cases hsq : IsSquare dK
  · obtain ⟨y, hy⟩ := exists_sq_eq_of_isSquare K hsq
    exact ⟨FinitePlace.embedding w.maximalIdeal y, by rw [← map_pow, hy]⟩
  -- the quadratic extension `K' = K(√d)`
  set K' := sqrtField K dK with hK'
  obtain ⟨w', hw'⟩ := FinitePlace.exists_liesOver (K := ↥K') w
  have hw₀ := mult_placeUnder E K hmult hw
  have hww₀ : FinitePlace.LiesOver w (placeUnder w : FinitePlace F) := liesOver_placeUnder w
  -- `2 ∉ w'`
  have h2w : (2 : 𝓞 ↥K) ∉ w.maximalIdeal.asIdeal := two_notMem_of_isBadPlace E K hVBad hw
  have h2w' : (2 : 𝓞 ↥K') ∉ w'.maximalIdeal.asIdeal := by
    haveI : w'.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hw'
    intro h
    apply h2w
    rw [Ideal.mem_of_liesOver (P := w'.maximalIdeal.asIdeal), map_ofNat]
    exact h
  have h2L : ‖(2 : localCompletion w')‖ = 1 := norm_two_eq_one_of_notMem h2w'
  have h2L0 : (2 : localCompletion w') ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2L
    exact zero_ne_one h2L
  have h2K : ‖(2 : localCompletion w)‖ = 1 := norm_two_eq_one_of_notMem h2w
  -- the norm conditions over `L = K'_{w'}` and over `K_w`
  have hw'w₀ : FinitePlace.LiesOver w' (placeUnder w : FinitePlace F) :=
    FinitePlace.liesOver_trans hw' hww₀
  have hc₄L := norm_c₄_curveLoc E (K' := ↥K') (w := w') hw'w₀ hw₀
  have hΔL := norm_Δ_curveLoc E (K' := ↥K') (w := w') hw'w₀ hw₀
  have hdL : ‖-((curveLoc E ↥K' w').c₄ * (curveLoc E ↥K' w').c₆)‖ = 1 :=
    norm_d_curveLoc E (w := w') hw'w₀ hw₀
  have hc₄K := norm_c₄_curveLoc E (K' := ↥K) (w := w) hww₀ hw₀
  have hdK1 : ‖FinitePlace.embedding w.maximalIdeal dK‖ = 1 := by
    have := norm_d_curveLoc E (K' := ↥K) (w := w) hww₀ hw₀
    rwa [neg_c₄_mul_c₆_curveLoc] at this
  -- the square root `√d ∈ K'` and its image `s₀ ∈ L`
  set s₀ : localCompletion w' := FinitePlace.embedding w'.maximalIdeal (sqrtD K dK) with hs₀
  have hs₀sq : s₀ ^ 2 = -((curveLoc E ↥K' w').c₄ * (curveLoc E ↥K' w').c₆) := by
    rw [neg_c₄_mul_c₆_curveLoc, hs₀, ← map_pow, sqrtD_sq, IsScalarTower.algebraMap_apply F ↥K ↥K']
  have hs₀n : ‖s₀‖ = 1 := by
    have : ‖s₀‖ ^ 2 = 1 := by rw [← norm_pow, hs₀sq, hdL]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  -- `E` over `L` is a Tate curve
  have hc₄L0 : (curveLoc E ↥K' w').c₄ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc₄L
    exact zero_ne_one hc₄L
  obtain ⟨S⟩ : Nonempty (TateStructure (curveLoc E ↥K' w')) := by
    obtain ⟨t, C, hC, -⟩ := exists_variableChange_tateCurve h2L (twelve_ne_zero w')
      (curveLoc E ↥K' w') hc₄L hΔL (exists_tangent_root_of_sq _ h2L0 hc₄L0 hs₀sq)
    exact ⟨TateStructure.ofVariableChange t C hC ⟨h2L, twelve_ne_zero w'⟩⟩
  -- the ℓ-torsion of `E(L)` is the image of `TK`
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI := S.finite_torsion ℓ
  let f : ↥TK → ↥(TateStructure.torsion ℓ (curveLoc E ↥K' w')) := fun R =>
    ⟨toLoc (k := ↥K) w' E R.1, by
      have h0 : ℓ • (R : (E.map (algebraMap F ↥K)).toAffine.Point) = 0 :=
        (AddSubgroup.torsionBy.nsmul_iff).mp (hTK R.2)
      rw [AddSubgroup.torsionBy.nsmul_iff, ← toLoc_nsmul]
      exact (congrArg (toLoc (k := ↥K) w' E) h0).trans (toLoc_zero w' E)⟩
  have hfinj : Function.Injective f := fun R R' h =>
    Subtype.ext (toLoc_injective (k := ↥K) w' E (congrArg Subtype.val h))
  have hcardL : ℓ * ℓ ≤ Nat.card ↥(TateStructure.torsion ℓ (curveLoc E ↥K' w')) :=
    hcard.trans (Nat.card_le_card_of_injective f hfinj)
  have hfbij : Function.Bijective f :=
    hfinj.bijective_of_nat_card_le ((S.card_torsion_le ℓ).trans hcard)
  by_cases hfix : galPlace (conj K hsq) w' = w'
  · -- the inert/ramified case is impossible
    exfalso
    set σ := localAut (conj K hsq) w' hfix with hσ
    have hE := map_curveLoc_localAut (conj K hsq) w' hfix E
    have htors : ∀ P ∈ TateStructure.torsion ℓ (curveLoc E ↥K' w'),
        pointMap (curveLoc E ↥K' w') (σ : localCompletion w' →+* localCompletion w') P =
          pointCongr hE.symm P := by
      intro P hP
      obtain ⟨R, hR⟩ := hfbij.2 ⟨P, hP⟩
      have hPR : P = toLoc (k := ↥K) w' E R.1 := (congrArg Subtype.val hR).symm
      rw [hPR]
      exact pointMap_localAut_toLoc (conj K hsq) w' hfix E R.1
    obtain ⟨r, hr, hr2⟩ := exists_sqrt_neg_c₄_mul_c₆_fixed σ (norm_localAut _ _ _)
      (curveLoc E ↥K' w') hE ⟨h2L, twelve_ne_zero w'⟩ S hℓ hodd htors hcardL
    have hσs₀ : σ s₀ = -s₀ := by
      rw [hs₀, hσ, localAut_embedding, conj_sqrtD, map_neg]
    have hrs : r = s₀ ∨ r = -s₀ := by
      rw [← hs₀sq] at hr2
      exact sq_eq_sq_iff_eq_or_eq_neg.mp hr2
    have hs₀0 : s₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hs₀n
      exact zero_ne_one hs₀n
    rcases hrs with rfl | rfl
    · rw [hσs₀] at hr
      apply hs₀0
      have : (2 : localCompletion w') * s₀ = 0 := by linear_combination -hr
      exact (mul_eq_zero.mp this).resolve_left h2L0
    · rw [map_neg, hσs₀, neg_neg] at hr
      apply hs₀0
      have : (2 : localCompletion w') * s₀ = 0 := by linear_combination hr
      exact (mul_eq_zero.mp this).resolve_left h2L0
  · -- the split case: `√d` is congruent to an element of `𝓞_K` modulo `w'`
    have hgal : FinitePlace.LiesOver (galPlace (conj K hsq) w') w :=
      galPlace_liesOver (k₀ := ↥K) (fun _ => rfl) (conj K hsq) hw'
    have hf := inertiaDeg'_eq_one_of_ne (sqrtField_finrank_le K dK) (Ne.symm hfix) hw' hgal
    have hvs : w'.maximalIdeal.valuation ↥K' (sqrtD K dK) ≤ 1 := by
      rw [← norm_emb_le_one_iff, ← hs₀, hs₀n]
    obtain ⟨a, ha⟩ := exists_ringOfIntegers_sub_mem w' (sqrtD K dK) hvs
    obtain ⟨b, hb⟩ := exists_algebraMap_sub_mem_of_inertiaDeg_eq_one hw' hf a
    -- `w'(√d - b) < 1`
    have hb' : w'.maximalIdeal.valuation ↥K'
        (algebraMap (𝓞 ↥K') ↥K' (algebraMap (𝓞 ↥K) (𝓞 ↥K') b - a)) < 1 :=
      (valuation_lt_one_iff_mem _ _).mpr hb
    set bK : ↥K := algebraMap (𝓞 ↥K) ↥K b with hbK
    have hbK' : algebraMap ↥K ↥K' bK = algebraMap (𝓞 ↥K') ↥K' (algebraMap (𝓞 ↥K) (𝓞 ↥K') b) := by
      rw [hbK, ← IsScalarTower.algebraMap_apply (𝓞 ↥K) ↥K ↥K',
        IsScalarTower.algebraMap_apply (𝓞 ↥K) (𝓞 ↥K') ↥K']
    have hdiff : w'.maximalIdeal.valuation ↥K' (sqrtD K dK - algebraMap ↥K ↥K' bK) < 1 := by
      have : sqrtD K dK - algebraMap ↥K ↥K' bK =
          (sqrtD K dK - algebraMap (𝓞 ↥K') ↥K' a) -
            algebraMap (𝓞 ↥K') ↥K' (algebraMap (𝓞 ↥K) (𝓞 ↥K') b - a) := by
        rw [hbK', map_sub]
        ring
      rw [this]
      exact (Valuation.map_sub _ _ _).trans_lt (max_lt ha hb')
    -- `w'(d - b²) < 1`, hence `w(d - b²) < 1`
    have hsum : w'.maximalIdeal.valuation ↥K' (sqrtD K dK + algebraMap ↥K ↥K' bK) ≤ 1 := by
      refine (Valuation.map_add _ _ _).trans (max_le hvs ?_)
      rw [hbK']
      exact valuation_le_one w'.maximalIdeal (algebraMap (𝓞 ↥K) (𝓞 ↥K') b)
    have hdb : w'.maximalIdeal.valuation ↥K' (algebraMap ↥K ↥K' (dK - bK ^ 2)) < 1 := by
      have : algebraMap ↥K ↥K' (dK - bK ^ 2) =
          (sqrtD K dK - algebraMap ↥K ↥K' bK) * (sqrtD K dK + algebraMap ↥K ↥K' bK) := by
        rw [map_sub, map_pow, ← sqrtD_sq]
        ring
      rw [this, Valuation.map_mul]
      calc w'.maximalIdeal.valuation ↥K' (sqrtD K dK - algebraMap ↥K ↥K' bK) *
            w'.maximalIdeal.valuation ↥K' (sqrtD K dK + algebraMap ↥K ↥K' bK)
          ≤ w'.maximalIdeal.valuation ↥K' (sqrtD K dK - algebraMap ↥K ↥K' bK) * 1 :=
            mul_le_mul_right hsum _
        _ = w'.maximalIdeal.valuation ↥K' (sqrtD K dK - algebraMap ↥K ↥K' bK) := mul_one _
        _ < 1 := hdiff
    have hdbK : ‖FinitePlace.embedding w.maximalIdeal (dK - bK ^ 2)‖ < 1 := by
      rw [norm_emb_lt_one_iff, ← valuation_algebraMap_lt_one_iff hw']
      exact hdb
    -- Hensel in `K_w`
    have hbn : ‖FinitePlace.embedding w.maximalIdeal bK‖ = 1 := by
      have h1 : ‖(FinitePlace.embedding w.maximalIdeal bK) ^ 2‖ = 1 := by
        have : (FinitePlace.embedding w.maximalIdeal bK) ^ 2 =
            FinitePlace.embedding w.maximalIdeal dK -
              FinitePlace.embedding w.maximalIdeal (dK - bK ^ 2) := by
          rw [map_sub, map_pow]
          ring
        rw [this, sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm,
          norm_neg, hdK1, max_eq_left hdbK.le]
        rw [norm_neg, hdK1]
        exact hdbK.ne'
      rw [norm_pow] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h1
    obtain ⟨s, hs, -⟩ := exists_sq_eq_of_norm_sq_sub_lt h2K hbn (a := FinitePlace.embedding w.maximalIdeal dK)
      (by rw [← map_pow, ← map_sub, ← neg_sub, map_neg, norm_neg]; exact hdbK)
    exact ⟨s, hs⟩

end

end Iut
