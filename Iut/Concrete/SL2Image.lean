/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.ModEllRepGalois
import Iut.Cor312.ThetaData.TateFamilyOfTorsion
import Iut.Anabelian.TateTorsion
import Iut.Tripod.SL2Generation

/-!
# The image of the mod-`ℓ` representation contains `SL₂(𝔽_ℓ)` ([GenEll], Lemma 3.1(iii))

For an elliptic curve `E/F` over a number field with mod-`ℓ` representation data `R`
(`Iut.EllipticCurveData.ModEllRepData`), a prime `ℓ ≥ 5` such that

* (P2) `ℓ ∤ ord_w(q_w)` at every place `w` of multiplicative reduction,
* (P4) `E` has no `ℓ`-cyclic subgroup scheme (`Iut.EllipticCurveData.HasCyclicSubgroup`),
* (P5) some place of multiplicative reduction has residue characteristic `≠ 2, ℓ`,

the image of `ρ : Gal(F̄/F) → GL₂(𝔽_ℓ)` contains `SL₂(𝔽_ℓ)`
(`Iut.EllipticCurveData.sl_le_range_of`).

## The proof

Let `K = F(E[ℓ])` be the torsion field, `w` a place of (P5) and `w'` a place of `K` over
`w`. Over `K_{w'}` the curve is a Tate curve (`Iut.tateStructureOfTorsion`, from the
multiplicative reduction and the rationality of the `ℓ²` torsion points over `K`), and since
`E[ℓ] ⊆ E(K_{w'})` the Tate parameter `q` has an `ℓ`-th root modulo `q^{ℓℤ}`
(`Iut.TateStructure.exists_root_class`): `u^ℓ = q^{1 + ℓm}` for a unit `u` of `K_{w'}`. Taking
valuations, `ℓ ∣ ord_{w'}(q) = e(w'/w)·ord_w(q)` (`v(q) = v(j)⁻¹` for a Tate curve, and
`v_{w'} = v_w^e` on `F`), so `ℓ ∣ e(w'/w)` by (P2) (`prime_dvd_ramificationIdx`). The
ramification index divides `|Gal(K/F)| = |ρ(Gal(F̄/F))|`, so by Cauchy's theorem the image
contains an element of order `ℓ`, which is a transvection `T ≠ 1`
(`Iut.SL2.transvection_of_orderOf`). By (P4) the image stabilizes no line
(`ModEllRepData.exists_mulVec_ne_smul_of_not_hasCyclicSubgroup`), hence contains `SL₂(𝔽_ℓ)`
(`Iut.SL2.toGL_mem_of_transvection`).
-/

namespace Iut

universe u

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum TateCurvesTheta
  WeierstrassCurve WithZero Iut.Anabelian
open scoped WithZero Valued MatrixGroups Classical

noncomputable section

/-! ### Valuations of Tate parameters on a completion -/

section Valued

variable {k : Type*} [Field k] [NumberField k] {w : FinitePlace k}

/-- Elements of `k_w` of the same norm have the same valuation. -/
lemma valued_eq_of_norm_eq {x y : localCompletion w} (h : ‖x‖ = ‖y‖) :
    Valued.v x = Valued.v y :=
  le_antisymm (Valued.toNormedField.norm_le_iff.mp h.le) (Valued.toNormedField.norm_le_iff.mp h.ge)

/-- The valuation on `k_w` of the image of `x ∈ k` is the `w`-adic valuation of `x`. -/
lemma valued_embedding (x : k) :
    Valued.v (FinitePlace.embedding w.maximalIdeal x : localCompletion w) =
      w.maximalIdeal.valuation k x := by
  rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']

/-- A uniformizer of `k_w` in the sense of the norm has valuation `exp (−1)`. -/
lemma valued_of_isUniformizer {π : localCompletion w} (hπ : IsUniformizer π) :
    Valued.v π = exp (-1 : ℤ) := by
  obtain ⟨π₀, hπ₀⟩ := w.maximalIdeal.valuation_exists_uniformizer k
  have h0 : Valued.v (FinitePlace.embedding w.maximalIdeal π₀ : localCompletion w) =
      exp (-1 : ℤ) := by
    rw [valued_embedding, hπ₀]
  have hne : (FinitePlace.embedding w.maximalIdeal π₀ : localCompletion w) ≠ 0 := by
    intro h
    rw [h, map_zero] at h0
    exact exp_ne_zero h0.symm
  obtain ⟨m, hm⟩ := hπ.generates (Units.mk0 _ hne)
  have hπ0 : Valued.v π ≠ 0 := (Valuation.ne_zero_iff _).mpr hπ.ne_zero
  have hexp : Valued.v π = exp (log (Valued.v π)) := (exp_log hπ0).symm
  have h1 : Valued.v (FinitePlace.embedding w.maximalIdeal π₀ : localCompletion w) =
      Valued.v (π ^ m) :=
    valued_eq_of_norm_eq (by rw [norm_zpow]; exact hm)
  rw [h0, map_zpow₀, hexp, ← exp_zsmul, exp_inj, smul_eq_mul] at h1
  have hlt : Valued.v π < 1 := (norm_lt_one_iff_valued w π).mp hπ.norm_lt_one
  rw [hexp, ← exp_zero, exp_lt_exp] at hlt
  have hmul : (-log (Valued.v π)) * m = 1 := by linear_combination h1
  have hone := Int.eq_one_of_mul_eq_one_right (by omega) hmul
  rw [hexp]
  congr 1
  omega

/-- The valuation of a Tate parameter is `exp (−ord q)`, for the discrete order with respect
to a uniformizer. -/
lemma valued_q_toOrdered (t : TateParameter (localCompletion w)) {π : localCompletion w}
    (hπ : IsUniformizer π) :
    Valued.v (t.q : localCompletion w) = exp (-((t.toOrdered hπ).orderNat : ℤ)) := by
  have h := valued_eq_of_norm_eq (x := (t.q : localCompletion w))
    (y := π ^ (t.toOrdered hπ).orderNat) (by rw [norm_pow]; exact t.norm_q_eq_pow_orderNat hπ)
  rw [h, map_pow, valued_of_isUniformizer hπ, ← exp_nsmul]
  congr 1
  simp

/-- `v(q) = v(j(E_q))⁻¹` for a Tate curve over `k_w`. -/
lemma valued_q_eq_inv_tateJ (t : TateParameter (localCompletion w)) :
    Valued.v (t.q : localCompletion w) = (Valued.v t.tateJ)⁻¹ := by
  have h := valued_eq_of_norm_eq (x := t.tateJ) (y := (t.q : localCompletion w)⁻¹)
    (by rw [norm_inv]; exact t.norm_tateJ (twelve_ne_zero w))
  rw [h, map_inv₀, inv_inv]

end Valued

/-! ### The ramification index at a bad place -/

namespace EllipticCurveData

variable (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic) (TI : C.TateInputs) {ℓ : ℕ}
  (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (R : C.ModEllRepData ℓ)

/-- The classical decidable equality on `K`, as used by the model orbicurves. -/
local instance (priority := 1100) instDecidableEqTorsionField' :
    DecidableEq ↥R.torsionField :=
  fun a b => Classical.propDecidable (a = b)

/-- The ramification index of a place of the torsion field divides the order of its Galois
group (the fundamental identity `g·e·f = |Gal(K/F)|`). -/
lemma ramificationIdx'_dvd_card_gal {w : FinitePlace C.F} {w' : FinitePlace ↥R.torsionField}
    (hw'w : FinitePlace.LiesOver w' w) :
    w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal ∣
      Nat.card (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField) := by
  haveI : w'.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hw'w
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn w.maximalIdeal.asIdeal
    (𝓞 ↥R.torsionField) (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ w'.maximalIdeal.asIdeal
    (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)] at h
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ w.maximalIdeal.ne_bot]
  exact ⟨(w.maximalIdeal.asIdeal.primesOver (𝓞 ↥R.torsionField)).ncard *
    w.maximalIdeal.asIdeal.inertiaDegIn (𝓞 ↥R.torsionField), by rw [← h]; ring⟩

/-- The `ℓ`-torsion of `E(K)` embeds in the `ℓ`-torsion of `E(K_{w'})`. -/
lemma card_torsion_curveKw_ge (w' : FinitePlace ↥R.torsionField)
    [Finite ↥(TateStructure.torsion ℓ (curveKw C.E R.torsionField w'))] :
    ℓ * ℓ ≤ Nat.card ↥(TateStructure.torsion ℓ (curveKw C.E R.torsionField w')) := by
  let f : ↥R.TK →+ ↥(TateStructure.torsion ℓ (curveKw C.E R.torsionField w')) :=
    ((pointMap (curveK C.E R.torsionField) (emb R.torsionField w')).restrict R.TK).codRestrict _
      fun P => by
        rw [AddSubgroup.torsionBy.nsmul_iff]
        have hP := AddSubgroup.torsionBy.nsmul_iff.mp P.2
        rw [AddMonoidHom.restrict_apply, ← map_nsmul, hP, map_zero]
  have hf : Function.Injective f := fun P P' h => by
    apply Subtype.ext
    apply pointMap_injective (curveK C.E R.torsionField) (emb R.torsionField w')
    have h' := congrArg Subtype.val h
    simpa only [f, AddMonoidHom.codRestrict_apply, AddMonoidHom.restrict_apply] using h'
  calc ℓ * ℓ = Nat.card ↥R.TK := by rw [R.card_torsionBy_EK, sq]
    _ ≤ _ := Nat.card_le_card_of_injective f hf

include CA hℓ hodd in
/-- **`ℓ` divides the ramification index** of a place `w'` of the torsion field `K = F(E[ℓ])`
over a place `w` of multiplicative reduction of residue characteristic `≠ 2, ℓ` with
`ℓ ∤ ord_w(q_w)`: the Tate parameter is an `ℓ`-th power in `K_{w'}` modulo `q^{ℓℤ}`. -/
theorem prime_dvd_ramificationIdx {w : FinitePlace C.F} (hw : w ∈ C.badAll)
    (h2 : residueChar w ≠ 2) (hwℓ : residueChar w ≠ ℓ) (hP2 : ¬ ℓ ∣ TI.qOrder w hw)
    {w' : FinitePlace ↥R.torsionField} (hw'w : FinitePlace.LiesOver w' w) :
    ℓ ∣ w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  -- `w'` is a bad place of `K` over `V_mod^bad(ℓ)`
  have hmem : w ∈ badPlacesOver C.F C.E (C.VBadOf ℓ) := by
    rw [C.badPlacesOver_VBadOf CA]
    exact ⟨hw, h2, hwℓ⟩
  obtain ⟨v, hv, hwv⟩ := hmem
  have hbad : IsBadPlace C.E R.torsionField (C.VBadOf ℓ) w' :=
    ⟨v, hv, FinitePlace.liesOver_trans hw'w hwv⟩
  have hcard : ℓ * ℓ ≤ Nat.card ↥R.TK := by rw [R.card_torsionBy_EK, sq]
  -- the Tate structure over `K_{w'}` and the `ℓ`-th root of `q`
  let S := tateStructureOfTorsion C.E R.torsionField ℓ (fun _ hv => hv.1)
    (fun _ hv w hwv => hv.2.2.2 w hwv) hℓ hodd R.TK le_rfl hcard hbad
  haveI := S.finite_torsion ℓ
  obtain ⟨u, m, hu⟩ := S.exists_root_class ℓ (card_torsion_curveKw_ge C R w')
  set e := w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal with he
  set n := TI.qOrder w hw with hn
  have hn' : ((TI.tate w hw).toOrdered (TI.unif_isUniformizer w hw)).orderNat = n := rfl
  -- `v_w(j) = exp (ord_w q)`
  have hjF : w.maximalIdeal.valuation C.F C.E.j = exp (n : ℤ) := by
    have h1 := valued_q_eq_inv_tateJ (TI.tate w hw)
    rw [TI.tateJ_eq w hw, valued_embedding,
      valued_q_toOrdered _ (TI.unif_isUniformizer w hw), hn'] at h1
    rw [← inv_inv (w.maximalIdeal.valuation C.F C.E.j), ← h1, ← exp_neg, neg_neg]
  -- `j(E_q) = j(E)` over `K_{w'}`
  have hJ : S.t.tateJ = emb R.torsionField w' (algebraMap C.F ↥R.torsionField C.E.j) := by
    haveI := S.t.tateCurve_isElliptic (twelve_ne_zero w')
    rw [S.t.tateJ_eq_j (twelve_ne_zero w'), j_eq_inv_Δ_mul, ← S.hC, ← j_eq_inv_Δ_mul,
      variableChange_j]
    change ((curveK C.E R.torsionField).map (emb R.torsionField w')).j = _
    rw [map_j]
    congr 1
    exact map_j C.E _
  -- `v_{w'}(q) = exp (−e·ord_w q)`
  have hqK : Valued.v (S.t.q : localCompletion w') = exp (-((e : ℤ) * n)) := by
    rw [valued_q_eq_inv_tateJ, hJ, valued_embedding, valuation_algebraMap_eq_pow hw'w, hjF,
      ← exp_nsmul, ← exp_neg, ← he, nsmul_eq_mul]
  -- valuations of `u^ℓ = q^{1 + ℓm}`
  have hu' := congrArg (fun x : (localCompletion w')ˣ => Valued.v (x : localCompletion w')) hu
  simp only [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_pow, map_zpow₀] at hu'
  rw [hqK] at hu'
  have hu0 : Valued.v (u : localCompletion w') ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  rw [← exp_log hu0, ← exp_nsmul, ← exp_zsmul, exp_inj, nsmul_eq_mul, smul_eq_mul] at hu'
  -- `ℓ ∣ e·n` in `ℤ`
  have hdvd : (ℓ : ℤ) ∣ (1 + ℓ * m) * ((e : ℤ) * n) :=
    ⟨-log (Valued.v (u : localCompletion w')), by linear_combination hu'⟩
  rw [add_mul, one_mul, dvd_add_left (Dvd.intro (m * ((e : ℤ) * n)) (by ring))] at hdvd
  have hdvd' : ℓ ∣ e * n := by exact_mod_cast hdvd
  exact (hℓ.dvd_mul.mp hdvd').resolve_right hP2

include CA TI hℓ hodd in
/-- **`ℓ` divides `|ρ(Gal(F̄/F))|`** under (P2) and (P5). -/
theorem prime_dvd_card_range (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
    (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ) :
    ℓ ∣ Nat.card R.rep.range := by
  obtain ⟨w, hw, h2, hwℓ⟩ := hP5
  obtain ⟨w', hw'w⟩ := FinitePlace.exists_liesOver (K := ↥R.torsionField) w
  rw [R.card_range]
  exact (C.prime_dvd_ramificationIdx CA TI hℓ hodd R hw h2 hwℓ (hP2 w hw) hw'w).trans
    (C.ramificationIdx'_dvd_card_gal R hw'w)

include CA TI hℓ in
/-- **[GenEll], Lemma 3.1(iii)**: under (P2), (P4), (P5) the image of the mod-`ℓ`
representation contains `SL₂(𝔽_ℓ)`. -/
theorem sl_le_range_of (h5 : 5 ≤ ℓ) (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
    (hP4 : ¬ C.HasCyclicSubgroup ℓ)
    (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)
    (A : SL(2, ZMod ℓ)) : A.toGL ∈ R.rep.range := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hdvd := C.prime_dvd_card_range CA TI hℓ (by omega) R hP2 hP5
  obtain ⟨T, hT⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  rw [← Subgroup.orderOf_coe] at hT
  obtain ⟨hT1, hT2⟩ := SL2.transvection_of_orderOf (T : GL (Fin 2) (ZMod ℓ)) hT
  exact SL2.toGL_mem_of_transvection R.rep.range T.2 hT1 hT2
    (R.exists_mulVec_ne_smul_of_not_hasCyclicSubgroup hP4) A

end EllipticCurveData

end

end Iut
