/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.CyclicTorsion
import Iut.Tripod.TwoAdic
import Iut.Anabelian.TateTorsion

/-!
# Local rank-one subgroups of the ℓ-torsion ([GenEll], Lemma 3.2(i))

Let `E/F` be an elliptic curve over a number field with mod-`ℓ` representation data `R`
(`ℓ` an odd prime), `K = F(E[ℓ])` its ℓ-torsion field, and `w` a place of `K` over a
multiplicative place `w₀` of `F` of odd residue characteristic, with Tate structure
`S_w : K_w^×/q^ℤ ≃ E(K_w)` (`ModEllRepData.tateFamilyOdd`). **[GenEll], Lemma 3.2(i)** says
that a `Gal(F̄/F)`-stable subgroup `H ⊆ E(F̄)` of order `ℓ` is the graph line `μ_ℓ` at `w`
as soon as `ℓ ∤ ord_{w₀}(q)`:

`ModEllRepData.comap_bcKR_eq_graphLineAt`: `H.comap (E(K) → E(F̄)) = graphLineAt w`.

## The proof

The proof avoids the Galois theory of the completion `K_w/F_{w₀}` and uses only the finite
Galois group `Gal(K/F)`, its decomposition group `D_w` (the stabilizer of the prime `𝔓_w`,
`MulAction.stabilizer`), and valuations:

1. `E(K)[ℓ]` has `ℓ²` elements and `Gal(K/F)` acts faithfully on it
   (`Iut.Tripod.CyclicTorsion`); the graph line `G = graphLineAt w` has `ℓ` elements and is
   `D_w`-stable, the canonical generators `±q^{1/ℓ}` are permuted by `D_w`
   (the equivariance fields of `Iut.TateFamily`).
2. If `H_K := H.comap bcK ≠ G`, then `E(K)[ℓ] = G ⊕ H_K` and `H_K` contains a canonical
   generator `b` (`exists_canonical_mem_of_ne`); for `σ ∈ D_w`, `σ b` is again canonical and
   lies in `H_K`, so `σ b = ±b` (`galK_eq_or_eq_neg_of_mem_stabilizer`).
3. Hence no element of `D_w` has order `ℓ`: such a `σ` would fix `G` (Fermat: `m^ℓ ≡ 1` forces
   `m ≡ 1`) and `b` (as `ℓ` is odd), hence all of `E(K)[ℓ]`, hence be trivial. By Cauchy's
   theorem `ℓ ∤ |D_w|` (`not_dvd_card_stabilizer_of_ne`).
4. `|D_w| = e(w/w₀) f(w/w₀)` (Mathlib, `Ideal.card_stabilizer_eq`), so `ℓ ∤ e(w/w₀)`.
5. But `E[ℓ] ⊆ E(K_w)` gives a unit `u ∈ K_w^×` with `u^ℓ = q^{1+ℓm}`
   (`Iut.TateStructure.exists_root_class`), and `ord_w(q) = e(w/w₀)·ord_{w₀}(q)` (from
   `‖j‖ = ‖q‖⁻¹` and `w(j) = w₀(j)^e`), so `ℓ ∣ e(w/w₀)·ord_{w₀}(q)`
   (`prime_dvd_ramificationIdx_mul_qOrder`) — a contradiction with `ℓ ∤ ord_{w₀}(q)`.

Step 5 is the well-known fact that the ℓ-torsion field is wildly ramified at `w₀` when
`ℓ ∤ ord_{w₀}(q)`; steps 2–4 replace the local statement "the extension class of
`0 → μ_ℓ → E[ℓ] → ℤ/ℓ → 0` is `q^{1/ℓ}`" of [GenEll] by a counting argument in `Gal(K/F)`.
-/

namespace Iut.EllipticCurveData.ModEllRepData

open WeierstrassCurve NumberField Iut Iut.Anabelian TateCurvesTheta
open scoped Classical Pointwise

universe u

noncomputable section

variable {C : EllipticCurveData.{u}} {ℓ : ℕ} (R : C.ModEllRepData ℓ)

attribute [local instance 1100] Iut.EllipticCurveData.ModEllRepData.instDecidableEqTorsionFieldR

/-! ### The local ℓ-torsion is rational over `K` -/

section Local

variable {VBad : Set (FinitePlace ↥(fieldOfModuli C.F C.E))}
  (TF : TateFamily C.E R.torsionField ℓ VBad)

/-- The map `E(K) → E(K_w)`. -/
abbrev toLocalR (w : FinitePlace ↥R.torsionField) :
    (curveK C.E R.torsionField).toAffine.Point →+
      (curveKw C.E R.torsionField w).toAffine.Point :=
  pointMap (curveK C.E R.torsionField) (emb R.torsionField w)

variable {w : FinitePlace ↥R.torsionField}

lemma toLocalR_mem_torsion {P : (curveK C.E R.torsionField).toAffine.Point} (hP : P ∈ R.TKR) :
    R.toLocalR w P ∈ TateStructure.torsion ℓ (curveKw C.E R.torsionField w) := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

lemma mem_TKR_of_toLocalR {P : (curveK C.E R.torsionField).toAffine.Point}
    (hP : R.toLocalR w P ∈ TateStructure.torsion ℓ (curveKw C.E R.torsionField w)) :
    P ∈ R.TKR := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul] at hP
  exact pointMap_injective _ _ (hP.trans (map_zero _).symm)

lemma card_map_toLocalR : Nat.card (R.TKR.map (R.toLocalR w)) = ℓ * ℓ := by
  rw [← pow_two, ← R.card_TKR]
  exact (Nat.card_congr (AddSubgroup.equivMapOfInjective _ _ (pointMap_injective _ _)).toEquiv).symm

variable (hw : IsBadPlace C.E R.torsionField VBad w)
include TF hw

/-- `ℓ² ≤ |E(K_w)[ℓ]|`. -/
lemma sq_le_card_torsionR [NeZero ℓ] :
    ℓ * ℓ ≤ Nat.card (TateStructure.torsion ℓ (curveKw C.E R.torsionField w)) := by
  haveI := (TF.S w hw).finite_torsion ℓ
  rw [← R.card_map_toLocalR (w := w)]
  exact AddSubgroup.card_le_of_le
    (AddSubgroup.map_le_iff_le_comap.mpr fun _ hP => R.toLocalR_mem_torsion hP)

/-- **The local ℓ-torsion is rational over `K`.** -/
lemma map_toLocalR_eq [NeZero ℓ] :
    R.TKR.map (R.toLocalR w) = TateStructure.torsion ℓ (curveKw C.E R.torsionField w) := by
  haveI := (TF.S w hw).finite_torsion ℓ
  refine AddSubgroup.eq_of_le_of_card_ge ?_ ?_
  · exact AddSubgroup.map_le_iff_le_comap.mpr fun _ hP => R.toLocalR_mem_torsion hP
  · rw [R.card_map_toLocalR]
    exact (TF.S w hw).card_torsion_le ℓ

lemma exists_toLocalR_eq [NeZero ℓ] {Q : (curveKw C.E R.torsionField w).toAffine.Point}
    (hQ : Q ∈ TateStructure.torsion ℓ (curveKw C.E R.torsionField w)) :
    ∃ P ∈ R.TKR, R.toLocalR w P = Q := by
  rw [← R.map_toLocalR_eq TF hw] at hQ
  exact hQ

/-- The graph line at `w` maps onto the graph line of the Tate structure. -/
lemma map_graphLineAtR [NeZero ℓ] :
    (TF.graphLineAt w hw).map (R.toLocalR w) = (TF.S w hw).graphLine ℓ := by
  ext Q
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact hP
  · intro hQ
    obtain ⟨P, -, rfl⟩ := R.exists_toLocalR_eq TF hw ((TF.S w hw).graphLine_le_torsion ℓ hQ)
    exact ⟨P, hQ, rfl⟩

/-- The graph line at `w` has `ℓ` elements. -/
lemma card_graphLineAtR [NeZero ℓ] : Nat.card (TF.graphLineAt w hw) = ℓ := by
  have h1 : Nat.card (TF.graphLineAt w hw) =
      Nat.card ((TF.graphLineAt w hw).map (R.toLocalR w)) :=
    Nat.card_congr (AddSubgroup.equivMapOfInjective _ _ (pointMap_injective _ _)).toEquiv
  rw [h1, R.map_graphLineAtR TF hw]
  exact (TF.S w hw).card_graphLine_eq ℓ (R.sq_le_card_torsionR TF hw)

/-- The graph line at `w` consists of ℓ-torsion points. -/
lemma graphLineAtR_le_TKR [NeZero ℓ] : TF.graphLineAt w hw ≤ R.TKR := fun _ hP =>
  R.mem_TKR_of_toLocalR ((TF.S w hw).graphLine_le_torsion ℓ hP)

/-- **The canonical generators at `w`** are the two cosets `±g + L_w` of an ℓ-torsion point
`g ∉ L_w`. -/
lemma exists_canonicalR [NeZero ℓ] [Fact (1 < ℓ)] :
    ∃ g ∈ R.TKR, g ∉ TF.graphLineAt w hw ∧
      ∀ P, TF.IsCanonicalAt w hw P ↔
        (P - g ∈ TF.graphLineAt w hw ∨ P + g ∈ TF.graphLineAt w hw) := by
  obtain ⟨u₁, m₁, hu₁⟩ := (TF.S w hw).exists_root_class ℓ (R.sq_le_card_torsionR TF hw)
  obtain ⟨g, hgT, hg⟩ := R.exists_toLocalR_eq TF hw ((TF.S w hw).ofUnit_mem_torsion ℓ hu₁)
  refine ⟨g, hgT, ?_, fun P => ?_⟩
  · intro h
    apply (TF.S w hw).ofUnit_not_mem_graphLine ℓ hu₁
    rw [← hg]
    exact h
  · unfold TateFamily.IsCanonicalAt
    rw [(TF.S w hw).isCanonical_iff ℓ hu₁, ← hg]
    unfold TateFamily.graphLineAt
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap, map_sub, map_add]

end Local

/-! ### The action of `Gal(K/F)` on `E(K)` -/

section GalK

variable (σ τ : ↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)

lemma galK_one_apply (P : (curveK C.E R.torsionField).toAffine.Point) :
    galK C.E R.torsionField 1 P = P := by
  cases P <;> rfl

lemma galK_mul_apply (P : (curveK C.E R.torsionField).toAffine.Point) :
    galK C.E R.torsionField (σ * τ) P =
      galK C.E R.torsionField σ (galK C.E R.torsionField τ P) := by
  cases P <;> rfl

/-- The iterates of `σ` on a point `a` with `σ a = m • a`. -/
lemma galK_pow_apply_of_zsmul {a : (curveK C.E R.torsionField).toAffine.Point} {m : ℤ}
    (h : galK C.E R.torsionField σ a = m • a) (n : ℕ) :
    galK C.E R.torsionField (σ ^ n) a = m ^ n • a := by
  induction n with
  | zero => rw [pow_zero, R.galK_one_apply, pow_zero, one_smul]
  | succ n ih =>
    rw [pow_succ, R.galK_mul_apply, h, map_zsmul, ih, smul_smul, pow_succ, mul_comm]

/-- The restriction of `σ ∈ Gal(F̄/F)` carries a `Gal(F̄/F)`-stable subgroup of `E(F̄)`,
pulled back to `E(K)`, to itself. -/
lemma galK_mem_comap_bcKR {H : AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar))}
    (hgal : ∀ σ : C.Fbar ≃ₐ[C.F] C.Fbar, ∀ P ∈ H, galPointMap C.F C.E C.Fbar σ P ∈ H)
    {P : (curveK C.E R.torsionField).toAffine.Point} (hP : P ∈ H.comap R.bcKR) :
    galK C.E R.torsionField σ P ∈ H.comap R.bcKR := by
  obtain ⟨τ, rfl⟩ := R.restrictKR_surjective σ
  rw [AddSubgroup.mem_comap, R.bcKR_galK]
  exact hgal τ _ hP

end GalK

end

end Iut.EllipticCurveData.ModEllRepData

/-! ### The decomposition group as the stabilizer of the prime -/

namespace Iut

open NumberField IsDedekindDomain
open scoped Pointwise

section Decomposition

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- The action of `Gal(K/k)` on `𝓞_K` through the restriction `galRestrict`. -/
noncomputable local instance instGalRingOfIntegersAction :
    MulSemiringAction (K ≃ₐ[k] K) (𝓞 K) :=
  IsIntegralClosure.MulSemiringAction (𝓞 k) k K (𝓞 K)

/-- `Gal(K/k)` is the Galois group of `𝓞_K/𝓞_k`. -/
noncomputable local instance instGalRingOfIntegersGaloisGroup :
    IsGaloisGroup (K ≃ₐ[k] K) (𝓞 k) (𝓞 K) :=
  IsGaloisGroup.of_isFractionRing (K ≃ₐ[k] K) (𝓞 k) (𝓞 K) k K

omit [IsGalois k K] in
/-- **An element of the decomposition group fixes the place**: if `σ` stabilizes the prime
`𝔓_w`, then `σ·w = w`. -/
theorem galPlace_eq_of_mem_stabilizer (σ : K ≃ₐ[k] K) (w : FinitePlace K)
    (hσ : σ ∈ MulAction.stabilizer (K ≃ₐ[k] K) w.maximalIdeal.asIdeal) : galPlace σ w = w := by
  rw [MulAction.mem_stabilizer_iff, Ideal.pointwise_smul_def] at hσ
  unfold galPlace
  conv_rhs => rw [← FinitePlace.mk_maximalIdeal w]
  congr 1
  ext1
  simp only [HeightOneSpectrum.comap_asIdeal]
  have hinv : galRestrictInt σ⁻¹ = (galRestrictInt σ).symm := by
    rw [galRestrictInt, galRestrictInt, map_inv, AlgEquiv.aut_inv]
  have h1 : Ideal.comap (galRestrictInt σ⁻¹ : 𝓞 K →+* 𝓞 K) w.maximalIdeal.asIdeal =
      Ideal.comap (galRestrictInt σ).toRingEquiv.symm w.maximalIdeal.asIdeal := by
    ext a
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.coe_coe, hinv]
    rfl
  have h2 : Ideal.map (galRestrictInt σ).toRingEquiv w.maximalIdeal.asIdeal =
      Ideal.map (MulSemiringAction.toRingHom (K ≃ₐ[k] K) (𝓞 K) σ) w.maximalIdeal.asIdeal := rfl
  rw [h1, Ideal.comap_symm, h2, hσ]

/-- **The ramification index divides the order of the decomposition group**:
`|D_w| = e(w/v)·f(w/v)` (`Ideal.card_stabilizer_eq`). -/
theorem ramificationIdx'_dvd_card_stabilizer {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) :
    v.maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal ∣
      Nat.card (MulAction.stabilizer (K ≃ₐ[k] K) w.maximalIdeal.asIdeal) := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  haveI : Finite (𝓞 k ⧸ v.maximalIdeal.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ v.maximalIdeal.ne_bot
  rw [Ideal.card_stabilizer_eq (G := K ≃ₐ[k] K) v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal
      (K ≃ₐ[k] K),
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal
      v.maximalIdeal.ne_bot]
  exact dvd_mul_right _ _

end Decomposition

end Iut

/-! ### Subgroups of prime order -/

namespace Iut

variable {X : Type*} [AddCommGroup X]

/-- Two distinct subgroups of prime order `p` intersect trivially. -/
lemma addSubgroup_inf_eq_bot_of_card_prime {p : ℕ} (hp : p.Prime) {A B : AddSubgroup X}
    (hA : Nat.card A = p) (hB : Nat.card B = p) (hne : A ≠ B) : A ⊓ B = ⊥ := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (hA ▸ hp.ne_zero)
  haveI : Finite B := Nat.finite_of_card_ne_zero (hB ▸ hp.ne_zero)
  have hdvd : Nat.card (A ⊓ B : AddSubgroup X) ∣ p := hA ▸ AddSubgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · exact AddSubgroup.card_eq_one.mp h1
  · exfalso
    apply hne
    have h1 : A ⊓ B = A := AddSubgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp', hA])
    have h2 : A ⊓ B = B := AddSubgroup.eq_of_le_of_card_ge inf_le_right (by rw [hp', hB])
    rw [← h1, h2]

/-- Two subgroups of order `p` of a group of order `p²` intersecting trivially generate it. -/
lemma addSubgroup_sup_eq_of_inf_eq_bot {p : ℕ} {A B T : AddSubgroup X} [Finite T]
    (hA : Nat.card A = p) (hB : Nat.card B = p) (hT : Nat.card T = p * p) (hAT : A ≤ T)
    (hBT : B ≤ T) (hinf : A ⊓ B = ⊥) : A ⊔ B = T := by
  refine AddSubgroup.eq_of_le_of_card_ge (sup_le hAT hBT) ?_
  rw [hT]
  haveI : Finite ↥(A ⊔ B) :=
    Finite.of_injective (AddSubgroup.inclusion (sup_le hAT hBT)) (AddSubgroup.inclusion_injective _)
  let f : A × B → ↥(A ⊔ B) := fun x => ⟨x.1 + x.2, AddSubgroup.add_mem_sup x.1.2 x.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : X) + b = a' + b' := congrArg Subtype.val h
    have hmem : (a : X) - a' ∈ A ⊓ B := by
      refine ⟨A.sub_mem a.2 a'.2, ?_⟩
      have : (a : X) - a' = b' - b := by
        rw [sub_eq_sub_iff_add_eq_add, h', add_comm]
      rw [this]
      exact B.sub_mem b'.2 b.2
    rw [hinf, AddSubgroup.mem_bot, sub_eq_zero] at hmem
    have hb : (b : X) = b' := by
      have := h'
      rw [hmem] at this
      exact add_left_cancel this
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hb)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, hA, hB] at this

/-- A nonzero element of a subgroup of prime order `p` has order `p`. -/
lemma addOrderOf_eq_of_mem_of_card_prime {p : ℕ} (hp : p.Prime) {A : AddSubgroup X}
    (hA : Nat.card A = p) {a : X} (ha : a ∈ A) (ha0 : a ≠ 0) : addOrderOf a = p := by
  have hdvd : addOrderOf a ∣ p := by
    have h := addOrderOf_dvd_natCard (⟨a, ha⟩ : A)
    rw [← AddSubgroup.addOrderOf_coe, hA] at h
    exact h
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) ha0
  · exact h

/-- A subgroup of prime order is generated by any nonzero element. -/
lemma zmultiples_eq_of_mem_of_card_prime {p : ℕ} (hp : p.Prime) {A : AddSubgroup X}
    (hA : Nat.card A = p) {a : X} (ha : a ∈ A) (ha0 : a ≠ 0) :
    AddSubgroup.zmultiples a = A := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (hA ▸ hp.ne_zero)
  refine AddSubgroup.eq_of_le_of_card_ge (AddSubgroup.zmultiples_le.mpr ha) ?_
  rw [Nat.card_zmultiples, addOrderOf_eq_of_mem_of_card_prime hp hA ha ha0, hA]

end Iut

/-! ### The main theorem -/

namespace Iut.EllipticCurveData.ModEllRepData

open WeierstrassCurve NumberField Iut Iut.Anabelian TateCurvesTheta IsDedekindDomain
open scoped Classical Pointwise

universe u

noncomputable section

variable {C : EllipticCurveData.{u}} {ℓ : ℕ} (R : C.ModEllRepData ℓ)

attribute [local instance 1100] Iut.EllipticCurveData.ModEllRepData.instDecidableEqTorsionFieldR
attribute [local instance] Iut.instGalRingOfIntegersAction Iut.instGalRingOfIntegersGaloisGroup

lemma graphLineAt_congrR {VBad : Set (FinitePlace ↥(fieldOfModuli C.F C.E))}
    (TF : TateFamily C.E R.torsionField ℓ VBad) {w w' : FinitePlace ↥R.torsionField} (h : w = w')
    (hw : IsBadPlace C.E R.torsionField VBad w) (hw' : IsBadPlace C.E R.torsionField VBad w') :
    TF.graphLineAt w hw = TF.graphLineAt w' hw' := by
  subst h
  rfl

lemma isCanonicalAt_congrR {VBad : Set (FinitePlace ↥(fieldOfModuli C.F C.E))}
    (TF : TateFamily C.E R.torsionField ℓ VBad) {w w' : FinitePlace ↥R.torsionField} (h : w = w')
    (hw : IsBadPlace C.E R.torsionField VBad w) (hw' : IsBadPlace C.E R.torsionField VBad w')
    (P : (curveK C.E R.torsionField).toAffine.Point) :
    TF.IsCanonicalAt w hw P ↔ TF.IsCanonicalAt w' hw' P := by
  subst h
  exact Iff.rfl

section Valuation

variable {VBad : Set (FinitePlace ↥(fieldOfModuli C.F C.E))}
  (TF : TateFamily C.E R.torsionField ℓ VBad) {w : FinitePlace ↥R.torsionField}
  (hw : IsBadPlace C.E R.torsionField VBad w)

/-- The `j`-invariant of the Tate curve of `E` over `K_w` is `j(E)`. -/
lemma tateJ_eq_emb :
    (TF.S w hw).t.tateJ = emb R.torsionField w (algebraMap C.F ↥R.torsionField C.E.j) := by
  set S := TF.S w hw
  have hu : (((S.C.u⁻¹ : (localCompletion w)ˣ)) : localCompletion w) ≠ 0 := Units.ne_zero _
  rw [S.t.tateJ_def, ← S.hC, variableChange_c₄, variableChange_Δ, mul_pow, ← pow_mul,
    show (4 * 3 : ℕ) = 12 from rfl, mul_div_mul_left _ _ (pow_ne_zero 12 hu)]
  simp only [curveKw, curveK, map_c₄, map_Δ]
  rw [← map_pow, ← map_pow, ← map_div₀, ← map_div₀, Iut.j_eq_inv_Δ_mul C.E, div_eq_inv_mul]

/-- **The valuation of the Tate parameter at `w`**: `ord_w(q) = e(w/w₀)·ord_{w₀}(q)`, from
`‖j‖ = ‖q‖⁻¹` and `w(j) = w₀(j)^{e(w/w₀)}`. -/
lemma valued_q_eq (hw₀ : (placeUnder w : FinitePlace C.F) ∈ C.badAll) :
    Valued.v ((TF.S w hw).t.q : localCompletion w) =
      WithZero.exp (-(((placeUnder (k := C.F) w).maximalIdeal.asIdeal.ramificationIdx'
        w.maximalIdeal.asIdeal : ℤ) * (C.tateInputs.qOrder (placeUnder w) hw₀ : ℤ))) := by
  set S := TF.S w hw
  have h12 : (12 : localCompletion w) ≠ 0 := twelve_ne_zero w
  have hq0 : (S.t.q : localCompletion w) ≠ 0 := S.t.q.ne_zero
  have h1 : ‖S.t.tateJ * (S.t.q : localCompletion w)‖ = 1 := by
    rw [norm_mul, S.t.norm_tateJ h12, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq0)]
  rw [norm_eq_one_iff_valued, map_mul, R.tateJ_eq_emb TF hw, FinitePlace.embedding_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    valuation_algebraMap_eq_pow (liesOver_placeUnder w), C.valuation_j_eq_exp_qOrder hw₀,
    ← WithZero.exp_nsmul] at h1
  rw [eq_inv_of_mul_eq_one_right h1, ← WithZero.exp_neg, nsmul_eq_mul]

include TF hw in
/-- **`ℓ ∣ e(w/w₀)·ord_{w₀}(q)`**: the ℓ-torsion field contains `q^{1/ℓ}`
(`Iut.TateStructure.exists_root_class`), whose valuation is `ord_w(q)/ℓ`. -/
lemma prime_dvd_ramificationIdx_mul_qOrder [NeZero ℓ]
    (hw₀ : (placeUnder w : FinitePlace C.F) ∈ C.badAll) :
    ℓ ∣ (placeUnder (k := C.F) w).maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal *
      C.tateInputs.qOrder (placeUnder w) hw₀ := by
  set S := TF.S w hw
  obtain ⟨u, m, hu⟩ := S.exists_root_class ℓ (R.sq_le_card_torsionR TF hw)
  have hv := congrArg (fun x : (localCompletion w)ˣ => Valued.v (x : localCompletion w)) hu
  simp only [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_pow, map_zpow₀] at hv
  have hu0 : Valued.v (u : localCompletion w) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  rw [← WithZero.exp_log hu0, R.valued_q_eq TF hw hw₀, ← WithZero.exp_nsmul,
    ← WithZero.exp_zsmul, WithZero.exp_inj, nsmul_eq_mul, zsmul_eq_mul, Int.cast_id] at hv
  set e : ℕ :=
    (placeUnder (k := C.F) w).maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal
  set h₀ : ℕ := C.tateInputs.qOrder (placeUnder w) hw₀
  have hdvd : (ℓ : ℤ) ∣ (e : ℤ) * h₀ := by
    refine ⟨-WithZero.log (Valued.v (u : localCompletion w)) - m * (e * h₀), ?_⟩
    linear_combination hv
  exact_mod_cast hdvd

end Valuation

section Main

variable {w : FinitePlace ↥R.torsionField}

/-- **No element of the decomposition group has order `ℓ`**, when `E(K)[ℓ] = ⟨a⟩ ⊕ ⟨b⟩` with
`⟨a⟩` stable under `D_w` and `D_w` acting on `b` by `±1`: such an element would fix `a` (by
Fermat's little theorem) and `b` (as `ℓ` is odd), hence all of `E(K)[ℓ]`, hence be trivial by
faithfulness. Hence `ℓ ∤ |D_w|` by Cauchy's theorem. -/
theorem not_dvd_card_stabilizer (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    {a b : (curveK C.E R.torsionField).toAffine.Point} (ha : addOrderOf a = ℓ)
    (hb : addOrderOf b = ℓ)
    (hsup : AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b = R.TKR)
    (hσa : ∀ σ ∈ MulAction.stabilizer (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)
      w.maximalIdeal.asIdeal, galK C.E R.torsionField σ a ∈ AddSubgroup.zmultiples a)
    (hσb : ∀ σ ∈ MulAction.stabilizer (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)
      w.maximalIdeal.asIdeal,
      galK C.E R.torsionField σ b = b ∨ galK C.E R.torsionField σ b = -b) :
    ¬ ℓ ∣ Nat.card (MulAction.stabilizer (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)
      w.maximalIdeal.asIdeal) := by
  intro hdvd
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨⟨σ, hσ⟩, hord⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hordσ : orderOf σ = ℓ := by
    rw [← Subgroup.orderOf_coe] at hord
    exact hord
  have hσℓ : σ ^ ℓ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hordσ] at this
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hordσ
    exact hℓ.one_lt.ne hordσ
  -- `σ` fixes `a`
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (hσa σ hσ)
  have hpow := R.galK_pow_apply_of_zsmul σ hm.symm ℓ
  rw [hσℓ, R.galK_one_apply] at hpow
  have h1 : (m ^ ℓ - 1) • a = 0 := by rw [sub_smul, one_smul, ← hpow, sub_self]
  have h2 : (ℓ : ℤ) ∣ m ^ ℓ - 1 := by
    have h2 : ((addOrderOf a : ℕ) : ℤ) ∣ m ^ ℓ - 1 := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h1
    rwa [ha] at h2
  have h3 : (ℓ : ℤ) ∣ m - 1 := by
    have h4 : ((m : ZMod ℓ)) ^ ℓ = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
      push_cast at this
      exact sub_eq_zero.mp this
    rw [ZMod.pow_card] at h4
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (m - 1) ℓ).mp ?_
    push_cast
    exact sub_eq_zero.mpr h4
  have hfixa : galK C.E R.torsionField σ a = a := by
    have h5 : (m - 1) • a = 0 := by
      have h3' : ((addOrderOf a : ℕ) : ℤ) ∣ m - 1 := by rwa [ha]
      exact addOrderOf_dvd_iff_zsmul_eq_zero.mp h3'
    rw [← hm]
    calc m • a = (m - 1) • a + a := by rw [sub_smul, one_smul, sub_add_cancel]
      _ = a := by rw [h5, zero_add]
  -- `σ` fixes `b`
  have hfixb : galK C.E R.torsionField σ b = b := by
    rcases hσb σ hσ with h | h
    · exact h
    · exfalso
      have hb' : galK C.E R.torsionField σ b = (-1 : ℤ) • b := by rw [h, neg_one_zsmul]
      have hpow := R.galK_pow_apply_of_zsmul σ hb' ℓ
      rw [hσℓ, R.galK_one_apply, Odd.neg_one_pow (hℓ.odd_of_ne_two hodd), neg_one_zsmul] at hpow
      have h2b : (2 : ℤ) • b = 0 := by
        rw [two_zsmul]
        nth_rewrite 2 [hpow]
        exact add_neg_cancel b
      have h6 : (ℓ : ℤ) ∣ 2 := by
        have h6 : ((addOrderOf b : ℕ) : ℤ) ∣ 2 := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h2b
        rwa [hb] at h6
      have h7 : ℓ ∣ 2 := by exact_mod_cast h6
      have := Nat.le_of_dvd two_pos h7
      have := hℓ.two_le
      omega
  -- `σ` fixes `E(K)[ℓ]`
  have hfix : ∀ P ∈ R.TKR, galK C.E R.torsionField σ P = P := by
    intro P hP
    rw [← hsup] at hP
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hP
    obtain ⟨i, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
    rw [map_add, map_zsmul, map_zsmul, hfixa, hfixb]
  exact hσ1 (R.eq_one_of_forall_galK_eq σ hfix)

variable (TF : TateFamily C.E R.torsionField ℓ C.VBadOdd)
  (hw : IsBadPlace C.E R.torsionField C.VBadOdd w)

/-- **[GenEll], Lemma 3.2(i)**: a `Gal(F̄/F)`-stable subgroup `H ⊆ E(F̄)` of order `ℓ` is
the graph line `μ_ℓ ⊆ E[ℓ]` at every place `w` of the ℓ-torsion field over a multiplicative
place `w₀` of `F` of odd residue characteristic with `ℓ ∤ ord_{w₀}(q)`. -/
theorem comap_bcKR_eq_graphLineAt (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    {H : AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar))} (hH : Nat.card H = ℓ)
    (hgal : ∀ σ : C.Fbar ≃ₐ[C.F] C.Fbar, ∀ P ∈ H, galPointMap C.F C.E C.Fbar σ P ∈ H)
    (hP2 : ¬ ℓ ∣ C.tateInputs.qOrder (placeUnder w)
      (C.placeUnder_mem_badAll_of_isBadPlace R.torsionField hw)) :
    H.comap R.bcKR = TF.graphLineAt w hw := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fact (1 < ℓ) := ⟨hℓ.one_lt⟩
  haveI : Finite R.TKR :=
    Nat.finite_of_card_ne_zero (by rw [R.card_TKR]; exact pow_ne_zero 2 hℓ.ne_zero)
  set hw₀ := C.placeUnder_mem_badAll_of_isBadPlace R.torsionField hw
  set HK := H.comap R.bcKR with hHK
  set G := TF.graphLineAt w hw with hG
  -- the cardinalities
  have hHle : H ≤ R.TFbarR := le_torsionBy_of_card_eq hH
  have hHKle : HK ≤ R.TKR := fun P hP => R.mem_TKR_of_bcKR (hHle hP)
  have hcardHK : Nat.card HK = ℓ := by
    have hrange : H ≤ R.bcKR.range := fun Q hQ => by
      obtain ⟨P, hP⟩ := R.exists_bcKR_eq Q (hHle hQ)
      exact ⟨P, hP⟩
    have hmap : HK.map R.bcKR = H := by
      rw [hHK, AddSubgroup.map_comap_eq, inf_eq_right.mpr hrange]
    rw [Nat.card_congr (AddSubgroup.equivMapOfInjective _ _ R.bcKR_injective).toEquiv, hmap, hH]
  have hcardG : Nat.card G = ℓ := R.card_graphLineAtR TF hw
  have hGle : G ≤ R.TKR := R.graphLineAtR_le_TKR TF hw
  by_contra hne
  have hne' : G ≠ HK := fun h => hne h.symm
  have hinf : G ⊓ HK = ⊥ := addSubgroup_inf_eq_bot_of_card_prime hℓ hcardG hcardHK hne'
  have hsup : G ⊔ HK = R.TKR :=
    addSubgroup_sup_eq_of_inf_eq_bot hcardG hcardHK (by rw [R.card_TKR, sq]) hGle hHKle hinf
  -- a canonical generator `b ∈ H_K`
  obtain ⟨g, hgT, hgG, hgcan⟩ := R.exists_canonicalR TF hw
  have hg' : g ∈ G ⊔ HK := hsup ▸ hgT
  obtain ⟨a, haG, b, hbHK, hab⟩ := AddSubgroup.mem_sup.mp hg'
  have hbg : b - g ∈ G := by
    rw [← hab, sub_add_cancel_right]
    exact G.neg_mem haG
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [add_zero] at hab
    exact hgG (hab ▸ haG)
  -- a generator `a₀` of the graph line
  have hGbot : G ≠ ⊥ := fun h => by
    rw [h, AddSubgroup.card_bot] at hcardG
    exact hℓ.one_lt.ne hcardG
  obtain ⟨⟨a₀, ha₀G⟩, ha₀⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hGbot
  have ha₀0 : a₀ ≠ 0 := fun h => ha₀ (Subtype.ext h)
  have hza : AddSubgroup.zmultiples a₀ = G := zmultiples_eq_of_mem_of_card_prime hℓ hcardG ha₀G ha₀0
  have hzb : AddSubgroup.zmultiples b = HK := zmultiples_eq_of_mem_of_card_prime hℓ hcardHK hbHK hb0
  -- the decomposition group acts on `G` and on `b` by `±1`
  have hσG : ∀ σ ∈ MulAction.stabilizer (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)
      w.maximalIdeal.asIdeal, G.map (galK C.E R.torsionField σ) = G := by
    intro σ hσ
    have hfix := galPlace_eq_of_mem_stabilizer σ w hσ
    have h := TF.graphLine_galPlace w hw σ
    change TF.graphLineAt (galPlace σ w) _ = G.map _ at h
    rw [R.graphLineAt_congrR TF hfix] at h
    exact h.symm
  have hσa : ∀ σ ∈ MulAction.stabilizer (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)
      w.maximalIdeal.asIdeal, galK C.E R.torsionField σ a₀ ∈ AddSubgroup.zmultiples a₀ := by
    intro σ hσ
    rw [hza, ← hσG σ hσ]
    exact AddSubgroup.mem_map_of_mem _ ha₀G
  have hσb : ∀ σ ∈ MulAction.stabilizer (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)
      w.maximalIdeal.asIdeal,
      galK C.E R.torsionField σ b = b ∨ galK C.E R.torsionField σ b = -b := by
    intro σ hσ
    have hfix := galPlace_eq_of_mem_stabilizer σ w hσ
    have hcanb : TF.IsCanonicalAt w hw b := (hgcan b).mpr (Or.inl hbg)
    have hcan : TF.IsCanonicalAt w hw (galK C.E R.torsionField σ b) := by
      have h := TF.isCanonical_galPlace w hw σ b
      change TF.IsCanonicalAt (galPlace σ w) _ _ ↔ TF.IsCanonicalAt w hw b at h
      rw [R.isCanonicalAt_congrR TF hfix] at h
      exact h.mpr hcanb
    have hσbHK : galK C.E R.torsionField σ b ∈ HK := R.galK_mem_comap_bcKR σ hgal hbHK
    rcases (hgcan _).mp hcan with h | h
    · left
      have hmem : galK C.E R.torsionField σ b - b ∈ G ⊓ HK := by
        refine ⟨?_, HK.sub_mem hσbHK hbHK⟩
        have := G.sub_mem h hbg
        rwa [sub_sub_sub_cancel_right] at this
      rw [hinf, AddSubgroup.mem_bot, sub_eq_zero] at hmem
      exact hmem
    · right
      have hmem : galK C.E R.torsionField σ b + b ∈ G ⊓ HK := by
        refine ⟨?_, HK.add_mem hσbHK hbHK⟩
        have := G.add_mem h hbg
        rwa [add_add_sub_cancel] at this
      rw [hinf, AddSubgroup.mem_bot, add_eq_zero_iff_eq_neg] at hmem
      exact hmem
  -- `ℓ ∤ |D_w|`, but `ℓ ∣ e(w/w₀)` and `e(w/w₀) ∣ |D_w|`
  have hnot := R.not_dvd_card_stabilizer hℓ hodd
    (addOrderOf_eq_of_mem_of_card_prime hℓ hcardG ha₀G ha₀0)
    (addOrderOf_eq_of_mem_of_card_prime hℓ hcardHK hbHK hb0) (by rw [hza, hzb, hsup]) hσa hσb
  have hdvd := R.prime_dvd_ramificationIdx_mul_qOrder TF hw hw₀
  rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with he | hh
  · exact hnot (he.trans (ramificationIdx'_dvd_card_stabilizer (liesOver_placeUnder w)))
  · exact hP2 hh

end Main

end

end Iut.EllipticCurveData.ModEllRepData
