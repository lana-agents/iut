/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GlobalPrime
import Iut.Frobenioid.GlobalNonRlf

/-!
# Primes of the non-realified global Frobenioid: `Prime(Φ(F)) ≅ V(F)` ([FrdI], Example 6.3)

[FrdI], Example 6.3 (l.6281–6284): "for each finite extension `L ⊆ F̃` of `F`, one verifies
immediately that `Φ(L) ≠ 0` is perf-factorial, that there is a natural bijection
`Prime(Φ(L)) ≅ V(L)`, and that the supports of elements of `Φ(L)` are precisely the finite
subsets of `V(L)`". `GlobalPrime.lean` proves `Prime ≅ V` for the realification `Φ^rlf`
(IUT I, Example 3.5(i)); here the same is done for the divisor monoid `Φ(F) = ⊕_v ord(O^▷_v)` of
the Frobenioid `C_F = GlobalFrobenioid F` of Example 6.3 itself (`ℤ_{≥0}` at finite places), and
compared with the realification ([FrdI] §0: `Prime(M) ≅ Prime(M^pf)`):

* `GlobalFrobenioid.preceqZ_iff`: `a ≼ b` in `Φ(F)` iff `a ≼ b` in `Φ^rlf(F)` (via
  `castDiv : Φ^gp → (Φ^rlf)^gp`), i.e. iff `supp a ⊆ supp b`;
* `GlobalFrobenioid.isPrimaryZ_iff`: `a` is primary iff it is supported at a single place;
* **`GlobalFrobenioid.primeEquivZ : PrimeZ F ≃ Place F`**;
* **`GlobalFrobenioid.primeRlf`**, **`primeEquiv_primeRlf`**: realification `a ↦ castDiv a`
  induces `Prime(Φ) → Prime(Φ^rlf)`, compatible with the two bijections with `V(F)` (so it is a
  bijection, as in [FrdI] §0);
* `GlobalFrobenioid.supp_finite`, `exists_supp_eq`: supports are exactly the finite sets of places.
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

open NumberField GlobalRealified

universe u

namespace GlobalFrobenioid

attribute [local instance] Classical.propDecidable

variable {K : Type u} [Field K] [NumberField K]

/-- `a ≼ b` in the divisor monoid `Φ(F)` of [FrdI], Example 6.3. -/
abbrev PreceqZ (a b : ArithDivZ K) : Prop := (phiZ K).preceq (A := pt) a b

lemma castDiv_nsmul (n : ℕ) (x : ArithDivZ K) : castDiv K (n • x) = n • castDiv K x :=
  map_nsmul _ _ _

/-- **`≼` in `Φ(F)` is `≼` in `Φ^rlf(F)`.** -/
theorem preceqZ_iff_cast (a b : ArithDivZ K) :
    PreceqZ a b ↔ Preceq (castDiv K a) (castDiv K b) := by
  constructor
  · rintro ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    change n • castDiv K b - castDiv K a ∈ effCone K
    rw [← castDiv_nsmul, ← map_sub, castDiv_mem_iff]
    exact h
  · rintro ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    change n • b - a ∈ effConeZ K
    rw [← castDiv_mem_iff, map_sub, castDiv_nsmul]
    exact h

/-- **`a ≼ b` iff `supp a ⊆ supp b`** in `Φ(F)`. -/
theorem preceqZ_iff {a b : ArithDivZ K} (ha : a ∈ effConeZ K) (hb : b ∈ effConeZ K) :
    PreceqZ a b ↔ supp (castDiv K a) ⊆ supp (castDiv K b) :=
  (preceqZ_iff_cast a b).trans
    (preceq_iff (castDiv_mem_iff.mpr ha) (castDiv_mem_iff.mpr hb))

/-- The divisor `t·[p]` with `t ∈ ℤ` at a finite place (`t` is cast to `ℝ` at an infinite one). -/
noncomputable def singleZ : Place K → ℤ → ArithDivZ K
  | Sum.inl w, t => (Finsupp.single w t, 0)
  | Sum.inr v, t => (0, Pi.single v (t : ℝ))

/-- The restriction of `a` to the place `p`. -/
noncomputable def restrictZ (a : ArithDivZ K) : Place K → ArithDivZ K
  | Sum.inl w => (Finsupp.single w (a.1 w), 0)
  | Sum.inr v => (0, Pi.single v (a.2 v))

lemma castDiv_singleZ (p : Place K) (t : ℤ) : castDiv K (singleZ p t) = single p t := by
  cases p with
  | inl w => exact Prod.ext (by simp [singleZ, single, castDiv, Finsupp.mapRange_single]) rfl
  | inr v => exact Prod.ext (by simp [singleZ, single, castDiv]) rfl

lemma castDiv_restrictZ (a : ArithDivZ K) (p : Place K) :
    castDiv K (restrictZ a p) = single p (coord (castDiv K a) p) := by
  cases p with
  | inl w => exact Prod.ext (by simp [restrictZ, single, castDiv, Finsupp.mapRange_single]) rfl
  | inr v => exact Prod.ext (by simp [restrictZ, single, castDiv]) rfl

lemma ne_zero_of_coord {a : ArithDivZ K} {p : Place K} (h : coord (castDiv K a) p ≠ 0) :
    a ≠ 0 := by
  rintro rfl
  simp at h

/-- **Primary elements of `Φ(F)` are those supported at a single place.** -/
theorem isPrimaryZ_iff {a : ArithDivZ K} (ha : a ∈ effConeZ K) :
    (phiZ K).IsPrimary (A := pt) a ↔ ∃ p, supp (castDiv K a) = {p} := by
  have hac := castDiv_mem_iff.mpr ha
  constructor
  · rintro ⟨-, ha0, hp⟩
    obtain ⟨p, hp0⟩ : ∃ p, coord (castDiv K a) p ≠ 0 := by
      by_contra h
      simp only [not_exists, ne_eq, not_not] at h
      exact ha0 (castDiv_injective (eq_iff_coord.mpr fun p => by rw [h p, map_zero,
        coord_zero]))
    have hb : restrictZ a p ∈ effConeZ K := by
      rw [← castDiv_mem_iff, castDiv_restrictZ]
      exact single_mem ((mem_effCone_iff_coord.mp hac) p)
    have hbc : castDiv K (restrictZ a p) ∈ effCone K := castDiv_mem_iff.mpr hb
    have hs : supp (castDiv K (restrictZ a p)) = {p} := by
      rw [castDiv_restrictZ]; exact supp_single hp0
    have hb0 : restrictZ a p ≠ 0 := by
      intro h
      have := congrArg (castDiv K) h
      rw [map_zero, castDiv_restrictZ] at this
      have h2 := congrArg (fun x => coord x p) this
      simp only [coord_single, coord_zero] at h2
      exact hp0 h2
    have h1 : PreceqZ (restrictZ a p) a :=
      (preceqZ_iff hb ha).mpr (by rw [hs]; simpa [supp] using hp0)
    have h2 := (preceqZ_iff ha hb).mp (hp _ hb hb0 h1)
    rw [hs] at h2
    exact ⟨p, Set.Subset.antisymm h2 (by simpa [supp] using hp0)⟩
  · rintro ⟨p, hp⟩
    have hp0 : coord (castDiv K a) p ≠ 0 := by
      have : p ∈ supp (castDiv K a) := hp ▸ rfl
      exact this
    refine ⟨ha, ne_zero_of_coord hp0, fun b hb hb0 hba => ?_⟩
    have h1 := (preceqZ_iff hb ha).mp hba
    rw [hp] at h1
    obtain ⟨q, hq⟩ : ∃ q, coord (castDiv K b) q ≠ 0 := by
      by_contra h
      simp only [not_exists, ne_eq, not_not] at h
      exact hb0 (castDiv_injective (eq_iff_coord.mpr fun q => by rw [h q, map_zero,
        coord_zero]))
    have hqp : q = p := h1 hq
    refine (preceqZ_iff ha hb).mpr ?_
    rw [hp]
    intro r hr
    rw [Set.mem_singleton_iff.mp hr, ← hqp]
    exact hq

/-- Primary elements of `Φ(F)` are primary in `Φ^rlf(F)`. -/
lemma isPrimary_castDiv {a : ArithDivZ K} (h : (phiZ K).IsPrimary (A := pt) a) :
    (phiRlf K).IsPrimary (A := pt) (castDiv K a) :=
  (isPrimary_iff (castDiv_mem_iff.mpr h.1)).mpr ((isPrimaryZ_iff h.1).mp h)

/-- The primary element `[p]` of `Φ(F)`. -/
lemma singleZ_one_isPrimary (p : Place K) : (phiZ K).IsPrimary (A := pt) (singleZ p 1) := by
  have hm : singleZ p 1 ∈ effConeZ K := by
    rw [← castDiv_mem_iff, castDiv_singleZ]
    exact single_mem (by norm_num)
  refine (isPrimaryZ_iff hm).mpr ⟨p, ?_⟩
  rw [castDiv_singleZ]
  exact supp_single (by norm_num)

/-- The primary elements of `Φ(F)`. -/
def PrimaryZ (K : Type u) [Field K] [NumberField K] : Type u :=
  {a : ArithDivZ K // (phiZ K).IsPrimary (A := pt) a}

/-- `≼`-equivalence on primary elements of `Φ(F)`. -/
def primarySetoidZ : Setoid (PrimaryZ K) where
  r a b := PreceqZ a.1 b.1 ∧ PreceqZ b.1 a.1
  iseqv := by
    refine ⟨fun a => ?_, fun h => ⟨h.2, h.1⟩, fun h₁ h₂ => ?_⟩
    · have := (preceqZ_iff a.2.1 a.2.1).mpr subset_rfl
      exact ⟨this, this⟩
    · rename_i a b c
      exact ⟨(preceqZ_iff a.2.1 c.2.1).mpr (((preceqZ_iff a.2.1 b.2.1).mp h₁.1).trans
          ((preceqZ_iff b.2.1 c.2.1).mp h₂.1)),
        (preceqZ_iff c.2.1 a.2.1).mpr (((preceqZ_iff c.2.1 b.2.1).mp h₂.2).trans
          ((preceqZ_iff b.2.1 a.2.1).mp h₁.2))⟩

/-- **`Prime(Φ(F))`** ([FrdI] §0). -/
def PrimeZ (K : Type u) [Field K] [NumberField K] : Type u :=
  Quotient (primarySetoidZ (K := K))

/-- The realification map on primes `Prime(Φ) → Prime(Φ^rlf)`, `[a] ↦ [castDiv a]`. -/
noncomputable def primeRlf : PrimeZ K → GlobalRealified.Prime K :=
  Quotient.map (fun a => ⟨castDiv K a.1, isPrimary_castDiv a.2⟩) fun _ _ h =>
    ⟨(preceqZ_iff_cast _ _).mp h.1, (preceqZ_iff_cast _ _).mp h.2⟩

/-- **`Prime(Φ(F)) ≅ V(F)`** ([FrdI], Example 6.3), as the composite of the realification map
`Prime(Φ) → Prime(Φ^rlf)` with `Prime(Φ^rlf) ≅ V(F)` (`GlobalRealified.primeEquiv`). -/
noncomputable def primeEquivZ : PrimeZ K ≃ Place K where
  toFun x := GlobalRealified.primeEquiv (primeRlf x)
  invFun p := Quotient.mk _ ⟨singleZ p 1, singleZ_one_isPrimary p⟩
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h a =>
      refine Quotient.sound ?_
      have hp : supp (castDiv K a.1) =
          {GlobalRealified.primeEquiv (primeRlf (Quotient.mk _ a))} :=
        supp_eq_placeOf ⟨castDiv K a.1, isPrimary_castDiv a.2⟩
      have hs : supp (castDiv K (singleZ (GlobalRealified.primeEquiv
          (primeRlf (Quotient.mk _ a))) 1)) =
          {GlobalRealified.primeEquiv (primeRlf (Quotient.mk _ a))} := by
        rw [castDiv_singleZ]; exact supp_single (by norm_num)
      exact ⟨(preceqZ_iff (singleZ_one_isPrimary _).1 a.2.1).mpr (by rw [hs, hp]),
        (preceqZ_iff a.2.1 (singleZ_one_isPrimary _).1).mpr (by rw [hs, hp])⟩
  right_inv p := by
    have h := supp_eq_placeOf ⟨castDiv K (singleZ p 1), isPrimary_castDiv
      (singleZ_one_isPrimary p)⟩
    have h' : supp (castDiv K (singleZ p 1)) = {p} := by
      rw [castDiv_singleZ]; exact supp_single (by norm_num)
    change supp (castDiv K (singleZ p 1)) = _ at h
    rw [h'] at h
    exact (Set.singleton_eq_singleton_iff.mp h).symm

/-- **Compatibility with the realification**: `Prime(Φ) → Prime(Φ^rlf)` followed by
`Prime(Φ^rlf) ≅ V(F)` is `Prime(Φ) ≅ V(F)`; in particular `primeRlf` is a bijection. -/
theorem primeEquiv_primeRlf (x : PrimeZ K) :
    GlobalRealified.primeEquiv (primeRlf x) = primeEquivZ x := rfl

lemma primeRlf_bijective : Function.Bijective (primeRlf (K := K)) := by
  have : primeRlf (K := K) = GlobalRealified.primeEquiv.symm ∘ primeEquivZ := by
    funext x
    simp only [Function.comp_apply, ← primeEquiv_primeRlf, Equiv.symm_apply_apply]
  rw [this]
  exact GlobalRealified.primeEquiv.symm.bijective.comp primeEquivZ.bijective

/-- **Supports of elements of `Φ(F)` are finite** ([FrdI], Example 6.3). -/
theorem supp_finite (a : ArithDivZ K) : (supp (castDiv K a)).Finite :=
  (suppFinset (castDiv K a)).finite_toSet.subset fun _ hp => mem_suppFinset hp

/-- **Every finite set of places is the support of an element of `Φ(F)`** ([FrdI], Example 6.3:
"the supports of elements of `Φ(L)` are precisely the finite subsets of `V(L)`"). -/
theorem exists_supp_eq (S : Finset (GlobalRealified.Place K)) :
    ∃ a ∈ effConeZ K, supp (castDiv K a) = (S : Set (GlobalRealified.Place K)) := by
  refine ⟨∑ p ∈ S, singleZ p 1, ?_, ?_⟩
  · exact (effConeZ K).sum_mem fun p _ => (singleZ_one_isPrimary p).1
  · ext q
    simp only [supp, Set.mem_setOf_eq, map_sum, castDiv_singleZ, Finset.mem_coe]
    have : coord (∑ p ∈ S, single p ((1 : ℤ) : ℝ)) q = if q ∈ S then 1 else 0 := by
      induction S using Finset.induction_on with
      | empty => simp
      | insert p S hp ih =>
        rw [Finset.sum_insert hp, coord_add, ih, coord_single]
        by_cases hq : q = p
        · subst hq; simp [Finset.mem_insert, hp]
        · simp [Finset.mem_insert, hq]
    rw [this]
    split_ifs with h <;> simp [h]

end GlobalFrobenioid

end Frobenioid

end Iut
