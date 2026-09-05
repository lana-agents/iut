/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Implication.Corollary22
import Genl.GeneralPosition.TheoremTwoOne

/-!
# IUT IV, Corollary 2.3 and the implication to ABC (taxis #1449, #1455)

**Corollary 2.3 (Diophantine inequalities).** For every hyperbolic curve `U_X = X ∖ D`
over a number field, `d ≥ 1` and `ε > 0`,
`ht_{ω_X(D)} ≲ (1 + ε)·(log-diff_X + log-cond_D)` on `U_X(ℚ̄)^{≤d}` — the ABC target
`Iut.ABC T`.

The proof follows IUT IV: by [GenEll], Theorem 2.1 (proved in genl relative to a height
formalism and its proof package, taxis #2) it suffices to prove statement (ii) of that
theorem, the inequality for the tripod on `K_V ∩ U_X(ℚ̄)^{≤d}` for every compactly bounded
subset `K_V` (with support containing `2`). Statement (ii) follows from Corollary 2.2:
outside a finite exceptional set (the Northcott set of points of height below the
threshold together with the four exceptional `j`-invariants) the inequality (C2) holds
with `ε_E ≤ ε`, and by Corollary 2.2(i) `ht_{ω_X(D)} ≈ (1/6)·log(q_∀)`; a finite set
contributes only a bounded discrepancy.

## The main theorem

`Iut.cor312Variant_implies_abc`: **the Corollary 3.12 variant implies ABC**. Its inputs,
all explicit:

* `h312`: the Corollary 3.12 variant for all data bundles — the only IUT I–III input;
* `A`: genl's proof package for [GenEll], Theorem 2.1 (coverings, noncritical Belyi maps);
* `I`: the standard height-theoretic inputs of Corollary 2.2 for every `K_V` and `d`;
* `ex`: the existence of suitable initial Θ-data (the anabelian construction (P7));
* `cheb`, `pnt`: the prime-number-theorem inputs.
-/

namespace Iut

universe u v

open Finset Real

/-- Any bounded-discrepancy inequality holds on a finite set. -/
lemma DiscrepancyLE.of_finite {α : Type*} {f g : α → ℝ} {s : Set α} (hs : s.Finite) :
    f ≲[s] g := by
  obtain ⟨C, hC⟩ := (hs.image fun x => f x - g x).bddAbove
  exact ⟨C, fun x hx => by linarith [hC (Set.mem_image_of_mem _ hx)]⟩

variable {T : Genl.HeightTheory}
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- **Corollary 2.3, statement (ii) of [GenEll], Theorem 2.1**: for every compactly
bounded subset `K` of the tripod, every `d` and every `ε > 0`, the inequality
`ht_{ω_ℙ(C)} ≲ (1 + ε)·(log-diff_ℙ + log-cond_C)` holds on `K ∩ U_ℙ(ℚ̄)^{≤d}`. -/
theorem statementII_of_cor312 {P : Corollary312VariantData.{u, v} AG TG → Prop}
    (I : ∀ (K : T.CBS) (d : ℕ), Corollary22Inputs T K d)
    (ex : ∀ K d, ThetaDataExistence P (I K d))
    (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ X : Corollary312VariantData.{u, v} AG TG, P X → Corollary312Variant X) :
    T.StatementII := by
  intro d ε hε K
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · rw [hd0, T.ptLE_zero, Set.inter_empty]
    exact DiscrepancyLE.empty
  set S := T.cbsSet K ∩ T.ptLE T.tripod d with hS
  set Id := I K d with hId
  -- the threshold and the finite exceptional set
  have hδ1 : (1 : ℝ) ≤ deltaBound d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    unfold deltaBound; linarith
  set H : ℝ := max (Id.threshold cheb)
    (max (((60 * deltaBound d) ^ 2 * (2 * deltaBound d + 4) / ε) ^ 4) 1) with hH
  set Exc : Set (T.Pt T.tripod) :=
    (Id.excCore ∩ S) ∪ {x | x ∈ S ∧ Id.h x ≤ H} with hExc
  have hExc_fin : Exc.Finite := Id.excCore_finite.union (Id.northcott H)
  -- on `S ∖ Exc`, Corollary 2.2 gives the inequality with a uniform number
  have hgood : Id.h ≲[S \ Exc]
      (6 * (1 + ε)) • (T.logDiff T.tripod + T.logCond T.tripod) := by
    refine ⟨6 * (40 * pnt.η + Id.B / 3), fun x hx => ?_⟩
    obtain ⟨hxS, hxE⟩ := hx
    have hxe : x ∉ Id.excCore := fun h => hxE (Or.inl ⟨h, hxS⟩)
    have hxH : H < Id.h x := by
      by_contra hle
      exact hxE (Or.inr ⟨hxS, not_lt.mp hle⟩)
    have hth : Id.threshold cheb ≤ Id.h x := (le_max_left _ _).trans hxH.le
    obtain ⟨hc2, _, hnn⟩ := Id.c2 hd (ex K d) cheb pnt h312 x hxS hxe hth
    have hεE : epsilonE (deltaBound d) (Id.h x) ≤ ε := by
      apply epsilonE_le hδ1 hε
      · exact ((le_max_left _ _).trans (le_max_right _ _)).trans hxH.le
      · exact ((le_max_right _ _).trans (le_max_right _ _)).trans hxH.le
    have : (1 + epsilonE (deltaBound d) (Id.h x)) *
        (T.logDiff T.tripod x + T.logCond T.tripod x) ≤
        (1 + ε) * (T.logDiff T.tripod x + T.logCond T.tripod x) :=
      mul_le_mul_of_nonneg_right (by linarith) hnn
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linarith
  -- `ht ≲ (1/6)·h` on `K`, hence on `S ∖ Exc`
  have hht : T.htCan T.tripod ≲[S \ Exc] (1 / 6 : ℝ) • Id.h :=
    (Id.htCan_equiv.ge).mono fun x hx => hx.1.1
  have hcomb : T.htCan T.tripod ≲[S \ Exc]
      (1 + ε) • (T.logDiff T.tripod + T.logCond T.tripod) := by
    refine hht.trans ?_
    have := hgood.smul (by norm_num : (0 : ℝ) ≤ 1 / 6)
    rw [smul_smul, show (1 / 6 : ℝ) * (6 * (1 + ε)) = 1 + ε by ring] at this
    exact this
  -- combine with the finite exceptional set
  have hsub : S ⊆ (S \ Exc) ∪ Exc := fun x hx => by
    by_cases h : x ∈ Exc
    · exact Or.inr h
    · exact Or.inl ⟨hx, h⟩
  exact (hcomb.union (DiscrepancyLE.of_finite hExc_fin)).mono hsub

/-- **The Corollary 3.12 variant implies ABC** (IUT IV, Corollary 2.3 = [GenEll],
Theorem 2.1(i)), for every height formalism `T` equipped with its proof package and the
standard inputs of Corollary 2.2, given the existence of suitable initial Θ-data (with
data bundles satisfying `P`) and the prime-number-theorem inputs. The only IUT I–III input
is `h312`, the variant for the data bundles satisfying `P`. -/
theorem cor312Variant_implies_abc {P : Corollary312VariantData.{u, v} AG TG → Prop}
    (A : T.ProofPackage) (I : ∀ (K : T.CBS) (d : ℕ), Corollary22Inputs T K d)
    (ex : ∀ K d, ThetaDataExistence P (I K d))
    (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ X : Corollary312VariantData.{u, v} AG TG, P X → Corollary312Variant X) :
    ABC T :=
  T.statementII_implies_statementI A (statementII_of_cor312 I ex cheb pnt h312)

/-- The unrestricted form: the variant for all data bundles implies ABC. -/
theorem cor312Variant_implies_abc' (A : T.ProofPackage)
    (I : ∀ (K : T.CBS) (d : ℕ), Corollary22Inputs T K d)
    (ex : ∀ K d, ThetaDataExistence (fun _ : Corollary312VariantData.{u, v} AG TG => True) (I K d))
    (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ X : Corollary312VariantData.{u, v} AG TG, Corollary312Variant X) :
    ABC T :=
  cor312Variant_implies_abc A I ex cheb pnt fun X _ => h312 X

end Iut
