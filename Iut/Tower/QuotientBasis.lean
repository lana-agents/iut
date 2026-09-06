/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib

/-!
# Bases and traces modulo an ideal, and adic completeness of nilpotent ideals

Tools for the bound on the different (IUT IV, Proposition 1.3):

* `Iut.basisQuotientMap`: a basis of a free `R`-algebra `S` induces a basis of `S/IS` over
  `R/I`, for any ideal `I` of `R` (Mathlib's `IsLocalRing.basisQuotient` is the case of the
  maximal ideal of a local ring);
* `Iut.trace_quotient_mk_map`: `Tr_{(S/IS)/(R/I)}(x mod IS) = Tr_{S/R}(x) mod I`;
* `Iut.isAdicComplete_of_pow_eq_bot`: a ring is `I`-adically complete for a nilpotent
  ideal `I` (so that Hensel's lemma applies to `B/𝔓^N`).
-/

namespace Iut

open Module

section QuotientBasis

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The coordinates of an element of `I·S` lie in `I`. -/
lemma repr_mem_of_mem_map (b : Basis ι R S) (I : Ideal R) {x : S}
    (hx : x ∈ I.map (algebraMap R S)) (i : ι) : b.repr x i ∈ I := by
  have hx' : x ∈ I • (⊤ : Submodule R S) := by
    rw [Ideal.smul_top_eq_map]
    exact hx
  refine Submodule.smul_induction_on hx' ?_ ?_
  · intro a ha m _
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ ha
  · intro x y hx hy
    rw [map_add, Finsupp.add_apply]
    exact I.add_mem hx hy

/-- `(r mod I) • (s mod IS) = (r • s) mod IS`. -/
lemma mk_smul_mk (I : Ideal R) (r : R) (s : S) :
    Ideal.Quotient.mk I r • Ideal.Quotient.mk (I.map (algebraMap R S)) s =
      Ideal.Quotient.mk (I.map (algebraMap R S)) (r • s) := by
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_quotient_map_quotient, ← map_mul,
    ← Algebra.smul_def]

variable [Fintype ι]

/-- `x mod IS = ∑ (c_i mod I)·(b_i mod IS)` for the coordinates `c_i` of `x`. -/
lemma mk_eq_sum_repr_smul (b : Basis ι R S) (I : Ideal R) (x : S) :
    Ideal.Quotient.mk (I.map (algebraMap R S)) x =
      ∑ i, Ideal.Quotient.mk I (b.repr x i) •
        Ideal.Quotient.mk (I.map (algebraMap R S)) (b i) := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => (mk_smul_mk I _ _).symm

/-- The induced family `b_i mod IS` is linearly independent over `R/I`. -/
lemma linearIndependent_mk_basis (b : Basis ι R S) (I : Ideal R) :
    LinearIndependent (R ⧸ I) fun i => Ideal.Quotient.mk (I.map (algebraMap R S)) (b i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose g' hg' using fun i => Ideal.Quotient.mk_surjective (g i)
  have h : ∑ j, g' j • b j ∈ I.map (algebraMap R S) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hg' j, mk_smul_mk]
  have := repr_mem_of_mem_map b I h i
  rw [b.repr_sum_self] at this
  rw [← hg' i, Ideal.Quotient.eq_zero_iff_mem]
  exact this

/-- The basis of `S/IS` over `R/I` induced by a basis of `S` over `R`. -/
noncomputable def basisQuotientMap (b : Basis ι R S) (I : Ideal R) :
    Basis ι (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  Basis.mk (linearIndependent_mk_basis b I) (by
    rintro x -
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [mk_eq_sum_repr_smul b I x]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

@[simp] lemma basisQuotientMap_apply (b : Basis ι R S) (I : Ideal R) (i : ι) :
    basisQuotientMap b I i = Ideal.Quotient.mk (I.map (algebraMap R S)) (b i) :=
  Basis.mk_apply _ _ _

lemma basisQuotientMap_repr (b : Basis ι R S) (I : Ideal R) (x : S) (i : ι) :
    (basisQuotientMap b I).repr (Ideal.Quotient.mk (I.map (algebraMap R S)) x) i =
      Ideal.Quotient.mk I (b.repr x i) := by
  have h : Ideal.Quotient.mk (I.map (algebraMap R S)) x =
      ∑ j, Ideal.Quotient.mk I (b.repr x j) • basisQuotientMap b I j := by
    rw [mk_eq_sum_repr_smul b I x]
    simp only [basisQuotientMap_apply]
  rw [h, (basisQuotientMap b I).repr_sum_self]

/-- **The trace modulo an ideal**: `Tr_{(S/IS)/(R/I)}(x mod IS) = Tr_{S/R}(x) mod I` for a
finite free algebra `S/R`. -/
lemma trace_quotient_mk_map [Module.Free R S] [Module.Finite R S] (I : Ideal R) (x : S) :
    Algebra.trace (R ⧸ I) (S ⧸ I.map (algebraMap R S))
        (Ideal.Quotient.mk (I.map (algebraMap R S)) x) =
      Ideal.Quotient.mk I (Algebra.trace R S x) := by
  classical
  let b := Module.Free.chooseBasis R S
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace (basisQuotientMap b I),
    AddMonoidHom.map_trace]
  congr 1
  ext i j
  rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    basisQuotientMap_apply, ← map_mul, basisQuotientMap_repr]

instance free_quotient_map [Module.Free R S] [Module.Finite R S] (I : Ideal R) :
    Module.Free (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  Module.Free.of_basis (basisQuotientMap (Module.Free.chooseBasis R S) I)

end QuotientBasis

section Nilpotent

variable {R : Type*} [CommRing R]

/-- A ring is `I`-adically complete for an ideal with `I ^ n = ⊥`. -/
lemma isAdicComplete_of_pow_eq_bot (I : Ideal R) (n : ℕ) (hI : I ^ n = ⊥) :
    IsAdicComplete I R where
  haus' x hx := by
    have := hx n
    rw [SModEq.zero, hI, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_bot,
      Ideal.mem_bot] at this
    exact this
  prec' f hf := by
    refine ⟨f n, fun m => ?_⟩
    rcases le_or_gt m n with hmn | hmn
    · exact hf hmn
    · have h := hf hmn.le
      rw [SModEq.sub_mem, hI, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
        Ideal.map_bot, Ideal.mem_bot, sub_eq_zero] at h
      rw [h]

end Nilpotent

end Iut
