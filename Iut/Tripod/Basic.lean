/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.Places
import Genl.GeneralPosition.HeightTheory

/-!
# The concrete height theory of the tripod

This file instantiates the abstract height formalism `Genl.HeightTheory` of [GenEll], §1,
for the tripod `(ℙ¹_ℚ, {0, 1, ∞})` alone, with the arithmetic invariants of Mathlib:

- the points are the elements `λ ∈ ℚ̄ ∖ {0, 1}` of `U_ℙ(ℚ̄) = ℙ¹(ℚ̄) ∖ {0, 1, ∞}`, where
  `ℚ̄ := AlgebraicClosure ℚ` (`Iut.Tripod.Pt`);
- the degree of a point is `[ℚ(λ) : ℚ] = deg(minpoly λ)` (`Iut.Tripod.deg`), and
  `U_ℙ(ℚ̄)^{≤ d}`, `U_ℙ(ℚ̄)^{= d}` are the points of degree `≤ d`, `= d` (`ptLE`, `ptEQ`);
- the height `ht_{ω_ℙ({0,1,∞})} = ht_{𝒪(1)}` is the absolute logarithmic Weil height of `λ`
  (`Iut.Tripod.htCan`), i.e. Mathlib's `Height.logHeight₁` of `λ` in its minimal field of
  definition `ℚ(λ)`, divided by `[ℚ(λ) : ℚ]`;
- the log-different `log-diff_ℙ(λ) = log|𝔡_{ℚ(λ)}|/[ℚ(λ) : ℚ]` (`Iut.Tripod.logDiff`), with
  `|𝔡_{ℚ(λ)}| = |disc(ℚ(λ))|` the absolute value of the discriminant;
- the log-conductor `log-cond_{{0,1,∞}}(λ) = (1/[ℚ(λ) : ℚ]) ∑_v log N(v)` over the finite
  places `v` of `ℚ(λ)` at which `λ` meets `{0, 1, ∞}` (`Iut.Tripod.logCond`);
- the compactly bounded subsets `K_V` (`Iut.Tripod.CompactlyBounded`), in the
  valuation-bounded form: a finite set `V` of primes containing `2` and a bound `c` on
  `|log v(λ)|`, `|log v(λ − 1)|` at all places `v` of `ℚ(λ)` over `V` and at all
  archimedean places of `ℚ(λ)`.

The resulting `Iut.Tripod.tripodTheory : Genl.HeightTheory` turns
`Genl.HeightTheory.StatementII` into the concrete Diophantine statement
`Iut.Tripod.statementII_iff`: the ABC inequality for points of bounded degree in a
compactly bounded subset of `ℙ¹ ∖ {0, 1, ∞}`.

## Normalizations

All three functions are normalized by `1/[ℚ(λ) : ℚ]`, as in [GenEll], Definition 1.2(i)
and Definition 1.5(iii),(iv): Mathlib's `Height.logHeight₁` on a number field `K` is the
*relative* height `∑_{v} [K_v : ℚ_v] log⁺|x|_v`, which is `[K : ℚ]` times the absolute
height; dividing by `[ℚ(λ) : ℚ]` gives the absolute logarithmic Weil height. It is
independent of the choice of a field of definition; since Mathlib does not (yet) provide the
invariance of heights under finite extensions, the height is *defined* through the minimal
field of definition `ℚ(λ)`.

## Northcott

The Northcott property in the form needed by `Iut.CurveInputs.northcott` (finiteness of
the points of bounded degree *over all number fields* and bounded height) is not available
in Mathlib, which proves the Northcott property for each fixed number field
(`NumberField.finite_setOf_logHeight₁_le`). We prove the fixed-field form
(`Iut.Tripod.finite_of_fieldOf_eq`), isolate the missing statement as the `Prop`
`Iut.Tripod.NorthcottHyp` (no axiom), reduce it to the finiteness of the fields of
definition of the points in question (`Iut.Tripod.northcottHyp_of_finite_fieldOf`), and
derive the target form `Iut.Tripod.northcott` from it.

## References

- [GenEll] S. Mochizuki, *Arithmetic elliptic curves in general position*,
  Math. J. Okayama Univ. **52** (2010), 1–28.
-/

namespace Iut.Tripod

open NumberField

open scoped IntermediateField

/-- The algebraic closure `ℚ̄` of `ℚ`. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- The set of algebraic points `U_ℙ(ℚ̄) = ℙ¹(ℚ̄) ∖ {0, 1, ∞}` of the tripod: the elements
`λ ∈ ℚ̄` with `λ ≠ 0`, `λ ≠ 1`. -/
def Pt : Type := {l : Qbar // l ≠ 0 ∧ l ≠ 1}

/-- Every element of `ℚ̄` is integral over `ℚ`. -/
theorem isIntegral (l : Qbar) : IsIntegral ℚ l :=
  (AlgebraicClosure.isAlgebraic ℚ |>.isAlgebraic l).isIntegral

/-- The degree `[ℚ(λ) : ℚ]` of an algebraic number, as the degree of its minimal
polynomial. -/
noncomputable def deg (l : Qbar) : ℕ := (minpoly ℚ l).natDegree

/-- The degree of an algebraic number is positive. -/
theorem deg_pos (l : Qbar) : 0 < deg l :=
  minpoly.natDegree_pos (isIntegral l)

/-- The degree of an algebraic number is at least one. -/
theorem one_le_deg (l : Qbar) : 1 ≤ deg l := deg_pos l

/-- `(deg λ : ℝ)` is positive. -/
theorem deg_pos_real (l : Qbar) : (0 : ℝ) < deg l := by
  exact_mod_cast deg_pos l

/-- The minimal field of definition `ℚ(λ) ⊆ ℚ̄` of an algebraic number. -/
noncomputable abbrev fieldOf (l : Qbar) : IntermediateField ℚ Qbar := ℚ⟮l⟯

instance (l : Qbar) : FiniteDimensional ℚ (fieldOf l) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral l)

/-- A finite-dimensional intermediate field of `ℚ̄` is a number field. -/
instance (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] : NumberField F where

/-- `deg λ = [ℚ(λ) : ℚ]`. -/
theorem deg_eq_finrank (l : Qbar) : deg l = Module.finrank ℚ (fieldOf l) :=
  (IntermediateField.adjoin.finrank (isIntegral l)).symm

/-- The element `λ` viewed as an element of its minimal field of definition `ℚ(λ)`. -/
noncomputable def gen (l : Qbar) : fieldOf l := IntermediateField.AdjoinSimple.gen ℚ l

@[simp]
theorem coe_gen (l : Qbar) : (gen l : Qbar) = l := IntermediateField.AdjoinSimple.coe_gen ℚ l

theorem gen_ne_zero {l : Qbar} (hl : l ≠ 0) : gen l ≠ 0 := by
  intro h
  apply hl
  simpa using congrArg (fun y : fieldOf l ↦ (y : Qbar)) h

theorem gen_sub_one_ne_zero {l : Qbar} (hl : l ≠ 1) : gen l - 1 ≠ 0 := by
  intro h
  apply hl
  have h1 : gen l = 1 := sub_eq_zero.mp h
  have := congrArg (fun y : fieldOf l ↦ (y : Qbar)) h1
  simpa using this

/-! ### The filtration by degree -/

/-- The points of degree `≤ d`: `U_ℙ(ℚ̄)^{≤ d}` ([GenEll], Example 1.3(i)). -/
def ptLE (d : ℕ) : Set Pt := {x | deg x.1 ≤ d}

/-- The points of degree exactly `d`: `U_ℙ(ℚ̄)^{= d}` ([GenEll], Example 1.3(i)). -/
def ptEQ (d : ℕ) : Set Pt := {x | deg x.1 = d}

theorem mem_ptLE {d : ℕ} {x : Pt} : x ∈ ptLE d ↔ deg x.1 ≤ d := Iff.rfl

theorem mem_ptEQ {d : ℕ} {x : Pt} : x ∈ ptEQ d ↔ deg x.1 = d := Iff.rfl

/-- There are no points of degree `≤ 0`. -/
theorem ptLE_zero : ptLE 0 = ∅ := by
  ext x
  simp only [mem_ptLE, Set.mem_empty_iff_false, iff_false]
  exact Nat.not_le.mpr (deg_pos x.1)

/-- `U_ℙ(ℚ̄)^{≤ d+1} = U_ℙ(ℚ̄)^{≤ d} ∪ U_ℙ(ℚ̄)^{= d+1}`. -/
theorem ptLE_succ (d : ℕ) : ptLE (d + 1) = ptLE d ∪ ptEQ (d + 1) := by
  ext x
  simp only [mem_ptLE, Set.mem_union, mem_ptEQ]
  omega

/-! ### The height, the log-different and the log-conductor -/

/-- The **absolute logarithmic Weil height** of a point `λ` of the tripod: Mathlib's
logarithmic height `Height.logHeight₁` of `λ` in its minimal field of definition `ℚ(λ)`
(the relative height `∑_v [ℚ(λ)_v : ℚ_v] log⁺|λ|_v`), divided by `[ℚ(λ) : ℚ]`. This is
a representative of the BD-class `ht_{ω_ℙ({0,1,∞})} = ht_{𝒪(1)}` of [GenEll],
Definition 1.2(i), for the tripod (`ω_ℙ({0,1,∞}) ≅ 𝒪(1)`). -/
noncomputable def htCan (x : Pt) : ℝ :=
  Height.logHeight₁ (gen x.1) / deg x.1

/-- The height is nonnegative. -/
theorem htCan_nonneg (x : Pt) : 0 ≤ htCan x :=
  div_nonneg (Height.zero_le_logHeight₁ _) (Nat.cast_nonneg _)

/-- `[ℚ(λ) : ℚ] · htCan λ` is the relative logarithmic height of `λ` in `ℚ(λ)`. -/
theorem deg_mul_htCan (x : Pt) : (deg x.1 : ℝ) * htCan x = Height.logHeight₁ (gen x.1) := by
  rw [htCan, mul_div_cancel₀ _ (deg_pos_real x.1).ne']

/-- The **log-different** `log-diff_ℙ(λ) = log|disc(ℚ(λ))|/[ℚ(λ) : ℚ]` of a point `λ` of
the tripod ([GenEll], Definition 1.5(iii)): the normalized logarithm of the absolute value
of the discriminant of the minimal field of definition, which equals the normalized degree
`log N(𝔡_{ℚ(λ)/ℚ})/[ℚ(λ) : ℚ]` of the different (`|disc(K)| = N(𝔡_{K/ℚ})`). -/
noncomputable def logDiff (x : Pt) : ℝ :=
  Real.log |(discr (fieldOf x.1) : ℝ)| / deg x.1

/-- `1 ≤ |disc(K)|` for a number field `K`. -/
theorem one_le_abs_discr_real (K : Type*) [Field K] [NumberField K] :
    (1 : ℝ) ≤ |(discr K : ℝ)| := by
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (discr_ne_zero K)

/-- The log-different is nonnegative. -/
theorem logDiff_nonneg (x : Pt) : 0 ≤ logDiff x :=
  div_nonneg (Real.log_nonneg (one_le_abs_discr_real _)) (Nat.cast_nonneg _)

/-- The log-different is the normalized degree `log N(𝔡_{ℚ(λ)/ℚ})/[ℚ(λ) : ℚ]` of the
different ideal (`|disc(K)| = N(𝔡_{K/ℚ})`, `NumberField.absNorm_differentIdeal`); this is
the convention of `Iut.logDifferentDeg`. -/
theorem logDiff_eq_log_absNorm_differentIdeal (x : Pt) :
    logDiff x = Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 (fieldOf x.1)))) / deg x.1 := by
  unfold logDiff
  rw [absNorm_differentIdeal (K := fieldOf x.1), Nat.cast_natAbs, Int.cast_abs]

/-- The finite places `v` of `ℚ(λ)` at which `λ` meets the divisor `{0, 1, ∞}`: those with
`|λ|_v ≠ 1` (`λ` meets `0` or `∞`) or `|λ − 1|_v ≠ 1` (`λ` meets `1` or `∞`). -/
def badPlaces (l : Qbar) : Set (FinitePlace (fieldOf l)) :=
  {v | v (gen l) ≠ 1 ∨ v (gen l - 1) ≠ 1}

theorem mem_badPlaces {l : Qbar} {v : FinitePlace (fieldOf l)} :
    v ∈ badPlaces l ↔ v (gen l) ≠ 1 ∨ v (gen l - 1) ≠ 1 := Iff.rfl

/-- Only finitely many places of `ℚ(λ)` are bad for a point `λ ∉ {0, 1}`. -/
theorem badPlaces_finite {l : Qbar} (hl : l ≠ 0 ∧ l ≠ 1) : (badPlaces l).Finite := by
  have h₁ := FinitePlace.hasFiniteMulSupport (gen_ne_zero hl.1)
  have h₂ := FinitePlace.hasFiniteMulSupport (gen_sub_one_ne_zero hl.2)
  refine (h₁.union h₂).subset fun v hv ↦ ?_
  rcases hv with hv | hv
  · exact Or.inl hv
  · exact Or.inr hv

open scoped Classical in
/-- The **log-conductor** `log-cond_{{0,1,∞}}(λ)` of a point `λ` of the tripod ([GenEll],
Definition 1.5(iv)): the sum of `log N(v)` over the finite places `v` of `ℚ(λ)` at which
`λ` meets `{0, 1, ∞}` (`badPlaces λ`), divided by `[ℚ(λ) : ℚ]`. The sum is finite for
`λ ∉ {0, 1}` (`badPlaces_finite`); it is a `finsum`, so the definition makes sense for all
`λ`. -/
noncomputable def logCond (x : Pt) : ℝ :=
  (∑ᶠ v : FinitePlace (fieldOf x.1),
    if v ∈ badPlaces x.1 then Real.log (Ideal.absNorm v.maximalIdeal.asIdeal) else 0) /
    deg x.1

/-- `1 ≤ N(v)` for a finite place `v`. -/
theorem one_le_absNorm_real {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) :
    (1 : ℝ) ≤ Ideal.absNorm v.maximalIdeal.asIdeal := by
  exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.maximalIdeal).le

/-- The log-conductor is nonnegative. -/
theorem logCond_nonneg (x : Pt) : 0 ≤ logCond x := by
  classical
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply finsum_nonneg
  intro v
  split_ifs
  · exact Real.log_nonneg (one_le_absNorm_real v)
  · exact le_rfl

open scoped Classical in
/-- The log-conductor as a finite sum over the bad places. -/
theorem logCond_eq_sum (x : Pt) :
    logCond x = (∑ v ∈ (badPlaces_finite x.2).toFinset,
      Real.log (Ideal.absNorm v.maximalIdeal.asIdeal)) / deg x.1 := by
  unfold logCond
  congr 1
  rw [finsum_eq_sum_of_support_subset (s := (badPlaces_finite x.2).toFinset)]
  · rw [Finset.sum_ite_of_true]
    intro v hv
    simpa using hv
  · intro v hv
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hv
    simpa using hv.1

/-! ### Compactly bounded subsets -/

/-- **A compactly bounded subset of `U_ℙ(ℚ̄)`**, in the valuation-bounded form: a finite
set `V` of prime numbers containing `2` (the *support*; the set `Σ` of [GenEll], Theorem
2.1 and of IUT IV, Corollary 2.2 is contained in it) and a bound `c`. The underlying set
`CompactlyBounded.set K` consists of the points `λ` such that for every finite place `v` of
`ℚ(λ)` whose residue characteristic lies in `V`, `|log|λ|_v| ≤ c` and `|log|λ − 1|_v| ≤ c`,
where `|·|_v` is the absolute value of the finite place, normalized by
`|π_v|_v = N(v)⁻¹`; in terms of the valuation `ord_p` normalized by `ord_p(p) = 1`
(cf. `Iut.ordp`), `log|λ|_v = −[ℚ(λ)_v : ℚ_p] · ord_p(λ) · log p`; and such that for every
archimedean place `w` of `ℚ(λ)`, `|log|λ|_w| ≤ c` and `|log|λ − 1|_w| ≤ c` (the compactness
of the archimedean components of `K_V`; without it the height comparison of IUT IV,
Corollary 2.2(i) fails, since `λ ∈ ℚ` with `λ → ∞` has bounded nonarchimedean data at `V`
but unbounded height).

This is the valuation-bounded proxy for Mochizuki's compactly bounded subsets `K_V`
([GenEll], Example 1.3(ii)): a subset `K_V ⊆ U_ℙ(ℚ̄)` is compactly bounded with support
`V` if it consists of the points whose images in `U_ℙ(ℚ̄_v)` lie in a fixed compact subset,
for each `v ∈ V`. A compact subset of `U_ℙ(ℚ̄_p) = ℚ̄_p ∖ {0, 1}` is bounded away from
`0`, `1` and `∞`, i.e. `|log|λ|_v|` and `|log|λ − 1|_v|` are bounded on it, and likewise
a compact subset of `U_ℙ(ℂ) = ℂ ∖ {0, 1}` is bounded away from `0`, `1` and `∞`, so every
compactly bounded subset whose support contains `V` and the archimedean place is
contained in `CompactlyBounded.set ⟨V, _, _, c⟩` for some `c`. Since the statements about
`K_V` are inequalities of BD-classes *on* `K_V`, they only get stronger by enlarging
`K_V`. -/
structure CompactlyBounded where
  /-- The support: a finite set of prime numbers. -/
  V : Finset ℕ
  /-- The elements of the support are prime. -/
  prime : ∀ p ∈ V, p.Prime
  /-- The support contains `2`. -/
  two_mem : 2 ∈ V
  /-- The bound on `|log|λ|_v|` and `|log|λ − 1|_v|` at the places over `V`. -/
  c : ℝ

/-- The underlying set of points of a compactly bounded subset: the points `λ` with
`|log|λ|_v| ≤ c` and `|log|λ − 1|_v| ≤ c` at every finite place `v` of `ℚ(λ)` whose residue
characteristic lies in `V`. -/
def CompactlyBounded.set (K : CompactlyBounded) : Set Pt :=
  {x | (∀ v : FinitePlace (fieldOf x.1), residueChar v ∈ K.V →
    |Real.log (v (gen x.1))| ≤ K.c ∧ |Real.log (v (gen x.1 - 1))| ≤ K.c) ∧
    ∀ w : InfinitePlace (fieldOf x.1),
      |Real.log (w (gen x.1))| ≤ K.c ∧ |Real.log (w (gen x.1 - 1))| ≤ K.c}

theorem CompactlyBounded.mem_set {K : CompactlyBounded} {x : Pt} :
    x ∈ K.set ↔ (∀ v : FinitePlace (fieldOf x.1), residueChar v ∈ K.V →
      |Real.log (v (gen x.1))| ≤ K.c ∧ |Real.log (v (gen x.1 - 1))| ≤ K.c) ∧
      ∀ w : InfinitePlace (fieldOf x.1),
        |Real.log (w (gen x.1))| ≤ K.c ∧ |Real.log (w (gen x.1 - 1))| ≤ K.c := Iff.rfl

/-- The nonarchimedean bounds of a compactly bounded subset. -/
theorem CompactlyBounded.finite_bound {K : CompactlyBounded} {x : Pt} (hx : x ∈ K.set)
    (v : FinitePlace (fieldOf x.1)) (hv : residueChar v ∈ K.V) :
    |Real.log (v (gen x.1))| ≤ K.c ∧ |Real.log (v (gen x.1 - 1))| ≤ K.c :=
  hx.1 v hv

/-- The archimedean bounds of a compactly bounded subset. -/
theorem CompactlyBounded.infinite_bound {K : CompactlyBounded} {x : Pt} (hx : x ∈ K.set)
    (w : InfinitePlace (fieldOf x.1)) :
    |Real.log (w (gen x.1))| ≤ K.c ∧ |Real.log (w (gen x.1 - 1))| ≤ K.c :=
  hx.2 w

/-- Enlarging the bound enlarges the set. -/
theorem CompactlyBounded.set_mono_c {V : Finset ℕ} {hV : ∀ p ∈ V, p.Prime} {h2 : 2 ∈ V}
    {c c' : ℝ} (hc : c ≤ c') :
    CompactlyBounded.set ⟨V, hV, h2, c⟩ ⊆ CompactlyBounded.set ⟨V, hV, h2, c'⟩ :=
  fun _ hx ↦ ⟨fun v hv ↦ ⟨(hx.1 v hv).1.trans hc, (hx.1 v hv).2.trans hc⟩,
    fun w ↦ ⟨(hx.2 w).1.trans hc, (hx.2 w).2.trans hc⟩⟩

/-- Shrinking the support enlarges the set. -/
theorem CompactlyBounded.set_mono_V {V V' : Finset ℕ} {hV : ∀ p ∈ V, p.Prime}
    {hV' : ∀ p ∈ V', p.Prime} {h2 : 2 ∈ V} {h2' : 2 ∈ V'} {c : ℝ} (hVV : V ⊆ V') :
    CompactlyBounded.set ⟨V', hV', h2', c⟩ ⊆ CompactlyBounded.set ⟨V, hV, h2, c⟩ :=
  fun _ hx ↦ ⟨fun v hv ↦ hx.1 v (hVV hv), hx.2⟩

/-! ### The height theory of the tripod -/

/-- **The concrete height theory of the tripod**: the instance of `Genl.HeightTheory` with
the tripod `(ℙ¹_ℚ, {0, 1, ∞})` as its only curve, the algebraic numbers `λ ∉ {0, 1}` as its
points, the absolute logarithmic Weil height, the log-different and the log-conductor of
`ℚ(λ)`, and the valuation-bounded compactly bounded subsets. -/
noncomputable def tripodTheory : Genl.HeightTheory where
  Curve := Unit
  Pt _ := Pt
  Hyperbolic _ := True
  DivisorFree _ := False
  ptLE _ := ptLE
  ptEQ _ := ptEQ
  ptLE_zero _ := ptLE_zero
  ptLE_succ _ := ptLE_succ
  htCan _ := htCan
  logDiff _ := logDiff
  logCond _ := logCond
  tripod := ()
  hyperbolic_tripod := trivial
  CBS := CompactlyBounded
  cbsSet := CompactlyBounded.set

@[simp] theorem tripodTheory_Pt (X : Unit) : tripodTheory.Pt X = Pt := rfl
@[simp] theorem tripodTheory_ptLE (X : Unit) : tripodTheory.ptLE X = ptLE := rfl
@[simp] theorem tripodTheory_ptEQ (X : Unit) : tripodTheory.ptEQ X = ptEQ := rfl
@[simp] theorem tripodTheory_htCan (X : Unit) : tripodTheory.htCan X = htCan := rfl
@[simp] theorem tripodTheory_logDiff (X : Unit) : tripodTheory.logDiff X = logDiff := rfl
@[simp] theorem tripodTheory_logCond (X : Unit) : tripodTheory.logCond X = logCond := rfl
@[simp] theorem tripodTheory_tripod : tripodTheory.tripod = () := rfl
@[simp] theorem tripodTheory_CBS : tripodTheory.CBS = CompactlyBounded := rfl
@[simp] theorem tripodTheory_cbsSet (K : CompactlyBounded) :
    tripodTheory.cbsSet K = K.set := rfl

/-- **The ABC conjecture for compactly bounded subsets of the tripod**, concretely:
`Genl.HeightTheory.StatementII` for `tripodTheory` says that for every `d`, every `ε > 0`
and every compactly bounded subset `K`, the absolute logarithmic Weil height satisfies
`h(λ) ≤ (1 + ε) (log|disc(ℚ(λ))| + ∑_{v bad} log N(v))/[ℚ(λ) : ℚ] + C` for all `λ ∈ K` of
degree `≤ d`, for some constant `C = C(d, ε, K)`. -/
theorem statementII_iff :
    tripodTheory.StatementII ↔
      ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∀ K : CompactlyBounded,
        htCan ≲[K.set ∩ ptLE d] (1 + ε) • (logDiff + logCond) :=
  Iff.rfl

/-- `Genl.HeightTheory.StatementII` for the tripod, fully unfolded: the existence of a
constant `C` with `h(λ) ≤ (1 + ε) (log-diff(λ) + log-cond(λ)) + C` on `K ∩ U_ℙ(ℚ̄)^{≤ d}`. -/
theorem statementII_iff' :
    tripodTheory.StatementII ↔
      ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∀ K : CompactlyBounded, ∃ C : ℝ,
        ∀ x : Pt, x ∈ K.set → deg x.1 ≤ d →
          htCan x ≤ (1 + ε) * (logDiff x + logCond x) + C := by
  rw [statementII_iff]
  refine forall_congr' fun d ↦ forall_congr' fun ε ↦ imp_congr_right fun _ ↦
    forall_congr' fun K ↦ exists_congr fun C ↦ ?_
  simp only [Set.mem_inter_iff, mem_ptLE, and_imp, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

/-- Statement (i) of [GenEll], Theorem 2.1 for the tripod theory is the same inequality
without the restriction to a compactly bounded subset. -/
theorem statementI_iff :
    tripodTheory.StatementI ↔
      ∀ (d : ℕ) (ε : ℝ), 0 < ε → htCan ≲[ptLE d] (1 + ε) • (logDiff + logCond) := by
  constructor
  · intro h d ε hε
    exact h () trivial d ε hε
  · intro h X _ d ε hε
    exact h d ε hε

/-! ### Northcott -/

/-- **Northcott's theorem for a fixed field of definition**: for every finite-dimensional
`F ⊆ ℚ̄` and every `H`, there are only finitely many points `λ` with `ℚ(λ) = F` and
`htCan λ ≤ H` (from `NumberField.finite_setOf_logHeight₁_le` for `F`). -/
theorem finite_of_fieldOf_eq (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] (H : ℝ) :
    {x : Pt | fieldOf x.1 = F ∧ htCan x ≤ H}.Finite := by
  have hF : {y : F | Height.logHeight₁ y ≤ max H 0 * Module.finrank ℚ F}.Finite :=
    finite_setOf_logHeight₁_le F _
  have himg : {x : Pt | fieldOf x.1 = F ∧ htCan x ≤ H} ⊆
      (fun x : Pt ↦ x.1) ⁻¹' (Subtype.val '' {y : F | Height.logHeight₁ y ≤
        max H 0 * Module.finrank ℚ F}) := by
    rintro ⟨l, hl⟩ ⟨hFl, hH⟩
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
    subst hFl
    refine ⟨gen l, ?_, rfl⟩
    rw [← deg_mul_htCan ⟨l, hl⟩, ← deg_eq_finrank, mul_comm]
    exact mul_le_mul_of_nonneg_right (hH.trans (le_max_left _ _)) (Nat.cast_nonneg _)
  refine ((hF.image Subtype.val).preimage ?_).subset himg
  intro x _ y _ h
  exact Subtype.ext h

/-- **The Northcott property for points of bounded degree** in `ℚ̄`: for every `d` and `H`
there are only finitely many `λ ∈ ℚ̄ ∖ {0, 1}` with `[ℚ(λ) : ℚ] ≤ d` and absolute
logarithmic Weil height `≤ H`. This is the classical Northcott theorem [Northcott 1949];
Mathlib provides it for each fixed number field (`NumberField.finite_setOf_logHeight₁_le`,
i.e. `Iut.Tripod.finite_of_fieldOf_eq` here) but not, at present, uniformly over all
number fields of bounded degree, which needs the comparison of the heights of an algebraic
number and of the coefficients of its minimal polynomial (or the invariance of heights under
field extensions). It is recorded as a `Prop`, not an axiom; see
`Iut.Tripod.northcottHyp_of_finite_fieldOf` for a reduction. -/
def NorthcottHyp : Prop :=
  ∀ (d : ℕ) (H : ℝ), {x : Pt | x ∈ ptLE d ∧ htCan x ≤ H}.Finite

/-- **Reduction of the Northcott property to the finiteness of the fields of definition**:
if for every `d` and `H` only finitely many number fields `F ⊆ ℚ̄` occur as the minimal
field of definition of a point of degree `≤ d` and height `≤ H`, then `NorthcottHyp` holds
(by `finite_of_fieldOf_eq` applied to each of them). -/
theorem northcottHyp_of_finite_fieldOf
    (hfin : ∀ (d : ℕ) (H : ℝ),
      {F : IntermediateField ℚ Qbar | ∃ x : Pt, x ∈ ptLE d ∧ htCan x ≤ H ∧ fieldOf x.1 = F}.Finite) :
    NorthcottHyp := by
  intro d H
  have hsub : {x : Pt | x ∈ ptLE d ∧ htCan x ≤ H} ⊆
      ⋃ F ∈ {F : IntermediateField ℚ Qbar |
        ∃ x : Pt, x ∈ ptLE d ∧ htCan x ≤ H ∧ fieldOf x.1 = F},
        {x : Pt | fieldOf x.1 = F ∧ htCan x ≤ H} := by
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨fieldOf x.1, ⟨x, hx.1, hx.2, rfl⟩, rfl, hx.2⟩
  refine ((hfin d H).biUnion fun F hF ↦ ?_).subset hsub
  obtain ⟨x, -, -, rfl⟩ := hF
  exact finite_of_fieldOf_eq (fieldOf x.1) H

/-- **The Northcott finiteness needed by `Iut.CurveInputs.northcott`**, from
`NorthcottHyp`: for every compactly bounded subset `K`, every `d` and every `H`, the set
of points of `K` of degree `≤ d` and height `≤ H` is finite. -/
theorem northcott (hN : NorthcottHyp) (K : CompactlyBounded) (d : ℕ) (H : ℝ) :
    {x : Pt | x ∈ K.set ∩ ptLE d ∧ htCan x ≤ H}.Finite :=
  (hN d H).subset fun _ hx ↦ ⟨hx.1.2, hx.2⟩

/-- The Northcott finiteness for a function `h` with `(1/6) h ≈ htCan` on `K`, as in
`Iut.CurveInputs.northcott`: a bound on `h` implies a bound on `htCan`. -/
theorem northcott_of_equiv (hN : NorthcottHyp) (K : CompactlyBounded) (d : ℕ)
    {h : Pt → ℝ} (hh : ((1 / 6 : ℝ) • h) ≈[K.set] htCan) (H : ℝ) :
    {x : Pt | x ∈ K.set ∩ ptLE d ∧ h x ≤ H}.Finite := by
  obtain ⟨C, hC⟩ := hh.ge
  refine (northcott hN K d (H / 6 + C)).subset fun x hx ↦ ⟨hx.1, ?_⟩
  have := hC x hx.1.1
  simp only [Pi.smul_apply, smul_eq_mul] at this
  linarith [hx.2]

end Iut.Tripod
