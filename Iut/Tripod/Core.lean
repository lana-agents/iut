/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.CurveFacts
import Iut.Anabelian.Geometry

/-!
# The core finiteness for the tripod ([CanLift], Proposition 2.7)

`Iut.Tripod.coreFiniteness`: for the model anabelian geometry `modelAG Pi1` of a theory
`Pi1 : EtalePi1Theory` of étale fundamental groups, only finitely many points `λ` of the
tripod (of any set of points, in fact) have a once-punctured Legendre curve
`X_λ = E_λ ∖ {0}` without the `F_λ`-core `X_λ/{±1}`. This is the hypothesis
`Iut.Tripod.CoreFinitenessHyp` consumed by `Iut.Tripod.curveInputs`.

The proof: the interface `Pi1` records [CanLift], Proposition 2.7 — `X_λ` has the core
`X_λ/{±1}` unless `j(E_λ)` lies in the finite set `Pi1.excJ` of exceptional
`j`-invariants — and `j(E_λ) = 256 (λ² − λ + 1)³ / (λ² (λ − 1)²)`, so an exceptional point
`λ ∈ ℚ̄` is a root of one of the finitely many nonzero polynomials
`256 (X² − X + 1)³ − c·X² (X − 1)²`, `c ∈ Pi1.excJ` (nonzero: its value at `0` is `256`),
each of which has finitely many roots.
-/

namespace Iut.Tripod

open WeierstrassCurve Polynomial Iut.Anabelian

/-- The polynomial `256 (X² − X + 1)³ − c·X² (X − 1)²` over `ℚ̄`, whose roots `λ ≠ 0, 1` are
the parameters with `j(E_λ) = c`. -/
noncomputable def jPolyRat (c : ℚ) : Polynomial Qbar :=
  C 256 * (X ^ 2 - X + 1) ^ 3 - C (c : Qbar) * (X ^ 2 * (X - 1) ^ 2)

/-- `jPolyRat c` takes the value `256` at `0`. -/
theorem jPoly_eval_zero (c : ℚ) : (jPolyRat c).eval 0 = 256 := by
  simp [jPolyRat]

/-- `jPolyRat c ≠ 0`. -/
theorem jPoly_ne_zero (c : ℚ) : jPolyRat c ≠ 0 := by
  intro h
  have h0 := jPoly_eval_zero c
  rw [h, eval_zero] at h0
  exact absurd h0 (by norm_num)

/-- A parameter `λ ≠ 0, 1` with `j(E_λ) = c` is a root of `jPolyRat c`. -/
theorem isRoot_jPoly_of_eq (c : ℚ) {l : Qbar} (h0 : l ≠ 0) (h1 : l ≠ 1)
    (h : 256 * (l ^ 2 - l + 1) ^ 3 / (l ^ 2 * (l - 1) ^ 2) = (c : Qbar)) :
    (jPolyRat c).IsRoot l := by
  have hden : l ^ 2 * (l - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ (sub_ne_zero.mpr h1))
  rw [div_eq_iff hden] at h
  rw [IsRoot, jPolyRat]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
  rw [h, sub_self]

/-- **The exceptional parameters**: the `λ ∈ ℚ̄` at which `jPolyRat c` vanishes for some
exceptional `j`-invariant `c ∈ Pi1.excJ`. -/
def excLam (Pi1 : EtalePi1Theory.{0}) : Set Qbar :=
  ⋃ c ∈ Pi1.excJ, {l | (jPolyRat c).IsRoot l}

/-- The exceptional parameters form a finite set. -/
theorem excLam_finite (Pi1 : EtalePi1Theory.{0}) : (excLam Pi1).Finite :=
  Pi1.excJ.finite_toSet.biUnion fun c _ => finite_setOf_isRoot (jPoly_ne_zero c)

section Curve

variable (Pi1 : EtalePi1Theory.{0}) (x : Pt) (h3 : TorsionFinite x.1 3)
  (h5 : TorsionFinite x.1 5)

/-- If `X_λ` fails to have the core `X_λ/{±1}` in the model geometry then `j(E_λ)` is an
exceptional value ([CanLift], Proposition 2.7, as recorded in `Pi1`). -/
theorem exists_excJ_of_not_hasCore
    (h : ¬ (modelAG Pi1).HasCore ((modelAG Pi1).oncePunctured (curveOf x h3 h5).E)
      (OrbicurveDataSection.CF (modelAG Pi1) (curveOf x h3 h5).F (curveOf x h3 h5).E)) :
    ∃ c ∈ Pi1.excJ, (curveOf x h3 h5).E.j = (c : (curveOf x h3 h5).F) := by
  by_contra hc
  push Not at hc
  exact h (Pi1.hasCore_oncePunctured (curveOf x h3 h5).E hc)

/-- If `j(E_λ) = c` then `λ` is a root of `jPolyRat c`. -/
theorem isRoot_jPoly_of_j_eq {c : ℚ}
    (hj : (curveOf x h3 h5).E.j = (c : (curveOf x h3 h5).F)) : (jPolyRat c).IsRoot x.1 := by
  haveI : (legendre (gen' x.1)).IsElliptic := (curveOf x h3 h5).isElliptic
  have hj' : (legendre (gen' x.1)).j =
      256 * (gen' x.1 ^ 2 - gen' x.1 + 1) ^ 3 / (gen' x.1 ^ 2 * (gen' x.1 - 1) ^ 2) :=
    legendre_j (l := gen' x.1)
  change (legendre (gen' x.1)).j = ((c : ℚ) : fieldOf' x.1) at hj
  rw [hj'] at hj
  have h := congrArg (algebraMap (fieldOf' x.1) Qbar) hj
  simp only [map_div₀, map_mul, map_pow, map_add, map_sub, map_one, map_ofNat, map_ratCast,
    IntermediateField.algebraMap_apply, coe_gen'] at h
  exact isRoot_jPoly_of_eq c x.2.1 x.2.2 h

end Curve

/-- **The core finiteness for the tripod** ([CanLift], Proposition 2.7): for the model
anabelian geometry of any theory `Pi1` of étale fundamental groups, only finitely many
points of bounded degree in a compactly bounded subset have a once-punctured Legendre
curve without the core `X_λ/{±1}` — they lie among the roots of the finitely many nonzero
polynomials `256 (X² − X + 1)³ − c·X² (X − 1)²`, `c ∈ Pi1.excJ`. -/
theorem coreFiniteness (Pi1 : EtalePi1Theory.{0}) (P : CurveProviders) (K : CompactlyBounded)
    (d : ℕ) : CoreFinitenessHyp P K d (modelAG Pi1) := by
  have hinj : Function.Injective (fun x : Pt => x.1) := Subtype.val_injective
  refine ((excLam_finite Pi1).preimage hinj.injOn).subset ?_
  rintro x ⟨_, hx⟩
  obtain ⟨c, hc, hj⟩ := exists_excJ_of_not_hasCore Pi1 x _ _ hx
  exact Set.mem_iUnion₂.mpr ⟨c, hc, isRoot_jPoly_of_j_eq x _ _ hj⟩

end Iut.Tripod
