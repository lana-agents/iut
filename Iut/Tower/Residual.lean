/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.Basic
import Iut.Concrete.Invariants
import Iut.Concrete.ThetaLocalConstruct.Data

/-!
# The local facts of the tower `F_mod ⊆ F_tpd ⊆ F ⊆ K` (IUT IV, Propositions 1.3 and 1.8)

The tower arithmetic `Iut.TowerArithmetic` (IUT IV, (R4) and Steps (ii), (iii) of the proof
of Theorem 1.10) is derived in `Iut.Tower.Main` from the standard global theory of Dedekind
domains together with the **local facts** collected here as the `Prop`-structure
`Iut.TowerLocalFacts`, about the tower

  `ℚ ⊆ F_mod = ℚ(j) ⊆ F_tpd = F_mod(E[2]) ⊆ F ⊆ K = F(E[ℓ])`

of the Θ-data. For a place `v` of `K` over `u` of `F_tpd`, with `e(v/u)` the relative
ramification index and `e_v` the absolute one:

* `ordAt_different_le` — **the different bound** (IUT IV, Proposition 1.3 together with the
  tameness of `K/F` away from `ℓ` and of `F/F_tpd` away from `2·3·5`, Proposition 1.8):
  `ord_v(𝔇_{K/F_tpd}) ≤ e(v/u) − 1 + e_v·c_p`, where the wild factor `c_p`
  (`Iut.wildConst`) is `12, 2, 1` at `p = 2, 3, 5` (the `p`-adic valuations of
  `[F : F_tpd] ∣ 2¹²·3²·5`, `F = F_tpd(√−1, √λ, √(1 − λ), E[3], E[5])`), `1` at `p = ℓ`
  (`ord_ℓ |GL₂(𝔽_ℓ)| = 1`) and `0` otherwise (tame ramification, `ord_v(𝔇) = e − 1`);
* `relRamIdx_eq_one` — **Néron–Ogg–Shafarevich**: `K/F_tpd` is unramified at the places
  `v` of residue characteristic `∉ {2, 3, 5, ℓ}` whose place `u` of `F_tpd` is not bad;
* `relRamIdx_le` — at the places of residue characteristic `∉ {2, 3, 5, ℓ}`,
  `e(v/u) ≤ 30ℓ` (`K/F` has `e ∣ ℓ` there, by the Tate uniformization at the bad places and
  Néron–Ogg–Shafarevich at the good ones; `F/F_tpd` has `e ∣ 2·3·5`);
* `relRamIdx_mod_le_two` — `F_tpd/F_mod` has ramification index `≤ 2` at the places over
  `V_mod^bad` (`F_tpd,u = F_mod,u₀(√q)` by the Tate uniformization of the `2`-torsion).

These four statements are the residual local input of the tower arithmetic; everything else
(the fundamental identity, the multiplicativity of ramification indices and of the
different in towers, the norm of the different, the Galois-theoretic degree bounds) is
proved. They are formulated for the global and admissible-prime data `(F, E, V_mod^bad, ℓ)`
of initial Θ-data (`Iut.AdmissiblePrimeData`), so that the hypothesis can be stated for
the curves of the tripod without reference to the anabelian part of the Θ-data.

The file also provides the `F_mod`-algebra structure of `F_tpd` (the inclusion
`ℚ(j) ⊆ ℚ(j, E[2])`) and the notation `Iut.placeTpd v` for the place of `F_tpd` below a
place of `K`.
-/

namespace Iut

open NumberField IsDedekindDomain

universe u

/-- **The wild constants** `c_p` of the different bound: the `p`-adic valuation of
`2¹²·3²·5` (the degree `[F : F_tpd]`) plus `1` at `p = ℓ`. -/
def wildConst (ℓ p : ℕ) : ℕ :=
  (if p = 2 then 12 else if p = 3 then 2 else if p = 5 then 1 else 0) + (if p = ℓ then 1 else 0)

lemma wildConst_eq_zero {ℓ p : ℕ} (hp : p ∉ ({2, 3, 5, ℓ} : Finset ℕ)) : wildConst ℓ p = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  simp [wildConst, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

/-! ### The tower of fields -/

section Fields

variable (F : Type u) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]

/-- `F_mod = ℚ(j) ⊆ F_tpd = ℚ(j, x(E[2]))`. -/
lemma fieldOfModuli_le_tripodalFieldOf : fieldOfModuli F E ≤ tripodalFieldOf F E :=
  IntermediateField.adjoin_simple_le_iff.mpr
    (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _))

/-- The `F_mod`-algebra structure of `F_tpd`, by the inclusion. -/
noncomputable instance instAlgebraFieldOfModuliTripodal :
    Algebra ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) :=
  (IntermediateField.inclusion (fieldOfModuli_le_tripodalFieldOf F E)).toAlgebra

lemma algebraMap_fieldOfModuli_tripodal_apply (x : ↥(fieldOfModuli F E)) :
    (algebraMap ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) x : F) = x :=
  IntermediateField.coe_inclusion _ x

instance instIsScalarTowerFieldOfModuliTripodal :
    IsScalarTower ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) F :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply,
      algebraMap_fieldOfModuli_tripodal_apply]

instance instIsScalarTowerRatFieldOfModuliTripodal :
    IsScalarTower ℚ ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

instance instFiniteDimensionalFieldOfModuliTripodal :
    FiniteDimensional ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) :=
  Module.Finite.of_restrictScalars_finite ℚ _ _

/-- `[F_tpd : ℚ] = [F_tpd : F_mod]·d_mod`. -/
lemma finrank_tripodal_eq_mul :
    Module.finrank ℚ ↥(tripodalFieldOf F E) =
      Module.finrank ℚ ↥(fieldOfModuli F E) *
        Module.finrank ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E) :=
  (Module.finrank_mul_finrank ℚ ↥(fieldOfModuli F E) ↥(tripodalFieldOf F E)).symm

variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] (L : IntermediateField F Fbar)
  [NumberField ↥L]

/-- The place of `F_tpd` below a place of a finite extension `L` of `F`. -/
noncomputable abbrev placeTpd (v : FinitePlace ↥L) : FinitePlace ↥(tripodalFieldOf F E) :=
  placeUnder (k := ↥(tripodalFieldOf F E)) v

variable {F E L}

lemma liesOver_placeTpd (v : FinitePlace ↥L) : FinitePlace.LiesOver v (placeTpd F E L v) :=
  liesOver_placeUnder v

lemma residueChar_placeTpd (v : FinitePlace ↥L) :
    residueChar (placeTpd F E L v) = residueChar v :=
  (residueChar_eq_of_liesOver (liesOver_placeTpd v)).symm

/-- `e_v = e_u · e(v/u)` for `u` the place of `F_tpd` below `v`. -/
lemma ramIdx_eq_ramIdx_placeTpd_mul (v : FinitePlace ↥L) :
    ramIdx (↥L) v =
      ramIdx ↥(tripodalFieldOf F E) (placeTpd F E L v) * relRamIdx v (placeTpd F E L v) :=
  ramIdx_eq_mul (liesOver_placeTpd v)

/-- `f_v = f_u · f(v/u)` for `u` the place of `F_tpd` below `v`. -/
lemma inertDeg_eq_inertDeg_placeTpd_mul (v : FinitePlace ↥L) :
    inertDeg (↥L) v =
      inertDeg ↥(tripodalFieldOf F E) (placeTpd F E L v) * relInertDeg v (placeTpd F E L v) :=
  inertDeg_eq_mul (liesOver_placeTpd v)

end Fields

/-! ### The residual local facts -/

section Facts

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (VBad : Set (FinitePlace ↥(fieldOfModuli F E)))
variable (Pr : AdmissiblePrimeData F E Fbar VBad) [NumberField ↥Pr.torsionField]

/-- **The local facts of the tower** `F_mod ⊆ F_tpd ⊆ F ⊆ K` (IUT IV, Propositions 1.3 and
1.8; see the module docstring): the different bound, Néron–Ogg–Shafarevich, the
ramification bound away from `2·3·5·ℓ`, and the ramification of `F_tpd/F_mod` at the
bad places. -/
structure TowerLocalFacts : Prop where
  /-- **The different bound** (Proposition 1.3 with the tameness of Proposition 1.8):
  `ord_v(𝔇_{K/F_tpd}) + 1 ≤ e(v/u) + e_v·c_p`. -/
  ordAt_different_le : ∀ v : FinitePlace ↥Pr.torsionField,
    ordAt (differentIdeal (𝓞 ↥(tripodalFieldOf F E)) (𝓞 ↥Pr.torsionField)) v + 1 ≤
      relRamIdx v (placeTpd F E Pr.torsionField v) +
        ramIdx (↥Pr.torsionField) v * wildConst Pr.ℓ (residueChar v)
  /-- **Néron–Ogg–Shafarevich**: `K/F_tpd` is unramified at the places of residue
  characteristic `∉ {2, 3, 5, ℓ}` over a place of `F_tpd` that is not bad. -/
  relRamIdx_eq_one : ∀ v : FinitePlace ↥Pr.torsionField,
    residueChar v ∉ ({2, 3, 5, Pr.ℓ} : Finset ℕ) →
    ¬ IsBadTpdOf F E VBad (placeTpd F E Pr.torsionField v) →
    relRamIdx v (placeTpd F E Pr.torsionField v) = 1
  /-- **The ramification bound away from `2·3·5·ℓ`**: `e(v/u) ≤ 30ℓ`. -/
  relRamIdx_le : ∀ v : FinitePlace ↥Pr.torsionField,
    residueChar v ∉ ({2, 3, 5, Pr.ℓ} : Finset ℕ) →
    relRamIdx v (placeTpd F E Pr.torsionField v) ≤ 30 * Pr.ℓ
  /-- **`F_tpd/F_mod` at the bad places**: `e(u/u₀) ≤ 2` for `u₀ ∈ V_mod^bad`. -/
  relRamIdx_mod_le_two : ∀ (u : FinitePlace ↥(tripodalFieldOf F E))
    (u₀ : FinitePlace ↥(fieldOfModuli F E)), u₀ ∈ VBad → FinitePlace.LiesOver u u₀ →
    relRamIdx u u₀ ≤ 2

end Facts

end Iut
