/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.ThetaLocalConstruct.Data
import Iut.Cor312.Statement

/-!
# The concrete theta-pilot region and the concrete variant data (taxis #278, #1449)

This file fills the remaining inputs of the Corollary 3.12 variant with concrete
implementations, as functions of the initial Θ-data `D` alone: the tensor packets of its
`ℓ`-torsion field `K` (`Iut.LocalTheory`) at the places of its valuation section
`V ≅ V_mod` (`InitialThetaData.placeSect`; IUT I, Definition 3.1(e)) and its local theta data
(the `2ℓ`-th roots `InitialThetaData.qroot` of the Tate parameters at the bad places of `K`).

## The indexing of the direct summands by `V`

Following IUT III, Propositions 3.1, 3.2, Theorem 3.11 (Ind2) and Remark 3.1.1(ii), the direct
summands of the packet at a rational place `v_ℚ` are indexed by the tuples of places
`v ∈ V` over `v_ℚ` — not by all places of `K` over `v_ℚ` — and the log-volume of the summand
`⊗_j K_{v_j}` is counted with the weight `∏_j [(F_mod)_{v_j} : ℚ_{v_ℚ}]/[F_mod : ℚ]`
(`LocalTheory.container`, `LocalTheory.vol` for the section `D.placeSect`).

## The theta-pilot region

In IUT IV, Step (v) of the proof of Theorem 1.10, the union of the possible images of
the Θ-pilot object in the tensor packet at a distinguished prime `p`, for the capsule
`S_{j+1} = {0, …, j}` and a tuple `(v_i)_{i ∈ S_{j+1}}`, is contained in the images
`φ(p^λ·(R_I)^∼)` under the indeterminacy automorphisms `φ` of Proposition 1.2, where
`λ = ord_p(q_{v_j}^{j²})` and `q_v` is the `2ℓ`-th root of the Tate parameter of
IUT I, Example 3.2(iv) (`λ = 0` at good places). At the archimedean place the images lie
in `φ(⊗ 𝓘_{v_i})`, the images of the tensor product of the archimedean log-shells
(Proposition 1.5(iii),(iv)).

The **concrete theta-pilot region** of the variant is exactly this container:

`Θ_{i,v_ℚ} := ∏_{tuples c} ⋃_{φ ∈ indAut} φ(q_{v_j}^{j²}·(R_I)^∼)` (`p` finite), resp.
`∏_c ⋃_{φ} φ(⊗ 𝓘)` (archimedean).

It contains the union of the possible images of the Θ-pilot object in the sense of
IUT III, Theorem 3.11 (that containment is the content of IUT IV, Step (v); it is *not*
needed for the implication to ABC, which only uses the region itself). This is the
project-owner-specified concretization of the input `RHSData.thetaPilot` of taxis #35.

## The `q`-pilot data

`QPilotData` is built from the finiteness of the bad locus and the weights
`f_w/[F : ℚ]` (`f_w` the residue degree), so that `log(q) = ∑_w f_w·ord_w(q_w)·log p_w /
[F : ℚ]` is the normalized degree of the `q`-divisor with the integer orders of taxis #37
(IUT IV, Theorem 1.10, `log(q) := deg(q_ADiv)`).
-/

namespace Iut

universe u

open NumberField
open scoped Pointwise


variable (D : InitialThetaData.{u})

namespace InitialThetaData

/-- The field of moduli `F_mod` of the Θ-data, as a type. -/
abbrev Fmod : Type u := ↥(fieldOfModuli D.F D.E)

/-- **The valuation section `V_mod ≅ V ⊆ V(K)`** of the Θ-data (IUT I, Definition 3.1(e);
`Iut.ValuationSection`), as a section of places `V(F_mod) → V(K)`: it indexes the direct summands
of the tensor packets (IUT III, Proposition 3.1, Remark 3.1.1(ii)). -/
noncomputable def placeSect : LocalTheory.PlaceSection D.Kt D.Fmod where
  fin := D.V.sectFin
  inf := D.V.sectInf
  residueChar_fin w := residueChar_eq_of_liesOver (D.V.sectFin_liesOver w)

variable (n : ℕ)

/-- The distinguished label `j = i + 1` of the capsule `S_{j+1} = {0, …, i+1}` of the
standard procession. -/
def distinguished (i : Fin n) : ((Procession.standard n).capsule i).LabelType :=
  ⟨i.1 + 1, by simp [Procession.standard, procLabels]⟩

/-- The label type of the `i`-th capsule `S_{i+2} = {0, …, i+1}` of the standard procession. -/
abbrev Lab (i : Fin n) : Type := ((Procession.standard n).capsule i).LabelType

/-- The scaling element `q_{v_l}^{j²}` (`j = i + 1`) of a tuple at a finite place, placed in the
`l`-th tensor factor. -/
noncomputable def scaleEltAt (i : Fin n) (p : Nat.Primes)
    (c : Lab n i → LocalTheory.Fiber D.Fmod (.finite p)) (l : Lab n i) :
    LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c) :=
  LocalTheory.incl D.Kt p (LocalTheory.tuple D.placeSect _ c) l
    (LocalTheory.sectPlace D.placeSect (c l))
    (LocalTheory.tuple_finite D.placeSect c l)
    (D.qroot (LocalTheory.sectPlace D.placeSect (c l)) ^ (i.1 + 1) ^ 2)

/-- The scaling element `q_{v_j}^{j²}` of a tuple at a finite place, in the `j`-th tensor
factor. -/
noncomputable def scaleElt (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber D.Fmod (.finite p)) :
    LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c) :=
  D.scaleEltAt n i p c (distinguished n i)

lemma isUnit_scaleEltAt (i : Fin n) (p : Nat.Primes)
    (c : Lab n i → LocalTheory.Fiber D.Fmod (.finite p)) (l : Lab n i) :
    IsUnit (D.scaleEltAt n i p c l) :=
  LocalTheory.isUnit_incl D.Kt p _ _ _ _ _ (pow_ne_zero _ (D.qroot_ne_zero _))

lemma isUnit_scaleElt (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber D.Fmod (.finite p)) :
    IsUnit (D.scaleElt n i p c) :=
  D.isUnit_scaleEltAt n i p c _

/-- `ord_p` of the scaling element's root: `j²·ord_p(q_{v_j}) ≥ 0`. -/
lemma ordp_pow_nonneg (v : FinitePlace D.Kt) (m : ℕ) :
    0 ≤ ordp D.Kt v (D.qroot v ^ m) := by
  induction m with
  | zero => simp [ordp, norm_one]
  | succ k ih =>
    rw [pow_succ, LocalTheory.ordp_mul D.Kt v _ _ (pow_ne_zero _ (D.qroot_ne_zero v))
        (D.qroot_ne_zero v)]
    linarith [D.ordp_qroot_nonneg v]

/-! ### The theta-pilot region, for a set of admissible label positions

`S i ⊆ S_{i+2}` is the set of labels at which the theta value `q^{j²}` (`j = i + 1`) of the
capsule may sit: `{j}` in the reading of IUT IV, proof of Theorem 1.10, Steps (iv)–(v)
(`ivLabels`), and all of `S_{j+1}` for the label permutations of the indeterminacy (Ind1) of
IUT III, Theorem 3.11 (`litLabels`). -/

/-- The theta-pilot component at a finite place: the union of the images of
`⋃_{l ∈ S} q_{v_l}^{j²}·⊗_i 𝓘_{v_i}` under the indeterminacy automorphisms. -/
noncomputable def thetaFiniteOn (i : Fin n) (S : Set (Lab n i)) (p : Nat.Primes)
    (c : Lab n i → LocalTheory.Fiber D.Fmod (.finite p)) :
    Set (LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)) :=
  ⋃ φ ∈ LocalTheory.indAut D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c),
    φ '' (⋃ l ∈ S, D.scaleEltAt n i p c l •
      LocalTheory.shell D.Kt p (LocalTheory.tuple D.placeSect _ c))

/-- The theta-pilot component at any rational place. -/
noncomputable def thetaComponentOn (i : Fin n) (S : Set (Lab n i)) (vQ : RationalPlace)
    (c : Lab n i → LocalTheory.Fiber D.Fmod vQ) :
    Set (LocalTheory.Tensor D.Kt vQ (LocalTheory.tuple D.placeSect vQ c)) :=
  match vQ, c with
  | .finite p, c => D.thetaFiniteOn n i S p c
  | .infinite, c => LocalTheory.thetaInfinite D.placeSect n i c

/-- Each theta-pilot component is admissible for the hull. -/
lemma thetaComponentOn_admissible (i : Fin n) (S : Set (Lab n i)) (hS : S.Nonempty)
    (vQ : RationalPlace) (c : Lab n i → LocalTheory.Fiber D.Fmod vQ) :
    D.thetaComponentOn n i S vQ c ∈
      LocalTheory.admissible D.Kt vQ (LocalTheory.tuple D.placeSect _ c) := by
  rcases vQ with p | _
  · have h := fun l => LocalTheory.smul_shell_bounded_open_pos D.Kt p
      (LocalTheory.tuple D.placeSect _ c)
      _ (D.isUnit_scaleEltAt n i p c l)
    obtain ⟨l₀, hl₀⟩ := hS
    refine LocalTheory.iUnion_indAut_admissible D.Kt p _ ?_ ?_ ?_
    · exact (Bornology.isBounded_biUnion (Set.toFinite S)).mpr fun l _ => (h l).1
    · exact isOpen_biUnion fun l _ => (h l).2.1
    · exact lt_of_lt_of_le (h l₀).2.2 (MeasureTheory.measure_mono
        (Set.subset_biUnion_of_mem (u := fun l => D.scaleEltAt n i p c l •
          LocalTheory.shell D.Kt p (LocalTheory.tuple D.placeSect _ c)) hl₀))
  · exact LocalTheory.thetaShell_admissible D.Kt _ _

/-- At an odd prime which is not a bad residue characteristic and is unramified in `K`, the
theta-pilot component is the integral structure: there all theta values are `1`, the tensor
product of the log-shells is `(R_I)^∼` (IUT I, Definition 5.4.5) and it is preserved by the
indeterminacy automorphisms (IUT IV, Proposition 1.4(iv)). -/
lemma thetaComponentOn_eq_integral (i : Fin n) (S : Set (Lab n i)) (hS : S.Nonempty)
    (p : Nat.Primes) (c : Lab n i → LocalTheory.Fiber D.Fmod (.finite p))
    (hbad : (p : ℕ) ∉ D.badChars) (hodd : Odd (p : ℕ))
    (hunr : ∀ w : FinitePlace D.Kt, residueChar w = p → ramIdx D.Kt w = 1) :
    D.thetaComponentOn n i S (.finite p) c = LocalTheory.integral D.Kt (.finite p)
        (LocalTheory.tuple D.placeSect _ c) := by
  have hscale : ∀ l, D.scaleEltAt n i p c l = 1 := fun l => by
    unfold scaleEltAt
    rw [D.qroot_eq_one _ (by rw [LocalTheory.residueChar_sectPlace D.placeSect]; exact hbad),
        one_pow, map_one]
  have hunr' : ∀ j w, LocalTheory.tuple D.placeSect _ c j = Place.finite w → ramIdx D.Kt w = 1 := by
    intro j w hw
    obtain ⟨w', hw', hres⟩ := LocalTheory.tuple_isOver D.placeSect p c j
    rw [hw] at hw'
    cases Sum.inl.inj hw'
    exact hunr w hres
  have hbase : (⋃ l ∈ S, D.scaleEltAt n i p c l •
      LocalTheory.shell D.Kt p (LocalTheory.tuple D.placeSect _ c)) =
      LocalTheory.shell D.Kt p (LocalTheory.tuple D.placeSect _ c) := by
    simp only [hscale, one_smul]
    exact Set.biUnion_const hS _
  change (⋃ φ ∈ LocalTheory.indAut D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c), φ '' _) = _
  rw [hbase, ← LocalTheory.shell_eq_integral D.Kt p _ (LocalTheory.tuple_isOver D.placeSect p c)
    hodd hunr']
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun φ hφ => (LocalTheory.indAut_shell D.Kt p _ φ hφ).le
  · intro x hx
    exact Set.mem_iUnion₂.mpr ⟨id, LocalTheory.id_mem_indAut D.Kt _ _, ⟨x, hx, rfl⟩⟩

/-- The label position of the theta value in IUT IV's reading: `{j}`. -/
def ivLabels (i : Fin n) : Set (Lab n i) := {distinguished n i}

/-- The label positions of the theta value under the label permutations of (Ind1)
(IUT III, Theorem 3.11): all of `S_{j+1}`. -/
def litLabels (i : Fin n) : Set (Lab n i) := Set.univ

lemma ivLabels_nonempty (i : Fin n) : (ivLabels n i).Nonempty := Set.singleton_nonempty _

lemma litLabels_nonempty (i : Fin n) : (litLabels n i).Nonempty :=
  ⟨distinguished n i, Set.mem_univ _⟩

lemma ivLabels_subset_litLabels (i : Fin n) : ivLabels n i ⊆ litLabels n i :=
  Set.subset_univ _

/-- The theta-pilot component at a finite place, in IUT IV's reading. -/
noncomputable abbrev thetaFinite (i : Fin n) (p : Nat.Primes)
    (c : Lab n i → LocalTheory.Fiber D.Fmod (.finite p)) :=
  D.thetaFiniteOn n i (ivLabels n i) p c

/-- The theta-pilot component, in IUT IV's reading. -/
noncomputable abbrev thetaComponent (i : Fin n) (vQ : RationalPlace)
    (c : Lab n i → LocalTheory.Fiber D.Fmod vQ) :=
  D.thetaComponentOn n i (ivLabels n i) vQ c

lemma thetaFinite_eq (i : Fin n) (p : Nat.Primes)
    (c : Lab n i → LocalTheory.Fiber D.Fmod (.finite p)) :
    D.thetaFinite n i p c =
      ⋃ φ ∈ LocalTheory.indAut D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c),
        φ '' (D.scaleElt n i p c •
          LocalTheory.shell D.Kt p (LocalTheory.tuple D.placeSect _ c)) := by
  unfold thetaFinite thetaFiniteOn ivLabels
  simp only [Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]
  rfl

/-- **The concrete theta-pilot region** of the container at capsule `i`, for the label
positions `S`. -/
noncomputable def thetaPilotOn (S : ∀ i : Fin n, Set (Lab n i)) (hS : ∀ i, (S i).Nonempty)
    (i : Fin (LocalTheory.container D.placeSect n).proc.length) :
    (LocalTheory.container D.placeSect n).AdmissibleRegion i where
  region vQ := (LocalTheory.packet D.placeSect _ vQ).productRegion fun c =>
    D.thetaComponentOn n i (S i) vQ c
  finiteSupport := by
    have hfin : (({RationalPlace.infinite} ∪ {RationalPlace.finite ⟨2, Nat.prime_two⟩} ∪
        ((fun w => LocalTheory.toRational D.Kt (Place.finite w)) '' {w | ramIdx D.Kt w ≠ 1}) ∪
        ((fun q : ℕ => if h : q.Prime then RationalPlace.finite ⟨q, h⟩ else .infinite) ''
          ↑D.badChars) : Set RationalPlace)).Finite :=
      (((Set.finite_singleton _).union (Set.finite_singleton _)).union
        ((LocalTheory.ramified_finite D.Kt).image _)).union (D.badChars.finite_toSet.image _)
    refine hfin.subset fun vQ hvQ => ?_
    by_contra hmem
    apply hvQ
    rcases vQ with p | _
    · have hbad : (p : ℕ) ∉ D.badChars := by
        intro hb
        apply hmem
        refine Or.inr ⟨p, hb, ?_⟩
        simp [p.2]
      have hodd : Odd (p : ℕ) := by
        refine p.2.odd_of_ne_two fun h2 => hmem (Or.inl (Or.inl (Or.inr ?_)))
        change RationalPlace.finite p = RationalPlace.finite ⟨2, Nat.prime_two⟩
        exact congrArg _ (Subtype.ext h2)
      have hunr : ∀ w : FinitePlace D.Kt, residueChar w = p → ramIdx D.Kt w = 1 := by
        intro w hw
        by_contra hram
        apply hmem
        refine Or.inl (Or.inr ⟨w, hram, ?_⟩)
        change RationalPlace.finite _ = RationalPlace.finite p
        exact congrArg _ (Subtype.ext hw)
      change (LocalTheory.packet D.placeSect _ _).productRegion _ =
          (LocalTheory.packet D.placeSect _ _).integralRegion
      ext x
      simp only [DirectSumPresentation.mem_productRegion,
        DirectSumPresentation.mem_integralRegion]
      refine forall_congr' fun c => ?_
      rw [D.thetaComponentOn_eq_integral n i (S i) (hS i) p c hbad hodd hunr]
      rfl
    · exact absurd (Or.inl (Or.inl (Or.inl rfl))) hmem

/-- **The concrete theta-pilot region**, in IUT IV's reading. -/
noncomputable abbrev thetaPilot := D.thetaPilotOn n (ivLabels n) (ivLabels_nonempty n)

/-- **The concrete right-hand-side data** of the Corollary 3.12 variant (taxis #35), for the
label positions `S`. -/
noncomputable def rhsDataOn (S : ∀ i : Fin ((D.ℓ - 1) / 2), Set (Lab ((D.ℓ - 1) / 2) i))
    (hS : ∀ i, (S i).Nonempty) : RHSData.{u, u} D where
  container := LocalTheory.container D.placeSect ((D.ℓ - 1) / 2)
  proc_standard := rfl
  toRational_finite _ := rfl
  toRational_infinite _ := rfl
  vol := LocalTheory.vol D.placeSect _
  hull := LocalTheory.hull D.placeSect _
  thetaPilot := D.thetaPilotOn _ S hS
  thetaPilot_hullAdmissible i vQ :=
    ⟨fun c => D.thetaComponentOn _ i (S i) vQ c,
      fun c => D.thetaComponentOn_admissible _ i (S i) (hS i) vQ c, rfl⟩

/-- **The concrete right-hand-side data**, in IUT IV's reading (`−|log(Θ)|` with the theta
value of the capsule `S_{j+1}` at the label `j`). -/
noncomputable abbrev rhsData : RHSData.{u, u} D :=
  D.rhsDataOn (ivLabels _) (ivLabels_nonempty _)

/-- **The concrete right-hand-side data**, in the literal reading of IUT III, Corollary 3.12
(the union also over the label permutations of (Ind1)). -/
noncomputable abbrev rhsDataLit : RHSData.{u, u} D :=
  D.rhsDataOn (litLabels _) (litLabels_nonempty _)

end InitialThetaData

/-- **The concrete `q`-pilot data** (taxis #34): the bad locus as a finite set
(`InitialThetaData.bad_finite`), and the weights `f_w/[F : ℚ]`, so that `log(q)` is the
normalized degree of the `q`-divisor. -/
noncomputable def InitialThetaData.qPilot : QPilotData D where
  badFinset := D.bad_finite.toFinset
  badFinset_spec := D.bad_finite.coe_toFinset
  weight w := (inertDeg D.F w : ℝ) / Module.finrank ℚ D.F
  weight_pos w _ := div_pos (by exact_mod_cast inertDeg_pos' w) (LocalTheory.finrank_pos D.F)

/-- **The concrete Corollary 3.12 variant data** of initial Θ-data `D`: `D` with its concrete
`q`-pilot data and the concrete right-hand side (the large volume container of the tensor
packets of the `ℓ`-torsion field at the places of the valuation section `V ≅ V_mod`, with the
weights of IUT III, Remark 3.1.1(ii), and the theta-pilot region built from the `2ℓ`-th roots
of the Tate parameters). A function of `D` alone. -/
noncomputable def concreteVariantData : Corollary312VariantData.{u} where
  data := D
  qPilot := D.qPilot
  rhsData := D.rhsData

/-- **The concrete Corollary 3.12 data in the literal reading of IUT III**: as
`concreteVariantData`, with the theta-pilot region taken over all label positions (the label
permutations of the indeterminacy (Ind1) of IUT III, Theorem 3.11). -/
noncomputable def concreteVariantDataLit : Corollary312VariantData.{u} where
  data := D
  qPilot := D.qPilot
  rhsData := D.rhsDataLit

/-- **The Corollary 3.12 variant** (IUT III, Corollary 3.12, in the form of IUT IV,
Theorem 1.10's input): for all initial Θ-data `D` (IUT I, Definition 3.1, stated about the
genuine étale and tempered fundamental groups of the model orbicurves), the concrete variant
data of `D` satisfy the variant inequality `−|log(q)| ≤ −|log(Θ)|`. -/
def Cor312VariantHolds : Prop :=
  ∀ D : InitialThetaData.{0}, Corollary312Variant (concreteVariantData D)

/-- **The Corollary 3.12 variant, literal reading of IUT III**: as `Cor312VariantHolds`, with
the union of the possible images of the theta-pilot taken also over the label permutations of
the indeterminacy (Ind1) of IUT III, Theorem 3.11 (`concreteVariantDataLit`). It is implied by
`Cor312VariantHolds` (`cor312Literal_of_variant`, `Iut/Concrete/Literal.lean`); the converse is
the step from the literal Corollary 3.12 to IUT IV, proof of Theorem 1.10, Steps (iv)–(v). -/
def Cor312LiteralHolds : Prop :=
  ∀ D : InitialThetaData.{0}, Corollary312Variant (concreteVariantDataLit D)

end Iut
