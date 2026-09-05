/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.Container
import Iut.Cor312.Statement

/-!
# The concrete theta-pilot region and the concrete variant data (taxis #278, #1449)

This file fills the remaining inputs of the Corollary 3.12 variant with concrete
implementations, given initial Θ-data `D`, the local-field theory `LT` of its
`ℓ`-torsion field `K`, and the local theta data `TL` (the `2ℓ`-th roots of the Tate
parameters at the bad places of `K`).

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

universe u v

open NumberField
open scoped Pointwise

namespace LocalTheory

variable {K : Type u} [Field K] [NumberField K] (LT : LocalTheory.{u, v} K)

/-- The finite place underlying an element of the fiber over a prime. -/
noncomputable def fiberPlace {p : Nat.Primes} (v : LT.Fiber (.finite p)) : FinitePlace K :=
  (LT.fiberFiniteEquiv p v).1

lemma fiberPlace_spec {p : Nat.Primes} (v : LT.Fiber (.finite p)) :
    v.1 = Place.finite (LT.fiberPlace v) := by
  rcases v with ⟨v, hv⟩
  rcases v with w | w
  · rfl
  · exact absurd hv (by simp [toRational])

lemma residueChar_fiberPlace {p : Nat.Primes} (v : LT.Fiber (.finite p)) :
    residueChar (LT.fiberPlace v) = p :=
  (LT.fiberFiniteEquiv p v).2

/-- The theta-pilot component at the archimedean place: the union of the images of the
tensor product of the log-shells under the indeterminacy automorphisms. -/
noncomputable def thetaInfinite (n : ℕ) (i : Fin n)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber .infinite) :
    Set (LT.Tensor .infinite (LT.tuple .infinite c)) :=
  ⋃ φ ∈ LT.indAut .infinite (LT.tuple .infinite c),
    φ '' LT.logShell .infinite (LT.tuple .infinite c)

end LocalTheory

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (D : InitialThetaData AG TG)

/-- The `ℓ`-torsion field of the Θ-data, as a type. -/
abbrev InitialThetaData.Kt : Type u := ↥D.prime.torsionField

/-- **The local theta data**: the `2ℓ`-th roots `q_v = q^{1/2ℓ}` of the Tate parameters at
the places of `K` over the bad places of `F` (IUT I, Example 3.2(iv)), with the
comparison map of completions `F_w → K_v`. Delegated: the existence of the roots follows
from the rationality of the `2ℓ`-torsion of the Tate curve over `K_v` (taxis #13/#36,
`lana-agents/tate-curves-theta`). The places whose residue characteristic is not in the
finite set `badChars` (the residue characteristics of the bad places) carry `q_v = 1`. -/
structure ThetaLocalData (LT : LocalTheory.{u, v} D.Kt) where
  /-- The residue characteristics of the bad places. -/
  badChars : Finset ℕ
  /-- The `2ℓ`-th root of the Tate parameter at `v` (`1` away from the bad places). -/
  qroot : ∀ v : FinitePlace D.Kt, completionAt D.Kt v
  /-- `q_v ≠ 0`. -/
  qroot_ne_zero : ∀ v, qroot v ≠ 0
  /-- `ord_p(q_v) ≥ 0`. -/
  ordp_qroot_nonneg : ∀ v, 0 ≤ ordp D.Kt v (qroot v)
  /-- Away from the bad residue characteristics, `q_v = 1`. -/
  qroot_eq_one : ∀ v, residueChar v ∉ badChars → qroot v = 1
  /-- The comparison map of completions `F_w → K_v` for `v ∣ w`. -/
  embedF : ∀ (v : FinitePlace D.Kt) (w : FinitePlace D.F),
    (Place.finite v).LiesOver (Place.finite w) → localCompletion w →+* completionAt D.Kt v
  /-- `q_v^{2ℓ}` is the Tate parameter of `E` at `w` (IUT I, Example 3.2(iv)). -/
  qroot_pow : ∀ (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : (Place.finite v).LiesOver (Place.finite w)) (hw : w ∈ badPlacesOver D.F D.E D.VBad),
    qroot v ^ (2 * D.ℓ) = embedF v w h ((D.prime.tate w hw).q : localCompletion w)
  /-- `ord_p(q_v) = ord_w(q_w)/(2ℓ·e_w)`: the normalized order of the root, from the
  integer order of the Tate parameter (taxis #37) and the ramification index of `w`. -/
  ordp_qroot : ∀ (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (_ : (Place.finite v).LiesOver (Place.finite w)) (hw : w ∈ badPlacesOver D.F D.E D.VBad),
    ordp D.Kt v (qroot v) = (D.prime.qOrder w hw : ℝ) / (2 * D.ℓ * ramIdx D.F w)
  /-- The bad places of `K` have residue characteristic in `badChars`. -/
  residueChar_mem : ∀ (v : FinitePlace D.Kt) (w : FinitePlace D.F),
    (Place.finite v).LiesOver (Place.finite w) → w ∈ badPlacesOver D.F D.E D.VBad →
    residueChar v ∈ badChars
  /-- The bad places of `F` have residue characteristic in `badChars`. -/
  bad_residueChar_mem : ∀ w ∈ badPlacesOver D.F D.E D.VBad, residueChar w ∈ badChars
  /-- The bad residue characteristics are prime. -/
  badChars_prime : ∀ p ∈ badChars, p.Prime
  /-- **Base-change invariance of the `q`-degree** at each prime `p`: the weighted sum
  over the places `v ∣ p` of `K` of `[K_v : ℚ_p]/[K : ℚ]·ord_p(q_v)` equals
  `(1/2ℓ)·∑_{w ∣ p, w bad} (f_w/[F : ℚ])·ord_w(q_w)` (from `∑_{v ∣ w} e_v f_v = [K : F]·e_w f_w`
  and `ord_p(q_v) = ord_w(q_w)/(2ℓ e_w)`). -/
  sum_weight_ordp_qroot : ∀ (p : Nat.Primes) (bad : Finset (FinitePlace D.F))
    (hbad : ↑bad = badPlacesOver D.F D.E D.VBad),
    ∑ v : LT.Fiber (.finite p), LT.weight (.finite p) v * ordp D.Kt (LT.fiberPlace v)
        (qroot (LT.fiberPlace v)) =
      (∑ w ∈ bad.attach.filter (fun w => residueChar w.1 = p),
        (inertDeg D.F w.1 : ℝ) / Module.finrank ℚ D.F *
          (D.prime.qOrder w.1 (hbad ▸ Finset.mem_coe.mpr w.2) : ℝ)) / (2 * D.ℓ)

variable (LT : LocalTheory.{u, v} D.Kt) (TL : ThetaLocalData D LT)


namespace ThetaLocalData

variable {D LT}
variable (n : ℕ)

/-- The distinguished label `j = i + 1` of the capsule `S_{j+1} = {0, …, i+1}` of the
standard procession. -/
def distinguished (i : Fin n) : ((Procession.standard n).capsule i).LabelType :=
  ⟨i.1 + 1, by simp [Procession.standard, procLabels]⟩

/-- The scaling element `q_{v_j}^{j²}` of a tuple at a finite place, in the `j`-th tensor
factor. -/
noncomputable def scaleElt (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber (.finite p)) :
    LT.Tensor (.finite p) (LT.tuple _ c) :=
  LT.incl p (LT.tuple _ c) (distinguished n i) (LT.fiberPlace (c (distinguished n i)))
    (LT.fiberPlace_spec _) (TL.qroot (LT.fiberPlace (c (distinguished n i))) ^ (i.1 + 1) ^ 2)

lemma isUnit_scaleElt (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber (.finite p)) :
    IsUnit (TL.scaleElt n i p c) :=
  LT.isUnit_incl p _ _ _ _ _ (pow_ne_zero _ (TL.qroot_ne_zero _))

/-- `ord_p` of the scaling element's root: `j²·ord_p(q_{v_j}) ≥ 0`. -/
lemma ordp_pow_nonneg (v : FinitePlace D.Kt) (m : ℕ) :
    0 ≤ ordp D.Kt v (TL.qroot v ^ m) := by
  induction m with
  | zero => simp [ordp, norm_one]
  | succ k ih =>
    rw [pow_succ, LT.ordp_mul v _ _ (pow_ne_zero _ (TL.qroot_ne_zero v)) (TL.qroot_ne_zero v)]
    linarith [TL.ordp_qroot_nonneg v]

/-- The theta-pilot component at a finite place: the union of the images of
`q_{v_j}^{j²}·(R_I)^∼` under the indeterminacy automorphisms. -/
noncomputable def thetaFinite (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber (.finite p)) :
    Set (LT.Tensor (.finite p) (LT.tuple _ c)) :=
  ⋃ φ ∈ LT.indAut (.finite p) (LT.tuple _ c),
    φ '' (TL.scaleElt n i p c • LT.integral (.finite p) (LT.tuple _ c))

/-- The theta-pilot component at any rational place. -/
noncomputable def thetaComponent (i : Fin n) (vQ : RationalPlace)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber vQ) :
    Set (LT.Tensor vQ (LT.tuple vQ c)) :=
  match vQ, c with
  | .finite p, c => TL.thetaFinite n i p c
  | .infinite, c => LT.thetaInfinite n i c

/-- Each theta-pilot component is admissible for the hull. -/
lemma thetaComponent_admissible (i : Fin n) (vQ : RationalPlace)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber vQ) :
    TL.thetaComponent n i vQ c ∈ LT.admissible vQ (LT.tuple _ c) := by
  rcases vQ with p | _
  · exact LT.theta_admissible _ _ _ (TL.isUnit_scaleElt n i p c)
  · exact LT.thetaShell_admissible _ _

/-- Each theta-pilot component lies in the log-shell. -/
lemma thetaComponent_subset_logShell (i : Fin n) (vQ : RationalPlace)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber vQ) :
    TL.thetaComponent n i vQ c ⊆ LT.logShell vQ (LT.tuple _ c) := by
  rcases vQ with p | _
  · intro x hx
    change x ∈ ⋃ φ ∈ LT.indAut (.finite p) (LT.tuple _ c),
      φ '' (TL.scaleElt n i p c • LT.integral (.finite p) (LT.tuple _ c)) at hx
    obtain ⟨φ, hφ, hx⟩ := Set.mem_iUnion₂.mp hx
    refine LT.indAut_logShell _ _ φ hφ (Set.image_mono ?_ hx)
    exact (LT.smul_integral_subset p _ _ _ _ _ (pow_ne_zero _ (TL.qroot_ne_zero _))
      (TL.ordp_pow_nonneg _ _)).trans (LT.integral_subset_logShell p _)
  · intro x hx
    change x ∈ ⋃ φ ∈ LT.indAut .infinite (LT.tuple .infinite c),
      φ '' LT.logShell .infinite (LT.tuple .infinite c) at hx
    obtain ⟨φ, hφ, hx⟩ := Set.mem_iUnion₂.mp hx
    exact LT.indAut_logShell _ _ φ hφ hx

/-- Away from the bad residue characteristics, the theta-pilot component is the integral
structure (the indeterminacy automorphisms preserve the maximal order at every prime). -/
lemma thetaComponent_eq_integral (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber (.finite p))
    (hbad : (p : ℕ) ∉ TL.badChars) :
    TL.thetaComponent n i (.finite p) c = LT.integral (.finite p) (LT.tuple _ c) := by
  have hscale : TL.scaleElt n i p c = 1 := by
    unfold scaleElt
    rw [TL.qroot_eq_one _ (by rw [LT.residueChar_fiberPlace]; exact hbad), one_pow, map_one]
  apply Set.Subset.antisymm
  · intro x hx
    change x ∈ ⋃ φ ∈ LT.indAut (.finite p) (LT.tuple _ c),
      φ '' (TL.scaleElt n i p c • LT.integral (.finite p) (LT.tuple _ c)) at hx
    obtain ⟨φ, hφ, hx⟩ := Set.mem_iUnion₂.mp hx
    rw [hscale, one_smul] at hx
    exact LT.prop14_iv p _ φ hφ hx
  · intro x hx
    change x ∈ ⋃ φ ∈ LT.indAut (.finite p) (LT.tuple _ c),
      φ '' (TL.scaleElt n i p c • LT.integral (.finite p) (LT.tuple _ c))
    exact Set.mem_iUnion₂.mpr ⟨id, LT.id_mem_indAut _ _, by
      rw [hscale, one_smul]; exact ⟨x, hx, rfl⟩⟩

/-- **The concrete theta-pilot region** of the container at capsule `i`. -/
noncomputable def thetaPilot (i : Fin (LT.container n).proc.length) :
    (LT.container n).AdmissibleRegion i where
  region vQ := (LT.packet _ vQ).productRegion fun c => TL.thetaComponent n i vQ c
  finiteSupport := by
    have hfin : (({RationalPlace.infinite} ∪ {RationalPlace.finite ⟨2, Nat.prime_two⟩} ∪
        ((fun w => LT.toRational (Place.finite w)) '' {w | ramIdx D.Kt w ≠ 1}) ∪
        ((fun q : ℕ => if h : q.Prime then RationalPlace.finite ⟨q, h⟩ else .infinite) ''
          ↑TL.badChars) : Set RationalPlace)).Finite :=
      (((Set.finite_singleton _).union (Set.finite_singleton _)).union
        (LT.ramified_finite.image _)).union (TL.badChars.finite_toSet.image _)
    refine hfin.subset fun vQ hvQ => ?_
    by_contra hmem
    apply hvQ
    rcases vQ with p | _
    · have hbad : (p : ℕ) ∉ TL.badChars := by
        intro hb
        apply hmem
        refine Or.inr ⟨p, hb, ?_⟩
        simp [p.2]
      change (LT.packet _ _).productRegion _ = (LT.packet _ _).integralRegion
      ext x
      simp only [DirectSumPresentation.mem_productRegion,
        DirectSumPresentation.mem_integralRegion]
      refine forall_congr' fun c => ?_
      rw [TL.thetaComponent_eq_integral n i p c hbad]
      rfl
    · exact absurd (Or.inl (Or.inl (Or.inl rfl))) hmem

/-- **The concrete right-hand-side data** of the Corollary 3.12 variant (taxis #35). -/
noncomputable def rhsData : RHSData.{u, v} D where
  container := LT.container ((D.ℓ - 1) / 2)
  proc_standard := rfl
  toRational_finite _ := rfl
  toRational_infinite _ := rfl
  vol := LT.vol _
  hull := LT.hull _
  thetaPilot := TL.thetaPilot _
  thetaPilot_hullAdmissible i vQ :=
    ⟨fun c => TL.thetaComponent _ i vQ c, fun c => TL.thetaComponent_admissible _ i vQ c, rfl⟩
  thetaPilot_le_shell i vQ _ hx c :=
    TL.thetaComponent_subset_logShell _ i vQ c (hx c)

end ThetaLocalData

/-- **The inputs of the concrete `q`-pilot data**: finiteness of the bad locus and
positivity of residue degrees (standard; taxis #5, `lana-agents/elliptic-reduction`). -/
structure QPilotInputs where
  /-- The bad locus `V(F)^bad` is finite. -/
  bad_finite : (badPlacesOver D.F D.E D.VBad).Finite
  /-- Residue degrees are positive. -/
  inertDeg_pos : ∀ w : FinitePlace D.F, 0 < inertDeg D.F w

/-- **The concrete `q`-pilot data** (taxis #34): the bad locus as a finite set, and the
weights `f_w/[F : ℚ]`, so that `log(q)` is the normalized degree of the `q`-divisor. -/
noncomputable def QPilotInputs.qPilot (QI : QPilotInputs D) : QPilotData D where
  badFinset := QI.bad_finite.toFinset
  badFinset_spec := QI.bad_finite.coe_toFinset
  weight w := (inertDeg D.F w : ℝ) / Module.finrank ℚ D.F
  weight_pos w _ := div_pos (by exact_mod_cast QI.inertDeg_pos w) (LocalTheory.finrank_pos)

/-- **The concrete Corollary 3.12 variant data**: initial Θ-data with the concrete
`q`-pilot data and the concrete right-hand side. -/
noncomputable def concreteVariantData (QI : QPilotInputs D) :
    Corollary312VariantData.{u, v} AG TG where
  data := D
  qPilot := QI.qPilot
  rhsData := TL.rhsData

end Iut
