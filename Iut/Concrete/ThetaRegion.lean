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
`ℓ`-torsion field `K` (`Iut.LocalTheory`) and its local theta data (the `2ℓ`-th roots
`InitialThetaData.qroot` of the Tate parameters at the bad places of `K`).

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

variable (n : ℕ)

/-- The distinguished label `j = i + 1` of the capsule `S_{j+1} = {0, …, i+1}` of the
standard procession. -/
def distinguished (i : Fin n) : ((Procession.standard n).capsule i).LabelType :=
  ⟨i.1 + 1, by simp [Procession.standard, procLabels]⟩

/-- The scaling element `q_{v_j}^{j²}` of a tuple at a finite place, in the `j`-th tensor
factor. -/
noncomputable def scaleElt (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber D.Kt (.finite p)) :
    LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c) :=
  LocalTheory.incl D.Kt p (LocalTheory.tuple D.Kt _ c) (distinguished n i)
      (LocalTheory.fiberPlace D.Kt (c (distinguished n i)))
    (LocalTheory.fiberPlace_spec D.Kt _)
        (D.qroot (LocalTheory.fiberPlace D.Kt (c (distinguished n i))) ^ (i.1 + 1) ^ 2)

lemma isUnit_scaleElt (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber D.Kt (.finite p)) :
    IsUnit (D.scaleElt n i p c) :=
  LocalTheory.isUnit_incl D.Kt p _ _ _ _ _ (pow_ne_zero _ (D.qroot_ne_zero _))

/-- `ord_p` of the scaling element's root: `j²·ord_p(q_{v_j}) ≥ 0`. -/
lemma ordp_pow_nonneg (v : FinitePlace D.Kt) (m : ℕ) :
    0 ≤ ordp D.Kt v (D.qroot v ^ m) := by
  induction m with
  | zero => simp [ordp, norm_one]
  | succ k ih =>
    rw [pow_succ, LocalTheory.ordp_mul D.Kt v _ _ (pow_ne_zero _ (D.qroot_ne_zero v))
        (D.qroot_ne_zero v)]
    linarith [D.ordp_qroot_nonneg v]

/-- The theta-pilot component at a finite place: the union of the images of
`q_{v_j}^{j²}·(R_I)^∼` under the indeterminacy automorphisms. -/
noncomputable def thetaFinite (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber D.Kt (.finite p)) :
    Set (LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c)) :=
  ⋃ φ ∈ LocalTheory.indAut D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c),
    φ '' (D.scaleElt n i p c • LocalTheory.integral D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c))

/-- The theta-pilot component at any rational place. -/
noncomputable def thetaComponent (i : Fin n) (vQ : RationalPlace)
    (c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber D.Kt vQ) :
    Set (LocalTheory.Tensor D.Kt vQ (LocalTheory.tuple D.Kt vQ c)) :=
  match vQ, c with
  | .finite p, c => D.thetaFinite n i p c
  | .infinite, c => LocalTheory.thetaInfinite D.Kt n i c

/-- Each theta-pilot component is admissible for the hull. -/
lemma thetaComponent_admissible (i : Fin n) (vQ : RationalPlace)
    (c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber D.Kt vQ) :
    D.thetaComponent n i vQ c ∈ LocalTheory.admissible D.Kt vQ (LocalTheory.tuple D.Kt _ c) := by
  rcases vQ with p | _
  · exact LocalTheory.theta_admissible D.Kt _ _ _ (D.isUnit_scaleElt n i p c)
  · exact LocalTheory.thetaShell_admissible D.Kt _ _

/-- Each theta-pilot component lies in the log-shell. -/
lemma thetaComponent_subset_logShell (i : Fin n) (vQ : RationalPlace)
    (c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber D.Kt vQ) :
    D.thetaComponent n i vQ c ⊆ LocalTheory.logShell D.Kt vQ (LocalTheory.tuple D.Kt _ c) := by
  rcases vQ with p | _
  · intro x hx
    change x ∈ ⋃ φ ∈ LocalTheory.indAut D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c),
      φ '' (D.scaleElt n i p c • LocalTheory.integral D.Kt (.finite p)
          (LocalTheory.tuple D.Kt _ c)) at hx
    obtain ⟨φ, hφ, hx⟩ := Set.mem_iUnion₂.mp hx
    refine LocalTheory.indAut_logShell D.Kt _ _ φ hφ (Set.image_mono ?_ hx)
    exact (LocalTheory.smul_integral_subset D.Kt p _ _ _ _ _ (pow_ne_zero _ (D.qroot_ne_zero _))
      (D.ordp_pow_nonneg _ _)).trans (LocalTheory.integral_subset_logShell D.Kt p _)
  · intro x hx
    change x ∈ ⋃ φ ∈ LocalTheory.indAut D.Kt .infinite (LocalTheory.tuple D.Kt .infinite c),
      φ '' LocalTheory.logShell D.Kt .infinite (LocalTheory.tuple D.Kt .infinite c) at hx
    obtain ⟨φ, hφ, hx⟩ := Set.mem_iUnion₂.mp hx
    exact LocalTheory.indAut_logShell D.Kt _ _ φ hφ hx

/-- Away from the bad residue characteristics, the theta-pilot component is the integral
structure (the indeterminacy automorphisms preserve the maximal order at every prime). -/
lemma thetaComponent_eq_integral (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber D.Kt (.finite p))
    (hbad : (p : ℕ) ∉ D.badChars) :
    D.thetaComponent n i (.finite p) c = LocalTheory.integral D.Kt (.finite p)
        (LocalTheory.tuple D.Kt _ c) := by
  have hscale : D.scaleElt n i p c = 1 := by
    unfold scaleElt
    rw [D.qroot_eq_one _ (by rw [LocalTheory.residueChar_fiberPlace D.Kt]; exact hbad),
        one_pow, map_one]
  apply Set.Subset.antisymm
  · intro x hx
    change x ∈ ⋃ φ ∈ LocalTheory.indAut D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c),
      φ '' (D.scaleElt n i p c • LocalTheory.integral D.Kt (.finite p)
          (LocalTheory.tuple D.Kt _ c)) at hx
    obtain ⟨φ, hφ, hx⟩ := Set.mem_iUnion₂.mp hx
    rw [hscale, one_smul] at hx
    exact LocalTheory.prop14_iv D.Kt p _ φ hφ hx
  · intro x hx
    change x ∈ ⋃ φ ∈ LocalTheory.indAut D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c),
      φ '' (D.scaleElt n i p c • LocalTheory.integral D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c))
    exact Set.mem_iUnion₂.mpr ⟨id, LocalTheory.id_mem_indAut D.Kt _ _, by
      rw [hscale, one_smul]; exact ⟨x, hx, rfl⟩⟩

/-- **The concrete theta-pilot region** of the container at capsule `i`. -/
noncomputable def thetaPilot (i : Fin (LocalTheory.container D.Kt n).proc.length) :
    (LocalTheory.container D.Kt n).AdmissibleRegion i where
  region vQ := (LocalTheory.packet D.Kt _ vQ).productRegion fun c => D.thetaComponent n i vQ c
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
      change (LocalTheory.packet D.Kt _ _).productRegion _ =
          (LocalTheory.packet D.Kt _ _).integralRegion
      ext x
      simp only [DirectSumPresentation.mem_productRegion,
        DirectSumPresentation.mem_integralRegion]
      refine forall_congr' fun c => ?_
      rw [D.thetaComponent_eq_integral n i p c hbad]
      rfl
    · exact absurd (Or.inl (Or.inl (Or.inl rfl))) hmem

/-- **The concrete right-hand-side data** of the Corollary 3.12 variant (taxis #35). -/
noncomputable def rhsData : RHSData.{u, u} D where
  container := LocalTheory.container D.Kt ((D.ℓ - 1) / 2)
  proc_standard := rfl
  toRational_finite _ := rfl
  toRational_infinite _ := rfl
  vol := LocalTheory.vol D.Kt _
  hull := LocalTheory.hull D.Kt _
  thetaPilot := D.thetaPilot _
  thetaPilot_hullAdmissible i vQ :=
    ⟨fun c => D.thetaComponent _ i vQ c, fun c => D.thetaComponent_admissible _ i vQ c, rfl⟩
  thetaPilot_le_shell i vQ _ hx c :=
    D.thetaComponent_subset_logShell _ i vQ c (hx c)

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
packets of the `ℓ`-torsion field, with the theta-pilot region built from the `2ℓ`-th roots
of the Tate parameters). A function of `D` alone. -/
noncomputable def concreteVariantData : Corollary312VariantData.{u} where
  data := D
  qPilot := D.qPilot
  rhsData := D.rhsData

/-- **The Corollary 3.12 variant** (IUT III, Corollary 3.12, in the form of IUT IV,
Theorem 1.10's input): for all initial Θ-data `D` (IUT I, Definition 3.1, stated about the
genuine étale and tempered fundamental groups of the model orbicurves), the concrete variant
data of `D` satisfy the variant inequality `−|log(Θ)| ≤ −|log(q)|`. -/
def Cor312VariantHolds : Prop :=
  ∀ D : InitialThetaData.{0}, Corollary312Variant (concreteVariantData D)

end Iut
