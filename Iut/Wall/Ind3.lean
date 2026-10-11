/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Wall.Rss

/-!
# The log-shell container `VC(I)` and the (Ind3)-choices `S ⊆ VC(I)` (the wall, M1b/M1c)

[LANA] (the LANA interim report, July 2026), §5.2(b), §6 (Ind3), §9.2: the η-algorithm reads
its output inside the log-shell version `VC(I)` of the large volume container, and the
indeterminacy (Ind3) means that "instead of just `VC(O)`, we must take into account all"
adelic measurable subsets `S ⊆ VC(I)`.

* `vcI D`: the log-shell container, capsule-wise: at a prime `p` the product over the tuples
  `c` of the tensor products of the log-shells `⊗_j 𝓘_{c_j}` (`LocalTheory.shell`, the base
  region of the theta-pilot region, IUT III, Proposition 3.2), at `∞` the product of the
  archimedean log-shells (`LocalTheory.logShell`, IUT III, Proposition 3.2(ii)). It is adelic
  (`isAdelic_vcI`).
* `Ind3 D`: the (Ind3)-choices, i.e. the adelic regions `S ⊆ VC(I)`.
* `exists_ind3_logVol_iff`: the log-volumes of the (Ind3)-choices are exactly
  `ℝ_{≤ log-vol(VC(I))}` (non-atomicity, realized by the archimedean rescaling).

**Deviation.** [LANA], §5.2(b), forms `VC(I)` with `⊗_{ℤ_{v_ℚ}}`; at a prime we use the
`ℤ_p`-span of the elementary tensors of log-shell elements (`LocalConstruct.tensorLogShell`),
which is the image of that tensor product in the tensor packet, i.e. the base region of the
concrete theta-pilot region (`InitialThetaData.thetaFiniteOn`).
-/

namespace Iut

open NumberField MeasureTheory
open scoped Pointwise

universe u

namespace Wall

variable (D : InitialThetaData.{u})

/-- The components of the log-shell container. -/
noncomputable def vcIComp (i : Fin (nC D)) :
    ∀ (vQ : RationalPlace) (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ),
      Set (LocalTheory.Tensor D.Kt vQ (LocalTheory.tuple D.placeSect vQ c))
  | .finite p, c => LocalTheory.shell D.Kt p (LocalTheory.tuple D.placeSect _ c)
  | .infinite, c => LocalTheory.logShell D.Kt .infinite (LocalTheory.tuple D.placeSect _ c)

lemma vcIComp_admissible (i : Fin (nC D)) (vQ : RationalPlace)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ) :
    vcIComp D i vQ c ∈ LocalTheory.admissible D.Kt vQ (LocalTheory.tuple D.placeSect vQ c) := by
  rcases vQ with p | _
  · obtain ⟨hb, ho, hpos⟩ := LocalTheory.smul_shell_bounded_open_pos D.Kt p
      (LocalTheory.tuple D.placeSect _ c) 1 isUnit_one
    rw [one_smul] at hb ho hpos
    exact ⟨nonempty_of_measure_ne_zero hpos.ne', hb.isCompact_closure, ho.measurableSet, hpos,
      hb.measure_lt_top⟩
  · have hpos := LocalConstruct.haar_archLogShell_pos (LocalTheory.tuple D.placeSect .infinite c)
    exact ⟨nonempty_of_measure_ne_zero hpos.ne',
      LocalConstruct.isCompact_closure_archLogShell _,
      (LocalConstruct.isClosed_archLogShell _).measurableSet, hpos,
      (LocalConstruct.isCompact_archLogShell _).measure_lt_top⟩

/-- **The log-shell container `VC(I)`** at capsule `i` ([LANA], §5.2(b)). -/
noncomputable def vcIAt (i : Fin (VC D).proc.length) : (VC D).AdmissibleRegion i where
  region vQ := (LocalTheory.packet D.placeSect _ vQ).productRegion fun c => vcIComp D i vQ c
  finiteSupport := by
    have hfin : (({RationalPlace.infinite} ∪ {RationalPlace.finite ⟨2, Nat.prime_two⟩} ∪
        ((fun w => LocalTheory.toRational D.Kt (Place.finite w)) '' {w | ramIdx D.Kt w ≠ 1}) :
          Set RationalPlace)).Finite :=
      ((Set.finite_singleton _).union (Set.finite_singleton _)).union
        ((LocalTheory.ramified_finite D.Kt).image _)
    refine hfin.subset fun vQ hvQ => ?_
    by_contra hmem
    apply hvQ
    rcases vQ with p | _
    · have hodd : Odd (p : ℕ) := by
        refine p.2.odd_of_ne_two fun h2 => hmem (Or.inl (Or.inr ?_))
        change RationalPlace.finite p = RationalPlace.finite ⟨2, Nat.prime_two⟩
        exact congrArg _ (Subtype.ext h2)
      have hunr : ∀ w : FinitePlace D.Kt, residueChar w = p → ramIdx D.Kt w = 1 := by
        intro w hw
        by_contra hram
        apply hmem
        refine Or.inr ⟨w, hram, ?_⟩
        change RationalPlace.finite _ = RationalPlace.finite p
        exact congrArg _ (Subtype.ext hw)
      change (LocalTheory.packet D.placeSect _ _).productRegion _ =
          (LocalTheory.packet D.placeSect _ _).integralRegion
      ext x
      simp only [DirectSumPresentation.mem_productRegion,
        DirectSumPresentation.mem_integralRegion]
      refine forall_congr' fun c => ?_
      have hunr' : ∀ j w, LocalTheory.tuple D.placeSect _ c j = Place.finite w →
          ramIdx D.Kt w = 1 := by
        intro j w hw
        obtain ⟨w', hw', hres⟩ := LocalTheory.tuple_isOver D.placeSect p c j
        rw [hw] at hw'
        cases Sum.inl.inj hw'
        exact hunr w hres
      change x c ∈ LocalTheory.shell D.Kt p _ ↔ _
      rw [LocalTheory.shell_eq_integral D.Kt p _ (LocalTheory.tuple_isOver D.placeSect p c)
        hodd hunr']
      rfl
    · exact absurd (Or.inl (Or.inl rfl)) hmem

/-- **The log-shell container `VC(I)`.** -/
noncomputable def vcI : Region D := vcIAt D

lemma isAdelic_vcI : IsAdelic D (vcI D) := fun i vQ =>
  ⟨fun c => vcIComp D i vQ c, fun c => vcIComp_admissible D i vQ c, rfl⟩

/-- **The (Ind3)-choices** ([LANA], §6 (Ind3), §9.2): the adelic measurable regions
`S ⊆ VC(I)`. -/
def Ind3 : Type _ := {S : Region D // IsAdelic D S ∧ ∀ i, S i ≤ vcI D i}

/-- `VC(I)` itself is an (Ind3)-choice. -/
noncomputable def Ind3.top : Ind3 D := ⟨vcI D, isAdelic_vcI D, fun _ _ => subset_rfl⟩

instance : Nonempty (Ind3 D) := ⟨Ind3.top D⟩

/-- Rescaling `VC(I)` at `∞` by `0 < t ≤ 1` stays inside `VC(I)` (the archimedean log-shell is
balanced). -/
lemma archScale_vcI_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (i) :
    archScale D t (vcI D) i ≤ vcI D i := by
  intro vQ
  rcases vQ with p | _
  · exact subset_rfl
  · intro y hy c
    have hy' : y c ∈ t • LocalTheory.proj D.placeSect .infinite c ((vcI D i).region .infinite) :=
      hy c
    rw [show (vcI D i).region .infinite = (LocalTheory.packet D.placeSect _ .infinite).productRegion
      (fun c => vcIComp D i .infinite c) from rfl,
      LocalTheory.proj_productRegion D.placeSect _ _
        (fun c => (vcIComp_admissible D i .infinite c).1) c] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    rw [← hzy]
    exact (LocalConstruct.absConvex_archLogShell _).1.smul_mem
      (by rw [Real.norm_eq_abs, abs_of_pos ht]; exact ht1) hz

/-- An (Ind3)-choice has log-volume at most that of `VC(I)`. -/
lemma logVol_le_vcI (S : Ind3 D) : logVol D S.1 ≤ logVol D (vcI D) := by
  refine LocalTheory.processionVol_le_of_packetVol _ _ _ _ fun i vQ => ?_
  refine LocalTheory.packetVol_le_of_subset _ _ i vQ (S.2.1 i vQ) (fun c => ?_) (S.2.2 i vQ)
  change LocalConstruct.haar vQ _ (LocalTheory.proj D.placeSect vQ c
    ((LocalTheory.packet D.placeSect _ vQ).productRegion fun c => vcIComp D i vQ c)) < ⊤
  rw [LocalTheory.proj_productRegion D.placeSect _ _
    (fun c => (vcIComp_admissible D i vQ c).1) c]
  exact (vcIComp_admissible D i vQ c).2.2.2.2

/-- **The log-volumes of the (Ind3)-choices are exactly `ℝ_{≤ log-vol(VC(I))}`.** -/
theorem exists_ind3_logVol_iff (x : ℝ) :
    (∃ S : Ind3 D, logVol D S.1 = x) ↔ x ≤ logVol D (vcI D) := by
  constructor
  · rintro ⟨S, rfl⟩
    exact logVol_le_vcI D S
  · intro hx
    set t := Real.exp (x - logVol D (vcI D))
    have ht : 0 < t := Real.exp_pos _
    have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    refine ⟨⟨archScale D t (vcI D), isAdelic_archScale D ht (isAdelic_vcI D),
      archScale_vcI_le D ht ht1⟩, ?_⟩
    change logVol D (archScale D t (vcI D)) = x
    rw [logVol_archScale D ht (isAdelic_vcI D), Real.log_exp]
    ring

end Wall

end Iut
