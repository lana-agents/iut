/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Wall.Rss

/-!
# The log-shell container `VC(I)`, its hull, and the (Ind3)-choices `S ⊆ hull(VC(I))`
(the wall, M1b/M1c)

[LANA] (the LANA interim report, July 2026), §5.2(b), §6 (Ind3), §9.2: the η-algorithm reads
its output inside the log-shell version `VC(I)` of the large volume container, and the
indeterminacy (Ind3) means that "instead of just `VC(O)`, we must take into account all"
adelic measurable subsets `S ⊆ VC(I)`.

* `vcI D`: the log-shell container, capsule-wise: at a prime `p` the product over the tuples
  `c` of the tensor products of the log-shells `⊗_j 𝓘_{c_j}` (`LocalTheory.shell`, the base
  region of the theta-pilot region, IUT III, Proposition 3.2), at `∞` the product of the
  archimedean log-shells (`LocalTheory.logShell`, IUT III, Proposition 3.2(ii)). It is adelic
  (`isAdelic_vcI`).
* `hullOf D (vcI D)`: its holomorphic hull (`isAdelic_hullOf_vcI`, `vcI_le_hullOf`).
* `Ind3 D`: the (Ind3)-choices, the adelic regions `S ⊆ hull(VC(I))`; `Ind3.top` is the hull,
  `Ind3.base` is `VC(I)`.
* `exists_ind3_logVol_iff`: the log-volumes of the (Ind3)-choices are exactly
  `ℝ_{≤ log-vol(hull(VC(I)))}` (non-atomicity, realized by the archimedean rescaling of the
  hull, `archScale_hullOf_le`); `exists_le_vcI_logVol_iff`: those of the adelic `S ⊆ VC(I)` are
  `ℝ_{≤ log-vol(VC(I))}`.
* `mul_mem_of_mem_hull`: multiplication by units at a prime passes to the hull (used for the
  equivariance of the hull under `LGP` and under the Kummer scalings).

**Deviation (deliberate): (Ind3) ranges over the hull.** [LANA], §6 takes `S ⊆ VC(I)`. Here
`S ⊆ hull(VC(I))`. Reason: IUT III, proof of Corollary 3.12, Step (xi-d)–(xi-f) (pp. 183–184),
takes the log-volume of the *holomorphic hull* of the union of the possible images, and IUT IV,
Theorem 1.10 bounds the log-volume of that hull; the container volume of IUT is
`log-vol(hull(VC(I)))`, not `log-vol(VC(I))` (`Iut/WallEquiv/VcI.md`). With `S ⊆ VC(I)` the
Scholze–Stix inequality loses the packet index terms (it is numerically false on many
Szpiro-record curves); the no-hull reading is kept as `Wall.SSIneqNoHull`.

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

/-- **The holomorphic hull `hull(VC(I))` of the log-shell container** is adelic. -/
lemma isAdelic_hullOf_vcI : IsAdelic D (hullOf D (vcI D)) :=
  isAdmissible_hullOf D _ (isAdelic_vcI D)

/-- `VC(I) ⊆ hull(VC(I))`. -/
lemma vcI_le_hullOf (i : Fin (VC D).proc.length) : vcI D i ≤ hullOf D (vcI D) i :=
  (LocalTheory.hull D.placeSect (nC D)).le_hullAdmissible (isAdelic_vcI D i)

/-- **Monotonicity of the log-volume into a hull**: an adelic region contained in the hull of an
adelic region `U` has log-volume at most `log-vol(hull(U))`. -/
theorem logVol_le_logVol_hullOf {U S : Region D} (hU : IsAdelic D U) (hS : IsAdelic D S)
    (h : ∀ i, S i ≤ hullOf D U i) : logVol D S ≤ logVol D (hullOf D U) := by
  refine LocalTheory.processionVol_le_of_packetVol _ _ _ _ fun i vQ => ?_
  refine LocalTheory.packetVol_le_of_subset _ _ i vQ (hS i vQ) (fun c => ?_) (h i vQ)
  obtain ⟨a, -, h⟩ := LocalTheory.isHullRegion_of_mem_hullRegions D.placeSect _ vQ _
    (((LocalTheory.hull D.placeSect (nC D)).system i vQ).hull_mem_hullRegions (hU i vQ))
  change LocalConstruct.haar vQ _ (LocalTheory.proj D.placeSect vQ c
    (((LocalTheory.hull D.placeSect (nC D)).system i vQ).hull ((U i).region vQ))) < ⊤
  rw [h]
  exact LocalTheory.haar_proj_scaledIntegral_lt_top D.placeSect _ i vQ a c

/-- **The archimedean rescaling by `0 < t ≤ 1` maps a hull into itself** (the hull at `∞` is a
polydisc `a·B_I`, which is balanced). -/
lemma archScale_hullOf_le {U : Region D} (hU : IsAdelic D U) {t : ℝ} (ht : 0 < t)
    (ht1 : t ≤ 1) (i : Fin (VC D).proc.length) :
    archScale D t (hullOf D U) i ≤ hullOf D U i := by
  intro vQ
  rcases vQ with p | _
  · exact subset_rfl
  · intro y hy
    obtain ⟨a, -, h⟩ := LocalTheory.isHullRegion_of_mem_hullRegions D.placeSect _ _ _
      (((LocalTheory.hull D.placeSect (nC D)).system i .infinite).hull_mem_hullRegions
        (hU i .infinite))
    have hHi : (hullOf D U i).region .infinite =
        (LocalTheory.packet D.placeSect _ .infinite).productRegion fun c =>
          LocalTheory.scaled D.placeSect .infinite c (a c) := h
    change y ∈ (hullOf D U i).region .infinite
    have hy' : ∀ c, y c ∈ t • LocalTheory.proj D.placeSect .infinite c
        ((hullOf D U i).region .infinite) := hy
    rw [hHi]
    intro c
    have hy'' := hy' c
    rw [hHi, LocalTheory.proj_productRegion D.placeSect _
      (fun c => LocalTheory.scaled D.placeSect .infinite c (a c)) (fun c => ⟨_,
        Set.smul_mem_smul_set (LocalTheory.one_mem_integral D.Kt _
          (LocalTheory.tuple D.placeSect _ c))⟩) c] at hy''
    exact LocalConstruct.smul_smul_integralAt_infinite_subset _ ht ht1 hy''

/-- **Multiplication by units passes to the hull** at a prime: if `u·y ∈ R` for every `y ∈ U`
(componentwise multiplication by units `u_c`) and `R` is a hull region `b·O`, then
`u·x ∈ R` for every `x ∈ hull(U)` (`u⁻¹·R` is a hull region containing `U`). This gives the
equivariance of the hull under the unit scalings `LGP` and `Scaling`. -/
lemma mul_mem_of_mem_hull (i : Fin (VC D).proc.length) (p : Nat.Primes)
    {U : Set ((VC D).packet i (.finite p)).Total}
    (hU : U ∈ ((LocalTheory.hull D.placeSect (nC D)).system i (.finite p)).Admissible)
    (u : ((VC D).packet i (.finite p)).Total) (hu : ∀ c, IsUnit (u c))
    {R : Set ((VC D).packet i (.finite p)).Total}
    (hR : R ∈ ((LocalTheory.hull D.placeSect (nC D)).system i (.finite p)).HullRegions)
    (hUR : ∀ y ∈ U, (fun c => u c * y c) ∈ R) {x : ((VC D).packet i (.finite p)).Total}
    (hx : x ∈ ((LocalTheory.hull D.placeSect (nC D)).system i (.finite p)).hull U) :
    (fun c => u c * x c) ∈ R := by
  set H := (LocalTheory.hull D.placeSect (nC D)).system i (.finite p)
  obtain ⟨b, hb, rfl⟩ := H.isHullRegion_of_mem R hR
  have hR' : ((VC D).packet i (.finite p)).scaledIntegral
      (fun c => ((hu c).unit⁻¹ : _) * b c) ∈ H.HullRegions :=
    ⟨_, fun c => (Units.isUnit _).mul (hb c), rfl⟩
  have hUR' : U ⊆ ((VC D).packet i (.finite p)).scaledIntegral
      (fun c => ((hu c).unit⁻¹ : _) * b c) := by
    intro y hy c
    obtain ⟨o, ho, hoy⟩ := hUR y hy c
    refine ⟨o, ho, ?_⟩
    change b c * o = u c * y c at hoy
    change ((hu c).unit⁻¹ : _) * b c * o = y c
    rw [mul_assoc, hoy, ← mul_assoc, (hu c).val_inv_mul, one_mul]
  intro c
  obtain ⟨o, ho, hox⟩ := H.hull_le hU hR' hUR' hx c
  refine ⟨o, ho, ?_⟩
  change ((hu c).unit⁻¹ : _) * b c * o = x c at hox
  change b c * o = u c * x c
  rw [← hox, ← mul_assoc, ← mul_assoc, (hu c).mul_val_inv, one_mul]

/-- **The (Ind3)-choices** ([LANA], §6 (Ind3), §9.2; IUT III, Corollary 3.12,
Step (xi-d)–(xi-f)): the adelic measurable regions `S ⊆ hull(VC(I))`, the holomorphic hull of
the log-shell container (see the module docstring for the deviation from [LANA], §6,
`S ⊆ VC(I)`). -/
def Ind3 : Type _ := {S : Region D // IsAdelic D S ∧ ∀ i, S i ≤ hullOf D (vcI D) i}

/-- `hull(VC(I))` itself is an (Ind3)-choice, the largest one. -/
noncomputable def Ind3.top : Ind3 D :=
  ⟨hullOf D (vcI D), isAdelic_hullOf_vcI D, fun _ _ => subset_rfl⟩

/-- `VC(I)` is an (Ind3)-choice. -/
noncomputable def Ind3.base : Ind3 D := ⟨vcI D, isAdelic_vcI D, vcI_le_hullOf D⟩

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

/-- **An (Ind3)-choice has log-volume at most that of `hull(VC(I))`.** -/
lemma logVol_le_vcI (S : Ind3 D) : logVol D S.1 ≤ logVol D (hullOf D (vcI D)) :=
  logVol_le_logVol_hullOf D (isAdelic_vcI D) S.2.1 S.2.2

/-- **`log-vol(VC(I)) ≤ log-vol(hull(VC(I)))`** (`VC(I)` is an (Ind3)-choice). -/
lemma logVol_vcI_le_logVol_hullOf : logVol D (vcI D) ≤ logVol D (hullOf D (vcI D)) :=
  logVol_le_vcI D (Ind3.base D)

/-- **The log-volumes of the (Ind3)-choices are exactly `ℝ_{≤ log-vol(hull(VC(I)))}`**
(non-atomicity, realized by the archimedean rescaling of the hull). -/
theorem exists_ind3_logVol_iff (x : ℝ) :
    (∃ S : Ind3 D, logVol D S.1 = x) ↔ x ≤ logVol D (hullOf D (vcI D)) := by
  constructor
  · rintro ⟨S, rfl⟩
    exact logVol_le_vcI D S
  · intro hx
    set t := Real.exp (x - logVol D (hullOf D (vcI D)))
    have ht : 0 < t := Real.exp_pos _
    have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    refine ⟨⟨archScale D t (hullOf D (vcI D)), isAdelic_archScale D ht (isAdelic_hullOf_vcI D),
      archScale_hullOf_le D (isAdelic_vcI D) ht ht1⟩, ?_⟩
    change logVol D (archScale D t (hullOf D (vcI D))) = x
    rw [logVol_archScale D ht (isAdelic_hullOf_vcI D), Real.log_exp]
    ring

/-- **The no-hull (Ind3)-volumes**: the log-volumes of the adelic regions `S ⊆ VC(I)` are
exactly `ℝ_{≤ log-vol(VC(I))}` ([LANA], §6 (Ind3) read literally). -/
theorem exists_le_vcI_logVol_iff (x : ℝ) :
    (∃ S : Region D, IsAdelic D S ∧ (∀ i, S i ≤ vcI D i) ∧ logVol D S = x) ↔
      x ≤ logVol D (vcI D) := by
  constructor
  · rintro ⟨S, hS, hle, rfl⟩
    refine LocalTheory.processionVol_le_of_packetVol _ _ _ _ fun i vQ => ?_
    refine LocalTheory.packetVol_le_of_subset _ _ i vQ (hS i vQ) (fun c => ?_) (hle i vQ)
    change LocalConstruct.haar vQ _ (LocalTheory.proj D.placeSect vQ c
      ((LocalTheory.packet D.placeSect _ vQ).productRegion fun c => vcIComp D i vQ c)) < ⊤
    rw [LocalTheory.proj_productRegion D.placeSect _ _
      (fun c => (vcIComp_admissible D i vQ c).1) c]
    exact (vcIComp_admissible D i vQ c).2.2.2.2
  · intro hx
    set t := Real.exp (x - logVol D (vcI D))
    have ht : 0 < t := Real.exp_pos _
    have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    refine ⟨archScale D t (vcI D), isAdelic_archScale D ht (isAdelic_vcI D),
      archScale_vcI_le D ht ht1, ?_⟩
    rw [logVol_archScale D ht (isAdelic_vcI D), Real.log_exp]
    ring

end Wall

end Iut
