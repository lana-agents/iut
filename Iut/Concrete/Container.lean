/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.Theory

/-!
# The concrete large volume container over a number field (taxis #278)

From the tensor packets of a number field `K` (`Iut.LocalTheory`), this file builds
the concrete instances of the container interfaces of taxis #43–#45 for the standard
procession of length `n`:

* `LocalTheory.container K n : LargeVolumeContainerData ℕ (Place K)` — the places of
  `K` mapped to their rational places, the tensor packets `⊗_{j ∈ S} K_{v_j}` presented
  with the tuple index of IUT III, Proposition 3.1, and the tensor products of log-shells
  as product regions;
* `LocalTheory.vol K n : LogVolumeData (container)` — the normalized Haar log-volume
  with the weights `[K_v : ℚ_{v_ℚ}]/[K : ℚ]`, whose sum over the places above a rational
  place is `1` by `∑_{v ∣ p} e_v f_v = [K : ℚ]`;
* `LocalTheory.hull K n : ContainerHullSystem (container)` — the packet-wise holomorphic
  hull, from the least hull regions of the components: the hull of a product region is
  the product of the component hulls.

Everything here is proved from the constructions of `Iut/Concrete/LocalConstruct/*`
(standard local-field theory, taxis #4/#278).
-/

namespace Iut

universe u

open NumberField
open scoped Pointwise

variable (K : Type u) [Field K] [NumberField K]

namespace LocalTheory

/-- The rational place under a place of `K`. -/
noncomputable def toRational : Place K → RationalPlace
  | Sum.inl w => .finite ⟨residueChar w, LocalTheory.residueChar_prime K w⟩
  | Sum.inr _ => .infinite

@[simp] lemma toRational_finite (w : FinitePlace K) :
    toRational K (Place.finite w) = .finite
        ⟨residueChar w, LocalTheory.residueChar_prime K w⟩ := rfl

@[simp] lemma toRational_infinite (w : InfinitePlace K) :
    toRational K (Place.infinite w) = .infinite := rfl

/-- The places of `K` over a rational place. -/
abbrev Fiber (vQ : RationalPlace) : Type u := {v : Place K // toRational K v = vQ}

/-- The fiber over a prime `p`, identified with the finite places of residue
characteristic `p`. -/
def fiberFiniteEquiv (p : Nat.Primes) :
    LocalTheory.Fiber K (.finite p) ≃ {w : FinitePlace K // residueChar w = p} where
  toFun v := match v with
    | ⟨Sum.inl w, h⟩ => ⟨w, by
        have h' := RationalPlace.finite.inj h
        exact congrArg Subtype.val h'⟩
    | ⟨Sum.inr _, h⟩ => absurd h (by simp [toRational])
  invFun w := ⟨Sum.inl w.1, by
    simp only [toRational]
    congr 1
    exact Subtype.ext w.2⟩
  left_inv v := by
    rcases v with ⟨v, h⟩
    rcases v with w | w
    · rfl
    · exact absurd h (by simp [toRational])
  right_inv w := rfl

/-- The fiber over the archimedean place, identified with the infinite places. -/
def fiberInfiniteEquiv : LocalTheory.Fiber K .infinite ≃ InfinitePlace K where
  toFun v := match v with
    | ⟨Sum.inl _, h⟩ => absurd h (by simp [toRational])
    | ⟨Sum.inr w, _⟩ => w
  invFun w := ⟨Sum.inr w, rfl⟩
  left_inv v := by
    rcases v with ⟨v, h⟩
    rcases v with w | w
    · exact absurd h (by simp [toRational])
    · rfl
  right_inv w := rfl

/-- Finiteness of the fibers. -/
noncomputable instance fiberFintype (vQ : RationalPlace) : Fintype (LocalTheory.Fiber K vQ) := by
  rcases vQ with p | _
  · haveI := fiber_finite K p
    haveI : Fintype {w : FinitePlace K // residueChar w = p} := Fintype.ofFinite _
    exact Fintype.ofEquiv _ (fiberFiniteEquiv K p).symm
  · exact Fintype.ofEquiv _ (fiberInfiniteEquiv K).symm

/-- The family of places underlying a tuple of the fiber. -/
def tuple {ι : Type} (vQ : RationalPlace) (c : ι → LocalTheory.Fiber K vQ) : ι → Place K :=
  fun j => (c j).1

/-- Every place of a tuple of the fiber over `p` lies over `p`. -/
lemma tuple_isOver {ι : Type} (p : Nat.Primes) (c : ι → LocalTheory.Fiber K (.finite p)) :
    ∀ j, ∃ w : FinitePlace K, tuple K _ c j = Place.finite w ∧ residueChar w = p := by
  intro j
  have hv := (c j).2
  change toRational K (tuple K _ c j) = _ at hv
  rcases hw : tuple K _ c j with w | w
  · rw [hw] at hv
    exact ⟨w, rfl, congrArg Subtype.val (RationalPlace.finite.inj hv)⟩
  · rw [hw] at hv
    exact absurd hv (by simp [toRational])

/-- The packet presentation at capsule labels `ι` and rational place `v_ℚ`. -/
noncomputable def packet (ι : Type) [Fintype ι] (vQ : RationalPlace) :
    DirectSumPresentation.{u, u} (ι → LocalTheory.Fiber K vQ) where
  Summand c := Tensor K vQ (tuple K vQ c)
  integral c := integral K vQ (tuple K vQ c)

/-- A product region is a `Set.pi`. -/
lemma productRegion_eq_pi {C : Type*} (P : DirectSumPresentation C)
    (U : ∀ c, Set (P.Summand c)) : P.productRegion U = Set.pi Set.univ U := by
  ext x; exact ⟨fun h c _ => h c, fun h c => h c (Set.mem_univ c)⟩

/-- The closure of a product of relatively compact regions is compact. -/
lemma isCompact_closure_productRegion {C : Type*} (P : DirectSumPresentation C)
    (U : ∀ c, Set (P.Summand c)) (hU : ∀ c, IsCompact (closure (U c))) :
    IsCompact (closure (P.productRegion U)) := by
  rw [productRegion_eq_pi]
  change IsCompact (closure (Set.pi Set.univ U : Set (∀ c, P.Summand c)))
  rw [closure_pi_set]
  exact isCompact_univ_pi hU

/-- **The concrete large volume container** for the standard procession of length `n`
(IUT III, Propositions 3.1–3.3). -/
noncomputable def container (n : ℕ) : LargeVolumeContainerData.{0, u, u} ℕ (Place K) where
  proc := Procession.standard n
  toRational := toRational K
  fiberFintype vQ := fiberFintype K vQ
  packet i vQ := packet K ((Procession.standard n).capsule i).LabelType vQ
  logShell i vQ := (packet K _ vQ).productRegion fun c => logShell K vQ (tuple K vQ c)
  logShell_isProduct i vQ := DirectSumPresentation.isProductRegion_productRegion _ _
  logShell_relCompact i vQ :=
    isCompact_closure_productRegion _ _ fun c => logShell_relCompact K vQ _
  logShell_finiteSupport i := by
    -- outside `∞`, `2` and the primes ramified in `K`, the log-shell is the integral
    -- structure
    have hfin : (({RationalPlace.infinite} ∪ {RationalPlace.finite ⟨2, Nat.prime_two⟩} ∪
        ((fun w => toRational K (Place.finite w)) '' {w | ramIdx K w ≠ 1}) :
          Set RationalPlace)).Finite :=
      ((Set.finite_singleton _).union (Set.finite_singleton _)).union
        ((ramified_finite K).image _)
    refine hfin.subset fun vQ hvQ => ?_
    by_contra hmem
    apply hvQ
    rcases vQ with p | _
    · have hp2 : (p : ℕ) ≠ 2 := by
        intro h
        apply hmem
        refine Or.inl (Or.inr ?_)
        simp only [Set.mem_singleton_iff]
        congr 1
        exact Subtype.ext h
      have hodd : Odd (p : ℕ) := (p.2.eq_two_or_odd').resolve_left hp2
      have hunr : ∀ w : FinitePlace K, residueChar w = p → ramIdx K w = 1 := by
        intro w hw
        by_contra hne
        apply hmem
        refine Or.inr ⟨w, hne, ?_⟩
        all_goals (simp only [toRational_finite]; congr 1; exact Subtype.ext hw)
      change (packet K _ _).productRegion _ = (packet K _ _).integralRegion
      ext x
      simp only [DirectSumPresentation.mem_productRegion,
        DirectSumPresentation.mem_integralRegion]
      refine forall_congr' fun c => ?_
      rw [logShell_eq_integral K p (tuple K _ c) hodd]
      · rfl
      · intro j w hw
        apply hunr
        have := (c j).2
        rw [show (c j).1 = Place.finite w from hw, toRational_finite] at this
        exact congrArg Subtype.val (RationalPlace.finite.inj this)
    · exact absurd (Or.inl (Or.inl rfl)) hmem
  integral_subset_logShell_nonarch i p := by
    intro x hx c
    exact integral_subset_logShell K p _ (hx c)

variable (n : ℕ)

@[simp] lemma container_proc : (container K n).proc = Procession.standard n := rfl

/-- The weight of a place of `K` over a rational place. -/
noncomputable def weight (vQ : RationalPlace) (v : LocalTheory.Fiber K vQ) : ℝ :=
  match v.1 with
  | Sum.inl w => placeWeight K w
  | Sum.inr w => infPlaceWeight K w

lemma finrank_pos : (0 : ℝ) < Module.finrank ℚ K := by
  exact_mod_cast Module.finrank_pos

lemma weight_pos (vQ : RationalPlace) (v : LocalTheory.Fiber K vQ) : 0 < weight K vQ v := by
  rcases v with ⟨v, hv⟩
  rcases v with w | w
  · change 0 < placeWeight K w
    exact div_pos (by exact_mod_cast (localDeg_pos K) w) (finrank_pos K)
  · change 0 < infPlaceWeight K w
    exact div_pos (by exact_mod_cast w.mult_pos) (finrank_pos K)

lemma weight_sum_one (vQ : RationalPlace) : ∑ v, weight K vQ v = 1 := by
  rcases vQ with p | _
  · haveI := fiber_finite K p
    haveI : Fintype {w : FinitePlace K // residueChar w = p} := Fintype.ofFinite _
    have hsum := sum_localDeg K p p.2
    rw [Fintype.sum_equiv (fiberFiniteEquiv K p) (fun v => weight K (.finite p) v)
      (fun w => placeWeight K w.1)
      (fun v => by
        rcases v with ⟨v, hv⟩
        rcases v with w | w
        · rfl
        · exact absurd hv (by simp [toRational]))]
    simp only [placeWeight, ← Finset.sum_div]
    rw [div_eq_one_iff_eq (finrank_pos K).ne']
    rw [← Nat.cast_sum, hsum]
  · rw [Fintype.sum_equiv (fiberInfiniteEquiv K) (fun v => weight K .infinite v)
      (fun w => infPlaceWeight K w)
      (fun v => by
        rcases v with ⟨v, hv⟩
        rcases v with w | w
        · exact absurd hv (by simp [toRational])
        · rfl)]
    simp only [infPlaceWeight, ← Finset.sum_div]
    rw [div_eq_one_iff_eq (finrank_pos K).ne']
    exact_mod_cast (sum_mult K)

/-- The packet weight of a tuple: the product of the place weights. -/
noncomputable def tupleWeight {ι : Type} [Fintype ι] (vQ : RationalPlace)
    (c : ι → LocalTheory.Fiber K vQ) : ℝ :=
  ∏ j, weight K vQ (c j)

/-- The scaled integral structure `a·O` of a component. -/
def scaled {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → LocalTheory.Fiber K vQ)
    (a : Tensor K vQ (tuple K vQ c)) : Set (Tensor K vQ (tuple K vQ c)) :=
  a • integral K vQ (tuple K vQ c)

/-- The element `a·1` of the scaled integral structure `a·O` of a component. -/
noncomputable def scaledOne {ι : Type} [Fintype ι] (vQ : RationalPlace)
    (c : ι → LocalTheory.Fiber K vQ)
    (a : Tensor K vQ (tuple K vQ c)) : Tensor K vQ (tuple K vQ c) :=
  a • (1 : Tensor K vQ (tuple K vQ c))

/-- The projection of a region of the packet to a component. -/
def proj {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → LocalTheory.Fiber K vQ)
    (U : Set (packet K ι vQ).Total) : Set (Tensor K vQ (tuple K vQ c)) :=
  (fun x => x c) '' U

/-- The projection of a product region with nonempty components is the component. -/
lemma proj_productRegion {ι : Type} [Fintype ι] (vQ : RationalPlace)
    (U : ∀ c : ι → LocalTheory.Fiber K vQ, Set (Tensor K vQ (tuple K vQ c)))
    (hU : ∀ c, (U c).Nonempty) (c : ι → LocalTheory.Fiber K vQ) :
    proj K vQ c ((packet K ι vQ).productRegion U) = U c := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx c
  · intro hy
    classical
    refine ⟨Function.update (fun c' => (hU c').some) c y, fun c' => ?_, by simp⟩
    by_cases h : c' = c
    · subst h; rw [Function.update_self]; exact hy
    · rw [Function.update_of_ne h]; exact (hU c').some_mem

/-- **The concrete log-volume data** (IUT III, Proposition 3.9). -/
noncomputable def vol : LogVolumeData (container K n) where
  weight := weight K
  weight_pos := weight_pos K
  weight_sum_one := weight_sum_one K
  componentVol i vQ c U := componentVol K vQ (tuple K vQ c) U
  componentVol_integral_nonarch i p c := componentVol_integral K _ _
  componentVol_prime_preimage i p c a ha :=
    componentVol_prime_preimage K p _ (tuple_isOver K p c) _
      (smul_integral_admissible K _ _ a ha)
  archBall i c := integral K .infinite (tuple K .infinite c)
  componentVol_archBall i c := componentVol_integral K _ _
  packetVol i vQ U := ∑ c : (container K n).Components i vQ,
    tupleWeight K vQ c * componentVol K vQ (tuple K vQ c) (proj K vQ c U)
  packetVol_integral i vQ := by
    refine Finset.sum_eq_zero fun c _ => ?_
    have h : proj K vQ c ((container K n).packet i vQ).integralRegion =
        integral K vQ (tuple K vQ c) :=
      proj_productRegion K vQ (fun c => integral K vQ (tuple K vQ c))
        (fun c => ⟨1, one_mem_integral K vQ _⟩) c
    have := congrArg (fun S => tupleWeight K vQ c * componentVol K vQ (tuple K vQ c) S) h
    rw [componentVol_integral K, mul_zero] at this
    exact this
  packetVol_product i vQ U hU := by
    refine Finset.sum_congr rfl fun c _ => ?_
    have h := proj_productRegion K vQ U hU c
    exact congrArg (fun S => tupleWeight K vQ c * componentVol K vQ (tuple K vQ c) S) h

/-- **The class of hull regions of a packet** among which the holomorphic hull is least
(`HullSystem.HullRegions`): at a prime all regions `a·O` with all components of `a` units
(IUT III, Remark 3.9.5(i)); at the archimedean place the real radial scalings `t·B_I`
with `t > 0` componentwise (IUT IV, Proposition 1.5(iii)). -/
def hullRegions (ι : Type) [Fintype ι] :
    ∀ vQ : RationalPlace, Set (Set (packet K ι vQ).Total)
  | .finite p => {R | (packet K ι (.finite p)).IsHullRegion R}
  | .infinite => {R | ∃ t : (ι → LocalTheory.Fiber K .infinite) → ℝ, (∀ c, 0 < t c) ∧
      R = (packet K ι .infinite).scaledIntegral fun c =>
        algebraMap ℝ (Tensor K .infinite (tuple K .infinite c)) (t c)}

/-- Members of the class of hull regions are hull regions `a·O` with all components of
`a` units. -/
lemma isHullRegion_of_mem_hullRegions (ι : Type) [Fintype ι] (vQ : RationalPlace) :
    ∀ R ∈ hullRegions K ι vQ, (packet K ι vQ).IsHullRegion R := by
  cases vQ with
  | finite p => exact fun R hR => hR
  | infinite =>
    rintro R ⟨t, ht, rfl⟩
    exact ⟨_, fun c => (isUnit_iff_ne_zero.mpr (ht c).ne').map
      (algebraMap ℝ (Tensor K .infinite (tuple K .infinite c))), rfl⟩

/-- The holomorphic integral region belongs to the class of hull regions. -/
lemma integralRegion_mem_hullRegions (ι : Type) [Fintype ι] (vQ : RationalPlace) :
    (packet K ι vQ).integralRegion ∈ hullRegions K ι vQ := by
  cases vQ with
  | finite p => exact (packet K ι (.finite p)).isHullRegion_integralRegion
  | infinite =>
    refine ⟨fun _ => 1, fun _ => one_pos, ?_⟩
    rw [← DirectSumPresentation.scaledIntegral_one]
    congr 1
    funext c
    exact (map_one _).symm

/-- **Least hull regions of product regions** with admissible components, from the least
hull regions of the components (`exists_leastHull` at a prime, `exists_leastHull_infinite`
and the radial monotonicity `smul_integral_infinite_mono` at `∞`). -/
lemma exists_leastHullRegion (ι : Type) [Fintype ι] (vQ : RationalPlace)
    (fam : ∀ c : ι → LocalTheory.Fiber K vQ, Set (Tensor K vQ (tuple K vQ c)))
    (hfam : ∀ c, fam c ∈ admissible K vQ (tuple K vQ c)) :
    ∃ R, (packet K ι vQ).IsLeastHullRegionIn (hullRegions K ι vQ)
      ((packet K ι vQ).productRegion fam) R := by
  cases vQ with
  | finite p =>
    choose a ha using fun c => exists_leastHull K p (tuple K _ c) (fam c) (hfam c)
    refine ⟨(packet K _ _).scaledIntegral a, ⟨a, fun c => (ha c).1, rfl⟩, ?_, ?_⟩
    · intro x hx c
      exact (ha c).2.1 (hx c)
    · rintro R ⟨b, hb, rfl⟩ hUR
      intro x hx c
      have hproj : fam c ⊆ scaled K _ c (b c) := by
        have := proj_productRegion K _ fam
          (fun c => admissible_nonempty K _ _ _ (hfam c)) c
        rw [← this]
        rintro y ⟨z, hz, rfl⟩
        exact hUR hz c
      exact (ha c).2.2 (b c) (hb c) hproj (hx c)
  | infinite =>
    choose t ht using fun c => exists_leastHull_infinite K (tuple K _ c) (fam c) (hfam c)
    refine ⟨(packet K _ _).scaledIntegral fun c =>
      algebraMap ℝ (Tensor K .infinite (tuple K .infinite c)) (t c),
      ⟨t, fun c => (ht c).1, rfl⟩, ?_, ?_⟩
    · intro x hx c
      exact (ht c).2.1 (hx c)
    · rintro R ⟨t', ht', rfl⟩ hUR
      intro x hx c
      have hproj : fam c ⊆ algebraMap ℝ (Tensor K .infinite (tuple K .infinite c)) (t' c) •
          integral K .infinite (tuple K .infinite c) := by
        have := proj_productRegion K _ fam
          (fun c => admissible_nonempty K _ _ _ (hfam c)) c
        rw [← this]
        rintro y ⟨z, hz, rfl⟩
        exact hUR hz c
      exact smul_integral_infinite_mono K _ _ _ (ht c).1
        ((ht c).2.2 (t' c) (ht' c) hproj) (hx c)

/-- **The concrete hull system**: least hull regions of product regions with admissible
components, from the least hull regions of the components. -/
noncomputable def hull : ContainerHullSystem (container K n) where
  system i vQ :=
    HullSystem.ofExists (packet K _ vQ)
      {U | ∃ fam : ∀ c, Set (Tensor K vQ (tuple K vQ c)),
        (∀ c, fam c ∈ admissible K vQ (tuple K vQ c)) ∧
          U = (packet K _ vQ).productRegion fam}
      (by
        rintro U ⟨fam, hfam, rfl⟩
        exact isCompact_closure_productRegion _ _ fun c =>
          admissible_relCompact K vQ _ _ (hfam c))
      (hullRegions K _ vQ)
      (isHullRegion_of_mem_hullRegions K _ vQ)
      (integralRegion_mem_hullRegions K _ vQ)
      (by
        rintro U ⟨fam, hfam, rfl⟩
        exact exists_leastHullRegion K _ vQ fam hfam)
      (by
        rintro U ⟨fam, hfam, rfl⟩ R ⟨hR, _, _⟩
        obtain ⟨a, ha, rfl⟩ := isHullRegion_of_mem_hullRegions K _ vQ R hR
        exact ⟨fun c => scaled K vQ c (a c),
          fun c => smul_integral_admissible K vQ _ (a c) (ha c), rfl⟩)
  integral_admissible i vQ :=
    ⟨fun c => integral K vQ (tuple K vQ c), fun c => integral_admissible K vQ _, rfl⟩

/-- The finite place underlying an element of the fiber over a prime. -/
noncomputable def fiberPlace {p : Nat.Primes} (v : LocalTheory.Fiber K (.finite p)) :
    FinitePlace K :=
  (fiberFiniteEquiv K p v).1

lemma fiberPlace_spec {p : Nat.Primes} (v : LocalTheory.Fiber K (.finite p)) :
    v.1 = Place.finite (fiberPlace K v) := by
  rcases v with ⟨v, hv⟩
  rcases v with w | w
  · rfl
  · exact absurd hv (by simp [toRational])

lemma residueChar_fiberPlace {p : Nat.Primes} (v : LocalTheory.Fiber K (.finite p)) :
    residueChar (fiberPlace K v) = p :=
  (fiberFiniteEquiv K p v).2

/-- The theta-pilot component at the archimedean place: the union of the images of the
tensor product of the log-shells under the indeterminacy automorphisms. -/
noncomputable def thetaInfinite (n : ℕ) (i : Fin n)
    (c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber K .infinite) :
    Set (Tensor K .infinite (tuple K .infinite c)) :=
  ⋃ φ ∈ indAut K .infinite (tuple K .infinite c),
    φ '' logShell K .infinite (tuple K .infinite c)

end LocalTheory

end Iut
