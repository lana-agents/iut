/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalTheory

/-!
# The concrete large volume container over a number field (taxis #278)

Given the local-field theory `LT : LocalTheory K` of a number field `K`, this file builds
the concrete instances of the container interfaces of taxis #43–#45 for the standard
procession of length `n`:

* `LocalTheory.container LT n : LargeVolumeContainerData ℕ (Place K)` — the places of
  `K` mapped to their rational places, the tensor packets `⊗_{j ∈ S} K_{v_j}` presented
  with the tuple index of IUT III, Proposition 3.1, and the tensor products of log-shells
  as product regions;
* `LocalTheory.vol LT n : LogVolumeData (container)` — the normalized Haar log-volume
  with the weights `[K_v : ℚ_{v_ℚ}]/[K : ℚ]`, whose sum over the places above a rational
  place is `1` by `∑_{v ∣ p} e_v f_v = [K : ℚ]`;
* `LocalTheory.hull LT n : ContainerHullSystem (container)` — the packet-wise holomorphic
  hull, from the least hull regions of the components: the hull of a product region is
  the product of the component hulls.

Everything here is proved; the only inputs are the fields of `LocalTheory` (standard
local-field theory, taxis #4/#278).
-/

namespace Iut

universe u v

open NumberField
open scoped Pointwise

variable {K : Type u} [Field K] [NumberField K] (LT : LocalTheory.{u, v} K)

namespace LocalTheory

/-- The rational place under a place of `K`. -/
noncomputable def toRational : Place K → RationalPlace
  | Sum.inl w => .finite ⟨residueChar w, LT.residueChar_prime w⟩
  | Sum.inr _ => .infinite

@[simp] lemma toRational_finite (w : FinitePlace K) :
    LT.toRational (Place.finite w) = .finite ⟨residueChar w, LT.residueChar_prime w⟩ := rfl

@[simp] lemma toRational_infinite (w : InfinitePlace K) :
    LT.toRational (Place.infinite w) = .infinite := rfl

/-- The places of `K` over a rational place. -/
abbrev Fiber (vQ : RationalPlace) : Type u := {v : Place K // LT.toRational v = vQ}

/-- The fiber over a prime `p`, identified with the finite places of residue
characteristic `p`. -/
def fiberFiniteEquiv (p : Nat.Primes) :
    LT.Fiber (.finite p) ≃ {w : FinitePlace K // residueChar w = p} where
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
def fiberInfiniteEquiv : LT.Fiber .infinite ≃ InfinitePlace K where
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
noncomputable instance fiberFintype (vQ : RationalPlace) : Fintype (LT.Fiber vQ) := by
  rcases vQ with p | _
  · haveI := LT.fiber_finite p
    haveI : Fintype {w : FinitePlace K // residueChar w = p} := Fintype.ofFinite _
    exact Fintype.ofEquiv _ (LT.fiberFiniteEquiv p).symm
  · exact Fintype.ofEquiv _ LT.fiberInfiniteEquiv.symm

/-- The family of places underlying a tuple of the fiber. -/
def tuple {ι : Type} (vQ : RationalPlace) (c : ι → LT.Fiber vQ) : ι → Place K :=
  fun j => (c j).1

/-- The packet presentation at capsule labels `ι` and rational place `v_ℚ`. -/
noncomputable def packet (ι : Type) [Fintype ι] (vQ : RationalPlace) :
    DirectSumPresentation.{u, v} (ι → LT.Fiber vQ) where
  Summand c := LT.Tensor vQ (LT.tuple vQ c)
  integral c := LT.integral vQ (LT.tuple vQ c)

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
noncomputable def container (n : ℕ) : LargeVolumeContainerData.{0, u, v} ℕ (Place K) where
  proc := Procession.standard n
  toRational := LT.toRational
  fiberFintype vQ := LT.fiberFintype vQ
  packet i vQ := LT.packet ((Procession.standard n).capsule i).LabelType vQ
  logShell i vQ := (LT.packet _ vQ).productRegion fun c => LT.logShell vQ (LT.tuple vQ c)
  logShell_isProduct i vQ := DirectSumPresentation.isProductRegion_productRegion _ _
  logShell_relCompact i vQ :=
    isCompact_closure_productRegion _ _ fun c => LT.logShell_relCompact vQ _
  logShell_finiteSupport i := by
    -- outside `∞`, `2` and the primes ramified in `K`, the log-shell is the integral
    -- structure
    have hfin : (({RationalPlace.infinite} ∪ {RationalPlace.finite ⟨2, Nat.prime_two⟩} ∪
        ((fun w => LT.toRational (Place.finite w)) '' {w | ramIdx K w ≠ 1}) :
          Set RationalPlace)).Finite :=
      ((Set.finite_singleton _).union (Set.finite_singleton _)).union
        (LT.ramified_finite.image _)
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
      change (LT.packet _ _).productRegion _ = (LT.packet _ _).integralRegion
      ext x
      simp only [DirectSumPresentation.mem_productRegion,
        DirectSumPresentation.mem_integralRegion]
      refine forall_congr' fun c => ?_
      rw [LT.logShell_eq_integral p (LT.tuple _ c) hodd]
      · rfl
      · intro j w hw
        apply hunr
        have := (c j).2
        rw [show (c j).1 = Place.finite w from hw, toRational_finite] at this
        exact congrArg Subtype.val (RationalPlace.finite.inj this)
    · exact absurd (Or.inl (Or.inl rfl)) hmem
  integral_subset_logShell_nonarch i p := by
    intro x hx c
    exact LT.integral_subset_logShell p _ (hx c)

variable (n : ℕ)

@[simp] lemma container_proc : (LT.container n).proc = Procession.standard n := rfl

/-- The weight of a place of `K` over a rational place. -/
noncomputable def weight (vQ : RationalPlace) (v : LT.Fiber vQ) : ℝ :=
  match v.1 with
  | Sum.inl w => placeWeight K w
  | Sum.inr w => infPlaceWeight K w

lemma finrank_pos : (0 : ℝ) < Module.finrank ℚ K := by
  exact_mod_cast Module.finrank_pos

lemma weight_pos (vQ : RationalPlace) (v : LT.Fiber vQ) : 0 < LT.weight vQ v := by
  rcases v with ⟨v, hv⟩
  rcases v with w | w
  · change 0 < placeWeight K w
    exact div_pos (by exact_mod_cast LT.localDeg_pos w) finrank_pos
  · change 0 < infPlaceWeight K w
    exact div_pos (by exact_mod_cast w.mult_pos) finrank_pos

lemma weight_sum_one (vQ : RationalPlace) : ∑ v, LT.weight vQ v = 1 := by
  rcases vQ with p | _
  · haveI := LT.fiber_finite p
    haveI : Fintype {w : FinitePlace K // residueChar w = p} := Fintype.ofFinite _
    have hsum := LT.sum_localDeg p p.2
    rw [Fintype.sum_equiv (LT.fiberFiniteEquiv p) (fun v => LT.weight (.finite p) v)
      (fun w => placeWeight K w.1)
      (fun v => by
        rcases v with ⟨v, hv⟩
        rcases v with w | w
        · rfl
        · exact absurd hv (by simp [toRational]))]
    simp only [placeWeight, ← Finset.sum_div]
    rw [div_eq_one_iff_eq finrank_pos.ne']
    rw [← Nat.cast_sum, hsum]
  · rw [Fintype.sum_equiv LT.fiberInfiniteEquiv (fun v => LT.weight .infinite v)
      (fun w => infPlaceWeight K w)
      (fun v => by
        rcases v with ⟨v, hv⟩
        rcases v with w | w
        · exact absurd hv (by simp [toRational])
        · rfl)]
    simp only [infPlaceWeight, ← Finset.sum_div]
    rw [div_eq_one_iff_eq finrank_pos.ne']
    exact_mod_cast LT.sum_mult

/-- The packet weight of a tuple: the product of the place weights. -/
noncomputable def tupleWeight {ι : Type} [Fintype ι] (vQ : RationalPlace)
    (c : ι → LT.Fiber vQ) : ℝ :=
  ∏ j, LT.weight vQ (c j)

/-- The scaled integral structure `a·O` of a component. -/
def scaled {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → LT.Fiber vQ)
    (a : LT.Tensor vQ (LT.tuple vQ c)) : Set (LT.Tensor vQ (LT.tuple vQ c)) :=
  a • LT.integral vQ (LT.tuple vQ c)

/-- The element `a·1` of the scaled integral structure `a·O` of a component. -/
def scaledOne {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → LT.Fiber vQ)
    (a : LT.Tensor vQ (LT.tuple vQ c)) : LT.Tensor vQ (LT.tuple vQ c) :=
  a • (1 : LT.Tensor vQ (LT.tuple vQ c))

/-- The projection of a region of the packet to a component. -/
def proj {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → LT.Fiber vQ)
    (U : Set (LT.packet ι vQ).Total) : Set (LT.Tensor vQ (LT.tuple vQ c)) :=
  (fun x => x c) '' U

/-- The projection of a product region with nonempty components is the component. -/
lemma proj_productRegion {ι : Type} [Fintype ι] (vQ : RationalPlace)
    (U : ∀ c : ι → LT.Fiber vQ, Set (LT.Tensor vQ (LT.tuple vQ c)))
    (hU : ∀ c, (U c).Nonempty) (c : ι → LT.Fiber vQ) :
    LT.proj vQ c ((LT.packet ι vQ).productRegion U) = U c := by
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
noncomputable def vol : LogVolumeData (LT.container n) where
  weight := LT.weight
  weight_pos := LT.weight_pos
  weight_sum_one := LT.weight_sum_one
  componentVol i vQ c U := LT.componentVol vQ (LT.tuple vQ c) U
  componentVol_integral_nonarch i p c := LT.componentVol_integral _ _
  componentVol_prime_preimage i p c U := LT.componentVol_prime_preimage p _ U
  archBall i c := LT.integral .infinite (LT.tuple .infinite c)
  componentVol_archBall i c := LT.componentVol_integral _ _
  packetVol i vQ U := ∑ c : (LT.container n).Components i vQ,
    LT.tupleWeight vQ c * LT.componentVol vQ (LT.tuple vQ c) (LT.proj vQ c U)
  packetVol_integral i vQ := by
    refine Finset.sum_eq_zero fun c _ => ?_
    have h : LT.proj vQ c ((LT.container n).packet i vQ).integralRegion =
        LT.integral vQ (LT.tuple vQ c) :=
      LT.proj_productRegion vQ (fun c => LT.integral vQ (LT.tuple vQ c))
        (fun c => ⟨1, LT.one_mem_integral vQ _⟩) c
    have := congrArg (fun S => LT.tupleWeight vQ c * LT.componentVol vQ (LT.tuple vQ c) S) h
    rw [LT.componentVol_integral, mul_zero] at this
    exact this
  packetVol_product i vQ U hU := by
    refine Finset.sum_congr rfl fun c _ => ?_
    have h := LT.proj_productRegion vQ U hU c
    exact congrArg (fun S => LT.tupleWeight vQ c * LT.componentVol vQ (LT.tuple vQ c) S) h

/-- **The concrete hull system**: least hull regions of product regions with admissible
components, from the least hull regions of the components. -/
noncomputable def hull : ContainerHullSystem (LT.container n) where
  system i vQ :=
    HullSystem.ofExists (LT.packet _ vQ)
      {U | ∃ fam : ∀ c, Set (LT.Tensor vQ (LT.tuple vQ c)),
        (∀ c, fam c ∈ LT.admissible vQ (LT.tuple vQ c)) ∧
          U = (LT.packet _ vQ).productRegion fam}
      (by
        rintro U ⟨fam, hfam, rfl⟩
        exact isCompact_closure_productRegion _ _ fun c =>
          LT.admissible_relCompact vQ _ _ (hfam c))
      (by
        rintro U ⟨fam, hfam, rfl⟩
        choose a ha using fun c => LT.exists_leastHull vQ (LT.tuple vQ c) (fam c) (hfam c)
        refine ⟨(LT.packet _ vQ).scaledIntegral a, ⟨a, fun c => (ha c).1, rfl⟩, ?_, ?_⟩
        · intro x hx c
          exact (ha c).2.1 (hx c)
        · rintro R ⟨b, hb, rfl⟩ hUR
          intro x hx c
          have hproj : fam c ⊆ LT.scaled vQ c (b c) := by
            have := LT.proj_productRegion vQ fam
              (fun c => LT.admissible_nonempty vQ _ _ (hfam c)) c
            rw [← this]
            rintro y ⟨z, hz, rfl⟩
            exact hUR hz c
          exact (ha c).2.2 (b c) (hb c) hproj (hx c))
      (by
        rintro U ⟨fam, hfam, rfl⟩ R ⟨⟨a, ha, rfl⟩, _, _⟩
        exact ⟨fun c => LT.scaled vQ c (a c),
          fun c => LT.smul_integral_admissible vQ _ (a c) (ha c), rfl⟩)
  integral_admissible i vQ :=
    ⟨fun c => LT.integral vQ (LT.tuple vQ c), fun c => LT.integral_admissible vQ _, rfl⟩

end LocalTheory

end Iut
