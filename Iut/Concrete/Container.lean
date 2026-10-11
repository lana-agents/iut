/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.Theory

/-!
# The concrete large volume container over a section of places (taxis #278)

From the tensor packets of a number field `K` (`Iut.LocalTheory`), this file builds
the concrete instances of the container interfaces of taxis #43–#45 for the standard
procession of length `n`, **indexed by a section of places** `V ⊆ V(K)` of the restriction
`V(K) → V(k)` to a subfield `k` (for the Θ-data: `k = F_mod`, `V ≅ V_mod`, IUT I,
Definition 3.1(e)):

* `LocalTheory.PlaceSection k K`: a section `V(k) → V(K)`, place-type preserving, over the
  same rational places;
* `LocalTheory.container σ n : LargeVolumeContainerData ℕ (Place k)` — the direct summands of
  the packet at a rational place `v_ℚ` are indexed by the tuples of places `w ∈ V(k)` over `v_ℚ`,
  i.e. (via the section) by the tuples of places `v ∈ V` over `v_ℚ`, as in IUT III,
  Propositions 3.1, 3.2 and Theorem 3.11 (Ind2) ("the cardinality of the collection of direct
  summands is equal to the cardinality of the set of `v ∈ V` that lie over `v_ℚ`"); the summand
  at a tuple `(w_j)_j` is `⊗_{j ∈ S} K_{σ(w_j)}`, and the tensor products of log-shells are
  product regions;
* `LocalTheory.vol σ n : LogVolumeData (container)` — the normalized Haar log-volume with the
  weights `[k_w : ℚ_{v_ℚ}]/[k : ℚ]` of IUT III, Remark 3.1.1(ii): the log-volume on `K_v`,
  `v = σ(w) ∈ V`, counted with weight `[K_v : k_w]⁻¹` and normalized by
  `∑_{w' ∣ v_ℚ} [k_{w'} : ℚ_{v_ℚ}]` (the component log-volume `componentVol` is already
  normalized by the `ℚ_{v_ℚ}`-dimension of `K_v`); the weights over a rational place sum to `1`
  by `∑_{w ∣ p} e_w f_w = [k : ℚ]` (and `∑_{w ∣ ∞} [k_w : ℝ] = [k : ℚ]`);
* `LocalTheory.hull σ n : ContainerHullSystem (container)` — the packet-wise holomorphic
  hull, from the least hull regions of the components: the hull of a product region is
  the product of the component hulls.

Everything here is proved from the constructions of `Iut/Concrete/LocalConstruct/*`
(standard local-field theory, taxis #4/#278); the packet machinery works for any family of
places `c : ι → Place K`, here `c = σ ∘ (tuple of places of k)`.
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

/-- The infinite place underlying an element of the fiber over the archimedean place. -/
def fiberInfPlace (v : LocalTheory.Fiber K .infinite) : InfinitePlace K :=
  fiberInfiniteEquiv K v

lemma fiberInfPlace_spec (v : LocalTheory.Fiber K .infinite) :
    v.1 = Place.infinite (fiberInfPlace K v) := by
  rcases v with ⟨v, hv⟩
  rcases v with w | w
  · exact absurd hv (by simp [toRational])
  · rfl

/-! ### The weights (IUT III, Remark 3.1.1(ii)) -/

/-- The weight of a place of `K` over a rational place: `[K_w : ℚ_p]/[K : ℚ]` at a finite place,
`[K_w : ℝ]/[K : ℚ]` at an infinite place. -/
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

/-- The weight of a finite place of the fiber over `p` is `[K_w : ℚ_p]/[K : ℚ]`. -/
lemma weight_finite_eq {p : Nat.Primes} (v : LocalTheory.Fiber K (.finite p)) :
    weight K (.finite p) v = placeWeight K (fiberPlace K v) := by
  unfold weight
  rw [fiberPlace_spec K v]
  rfl

/-- The weights over a rational place sum to `1`. -/
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

/-! ### Sections of places -/

/-- **A section of places** `V(k) → V(K)` (IUT I, Definition 3.1(e); IUT III, Remark 3.1.1(ii)):
a place-type preserving map sending each place `w` of `k` to a place of `K` over the same
rational place. For the Θ-data, `k = F_mod` and the section is the valuation section
`V_mod ≅ V ⊆ V(K)` (`Iut.ValuationSection`), whose image `V` indexes the direct summands of the
tensor packets (IUT III, Proposition 3.1, Remark 3.1.1(ii)). -/
structure PlaceSection (k : Type u) [Field k] [NumberField k] where
  /-- The section on nonarchimedean places. -/
  fin : FinitePlace k → FinitePlace K
  /-- The section on archimedean places. -/
  inf : InfinitePlace k → InfinitePlace K
  /-- The section preserves residue characteristics. -/
  residueChar_fin : ∀ w, residueChar (fin w) = residueChar w

variable {K}
variable {k : Type u} [Field k] [NumberField k] (σ : PlaceSection K k)

/-- The section as a map `V(k) → V(K)`. -/
def PlaceSection.toPlace : Place k → Place K
  | Sum.inl w => Place.finite (σ.fin w)
  | Sum.inr w => Place.infinite (σ.inf w)

/-- The section lies over the same rational places. -/
lemma PlaceSection.toRational_toPlace (w : Place k) :
    toRational K (σ.toPlace w) = toRational k w := by
  rcases w with w | w
  · change RationalPlace.finite _ = RationalPlace.finite _
    congr 1
    exact Subtype.ext (σ.residueChar_fin w)
  · rfl

/-- The family of places `σ(w_j) ∈ V` of `K` underlying a tuple `(w_j)_j` of the fiber of `k`. -/
def tuple {ι : Type} (vQ : RationalPlace) (c : ι → LocalTheory.Fiber k vQ) : ι → Place K :=
  fun j => σ.toPlace (c j).1

/-- At a prime, the places of a tuple are the images of the finite places of the fiber. -/
lemma tuple_finite {ι : Type} {p : Nat.Primes} (c : ι → LocalTheory.Fiber k (.finite p))
    (j : ι) : tuple σ _ c j = Place.finite (σ.fin (fiberPlace k (c j))) := by
  unfold tuple
  rw [fiberPlace_spec k (c j)]
  rfl

/-- At the archimedean place, the places of a tuple are the images of the infinite places of
the fiber. -/
lemma tuple_infinite {ι : Type} (c : ι → LocalTheory.Fiber k .infinite) (j : ι) :
    tuple σ _ c j = Place.infinite (σ.inf (fiberInfPlace k (c j))) := by
  unfold tuple
  rw [fiberInfPlace_spec k (c j)]
  rfl

/-- Every place of a tuple of the fiber over `p` lies over `p`. -/
lemma tuple_isOver {ι : Type} (p : Nat.Primes) (c : ι → LocalTheory.Fiber k (.finite p)) :
    ∀ j, ∃ w : FinitePlace K, tuple σ _ c j = Place.finite w ∧ residueChar w = p := by
  intro j
  refine ⟨_, tuple_finite σ c j, ?_⟩
  rw [σ.residueChar_fin, residueChar_fiberPlace]

/-- The finite place `σ(w) ∈ V` of `K` of an element `w` of the fiber of `k` over a prime. -/
noncomputable def sectPlace {p : Nat.Primes} (v : LocalTheory.Fiber k (.finite p)) :
    FinitePlace K :=
  σ.fin (fiberPlace k v)

lemma residueChar_sectPlace {p : Nat.Primes} (v : LocalTheory.Fiber k (.finite p)) :
    residueChar (sectPlace σ v) = p := by
  unfold sectPlace
  rw [σ.residueChar_fin, residueChar_fiberPlace]

/-- The packet presentation at capsule labels `ι` and rational place `v_ℚ`: the direct summands
are indexed by the tuples of places of `V` over `v_ℚ` (IUT III, Proposition 3.1). -/
noncomputable def packet (ι : Type) [Fintype ι] (vQ : RationalPlace) :
    DirectSumPresentation.{u, u} (ι → LocalTheory.Fiber k vQ) where
  Summand c := Tensor K vQ (tuple σ vQ c)
  integral c := integral K vQ (tuple σ vQ c)

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
(IUT III, Propositions 3.1–3.3), indexed by the places of `V` (through `V ≅ V(k)`). -/
noncomputable def container (n : ℕ) : LargeVolumeContainerData.{0, u, u} ℕ (Place k) where
  proc := Procession.standard n
  toRational := toRational k
  fiberFintype vQ := fiberFintype k vQ
  packet i vQ := packet σ ((Procession.standard n).capsule i).LabelType vQ
  logShell i vQ := (packet σ _ vQ).productRegion fun c => logShell K vQ (tuple σ vQ c)
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
      change (packet σ _ _).productRegion _ = (packet σ _ _).integralRegion
      ext x
      simp only [DirectSumPresentation.mem_productRegion,
        DirectSumPresentation.mem_integralRegion]
      refine forall_congr' fun c => ?_
      rw [logShell_eq_integral K p (tuple σ _ c) hodd]
      · rfl
      · intro j w hw
        obtain ⟨w', hw', hres⟩ := tuple_isOver σ p c j
        rw [hw] at hw'
        cases Sum.inl.inj hw'
        exact hunr w hres
    · exact absurd (Or.inl (Or.inl rfl)) hmem
  integral_subset_logShell_nonarch i p := by
    intro x hx c
    exact integral_subset_logShell K p _ (hx c)

variable (n : ℕ)

@[simp] lemma container_proc : (container σ n).proc = Procession.standard n := rfl

/-- The packet weight of a tuple: the product of the place weights (IUT III,
Remark 3.1.1(ii)). -/
noncomputable def tupleWeight {ι : Type} [Fintype ι] (vQ : RationalPlace)
    (c : ι → LocalTheory.Fiber k vQ) : ℝ :=
  ∏ j, weight k vQ (c j)

/-- The scaled integral structure `a·O` of a component. -/
def scaled {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → LocalTheory.Fiber k vQ)
    (a : Tensor K vQ (tuple σ vQ c)) : Set (Tensor K vQ (tuple σ vQ c)) :=
  a • integral K vQ (tuple σ vQ c)

/-- The element `a·1` of the scaled integral structure `a·O` of a component. -/
noncomputable def scaledOne {ι : Type} [Fintype ι] (vQ : RationalPlace)
    (c : ι → LocalTheory.Fiber k vQ)
    (a : Tensor K vQ (tuple σ vQ c)) : Tensor K vQ (tuple σ vQ c) :=
  a • (1 : Tensor K vQ (tuple σ vQ c))

/-- The projection of a region of the packet to a component. -/
def proj {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → LocalTheory.Fiber k vQ)
    (U : Set (packet σ ι vQ).Total) : Set (Tensor K vQ (tuple σ vQ c)) :=
  (fun x => x c) '' U

/-- The projection of a product region with nonempty components is the component. -/
lemma proj_productRegion {ι : Type} [Fintype ι] (vQ : RationalPlace)
    (U : ∀ c : ι → LocalTheory.Fiber k vQ, Set (Tensor K vQ (tuple σ vQ c)))
    (hU : ∀ c, (U c).Nonempty) (c : ι → LocalTheory.Fiber k vQ) :
    proj σ vQ c ((packet σ ι vQ).productRegion U) = U c := by
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

/-- **The concrete log-volume data** (IUT III, Proposition 3.9, with the weights of
Remark 3.1.1(ii)): the packet log-volume is the sum over the direct summands, indexed by the
tuples of places of `V` over `v_ℚ`, of the component log-volumes weighted by the products of the
weights `[k_w : ℚ_{v_ℚ}]/[k : ℚ]`. -/
noncomputable def vol : LogVolumeData (container σ n) where
  weight := weight k
  weight_pos := weight_pos k
  weight_sum_one := weight_sum_one k
  componentVol i vQ c U := componentVol K vQ (tuple σ vQ c) U
  componentVol_integral_nonarch i p c := componentVol_integral K _ _
  componentVol_prime_preimage i p c a ha :=
    componentVol_prime_preimage K p _ (tuple_isOver σ p c) _
      (smul_integral_admissible K _ _ a ha)
  archBall i c := integral K .infinite (tuple σ .infinite c)
  componentVol_archBall i c := componentVol_integral K _ _
  packetVol i vQ U := ∑ c : (container σ n).Components i vQ,
    tupleWeight vQ c * componentVol K vQ (tuple σ vQ c) (proj σ vQ c U)
  packetVol_integral i vQ := by
    refine Finset.sum_eq_zero fun c _ => ?_
    have h : proj σ vQ c ((container σ n).packet i vQ).integralRegion =
        integral K vQ (tuple σ vQ c) :=
      proj_productRegion σ vQ (fun c => integral K vQ (tuple σ vQ c))
        (fun c => ⟨1, one_mem_integral K vQ _⟩) c
    have := congrArg (fun S => tupleWeight vQ c * componentVol K vQ (tuple σ vQ c) S) h
    rw [componentVol_integral K, mul_zero] at this
    exact this
  packetVol_product i vQ U hU := by
    refine Finset.sum_congr rfl fun c _ => ?_
    have h := proj_productRegion σ vQ U hU c
    exact congrArg (fun S => tupleWeight vQ c * componentVol K vQ (tuple σ vQ c) S) h

/-- **The class of hull regions of a packet** among which the holomorphic hull is least
(`HullSystem.HullRegions`): all regions `a·O` with all components of `a` units, i.e. with every
direct-summand component of `a` nonzero (IUT III, Remark 3.9.5(i)) — at a prime `O = (R_I)^∼`,
at the archimedean place `O = B_I`, the product of the unit balls of the copies of `ℝ`, `ℂ` in
the direct sum decomposition of the packet (IUT IV, Proposition 1.5(iii)). -/
def hullRegions (ι : Type) [Fintype ι] :
    ∀ vQ : RationalPlace, Set (Set (packet σ ι vQ).Total)
  | .finite p => {R | (packet σ ι (.finite p)).IsHullRegion R}
  | .infinite => {R | (packet σ ι .infinite).IsHullRegion R}

/-- Members of the class of hull regions are hull regions `a·O` with all components of
`a` units. -/
lemma isHullRegion_of_mem_hullRegions (ι : Type) [Fintype ι] (vQ : RationalPlace) :
    ∀ R ∈ hullRegions σ ι vQ, (packet σ ι vQ).IsHullRegion R := by
  cases vQ with
  | finite p => exact fun R hR => hR
  | infinite => exact fun R hR => hR

/-- The holomorphic integral region belongs to the class of hull regions. -/
lemma integralRegion_mem_hullRegions (ι : Type) [Fintype ι] (vQ : RationalPlace) :
    (packet σ ι vQ).integralRegion ∈ hullRegions σ ι vQ := by
  cases vQ with
  | finite p => exact (packet σ ι (.finite p)).isHullRegion_integralRegion
  | infinite => exact (packet σ ι .infinite).isHullRegion_integralRegion

/-- **Least hull regions of product regions** with admissible components, from the least
hull regions of the components (`exists_leastHull` at a prime, `exists_leastHull_infinite` at
`∞`). -/
lemma exists_leastHullRegion (ι : Type) [Fintype ι] (vQ : RationalPlace)
    (fam : ∀ c : ι → LocalTheory.Fiber k vQ, Set (Tensor K vQ (tuple σ vQ c)))
    (hfam : ∀ c, fam c ∈ admissible K vQ (tuple σ vQ c)) :
    ∃ R, (packet σ ι vQ).IsLeastHullRegionIn (hullRegions σ ι vQ)
      ((packet σ ι vQ).productRegion fam) R := by
  cases vQ with
  | finite p =>
    choose a ha using fun c => exists_leastHull K p (tuple σ _ c) (fam c) (hfam c)
    refine ⟨(packet σ _ _).scaledIntegral a, ⟨a, fun c => (ha c).1, rfl⟩, ?_, ?_⟩
    · intro x hx c
      exact (ha c).2.1 (hx c)
    · rintro R ⟨b, hb, rfl⟩ hUR
      intro x hx c
      have hproj : fam c ⊆ scaled σ _ c (b c) := by
        have := proj_productRegion σ _ fam
          (fun c => admissible_nonempty K _ _ _ (hfam c)) c
        rw [← this]
        rintro y ⟨z, hz, rfl⟩
        exact hUR hz c
      exact (ha c).2.2 (b c) (hb c) hproj (hx c)
  | infinite =>
    choose a ha using fun c => exists_leastHull_infinite K (tuple σ _ c) (fam c) (hfam c)
    refine ⟨(packet σ _ _).scaledIntegral a, ⟨a, fun c => (ha c).1, rfl⟩, ?_, ?_⟩
    · intro x hx c
      exact (ha c).2.1 (hx c)
    · rintro R ⟨b, hb, rfl⟩ hUR
      intro x hx c
      have hproj : fam c ⊆ scaled σ _ c (b c) := by
        have := proj_productRegion σ _ fam
          (fun c => admissible_nonempty K _ _ _ (hfam c)) c
        rw [← this]
        rintro y ⟨z, hz, rfl⟩
        exact hUR hz c
      exact (ha c).2.2 (b c) (hb c) hproj (hx c)

/-- **The concrete hull system**: least hull regions of product regions with admissible
components, from the least hull regions of the components. -/
noncomputable def hull : ContainerHullSystem (container σ n) where
  system i vQ :=
    HullSystem.ofExists (packet σ _ vQ)
      {U | ∃ fam : ∀ c, Set (Tensor K vQ (tuple σ vQ c)),
        (∀ c, fam c ∈ admissible K vQ (tuple σ vQ c)) ∧
          U = (packet σ _ vQ).productRegion fam}
      (by
        rintro U ⟨fam, hfam, rfl⟩
        exact isCompact_closure_productRegion _ _ fun c =>
          admissible_relCompact K vQ _ _ (hfam c))
      (hullRegions σ _ vQ)
      (isHullRegion_of_mem_hullRegions σ _ vQ)
      (integralRegion_mem_hullRegions σ _ vQ)
      (by
        rintro U ⟨fam, hfam, rfl⟩
        exact exists_leastHullRegion σ _ vQ fam hfam)
      (by
        rintro U ⟨fam, hfam, rfl⟩ R ⟨hR, _, _⟩
        obtain ⟨a, ha, rfl⟩ := isHullRegion_of_mem_hullRegions σ _ vQ R hR
        exact ⟨fun c => scaled σ vQ c (a c),
          fun c => smul_integral_admissible K vQ _ (a c) (ha c), rfl⟩)
  integral_admissible i vQ :=
    ⟨fun c => integral K vQ (tuple σ vQ c), fun c => integral_admissible K vQ _, rfl⟩

/-- **The theta-pilot component at the archimedean place** (IUT IV, Theorem 1.10, Step (vii)):
the union of the images of the tensor product of the log-shells (the closed absolutely convex
hull of the tensor products `⊗_j y_j` of log-shell elements `|y_j| ≤ π`, IUT III, Proposition
3.2(ii); IUT IV, Proposition 1.5(iv)) under the indeterminacy automorphisms (IUT III, Theorem
3.11 (Ind1), (Ind2)). -/
noncomputable def thetaInfinite (i : Fin n)
    (c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber k .infinite) :
    Set (Tensor K .infinite (tuple σ .infinite c)) :=
  ⋃ φ ∈ indAut K .infinite (tuple σ .infinite c),
    φ '' logShell K .infinite (tuple σ .infinite c)

end LocalTheory

end Iut
