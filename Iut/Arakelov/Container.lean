/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Wall.QPilotRegion
import Iut.Arakelov.LineBundle

/-!
# Log-volumes of regions `(a_v·𝒪_v)_v` as Arakelov degrees (IUT III, Proposition 3.9(iii))

IUT III, Proposition 3.9(iii) (Global Compatibility): the global log-volume (the sum over
`v_ℚ ∈ V_ℚ` of the packet log-volumes) of the region determined by an object `J = {J_v}_{v ∈ V}`
of the global realified Frobenioid `F^⊛_mod` is "equal to the degree of the arithmetic line bundle
determined by `J`, relative to a suitable normalization", and it is invariant under
multiplication by the global multiplicative monoid (the product formula). Here this is proved
for the concrete large volume container of initial Θ-data `D` (`Iut/Concrete/Container.lean`).

## The regions

A `ScalingDatum D` is a family `b = (b_w)_w`, `b_w ∈ K_w^×` at the finite places `w` of the
`ℓ`-torsion field `K`, with `b_w = 1` away from finitely many residue characteristics. The region
`scale D a lab O` is, in the capsule `i` of the procession, the integral structure with each
packet component (indexed by a tuple `c` of places of the valuation section `V ≅ V_mod`) scaled by
`b_v`, `b = a i`, `v = c(lab i)`, in the tensor factor of the label `lab i`; integral at `∞`. This
is the region `(a_v·𝒪_v)_{v ∈ V}` of IUT III, Proposition 3.9(iii), placed in one tensor factor of
each capsule (the same choice as for `LGP·O` and the `q`-pilot region in
`Iut/Wall/QPilotRegion.lean`, whose `pow` is the special case `scale D (qPow D e)`).

## Results

* `packetVol_scale_integral_finite`, `globalVol_scale_integral`: the packet log-volume at `p` is
  `−log p·Σ_{w | p} ([(F_mod)_w : ℚ_p]/[F_mod : ℚ])·ord_p(b_{v(w)})` (`ScalingDatum.sectDegAt`),
  the global log-volume of a capsule is `−sectDeg b`;
* `logVol_scale_integral`: the procession-normalized log-volume is the average over the capsules;
* **`ScalingDatum.degNorm_toBundle`**: if `ord_p(b_v)` depends only on the place of `F_mod`
  below `v` (`IsModInvariant`: the "`F_mod`-rationality" of the objects of `F^⊛_mod`), then
  `sectDeg b` is the **normalized Arakelov degree** `deg(L_b)/[K : ℚ]` of the arithmetic line
  bundle `L_b` with idelic description `b` (trivial archimedean metrics; `toBundle`): the
  section-average over `V` of IUT III, Remark 3.1.1(ii) equals the average over all places of
  `K` (`sum_placeWeight_placeUnder`);
* **`logVol_scale_integral_eq_degNorm`**, **`logVol_scaleConst_eq_neg_degNorm`** (IUT III,
  Proposition 3.9(iii)): `log-vol((b_v·𝒪_v)_v) = −deg(L_b)/[K : ℚ]`.

Archimedean metrics (`r_v·B_v` in the archimedean packets) and the invariance of the log-volume
under `F_mod^×` (the product formula on regions) are added in `Iut/Arakelov/ArchScaling.lean`.

## Sign convention

The degree `deg(L_b) = −Σ_w log‖b_w‖_w` is the degree of the arithmetic divisor
`Σ_w ord_w(b_w)·[w]` of the section with local norms `‖b_w‖_w`; the region `b·𝒪` is the
lattice of that divisor's *inverse*, so `log-vol(b·𝒪) = −deg(L_b)` (equivalently: `log-vol(J)` is
the degree of the line bundle whose lattice is `J`, as in IUT III, Proposition 3.9(iii)).
-/

namespace Iut

namespace Arakelov

open NumberField Wall
open scoped Pointwise

universe u

/-! ### Grouping a sum over the finite places by residue characteristic -/

section Fibers

variable {K : Type u} [Field K] [NumberField K]

lemma finite_residueChar_mem (S : Finset ℕ) : {w : FinitePlace K | residueChar w ∈ S}.Finite := by
  have h : {w : FinitePlace K | residueChar w ∈ S} =
      ⋃ p ∈ S, {w : FinitePlace K | residueChar w = p} := by
    ext w
    simp
  rw [h]
  refine S.finite_toSet.biUnion fun p _ => ?_
  haveI := LocalTheory.fiber_finite K p
  exact Set.finite_coe_iff.mp this

/-- A finitely supported sum over the finite places, grouped by residue characteristic. -/
lemma finsum_eq_sum_fiber [∀ p, Fintype {w : FinitePlace K // residueChar w = p}]
    (f : FinitePlace K → ℝ) (S : Finset ℕ) (hS : ∀ w, residueChar w ∉ S → f w = 0) :
    ∑ᶠ w, f w = ∑ p ∈ S, ∑ w : {w : FinitePlace K // residueChar w = p}, f w.1 := by
  classical
  have hfin := finite_residueChar_mem (K := K) S
  have hsub : Function.support f ⊆ ↑hfin.toFinset := by
    intro w hw
    rw [hfin.coe_toFinset]
    by_contra h
    exact hw (hS w h)
  rw [finsum_eq_sum_of_support_subset f hsub,
    ← Finset.sum_fiberwise_of_maps_to (g := residueChar) (t := S)
      (fun w hw => by simpa using hw)]
  refine Finset.sum_congr rfl fun p hp => ?_
  refine Finset.sum_subtype _ (fun w => ?_) f
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h ▸ hp, h⟩

end Fibers

variable (D : InitialThetaData.{u})

/-! ### Idelic scaling data on the `ℓ`-torsion field -/

/-- **An idelic scaling datum** `b = (b_w)_w` on the finite places of `K`: `b_w ∈ K_w^×`, with
`b_w = 1` away from the finitely many residue characteristics `chars`. -/
structure ScalingDatum where
  /-- The local components `b_w`. -/
  elt : ∀ w : FinitePlace D.Kt, completionAt D.Kt w
  elt_ne_zero : ∀ w, elt w ≠ 0
  /-- A finite set of residue characteristics outside which `b_w = 1`. -/
  chars : Finset ℕ
  elt_eq_one : ∀ w, residueChar w ∉ chars → elt w = 1

namespace ScalingDatum

variable {D} (b : ScalingDatum D)

/-- **The arithmetic line bundle of `b`**: idelic description `b` at the finite places, trivial
metrics at the archimedean places. -/
noncomputable def toBundle : ArithLineBundle D.Kt where
  fin := b.elt
  fin_ne_zero := b.elt_ne_zero
  finite_fin := (finite_residueChar_mem b.chars).subset fun w hw => by
    by_contra h
    exact hw (show ‖b.elt w‖ = 1 by rw [b.elt_eq_one w h, norm_one])
  inf _ := 1
  inf_pos _ := one_pos

/-- The primes in `chars`. -/
def primes : Finset Nat.Primes := b.chars.subtype Nat.Prime

/-- The contribution of the prime `p` to the section-average degree:
`log p · Σ_{w | p} ([(F_mod)_w : ℚ_p]/[F_mod : ℚ])·ord_p(b_{v(w)})`, `v(w) ∈ V` the place of the
valuation section over `w` (IUT III, Remark 3.1.1(ii)). -/
noncomputable def sectDegAt (p : Nat.Primes) : ℝ :=
  Real.log p * ∑ u : LocalTheory.Fiber D.Fmod (.finite p), LocalTheory.weight D.Fmod _ u *
    ordp D.Kt (LocalTheory.sectPlace D.placeSect u) (b.elt (LocalTheory.sectPlace D.placeSect u))

/-- **The section-average degree** of `b`: the sum of the `sectDegAt p`. -/
noncomputable def sectDeg : ℝ := ∑ p ∈ b.primes, b.sectDegAt p

/-- A sum over `primes` as a sum over the primes in `chars`. -/
lemma sum_primes (f : ℕ → ℝ) : ∑ p ∈ b.primes, f p = ∑ p ∈ b.chars.filter Nat.Prime, f p :=
  Finset.sum_subtype_eq_sum_filter f

lemma sectDegAt_eq_zero (p : Nat.Primes) (hp : p ∉ b.primes) : b.sectDegAt p = 0 := by
  have hp' : (p : ℕ) ∉ b.chars := fun h => hp (Finset.mem_subtype.mpr h)
  unfold sectDegAt
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun u _ => ?_)
  rw [b.elt_eq_one _ (by rw [LocalTheory.residueChar_sectPlace]; exact hp')]
  simp [ordp]

/-- **`F_mod`-rationality**: `ord_p(b_v)` depends only on the place of `F_mod` below `v`. -/
def IsModInvariant : Prop :=
  ∀ v v' : FinitePlace D.Kt, placeUnder (k := D.Fmod) v = placeUnder (k := D.Fmod) v' →
    ordp D.Kt v (b.elt v) = ordp D.Kt v' (b.elt v')

/-- The normalized local degrees of `L_b` over `p` sum to `sectDegAt p`. -/
lemma sum_fiber_eq_sectDegAt (h : b.IsModInvariant) (p : Nat.Primes)
    [Fintype {w : FinitePlace D.Kt // residueChar w = p}] :
    ∑ w : {w : FinitePlace D.Kt // residueChar w = p},
        placeWeight D.Kt w.1 * (ordp D.Kt w.1 (b.elt w.1) * Real.log (residueChar w.1)) =
      b.sectDegAt p := by
  letI : Fintype {w : FinitePlace D.Fmod // residueChar w = p} :=
    @Fintype.ofFinite _ (LocalTheory.fiber_finite D.Fmod p)
  set c : FinitePlace D.Fmod → ℝ := fun u =>
    ordp D.Kt (D.V.sectFin u) (b.elt (D.V.sectFin u)) * Real.log p with hc
  have h1 : ∀ w : {w : FinitePlace D.Kt // residueChar w = p},
      placeWeight D.Kt w.1 * (ordp D.Kt w.1 (b.elt w.1) * Real.log (residueChar w.1)) =
        placeWeight D.Kt w.1 * c (placeUnder w.1) := by
    intro w
    rw [w.2, hc]
    congr 2
    exact h _ _ (eq_placeUnder_of_liesOver (D.V.sectFin_liesOver (placeUnder w.1)))
  rw [Finset.sum_congr rfl fun w _ => h1 w, sum_placeWeight_placeUnder (p : ℕ) c, sectDegAt,
    Finset.mul_sum]
  refine (Fintype.sum_equiv (LocalTheory.fiberFiniteEquiv D.Fmod p) _ _ fun u => ?_).symm
  rw [LocalTheory.weight_finite_eq, hc]
  change _ = placeWeight D.Fmod (LocalTheory.fiberPlace D.Fmod u) *
    (ordp D.Kt (D.V.sectFin (LocalTheory.fiberPlace D.Fmod u))
      (b.elt (D.V.sectFin (LocalTheory.fiberPlace D.Fmod u))) * Real.log p)
  change Real.log p * (placeWeight D.Fmod (LocalTheory.fiberPlace D.Fmod u) *
    ordp D.Kt (D.V.sectFin (LocalTheory.fiberPlace D.Fmod u))
      (b.elt (D.V.sectFin (LocalTheory.fiberPlace D.Fmod u)))) = _
  ring

/-- **The section-average degree is the normalized Arakelov degree** (for `F_mod`-rational
`b`): `sectDeg b = deg(L_b)/[K : ℚ]`. The average over the valuation section `V ≅ V_mod`, with
the weights `[(F_mod)_w : ℚ_p]/[F_mod : ℚ]` of IUT III, Remark 3.1.1(ii), is the average over all
places of `K` with the weights `[K_v : ℚ_p]/[K : ℚ]`. -/
theorem degNorm_toBundle (h : b.IsModInvariant) : b.toBundle.degNorm = b.sectDeg := by
  classical
  letI : ∀ p, Fintype {w : FinitePlace D.Kt // residueChar w = p} := fun p =>
    @Fintype.ofFinite _ (LocalTheory.fiber_finite D.Kt p)
  rw [ArithLineBundle.degNorm_eq]
  have hinf : ∑ v, -(infPlaceWeight D.Kt v * Real.log (b.toBundle.inf v)) = 0 := by
    simp [toBundle]
  rw [hinf, add_zero]
  have hS : ∀ w, residueChar w ∉ b.chars.filter Nat.Prime →
      placeWeight D.Kt w * (ordp D.Kt w (b.toBundle.fin w) * Real.log (residueChar w)) = 0 := by
    intro w hw
    have : residueChar w ∉ b.chars := fun hc =>
      hw (Finset.mem_filter.mpr ⟨hc, residueChar_prime w⟩)
    simp [toBundle, b.elt_eq_one w this, ordp]
  rw [finsum_eq_sum_fiber _ _ hS, ← Finset.sum_subtype_eq_sum_filter, sectDeg]
  exact Finset.sum_congr rfl fun p _ => b.sum_fiber_eq_sectDegAt h p

end ScalingDatum

/-! ### The scaled regions -/

variable (a : Fin (nC D) → ScalingDatum D) (lab : ∀ i, InitialThetaData.Lab (nC D) i)

/-- The element `b_v`, `b = a i`, `v = c(lab i)`, in the tensor factor of the label `lab i`. -/
noncomputable def scaleElt (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c) :=
  LocalTheory.incl D.Kt p (LocalTheory.tuple D.placeSect _ c) (lab i)
    (LocalTheory.sectPlace D.placeSect (c (lab i)))
    (LocalTheory.tuple_finite D.placeSect c (lab i))
    ((a i).elt (LocalTheory.sectPlace D.placeSect (c (lab i))))

lemma isUnit_scaleElt (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    IsUnit (scaleElt D a lab i p c) :=
  LocalTheory.isUnit_incl D.Kt p _ _ _ _ _ ((a i).elt_ne_zero _)

/-- Multiplication by `scaleElt`. -/
noncomputable def scaleMap (i : Fin (nC D)) (p : Nat.Primes) :
    (LocalTheory.packet D.placeSect (InitialThetaData.Lab (nC D) i) (.finite p)).Total →
      (LocalTheory.packet D.placeSect (InitialThetaData.Lab (nC D) i) (.finite p)).Total :=
  fun x c => @HMul.hMul (LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c))
    (LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c))
    (LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)) instHMul
    (scaleElt D a lab i p c) (x c)

lemma scaleMap_eq_id (i : Fin (nC D)) (p : Nat.Primes) (hp : (p : ℕ) ∉ (a i).chars) :
    scaleMap D a lab i p = id := by
  funext x c
  have h1 : scaleElt D a lab i p c = 1 := by
    unfold scaleElt
    rw [(a i).elt_eq_one _ (by rw [LocalTheory.residueChar_sectPlace D.placeSect]; exact hp),
      map_one]
  simp only [scaleMap, h1, one_mul, id]

/-- The packet regions of `scale D a lab R`. -/
noncomputable def scaleRegion (i : Fin (VC D).proc.length) (R : (VC D).AdmissibleRegion i) :
    ∀ vQ : RationalPlace, Set ((VC D).packet i vQ).Total
  | .finite p => scaleMap D a lab i p '' R.region (.finite p)
  | .infinite => R.region .infinite

/-- `scale D a lab R` at capsule `i`. -/
noncomputable def scaleAt (i : Fin (VC D).proc.length) (R : (VC D).AdmissibleRegion i) :
    (VC D).AdmissibleRegion i where
  region := scaleRegion D a lab i R
  finiteSupport := by
    refine (R.finiteSupport.union (((a i).chars.finite_toSet.image
      fun q : ℕ => if h : q.Prime then RationalPlace.finite ⟨q, h⟩ else .infinite))).subset
      fun vQ hvQ => ?_
    rcases vQ with p | _
    · by_cases hp : (p : ℕ) ∈ (a i).chars
      · exact Or.inr ⟨p, hp, by simp [p.2]⟩
      · refine Or.inl fun h => hvQ ?_
        change scaleMap D a lab i p '' R.region (.finite p) = _
        rw [scaleMap_eq_id D a lab i p hp, Set.image_id]
        exact h
    · exact Or.inl hvQ

/-- **The region `S` scaled by the idelic data `a i`** (at the labels `lab i`): for `S = O`, the
region `(b_v·𝒪_v)_{v ∈ V}` of IUT III, Proposition 3.9(iii) in each capsule. -/
noncomputable def scale (S : Region D) : Region D := fun i => scaleAt D a lab i (S i)

lemma proj_scale (S : Region D) (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    LocalTheory.proj D.placeSect (.finite p) c ((scale D a lab S i).region (.finite p)) =
      scaleElt D a lab i p c • LocalTheory.proj D.placeSect (.finite p) c
        ((S i).region (.finite p)) := by
  change (fun x => x c) '' (scaleMap D a lab i p '' (S i).region (.finite p)) = _
  rw [Set.image_image]
  unfold LocalTheory.proj
  rw [← Set.image_smul, Set.image_image]
  rfl

/-- `scale D a lab S` is adelic for adelic `S`. -/
theorem isAdelic_scale {S : Region D} (hS : IsAdelic D S) : IsAdelic D (scale D a lab S) := by
  intro i vQ
  rcases vQ with p | _
  · obtain ⟨fam, hfam, hR⟩ := hS i (.finite p)
    refine ⟨fun c => scaleElt D a lab i p c • fam c, fun c =>
      LocalConstruct.units_smul_mem_admissible (isUnit_scaleElt D a lab i p c) (hfam c), ?_⟩
    change scaleMap D a lab i p '' (S i).region (.finite p) = _
    rw [hR]
    ext x
    simp only [DirectSumPresentation.mem_productRegion, Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩ c
      exact ⟨y c, hy c, rfl⟩
    · intro hx
      choose y hy hxy using hx
      exact ⟨y, hy, funext hxy⟩
  · exact hS i .infinite

/-! ### The log-volume of `scale D a lab O` -/

/-- `μ^log(b_v·O) = −ord_p(b_v)·log p`, `v = c(lab i)` (IUT IV, Proposition 1.4). -/
theorem componentVol_scaleElt (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)
        (scaleElt D a lab i p c • LocalTheory.integral D.Kt (.finite p)
          (LocalTheory.tuple D.placeSect _ c)) =
      -ordp D.Kt (LocalTheory.sectPlace D.placeSect (c (lab i)))
        ((a i).elt (LocalTheory.sectPlace D.placeSect (c (lab i)))) * Real.log p := by
  classical
  set j := lab i
  set W := fun l => LocalTheory.sectPlace D.placeSect (c l)
  set y : ∀ l, completionAt D.Kt (W l) := Function.update (fun _ => 1) j ((a i).elt (W j))
  have hy : ∀ l, y l ≠ 0 := by
    intro l
    by_cases h : l = j
    · subst h
      simp only [y, Function.update_self]
      exact (a i).elt_ne_zero _
    · simp only [y, Function.update_of_ne h]
      exact one_ne_zero
  have hprod : (∏ l, LocalConstruct.incl p (LocalTheory.tuple D.placeSect _ c) l (W l)
      (LocalTheory.tuple_finite D.placeSect c l) (y l)) = scaleElt D a lab i p c := by
    rw [Finset.prod_eq_single j]
    · simp only [y, Function.update_self]
      rfl
    · intro l _ hl
      simp only [y, Function.update_of_ne hl, map_one]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hsum : ∑ l, ordp D.Kt (W l) (y l) = ordp D.Kt (W j) ((a i).elt (W j)) := by
    rw [Finset.sum_eq_single j]
    · simp only [y, Function.update_self]
    · intro l _ hl
      simp only [y, Function.update_of_ne hl]
      simp [ordp, norm_one]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have := LocalConstruct.componentVol_prod_incl_smul_integral
    (LocalTheory.tuple_isOver D.placeSect p c) W (LocalTheory.tuple_finite D.placeSect c) y hy
  rw [hprod, hsum] at this
  exact this

/-- **The packet log-volume of `scale D a lab O` at `p`** is `−sectDegAt (a i) p`. -/
theorem packetVol_scale_integral_finite (i : Fin (nC D)) (p : Nat.Primes) :
    (LocalTheory.vol D.placeSect (nC D)).packetVol i (.finite p)
        ((scale D a lab (integralRegion D) i).region (.finite p)) = -(a i).sectDegAt p := by
  rw [LocalTheory.packetVol_eq]
  have hpO : ∀ c, LocalTheory.proj D.placeSect (.finite p) c
      ((integralRegion D i).region (.finite p)) =
      LocalTheory.integral D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c) := fun c =>
    LocalTheory.proj_productRegion D.placeSect _ _
      (fun c => ⟨1, LocalTheory.one_mem_integral D.Kt _ _⟩) c
  have hc : ∀ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
      LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)
        (LocalTheory.proj D.placeSect (.finite p) c
          ((scale D a lab (integralRegion D) i).region (.finite p))) =
      -ordp D.Kt (LocalTheory.sectPlace D.placeSect (c (lab i)))
        ((a i).elt (LocalTheory.sectPlace D.placeSect (c (lab i)))) * Real.log p := by
    intro c
    rw [proj_scale, hpO]
    exact componentVol_scaleElt D a lab i p c
  simp only [hc]
  have key := sum_prod_tuple_mul_coord (LocalTheory.weight D.Fmod (.finite p))
    (LocalTheory.weight_sum_one D.Fmod _)
    (fun v => ordp D.Kt (LocalTheory.sectPlace D.placeSect v)
      ((a i).elt (LocalTheory.sectPlace D.placeSect v))) (lab i)
  have hsplit : ∀ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
      LocalTheory.tupleWeight (.finite p) c * (-ordp D.Kt
        (LocalTheory.sectPlace D.placeSect (c (lab i)))
        ((a i).elt (LocalTheory.sectPlace D.placeSect (c (lab i)))) * Real.log p) =
      (-Real.log p) *
        ((∏ l, LocalTheory.weight D.Fmod (.finite p) (c l)) *
          ordp D.Kt (LocalTheory.sectPlace D.placeSect (c (lab i)))
            ((a i).elt (LocalTheory.sectPlace D.placeSect (c (lab i))))) := by
    intro c
    unfold LocalTheory.tupleWeight
    ring
  rw [Finset.sum_congr rfl fun c _ => hsplit c, ← Finset.mul_sum, key, ScalingDatum.sectDegAt]
  ring

/-- **The global log-volume of `scale D a lab O` at capsule `i`** (the sum over `V_ℚ` of IUT III,
Proposition 3.9(iii)) is `−sectDeg (a i)`. -/
theorem globalVol_scale_integral (i : Fin (nC D)) :
    (LocalTheory.vol D.placeSect (nC D)).globalVol (scale D a lab (integralRegion D) i) =
      -(a i).sectDeg := by
  classical
  unfold LogVolumeData.globalVol
  set g := fun vQ => (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ
    ((scale D a lab (integralRegion D) i).region vQ) with hg
  have hinf : g .infinite = 0 :=
    (LocalTheory.vol D.placeSect (nC D)).packetVol_integral i .infinite
  have hsupp : Function.support g ⊆ ↑((a i).primes.image RationalPlace.finite) := by
    intro vQ hvQ
    rcases vQ with p | _
    · by_contra h
      apply hvQ
      change (LocalTheory.vol D.placeSect (nC D)).packetVol i (.finite p) _ = 0
      rw [packetVol_scale_integral_finite, (a i).sectDegAt_eq_zero p
        (fun hp => h (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hp))), neg_zero]
    · exact absurd hinf hvQ
  rw [finsum_eq_sum_of_support_subset g hsupp,
    Finset.sum_image (fun p _ q _ h => RationalPlace.finite.inj h), ScalingDatum.sectDeg,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ => packetVol_scale_integral_finite D a lab i p

/-- **The procession-normalized log-volume of `scale D a lab O`** is the average over the
capsules of `−sectDeg (a i)`. -/
theorem logVol_scale_integral :
    logVol D (scale D a lab (integralRegion D)) = -(∑ i, (a i).sectDeg) / nC D := by
  unfold logVol LogVolumeData.processionVol
  simp only [globalVol_scale_integral]
  rw [Finset.sum_neg_distrib]
  rfl

/-- **IUT III, Proposition 3.9(iii) for the concrete container**: the procession-normalized
log-volume of the region `(b_v·𝒪_v)` (`b = a i` in the capsule `i`) is the average over the
capsules of minus the normalized Arakelov degrees of the arithmetic line bundles `L_{a i}`. -/
theorem logVol_scale_integral_eq_degNorm (h : ∀ i, (a i).IsModInvariant) :
    logVol D (scale D a lab (integralRegion D)) =
      -(∑ i, (a i).toBundle.degNorm) / nC D := by
  rw [logVol_scale_integral]
  simp only [fun i => (a i).degNorm_toBundle (h i)]

/-- **`log-vol((b_v·𝒪_v)_v) = −deg(L_b)/[K : ℚ]`** (IUT III, Proposition 3.9(iii)): the same
idelic datum `b` in every capsule. -/
theorem logVol_scaleConst_eq_neg_degNorm (b : ScalingDatum D) (hb : b.IsModInvariant) :
    logVol D (scale D (fun _ => b) lab (integralRegion D)) = -b.toBundle.degNorm := by
  rw [logVol_scale_integral_eq_degNorm D _ lab fun _ => hb]
  have hn : (nC D : ℝ) ≠ 0 := by exact_mod_cast (nC_pos D).ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end Arakelov

end Iut
