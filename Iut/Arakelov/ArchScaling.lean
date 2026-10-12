/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Arakelov.Container

/-!
# Archimedean scalings and the product formula on regions (IUT III, Proposition 3.9(iii))

`Iut/Arakelov/Container.lean` proves `log-vol((b_v·𝒪_v)_v) = −deg(L_b)/[K : ℚ]` for idelic data
`b` at the finite places only (trivial archimedean metrics). This file adds the archimedean
metrics and proves the product formula on regions.

## Archimedean scalings

A `FullScalingDatum D` is a `ScalingDatum D` together with positive reals `r_v` at the infinite
places `v` of the `ℓ`-torsion field `K` (`rad`). Its arithmetic line bundle `toBundle` has the
idelic description `b` at the finite places and the metrics `r_v` at the archimedean places.
The region `fullScale D a lab S` is `scale D a lab S` (`Iut/Arakelov/Container.lean`) further
scaled, in the archimedean packet of capsule `i`, by the real number `r_{v}`, `v = c(lab i)`, in
each component `c` (`archScaleElt`; a real scalar of the factor `lab i` is the same as the real
scalar of the whole tensor packet `⊗_j K_{c j}`, an `ℝ`-algebra). By
`LocalTheory.componentVol_arch_scale`, `μ^log(r·B_I) = log r`.

## Results

* `sum_mult_comap_eq`: `∑_{v ∣ u} [K_v : ℝ] = [K : k]·[k_u : ℝ]` for an extension of number fields
  (from `InfinitePlace.unramifedPlacesOver_ncard_add_eq_finrank`), and its normalized form
  `sum_infPlaceWeight_comap` (the archimedean analogue of `sum_placeWeight_placeUnder`);
* `packetVol_fullScale_integral_infinite`: the archimedean packet log-volume of
  `fullScale D a lab O` is `Σ_{u ∈ V_mod^arc} ([(F_mod)_u : ℝ]/[F_mod : ℚ])·log r_{v(u)}`
  (`= −archSectDeg`);
* `globalVol_fullScale_integral`, `logVol_fullScale_integral`: the global log-volume of a capsule
  is `−fullSectDeg = −(sectDeg + archSectDeg)`;
* **`FullScalingDatum.degNorm_toBundle`**: for `F_mod`-rational data (`IsModInvariant`: `ord_p(b_v)`
  and `r_v` depend only on the place of `F_mod` below `v`), `fullSectDeg` is the normalized
  Arakelov degree `deg(L)/[K : ℚ]` of `L = toBundle`, archimedean part included;
* **`logVol_fullScale_integral_eq_degNorm`**, **`logVol_fullScaleConst_eq_neg_degNorm`**:
  `log-vol((b_v·𝒪_v)_{v ∤ ∞}, (r_v·B_v)_{v ∣ ∞}) = −deg(L)/[K : ℚ]` (IUT III, Proposition 3.9(iii),
  with the archimedean part).

## The product formula on regions

For `x ∈ F_mod^×`, `diag x hx` is the diagonal image of `x`: the components `x ∈ K_w` at all finite
places over the finitely many residue characteristics where some `|x|_w ≠ 1`, and `|x|_v` at the
archimedean places. (At the other finite places `x` is a unit, and its component is replaced by
`1`; the region `x·𝒪_w = 𝒪_w` is the same.) It is `F_mod`-rational (`isModInvariant_diag`, from
`ordp_embedCompletion` and `InfinitePlace.comap_apply`), and its bundle has the degree of the
principal bundle of `x`, which is `0` by the product formula (`deg_toBundle_diag`). Hence:

* **`logVol_fullScale_mul_diag`** (IUT III, Proposition 3.9(iii), the invariance of the log-volume
  under the global multiplicative monoid): for `F_mod`-rational data `a`, scaling every capsule
  further by the diagonal image of `x ∈ F_mod^×` does not change the log-volume;
* **`logVol_fullScale_diag`**: `log-vol(x·O) = log-vol(O) = 0`.

The restriction to `x ∈ F_mod^×` (rather than `K^×`) is the one of IUT III: the objects of
`F^⊛_mod` and the global monoid acting on them come from `F_mod`; the regions see the places of
the valuation section `V ≅ V_mod` only, and for `x ∈ K^× ∖ F_mod` the `V`-average of `ord(x)`
need not be the average over all places of `K`.
-/

namespace Iut

namespace Arakelov

open NumberField Wall
open scoped Pointwise

universe u

/-! ### Archimedean fibers of an extension of number fields -/

section ArchFiber

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

omit [NumberField k] [NumberField K] in
lemma infinitePlace_liesOver_iff (v : InfinitePlace K) (u : InfinitePlace k) :
    v.1.LiesOver u.1 ↔ v.comap (algebraMap k K) = u := by
  constructor
  · intro h
    exact InfinitePlace.LiesOver.comap_eq v u
  · intro h
    subst h
    exact ⟨rfl⟩

open scoped Classical in
/-- **`∑_{v ∣ u} [K_v : ℝ] = [K : k]·[k_u : ℝ]`** for an infinite place `u` of `k`. -/
theorem sum_mult_comap_eq (u : InfinitePlace k) :
    ∑ v ∈ Finset.univ.filter (fun v : InfinitePlace K => v.comap (algebraMap k K) = u),
      v.mult = Module.finrank k K * u.mult := by
  set S := Finset.univ.filter (fun v : InfinitePlace K => v.comap (algebraMap k K) = u)
  have hfr := InfinitePlace.unramifedPlacesOver_ncard_add_eq_finrank (L := K) u
  have hU : InfinitePlace.unramifiedPlacesOver K u =
      ↑(S.filter fun v => v.IsUnramified k) := by
    ext v
    simp [S, InfinitePlace.unramifiedPlacesOver, infinitePlace_liesOver_iff]
  have hR : InfinitePlace.ramifiedPlacesOver K u =
      ↑(S.filter fun v => ¬ v.IsUnramified k) := by
    ext v
    simp [S, InfinitePlace.ramifiedPlacesOver, infinitePlace_liesOver_iff]
  rw [hU, hR, Set.ncard_coe_finset, Set.ncard_coe_finset] at hfr
  rw [← Finset.sum_filter_add_sum_filter_not S (fun v => v.IsUnramified k)]
  have h1 : ∀ v ∈ S.filter (fun v => v.IsUnramified k), v.mult = u.mult := by
    intro v hv
    simp only [Finset.mem_filter, S, Finset.mem_univ, true_and] at hv
    rw [← hv.1]
    exact hv.2.symm
  have h2 : ∀ v ∈ S.filter (fun v => ¬ v.IsUnramified k), v.mult = 2 := by
    intro v hv
    simp only [Finset.mem_filter] at hv
    have hc := InfinitePlace.IsRamified.isComplex (k := k) hv.2
    simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.mpr hc]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, ← hfr]
  by_cases hr : (S.filter fun v => ¬ v.IsUnramified k) = ∅
  · rw [hr]
    simp
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hr
    simp only [Finset.mem_filter, S, Finset.mem_univ, true_and] at hv
    have hre := InfinitePlace.IsRamified.isReal (k := k) hv.2
    rw [hv.1] at hre
    have hu : u.mult = 1 := by simp [InfinitePlace.mult, hre]
    rw [hu]
    ring

/-- **Averages of functions of the place below, at `∞`**: `∑_v ([K_v : ℝ]/[K : ℚ])·c(v|_k) =
`∑_u ([k_u : ℝ]/[k : ℚ])·c(u)`. -/
theorem sum_infPlaceWeight_comap (c : InfinitePlace k → ℝ) :
    ∑ v : InfinitePlace K, infPlaceWeight K v * c (v.comap (algebraMap k K)) =
      ∑ u : InfinitePlace k, infPlaceWeight k u * c u := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun v : InfinitePlace K => v.comap (algebraMap k K))]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hS : ∀ v ∈ Finset.univ.filter (fun v : InfinitePlace K => v.comap (algebraMap k K) = u),
      infPlaceWeight K v * c (v.comap (algebraMap k K)) =
        (v.mult : ℝ) * (c u / Module.finrank ℚ K) := by
    intro v hv
    rw [(Finset.mem_filter.mp hv).2, infPlaceWeight]
    ring
  rw [Finset.sum_congr rfl hS, ← Finset.sum_mul, ← Nat.cast_sum, sum_mult_comap_eq,
    infPlaceWeight, ← Module.finrank_mul_finrank ℚ k K]
  have hk : (Module.finrank k K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hk' : (Module.finrank ℚ k : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  push_cast
  field_simp

end ArchFiber

lemma LocalTheory.weight_infinite_eq {k : Type u} [Field k] [NumberField k]
    (v : LocalTheory.Fiber k .infinite) :
    LocalTheory.weight k .infinite v = infPlaceWeight k (LocalTheory.fiberInfPlace k v) := by
  unfold LocalTheory.weight
  rw [LocalTheory.fiberInfPlace_spec k v]
  rfl

variable (D : InitialThetaData.{u})

/-- The archimedean section `V_mod^arc → V(K)` lies over the identity. -/
lemma comap_placeSect_inf (u : InfinitePlace D.Fmod) :
    (D.placeSect.inf u).comap (algebraMap D.Fmod D.Kt) = u := by
  haveI := D.V.sectInf_liesOver u
  exact InfinitePlace.LiesOver.comap_eq (D.V.sectInf u) u

/-! ### Scaling data with archimedean metrics -/

/-- **An idelic scaling datum with archimedean metrics**: a `ScalingDatum` `b` at the finite
places and positive reals `r_v` at the infinite places of `K`. -/
structure FullScalingDatum extends ScalingDatum D where
  /-- The archimedean metrics `r_v > 0`. -/
  rad : InfinitePlace D.Kt → ℝ
  rad_pos : ∀ v, 0 < rad v

namespace FullScalingDatum

variable {D} (b : FullScalingDatum D)

/-- **The arithmetic line bundle** with idelic description `b` and metrics `r_v`. -/
noncomputable def toBundle : ArithLineBundle D.Kt where
  fin := b.elt
  fin_ne_zero := b.elt_ne_zero
  finite_fin := b.toScalingDatum.toBundle.finite_fin
  inf := b.rad
  inf_pos := b.rad_pos

/-- A finite scaling datum with trivial archimedean metrics. -/
noncomputable def ofScaling (b : ScalingDatum D) : FullScalingDatum D where
  toScalingDatum := b
  rad _ := 1
  rad_pos _ := one_pos

lemma toBundle_ofScaling (b : ScalingDatum D) : (ofScaling b).toBundle = b.toBundle := rfl

/-- **Archimedean `F_mod`-rationality**: `r_v` depends only on the place of `F_mod` below `v`. -/
def IsArchModInvariant : Prop :=
  ∀ v v' : InfinitePlace D.Kt, v.comap (algebraMap D.Fmod D.Kt) =
    v'.comap (algebraMap D.Fmod D.Kt) → b.rad v = b.rad v'

/-- **`F_mod`-rationality** at the finite and the archimedean places. -/
def IsModInvariant : Prop := b.toScalingDatum.IsModInvariant ∧ b.IsArchModInvariant

/-- The archimedean section-average degree:
`−Σ_{u ∈ V_mod^arc} ([(F_mod)_u : ℝ]/[F_mod : ℚ])·log r_{v(u)}`. -/
noncomputable def archSectDeg : ℝ :=
  -∑ u : LocalTheory.Fiber D.Fmod .infinite, LocalTheory.weight D.Fmod _ u *
    Real.log (b.rad (D.placeSect.inf (LocalTheory.fiberInfPlace D.Fmod u)))

/-- The full section-average degree `sectDeg + archSectDeg`. -/
noncomputable def fullSectDeg : ℝ := b.sectDeg + b.archSectDeg

/-- The archimedean part of the normalized degree is the archimedean section average. -/
lemma sum_infDeg_eq_archSectDeg (h : b.IsArchModInvariant) :
    ∑ v, -(infPlaceWeight D.Kt v * Real.log (b.toBundle.inf v)) = b.archSectDeg := by
  set g : InfinitePlace D.Fmod → ℝ := fun u => Real.log (b.rad (D.placeSect.inf u)) with hg
  have h1 : ∀ v : InfinitePlace D.Kt, Real.log (b.toBundle.inf v) =
      g (v.comap (algebraMap D.Fmod D.Kt)) := by
    intro v
    rw [hg]
    change Real.log (b.rad v) = _
    rw [h v (D.placeSect.inf (v.comap (algebraMap D.Fmod D.Kt)))
      (comap_placeSect_inf D _).symm]
  simp only [h1]
  rw [Finset.sum_neg_distrib, sum_infPlaceWeight_comap (k := D.Fmod) g, archSectDeg]
  congr 1
  refine (Fintype.sum_equiv (LocalTheory.fiberInfiniteEquiv D.Fmod)
    (fun u => LocalTheory.weight D.Fmod _ u *
      Real.log (b.rad (D.placeSect.inf (LocalTheory.fiberInfPlace D.Fmod u))))
    (fun u => infPlaceWeight D.Fmod u * g u) fun u => ?_).symm
  rw [LocalTheory.weight_infinite_eq]
  rfl

/-- **The full section-average degree is the normalized Arakelov degree** (for `F_mod`-rational
data): `fullSectDeg b = deg(L_b)/[K : ℚ]`, archimedean metrics included. -/
theorem degNorm_toBundle (h : b.IsModInvariant) : b.toBundle.degNorm = b.fullSectDeg := by
  have h1 := b.toScalingDatum.degNorm_toBundle h.1
  rw [ArithLineBundle.degNorm_eq] at h1 ⊢
  have hinf0 : ∑ v, -(infPlaceWeight D.Kt v *
      Real.log (b.toScalingDatum.toBundle.inf v)) = 0 := by
    simp [ScalingDatum.toBundle]
  rw [hinf0, add_zero] at h1
  rw [fullSectDeg, ← h1, b.sum_infDeg_eq_archSectDeg h.2]
  rfl

/-- The product of two full scaling data. -/
noncomputable def mul (b c : FullScalingDatum D) : FullScalingDatum D where
  elt w := b.elt w * c.elt w
  elt_ne_zero w := mul_ne_zero (b.elt_ne_zero w) (c.elt_ne_zero w)
  chars := b.chars ∪ c.chars
  elt_eq_one w hw := by
    rw [Finset.mem_union, not_or] at hw
    rw [b.elt_eq_one w hw.1, c.elt_eq_one w hw.2, mul_one]
  rad v := b.rad v * c.rad v
  rad_pos v := mul_pos (b.rad_pos v) (c.rad_pos v)

lemma toBundle_mul (b c : FullScalingDatum D) :
    (b.mul c).toBundle = b.toBundle.mul c.toBundle := rfl

lemma isModInvariant_mul {b c : FullScalingDatum D} (hb : b.IsModInvariant)
    (hc : c.IsModInvariant) : (b.mul c).IsModInvariant := by
  refine ⟨fun v v' hvv' => ?_, fun v v' hvv' => ?_⟩
  · change ordp D.Kt v (b.elt v * c.elt v) = ordp D.Kt v' (b.elt v' * c.elt v')
    rw [LocalConstruct.ordp_mul _ _ _ (b.elt_ne_zero v) (c.elt_ne_zero v),
      LocalConstruct.ordp_mul _ _ _ (b.elt_ne_zero v') (c.elt_ne_zero v'), hb.1 v v' hvv',
      hc.1 v v' hvv']
  · change b.rad v * c.rad v = b.rad v' * c.rad v'
    rw [hb.2 v v' hvv', hc.2 v v' hvv']

/-! ### The diagonal image of `F_mod^×` -/

/-- The residue characteristics of the finite places of `K` where `|x|_w ≠ 1`. -/
noncomputable def diagChars (x : D.Fmod) (hx : x ≠ 0) : Finset ℕ :=
  (FinitePlace.hasFiniteMulSupport
    ((map_ne_zero (algebraMap D.Fmod D.Kt)).mpr hx)).toFinset.image residueChar

open scoped Classical in
/-- **The diagonal image of `x ∈ F_mod^×`**: `x ∈ K_w` at the finite places over `diagChars`
(the components at the other finite places are units, replaced by `1`), and `|x|_v` at the
archimedean places. -/
noncomputable def diag (x : D.Fmod) (hx : x ≠ 0) : FullScalingDatum D where
  elt w := if residueChar w ∈ diagChars x hx then
    FinitePlace.embedding w.maximalIdeal (algebraMap D.Fmod D.Kt x) else 1
  elt_ne_zero w := by
    split_ifs
    · exact (map_ne_zero _).mpr ((map_ne_zero _).mpr hx)
    · exact one_ne_zero
  chars := diagChars x hx
  elt_eq_one w hw := if_neg hw
  rad v := v (algebraMap D.Fmod D.Kt x)
  rad_pos _ := InfinitePlace.pos_iff.mpr ((map_ne_zero _).mpr hx)

lemma norm_diag_elt (x : D.Fmod) (hx : x ≠ 0) (w : FinitePlace D.Kt) :
    ‖(diag x hx).elt w‖ =
      ‖FinitePlace.embedding w.maximalIdeal (algebraMap D.Fmod D.Kt x)‖ := by
  classical
  change ‖if residueChar w ∈ diagChars x hx then _ else _‖ = _
  split_ifs with h
  · rfl
  · rw [norm_one, FinitePlace.norm_embedding_eq]
    by_contra hne
    apply h
    refine Finset.mem_image.mpr ⟨w, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport]
    exact fun h' => hne h'.symm

/-- **The product formula for the diagonal image**: `deg(L_{diag x}) = deg(principal x) = 0`. -/
theorem deg_toBundle_diag (x : D.Fmod) (hx : x ≠ 0) : (diag x hx).toBundle.deg = 0 := by
  have hxK : algebraMap D.Fmod D.Kt x ≠ 0 := (map_ne_zero _).mpr hx
  rw [← ArithLineBundle.deg_principal _ hxK]
  exact ArithLineBundle.deg_congr _ _ (fun w => norm_diag_elt x hx w) fun _ => rfl

theorem degNorm_toBundle_diag (x : D.Fmod) (hx : x ≠ 0) : (diag x hx).toBundle.degNorm = 0 := by
  rw [ArithLineBundle.degNorm, deg_toBundle_diag, zero_div]

/-- `ord_p` of the image of `x ∈ F_mod` at `v` is `ord_p(x)` at the place of `F_mod` below. -/
lemma ordp_algebraMap_placeUnder (x : D.Fmod) (v : FinitePlace D.Kt) :
    ordp D.Kt v (FinitePlace.embedding v.maximalIdeal (algebraMap D.Fmod D.Kt x)) =
      ordp D.Fmod (placeUnder v)
        (FinitePlace.embedding (placeUnder (k := D.Fmod) v).maximalIdeal x) := by
  rw [← embedCompletion_embedding (liesOver_placeUnder v), ordp_embedCompletion]

/-- **The diagonal image is `F_mod`-rational.** -/
theorem isModInvariant_diag (x : D.Fmod) (hx : x ≠ 0) : (diag x hx).IsModInvariant := by
  classical
  refine ⟨fun v v' hvv' => ?_, fun v v' hvv' => ?_⟩
  · have hres : residueChar v = residueChar v' := by
      rw [residueChar_eq_of_liesOver (liesOver_placeUnder (k := D.Fmod) v),
        residueChar_eq_of_liesOver (liesOver_placeUnder (k := D.Fmod) v'), hvv']
    change ordp D.Kt v (if residueChar v ∈ diagChars x hx then _ else _) =
      ordp D.Kt v' (if residueChar v' ∈ diagChars x hx then _ else _)
    rw [hres]
    split_ifs
    · rw [ordp_algebraMap_placeUnder, ordp_algebraMap_placeUnder, hvv']
    · simp [ordp]
  · change v (algebraMap D.Fmod D.Kt x) = v' (algebraMap D.Fmod D.Kt x)
    rw [← InfinitePlace.comap_apply, ← InfinitePlace.comap_apply, hvv']

end FullScalingDatum

/-! ### The regions -/

variable (a : Fin (nC D) → FullScalingDatum D) (lab : ∀ i, InitialThetaData.Lab (nC D) i)

/-- The real number `r_v`, `r = (a i).rad`, `v = c(lab i)`, in the archimedean packet. -/
noncomputable def archScaleElt (i : Fin (nC D))
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod .infinite) :
    LocalTheory.Tensor D.Kt .infinite (LocalTheory.tuple D.placeSect _ c) :=
  algebraMap ℝ _ ((a i).rad (D.placeSect.inf (LocalTheory.fiberInfPlace D.Fmod (c (lab i)))))

lemma isUnit_archScaleElt (i : Fin (nC D))
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod .infinite) :
    IsUnit (archScaleElt D a lab i c) :=
  (isUnit_iff_ne_zero.mpr ((a i).rad_pos _).ne').map _

/-- Multiplication by `archScaleElt`. -/
noncomputable def archScaleMap (i : Fin (nC D)) :
    (LocalTheory.packet D.placeSect (InitialThetaData.Lab (nC D) i) .infinite).Total →
      (LocalTheory.packet D.placeSect (InitialThetaData.Lab (nC D) i) .infinite).Total :=
  fun x c => @HMul.hMul (LocalTheory.Tensor D.Kt .infinite (LocalTheory.tuple D.placeSect _ c))
    (LocalTheory.Tensor D.Kt .infinite (LocalTheory.tuple D.placeSect _ c))
    (LocalTheory.Tensor D.Kt .infinite (LocalTheory.tuple D.placeSect _ c)) instHMul
    (archScaleElt D a lab i c) (x c)

/-- The packet regions of `archScaleAt`: the archimedean packet scaled by the metrics. -/
noncomputable def archScaleRegion (i : Fin (VC D).proc.length) (R : (VC D).AdmissibleRegion i) :
    ∀ vQ : RationalPlace, Set ((VC D).packet i vQ).Total
  | .finite p => R.region (.finite p)
  | .infinite => archScaleMap D a lab i '' R.region .infinite

/-- The archimedean scaling of an admissible region at capsule `i`. -/
noncomputable def archScaleAt (i : Fin (VC D).proc.length) (R : (VC D).AdmissibleRegion i) :
    (VC D).AdmissibleRegion i where
  region := archScaleRegion D a lab i R
  finiteSupport := by
    refine (R.finiteSupport.union (Set.finite_singleton RationalPlace.infinite)).subset
      fun vQ hvQ => ?_
    rcases vQ with p | _
    · exact Or.inl hvQ
    · exact Or.inr rfl

/-- **The region `S` scaled by the full idelic data `a i`**: for `S = O`, the region
`((b_v·𝒪_v)_{v ∤ ∞}, (r_v·B_v)_{v ∣ ∞})` of IUT III, Proposition 3.9(iii), in each capsule. -/
noncomputable def fullScale (S : Region D) : Region D := fun i =>
  archScaleAt D a lab i (scale D (fun i => (a i).toScalingDatum) lab S i)

lemma proj_fullScale_infinite (S : Region D) (i : Fin (nC D))
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod .infinite) :
    LocalTheory.proj D.placeSect .infinite c ((fullScale D a lab S i).region .infinite) =
      archScaleElt D a lab i c • LocalTheory.proj D.placeSect .infinite c
        ((S i).region .infinite) := by
  change (fun x => x c) '' (archScaleMap D a lab i '' (S i).region .infinite) = _
  rw [Set.image_image]
  unfold LocalTheory.proj
  rw [← Set.image_smul, Set.image_image]
  rfl

/-- `fullScale D a lab S` is adelic for adelic `S`. -/
theorem isAdelic_fullScale {S : Region D} (hS : IsAdelic D S) :
    IsAdelic D (fullScale D a lab S) := by
  have h := isAdelic_scale D (fun i => (a i).toScalingDatum) lab hS
  intro i vQ
  rcases vQ with p | _
  · exact h i (.finite p)
  · obtain ⟨fam, hfam, hR⟩ := h i .infinite
    refine ⟨fun c => archScaleElt D a lab i c • fam c, fun c => ?_, ?_⟩
    · change algebraMap ℝ _ _ • fam c ∈ _
      rw [LocalConstruct.algebraMap_smul_set]
      exact LocalConstruct.smul_mem_admissible_infinite (hfam c) ((a i).rad_pos _)
    change archScaleMap D a lab i ''
      (scale D (fun i => (a i).toScalingDatum) lab S i).region .infinite = _
    rw [hR]
    ext x
    simp only [DirectSumPresentation.mem_productRegion, Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩ c
      exact ⟨y c, hy c, rfl⟩
    · intro hx
      choose y hy hxy using hx
      exact ⟨y, hy, funext hxy⟩

/-! ### The log-volume of `fullScale D a lab O` -/

/-- At a prime the packet log-volume is that of `scale`: `−sectDegAt (a i) p`. -/
theorem packetVol_fullScale_integral_finite (i : Fin (nC D)) (p : Nat.Primes) :
    (LocalTheory.vol D.placeSect (nC D)).packetVol i (.finite p)
        ((fullScale D a lab (integralRegion D) i).region (.finite p)) =
      -(a i).sectDegAt p :=
  packetVol_scale_integral_finite D (fun i => (a i).toScalingDatum) lab i p

/-- **The archimedean packet log-volume of `fullScale D a lab O`** is `−archSectDeg (a i)`
(`μ^log(r·B_I) = log r`, `LocalTheory.componentVol_arch_scale`). -/
theorem packetVol_fullScale_integral_infinite (i : Fin (nC D)) :
    (LocalTheory.vol D.placeSect (nC D)).packetVol i .infinite
        ((fullScale D a lab (integralRegion D) i).region .infinite) = -(a i).archSectDeg := by
  rw [LocalTheory.packetVol_eq]
  have hpO : ∀ c, LocalTheory.proj D.placeSect .infinite c
      ((integralRegion D i).region .infinite) =
      LocalTheory.integral D.Kt .infinite (LocalTheory.tuple D.placeSect _ c) := fun c =>
    LocalTheory.proj_productRegion D.placeSect _ _
      (fun c => ⟨1, LocalTheory.one_mem_integral D.Kt _ _⟩) c
  have hc : ∀ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod .infinite,
      LocalTheory.componentVol D.Kt .infinite (LocalTheory.tuple D.placeSect _ c)
        (LocalTheory.proj D.placeSect .infinite c
          ((fullScale D a lab (integralRegion D) i).region .infinite)) =
      Real.log ((a i).rad (D.placeSect.inf (LocalTheory.fiberInfPlace D.Fmod (c (lab i))))) := by
    intro c
    rw [proj_fullScale_infinite, hpO]
    exact LocalTheory.componentVol_arch_scale D.Kt _ _ ((a i).rad_pos _)
  simp only [hc]
  have key := sum_prod_tuple_mul_coord (LocalTheory.weight D.Fmod .infinite)
    (LocalTheory.weight_sum_one D.Fmod _)
    (fun u => Real.log ((a i).rad (D.placeSect.inf (LocalTheory.fiberInfPlace D.Fmod u))))
    (lab i)
  unfold LocalTheory.tupleWeight
  rw [key, FullScalingDatum.archSectDeg, neg_neg]

/-- **The global log-volume of `fullScale D a lab O` at capsule `i`** is `−fullSectDeg (a i)`. -/
theorem globalVol_fullScale_integral (i : Fin (nC D)) :
    (LocalTheory.vol D.placeSect (nC D)).globalVol (fullScale D a lab (integralRegion D) i) =
      -(a i).fullSectDeg := by
  classical
  unfold LogVolumeData.globalVol
  set g := fun vQ => (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ
    ((fullScale D a lab (integralRegion D) i).region vQ) with hg
  have hsupp : Function.support g ⊆
      ↑(insert RationalPlace.infinite ((a i).primes.image RationalPlace.finite)) := by
    intro vQ hvQ
    rcases vQ with p | _
    · by_contra h
      apply hvQ
      change (LocalTheory.vol D.placeSect (nC D)).packetVol i (.finite p) _ = 0
      rw [packetVol_fullScale_integral_finite, (a i).sectDegAt_eq_zero p
        (fun hp => h (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ hp)))), neg_zero]
    · exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
  rw [finsum_eq_sum_of_support_subset g hsupp, Finset.sum_insert (by simp),
    Finset.sum_image (fun p _ q _ h => RationalPlace.finite.inj h)]
  have h1 : g .infinite = -(a i).archSectDeg := packetVol_fullScale_integral_infinite D a lab i
  have h2 : ∀ p ∈ (a i).primes, g (.finite p) = -(a i).sectDegAt p := fun p _ =>
    packetVol_fullScale_integral_finite D a lab i p
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_neg_distrib, FullScalingDatum.fullSectDeg,
    ScalingDatum.sectDeg]
  ring

/-- **The procession-normalized log-volume of `fullScale D a lab O`** is the average over the
capsules of `−fullSectDeg (a i)`. -/
theorem logVol_fullScale_integral :
    logVol D (fullScale D a lab (integralRegion D)) = -(∑ i, (a i).fullSectDeg) / nC D := by
  unfold logVol LogVolumeData.processionVol
  simp only [globalVol_fullScale_integral]
  rw [Finset.sum_neg_distrib]
  rfl

/-- **IUT III, Proposition 3.9(iii) with archimedean part**: the log-volume of the region
`((b_v·𝒪_v), (r_v·B_v))` is the capsule average of `−deg(L_{a i})/[K : ℚ]`. -/
theorem logVol_fullScale_integral_eq_degNorm (h : ∀ i, (a i).IsModInvariant) :
    logVol D (fullScale D a lab (integralRegion D)) =
      -(∑ i, (a i).toBundle.degNorm) / nC D := by
  rw [logVol_fullScale_integral]
  simp only [fun i => (a i).degNorm_toBundle (h i)]

/-- **`log-vol((b_v·𝒪_v), (r_v·B_v)) = −deg(L)/[K : ℚ]`**: the same datum in every capsule. -/
theorem logVol_fullScaleConst_eq_neg_degNorm (b : FullScalingDatum D) (hb : b.IsModInvariant) :
    logVol D (fullScale D (fun _ => b) lab (integralRegion D)) = -b.toBundle.degNorm := by
  rw [logVol_fullScale_integral_eq_degNorm D _ lab fun _ => hb]
  have hn : (nC D : ℝ) ≠ 0 := by exact_mod_cast (nC_pos D).ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-! ### The product formula on regions -/

/-- **IUT III, Proposition 3.9(iii), invariance under the global multiplicative monoid**: for
`F_mod`-rational data `a` and `x ∈ F_mod^×`, scaling each capsule further by the diagonal image of
`x` (finite and archimedean) does not change the log-volume (the product formula). -/
theorem logVol_fullScale_mul_diag (h : ∀ i, (a i).IsModInvariant) (x : D.Fmod) (hx : x ≠ 0) :
    logVol D (fullScale D (fun i => (a i).mul (FullScalingDatum.diag x hx)) lab
        (integralRegion D)) =
      logVol D (fullScale D a lab (integralRegion D)) := by
  rw [logVol_fullScale_integral_eq_degNorm D _ lab fun i =>
      FullScalingDatum.isModInvariant_mul (h i) (FullScalingDatum.isModInvariant_diag x hx),
    logVol_fullScale_integral_eq_degNorm D a lab h]
  simp only [FullScalingDatum.toBundle_mul, ArithLineBundle.degNorm_mul,
    FullScalingDatum.degNorm_toBundle_diag, add_zero]

/-- **`log-vol(x·O) = log-vol(O) = 0`** for `x ∈ F_mod^×` (the product formula on regions). -/
theorem logVol_fullScale_diag (x : D.Fmod) (hx : x ≠ 0) :
    logVol D (fullScale D (fun _ => FullScalingDatum.diag x hx) lab (integralRegion D)) =
      logVol D (integralRegion D) := by
  rw [logVol_fullScaleConst_eq_neg_degNorm D lab _ (FullScalingDatum.isModInvariant_diag x hx),
    FullScalingDatum.degNorm_toBundle_diag, neg_zero, logVol_integralRegion]

end Arakelov

end Iut
