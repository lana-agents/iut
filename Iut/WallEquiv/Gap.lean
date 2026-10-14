/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.WallEquiv.Forms

/-!
# The gap between (Var) and (SS)

Christian's question: *is the LANA wall any weaker than the Scholze–Stix wall?* For initial
Θ-data `D` the two walls are the inequalities

* **(Var)** `−|log(q)| ≤ −|log(Θ)| = R := log-vol(hull(Θ-pilot region))` (`rhs_eq_logVol`,
  `rhs_eq_logVol_image`), the Corollary 3.12 variant, equivalently (9-1) for *some* η-algorithm;
* **(SS)** `−|log(q)| ≤ log-vol(LGP·hull(VC(I)))` (`ss_iff_lgp_vcI`), the Scholze–Stix
  inequality with IUT's container `hull(VC(I))`;
* (no-hull) `−|log(q)| ≤ log-vol(LGP·VC(I))` (`ssNoHull_iff_lgp_vcI`), the no-hull wall
  `SSIneqNoHull`, which implies (SS).

## Results: the gap `Δ(D)` between (Var) and (SS)

* `logVol_lgp_vcI_le_rhs : log-vol(LGP·hull(VC(I))) ≤ R`;
  **`gap D := R − log-vol(LGP·hull(VC(I)))`**, `gap_nonneg`, `gap_eq_rhs_add`;
  `ss_iff_le_rhs_sub_gap : SSIneq D ↔ −|log q| ≤ R − gap D`,
  `variant_iff_le_rhs : (Var) ↔ −|log q| ≤ R`, `variant_of_ss_gap`,
  `ss_iff_variant_of_gap_eq_zero`, and `variant_and_not_ss_iff`: (Var) holds and (SS) fails iff
  `−|log q| ∈ (R − gap D, R]`.
* **Local formula** (`gap_eq`): `gap D = (1/ℓ*)·∑_i ∑ᶠ_{v_ℚ} gapHullAt D i v_ℚ`, where
  `gapHullAt` is `∑_c w_c·ind2Term` at a prime and `0` at `∞` (`gapHullAt_eq`): with the hull on
  both sides only the enlargement of the hull by the (Ind2)-union of the images of
  `q^{j²}·⊗𝓘` remains (`ind2Term_nonneg`). It vanishes away from the bad residue characteristics
  (`gapHullAt_eq_zero`), and if it vanishes there too, (SS) is (Var)
  (`gap_eq_zero_of_ind2Term`, `ss_iff_variant_of_ind2Term`). **Open**: whether the (Ind2)-terms
  at the bad primes are `0` or `> 0` (the indeterminacy automorphisms at a prime are all
  `ℤ_p`-lattice automorphisms of the factor log-shells, `tensorAut`, which need not commute
  with the theta values); so the sign `Δ(D) ≥ 0` is all that is proved.

## The no-hull gap `Δ_noHull(D)`

* `gapNoHull D := R − log-vol(LGP·VC(I))`; `gapNoHull_eq_gap_add`:
  `Δ_noHull(D) = Δ(D) + (log-vol(hull(VC(I))) − log-vol(VC(I)))`, `gap_le_gapNoHull`,
  `ssNoHull_iff_le_rhs_sub_gapNoHull`.
* **Local formula** (`gapNoHull_eq`): `gapNoHull D = (1/ℓ*)·∑_i ∑ᶠ_{v_ℚ} ∑_c w_c·δ_{i,v_ℚ,c}`
  with `δ = μ^log(hull(Θ_{i,v_ℚ,c})) − μ^log((LGP·VC(I))_{i,v_ℚ,c}) ≥ 0` (`gapTerm`,
  `gapTerm_nonneg`), where `hull` is the least region `a·O` containing a component
  (`LocalTheory.leastHull`; the packet hull is componentwise this, `proj_hull_productRegion`).
  - at `∞`: the theta-pilot component *is* the log-shell (`thetaComponent_infinite`: the
    indeterminacies change nothing) and `δ = archDefect`, the defect of the log-shell (a
    Euclidean ball) against its least polydisc `a·B_I` (`gapTerm_infinite`);
  - at a prime: `δ = shellDefect + ind2Term` (`gapTerm_finite`): the defect of the tensor product
    of the log-shells against its hull (independent of theta values and indeterminacies), plus
    the (Ind2)-term, which vanishes away from the bad residue characteristics
    (`ind2Term_eq_zero`); the shell defect vanishes at odd primes unramified in `K`
    (`shellDefect_eq_zero`). So `δ = 0` at odd unramified primes that are not bad
    (`gapTerm_eq_zero`), and `gapAt D i` is supported on `∞`, `2`, the bad residue
    characteristics and the ramified primes (`support_gapAt_subset`).
* **Strictness** (`gapNoHull_pos : 0 < gapNoHull D` for every `D`): `K` is totally complex since
  `√−1 ∈ F` (`InitialThetaData.isComplex_Kt`), every capsule has at least two labels, so every
  archimedean packet is a product of at least two copies of `ℂ` (`exists_ne_maximalSpectrum`),
  and there the log-shell ball is strictly smaller than its least polydisc
  (`componentVol_archLogShell_lt_leastHull`): `δ_∞ > 0` for every tuple (`gapTerm_infinite_pos`).
  `archPart_le_gapNoHull` bounds `gapNoHull D` below by its archimedean part;
  `ssNoHull_imp_lt_rhs`. The shell and archimedean defects are exactly what the hull removes.

The value of `archDefect` (by the orthogonality of the components for the tensor-product metric,
`log((2^{N−1})!)/2^N` for a packet of `N` complex factors) and the sign of the shell defect at `2`
and at ramified primes are not formalized here; only `≥ 0` is proved for the finite terms.
-/

namespace Iut

open NumberField MeasureTheory
open scoped Pointwise

universe u

namespace LocalTheory

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]

/-! ### The least hull `a·O` of a component region -/

/-- **The least hull region of a component region** `U` of a packet: the intersection of all
regions `b·O` (`b` a unit) containing `U`. For admissible `U` it is the least such region
(`leastHull_eq`, `exists_leastHull_eq`; IUT III, Remark 3.9.5(i)). -/
def leastHull (vQ : RationalPlace) (c : ι → Place K) (U : Set (Tensor K vQ c)) :
    Set (Tensor K vQ c) :=
  ⋂ (b : Tensor K vQ c) (_ : IsUnit b) (_ : U ⊆ b • integral K vQ c), b • integral K vQ c

variable {vQ : RationalPlace} {c : ι → Place K} {U : Set (Tensor K vQ c)}

lemma leastHull_subset {b : Tensor K vQ c} (hb : IsUnit b) (h : U ⊆ b • integral K vQ c) :
    leastHull vQ c U ⊆ b • integral K vQ c :=
  fun _ hx => Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hx b) hb) h

lemma leastHull_eq {a : Tensor K vQ c} (ha : IsUnit a) (hU : U ⊆ a • integral K vQ c)
    (hl : ∀ b : Tensor K vQ c, IsUnit b → U ⊆ b • integral K vQ c →
      a • integral K vQ c ⊆ b • integral K vQ c) :
    leastHull vQ c U = a • integral K vQ c :=
  Set.Subset.antisymm (leastHull_subset ha hU) fun _ hx =>
    Set.mem_iInter.mpr fun b => Set.mem_iInter.mpr fun hb => Set.mem_iInter.mpr fun h =>
      hl b hb h hx

/-- **The least hull of an admissible region is a region `a·O`** (`exists_leastHull`,
`exists_leastHull_infinite`). -/
lemma exists_leastHull_eq (hU : U ∈ admissible K vQ c) :
    ∃ a : Tensor K vQ c, IsUnit a ∧ U ⊆ a • integral K vQ c ∧
      leastHull vQ c U = a • integral K vQ c := by
  cases vQ with
  | finite p =>
    obtain ⟨a, ha, hU', hl⟩ := exists_leastHull K p c U hU
    exact ⟨a, ha, hU', leastHull_eq ha hU' hl⟩
  | infinite =>
    obtain ⟨a, ha, hU', hl⟩ := exists_leastHull_infinite K c U hU
    exact ⟨a, ha, hU', leastHull_eq ha hU' hl⟩

lemma subset_leastHull (hU : U ∈ admissible K vQ c) : U ⊆ leastHull vQ c U := by
  obtain ⟨a, -, hU', h⟩ := exists_leastHull_eq hU
  rw [h]
  exact hU'

lemma leastHull_admissible (hU : U ∈ admissible K vQ c) :
    leastHull vQ c U ∈ admissible K vQ c := by
  obtain ⟨a, ha, -, h⟩ := exists_leastHull_eq hU
  rw [h]
  exact smul_integral_admissible K vQ c a ha

/-- `μ^log(X) ≤ μ^log(hull U)` for an admissible `X ⊆ U`. -/
lemma componentVol_le_leastHull {X : Set (Tensor K vQ c)} (hX : X ∈ admissible K vQ c)
    (hXU : X ⊆ U) (hU : U ∈ admissible K vQ c) :
    componentVol K vQ c X ≤ componentVol K vQ c (leastHull vQ c U) :=
  LocalConstruct.componentVol_le_of_subset (hXU.trans (subset_leastHull hU))
    (LocalConstruct.admissible_haar_pos hX)
    (LocalConstruct.admissible_haar_lt_top (leastHull_admissible hU))

/-- The least hull of a hull region `a·O` is itself. -/
lemma leastHull_smul_integral {a : Tensor K vQ c} (ha : IsUnit a) :
    leastHull vQ c (a • integral K vQ c) = a • integral K vQ c :=
  leastHull_eq ha subset_rfl fun _ _ h => h

/-- `μ^log(hull U) − μ^log(U) ≥ 0` for admissible `U`. -/
lemma componentVol_le_leastHull_self (hU : U ∈ admissible K vQ c) :
    componentVol K vQ c U ≤ componentVol K vQ c (leastHull vQ c U) :=
  componentVol_le_leastHull hU subset_rfl hU

/-- **Scaling by a unit commutes with the least hull**: `hull(s·U) = s·hull(U)`. -/
lemma leastHull_units_smul {s : Tensor K vQ c} (hs : IsUnit s) (hU : U ∈ admissible K vQ c) :
    leastHull vQ c (s • U) = s • leastHull vQ c U := by
  obtain ⟨a, ha, hU', h⟩ := exists_leastHull_eq hU
  rw [h, smul_smul]
  refine leastHull_eq (hs.mul ha) ?_ fun b hb hsb => ?_
  · rw [← smul_smul]
    exact Set.smul_set_mono hU'
  · obtain ⟨u, rfl⟩ := hs
    have h1 : U ⊆ (↑u⁻¹ * b) • integral K vQ c := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hsb ⟨x, hx, rfl⟩
      refine ⟨y, hy, ?_⟩
      change (↑u⁻¹ * b) * y = x
      change b * y = ↑u * x at hxy
      rw [mul_assoc, hxy, ← mul_assoc, Units.inv_mul, one_mul]
    have h2 := leastHull_subset ((Units.isUnit u⁻¹).mul hb) h1
    rw [h] at h2
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := h2 ⟨z, hz, rfl⟩
    refine ⟨w, hw, ?_⟩
    change b * w = (↑u * a) * z
    change (↑u⁻¹ * b) * w = a * z at hwz
    rw [mul_assoc, hwz.symm, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]

end LocalTheory


namespace LocalTheory

variable {K : Type u} [Field K] [NumberField K] {k : Type u} [Field k] [NumberField k]
  (σ : PlaceSection K k) (n : ℕ)

lemma mem_hullRegions_iff (ι : Type) [Fintype ι] (vQ : RationalPlace)
    (R : Set (packet σ ι vQ).Total) : R ∈ hullRegions σ ι vQ ↔ (packet σ ι vQ).IsHullRegion R := by
  cases vQ <;> rfl

/-- **The components of the packet hull are the least hulls of the components**: the
holomorphic hull of a product region with admissible components is the product of the least
regions `a_c·O` containing the components. -/
theorem proj_hull_productRegion (i : Fin (container σ n).proc.length) (vQ : RationalPlace)
    (fam : ∀ c : ((Procession.standard n).capsule i).LabelType → Fiber k vQ,
      Set (Tensor K vQ (tuple σ vQ c)))
    (hfam : ∀ c, fam c ∈ admissible K vQ (tuple σ vQ c))
    (c : ((Procession.standard n).capsule i).LabelType → Fiber k vQ) :
    proj σ vQ c (((hull σ n).system i vQ).hull ((packet σ _ vQ).productRegion fam)) =
      leastHull vQ (tuple σ vQ c) (fam c) := by
  choose a ha hsub heq using fun c => exists_leastHull_eq (hfam c)
  have hR : (packet σ _ vQ).IsLeastHullRegionIn (hullRegions σ _ vQ)
      ((packet σ _ vQ).productRegion fam) ((packet σ _ vQ).scaledIntegral a) := by
    refine ⟨(mem_hullRegions_iff σ _ vQ _).mpr ⟨a, ha, rfl⟩, fun x hx c => hsub c (hx c), ?_⟩
    intro R' hR' hUR'
    obtain ⟨b, hb, rfl⟩ := (mem_hullRegions_iff σ _ vQ _).mp hR'
    intro x hx c
    have hproj : fam c ⊆
        (show Tensor K vQ (tuple σ vQ c) from b c) • integral K vQ (tuple σ vQ c) := by
      have := proj_productRegion σ _ fam (fun c => admissible_nonempty K _ _ _ (hfam c)) c
      rw [← this]
      rintro y ⟨z, hz, rfl⟩
      exact hUR' hz c
    have h := leastHull_subset (show IsUnit (show Tensor K vQ (tuple σ vQ c) from b c) from hb c)
      hproj
    rw [heq c] at h
    exact h (hx c)
  have hH := (((hull σ n).system i vQ).isLeastHullRegion_hull _ ⟨fam, hfam, rfl⟩).unique hR
  rw [hH, heq c]
  exact proj_productRegion σ vQ (fun c => a c • integral K vQ (tuple σ vQ c))
    (fun c => ⟨a c • 1, Set.smul_mem_smul_set (one_mem_integral K vQ _)⟩) c

end LocalTheory

namespace LocalConstruct

open LocalTheory

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι] (c : ι → Place K)

/-! ### At `∞`: the log-shell is strictly smaller than its hull -/

/-- The archimedean log-shell is admissible. -/
lemma archLogShell_admissible : archLogShell c ∈ admissible .infinite c :=
  ⟨nonempty_of_measure_ne_zero (haar_archLogShell_pos c).ne',
    isCompact_closure_archLogShell c, (isClosed_archLogShell c).measurableSet,
    haar_archLogShell_pos c, (isCompact_archLogShell c).measure_lt_top⟩

lemma archTensorCoord_injective : Function.Injective (archTensorCoord c) := fun _ _ h =>
  (archTensorBasis c).equivFun.injective ((WithLp.linearEquiv 2 ℝ _).symm.injective h)

lemma norm_archTensorCoord_le_of_mem {x : Tensor K .infinite c} (hx : x ∈ archLogShell c) :
    ‖archTensorCoord c x‖ ≤ Real.pi ^ Fintype.card ι := by
  rw [archLogShell_eq_preimage, Set.mem_preimage, mem_closedBall_zero_iff] at hx
  exact hx

variable {c}

/-- **The archimedean log-shell is not a polydisc** as soon as the packet has two distinct
components `m₁ ≠ m₂` (copies of `ℝ`, `ℂ` in its direct sum decomposition): every polydisc
`a·B_I` containing it has a point outside it. (The log-shell is a Euclidean ball, hence strictly
convex; a polydisc with two factors contains the "corners" `(r₁, ±r₂, 0, …)` whose midpoint lies
on its boundary.) -/
theorem exists_mem_smul_archIntegral_not_mem_archLogShell
    {m₁ m₂ : MaximalSpectrum (Tensor K .infinite c)} (hm : m₁ ≠ m₂) {a : Tensor K .infinite c}
    (ha : IsUnit a) (hsub : archLogShell c ⊆ a • archIntegral c) :
    ∃ y ∈ a • archIntegral c, y ∉ archLogShell c := by
  classical
  set r : MaximalSpectrum (Tensor K .infinite c) → ℝ := fun m => ‖archChar c m a‖ with hr_def
  have hr : ∀ m, 0 < r m := fun m =>
    norm_pos_iff.mpr ((isUnit_iff_forall_archChar_ne_zero c).mp ha m)
  obtain ⟨y₁, hy₁⟩ := exists_forall_archChar_eq c
    (fun m => if m = m₁ then r m₁ else if m = m₂ then r m₂ else 0)
  obtain ⟨y₂, hy₂⟩ := exists_forall_archChar_eq c
    (fun m => if m = m₁ then r m₁ else if m = m₂ then -r m₂ else 0)
  have hmem : ∀ y : Tensor K .infinite c, (∀ m, ‖archChar c m y‖ ≤ r m) →
      y ∈ a • archIntegral c := fun y h => (mem_smul_archIntegral_iff ha).mpr h
  have h₁ : y₁ ∈ a • archIntegral c := hmem _ fun m => by
    rw [hy₁, Complex.norm_real, Real.norm_eq_abs]
    split_ifs with h h'
    · rw [h, abs_of_pos (hr _)]
    · rw [h', abs_of_pos (hr _)]
    · rw [abs_zero]; exact (hr m).le
  have h₂ : y₂ ∈ a • archIntegral c := hmem _ fun m => by
    rw [hy₂, Complex.norm_real, Real.norm_eq_abs]
    split_ifs with h h'
    · rw [h, abs_of_pos (hr _)]
    · rw [h', abs_neg, abs_of_pos (hr _)]
    · rw [abs_zero]; exact (hr m).le
  by_contra hcon'
  have hcon : ∀ y ∈ a • archIntegral c, y ∈ archLogShell c := fun y hy => by
    by_contra h
    exact hcon' ⟨y, hy, h⟩
  have hL₁ := hcon y₁ h₁
  have hL₂ := hcon y₂ h₂
  set e := archTensorCoord c
  set R := Real.pi ^ Fintype.card ι
  have hne : e y₁ ≠ e y₂ := by
    intro h
    have h' := congrArg (archChar c m₂) (archTensorCoord_injective c h)
    rw [hy₁, hy₂, if_neg hm.symm, if_pos rfl, if_neg hm.symm, if_pos rfl] at h'
    have := hr m₂
    have h'' : r m₂ = -r m₂ := by exact_mod_cast h'
    linarith
  set z : Tensor K .infinite c := (1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂ with hz
  have hez : e z = (1 / 2 : ℝ) • e y₁ + (1 / 2 : ℝ) • e y₂ := by
    rw [hz, map_add, map_smul, map_smul]
  have hlt : ‖e z‖ < R := by
    rw [hez]
    exact norm_combo_lt_of_ne (norm_archTensorCoord_le_of_mem c hL₁)
      (norm_archTensorCoord_le_of_mem c hL₂) hne (by norm_num) (by norm_num) (by norm_num)
  have hχz : archChar c m₁ z = (r m₁ : ℂ) := by
    rw [hz, map_add, map_smul, map_smul, hy₁, hy₂, if_pos rfl, if_pos rfl, Complex.real_smul]
    push_cast
    ring
  have hez0 : 0 < ‖e z‖ := by
    refine norm_pos_iff.mpr fun h0 => ?_
    have : z = 0 := archTensorCoord_injective c (h0.trans (map_zero e).symm)
    rw [this, map_zero] at hχz
    have := hr m₁
    have h0' : (0 : ℝ) = r m₁ := by exact_mod_cast hχz
    linarith
  set t := R / ‖e z‖ with ht
  have ht1 : 1 < t := by rw [ht, one_lt_div hez0]; exact hlt
  have htz : t • z ∈ archLogShell c := by
    rw [archLogShell_eq_preimage, Set.mem_preimage, mem_closedBall_zero_iff, map_smul,
      norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), ht, div_mul_cancel₀ _ hez0.ne']
  have hH := (mem_smul_archIntegral_iff ha).mp (hsub htz) m₁
  rw [map_smul, hχz, norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by linarith), abs_of_pos (hr m₁)] at hH
  change t * r m₁ ≤ r m₁ at hH
  nlinarith [hr m₁]

/-- **Strict Haar measure inequality**: with two distinct components, every polydisc
`a·B_I` containing the archimedean log-shell has strictly larger Haar measure. -/
theorem haar_archLogShell_lt {m₁ m₂ : MaximalSpectrum (Tensor K .infinite c)} (hm : m₁ ≠ m₂)
    {a : Tensor K .infinite c} (ha : IsUnit a) (hsub : archLogShell c ⊆ a • archIntegral c) :
    haar .infinite c (archLogShell c) < haar .infinite c (a • archIntegral c) := by
  obtain ⟨y, hyH, hyL⟩ := exists_mem_smul_archIntegral_not_mem_archLogShell hm ha hsub
  set r : MaximalSpectrum (Tensor K .infinite c) → ℝ := fun m => ‖archChar c m a‖ with hr_def
  have hr : ∀ m, 0 < r m := fun m =>
    norm_pos_iff.mpr ((isUnit_iff_forall_archChar_ne_zero c).mp ha m)
  have hy := (mem_smul_archIntegral_iff ha).mp hyH
  set V : Set (Tensor K .infinite c) :=
    {x | ∀ m, ‖archChar c m x‖ < r m} ∩ (archLogShell c)ᶜ with hV
  have hVo : IsOpen V := by
    refine IsOpen.inter ?_ (isClosed_archLogShell c).isOpen_compl
    have : {x : Tensor K .infinite c | ∀ m, ‖archChar c m x‖ < r m} =
        ⋂ m, {x | ‖archChar c m x‖ < r m} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun m =>
      isOpen_lt (continuous_norm.comp (continuous_archChar c m)) continuous_const
  have hev : ∀ᶠ t in nhds (1 : ℝ), t • y ∈ (archLogShell c)ᶜ ∧ t ∈ Set.Ioi (0 : ℝ) := by
    refine Filter.Eventually.and ?_ (Ioi_mem_nhds zero_lt_one)
    have hT : Filter.Tendsto (fun t : ℝ => t • y) (nhds 1) (nhds y) :=
      Continuous.tendsto' (f := fun t : ℝ => t • y) (by fun_prop) 1 y (one_smul ℝ y)
    exact hT.eventually ((isClosed_archLogShell c).isOpen_compl.mem_nhds hyL)
  obtain ⟨t, ⟨htL, ht0⟩, ht1⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Iio (1 : ℝ)))).exists
  have htV : t • y ∈ V := by
    refine ⟨fun m => ?_, htL⟩
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    calc t * ‖archChar c m y‖ ≤ t * r m := mul_le_mul_of_nonneg_left (hy m) ht0.le
      _ < 1 * r m := mul_lt_mul_of_pos_right ht1 (hr m)
      _ = r m := one_mul _
  have hVH : V ⊆ a • archIntegral c := fun x hx =>
    (mem_smul_archIntegral_iff ha).mpr fun m => (hx.1 m).le
  have hdisj : Disjoint (archLogShell c) V := Set.disjoint_left.mpr fun x hx hxV => hxV.2 hx
  have hVpos : 0 < haar .infinite c V := hVo.measure_pos _ ⟨_, htV⟩
  have hLtop : haar .infinite c (archLogShell c) ≠ ⊤ := (isCompact_archLogShell c).measure_lt_top.ne
  calc haar .infinite c (archLogShell c)
      < haar .infinite c (archLogShell c) + haar .infinite c V :=
        ENNReal.lt_add_right hLtop hVpos.ne'
    _ = haar .infinite c (archLogShell c ∪ V) := (measure_union hdisj hVo.measurableSet).symm
    _ ≤ haar .infinite c (a • archIntegral c) := measure_mono (Set.union_subset hsub hVH)

/-- **The archimedean log-shell has strictly smaller log-volume than its hull**, as soon as
the packet has two distinct components. -/
theorem componentVol_archLogShell_lt_leastHull
    {m₁ m₂ : MaximalSpectrum (Tensor K .infinite c)} (hm : m₁ ≠ m₂) :
    componentVol .infinite c (archLogShell c) <
      componentVol .infinite c (leastHull .infinite c (archLogShell c)) := by
  obtain ⟨a, ha, hsub, heq⟩ := exists_leastHull_eq (archLogShell_admissible c)
  rw [heq]
  have hsub' : archLogShell c ⊆ a • archIntegral c := hsub
  have hlt := haar_archLogShell_lt hm ha hsub'
  change componentVol .infinite c (archLogShell c) <
    componentVol .infinite c (a • archIntegral c)
  unfold componentVol
  have hn : (0 : ℝ) < Module.finrank (baseField .infinite) (Tensor K .infinite c) := by
    exact_mod_cast finrank_tensor_infinite_pos (c := c)
  refine div_lt_div_of_pos_right ?_ hn
  have hLpos := ENNReal.toReal_pos (haar_archLogShell_pos c).ne'
    (isCompact_archLogShell c).measure_lt_top.ne
  refine Real.log_lt_log (div_pos hLpos toReal_haar_integralAt_pos) ?_
  refine div_lt_div_of_pos_right ?_ toReal_haar_integralAt_pos
  exact (ENNReal.toReal_lt_toReal (isCompact_archLogShell c).measure_lt_top.ne
    (haar_smul_integralAt_lt_top (vQ := .infinite) a).ne).mpr hlt

/-! ### Packets with two complex factors have two components -/

lemma finrank_archFactorSub_of_isComplex {v : Place K} (h : (archPlace K v).IsComplex) :
    Module.finrank ℝ (archFactorSub v) = 2 := by
  change Module.finrank ℝ (Subalgebra.toSubmodule (archField K (archPlace K v))) = 2
  rw [archField_of_isComplex (K := K) h, Algebra.top_toSubmodule, finrank_top,
    Complex.finrank_real_complex]

/-- **A packet `⊗_j K_{c j}` with all factors `ℂ` and at least two of them has two distinct
components**: its real dimension `2^{|I|}` exceeds `2`, the dimension of a single copy of `ℂ`. -/
theorem exists_ne_maximalSpectrum {j₁ j₂ : ι} (hj : j₁ ≠ j₂)
    (hc : ∀ j, (archPlace K (c j)).IsComplex) :
    ∃ m₁ m₂ : MaximalSpectrum (Tensor K .infinite c), m₁ ≠ m₂ := by
  classical
  have hdim : Module.finrank ℝ (Tensor K .infinite c) = 2 ^ Fintype.card ι := by
    rw [Module.finrank_eq_card_basis (archTensorBasis c), Fintype.card_eq_nat_card,
      Nat.card_pi, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, finrank_archFactorSub_of_isComplex (hc j)]
  have hle : Module.finrank ℝ (Tensor K .infinite c) ≤
      Module.finrank ℝ (MaximalSpectrum (Tensor K .infinite c) → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective (f := archCharLin c)
      (LinearMap.ker_eq_bot.mp (ker_archCharLin c))
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Complex.finrank_real_complex, hdim] at hle
  have hι : 2 ≤ Fintype.card ι := Fintype.one_lt_card_iff.mpr ⟨j₁, j₂, hj⟩
  have h4 : 4 ≤ 2 ^ Fintype.card ι :=
    (Nat.pow_le_pow_right (by norm_num) hι).trans' (by norm_num)
  have hcard : 1 < Fintype.card (MaximalSpectrum (Tensor K .infinite c)) := by omega
  obtain ⟨m₁, m₂, hm⟩ := Fintype.one_lt_card_iff.mp hcard
  exact ⟨m₁, m₂, hm⟩

end LocalConstruct

namespace LocalTheory

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]

/-- `hull(U) ⊆ hull(V)` for `U ⊆ V`, `V` admissible. -/
lemma leastHull_mono {vQ : RationalPlace} {c : ι → Place K} {U V : Set (Tensor K vQ c)}
    (hUV : U ⊆ V) (hV : V ∈ admissible K vQ c) : leastHull vQ c U ⊆ leastHull vQ c V := by
  obtain ⟨b, hb, hVb, h⟩ := exists_leastHull_eq hV
  rw [h]
  exact leastHull_subset hb (hUV.trans hVb)

/-- The tensor product of the log-shells is admissible. -/
lemma shell_admissible (p : Nat.Primes) (c : ι → Place K) :
    shell K p c ∈ admissible K (.finite p) c := by
  obtain ⟨hb, ho, hpos⟩ := smul_shell_bounded_open_pos K p c 1 isUnit_one
  rw [one_smul] at hb ho hpos
  exact ⟨nonempty_of_measure_ne_zero hpos.ne', hb.isCompact_closure, ho.measurableSet, hpos,
    hb.measure_lt_top⟩

/-- **The shell defect** at a prime: `μ^log(hull(⊗_j 𝓘_j)) − μ^log(⊗_j 𝓘_j)`, how much the
least region `a·O` containing the tensor product of the log-shells exceeds it. -/
noncomputable def shellDefect (p : Nat.Primes) (c : ι → Place K) : ℝ :=
  componentVol K (.finite p) c (leastHull (.finite p) c (shell K p c)) -
    componentVol K (.finite p) c (shell K p c)

lemma shellDefect_nonneg (p : Nat.Primes) (c : ι → Place K) : 0 ≤ shellDefect p c :=
  sub_nonneg.mpr (componentVol_le_leastHull_self (shell_admissible p c))

/-- At an odd prime unramified in every factor the shell defect vanishes: there the tensor
product of the log-shells is the integral structure (`shell_eq_integral`). -/
lemma shellDefect_eq_zero (p : Nat.Primes) (c : ι → Place K)
    (hc : ∀ j, ∃ w : FinitePlace K, c j = Place.finite w ∧ residueChar w = p)
    (hp : Odd (p : ℕ)) (hunr : ∀ j w, c j = Place.finite w → ramIdx K w = 1) :
    shellDefect p c = 0 := by
  unfold shellDefect
  rw [shell_eq_integral K p c hc hp hunr]
  have h := leastHull_smul_integral (vQ := .finite p) (c := c) isUnit_one
  rw [one_smul] at h
  rw [h, sub_self]

/-- **The archimedean defect**: `μ^log(hull(𝓘_∞)) − μ^log(𝓘_∞)` for the archimedean log-shell
(the ball of the tensor-product metric) and its least polydisc `a·B_I`. -/
noncomputable def archDefect (c : ι → Place K) : ℝ :=
  componentVol K .infinite c (leastHull .infinite c (logShell K .infinite c)) -
    componentVol K .infinite c (logShell K .infinite c)

lemma archDefect_nonneg (c : ι → Place K) : 0 ≤ archDefect c :=
  sub_nonneg.mpr (componentVol_le_leastHull_self (LocalConstruct.archLogShell_admissible c))

/-- **The archimedean defect is positive** as soon as two factors are complex: the log-shell
is a Euclidean ball, strictly smaller than the least polydisc containing it. -/
theorem archDefect_pos (c : ι → Place K) {j₁ j₂ : ι} (hj : j₁ ≠ j₂)
    (hc : ∀ j, (LocalConstruct.archPlace K (c j)).IsComplex) : 0 < archDefect c := by
  obtain ⟨m₁, m₂, hm⟩ := LocalConstruct.exists_ne_maximalSpectrum (c := c) hj hc
  exact sub_pos.mpr (LocalConstruct.componentVol_archLogShell_lt_leastHull hm)

end LocalTheory

/-- **A number field containing a square root of `−1` is totally complex.** -/
lemma InfinitePlace.isComplex_of_sqrt_neg_one {L : Type u} [Field L] [NumberField L]
    {x : L} (hx : x * x = -1) (w : InfinitePlace L) : w.IsComplex := by
  by_contra h
  have hw := InfinitePlace.not_isComplex_iff_isReal.mp h
  have h1 := congrArg (InfinitePlace.embedding_of_isReal hw) hx
  rw [map_mul, map_neg, map_one] at h1
  nlinarith [mul_self_nonneg (InfinitePlace.embedding_of_isReal hw x)]

/-- **The `ℓ`-torsion field of initial Θ-data is totally complex**: `F` contains `√−1`
(IUT I, Definition 3.1(a); `IsInitialThetaGlobalData.sqrt_neg_one`), hence so does `K ⊇ F`. -/
lemma InitialThetaData.isComplex_Kt (D : InitialThetaData.{u}) (w : InfinitePlace D.Kt) :
    w.IsComplex := by
  obtain ⟨r, hr⟩ := D.global.sqrt_neg_one
  refine InfinitePlace.isComplex_of_sqrt_neg_one (x := algebraMap D.F D.Kt r) ?_ w
  rw [← map_mul, ← hr, map_neg, map_one]

namespace WallEquiv

open Wall LocalTheory

noncomputable section

variable (D : InitialThetaData.{0})

/-! ### The gap `Δ(D)` -/

/-- **The gap** `Δ(D) = −|log(Θ)| − log-vol(LGP·hull(VC(I)))` between the right-hand sides of the
Corollary 3.12 variant (Var) and of the Scholze–Stix inequality in its form
`−|log(q)| ≤ log-vol(LGP·hull(VC(I)))` (`ss_iff_lgp_vcI`). -/
def gap : ℝ := (concreteVariantData D).rhsData.rhs - logVol D (lgp D (hullOf D (vcI D)))

/-- **`log-vol(LGP·hull(VC(I))) ≤ −|log(Θ)|`**: `LGP·hull(VC(I))` lies in the hull of the
(Ind1)-image of the theta-pilot region with the theta values at the labels `j`
(`inHullOfImage_lgp`). -/
theorem logVol_lgp_vcI_le_rhs :
    logVol D (lgp D (hullOf D (vcI D))) ≤ (concreteVariantData D).rhsData.rhs :=
  logVol_le_rhs D (isAdelic_lgp D (isAdelic_hullOf_vcI D)) (inHullOfImage_lgp D (Ind3.top D))

theorem gap_nonneg : 0 ≤ gap D := sub_nonneg.mpr (logVol_lgp_vcI_le_rhs D)

lemma logVol_lgp_vcI_eq :
    logVol D (lgp D (hullOf D (vcI D))) = (concreteVariantData D).rhsData.rhs - gap D := by
  unfold gap
  ring

/-- `Δ(D) = −|log(Θ)| + s·|log(q)| − log-vol(hull(VC(I)))` (`logVol_lgp`,
`logVol_lgp_integral`). -/
lemma gap_eq_rhs_add : gap D = (concreteVariantData D).rhsData.rhs +
    sFactor (nC D) * D.qPilot.absLogQ - logVol D (hullOf D (vcI D)) := by
  unfold gap
  rw [logVol_lgp D (isAdelic_hullOf_vcI D), logVol_lgp_integral]
  ring

/-- **(SS) is (Var) with the right-hand side lowered by the gap**:
`SSIneq D ↔ −|log(q)| ≤ −|log(Θ)| − Δ(D)`. -/
theorem ss_iff_le_rhs_sub_gap :
    SSIneq D ↔ -D.qPilot.absLogQ ≤ (concreteVariantData D).rhsData.rhs - gap D := by
  rw [ss_iff_lgp_vcI, logVol_lgp_vcI_eq]
  rfl

/-- **(Var)** is `−|log(q)| ≤ −|log(Θ)|`. -/
theorem variant_iff_le_rhs :
    Corollary312Variant (concreteVariantData D) ↔
      -D.qPilot.absLogQ ≤ (concreteVariantData D).rhsData.rhs :=
  Iff.rfl

/-- (SS) ⇒ (Var), through `Δ(D) ≥ 0`. -/
theorem variant_of_ss_gap (h : SSIneq D) : Corollary312Variant (concreteVariantData D) :=
  (variant_iff_le_rhs D).mpr
    (((ss_iff_le_rhs_sub_gap D).mp h).trans (sub_le_self _ (gap_nonneg D)))

/-- If the gap vanishes, (SS) and (Var) are the same inequality. -/
theorem ss_iff_variant_of_gap_eq_zero (h : gap D = 0) :
    SSIneq D ↔ Corollary312Variant (concreteVariantData D) := by
  rw [ss_iff_le_rhs_sub_gap, variant_iff_le_rhs, h, sub_zero]

/-- **The window between the walls**: (Var) holds and (SS) fails exactly when `−|log(q)|` lies
in the interval `(−|log(Θ)| − Δ(D), −|log(Θ)|]`, of length `Δ(D)`. -/
theorem variant_and_not_ss_iff :
    Corollary312Variant (concreteVariantData D) ∧ ¬ SSIneq D ↔
      (concreteVariantData D).rhsData.rhs - gap D < -D.qPilot.absLogQ ∧
        -D.qPilot.absLogQ ≤ (concreteVariantData D).rhsData.rhs := by
  rw [ss_iff_le_rhs_sub_gap, variant_iff_le_rhs, not_le]
  exact and_comm

/-! ### The no-hull gap -/

/-- **The no-hull gap** `Δ_noHull(D) = −|log(Θ)| − log-vol(LGP·VC(I))`, the gap between (Var) and
the no-hull wall `SSIneqNoHull` (`ssNoHull_iff_lgp_vcI`). -/
def gapNoHull : ℝ := (concreteVariantData D).rhsData.rhs - logVol D (lgp D (vcI D))

/-- **The no-hull gap is the gap plus the hull–container difference**:
`Δ_noHull(D) = Δ(D) + (log-vol(hull(VC(I))) − log-vol(VC(I)))`. -/
theorem gapNoHull_eq_gap_add : gapNoHull D =
    gap D + (logVol D (hullOf D (vcI D)) - logVol D (vcI D)) := by
  unfold gapNoHull gap
  rw [logVol_lgp D (isAdelic_vcI D), logVol_lgp D (isAdelic_hullOf_vcI D)]
  ring

theorem gap_le_gapNoHull : gap D ≤ gapNoHull D := by
  rw [gapNoHull_eq_gap_add]
  linarith [logVol_vcI_le_logVol_hullOf D]

theorem gapNoHull_nonneg : 0 ≤ gapNoHull D := (gap_nonneg D).trans (gap_le_gapNoHull D)

/-- **The no-hull wall is (Var) with the right-hand side lowered by the no-hull gap.** -/
theorem ssNoHull_iff_le_rhs_sub_gapNoHull :
    SSIneqNoHull D ↔ -D.qPilot.absLogQ ≤ (concreteVariantData D).rhsData.rhs - gapNoHull D := by
  rw [ssNoHull_iff_lgp_vcI]
  have hlhs : (concreteVariantData D).qPilot.lhs = -D.qPilot.absLogQ := rfl
  unfold gapNoHull
  rw [hlhs]
  constructor <;> intro h <;> linarith

/-! ### The no-hull gap as a sum of local terms -/

/-- **The component of `LGP·VC(I)`** at a tuple `c`: `q_{v_j}^{j²}·⊗_l 𝓘_{v_l}` at a prime,
the archimedean log-shell at `∞`. -/
def lgpComp (i : Fin (nC D)) :
    ∀ (vQ : RationalPlace) (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ),
      Set (LocalTheory.Tensor D.Kt vQ (LocalTheory.tuple D.placeSect vQ c))
  | .finite p, c =>
    D.scaleElt (nC D) i p c • LocalTheory.shell D.Kt p (LocalTheory.tuple D.placeSect _ c)
  | .infinite, c => LocalTheory.logShell D.Kt .infinite (LocalTheory.tuple D.placeSect _ c)

lemma lgpComp_admissible (i : Fin (nC D)) (vQ : RationalPlace)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ) :
    lgpComp D i vQ c ∈ LocalTheory.admissible D.Kt vQ (LocalTheory.tuple D.placeSect vQ c) := by
  rcases vQ with p | _
  · exact LocalConstruct.units_smul_mem_admissible (D.isUnit_scaleElt _ i p c)
      (shell_admissible p _)
  · exact LocalConstruct.archLogShell_admissible _

/-- The components of `LGP·VC(I)`. -/
lemma proj_lgp_vcI (i : Fin (nC D)) (vQ : RationalPlace)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ) :
    LocalTheory.proj D.placeSect vQ c ((lgp D (vcI D) i).region vQ) = lgpComp D i vQ c := by
  rcases vQ with p | _
  · rw [proj_lgp]
    have h : LocalTheory.proj D.placeSect (.finite p) c ((vcI D i).region (.finite p)) =
        vcIComp D i (.finite p) c :=
      proj_productRegion D.placeSect _ _ (fun c => (vcIComp_admissible D i _ c).1) c
    rw [h]
    rfl
  · exact proj_productRegion D.placeSect _ _ (fun c => (vcIComp_admissible D i _ c).1) c

/-- `LGP·VC(I) ⊆` the theta-pilot region, componentwise (the identity is an indeterminacy
automorphism). -/
lemma lgpComp_subset_theta (i : Fin (nC D)) (vQ : RationalPlace)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ) :
    lgpComp D i vQ c ⊆ D.thetaComponent (nC D) i vQ c := by
  rcases vQ with p | _
  · change _ ⊆ D.thetaFinite (nC D) i p c
    rw [D.thetaFinite_eq]
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨id, LocalTheory.id_mem_indAut D.Kt _ _, by rwa [Set.image_id]⟩
  · intro x hx
    exact Set.mem_iUnion₂.mpr ⟨id, LocalTheory.id_mem_indAut D.Kt _ _, by rwa [Set.image_id]⟩

/-- **The local term** `δ_{i,v_ℚ,c} = μ^log(hull(Θ_{i,v_ℚ,c})) − μ^log((LGP·VC(I))_{i,v_ℚ,c})`:
the least region `a·O` containing the theta-pilot component (the union of the
indeterminacy images of `q^{j²}·⊗𝓘` at a prime, of the log-shell at `∞`) against the
component `q^{j²}·⊗𝓘` (resp. the log-shell) of `LGP·VC(I)`. -/
def gapTerm (i : Fin (nC D)) (vQ : RationalPlace)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ) : ℝ :=
  LocalTheory.componentVol D.Kt vQ (LocalTheory.tuple D.placeSect vQ c)
      (LocalTheory.leastHull vQ (LocalTheory.tuple D.placeSect vQ c)
        (D.thetaComponent (nC D) i vQ c)) -
    LocalTheory.componentVol D.Kt vQ (LocalTheory.tuple D.placeSect vQ c) (lgpComp D i vQ c)

theorem gapTerm_nonneg (i : Fin (nC D)) (vQ : RationalPlace)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ) : 0 ≤ gapTerm D i vQ c :=
  sub_nonneg.mpr (componentVol_le_leastHull (lgpComp_admissible D i vQ c)
    (lgpComp_subset_theta D i vQ c)
    (D.thetaComponentOn_admissible _ i _ (InitialThetaData.ivLabels_nonempty _ i) vQ c))

/-- **The packet term** at capsule `i` and rational place `v_ℚ`: `∑_c w_c·δ_{i,v_ℚ,c}`. -/
def gapAt (i : Fin (nC D)) (vQ : RationalPlace) : ℝ :=
  ∑ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ,
    tupleWeight vQ c * gapTerm D i vQ c

lemma gapAt_nonneg (i : Fin (nC D)) (vQ : RationalPlace) : 0 ≤ gapAt D i vQ :=
  Finset.sum_nonneg fun c _ => mul_nonneg (Finset.prod_nonneg fun _ _ => (weight_pos _ _ _).le)
    (gapTerm_nonneg D i vQ c)

/-- The packet term is the difference of the packet log-volumes of the hull of the theta-pilot
region and of `LGP·VC(I)`. -/
lemma gapAt_eq (i : Fin (nC D)) (vQ : RationalPlace) :
    gapAt D i vQ =
      (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ
          ((hullOf D (D.thetaPilot (nC D)) i).region vQ) -
        (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ ((lgp D (vcI D) i).region vQ) := by
  rw [LocalTheory.packetVol_eq, LocalTheory.packetVol_eq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_sub]
  congr 1
  unfold gapTerm
  rw [proj_lgp_vcI]
  congr 2
  exact (proj_hull_productRegion D.placeSect (nC D) i vQ _
    (fun c => D.thetaComponentOn_admissible _ i _ (InitialThetaData.ivLabels_nonempty _ i) vQ c)
      c).symm

lemma finite_support_gapAt (i : Fin (nC D)) : (Function.support (gapAt D i)).Finite := by
  refine (((LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol
    (hullOf D (D.thetaPilot (nC D)) i)).union
    ((LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol (lgp D (vcI D) i))).subset ?_
  have : gapAt D i = fun vQ =>
      (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ
          ((hullOf D (D.thetaPilot (nC D)) i).region vQ) -
        (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ ((lgp D (vcI D) i).region vQ) :=
    funext (gapAt_eq D i)
  rw [this]
  exact Function.support_sub _ _

/-- **The no-hull gap is an average of sums of local terms**:
`Δ_noHull(D) = (1/ℓ*)·∑_i ∑_{v_ℚ} ∑_c w_c·δ_{i,v_ℚ,c}`. -/
theorem gapNoHull_eq : gapNoHull D = (∑ i : Fin (nC D), ∑ᶠ vQ, gapAt D i vQ) / nC D := by
  unfold gapNoHull
  rw [rhs_eq_logVol]
  unfold logVol LogVolumeData.processionVol
  rw [← sub_div, ← Finset.sum_sub_distrib]
  refine congrArg₂ (· / ·) (Finset.sum_congr rfl fun i _ => ?_) rfl
  unfold LogVolumeData.globalVol
  rw [← finsum_sub_distrib ((LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol _)
    ((LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol _)]
  exact finsum_congr fun vQ => (gapAt_eq D i vQ).symm

/-! ### The local terms -/

lemma scaleElt_eq_one (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p))
    (hbad : (p : ℕ) ∉ D.badChars) : D.scaleElt (nC D) i p c = 1 := by
  unfold InitialThetaData.scaleElt InitialThetaData.scaleEltAt
  rw [D.qroot_eq_one _ (by rw [residueChar_sectPlace D.placeSect]; exact hbad), one_pow, map_one]

/-- **At `∞` the indeterminacies change nothing**: the theta-pilot component is the log-shell
(the indeterminacy automorphisms preserve it, `archIndAut_image_archLogShell`). -/
lemma thetaComponent_infinite (i : Fin (nC D))
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod .infinite) :
    D.thetaComponent (nC D) i .infinite c =
      LocalTheory.logShell D.Kt .infinite (LocalTheory.tuple D.placeSect _ c) := by
  refine Set.Subset.antisymm (Set.iUnion₂_subset fun φ hφ =>
    LocalConstruct.archIndAut_image_archLogShell _ φ hφ) fun x hx => ?_
  exact Set.mem_iUnion₂.mpr ⟨id, LocalTheory.id_mem_indAut D.Kt _ _, by rwa [Set.image_id]⟩

/-- **At a prime that is not a bad residue characteristic** the theta-pilot component is the
tensor product of the log-shells (theta values `1`; the indeterminacy automorphisms preserve
it, `indAut_shell`). -/
lemma thetaComponent_finite_of_not_bad (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p))
    (hbad : (p : ℕ) ∉ D.badChars) :
    D.thetaComponent (nC D) i (.finite p) c =
      LocalTheory.shell D.Kt p (LocalTheory.tuple D.placeSect _ c) := by
  change D.thetaFinite (nC D) i p c = _
  rw [D.thetaFinite_eq, scaleElt_eq_one D i p c hbad, one_smul]
  refine Set.Subset.antisymm (Set.iUnion₂_subset fun φ hφ =>
    (LocalTheory.indAut_shell D.Kt p _ φ hφ).le) fun x hx => ?_
  exact Set.mem_iUnion₂.mpr ⟨id, LocalTheory.id_mem_indAut D.Kt _ _, by rwa [Set.image_id]⟩

/-- **The local term at `∞` is the archimedean defect** of the packet. -/
theorem gapTerm_infinite (i : Fin (nC D))
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod .infinite) :
    gapTerm D i .infinite c = archDefect (LocalTheory.tuple D.placeSect .infinite c) := by
  unfold gapTerm archDefect
  rw [thetaComponent_infinite]
  rfl

/-- **The (Ind2)-term** at a prime: `μ^log(hull(Θ_{i,p,c})) − μ^log(q^{j²}·hull(⊗𝓘))`, the
enlargement of the hull by the union over the indeterminacy automorphisms of the
theta-scaled shell. -/
def ind2Term (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) : ℝ :=
  LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)
      (LocalTheory.leastHull (.finite p) (LocalTheory.tuple D.placeSect _ c)
        (D.thetaComponent (nC D) i (.finite p) c)) -
    LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)
      (D.scaleElt (nC D) i p c • leastHull (.finite p) (LocalTheory.tuple D.placeSect _ c)
        (LocalTheory.shell D.Kt p (LocalTheory.tuple D.placeSect _ c)))

theorem ind2Term_nonneg (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    0 ≤ ind2Term D i p c := by
  have hs := D.isUnit_scaleElt _ i p c
  have hsh := shell_admissible p (LocalTheory.tuple D.placeSect _ c)
  have hθ := D.thetaComponentOn_admissible _ i _ (InitialThetaData.ivLabels_nonempty _ i)
    (.finite p) c
  refine sub_nonneg.mpr (LocalConstruct.componentVol_le_of_subset ?_ ?_ ?_)
  · rw [← leastHull_units_smul hs hsh]
    exact leastHull_mono (lgpComp_subset_theta D i (.finite p) c) hθ
  · rw [← leastHull_units_smul hs hsh]
    exact LocalConstruct.admissible_haar_pos
      (leastHull_admissible (LocalConstruct.units_smul_mem_admissible hs hsh))
  · exact LocalConstruct.admissible_haar_lt_top (leastHull_admissible hθ)

theorem ind2Term_eq_zero (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p))
    (hbad : (p : ℕ) ∉ D.badChars) : ind2Term D i p c = 0 := by
  unfold ind2Term
  rw [thetaComponent_finite_of_not_bad D i p c hbad, scaleElt_eq_one D i p c hbad, one_smul,
    sub_self]

/-- **The local term at a prime splits** into the shell defect (independent of the theta
values and of the indeterminacies) and the (Ind2)-term. -/
theorem gapTerm_finite (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    gapTerm D i (.finite p) c =
      shellDefect p (LocalTheory.tuple D.placeSect _ c) + ind2Term D i p c := by
  have hs := D.isUnit_scaleElt _ i p c
  have hsh := shell_admissible p (LocalTheory.tuple D.placeSect _ c)
  have h1 := LocalConstruct.componentVol_units_smul hs (LocalConstruct.admissible_haar_pos hsh)
    (LocalConstruct.admissible_haar_lt_top hsh)
  have h2 := LocalConstruct.componentVol_units_smul hs
    (LocalConstruct.admissible_haar_pos (leastHull_admissible hsh))
    (LocalConstruct.admissible_haar_lt_top (leastHull_admissible hsh))
  unfold gapTerm shellDefect ind2Term
  change _ - LocalConstruct.componentVol (.finite p) _ (D.scaleElt (nC D) i p c • _) = _
  rw [h1]
  change _ = _ - _ + (_ - LocalConstruct.componentVol (.finite p) _
    (D.scaleElt (nC D) i p c • _))
  rw [h2]
  ring

/-- **The local terms vanish at the good primes**: odd, unramified in `K`, and not a bad
residue characteristic. So `gapAt D i` is supported on `∞`, `2`, the primes ramified in `K`
and the bad residue characteristics. -/
theorem gapTerm_eq_zero (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p))
    (hbad : (p : ℕ) ∉ D.badChars) (hodd : Odd (p : ℕ))
    (hunr : ∀ w : FinitePlace D.Kt, residueChar w = p → ramIdx D.Kt w = 1) :
    gapTerm D i (.finite p) c = 0 := by
  rw [gapTerm_finite, ind2Term_eq_zero D i p c hbad, add_zero]
  refine shellDefect_eq_zero p _ (tuple_isOver D.placeSect p c) hodd fun j w hw => ?_
  obtain ⟨w', hw', hres⟩ := tuple_isOver D.placeSect p c j
  rw [hw] at hw'
  cases Sum.inl.inj hw'
  exact hunr w hres

theorem gapAt_eq_zero (i : Fin (nC D)) (p : Nat.Primes) (hbad : (p : ℕ) ∉ D.badChars)
    (hodd : Odd (p : ℕ))
    (hunr : ∀ w : FinitePlace D.Kt, residueChar w = p → ramIdx D.Kt w = 1) :
    gapAt D i (.finite p) = 0 :=
  Finset.sum_eq_zero fun c _ => by rw [gapTerm_eq_zero D i p c hbad hodd hunr, mul_zero]

/-- **The places carrying the gap**: `gapAt D i` is supported on `∞`, `2`, the bad residue
characteristics and the primes ramified in `K`. -/
theorem support_gapAt_subset (i : Fin (nC D)) :
    Function.support (gapAt D i) ⊆ {vQ | vQ = .infinite ∨ ∃ p : Nat.Primes, vQ = .finite p ∧
      ((p : ℕ) = 2 ∨ (p : ℕ) ∈ D.badChars ∨
        ∃ w : FinitePlace D.Kt, residueChar w = p ∧ ramIdx D.Kt w ≠ 1)} := by
  intro vQ h
  rcases vQ with p | _
  · refine Or.inr ⟨p, rfl, ?_⟩
    by_cases h2 : (p : ℕ) = 2
    · exact Or.inl h2
    by_cases hb : (p : ℕ) ∈ D.badChars
    · exact Or.inr (Or.inl hb)
    by_cases hr : ∃ w : FinitePlace D.Kt, residueChar w = p ∧ ramIdx D.Kt w ≠ 1
    · exact Or.inr (Or.inr hr)
    exfalso
    exact h (gapAt_eq_zero D i p hb (p.2.odd_of_ne_two h2)
      fun w hw => by_contra fun hne => hr ⟨w, hw, hne⟩)
  · exact Or.inl rfl

/-! ### Strictness of the no-hull gap: `Δ_noHull(D) > 0` -/

/-- Every capsule `S_{j+1} = {0, …, j}` (`j = i + 1 ≥ 1`) has the two labels `0 ≠ j`. -/
lemma zero_ne_distinguished (i : Fin (nC D)) :
    (⟨0, by simp [Procession.standard, procLabels]⟩ : InitialThetaData.Lab (nC D) i) ≠
      InitialThetaData.distinguished _ i := by
  intro h
  have := congrArg Subtype.val h
  simp [InitialThetaData.distinguished] at this

/-- **The local term at `∞` is positive** for every tuple: `K` is totally complex and every
capsule has at least two labels, so the archimedean packet is a product of at least two
copies of `ℂ`, in which the log-shell (a ball) is strictly smaller than its least polydisc. -/
theorem gapTerm_infinite_pos (i : Fin (nC D))
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod .infinite) :
    0 < gapTerm D i .infinite c := by
  rw [gapTerm_infinite]
  refine archDefect_pos _ (zero_ne_distinguished D i) fun j => ?_
  rw [tuple_infinite]
  exact D.isComplex_Kt _

theorem gapAt_infinite_pos (i : Fin (nC D)) : 0 < gapAt D i .infinite := by
  have hne : (Finset.univ :
      Finset (InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod .infinite)).Nonempty :=
    Finset.nonempty_of_sum_ne_zero (f := tupleWeight .infinite)
      (by rw [sum_tupleWeight D.placeSect (nC D) i .infinite]; exact one_ne_zero)
  exact Finset.sum_pos (fun c _ => mul_pos (Finset.prod_pos fun _ _ => weight_pos _ _ _)
    (gapTerm_infinite_pos D i c)) hne

/-- **The no-hull gap is positive for every initial Θ-datum**: the (Var)-wall is strictly
weaker than the no-hull wall. -/
theorem gapNoHull_pos : 0 < gapNoHull D := by
  rw [gapNoHull_eq]
  refine div_pos (Finset.sum_pos (fun i _ => ?_) ⟨⟨0, nC_pos D⟩, Finset.mem_univ _⟩)
    (by exact_mod_cast nC_pos D)
  exact (gapAt_infinite_pos D i).trans_le
    (single_le_finsum _ (finite_support_gapAt D i) (gapAt_nonneg D i))

/-- **The archimedean lower bound**: `Δ_noHull(D) ≥ (1/ℓ*)·∑_i ∑_c w_c·δ_∞(c) > 0`. -/
theorem archPart_le_gapNoHull :
    (∑ i : Fin (nC D), gapAt D i .infinite) / nC D ≤ gapNoHull D := by
  rw [gapNoHull_eq]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _)
  exact single_le_finsum _ (finite_support_gapAt D i) (gapAt_nonneg D i)

/-- With `Δ_noHull(D) > 0`, the no-hull wall is strictly stronger than (Var) as an inequality:
it gives `−|log(q)| ≤ −|log(Θ)| − Δ_noHull(D) < −|log(Θ)|`. -/
theorem ssNoHull_imp_lt_rhs (h : SSIneqNoHull D) :
    -D.qPilot.absLogQ < (concreteVariantData D).rhsData.rhs :=
  ((ssNoHull_iff_le_rhs_sub_gapNoHull D).mp h).trans_lt (sub_lt_self _ (gapNoHull_pos D))


/-! ### The gap as a sum of local terms: only the (Ind2)-terms remain -/

/-- **The local term of the gap** at capsule `i`: `∑_c w_c·ind2Term` at a prime, `0` at `∞`. -/
def gapHullAt (i : Fin (nC D)) : RationalPlace → ℝ
  | .finite p => ∑ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
      tupleWeight (.finite p) c * ind2Term D i p c
  | .infinite => 0

/-- The components of `hull(VC(I))` are the least hulls of the components of `VC(I)`. -/
lemma proj_hull_vcI (i : Fin (nC D)) (vQ : RationalPlace)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ) :
    LocalTheory.proj D.placeSect vQ c ((hullOf D (vcI D) i).region vQ) =
      leastHull vQ (LocalTheory.tuple D.placeSect vQ c) (vcIComp D i vQ c) :=
  proj_hull_productRegion D.placeSect (nC D) i vQ (fun c => vcIComp D i vQ c)
    (fun c => vcIComp_admissible D i vQ c) c

/-- The components of the hull of the theta-pilot region. -/
lemma proj_hull_thetaPilot (i : Fin (nC D)) (vQ : RationalPlace)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ) :
    LocalTheory.proj D.placeSect vQ c ((hullOf D (D.thetaPilot (nC D)) i).region vQ) =
      leastHull vQ (LocalTheory.tuple D.placeSect vQ c) (D.thetaComponent (nC D) i vQ c) :=
  proj_hull_productRegion D.placeSect (nC D) i vQ _
    (fun c => D.thetaComponentOn_admissible _ i _ (InitialThetaData.ivLabels_nonempty _ i) vQ c) c

/-- **The packet term of the gap** is the difference of the packet log-volumes of the hull of
the theta-pilot region and of `LGP·hull(VC(I))`: at `∞` both components are the least polydisc
of the log-shell (`thetaComponent_infinite`), at a prime the difference is the (Ind2)-term. -/
lemma gapHullAt_eq (i : Fin (nC D)) (vQ : RationalPlace) :
    gapHullAt D i vQ =
      (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ
          ((hullOf D (D.thetaPilot (nC D)) i).region vQ) -
        (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ
          ((lgp D (hullOf D (vcI D)) i).region vQ) := by
  rw [LocalTheory.packetVol_eq, LocalTheory.packetVol_eq, ← Finset.sum_sub_distrib]
  rcases vQ with p | _
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_sub, proj_lgp, proj_hull_vcI, proj_hull_thetaPilot]
    rfl
  · refine (Finset.sum_eq_zero fun c _ => ?_).symm
    have h : LocalTheory.proj D.placeSect .infinite c
        ((lgp D (hullOf D (vcI D)) i).region .infinite) =
        LocalTheory.proj D.placeSect .infinite c ((hullOf D (vcI D) i).region .infinite) := rfl
    rw [h, proj_hull_vcI, proj_hull_thetaPilot, thetaComponent_infinite]
    exact sub_self _

lemma gapHullAt_nonneg (i : Fin (nC D)) (vQ : RationalPlace) : 0 ≤ gapHullAt D i vQ := by
  rcases vQ with p | _
  · exact Finset.sum_nonneg fun c _ => mul_nonneg
      (Finset.prod_nonneg fun _ _ => (weight_pos _ _ _).le) (ind2Term_nonneg D i p c)
  · exact le_rfl

/-- **The gap is carried by the bad residue characteristics**: the local term vanishes at `∞`
and at every prime that is not a bad residue characteristic. -/
theorem gapHullAt_eq_zero (i : Fin (nC D)) (p : Nat.Primes) (hbad : (p : ℕ) ∉ D.badChars) :
    gapHullAt D i (.finite p) = 0 :=
  Finset.sum_eq_zero fun c _ => by rw [ind2Term_eq_zero D i p c hbad, mul_zero]

lemma finite_support_gapHullAt (i : Fin (nC D)) : (Function.support (gapHullAt D i)).Finite := by
  refine (((LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol
    (hullOf D (D.thetaPilot (nC D)) i)).union
    ((LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol
      (lgp D (hullOf D (vcI D)) i))).subset ?_
  rw [show gapHullAt D i = _ from funext (gapHullAt_eq D i)]
  exact Function.support_sub _ _

/-- **The gap is the average of the (Ind2)-terms**:
`Δ(D) = (1/ℓ*)·∑_i ∑_p ∑_c w_c·ind2Term(i, p, c)`. With the hull on both sides, the shell
defects and the archimedean defects (which make up the no-hull gap together with the
(Ind2)-terms) cancel. -/
theorem gap_eq : gap D = (∑ i : Fin (nC D), ∑ᶠ vQ, gapHullAt D i vQ) / nC D := by
  unfold gap
  rw [rhs_eq_logVol]
  unfold logVol LogVolumeData.processionVol
  rw [← sub_div, ← Finset.sum_sub_distrib]
  refine congrArg₂ (· / ·) (Finset.sum_congr rfl fun i _ => ?_) rfl
  unfold LogVolumeData.globalVol
  rw [← finsum_sub_distrib ((LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol _)
    ((LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol _)]
  exact finsum_congr fun vQ => (gapHullAt_eq D i vQ).symm

/-- **If the (Ind2)-terms vanish at the bad residue characteristics, the gap vanishes**, and the
Scholze–Stix inequality (with the hull) is the Corollary 3.12 variant. -/
theorem gap_eq_zero_of_ind2Term
    (h : ∀ (i : Fin (nC D)) (p : Nat.Primes) c, (p : ℕ) ∈ D.badChars → ind2Term D i p c = 0) :
    gap D = 0 := by
  rw [gap_eq]
  refine div_eq_zero_iff.mpr (Or.inl (Finset.sum_eq_zero fun i _ => ?_))
  refine finsum_eq_zero_of_forall_eq_zero fun vQ => ?_
  rcases vQ with p | _
  · by_cases hb : (p : ℕ) ∈ D.badChars
    · exact Finset.sum_eq_zero fun c _ => by rw [h i p c hb, mul_zero]
    · exact gapHullAt_eq_zero D i p hb
  · rfl

theorem ss_iff_variant_of_ind2Term
    (h : ∀ (i : Fin (nC D)) (p : Nat.Primes) c, (p : ℕ) ∈ D.badChars → ind2Term D i p c = 0) :
    SSIneq D ↔ Corollary312Variant (concreteVariantData D) :=
  ss_iff_variant_of_gap_eq_zero D (gap_eq_zero_of_ind2Term D h)

/-- **The two gaps, locally**: `Δ_noHull(D) − Δ(D) = log-vol(hull(VC(I))) − log-vol(VC(I))`, the
average of the shell defects and of the archimedean defects (`gapNoHull_eq_gap_add`; the local
form is `logVol_hull_vcI_sub_eq` in `VcI.lean`). In particular `Δ_noHull(D) > 0` for every `D`
(`gapNoHull_pos`), while `Δ(D)` is the average of the (Ind2)-terms only (`gap_eq`). -/
theorem gap_le_gapNoHull_summary :
    0 ≤ gap D ∧ gap D ≤ gapNoHull D ∧ 0 < gapNoHull D :=
  ⟨gap_nonneg D, gap_le_gapNoHull D, gapNoHull_pos D⟩

end

end WallEquiv

end Iut
