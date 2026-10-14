/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.WallEquiv.Gap

/-!
# The log-volume of the log-shell container `VC(I)` and of its hull

Task VCI-CHECK: formulas for `log-vol(VC(I))` (`Wall.vcI`, the right-hand side of the no-hull
wall `Wall.SSIneqNoHull`) and for `log-vol(hull(VC(I)))` (the right-hand side of the Scholze–Stix
inequality `Wall.SSIneq`, after the hull switch) in terms of local data, for
the comparison with IUT III, Proposition 3.9, Corollary 3.12 and IUT IV, Propositions 1.2, 1.4,
Theorem 1.10. The discussion (and what is computed only on paper) is in `VcI.md`.

## Global reduction

* `logVol_vcI_eq`: `log-vol(VC(I)) = (1/ℓ*)·∑_i ∑ᶠ_{v_ℚ} ∑_c w_c·μ^log(VC(I)_{i,v_ℚ,c})`
  (`vcIPacket`); the component is `⊗_j 𝓘_{c j}` (the `ℤ_p`-span of the tensor product of the factor
  log-shells) at a prime, the archimedean log-shell at `∞`. `ssIneqNoHull_iff_packets` restates
  `SSIneqNoHull D` with this right-hand side.
* `logVol_hull_vcI_eq`: the same for `hull(VC(I))` with the components replaced by their least
  hulls `a·O` (`hullPacket`); `ssIneq_iff_packets` restates `SSIneq D` with this right-hand
  side.
* `logVol_hull_vcI_sub_eq`: `log-vol(hull(VC(I))) − log-vol(VC(I))` is the average of the weighted
  sums of the shell defects (`shellDefect`) at the primes and of the archimedean defects
  (`archDefect`) at `∞` (`defectPacket`); `logVol_vcI_le_hull`.
* At a prime: `vcIPacket_finite` (`∑_c w_c·(shellExcess + μ^log(R_I))`), `hullPacket_finite`
  (`∑_c w_c·∑_j ρ_{c j}·log p`, exact); at a tame prime (`IsTamePrime`: `p` odd, every
  `e_w ≤ p − 2`): `vcIPacket_tame`, `hullPacket_tame` (`∑_c w_c·∑_j (1 − 1/e_{c j})·log p`) and
  `defectPacket_tame` (the defect is `−∑_c w_c·μ^log(R_{I,c})`), `defectPacket_tame_le`.

## Local terms at a prime

For a packet `T = ⊗_j K_{c j}` all of whose places lie over `p`, with `R_I = ⊗_{ℤ_p} 𝓞_{c j}`
(`order`), `(R_I)^∼` its normalization (`integral`, the normalizing region of `componentVol`,
IUT IV, Proposition 1.4(i)) and `n = [T : ℚ_p]`:

* **the packet index term** `orderVol p c = μ^log(R_I) = −log[(R_I)^∼ : R_I]/n`:
  `orderVol_nonpos`, `neg_sum_differentExponent_mul_log_le_orderVol`
  (`−d_I·log p ≤ μ^log(R_I) ≤ 0`, from IUT IV, Proposition 1.1), `orderVol_eq_zero` (`0` at odd
  primes unramified in every factor);
* **the shell excess** `shellExcess p c = log(μ(⊗𝓘)/μ(R_I))/n`, the log-volume of `⊗_j 𝓘_{c j}`
  measured against `⊗_j 𝓞_{c j}` instead of the maximal order;
* **the decomposition** `componentVol_tensorLogShell_eq`:
  `μ^log(⊗_j 𝓘_{c j}) = shellExcess p c + orderVol p c` — the identity
  `μ^log(log_p(R_I^×)) = ∑_i μ^log(log_p(R_i^×)) + μ^log(R_I)` of the proof of IUT IV,
  Proposition 1.4(iii), where only `μ^log(R_I) ≤ 0` is used;
* the bounds `neg_sum_ordp_scalA_mul_log_le_shellExcess`,
  `shellExcess_le_neg_sum_ordp_scalB_mul_log` (lattice sandwich `α·R_I ⊆ ⊗𝓘 ⊆ β·R_I`, IUT IV,
  Proposition 1.2(i)), and the same bounds for the hull
  (`componentVol_leastHull_tensorLogShell_ge`, `componentVol_leastHull_tensorLogShell_le`);
* **the exact hull** at every prime: `leastHull_tensorLogShell_eq`
  (`hull(⊗𝓘) = (⊗_j y_j)·(R_I)^∼` for `y_j ∈ 𝓘_{c j}` of maximal norm, which exist:
  `exists_isGreatest_logShellRadius`) and `componentVol_leastHull_tensorLogShell_eq`
  (`μ^log(hull(⊗𝓘)) = ∑_j ρ_{c j}·log p`, `ρ_w = logShellRadius`: `𝓘_w ⊆ p^{−ρ_w}·𝓞_w` sharply);
* **the tame case** (`p` odd, every `e_j ≤ p − 2`): `shellExcess_eq_tame`,
  `componentVol_leastHull_tensorLogShell_eq_tame` (both `∑_j (1 − 1/e_j)·log p`),
  `componentVol_tensorLogShell_eq_tame` and **`shellDefect_eq_neg_orderVol_tame`: the shell defect
  is exactly the packet index term `log[(R_I)^∼ : R_I]/n`**;
* in general `|shellDefect + μ^log(R_I)| ≤ ∑_{j ∈ I*} (3 + log e_j)`
  (`abs_shellDefect_add_orderVol_le`).

Not formalized (stated as named propositions, computed on paper in `VcI.md`): the additivity
`shellExcess = ∑_j λ_j` (`ShellExcessAdditive`, `λ_j = factorShellVol`) and the packet index
formula `μ^log(R_I) = −((m − 1)/2)·d_w·log p` for `K_w^{⊗m}`, `K_w/ℚ_p` Galois
(`PacketIndexFormulaGalois`; in general `−½·(d_I − d_T)·log p`).

## At `∞`

`componentVol_archLogShell_le_leastHull_le`: `μ^log(𝓘_∞) ≤ μ^log(hull 𝓘_∞) ≤ |I|·log(√2·π)`. The
exact values `|I|·log π + ½·log N − log(N!)/(2N)` and `|I|·log π + ½·log N` (`N = 2^{|I|−1}`
complex components) are computed on paper in `VcI.md`.
-/

namespace Iut

open NumberField MeasureTheory PadicLogVolume
open scoped Pointwise

universe u

namespace LocalConstruct

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (p : Nat.Primes) (c : ι → Place K)

/-! ### The packet index term `μ^log(R_I)` -/

/-- **The packet index term** `μ^log(R_I) = −log[(R_I)^∼ : R_I]/[T : ℚ_p]`: the normalized
log-volume of the order `R_I = ⊗_{ℤ_p} 𝓞_{c j}` against its normalization. -/
noncomputable def orderVol : ℝ := componentVol (.finite p) c (order p c)

lemma haar_order_pos : 0 < haar (.finite p) c (order p c) :=
  (isOpen_order p c).measure_pos _ ⟨1, one_mem_order p c⟩

lemma haar_order_lt_top : haar (.finite p) c (order p c) < ⊤ :=
  (isCompact_order p c).measure_lt_top

/-- `μ^log(R_I) ≤ 0` (`R_I ⊆ (R_I)^∼`). -/
theorem orderVol_nonpos : orderVol p c ≤ 0 := by
  have h := componentVol_le_of_subset (order_subset_integral p c) (haar_order_pos p c)
    (haar_integralAt_lt_top (vQ := .finite p) (c := c))
  exact h.trans_eq (componentVol_integral (vQ := .finite p) (c := c))

variable {p c}

/-- **`μ^log(R_I) ≥ −d_I·log p`** (IUT IV, Proposition 1.1: `p^{d_I}·(R_I)^∼ ⊆ R_I`, realized by
the local different elements, `exists_local_different_elt`). -/
theorem neg_sum_differentExponent_mul_log_le_orderVol (hc : ∀ j, IsOver K p (c j)) :
    -(∑ j, differentExponent K (finPart K (c j))) * Real.log p ≤ orderVol p c := by
  classical
  have hWi : ∀ j, c j = Place.finite (finPart K (c j)) := hW hc
  have hδ := fun j => exists_local_different_elt (p := (p : ℕ)) (hres hc j)
  choose δ hδ0 hδord hδdual using hδ
  have hz : IsUnit (∏ j, incl p c j (finPart K (c j)) (hWi j) (δ j)) :=
    isUnit_prod_incl _ hWi δ hδ0
  have hsub : (∏ j, incl p c j (finPart K (c j)) (hWi j) (δ j)) • integral p c ⊆ order p c := by
    rintro _ ⟨x, hx, rfl⟩
    exact prod_incl_mul_mem_order_of_mem_integral p c hc _ hWi δ
      (fun i yy hyy => hδdual i yy hyy) x hx
  have h1 := componentVol_le_of_subset hsub (haar_smul_integralAt_pos (vQ := .finite p) hz)
    (haar_order_lt_top p c)
  have h2 := componentVol_prod_incl_smul_integral hc _ hWi δ hδ0
  have h3 : (∑ j, ordp K (finPart K (c j)) (δ j)) =
      ∑ j, differentExponent K (finPart K (c j)) :=
    Finset.sum_congr rfl fun j _ => hδord j
  change componentVol (.finite p) c (_ • integralAt (.finite p) c) ≤ _ at h1
  change componentVol (.finite p) c (_ • integralAt (.finite p) c) = _ at h2
  rw [h2, h3] at h1
  exact h1

/-- `μ^log(R_I) = 0` at an odd prime unramified in every factor (`R_I = (R_I)^∼`). -/
theorem orderVol_eq_zero (hc : ∀ j, IsOver K p (c j))
    (hunr : ∀ j w, c j = Place.finite w → ramIdx K w = 1) : orderVol p c = 0 := by
  unfold orderVol
  rw [← integral_eq_order_of_unramified p c hc hunr]
  exact componentVol_integral (vQ := .finite p) (c := c)

/-! ### The shell excess and the decomposition of `μ^log(⊗𝓘)` -/

variable (p c)

lemma haar_tensorLogShell_pos : 0 < haar (.finite p) c (tensorLogShell p c) := by
  have h := (smul_tensorLogShell_bounded_open_pos p c 1 isUnit_one).2.2
  rwa [one_smul] at h

lemma haar_tensorLogShell_lt_top : haar (.finite p) c (tensorLogShell p c) < ⊤ := by
  have h := (smul_tensorLogShell_bounded_open_pos p c 1 isUnit_one).1
  rw [one_smul] at h
  exact h.measure_lt_top

/-- **The shell excess** `log(μ(⊗_j 𝓘_{c j})/μ(R_I))/[T : ℚ_p]`: the log-volume of the tensor
product of the log-shells measured against `R_I = ⊗_j 𝓞_{c j}` (the "product measure"), rather
than against the maximal order. On paper it is `∑_j λ_j`, `λ_j` the normalized log-volume of the
factor log-shell (`ShellExcessAdditive`). -/
noncomputable def shellExcess : ℝ :=
  Real.log ((haar (.finite p) c (tensorLogShell p c)).toReal /
      (haar (.finite p) c (order p c)).toReal) /
    Module.finrank (baseField (.finite p)) (Tensor K (.finite p) c)

/-- **`μ^log(⊗_j 𝓘_{c j}) = shellExcess + μ^log(R_I)`** (the decomposition in the proof of
IUT IV, Proposition 1.4(iii)). -/
theorem componentVol_tensorLogShell_eq :
    componentVol (.finite p) c (tensorLogShell p c) = shellExcess p c + orderVol p c := by
  unfold shellExcess orderVol componentVol
  have hS := ENNReal.toReal_pos (haar_tensorLogShell_pos p c).ne'
    (haar_tensorLogShell_lt_top p c).ne
  have hR := ENNReal.toReal_pos (haar_order_pos p c).ne' (haar_order_lt_top p c).ne
  have hO := toReal_haar_integralAt_pos (vQ := .finite p) (c := c)
  rw [← add_div, ← Real.log_mul (div_pos hS hR).ne' (div_pos hR hO).ne']
  congr 2
  field_simp

variable {p c}

/-- Multiplication by a unit scales the Haar measure by a positive finite factor. -/
lemma haar_isUnit_smul_pos_iff {a : Tensor K (.finite p) c} (ha : IsUnit a)
    {S : Set (Tensor K (.finite p) c)} (hS : 0 < haar (.finite p) c S) :
    0 < haar (.finite p) c (a • S) := by
  obtain ⟨u, rfl⟩ := ha
  rw [haar_units_smul]
  exact ENNReal.mul_pos (by simpa using (distribHaarChar_pos (g := u)).ne') hS.ne'

lemma haar_isUnit_smul_lt_top {a : Tensor K (.finite p) c} (ha : IsUnit a)
    {S : Set (Tensor K (.finite p) c)} (hS : haar (.finite p) c S < ⊤) :
    haar (.finite p) c (a • S) < ⊤ := by
  obtain ⟨u, rfl⟩ := ha
  rw [haar_units_smul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hS

/-- `μ^log(a·R_I) = μ^log(a·(R_I)^∼) + μ^log(R_I)` for a unit `a`. -/
lemma componentVol_units_smul_order {a : Tensor K (.finite p) c} (ha : IsUnit a) :
    componentVol (.finite p) c (a • order p c) =
      componentVol (.finite p) c (a • integralAt (.finite p) c) + orderVol p c :=
  componentVol_units_smul ha (haar_order_pos p c) (haar_order_lt_top p c)

/-- The scalar `α = ∏_j incl_j((2p)⁻¹ϖ_{a,j})` of the lattice sandwich. -/
noncomputable abbrev scalAProd (hc : ∀ j, IsOver K p (c j)) : Tensor K (.finite p) c :=
  ∏ j, incl p c j (finPart K (c j)) (hW hc j) (scalA c j)

/-- The scalar `β = ∏_j incl_j((2p)⁻¹ϖ_{b,j})` of the lattice sandwich. -/
noncomputable abbrev scalBProd (hc : ∀ j, IsOver K p (c j)) : Tensor K (.finite p) c :=
  ∏ j, incl p c j (finPart K (c j)) (hW hc j) (scalB c j)

lemma isUnit_scalAProd (hc : ∀ j, IsOver K p (c j)) : IsUnit (scalAProd hc) :=
  isUnit_prod_incl _ (hW hc) _ (scalA_ne_zero c)

lemma isUnit_scalBProd (hc : ∀ j, IsOver K p (c j)) : IsUnit (scalBProd hc) :=
  isUnit_prod_incl _ (hW hc) _ (scalB_ne_zero c)

lemma componentVol_scalAProd (hc : ∀ j, IsOver K p (c j)) :
    componentVol (.finite p) c (scalAProd hc • integralAt (.finite p) c) =
      -(∑ j, ordp K (finPart K (c j)) (scalA c j)) * Real.log p :=
  componentVol_prod_incl_smul_integral hc _ (hW hc) _ (scalA_ne_zero c)

lemma componentVol_scalBProd (hc : ∀ j, IsOver K p (c j)) :
    componentVol (.finite p) c (scalBProd hc • integralAt (.finite p) c) =
      -(∑ j, ordp K (finPart K (c j)) (scalB c j)) * Real.log p :=
  componentVol_prod_incl_smul_integral hc _ (hW hc) _ (scalB_ne_zero c)

/-- `α·R_I ⊆ ⊗_j 𝓘_{c j}` (IUT IV, Proposition 1.2(i)). -/
lemma scalAProd_smul_order_subset (hc : ∀ j, IsOver K p (c j)) :
    scalAProd hc • order p c ⊆ tensorLogShell p c := by
  rintro _ ⟨r, hr, rfl⟩
  change scalAProd hc * r ∈ _
  rw [scalAProd, prod_incl_eq_tprod hc]
  exact tprod_scalA_mul_mem_tensorLogShell hc hr

/-- `⊗_j 𝓘_{c j} ⊆ β·R_I` (IUT IV, Proposition 1.2(i)). -/
lemma tensorLogShell_subset_scalBProd_smul_order (hc : ∀ j, IsOver K p (c j)) :
    tensorLogShell p c ⊆ scalBProd hc • order p c := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := exists_mem_order_of_mem_tensorLogShell hc hx
  refine ⟨r, hr, ?_⟩
  change scalBProd hc * r = _
  rw [scalBProd, prod_incl_eq_tprod hc]

/-- **Lower bound for the shell excess**: `shellExcess ≥ −ord_p(α)·log p`. -/
theorem neg_sum_ordp_scalA_mul_log_le_shellExcess (hc : ∀ j, IsOver K p (c j)) :
    -(∑ j, ordp K (finPart K (c j)) (scalA c j)) * Real.log p ≤ shellExcess p c := by
  have h := componentVol_le_of_subset (scalAProd_smul_order_subset hc)
    (haar_isUnit_smul_pos_iff (isUnit_scalAProd hc) (haar_order_pos p c))
    (haar_tensorLogShell_lt_top p c)
  rw [componentVol_units_smul_order (isUnit_scalAProd hc), componentVol_scalAProd,
    componentVol_tensorLogShell_eq] at h
  linarith

/-- **Upper bound for the shell excess**: `shellExcess ≤ −ord_p(β)·log p`. -/
theorem shellExcess_le_neg_sum_ordp_scalB_mul_log (hc : ∀ j, IsOver K p (c j)) :
    shellExcess p c ≤ -(∑ j, ordp K (finPart K (c j)) (scalB c j)) * Real.log p := by
  have h := componentVol_le_of_subset (tensorLogShell_subset_scalBProd_smul_order hc)
    (haar_tensorLogShell_pos p c)
    (haar_isUnit_smul_lt_top (isUnit_scalBProd hc) (haar_order_lt_top p c))
  rw [componentVol_units_smul_order (isUnit_scalBProd hc), componentVol_scalBProd,
    componentVol_tensorLogShell_eq] at h
  linarith

/-! ### The hull of `⊗𝓘` -/

variable (p c) in
/-- `R_I` is admissible. -/
lemma order_admissible : order p c ∈ admissible (.finite p) c :=
  ⟨⟨1, one_mem_order p c⟩, isCompact_closure_order p c, (isClosed_order p c).measurableSet,
    haar_order_pos p c, haar_order_lt_top p c⟩

variable (p c) in
/-- **The least hull of `R_I` is `(R_I)^∼`**: a region `b·(R_I)^∼` containing `1` contains
`(R_I)^∼`. -/
lemma leastHull_order :
    LocalTheory.leastHull (.finite p) c (order p c) = integralAt (.finite p) c := by
  have h := LocalTheory.leastHull_eq (vQ := .finite p) (c := c) (U := order p c) isUnit_one
    (by rw [one_smul]; exact order_subset_integral p c) fun b _ hb => by
      rw [one_smul]
      obtain ⟨o, ho, hbo⟩ := hb (one_mem_order p c)
      change b * o = 1 at hbo
      intro x hx
      refine ⟨o * x, mul_mem_integral p c ho hx, ?_⟩
      change b * (o * x) = x
      rw [← mul_assoc, hbo, one_mul]
  rw [one_smul] at h
  exact h

/-- **Lower bound for the hull**: `μ^log(hull(⊗𝓘)) ≥ −ord_p(α)·log p`. -/
theorem componentVol_leastHull_tensorLogShell_ge (hc : ∀ j, IsOver K p (c j)) :
    -(∑ j, ordp K (finPart K (c j)) (scalA c j)) * Real.log p ≤
      componentVol (.finite p) c (LocalTheory.leastHull (.finite p) c (tensorLogShell p c)) := by
  have hadm := LocalTheory.shell_admissible (K := K) p c
  have h1 : LocalTheory.leastHull (.finite p) c (scalAProd hc • order p c) ⊆
      LocalTheory.leastHull (.finite p) c (tensorLogShell p c) :=
    LocalTheory.leastHull_mono (scalAProd_smul_order_subset hc) hadm
  rw [LocalTheory.leastHull_units_smul (isUnit_scalAProd hc) (order_admissible p c),
    leastHull_order] at h1
  rw [← componentVol_scalAProd hc]
  exact componentVol_le_of_subset h1 (haar_smul_integralAt_pos (isUnit_scalAProd hc))
    (admissible_haar_lt_top (LocalTheory.leastHull_admissible hadm))

/-- **Upper bound for the hull**: `μ^log(hull(⊗𝓘)) ≤ −ord_p(β)·log p`. -/
theorem componentVol_leastHull_tensorLogShell_le (hc : ∀ j, IsOver K p (c j)) :
    componentVol (.finite p) c (LocalTheory.leastHull (.finite p) c (tensorLogShell p c)) ≤
      -(∑ j, ordp K (finPart K (c j)) (scalB c j)) * Real.log p := by
  have hadm := LocalTheory.shell_admissible (K := K) p c
  have h1 : LocalTheory.leastHull (.finite p) c (tensorLogShell p c) ⊆
      scalBProd hc • integralAt (.finite p) c :=
    LocalTheory.leastHull_subset (isUnit_scalBProd hc)
      ((tensorLogShell_subset_scalBProd_smul_order hc).trans
        (Set.smul_set_mono (order_subset_integral p c)))
  rw [← componentVol_scalBProd hc]
  exact componentVol_le_of_subset h1 (admissible_haar_pos (LocalTheory.leastHull_admissible hadm))
    (haar_smul_integralAt_lt_top _)

/-- **The shell defect is the packet index term up to the log-lattice slack**:
`|shellDefect + μ^log(R_I)| ≤ ∑_j (a_j + b_j)·log p ≤ ∑_{j ∈ I*} (3 + log e_j)` (both
`μ^log(hull(⊗𝓘))` and the shell excess lie in `[−ord_p(α)·log p, −ord_p(β)·log p]`). -/
theorem abs_shellDefect_add_orderVol_le (hc : ∀ j, IsOver K p (c j)) :
    |LocalTheory.shellDefect p c + orderVol p c| ≤
      ∑ j, if (p : ℕ) - 2 < ramIdx K (finPart K (c j)) then
        3 + Real.log (ramIdx K (finPart K (c j))) else 0 := by
  have hsub : ∀ j, ordp K (finPart K (c j)) (scalA c j) - ordp K (finPart K (c j)) (scalB c j) =
      logLatticeA (residueChar (finPart K (c j))) (ramIdx K (finPart K (c j))) +
        logLatticeB (residueChar (finPart K (c j))) (ramIdx K (finPart K (c j))) :=
    fun j => ordp_scalA_sub_scalB c j
  have hterm := fun j => logLattice_term_le p (finPart K (c j)) (hres hc j)
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
  simp only [← hsub] at hsum
  rw [← Finset.sum_mul, Finset.sum_sub_distrib] at hsum
  have hdef : LocalTheory.shellDefect p c + orderVol p c =
      componentVol (.finite p) c (LocalTheory.leastHull (.finite p) c (tensorLogShell p c)) -
        shellExcess p c := by
    unfold LocalTheory.shellDefect
    change _ - componentVol (.finite p) c (tensorLogShell p c) + _ = _
    rw [componentVol_tensorLogShell_eq]
    ring
  rw [hdef, abs_le]
  have h1 := componentVol_leastHull_tensorLogShell_ge hc
  have h2 := componentVol_leastHull_tensorLogShell_le hc
  have h3 := neg_sum_ordp_scalA_mul_log_le_shellExcess hc
  have h4 := shellExcess_le_neg_sum_ordp_scalB_mul_log hc
  constructor <;> nlinarith

/-! ### The tame case: `p` odd, every `e_j ≤ p − 2` -/

omit [Fintype ι] in
/-- In the tame case `ord_p((2p)⁻¹ϖ_a) = 1/e − 1`. -/
lemma ordp_scalA_tame (hc : ∀ j, IsOver K p (c j)) (hodd : Odd (p : ℕ))
    (j : ι) (he : ramIdx K (finPart K (c j)) ≤ (p : ℕ) - 2) :
    ordp K (finPart K (c j)) (scalA c j) = (ramIdx K (finPart K (c j)) : ℝ)⁻¹ - 1 := by
  set w := finPart K (c j)
  have hw : residueChar w = p := hres hc j
  have hp0 := residueChar_ne_zero' w
  have h2 : (2 : completionAt K w) ≠ 0 := two_ne_zero
  have h2p : (2 * ((residueChar w : ℕ) : completionAt K w)) ≠ 0 := mul_ne_zero h2 hp0
  have hpk : ‖((p : ℕ) : completionAt K w)‖ < 1 := norm_natCast_lt_one_completion hw
  have hn2 : ‖(2 : completionAt K w)‖ = 1 := norm_two_eq_one p.2 hpk hodd
  have hord2 : ordp K w 2 = 0 := by
    unfold ordp
    rw [hn2, Real.log_one, neg_zero, zero_div]
  have hepos : 0 < ramIdx K w := ramIdx_pos' w
  have hp3 : 3 ≤ (p : ℕ) := by
    rcases hodd with ⟨k, hk⟩
    have := p.2.two_le
    omega
  have hA : logLatticeA (residueChar w) (ramIdx K w) = (ramIdx K w : ℝ)⁻¹ := by
    rw [hw, logLatticeA, if_neg (by omega)]
    have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      linarith
    have hle : (ramIdx K w : ℝ) ≤ (p : ℝ) - 2 := by
      have : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [← this]
      exact_mod_cast he
    have hceil : ⌈(ramIdx K w : ℝ) / ((p : ℝ) - 2)⌉ = 1 := by
      rw [Int.ceil_eq_iff]
      constructor
      · norm_num
        exact div_pos (by exact_mod_cast hepos) hp2
      · norm_num
        exact (div_le_one hp2).mpr hle
    rw [hceil]
    simp
  unfold scalA
  change ordp K w ((2 * ((residueChar w : ℕ) : completionAt K w))⁻¹ * varpiA w) = _
  rw [ordp_mul _ _ _ (inv_ne_zero h2p) (varpiA_ne_zero w), ordp_inv,
    ordp_mul _ _ _ h2 hp0, hord2, ordp_residueChar, ordp_varpiA, hA]
  ring

omit [Fintype ι] in
/-- In the tame case `ord_p((2p)⁻¹ϖ_b) = ord_p((2p)⁻¹ϖ_a)` (`a = −b`, IUT IV,
Proposition 1.2(i)). -/
lemma ordp_scalB_tame (hc : ∀ j, IsOver K p (c j)) (hodd : Odd (p : ℕ))
    (j : ι) (he : ramIdx K (finPart K (c j)) ≤ (p : ℕ) - 2) :
    ordp K (finPart K (c j)) (scalB c j) = ordp K (finPart K (c j)) (scalA c j) := by
  have hw : residueChar (finPart K (c j)) = p := hres hc j
  have h := ordp_scalA_sub_scalB c j
  have hp2 : (p : ℕ) ≠ 2 := by
    rintro h2
    rw [h2] at hodd
    exact absurd hodd (by decide)
  rw [hw, logLatticeA_add_B_eq_zero hp2 (ramIdx_pos' _) he] at h
  linarith

/-- The common value `−ord_p(α)·log p = ∑_j (1 − 1/e_j)·log p` in the tame case. -/
lemma neg_sum_ordp_scalA_tame (hc : ∀ j, IsOver K p (c j)) (hodd : Odd (p : ℕ))
    (he : ∀ j, ramIdx K (finPart K (c j)) ≤ (p : ℕ) - 2) :
    -(∑ j, ordp K (finPart K (c j)) (scalA c j)) * Real.log p =
      ∑ j, (1 - (ramIdx K (finPart K (c j)) : ℝ)⁻¹) * Real.log p := by
  rw [← Finset.sum_neg_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ordp_scalA_tame hc hodd j (he j)]
  ring

/-- **The shell excess in the tame case**: `∑_j (1 − 1/e_j)·log p`. -/
theorem shellExcess_eq_tame (hc : ∀ j, IsOver K p (c j)) (hodd : Odd (p : ℕ))
    (he : ∀ j, ramIdx K (finPart K (c j)) ≤ (p : ℕ) - 2) :
    shellExcess p c = ∑ j, (1 - (ramIdx K (finPart K (c j)) : ℝ)⁻¹) * Real.log p := by
  have h1 := neg_sum_ordp_scalA_mul_log_le_shellExcess hc
  have h2 := shellExcess_le_neg_sum_ordp_scalB_mul_log hc
  have hB : (∑ j, ordp K (finPart K (c j)) (scalB c j)) =
      ∑ j, ordp K (finPart K (c j)) (scalA c j) :=
    Finset.sum_congr rfl fun j _ => ordp_scalB_tame hc hodd j (he j)
  rw [hB] at h2
  rw [← neg_sum_ordp_scalA_tame hc hodd he]
  exact le_antisymm h2 h1

/-- **`μ^log(⊗𝓘)` in the tame case**: `∑_j (1 − 1/e_j)·log p + μ^log(R_I)`. -/
theorem componentVol_tensorLogShell_eq_tame (hc : ∀ j, IsOver K p (c j)) (hodd : Odd (p : ℕ))
    (he : ∀ j, ramIdx K (finPart K (c j)) ≤ (p : ℕ) - 2) :
    componentVol (.finite p) c (tensorLogShell p c) =
      ∑ j, (1 - (ramIdx K (finPart K (c j)) : ℝ)⁻¹) * Real.log p + orderVol p c := by
  rw [componentVol_tensorLogShell_eq, shellExcess_eq_tame hc hodd he]

/-- **`μ^log(hull(⊗𝓘))` in the tame case**: `∑_j (1 − 1/e_j)·log p` (`= d_I·log p`, the
different exponent of a tamely ramified extension being `1 − 1/e`, IUT IV, Proposition 1.3(i)). -/
theorem componentVol_leastHull_tensorLogShell_eq_tame (hc : ∀ j, IsOver K p (c j))
    (hodd : Odd (p : ℕ)) (he : ∀ j, ramIdx K (finPart K (c j)) ≤ (p : ℕ) - 2) :
    componentVol (.finite p) c (LocalTheory.leastHull (.finite p) c (tensorLogShell p c)) =
      ∑ j, (1 - (ramIdx K (finPart K (c j)) : ℝ)⁻¹) * Real.log p := by
  have h1 := componentVol_leastHull_tensorLogShell_ge hc
  have h2 := componentVol_leastHull_tensorLogShell_le hc
  have hB : (∑ j, ordp K (finPart K (c j)) (scalB c j)) =
      ∑ j, ordp K (finPart K (c j)) (scalA c j) :=
    Finset.sum_congr rfl fun j _ => ordp_scalB_tame hc hodd j (he j)
  rw [hB] at h2
  rw [← neg_sum_ordp_scalA_tame hc hodd he]
  exact le_antisymm h2 h1

/-- **In the tame case the shell defect is exactly the packet index term**:
`shellDefect = −μ^log(R_I) = log[(R_I)^∼ : R_I]/[T : ℚ_p]`. -/
theorem shellDefect_eq_neg_orderVol_tame (hc : ∀ j, IsOver K p (c j)) (hodd : Odd (p : ℕ))
    (he : ∀ j, ramIdx K (finPart K (c j)) ≤ (p : ℕ) - 2) :
    LocalTheory.shellDefect p c = -orderVol p c := by
  unfold LocalTheory.shellDefect
  change componentVol (.finite p) c (LocalTheory.leastHull (.finite p) c (tensorLogShell p c)) -
    componentVol (.finite p) c (tensorLogShell p c) = _
  rw [componentVol_leastHull_tensorLogShell_eq_tame hc hodd he,
    componentVol_tensorLogShell_eq_tame hc hodd he]
  ring

/-! ### The exact hull of `⊗𝓘` at every prime -/

/-- **The radius of a log-shell**: `ρ_w = −min{ord_p z | z ∈ 𝓘_w, z ≠ 0}` (as a supremum), so that
`𝓘_w ⊆ p^{−ρ_w}·𝓞_w` is the least such fractional ideal (`exists_isGreatest_logShellRadius`). -/
noncomputable def logShellRadius (w : FinitePlace K) (p : ℕ) : ℝ :=
  sSup ((fun z => -ordp K w z) '' {z | z ∈ Iut.logShell (completionAt K w) p ∧ z ≠ 0})

/-- **The log-shell of a completion has an element of maximal norm**, and its `−ord_p` is the
radius of the log-shell. -/
theorem exists_isGreatest_logShellRadius {w : FinitePlace K} (hw : residueChar w = p) :
    ∃ y ∈ Iut.logShell (completionAt K w) p, y ≠ 0 ∧
      (∀ z ∈ Iut.logShell (completionAt K w) p, ‖z‖ ≤ ‖y‖) ∧
      logShellRadius w p = -ordp K w y := by
  classical
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  set S := Iut.logShell (completionAt K w) p
  have hpk : ‖((p : ℕ) : completionAt K w)‖ < 1 := norm_natCast_lt_one_completion hw
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (logShell_isBounded p.2 hpk)
  have h1 : (1 : completionAt K w) ∈ S :=
    closedBall_subset_logShell p.2 hpk (by simp)
  have hD : 0 < (localDeg K w : ℝ) * Real.log (residueChar w) :=
    mul_pos (by exact_mod_cast localDeg_pos w)
      (Real.log_pos (by exact_mod_cast (residueChar_prime w).one_lt))
  have hint : ∀ z : completionAt K w, z ≠ 0 → ∃ n : ℤ, (n : ℝ) = ramIdx K w * ordp K w z :=
    fun z hz => by
      obtain ⟨n, hn, -⟩ := exists_pow_eq_zpow_mul (p := (p : ℕ)) hw hz (dvd_refl _)
      exact ⟨n, by rw [hn]⟩
  have hbd : ∀ z ∈ S, z ≠ 0 → -Real.log (max M 1) / ((localDeg K w : ℝ) *
      Real.log (residueChar w)) ≤ ordp K w z := by
    intro z hz hz0
    unfold ordp
    refine div_le_div_of_nonneg_right ?_ hD.le
    have := Real.log_le_log (norm_pos_iff.mpr hz0) ((hM z hz).trans (le_max_left M 1))
    linarith
  set A : Set ℤ := {n | ∃ z ∈ S, z ≠ 0 ∧ (n : ℝ) = ramIdx K w * ordp K w z}
  have hord1 : ordp K w 1 = 0 := by unfold ordp; simp
  have hA : A.Nonempty := ⟨0, 1, h1, one_ne_zero, by rw [hord1]; simp⟩
  have he : (0 : ℝ) < ramIdx K w := by exact_mod_cast ramIdx_pos' w
  obtain ⟨b, hb⟩ : ∃ b : ℤ, ∀ n ∈ A, b ≤ n := by
    refine ⟨⌊(ramIdx K w : ℝ) * (-Real.log (max M 1) / ((localDeg K w : ℝ) *
      Real.log (residueChar w)))⌋, fun n ⟨z, hz, hz0, hn⟩ => ?_⟩
    have h' : (ramIdx K w : ℝ) * (-Real.log (max M 1) / ((localDeg K w : ℝ) *
        Real.log (residueChar w))) ≤ (n : ℝ) := by
      rw [hn]
      exact mul_le_mul_of_nonneg_left (hbd z hz hz0) he.le
    exact_mod_cast (Int.floor_le _).trans h'
  obtain ⟨n₀, ⟨y, hy, hy0, hn₀⟩, hleast⟩ := Int.exists_least_of_bdd ⟨b, hb⟩ hA
  have hmin : ∀ z ∈ S, z ≠ 0 → ordp K w y ≤ ordp K w z := by
    intro z hz hz0
    obtain ⟨n, hn⟩ := hint z hz0
    have := hleast n ⟨z, hz, hz0, hn⟩
    have h' : (n₀ : ℝ) ≤ n := by exact_mod_cast this
    rw [hn₀, hn] at h'
    exact le_of_mul_le_mul_left h' he
  have hpw := norm_residueChar_pos w
  have hpw1 := norm_residueChar_lt_one w
  have hnorm : ∀ z ∈ S, ‖z‖ ≤ ‖y‖ := by
    intro z hz
    by_cases hz0 : z = 0
    · rw [hz0, norm_zero]; exact norm_nonneg _
    · rw [norm_eq_rpow_ordp w hz0, norm_eq_rpow_ordp w hy0]
      exact Real.rpow_le_rpow_of_exponent_ge hpw hpw1.le (hmin z hz hz0)
  refine ⟨y, hy, hy0, hnorm, ?_⟩
  refine IsGreatest.csSup_eq ⟨⟨y, ⟨hy, hy0⟩, rfl⟩, ?_⟩
  rintro _ ⟨z, ⟨hz, hz0⟩, rfl⟩
  exact neg_le_neg (hmin z hz hz0)

/-- **The least hull of `⊗𝓘` at every prime**: if `y_j ∈ 𝓘_{c j}` has maximal norm, then
`hull(⊗_j 𝓘_{c j}) = (⊗_j y_j)·(R_I)^∼`. -/
theorem leastHull_tensorLogShell_eq (hc : ∀ j, IsOver K p (c j))
    (y : ∀ j, completionAt K (finPart K (c j))) (hy0 : ∀ j, y j ≠ 0)
    (hy : ∀ j, y j ∈ Iut.logShell (completionAt K (finPart K (c j))) p)
    (hmax : ∀ j, ∀ z ∈ Iut.logShell (completionAt K (finPart K (c j))) p, ‖z‖ ≤ ‖y j‖) :
    LocalTheory.leastHull (.finite p) c (tensorLogShell p c) =
      (∏ j, incl p c j (finPart K (c j)) (hW hc j) (y j)) • integralAt (.finite p) c := by
  classical
  set Y := ∏ j, incl p c j (finPart K (c j)) (hW hc j) (y j)
  have hYu : IsUnit Y := isUnit_prod_incl _ (hW hc) y hy0
  have hYmem : Y ∈ tensorLogShell p c := by
    change Y ∈ Submodule.span ℤ_[p] (logShellSet p c)
    refine Submodule.subset_span ⟨fun j => ⟨factorMk p (c j) (y j), y j, hy j, rfl⟩, ?_⟩
    exact (prod_incl_eq_tprod hc y).symm
  let N : Submodule ℤ_[p] (Tensor K (.finite p) c) :=
    { carrier := {x | ∃ r ∈ integral p c, x = Y * r}
      add_mem' := by
        rintro _ _ ⟨r, hr, rfl⟩ ⟨r', hr', rfl⟩
        exact ⟨r + r', (integralClosure ℤ_[p] (Tensor K (.finite p) c)).add_mem hr hr',
          (mul_add _ _ _).symm⟩
      zero_mem' := ⟨0, (integralClosure ℤ_[p] (Tensor K (.finite p) c)).zero_mem,
        (mul_zero _).symm⟩
      smul_mem' := by
        rintro t _ ⟨r, hr, rfl⟩
        exact ⟨t • r, (integralClosure ℤ_[p] (Tensor K (.finite p) c)).smul_mem hr t,
          (Algebra.mul_smul_comm t Y r).symm⟩ }
  have hle : tensorLogShell p c ⊆ (N : Set (Tensor K (.finite p) c)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    have hz : ∀ j, ∃ z ∈ Iut.logShell (completionAt K (finPart K (c j))) p,
        factorMk p (c j) z = a j := fun j => (a j).2
    choose z hz hza using hz
    have htp : (PiTensorProduct.tprod ℚ_[p] fun j => (a j : Factor K p (c j))) =
        ∏ j, incl p c j (finPart K (c j)) (hW hc j) (z j) := by
      rw [prod_incl_eq_tprod hc]
      congr 1
      funext j
      exact (hza j).symm
    change (PiTensorProduct.tprod ℚ_[p] fun j => (a j : Factor K p (c j))) ∈ N
    rw [htp]
    by_cases h0 : ∃ j, z j = 0
    · obtain ⟨j, hj⟩ := h0
      refine ⟨0, (integralClosure ℤ_[p] (Tensor K (.finite p) c)).zero_mem, ?_⟩
      rw [mul_zero]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, map_zero])
    · push Not at h0
      have hq0 : ∀ j, z j / y j ≠ 0 := fun j => div_ne_zero (h0 j) (hy0 j)
      refine ⟨∏ j, incl p c j (finPart K (c j)) (hW hc j) (z j / y j),
        prod_incl_mem_integral hc _ (hW hc) _ hq0
          (Finset.sum_nonneg fun j _ => ?_), ?_⟩
      · have hle1 : ‖z j / y j‖ ≤ 1 := by
          rw [norm_div, div_le_one (norm_pos_iff.mpr (hy0 j))]
          exact hmax j (z j) (hz j)
        unfold ordp
        refine div_nonneg ?_ (mul_pos (by exact_mod_cast localDeg_pos _)
          (Real.log_pos (by exact_mod_cast (residueChar_prime _).one_lt))).le
        have := Real.log_nonpos (norm_nonneg _) hle1
        linarith
      · rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← map_mul, mul_div_cancel₀ _ (hy0 j)]
  have hsub : tensorLogShell p c ⊆ Y • integralAt (.finite p) c := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hle hx
    exact ⟨r, hr, rfl⟩
  refine LocalTheory.leastHull_eq hYu hsub fun b _ hb => ?_
  obtain ⟨o, ho, hbo⟩ := hb hYmem
  change b * o = Y at hbo
  rintro _ ⟨r, hr, rfl⟩
  refine ⟨o * r, mul_mem_integral p c ho hr, ?_⟩
  change b * (o * r) = Y * r
  rw [← mul_assoc, hbo]

/-- **The exact log-volume of the hull of `⊗𝓘` at every prime**:
`μ^log(hull(⊗_j 𝓘_{c j})) = ∑_j ρ_{c j}·log p`, `ρ` the radius of the factor log-shell. -/
theorem componentVol_leastHull_tensorLogShell_eq (hc : ∀ j, IsOver K p (c j)) :
    componentVol (.finite p) c (LocalTheory.leastHull (.finite p) c (tensorLogShell p c)) =
      ∑ j, logShellRadius (finPart K (c j)) p * Real.log p := by
  choose y hy hy0 hmax hrad using fun j =>
    exists_isGreatest_logShellRadius (K := K) (p := p) (hres hc j)
  have h2 := componentVol_prod_incl_smul_integral hc _ (hW hc) y hy0
  change componentVol (.finite p) c (_ • integralAt (.finite p) c) = _ at h2
  rw [leastHull_tensorLogShell_eq hc y hy0 hy hmax, h2, ← Finset.sum_neg_distrib,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [hrad j]

/-! ### The remaining identifications (named, not proved here) -/

/-- **The normalized log-volume of the log-shell of a factor**
`λ_w = log(μ(𝓘_w)/μ(𝓞_w))/[K_w : ℚ_p]` (any Haar measure `μ` on `K_w`). Its value is
`(log p/e)·logShellConst p f e m = log p* − (1/e + m/[K_w : ℚ_p])·log p`
(`Reconstruction.logVolume_logShell_completionAt`, [AbsTopIII], Proposition 5.8(iii); IUT IV,
Proposition 1.4(ii) up to the factor `(2p)⁻¹`). -/
noncomputable def factorShellVol (w : FinitePlace K) (p : ℕ) : ℝ :=
  letI : MeasurableSpace (completionAt K w) := borel _
  haveI : BorelSpace (completionAt K w) := ⟨rfl⟩
  Real.log ((Measure.addHaar (Iut.logShell (completionAt K w) p)).toReal /
      (Measure.addHaar (Metric.closedBall (0 : completionAt K w) 1)).toReal) / localDeg K w

/-- **Additivity of the shell excess** (not proved here): the log-volume of `⊗_{ℤ_p} 𝓘_j`
against `⊗_{ℤ_p} 𝓞_j` is the sum of the factor log-volumes `λ_j` (multiplicativity of
determinants: `det(⊗_j g_j) = ∏_j det(g_j)^{n/n_j}` for `𝓘_j = g_j(𝓞_j)`). In the tame case both
sides are `∑_j (1 − 1/e_j)·log p` (`shellExcess_eq_tame`; on paper for the right-hand side). -/
def ShellExcessAdditive (p : Nat.Primes) (c : ι → Place K) : Prop :=
  shellExcess p c = ∑ j, factorShellVol (finPart K (c j)) p

/-- **The packet index formula in the Galois case** (not proved here): for the packet
`K_w^{⊗m}` with `K_w/ℚ_p` Galois (so `K_w^{⊗m} ≅ K_w^{n^{m−1}}`, `n = [K_w : ℚ_p]`),
`μ^log(R_I) = −((m − 1)/2)·d_w·log p`, from `disc(⊗^m 𝓞_w) = disc(𝓞_w)^{m·n^{m−1}}` against
`disc(𝓞_w^{n^{m−1}}) = disc(𝓞_w)^{n^{m−1}}`. In general
`μ^log(R_I) = −½·(d_I − d_T)·log p`, `d_T` the weighted average of the different exponents of
the field factors of `T`. -/
def PacketIndexFormulaGalois (p : Nat.Primes) (w : FinitePlace K) (hw : residueChar w = p)
    (m : ℕ) : Prop :=
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  letI := padicAlgebra hw
  IsGalois ℚ_[p] (completionAt K w) →
    orderVol p (fun _ : Fin m => Place.finite w) =
      -(((m : ℝ) - 1) / 2) * differentExponent K w * Real.log p

/-! ### At `∞` -/

variable (c) in
/-- **The archimedean log-shell and its hull**: `μ^log(𝓘_∞) ≤ μ^log(hull 𝓘_∞) ≤ |I|·log(√2·π)`
(IUT IV, Proposition 1.5; `archLogShell_subset`). -/
theorem componentVol_archLogShell_le_leastHull_le :
    componentVol .infinite c (archLogShell c) ≤
        componentVol .infinite c (LocalTheory.leastHull .infinite c (archLogShell c)) ∧
      componentVol .infinite c (LocalTheory.leastHull .infinite c (archLogShell c)) ≤
        Fintype.card ι * Real.log (Real.sqrt 2 * Real.pi) := by
  have hadm := archLogShell_admissible c
  refine ⟨LocalTheory.componentVol_le_leastHull_self hadm, ?_⟩
  have hsub : LocalTheory.leastHull .infinite c (archLogShell c) ⊆
      algebraMap ℝ (Tensor K .infinite c) (archHullRadius ^ Fintype.card ι) •
        integralAt .infinite c :=
    LocalTheory.leastHull_subset (isUnit_archScalar c) (archLogShell_subset c)
  refine (componentVol_le_of_subset hsub
    (admissible_haar_pos (LocalTheory.leastHull_admissible hadm))
    (haar_smul_integralAt_lt_top _)).trans_eq ?_
  rw [componentVol_arch_scale _ (pow_pos archHullRadius_pos _), Real.log_pow, archHullRadius]

end LocalConstruct

/-! ### The global formulas -/

namespace WallEquiv

open Wall LocalTheory

noncomputable section

variable (D : InitialThetaData.{u})

/-- **The packet term of `VC(I)`** at capsule `i` and rational place `v_ℚ`:
`∑_c w_c·μ^log(VC(I)_{i,v_ℚ,c})`. -/
def vcIPacket (i : Fin (nC D)) (vQ : RationalPlace) : ℝ :=
  ∑ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ,
    tupleWeight vQ c *
      LocalTheory.componentVol D.Kt vQ (LocalTheory.tuple D.placeSect vQ c) (vcIComp D i vQ c)

/-- **The packet term of `hull(VC(I))`**: `∑_c w_c·μ^log(hull(VC(I)_{i,v_ℚ,c}))`. -/
def hullPacket (i : Fin (nC D)) (vQ : RationalPlace) : ℝ :=
  ∑ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ,
    tupleWeight vQ c *
      LocalTheory.componentVol D.Kt vQ (LocalTheory.tuple D.placeSect vQ c)
        (LocalTheory.leastHull vQ (LocalTheory.tuple D.placeSect vQ c) (vcIComp D i vQ c))

/-- The local defect of a component of `VC(I)`: the shell defect at a prime, the archimedean
defect at `∞`. -/
def vcIDefect (i : Fin (nC D)) :
    ∀ (vQ : RationalPlace), (InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ) → ℝ
  | .finite p, c => shellDefect p (LocalTheory.tuple D.placeSect _ c)
  | .infinite, c => archDefect (LocalTheory.tuple D.placeSect .infinite c)

/-- The packet defect `∑_c w_c·δ_c`. -/
def defectPacket (i : Fin (nC D)) (vQ : RationalPlace) : ℝ :=
  ∑ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ,
    tupleWeight vQ c * vcIDefect D i vQ c

lemma packetVol_vcI (i : Fin (nC D)) (vQ : RationalPlace) :
    (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ ((vcI D i).region vQ) =
      vcIPacket D i vQ := by
  rw [LocalTheory.packetVol_eq]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h : LocalTheory.proj D.placeSect vQ c ((vcI D i).region vQ) = vcIComp D i vQ c :=
    proj_productRegion D.placeSect _ _ (fun c => (vcIComp_admissible D i vQ c).1) c
  rw [h]

lemma packetVol_hull_vcI (i : Fin (nC D)) (vQ : RationalPlace) :
    (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ ((hullOf D (vcI D) i).region vQ) =
      hullPacket D i vQ := by
  rw [LocalTheory.packetVol_eq]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← proj_hull_productRegion D.placeSect (nC D) i vQ (fun c => vcIComp D i vQ c)
    (fun c => vcIComp_admissible D i vQ c) c]
  rfl

lemma hullPacket_sub_vcIPacket (i : Fin (nC D)) (vQ : RationalPlace) :
    hullPacket D i vQ - vcIPacket D i vQ = defectPacket D i vQ := by
  unfold hullPacket vcIPacket defectPacket
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_sub]
  congr 1
  rcases vQ with p | _ <;> rfl

/-- **`log-vol(VC(I))` as an average of sums of local terms**:
`log-vol(VC(I)) = (1/ℓ*)·∑_i ∑ᶠ_{v_ℚ} ∑_c w_c·μ^log(VC(I)_{i,v_ℚ,c})`. -/
theorem logVol_vcI_eq : logVol D (vcI D) = (∑ i : Fin (nC D), ∑ᶠ vQ, vcIPacket D i vQ) / nC D :=
  congrArg₂ (· / ·) (Finset.sum_congr rfl fun i _ =>
    finsum_congr fun vQ => packetVol_vcI D i vQ) rfl

/-- **`log-vol(hull(VC(I)))` as an average of sums of local terms**. -/
theorem logVol_hull_vcI_eq :
    logVol D (hullOf D (vcI D)) = (∑ i : Fin (nC D), ∑ᶠ vQ, hullPacket D i vQ) / nC D :=
  congrArg₂ (· / ·) (Finset.sum_congr rfl fun i _ =>
    finsum_congr fun vQ => packetVol_hull_vcI D i vQ) rfl

lemma finite_support_vcIPacket (i : Fin (nC D)) :
    (Function.support (vcIPacket D i)).Finite := by
  have h := (LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol (vcI D i)
  rwa [show (fun vQ => (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ
    ((vcI D i).region vQ)) = vcIPacket D i from funext (packetVol_vcI D i)] at h

lemma finite_support_hullPacket (i : Fin (nC D)) :
    (Function.support (hullPacket D i)).Finite := by
  have h := (LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol (hullOf D (vcI D) i)
  rwa [show (fun vQ => (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ
    ((hullOf D (vcI D) i).region vQ)) = hullPacket D i from
      funext (packetVol_hull_vcI D i)] at h

/-- **The hull–container difference is an average of local defects**:
`log-vol(hull(VC(I))) − log-vol(VC(I)) = (1/ℓ*)·∑_i ∑ᶠ_{v_ℚ} ∑_c w_c·δ_{v_ℚ,c}` with
`δ = shellDefect` at a prime and `δ = archDefect` at `∞`. -/
theorem logVol_hull_vcI_sub_eq :
    logVol D (hullOf D (vcI D)) - logVol D (vcI D) =
      (∑ i : Fin (nC D), ∑ᶠ vQ, defectPacket D i vQ) / nC D := by
  rw [logVol_hull_vcI_eq, logVol_vcI_eq, ← sub_div, ← Finset.sum_sub_distrib]
  refine congrArg₂ (· / ·) (Finset.sum_congr rfl fun i _ => ?_) rfl
  rw [← finsum_sub_distrib (finite_support_hullPacket D i) (finite_support_vcIPacket D i)]
  exact finsum_congr fun vQ => hullPacket_sub_vcIPacket D i vQ

lemma defectPacket_nonneg (i : Fin (nC D)) (vQ : RationalPlace) : 0 ≤ defectPacket D i vQ := by
  refine Finset.sum_nonneg fun c _ => mul_nonneg
    (Finset.prod_nonneg fun _ _ => (weight_pos _ _ _).le) ?_
  rcases vQ with p | _
  · exact shellDefect_nonneg p _
  · exact archDefect_nonneg _

/-- `log-vol(VC(I)) ≤ log-vol(hull(VC(I)))`. -/
theorem logVol_vcI_le_hull : logVol D (vcI D) ≤ logVol D (hullOf D (vcI D)) := by
  have h := logVol_hull_vcI_sub_eq D
  have h0 : 0 ≤ (∑ i : Fin (nC D), ∑ᶠ vQ, defectPacket D i vQ) / nC D :=
    div_nonneg (Finset.sum_nonneg fun i _ =>
      finsum_nonneg fun vQ => defectPacket_nonneg D i vQ) (Nat.cast_nonneg _)
  linarith

/-! ### The packet terms at a prime -/

lemma tuple_isOver' (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    ∀ j, LocalConstruct.IsOver D.Kt p (LocalTheory.tuple D.placeSect _ c j) :=
  LocalTheory.tuple_isOver D.placeSect p c

/-- **The prime packet term of `VC(I)`**:
`∑_c w_c·(shellExcess(c) + μ^log(R_{I,c}))`. -/
theorem vcIPacket_finite (i : Fin (nC D)) (p : Nat.Primes) :
    vcIPacket D i (.finite p) =
      ∑ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
        tupleWeight (.finite p) c *
          (LocalConstruct.shellExcess p (LocalTheory.tuple D.placeSect _ c) +
            LocalConstruct.orderVol p (LocalTheory.tuple D.placeSect _ c)) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← LocalConstruct.componentVol_tensorLogShell_eq]
  rfl

/-- **The prime packet term of `hull(VC(I))`, exactly**: `∑_c w_c·∑_j ρ_{c j}·log p`, `ρ` the
radius of the log-shell of the factor. -/
theorem hullPacket_finite (i : Fin (nC D)) (p : Nat.Primes) :
    hullPacket D i (.finite p) =
      ∑ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
        tupleWeight (.finite p) c *
          ∑ j, LocalConstruct.logShellRadius
            (LocalConstruct.finPart D.Kt (LocalTheory.tuple D.placeSect _ c j)) p *
              Real.log p := by
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← LocalConstruct.componentVol_leastHull_tensorLogShell_eq (tuple_isOver' D i p c)]
  rfl

/-- At an odd prime `p` all of whose places in `K` have `e_w ≤ p − 2` (tamely ramified, with the
bound of IUT IV, Proposition 1.2(i)). -/
def IsTamePrime (p : Nat.Primes) : Prop :=
  Odd (p : ℕ) ∧ ∀ w : FinitePlace D.Kt, residueChar w = p → ramIdx D.Kt w ≤ (p : ℕ) - 2

lemma ramIdx_le_of_isTamePrime {p : Nat.Primes} (h : IsTamePrime D p) (i : Fin (nC D))
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) (j) :
    ramIdx D.Kt (LocalConstruct.finPart D.Kt (LocalTheory.tuple D.placeSect _ c j)) ≤
      (p : ℕ) - 2 :=
  h.2 _ (LocalConstruct.hres (tuple_isOver' D i p c) j)

/-- **The prime packet term of `VC(I)` at a tame prime**:
`∑_c w_c·(∑_j (1 − 1/e_{c j})·log p + μ^log(R_{I,c}))`. -/
theorem vcIPacket_tame (i : Fin (nC D)) {p : Nat.Primes} (h : IsTamePrime D p) :
    vcIPacket D i (.finite p) =
      ∑ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
        tupleWeight (.finite p) c *
          (∑ j, (1 - (ramIdx D.Kt (LocalConstruct.finPart D.Kt
              (LocalTheory.tuple D.placeSect _ c j)) : ℝ)⁻¹) * Real.log p +
            LocalConstruct.orderVol p (LocalTheory.tuple D.placeSect _ c)) := by
  rw [vcIPacket_finite]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LocalConstruct.shellExcess_eq_tame (tuple_isOver' D i p c) h.1
    (ramIdx_le_of_isTamePrime D h i c)]

/-- **The prime packet term of `hull(VC(I))` at a tame prime**:
`∑_c w_c·∑_j (1 − 1/e_{c j})·log p` (`= ∑_c w_c·d_{I,c}·log p`). -/
theorem hullPacket_tame (i : Fin (nC D)) {p : Nat.Primes} (h : IsTamePrime D p) :
    hullPacket D i (.finite p) =
      ∑ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
        tupleWeight (.finite p) c *
          ∑ j, (1 - (ramIdx D.Kt (LocalConstruct.finPart D.Kt
            (LocalTheory.tuple D.placeSect _ c j)) : ℝ)⁻¹) * Real.log p := by
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← LocalConstruct.componentVol_leastHull_tensorLogShell_eq_tame (tuple_isOver' D i p c) h.1
    (ramIdx_le_of_isTamePrime D h i c)]
  rfl

/-- **At a tame prime the packet defect is the packet index term**:
`defectPacket = −∑_c w_c·μ^log(R_{I,c}) = ∑_c w_c·log[(R_{I,c})^∼ : R_{I,c}]/[T_c : ℚ_p]`. -/
theorem defectPacket_tame (i : Fin (nC D)) {p : Nat.Primes} (h : IsTamePrime D p) :
    defectPacket D i (.finite p) =
      -∑ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
        tupleWeight (.finite p) c *
          LocalConstruct.orderVol p (LocalTheory.tuple D.placeSect _ c) := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  change _ * shellDefect p _ = _
  rw [LocalConstruct.shellDefect_eq_neg_orderVol_tame (tuple_isOver' D i p c) h.1
    (ramIdx_le_of_isTamePrime D h i c), mul_neg]

/-- At a tame prime the packet defect is at most `∑_c w_c·d_{I,c}·log p`
(`μ^log(R_I) ≥ −d_I·log p`, IUT IV, Proposition 1.1). -/
theorem defectPacket_tame_le (i : Fin (nC D)) {p : Nat.Primes} (h : IsTamePrime D p) :
    defectPacket D i (.finite p) ≤
      ∑ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
        tupleWeight (.finite p) c *
          ((∑ j, differentExponent D.Kt
            (LocalConstruct.finPart D.Kt (LocalTheory.tuple D.placeSect _ c j))) * Real.log p) := by
  rw [defectPacket_tame D i h, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [← mul_neg]
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun _ _ => (weight_pos _ _ _).le)
  have := LocalConstruct.neg_sum_differentExponent_mul_log_le_orderVol (tuple_isOver' D i p c)
  linarith

end

end WallEquiv

/-- **`SSIneq` in terms of local terms**:
`(s − 1)·|log q| ≤ (1/ℓ*)·∑_i ∑ᶠ_{v_ℚ} ∑_c w_c·μ^log(hull(VC(I)_{i,v_ℚ,c}))`. -/
theorem WallEquiv.ssIneq_iff_packets (D : InitialThetaData.{0}) :
    Wall.SSIneq D ↔ (Wall.sFactor (Wall.nC D) - 1) * D.qPilot.absLogQ ≤
      (∑ i : Fin (Wall.nC D), ∑ᶠ vQ, WallEquiv.hullPacket D i vQ) / Wall.nC D := by
  rw [Wall.SSIneq, WallEquiv.logVol_hull_vcI_eq]

/-- **The no-hull wall in terms of local terms**:
`(s − 1)·|log q| ≤ (1/ℓ*)·∑_i ∑ᶠ_{v_ℚ} ∑_c w_c·μ^log(VC(I)_{i,v_ℚ,c})`. -/
theorem WallEquiv.ssIneqNoHull_iff_packets (D : InitialThetaData.{0}) :
    Wall.SSIneqNoHull D ↔ (Wall.sFactor (Wall.nC D) - 1) * D.qPilot.absLogQ ≤
      (∑ i : Fin (Wall.nC D), ∑ᶠ vQ, WallEquiv.vcIPacket D i vQ) / Wall.nC D := by
  rw [Wall.SSIneqNoHull, WallEquiv.logVol_vcI_eq]

end Iut
