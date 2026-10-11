/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.Prop14Lattice

/-!
# The hull of a scaled tensor product of log-shells (IUT IV, Proposition 1.4(iii), Step (v))

Let all places of the packet `⊗_i K_{c i}` lie over `p`, let `L = ⊗_i 𝓘_{c i}` be the tensor
product of the log-shells, and let `x ∈ K_{c l}`, `x ≠ 0`, with `ord_p x = λ`. For the
indeterminacy automorphisms `φ = ⊗_i g_i` of IUT III, Theorem 3.11 (Ind2) (`tensorAut`):

* `x·𝓘_{c l} ⊆ p^m·𝓘_{c l}` with `m = ⌊λ − a_l − b_l⌋` (Proposition 1.2(i), `FactorShell.lean`),
  hence `incl_l(x)·L ⊆ p^m·L` and `φ(incl_l(x)·L) ⊆ p^m·L` (`φ` preserves `L`);
* `L ⊆ β·R_I` with `β = ⊗_i (2p)⁻¹ϖ_{b,i}` (`LatticeSandwich.lean`), so the images lie in the
  hull region `p^m·β·(R_I)^∼`, of log-volume `−(m + ord_p β)·log p` (`ScaleVolume.lean`);
* with `d_i + a_i ≥ 1 + ord_p(2)` (IUT IV, proof of Proposition 1.4(iii); from
  `d_i ≥ (e_i − 1)/e_i`, Proposition 1.3(i), `ramIdx_sub_one_le_ordDifferent`) and
  `(a_i + b_i)·log p ≤ 3 + log e_i` (resp. `= 0`), this is at most
  `(−λ + d_I + 1)·log p + ∑_{i ∈ I*} (3 + log e_i) + [l ∈ I*]·(3 + log e_l)`
  (`prop14iii_shell`). The extra term at `l` (compared with IUT IV, Proposition 1.4(iii)) is
  the price of the log-shell base region; no different bound (Proposition 1.1) is needed.
-/

namespace Iut

open PadicLogVolume

namespace LocalConstruct

open NumberField IsDedekindDomain
open scoped TensorProduct Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K]

/-! ### Arithmetic of the exponents -/

/-- **`e_w − 1 ≤ ord_w(𝔡_{K/ℚ})`** (IUT IV, Proposition 1.3(i)). -/
theorem ramIdx_sub_one_le_ordDifferent (w : FinitePlace K) :
    ramIdx K w - 1 ≤ ordDifferent K w := by
  classical
  set P := w.maximalIdeal.asIdeal
  set q := residueChar w
  have hq : q.Prime := residueChar_prime w
  haveI := liesOver_span_of_residueChar w (rfl : residueChar w = q)
  haveI := span_prime_isMaximal hq
  have hp0 : Ideal.span {(q : ℤ)} ≠ ⊥ := span_prime_ne_bot hq
  have hpS : (Ideal.span {(q : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hp0
  have he : ramIdx K w = multiplicity P ((Ideal.span {(q : ℤ)}).map (algebraMap ℤ (𝓞 K))) :=
    Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ P hpS
  have hdvd : P ^ ramIdx K w ∣ (Ideal.span {(q : ℤ)}).map (algebraMap ℤ (𝓞 K)) := by
    rw [he]; exact pow_multiplicity_dvd _ _
  have hdiff := pow_sub_one_dvd_differentIdeal (A := ℤ) (B := 𝓞 K)
    (p := Ideal.span {(q : ℤ)}) P (ramIdx K w) hp0 hdvd
  have hD : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hirr : Irreducible P := w.maximalIdeal.irreducible
  have hem := le_emultiplicity_of_pow_dvd hdiff
  rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hirr hD,
    normalize_eq] at hem
  exact_mod_cast hem

/-- `d_w ≥ (e_w − 1)/e_w`. -/
lemma differentExponent_ge (w : FinitePlace K) :
    ((ramIdx K w : ℝ) - 1) / ramIdx K w ≤ differentExponent K w := by
  have he : (0 : ℝ) < ramIdx K w := by exact_mod_cast ramIdx_pos' w
  unfold differentExponent
  refine div_le_div_of_nonneg_right ?_ he.le
  have h := ramIdx_sub_one_le_ordDifferent w
  have h1 : 1 ≤ ramIdx K w := ramIdx_pos' w
  have : ((ramIdx K w - 1 : ℕ) : ℝ) = (ramIdx K w : ℝ) - 1 := by push_cast [h1]; ring
  rw [← this]
  exact_mod_cast h

/-- `ord_p(2) = 1` if `p = 2`, `0` otherwise. -/
lemma ordp_two (w : FinitePlace K) :
    ordp K w (2 : completionAt K w) = if residueChar w = 2 then 1 else 0 := by
  split_ifs with h2
  · have := ordp_residueChar w
    rwa [h2, Nat.cast_ofNat] at this
  · have hp : (residueChar w).Prime := residueChar_prime w
    have hodd : Odd (residueChar w) := hp.odd_of_ne_two h2
    have hn : ‖(2 : completionAt K w)‖ = 1 :=
      norm_two_eq_one hp (norm_residueChar_lt_one w) hodd
    unfold ordp
    rw [hn, Real.log_one, neg_zero, zero_div]

/-- `a ≥ 1/e` for odd `p`. -/
lemma inv_le_logLatticeA {p e : ℕ} (hp : 3 ≤ p) (he : 0 < e) :
    (e : ℝ)⁻¹ ≤ logLatticeA p e := by
  have hp2 : p ≠ 2 := by omega
  unfold logLatticeA
  rw [if_neg hp2]
  have hpos : (0 : ℝ) < (e : ℝ) / ((p : ℝ) - 2) :=
    div_pos (by exact_mod_cast he) (by have h3 : (3 : ℝ) ≤ p := (by exact_mod_cast hp); linarith)
  have : (1 : ℝ) ≤ (⌈(e : ℝ) / ((p : ℝ) - 2)⌉ : ℝ) := by
    exact_mod_cast Int.one_le_ceil_iff.mpr hpos
  calc (e : ℝ)⁻¹ = (e : ℝ)⁻¹ * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- **`d_w + a_w ≥ 1 + ord_p(2)`** (IUT IV, proof of Proposition 1.4(iii)). -/
lemma one_add_ordp_two_le (w : FinitePlace K) :
    1 + ordp K w (2 : completionAt K w) ≤
      differentExponent K w + logLatticeA (residueChar w) (ramIdx K w) := by
  have he : (0 : ℝ) < ramIdx K w := by exact_mod_cast ramIdx_pos' w
  have hd0 : 0 ≤ differentExponent K w :=
    div_nonneg (Nat.cast_nonneg _) he.le
  rw [ordp_two]
  split_ifs with h2
  · unfold logLatticeA; rw [if_pos h2]; linarith
  · have hp : (residueChar w).Prime := residueChar_prime w
    have hp3 : 3 ≤ residueChar w := by have := hp.two_le; omega
    have ha := inv_le_logLatticeA hp3 (ramIdx_pos' w)
    have hd := differentExponent_ge w
    have : ((ramIdx K w : ℝ) - 1) / ramIdx K w + (ramIdx K w : ℝ)⁻¹ = 1 := by
      field_simp; ring
    linarith

/-! ### The factor inclusion `x·𝓘 ⊆ p^m·𝓘` -/

/-- `p` as an element of `K_w`. -/
local notation "pw" w => ((residueChar w : ℕ) : completionAt K w)

/-- **`x·𝓘_w ⊆ p^m·𝓘_w`** with `m = ⌊ord_p x − a − b⌋` (IUT IV, Proposition 1.2(i)). -/
theorem exists_mul_mem_logShell (w : FinitePlace K) {x : completionAt K w} (hx : x ≠ 0)
    {y : completionAt K w} (hy : y ∈ PadicLogVolume.logShell (completionAt K w) (residueChar w)) :
    ∃ y' ∈ PadicLogVolume.logShell (completionAt K w) (residueChar w),
      x * y = (pw w) ^ ⌊ordp K w x - (logLatticeA (residueChar w) (ramIdx K w) +
        logLatticeB (residueChar w) (ramIdx K w))⌋ * y' := by
  set a := logLatticeA (residueChar w) (ramIdx K w)
  set b := logLatticeB (residueChar w) (ramIdx K w)
  set m : ℤ := ⌊ordp K w x - (a + b)⌋
  have hp0 : (pw w) ≠ 0 := residueChar_ne_zero' w
  have h2p : (2 * pw w) ≠ 0 := mul_ne_zero two_ne_zero hp0
  have hA := varpiA_ne_zero w
  have hB := varpiB_ne_zero w
  have hpm : (pw w) ^ m ≠ 0 := zpow_ne_zero _ hp0
  set r := y / ((2 * pw w)⁻¹ * varpiB w)
  have hr : ‖r‖ ≤ 1 := norm_div_le_one_of_mem_logShell w hy
  set r' := x * varpiB w * r / ((pw w) ^ m * varpiA w)
  have hr' : ‖r'‖ ≤ 1 := by
    rcases eq_or_ne r 0 with h0 | h0
    · simp [r', h0]
    have hρ : 0 < ‖pw w‖ := norm_residueChar_pos w
    have hρ1 : ‖pw w‖ < 1 := norm_residueChar_lt_one w
    have hxn := norm_eq_rpow_ordp w hx
    have hAn := norm_eq_rpow_of_ordp w hA (ordp_varpiA w)
    have hBn := norm_eq_rpow_of_ordp w hB (ordp_varpiB w)
    have hpmn : ‖(pw w) ^ m‖ = ‖pw w‖ ^ (m : ℝ) := by
      rw [norm_zpow, Real.rpow_intCast]
    have hk : 0 ≤ ordp K w x + -b - (m : ℝ) - a := by
      have := Int.floor_le (ordp K w x - (a + b)); linarith
    simp only [r', norm_div, norm_mul, hxn, hAn, hBn, hpmn]
    rw [div_le_one (mul_pos (Real.rpow_pos_of_pos hρ _) (Real.rpow_pos_of_pos hρ _))]
    calc ‖pw w‖ ^ ordp K w x * ‖pw w‖ ^ (-b) * ‖r‖
        ≤ ‖pw w‖ ^ ordp K w x * ‖pw w‖ ^ (-b) * 1 :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = ‖pw w‖ ^ (ordp K w x + -b - (m : ℝ) - a) * (‖pw w‖ ^ (m : ℝ) * ‖pw w‖ ^ a) := by
          rw [mul_one, ← Real.rpow_add hρ, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
          ring_nf
      _ ≤ 1 * (‖pw w‖ ^ (m : ℝ) * ‖pw w‖ ^ a) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_one hρ.le hρ1.le hk) (by positivity)
      _ = _ := one_mul _
  refine ⟨(2 * pw w)⁻¹ * (varpiA w * r'), mul_mem_logShell_of_norm_le_one w hr', ?_⟩
  have hyr : y = (2 * pw w)⁻¹ * varpiB w * r := by
    simp only [r]; field_simp
  simp only [r']
  rw [hyr]
  field_simp

/-! ### The packet inclusion `incl_l(x)·⊗𝓘 ⊆ p^m·⊗𝓘` -/

section Packet

variable {ι : Type} [Fintype ι] {p : Nat.Primes} {c : ι → Place K}
  (hc : ∀ j, IsOver K p (c j))
include hc

/-- The exponent `m = ⌊ord_p x − a_l − b_l⌋` at the factor `l`. -/
noncomputable def shellExp (l : ι) (x : completionAt K (finPart K (c l))) : ℤ :=
  ⌊ordp K _ x - (logLatticeA (residueChar (finPart K (c l))) (ramIdx K (finPart K (c l))) +
    logLatticeB (residueChar (finPart K (c l))) (ramIdx K (finPart K (c l))))⌋

omit hc in
open Classical in
lemma incl_mul_tprod (l : ι) (h : c l = Place.finite (finPart K (c l)))
    (x : completionAt K (finPart K (c l))) (b : ∀ j, Factor K p (c j)) :
    incl p c l (finPart K (c l)) h x * PiTensorProduct.tprod ℚ_[p] b =
      PiTensorProduct.tprod ℚ_[p] (Function.update b l (factorMk p (c l) x * b l)) := by
  have h1 : incl p c l (finPart K (c l)) h x =
      PiTensorProduct.tprod ℚ_[p] (Function.update (fun j => (1 : Factor K p (c j))) l
        (factorMk p (c l) x)) := by
    rw [incl_apply, completionCongr_rfl, RingEquiv.refl_apply]
    unfold inclFactor
    rw [PiTensorProduct.singleAlgHom_apply]
    congr 1
  rw [h1, PiTensorProduct.tprod_mul_tprod]
  congr 1
  funext j
  by_cases hj : j = l
  · subst hj; simp
  · simp [Function.update_of_ne hj]

open Classical in
/-- **`incl_l(x)·⊗𝓘 ⊆ p^m·⊗𝓘`**. -/
theorem incl_smul_tensorLogShell_subset (l : ι) (x : completionAt K (finPart K (c l)))
    (hx : x ≠ 0) :
    incl p c l (finPart K (c l)) (hW hc l) x • tensorLogShell p c ⊆
      (((p : ℕ) : ℚ_[p]) ^ shellExp (c := c) l x) • tensorLogShell p c := by
  set t : ℚ_[p] := ((p : ℕ) : ℚ_[p]) ^ shellExp (c := c) l x
  have hres' := hres hc l
  -- the factor statement, transported to `p`
  have hfac : ∀ y ∈ PadicLogVolume.logShell (completionAt K (finPart K (c l))) p,
      ∃ y' ∈ PadicLogVolume.logShell (completionAt K (finPart K (c l))) p,
        factorMk p (c l) x * factorMk p (c l) y = t • factorMk p (c l) y' := by
    intro y hy
    rw [← hres'] at hy
    obtain ⟨y', hy', hyy⟩ := exists_mul_mem_logShell (finPart K (c l)) hx hy
    refine ⟨y', hres' ▸ hy', ?_⟩
    rw [← map_mul, hyy, map_mul, Algebra.smul_def,
      algebraMap_factor_apply_of_isOver p (c l) (hc l)]
    congr 1
    simp only [t, map_zpow₀, map_natCast]
    unfold shellExp
    rw [hres']
  -- span induction over `⊗𝓘`
  rintro _ ⟨z, hz, rfl⟩
  have key : ∀ z ∈ tensorLogShell p c,
      incl p c l (finPart K (c l)) (hW hc l) x * z ∈ t • tensorLogShell p c := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, rfl⟩ := hz
      obtain ⟨y, hy, hyb⟩ := (b l).2
      obtain ⟨y', hy', hfy⟩ := hfac y hy
      rw [incl_mul_tprod, ← hyb, hfy]
      have hupd : Function.update (fun j => (b j : Factor K p (c j))) l
          (t • factorMk p (c l) y') =
          Function.update (Function.update (fun j => (b j : Factor K p (c j))) l
            (factorMk p (c l) y')) l (t • (Function.update (fun j => (b j : Factor K p (c j))) l
              (factorMk p (c l) y')) l) := by
        simp
      rw [hupd, MultilinearMap.map_update_smul, Function.update_eq_self]
      refine ⟨_, Submodule.subset_span ⟨fun j => ⟨Function.update
        (fun j => (b j : Factor K p (c j))) l (factorMk p (c l) y') j, ?_⟩, rfl⟩, rfl⟩
      by_cases hj : j = l
      · subst hj; rw [Function.update_self]; exact ⟨y', hy', rfl⟩
      · rw [Function.update_of_ne hj]; exact (b j).2
    | zero => rw [mul_zero]; exact ⟨0, (Submodule.span ℤ_[p] _).zero_mem, smul_zero _⟩
    | add z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨u₁, hu₁, e₁⟩ := h₁
      obtain ⟨u₂, hu₂, e₂⟩ := h₂
      refine ⟨u₁ + u₂, (Submodule.span ℤ_[p] _).add_mem hu₁ hu₂, ?_⟩
      beta_reduce at e₁ e₂ ⊢
      rw [smul_add, e₁, e₂, mul_add]
    | smul r z _ hz' =>
      obtain ⟨u, hu, e⟩ := hz'
      refine ⟨r • u, (Submodule.span ℤ_[p] _).smul_mem r hu, ?_⟩
      beta_reduce at e ⊢
      rw [padicInt_smul_def, padicInt_smul_def, mul_smul_comm, ← e, smul_comm]
  exact key z hz

end Packet

/-! ### Proposition 1.4(iii) for the log-shell base region -/

lemma ordp_scalB {ι : Type} (c : ι → Place K) (j : ι) :
    ordp K _ (scalB c j) = -(ordp K _ (2 : completionAt K (finPart K (c j))) + 1 +
      logLatticeB (residueChar (finPart K (c j))) (ramIdx K (finPart K (c j)))) := by
  have h2 : (2 : completionAt K (finPart K (c j))) ≠ 0 := two_ne_zero
  have hp := residueChar_ne_zero' (finPart K (c j))
  unfold scalB
  rw [ordp_mul _ _ _ (inv_ne_zero (mul_ne_zero h2 hp)) (varpiB_ne_zero _), ordp_inv,
    ordp_mul _ _ _ h2 hp, ordp_residueChar, ordp_varpiB]
  ring

/-- **IUT IV, Proposition 1.4(iii)** for the indeterminacy automorphisms of IUT III (Ind2) and
the log-shell base region (Ind3): for `x ∈ K_{c l}`, `x ≠ 0`, the images
`φ(incl_l(x)·⊗𝓘)` lie in a hull region `a·(R_I)^∼` of log-volume at most
`(−ord_p x + d_I + 1)·log p + ∑_i [p − 2 < e_i]·(3 + log e_i) + [p − 2 < e_l]·(3 + log e_l)`. -/
theorem prop14iii_shell {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)
    (hc : ∀ j, ∃ w : FinitePlace K, c j = Place.finite w ∧ residueChar w = p)
    (d : ι → ℝ) (hd : ∀ i w', c i = Place.finite w' → d i = differentExponent K w')
    (l : ι) (w : FinitePlace K) (h : c l = Place.finite w) (x : completionAt K w) (hx : x ≠ 0) :
    ∃ a : Tensor K (.finite p) c, IsUnit a ∧
      (∀ φ ∈ indAut (.finite p) c,
        φ '' (incl p c l w h x • tensorLogShell p c) ⊆ a • integral p c) ∧
      componentVol (.finite p) c (a • integral p c) ≤
        (-ordp K w x + ∑ i, d i + 1) * Real.log p +
          (∑ i, if (p : ℕ) - 2 < ramIdxAt K (c i) then
            3 + Real.log (ramIdxAt K (c i)) else 0) +
          (if (p : ℕ) - 2 < ramIdxAt K (c l) then 3 + Real.log (ramIdxAt K (c l)) else 0) := by
  classical
  have hc' : ∀ j, IsOver K p (c j) := hc
  obtain rfl : w = finPart K (c l) := eq_finPart h
  set W : ι → FinitePlace K := fun i => finPart K (c i)
  have hWi : ∀ i, c i = Place.finite (W i) := hW hc'
  set m : ℤ := shellExp (c := c) l x
  set t : ℚ_[p] := ((p : ℕ) : ℚ_[p]) ^ m
  have ht0 : t ≠ 0 := zpow_ne_zero _ (by exact_mod_cast p.2.ne_zero)
  set e : completionAt K (W l) := padicEmb (hres hc' l) t
  have he0 : e ≠ 0 := (map_ne_zero _).mpr ht0
  have heord : ordp K (W l) e = m := by
    have : e = ((residueChar (W l) : ℕ) : completionAt K (W l)) ^ m := by
      change padicEmb (hres hc' l) t = _
      rw [map_zpow₀, map_natCast, hres hc' l]
    rw [this, ordp_zpow_residueChar]
  have hinc : incl p c l (W l) (hWi l) e = algebraMap ℚ_[p] (Tensor K (.finite p) c) t :=
    incl_padicEmb hc' l t
  set a : Tensor K (.finite p) c :=
    algebraMap ℚ_[p] (Tensor K (.finite p) c) t * ∏ i, incl p c i (W i) (hWi i) (scalB c i)
  have ha : a = ∏ i, incl p c i (W i) (hWi i)
      (Function.update (fun i => scalB c i) l (e * scalB c l) i) := by
    rw [prod_incl_update, map_mul, hinc]
    change algebraMap ℚ_[p] _ t * ∏ i, incl p c i (W i) (hWi i) (scalB c i) = _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l), mul_assoc]
  have hB0 : ∀ i, Function.update (fun i => scalB c i) l (e * scalB c l) i ≠ 0 :=
    update_ne_zero W _ (scalB_ne_zero c) l _ (mul_ne_zero he0 (scalB_ne_zero c l))
  refine ⟨a, ha ▸ isUnit_prod_incl W hWi _ hB0, ?_, ?_⟩
  · -- containment
    intro φ hφ
    have hφ' := tensorAut_subset_latticeAut p c hφ
    have hsub := incl_smul_tensorLogShell_subset hc' l x hx
    refine (Set.image_mono hsub).trans ?_
    rw [image_smul_tensorLogShell hφ']
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨r, hr, rfl⟩ := exists_mem_order_of_mem_tensorLogShell hc' hz
    refine ⟨r, order_subset_integral p c hr, ?_⟩
    change a * r = t • (_ * r)
    rw [← prod_incl_eq_tprod hc', Algebra.smul_def, mul_assoc]
  · -- the volume bound
    rw [ha, componentVol_prod_incl_smul_integral hc' W hWi _ hB0, sum_ordp_update,
      ordp_mul _ _ _ he0 (scalB_ne_zero c l), heord]
    have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast p.2.one_lt)
    have hfl : ordp K (W l) x - (logLatticeA (residueChar (W l)) (ramIdx K (W l)) +
        logLatticeB (residueChar (W l)) (ramIdx K (W l))) - 1 < m :=
      Int.sub_one_lt_floor _
    have hram : ∀ i, ramIdxAt K (c i) = ramIdx K (W i) := fun i => by rw [hWi i]; rfl
    -- per-factor estimate
    have hterm : ∀ i, (-ordp K (W i) (scalB c i) - d i) * Real.log p ≤
        if (p : ℕ) - 2 < ramIdxAt K (c i) then 3 + Real.log (ramIdxAt K (c i)) else 0 := by
      intro i
      rw [ordp_scalB, hram, hd i (W i) (hWi i)]
      have h1 := one_add_ordp_two_le (W i)
      have h2 := logLattice_term_le p (W i) (hres hc' i)
      have : (-(-(ordp K (W i) (2 : completionAt K (W i)) + 1 +
          logLatticeB (residueChar (W i)) (ramIdx K (W i)))) - differentExponent K (W i)) *
            Real.log p ≤ (logLatticeA (residueChar (W i)) (ramIdx K (W i)) +
          logLatticeB (residueChar (W i)) (ramIdx K (W i))) * Real.log p :=
        mul_le_mul_of_nonneg_right (by linarith) hlogp.le
      exact this.trans h2
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hsum
    have hl : (logLatticeA (residueChar (W l)) (ramIdx K (W l)) +
        logLatticeB (residueChar (W l)) (ramIdx K (W l))) * Real.log p ≤
        if (p : ℕ) - 2 < ramIdxAt K (c l) then 3 + Real.log (ramIdxAt K (c l)) else 0 := by
      rw [hram l]; exact logLattice_term_le p (W l) (hres hc' l)
    have hm := mul_lt_mul_of_pos_right hfl hlogp
    have hx' : ordp K (W l) x = ordp K (finPart K (c l)) x := rfl
    rw [← hx']
    nlinarith [hsum, hl, hm, hlogp]

end LocalConstruct

end Iut
