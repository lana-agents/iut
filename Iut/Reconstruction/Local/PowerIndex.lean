/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.UnitIndex

/-!
# The exact index of `p^k`-th powers and the `p`-power roots of unity (roadmap P17, M1c)

For a finite extension `K/ℚ_p` with absolute ramification index `e`:

* `Iut.Reconstruction.v_one_add_pow_p_sub_one`: if `v(x) ≥ e + 1` then
  `v((1 + x)^p − 1) = v(x) + e`; hence `U^(e+1)` has no `p`-torsion
  (`Iut.Reconstruction.pow_p_pow_eq_one_iff`);
* `Iut.Reconstruction.map_pow_unitFilt`: `(U^(e+1))^{p^k} = U^(e+1+ke)` (Hensel in root form);
* `Iut.Reconstruction.index_unitFilt_eq`, `relIndex_unitFilt`: `[𝒪ˣ : U^(m)] = q^m − q^{m−1}`;
* `Iut.Reconstruction.powIndex_integers_p_pow`: **`[𝒪ˣ : (𝒪ˣ)^{p^k}] = #μ_{p^k}(K) · q^{ke}`**:
  with `V = U^(e+1)`, `W = Vⁿ = U^(e+1+ke)` and `T = μ_n` (`n = p^k`), the subgroup
  `{u | uⁿ ∈ W}` is `V · T` with `V ∩ T = 1`, so `[𝒪ˣ : (𝒪ˣ)ⁿ] · [𝒪ˣ : V] = [𝒪ˣ : W] · #T`;
* `Iut.Reconstruction.powIndex_p_pow`: `[Kˣ : (Kˣ)^{p^k}] = #μ_{p^k}(K) · p^{k([K:ℚ_p]+1)}`.
-/

open IsLocalRing PadicField

namespace Iut.Reconstruction

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

section Valuation

theorem v_isUnit {r : 𝒪 p K} (hr : IsUnit r) : v p ((r : 𝒪 p K) : K) = 0 :=
  v_unit hr.unit

theorem isUnit_of_sub_one_mem {r : 𝒪 p K} (hr : r - 1 ∈ maximalIdeal (𝒪 p K)) : IsUnit r := by
  by_contra h
  have hr' : r ∈ maximalIdeal (𝒪 p K) := (mem_maximalIdeal _).2 h
  have h1 : (1 : 𝒪 p K) ∈ maximalIdeal (𝒪 p K) := by
    have := sub_mem hr' hr
    rwa [sub_sub_cancel] at this
  exact (maximalIdeal.isMaximal (𝒪 p K)).ne_top ((Ideal.eq_top_iff_one _).2 h1)

/-- `(1 + x)^p = 1 + p x r + x^p` with a unit `r`, for `x ∈ 𝔪`. -/
theorem exists_one_add_pow_p_eq {x : 𝒪 p K} (hx : x ∈ maximalIdeal (𝒪 p K)) :
    ∃ r : 𝒪 p K, IsUnit r ∧ (1 + x) ^ p = 1 + (p : 𝒪 p K) * x * r + x ^ p := by
  set r : 𝒪 p K := ∑ k ∈ Finset.Ioo 0 p, x ^ (k - 1) * 1 ^ (p - k - 1) *
    ((p.choose k / p : ℕ) : 𝒪 p K)
  have h := add_pow_prime_eq hp.out x (1 : 𝒪 p K)
  refine ⟨r, isUnit_of_sub_one_mem ?_, ?_⟩
  · have h1 : (1 : ℕ) ∈ Finset.Ioo 0 p := Finset.mem_Ioo.2 ⟨one_pos, hp.out.one_lt⟩
    simp only [r]
    rw [← Finset.add_sum_erase _ _ h1]
    simp only [tsub_self, pow_zero, one_pow, one_mul, Nat.choose_one_right,
      Nat.div_self hp.out.pos, Nat.cast_one, add_sub_cancel_left]
    refine Ideal.sum_mem _ fun k hk => ?_
    simp only [Finset.mem_erase, Finset.mem_Ioo] at hk
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ?_)
    exact Ideal.pow_mem_of_mem _ hx _ (by omega)
  · rw [add_comm (1 : 𝒪 p K) x, h]
    ring

theorem coe_ne_zero_of_ne_zero {x : 𝒪 p K} (hx : x ≠ 0) : (x : K) ≠ 0 :=
  fun h => hx (Integers.coe_eq_zero_iff.1 h)

/-- **Exact valuation of `(1 + x)^p − 1`** for `v(x) ≥ e + 1`. -/
theorem v_one_add_pow_p_sub_one {x : 𝒪 p K} (hx0 : x ≠ 0)
    (hx : (e p ℚ_[p] K : ℤ) + 1 ≤ v p (x : K)) :
    (1 + x) ^ p - 1 ≠ 0 ∧ v p (((1 + x) ^ p - 1 : 𝒪 p K) : K) = v p (x : K) + e p ℚ_[p] K := by
  have hxm : x ∈ maximalIdeal (𝒪 p K) :=
    Integers.mem_maximalIdeal_iff.2 ((nrm_lt_one_iff_v_pos (coe_ne_zero_of_ne_zero hx0)).2
      (by have := (e_pos' p K); omega))
  obtain ⟨r, hr, hrx⟩ := exists_one_add_pow_p_eq hxm
  have hr0 : ((r : 𝒪 p K) : K) ≠ 0 := coe_ne_zero_of_ne_zero hr.ne_zero
  have hp0 : (p : K) ≠ 0 := natCast_p_ne_zero
  have hxK := coe_ne_zero_of_ne_zero hx0
  set a : K := (p : K) * (x : K) * (r : K)
  set b : K := (x : K) ^ p
  have ha0 : a ≠ 0 := mul_ne_zero (mul_ne_zero hp0 hxK) hr0
  have hb0 : b ≠ 0 := pow_ne_zero _ hxK
  have hva : v p a = v p (x : K) + e p ℚ_[p] K := by
    simp only [a]
    rw [v_mul (mul_ne_zero hp0 hxK) hr0, v_mul hp0 hxK, v_natCast_p_eq, v_isUnit hr]
    ring
  have hvb : v p b = p * v p (x : K) := v_pow hxK p
  have hlt : v p a < v p b := by
    rw [hva, hvb]
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
    have he := (e_pos' p K)
    nlinarith
  have hnrm : nrm p K b < nrm p K a := (nrm_lt_iff_v_lt hb0 ha0).2 hlt
  have hsum : (((1 + x) ^ p - 1 : 𝒪 p K) : K) = a + b := by
    rw [hrx]
    simp only [a, b, Integers.coe_sub, Integers.coe_add, Integers.coe_mul, Integers.coe_pow,
      Integers.coe_one, coe_natCast_integers]
    ring
  have heq : nrm p K (a + b) = nrm p K a := nrm_add_eq_left hnrm
  have hab0 : a + b ≠ 0 := by
    intro h0; rw [h0, nrm_eq_zero_iff.2 rfl] at heq
    exact (nrm_pos_iff.2 ha0).ne heq
  refine ⟨fun h0 => hab0 (by rw [← hsum, h0, Integers.coe_zero]), ?_⟩
  rw [hsum, ← hva]
  exact (nrm_eq_iff_v_eq hab0 ha0).1 heq

end Valuation

section ExactFiltration

theorem nontrivial_quot_pow {m : ℕ} (hm : m ≠ 0) :
    Nontrivial (𝒪 p K ⧸ maximalIdeal (𝒪 p K) ^ m) :=
  Ideal.Quotient.nontrivial_iff.2 (by
    rw [Ne, Ideal.eq_top_iff_one]
    intro h1
    exact (maximalIdeal.isMaximal (𝒪 p K)).ne_top
      ((Ideal.eq_top_iff_one _).2 (Ideal.pow_le_self hm h1)))

/-- `#(𝒪/𝔪^m)ˣ = q^m − q^{m−1}`. -/
theorem card_units_quot_pow {m : ℕ} (hm : m ≠ 0) :
    Nat.card (𝒪 p K ⧸ maximalIdeal (𝒪 p K) ^ m)ˣ = q p K ^ m - q p K ^ (m - 1) := by
  classical
  set I := maximalIdeal (𝒪 p K) ^ m
  set S : Submodule (𝒪 p K) (𝒪 p K) := maximalIdeal (𝒪 p K)
  have hIS : (I : Submodule (𝒪 p K) (𝒪 p K)) ≤ S := Ideal.pow_le_self hm
  have hc := Submodule.card_quotient_mul_card_quotient S I hIS
  have hS : Nat.card (𝒪 p K ⧸ S) = q p K := rfl
  have hI : Nat.card (𝒪 p K ⧸ I) = q p K ^ m := card_quot_maximalIdeal_pow p K m
  rw [hS] at hc
  have hq := one_lt_q p K
  have hmap : Nat.card (S.map I.mkQ) = q p K ^ (m - 1) := by
    have h' : q p K ^ m = q p K ^ (m - 1) * q p K := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm)]
    have hc' : Nat.card (S.map I.mkQ) * q p K = q p K ^ (m - 1) * q p K := by
      rw [← h', ← hI]; exact hc
    exact Nat.eq_of_mul_eq_mul_right (by omega) hc'
  haveI := nontrivial_quot_pow (p := p) (K := K) hm
  have hunit : ∀ y : 𝒪 p K ⧸ I, IsUnit y ↔ ¬ (y ∈ S.map I.mkQ) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro hu ⟨x', hx', hxx'⟩
      have hd : x' - x ∈ I := Ideal.Quotient.eq.1 hxx'
      have hxS : x ∈ maximalIdeal (𝒪 p K) := by
        have h2 := sub_mem hx' (Ideal.pow_le_self hm hd)
        rwa [sub_sub_cancel] at h2
      have hnil : IsNilpotent (Ideal.Quotient.mk I x) := by
        refine ⟨m, ?_⟩
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_pow hxS m
      exact hnil.not_isUnit hu
    · intro hnot
      have hx : x ∉ maximalIdeal (𝒪 p K) := fun h => hnot ⟨x, h, rfl⟩
      rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hx
      exact hx.map _
  haveI : Fintype (𝒪 p K ⧸ I) := Fintype.ofFinite _
  have hcard : Nat.card (𝒪 p K ⧸ I)ˣ = Nat.card {y : 𝒪 p K ⧸ I // ¬ (y ∈ S.map I.mkQ)} := by
    let eU : (𝒪 p K ⧸ I)ˣ ≃ {y : 𝒪 p K ⧸ I // IsUnit y} :=
      { toFun := fun u => ⟨u, u.isUnit⟩
        invFun := fun y => y.2.unit
        left_inv := fun u => Units.ext rfl
        right_inv := fun y => Subtype.ext rfl }
    exact (Nat.card_congr eU).trans (Nat.card_congr (Equiv.subtypeEquivRight hunit))
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, hI]
  congr 1

theorem index_unitFilt_eq {m : ℕ} (hm : m ≠ 0) :
    (unitFilt p K m).index = q p K ^ m - q p K ^ (m - 1) := by
  rw [index_unitFilt hm, card_units_quot_pow hm]

theorem unitFilt_anti {a b : ℕ} (h : a ≤ b) : unitFilt p K b ≤ unitFilt p K a :=
  fun _ hu => Ideal.pow_le_pow_right h hu

/-- `[U^(a) : U^(b)] = q^{b−a}` for `1 ≤ a ≤ b`. -/
theorem relIndex_unitFilt {a b : ℕ} (ha : a ≠ 0) (h : a ≤ b) :
    (unitFilt p K b).relIndex (unitFilt p K a) = q p K ^ (b - a) := by
  have h1 := Subgroup.relIndex_mul_index (unitFilt_anti (p := p) (K := K) h)
  rw [index_unitFilt_eq ha, index_unitFilt_eq (by omega)] at h1
  have hq := one_lt_q p K
  have hpos : 0 < q p K ^ a - q p K ^ (a - 1) := by
    have : q p K ^ (a - 1) < q p K ^ a := Nat.pow_lt_pow_right hq (by omega)
    omega
  have h2 : q p K ^ b - q p K ^ (b - 1) = q p K ^ (b - a) * (q p K ^ a - q p K ^ (a - 1)) := by
    rw [Nat.mul_sub, ← pow_add, ← pow_add, Nat.sub_add_cancel h]
    congr 2
    omega
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

end ExactFiltration

section Torsion

theorem v_pow_p_pow_sub_one {y : 𝒪 p K} (hy0 : y - 1 ≠ 0)
    (hy : (e p ℚ_[p] K : ℤ) + 1 ≤ v p ((y - 1 : 𝒪 p K) : K)) (k : ℕ) :
    y ^ (p ^ k) - 1 ≠ 0 ∧
      v p ((y ^ (p ^ k) - 1 : 𝒪 p K) : K) = v p ((y - 1 : 𝒪 p K) : K) + k * e p ℚ_[p] K := by
  induction k with
  | zero => simpa using hy0
  | succ k ih =>
    obtain ⟨h0, hv⟩ := ih
    have hx : (e p ℚ_[p] K : ℤ) + 1 ≤ v p ((y ^ (p ^ k) - 1 : 𝒪 p K) : K) := by
      rw [hv]; have := (e_pos' p K); nlinarith
    obtain ⟨h1, h2⟩ := v_one_add_pow_p_sub_one h0 hx
    rw [add_sub_cancel, ← pow_mul, ← pow_succ] at h1 h2
    refine ⟨h1, ?_⟩
    rw [h2, hv]; push_cast; ring

theorem v_ge_of_mem_unitFilt {m : ℕ} {u : (𝒪 p K)ˣ} (hu : u ∈ unitFilt p K m)
    (h0 : (u : 𝒪 p K) - 1 ≠ 0) : (m : ℤ) ≤ v p (((u : 𝒪 p K) - 1 : 𝒪 p K) : K) := by
  rw [mem_unitFilt, Integers.mem_maximalIdeal_pow_iff] at hu
  exact hu.resolve_left h0

/-- `U^(e+1)` has no nontrivial `p`-power torsion. -/
theorem eq_one_of_pow_p_pow_eq_one {u : (𝒪 p K)ˣ} (hu : u ∈ unitFilt p K (e p ℚ_[p] K + 1))
    {k : ℕ} (h : u ^ (p ^ k) = 1) : u = 1 := by
  by_contra hne
  have h0 : (u : 𝒪 p K) - 1 ≠ 0 := fun h0 => hne (Units.ext (sub_eq_zero.1 h0))
  have hv := v_ge_of_mem_unitFilt hu h0
  push_cast at hv
  have := (v_pow_p_pow_sub_one h0 hv k).1
  apply this
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self]

/-- `(U^(e+1))^{p^k} ⊆ U^(e+1+ke)`. -/
theorem pow_p_pow_mem_unitFilt_add {u : (𝒪 p K)ˣ} (hu : u ∈ unitFilt p K (e p ℚ_[p] K + 1))
    (k : ℕ) : u ^ (p ^ k) ∈ unitFilt p K (e p ℚ_[p] K + 1 + k * e p ℚ_[p] K) := by
  induction k with
  | zero => simpa using hu
  | succ k ih =>
    rw [mem_unitFilt] at ih ⊢
    have h := one_add_pow_p_sub_one_mem ih
    rw [add_sub_cancel] at h
    rw [pow_succ, pow_mul, Units.val_pow_eq_pow_val]
    have hmin : min (e p ℚ_[p] K) (e p ℚ_[p] K + 1 + k * e p ℚ_[p] K) = e p ℚ_[p] K :=
      min_eq_left (by omega)
    rw [hmin] at h
    convert h using 2
    ring

theorem p_mul_ϖ_mem : (p : 𝒪 p K) * Integers.ϖ p K ∈ maximalIdeal (𝒪 p K) ^ (e p ℚ_[p] K + 1) := by
  have hpm : (p : 𝒪 p K) ∈ maximalIdeal (𝒪 p K) ^ e p ℚ_[p] K := by
    rw [Integers.mem_maximalIdeal_pow_iff, coe_natCast_integers, v_natCast_p_eq]
    exact Or.inr le_rfl
  rw [pow_succ]
  exact Ideal.mul_mem_mul hpm ϖ_mem_maximalIdeal

/-- Iterated Hensel with the root in `U^(e+1)`. -/
theorem exists_pow_p_pow_eq' (k : ℕ) (w : 𝒪 p K) :
    ∃ y : 𝒪 p K, y - 1 ∈ maximalIdeal (𝒪 p K) ^ (e p ℚ_[p] K + 1) ∧
      y ^ (p ^ k) = 1 + (p : 𝒪 p K) ^ (k + 1) * Integers.ϖ p K * w := by
  induction k generalizing w with
  | zero =>
    refine ⟨1 + p * Integers.ϖ p K * w, ?_, by simp⟩
    rw [add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ p_mul_ϖ_mem
  | succ k ih =>
    have hd : (p : 𝒪 p K) ^ k * Integers.ϖ p K ∈ maximalIdeal (𝒪 p K) :=
      Ideal.mul_mem_left _ _ ϖ_mem_maximalIdeal
    obtain ⟨y, hy⟩ := exists_one_add_pow_eq p hd w
    obtain ⟨z, hz1, hz⟩ := ih y
    refine ⟨z, hz1, ?_⟩
    rw [pow_succ, pow_mul, hz]
    convert hy using 2 <;> ring

/-- `(U^(e+1))^{p^k} = U^(e+1+ke)`. -/
theorem unitFilt_le_map_pow (k : ℕ) {u : (𝒪 p K)ˣ}
    (hu : u ∈ unitFilt p K (e p ℚ_[p] K + 1 + k * e p ℚ_[p] K)) :
    ∃ y ∈ unitFilt p K (e p ℚ_[p] K + 1), y ^ (p ^ k) = u := by
  have hu' : u ∈ unitFilt p K ((k + 1) * e p ℚ_[p] K + 1) := by
    convert hu using 2; ring
  rw [mem_unitFilt, Integers.mem_maximalIdeal_pow_iff] at hu'
  have hp0 : (p : 𝒪 p K) ≠ 0 := fun h => by
    have := congrArg (fun x : 𝒪 p K => (x : K)) h
    simp only [coe_natCast_integers, Integers.coe_zero] at this
    exact natCast_p_ne_zero this
  have ha : (p : 𝒪 p K) ^ (k + 1) * Integers.ϖ p K ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp0) Integers.irreducible_ϖ.ne_zero
  have hdvd : (p : 𝒪 p K) ^ (k + 1) * Integers.ϖ p K ∣ (u : 𝒪 p K) - 1 := by
    rw [Integers.dvd_iff_v_le ha, v_p_pow_mul_ϖ]
    rcases hu' with h | h
    · exact Or.inl h
    · right; exact_mod_cast h
  obtain ⟨w, hw⟩ := hdvd
  obtain ⟨y, hy1, hy⟩ := exists_pow_p_pow_eq' (K := K) k w
  have hyu : y ^ (p ^ k) = (u : 𝒪 p K) := by rw [hy, ← hw, add_sub_cancel]
  have hyunit : IsUnit y :=
    (isUnit_pow_iff (pow_ne_zero _ hp.out.ne_zero)).1 (hyu ▸ u.isUnit)
  exact ⟨hyunit.unit, hy1, Units.ext (by simp [hyu])⟩

end Torsion

section ExactIndex

variable (p K) in
/-- The number `#μ_{p^k}(K)` of `p^k`-th roots of unity of `K` (all of which are units of `𝒪`). -/
noncomputable def muCard (k : ℕ) : ℕ :=
  Nat.card (powMonoidHom (p ^ k) : (𝒪 p K)ˣ →* (𝒪 p K)ˣ).ker

/-- **`[𝒪ˣ : (𝒪ˣ)^{p^k}] = #μ_{p^k}(K) · q^{ke}`.** -/
theorem powIndex_integers_p_pow (k : ℕ) :
    powIndex (𝒪 p K)ˣ (p ^ k) = muCard p K k * q p K ^ (k * e p ℚ_[p] K) := by
  set a := e p ℚ_[p] K + 1
  set n := p ^ k
  set V := unitFilt p K a
  set W := unitFilt p K (a + k * e p ℚ_[p] K)
  set P := (powMonoidHom n : (𝒪 p K)ˣ →* (𝒪 p K)ˣ).range
  set T := (powMonoidHom n : (𝒪 p K)ˣ →* (𝒪 p K)ˣ).ker
  have hq := one_lt_q p K
  have hWP : W ≤ P := by
    intro u hu
    obtain ⟨y, -, hy⟩ := unitFilt_le_map_pow k hu
    exact ⟨y, hy⟩
  -- `[U : W] = [P : W] [U : P]`
  have h1 := Subgroup.relIndex_mul_index hWP
  -- `[P : W] = [U : C]` with `C = {u | uⁿ ∈ W}`
  set f : (𝒪 p K)ˣ →* P := (powMonoidHom n : (𝒪 p K)ˣ →* (𝒪 p K)ˣ).rangeRestrict
  have hf : Function.Surjective f := MonoidHom.rangeRestrict_surjective _
  have h2 : W.relIndex P = ((W.subgroupOf P).comap f).index := by
    rw [Subgroup.index_comap_of_surjective _ hf]; rfl
  -- `C = V ⊔ T`
  have hC : (W.subgroupOf P).comap f = V ⊔ T := by
    apply le_antisymm
    · intro u hu
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hu
      change u ^ n ∈ W at hu
      obtain ⟨y, hyV, hy⟩ := unitFilt_le_map_pow k hu
      have ht : u * y⁻¹ ∈ T := by
        rw [MonoidHom.mem_ker, powMonoidHom_apply, mul_pow, inv_pow, hy, mul_inv_cancel]
      have : u = (u * y⁻¹) * y := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hyV)
    · refine sup_le ?_ ?_
      · intro u hu
        rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
        exact pow_p_pow_mem_unitFilt_add hu k
      · intro u hu
        rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
        change u ^ n ∈ W
        have hu' : u ^ n = 1 := (MonoidHom.mem_ker).1 hu
        rw [hu']
        exact one_mem _
  -- `[U : V] = [V ⊔ T : V] [U : V ⊔ T]` and `[V ⊔ T : V] = #T`
  have h3 := Subgroup.relIndex_mul_index (le_sup_left : V ≤ V ⊔ T)
  have h4 : V.relIndex (V ⊔ T) = Nat.card T := by
    rw [Subgroup.relIndex_sup_left]
    have hVT : V.subgroupOf T = ⊥ := by
      rw [eq_bot_iff]
      intro t ht
      rw [Subgroup.mem_subgroupOf] at ht
      rw [Subgroup.mem_bot]
      exact Subtype.ext (eq_one_of_pow_p_pow_eq_one ht ((MonoidHom.mem_ker).1 t.2))
    rw [Subgroup.relIndex, hVT, Subgroup.index_bot]
  rw [h2, hC] at h1
  rw [h4] at h3
  -- indices of the filtration
  have hVi : V.index = q p K ^ a - q p K ^ (a - 1) := index_unitFilt_eq (by omega)
  have hWi : W.index = q p K ^ (k * e p ℚ_[p] K) * (q p K ^ a - q p K ^ (a - 1)) := by
    rw [index_unitFilt_eq (by omega), Nat.mul_sub, ← pow_add, ← pow_add]
    congr 2 <;> omega
  have hpos : 0 < q p K ^ a - q p K ^ (a - 1) := by
    have : q p K ^ (a - 1) < q p K ^ a := Nat.pow_lt_pow_right hq (by omega)
    omega
  -- combine: `[U:P] · [U:V] = [U:W] · #T`
  have key : P.index * V.index = W.index * Nat.card T := by
    rw [← h1, ← h3]; ring
  rw [hVi, hWi] at key
  have : P.index = q p K ^ (k * e p ℚ_[p] K) * Nat.card T :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [key]; ring)
  rw [powIndex, this, muCard, mul_comm]

/-- **`[Kˣ : (Kˣ)^{p^k}] = #μ_{p^k}(K) · p^{k([K:ℚ_p] + 1)}`.** -/
theorem powIndex_p_pow (k : ℕ) :
    powIndex Kˣ (p ^ k) = muCard p K k * p ^ (k * (Module.finrank ℚ_[p] K + 1)) := by
  rw [powIndex_units_eq (p := p) (pow_ne_zero _ hp.out.ne_zero), powIndex_integers_p_pow,
    mul_comm k, pow_mul, q_pow_e, ← pow_mul]
  ring

end ExactIndex

end Iut.Reconstruction
