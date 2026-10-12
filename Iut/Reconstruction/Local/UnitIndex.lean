/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.UnramifiedExistence
import ContinuousKummerTheory.Kummer.PAdic

/-!
# Indices of `n`-th powers in `p`-adic fields (roadmap P17, M1a)

For a finite extension `K/ℚ_p` write `N(n) = [Kˣ : (Kˣ)ⁿ]` (`Iut.Reconstruction.powIndex`).
By local duality `N(n)` is the number of continuous characters `G_K → ℤ/n`
(`Local/CharCount.lean`), so everything that can be read off from the function `n ↦ N(n)` is
determined by the topological group `G_K` ([AbsTopIII], Proposition 5.8 (i); [AbsAnab],
Proposition 1.2.1 (i)). Here we compute enough of `N` for that purpose:

* `Iut.Reconstruction.powIndex_units_eq` : `N(n) = n · [𝒪ˣ : (𝒪ˣ)ⁿ]` for `n ≥ 1`
  (valuation sequence `1 → 𝒪ˣ → Kˣ → ℤ → 0`).
-/

open IsLocalRing PadicField

namespace Iut.Reconstruction

section Group

variable (A : Type*) [CommGroup A]

/-- The index `[A : Aⁿ]` of the subgroup of `n`-th powers of a commutative group. -/
noncomputable def powIndex (n : ℕ) : ℕ := (powMonoidHom n : A →* A).range.index

variable {A}

theorem mem_powRange {n : ℕ} {x : A} :
    x ∈ (powMonoidHom n : A →* A).range ↔ ∃ y : A, y ^ n = x := Iff.rfl

end Group

section Units

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

variable (p K) in
/-- The inclusion `𝒪ˣ → Kˣ`. -/
noncomputable def unitsIncl : (𝒪 p K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝒪 p K) K : 𝒪 p K →* K)

@[simp]
theorem coe_unitsIncl (u : (𝒪 p K)ˣ) : ((unitsIncl p K u : Kˣ) : K) = ((u : 𝒪 p K) : K) := rfl

theorem unitsIncl_injective : Function.Injective (unitsIncl p K) := by
  intro u u' h
  apply Units.ext
  apply Integers.ext
  have := congrArg (fun x : Kˣ => (x : K)) h
  simpa using this

theorem nrm_unit (u : (𝒪 p K)ˣ) : nrm p K ((u : 𝒪 p K) : K) = 1 :=
  Integers.isUnit_iff_nrm_eq_one.1 u.isUnit

theorem v_unit (u : (𝒪 p K)ˣ) : v p ((u : 𝒪 p K) : K) = 0 :=
  (nrm_eq_one_iff_v_eq_zero (fun h => u.ne_zero (Integers.coe_eq_zero_iff.1 h))).1 (nrm_unit u)

/-- An element of absolute value one, as a unit of `𝒪`. -/
noncomputable def unitOfNrm (x : K) (hx : nrm p K x = 1) : (𝒪 p K)ˣ where
  val := Integers.mk x hx.le
  inv := Integers.mk x⁻¹ (by rw [nrm_inv, hx, inv_one])
  val_inv := Integers.ext (by
    have : x ≠ 0 := fun h => by rw [h, nrm_eq_zero_iff.2 rfl] at hx; exact zero_ne_one hx
    simp [this])
  inv_val := Integers.ext (by
    have : x ≠ 0 := fun h => by rw [h, nrm_eq_zero_iff.2 rfl] at hx; exact zero_ne_one hx
    simp [this])

theorem coe_unitOfNrm (x : K) (hx : nrm p K x = 1) :
    (((unitOfNrm x hx : (𝒪 p K)ˣ) : 𝒪 p K) : K) = x := rfl

theorem exists_unitsIncl_eq {x : Kˣ} (hx : nrm p K (x : K) = 1) :
    ∃ u : (𝒪 p K)ˣ, unitsIncl p K u = x :=
  ⟨unitOfNrm (x : K) hx, Units.ext (coe_unitOfNrm _ hx)⟩

/-- `(Kˣ)ⁿ ∩ 𝒪ˣ = (𝒪ˣ)ⁿ`. -/
theorem comap_unitsIncl_powRange {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : Kˣ →* Kˣ).range.comap (unitsIncl p K) =
      (powMonoidHom n : (𝒪 p K)ˣ →* (𝒪 p K)ˣ).range := by
  ext u
  simp only [Subgroup.mem_comap, mem_powRange]
  constructor
  · rintro ⟨y, hy⟩
    have hy1 : nrm p K (y : K) = 1 := by
      have h := congrArg (fun z : Kˣ => nrm p K (z : K)) hy
      simp only [Units.val_pow_eq_pow_val, nrm_pow, coe_unitsIncl, nrm_unit] at h
      exact (pow_eq_one_iff_of_nonneg (nrm_nonneg _) hn).1 h
    obtain ⟨w, hw⟩ := exists_unitsIncl_eq hy1
    refine ⟨w, unitsIncl_injective ?_⟩
    rw [map_pow, hw, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨unitsIncl p K y, by rw [map_pow]⟩

variable (p K) in
/-- The valuation modulo `n`, `Kˣ → ℤ/n`. -/
noncomputable def vMod (n : ℕ) : Kˣ →* Multiplicative (ZMod n) where
  toFun x := Multiplicative.ofAdd ((v p (x : K) : ℤ) : ZMod n)
  map_one' := by simp [v_one]
  map_mul' x y := by
    rw [Units.val_mul, v_mul x.ne_zero y.ne_zero, Int.cast_add, ofAdd_add]

theorem vMod_surjective (n : ℕ) : Function.Surjective (vMod p K n) := by
  intro z
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd z)
  have hπ := uniformizer_spec (p := p) (K := K)
  refine ⟨Units.mk0 (uniformizer p K) hπ.ne_zero ^ k, ?_⟩
  simp only [vMod, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_zpow_eq_zpow_val, Units.val_mk0,
    v_zpow hπ.ne_zero]
  rw [show v p (uniformizer p K) = 1 from hπ, mul_one, hk]
  rfl

theorem ker_vMod {n : ℕ} :
    (vMod p K n).ker = (powMonoidHom n : Kˣ →* Kˣ).range ⊔ (unitsIncl p K).range := by
  apply le_antisymm
  · intro x hx
    have hx' : ((v p (x : K) : ℤ) : ZMod n) = 0 := by
      have := (MonoidHom.mem_ker).1 hx
      simpa [vMod] using this
    obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hx'
    have hπ := uniformizer_spec (p := p) (K := K)
    obtain ⟨u, hu, hxu⟩ := eq_zpow_mul_unit hπ x.ne_zero
    obtain ⟨w, hw⟩ := exists_unitsIncl_eq (x := Units.mk0 u (by
      intro h; rw [h, nrm_eq_zero_iff.2 rfl] at hu; exact zero_ne_one hu)) hu
    have hx2 : x = (Units.mk0 (uniformizer p K) hπ.ne_zero ^ c) ^ n * unitsIncl p K w := by
      apply Units.ext
      rw [Units.val_mul, hw, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
        Units.val_mk0, Units.val_mk0, hxu, hc, ← zpow_natCast, ← zpow_mul, mul_comm (n : ℤ) c]
    rw [hx2]
    exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨w, rfl⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      rw [MonoidHom.mem_ker]
      simp only [vMod, MonoidHom.coe_mk, OneHom.coe_mk, powMonoidHom_apply,
        Units.val_pow_eq_pow_val, v_pow y.ne_zero, Int.cast_mul, Int.cast_natCast,
        ZMod.natCast_self, zero_mul, ofAdd_zero]
    · rintro _ ⟨w, rfl⟩
      rw [MonoidHom.mem_ker]
      simp [vMod, v_unit]

/-- **`N(n) = n · [𝒪ˣ : (𝒪ˣ)ⁿ]`.** -/
theorem powIndex_units_eq {n : ℕ} (hn : n ≠ 0) :
    powIndex Kˣ n = n * powIndex (𝒪 p K)ˣ n := by
  set P := (powMonoidHom n : Kˣ →* Kˣ).range
  have h1 : P.relIndex (P ⊔ (unitsIncl p K).range) * (P ⊔ (unitsIncl p K).range).index =
      P.index := Subgroup.relIndex_mul_index le_sup_left
  have h2 : (P ⊔ (unitsIncl p K).range).index = n := by
    haveI : NeZero n := ⟨hn⟩
    rw [← ker_vMod, Subgroup.index_ker, MonoidHom.range_eq_top.2 (vMod_surjective n),
      Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [Subgroup.relIndex_sup_left, ← Subgroup.index_comap, comap_unitsIncl_powRange hn,
    h2] at h1
  rw [powIndex, ← h1, powIndex, mul_comm]

end Units

section Coprime

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

theorem nrm_natCast_eq_one {n : ℕ} (hn : p.Coprime n) : nrm p K (n : K) = 1 := by
  rw [show (n : K) = algebraMap ℚ_[p] K (n : ℚ_[p]) by simp, nrm_algebraMap,
    Padic.norm_natCast_eq_one_iff]
  exact hn

theorem isUnit_natCast_integers {n : ℕ} (hn : p.Coprime n) : IsUnit (n : 𝒪 p K) := by
  rw [Integers.isUnit_iff_nrm_eq_one]
  simpa using nrm_natCast_eq_one (K := K) hn

variable (p K) in
/-- Reduction of units, `𝒪ˣ → 𝓴ˣ`. -/
noncomputable def resUnits : (𝒪 p K)ˣ →* (𝓴 p K)ˣ :=
  Units.map (residue (𝒪 p K)).toMonoidHom

theorem resUnits_surjective : Function.Surjective (resUnits p K) :=
  IsLocalRing.surjective_units_map_of_local_ringHom _ residue_surjective inferInstance

theorem sub_one_mem_of_resUnits {u : (𝒪 p K)ˣ} (hu : resUnits p K u = 1) :
    (u : 𝒪 p K) - 1 ∈ maximalIdeal (𝒪 p K) := by
  have h : residue (𝒪 p K) (u : 𝒪 p K) = residue (𝒪 p K) 1 := by
    rw [map_one]
    exact congrArg Units.val hu
  exact Ideal.Quotient.eq.1 h

/-- **Hensel**: for `p ∤ n`, every principal unit is an `n`-th power. -/
theorem ker_resUnits_le_powRange {n : ℕ} (hn : p.Coprime n) (hn0 : n ≠ 0) :
    (resUnits p K).ker ≤ (powMonoidHom n : (𝒪 p K)ˣ →* (𝒪 p K)ˣ).range := by
  intro u hu
  have hm := sub_one_mem_of_resUnits ((MonoidHom.mem_ker).1 hu)
  obtain ⟨c, hc⟩ := (isUnit_natCast_integers (K := K) hn).pow 2
  set d : 𝒪 p K := ((u : 𝒪 p K) - 1) * (c⁻¹ : (𝒪 p K)ˣ) with hd
  have hdm : d ∈ maximalIdeal (𝒪 p K) := Ideal.mul_mem_right _ _ hm
  obtain ⟨y, hy⟩ := KummerTheory.exists_pow_eq_one_add (maximalIdeal (𝒪 p K)) n hdm 1
  have hyu : y ^ n = (u : 𝒪 p K) := by
    rw [hy, hd, ← hc]
    simp only [mul_one]
    rw [mul_comm ((u : 𝒪 p K) - 1), ← mul_assoc, Units.mul_inv, one_mul, add_sub_cancel]
  have hyunit : IsUnit y := (isUnit_pow_iff hn0).1 (hyu ▸ u.isUnit)
  refine ⟨hyunit.unit, Units.ext ?_⟩
  simp [hyu]

theorem powRange_eq_comap_resUnits {n : ℕ} (hn : p.Coprime n) (hn0 : n ≠ 0) :
    (powMonoidHom n : (𝒪 p K)ˣ →* (𝒪 p K)ˣ).range =
      (powMonoidHom n : (𝓴 p K)ˣ →* (𝓴 p K)ˣ).range.comap (resUnits p K) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact ⟨resUnits p K y, by simp⟩
  · rintro u ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := resUnits_surjective z
    have h1 : u * (y ^ n)⁻¹ ∈ (resUnits p K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow]
      simp only [powMonoidHom_apply] at hz
      rw [hz, mul_inv_cancel]
    obtain ⟨w, hw⟩ := ker_resUnits_le_powRange hn hn0 h1
    refine ⟨y * w, ?_⟩
    simp only [powMonoidHom_apply] at hw ⊢
    rw [mul_pow, hw, mul_comm u, ← mul_assoc, mul_inv_cancel, one_mul]

variable (p K) in
theorem natCard_units_residue : Nat.card (𝓴 p K)ˣ = q p K - 1 := Nat.card_units _

/-- **`[𝒪ˣ : (𝒪ˣ)ⁿ] = gcd(q − 1, n)`** for `p ∤ n`. -/
theorem powIndex_integers_of_coprime {n : ℕ} (hn : p.Coprime n) (hn0 : n ≠ 0) :
    powIndex (𝒪 p K)ˣ n = (q p K - 1).gcd n := by
  rw [powIndex, powRange_eq_comap_resUnits hn hn0,
    Subgroup.index_comap_of_surjective _ resUnits_surjective,
    IsCyclic.index_powMonoidHom_range, natCard_units_residue p K]

/-- **`[Kˣ : (Kˣ)ⁿ] = n · gcd(q − 1, n)`** for `p ∤ n`. -/
theorem powIndex_of_coprime {n : ℕ} (hn : p.Coprime n) (hn0 : n ≠ 0) :
    powIndex Kˣ n = n * (q p K - 1).gcd n := by
  rw [powIndex_units_eq (p := p) hn0, powIndex_integers_of_coprime hn hn0]

end Coprime

section Absolute

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

theorem nrm_Qp (x : ℚ_[p]) : nrm p ℚ_[p] x = ‖x‖ := nrm_algebraMap (K := ℚ_[p]) x

variable (p) in
theorem v_p_Qp : v p ((p : ℚ_[p])) = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hπ := uniformizer_spec (p := p) (K := ℚ_[p])
  have hlt : ‖uniformizer p ℚ_[p]‖ < 1 := by
    rw [← nrm_Qp]; exact hπ.nrm_lt_one
  have hle : ‖uniformizer p ℚ_[p]‖ ≤ ‖(p : ℚ_[p])‖ := by
    have h := (Padic.norm_le_pow_iff_norm_lt_pow_add_one (uniformizer p ℚ_[p]) (-1)).2
      (by simpa using hlt)
    rw [Padic.norm_p]; rwa [zpow_neg_one] at h
  have h1 : v p ((p : ℚ_[p])) ≤ 1 := by
    rw [← nrm_Qp, ← nrm_Qp, nrm_le_iff_v_le hπ.ne_zero hp0] at hle
    exact hle.trans_eq hπ
  have h2 : 0 < v p ((p : ℚ_[p])) := by
    rw [← nrm_lt_one_iff_v_pos hp0, nrm_Qp, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  omega

variable (p K) in
/-- `v_K(p) = e(K/ℚ_p)`. -/
theorem v_natCast_p_eq : v p ((p : K)) = e p ℚ_[p] K := by
  rw [show (p : K) = algebraMap ℚ_[p] K (p : ℚ_[p]) by simp, v_algebraMap, v_p_Qp, mul_one]

variable (p) in
theorem q_Qp : q p ℚ_[p] = p := by
  rw [q, Nat.card_congr ((ResidueField.mapEquiv (integersQpEquiv p)).trans
    (PadicInt.residueField (p := p))).toEquiv, Nat.card_zmod]

variable (p K) in
/-- `q = p ^ f`. -/
theorem q_eq_p_pow_f : q p K = p ^ f p ℚ_[p] K := by
  rw [q_eq_pow_f (K := ℚ_[p]) (L := K), q_Qp]

variable (p K) in
/-- `q ^ e = p ^ [K : ℚ_p]`. -/
theorem q_pow_e : q p K ^ e p ℚ_[p] K = p ^ Module.finrank ℚ_[p] K := by
  rw [q_eq_p_pow_f, ← pow_mul, mul_comm, e_mul_f]

variable (p K) in
theorem e_pos' : 0 < e p ℚ_[p] K := e_pos

variable (p K) in
theorem p_coprime_q_sub_one : p.Coprime (q p K - 1) := by
  rw [q_eq_p_pow_f]
  have hf : 0 < f p ℚ_[p] K := f_pos
  have h1 : 1 ≤ p ^ f p ℚ_[p] K := Nat.one_le_pow _ _ hp.out.pos
  have h2 : Nat.Coprime (p ^ f p ℚ_[p] K) (p ^ f p ℚ_[p] K - 1) :=
    (Nat.coprime_self_sub_right h1).2 (Nat.coprime_one_right _)
  exact Nat.Coprime.coprime_dvd_left (dvd_pow_self p hf.ne') h2

end Absolute

section Filtration

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

variable (p K) in
/-- The unit filtration `U^(m) = 1 + 𝔪^m ⊆ 𝒪ˣ`. -/
noncomputable def unitFilt (m : ℕ) : Subgroup (𝒪 p K)ˣ where
  carrier := {u | (u : 𝒪 p K) - 1 ∈ maximalIdeal (𝒪 p K) ^ m}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have h : ((a * b : (𝒪 p K)ˣ) : 𝒪 p K) - 1 =
        (a : 𝒪 p K) * ((b : 𝒪 p K) - 1) + ((a : 𝒪 p K) - 1) := by
      rw [Units.val_mul]; ring
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [h]
    exact add_mem (Ideal.mul_mem_left _ _ hb) ha
  inv_mem' {a} ha := by
    have h : ((a⁻¹ : (𝒪 p K)ˣ) : 𝒪 p K) - 1 =
        -(((a⁻¹ : (𝒪 p K)ˣ) : 𝒪 p K) * ((a : 𝒪 p K) - 1)) := by
      rw [mul_sub, Units.inv_mul]; ring
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [h]
    exact neg_mem (Ideal.mul_mem_left _ _ ha)

theorem mem_unitFilt {m : ℕ} {u : (𝒪 p K)ˣ} :
    u ∈ unitFilt p K m ↔ (u : 𝒪 p K) - 1 ∈ maximalIdeal (𝒪 p K) ^ m := Iff.rfl

variable (p K) in
/-- Reduction of units modulo `𝔪^m`. -/
noncomputable def unitsMod (m : ℕ) : (𝒪 p K)ˣ →* (𝒪 p K ⧸ maximalIdeal (𝒪 p K) ^ m)ˣ :=
  Units.map (Ideal.Quotient.mk (maximalIdeal (𝒪 p K) ^ m)).toMonoidHom

theorem ker_unitsMod (m : ℕ) : (unitsMod p K m).ker = unitFilt p K m := by
  ext u
  rw [MonoidHom.mem_ker, mem_unitFilt, ← Ideal.Quotient.eq, Units.ext_iff]
  simp [unitsMod]

theorem isLocalHom_mk_pow {m : ℕ} (hm : m ≠ 0) :
    IsLocalHom (Ideal.Quotient.mk (maximalIdeal (𝒪 p K) ^ m)) := by
  refine ⟨fun x hx => ?_⟩
  by_contra hxu
  have hxm : x ∈ maximalIdeal (𝒪 p K) := (mem_maximalIdeal _).2 hxu
  have h0 : (Ideal.Quotient.mk (maximalIdeal (𝒪 p K) ^ m) x) ^ m = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hxm m
  have hnt : Nontrivial (𝒪 p K ⧸ maximalIdeal (𝒪 p K) ^ m) :=
    Ideal.Quotient.nontrivial_iff.2 (by
      rw [Ne, Ideal.eq_top_iff_one]
      intro h1
      exact (maximalIdeal.isMaximal (𝒪 p K)).ne_top
        ((Ideal.eq_top_iff_one _).2 (Ideal.pow_le_self hm h1)))
  exact (hx.pow m).ne_zero h0

theorem unitsMod_surjective {m : ℕ} (hm : m ≠ 0) : Function.Surjective (unitsMod p K m) :=
  haveI := isLocalHom_mk_pow (p := p) (K := K) hm
  IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective inferInstance

theorem index_unitFilt {m : ℕ} (hm : m ≠ 0) :
    (unitFilt p K m).index = Nat.card (𝒪 p K ⧸ maximalIdeal (𝒪 p K) ^ m)ˣ := by
  rw [← ker_unitsMod, Subgroup.index_ker, MonoidHom.range_eq_top.2 (unitsMod_surjective hm),
    Subgroup.card_top]

variable (p K) in
theorem card_quot_maximalIdeal_pow (m : ℕ) :
    Nat.card (𝒪 p K ⧸ maximalIdeal (𝒪 p K) ^ m) = q p K ^ m := by
  have h := cardQuot_pow_of_prime (S := 𝒪 p K) (Integers.maximalIdeal_ne_bot (p := p) (K := K))
    (i := m)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
  rw [h]
  rfl

instance finite_quot_maximalIdeal_pow (m : ℕ) :
    Finite (𝒪 p K ⧸ maximalIdeal (𝒪 p K) ^ m) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_quot_maximalIdeal_pow]
  exact pow_ne_zero _ (Nat.pos_of_ne_zero (by have := one_lt_q p K; omega)).ne'

theorem index_unitFilt_le {m : ℕ} (hm : m ≠ 0) : (unitFilt p K m).index ≤ q p K ^ m := by
  rw [index_unitFilt hm, ← card_quot_maximalIdeal_pow p K m]
  exact Nat.card_le_card_of_injective _ Units.val_injective

theorem le_index_unitFilt {m : ℕ} (hm : m ≠ 0) : q p K ^ m ≤ (unitFilt p K m).index * q p K := by
  set I := maximalIdeal (𝒪 p K) ^ m
  set S : Submodule (𝒪 p K) (𝒪 p K) := maximalIdeal (𝒪 p K)
  have hIS : (I : Submodule (𝒪 p K) (𝒪 p K)) ≤ S := Ideal.pow_le_self hm
  have hc := Submodule.card_quotient_mul_card_quotient S I hIS
  have hS : Nat.card (𝒪 p K ⧸ S) = q p K := rfl
  have hI : Nat.card (𝒪 p K ⧸ (I : Submodule (𝒪 p K) (𝒪 p K))) = q p K ^ m :=
    card_quot_maximalIdeal_pow p K m
  rw [hS, hI] at hc
  rw [← hc, index_unitFilt hm]
  refine Nat.mul_le_mul_right _ ?_
  have hnil : ∀ y ∈ S.map I.mkQ, IsNilpotent y := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨m, ?_⟩
    change (Ideal.Quotient.mk I x) ^ m = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hx m
  let F : S.map I.mkQ → (𝒪 p K ⧸ I)ˣ := fun y => (hnil y.1 y.2).isUnit_one_add.unit
  refine Nat.card_le_card_of_injective F fun y y' h => ?_
  have h' := congrArg (fun u : (𝒪 p K ⧸ I)ˣ => (u : 𝒪 p K ⧸ I)) h
  simp only [F, IsUnit.unit_spec] at h'
  exact Subtype.ext (add_left_cancel h')

end Filtration

section Submultiplicative

variable {A : Type*} [CommGroup A]

/-- `[A : A^{ab}] ≤ [A : Aᵃ] · [A : Aᵇ]`. -/
theorem powIndex_mul_le (a b : ℕ) [(powMonoidHom b : A →* A).range.FiniteIndex] :
    powIndex A (a * b) ≤ powIndex A a * powIndex A b := by
  set Pa := (powMonoidHom a : A →* A).range
  set Pab := (powMonoidHom (a * b) : A →* A).range
  have hle : Pab ≤ Pa := by
    rintro _ ⟨y, rfl⟩
    exact ⟨y ^ b, by simp only [powMonoidHom_apply, ← pow_mul, mul_comm]⟩
  have h1 := Subgroup.relIndex_mul_index hle
  set f : A →* Pa := (powMonoidHom a : A →* A).rangeRestrict
  have hf : Function.Surjective f := MonoidHom.rangeRestrict_surjective _
  have h2 : Pab.relIndex Pa = ((Pab.subgroupOf Pa).comap f).index := by
    rw [Subgroup.index_comap_of_surjective _ hf]; rfl
  have h3 : (powMonoidHom b : A →* A).range ≤ (Pab.subgroupOf Pa).comap f := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    refine ⟨y, ?_⟩
    change y ^ (a * b) = (y ^ b) ^ a
    rw [← pow_mul, mul_comm]
  have h4 := Subgroup.index_antitone h3
  rw [powIndex, powIndex, powIndex, ← h1, h2, mul_comm]
  exact Nat.mul_le_mul_left _ h4

end Submultiplicative

section PPower

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

/-- **Hensel's lemma in root form**: for `d ∈ 𝔪`, `1 + n² d w = (1 + n d y)ⁿ` for some `y`
(the argument of `KummerTheory.exists_pow_eq_one_add`, keeping track of the root). -/
theorem exists_one_add_pow_eq (n : ℕ) {d : 𝒪 p K} (hd : d ∈ maximalIdeal (𝒪 p K))
    (w : 𝒪 p K) :
    ∃ y : 𝒪 p K, (1 + (n : 𝒪 p K) * d * y) ^ n = 1 + (n : 𝒪 p K) ^ 2 * d * w := by
  obtain _ | m := n
  · exact ⟨0, by simp⟩
  obtain ⟨y, hy⟩ := KummerTheory.exists_fixedPoint_of_adicContraction (maximalIdeal (𝒪 p K))
    (fun y => w - KummerTheory.powCorr m d y)
    (fun y y' => by
      refine ⟨-∑ k ∈ Finset.range m, ((m + 1).choose (k + 2) : 𝒪 p K) *
        ((m + 1 : ℕ) : 𝒪 p K) ^ k * d ^ (k + 1) *
          ∑ i ∈ Finset.range (k + 2), y ^ i * y' ^ (k + 2 - 1 - i), ?_, ?_⟩
      · refine neg_mem (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_)
        exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hd _ k.succ_pos)
      · simp only [KummerTheory.powCorr, sub_sub_sub_cancel_left, neg_mul, Finset.sum_mul,
          ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_assoc _ (∑ i ∈ _, _), geom_sum₂_mul]
        ring)
  refine ⟨y, ?_⟩
  rw [KummerTheory.one_add_pow_eq, show y + KummerTheory.powCorr m d y = w by
    linear_combination -hy]

theorem ϖ_mem_maximalIdeal : (Integers.ϖ p K : 𝒪 p K) ∈ maximalIdeal (𝒪 p K) :=
  (mem_maximalIdeal _).2 (Integers.irreducible_ϖ).not_isUnit

/-- Iterated Hensel: `1 + p^{k+1} ϖ w` is a `p^k`-th power. -/
theorem exists_pow_p_pow_eq (k : ℕ) (w : 𝒪 p K) :
    ∃ y : 𝒪 p K, y ^ (p ^ k) = 1 + (p : 𝒪 p K) ^ (k + 1) * Integers.ϖ p K * w := by
  induction k generalizing w with
  | zero => exact ⟨1 + p * Integers.ϖ p K * w, by simp⟩
  | succ k ih =>
    have hd : (p : 𝒪 p K) ^ k * Integers.ϖ p K ∈ maximalIdeal (𝒪 p K) :=
      Ideal.mul_mem_left _ _ ϖ_mem_maximalIdeal
    obtain ⟨y, hy⟩ := exists_one_add_pow_eq p hd w
    obtain ⟨z, hz⟩ := ih y
    refine ⟨z, ?_⟩
    rw [pow_succ, pow_mul, hz]
    convert hy using 2 <;> ring

theorem coe_natCast_integers (n : ℕ) : (((n : 𝒪 p K)) : K) = (n : K) := by
  rw [Integers.coe_eq_algebraMap, map_natCast]

theorem v_p_pow_mul_ϖ (k : ℕ) :
    v p ((((p : 𝒪 p K) ^ (k + 1) * Integers.ϖ p K : 𝒪 p K)) : K) = (k + 1) * e p ℚ_[p] K + 1 := by
  have hp0 : (p : K) ≠ 0 := natCast_p_ne_zero
  have hϖ0 : ((Integers.ϖ p K : 𝒪 p K) : K) ≠ 0 := fun h =>
    (Integers.irreducible_ϖ (p := p) (K := K)).ne_zero (Integers.coe_eq_zero_iff.1 h)
  rw [Integers.coe_mul, Integers.coe_pow, coe_natCast_integers,
    v_mul (pow_ne_zero _ hp0) hϖ0, v_pow hp0, v_natCast_p_eq, Integers.v_ϖ]
  push_cast; ring

/-- `U^((k+1)e+1) ⊆ (𝒪ˣ)^{p^k}`. -/
theorem unitFilt_le_powRange (k : ℕ) :
    unitFilt p K ((k + 1) * e p ℚ_[p] K + 1) ≤
      (powMonoidHom (p ^ k) : (𝒪 p K)ˣ →* (𝒪 p K)ˣ).range := by
  intro u hu
  rw [mem_unitFilt, Integers.mem_maximalIdeal_pow_iff] at hu
  have hp0 : (p : 𝒪 p K) ≠ 0 := fun h => by
    have := congrArg (fun x : 𝒪 p K => (x : K)) h
    simp only [coe_natCast_integers, Integers.coe_zero] at this
    exact natCast_p_ne_zero this
  have ha : (p : 𝒪 p K) ^ (k + 1) * Integers.ϖ p K ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp0) Integers.irreducible_ϖ.ne_zero
  have hdvd : (p : 𝒪 p K) ^ (k + 1) * Integers.ϖ p K ∣ (u : 𝒪 p K) - 1 := by
    rw [Integers.dvd_iff_v_le ha, v_p_pow_mul_ϖ]
    rcases hu with h | h
    · exact Or.inl h
    · right; exact_mod_cast h
  obtain ⟨w, hw⟩ := hdvd
  obtain ⟨y, hy⟩ := exists_pow_p_pow_eq (K := K) k w
  have hyu : y ^ (p ^ k) = (u : 𝒪 p K) := by rw [hy, ← hw, add_sub_cancel]
  have hyunit : IsUnit y :=
    (isUnit_pow_iff (pow_ne_zero _ hp.out.ne_zero)).1 (hyu ▸ u.isUnit)
  exact ⟨hyunit.unit, Units.ext (by simp [hyu])⟩

instance finiteIndex_unitFilt (m : ℕ) : (unitFilt p K m).FiniteIndex := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : unitFilt p K 0 = ⊤ := by
      ext u; simp [mem_unitFilt]
    rw [this]; infer_instance
  · exact ⟨by rw [index_unitFilt hm.ne']; exact Nat.card_pos.ne'⟩

/-- **Upper bound**: `[𝒪ˣ : (𝒪ˣ)^{p^k}] ≤ q^{(k+1)e+1}`. -/
theorem powIndex_p_pow_le (k : ℕ) :
    powIndex (𝒪 p K)ˣ (p ^ k) ≤ q p K ^ ((k + 1) * e p ℚ_[p] K + 1) :=
  (Subgroup.index_antitone (unitFilt_le_powRange k)).trans (index_unitFilt_le (by omega))

/-- `(1 + 𝔪^j)^p ⊆ 1 + 𝔪^{j + min(e, j)}`. -/
theorem one_add_pow_p_sub_one_mem {j : ℕ} {x : 𝒪 p K} (hx : x ∈ maximalIdeal (𝒪 p K) ^ j) :
    (1 + x) ^ p - 1 ∈ maximalIdeal (𝒪 p K) ^ (j + min (e p ℚ_[p] K) j) := by
  obtain ⟨r, hr⟩ := _root_.exists_add_pow_prime_eq hp.out (1 : 𝒪 p K) x
  have h : (1 + x) ^ p - 1 = x ^ p + (p : 𝒪 p K) * x * r := by rw [hr]; ring
  rw [h]
  have hp2 : 2 ≤ p := hp.out.two_le
  refine add_mem ?_ ?_
  · refine Ideal.pow_le_pow_right (n := j * p) ?_ ?_
    · have : j * 2 ≤ j * p := Nat.mul_le_mul_left _ hp2
      omega
    · rw [pow_mul]; exact Ideal.pow_mem_pow hx p
  · refine Ideal.mul_mem_right _ _ ?_
    have hpm : (p : 𝒪 p K) ∈ maximalIdeal (𝒪 p K) ^ e p ℚ_[p] K := by
      rw [Integers.mem_maximalIdeal_pow_iff, coe_natCast_integers, v_natCast_p_eq]
      exact Or.inr le_rfl
    refine Ideal.pow_le_pow_right (n := e p ℚ_[p] K + j) (by omega) ?_
    rw [pow_add]
    exact Ideal.mul_mem_mul hpm hx

/-- The exponents `m(0) = 1`, `m(k+1) = m(k) + min(e, m(k))`. -/
def mSeq (e : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => mSeq e k + min e (mSeq e k)

theorem mSeq_succ (e k : ℕ) : mSeq e (k + 1) = mSeq e k + min e (mSeq e k) := rfl

theorem pow_p_pow_mem_unitFilt {u : (𝒪 p K)ˣ} (hu : u ∈ unitFilt p K 1) (k : ℕ) :
    u ^ (p ^ k) ∈ unitFilt p K (mSeq (e p ℚ_[p] K) k) := by
  induction k with
  | zero => simpa [mSeq] using hu
  | succ k ih =>
    rw [mem_unitFilt] at ih ⊢
    have h := one_add_pow_p_sub_one_mem ih
    rw [add_sub_cancel] at h
    rw [pow_succ, pow_mul, Units.val_pow_eq_pow_val, mSeq_succ]
    exact h

theorem pow_q_sub_one_mem_unitFilt (u : (𝒪 p K)ˣ) : u ^ (q p K - 1) ∈ unitFilt p K 1 := by
  rw [mem_unitFilt, pow_one]
  refine sub_one_mem_of_resUnits ?_
  rw [map_pow, ← natCard_units_residue p K]
  exact pow_card_eq_one'

theorem powRange_le_unitFilt (k : ℕ) :
    (powMonoidHom ((q p K - 1) * p ^ k) : (𝒪 p K)ˣ →* (𝒪 p K)ˣ).range ≤
      unitFilt p K (mSeq (e p ℚ_[p] K) k) := by
  rintro _ ⟨y, rfl⟩
  simp only [powMonoidHom_apply, pow_mul]
  exact pow_p_pow_mem_unitFilt (pow_q_sub_one_mem_unitFilt y) k

theorem powIndex_integers_ne_zero {n : ℕ} (hn : n ≠ 0) : powIndex (𝒪 p K)ˣ n ≠ 0 := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  haveI := KummerTheory.finiteIndex_powRange_of_isDiscreteValuationRing (𝒪 p K) K n
    (Nat.cast_ne_zero.2 hn)
  have h := powIndex_units_eq (p := p) (K := K) hn
  intro h0
  rw [h0, mul_zero] at h
  exact Subgroup.FiniteIndex.index_ne_zero h

instance finiteIndex_powRange_integers (n : ℕ) [NeZero n] :
    (powMonoidHom n : (𝒪 p K)ˣ →* (𝒪 p K)ˣ).range.FiniteIndex :=
  ⟨powIndex_integers_ne_zero (NeZero.ne n)⟩

theorem mSeq_pos (e k : ℕ) : 0 < mSeq e k := by
  induction k with
  | zero => simp [mSeq]
  | succ k ih => rw [mSeq_succ]; omega

/-- **Lower bound**: `q^{m(k)} ≤ (q − 1) · q · [𝒪ˣ : (𝒪ˣ)^{p^k}]`. -/
theorem le_powIndex_p_pow (k : ℕ) :
    q p K ^ mSeq (e p ℚ_[p] K) k ≤ (q p K - 1) * q p K * powIndex (𝒪 p K)ˣ (p ^ k) := by
  have hq1 : q p K - 1 ≠ 0 := by have := one_lt_q p K; omega
  haveI : NeZero ((q p K - 1) * p ^ k) :=
    ⟨mul_ne_zero hq1 (pow_ne_zero _ hp.out.ne_zero)⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have h1 := le_index_unitFilt (p := p) (K := K) (mSeq_pos (e p ℚ_[p] K) k).ne'
  have h2 := Subgroup.index_antitone (powRange_le_unitFilt (p := p) (K := K) k)
  have h3 := powIndex_mul_le (A := (𝒪 p K)ˣ) (q p K - 1) (p ^ k)
  rw [powIndex_integers_of_coprime (p_coprime_q_sub_one p K) hq1, Nat.gcd_self] at h3
  calc q p K ^ mSeq (e p ℚ_[p] K) k ≤ (unitFilt p K _).index * q p K := h1
    _ ≤ powIndex (𝒪 p K)ˣ ((q p K - 1) * p ^ k) * q p K := Nat.mul_le_mul_right _ h2
    _ ≤ (q p K - 1) * powIndex (𝒪 p K)ˣ (p ^ k) * q p K := Nat.mul_le_mul_right _ h3
    _ = _ := by ring

theorem succ_le_mSeq {e : ℕ} (he : 0 < e) (k : ℕ) : k + 1 ≤ mSeq e k := by
  induction k with
  | zero => simp [mSeq]
  | succ k ih => rw [mSeq_succ]; have := mSeq_pos e k; omega

theorem mSeq_lower {e : ℕ} (k : ℕ) : min (k + 1) e ≤ mSeq e k ∧ e * (k + 1) ≤ mSeq e k + e * e := by
  induction k with
  | zero =>
    refine ⟨by simp [mSeq], ?_⟩
    simp only [mSeq, zero_add, mul_one]
    nlinarith
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [mSeq_succ]
    rcases le_or_gt e (mSeq e k) with h | h
    · rw [min_eq_left h]
      refine ⟨by omega, ?_⟩
      nlinarith
    · rw [min_eq_right h.le]
      have hk : k + 1 < e := by omega
      refine ⟨by omega, ?_⟩
      nlinarith

end PPower

end Iut.Reconstruction
