/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.CharCount

/-!
# Group-theoretic reconstruction of the basic invariants of a `p`-adic field
(roadmap P17, M1c)

[AbsTopIII], Proposition 5.8 (i) (and [AbsAnab], Proposition 1.2.1 (i), as used in IUT I,
Remark 1.9.2 and IUT III, Proposition 1.2): from the absolute Galois group `G_K` of a finite
extension `K/ℚ_p`, regarded as an abstract topological group, one reconstructs

* the residue characteristic `p`,
* the cardinality `q = p^f` of the residue field, and `f`,
* the absolute degree `[K : ℚ_p]`, and the absolute ramification index `e`.

## The algorithms

All invariants are read off from the function `N(n) = #Hom_cont(G, ℤ/n)`
(`Iut.Reconstruction.charCount`), which equals `[Kˣ : (Kˣ)ⁿ]` by local duality
(`charCount_gal`):

* `primeOf N`: the unique prime `ℓ` such that `N(n) = O(n)` on `n` prime to `ℓ` (for `p ∤ n`,
  `N(n) = n · gcd(q − 1, n)`; for `ℓ ≠ p` the values `N(p^k)/p^k` are unbounded);
* `qOf N ℓ = 1 + min {C | N(n) ≤ C n for all n prime to ℓ}` (attained at `n = q − 1`);
* `degOf N ℓ = min {D | N(ℓ^k) = O(ℓ^{k(D+1)})}` (`N(p^k)` grows like `p^{k([K:ℚ_p]+1)}`);
* `fOf = log_p q`, `eOf = [K : ℚ_p] / f`.

## Main results

* `Iut.Reconstruction.primeOf_eq`, `qOf_eq`, `degOf_eq`, `fOf_eq`, `eOf_eq`: the algorithms
  return `p`, `q`, `[K : ℚ_p]`, `f`, `e` on `N = [Kˣ : (Kˣ)^·]`;
* `Iut.Reconstruction.recPrime`, `recQ`, `recDeg`, `recF`, `recE`: the group-theoretic
  algorithms on topological groups, `isGroupTheoretic_recPrime` etc., and
  `recPrime_gal` etc.: their values on `Gal(Ω/K)`;
* `Iut.Reconstruction.galEquiv_invariants`: an isomorphism of topological groups
  `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` (`K/ℚ_p`, `K'/ℚ_{p'}`) forces `p = p'`, `[K : ℚ_p] = [K' : ℚ_{p'}]`,
  `q = q'`, `f = f'`, `e = e'`.
-/

open PadicField

namespace Iut.Reconstruction

/-! ### The algorithms on functions `ℕ → ℕ` -/

section Algorithms

/-- `N(n) = O(n)` on the integers prime to `ℓ`. -/
def BddLin (N : ℕ → ℕ) (ℓ : ℕ) : Prop := ∃ C, ∀ n, 0 < n → ¬ ℓ ∣ n → N n ≤ C * n

/-- The reconstructed residue characteristic. -/
noncomputable def primeOf (N : ℕ → ℕ) : ℕ := sInf {ℓ | ℓ.Prime ∧ BddLin N ℓ}

/-- The reconstructed cardinality of the residue field. -/
noncomputable def qOf (N : ℕ → ℕ) (ℓ : ℕ) : ℕ :=
  sInf {C | ∀ n, 0 < n → ¬ ℓ ∣ n → N n ≤ C * n} + 1

/-- The reconstructed absolute degree. -/
noncomputable def degOf (N : ℕ → ℕ) (ℓ : ℕ) : ℕ :=
  sInf {D | ∃ C, ∀ k, N (ℓ ^ k) ≤ C * ℓ ^ (k * (D + 1))}

/-- The reconstructed residue degree `f = log_p q`. -/
noncomputable def fOf (N : ℕ → ℕ) : ℕ := Nat.log (primeOf N) (qOf N (primeOf N))

/-- The reconstructed absolute ramification index `e = [K : ℚ_p] / f`. -/
noncomputable def eOf (N : ℕ → ℕ) : ℕ := degOf N (primeOf N) / fOf N

end Algorithms

/-! ### Correctness for `p`-adic fields -/

section Correctness

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {N : ℕ → ℕ}

/-- `N` agrees with `n ↦ [Kˣ : (Kˣ)ⁿ]` on positive integers. -/
def IsKummerIndexFun (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] (N : ℕ → ℕ) : Prop :=
  ∀ n, 0 < n → N n = powIndex Kˣ n

theorem bddLin_p (hN : IsKummerIndexFun p K N) : BddLin N p := by
  refine ⟨q p K - 1, fun n hn hpn => ?_⟩
  have hcop : p.Coprime n := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hpn
  rw [hN n hn, powIndex_of_coprime hcop hn.ne', mul_comm]
  exact Nat.mul_le_mul_right _ (Nat.gcd_le_left _ (by have := one_lt_q p K; omega))

theorem p_pow_mul_le (k : ℕ) :
    p ^ k * q p K ^ (k + 1) ≤ (q p K - 1) * q p K * powIndex Kˣ (p ^ k) := by
  have h1 := le_powIndex_p_pow (p := p) (K := K) k
  have h2 := succ_le_mSeq (e_pos' p K) k
  have hq := one_lt_q p K
  rw [powIndex_units_eq (p := p) (pow_ne_zero _ hp.out.ne_zero)]
  calc p ^ k * q p K ^ (k + 1) ≤ p ^ k * q p K ^ mSeq (e p ℚ_[p] K) k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h2)
    _ ≤ p ^ k * ((q p K - 1) * q p K * powIndex (𝒪 p K)ˣ (p ^ k)) :=
        Nat.mul_le_mul_left _ h1
    _ = _ := by ring

theorem not_bddLin_of_ne (hN : IsKummerIndexFun p K N) {ℓ : ℕ} (hℓ : ℓ.Prime) (hne : ℓ ≠ p) :
    ¬ BddLin N ℓ := by
  rintro ⟨C, hC⟩
  set A := (q p K - 1) * q p K
  set k := A * C
  have hq := one_lt_q p K
  have hpk : 0 < p ^ k := pow_pos hp.out.pos k
  have hdvd : ¬ ℓ ∣ p ^ k := fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq hℓ hp.out).1 (hℓ.dvd_of_dvd_pow h))
  have h1 := hC (p ^ k) hpk hdvd
  rw [hN _ hpk] at h1
  have h2 := p_pow_mul_le (p := p) (K := K) k
  have h3 : k < q p K ^ (k + 1) :=
    (Nat.lt_pow_self (by omega)).trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_succ k))
  have h4 : p ^ k * q p K ^ (k + 1) ≤ p ^ k * k := by
    calc p ^ k * q p K ^ (k + 1) ≤ A * powIndex Kˣ (p ^ k) := h2
      _ ≤ A * (C * p ^ k) := Nat.mul_le_mul_left _ h1
      _ = p ^ k * k := by ring
  have h5 := Nat.le_of_mul_le_mul_left h4 hpk
  omega

/-- **The residue characteristic is recovered.** -/
theorem primeOf_eq (hN : IsKummerIndexFun p K N) : primeOf N = p := by
  have hset : {ℓ | ℓ.Prime ∧ BddLin N ℓ} = {p} := by
    ext ℓ
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hℓ, hb⟩
      by_contra hne
      exact not_bddLin_of_ne hN hℓ hne hb
    · rintro rfl
      exact ⟨hp.out, bddLin_p hN⟩
  rw [primeOf, hset, csInf_singleton]

/-- **The cardinality of the residue field is recovered.** -/
theorem qOf_eq (hN : IsKummerIndexFun p K N) : qOf N p = q p K := by
  have hq := one_lt_q p K
  set S := {C | ∀ n, 0 < n → ¬ p ∣ n → N n ≤ C * n}
  have hmem : q p K - 1 ∈ S := by
    intro n hn hpn
    have hcop : p.Coprime n := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hpn
    rw [hN n hn, powIndex_of_coprime hcop hn.ne', mul_comm]
    exact Nat.mul_le_mul_right _ (Nat.gcd_le_left _ (by omega))
  have hlow : ∀ C ∈ S, q p K - 1 ≤ C := by
    intro C hC
    have hpos : 0 < q p K - 1 := by omega
    have hcop := p_coprime_q_sub_one p K
    have h := hC (q p K - 1) hpos ((Nat.Prime.coprime_iff_not_dvd hp.out).1 hcop)
    rw [hN _ hpos, powIndex_of_coprime hcop hpos.ne', Nat.gcd_self] at h
    exact Nat.le_of_mul_le_mul_right h hpos
  have : sInf S = q p K - 1 := le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ hlow)
  rw [qOf, this]
  omega

theorem powIndex_p_pow_le_mul (k : ℕ) :
    powIndex Kˣ (p ^ k) ≤ q p K ^ (e p ℚ_[p] K + 1) *
      p ^ (k * (Module.finrank ℚ_[p] K + 1)) := by
  rw [powIndex_units_eq (p := p) (pow_ne_zero _ hp.out.ne_zero)]
  have h := powIndex_p_pow_le (p := p) (K := K) k
  have hqe := q_pow_e p K
  calc p ^ k * powIndex (𝒪 p K)ˣ (p ^ k)
      ≤ p ^ k * q p K ^ ((k + 1) * e p ℚ_[p] K + 1) := Nat.mul_le_mul_left _ h
    _ = q p K ^ (e p ℚ_[p] K + 1) * (p ^ k * (q p K ^ e p ℚ_[p] K) ^ k) := by ring
    _ = _ := by rw [hqe, ← pow_mul, ← pow_add]; ring_nf

theorem le_powIndex_p_pow_mul (k : ℕ) :
    p ^ (Module.finrank ℚ_[p] K * (k + 1) + k) ≤
      (q p K - 1) * q p K ^ (e p ℚ_[p] K * e p ℚ_[p] K + 1) * powIndex Kˣ (p ^ k) := by
  have h1 := le_powIndex_p_pow (p := p) (K := K) k
  have h2 := (mSeq_lower (e := e p ℚ_[p] K) k).2
  have hq := one_lt_q p K
  have hqe := q_pow_e p K
  have h3 : p ^ (Module.finrank ℚ_[p] K * (k + 1)) ≤
      q p K ^ (mSeq (e p ℚ_[p] K) k + e p ℚ_[p] K * e p ℚ_[p] K) := by
    rw [pow_mul, ← hqe, ← pow_mul]
    exact Nat.pow_le_pow_right (by omega) h2
  rw [powIndex_units_eq (p := p) (pow_ne_zero _ hp.out.ne_zero)]
  calc p ^ (Module.finrank ℚ_[p] K * (k + 1) + k)
      = p ^ k * p ^ (Module.finrank ℚ_[p] K * (k + 1)) := by ring
    _ ≤ p ^ k * (q p K ^ mSeq (e p ℚ_[p] K) k * q p K ^ (e p ℚ_[p] K * e p ℚ_[p] K)) :=
        Nat.mul_le_mul_left _ (by rw [← pow_add]; exact h3)
    _ ≤ p ^ k * ((q p K - 1) * q p K * powIndex (𝒪 p K)ˣ (p ^ k) *
          q p K ^ (e p ℚ_[p] K * e p ℚ_[p] K)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h1)
    _ = _ := by ring

/-- **The absolute degree is recovered.** -/
theorem degOf_eq (hN : IsKummerIndexFun p K N) : degOf N p = Module.finrank ℚ_[p] K := by
  set d := Module.finrank ℚ_[p] K
  set T := {D | ∃ C, ∀ k, N (p ^ k) ≤ C * p ^ (k * (D + 1))}
  have hmem : d ∈ T := ⟨_, fun k => by
    rw [hN _ (pow_pos hp.out.pos k)]; exact powIndex_p_pow_le_mul k⟩
  have hlow : ∀ D ∈ T, d ≤ D := by
    rintro D ⟨C, hC⟩
    by_contra hlt
    push Not at hlt
    set A := (q p K - 1) * q p K ^ (e p ℚ_[p] K * e p ℚ_[p] K + 1)
    set k := A * C
    have h1 := le_powIndex_p_pow_mul (p := p) (K := K) k
    have h2 := hC k
    rw [hN _ (pow_pos hp.out.pos k)] at h2
    have h3 : p ^ (k * (D + 1)) ≤ p ^ (k * d) :=
      Nat.pow_le_pow_right hp.out.pos (Nat.mul_le_mul_left _ hlt)
    have h4 : p ^ (k * d) * p ^ (d + k) ≤ p ^ (k * d) * (A * C) := by
      calc p ^ (k * d) * p ^ (d + k) = p ^ (d * (k + 1) + k) := by ring
        _ ≤ A * powIndex Kˣ (p ^ k) := h1
        _ ≤ A * (C * p ^ (k * (D + 1))) := Nat.mul_le_mul_left _ h2
        _ ≤ A * (C * p ^ (k * d)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
        _ = p ^ (k * d) * (A * C) := by ring
    have h5 := Nat.le_of_mul_le_mul_left h4 (pow_pos hp.out.pos _)
    have h6 : k < p ^ k := Nat.lt_pow_self hp.out.one_lt
    have h7 : p ^ k ≤ p ^ (d + k) := Nat.pow_le_pow_right hp.out.pos (Nat.le_add_left _ _)
    omega
  exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ hlow)

/-- **The residue degree is recovered.** -/
theorem fOf_eq (hN : IsKummerIndexFun p K N) : fOf N = f p ℚ_[p] K := by
  rw [fOf, primeOf_eq hN, qOf_eq hN, q_eq_p_pow_f, Nat.log_pow hp.out.one_lt]

/-- **The absolute ramification index is recovered.** -/
theorem eOf_eq (hN : IsKummerIndexFun p K N) : eOf N = e p ℚ_[p] K := by
  rw [eOf, primeOf_eq hN, degOf_eq hN, fOf_eq hN, ← e_mul_f (p := p) (K := ℚ_[p]) (L := K),
    Nat.mul_div_cancel _ f_pos]

end Correctness

/-! ### The group-theoretic algorithms -/

section GroupTheoretic

universe u

/-- The character-count function of a topological group. -/
noncomputable def charCountFun (G : Type*) [Group G] [TopologicalSpace G] : ℕ → ℕ :=
  fun n => charCount G n

/-- The reconstructed residue characteristic of a topological group. -/
noncomputable def recPrime (G : Type*) [Group G] [TopologicalSpace G] : ℕ :=
  primeOf (charCountFun G)

/-- The reconstructed cardinality of the residue field. -/
noncomputable def recQ (G : Type*) [Group G] [TopologicalSpace G] : ℕ :=
  qOf (charCountFun G) (recPrime G)

/-- The reconstructed absolute degree. -/
noncomputable def recDeg (G : Type*) [Group G] [TopologicalSpace G] : ℕ :=
  degOf (charCountFun G) (recPrime G)

/-- The reconstructed residue degree. -/
noncomputable def recF (G : Type*) [Group G] [TopologicalSpace G] : ℕ := fOf (charCountFun G)

/-- The reconstructed absolute ramification index. -/
noncomputable def recE (G : Type*) [Group G] [TopologicalSpace G] : ℕ := eOf (charCountFun G)

theorem charCountFun_congr {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] (φ : G ≃ₜ* H) : charCountFun G = charCountFun H :=
  funext fun n => charCount_congr φ n

theorem isGroupTheoretic_recPrime : IsGroupTheoretic.{u} fun G _ _ => recPrime G :=
  fun _ _ _ _ _ _ φ => by simp only [recPrime, charCountFun_congr φ]

theorem isGroupTheoretic_recQ : IsGroupTheoretic.{u} fun G _ _ => recQ G :=
  fun _ _ _ _ _ _ φ => by simp only [recQ, recPrime, charCountFun_congr φ]

theorem isGroupTheoretic_recDeg : IsGroupTheoretic.{u} fun G _ _ => recDeg G :=
  fun _ _ _ _ _ _ φ => by simp only [recDeg, recPrime, charCountFun_congr φ]

theorem isGroupTheoretic_recF : IsGroupTheoretic.{u} fun G _ _ => recF G :=
  fun _ _ _ _ _ _ φ => by simp only [recF, charCountFun_congr φ]

theorem isGroupTheoretic_recE : IsGroupTheoretic.{u} fun G _ _ => recE G :=
  fun _ _ _ _ _ _ φ => by simp only [recE, charCountFun_congr φ]

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

variable (p K Ω) in
theorem isKummerIndexFun_gal : IsKummerIndexFun p K (charCountFun (Ω ≃ₐ[K] Ω)) := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  exact charCount_gal (K := K) (Ω := Ω) p n

variable (p) in
/-- `recPrime (G_K) = p`. -/
theorem recPrime_gal : recPrime (Ω ≃ₐ[K] Ω) = p := primeOf_eq (isKummerIndexFun_gal p K Ω)

variable (p) in
/-- `recQ (G_K) = q`. -/
theorem recQ_gal : recQ (Ω ≃ₐ[K] Ω) = q p K := by
  rw [recQ, recPrime_gal p]; exact qOf_eq (isKummerIndexFun_gal p K Ω)

variable (p) in
/-- `recDeg (G_K) = [K : ℚ_p]`. -/
theorem recDeg_gal : recDeg (Ω ≃ₐ[K] Ω) = Module.finrank ℚ_[p] K := by
  rw [recDeg, recPrime_gal p]; exact degOf_eq (isKummerIndexFun_gal p K Ω)

variable (p) in
/-- `recF (G_K) = f`. -/
theorem recF_gal : recF (Ω ≃ₐ[K] Ω) = f p ℚ_[p] K := fOf_eq (isKummerIndexFun_gal p K Ω)

variable (p) in
/-- `recE (G_K) = e`. -/
theorem recE_gal : recE (Ω ≃ₐ[K] Ω) = e p ℚ_[p] K := eOf_eq (isKummerIndexFun_gal p K Ω)

variable {p' : ℕ} [Fact p'.Prime]
variable {K' : Type*} [Field K'] [Algebra ℚ_[p'] K'] [FiniteDimensional ℚ_[p'] K']
variable {Ω' : Type*} [Field Ω'] [Algebra K' Ω'] [Algebra ℚ_[p'] Ω'] [IsScalarTower ℚ_[p'] K' Ω']
  [IsAlgClosed Ω'] [IsGalois K' Ω']

/-- **[AbsTopIII], Proposition 5.8 (i)** (invariance form): an isomorphism of topological groups
`Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` between the absolute Galois groups of a finite extension `K/ℚ_p` and
a finite extension `K'/ℚ_{p'}` forces `p = p'` and the equality of the absolute degrees,
residue field cardinalities, residue degrees and absolute ramification indices. -/
theorem galEquiv_invariants (φ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) :
    p = p' ∧ Module.finrank ℚ_[p] K = Module.finrank ℚ_[p'] K' ∧ q p K = q p' K' ∧
      f p ℚ_[p] K = f p' ℚ_[p'] K' ∧ e p ℚ_[p] K = e p' ℚ_[p'] K' := by
  have h := charCountFun_congr φ
  have h1 := recPrime_gal p (K := K) (Ω := Ω)
  have h1' := recPrime_gal p' (K := K') (Ω := Ω')
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← h1, ← h1', recPrime, recPrime, h]
  · rw [← recDeg_gal p (K := K) (Ω := Ω), ← recDeg_gal p' (K := K') (Ω := Ω'), recDeg, recDeg,
      recPrime, recPrime, h]
  · rw [← recQ_gal p (K := K) (Ω := Ω), ← recQ_gal p' (K := K') (Ω := Ω'), recQ, recQ,
      recPrime, recPrime, h]
  · rw [← recF_gal p (K := K) (Ω := Ω), ← recF_gal p' (K := K') (Ω := Ω'), recF, recF, h]
  · rw [← recE_gal p (K := K) (Ω := Ω), ← recE_gal p' (K := K') (Ω := Ω'), recE, recE, h]

end GroupTheoretic

end Iut.Reconstruction
