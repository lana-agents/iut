/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.SerreBound
import Iut.Tower.Residual

/-!
# The different bound of IUT IV, Proposition 1.3, for number fields

* `Iut.ordAt_differentIdeal_add_one_le`, **Serre's bound**: for an extension `K/k` of number
  fields and a place `v` of `K` over `u` of `k`,
  `ord_v(𝔇_{K/k}) + 1 ≤ e(v/u) + e_v·v_p(e(v/u))`
  (`ord_v(𝔇) ≤ e − 1 + ord_v(e)`, Serre, *Local Fields*, III §6; IUT IV, Proposition 1.3),
  from `Iut.Serre.not_pow_dvd_differentIdeal` with `κ = e_u·v_p(e(v/u))`, so that
  `e(v/u) ∉ 𝔭_u^{κ+1}`;
* `Iut.TowerLocalFacts.ordAt_different_le`, **the different bound of the tower**:
  `ord_v(𝔇_{K/F_tpd}) + 1 ≤ e(v/u) + e_v·c_p` from the bound `v_p(e(v/u)) ≤ c_p` on the
  wild part of the ramification (the field `padicValNat_relRamIdx_le` of
  `Iut.TowerLocalFacts`).
-/

namespace Iut

open NumberField IsDedekindDomain UniqueFactorizationMonoid

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Ord

variable {K : Type*} [Field K] [NumberField K]

/-- `𝔭_v^{ord_v(I)} ∣ I`, for `I ≠ 0`. -/
lemma pow_ordAt_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0) (v : FinitePlace K) :
    v.maximalIdeal.asIdeal ^ ordAt I v ∣ I := by
  classical
  have hirr : Irreducible v.maximalIdeal.asIdeal :=
    (Ideal.prime_of_isPrime v.maximalIdeal.ne_bot v.maximalIdeal.isPrime).irreducible
  refine pow_dvd_of_le_emultiplicity ?_
  rw [emultiplicity_eq_count_normalizedFactors hirr hI, normalize_eq]
  exact le_rfl

/-- `¬ 𝔭_v^{n+1} ∣ I → ord_v(I) ≤ n`, for `I ≠ 0`. -/
lemma ordAt_le_of_not_pow_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0) (v : FinitePlace K) (n : ℕ)
    (h : ¬ v.maximalIdeal.asIdeal ^ (n + 1) ∣ I) : ordAt I v ≤ n := by
  by_contra hlt
  exact h ((pow_dvd_pow _ (by omega)).trans (pow_ordAt_dvd I hI v))

end Ord

section Powers

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- `a^m ∉ 𝔓^{em+1}` for `a ∈ 𝔓^e ∖ 𝔓^{e+1}`, `𝔓` a nonzero prime of a Dedekind domain. -/
lemma pow_notMem_pow_mul_succ (𝔓 : Ideal R) [𝔓.IsPrime] (h𝔓 : 𝔓 ≠ ⊥) {a : R} {e : ℕ}
    (ha : a ∈ 𝔓 ^ e) (ha' : a ∉ 𝔓 ^ (e + 1)) (m : ℕ) : a ^ m ∉ 𝔓 ^ (e * m + 1) := by
  intro h
  have hprime : Prime 𝔓 := Ideal.prime_of_isPrime h𝔓 inferInstance
  obtain ⟨𝔞, h𝔞⟩ : 𝔓 ^ e ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr ha
  have h1 : 𝔓 ^ (e * m + 1) ∣ Ideal.span {a} ^ m := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_span_singleton.mpr h
  rw [h𝔞, mul_pow, pow_succ, ← pow_mul] at h1
  have h2 : 𝔓 ∣ 𝔞 ^ m := (mul_dvd_mul_iff_left (pow_ne_zero _ h𝔓)).mp h1
  have h3 : 𝔓 ∣ 𝔞 := hprime.dvd_of_dvd_pow h2
  apply ha'
  rw [← Ideal.dvd_span_singleton, h𝔞, pow_succ]
  exact mul_dvd_mul_left _ h3

end Powers

section Serre

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The residue characteristic `p` of `u` lies in `𝔭_u^{e_u}` and not in `𝔭_u^{e_u+1}`. -/
lemma residueChar_mem_pow_ramIdx (u : FinitePlace k) :
    ((residueChar u : ℕ) : 𝓞 k) ∈ u.maximalIdeal.asIdeal ^ ramIdx k u ∧
      ((residueChar u : ℕ) : 𝓞 k) ∉ u.maximalIdeal.asIdeal ^ (ramIdx k u + 1) := by
  haveI := liesOver_span_residueChar u
  have hp : (residueChar u).Prime := residueChar_prime u
  have hp0 : (residueChar u : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI : (Ideal.span {(residueChar u : ℤ)}).IsMaximal :=
    LocalConstruct.span_prime_isMaximal hp
  have h𝔭 : u.maximalIdeal.asIdeal ≠ ⊥ := u.maximalIdeal.ne_bot
  have hmap : (Ideal.span {(residueChar u : ℤ)}).map (algebraMap ℤ (𝓞 k)) =
      Ideal.span {((residueChar u : ℕ) : 𝓞 k)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have he : ramIdx k u = (Ideal.span {(residueChar u : ℤ)}).ramificationIdx'
      u.maximalIdeal.asIdeal :=
    (Ideal.ramificationIdx'_eq_ramificationIdx _ u.maximalIdeal.asIdeal
      (LocalConstruct.span_prime_ne_bot hp)).symm
  have hne : Ideal.span {((residueChar u : ℕ) : 𝓞 k)} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  constructor
  · have := Ideal.le_pow_ramificationIdx' (p := Ideal.span {(residueChar u : ℤ)})
      (P := u.maximalIdeal.asIdeal)
    rw [hmap, ← he] at this
    exact this (Ideal.mem_span_singleton_self _)
  · intro h
    have h1 : u.maximalIdeal.asIdeal ^ (ramIdx k u + 1) ∣
        Ideal.span {((residueChar u : ℕ) : 𝓞 k)} := Ideal.dvd_span_singleton.mpr h
    have h2 := le_ordAt_of_pow_dvd _ hne u _ h1
    have h3 : ordAt (Ideal.span {((residueChar u : ℕ) : 𝓞 k)}) u = ramIdx k u := by
      rw [he, ordAt, Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
        (by rw [hmap]; exact hne) u.maximalIdeal.isPrime h𝔭, hmap]
    omega

/-- `(r : 𝓞 k) ∉ 𝔭_u` for `p ∤ r`. -/
lemma natCast_notMem_of_not_dvd (u : FinitePlace k) {r : ℕ} (hpr : ¬ residueChar u ∣ r) :
    ((r : ℕ) : 𝓞 k) ∉ u.maximalIdeal.asIdeal := by
  intro hmem
  apply hpr
  have h1 : (r : ℤ) ∈ u.maximalIdeal.asIdeal.under ℤ := by
    rw [Ideal.mem_under, map_natCast]
    exact hmem
  rw [under_int_eq, Ideal.mem_span_singleton] at h1
  exact Int.natCast_dvd_natCast.mp h1

/-- `p ∤ e / p^{v_p(e)}`. -/
lemma not_dvd_of_pow_padicValNat_mul {p e r : ℕ} [Fact p.Prime] (he : e ≠ 0)
    (hr : e = p ^ padicValNat p e * r) : ¬ p ∣ r := by
  intro hdvd
  apply pow_succ_padicValNat_not_dvd (p := p) he
  calc p ^ (padicValNat p e + 1) = p ^ padicValNat p e * p := pow_succ _ _
    _ ∣ p ^ padicValNat p e * r := mul_dvd_mul_left _ hdvd
    _ = e := hr.symm

/-- `(e : 𝓞 k) ∉ 𝔭_u^{e_u·v_p(e) + 1}` for `e ≠ 0`, `p` the residue characteristic of `u`. -/
lemma natCast_notMem_pow_ramIdx_mul_padicValNat (u : FinitePlace k) {e : ℕ} (he : e ≠ 0) :
    ((e : ℕ) : 𝓞 k) ∉
      u.maximalIdeal.asIdeal ^ (ramIdx k u * padicValNat (residueChar u) e + 1) := by
  haveI : Fact (residueChar u).Prime := ⟨residueChar_prime u⟩
  haveI : u.maximalIdeal.asIdeal.IsMaximal :=
    u.maximalIdeal.isPrime.isMaximal u.maximalIdeal.ne_bot
  obtain ⟨hpmem, hpnot⟩ := residueChar_mem_pow_ramIdx u
  obtain ⟨r, hr⟩ : residueChar u ^ padicValNat (residueChar u) e ∣ e := pow_padicValNat_dvd
  have hr' := natCast_notMem_of_not_dvd u (not_dvd_of_pow_padicValNat_mul he hr)
  intro hmem
  have hmem' : ((r : ℕ) : 𝓞 k) * ((residueChar u : ℕ) : 𝓞 k) ^ padicValNat (residueChar u) e ∈
      u.maximalIdeal.asIdeal ^ (ramIdx k u * padicValNat (residueChar u) e + 1) := by
    rw [mul_comm ((r : ℕ) : 𝓞 k), ← Nat.cast_pow, ← Nat.cast_mul, ← hr]
    exact hmem
  exact pow_notMem_pow_mul_succ u.maximalIdeal.asIdeal u.maximalIdeal.ne_bot hpmem hpnot _
    (Serre.mem_pow_of_mul_mem_pow u.maximalIdeal.asIdeal hr' _ hmem')

/-- **Serre's bound on the different of an extension of number fields** (IUT IV,
Proposition 1.3): for a place `v` of `K` over `u` of `k`,
`ord_v(𝔇_{K/k}) + 1 ≤ e(v/u) + e_v·v_p(e(v/u))`. -/
theorem ordAt_differentIdeal_add_one_le {v : FinitePlace K} {u : FinitePlace k}
    (hvu : FinitePlace.LiesOver v u) :
    ordAt (differentIdeal (𝓞 k) (𝓞 K)) v + 1 ≤
      relRamIdx v u + ramIdx K v * padicValNat (residueChar v) (relRamIdx v u) := by
  haveI : v.maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal := hvu
  haveI : u.maximalIdeal.asIdeal.IsMaximal :=
    u.maximalIdeal.isPrime.isMaximal u.maximalIdeal.ne_bot
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  haveI : Finite (𝓞 k ⧸ u.maximalIdeal.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ u.maximalIdeal.ne_bot
  have he : relRamIdx v u ≠ 0 := relRamIdx_ne_zero hvu
  set κ := ramIdx k u * padicValNat (residueChar u) (relRamIdx v u) with hκdef
  have hκ : ((relRamIdx v u : ℕ) : 𝓞 k) ∉ u.maximalIdeal.asIdeal ^ (κ + 1) :=
    natCast_notMem_pow_ramIdx_mul_padicValNat u he
  have h := Serre.not_pow_dvd_differentIdeal u.maximalIdeal.asIdeal v.maximalIdeal.asIdeal
    u.maximalIdeal.ne_bot κ hκ
  have hpos : 1 ≤ relRamIdx v u * (κ + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 := ordAt_le_of_not_pow_dvd _ differentIdeal_ne_bot v (relRamIdx v u * (κ + 1) - 1)
    (by rwa [Nat.sub_add_cancel hpos])
  rw [ramIdx_eq_mul hvu, residueChar_eq_of_liesOver hvu]
  have h3 : relRamIdx v u * (κ + 1) =
      relRamIdx v u + ramIdx k u * relRamIdx v u * padicValNat (residueChar u) (relRamIdx v u) := by
    rw [hκdef]
    ring
  omega

end Serre

/-! ### The different bound of the tower -/

section Tower

universe u

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable {Pr : AdmissiblePrimeData F E Fbar VBad} [NumberField ↥Pr.torsionField]

/-- **The different bound** (IUT IV, Proposition 1.3 with the tameness of Proposition 1.8):
`ord_v(𝔇_{K/F_tpd}) + 1 ≤ e(v/u) + e_v·c_p`, from Serre's bound and the wild ramification
bound `v_p(e(v/u)) ≤ c_p` of the local facts. -/
theorem TowerLocalFacts.ordAt_different_le (H : TowerLocalFacts E VBad Pr)
    (v : FinitePlace ↥Pr.torsionField) :
    ordAt (differentIdeal (𝓞 ↥(tripodalFieldOf F E)) (𝓞 ↥Pr.torsionField)) v + 1 ≤
      relRamIdx v (placeTpd F E Pr.torsionField v) +
        ramIdx (↥Pr.torsionField) v * wildConst Pr.ℓ (residueChar v) :=
  (ordAt_differentIdeal_add_one_le (liesOver_placeTpd v)).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (H.padicValNat_relRamIdx_le v)) _)

end Tower

end Iut
