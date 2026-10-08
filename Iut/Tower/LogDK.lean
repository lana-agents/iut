/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.Basic
import Iut.Concrete.Invariants

/-!
# `∑_p log(d^K_p) = log(d_K)`

The local different contributions `log(d^K_p) = ∑_{v ∣ p} w_v d_v log p` of
`Iut.InitialThetaData.logDK` sum, over any finite set of primes containing the residue
characteristics of the places dividing the different, to the normalized degree
`log(d_K) = log N(𝔡_{K/ℚ})/[K : ℚ]` of the different (`Iut.logDifferentDeg`): since
`w_v d_v = (e_v f_v/[K : ℚ])·(ord_v(𝔡)/e_v) = f_v·ord_v(𝔡)/[K : ℚ]`, the contribution of `p`
is `∑_{v ∣ p} ord_v(𝔡)·f_v·log p/[K : ℚ]`, and `log N(𝔡) = ∑_v ord_v(𝔡)·f_v·log p_v`
(`Iut.log_absNorm_eq_sum_ordAt`).
-/

namespace Iut

open NumberField IsDedekindDomain

universe u

namespace InitialThetaData

variable (D : InitialThetaData.{u})

/-- The weight of a finite place of the fiber over `p` is `[K_v : ℚ_p]/[K : ℚ]`. -/
lemma weight_finite_eq {p : Nat.Primes} (w : LocalTheory.Fiber D.Kt (.finite p)) :
    LocalTheory.weight D.Kt (.finite p) w = placeWeight D.Kt (LocalTheory.fiberPlace D.Kt w) := by
  rcases w with ⟨w, hw⟩
  rcases w with w | w
  · rfl
  · exact absurd hw (by simp [LocalTheory.toRational])

/-- The summand of `log(d^K_p)` at a place `v ∣ p` is `ord_v(𝔡)·f_v·log p/[K : ℚ]`. -/
lemma weight_mul_differentExponent (v : FinitePlace D.Kt) :
    placeWeight D.Kt v * differentExponent D.Kt v * Real.log (residueChar v) =
      (ordAt (differentIdeal ℤ (𝓞 D.Kt)) v : ℝ) *
        (inertDeg D.Kt v * Real.log (residueChar v)) / Module.finrank ℚ D.Kt := by
  unfold placeWeight differentExponent localDeg
  rw [← ordDifferent_eq_ordAt]
  have he : (ramIdx D.Kt v : ℝ) ≠ 0 := by exact_mod_cast (ramIdx_pos' v).ne'
  have hn : (Module.finrank ℚ D.Kt : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  push_cast
  field_simp

/-- `log(d^K_p)` as a sum over any finite set of places containing the places over `p`
dividing the different: `log(d^K_p) = ∑_{v ∈ s, p_v = p} ord_v(𝔡)·f_v·log p/[K : ℚ]`. -/
lemma logDK_eq_sum_filter (p : ℕ) (s : Finset (FinitePlace D.Kt))
    (hs : ∀ w, ordAt (differentIdeal ℤ (𝓞 D.Kt)) w ≠ 0 → w ∈ s) :
    D.logDK p = ∑ w ∈ s.filter (fun w => residueChar w = p),
      (ordAt (differentIdeal ℤ (𝓞 D.Kt)) w : ℝ) *
        (inertDeg D.Kt w * Real.log (residueChar w)) / Module.finrank ℚ D.Kt := by
  classical
  unfold InitialThetaData.logDK
  split_ifs with hp
  · haveI := LocalTheory.fiber_finite D.Kt p
    haveI : Fintype {w : FinitePlace D.Kt // residueChar w = p} := Fintype.ofFinite _
    set g : FinitePlace D.Kt → ℝ := fun w => (ordAt (differentIdeal ℤ (𝓞 D.Kt)) w : ℝ) *
      (inertDeg D.Kt w * Real.log (residueChar w)) / Module.finrank ℚ D.Kt with hg
    have h1 : ∑ v : LocalTheory.Fiber D.Kt (.finite ⟨p, hp⟩), LocalTheory.weight D.Kt _ v *
        differentExponent D.Kt (LocalTheory.fiberPlace D.Kt v) * Real.log p =
        ∑ w : {w : FinitePlace D.Kt // residueChar w = p}, g w.1 := by
      refine Fintype.sum_equiv (LocalTheory.fiberFiniteEquiv D.Kt ⟨p, hp⟩) _ (fun w => g w.1) fun v => ?_
      rw [weight_finite_eq]
      change placeWeight D.Kt (LocalTheory.fiberPlace D.Kt v) * differentExponent D.Kt (LocalTheory.fiberPlace D.Kt v) *
        Real.log (p : ℝ) = g (LocalTheory.fiberPlace D.Kt v)
      rw [show ((p : ℕ) : ℝ) = residueChar (LocalTheory.fiberPlace D.Kt v) by
        rw [LocalTheory.residueChar_fiberPlace D.Kt v], hg]
      exact D.weight_mul_differentExponent _
    rw [h1]
    -- the sum over the subtype is the sum over the filtered set
    have h2 : ∑ w : {w : FinitePlace D.Kt // residueChar w = p}, g w.1 =
        ∑ w ∈ (Finset.univ : Finset {w : FinitePlace D.Kt // residueChar w = p}).map
          (Function.Embedding.subtype _), g w := by
      rw [Finset.sum_map]
      rfl
    rw [h2]
    symm
    refine Finset.sum_subset ?_ ?_
    · intro w hw
      rw [Finset.mem_filter] at hw
      rw [Finset.mem_map]
      exact ⟨⟨w, hw.2⟩, Finset.mem_univ _, rfl⟩
    · intro w hw₂ hw
      rw [Finset.mem_map] at hw₂
      obtain ⟨⟨w', hw'⟩, -, rfl⟩ := hw₂
      rw [Finset.mem_filter, not_and] at hw
      have hws : w' ∉ s := fun h => hw h hw'
      have : ordAt (differentIdeal ℤ (𝓞 D.Kt)) w' = 0 := by
        by_contra h
        exact hws (hs w' h)
      simp [this]
  · symm
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [Finset.mem_filter] at hw
    exact absurd (hw.2 ▸ Iut.residueChar_prime w) hp

/-- **`∑_p log(d^K_p) = log(d_K)`** over any finite set of primes containing the residue
characteristics of the places dividing the different. -/
theorem sum_logDK_eq (S : Finset ℕ)
    (hS : ∀ w : FinitePlace D.Kt, ordAt (differentIdeal ℤ (𝓞 D.Kt)) w ≠ 0 → residueChar w ∈ S) :
    ∑ p ∈ S, D.logDK p = logDifferentDeg D.Kt := by
  classical
  set s := (ordAt_support_finite (differentIdeal ℤ (𝓞 D.Kt))).toFinset with hs_def
  have hs : ∀ w, ordAt (differentIdeal ℤ (𝓞 D.Kt)) w ≠ 0 → w ∈ s :=
    fun w hw => (Set.Finite.mem_toFinset _).mpr hw
  simp_rw [D.logDK_eq_sum_filter _ s hs]
  rw [Finset.sum_fiberwise_of_maps_to (s := s) (t := S) (g := residueChar)
    (fun w (hw : w ∈ s) => hS w ((Set.Finite.mem_toFinset _).mp hw))]
  unfold logDifferentDeg
  rw [log_absNorm_eq_sum_ordAt _ differentIdeal_ne_bot s hs, Finset.sum_div]


/-- **`∑_{p ∈ V_ℚ^dst} log(d^K_p) = log(d_K)`**: the distinguished primes contain the residue
characteristics of the ramified places, hence of the places dividing the different. -/
theorem sum_dst_logDK_eq :
    ∑ p ∈ D.dst, D.logDK p = logDifferentDeg D.Kt :=
  D.sum_logDK_eq D.dst fun w hw => D.mem_dst_of_ramified w fun h1 =>
    hw (by rw [← ordDifferent_eq_ordAt]; exact LocalTheory.ordDifferent_eq_zero D.Kt w h1)

end InitialThetaData

end Iut
