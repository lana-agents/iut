/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Implication.Invariants

/-!
# The log-volume upper bound (IUT IV, Theorem 1.10, Steps (iv)–(vii))

The right-hand side `−|log(Θ)|` of the Corollary 3.12 variant is the
procession-normalized log-volume of the holomorphic hull of the theta-pilot region
(`RHSData.rhs`, taxis #35). Steps (iv)–(vii) of the proof of IUT IV, Theorem 1.10 bound
this quantity from above, one rational place `v_ℚ` and one capsule `S_{j+1}` at a time:

* at a distinguished nonarchimedean `v_ℚ` (Step (v)), the union of the possible images
  of the theta-pilot is contained in a hull region `p^{⌊λ − d_I − a_I⌋ − b_I}·(R_I)^∼`
  (Proposition 1.4(iii)), whose log-volume is at most
  `(j+1)·log(d^K_{v_ℚ}) − (j²/2ℓ)·log(q_{v_ℚ}) + log(s^ℚ_{v_ℚ}) + 4(j+1)·l*_mod·log(s^≤_{v_ℚ})`
  after the weighted average of Proposition 1.7;
* at a non-distinguished nonarchimedean `v_ℚ` (Step (vi)), the container is the
  holomorphic integral structure itself, of log-volume `0` (Proposition 1.4(iv));
* at the archimedean place (Step (vii)), the container `π^{j+1}·B_I` has log-volume at
  most `(j+1)·log π` (Proposition 1.5(iii),(iv)).

## What is proved here and what is assumed

The local-field content — the existence of the containing hull regions and the bounds
on their log-volumes, i.e. IUT IV, Propositions 1.4 and 1.5 applied to the theta-pilot
images, together with the weighted average of Proposition 1.7 — is the explicit
certificate `LocalEstimate` (taxis #4, #278: it requires the `p`-adic log-shell theory
that this repository does not yet have). It also records monotonicity of the packet
log-volume between hull regions, a standard law of Haar measure deliberately left out of
the log-volume interface of taxis #44 (which records no law for zero or infinite
volumes); it is stated here only for hull regions, where it is meaningful.

What is *proved* is the passage from these local containments to the bound on
`RHSData.rhs`: the hull of the theta-pilot region is contained in every hull region
containing the theta-pilot region (minimality, taxis #45), the log-volume is bounded by
monotonicity, the sum over rational places is finitely supported (the container's
admissibility condition, taxis #43), and the procession average is the plain average
over capsules (taxis #44). This is `LocalEstimate.rhs_le`.
-/

namespace Iut

universe u v

open NumberField

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

namespace Theorem110Invariants

variable {X : Corollary312VariantData.{u, v} AG TG} (inv : Theorem110Invariants X)

/-- The Step (v) upper bound for the packet log-volume of the container of theta-pilot
images at a distinguished prime `p`, for a capsule of cardinality `n = j + 1`:
`n·log(d^K_p) − ((n−1)²/2ℓ)·log(q_p) + log p + 4·n·l*_mod·ι_p`. -/
noncomputable def capsuleBound (n : ℕ) (p : ℕ) : ℝ :=
  n * inv.logDK p - ((n : ℝ) - 1) ^ 2 / (2 * X.ℓ) * X.logQAt p + Real.log p +
    4 * n * inv.lmod * inv.ι p

/-- **The local estimates of Steps (iv)–(vii)** as an explicit certificate: for every
capsule `i` and rational place `v_ℚ`, a hull region `cont i v_ℚ` containing the
theta-pilot region, equal to the holomorphic integral structure away from the
distinguished primes, with the log-volume bounds of Propositions 1.4(iii),(iv) and
1.5(iii),(iv); and monotonicity of the packet log-volume between hull regions. -/
structure LocalEstimate : Type (max u v) where
  /-- The containing hull region at capsule `i` and rational place `v_ℚ`
  (`p^{⌊λ − d_I − a_I⌋ − b_I}·(R_I)^∼`, resp. `(R_I)^∼`, resp. `π^{j+1}·B_I`). -/
  cont : ∀ (i : Fin X.rhsData.container.proc.length) (vQ : RationalPlace),
    Set (X.rhsData.container.packet i vQ).Total
  /-- Each container is a hull region `a·O` with all components of `a` nonzero. -/
  cont_isHullRegion : ∀ i vQ, (X.rhsData.container.packet i vQ).IsHullRegion (cont i vQ)
  /-- The theta-pilot region (the union of the images under (Ind1)–(Ind3)) is contained
  in the container: the inclusions `φ(p^λ·(R_I)^∼) ⊆ …` of Proposition 1.4(iii),(iv)
  and `⊗ m_i ∈ π^{|I|}·B_I` of Proposition 1.5(iv). -/
  thetaPilot_subset : ∀ i vQ, (X.rhsData.thetaPilot i).region vQ ⊆ cont i vQ
  /-- Away from the distinguished primes the container is the holomorphic integral
  structure (Proposition 1.4(iv): `φ((R_I)^∼) ⊆ (R_I)^∼`). -/
  cont_eq_integral : ∀ i (p : Nat.Primes), (p : ℕ) ∉ inv.dst →
    cont i (.finite p) = (X.rhsData.container.packet i (.finite p)).integralRegion
  /-- Step (v): at a distinguished prime the packet log-volume of the container is
  bounded by `capsuleBound` (Proposition 1.4(iii), (R4), and the weighted average of
  Proposition 1.7). -/
  vol_finite : ∀ i (p : Nat.Primes), (p : ℕ) ∈ inv.dst →
    X.rhsData.vol.packetVol i (.finite p) (cont i (.finite p)) ≤
      inv.capsuleBound (X.rhsData.container.proc.capsule i).card p
  /-- Step (vii): at the archimedean place the packet log-volume of the container is at
  most `(j+1)·log π` (Proposition 1.5(iii),(iv) and the normalization `μ(B_I) = 0`). -/
  vol_infinite : ∀ i,
    X.rhsData.vol.packetVol i .infinite (cont i .infinite) ≤
      (X.rhsData.container.proc.capsule i).card * Real.log Real.pi
  /-- Monotonicity of the packet log-volume between hull regions (a law of Haar
  measure for regions of finite nonzero volume). -/
  packetVol_mono : ∀ i vQ (U V : Set (X.rhsData.container.packet i vQ).Total),
    (X.rhsData.container.packet i vQ).IsHullRegion U →
    (X.rhsData.container.packet i vQ).IsHullRegion V → U ⊆ V →
    X.rhsData.vol.packetVol i vQ U ≤ X.rhsData.vol.packetVol i vQ V

namespace LocalEstimate

variable (est : inv.LocalEstimate)

/-- The pointwise upper bound function on rational places, for a capsule of
cardinality `n`: `capsuleBound n p` at a distinguished prime `p`, `0` at the other
primes, `n·log π` at the archimedean place. -/
noncomputable def placeBound (n : ℕ) : RationalPlace → ℝ
  | .finite p => if (p : ℕ) ∈ inv.dst then inv.capsuleBound n p else 0
  | .infinite => n * Real.log Real.pi

/-- The finite set of rational places carrying the distinguished primes. -/
noncomputable def dstPlaces : Finset RationalPlace :=
  inv.dst.attach.image fun p => RationalPlace.finite ⟨p.1, inv.dst_prime p.1 p.2⟩

lemma support_placeBound_subset (n : ℕ) :
    Function.support (placeBound inv n) ⊆ ↑(insert RationalPlace.infinite (dstPlaces inv)) := by
  intro vQ hvQ
  rcases vQ with p | _
  · have hp : (p : ℕ) ∈ inv.dst := by
      by_contra h
      exact hvQ (by simp [placeBound, h])
    refine Finset.mem_coe.mpr (Finset.mem_insert_of_mem ?_)
    simp only [dstPlaces, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    exact ⟨p, hp, by rfl⟩
  · exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)

lemma infinite_notMem_dstPlaces : RationalPlace.infinite ∉ dstPlaces inv := by
  simp [dstPlaces]

/-- The finite sum of the pointwise bound over all rational places. -/
lemma finsum_placeBound (n : ℕ) :
    ∑ᶠ vQ, placeBound inv n vQ =
      ∑ p ∈ inv.dst, inv.capsuleBound n p + n * Real.log Real.pi := by
  rw [finsum_eq_sum_of_support_subset _ (support_placeBound_subset inv n),
    Finset.sum_insert (infinite_notMem_dstPlaces inv), add_comm]
  congr 1
  unfold dstPlaces
  rw [Finset.sum_image]
  · rw [← Finset.sum_attach inv.dst fun p => inv.capsuleBound n p]
    refine Finset.sum_congr rfl fun p _ => ?_
    change (if (p.1 : ℕ) ∈ inv.dst then inv.capsuleBound n p.1 else 0) = inv.capsuleBound n p.1
    rw [if_pos p.2]
  · intro p _ q _ h
    exact Subtype.ext (Subtype.mk.inj (RationalPlace.finite.inj h))

/-- A finite sum dominated pointwise by a finitely supported function is dominated by
its sum. -/
lemma finsum_le_finsum_of_le {α : Type*} {f g : α → ℝ} (h : ∀ a, f a ≤ g a)
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    ∑ᶠ a, f a ≤ ∑ᶠ a, g a := by
  rw [finsum_eq_sum_of_support_subset f (s := (hf.union hg).toFinset) (by
      intro a ha; simp only [Set.Finite.coe_toFinset]; exact Or.inl ha),
    finsum_eq_sum_of_support_subset g (s := (hf.union hg).toFinset) (by
      intro a ha; simp only [Set.Finite.coe_toFinset]; exact Or.inr ha)]
  exact Finset.sum_le_sum fun a _ => h a

variable {inv}
include est

/-- The holomorphic hull of the theta-pilot region is contained in the container of
`est`, by minimality of the hull (taxis #45). -/
lemma hull_subset_cont (i : Fin X.rhsData.container.proc.length) (vQ : RationalPlace) :
    (X.rhsData.hull.system i vQ).hull ((X.rhsData.thetaPilot i).region vQ) ⊆
      est.cont i vQ :=
  (X.rhsData.hull.system i vQ).hull_le (X.rhsData.thetaPilot_hullAdmissible i vQ)
    (est.cont_isHullRegion i vQ) (est.thetaPilot_subset i vQ)

/-- The pointwise bound: the packet log-volume of the hull of the theta-pilot region is
at most `placeBound` at every rational place. -/
lemma packetVol_hull_le (i : Fin X.rhsData.container.proc.length) (vQ : RationalPlace) :
    X.rhsData.vol.packetVol i vQ ((X.rhsData.thetaHull i).region vQ) ≤
      placeBound inv (X.rhsData.container.proc.capsule i).card vQ := by
  have hmono : X.rhsData.vol.packetVol i vQ ((X.rhsData.thetaHull i).region vQ) ≤
      X.rhsData.vol.packetVol i vQ (est.cont i vQ) :=
    est.packetVol_mono i vQ _ _
      ((X.rhsData.hull.system i vQ).isHullRegion_hull
        (X.rhsData.thetaPilot_hullAdmissible i vQ))
      (est.cont_isHullRegion i vQ) (est.hull_subset_cont i vQ)
  refine hmono.trans ?_
  rcases vQ with p | _
  · by_cases hp : (p : ℕ) ∈ inv.dst
    · simpa [placeBound, hp] using est.vol_finite i p hp
    · simp only [placeBound, hp, if_false]
      rw [est.cont_eq_integral i p hp]
      exact (X.rhsData.vol.packetVol_integral i _).le
  · exact est.vol_infinite i

/-- The global log-volume of the hull of the theta-pilot region at capsule `i` is
bounded by the sum of the local bounds. -/
lemma globalVol_thetaHull_le (i : Fin X.rhsData.container.proc.length) :
    X.rhsData.vol.globalVol (X.rhsData.thetaHull i) ≤
      ∑ p ∈ inv.dst, inv.capsuleBound (X.rhsData.container.proc.capsule i).card p +
        (X.rhsData.container.proc.capsule i).card * Real.log Real.pi := by
  rw [← finsum_placeBound]
  exact finsum_le_finsum_of_le (est.packetVol_hull_le i)
    (X.rhsData.vol.finite_support_packetVol _)
    ((Finset.finite_toSet _).subset (support_placeBound_subset inv _))

/-- **The log-volume upper bound of Steps (iv)–(vii)**: the right-hand side of the
Corollary 3.12 variant is at most the procession average of the summed local bounds. -/
theorem rhs_le :
    X.rhsData.rhs ≤
      (∑ i, (∑ p ∈ inv.dst, inv.capsuleBound (X.rhsData.container.proc.capsule i).card p +
        (X.rhsData.container.proc.capsule i).card * Real.log Real.pi)) /
        X.rhsData.container.proc.length := by
  unfold RHSData.rhs LogVolumeData.processionVol
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => est.globalVol_thetaHull_le i)
    (Nat.cast_nonneg _)

end LocalEstimate

end Theorem110Invariants

end Iut
