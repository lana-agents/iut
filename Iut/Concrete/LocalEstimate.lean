/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.Invariants

/-!
# The local estimates for the concrete theta-pilot region (IUT IV, Step (v)–(vii))

For the concrete variant data, the local estimates `LocalEstimate` consumed by
Theorem 1.10 are *derived* here from the local-field theory:

* at a distinguished prime `p`, the containing hull region of a tuple `c` is the region
  `a_c·(R_I)^∼` provided by Proposition 1.4(iii) for the scaling element
  `q_{v_j}^{j²}`, with the bound `(−λ_c + d_I + 1)·log p + ∑_{i ∈ I*} (3 + log e_i)`;
  the packet log-volume is the weighted sum over tuples (taxis #44), and the weighted
  average of Proposition 1.7 turns the per-tuple bounds into
  `(j+1)·log(d^K_p) − (j²/2ℓ)·log(q_p) + log p + 4(j+1)·l*_mod·ι_p` — the bound
  `capsuleBound` of Step (v), using (R4) for the ramification terms and the base-change
  invariance of the `q`-degree for the `λ` terms;
* at a non-distinguished prime the container is the integral structure itself
  (Proposition 1.4(iv)), of log-volume `0`;
* at the archimedean place the container is `π^{|I|}·B_I` (Proposition 1.5), of
  log-volume `|I|·log π`;
* monotonicity of the packet log-volume between hull regions follows from the
  component-wise monotonicity.

This is the content of IUT IV, Steps (iv)–(vii), formalized for the concrete region.
-/

namespace Iut

universe u

open NumberField
open scoped Pointwise

variable {D : InitialThetaData.{u}} (TA : TowerArithmetic D)

/-- `ord_p(1) = 0`. -/
lemma ordp_one (w : FinitePlace D.Kt) : ordp D.Kt w 1 = 0 := by
  simp [ordp, norm_one]

namespace LocalTheory

variable (K : Type u) [Field K] [NumberField K]

/-- `ord_p(x^m) = m·ord_p(x)`. -/
lemma ordp_pow (w : FinitePlace K) (x : completionAt K w) (hx : x ≠ 0) (m : ℕ) :
    ordp K w (x ^ m) = m * ordp K w x := by
  induction m with
  | zero => simp [ordp, norm_one]
  | succ k ih =>
    rw [pow_succ, LocalTheory.ordp_mul K w _ _ (pow_ne_zero _ hx) hx, ih]
    push_cast; ring

/-- The packet log-volume of a scaled integral region is the weighted sum of the component
log-volumes. -/
lemma packetVol_scaledIntegral (n : ℕ) (i : Fin (LocalTheory.container K n).proc.length)
    (vQ : RationalPlace) (a : ((LocalTheory.container K n).packet i vQ).Total) :
    (LocalTheory.vol K n).packetVol i vQ
        (((LocalTheory.container K n).packet i vQ).scaledIntegral a) =
      ∑ c : (LocalTheory.container K n).Components i vQ, (∏ j, LocalTheory.weight K vQ (c j)) *
        LocalTheory.componentVol K vQ (LocalTheory.tuple K vQ c)
            (LocalTheory.scaled K vQ c (a c)) :=
  (LocalTheory.vol K n).packetVol_product i vQ (fun c => LocalTheory.scaled K vQ c (a c)) fun c =>
    ⟨_, Set.smul_mem_smul_set (a := (a c : LocalTheory.Tensor K vQ (LocalTheory.tuple K vQ c)))
      (LocalTheory.one_mem_integral K vQ (LocalTheory.tuple K vQ c))⟩

/-- The cardinality of the label type of a capsule of the standard procession. -/
lemma card_labelType (n : ℕ) (i : Fin n) :
    Fintype.card ((Procession.standard n).capsule i).LabelType = i.1 + 2 := by
  change Fintype.card ↥((Procession.standard n).capsule i).labels = i.1 + 2
  rw [Fintype.card_coe]
  exact Procession.standard_capsule_card n i

end LocalTheory

namespace InitialThetaData

/-- `log(d^K_p)` at a prime, as the weighted sum over the fiber. -/
lemma logDK_prime (D : InitialThetaData.{u}) (p : Nat.Primes) :
    D.logDK p = ∑ v : LocalTheory.Fiber D.Kt (.finite p),
      LocalTheory.weight D.Kt _ v * differentExponent D.Kt (LocalTheory.fiberPlace D.Kt v) *
          Real.log p := by
  unfold InitialThetaData.logDK
  rw [dif_pos p.2]
  rfl

end InitialThetaData


/-- Evaluation of the weighted average of the per-tuple bounds (Proposition 1.7). -/
lemma sum_bound_eval {ι E : Type*} [Fintype ι] [Fintype E] (w : E → ℝ)
    (hw : ∑ e, w e = 1) (o d : E → ℝ) (J L T : ℝ) (j : ι) [inst : Fintype (ι → E)] :
    ∑ c : ι → E, (∏ l, w (c l)) * ((-J * o (c j) + ∑ l, d (c l) + 1) * L + ∑ _l : ι, T) =
      (-J * ∑ e, w e * o e + Fintype.card ι * ∑ e, w e * d e + 1) * L +
        Fintype.card ι * T := by
  classical
  rw [Subsingleton.elim inst Pi.instFintype]
  clear inst
  have key : ∀ c : ι → E, (∏ l, w (c l)) * ((-J * o (c j) + ∑ l, d (c l) + 1) * L +
      ∑ _l : ι, T) = (-J * L) * ((∏ l, w (c l)) * o (c j)) +
        L * ((∏ l, w (c l)) * ∑ l, d (c l)) + L * (∏ l, w (c l)) +
        (Fintype.card ι * T) * (∏ l, w (c l)) := by
    intro c
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_prod_tuple_mul_coord w hw o j, sum_prod_tuple_mul_sum w hw d,
    sum_prod_tuple_eq_one w hw]
  ring

namespace TowerArithmetic

local notation "𝒳" => concreteVariantData D

/-- The number of capsules, `ℓ* = (ℓ − 1)/2`. -/
abbrev nCaps : ℕ := (D.ℓ - 1) / 2

/-- The label type of the `i`-th capsule. -/
abbrev Lab (i : Fin (nCaps (D := D))) : Type :=
  ((Procession.standard (nCaps (D := D))).capsule i).LabelType

variable (D)

/-- The different exponents along a tuple. -/
noncomputable def dTuple {ι : Type} (p : Nat.Primes)
    (c : ι → LocalTheory.Fiber D.Kt (.finite p)) (i : ι) :
    ℝ :=
  differentExponent D.Kt (LocalTheory.fiberPlace D.Kt (c i))

lemma dTuple_spec {ι : Type} (p : Nat.Primes) (c : ι → LocalTheory.Fiber D.Kt (.finite p)) (i : ι)
    (w' : FinitePlace D.Kt) (h : LocalTheory.tuple D.Kt _ c i = Place.finite w') :
    dTuple D p c i = differentExponent D.Kt w' := by
  unfold dTuple
  congr 1
  have := LocalTheory.fiberPlace_spec D.Kt (c i)
  simp only [LocalTheory.tuple] at h
  rw [this] at h
  exact Sum.inl.inj h

variable {D}

/-- **Proposition 1.4(iii)** applied to the scaling element of a tuple at a distinguished
prime. -/
lemma prop14 (i : Fin (nCaps (D := D))) (p : Nat.Primes)
    (c : Lab i → LocalTheory.Fiber D.Kt (.finite p)) :
    ∃ a : LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c), IsUnit a ∧
      (∀ φ ∈ LocalTheory.indAut D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c),
        φ '' (D.scaleElt _ i p c • LocalTheory.integral D.Kt (.finite p)
            (LocalTheory.tuple D.Kt _ c)) ⊆
          a • LocalTheory.integral D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c)) ∧
      LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c)
          (a • LocalTheory.integral D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c)) ≤
        (-ordp D.Kt (LocalTheory.fiberPlace D.Kt (c (InitialThetaData.distinguished _ i)))
            (D.qroot (LocalTheory.fiberPlace D.Kt (c (InitialThetaData.distinguished _ i))) ^
                (i.1 + 1) ^ 2) +
          ∑ j, dTuple D p c j + 1) * Real.log p +
          ∑ j, if (p : ℕ) - 2 < ramIdxAt D.Kt (LocalTheory.tuple D.Kt _ c j) then
            3 + Real.log (ramIdxAt D.Kt (LocalTheory.tuple D.Kt _ c j)) else 0 :=
  LocalTheory.prop14_iii D.Kt p (LocalTheory.tuple D.Kt _ c) (LocalTheory.tuple_isOver D.Kt p c)
      (dTuple D p c)
    (InitialThetaData.distinguished _ i)
    (LocalTheory.fiberPlace D.Kt (c (InitialThetaData.distinguished _ i)))
        (LocalTheory.fiberPlace_spec D.Kt _)
    (D.qroot _ ^ (i.1 + 1) ^ 2) (pow_ne_zero _ (D.qroot_ne_zero _))
    (D.ordp_pow_nonneg _ _) (fun j w' h => dTuple_spec D p c j w' h)

/-- The chosen containing scalar `a_c` of a tuple at a distinguished prime. -/
noncomputable def contScalar (i : Fin (nCaps (D := D))) (p : Nat.Primes)
    (c : Lab i → LocalTheory.Fiber D.Kt (.finite p)) : LocalTheory.Tensor D.Kt (.finite p)
        (LocalTheory.tuple D.Kt _ c) :=
  Classical.choose (prop14 (D := D) i p c)

lemma contScalar_spec (i : Fin (nCaps (D := D))) (p : Nat.Primes)
    (c : Lab i → LocalTheory.Fiber D.Kt (.finite p)) :
    IsUnit (contScalar (D := D) i p c) ∧
      (∀ φ ∈ LocalTheory.indAut D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c),
        φ '' (D.scaleElt _ i p c • LocalTheory.integral D.Kt (.finite p)
            (LocalTheory.tuple D.Kt _ c)) ⊆
          contScalar (D := D) i p c • LocalTheory.integral D.Kt (.finite p)
              (LocalTheory.tuple D.Kt _ c)) ∧
      LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c)
        (contScalar (D := D) i p c • LocalTheory.integral D.Kt (.finite p)
            (LocalTheory.tuple D.Kt _ c)) ≤
        (-ordp D.Kt (LocalTheory.fiberPlace D.Kt (c (InitialThetaData.distinguished _ i)))
            (D.qroot (LocalTheory.fiberPlace D.Kt (c (InitialThetaData.distinguished _ i))) ^
                (i.1 + 1) ^ 2) +
          ∑ j, dTuple D p c j + 1) * Real.log p +
          ∑ j, if (p : ℕ) - 2 < ramIdxAt D.Kt (LocalTheory.tuple D.Kt _ c j) then
            3 + Real.log (ramIdxAt D.Kt (LocalTheory.tuple D.Kt _ c j)) else 0 :=
  Classical.choose_spec (prop14 (D := D) i p c)

/-- The archimedean scalar `π^{|I|}`. -/
noncomputable def archScalar (i : Fin (nCaps (D := D)))
    (c : Lab i → LocalTheory.Fiber D.Kt .infinite) :
    LocalTheory.Tensor D.Kt .infinite (LocalTheory.tuple D.Kt .infinite c) :=
  algebraMap ℝ (LocalTheory.Tensor D.Kt .infinite (LocalTheory.tuple D.Kt .infinite c))
      (Real.pi ^ (i.1 + 2))

lemma isUnit_archScalar (i : Fin (nCaps (D := D))) (c : Lab i → LocalTheory.Fiber D.Kt .infinite) :
    IsUnit (archScalar (D := D) i c) :=
  (isUnit_iff_ne_zero.mpr (pow_ne_zero _ Real.pi_ne_zero)).map (algebraMap ℝ _)

/-- The containing region at a rational place, as a region of the packet
`LocalTheory.packet D.Kt (Lab i) v_ℚ` (definitionally the container's packet). -/
noncomputable def cont (i : Fin (nCaps (D := D))) :
    ∀ vQ : RationalPlace, Set (LocalTheory.packet D.Kt (Lab i) vQ).Total
  | .finite p =>
    if (p : ℕ) ∈ D.dst then
      (LocalTheory.packet D.Kt (Lab i) (.finite p)).scaledIntegral fun c => contScalar
          (D := D) i p c
    else (LocalTheory.packet D.Kt (Lab i) (.finite p)).integralRegion
  | .infinite => (LocalTheory.packet D.Kt (Lab i) .infinite).scaledIntegral fun c => archScalar
      (D := D) i c

/-- The packet log-volume of a scaled integral region, in the theta-region's types. -/
lemma packetVol_scaledIntegral' (i : Fin (nCaps (D := D))) (vQ : RationalPlace)
    (a : (LocalTheory.packet D.Kt (Lab i) vQ).Total) :
    (LocalTheory.vol D.Kt (nCaps (D := D))).packetVol i vQ
        ((LocalTheory.packet D.Kt (Lab i) vQ).scaledIntegral a) =
      ∑ c : Lab i → LocalTheory.Fiber D.Kt vQ, (∏ j, LocalTheory.weight D.Kt vQ (c j)) *
        LocalTheory.componentVol D.Kt vQ (LocalTheory.tuple D.Kt vQ c)
            (LocalTheory.scaled D.Kt vQ c (a c)) :=
  (LocalTheory.packetVol_scaledIntegral D.Kt (nCaps (D := D)) i vQ a).trans
    (@Fintype.sum_equiv _ _ ℝ
        ((LocalTheory.container D.Kt (nCaps (D := D))).instFintypeComponents i vQ)
      Pi.instFintype _ (Equiv.refl _) _ _ fun _ => rfl)

/-- `log(q_p)` for the concrete `q`-pilot data, in terms of the local theta data. -/
lemma logQAt_eq (p : Nat.Primes) :
    (𝒳).logQAt p = 2 * D.ℓ * Real.log p *
      ∑ v : LocalTheory.Fiber D.Kt (.finite p), LocalTheory.weight D.Kt (.finite p) v *
        ordp D.Kt (LocalTheory.fiberPlace D.Kt v) (D.qroot (LocalTheory.fiberPlace D.Kt v)) := by
  rw [D.sum_weight_ordp_qroot p D.bad_finite.toFinset D.bad_finite.coe_toFinset]
  have hℓ : (2 * D.ℓ : ℝ) ≠ 0 := by
    have : (5 : ℝ) ≤ D.ℓ := by exact_mod_cast D.prime.five_le
    positivity
  have h1 : (𝒳).logQAt p = ∑ w ∈ (D.qPilot).badFinset.attach.filter
      (fun w => residueChar w.1 = p),
      (inertDeg D.F w.1 : ℝ) / Module.finrank ℚ D.F *
        (D.prime.qOrder w.1 ((D.qPilot).mem_bad w.2) : ℝ) *
        Real.log (residueChar w.1) := rfl
  rw [h1, mul_div_assoc', mul_comm (2 * (D.ℓ : ℝ)) (Real.log p), mul_assoc, mul_div_assoc,
    mul_div_cancel_left₀ _ hℓ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [(Finset.mem_filter.mp hw).2]
  ring

include TA in
/-- The (R4) bound in the form used per place: each ramification term is at most
`4·l*_mod·ι_p`. -/
lemma ramTerm_le (p : Nat.Primes) (v : FinitePlace D.Kt) (hv : residueChar v = p) :
    (if (p : ℕ) - 2 < ramIdx D.Kt v then 3 + Real.log (ramIdx D.Kt v) else 0) ≤
      4 * (D.invariants).lmod *
        (D.invariants).ι p := by
  have hlmod : (D.invariants).lmod =
      Real.log (((552960 * D.dmod : ℕ) : ℝ) * D.ℓ) := rfl
  have hlmod0 : 0 ≤ (D.invariants).lmod := by
    rw [hlmod]
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ D.dmod := by exact_mod_cast D.one_le_dmod
    have h2 : (5 : ℝ) ≤ D.ℓ := by exact_mod_cast D.prime.five_le
    push_cast
    nlinarith
  split_ifs with h
  · obtain ⟨hp, hlog⟩ := TA.ramIdx_bound v (hv ▸ h)
    have hι : (D.invariants).ι p = 1 := by
      change (if (p : ℕ) ≤ 552960 * D.dmod * D.ℓ then (1 : ℝ) else 0) = 1
      rw [if_pos]
      rw [← hv]; exact hp
    rw [hι, mul_one, hlmod]
    linarith
  · exact mul_nonneg (mul_nonneg (by norm_num) hlmod0)
      ((D.invariants).ι_nonneg p)

/-! ### The estimates -/

lemma cont_isHullRegion (i : Fin (nCaps (D := D))) (vQ : RationalPlace) :
    (LocalTheory.packet D.Kt (Lab i) vQ).IsHullRegion (cont (D := D) i vQ) := by
  rcases vQ with p | _
  · change DirectSumPresentation.IsHullRegion _ (if (p : ℕ) ∈ D.dst then _ else _)
    split_ifs with hp
    · exact ⟨_, fun c => (contScalar_spec (D := D) i p c).1, rfl⟩
    · exact DirectSumPresentation.isHullRegion_integralRegion _
  · exact ⟨_, fun c => isUnit_archScalar (D := D) i c, rfl⟩

/-- Each container belongs to the class of hull regions of the concrete hull system: at a
prime it is a hull region, at `∞` the real radial scaling `π^{|I|}·B_I`. -/
lemma cont_mem_hullRegions (i : Fin (nCaps (D := D))) (vQ : RationalPlace) :
    cont (D := D) i vQ ∈ LocalTheory.hullRegions D.Kt (Lab i) vQ := by
  rcases vQ with p | _
  · exact cont_isHullRegion (D := D) i (.finite p)
  · exact ⟨fun _ => Real.pi ^ (i.1 + 2), fun _ => pow_pos Real.pi_pos _, rfl⟩

lemma thetaPilot_subset (i : Fin (nCaps (D := D))) (vQ : RationalPlace) :
    (LocalTheory.packet D.Kt (Lab i) vQ).productRegion (fun c => D.thetaComponent _ i vQ c) ⊆
      cont (D := D) i vQ := by
  rcases vQ with p | _
  · intro x hx
    change x ∈ (if (p : ℕ) ∈ D.dst then _ else _)
    split_ifs with hp
    · intro c
      have hxc : x c ∈ D.thetaComponent _ i (.finite p) c := hx c
      change x c ∈ ⋃ φ ∈ LocalTheory.indAut D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c),
        φ '' (D.scaleElt _ i p c • LocalTheory.integral D.Kt (.finite p)
            (LocalTheory.tuple D.Kt _ c)) at hxc
      obtain ⟨φ, hφ, hxc⟩ := Set.mem_iUnion₂.mp hxc
      exact (contScalar_spec (D := D) i p c).2.1 φ hφ hxc
    · intro c
      have hxc : x c ∈ D.thetaComponent _ i (.finite p) c := hx c
      have hbad : (p : ℕ) ∉ D.badChars := fun h => hp (D.mem_dst_of_badChars _ h)
      rw [D.thetaComponent_eq_integral _ i p c hbad] at hxc
      exact hxc
  · intro x hx c
    have hxc : x c ∈ LocalTheory.thetaInfinite D.Kt _ i c := hx c
    change x c ∈ ⋃ φ ∈ LocalTheory.indAut D.Kt .infinite (LocalTheory.tuple D.Kt .infinite c),
      φ '' LocalTheory.logShell D.Kt .infinite (LocalTheory.tuple D.Kt .infinite c) at hxc
    obtain ⟨φ, hφ, hxc⟩ := Set.mem_iUnion₂.mp hxc
    have := LocalTheory.prop15 D.Kt (LocalTheory.tuple D.Kt .infinite c) φ hφ hxc
    rw [LocalTheory.card_labelType] at this
    exact this

include TA in
lemma vol_finite (i : Fin (nCaps (D := D))) (p : Nat.Primes) (hp : (p : ℕ) ∈ D.dst) :
    (LocalTheory.vol D.Kt (nCaps (D := D))).packetVol i (.finite p) (cont (D := D) i (.finite p)) ≤
      (D.invariants).capsuleBound (i.1 + 2) p := by
  change (LocalTheory.vol D.Kt (nCaps (D := D))).packetVol i (.finite p)
    (if (p : ℕ) ∈ D.dst then _ else _) ≤ _
  rw [if_pos hp, packetVol_scaledIntegral']
  have hcardι : Fintype.card (Lab i) = i.1 + 2 := LocalTheory.card_labelType _ i
  have hw1 : ∑ v, LocalTheory.weight D.Kt (.finite p) v = 1 := LocalTheory.weight_sum_one D.Kt _
  -- bound each tuple by the (R4)-simplified form
  have hstep : ∀ c : Lab i → LocalTheory.Fiber D.Kt (.finite p),
      (∏ l, LocalTheory.weight D.Kt (.finite p) (c l)) *
        LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.Kt _ c)
            (LocalTheory.scaled D.Kt _ c (contScalar (D := D) i p c)) ≤
      (∏ l, LocalTheory.weight D.Kt (.finite p) (c l)) *
        ((-(((i.1 + 1 : ℕ) : ℝ) ^ 2) *
            (fun v => ordp D.Kt (LocalTheory.fiberPlace D.Kt v)
                (D.qroot (LocalTheory.fiberPlace D.Kt v)))
              (c (InitialThetaData.distinguished _ i))
            + ∑ l, (fun v => differentExponent D.Kt (LocalTheory.fiberPlace D.Kt v)) (c l) + 1) *
                Real.log p +
          ∑ _l : Lab i, (4 * (D.invariants).lmod *
              (D.invariants).ι p)) := by
    intro c
    apply mul_le_mul_of_nonneg_left _
        (Finset.prod_nonneg fun l _ => (LocalTheory.weight_pos D.Kt _ _).le)
    refine (contScalar_spec (D := D) i p c).2.2.trans ?_
    rw [LocalTheory.ordp_pow D.Kt _ _ (D.qroot_ne_zero _)]
    push_cast
    refine add_le_add (le_of_eq ?_) ?_
    · simp only [dTuple]; ring
    refine Finset.sum_le_sum fun l _ => ?_
    have hram : ramIdxAt D.Kt (LocalTheory.tuple D.Kt _ c l) = ramIdx D.Kt
        (LocalTheory.fiberPlace D.Kt (c l)) := by
      simp only [LocalTheory.tuple]; rw [LocalTheory.fiberPlace_spec D.Kt (c l)]; rfl
    rw [hram]
    exact TA.ramTerm_le p _ (LocalTheory.residueChar_fiberPlace D.Kt _)
  refine (Finset.sum_le_sum fun c _ => hstep c).trans ?_
  rw [sum_bound_eval (LocalTheory.weight D.Kt (.finite p)) hw1
    (fun v => ordp D.Kt (LocalTheory.fiberPlace D.Kt v) (D.qroot (LocalTheory.fiberPlace D.Kt v)))
    (fun v => differentExponent D.Kt (LocalTheory.fiberPlace D.Kt v)) _ _ _
        (InitialThetaData.distinguished _ i),
    hcardι]
  -- identify the averaged quantities
  have hq : (∑ e, LocalTheory.weight D.Kt (.finite p) e *
      ordp D.Kt (LocalTheory.fiberPlace D.Kt e) (D.qroot (LocalTheory.fiberPlace D.Kt e))) *
          Real.log p =
      (𝒳).logQAt p / (2 * D.ℓ) := by
    rw [logQAt_eq (D := D) p]
    have hℓ : (D.ℓ : ℝ) ≠ 0 := by
      have : (5 : ℝ) ≤ D.ℓ := by exact_mod_cast D.prime.five_le
      positivity
    field_simp
  have hd :
      (∑ e, LocalTheory.weight D.Kt (.finite p) e * differentExponent D.Kt
      (LocalTheory.fiberPlace D.Kt e)) *
      Real.log p = D.logDK p := by
    rw [D.logDK_prime p, Finset.sum_mul]
  change _ ≤ ((i.1 + 2 : ℕ) : ℝ) * D.logDK p -
    (((i.1 + 2 : ℕ) : ℝ) - 1) ^ 2 / (2 * D.ℓ) * (𝒳).logQAt p + Real.log p +
    4 * ((i.1 + 2 : ℕ) : ℝ) * (D.invariants).lmod *
      (D.invariants).ι p
  have h1 : (((i.1 + 2 : ℕ) : ℝ) - 1) ^ 2 = ((i.1 + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
  rw [h1, ← hd]
  have h2 : (((i.1 + 1 : ℕ) : ℝ) ^ 2) / (2 * D.ℓ) * (𝒳).logQAt p =
      ((i.1 + 1 : ℕ) : ℝ) ^ 2 * ((𝒳).logQAt p / (2 * D.ℓ)) := by ring
  rw [h2, ← hq]
  apply le_of_eq
  ring

lemma vol_infinite (i : Fin (nCaps (D := D))) :
    (LocalTheory.vol D.Kt (nCaps (D := D))).packetVol i .infinite (cont (D := D) i .infinite) ≤
      ((i.1 + 2 : ℕ) : ℝ) * Real.log Real.pi := by
  change (LocalTheory.vol D.Kt (nCaps (D := D))).packetVol i .infinite
    ((LocalTheory.packet D.Kt (Lab i) .infinite).scaledIntegral fun c => archScalar
        (D := D) i c) ≤ _
  rw [packetVol_scaledIntegral']
  have : ∀ c : Lab i → LocalTheory.Fiber D.Kt .infinite,
      LocalTheory.componentVol D.Kt .infinite (LocalTheory.tuple D.Kt _ c)
          (LocalTheory.scaled D.Kt _ c (archScalar (D := D) i c)) =
        ((i.1 + 2 : ℕ) : ℝ) * Real.log Real.pi := by
    intro c
    change LocalTheory.componentVol D.Kt .infinite (LocalTheory.tuple D.Kt _ c)
      (algebraMap ℝ (LocalTheory.Tensor D.Kt .infinite (LocalTheory.tuple D.Kt .infinite c))
          (Real.pi ^ (i.1 + 2)) •
        LocalTheory.integral D.Kt .infinite (LocalTheory.tuple D.Kt _ c)) = _
    rw [LocalTheory.componentVol_arch_scale D.Kt _ _ (pow_pos Real.pi_pos _), Real.log_pow]
  simp_rw [this]
  rw [← Finset.sum_mul, sum_prod_tuple_eq_one _ (LocalTheory.weight_sum_one D.Kt _), one_mul]

lemma packetVol_mono (i : Fin (nCaps (D := D))) (vQ : RationalPlace)
    (U V : Set (LocalTheory.packet D.Kt (Lab i) vQ).Total)
        (hU : (LocalTheory.packet D.Kt (Lab i) vQ).IsHullRegion U)
    (hV : (LocalTheory.packet D.Kt (Lab i) vQ).IsHullRegion V) (hUV : U ⊆ V) :
    (LocalTheory.vol D.Kt (nCaps (D := D))).packetVol i vQ U ≤
        (LocalTheory.vol D.Kt (nCaps (D := D))).packetVol i vQ V := by
  obtain ⟨a, ha, rfl⟩ := hU
  obtain ⟨b, hb, rfl⟩ := hV
  rw [packetVol_scaledIntegral', packetVol_scaledIntegral']
  refine Finset.sum_le_sum fun c _ => ?_
  apply mul_le_mul_of_nonneg_left _
      (Finset.prod_nonneg fun l _ => (LocalTheory.weight_pos D.Kt _ _).le)
  apply LocalTheory.componentVol_mono D.Kt vQ _ _ _ (ha c) (hb c)
  intro y hy
  classical
  have hx :
      (Function.update
      (fun c' : Lab i → LocalTheory.Fiber D.Kt vQ => LocalTheory.scaledOne D.Kt vQ c' (a c')) c y) ∈
      (LocalTheory.packet D.Kt (Lab i) vQ).scaledIntegral a := by
    intro c'
    by_cases h : c' = c
    · subst h; rw [Function.update_self]; exact hy
    · rw [Function.update_of_ne h]
      exact Set.smul_mem_smul_set (LocalTheory.one_mem_integral D.Kt vQ _)
  have := hUV hx c
  rwa [Function.update_self] at this

include TA in
/-- **The concrete local estimates** (IUT IV, Steps (iv)–(vii)). -/
noncomputable def localEstimate :
    (D.invariants).LocalEstimate where
  cont i vQ := cont (D := D) i vQ
  cont_mem_hullRegions i vQ := cont_mem_hullRegions (D := D) i vQ
  thetaPilot_subset i vQ := thetaPilot_subset (D := D) i vQ
  cont_eq_integral i p hp := by
    change (if (p : ℕ) ∈ D.dst then _ else _) = _
    exact if_neg hp
  vol_finite i p hp :=
    (TA.vol_finite (D := D) i p hp).trans_eq
      (congrArg (fun m => (D.invariants).capsuleBound m p)
        (Procession.standard_capsule_card _ i).symm)
  vol_infinite i :=
    (vol_infinite (D := D) i).trans_eq
      (congrArg (fun m : ℕ => (m : ℝ) * Real.log Real.pi)
        (Procession.standard_capsule_card _ i).symm)
  packetVol_mono i vQ U V hU hV hUV := packetVol_mono (D := D) i vQ U V hU hV hUV

end TowerArithmetic

end Iut
