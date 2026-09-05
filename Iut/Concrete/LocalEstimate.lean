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

universe u v

open NumberField
open scoped Pointwise

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt} {TL : ThetaLocalData D LT}
  {QI : QPilotInputs D} (TA : TowerArithmetic D LT TL)

/-- `ord_p(1) = 0`. -/
lemma ordp_one (w : FinitePlace D.Kt) : ordp D.Kt w 1 = 0 := by
  simp [ordp, norm_one]

namespace LocalTheory

variable (LT)

include LT in
/-- `ord_p(x^m) = m·ord_p(x)`. -/
lemma ordp_pow (w : FinitePlace D.Kt) (x : completionAt D.Kt w) (hx : x ≠ 0) (m : ℕ) :
    ordp D.Kt w (x ^ m) = m * ordp D.Kt w x := by
  induction m with
  | zero => simp [ordp_one]
  | succ k ih =>
    rw [pow_succ, LT.ordp_mul w _ _ (pow_ne_zero _ hx) hx, ih]
    push_cast; ring

/-- `log(d^K_p)` at a prime, as the weighted sum over the fiber. -/
lemma logDK_prime (p : Nat.Primes) :
    LT.logDK p = ∑ v : LT.Fiber (.finite p),
      LT.weight _ v * differentExponent D.Kt (LT.fiberPlace v) * Real.log p := by
  unfold logDK
  rw [dif_pos p.2]
  rfl

/-- The packet log-volume of a scaled integral region is the weighted sum of the component
log-volumes. -/
lemma packetVol_scaledIntegral (n : ℕ) (i : Fin (LT.container n).proc.length)
    (vQ : RationalPlace) (a : ((LT.container n).packet i vQ).Total) :
    (LT.vol n).packetVol i vQ (((LT.container n).packet i vQ).scaledIntegral a) =
      ∑ c : (LT.container n).Components i vQ, (∏ j, LT.weight vQ (c j)) *
        LT.componentVol vQ (LT.tuple vQ c) (LT.scaled vQ c (a c)) :=
  (LT.vol n).packetVol_product i vQ (fun c => LT.scaled vQ c (a c)) fun c =>
    ⟨_, Set.smul_mem_smul_set (a := (a c : LT.Tensor vQ (LT.tuple vQ c)))
      (LT.one_mem_integral vQ (LT.tuple vQ c))⟩

/-- The cardinality of the label type of a capsule of the standard procession. -/
lemma card_labelType (n : ℕ) (i : Fin n) :
    Fintype.card ((Procession.standard n).capsule i).LabelType = i.1 + 2 := by
  change Fintype.card ↥((Procession.standard n).capsule i).labels = i.1 + 2
  rw [Fintype.card_coe]
  exact Procession.standard_capsule_card n i

end LocalTheory

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

local notation "𝒳" => concreteVariantData D LT TL QI

/-- The number of capsules, `ℓ* = (ℓ − 1)/2`. -/
abbrev nCaps : ℕ := (D.ℓ - 1) / 2

/-- The label type of the `i`-th capsule. -/
abbrev Lab (i : Fin (nCaps (D := D))) : Type :=
  ((Procession.standard (nCaps (D := D))).capsule i).LabelType

variable (LT TL)

/-- The different exponents along a tuple. -/
noncomputable def dTuple {ι : Type} (p : Nat.Primes) (c : ι → LT.Fiber (.finite p)) (i : ι) :
    ℝ :=
  differentExponent D.Kt (LT.fiberPlace (c i))

lemma dTuple_spec {ι : Type} (p : Nat.Primes) (c : ι → LT.Fiber (.finite p)) (i : ι)
    (w' : FinitePlace D.Kt) (h : LT.tuple _ c i = Place.finite w') :
    dTuple LT p c i = differentExponent D.Kt w' := by
  unfold dTuple
  congr 1
  have := LT.fiberPlace_spec (c i)
  simp only [LocalTheory.tuple] at h
  rw [this] at h
  exact Sum.inl.inj h

variable {LT TL}

/-- **Proposition 1.4(iii)** applied to the scaling element of a tuple at a distinguished
prime. -/
lemma prop14 (i : Fin (nCaps (D := D))) (p : Nat.Primes) (c : Lab i → LT.Fiber (.finite p)) :
    ∃ a : LT.Tensor (.finite p) (LT.tuple _ c), IsUnit a ∧
      (∀ φ ∈ LT.indAut (.finite p) (LT.tuple _ c),
        φ '' (TL.scaleElt _ i p c • LT.integral (.finite p) (LT.tuple _ c)) ⊆
          a • LT.integral (.finite p) (LT.tuple _ c)) ∧
      LT.componentVol (.finite p) (LT.tuple _ c) (a • LT.integral (.finite p) (LT.tuple _ c)) ≤
        (-ordp D.Kt (LT.fiberPlace (c (ThetaLocalData.distinguished _ i)))
            (TL.qroot (LT.fiberPlace (c (ThetaLocalData.distinguished _ i))) ^ (i.1 + 1) ^ 2) +
          ∑ j, dTuple LT p c j + 1) * Real.log p +
          ∑ j, if (p : ℕ) - 2 < ramIdxAt D.Kt (LT.tuple _ c j) then
            3 + Real.log (ramIdxAt D.Kt (LT.tuple _ c j)) else 0 :=
  LT.prop14_iii p (LT.tuple _ c) (dTuple LT p c) (ThetaLocalData.distinguished _ i)
    (LT.fiberPlace (c (ThetaLocalData.distinguished _ i))) (LT.fiberPlace_spec _)
    (TL.qroot _ ^ (i.1 + 1) ^ 2) (pow_ne_zero _ (TL.qroot_ne_zero _))
    (TL.ordp_pow_nonneg _ _) (fun j w' h => dTuple_spec LT p c j w' h)

/-- The chosen containing scalar `a_c` of a tuple at a distinguished prime. -/
noncomputable def contScalar (i : Fin (nCaps (D := D))) (p : Nat.Primes)
    (c : Lab i → LT.Fiber (.finite p)) : LT.Tensor (.finite p) (LT.tuple _ c) :=
  Classical.choose (prop14 (TL := TL) i p c)

lemma contScalar_spec (i : Fin (nCaps (D := D))) (p : Nat.Primes)
    (c : Lab i → LT.Fiber (.finite p)) :
    IsUnit (contScalar (TL := TL) i p c) ∧
      (∀ φ ∈ LT.indAut (.finite p) (LT.tuple _ c),
        φ '' (TL.scaleElt _ i p c • LT.integral (.finite p) (LT.tuple _ c)) ⊆
          contScalar (TL := TL) i p c • LT.integral (.finite p) (LT.tuple _ c)) ∧
      LT.componentVol (.finite p) (LT.tuple _ c)
        (contScalar (TL := TL) i p c • LT.integral (.finite p) (LT.tuple _ c)) ≤
        (-ordp D.Kt (LT.fiberPlace (c (ThetaLocalData.distinguished _ i)))
            (TL.qroot (LT.fiberPlace (c (ThetaLocalData.distinguished _ i))) ^ (i.1 + 1) ^ 2) +
          ∑ j, dTuple LT p c j + 1) * Real.log p +
          ∑ j, if (p : ℕ) - 2 < ramIdxAt D.Kt (LT.tuple _ c j) then
            3 + Real.log (ramIdxAt D.Kt (LT.tuple _ c j)) else 0 :=
  Classical.choose_spec (prop14 (TL := TL) i p c)

/-- The archimedean scalar `π^{|I|}`. -/
noncomputable def archScalar (i : Fin (nCaps (D := D))) (c : Lab i → LT.Fiber .infinite) :
    LT.Tensor .infinite (LT.tuple .infinite c) :=
  algebraMap ℝ (LT.Tensor .infinite (LT.tuple .infinite c)) (Real.pi ^ (i.1 + 2))

lemma isUnit_archScalar (i : Fin (nCaps (D := D))) (c : Lab i → LT.Fiber .infinite) :
    IsUnit (archScalar (LT := LT) i c) :=
  (isUnit_iff_ne_zero.mpr (pow_ne_zero _ Real.pi_ne_zero)).map (algebraMap ℝ _)

/-- The containing region at a rational place, as a region of the packet
`LT.packet (Lab i) v_ℚ` (definitionally the container's packet). -/
noncomputable def cont (i : Fin (nCaps (D := D))) :
    ∀ vQ : RationalPlace, Set (LT.packet (Lab i) vQ).Total
  | .finite p =>
    if (p : ℕ) ∈ TL.dst then
      (LT.packet (Lab i) (.finite p)).scaledIntegral fun c => contScalar (TL := TL) i p c
    else (LT.packet (Lab i) (.finite p)).integralRegion
  | .infinite => (LT.packet (Lab i) .infinite).scaledIntegral fun c => archScalar (LT := LT) i c

/-- The packet log-volume of a scaled integral region, in the theta-region's types. -/
lemma packetVol_scaledIntegral' (i : Fin (nCaps (D := D))) (vQ : RationalPlace)
    (a : (LT.packet (Lab i) vQ).Total) :
    (LT.vol (nCaps (D := D))).packetVol i vQ ((LT.packet (Lab i) vQ).scaledIntegral a) =
      ∑ c : Lab i → LT.Fiber vQ, (∏ j, LT.weight vQ (c j)) *
        LT.componentVol vQ (LT.tuple vQ c) (LT.scaled vQ c (a c)) :=
  (LT.packetVol_scaledIntegral (nCaps (D := D)) i vQ a).trans
    (@Fintype.sum_equiv _ _ ℝ ((LT.container (nCaps (D := D))).instFintypeComponents i vQ)
      Pi.instFintype _ (Equiv.refl _) _ _ fun _ => rfl)

/-- `log(q_p)` for the concrete `q`-pilot data, in terms of the local theta data. -/
lemma logQAt_eq (p : Nat.Primes) :
    (𝒳).logQAt p = 2 * D.ℓ * Real.log p *
      ∑ v : LT.Fiber (.finite p), LT.weight (.finite p) v *
        ordp D.Kt (LT.fiberPlace v) (TL.qroot (LT.fiberPlace v)) := by
  rw [TL.sum_weight_ordp_qroot p QI.bad_finite.toFinset QI.bad_finite.coe_toFinset]
  have hℓ : (2 * D.ℓ : ℝ) ≠ 0 := by
    have : (5 : ℝ) ≤ D.ℓ := by exact_mod_cast D.prime.five_le
    positivity
  have h1 : (𝒳).logQAt p = ∑ w ∈ (QI.qPilot).badFinset.attach.filter
      (fun w => residueChar w.1 = p),
      (inertDeg D.F w.1 : ℝ) / Module.finrank ℚ D.F *
        (D.prime.qOrder w.1 ((QI.qPilot).mem_bad w.2) : ℝ) *
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
      4 * (TL.invariants QI).lmod *
        (TL.invariants QI).ι p := by
  have hlmod : (TL.invariants QI).lmod =
      Real.log (((552960 * D.dmod : ℕ) : ℝ) * D.ℓ) := rfl
  have hlmod0 : 0 ≤ (TL.invariants QI).lmod := by
    rw [hlmod]
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ D.dmod := by exact_mod_cast D.one_le_dmod
    have h2 : (5 : ℝ) ≤ D.ℓ := by exact_mod_cast D.prime.five_le
    push_cast
    nlinarith
  split_ifs with h
  · obtain ⟨hp, hlog⟩ := TA.ramIdx_bound v (hv ▸ h)
    have hι : (TL.invariants QI).ι p = 1 := by
      change (if (p : ℕ) ≤ 552960 * D.dmod * D.ℓ then (1 : ℝ) else 0) = 1
      rw [if_pos]
      rw [← hv]; exact hp
    rw [hι, mul_one, hlmod]
    linarith
  · exact mul_nonneg (mul_nonneg (by norm_num) hlmod0)
      ((TL.invariants QI).ι_nonneg p)

/-! ### The estimates -/

lemma cont_isHullRegion (i : Fin (nCaps (D := D))) (vQ : RationalPlace) :
    (LT.packet (Lab i) vQ).IsHullRegion (cont (TL := TL) i vQ) := by
  rcases vQ with p | _
  · change DirectSumPresentation.IsHullRegion _ (if (p : ℕ) ∈ TL.dst then _ else _)
    split_ifs with hp
    · exact ⟨_, fun c => (contScalar_spec (TL := TL) i p c).1, rfl⟩
    · exact DirectSumPresentation.isHullRegion_integralRegion _
  · exact ⟨_, fun c => isUnit_archScalar (LT := LT) i c, rfl⟩

lemma thetaPilot_subset (i : Fin (nCaps (D := D))) (vQ : RationalPlace) :
    (LT.packet (Lab i) vQ).productRegion (fun c => TL.thetaComponent _ i vQ c) ⊆
      cont (TL := TL) i vQ := by
  rcases vQ with p | _
  · intro x hx
    change x ∈ (if (p : ℕ) ∈ TL.dst then _ else _)
    split_ifs with hp
    · intro c
      have hxc : x c ∈ TL.thetaComponent _ i (.finite p) c := hx c
      change x c ∈ ⋃ φ ∈ LT.indAut (.finite p) (LT.tuple _ c),
        φ '' (TL.scaleElt _ i p c • LT.integral (.finite p) (LT.tuple _ c)) at hxc
      obtain ⟨φ, hφ, hxc⟩ := Set.mem_iUnion₂.mp hxc
      exact (contScalar_spec (TL := TL) i p c).2.1 φ hφ hxc
    · intro c
      have hxc : x c ∈ TL.thetaComponent _ i (.finite p) c := hx c
      have hbad : (p : ℕ) ∉ TL.badChars := fun h => hp (TL.mem_dst_of_badChars _ h)
      rw [TL.thetaComponent_eq_integral _ i p c hbad] at hxc
      exact hxc
  · intro x hx c
    have hxc : x c ∈ LT.thetaInfinite _ i c := hx c
    change x c ∈ ⋃ φ ∈ LT.indAut .infinite (LT.tuple .infinite c),
      φ '' LT.logShell .infinite (LT.tuple .infinite c) at hxc
    obtain ⟨φ, hφ, hxc⟩ := Set.mem_iUnion₂.mp hxc
    have := LT.prop15 (LT.tuple .infinite c) φ hφ hxc
    rw [LocalTheory.card_labelType] at this
    exact this

include TA in
lemma vol_finite (i : Fin (nCaps (D := D))) (p : Nat.Primes) (hp : (p : ℕ) ∈ TL.dst) :
    (LT.vol (nCaps (D := D))).packetVol i (.finite p) (cont (TL := TL) i (.finite p)) ≤
      (TL.invariants QI).capsuleBound (i.1 + 2) p := by
  change (LT.vol (nCaps (D := D))).packetVol i (.finite p)
    (if (p : ℕ) ∈ TL.dst then _ else _) ≤ _
  rw [if_pos hp, packetVol_scaledIntegral']
  have hcardι : Fintype.card (Lab i) = i.1 + 2 := LocalTheory.card_labelType _ i
  have hw1 : ∑ v, LT.weight (.finite p) v = 1 := LT.weight_sum_one _
  -- bound each tuple by the (R4)-simplified form
  have hstep : ∀ c : Lab i → LT.Fiber (.finite p),
      (∏ l, LT.weight (.finite p) (c l)) *
        LT.componentVol (.finite p) (LT.tuple _ c) (LT.scaled _ c (contScalar (TL := TL) i p c)) ≤
      (∏ l, LT.weight (.finite p) (c l)) *
        ((-(((i.1 + 1 : ℕ) : ℝ) ^ 2) *
            (fun v => ordp D.Kt (LT.fiberPlace v) (TL.qroot (LT.fiberPlace v)))
              (c (ThetaLocalData.distinguished _ i))
            + ∑ l, (fun v => differentExponent D.Kt (LT.fiberPlace v)) (c l) + 1) * Real.log p +
          ∑ _l : Lab i, (4 * (TL.invariants QI).lmod *
              (TL.invariants QI).ι p)) := by
    intro c
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun l _ => (LT.weight_pos _ _).le)
    refine (contScalar_spec (TL := TL) i p c).2.2.trans ?_
    rw [LT.ordp_pow _ _ (TL.qroot_ne_zero _)]
    push_cast
    refine add_le_add (le_of_eq ?_) ?_
    · simp only [dTuple]; ring
    refine Finset.sum_le_sum fun l _ => ?_
    have hram : ramIdxAt D.Kt (LT.tuple _ c l) = ramIdx D.Kt (LT.fiberPlace (c l)) := by
      simp only [LocalTheory.tuple]; rw [LT.fiberPlace_spec (c l)]; rfl
    rw [hram]
    exact TA.ramTerm_le p _ (LT.residueChar_fiberPlace _)
  refine (Finset.sum_le_sum fun c _ => hstep c).trans ?_
  rw [sum_bound_eval (LT.weight (.finite p)) hw1
    (fun v => ordp D.Kt (LT.fiberPlace v) (TL.qroot (LT.fiberPlace v)))
    (fun v => differentExponent D.Kt (LT.fiberPlace v)) _ _ _ (ThetaLocalData.distinguished _ i),
    hcardι]
  -- identify the averaged quantities
  have hq : (∑ e, LT.weight (.finite p) e *
      ordp D.Kt (LT.fiberPlace e) (TL.qroot (LT.fiberPlace e))) * Real.log p =
      (𝒳).logQAt p / (2 * D.ℓ) := by
    rw [logQAt_eq (TL := TL) (QI := QI) p]
    have hℓ : (D.ℓ : ℝ) ≠ 0 := by
      have : (5 : ℝ) ≤ D.ℓ := by exact_mod_cast D.prime.five_le
      positivity
    field_simp
  have hd : (∑ e, LT.weight (.finite p) e * differentExponent D.Kt (LT.fiberPlace e)) *
      Real.log p = LT.logDK p := by
    rw [LT.logDK_prime p, Finset.sum_mul]
  change _ ≤ ((i.1 + 2 : ℕ) : ℝ) * LT.logDK p -
    (((i.1 + 2 : ℕ) : ℝ) - 1) ^ 2 / (2 * D.ℓ) * (𝒳).logQAt p + Real.log p +
    4 * ((i.1 + 2 : ℕ) : ℝ) * (TL.invariants QI).lmod *
      (TL.invariants QI).ι p
  have h1 : (((i.1 + 2 : ℕ) : ℝ) - 1) ^ 2 = ((i.1 + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
  rw [h1, ← hd]
  have h2 : (((i.1 + 1 : ℕ) : ℝ) ^ 2) / (2 * D.ℓ) * (𝒳).logQAt p =
      ((i.1 + 1 : ℕ) : ℝ) ^ 2 * ((𝒳).logQAt p / (2 * D.ℓ)) := by ring
  rw [h2, ← hq]
  apply le_of_eq
  ring

lemma vol_infinite (i : Fin (nCaps (D := D))) :
    (LT.vol (nCaps (D := D))).packetVol i .infinite (cont (TL := TL) i .infinite) ≤
      ((i.1 + 2 : ℕ) : ℝ) * Real.log Real.pi := by
  change (LT.vol (nCaps (D := D))).packetVol i .infinite
    ((LT.packet (Lab i) .infinite).scaledIntegral fun c => archScalar (LT := LT) i c) ≤ _
  rw [packetVol_scaledIntegral']
  have : ∀ c : Lab i → LT.Fiber .infinite,
      LT.componentVol .infinite (LT.tuple _ c) (LT.scaled _ c (archScalar (LT := LT) i c)) =
        ((i.1 + 2 : ℕ) : ℝ) * Real.log Real.pi := by
    intro c
    change LT.componentVol .infinite (LT.tuple _ c)
      (algebraMap ℝ (LT.Tensor .infinite (LT.tuple .infinite c)) (Real.pi ^ (i.1 + 2)) •
        LT.integral .infinite (LT.tuple _ c)) = _
    rw [LT.componentVol_arch_scale _ _ (pow_pos Real.pi_pos _), Real.log_pow]
  simp_rw [this]
  rw [← Finset.sum_mul, sum_prod_tuple_eq_one _ (LT.weight_sum_one _), one_mul]

lemma packetVol_mono (i : Fin (nCaps (D := D))) (vQ : RationalPlace)
    (U V : Set (LT.packet (Lab i) vQ).Total) (hU : (LT.packet (Lab i) vQ).IsHullRegion U)
    (hV : (LT.packet (Lab i) vQ).IsHullRegion V) (hUV : U ⊆ V) :
    (LT.vol (nCaps (D := D))).packetVol i vQ U ≤ (LT.vol (nCaps (D := D))).packetVol i vQ V := by
  obtain ⟨a, ha, rfl⟩ := hU
  obtain ⟨b, hb, rfl⟩ := hV
  rw [packetVol_scaledIntegral', packetVol_scaledIntegral']
  refine Finset.sum_le_sum fun c _ => ?_
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun l _ => (LT.weight_pos _ _).le)
  apply LT.componentVol_mono vQ _ _ _ (ha c) (hb c)
  intro y hy
  classical
  have hx : (Function.update (fun c' : Lab i → LT.Fiber vQ => LT.scaledOne vQ c' (a c')) c y) ∈
      (LT.packet (Lab i) vQ).scaledIntegral a := by
    intro c'
    by_cases h : c' = c
    · subst h; rw [Function.update_self]; exact hy
    · rw [Function.update_of_ne h]
      exact Set.smul_mem_smul_set (LT.one_mem_integral vQ _)
  have := hUV hx c
  rwa [Function.update_self] at this

include TA in
/-- **The concrete local estimates** (IUT IV, Steps (iv)–(vii)). -/
noncomputable def localEstimate :
    (TL.invariants QI).LocalEstimate where
  cont i vQ := cont (TL := TL) i vQ
  cont_isHullRegion i vQ := cont_isHullRegion (TL := TL) i vQ
  thetaPilot_subset i vQ := thetaPilot_subset (TL := TL) i vQ
  cont_eq_integral i p hp := by
    change (if (p : ℕ) ∈ TL.dst then _ else _) = _
    exact if_neg hp
  vol_finite i p hp :=
    (TA.vol_finite (TL := TL) (QI := QI) i p hp).trans_eq
      (congrArg (fun m => (TL.invariants QI).capsuleBound m p)
        (Procession.standard_capsule_card _ i).symm)
  vol_infinite i :=
    (vol_infinite (TL := TL) i).trans_eq
      (congrArg (fun m : ℕ => (m : ℝ) * Real.log Real.pi)
        (Procession.standard_capsule_card _ i).symm)
  packetVol_mono i vQ U V hU hV hUV := packetVol_mono (LT := LT) i vQ U V hU hV hUV

end TowerArithmetic

end Iut
