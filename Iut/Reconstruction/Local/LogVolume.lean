/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.LocalLogShell

/-!
# The Haar volume of the log-shell (roadmap P17, M3c)

[AbsTopIII], Proposition 5.7 (i) (c) and Proposition 5.8 (iii): the logarithm is
volume-preserving on the deep principal units, which computes the Haar volume of the log-shell

`𝓘_k = (2p)⁻¹ log 𝒪_k^× = (2p)⁻¹ log U^{(1)}`  (`Iut.logShell k p`, IUT III, Definition 1.1)

of a complete discretely valued field `k` of characteristic `0` and residue characteristic `p`
(e.g. a finite extension of `ℚ_p`, or a completion of a number field). With
`U = U^{(1)} = {‖u - 1‖ < 1}`, `D = {‖u - 1‖ ≤ ‖2p‖}` and `T = ker(log|_U)` (the `p`-power
roots of unity), for every translation-invariant measure `μ` on `k`:

`#T · μ(𝓘_k) = [U : D] · μ(𝒪_k)`   (`card_mul_measure_logShell`).

Proof: `log` maps `D` bijectively onto the ball `B = {‖y‖ ≤ ‖2p‖} = 2p 𝒪_k` (the remainder
`log(1 + a) - a` is a contraction with factor `‖p‖` there; surjectivity is
`PadicLogVolume.exists_padicLog_eq`), so `log⁻¹(B) = D · T` with `D ∩ T = 1`, and
`[log U : B] = [U : D T] = [U : D] / #T`; multiplication by `(2p)⁻¹` carries
`(log U, B)` to `(𝓘_k, 𝒪_k)`, and the Haar measure of an open subgroup is its index times the
measure of a smaller open subgroup (`measure_eq_relIndex_mul`).

For `k/ℚ_p` finite with residue field `𝔽_q`, `[k : ℚ_p] = d = e f`, `#μ_{p^∞}(k) = p^m`, one has
`[U : D] = q^{v(2p) - 1}` and `q^{v(2p)} = (p*)^d`, hence `μ(𝓘_k)/μ(𝒪_k) = p^{-(f+m)} (p*)^d`,
the volume encoded by `Iut.Reconstruction.logShellConst` (`logShellConst_mul`).

## Main results

* `Iut.Reconstruction.principalUnits`, `deepUnits`, `logHom`, `logKer`;
* `Iut.Reconstruction.comap_logHom_ball`, `disjoint_deepUnits_logKer`;
* `Iut.Reconstruction.index_deepUnits_eq`: `[U : D] = [log U : B] · #T`;
* `Iut.Reconstruction.measure_eq_relIndex_mul`: `μ(H) = [H : H'] μ(H')` for open subgroups;
* `Iut.Reconstruction.card_mul_measure_logShell`.
-/

namespace Iut.Reconstruction

open MeasureTheory PadicLogVolume
open scoped Valued Pointwise

noncomputable section

/-! ### Haar measure of open subgroups -/

section Measure

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-- **The Haar measure of an open subgroup is its index times the measure of a smaller open
subgroup.** -/
theorem measure_eq_relIndex_mul (μ : Measure G) [μ.IsAddLeftInvariant] {H' H : AddSubgroup G}
    (hle : H' ≤ H) (hH' : IsOpen (H' : Set G)) [(H'.addSubgroupOf H).FiniteIndex] :
    μ H = H'.relIndex H * μ H' := by
  have hH : IsOpen (H : Set G) := by
    refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    refine ⟨(fun y => -x + y) ⁻¹' (H' : Set G), fun y hy => ?_, ?_, ?_⟩
    · have : x + (-x + y) ∈ H := H.add_mem hx (hle hy)
      simpa using this
    · exact hH'.preimage (continuous_const.add continuous_id)
    · simp [H'.zero_mem]
  have hemb : MeasurableEmbedding (Subtype.val : H → G) :=
    MeasurableEmbedding.subtype_coe hH.measurableSet
  set ν : Measure H := μ.comap Subtype.val
  have hν : ∀ s : Set H, ν s = μ (Subtype.val '' s) := fun s => hemb.comap_apply μ s
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (measurable_const_add g) hs, hν, hν]
    have : (Subtype.val '' ((fun x : H => g + x) ⁻¹' s) : Set G) =
        (fun y : G => (g : G) + y) ⁻¹' (Subtype.val '' s) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage, Subtype.exists, exists_and_right,
        exists_eq_right]
      constructor
      · rintro ⟨hy, hgy⟩
        exact ⟨H.add_mem g.2 hy, hgy⟩
      · rintro ⟨hgy, hs'⟩
        have hy : y ∈ H := by
          have := H.add_mem (H.neg_mem g.2) hgy
          simpa using this
        exact ⟨hy, hs'⟩
    rw [this, measure_preimage_add]
  have hmeas : MeasurableSet ((H'.addSubgroupOf H : AddSubgroup H) : Set H) :=
    (hH'.preimage continuous_subtype_val).measurableSet
  have h := AddSubgroup.index_mul_measure (H'.addSubgroupOf H) hmeas ν
  rw [hν, hν, Set.image_univ, Subtype.range_coe] at h
  have h2 : (Subtype.val '' ((H'.addSubgroupOf H : AddSubgroup H) : Set H) : Set G) = H' := by
    ext y
    simp only [Set.mem_image, SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf, Subtype.exists,
      exists_and_right, exists_eq_right]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hle h, h⟩⟩
  rw [h2] at h
  rw [← h]
  rfl

end Measure

/-! ### Principal units and the logarithm -/

variable {k : Type*} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]

section Units

variable (k) in
/-- The principal units `U^{(1)} = {‖u - 1‖ < 1}`. -/
def principalUnits : Subgroup kˣ where
  carrier := {u | ‖(u : k) - 1‖ < 1}
  mul_mem' {x y} hx hy := by
    change ‖((x * y : kˣ) : k) - 1‖ < 1
    rw [Units.val_mul]
    exact norm_mul_sub_one_lt hx hy
  one_mem' := by simp
  inv_mem' {x} hx := by
    change ‖((x⁻¹ : kˣ) : k) - 1‖ < 1
    rw [Units.val_inv_eq_inv_val]
    exact norm_inv_sub_one_lt hx

theorem norm_sub_one_lt (u : principalUnits k) : ‖((u : kˣ) : k) - 1‖ < 1 := u.2

variable (k) in
/-- The deep principal units `D = {‖u - 1‖ ≤ ‖2p‖}`. -/
def deepUnits (p : ℕ) : Subgroup (principalUnits k) where
  carrier := {u | ‖((u : kˣ) : k) - 1‖ ≤ ‖2 * (p : k)‖}
  mul_mem' {x y} hx hy := by
    change ‖(((x * y : principalUnits k) : kˣ) : k) - 1‖ ≤ _
    have hx1 := norm_eq_one_of_norm_sub_one_lt (norm_sub_one_lt x)
    have : (((x * y : principalUnits k) : kˣ) : k) - 1 =
        ((x : kˣ) : k) * (((y : kˣ) : k) - 1) + (((x : kˣ) : k) - 1) := by
      simp only [Subgroup.coe_mul, Units.val_mul]; ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hx)
    rw [norm_mul, hx1, one_mul]
    exact hy
  one_mem' := by
    change ‖((1 : kˣ) : k) - 1‖ ≤ _
    simp only [Units.val_one, sub_self, norm_zero]
    positivity
  inv_mem' {x} hx := by
    change ‖(((x⁻¹ : principalUnits k) : kˣ) : k) - 1‖ ≤ _
    have hx1 := norm_eq_one_of_norm_sub_one_lt (norm_sub_one_lt x)
    have hx0 : ((x : kˣ) : k) ≠ 0 := (x : kˣ).ne_zero
    have : (((x⁻¹ : principalUnits k) : kˣ) : k) - 1 =
        -(((x : kˣ) : k) - 1) * ((x : kˣ) : k)⁻¹ := by
      simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
      field_simp
      ring
    rw [this, norm_mul, norm_neg, norm_inv, hx1, inv_one, mul_one]
    exact hx

variable (k) in
/-- The ball `B = {‖y‖ ≤ ‖2p‖}`, as a subgroup of `Multiplicative k`. -/
def logBall (p : ℕ) : Subgroup (Multiplicative k) where
  carrier := {y | ‖y.toAdd‖ ≤ ‖2 * (p : k)‖}
  mul_mem' {x y} hx hy := by
    change ‖(x * y).toAdd‖ ≤ _
    rw [toAdd_mul]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  one_mem' := by
    change ‖(1 : Multiplicative k).toAdd‖ ≤ _
    simp only [toAdd_one, norm_zero]
    positivity
  inv_mem' {x} hx := by
    change ‖(x⁻¹).toAdd‖ ≤ _
    rw [toAdd_inv, norm_neg]
    exact hx

variable [CompleteSpace k] [CharZero k] {p : ℕ} (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
include hp hpk

/-- The logarithm on the principal units, as a homomorphism to `(k, +)`. -/
def logHom : principalUnits k →* Multiplicative k where
  toFun u := Multiplicative.ofAdd (padicLog ((u : kˣ) : k))
  map_one' := by simp
  map_mul' x y := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [padicLog_mul hp hpk (norm_sub_one_lt x) (norm_sub_one_lt y), ofAdd_add]

theorem logHom_apply (u : principalUnits k) :
    (logHom hp hpk u).toAdd = padicLog ((u : kˣ) : k) := rfl

/-- `T = ker(log|_U)`. -/
def logKer : Subgroup (principalUnits k) := (logHom hp hpk).ker

/-- The logarithm maps `D` into `B`. -/
theorem norm_padicLog_le {a : k} (ha : ‖a‖ ≤ ‖2 * (p : k)‖) :
    ‖padicLog (1 + a)‖ ≤ ‖2 * (p : k)‖ := by
  have ha1 : ‖a‖ < 1 := ha.trans_lt (norm_two_mul_lt_one hpk)
  rw [padicLog_one_add hp hpk ha1]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha ?_)
  refine (norm_logRem_le hp hpk ha).trans ?_
  calc ‖(p : k)‖ * ‖a‖ ≤ 1 * ‖a‖ :=
        mul_le_mul_of_nonneg_right hpk.le (norm_nonneg _)
    _ = ‖a‖ := one_mul _
    _ ≤ _ := ha

/-- **The logarithm is injective on `D`.** -/
theorem eq_zero_of_padicLog_eq_zero {a : k} (ha : ‖a‖ ≤ ‖2 * (p : k)‖)
    (h : padicLog (1 + a) = 0) : a = 0 := by
  have ha1 : ‖a‖ < 1 := ha.trans_lt (norm_two_mul_lt_one hpk)
  rw [padicLog_one_add hp hpk ha1] at h
  have h1 : ‖a‖ ≤ ‖(p : k)‖ * ‖a‖ := by
    have := norm_logRem_le hp hpk ha
    rwa [show logRem a = -a by linear_combination h, norm_neg] at this
  by_contra hne
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 hne
  have := (mul_lt_iff_lt_one_left hpos).2 hpk
  linarith

/-- `D ∩ T = 1`. -/
theorem disjoint_deepUnits_logKer : Disjoint (deepUnits k p) (logKer hp hpk) := by
  rw [Subgroup.disjoint_def]
  intro u hD hT
  have h0 : padicLog (1 + (((u : kˣ) : k) - 1)) = 0 := by
    rw [add_sub_cancel]
    exact congrArg Multiplicative.toAdd hT
  have := eq_zero_of_padicLog_eq_zero hp hpk hD h0
  apply Subtype.ext
  apply Units.ext
  rw [sub_eq_zero] at this
  exact this

/-- **`log⁻¹(B) = D · T`.** -/
theorem comap_logHom_ball :
    (logBall k p).comap (logHom hp hpk) = deepUnits k p ⊔ logKer hp hpk := by
  apply le_antisymm
  · intro u hu
    obtain ⟨a, ha, hlog⟩ := exists_padicLog_eq hp hpk (y := padicLog ((u : kˣ) : k)) hu
    have ha1 : ‖a‖ < 1 := ha.trans_lt (norm_two_mul_lt_one hpk)
    have h1a : (1 + a) ≠ 0 := ne_zero_of_norm_sub_one_lt (by simpa using ha1)
    set w : principalUnits k := ⟨Units.mk0 (1 + a) h1a, by
      change ‖(1 + a) - 1‖ < 1
      simpa using ha1⟩
    have hw : w ∈ deepUnits k p := by
      change ‖(1 + a) - 1‖ ≤ _
      simpa using ha
    have hk : w⁻¹ * u ∈ logKer hp hpk := by
      change logHom hp hpk (w⁻¹ * u) = 1
      rw [map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, logHom_apply, logHom_apply, toAdd_one]
      change -padicLog (1 + a) + _ = 0
      rw [hlog, neg_add_cancel]
    have := Subgroup.mul_mem_sup hw hk
    rwa [mul_inv_cancel_left] at this
  · refine sup_le ?_ ?_
    · intro u hu
      change ‖(logHom hp hpk u).toAdd‖ ≤ _
      rw [logHom_apply]
      have := norm_padicLog_le hp hpk (a := ((u : kˣ) : k) - 1) hu
      rwa [add_sub_cancel] at this
    · intro u hu
      change logHom hp hpk u ∈ logBall k p
      rw [show logHom hp hpk u = 1 from hu]
      exact one_mem _

/-- `B ⊆ log U`. -/
theorem logBall_le_range : logBall k p ≤ (logHom hp hpk).range := by
  intro y hy
  obtain ⟨a, ha, hlog⟩ := exists_padicLog_eq hp hpk hy
  have ha1 : ‖a‖ < 1 := ha.trans_lt (norm_two_mul_lt_one hpk)
  have h1a : (1 + a) ≠ 0 := ne_zero_of_norm_sub_one_lt (by simpa using ha1)
  refine ⟨⟨Units.mk0 (1 + a) h1a, by change ‖(1 + a) - 1‖ < 1; simpa using ha1⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  exact hlog

/-- **The index formula** `[U : D] = [log U : B] · #T`. -/
theorem index_deepUnits_eq :
    (deepUnits k p).index =
      (logBall k p).relIndex (logHom hp hpk).range * Nat.card (logKer hp hpk) := by
  have h1 : ((logBall k p).subgroupOf (logHom hp hpk).range).comap
      (logHom hp hpk).rangeRestrict = deepUnits k p ⊔ logKer hp hpk := by
    rw [← comap_logHom_ball hp hpk]
    ext u
    simp [Subgroup.mem_subgroupOf]
  have h2 : (deepUnits k p ⊔ logKer hp hpk).index =
      (logBall k p).relIndex (logHom hp hpk).range := by
    rw [← h1, Subgroup.index_comap_of_surjective _ (logHom hp hpk).rangeRestrict_surjective]
    rfl
  have h3 : (deepUnits k p).relIndex (deepUnits k p ⊔ logKer hp hpk) =
      Nat.card (logKer hp hpk) := by
    rw [Subgroup.relIndex_sup_left, Subgroup.relIndex,
      (Subgroup.subgroupOf_eq_bot).2 (disjoint_deepUnits_logKer hp hpk),
      Subgroup.index_bot]
  rw [← Subgroup.relIndex_mul_index (le_sup_left : deepUnits k p ≤ _), h3, h2, mul_comm]

/-! ### The volume of the log-shell -/

/-- `log U` as an additive subgroup of `k`. -/
def logRange : AddSubgroup k := Subgroup.toAddSubgroup' (logHom hp hpk).range

omit hp hpk in
variable (k) in
/-- The ring of integers `𝒪_k = {‖y‖ ≤ 1}`, as an additive subgroup. -/
def integersSub : AddSubgroup k where
  carrier := Metric.closedBall 0 1
  add_mem' {x y} hx hy := by
    simp only [Metric.mem_closedBall, dist_zero_right] at hx hy ⊢
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  zero_mem' := by simp
  neg_mem' {x} hx := by simpa using hx

omit hp hpk in
variable (k p) in
/-- Multiplication by `(2p)⁻¹`. -/
def scaleHom : k →+ k := AddMonoidHom.mulLeft (2 * (p : k))⁻¹

omit hpk [CompleteSpace k] in
theorem two_mul_p_ne_zero : (2 * (p : k)) ≠ 0 := by
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  exact mul_ne_zero h2 (Nat.cast_ne_zero.2 hp.ne_zero)

omit hpk [CompleteSpace k] in
theorem scaleHom_injective : Function.Injective (scaleHom k p) :=
  mul_right_injective₀ (inv_ne_zero (two_mul_p_ne_zero hp))

/-- The log-shell `𝓘_k = (2p)⁻¹ log U` as an additive subgroup. -/
def logShellSub : AddSubgroup k := (logRange hp hpk).map (scaleHom k p)

theorem coe_logShellSub : (logShellSub hp hpk : Set k) = logShell k p := by
  ext y
  simp only [logShellSub, logRange, AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe,
    Subgroup.mem_toAddSubgroup', MonoidHom.mem_range, mem_logShell, scaleHom,
    AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨x, ⟨u, hu⟩, rfl⟩
    refine ⟨((u : kˣ) : k), u.2, ?_⟩
    rw [← logHom_apply hp hpk, hu]
    rfl
  · rintro ⟨u, hu, rfl⟩
    have hu0 : u ≠ 0 := ne_zero_of_norm_sub_one_lt hu
    exact ⟨padicLog u, ⟨⟨Units.mk0 u hu0, hu⟩, rfl⟩, rfl⟩

omit hpk [CompleteSpace k] in
theorem map_logBall :
    (Subgroup.toAddSubgroup' (logBall k p)).map (scaleHom k p) = integersSub k := by
  ext y
  simp only [AddSubgroup.mem_map, Subgroup.mem_toAddSubgroup', scaleHom,
    AddMonoidHom.coe_mulLeft]
  change (∃ x, ‖x‖ ≤ ‖2 * (p : k)‖ ∧ (2 * (p : k))⁻¹ * x = y) ↔ y ∈ Metric.closedBall 0 1
  rw [Metric.mem_closedBall, dist_zero_right]
  have h0 := two_mul_p_ne_zero hp (k := k)
  have hn : 0 < ‖2 * (p : k)‖ := norm_pos_iff.2 h0
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hn, mul_one]
    exact hx
  · intro hy
    refine ⟨2 * (p : k) * y, ?_, by rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]⟩
    rw [norm_mul]
    calc ‖2 * (p : k)‖ * ‖y‖ ≤ ‖2 * (p : k)‖ * 1 := mul_le_mul_of_nonneg_left hy hn.le
      _ = _ := mul_one _

theorem relIndex_integers_logShell :
    (integersSub k).relIndex (logShellSub hp hpk) =
      (logBall k p).relIndex (logHom hp hpk).range := by
  rw [← map_logBall hp, logShellSub]
  exact (AddSubgroup.relIndex_map_map_of_injective _ _ (scaleHom_injective hp)).trans rfl

theorem integersSub_le : integersSub k ≤ logShellSub hp hpk := by
  intro y hy
  rw [← SetLike.mem_coe, coe_logShellSub]
  exact closedBall_subset_logShell hp hpk hy

omit hp hpk [CompleteSpace k] [CharZero k] in
theorem isOpen_integersSub : IsOpen (integersSub k : Set k) :=
  IsUltrametricDist.isOpen_closedBall _ one_ne_zero

variable [ProperSpace k]

theorem finiteIndex_integers_logShell :
    ((integersSub k).addSubgroupOf (logShellSub hp hpk)).FiniteIndex := by
  have hopen : IsOpen (logShellSub hp hpk : Set k) :=
    AddSubgroup.isOpen_mono (integersSub_le hp hpk) (isOpen_integersSub (k := k))
  have hcl : IsClosed (logShellSub hp hpk : Set k) := AddSubgroup.isClosed_of_isOpen _ hopen
  have hcpt : IsCompact (logShellSub hp hpk : Set k) := by
    refine Metric.isCompact_of_isClosed_isBounded hcl ?_
    rw [coe_logShellSub]
    exact logShell_isBounded hp hpk
  haveI : CompactSpace (logShellSub hp hpk) := isCompact_iff_compactSpace.1 hcpt
  haveI := AddSubgroup.quotient_finite_of_isOpen
    ((integersSub k).addSubgroupOf (logShellSub hp hpk))
    ((isOpen_integersSub (k := k)).preimage continuous_subtype_val)
  exact AddSubgroup.finiteIndex_of_finite_quotient

variable [MeasurableSpace k] [BorelSpace k]

/-- **The Haar volume of the log-shell** ([AbsTopIII], Prop. 5.7 (i) (c), 5.8 (iii)):
`#T · μ(𝓘_k) = [U : D] · μ(𝒪_k)` for every translation-invariant measure `μ`, where `T` is the
group of `p`-power roots of unity of `k` (the kernel of `log` on `U = U^{(1)}`) and
`D = {‖u - 1‖ ≤ ‖2p‖}`. -/
theorem card_mul_measure_logShell (μ : Measure k) [μ.IsAddLeftInvariant] :
    (Nat.card (logKer hp hpk) : ENNReal) * μ (logShell k p) =
      (deepUnits k p).index * μ (Metric.closedBall 0 1) := by
  haveI := finiteIndex_integers_logShell hp hpk
  have h := measure_eq_relIndex_mul μ (integersSub_le hp hpk) (isOpen_integersSub (k := k))
  rw [coe_logShellSub] at h
  rw [h, relIndex_integers_logShell, index_deepUnits_eq hp hpk, ← mul_assoc]
  push_cast
  rw [mul_comm (Nat.card _ : ENNReal)]
  rfl

end Units

end

end Iut.Reconstruction
