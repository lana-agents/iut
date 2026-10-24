/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Uniformization.KoebeMap
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Holomorphic automorphisms of the unit disc: stabilisers, half-turns, midpoints

Input for [AbsTopIII] Proposition 2.2 (i) (`Disc/Normalizer.lean`). On the open unit disc
`Dk = ball 0 1 ⊆ ℂ`:

* `HolD g`: a self-map of `Dk` is holomorphic; `holAut`: the group of holomorphic automorphisms
  (homeomorphisms `g` with `g`, `g⁻¹` holomorphic);
* `mobH t` (`z ↦ (z + t) / (1 + t̄ z)`, oka's `mob`), `rotH u` (`z ↦ u z`, `‖u‖ = 1`) and
  `conjH` (complex conjugation, which normalises `holAut`: `conjH_conj_mem`);
* `eq_mul_of_mem_holAut`: **an automorphism fixing `0` is a rotation** (Schwarz lemma, with its
  equality case);
* `half x = mob x ∘ (-·) ∘ mob (-x)`, the **half-turn** about `x`; `eq_half`: the half-turns are
  the only involutions `≠ 1` of `holAut`, and `half x` is the only one fixing `x`;
* `mid x y`: the **midpoint**, the unique `m` with `half m x = y` (`half_mid`, `eq_mid`).
-/

namespace Iut

namespace AutHol

namespace Disc

open Complex Metric Set Filter Topology Uniformization

open scoped ComplexConjugate

/-- The open unit disc, as a subset of `ℂ`. -/
abbrev Dk : Set ℂ := ball (0 : ℂ) 1

theorem mem_Dk {z : ℂ} : z ∈ Dk ↔ ‖z‖ < 1 := mem_ball_zero_iff

theorem neg_mem_Dk {t : ℂ} (ht : t ∈ Dk) : -t ∈ Dk := by
  rw [mem_Dk, norm_neg]; exact mem_Dk.1 ht

theorem conj_mem_Dk {t : ℂ} (ht : t ∈ Dk) : conj t ∈ Dk := by
  rw [mem_Dk, Complex.norm_conj]; exact mem_Dk.1 ht

theorem zero_mem_Dk : (0 : ℂ) ∈ Dk := mem_Dk.2 (by simp)

/-- The centre of the disc. -/
def d0 : Dk := ⟨0, zero_mem_Dk⟩

@[simp] theorem coe_d0 : ((d0 : Dk) : ℂ) = 0 := rfl

theorem isOpen_Dk : IsOpen Dk := isOpen_ball

/-! ### Holomorphic self-maps -/

/-- `g : Dk → Dk` is **holomorphic**: it is given by a function holomorphic on `Dk`. -/
def HolD (g : Dk → Dk) : Prop :=
  ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Dk ∧ ∀ z : Dk, (g z : ℂ) = F z

theorem HolD.id : HolD _root_.id := ⟨_root_.id, differentiableOn_id, fun _ => rfl⟩

theorem HolD.comp {g h : Dk → Dk} (hg : HolD g) (hh : HolD h) : HolD (g ∘ h) := by
  obtain ⟨F, hF, hFg⟩ := hg
  obtain ⟨G, hG, hGh⟩ := hh
  refine ⟨F ∘ G, hF.comp hG ?_, fun z => ?_⟩
  · intro z hz
    have := hGh ⟨z, hz⟩
    change G z ∈ Dk
    rw [← this]
    exact (h ⟨z, hz⟩).2
  · simp only [Function.comp_apply, hFg, hGh]

/-- **The group of holomorphic automorphisms of the disc.** -/
def holAut : Subgroup (Dk ≃ₜ Dk) where
  carrier := {g | HolD g ∧ HolD g.symm}
  mul_mem' := fun hg hh => ⟨hg.1.comp hh.1, hh.2.comp hg.2⟩
  one_mem' := ⟨HolD.id, HolD.id⟩
  inv_mem' := fun hg => ⟨hg.2, hg.1⟩

theorem mem_holAut {g : Dk ≃ₜ Dk} : g ∈ holAut ↔ HolD g ∧ HolD g.symm := Iff.rfl

/-! ### Möbius maps, rotations, conjugation -/

/-- The disc automorphism `z ↦ (z + t) / (1 + t̄ z)`. -/
noncomputable def mobH (t : Dk) : Dk ≃ₜ Dk :=
  homeomorphOfInvOn (mob t) (mob (-t)) (fun _ hz => mob_mem_ball t.2 hz)
    (fun _ hz => mob_mem_ball (neg_mem_Dk t.2) hz) (fun _ hz => mob_neg_mob t.2 hz)
    (fun _ hz => mob_mob_neg t.2 hz) (continuousOn_mob t.2) (continuousOn_mob (neg_mem_Dk t.2))

@[simp] theorem coe_mobH (t z : Dk) : (mobH t z : ℂ) = mob t z := rfl

@[simp] theorem coe_mobH_symm (t z : Dk) : ((mobH t).symm z : ℂ) = mob (-t) z := rfl

theorem mobH_mem (t : Dk) : mobH t ∈ holAut :=
  ⟨⟨mob t, differentiableOn_mob t.2, fun _ => rfl⟩,
    ⟨mob (-t), differentiableOn_mob (neg_mem_Dk t.2), fun _ => rfl⟩⟩

theorem mobH_d0 (t : Dk) : mobH t d0 = t := Subtype.ext (by simp)

theorem mob_neg_self' (t : ℂ) : mob (-t) t = 0 := by
  have := mob_neg_self (-t)
  rwa [neg_neg] at this

theorem mobH_symm_self (t : Dk) : (mobH t).symm t = d0 := Subtype.ext (by simp [mob_neg_self'])

theorem mul_mem_Dk {u z : ℂ} (hu : ‖u‖ = 1) (hz : z ∈ Dk) : u * z ∈ Dk := by
  rw [mem_Dk, norm_mul, hu, one_mul]; exact mem_Dk.1 hz

/-- The rotation `z ↦ u z`, `‖u‖ = 1`. -/
noncomputable def rotH (u : ℂ) (hu : ‖u‖ = 1) : Dk ≃ₜ Dk where
  toFun z := ⟨u * z, mul_mem_Dk hu z.2⟩
  invFun z := ⟨u⁻¹ * z, mul_mem_Dk (by rw [norm_inv, hu, inv_one]) z.2⟩
  left_inv z := by
    have : u ≠ 0 := by rintro rfl; simp at hu
    ext1; simp [this]
  right_inv z := by
    have : u ≠ 0 := by rintro rfl; simp at hu
    ext1; simp [this]
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

@[simp] theorem coe_rotH (u : ℂ) (hu : ‖u‖ = 1) (z : Dk) : (rotH u hu z : ℂ) = u * z := rfl

@[simp] theorem coe_rotH_symm (u : ℂ) (hu : ‖u‖ = 1) (z : Dk) :
    ((rotH u hu).symm z : ℂ) = u⁻¹ * z := rfl

theorem rotH_mem (u : ℂ) (hu : ‖u‖ = 1) : rotH u hu ∈ holAut :=
  ⟨⟨(u * ·), (differentiable_const _).mul differentiable_id |>.differentiableOn, fun _ => rfl⟩,
    ⟨(u⁻¹ * ·), (differentiable_const _).mul differentiable_id |>.differentiableOn, fun _ => rfl⟩⟩

/-- Complex conjugation on the disc. -/
noncomputable def conjH : Dk ≃ₜ Dk where
  toFun z := ⟨conj (z : ℂ), conj_mem_Dk z.2⟩
  invFun z := ⟨conj (z : ℂ), conj_mem_Dk z.2⟩
  left_inv z := by ext1; simp
  right_inv z := by ext1; simp
  continuous_toFun := (continuous_conj.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_conj.comp continuous_subtype_val).subtype_mk _

@[simp] theorem coe_conjH (z : Dk) : (conjH z : ℂ) = conj (z : ℂ) := rfl

@[simp] theorem coe_conjH_symm (z : Dk) : (conjH.symm z : ℂ) = conj (z : ℂ) := rfl

theorem HolD.conj_conj {g : Dk → Dk} (hg : HolD g) : HolD (conjH ∘ g ∘ conjH) := by
  obtain ⟨F, hF, hFg⟩ := hg
  refine ⟨conj ∘ F ∘ conj, fun z hz => ?_, fun z => ?_⟩
  · have h1 : DifferentiableAt ℂ F (conj z) :=
      hF.differentiableAt (isOpen_Dk.mem_nhds (conj_mem_Dk hz))
    have h2 := h1.conj_conj
    simp only [Complex.conj_conj] at h2
    exact h2.differentiableWithinAt
  · simp [hFg]

theorem conjH_conj_mem {g : Dk ≃ₜ Dk} (hg : g ∈ holAut) :
    (conjH.symm.trans g).trans conjH ∈ holAut :=
  ⟨hg.1.conj_conj, hg.2.conj_conj⟩

/-! ### The stabiliser of the centre: the Schwarz lemma -/

theorem HolD.mapsTo {g : Dk → Dk} {F : ℂ → ℂ} (hFg : ∀ z : Dk, (g z : ℂ) = F z) :
    MapsTo F Dk Dk := fun z hz => by
  have := hFg ⟨z, hz⟩
  simp only at this
  rw [← this]
  exact (g _).2

/-- **An automorphism of the disc fixing `0` is a rotation** (Schwarz lemma). -/
theorem eq_mul_of_mem_holAut {g : Dk ≃ₜ Dk} (hg : g ∈ holAut) (h0 : g d0 = d0) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ z : Dk, (g z : ℂ) = u * z := by
  obtain ⟨⟨F, hF, hFg⟩, ⟨G, hG, hGg⟩⟩ := hg
  have hF0 : F 0 = 0 := by
    have := hFg d0
    rw [h0] at this
    exact this.symm
  have hG0 : G 0 = 0 := by
    have := hGg d0
    have h0' : g.symm d0 = d0 := by rw [Homeomorph.symm_apply_eq, h0]
    rw [h0'] at this
    exact this.symm
  have hFm : MapsTo F (ball 0 1) (closedBall (F 0) 1) := fun z hz => by
    rw [hF0]; exact ball_subset_closedBall (HolD.mapsTo hFg hz)
  have hGm : MapsTo G (ball 0 1) (closedBall (G 0) 1) := fun z hz => by
    rw [hG0]; exact ball_subset_closedBall (HolD.mapsTo hGg hz)
  have hdF := Complex.norm_deriv_le_one_of_mapsTo_ball hF hFm one_pos
  have hdG := Complex.norm_deriv_le_one_of_mapsTo_ball hG hGm one_pos
  -- `G ∘ F = id` near `0`
  have hGF : ∀ᶠ z in 𝓝 (0 : ℂ), (G ∘ F) z = z := by
    filter_upwards [isOpen_Dk.mem_nhds zero_mem_Dk] with z hz
    have h1 := hFg ⟨z, hz⟩
    have h2 := hGg (g ⟨z, hz⟩)
    simp only [Homeomorph.symm_apply_apply] at h2
    simp only [Function.comp_apply, ← h1, ← h2]
  have hFd : DifferentiableAt ℂ F 0 := hF.differentiableAt (isOpen_Dk.mem_nhds zero_mem_Dk)
  have hGd : DifferentiableAt ℂ G (F 0) := by
    rw [hF0]; exact hG.differentiableAt (isOpen_Dk.mem_nhds zero_mem_Dk)
  have hchain : HasDerivAt (G ∘ F) (deriv G (F 0) * deriv F 0) 0 :=
    hGd.hasDerivAt.comp 0 hFd.hasDerivAt
  have hid : HasDerivAt (G ∘ F) 1 0 :=
    (hasDerivAt_id (0 : ℂ)).congr_of_eventuallyEq hGF
  have hprod : deriv G 0 * deriv F 0 = 1 := by
    rw [hF0] at hchain
    exact hchain.unique hid
  have hnF : ‖deriv F 0‖ = 1 := by
    have h := congrArg norm hprod
    rw [norm_mul, norm_one] at h
    have hnn := norm_nonneg (deriv F 0)
    have hnn' := norm_nonneg (deriv G 0)
    nlinarith
  have hds : ‖dslope F 0 0‖ = 1 / 1 := by rw [dslope_same, hnF, div_one]
  have hEq := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hF hFm zero_mem_Dk hds
  refine ⟨deriv F 0, hnF, fun z => ?_⟩
  rw [hFg z, hEq z.2]
  simp only [hF0, sub_zero, smul_eq_mul, dslope_same, zero_add]
  ring

/-! ### Half-turns -/

/-- The **half-turn** about `x`: `mob x ∘ (-·) ∘ mob (-x)`. -/
noncomputable def half (x : Dk) : Dk ≃ₜ Dk :=
  ((mobH x).symm.trans (rotH (-1) (by simp))).trans (mobH x)

theorem coe_half (x z : Dk) : (half x z : ℂ) = mob x (-mob (-x) z) := by
  simp [half]

theorem half_mem (x : Dk) : half x ∈ holAut :=
  holAut.mul_mem (mobH_mem x) (holAut.mul_mem (rotH_mem _ _) (holAut.inv_mem (mobH_mem x)))

theorem half_self (x : Dk) : half x x = x := by
  apply Subtype.ext
  rw [coe_half, mob_neg_self', neg_zero, mob_zero]

theorem rotH_neg_one_rotH (h : ‖(-1 : ℂ)‖ = 1) (z : Dk) : rotH (-1) h (rotH (-1) h z) = z :=
  Subtype.ext (by simp)

theorem half_half (x z : Dk) : half x (half x z) = z := by
  simp only [half, Homeomorph.trans_apply, Homeomorph.symm_apply_apply, rotH_neg_one_rotH,
    Homeomorph.apply_symm_apply]

theorem half_ne_one (x : Dk) : half x ≠ 1 := by
  intro h
  -- `half x (mob x (1/2)) = mob x (-1/2)`
  have hhalf : (1 / 2 : ℂ) ∈ Dk := mem_Dk.2 (by norm_num)
  let z : Dk := mobH x ⟨1 / 2, hhalf⟩
  have h1 := congrArg (fun g : Dk ≃ₜ Dk => ((mobH x).symm (g z) : ℂ)) h
  simp only [half, Homeomorph.trans_apply, Homeomorph.symm_apply_apply, z] at h1
  change ((rotH (-1) _ ⟨1 / 2, hhalf⟩ : Dk) : ℂ) = ((mobH x).symm (mobH x ⟨1 / 2, hhalf⟩) : ℂ)
    at h1
  rw [Homeomorph.symm_apply_apply, coe_rotH] at h1
  norm_num at h1

/-- Conjugating a rotation-fixing element: an involution `≠ 1` of `holAut` fixing `0` is
`z ↦ -z`. -/
theorem eq_neg_of_inv {g : Dk ≃ₜ Dk} (hg : g ∈ holAut) (h0 : g d0 = d0)
    (h2 : ∀ z, g (g z) = z) (h1 : g ≠ 1) : ∀ z : Dk, (g z : ℂ) = -z := by
  obtain ⟨u, hu, hgu⟩ := eq_mul_of_mem_holAut hg h0
  have hhalf : (1 / 2 : ℂ) ∈ Dk := mem_Dk.2 (by norm_num)
  have hu2 : u * u = 1 := by
    have := h2 ⟨1 / 2, hhalf⟩
    have h' := congrArg Subtype.val this
    rw [hgu, hgu] at h'
    simp only at h'
    have : u * (u * (1 / 2)) = 1 * (1 / 2) := by rw [h', one_mul]
    rw [← mul_assoc] at this
    exact mul_right_cancel₀ (by norm_num) this
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply h1
    ext z
    rw [hgu, one_mul]
    rfl
  have hum : u = -1 := by
    have : (u - 1) * (u + 1) = 0 := by ring_nf; rw [sq, hu2]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hu1
    · exact eq_neg_of_add_eq_zero_left h
  intro z
  rw [hgu, hum, neg_one_mul]

/-- **Uniqueness of half-turns**: an involution `≠ 1` of `holAut` fixing `x` is `half x`. -/
theorem eq_half {g : Dk ≃ₜ Dk} (hg : g ∈ holAut) {x : Dk} (hx : g x = x)
    (h2 : ∀ z, g (g z) = z) (h1 : g ≠ 1) : g = half x := by
  set g' := ((mobH x).trans g).trans (mobH x).symm with hg'
  have hg'm : g' ∈ holAut :=
    holAut.mul_mem (holAut.inv_mem (mobH_mem x)) (holAut.mul_mem hg (mobH_mem x))
  have h0 : g' d0 = d0 := by
    simp only [hg', Homeomorph.trans_apply, mobH_d0, hx, mobH_symm_self]
  have h2' : ∀ z, g' (g' z) = z := by
    intro z
    simp [hg', h2]
  have h1' : g' ≠ 1 := by
    intro h
    apply h1
    ext z
    have := congrArg (fun k : Dk ≃ₜ Dk => mobH x (k ((mobH x).symm z))) h
    simpa [hg'] using congrArg Subtype.val this
  have key := eq_neg_of_inv hg'm h0 h2' h1'
  ext z
  have := key ((mobH x).symm z)
  simp only [hg', Homeomorph.trans_apply, Homeomorph.apply_symm_apply] at this
  rw [coe_half, ← coe_mobH_symm, ← this, ← coe_mobH, Homeomorph.apply_symm_apply]

/-- Conjugates of half-turns by automorphisms. -/
theorem conj_half {k : Dk ≃ₜ Dk} (hk : k ∈ holAut) (x : Dk) :
    (k.symm.trans (half x)).trans k = half (k x) := by
  refine eq_half (holAut.mul_mem hk (holAut.mul_mem (half_mem x) (holAut.inv_mem hk))) ?_ ?_ ?_
  · simp [half_self]
  · intro z; simp [half_half]
  · intro h
    apply half_ne_one x
    ext z
    have := congrArg (fun g : Dk ≃ₜ Dk => k.symm (g (k z))) h
    simpa using congrArg Subtype.val this

/-! ### Midpoints -/

/-- The value `half m 0 = 2 m / (1 + |m|²)`. -/
theorem coe_half_d0 (m : Dk) : (half m d0 : ℂ) = 2 * m / (1 + conj (m : ℂ) * m) := by
  rw [coe_half, coe_d0, mob, mob]
  simp only [zero_add, mul_zero, add_zero, neg_neg, div_one]
  ring

/-- The midpoint of `0` and `w`: `w / (1 + √(1 - |w|²))`. -/
noncomputable def mid0 (w : ℂ) : ℂ := w / (1 + Real.sqrt (1 - ‖w‖ ^ 2))

theorem sqrt_pos_of_mem {w : ℂ} (hw : w ∈ Dk) : 0 < Real.sqrt (1 - ‖w‖ ^ 2) := by
  apply Real.sqrt_pos.2
  have := mem_Dk.1 hw
  nlinarith [norm_nonneg w]

theorem norm_mid0_le {w : ℂ} (hw : w ∈ Dk) : ‖mid0 w‖ ≤ ‖w‖ := by
  have hs := sqrt_pos_of_mem hw
  rw [mid0, norm_div]
  have : ‖(1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ))‖ = 1 + Real.sqrt (1 - ‖w‖ ^ 2) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_of_nonneg (by linarith)]
  rw [this, div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg w]

theorem mid0_mem {w : ℂ} (hw : w ∈ Dk) : mid0 w ∈ Dk :=
  mem_Dk.2 ((norm_mid0_le hw).trans_lt (mem_Dk.1 hw))

/-- `half (mid0 w) 0 = w`. -/
theorem half_mid0 {w : ℂ} (hw : w ∈ Dk) : 2 * mid0 w / (1 + conj (mid0 w) * mid0 w) = w := by
  set s := Real.sqrt (1 - ‖w‖ ^ 2) with hs_def
  have hs := sqrt_pos_of_mem hw
  have hss : s ^ 2 = 1 - ‖w‖ ^ 2 := Real.sq_sqrt (by have := mem_Dk.1 hw; nlinarith [norm_nonneg w])
  have hcw : conj w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 : (1 + (s : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add]; exact_mod_cast (by linarith : (1 + s) ≠ 0)
  have hden : 1 + conj (mid0 w) * mid0 w = 2 / (1 + s) := by
    rw [mid0, map_div₀, map_add, map_one, Complex.conj_ofReal, div_mul_div_comm, hcw]
    rw [← hs_def]
    field_simp
    have : ((‖w‖ ^ 2 : ℝ) : ℂ) = 1 - (s : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow s, hss]; push_cast; ring
    rw [this]; ring
  rw [hden, mid0, ← hs_def]
  field_simp

/-- The real function `r ↦ 2 r / (1 + r²)` is injective on `[0, 1)`. -/
theorem two_mul_div_inj {r s : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (_hs : 0 ≤ s) (hs1 : s < 1)
    (h : 2 * r / (1 + r ^ 2) = 2 * s / (1 + s ^ 2)) : r = s := by
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have : (r - s) * (1 - r * s) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · nlinarith

/-- Injectivity of `m ↦ half m 0`. -/
theorem eq_of_half_d0 {m n : Dk} (h : half m d0 = half n d0) : m = n := by
  have h' := congrArg Subtype.val h
  rw [coe_half_d0, coe_half_d0] at h'
  have hcm : conj (m : ℂ) * m = ((‖(m : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcn : conj (n : ℂ) * n = ((‖(n : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hcm, hcn] at h'
  have hm1 : (1 + ((‖(m : ℂ)‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add]; exact_mod_cast (by positivity)
  have hn1 : (1 + ((‖(n : ℂ)‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add]; exact_mod_cast (by positivity)
  -- norms agree
  have hnorm : 2 * ‖(m : ℂ)‖ / (1 + ‖(m : ℂ)‖ ^ 2) = 2 * ‖(n : ℂ)‖ / (1 + ‖(n : ℂ)‖ ^ 2) := by
    have := congrArg norm h'
    rw [norm_div, norm_div, norm_mul, norm_mul] at this
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_add, Complex.norm_of_nonneg
      (by positivity), Complex.norm_of_nonneg (by positivity)] at this
    simpa using this
  have hmn := two_mul_div_inj (norm_nonneg _) (mem_Dk.1 m.2) (norm_nonneg _) (mem_Dk.1 n.2) hnorm
  apply Subtype.ext
  rw [hmn] at h'
  rw [div_left_inj' hn1] at h'
  exact mul_left_cancel₀ two_ne_zero h'

/-- The point with `half m 0 = w`. -/
theorem half_d0_mid0 (w : Dk) : half ⟨mid0 w, mid0_mem w.2⟩ d0 = w := by
  apply Subtype.ext
  rw [coe_half_d0]
  exact half_mid0 w.2

/-- **The midpoint** of `x` and `y`: the unique `m` with `half m x = y`. -/
noncomputable def mid (x y : Dk) : Dk :=
  mobH x ⟨mid0 ((mobH x).symm y), mid0_mem ((mobH x).symm y).2⟩

theorem half_conj_mobH (x m : Dk) :
    half ((mobH x).symm m) = ((mobH x).trans (half m)).trans (mobH x).symm := by
  have := conj_half (k := (mobH x).symm) (holAut.inv_mem (mobH_mem x)) m
  rw [← this]
  rfl

theorem half_mid (x y : Dk) : half (mid x y) x = y := by
  have h := half_conj_mobH x (mid x y)
  have e : (mobH x).symm (mid x y) = ⟨mid0 ((mobH x).symm y), mid0_mem ((mobH x).symm y).2⟩ := by
    simp [mid]
  rw [e] at h
  have h2 := congrArg (fun g : Dk ≃ₜ Dk => g d0) h
  simp only [half_d0_mid0, Homeomorph.trans_apply, mobH_d0] at h2
  have := congrArg (mobH x) h2
  simpa using this.symm

theorem eq_mid {x y m : Dk} (h : half m x = y) : m = mid x y := by
  have h1 := half_conj_mobH x m
  have h2 := half_conj_mobH x (mid x y)
  have e1 := congrArg (fun g : Dk ≃ₜ Dk => g d0) h1
  have e2 := congrArg (fun g : Dk ≃ₜ Dk => g d0) h2
  simp only [Homeomorph.trans_apply, mobH_d0] at e1 e2
  rw [h] at e1
  rw [half_mid] at e2
  have := eq_of_half_d0 (e1.trans e2.symm)
  simpa using congrArg (mobH x) this

end Disc

end AutHol

end Iut
