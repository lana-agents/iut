/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Disc.Formulas
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The normaliser of `Aut^hol(𝔻)` in `Aut(𝔻^top)` ([AbsTopIII] Proposition 2.2 (i))

**Theorem** (`rc_of_normalizes`). A homeomorphism `α` of the open unit disc such that conjugation by
`α` carries the group `holAut` of holomorphic automorphisms onto itself is **RC-holomorphic**: it
is `g` or `g ∘ conj` for some `g ∈ holAut`.

[AbsTopIII] Proposition 2.2 deduces this from the commensurable terminality of `Aut^hol` in
`Aut(X^top)`, via Cartan's theorem (continuous automorphisms of the real Lie group
`SL₂(ℝ)/{±1}` are analytic) and the structure of `GL₂(ℂ)`. The proof here is elementary
hyperbolic geometry; it only uses that `α` normalises `holAut`, which is what Corollary 2.3 (i)
needs:

1. `α` maps the half-turn about `x` (the unique involution `≠ 1` of `holAut` fixing `x`) to the
   half-turn about `α x`, hence preserves midpoints (`half_map`, `mid_map`);
2. after composing with elements of `holAut` (and possibly `conj`), `α 0 = 0`, `α (i z) = i α z`,
   and `α` maps rotations to rotations, so `|α z|` depends only on `|z|`;
3. since `α` preserves midpoints and is continuous, it maps the segment `[0, r]` into a ray
   (dyadic subdivision); after a rotation, `α` maps `[0, 1)` into `[0, 1)`;
4. writing `φ (cosh d(0, z)) = cosh d(0, α z)`, the hyperbolic Pythagoras theorem gives
   `φ (s t) = φ s φ t` and the doubling formula gives `φ (2 t² - 1) = 2 φ(t)² - 1`; these force
   `φ (2) = 2` and then `φ = id` (`fe_eq_id`); so `α` preserves `|z|`, fixes the real and the
   imaginary diameters, commutes with the half-turns about real points, and is the identity
   since every point is the image of an imaginary point under such a half-turn.
-/

namespace Iut

namespace AutHol

namespace Disc

open Complex Metric Set Filter Topology Uniformization

open scoped ComplexConjugate

/-! ### A functional equation -/

/-- **`φ (s t) = φ s φ t` and `φ (2 t² - 1) = 2 φ(t)² - 1` on `[1, ∞)`, with `φ` continuous and
`> 1` on `(1, ∞)`, force `φ = id`.** -/
theorem fe_eq_id {φ : ℝ → ℝ} (hc : ContinuousOn φ (Ici 1))
    (hmul : ∀ s t, 1 ≤ s → 1 ≤ t → φ (s * t) = φ s * φ t)
    (hdbl : ∀ t, 1 ≤ t → φ (2 * t ^ 2 - 1) = 2 * φ t ^ 2 - 1)
    (hgt : ∀ t, 1 < t → 1 < φ t) : ∀ t, 1 ≤ t → φ t = t := by
  have h1 : φ 1 = 1 := by
    have e1 := hmul 1 1 le_rfl le_rfl
    have e2 := hdbl 1 le_rfl
    norm_num at e1 e2
    nlinarith
  have hpos : ∀ t, 1 ≤ t → 0 < φ t := by
    intro t ht
    rcases ht.lt_or_eq with ht | rfl
    · linarith [hgt t ht]
    · rw [h1]; norm_num
  have hlin : ∀ t, 1 ≤ t → φ (2 * t - 1) = 2 * φ t - 1 := by
    intro t ht
    have hr : 1 ≤ Real.sqrt t := by rw [Real.one_le_sqrt]; exact ht
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt (by linarith)
    have := hdbl (Real.sqrt t) hr
    rw [hsq] at this
    rw [this, sq, ← hmul _ _ hr hr, ← sq, hsq]
  have h2 : φ 2 = 2 := by
    have e3 : φ 3 = 2 * φ 2 - 1 := by have := hlin 2 (by norm_num); norm_num at this; exact this
    have e5 : φ 5 = 2 * φ 3 - 1 := by have := hlin 3 (by norm_num); norm_num at this; exact this
    have e9 : φ 9 = 2 * φ 5 - 1 := by have := hlin 5 (by norm_num); norm_num at this; exact this
    have e9' : φ 9 = φ 3 * φ 3 := by
      have := hmul 3 3 (by norm_num) (by norm_num); norm_num at this; exact this
    have hg := hgt 2 (by norm_num)
    have : (φ 2 - 1) * (φ 2 - 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hsqrt : ∀ t, 1 ≤ t → φ t = t → φ (Real.sqrt t) = Real.sqrt t := by
    intro t ht hφ
    have hr : 1 ≤ Real.sqrt t := by rw [Real.one_le_sqrt]; exact ht
    have := hmul _ _ hr hr
    rw [Real.mul_self_sqrt (by linarith), hφ] at this
    have hp := hpos _ hr
    rw [← Real.sqrt_mul_self hp.le, ← this]
  -- `φ (2 ^ x) = 2 ^ x` for `x ∈ [0, n]`
  have hpow : ∀ n : ℕ, φ ((2 : ℝ) ^ n) = 2 ^ n := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [pow_succ, hmul _ _ (one_le_pow₀ (by norm_num)) (by norm_num), ih, h2]
  have hrp : ∀ x : ℝ, 0 ≤ x → 1 ≤ (2 : ℝ) ^ x := fun x hx => Real.one_le_rpow (by norm_num) hx
  have key : ∀ n : ℕ, Icc (0 : ℝ) n ⊆ {x | φ ((2 : ℝ) ^ x) = 2 ^ x} := by
    intro n
    set S : Set ℝ := Icc (0 : ℝ) n ∩ (fun x => (2 : ℝ) ^ x) ⁻¹' (Ici 1 ∩ (fun y => φ y - y) ⁻¹' {0})
    have hF : IsClosed (Ici (1 : ℝ) ∩ (fun y => φ y - y) ⁻¹' {0}) :=
      (hc.sub continuousOn_id).preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
    have hS : IsClosed S :=
      isClosed_Icc.inter (hF.preimage (Real.continuous_const_rpow (by norm_num)))
    have hmemS : ∀ x, x ∈ S ↔ x ∈ Icc (0 : ℝ) n ∧ φ ((2 : ℝ) ^ x) = 2 ^ x := by
      intro x
      simp only [S, mem_inter_iff, mem_preimage, mem_Ici, mem_singleton_iff, sub_eq_zero]
      constructor
      · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨h, hrp x h.1, h'⟩
    have hsub := Icc_subset_of_mid hS (Nat.cast_nonneg n)
      ((hmemS 0).2 ⟨⟨le_rfl, Nat.cast_nonneg n⟩, by simpa using h1⟩)
      ((hmemS n).2 ⟨⟨Nat.cast_nonneg n, le_rfl⟩, by rw [Real.rpow_natCast]; exact hpow n⟩)
      (fun a ha b hb haI hbI => by
        rw [hmemS] at ha hb ⊢
        refine ⟨⟨by linarith [haI.1, hbI.1], by linarith [haI.2, hbI.2]⟩, ?_⟩
        have hab : (2 : ℝ) ^ ((a + b) / 2) = Real.sqrt ((2 : ℝ) ^ a * 2 ^ b) := by
          rw [← Real.rpow_add (by norm_num), Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
          ring_nf
        rw [hab]
        apply hsqrt _ (one_le_mul_of_one_le_of_one_le (hrp a haI.1) (hrp b hbI.1))
        rw [hmul _ _ (hrp a haI.1) (hrp b hbI.1), ha.2, hb.2])
    intro x hx
    exact ((hmemS x).1 (hsub hx)).2
  intro t ht
  set x := Real.logb 2 t
  have hx : 0 ≤ x := Real.logb_nonneg (by norm_num) ht
  have htx : (2 : ℝ) ^ x = t := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_ge x
  have := key n ⟨hx, hn⟩
  simp only [mem_setOf_eq, htx] at this
  exact this

/-! ### Normalisers -/

/-- Conjugation `g ↦ α ∘ g ∘ α⁻¹`. -/
noncomputable def cj (α g : Dk ≃ₜ Dk) : Dk ≃ₜ Dk := (α.symm.trans g).trans α

@[simp] theorem cj_apply (α g : Dk ≃ₜ Dk) (z : Dk) : cj α g z = α (g (α.symm z)) := rfl

/-- `α` **normalises** `holAut`. -/
def Normalizes (α : Dk ≃ₜ Dk) : Prop := ∀ g : Dk ≃ₜ Dk, g ∈ holAut ↔ cj α g ∈ holAut

theorem cj_cj_symm (α g : Dk ≃ₜ Dk) : cj α.symm (cj α g) = g := by ext z; simp

theorem normalizes_of_mem {k : Dk ≃ₜ Dk} (hk : k ∈ holAut) : Normalizes k := by
  intro g
  have hmem : ∀ k g : Dk ≃ₜ Dk, k ∈ holAut → g ∈ holAut → cj k g ∈ holAut := fun k g hk hg =>
    holAut.mul_mem hk (holAut.mul_mem hg (holAut.inv_mem hk))
  refine ⟨hmem k g hk, fun h => ?_⟩
  rw [← cj_cj_symm k g]
  exact hmem _ _ (holAut.inv_mem hk) h

theorem Normalizes.trans {α β : Dk ≃ₜ Dk} (hα : Normalizes α) (hβ : Normalizes β) :
    Normalizes (α.trans β) := by
  intro g
  have : cj (α.trans β) g = cj β (cj α g) := by ext z; rfl
  rw [this, hα, hβ]

theorem conjH_symm_symm (z : Dk) : conjH.symm (conjH.symm z) = z := Subtype.ext (by simp)

theorem conjH_d0 : conjH d0 = d0 := Subtype.ext (by simp)

theorem normalizes_conjH : Normalizes conjH := by
  intro g
  refine ⟨conjH_conj_mem, fun h => ?_⟩
  have e : g = cj conjH (cj conjH g) := by ext z; simp [conjH_symm_symm]
  rw [e]
  exact conjH_conj_mem h

variable {α : Dk ≃ₜ Dk}

/-- **Half-turns go to half-turns.** -/
theorem half_map (hα : Normalizes α) (x : Dk) : cj α (half x) = half (α x) := by
  refine eq_half ((hα _).1 (half_mem x)) ?_ ?_ ?_
  · simp [half_self]
  · intro z; simp [half_half]
  · intro h
    apply half_ne_one x
    have := congrArg (cj α.symm) h
    rw [cj_cj_symm] at this
    rw [this]
    ext z; simp

theorem half_map_apply (hα : Normalizes α) (x z : Dk) : α (half x z) = half (α x) (α z) := by
  have := congrArg (fun g : Dk ≃ₜ Dk => g (α z)) (half_map hα x)
  simpa using this

/-- **Midpoints go to midpoints.** -/
theorem mid_map (hα : Normalizes α) (x y : Dk) : α (mid x y) = mid (α x) (α y) := by
  apply eq_mid
  rw [← half_map_apply hα, half_mid]

/-- Rotations about `0` go to rotations about `0`. -/
theorem rot_map (hα : Normalizes α) (h0 : α d0 = d0) (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ z, (α (rotH u hu z) : ℂ) = v * α z := by
  have hs : α.symm d0 = d0 := by rw [Homeomorph.symm_apply_eq, h0]
  have hr : rotH u hu d0 = d0 := Subtype.ext (by simp)
  have hg := (hα _).1 (rotH_mem u hu)
  obtain ⟨v, hv, hgv⟩ := eq_mul_of_mem_holAut hg (by simp [hs, hr, h0])
  refine ⟨v, hv, fun z => ?_⟩
  have := hgv (α z)
  simpa using this

/-! ### The core: a normalised normaliser is the identity -/

theorem norm_I : ‖I‖ = 1 := by simp

theorem norm_neg_one : ‖(-1 : ℂ)‖ = 1 := by simp

/-- `r ↦ √(max (t - 1) 0 / (|t| + 1))`, the inverse of `qN` on `[1, ∞)`. -/
noncomputable def rad (t : ℝ) : ℝ := Real.sqrt (max (t - 1) 0 / (|t| + 1))

theorem rad_nonneg (t : ℝ) : 0 ≤ rad t := Real.sqrt_nonneg _

theorem rad_lt_one (t : ℝ) : rad t < 1 := by
  rw [rad, Real.sqrt_lt' one_pos, one_pow, div_lt_one (by positivity)]
  rcases le_total (t - 1) 0 with h | h
  · rw [max_eq_right h]; positivity
  · rw [max_eq_left h]; have := le_abs_self t; linarith

theorem abs_rad_lt_one (t : ℝ) : |rad t| < 1 := by
  rw [abs_of_nonneg (rad_nonneg t)]; exact rad_lt_one t

/-- `rad t` as a point of the disc. -/
noncomputable def radD (t : ℝ) : Dk := ⟨(rad t : ℂ), ofReal_mem_Dk (abs_rad_lt_one t)⟩

theorem continuous_rad : Continuous rad := by
  unfold rad
  refine Real.continuous_sqrt.comp ?_
  refine (continuous_id.sub continuous_const |>.max continuous_const).div
    (continuous_abs.add continuous_const) fun t => by positivity

theorem continuous_radD : Continuous radD :=
  (Complex.continuous_ofReal.comp continuous_rad).subtype_mk _

theorem qN_rad {t : ℝ} (ht : 1 ≤ t) : qN (rad t : ℂ) = t := by
  have hr : rad t * rad t = (t - 1) / (t + 1) := by
    rw [rad, Real.mul_self_sqrt (by positivity), max_eq_left (by linarith),
      abs_of_nonneg (by linarith)]
  rw [qN, Complex.normSq_ofReal, hr]
  have h : t + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem rad_qN {z : ℂ} (hz : z ∈ Dk) : rad (qN z) = ‖z‖ := by
  have h1 := one_le_qN hz
  have hn := normSq_lt_one_of_mem hz
  have hn0 := normSq_nonneg z
  rw [rad, max_eq_left (by linarith), abs_of_nonneg (by linarith)]
  have : (qN z - 1) / (qN z + 1) = normSq z := by
    rw [qN]
    have : 1 - normSq z ≠ 0 := by linarith
    field_simp
    ring
  rw [this, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]

theorem continuousOn_qN : ContinuousOn qN Dk := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
  have := normSq_lt_one_of_mem hz
  linarith

/-- A point equals the rotation of `‖z‖` by `z / ‖z‖`. -/
theorem polar (z : Dk) (hz : (z : ℂ) ≠ 0) :
    ∃ (u : ℂ) (hu : ‖u‖ = 1), z = rotH u hu ⟨(‖(z : ℂ)‖ : ℂ), ofReal_mem_Dk (by
      rw [abs_of_nonneg (norm_nonneg _)]; exact mem_Dk.1 z.2)⟩ := by
  have hn : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 hz
  refine ⟨(z : ℂ) / ‖(z : ℂ)‖, ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn.ne']
  · apply Subtype.ext
    rw [coe_rotH]
    have : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp

section Core

variable {β : Dk ≃ₜ Dk} (hβ : Normalizes β) (h0 : β d0 = d0)
  (hI : ∀ z, (β (rotH I norm_I z) : ℂ) = I * β z)
  (hR : ∀ (r : ℝ) (hr : (r : ℂ) ∈ Dk), 0 ≤ r → ∃ s : ℝ, 0 ≤ s ∧ (β ⟨r, hr⟩ : ℂ) = s)

include hβ h0 in
/-- `|β z|` only depends on `|z|`. -/
theorem qN_polar (z : Dk) :
    qN (β z) = qN (β ⟨(‖(z : ℂ)‖ : ℂ), ofReal_mem_Dk (by
      rw [abs_of_nonneg (norm_nonneg _)]; exact mem_Dk.1 z.2)⟩) := by
  by_cases hz : (z : ℂ) = 0
  · have : z = ⟨(‖(z : ℂ)‖ : ℂ), ofReal_mem_Dk (by
        rw [abs_of_nonneg (norm_nonneg _)]; exact mem_Dk.1 z.2)⟩ :=
      Subtype.ext (by simp [hz])
    rw [← this]
  · obtain ⟨u, hu, hzu⟩ := polar z hz
    obtain ⟨v, hv, hvβ⟩ := rot_map hβ h0 u hu
    conv_lhs => rw [hzu]
    rw [hvβ, qN_mul_unit hv]

include hI in
theorem neg_map (z : Dk) : (β (rotH (-1) norm_neg_one z) : ℂ) = -β z := by
  have : rotH (-1) norm_neg_one z = rotH I norm_I (rotH I norm_I z) :=
    Subtype.ext (by simp [← mul_assoc])
  rw [this, hI, hI, ← mul_assoc, I_mul_I, neg_one_mul]

/-- The function `φ` with `qN (β z) = φ (qN z)`. -/
noncomputable def phiOf (β : Dk ≃ₜ Dk) (t : ℝ) : ℝ := qN (β (radD t))

include hβ h0 in
theorem qN_eq_phi (z : Dk) : qN (β z) = phiOf β (qN z) := by
  rw [qN_polar hβ h0 z, phiOf]
  congr 3
  apply Subtype.ext
  simp only [radD]
  rw [rad_qN z.2]

theorem qN_I_mul (y : ℝ) : qN (I * y) = qN (y : ℂ) := by
  simp only [qN, Complex.normSq_mul, Complex.normSq_I, one_mul]

/-- Every real `A ∈ (-1, 1)` is `half a 0` for a real `a` (of the same sign). -/
theorem exists_half_d0_real {A : ℝ} (hA : |A| < 1) :
    ∃ (a : ℝ) (ha : (a : ℂ) ∈ Dk), (0 ≤ A → 0 ≤ a) ∧ (half ⟨a, ha⟩ d0 : ℂ) = A := by
  have hAD : (A : ℂ) ∈ Dk := ofReal_mem_Dk hA
  have hs : 0 < Real.sqrt (1 - A ^ 2) := sqrt_pos_of_mem (w := (A : ℂ)) hAD |>.trans_eq (by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])
  have e : mid0 (A : ℂ) = ((A / (1 + Real.sqrt (1 - A ^ 2)) : ℝ) : ℂ) := by
    rw [mid0, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    push_cast
    rfl
  have ha : ((A / (1 + Real.sqrt (1 - A ^ 2)) : ℝ) : ℂ) ∈ Dk := e ▸ mid0_mem hAD
  refine ⟨_, ha, fun h => by positivity, ?_⟩
  have := half_d0_mid0 ⟨A, hAD⟩
  have e' : (⟨((A / (1 + Real.sqrt (1 - A ^ 2)) : ℝ) : ℂ), ha⟩ : Dk) =
      ⟨mid0 (A : ℂ), mid0_mem hAD⟩ :=
    Subtype.ext e.symm
  rw [e', this]

theorem abs_double_lt {b : ℝ} (hb : |b| < 1) : |2 * b / (1 + b ^ 2)| < 1 := by
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + b ^ 2), div_lt_one (by positivity),
    abs_mul, abs_two]
  nlinarith [abs_nonneg b, sq_abs b]

theorem abs_lt_of_I_mem {c : ℝ} (hc : I * (c : ℂ) ∈ Dk) : |c| < 1 := by
  have := mem_Dk.1 hc
  rwa [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at this

/-- `qN (half b (i c)) = qN (half b 0) · qN c` for real `b`, `c`. -/
theorem qN_half_I (x w : Dk) (b c : ℝ) (hx : (x : ℂ) = b) (hw : (w : ℂ) = I * c) :
    qN (half x w) = qN (half x d0) * qN (c : ℂ) := by
  have hb : (b : ℂ) ∈ Dk := hx ▸ x.2
  have ex : x = ⟨b, hb⟩ := Subtype.ext hx
  have hb1 : |b| < 1 := by
    have := mem_Dk.1 hb; rwa [Complex.norm_real, Real.norm_eq_abs] at this
  have hc1 : |c| < 1 := abs_lt_of_I_mem (hw ▸ w.2)
  rw [ex, half_real hb w, hw, coe_half_d0_real hb]
  have e : -(I * (c : ℂ)) = I * ((-c : ℝ) : ℂ) := by push_cast; ring
  rw [e, qN_mob_I (abs_double_lt hb1) (by rwa [abs_neg]), qN_I_mul, Complex.ofReal_neg, qN_neg]

theorem mem_of_real {r : ℝ} (hr : |r| < 1) : (r : ℂ) ∈ Dk := ofReal_mem_Dk hr

include hβ h0 hI hR in
/-- **The key step**: `β` preserves `|z|`. -/
theorem normSq_map (z : Dk) : normSq (β z) = normSq (z : ℂ) := by
  -- values of `β` on nonnegative real points are nonnegative reals
  have hreal : ∀ x : Dk, ∀ b : ℝ, (x : ℂ) = b → 0 ≤ b → ∃ s : ℝ, 0 ≤ s ∧ (β x : ℂ) = s := by
    intro x b hx hb0
    have hb : (b : ℂ) ∈ Dk := hx ▸ x.2
    have ex : x = ⟨b, hb⟩ := Subtype.ext hx
    rw [ex]
    exact hR b hb hb0
  have hhalf0 : ∀ x : Dk, β (half x d0) = half (β x) d0 := by
    intro x; rw [half_map_apply hβ, h0]
  have hc : ContinuousOn (phiOf β) (Ici 1) :=
    (continuousOn_qN.comp_continuous (continuous_subtype_val.comp
      (β.continuous.comp continuous_radD)) (fun t => (β (radD t)).2)).continuousOn
  have hmul : ∀ s t, 1 ≤ s → 1 ≤ t → phiOf β (s * t) = phiOf β s * phiOf β t := by
    intro s t hs ht
    obtain ⟨a, ha, ha0, hA⟩ := exists_half_d0_real (abs_rad_lt_one s)
    have ha0 := ha0 (rad_nonneg s)
    have hyD : I * (rad t : ℂ) ∈ Dk := by
      rw [mem_Dk, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact abs_rad_lt_one t
    set x : Dk := ⟨a, ha⟩
    set w : Dk := ⟨I * (rad t : ℂ), hyD⟩
    have hxd : half x d0 = radD s := Subtype.ext hA
    have hw : w = rotH I norm_I (radD t) := Subtype.ext rfl
    have h1 : qN (half x w) = s * t := by
      rw [qN_half_I x w a (rad t) rfl rfl, hxd]
      simp only [radD]
      rw [qN_rad hs, qN_rad ht]
    obtain ⟨b, hb0, hb⟩ := hreal x a rfl ha0
    obtain ⟨c, hc0, hc⟩ := hreal (radD t) (rad t) rfl (rad_nonneg t)
    have hβw : (β w : ℂ) = I * c := by rw [hw, hI, hc]
    have h2 : qN (β (half x w)) = phiOf β s * phiOf β t := by
      rw [half_map_apply hβ, qN_half_I (β x) (β w) b c hb hβw, ← hhalf0, hxd, ← hc]
      rfl
    rw [← h1, ← h2, qN_eq_phi hβ h0]
  have hdbl : ∀ t, 1 ≤ t → phiOf β (2 * t ^ 2 - 1) = 2 * phiOf β t ^ 2 - 1 := by
    intro t ht
    have hd : qN (half (radD t) d0) = 2 * t ^ 2 - 1 := by
      rw [show (radD t) = ⟨(rad t : ℂ), ofReal_mem_Dk (abs_rad_lt_one t)⟩ from rfl,
        coe_half_d0_real, qN_double (abs_rad_lt_one t), qN_rad ht]
    obtain ⟨b, hb0, hb⟩ := hreal (radD t) (rad t) rfl (rad_nonneg t)
    have hbD : (b : ℂ) ∈ Dk := hb ▸ (β (radD t)).2
    have hb1 : |b| < 1 := by
      have := mem_Dk.1 hbD; rwa [Complex.norm_real, Real.norm_eq_abs] at this
    have ex : β (radD t) = ⟨b, hbD⟩ := Subtype.ext hb
    rw [← hd, ← qN_eq_phi hβ h0, hhalf0, ex, coe_half_d0_real, qN_double hb1]
    change _ = 2 * qN (β (radD t)) ^ 2 - 1
    rw [hb]
  have hgt : ∀ t, 1 < t → 1 < phiOf β t := by
    intro t ht
    apply one_lt_qN (β (radD t)).2
    intro h
    have h' : β (radD t) = β d0 := by rw [h0]; exact Subtype.ext h
    have := congrArg Subtype.val (β.injective h')
    simp only [radD, coe_d0, Complex.ofReal_eq_zero] at this
    have hpos : 0 < rad t := by
      rw [rad, Real.sqrt_pos, max_eq_left (by linarith)]
      exact div_pos (by linarith) (by positivity)
    linarith
  have hφ := fe_eq_id hc hmul hdbl hgt
  apply normSq_eq_of_qN_eq (β z).2 z.2
  rw [qN_eq_phi hβ h0, hφ _ (one_le_qN z.2)]

include hβ h0 hI hR in
/-- **A normaliser fixing `0`, commuting with `z ↦ i z` and preserving `[0, 1)` is the
identity.** -/
theorem eq_self_of_normalizes (z : Dk) : β z = z := by
  -- real points are fixed
  have hreal : ∀ (a : ℝ) (ha : (a : ℂ) ∈ Dk), β ⟨a, ha⟩ = ⟨a, ha⟩ := by
    have hpos : ∀ (a : ℝ) (ha : (a : ℂ) ∈ Dk), 0 ≤ a → β ⟨a, ha⟩ = ⟨a, ha⟩ := by
      intro a ha ha0
      obtain ⟨s, hs0, hs⟩ := hR a ha ha0
      have hn := normSq_map hβ h0 hI hR ⟨a, ha⟩
      rw [hs, Complex.normSq_ofReal, Complex.normSq_ofReal] at hn
      have : s = a := by nlinarith
      exact Subtype.ext (by rw [hs, this])
    intro a ha
    rcases le_total 0 a with h | h
    · exact hpos a ha h
    · have ha' : ((-a : ℝ) : ℂ) ∈ Dk := by push_cast; exact neg_mem_Dk ha
      have e : (⟨a, ha⟩ : Dk) = rotH (-1) norm_neg_one ⟨(-a : ℝ), ha'⟩ :=
        Subtype.ext (by simp)
      apply Subtype.ext
      rw [e, neg_map hI, hpos _ ha' (by linarith), coe_rotH]
      ring
  -- imaginary points are fixed
  have himag : ∀ (y : ℝ) (hy : I * (y : ℂ) ∈ Dk), β ⟨I * y, hy⟩ = ⟨I * y, hy⟩ := by
    intro y hy
    have hyD : (y : ℂ) ∈ Dk := ofReal_mem_Dk (abs_lt_of_I_mem hy)
    have e : (⟨I * y, hy⟩ : Dk) = rotH I norm_I ⟨y, hyD⟩ := Subtype.ext rfl
    apply Subtype.ext
    rw [e, hI, hreal]
    rfl
  obtain ⟨A, y, hA, hy, hz⟩ := exists_real_mob_imag z
  obtain ⟨a, ha, -, haA⟩ := exists_half_d0_real hA
  have hyD : I * ((-y : ℝ) : ℂ) ∈ Dk := by
    rw [mem_Dk, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    exact hy
  have hAa : ((2 * a / (1 + a ^ 2) : ℝ) : ℂ) = A := by rw [← coe_half_d0_real ha, haA]
  have ez : z = half ⟨a, ha⟩ ⟨I * ((-y : ℝ) : ℂ), hyD⟩ := by
    apply Subtype.ext
    rw [half_real ha, hAa, hz]
    congr 1
    push_cast
    ring
  rw [ez, half_map_apply hβ, hreal, himag]

end Core

/-! ### Rays -/

/-- A normaliser fixing `0` maps the segment `[0, tanh t]` into the ray through the image of
`tanh t`. -/
theorem onRay_map (hα : Normalizes α) (h0 : α d0 = d0) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    OnRay (α (tanhD t)) (α (tanhD s)) := by
  set S : Set ℝ := {u | OnRay (α (tanhD t)) (α (tanhD u))}
  have hS : IsClosed S :=
    (isClosed_onRay _).preimage (continuous_subtype_val.comp (α.continuous.comp continuous_tanhD))
  have hsub := Icc_subset_of_mid hS (hs.trans hst)
    (by
      change OnRay _ (α (tanhD 0) : ℂ)
      rw [tanhD_zero, h0, coe_d0]
      exact onRay_zero _)
    (onRay_self _)
    (fun a ha b hb _ _ => by
      change OnRay _ (α (tanhD ((a + b) / 2)) : ℂ)
      rw [← mid_tanh, mid_map hα]
      exact mid_onRay ha hb)
  exact hsub ⟨hs, hst⟩

theorem half_mem_Dk : ((1 / 2 : ℝ) : ℂ) ∈ Dk := ofReal_mem_Dk (by norm_num [abs_of_pos])

/-- All of `[0, 1)` is mapped into the ray through the image of `1/2`. -/
theorem onRay_map' (hα : Normalizes α) (h0 : α d0 = d0) (r : ℝ) (hr : (r : ℂ) ∈ Dk)
    (hr0 : 0 ≤ r) : OnRay (α ⟨((1 / 2 : ℝ) : ℂ), half_mem_Dk⟩) (α ⟨r, hr⟩) := by
  have hr1 : r < 1 := by
    have := mem_Dk.1 hr; rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at this
  have er : (⟨r, hr⟩ : Dk) = tanhD (Real.artanh r) :=
    Subtype.ext (by rw [coe_tanhD, Real.tanh_artanh ⟨by linarith, hr1⟩])
  have eh : (⟨((1 / 2 : ℝ) : ℂ), half_mem_Dk⟩ : Dk) = tanhD (Real.artanh (1 / 2)) :=
    Subtype.ext (by rw [coe_tanhD, Real.tanh_artanh ⟨by norm_num, by norm_num⟩])
  rw [er, eh]
  rcases le_total r (1 / 2) with h | h
  · exact onRay_map hα h0 (Real.artanh_nonneg hr0) (Real.artanh_le_artanh (by linarith)
      (by norm_num) h)
  · exact (onRay_map hα h0 (Real.artanh_nonneg (by norm_num)) (Real.artanh_le_artanh
      (by norm_num) hr1 h)).symm

/-! ### The theorem -/

/-- **[AbsTopIII] Proposition 2.2 (i) for the disc**: a homeomorphism of the disc which
normalises `holAut` is RC-holomorphic, i.e. `α = g` or `α = g ∘ conj` with `g ∈ holAut`. -/
theorem rc_of_normalizes (hα : Normalizes α) :
    ∃ g ∈ holAut, (∀ z, α z = g z) ∨ (∀ z, α z = g (conjH z)) := by
  set p := α d0
  set β₀ := α.trans (mobH p).symm with hβ₀
  have hβ₀n : Normalizes β₀ := hα.trans (normalizes_of_mem (holAut.inv_mem (mobH_mem p)))
  have hβ₀0 : β₀ d0 = d0 := by simp [hβ₀, p, mobH_symm_self]
  obtain ⟨v, hv, hvβ⟩ := rot_map hβ₀n hβ₀0 I norm_I
  -- `v = ± i`
  have hz₁ : ((1 / 2 : ℝ) : ℂ) ∈ Dk := half_mem_Dk
  set z₁ : Dk := ⟨((1 / 2 : ℝ) : ℂ), hz₁⟩
  have hβz₁ : (β₀ z₁ : ℂ) ≠ 0 := by
    intro h
    have : β₀ z₁ = β₀ d0 := by rw [hβ₀0]; exact Subtype.ext h
    have := congrArg Subtype.val (β₀.injective this)
    simp [z₁] at this
  have hv4 : v ^ 2 = -1 := by
    have e2 : ∀ z, (β₀ (rotH I norm_I (rotH I norm_I z)) : ℂ) = v ^ 2 * β₀ z := by
      intro z; rw [hvβ, hvβ]; ring
    have e4 : (β₀ z₁ : ℂ) = v ^ 2 * (v ^ 2 * β₀ z₁) := by
      have h4 : rotH I norm_I (rotH I norm_I (rotH I norm_I (rotH I norm_I z₁))) = z₁ :=
        Subtype.ext (by simp only [coe_rotH]; ring_nf; rw [I_pow_four, one_mul])
      have := e2 (rotH I norm_I (rotH I norm_I z₁))
      rw [h4, e2] at this
      exact this
    have hne : v ^ 2 ≠ 1 := by
      intro h1
      have := e2 z₁
      rw [h1, one_mul] at this
      have := congrArg Subtype.val (β₀.injective (Subtype.ext this))
      simp only [coe_rotH, z₁] at this
      rw [← mul_assoc, I_mul_I] at this
      have := congrArg Complex.re this
      norm_num at this
    have h4 : (v ^ 2 * v ^ 2 - 1) * (β₀ z₁ : ℂ) = 0 := by linear_combination -e4
    have h4' : v ^ 2 * v ^ 2 - 1 = 0 := (mul_eq_zero.1 h4).resolve_right hβz₁
    have : (v ^ 2 - 1) * (v ^ 2 + 1) = 0 := by linear_combination h4'
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact eq_neg_of_add_eq_zero_left h
  -- `β₁`: commutes with `z ↦ i z`
  obtain ⟨β₁, hβ₁n, hβ₁0, hβ₁I, hβ₀β₁⟩ : ∃ β₁ : Dk ≃ₜ Dk, Normalizes β₁ ∧ β₁ d0 = d0 ∧
      (∀ z, (β₁ (rotH I norm_I z) : ℂ) = I * β₁ z) ∧
      ((∀ z, β₀ z = β₁ z) ∨ (∀ z, β₀ z = conjH (β₁ z))) := by
    have : (v - I) * (v + I) = 0 := by ring_nf; rw [I_sq, hv4]; ring
    rcases mul_eq_zero.1 this with h | h
    · have hvI : v = I := sub_eq_zero.1 h
      exact ⟨β₀, hβ₀n, hβ₀0, fun z => by rw [hvβ, hvI], Or.inl fun _ => rfl⟩
    · have hvI : v = -I := eq_neg_of_add_eq_zero_left h
      refine ⟨β₀.trans conjH, hβ₀n.trans normalizes_conjH, by simp [hβ₀0, conjH_d0], fun z => ?_,
        Or.inr fun z => ?_⟩
      · simp only [Homeomorph.trans_apply, coe_conjH, hvβ, hvI, map_mul, map_neg,
          Complex.conj_I]
        ring
      · apply Subtype.ext; simp
  -- `β`: also maps `[0, 1)` into `[0, 1)`
  set w0 : ℂ := (β₁ z₁ : ℂ)
  have hw0 : w0 ≠ 0 := by
    intro h
    have : β₁ z₁ = β₁ d0 := by rw [hβ₁0]; exact Subtype.ext h
    have := congrArg Subtype.val (β₁.injective this)
    simp [z₁] at this
  have hnw : 0 < ‖w0‖ := norm_pos_iff.2 hw0
  set u0 : ℂ := conj w0 / ‖w0‖
  have hu0 : ‖u0‖ = 1 := by
    simp only [u0, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self hnw.ne']
  set β := β₁.trans (rotH u0 hu0) with hβdef
  have hβn : Normalizes β := hβ₁n.trans (normalizes_of_mem (rotH_mem u0 hu0))
  have hβ0 : β d0 = d0 := by
    apply Subtype.ext; simp [hβdef, hβ₁0]
  have hβI : ∀ z, (β (rotH I norm_I z) : ℂ) = I * β z := by
    intro z
    simp only [hβdef, Homeomorph.trans_apply, coe_rotH, hβ₁I]
    ring
  have hβR : ∀ (r : ℝ) (hr : (r : ℂ) ∈ Dk), 0 ≤ r → ∃ s : ℝ, 0 ≤ s ∧ (β ⟨r, hr⟩ : ℂ) = s := by
    intro r hr hr0
    have hray := onRay_map' hβ₁n hβ₁0 r hr hr0
    refine ⟨((β₁ ⟨r, hr⟩ : ℂ) * conj w0).re / ‖w0‖, div_nonneg hray.2 hnw.le, ?_⟩
    simp only [hβdef, Homeomorph.trans_apply, coe_rotH, u0]
    have hre : (β₁ ⟨r, hr⟩ : ℂ) * conj w0 = (((β₁ ⟨r, hr⟩ : ℂ) * conj w0).re : ℂ) := by
      apply Complex.ext
      · simp
      · rw [Complex.ofReal_im]; exact hray.1
    have hw' : (‖w0‖ : ℂ) ≠ 0 := by exact_mod_cast hnw.ne'
    push_cast
    rw [← hre]
    field_simp
  have hid := eq_self_of_normalizes hβn hβ0 hβI hβR
  -- unwind
  have hβ₁ : ∀ z, β₁ z = (rotH u0 hu0).symm z := by
    intro z
    have := hid z
    simp only [hβdef, Homeomorph.trans_apply] at this
    calc β₁ z = (rotH u0 hu0).symm (rotH u0 hu0 (β₁ z)) := ((rotH u0 hu0).symm_apply_apply _).symm
      _ = (rotH u0 hu0).symm z := by rw [this]
  have hαβ₀ : ∀ z, α z = mobH p (β₀ z) := by
    intro z; simp [hβ₀]
  rcases hβ₀β₁ with h | h
  · refine ⟨(rotH u0 hu0).symm.trans (mobH p),
      holAut.mul_mem (mobH_mem p) (holAut.inv_mem (rotH_mem u0 hu0)), Or.inl fun z => ?_⟩
    rw [Homeomorph.trans_apply, ← hβ₁, ← h, hαβ₀]
  · refine ⟨((conjH.symm.trans (rotH u0 hu0).symm).trans conjH).trans (mobH p),
      holAut.mul_mem (mobH_mem p) (conjH_conj_mem (holAut.inv_mem (rotH_mem u0 hu0))),
      Or.inr fun z => ?_⟩
    simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rw [← hβ₁, ← h, hαβ₀]

end Disc

end AutHol

end Iut
