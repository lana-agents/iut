/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.Labels

/-!
# Automorphisms normalising a dihedral action act on `F_ℓ` by a scalar (MR22 T6, group part)

IUT I, Example 4.3 (i) (l.6545–6600 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller
Theory I.txt`): the image of `Aut(C̲_K)` in `GL₂(F_ℓ)/{±1}` is a Borel subgroup, and
`Aut(C̲_K)/Aut_ϵ(C̲_K) ≅ F_ℓ^⋇` is the action on the rank-one quotient `Q ≅ F_ℓ` of `Δ_X^ab ⊗ F_ℓ`
(the lower right entry of the Borel matrix, up to `±1`). This file contains the elementary group
theory behind this, for an abstract group `G` (in the application `π₁(C_K)`) acting on `F_ℓ`
through `ρ : G → F_ℓ ⋊ {±1}` (affine maps `z ↦ ±z + c`, `FlSemi`), with a subgroup `R` (in the
application `π₁(C̲_K)`) equal to the stabiliser of `0` (`IsDihedralQuot`):

* **`exists_scalar`**: an automorphism `α` of `G` with `α(R) = R` acts on the orbit of `0` by a
  scalar: `ρ(α g)(0) = s · ρ(g)(0)` for a unit `s ∈ F_ℓ^×` (the conjugate of the translation
  `z ↦ z + 1` by the induced bijection of `G/R ≅ F_ℓ` is a translation, since the reflections
  have order `2` and `ℓ` is odd);
* `stabAut ρ R`, the automorphisms preserving `R`, and the homomorphism **`scalHom`** to
  `F_ℓ^×`;
* **`scalHom_conj`**: conjugation by an element of `R` has scalar `±1`.
-/

noncomputable section

namespace Iut.Multiradial.Theater

open Iut.HodgeTheater

variable {ℓ : ℕ} [OddPrime ℓ] {G : Type*} [Group G]

/-- **`G` acts on `F_ℓ` dihedrally with stabiliser `R` of `0`**: `ρ` takes values in the affine
maps `z ↦ ±z + c`, contains the translation `z ↦ z + 1`, and `R = {g | ρ(g)(0) = 0}`. -/
def IsDihedralQuot (ρ : G →* Equiv.Perm (ZMod ℓ)) (R : Subgroup G) : Prop :=
  (∀ g, ρ g ∈ FlSemi ℓ) ∧ (∀ g, g ∈ R ↔ ρ g 0 = 0) ∧ ∃ x : G, ρ x = affPerm ℓ 1 1

/-- `(2 : F_ℓ) ≠ 0` for an odd prime `ℓ`. -/
lemma two_ne_zero_zmod : (2 : ZMod ℓ) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  have := OddPrime.two_lt (ℓ := ℓ)
  omega

/-- **An automorphism preserving `R` acts on `F_ℓ = G/R` by a scalar.** -/
theorem exists_scalar {ρ : G →* Equiv.Perm (ZMod ℓ)} {R : Subgroup G}
    (h : IsDihedralQuot ρ R) (α : G ≃* G) (hα : ∀ g, α g ∈ R ↔ g ∈ R) :
    ∃ s : (ZMod ℓ)ˣ, ∀ g, ρ (α g) 0 = s * ρ g 0 := by
  obtain ⟨hS, hR, x₁, hx₁⟩ := h
  obtain ⟨ε, b, hg₁⟩ := hS (α x₁)
  have hb : ρ (α x₁) 0 = b := by rw [hg₁]; simp
  have step : ∀ g, ρ (α (x₁ * g)) 0 = sgn ℓ ε * ρ (α g) 0 + b := fun g => by
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, hg₁, affPerm_apply]
  have hρx : ∀ g, ρ (x₁ * g) 0 = ρ g 0 + 1 := fun g => by
    rw [map_mul, Equiv.Perm.mul_apply, hx₁, affPerm_apply, sgn_one, one_mul]
  have hx₁0 : ρ x₁ 0 = 1 := by rw [hx₁]; simp
  have hε : ε = 1 := by
    rcases Int.units_eq_one_or ε with h | h
    · exact h
    exfalso
    have h2 : ρ (α (x₁ * x₁)) 0 = 0 := by
      rw [step, hb, h, sgn_neg_one]
      ring
    have hmem : x₁ * x₁ ∈ R := (hα _).1 ((hR _).2 h2)
    have h3 := (hR _).1 hmem
    rw [hρx, hx₁0] at h3
    exact two_ne_zero_zmod (ℓ := ℓ) (by linear_combination h3)
  subst hε
  have hn : ∀ n : ℕ, ∀ g, ρ g 0 = n → ρ (α g) 0 = n * b := by
    intro n
    induction n with
    | zero =>
      intro g hg
      rw [Nat.cast_zero] at hg ⊢
      rw [zero_mul]
      exact (hR _).1 ((hα g).2 ((hR g).2 hg))
    | succ n ih =>
      intro g hg
      have e1 : ρ (x₁⁻¹ * g) 0 = n := by
        have := hρx (x₁⁻¹ * g)
        rw [mul_inv_cancel_left] at this
        push_cast at hg
        linear_combination hg - this
      have e2 := step (x₁⁻¹ * g)
      rw [mul_inv_cancel_left] at e2
      rw [e2, ih _ e1, sgn_one]
      push_cast
      ring
  have hb0 : b ≠ 0 := by
    intro h0
    have hmem : x₁ ∈ R := (hα _).1 ((hR _).2 (by rw [hb, h0]))
    have := (hR _).1 hmem
    rw [hx₁0] at this
    exact one_ne_zero this
  refine ⟨Units.mk0 b hb0, fun g => ?_⟩
  have := hn (ρ g 0).val g (by rw [ZMod.natCast_zmod_val])
  rw [this, ZMod.natCast_zmod_val, Units.val_mk0, mul_comm]

/-- The scalar is determined by the value at the translation `x₁`. -/
lemma scalar_unique {ρ : G →* Equiv.Perm (ZMod ℓ)} {x₁ : G} (hx₁ : ρ x₁ = affPerm ℓ 1 1)
    {α : G ≃* G} {s t : (ZMod ℓ)ˣ} (hs : ∀ g, ρ (α g) 0 = s * ρ g 0)
    (ht : ∀ g, ρ (α g) 0 = t * ρ g 0) : s = t := by
  have h1 : ρ x₁ 0 = 1 := by rw [hx₁]; simp
  have := (hs x₁).symm.trans (ht x₁)
  rw [h1, mul_one, mul_one] at this
  exact Units.ext this

variable (ρ : G →* Equiv.Perm (ZMod ℓ)) (R : Subgroup G)

/-- **The automorphisms of `G` preserving `R`.** -/
def stabAut : Subgroup (MulAut G) where
  carrier := {α | ∀ g, α g ∈ R ↔ g ∈ R}
  mul_mem' {α β} hα hβ g := by
    change α (β g) ∈ R ↔ g ∈ R
    rw [hα, hβ]
  one_mem' g := Iff.rfl
  inv_mem' {α} hα g := by
    have := hα (α⁻¹ g)
    rw [MulAut.apply_inv_self] at this
    exact this.symm

variable {ρ R}

/-- The scalar of an automorphism preserving `R`. -/
def scal (h : IsDihedralQuot ρ R) (α : stabAut R) : (ZMod ℓ)ˣ :=
  (exists_scalar h α.1 α.2).choose

lemma scal_spec (h : IsDihedralQuot ρ R) (α : stabAut R) (g : G) :
    ρ ((α : MulAut G) g) 0 = scal h α * ρ g 0 :=
  (exists_scalar h α.1 α.2).choose_spec g

/-- **The scalar homomorphism `stabAut R → F_ℓ^×`.** -/
def scalHom (h : IsDihedralQuot ρ R) : stabAut R →* (ZMod ℓ)ˣ where
  toFun := scal h
  map_one' := scalar_unique h.2.2.choose_spec (scal_spec h 1) fun g => by simp
  map_mul' α β := scalar_unique h.2.2.choose_spec (scal_spec h (α * β)) fun g => by
    change ρ ((α : MulAut G) ((β : MulAut G) g)) 0 = _
    rw [scal_spec, scal_spec, Units.val_mul, mul_assoc]

lemma scalHom_spec (h : IsDihedralQuot ρ R) (α : stabAut R) (g : G) :
    ρ ((α : MulAut G) g) 0 = scalHom h α * ρ g 0 :=
  scal_spec h α g

/-- Conjugation by an element of `R` preserves `R`. -/
lemma conj_mem_stabAut (r : R) : MulAut.conj (r : G) ∈ stabAut R := fun g => by
  change (r : G) * g * (r : G)⁻¹ ∈ R ↔ g ∈ R
  constructor
  · intro hg
    have := R.mul_mem (R.mul_mem (R.inv_mem r.2) hg) r.2
    simpa [mul_assoc] using this
  · intro hg
    exact R.mul_mem (R.mul_mem r.2 hg) (R.inv_mem r.2)

/-- **Conjugation by an element of `R` has scalar `±1`.** -/
theorem scalHom_conj (h : IsDihedralQuot ρ R) (r : R) :
    scalHom h ⟨MulAut.conj (r : G), conj_mem_stabAut r⟩ ∈ pmSub ℓ := by
  have hR := h.2.1
  obtain ⟨ε, c, hrc⟩ := h.1 r
  have hc : c = 0 := by
    have := (hR r).1 r.2
    rw [hrc] at this
    simpa using this
  subst hc
  have hinv : ρ (r : G)⁻¹ 0 = 0 := (hR _).1 (R.inv_mem r.2)
  have key : ∀ g, ρ ((MulAut.conj (r : G)) g) 0 = ((sgn ℓ ε : ZMod ℓ)) * ρ g 0 := fun g => by
    change ρ ((r : G) * g * (r : G)⁻¹) 0 = _
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, hrc, affPerm_apply,
      add_zero]
  rcases Int.units_eq_one_or ε with rfl | rfl
  · left
    exact scalar_unique h.2.2.choose_spec (scalHom_spec h _) fun g => by
      rw [key, sgn_one, Units.val_one]
  · right
    exact scalar_unique h.2.2.choose_spec (scalHom_spec h _) fun g => by
      rw [key, sgn_neg_one, Units.val_neg, Units.val_one]

/-! ### Automorphisms preserving the kernel: conjugation by an affine map -/

section Affine

variable (ℓ) in
/-- The affine permutation `z ↦ a z + b` of `F_ℓ`, `a ∈ F_ℓ^×`. -/
def affU (a : (ZMod ℓ)ˣ) (b : ZMod ℓ) : Equiv.Perm (ZMod ℓ) where
  toFun z := a * z + b
  invFun z := (a⁻¹ : (ZMod ℓ)ˣ) * (z - b)
  left_inv z := by
    change (a⁻¹ : (ZMod ℓ)ˣ) * ((a : ZMod ℓ) * z + b - b) = z
    rw [add_sub_cancel_right, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mul]
  right_inv z := by
    change (a : ZMod ℓ) * ((a⁻¹ : (ZMod ℓ)ˣ) * (z - b)) + b = z
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, sub_add_cancel]

@[simp] lemma affU_apply (a : (ZMod ℓ)ˣ) (b z : ZMod ℓ) : affU ℓ a b z = a * z + b := rfl

lemma affU_mul (a a' : (ZMod ℓ)ˣ) (b b' : ZMod ℓ) :
    affU ℓ a b * affU ℓ a' b' = affU ℓ (a * a') (a * b' + b) := by
  ext z
  simp only [Equiv.Perm.mul_apply, affU_apply, Units.val_mul]
  ring

/-- `affPerm ε c` is `affU ε c`. -/
lemma affPerm_eq_affU (ε : ℤˣ) (c : ZMod ℓ) :
    affPerm ℓ ε c = affU ℓ (Units.map (Int.castRingHom (ZMod ℓ)).toMonoidHom ε) c := by
  ext z
  simp [sgn]

/-- **`G` acts on `F_ℓ` through the full dihedral group**: `ρ` takes values in `F_ℓ ⋊ {±1}` and
contains the translation `z ↦ z + 1` and the reflection `z ↦ −z`. -/
def IsDihedralFull (ρ : G →* Equiv.Perm (ZMod ℓ)) : Prop :=
  (∀ g, ρ g ∈ FlSemi ℓ) ∧ (∃ x : G, ρ x = affPerm ℓ 1 1) ∧ ∃ x : G, ρ x = affPerm ℓ (-1) 0

lemma affPerm_one_pow (n : ℕ) : affPerm ℓ 1 1 ^ n = affPerm ℓ 1 n := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, affPerm_one]
  | succ n ih => rw [pow_succ, ih, affPerm_mul, sgn_one, one_mul, mul_one, Nat.cast_succ, add_comm]

/-- Every element of `F_ℓ ⋊ {±1}` is `τ^n` or `τ^n r` (`τ` the translation, `r` the
reflection). -/
lemma exists_word {ρ : G →* Equiv.Perm (ZMod ℓ)} (h : IsDihedralFull ρ) (g : G) :
    ∃ n : ℕ, ∃ m : ℕ, m < 2 ∧ ρ g = ρ (h.2.1.choose ^ n * h.2.2.choose ^ m) := by
  obtain ⟨ε, c, hc⟩ := h.1 g
  have h1 := h.2.1.choose_spec
  have h0 := h.2.2.choose_spec
  refine ⟨c.val, ?_⟩
  rcases Int.units_eq_one_or ε with rfl | rfl
  · refine ⟨0, by norm_num, ?_⟩
    rw [pow_zero, mul_one, map_pow, h1, affPerm_one_pow, ZMod.natCast_zmod_val, hc]
  · refine ⟨1, by norm_num, ?_⟩
    rw [pow_one, map_mul, map_pow, h1, h0, affPerm_one_pow, ZMod.natCast_zmod_val, hc,
      affPerm_mul, sgn_one, one_mul, mul_zero, zero_add]

/-- **An automorphism preserving `ker ρ` is conjugation by an affine map**: there are
`a ∈ F_ℓ^×`, `b ∈ F_ℓ` with `ρ(α g) ∘ ψ = ψ ∘ ρ(g)` for `ψ = (z ↦ a z + b)` (the automorphisms
of the dihedral group `F_ℓ ⋊ {±1}`, `ℓ` odd). -/
theorem exists_affine {ρ : G →* Equiv.Perm (ZMod ℓ)} (h : IsDihedralFull ρ) (α : G ≃* G)
    (hα : ∀ g, α g ∈ ρ.ker ↔ g ∈ ρ.ker) :
    ∃ a : (ZMod ℓ)ˣ, ∃ b : ZMod ℓ, ∀ g, ρ (α g) * affU ℓ a b = affU ℓ a b * ρ g := by
  obtain ⟨hS, ⟨x₁, hx₁⟩, ⟨x₀, hx₀⟩⟩ := h
  -- `ρ ∘ α` only depends on `ρ`
  have hdep : ∀ g g', ρ g = ρ g' → ρ (α g) = ρ (α g') := fun g g' he => by
    have hk : g⁻¹ * g' ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    have hk' := (hα _).2 hk
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one] at hk'
    exact hk'
  have hne : ∀ g, ρ g ≠ 1 → ρ (α g) ≠ 1 := fun g hg h1 => hg (by
    have := (hα g).1 (MonoidHom.mem_ker.2 h1)
    exact MonoidHom.mem_ker.1 this)
  obtain ⟨ε, a, ht⟩ := hS (α x₁)
  obtain ⟨ε', b, hs⟩ := hS (α x₀)
  have hτ1 : ρ x₁ ≠ 1 := fun h1 => by
    have := congrArg (· 0) h1
    simp [hx₁] at this
  have hr1 : ρ x₀ ≠ 1 := fun h1 => by
    have := congrArg (· 1) h1
    simp only [hx₀, affPerm_apply, sgn_neg_one, mul_one, add_zero, Equiv.Perm.coe_one, id_eq]
      at this
    exact two_ne_zero_zmod (ℓ := ℓ) (by linear_combination -this)
  -- `ρ(α x₁)` is a translation by `a ≠ 0`
  have hε : ε = 1 := by
    rcases Int.units_eq_one_or ε with h1 | h1
    · exact h1
    exfalso
    apply hne (x₁ * x₁)
    · rw [map_mul, hx₁, affPerm_mul]
      intro h2
      have := congrArg (· 0) h2
      simp only [affPerm_apply, sgn_one, mul_one, mul_zero, zero_add, Equiv.Perm.coe_one,
        id_eq] at this
      exact two_ne_zero_zmod (ℓ := ℓ) (by linear_combination this)
    · rw [map_mul, map_mul, ht, h1, affPerm_mul]
      ext z
      simp
  subst hε
  have ha : a ≠ 0 := fun h0 => hne x₁ hτ1 (by rw [ht, h0, affPerm_one])
  -- `ρ(α x₀)` is a reflection `z ↦ −z + b`
  have hε' : ε' = -1 := by
    rcases Int.units_eq_one_or ε' with h1 | h1
    · exfalso
      have hsq : ρ (α (x₀ * x₀)) = 1 := by
        have : ρ (x₀ * x₀) = ρ 1 := by
          rw [map_mul, hx₀, affPerm_mul, map_one]
          ext z
          simp
        rw [hdep _ _ this, map_one, map_one]
      rw [map_mul, map_mul, hs, h1, affPerm_mul] at hsq
      have hb : b = 0 := by
        have := congrArg (· 0) hsq
        simp only [affPerm_apply, sgn_one, one_mul, mul_zero, zero_add, Equiv.Perm.coe_one,
          id_eq] at this
        have h2 : (2 : ZMod ℓ) * b = 0 := by linear_combination this
        exact (mul_eq_zero.1 h2).resolve_left two_ne_zero_zmod
      exact hne x₀ hr1 (by rw [hs, h1, hb, affPerm_one])
    · exact h1
  subst hε'
  -- `ψ = (z ↦ a z + b/2)`
  have h2 : (2 : ZMod ℓ) ≠ 0 := two_ne_zero_zmod
  let ψ := affU ℓ (Units.mk0 a ha) (b / 2)
  have key1 : ρ (α x₁) * ψ = ψ * ρ x₁ := by
    rw [ht, hx₁]
    ext z
    simp only [Equiv.Perm.mul_apply, affPerm_apply, affU_apply, sgn_one, one_mul, ψ,
      Units.val_mk0]
    ring
  have key0 : ρ (α x₀) * ψ = ψ * ρ x₀ := by
    rw [hs, hx₀]
    ext z
    simp only [Equiv.Perm.mul_apply, affPerm_apply, affU_apply, sgn_neg_one, ψ, Units.val_mk0]
    field_simp
    ring
  refine ⟨Units.mk0 a ha, b / 2, fun g => ?_⟩
  obtain ⟨n, m, -, hg⟩ := exists_word ⟨hS, ⟨x₁, hx₁⟩, ⟨x₀, hx₀⟩⟩ g
  set y₁ := (⟨hS, ⟨x₁, hx₁⟩, ⟨x₀, hx₀⟩⟩ : IsDihedralFull ρ).2.1.choose
  set y₀ := (⟨hS, ⟨x₁, hx₁⟩, ⟨x₀, hx₀⟩⟩ : IsDihedralFull ρ).2.2.choose
  have hy₁ : ρ y₁ = ρ x₁ := by
    rw [(⟨hS, ⟨x₁, hx₁⟩, ⟨x₀, hx₀⟩⟩ : IsDihedralFull ρ).2.1.choose_spec, hx₁]
  have hy₀ : ρ y₀ = ρ x₀ := by
    rw [(⟨hS, ⟨x₁, hx₁⟩, ⟨x₀, hx₀⟩⟩ : IsDihedralFull ρ).2.2.choose_spec, hx₀]
  have k1 : ρ (α y₁) * ψ = ψ * ρ y₁ := by rw [hdep _ _ hy₁, hy₁]; exact key1
  have k0 : ρ (α y₀) * ψ = ψ * ρ y₀ := by rw [hdep _ _ hy₀, hy₀]; exact key0
  have kpow : ∀ (y : G), ρ (α y) * ψ = ψ * ρ y → ∀ k : ℕ, ρ (α (y ^ k)) * ψ = ψ * ρ (y ^ k) := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, map_mul, map_mul, map_mul, mul_assoc, hy, ← mul_assoc, ih, mul_assoc]
  rw [hdep _ _ hg, hg, map_mul, map_mul, map_mul, mul_assoc, kpow y₀ k0 m, ← mul_assoc,
    kpow y₁ k1 n, mul_assoc]

/-- Intertwining a translation pins down the linear part. -/
lemma eq_add_of_comm {P : Equiv.Perm (ZMod ℓ)} {a : (ZMod ℓ)ˣ} {b : ZMod ℓ}
    (h : P * affU ℓ a b = affU ℓ a b * affPerm ℓ 1 1) (w : ZMod ℓ) : P w = w + a := by
  have h' := congrArg (· ((a⁻¹ : (ZMod ℓ)ˣ) * (w - b))) h
  simp only [Equiv.Perm.mul_apply, affU_apply, affPerm_apply, sgn_one, one_mul] at h'
  have e : (a : ZMod ℓ) * ((a⁻¹ : (ZMod ℓ)ˣ) * (w - b)) + b = w := by
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, sub_add_cancel]
  rw [e] at h'
  rw [h']
  linear_combination e

/-- Intertwining the reflection pins down the translation part. -/
lemma eq_neg_add_of_comm {P : Equiv.Perm (ZMod ℓ)} {a : (ZMod ℓ)ˣ} {b : ZMod ℓ}
    (h : P * affU ℓ a b = affU ℓ a b * affPerm ℓ (-1) 0) (w : ZMod ℓ) : P w = -w + 2 * b := by
  have h' := congrArg (· ((a⁻¹ : (ZMod ℓ)ˣ) * (w - b))) h
  simp only [Equiv.Perm.mul_apply, affU_apply, affPerm_apply, sgn_neg_one, add_zero] at h'
  have e : (a : ZMod ℓ) * ((a⁻¹ : (ZMod ℓ)ˣ) * (w - b)) + b = w := by
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, sub_add_cancel]
  rw [e] at h'
  rw [h']
  linear_combination -e

/-- **The affine map of an automorphism preserving `ker ρ` is unique.** -/
theorem affine_unique {ρ : G →* Equiv.Perm (ZMod ℓ)} (h : IsDihedralFull ρ) {α : G ≃* G}
    {a a' : (ZMod ℓ)ˣ} {b b' : ZMod ℓ} (H : ∀ g, ρ (α g) * affU ℓ a b = affU ℓ a b * ρ g)
    (H' : ∀ g, ρ (α g) * affU ℓ a' b' = affU ℓ a' b' * ρ g) : a = a' ∧ b = b' := by
  obtain ⟨-, ⟨x₁, hx₁⟩, ⟨x₀, hx₀⟩⟩ := h
  have h1 := H x₁
  have h1' := H' x₁
  have h0 := H x₀
  have h0' := H' x₀
  rw [hx₁] at h1 h1'
  rw [hx₀] at h0 h0'
  have ea : (a : ZMod ℓ) = a' := by
    have := (eq_add_of_comm h1 0).symm.trans (eq_add_of_comm h1' 0)
    simpa using this
  refine ⟨Units.ext ea, ?_⟩
  have := (eq_neg_add_of_comm h0 0).symm.trans (eq_neg_add_of_comm h0' 0)
  have h2 : (2 : ZMod ℓ) * (b - b') = 0 := by linear_combination this
  exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left two_ne_zero_zmod)

variable {ρ : G →* Equiv.Perm (ZMod ℓ)}

/-- The affine data `(a, b)` of an automorphism preserving `ker ρ`. -/
def affOf (h : IsDihedralFull ρ) (α : stabAut ρ.ker) : (ZMod ℓ)ˣ × ZMod ℓ :=
  ((exists_affine h α.1 α.2).choose, (exists_affine h α.1 α.2).choose_spec.choose)

lemma affOf_spec (h : IsDihedralFull ρ) (α : stabAut ρ.ker) (g : G) :
    ρ ((α : MulAut G) g) * affU ℓ (affOf h α).1 (affOf h α).2 =
      affU ℓ (affOf h α).1 (affOf h α).2 * ρ g :=
  (exists_affine h α.1 α.2).choose_spec.choose_spec g

lemma affOf_eq (h : IsDihedralFull ρ) (α : stabAut ρ.ker) {a : (ZMod ℓ)ˣ} {b : ZMod ℓ}
    (H : ∀ g, ρ ((α : MulAut G) g) * affU ℓ a b = affU ℓ a b * ρ g) : affOf h α = (a, b) := by
  obtain ⟨h1, h2⟩ := affine_unique h (affOf_spec h α) H
  exact Prod.ext h1 h2

lemma affOf_mul (h : IsDihedralFull ρ) (α β : stabAut ρ.ker) :
    affOf h (α * β) = ((affOf h α).1 * (affOf h β).1,
      (affOf h α).1 * (affOf h β).2 + (affOf h α).2) := by
  apply affOf_eq
  intro g
  rw [← affU_mul]
  change ρ ((α : MulAut G) ((β : MulAut G) g)) * _ = _
  rw [← mul_assoc, affOf_spec, mul_assoc, affOf_spec, mul_assoc]

lemma affOf_one (h : IsDihedralFull ρ) : affOf h 1 = (1, 0) :=
  affOf_eq h 1 fun g => by
    have e : affU ℓ 1 0 = 1 := by ext z; simp
    rw [e, mul_one, one_mul]
    rfl

/-- **The permutation of `F_ℓ` (the cusps) induced by an automorphism preserving `ker ρ`.** -/
def psiHom (h : IsDihedralFull ρ) : stabAut ρ.ker →* Equiv.Perm (ZMod ℓ) where
  toFun α := affU ℓ (affOf h α).1 (affOf h α).2
  map_one' := by rw [affOf_one]; ext z; simp
  map_mul' α β := by rw [affOf_mul, affU_mul]

lemma psiHom_spec (h : IsDihedralFull ρ) (α : stabAut ρ.ker) (g : G) :
    ρ ((α : MulAut G) g) * psiHom h α = psiHom h α * ρ g :=
  affOf_spec h α g

/-- **The linear part `a ∈ F_ℓ^×` of the affine map** (the action on the rank-one quotient). -/
def linHom (h : IsDihedralFull ρ) : stabAut ρ.ker →* (ZMod ℓ)ˣ where
  toFun α := (affOf h α).1
  map_one' := by rw [affOf_one]
  map_mul' α β := by rw [affOf_mul]

lemma psiHom_eq (h : IsDihedralFull ρ) (α : stabAut ρ.ker) :
    psiHom h α = affU ℓ (linHom h α) (affOf h α).2 := rfl

omit [OddPrime ℓ] in
/-- Conjugation by `g ∈ G` preserves `ker ρ`. -/
lemma conj_mem_stabAut_ker (g : G) : MulAut.conj g ∈ stabAut ρ.ker := fun x => by
  change g * x * g⁻¹ ∈ ρ.ker ↔ x ∈ ρ.ker
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, map_mul, map_mul, map_inv]
  constructor
  · intro hx
    have := congrArg (fun y => (ρ g)⁻¹ * y * ρ g) hx
    simpa [mul_assoc] using this
  · intro hx
    rw [hx]
    group

/-- **Inner automorphisms act through `ρ`**: `ψ(conj g) = ρ(g)`, with linear part `±1`. -/
theorem affOf_conj (h : IsDihedralFull ρ) (g : G) :
    ∃ ε : ℤˣ, affOf h ⟨MulAut.conj g, conj_mem_stabAut_ker g⟩ =
      (Units.map (Int.castRingHom (ZMod ℓ)).toMonoidHom ε, (affOf h ⟨MulAut.conj g,
        conj_mem_stabAut_ker g⟩).2) ∧
      psiHom h ⟨MulAut.conj g, conj_mem_stabAut_ker g⟩ = ρ g := by
  obtain ⟨ε, c, hc⟩ := h.1 g
  have H : ∀ x, ρ ((MulAut.conj g : MulAut G) x) *
      affU ℓ (Units.map (Int.castRingHom (ZMod ℓ)).toMonoidHom ε) c =
      affU ℓ (Units.map (Int.castRingHom (ZMod ℓ)).toMonoidHom ε) c * ρ x := fun x => by
    rw [← affPerm_eq_affU, ← hc]
    change ρ (g * x * g⁻¹) * ρ g = ρ g * ρ x
    rw [map_mul, map_mul, map_inv, inv_mul_cancel_right]
  have e := affOf_eq h ⟨MulAut.conj g, conj_mem_stabAut_ker g⟩ H
  refine ⟨ε, by rw [e], ?_⟩
  change affU ℓ (affOf h _).1 (affOf h _).2 = ρ g
  rw [e, hc, affPerm_eq_affU]

end Affine

end Iut.Multiradial.Theater
