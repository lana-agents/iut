/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# The label combinatorics of IUT I (§4, Definition 6.1(i))

For an odd prime `ℓ` (the prime of initial Θ-data, IUT I, Definition 3.1(b)):

* `FlStar ℓ = F_ℓ^* = F_ℓ^×/{±1}` (IUT I, §4, beginning), a group of order `ℓ* = (ℓ − 1)/2`
  (`card_flStar`);
* `AbsFl ℓ = |F_ℓ| = F_ℓ/{±1}` (IUT I, Example 4.4(i)), a set of `ℓ± = ℓ* + 1` elements
  (`card_absFl`), with the minimal representatives `absRep : |F_ℓ| ≃ {0, …, ℓ*}` and the
  identification of its nonzero elements with `F_ℓ^*` (`nonzeroAbsEquiv`, "`|F_ℓ| = 0 ∪ F_ℓ^*`");
* `FlSemi ℓ = F_ℓ^{⋊±} = F_ℓ ⋊ {±1}` (Definition 6.1(i)), realised as the group of affine
  permutations `z ↦ ±z + λ` of `F_ℓ`, of order `2ℓ` (`card_flSemi`); it acts transitively on
  `F_ℓ` with stabilizers of order two (`flSemi_isPretransitive`, `card_stabilizer_flSemi`; the
  "double transitivity" of IUT I, Proposition 6.8(i));
* **`F_ℓ^±`-torsors** (`PmTorsor`: a set with an `F_ℓ^{⋊±}`-orbit of bijections to `F_ℓ`),
  **`F_ℓ^±`-groups** (`PmGroup`: a set with a `{±1}`-orbit of bijections to `F_ℓ`) and
  **`F_ℓ^*`-torsors** (`StarTorsor`), with their isomorphisms; **the sets of isomorphisms** are
  `≃ F_ℓ^{⋊±}` (`PmTorsor.isoEquivSemi`), `≃ {±1}` (`PmGroup.isoEquiv`), `≃ F_ℓ^*`
  (`StarTorsor.isoEquiv`).

## Encoding

An `F_ℓ^±`-torsor is recorded by one chart `T ≃ F_ℓ` of its orbit of charts; an isomorphism
records the sign `s` and the shift `λ` of the affine map `z ↦ s·z + λ` it induces in the charts
(`PmTorsor.Iso`). For `ℓ` odd these are determined by the underlying bijection
(`PmTorsor.Iso.ext`). An isomorphism of `F_ℓ^±`-groups is one with shift `0`; it is *positive* if
its sign is `+1` (Definition 6.1(i), (iii)).
-/

namespace Iut

namespace HodgeTheater

/-! ### `ℓ*` and `ℓ±` -/

/-- `ℓ* = (ℓ − 1)/2`. -/
abbrev ellStar (ℓ : ℕ) : ℕ := (ℓ - 1) / 2

/-- `ℓ± = ℓ* + 1 = (ℓ + 1)/2` (IUT I, Definition 6.4). -/
abbrev ellPm (ℓ : ℕ) : ℕ := ellStar ℓ + 1

/-- **`ℓ` is an odd prime** (the prime of initial Θ-data is `≥ 5`). -/
class OddPrime (ℓ : ℕ) : Prop where
  prime : ℓ.Prime
  two_lt : 2 < ℓ

instance (ℓ : ℕ) [h : OddPrime ℓ] : Fact ℓ.Prime := ⟨h.prime⟩

instance (ℓ : ℕ) [h : OddPrime ℓ] : Fact (2 < ℓ) := ⟨h.two_lt⟩

instance (ℓ : ℕ) [h : OddPrime ℓ] : NeZero ℓ := ⟨h.prime.ne_zero⟩

variable (ℓ : ℕ)

/-! ### Signs -/

/-- The image of a sign `±1` in `F_ℓ`. -/
def sgn (s : ℤˣ) : ZMod ℓ := ((s : ℤ) : ZMod ℓ)

variable {ℓ}

@[simp] lemma sgn_one : sgn ℓ 1 = 1 := by simp [sgn]

@[simp] lemma sgn_neg_one : sgn ℓ (-1) = -1 := by simp [sgn]

lemma sgn_mul (s t : ℤˣ) : sgn ℓ (s * t) = sgn ℓ s * sgn ℓ t := by simp [sgn]

@[simp] lemma sgn_mul_self (s : ℤˣ) : sgn ℓ s * sgn ℓ s = 1 := by
  rw [← sgn_mul, Int.units_mul_self, sgn_one]

lemma sgn_inv (s : ℤˣ) : sgn ℓ s⁻¹ = sgn ℓ s := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp

variable (ℓ)

/-- The subgroup `{±1} ⊆ F_ℓ^×`. -/
def pmSub : Subgroup (ZMod ℓ)ˣ where
  carrier := {u | u = 1 ∨ u = -1}
  mul_mem' {a b} ha hb := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  one_mem' := Or.inl rfl
  inv_mem' {a} ha := by rcases ha with rfl | rfl <;> simp

variable {ℓ} in
lemma mem_pmSub {u : (ZMod ℓ)ˣ} : u ∈ pmSub ℓ ↔ u = 1 ∨ u = -1 := Iff.rfl

/-- The relation `x = ±y` on `F_ℓ`. -/
def pmSetoid : Setoid (ZMod ℓ) where
  r x y := x = y ∨ x = -y
  iseqv := ⟨fun _ => Or.inl rfl, fun {x y} h => by
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (neg_neg y).symm, fun {x y z} h h' => by
    rcases h with rfl | rfl <;> rcases h' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg z)⟩

/-- **`|F_ℓ| = F_ℓ/{±1}`** (IUT I, Example 4.4(i)). -/
def AbsFl : Type := Quotient (pmSetoid ℓ)

variable {ℓ}

/-- The class `|z|` of `z ∈ F_ℓ`. -/
def AbsFl.mk (z : ZMod ℓ) : AbsFl ℓ := Quotient.mk (pmSetoid ℓ) z

lemma AbsFl.mk_eq_mk {x y : ZMod ℓ} : AbsFl.mk x = AbsFl.mk y ↔ x = y ∨ x = -y :=
  Quotient.eq (r := pmSetoid ℓ)

@[simp] lemma AbsFl.mk_neg (z : ZMod ℓ) : AbsFl.mk (-z) = AbsFl.mk z :=
  AbsFl.mk_eq_mk.mpr (Or.inr rfl)

lemma AbsFl.mk_surjective : Function.Surjective (AbsFl.mk (ℓ := ℓ)) := Quotient.mk_surjective

instance : Zero (AbsFl ℓ) := ⟨AbsFl.mk 0⟩

lemma AbsFl.zero_def : (0 : AbsFl ℓ) = AbsFl.mk 0 := rfl

lemma AbsFl.mk_eq_zero {z : ZMod ℓ} : AbsFl.mk z = 0 ↔ z = 0 := by
  rw [AbsFl.zero_def, AbsFl.mk_eq_mk, neg_zero, or_self]

variable (ℓ)

/-- The affine permutation `z ↦ s·z + c` of `F_ℓ`. -/
def affPerm (s : ℤˣ) (c : ZMod ℓ) : Equiv.Perm (ZMod ℓ) where
  toFun z := sgn ℓ s * z + c
  invFun z := sgn ℓ s * (z - c)
  left_inv z := by
    change sgn ℓ s * (sgn ℓ s * z + c - c) = z
    rw [add_sub_cancel_right, ← mul_assoc, sgn_mul_self, one_mul]
  right_inv z := by
    change sgn ℓ s * (sgn ℓ s * (z - c)) + c = z
    rw [← mul_assoc, sgn_mul_self, one_mul, sub_add_cancel]

variable {ℓ}

@[simp] lemma affPerm_apply (s : ℤˣ) (c z : ZMod ℓ) : affPerm ℓ s c z = sgn ℓ s * z + c := rfl

lemma affPerm_mul (s t : ℤˣ) (c d : ZMod ℓ) :
    affPerm ℓ s c * affPerm ℓ t d = affPerm ℓ (s * t) (sgn ℓ s * d + c) := by
  ext z
  simp only [Equiv.Perm.mul_apply, affPerm_apply, sgn_mul]
  ring

lemma affPerm_one : affPerm ℓ 1 0 = 1 := by
  ext z
  simp

lemma affPerm_inv (s : ℤˣ) (c : ZMod ℓ) :
    (affPerm ℓ s c)⁻¹ = affPerm ℓ s (-(sgn ℓ s * c)) := by
  rw [inv_eq_iff_mul_eq_one, affPerm_mul, Int.units_mul_self]
  convert affPerm_one using 2
  linear_combination (-c) * sgn_mul_self (ℓ := ℓ) s

variable (ℓ)

/-- **`F_ℓ^{⋊±} = F_ℓ ⋊ {±1}`** (IUT I, Definition 6.1(i)): the group of affine permutations
`z ↦ ±z + λ` of `F_ℓ`. -/
def FlSemi : Subgroup (Equiv.Perm (ZMod ℓ)) where
  carrier := {f | ∃ s c, f = affPerm ℓ s c}
  mul_mem' := by
    rintro _ _ ⟨s, c, rfl⟩ ⟨t, d, rfl⟩
    exact ⟨_, _, affPerm_mul s t c d⟩
  one_mem' := ⟨1, 0, affPerm_one.symm⟩
  inv_mem' := by
    rintro _ ⟨s, c, rfl⟩
    exact ⟨_, _, affPerm_inv s c⟩

/-! ### Consequences of `ℓ` being an odd prime -/

variable [OddPrime ℓ]

lemma two_lt : 2 < ℓ := OddPrime.two_lt

lemma prime : ℓ.Prime := OddPrime.prime

lemma odd : Odd ℓ := (prime ℓ).odd_of_ne_two (two_lt ℓ).ne'

lemma two_mul_ellStar : 2 * ellStar ℓ + 1 = ℓ := by
  obtain ⟨k, hk⟩ := odd ℓ
  subst hk
  simp only [ellStar]
  omega

variable {ℓ}

lemma sgn_injective : Function.Injective (sgn ℓ) := by
  intro s t h
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · rfl
  · exact absurd h.symm (by simpa using ZMod.neg_one_ne_one)
  · exact absurd h (by simpa using ZMod.neg_one_ne_one)
  · rfl

variable (ℓ)

/-! ### `F_ℓ^* = F_ℓ^×/{±1}` -/

lemma units_neg_one_ne_one : (-1 : (ZMod ℓ)ˣ) ≠ 1 := by
  intro h
  exact ZMod.neg_one_ne_one (by simpa using congrArg Units.val h)

lemma card_pmSub : Nat.card (pmSub ℓ) = 2 := by
  have : (pmSub ℓ : Set (ZMod ℓ)ˣ) = {1, -1} := by ext u; simp [mem_pmSub]
  rw [← SetLike.coe_sort_coe, this, Nat.card_coe_set_eq]
  exact Set.ncard_pair (units_neg_one_ne_one ℓ).symm

/-- **`F_ℓ^* = F_ℓ^×/{±1}`** (IUT I, §4). -/
abbrev FlStar : Type := (ZMod ℓ)ˣ ⧸ pmSub ℓ

/-- **`|F_ℓ^*| = ℓ*`.** -/
theorem card_flStar : Nat.card (FlStar ℓ) = ellStar ℓ := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pmSub ℓ)
  rw [card_pmSub, Nat.card_eq_fintype_card (α := (ZMod ℓ)ˣ), ZMod.card_units] at h
  have h2 := two_mul_ellStar ℓ
  change Nat.card (FlStar ℓ) = (ℓ - 1) / 2
  change ℓ - 1 = Nat.card (FlStar ℓ) * 2 at h
  change 2 * ((ℓ - 1) / 2) + 1 = ℓ at h2
  omega

instance : Finite (FlStar ℓ) := inferInstance

/-! ### `|F_ℓ| = F_ℓ/{±1}` -/

/-- The minimal representative `min(z.val, (−z).val) ∈ {0, …, ℓ*}`. -/
def repVal (z : ZMod ℓ) : ℕ := if z.val ≤ ellStar ℓ then z.val else (-z).val

lemma val_neg_of_ne_zero {z : ZMod ℓ} (hz : z ≠ 0) : (-z).val = ℓ - z.val := by
  rw [ZMod.neg_val, if_neg hz]

lemma repVal_le (z : ZMod ℓ) : repVal ℓ z ≤ ellStar ℓ := by
  unfold repVal
  split_ifs with h
  · exact h
  · have hz : z ≠ 0 := by rintro rfl; simp at h
    rw [val_neg_of_ne_zero ℓ hz]
    have := two_mul_ellStar ℓ
    have := ZMod.val_lt z
    omega

lemma repVal_neg (z : ZMod ℓ) : repVal ℓ (-z) = repVal ℓ z := by
  by_cases hz : z = 0
  · subst hz; simp
  have hz' : -z ≠ 0 := neg_ne_zero.mpr hz
  have h1 := val_neg_of_ne_zero ℓ hz
  have h2 := two_mul_ellStar ℓ
  have h3 := ZMod.val_lt z
  have h4 : z.val ≠ 0 := (ZMod.val_ne_zero z).mpr hz
  unfold repVal
  rw [neg_neg, h1]
  split_ifs <;> omega

lemma cast_repVal (z : ZMod ℓ) : ((repVal ℓ z : ℕ) : ZMod ℓ) = z ∨
    ((repVal ℓ z : ℕ) : ZMod ℓ) = -z := by
  unfold repVal
  split_ifs
  · exact Or.inl (ZMod.natCast_zmod_val z)
  · exact Or.inr (ZMod.natCast_zmod_val (-z))

lemma repVal_natCast {k : ℕ} (hk : k ≤ ellStar ℓ) : repVal ℓ (k : ZMod ℓ) = k := by
  have h2 := two_mul_ellStar ℓ
  have hk' : k < ℓ := by omega
  unfold repVal
  rw [ZMod.val_natCast_of_lt hk', if_pos hk]

/-- **The minimal representatives `|F_ℓ| ≃ {0, …, ℓ*}`.** -/
def absRep : AbsFl ℓ ≃ Fin (ellPm ℓ) where
  toFun := Quotient.lift (fun z => ⟨repVal ℓ z, Nat.lt_succ_of_le (repVal_le ℓ z)⟩) (by
    rintro x y (rfl | rfl)
    · rfl
    · exact Fin.ext (repVal_neg ℓ y))
  invFun k := AbsFl.mk (k.1 : ZMod ℓ)
  left_inv a := by
    obtain ⟨z, rfl⟩ := AbsFl.mk_surjective a
    change AbsFl.mk ((repVal ℓ z : ℕ) : ZMod ℓ) = AbsFl.mk z
    rcases cast_repVal ℓ z with h | h <;> rw [h]
    exact AbsFl.mk_neg z
  right_inv k := Fin.ext (repVal_natCast ℓ (Nat.le_of_lt_succ k.2))

lemma absRep_mk (z : ZMod ℓ) : (absRep ℓ (AbsFl.mk z) : ℕ) = repVal ℓ z := rfl

lemma absRep_symm_apply (k : Fin (ellPm ℓ)) : (absRep ℓ).symm k = AbsFl.mk (k.1 : ZMod ℓ) :=
  rfl

instance : Fintype (AbsFl ℓ) := Fintype.ofEquiv _ (absRep ℓ).symm

instance : DecidableEq (AbsFl ℓ) := (absRep ℓ).decidableEq

/-- **`||F_ℓ|| = ℓ± = ℓ* + 1`.** -/
theorem card_absFl : Nat.card (AbsFl ℓ) = ellPm ℓ := by
  rw [Nat.card_congr (absRep ℓ), Nat.card_eq_fintype_card, Fintype.card_fin]

lemma absRep_zero : absRep ℓ 0 = 0 := by
  apply Fin.ext
  change repVal ℓ 0 = 0
  simp [repVal]

lemma absRep_eq_zero {a : AbsFl ℓ} : absRep ℓ a = 0 ↔ a = 0 := by
  rw [← absRep_zero, (absRep ℓ).apply_eq_iff_eq]

/-- The natural number `k ≤ ℓ*` as an element of `|F_ℓ|` ("by abuse of notation, we use the
notation for nonnegative integers to denote the images of these nonnegative integers in `|F_ℓ|`",
IUT I, Proposition 6.9(i)). -/
def natAbs (k : ℕ) : AbsFl ℓ := AbsFl.mk (k : ZMod ℓ)

lemma natAbs_injOn {j k : ℕ} (hj : j ≤ ellStar ℓ) (hk : k ≤ ellStar ℓ)
    (h : natAbs ℓ j = natAbs ℓ k) : j = k := by
  have := congrArg (fun a => (absRep ℓ a : ℕ)) h
  simpa [natAbs, absRep_mk, repVal_natCast ℓ hj, repVal_natCast ℓ hk] using this

lemma natAbs_eq_zero {k : ℕ} (hk : k ≤ ellStar ℓ) : natAbs ℓ k = 0 ↔ k = 0 := by
  constructor
  · intro h
    exact natAbs_injOn ℓ hk (Nat.zero_le _) (h.trans (by simp [natAbs, AbsFl.zero_def]))
  · rintro rfl
    simp [natAbs, AbsFl.zero_def]

/-! ### `|F_ℓ| = 0 ∪ F_ℓ^*` -/

/-- The class of a unit in `|F_ℓ|`, well defined on `F_ℓ^*`. -/
def starToAbs : FlStar ℓ → AbsFl ℓ :=
  Quotient.lift (fun u : (ZMod ℓ)ˣ => AbsFl.mk (u : ZMod ℓ)) (by
    intro u v h
    have h : u⁻¹ * v ∈ pmSub ℓ := QuotientGroup.leftRel_apply.mp h
    rw [mem_pmSub] at h
    rcases h with h | h
    · rw [inv_mul_eq_one] at h
      rw [h]
    · have : v = -u := by
        rw [← mul_inv_cancel_left u v, h]
        simp
      rw [this, Units.val_neg, AbsFl.mk_neg])

lemma starToAbs_mk (u : (ZMod ℓ)ˣ) : starToAbs ℓ (u : FlStar ℓ) = AbsFl.mk (u : ZMod ℓ) := rfl

lemma starToAbs_ne_zero (x : FlStar ℓ) : starToAbs ℓ x ≠ 0 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  rw [starToAbs_mk, Ne, AbsFl.mk_eq_zero]
  exact u.ne_zero

lemma starToAbs_injective : Function.Injective (starToAbs ℓ) := by
  intro x y h
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
  rw [starToAbs_mk, starToAbs_mk, AbsFl.mk_eq_mk] at h
  rw [QuotientGroup.eq, mem_pmSub]
  rcases h with h | h
  · left
    rw [Units.ext h, inv_mul_cancel]
  · right
    have : u = -v := Units.ext (by simpa using h)
    rw [this]
    simp

/-- **The nonzero elements of `|F_ℓ|` are `F_ℓ^*`** (`|F_ℓ| = 0 ⊔ F_ℓ^*`, IUT I, Example
4.4(i)). -/
noncomputable def nonzeroAbsEquiv : {a : AbsFl ℓ // a ≠ 0} ≃ FlStar ℓ :=
  (Equiv.ofInjective _ (starToAbs_injective ℓ)).trans
    (Equiv.subtypeEquivRight fun a => by
      constructor
      · rintro ⟨x, rfl⟩
        exact starToAbs_ne_zero ℓ x
      · intro ha
        obtain ⟨z, rfl⟩ := AbsFl.mk_surjective a
        have hz : z ≠ 0 := fun h => ha (by rw [h]; rfl)
        exact ⟨((Units.mk0 z hz : (ZMod ℓ)ˣ) : FlStar ℓ), rfl⟩) |>.symm

lemma starToAbs_nonzeroAbsEquiv (a : {a : AbsFl ℓ // a ≠ 0}) :
    starToAbs ℓ (nonzeroAbsEquiv ℓ a) = a := by
  exact congrArg Subtype.val ((nonzeroAbsEquiv ℓ).symm_apply_apply a)

/-! ### `F_ℓ^{⋊±} = F_ℓ ⋊ {±1}` -/

variable {ℓ} in
lemma affPerm_injective2 {s t : ℤˣ} {c d : ZMod ℓ} (h : affPerm ℓ s c = affPerm ℓ t d) :
    s = t ∧ c = d := by
  have h0 := congrArg (· 0) h
  have h1 := congrArg (· 1) h
  simp only [affPerm_apply, mul_zero, zero_add, mul_one] at h0 h1
  subst h0
  exact ⟨sgn_injective (add_right_cancel h1), rfl⟩

/-- The parametrization `{±1} × F_ℓ ≃ F_ℓ^{⋊±}`, `(s, λ) ↦ (z ↦ s·z + λ)`. -/
noncomputable def flSemiEquiv : ℤˣ × ZMod ℓ ≃ FlSemi ℓ :=
  Equiv.ofBijective (fun p => ⟨affPerm ℓ p.1 p.2, p.1, p.2, rfl⟩)
    ⟨fun p q h => by
      have := affPerm_injective2 (ℓ := ℓ) (congrArg Subtype.val h)
      exact Prod.ext this.1 this.2, fun ⟨_, s, c, h⟩ => ⟨(s, c), Subtype.ext h.symm⟩⟩

@[simp] lemma flSemiEquiv_apply (p : ℤˣ × ZMod ℓ) :
    ((flSemiEquiv ℓ p : FlSemi ℓ) : Equiv.Perm (ZMod ℓ)) = affPerm ℓ p.1 p.2 := rfl

/-- **`|F_ℓ^{⋊±}| = 2ℓ`.** -/
theorem card_flSemi : Nat.card (FlSemi ℓ) = 2 * ℓ := by
  rw [← Nat.card_congr (flSemiEquiv ℓ), Nat.card_prod, Nat.card_eq_fintype_card (α := ℤˣ),
    Nat.card_zmod]
  rfl

/-- **The sign** `F_ℓ^{⋊±} ↠ {±1}` (an element is *positive* or *negative*). -/
noncomputable def FlSemi.sign (g : FlSemi ℓ) : ℤˣ := ((flSemiEquiv ℓ).symm g).1

lemma FlSemi.sign_affPerm (s : ℤˣ) (c : ZMod ℓ) :
    FlSemi.sign ℓ ⟨affPerm ℓ s c, s, c, rfl⟩ = s := by
  unfold FlSemi.sign
  rw [show (⟨affPerm ℓ s c, s, c, rfl⟩ : FlSemi ℓ) = flSemiEquiv ℓ (s, c) from rfl,
    Equiv.symm_apply_apply]

/-- `F_ℓ^{⋊±}` acts on `F_ℓ` **transitively** (IUT I, Proposition 6.8(i)). -/
theorem flSemi_isPretransitive : MulAction.IsPretransitive (FlSemi ℓ) (ZMod ℓ) :=
  ⟨fun a b => ⟨⟨affPerm ℓ 1 (b - a), 1, b - a, rfl⟩, by
    change affPerm ℓ 1 (b - a) a = b
    simp⟩⟩

/-- **The stabilizers of `F_ℓ^{⋊±} ↷ F_ℓ` have order two** (IUT I, Proposition 6.8(i): the action
is "doubly transitive", i.e. transitive with stabilizers of order two). -/
theorem card_stabilizer_flSemi (a : ZMod ℓ) :
    Nat.card (MulAction.stabilizer (FlSemi ℓ) a) = 2 := by
  have e : MulAction.stabilizer (FlSemi ℓ) a ≃ ℤˣ :=
    { toFun g := FlSemi.sign ℓ g.1
      invFun s := ⟨flSemiEquiv ℓ (s, a - sgn ℓ s * a), by
        rw [MulAction.mem_stabilizer_iff]
        change affPerm ℓ s (a - sgn ℓ s * a) a = a
        simp⟩
      left_inv g := by
        obtain ⟨⟨_, s, c, rfl⟩, hg⟩ := g
        rw [MulAction.mem_stabilizer_iff] at hg
        change affPerm ℓ s c a = a at hg
        simp only [affPerm_apply] at hg
        apply Subtype.ext
        apply Subtype.ext
        simp only [FlSemi.sign_affPerm, flSemiEquiv_apply]
        congr 1
        linear_combination -hg
      right_inv s := by
        change ((flSemiEquiv ℓ).symm (flSemiEquiv ℓ (s, _))).1 = s
        rw [Equiv.symm_apply_apply] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  rfl

/-! ### `F_ℓ^±`-torsors and `F_ℓ^±`-groups -/

/-- **An `F_ℓ^±`-torsor** (IUT I, Definition 6.1(i)): a set with an `F_ℓ^{⋊±}`-orbit of bijections
to `F_ℓ`, recorded by one chart of the orbit. -/
structure PmTorsor where
  /-- The underlying set. -/
  carrier : Type
  /-- A chart of the orbit of charts. -/
  chart : carrier ≃ ZMod ℓ

/-- **An `F_ℓ^±`-group** (IUT I, Definition 6.1(i)): a set with a `{±1}`-orbit of bijections to
`F_ℓ`, recorded by one chart of the orbit. It has a natural `F_ℓ^±`-torsor structure (the same
chart). -/
abbrev PmGroup := PmTorsor ℓ

/-- `F_ℓ` with its tautological structure. -/
@[reducible] def PmTorsor.std : PmTorsor ℓ := ⟨ZMod ℓ, Equiv.refl _⟩

variable {ℓ}

/-- **An isomorphism of `F_ℓ^±`-torsors**: a bijection which, in the charts, is an affine map
`z ↦ s·z + λ` (`s = sign`, `λ = shift`). -/
structure PmTorsor.Iso (A B : PmTorsor ℓ) where
  /-- The underlying bijection. -/
  toEquiv : A.carrier ≃ B.carrier
  /-- The sign `s ∈ {±1}`. -/
  sign : ℤˣ
  /-- The shift `λ ∈ F_ℓ`. -/
  shift : ZMod ℓ
  chart_apply : ∀ a, B.chart (toEquiv a) = sgn ℓ sign * A.chart a + shift

namespace PmTorsor

variable {A B C : PmTorsor ℓ}

instance : CoeFun (Iso A B) fun _ => A.carrier → B.carrier := ⟨fun f => f.toEquiv⟩

/-- The zero of an `F_ℓ^±`-group. -/
def zero (A : PmGroup ℓ) : A.carrier := A.chart.symm 0

@[simp] lemma chart_zero (A : PmGroup ℓ) : A.chart A.zero = 0 := by simp [zero]

/-- The isomorphism with given sign and shift. -/
def Iso.mk' (A B : PmTorsor ℓ) (s : ℤˣ) (c : ZMod ℓ) : Iso A B where
  toEquiv := A.chart.trans ((affPerm ℓ s c).trans B.chart.symm)
  sign := s
  shift := c
  chart_apply a := by simp

/-- An isomorphism is determined by its sign and shift. -/
lemma Iso.ext_sign {f g : Iso A B} (hs : f.sign = g.sign) (hc : f.shift = g.shift) : f = g := by
  obtain ⟨f, s, c, hf⟩ := f
  obtain ⟨g, t, d, hg⟩ := g
  simp only at hs hc
  subst hs hc
  have : f = g := Equiv.ext fun a => B.chart.injective (by rw [hf, hg])
  subst this
  rfl

/-- **For `ℓ` odd, an isomorphism is determined by its underlying bijection.** -/
lemma Iso.ext {f g : Iso A B} (h : ∀ a, f a = g a) : f = g := by
  have key : affPerm ℓ f.sign f.shift = affPerm ℓ g.sign g.shift := by
    ext z
    obtain ⟨a, rfl⟩ := A.chart.surjective z
    simp only [affPerm_apply]
    rw [← f.chart_apply, ← g.chart_apply]
    exact congrArg B.chart (h a)
  obtain ⟨h1, h2⟩ := affPerm_injective2 key
  exact Iso.ext_sign h1 h2

/-- The identity. -/
def Iso.refl (A : PmTorsor ℓ) : Iso A A where
  toEquiv := Equiv.refl _
  sign := 1
  shift := 0
  chart_apply a := by simp

/-- The composite. -/
def Iso.trans (f : Iso A B) (g : Iso B C) : Iso A C where
  toEquiv := f.toEquiv.trans g.toEquiv
  sign := g.sign * f.sign
  shift := sgn ℓ g.sign * f.shift + g.shift
  chart_apply a := by
    simp only [Equiv.trans_apply]
    rw [g.chart_apply, f.chart_apply, sgn_mul]
    ring

/-- The inverse. -/
def Iso.symm (f : Iso A B) : Iso B A where
  toEquiv := f.toEquiv.symm
  sign := f.sign
  shift := -(sgn ℓ f.sign * f.shift)
  chart_apply b := by
    obtain ⟨a, rfl⟩ := f.toEquiv.surjective b
    rw [Equiv.symm_apply_apply, f.chart_apply, mul_add, ← mul_assoc, sgn_mul_self, one_mul]
    ring

@[simp] lemma Iso.refl_apply (a : A.carrier) : Iso.refl A a = a := rfl

@[simp] lemma Iso.trans_apply (f : Iso A B) (g : Iso B C) (a : A.carrier) :
    f.trans g a = g (f a) := rfl

@[simp] lemma Iso.symm_apply_apply (f : Iso A B) (a : A.carrier) : f.symm (f a) = a :=
  f.toEquiv.symm_apply_apply a

@[simp] lemma Iso.apply_symm_apply (f : Iso A B) (b : B.carrier) : f (f.symm b) = b :=
  f.toEquiv.apply_symm_apply b

@[simp] lemma Iso.trans_sign (f : Iso A B) (g : Iso B C) : (f.trans g).sign = g.sign * f.sign :=
  rfl

@[simp] lemma Iso.symm_sign (f : Iso A B) : f.symm.sign = f.sign := rfl

/-- The parametrization of the isomorphisms by sign and shift. -/
def isoEquiv (A B : PmTorsor ℓ) : Iso A B ≃ ℤˣ × ZMod ℓ where
  toFun f := (f.sign, f.shift)
  invFun p := Iso.mk' A B p.1 p.2
  left_inv _ := Iso.ext_sign rfl rfl
  right_inv _ := rfl

/-- **The isomorphisms of two `F_ℓ^±`-torsors form an `F_ℓ^{⋊±}`-torsor** (IUT I, Proposition
6.6(ii) at the level of index sets). -/
noncomputable def isoEquivSemi (A B : PmTorsor ℓ) : Iso A B ≃ FlSemi ℓ :=
  (isoEquiv A B).trans (flSemiEquiv ℓ)

theorem card_iso (A B : PmTorsor ℓ) : Nat.card (Iso A B) = 2 * ℓ := by
  rw [Nat.card_congr (isoEquivSemi A B), card_flSemi]

/-! #### Isomorphisms of `F_ℓ^±`-groups -/

/-- **An isomorphism of `F_ℓ^±`-groups**: an isomorphism with shift `0`. -/
def GrpIso (A B : PmGroup ℓ) : Type := {f : Iso A B // f.shift = 0}

/-- An isomorphism of torsors between `F_ℓ^±`-groups is one of groups iff it preserves zero. -/
lemma shift_eq_zero_iff (f : Iso A B) : f.shift = 0 ↔ f A.zero = B.zero := by
  rw [← B.chart.injective.eq_iff, f.chart_apply, chart_zero, chart_zero, mul_zero, zero_add]

/-- **The isomorphisms of two `F_ℓ^±`-groups form a `{±1}`-torsor** (IUT I, Definition 6.1(i),
Proposition 6.6(i), (iii) at the level of index sets). -/
def GrpIso.equiv (A B : PmGroup ℓ) : GrpIso A B ≃ ℤˣ where
  toFun f := f.1.sign
  invFun s := ⟨Iso.mk' A B s 0, rfl⟩
  left_inv f := Subtype.ext (Iso.ext_sign rfl f.2.symm)
  right_inv _ := rfl

theorem card_grpIso (A B : PmGroup ℓ) : Nat.card (GrpIso A B) = 2 := by
  rw [Nat.card_congr (GrpIso.equiv A B), Nat.card_eq_fintype_card]
  rfl

/-- The identity isomorphism of groups. -/
def GrpIso.refl (A : PmGroup ℓ) : GrpIso A A := ⟨Iso.refl A, rfl⟩

/-- The composite isomorphism of groups. -/
def GrpIso.trans (f : GrpIso A B) (g : GrpIso B C) : GrpIso A C :=
  ⟨f.1.trans g.1, by simp [Iso.trans, f.2, g.2]⟩

/-- The inverse isomorphism of groups. -/
def GrpIso.symm (f : GrpIso A B) : GrpIso B A := ⟨f.1.symm, by simp [Iso.symm, f.2]⟩

/-- **Positive automorphisms** (IUT I, Definition 6.1(i)): sign `+1`. -/
def Iso.IsPositive (f : Iso A B) : Prop := f.sign = 1

/-- A positive isomorphism is determined by the image of one point. -/
lemma Iso.eq_of_isPositive {f g : Iso A B} (hf : f.IsPositive) (hg : g.IsPositive) (a : A.carrier)
    (h : f a = g a) : f = g := by
  have h' := congrArg B.chart h
  rw [f.chart_apply, g.chart_apply, hf, hg, add_right_inj] at h'
  exact Iso.ext_sign (hf.trans hg.symm) h'

/-- A torsor isomorphism between groups preserving zero is a group isomorphism. -/
def Iso.toGrpIso {A B : PmGroup ℓ} (f : Iso A B) (h : f A.zero = B.zero) : GrpIso A B :=
  ⟨f, (shift_eq_zero_iff f).mpr h⟩

end PmTorsor

/-! ### `F_ℓ^*`-torsors -/

variable (ℓ)

/-- **An `F_ℓ^*`-torsor** (IUT I, Definition 4.1(ii): `LabCusp(†D_v)` is an `F_ℓ^*`-torsor),
recorded by one chart of its orbit of charts. -/
structure StarTorsor where
  /-- The underlying set. -/
  carrier : Type
  /-- A chart. -/
  chart : carrier ≃ FlStar ℓ

/-- `F_ℓ^*` with its tautological structure. -/
@[reducible] def StarTorsor.std : StarTorsor ℓ := ⟨FlStar ℓ, Equiv.refl _⟩

variable {ℓ}

/-- **An isomorphism of `F_ℓ^*`-torsors**: in the charts, multiplication by `g ∈ F_ℓ^*`. -/
structure StarTorsor.Iso (A B : StarTorsor ℓ) where
  /-- The underlying bijection. -/
  toEquiv : A.carrier ≃ B.carrier
  /-- The multiplier. -/
  mult : FlStar ℓ
  chart_apply : ∀ a, B.chart (toEquiv a) = mult * A.chart a

namespace StarTorsor

variable {A B C : StarTorsor ℓ}

instance : CoeFun (Iso A B) fun _ => A.carrier → B.carrier := ⟨fun f => f.toEquiv⟩

lemma Iso.ext_mult {f g : Iso A B} (h : f.mult = g.mult) : f = g := by
  obtain ⟨f, m, hf⟩ := f
  obtain ⟨g, n, hg⟩ := g
  simp only at h
  subst h
  have : f = g := Equiv.ext fun a => B.chart.injective (by rw [hf, hg])
  subst this
  rfl

/-- An isomorphism is determined by its underlying bijection. -/
lemma Iso.ext {f g : Iso A B} (h : ∀ a, f a = g a) : f = g := by
  obtain ⟨a⟩ : Nonempty A.carrier := ⟨A.chart.symm 1⟩
  apply Iso.ext_mult
  have := congrArg B.chart (h a)
  rw [f.chart_apply, g.chart_apply] at this
  exact mul_right_cancel this

/-- The isomorphism with multiplier `g`. -/
def Iso.mk' (A B : StarTorsor ℓ) (g : FlStar ℓ) : Iso A B where
  toEquiv := A.chart.trans ((Equiv.mulLeft g).trans B.chart.symm)
  mult := g
  chart_apply a := by simp

/-- The identity. -/
def Iso.refl (A : StarTorsor ℓ) : Iso A A := ⟨Equiv.refl _, 1, fun a => by simp⟩

/-- The composite. -/
def Iso.trans (f : Iso A B) (g : Iso B C) : Iso A C :=
  ⟨f.toEquiv.trans g.toEquiv, g.mult * f.mult, fun a => by
    simp only [Equiv.trans_apply]
    rw [g.chart_apply, f.chart_apply, mul_assoc]⟩

/-- The inverse. -/
def Iso.symm (f : Iso A B) : Iso B A :=
  ⟨f.toEquiv.symm, f.mult⁻¹, fun b => by
    obtain ⟨a, rfl⟩ := f.toEquiv.surjective b
    rw [Equiv.symm_apply_apply, f.chart_apply, inv_mul_cancel_left]⟩

@[simp] lemma Iso.trans_apply (f : Iso A B) (g : Iso B C) (a : A.carrier) :
    f.trans g a = g (f a) := rfl

@[simp] lemma Iso.symm_apply_apply (f : Iso A B) (a : A.carrier) : f.symm (f a) = a :=
  f.toEquiv.symm_apply_apply a

@[simp] lemma Iso.apply_symm_apply (f : Iso A B) (b : B.carrier) : f (f.symm b) = b :=
  f.toEquiv.apply_symm_apply b

/-- **The isomorphisms of two `F_ℓ^*`-torsors form an `F_ℓ^*`-torsor.** -/
def isoEquiv (A B : StarTorsor ℓ) : Iso A B ≃ FlStar ℓ where
  toFun f := f.mult
  invFun g := Iso.mk' A B g
  left_inv _ := Iso.ext_mult rfl
  right_inv _ := rfl

theorem card_iso (A B : StarTorsor ℓ) : Nat.card (Iso A B) = ellStar ℓ := by
  rw [Nat.card_congr (isoEquiv A B), card_flStar]

/-- An isomorphism of torsors is determined by the image of one point. -/
lemma Iso.eq_of_apply_eq {f g : Iso A B} (a : A.carrier) (h : f a = g a) : f = g := by
  apply Iso.ext_mult
  have := congrArg B.chart h
  rw [f.chart_apply, g.chart_apply] at this
  exact mul_right_cancel this

/-- There is a (unique) isomorphism carrying a given point to a given point. -/
def Iso.ofPoints (A B : StarTorsor ℓ) (a : A.carrier) (b : B.carrier) : Iso A B :=
  Iso.mk' A B (B.chart b * (A.chart a)⁻¹)

@[simp] lemma Iso.ofPoints_apply (a : A.carrier) (b : B.carrier) : Iso.ofPoints A B a b a = b := by
  apply B.chart.injective
  rw [(Iso.ofPoints A B a b).chart_apply]
  simp [Iso.ofPoints, Iso.mk']

end StarTorsor

end HodgeTheater

end Iut
