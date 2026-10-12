/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Discrete rigidity and `ℤ`-torsors ([EtTh], Prop. 2.15)

[EtTh], Prop. 2.15 considers the category `T` whose objects `T_M` (`M ≥ 1`) are copies of `ℤ`
(thought of as `ℤ`-torsors) and whose morphisms `T_{M'} → T_M` (`M ∣ M'`) are the identity
`ℤ → ℤ` composed with a translation by an element of `M·ℤ`; and projective systems
(`E`-systems) in `T` indexed by a cofinal, totally ordered (for divisibility) subset
`1 ∈ E ⊆ ℕ_{≥1}`. Such an `E` is a chain `1 = e₀ ∣ e₁ ∣ e₂ ∣ ⋯`; we index it by `ℕ`
(`Chain`). A morphism `T_{M'} → T_M` is recorded by its translation amount (`∈ M·ℤ`).

* (i) `aut_transport`: an automorphism of `T_{M'}` (a translation by `a' ∈ M'ℤ`) and an
  automorphism of `T_M` (by `a`) are compatible with a morphism `T_{M'} → T_M` iff `a = a'`: the
  induced map `Aut(T_{M'}) = M'ℤ → Mℤ = Aut(T_M)` is the inclusion.
* (ii) `iso_of_level_one` (**piecewise rigid**): any two `E`-systems all of whose objects are
  `T_1` are isomorphic.
* (iii) `jInv` (**piecewise non-rigid I**): for systems with objects `T_{e_n}`, the elements
  `j^S_n = β_{n,0}(0) ∈ T_1 = ℤ` form a compatible system of residues mod `e_n`
  (`jInv_compat`), i.e. an element `j^S_∞ ∈ Ẑ`; every compatible system arises
  (`exists_jInv_eq`), and isomorphic systems have the same image in `Ẑ/ℤ` (`jInv_of_iso`).
* (iv) `exists_not_iso` (**piecewise non-rigid II**): for the chain `e_n = (n+1)!` there are
  non-isomorphic systems — the profinite `j_∞ = ∑ₖ (k+1)!` is not an integer.

This is the combinatorial input of discrete rigidity ([EtTh], Cor. 2.19(ii)): working with
mono-theta environments (rather than bi-theta environments) the labels form an `E`-system on
`T_1`, which is rigid, so no profinite (`Ẑ`) indeterminacy arises.
-/

namespace Iut.EtaleTheta.DiscreteRigidity

/-- A cofinal chain `1 = e₀ ∣ e₁ ∣ ⋯` in `(ℕ_{≥1}, ∣)`, i.e. the set `E` of [EtTh],
Prop. 2.15. -/
structure Chain where
  /-- The chain. -/
  e : ℕ → ℕ
  e_zero : e 0 = 1
  pos : ∀ n, 0 < e n
  dvd_succ : ∀ n, e n ∣ e (n + 1)
  cofinal : ∀ m, 0 < m → ∃ n, m ∣ e n

namespace Chain

variable (E : Chain)

lemma dvd_of_le {n n' : ℕ} (h : n ≤ n') : E.e n ∣ E.e n' := by
  induction h with
  | refl => exact dvd_rfl
  | step _ ih => exact ih.trans (E.dvd_succ _)

end Chain

/-! ### (i) Automorphisms -/

/-- **[EtTh], Prop. 2.15(i)**: for a morphism `T_{M'} → T_M` (translation by `c`), translations
`a` of `T_M` and `a'` of `T_{M'}` are compatible (`a ∘ c = c ∘ a'`) iff `a = a'`. Hence the
injection `Aut(T_{M'}) = M'ℤ ↪ Mℤ = Aut(T_M)` is the natural inclusion. -/
theorem aut_transport (c a a' : ℤ) :
    ((fun x : ℤ => x + a) ∘ (fun x => x + c)) = ((fun x => x + c) ∘ (fun x => x + a')) ↔
      a = a' := by
  constructor
  · intro h
    have := congrFun h 0
    simp only [Function.comp_apply, zero_add] at this
    linarith
  · rintro rfl
    funext x
    simp only [Function.comp_apply]
    ring

/-! ### `E`-systems -/

/-- An `E`-system ([EtTh], Prop. 2.15) with objects `S_n = T_{lev n}`: the transition maps
`β_{n',n} : S_{n'} → S_n` (`n ≤ n'`) are translations by `β n' n ∈ (lev n)·ℤ`, compatible with
composition. -/
structure ESystem (E : Chain) (lev : ℕ → ℕ) where
  /-- The translation amount of `β_{n',n}`. -/
  β : ℕ → ℕ → ℤ
  dvd : ∀ n n', n ≤ n' → (lev n : ℤ) ∣ β n' n
  comp : ∀ n n' n'', n ≤ n' → n' ≤ n'' → β n'' n = β n'' n' + β n' n

variable {E : Chain} {lev : ℕ → ℕ}

/-- An isomorphism of `E`-systems: automorphisms `α_n ∈ (lev n)·ℤ` of `S_n = S'_n` with
`α_n ∘ β_{n',n} = β'_{n',n} ∘ α_{n'}`. -/
def ESystem.Iso (S S' : ESystem E lev) : Prop :=
  ∃ α : ℕ → ℤ, (∀ n, (lev n : ℤ) ∣ α n) ∧
    ∀ n n', n ≤ n' → α n + S.β n' n = S'.β n' n + α n'

/-- **[EtTh], Prop. 2.15(ii) (piecewise rigid `E`-systems)**: any two `E`-systems all of whose
objects are `T_1` are isomorphic. -/
theorem iso_of_level_one (S S' : ESystem E (fun _ => 1)) : S.Iso S' := by
  refine ⟨fun n => S.β n 0 - S'.β n 0, fun _ => by simp, fun n n' h => ?_⟩
  have h1 := S.comp 0 n n' (Nat.zero_le _) h
  have h2 := S'.comp 0 n n' (Nat.zero_le _) h
  linarith

/-! ### (iii) The invariant `j^S_∞` -/

/-- `j^S_n = β_{n,0}(0) ∈ T_1 = ℤ` ([EtTh], Prop. 2.15(iii)). -/
def jInv (S : ESystem E E.e) (n : ℕ) : ℤ := S.β n 0

/-- The `j^S_n` form a compatible system of residues: `j^S_{n'} ≡ j^S_n mod e_n`, i.e. they
converge in `Ẑ`. -/
theorem jInv_compat (S : ESystem E E.e) {n n' : ℕ} (h : n ≤ n') :
    (E.e n : ℤ) ∣ jInv S n' - jInv S n := by
  unfold jInv
  rw [S.comp 0 n n' (Nat.zero_le _) h, add_sub_cancel_right]
  exact S.dvd n n' h

/-- **Surjectivity of `S ↦ j^S_∞`** ([EtTh], Prop. 2.15(iii)): every compatible system of
residues `j` (with `j 0 = 0`) is `j^S` for some `E`-system with objects `T_{e_n}`. -/
theorem exists_jInv_eq (j : ℕ → ℤ) (hj0 : j 0 = 0)
    (hj : ∀ n n', n ≤ n' → (E.e n : ℤ) ∣ j n' - j n) :
    ∃ S : ESystem E E.e, jInv S = j := by
  refine ⟨⟨fun n' n => j n' - j n, fun n n' h => hj n n' h, fun _ _ _ _ _ => by ring⟩, ?_⟩
  funext n
  simp [jInv, hj0]

/-- **Isomorphic `E`-systems have the same `j_∞` in `Ẑ/ℤ`** ([EtTh], Prop. 2.15(iii)). -/
theorem jInv_of_iso {S S' : ESystem E E.e} (h : S.Iso S') :
    ∃ c : ℤ, ∀ n, (E.e n : ℤ) ∣ jInv S n - jInv S' n - c := by
  obtain ⟨α, hα, hcomm⟩ := h
  refine ⟨-α 0, fun n => ?_⟩
  have := hcomm 0 n (Nat.zero_le n)
  have e : jInv S n - jInv S' n - -α 0 = α n := by unfold jInv; linarith
  rw [e]
  exact hα n

/-! ### (iv) Non-isomorphic systems -/

/-- The factorial chain `e_n = (n+1)!`. -/
def factorialChain : Chain where
  e n := (n + 1).factorial
  e_zero := rfl
  pos n := Nat.factorial_pos _
  dvd_succ n := Nat.factorial_dvd_factorial (by omega)
  cofinal m hm := ⟨m, (Nat.dvd_factorial hm le_rfl).trans
    (Nat.factorial_dvd_factorial (by omega))⟩

/-- `jF n = ∑_{k<n} (k+1)!`, a compatible system of residues for the factorial chain whose
limit in `Ẑ` is not an integer. -/
def jF (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, ((k + 1).factorial : ℤ)

lemma jF_succ (n : ℕ) : jF (n + 1) = jF n + ((n + 1).factorial : ℤ) := by
  simp [jF, Finset.sum_range_succ]

lemma jF_nonneg (n : ℕ) : 0 ≤ jF n := Finset.sum_nonneg fun _ _ => by positivity

lemma jF_lt (n : ℕ) : jF n < ((n + 1).factorial : ℤ) := by
  induction n with
  | zero => simp [jF]
  | succ k ih =>
    rw [jF_succ]
    have h : ((k + 1 + 1).factorial : ℤ) = (k + 2) * ((k + 1).factorial : ℤ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [h]
    have h0 : (0 : ℤ) ≤ ((k + 1).factorial : ℤ) := by positivity
    have hk : (0 : ℤ) ≤ k := by positivity
    nlinarith [mul_nonneg hk h0]

lemma jF_compat (n n' : ℕ) (h : n ≤ n') :
    ((n + 1).factorial : ℤ) ∣ jF n' - jF n := by
  induction h with
  | refl => simp
  | step hle ih =>
    rw [jF_succ, show ∀ a b c : ℤ, a + b - c = (a - c) + b by intros; ring]
    exact dvd_add ih
      (Int.natCast_dvd_natCast.2 (Nat.factorial_dvd_factorial (Nat.succ_le_succ hle)))

/-- `j_∞ = ∑ₖ (k+1)!` is not an integer: no `c` with `(n+1)! ∣ jF n - c` for all `n`. -/
theorem jF_not_integer (c : ℤ) : ¬ ∀ n, ((n + 1).factorial : ℤ) ∣ jF n - c := by
  intro hc
  -- at a level with `(m+1)! > |c|`, the residue `jF m - c` is `0` or `(m+1)!`
  have key : ∀ m, |c| < ((m + 1).factorial : ℤ) →
      jF m - c = 0 ∨ jF m - c = ((m + 1).factorial : ℤ) := by
    intro m hm
    obtain ⟨k, hk⟩ := hc m
    have hF : (0 : ℤ) < ((m + 1).factorial : ℤ) := by positivity
    have h0 := jF_nonneg m
    have h1 := jF_lt m
    have hab := abs_lt.1 hm
    have hk1 : k < 2 := by
      by_contra hk'
      have : (2 : ℤ) ≤ k := by omega
      nlinarith [mul_le_mul_of_nonneg_left this hF.le]
    have hk2 : 0 ≤ k := by
      by_contra hk'
      have : k ≤ -1 := by omega
      nlinarith [mul_le_mul_of_nonneg_left this hF.le]
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · left; simpa using hk
    · right; simpa using hk
  -- choose `n ≥ 1` with `(n+1)! > |c|`
  set n := c.natAbs + 1 with hn_def
  have hn : |c| < ((n + 1).factorial : ℤ) := by
    have h1 : c.natAbs < n + 1 := by omega
    have h2 : n + 1 ≤ (n + 1).factorial := Nat.self_le_factorial _
    rw [Int.abs_eq_natAbs]
    exact_mod_cast lt_of_lt_of_le h1 h2
  have hn1 : |c| < ((n + 1 + 1).factorial : ℤ) :=
    lt_of_lt_of_le hn (by exact_mod_cast Nat.factorial_le (by omega))
  have hF : (0 : ℤ) < ((n + 1).factorial : ℤ) := by positivity
  have hsucc := jF_succ n
  have hF2 : ((n + 1 + 1).factorial : ℤ) = (n + 2) * ((n + 1).factorial : ℤ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hn0 : (1 : ℤ) ≤ n := by omega
  rcases key n hn with h | h <;> rcases key (n + 1) hn1 with h' | h'
  · linarith
  · nlinarith
  · linarith
  · nlinarith

/-- **[EtTh], Prop. 2.15(iv) (piecewise non-rigid `E`-systems II)**: for the factorial chain
there are `E`-systems with the same objects `T_{e_n}` that are not isomorphic. -/
theorem exists_not_iso :
    ∃ S S' : ESystem factorialChain factorialChain.e, ¬ S.Iso S' := by
  obtain ⟨S, hS⟩ := exists_jInv_eq (E := factorialChain) jF (by simp [jF])
    (fun n n' h => jF_compat n n' h)
  obtain ⟨S', hS'⟩ := exists_jInv_eq (E := factorialChain) (fun _ => 0) rfl
    (fun _ _ _ => by simp)
  refine ⟨S, S', fun hiso => ?_⟩
  obtain ⟨c, hc⟩ := jInv_of_iso hiso
  apply jF_not_integer c
  intro n
  have := hc n
  rw [hS, hS'] at this
  simpa [factorialChain] using this

end Iut.EtaleTheta.DiscreteRigidity
