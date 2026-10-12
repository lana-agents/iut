/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

/-!
# The theta group and the commutator pairing ([EtTh], §2, Prop. 2.12)

The theta quotient `Δ^Θ` of the geometric tempered fundamental group of the Tate curve is a
central extension
```
1 → Δ_Θ → Δ^Θ → Δ^ell → 1,      Δ^ell ≅ Ẑ(1) × ℤ,
```
of the abelian group `Δ^ell` — the cyclotome `(Δ^tp_Y)^ell ≅ Ẑ(1)` of the `ℤ`-covering `Y` times
`Gal(Y/X) ≅ ℤ` — by a second copy `Δ_Θ` of the cyclotome, and its commutator pairing
`Δ^ell × Δ^ell → Δ_Θ` identifies the two cyclotomes ([EtTh], Prop. 1.5, Prop. 2.12,
"the well-known structure of the theta-group"). This is the mechanism behind cyclotomic
rigidity ([EtTh], Cor. 2.19(i)).

We model it by the Heisenberg group `ThetaGroup M l`: triples `(c, a, b) ∈ M × M × ℤ`, `M` the
cyclotome (an additive group, e.g. `Ẑ(1)` or `μ_N` written additively), with
```
(c, a, b)·(c', a', b') = (c + c' + (l·b)·a', a + a', b + b').
```
The parameter `l` records that the `ℤ`-part is the group `l·ℤ` of the `l`-th root covering of
[EtTh], §2 (for `l = 1` this is the theta group of `Y → X` itself).

## Main results

* `ThetaGroup.commutator_eq`: `[(c,a,b), (c',a',b')] = (l·(b·a' - b'·a), 0, 0)`.
* `ThetaGroup.mem_center_iff`: for torsion-free nontrivial `M` and `l ≠ 0` the center is
  `Δ_Θ = {(c, 0, 0)}`.
* `ThetaGroup.commutator_eq_theta`: **[EtTh], Prop. 2.12(i)**: the commutator subgroup is
  `l·Δ_Θ`.
* `ThetaGroup.cyclotomicRigidity`: **the algebraic core of cyclotomic rigidity** ([EtTh],
  Cor. 2.19(i), Prop. 2.14(i)): a homomorphism of theta groups inducing `α` on the `ell`-cyclotome
  and sending the generator of the `ℤ`-part to an element of `ℤ`-degree `ε` acts on `l·Δ_Θ` by
  `ε·α` (rescaled by `l'`). In particular the isomorphism of cyclotomes `a ↦ [t, a]` given by the
  commutator pairing is preserved by every automorphism fixing the `ℤ`-labels
  (`cyclotomicRigidity_aut`).
-/

namespace Iut.EtaleTheta

open scoped commutatorElement

/-- The Heisenberg model of the theta quotient `Δ^Θ` ([EtTh], §2): the `Δ_Θ`-component `c`, the
`ell`-cyclotome component `a` and the `ℤ`-component `b`. -/
@[ext]
structure ThetaGroup (M : Type*) [AddCommGroup M] (l : ℤ) where
  /-- The component in the central cyclotome `Δ_Θ`. -/
  c : M
  /-- The component in the cyclotome `(Δ_Y)^ell` of the `ℤ`-covering. -/
  a : M
  /-- The component in `Gal(Y/X) ≅ ℤ` (acting through `l·ℤ`). -/
  b : ℤ

namespace ThetaGroup

variable {M : Type*} [AddCommGroup M] {l : ℤ}

instance : Mul (ThetaGroup M l) :=
  ⟨fun x y => ⟨x.c + y.c + (l * x.b) • y.a, x.a + y.a, x.b + y.b⟩⟩

instance : One (ThetaGroup M l) := ⟨⟨0, 0, 0⟩⟩

instance : Inv (ThetaGroup M l) := ⟨fun x => ⟨-x.c + (l * x.b) • x.a, -x.a, -x.b⟩⟩

@[simp] lemma mul_c (x y : ThetaGroup M l) : (x * y).c = x.c + y.c + (l * x.b) • y.a := rfl
@[simp] lemma mul_a (x y : ThetaGroup M l) : (x * y).a = x.a + y.a := rfl
@[simp] lemma mul_b (x y : ThetaGroup M l) : (x * y).b = x.b + y.b := rfl
@[simp] lemma one_c : (1 : ThetaGroup M l).c = 0 := rfl
@[simp] lemma one_a : (1 : ThetaGroup M l).a = 0 := rfl
@[simp] lemma one_b : (1 : ThetaGroup M l).b = 0 := rfl
@[simp] lemma inv_c (x : ThetaGroup M l) : x⁻¹.c = -x.c + (l * x.b) • x.a := rfl
@[simp] lemma inv_a (x : ThetaGroup M l) : x⁻¹.a = -x.a := rfl
@[simp] lemma inv_b (x : ThetaGroup M l) : x⁻¹.b = -x.b := rfl

instance : Group (ThetaGroup M l) where
  mul_assoc x y z := by
    ext
    · simp only [mul_c, mul_b, mul_a]
      rw [mul_add, add_smul, smul_add]
      abel
    · simp [add_assoc]
    · simp [add_assoc]
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by
    ext
    · simp only [mul_c, inv_c, inv_b, one_c]
      rw [mul_neg, neg_smul]
      abel
    · simp
    · simp

/-- The central cyclotome `Δ_Θ ↪ Δ^Θ`. -/
def ιΘ : Multiplicative M →* ThetaGroup M l where
  toFun c := ⟨c.toAdd, 0, 0⟩
  map_one' := rfl
  map_mul' x y := by ext <;> simp

/-- The `ell`-cyclotome `(Δ_Y)^ell` (a subgroup, since the cocycle vanishes on it). -/
def ιell : Multiplicative M →* ThetaGroup M l where
  toFun a := ⟨0, a.toAdd, 0⟩
  map_one' := rfl
  map_mul' x y := by ext <;> simp

/-- The generator of the `ℤ`-part (`Gal(Y/X)`, acting through `l·ℤ`). -/
def tgen : ThetaGroup M l := ⟨0, 0, 1⟩

@[simp] lemma ιΘ_c (c : M) : (ιΘ (l := l) (Multiplicative.ofAdd c)).c = c := rfl
@[simp] lemma ιΘ_a (c : M) : (ιΘ (l := l) (Multiplicative.ofAdd c)).a = 0 := rfl
@[simp] lemma ιΘ_b (c : M) : (ιΘ (l := l) (Multiplicative.ofAdd c)).b = 0 := rfl
@[simp] lemma ιell_c (a : M) : (ιell (l := l) (Multiplicative.ofAdd a)).c = 0 := rfl
@[simp] lemma ιell_a (a : M) : (ιell (l := l) (Multiplicative.ofAdd a)).a = a := rfl
@[simp] lemma ιell_b (a : M) : (ιell (l := l) (Multiplicative.ofAdd a)).b = 0 := rfl

/-- **The commutator pairing**: `[(c,a,b), (c',a',b')] = (l·(b·a' - b'·a), 0, 0)`. -/
theorem commutator_eq (x y : ThetaGroup M l) :
    ⁅x, y⁆ = ⟨l • (x.b • y.a - y.b • x.a), 0, 0⟩ := by
  rw [commutatorElement_def]
  ext
  · simp only [mul_c, inv_c, mul_b, inv_b, inv_a]
    simp only [mul_add, mul_neg, add_smul, neg_smul, smul_neg, smul_sub, mul_smul]
    abel
  · simp
  · simp

lemma commutator_eq_ιΘ (x y : ThetaGroup M l) :
    ⁅x, y⁆ = ιΘ (Multiplicative.ofAdd (l • (x.b • y.a - y.b • x.a))) :=
  commutator_eq x y

/-- The commutator of the generator `t` of the `ℤ`-part with `a ∈ (Δ_Y)^ell` is `l·a ∈ Δ_Θ`:
the isomorphism of cyclotomes `(Δ_Y)^ell → Δ_Θ` given by the commutator pairing. -/
theorem commutator_tgen_ιell (a : M) :
    ⁅(tgen : ThetaGroup M l), ιell (l := l) (Multiplicative.ofAdd a)⁆ =
      ιΘ (l := l) (Multiplicative.ofAdd (l • a)) := by
  rw [commutator_eq_ιΘ]
  simp [tgen]

/-- **The center of the theta group** is `Δ_Θ` (for `M` torsion-free and nontrivial, `l ≠ 0`). -/
theorem mem_center_iff [IsAddTorsionFree M] [Nontrivial M] (hl : l ≠ 0) (x : ThetaGroup M l) :
    x ∈ Subgroup.center (ThetaGroup M l) ↔ x.a = 0 ∧ x.b = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    have hcomm : ∀ y : ThetaGroup M l, ⁅x, y⁆ = 1 := fun y =>
      commutatorElement_eq_one_iff_mul_comm.2 (h y).symm
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    have h1 := congrArg ThetaGroup.c (hcomm (ιell (Multiplicative.ofAdd m)))
    have h2 := congrArg ThetaGroup.c (hcomm tgen)
    rw [commutator_eq] at h1 h2
    simp only [ιell_a, ιell_b, zero_smul, sub_zero, one_c, tgen] at h1 h2
    rw [smul_smul] at h1
    have hb : l * x.b = 0 := by
      by_contra hne
      exact hm ((smul_eq_zero.1 h1).resolve_left hne)
    refine ⟨?_, (mul_eq_zero.1 hb).resolve_left hl⟩
    simp only [smul_zero, zero_sub, smul_neg, neg_eq_zero, one_smul] at h2
    exact (smul_eq_zero.1 h2).resolve_left hl
  · rintro ⟨ha, hb⟩ y
    have : ⁅x, y⁆ = 1 := by
      rw [commutator_eq]
      ext <;> simp [ha, hb]
    exact (commutatorElement_eq_one_iff_mul_comm.1 this).symm

/-- The subgroup `l·Δ_Θ = {(l·m, 0, 0)}`. -/
def thetaKernel (M : Type*) [AddCommGroup M] (l : ℤ) : Subgroup (ThetaGroup M l) where
  carrier := {x | x.a = 0 ∧ x.b = 0 ∧ ∃ m : M, x.c = l • m}
  mul_mem' := by
    rintro x y ⟨hxa, hxb, m, hm⟩ ⟨hya, hyb, m', hm'⟩
    refine ⟨by simp [hxa, hya], by simp [hxb, hyb], m + m', ?_⟩
    simp [hm, hm', hya, smul_add]
  one_mem' := ⟨rfl, rfl, 0, by simp⟩
  inv_mem' := by
    rintro x ⟨hxa, hxb, m, hm⟩
    exact ⟨by simp [hxa], by simp [hxb], -m, by simp [hm, hxa]⟩

/-- **[EtTh], Prop. 2.12(i)**: the commutator subgroup of the theta group is `l·Δ_Θ`. -/
theorem commutator_eq_theta : commutator (ThetaGroup M l) = thetaKernel M l := by
  apply le_antisymm
  · rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [commutator_eq]
    exact ⟨rfl, rfl, _, rfl⟩
  · rintro x ⟨hxa, hxb, m, hm⟩
    have hx : x = ⁅(tgen : ThetaGroup M l), ιell (l := l) (Multiplicative.ofAdd m)⁆ := by
      rw [commutator_tgen_ιell]
      ext <;> simp only [ιΘ_c, ιΘ_a, ιΘ_b, hxa, hxb, hm]
    rw [hx, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

variable {M' : Type*} [AddCommGroup M'] {l' : ℤ}

/-- **Cyclotomic rigidity, algebraic core** ([EtTh], Cor. 2.19(i), Prop. 2.14(i)). Let
`φ : Δ^Θ → Δ'^Θ` be a homomorphism of theta groups mapping the `ell`-cyclotome to the
`ell`-cyclotome by `α` (modulo `Δ'_Θ`) and the generator `t` to an element of `ℤ`-degree `ε`.
Then `φ` acts on `l·Δ_Θ` by `l'·ε·α`: `φ(l·m) = l'·ε·α(m)`. -/
theorem cyclotomicRigidity (φ : ThetaGroup M l →* ThetaGroup M' l') (α : M → M') {ε : ℤ}
    (hα : ∀ m, (φ (ιell (Multiplicative.ofAdd m))).a = α m)
    (hb : ∀ m, (φ (ιell (Multiplicative.ofAdd m))).b = 0) (hε : (φ tgen).b = ε) (m : M) :
    φ (ιΘ (Multiplicative.ofAdd (l • m))) = ιΘ (Multiplicative.ofAdd ((l' * ε) • α m)) := by
  rw [← commutator_tgen_ιell, map_commutatorElement, commutator_eq_ιΘ, hα, hb, hε, zero_smul,
    sub_zero, mul_smul]

/-- **Cyclotomic rigidity for automorphisms fixing the labels**: an automorphism of the theta
group (with `l ≠ 0`, `M` torsion-free) inducing `α` on the `ell`-cyclotome and fixing the
`ℤ`-degree of `t` acts on `Δ_Θ` by the same `α` — the identification `(Δ_Y)^ell ≅ Δ_Θ` by the
commutator pairing involves no further indeterminacy. -/
theorem cyclotomicRigidity_aut [IsAddTorsionFree M] (hl : l ≠ 0)
    (φ : ThetaGroup M l →* ThetaGroup M l) (α : M →+ M)
    (hα : ∀ m, (φ (ιell (Multiplicative.ofAdd m))).a = α m)
    (hb : ∀ m, (φ (ιell (Multiplicative.ofAdd m))).b = 0) (hε : (φ tgen).b = 1)
    (hΘ : ∀ c, (φ (ιΘ (Multiplicative.ofAdd c))).a = 0 ∧
      (φ (ιΘ (Multiplicative.ofAdd c))).b = 0) (c : M) :
    (φ (ιΘ (Multiplicative.ofAdd c))).c = α c := by
  have h := congrArg ThetaGroup.c (cyclotomicRigidity φ α hα hb hε c)
  simp only [ιΘ_c, mul_one] at h
  -- `φ ∘ ιΘ` is additive with values in `Δ_Θ`, so `l·φ(c) = φ(l·c) = l·α(c)`.
  have hadd : ∀ n : ℕ, (φ (ιΘ (Multiplicative.ofAdd ((n : ℤ) • c)))).c =
      (n : ℤ) • (φ (ιΘ (Multiplicative.ofAdd c))).c := by
    intro n
    induction n with
    | zero => simp [show (Multiplicative.ofAdd (0 : M)) = 1 from rfl]
    | succ k ih =>
      have e : Multiplicative.ofAdd (((k + 1 : ℕ) : ℤ) • c) =
          Multiplicative.ofAdd (((k : ℕ) : ℤ) • c) * Multiplicative.ofAdd c := by
        rw [← ofAdd_add]; congr 1; push_cast; rw [add_smul, one_smul]
      rw [e, map_mul, map_mul, mul_c, ih, (hΘ _).2, mul_zero, zero_smul, add_zero]
      push_cast
      rw [add_smul, one_smul]
  have hneg : ∀ x : M, (φ (ιΘ (Multiplicative.ofAdd (-x)))).c =
      -(φ (ιΘ (Multiplicative.ofAdd x))).c := by
    intro x
    have e := congrArg ThetaGroup.c
      (map_mul φ (ιΘ (Multiplicative.ofAdd (-x))) (ιΘ (Multiplicative.ofAdd x)))
    rw [← map_mul, ← ofAdd_add, neg_add_cancel, mul_c, (hΘ _).2, mul_zero, zero_smul,
      add_zero] at e
    have h0 : (φ (ιΘ (Multiplicative.ofAdd (0 : M)))).c = 0 := by
      simp [show (Multiplicative.ofAdd (0 : M)) = 1 from rfl]
    rw [h0] at e
    exact eq_neg_of_add_eq_zero_left e.symm
  have hl' : (φ (ιΘ (Multiplicative.ofAdd (l • c)))).c =
      l • (φ (ιΘ (Multiplicative.ofAdd c))).c := by
    rcases Int.eq_nat_or_neg l with ⟨n, rfl | rfl⟩
    · exact hadd n
    · rw [neg_smul, hneg, hadd, neg_smul]
  rw [hl'] at h
  exact smul_right_injective M hl h

end ThetaGroup

end Iut.EtaleTheta
