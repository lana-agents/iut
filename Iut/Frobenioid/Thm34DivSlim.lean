/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm34Base

/-!
# The base functor of an equivalence over a Div-slim base ([FrdI], Corollary 4.11(ii))

[FrdI], Theorem 3.4(v) reconstructs the base category from a Frobenioid when the base is
**slim** (`Iut/Frobenioid/Thm34Base.lean`). [FrdI], Corollary 4.11(ii) (l.4328–4352 of
`~/iut-scratch/wall/txt/The Geometry of Frobenioids I.txt`) weakens slimness to
**Div-slimness** ([FrdI], Definition 4.5(iv): `Aut(D_A → D) → Aut(D_A → Mon)` is injective):
automorphisms of the base are detected by their action on the divisor monoids. This is what is
needed for the arithmetic Frobenioids of [FrdI], Example 6.3 over `B(Gal(F̃/F))⁰`, whose base
is not slim when `Gal(F̃/F)` is finite and nontrivial, but is Div-slim ([FrdI], Theorem 6.4(i):
"any automorphism of a number field that fixes all of the valuations of the number field is
clearly equal to the identity automorphism").

[FrdI] proves Corollary 4.11(ii) through the birationalization `C^birat` and Theorem 4.2. Here
the statement is proved directly for model Frobenioids, from the types of morphisms matched by
the equivalence (`TypeCorresp`): pre-steps, base-isomorphisms and morphisms of Frobenius type.

## The divisor monoid seen by the category

For an object `X` of `C₁`, the pre-steps out of `X` up to isomorphism of their codomain are
classified by their zero divisors, i.e. by `Φ₁(A_X)`, and the factorization order of pre-steps is
the order `≤` of `Φ₁(A_X)` ([FrdI] §0). Hence an equivalence `F` induces
`τ_X : Φ₁(A_X) → Φ₂(A_{F X})`, `c ↦ Div(F(X → (A_X, α_X + c)))` (`Model.tau`), which is an
**order isomorphism** (`tau_le_iff`, `tau_surj`). Disjointness (`DivMonoid.Disj`: `0` is the only
common lower bound) and the elements whose lower bounds form a chain (`DivMonoid.IsChainPrime`;
for divisor monoids of number fields: the nonzero divisors supported at a single place) are
order-theoretic, so they are transported by `τ_X`.

## Hypotheses on the divisor monoids

* `DivMonoid.GoodDiv Φ`: chain-primes are stable under multiplication by `n ≥ 1`; a Riesz-type
  decomposition (`p ≤ x + y` with `p, x` disjoint implies `p ≤ y`); and `Φ(A)` is archimedean
  (`k·d ≤ e` for all `k` forces `d = 0`). These hold for (realified) divisor monoids, which are
  products of copies of `ℕ` and `ℝ_{≥0}`.
* `DivMonoid.AutFaithful Φ` (the form of Div-slimness used): an automorphism `h` of an object `A`
  of `D` such that `h^* x` and `x` are never disjoint for chain-primes `x` (i.e. `h` fixes every
  place) is the identity.

## Proof

For a base-isomorphism `γ : X → Z` of `C₁` (`f = Base(γ)`, `g = Base(F γ)`), every chain-prime
`d ∈ Φ₁(A_Z)` satisfies: `g^* τ_Z(d)` and `τ_X(f^* d)` are not disjoint (`Model.Compat`).
`Compat` is stable under composition (`compat_comp`); every base-isomorphism is a morphism of
Frobenius type followed by a pre-step (`compat_baseIso`). For a pre-step `σ` with zero divisor
`e` this comes from `τ_X(k f^* d + e) = g^* τ_Z(k d) + τ_X(e)` (`F` preserves composites of
pre-steps) and the archimedean property (`compat_preStep`); for a morphism of Frobenius type of
degree `n` from the square of [FrdI], Proposition 1.10(i): `m·τ_X(f^* d) = g^* τ_Z(n·d)`
(`compat_frob`).

Now let `φ, φ' : X → Y` have the same base. Both factor through the same pull-back after
base-identity morphisms `γ, γ' : X → Z` (`facAt`). Then `h = Base(F γ) ∘ Base(F γ')⁻¹` moves no
chain-prime of `Φ₂(A_{F X})` to a disjoint one (all of them are `Base(F γ')^* τ_Z(d)`), so
`h = id` by `AutFaithful`: **`Model.base_map_eq_of_base_eq_divSlim`**. With
`Model.preservesBase_of` (`Thm34Base.lean`) this gives **`Model.preservesBase_divSlim`**: `F`
lies over a functor of base categories.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w₁ w₂ v₁ v₂ u₁ u₂

/-! ### Order-theoretic notions on divisor monoids -/

namespace DivMonoid

variable {D : Type u₁} [Category.{v₁} D] (Φ : DivMonoid.{w₁} D)

/-- `a`, `b` are **disjoint**: `0` is their only common effective lower bound. -/
def Disj {A : D} (a b : Φ.obj A) : Prop :=
  ∀ r ∈ Φ.pos A, Φ.le r a → Φ.le r b → r = 0

/-- **Chain-primes**: nonzero effective elements whose effective lower bounds form a chain (for
divisor monoids of number fields: nonzero divisors supported at one place). -/
def IsChainPrime {A : D} (a : Φ.obj A) : Prop :=
  a ∈ Φ.pos A ∧ a ≠ 0 ∧ ∀ b ∈ Φ.pos A, ∀ c ∈ Φ.pos A, Φ.le b a → Φ.le c a → Φ.le b c ∨ Φ.le c b

/-- **Hypotheses on the divisor monoids** used for the base reconstruction: chain-primes are
stable under `n ≥ 1`; Riesz decomposition for disjoint elements; archimedean. -/
def GoodDiv : Prop :=
  (∀ (A : D) (a : Φ.obj A) (n : ℕ), Φ.IsChainPrime a → 0 < n → Φ.IsChainPrime (n • a)) ∧
  (∀ (A : D) (p x y : Φ.obj A), p ∈ Φ.pos A → x ∈ Φ.pos A → y ∈ Φ.pos A →
    Φ.le p (x + y) → Φ.Disj p x → Φ.le p y) ∧
  (∀ (A : D) (d e : Φ.obj A), d ∈ Φ.pos A → e ∈ Φ.pos A → (∀ k : ℕ, Φ.le (k • d) e) → d = 0)

/-- **Div-slimness** in the form used here: an automorphism `h` of `A` such that `h^* x` meets
`x` for every chain-prime `x` (i.e. `h` fixes every "place") is the identity. -/
def AutFaithful : Prop :=
  ∀ (A : D) (h : A ⟶ A), IsIso h → (∀ x : Φ.obj A, Φ.IsChainPrime x → ¬ Φ.Disj (Φ.pb h x) x) →
    h = 𝟙 A

variable {Φ}

lemma le_trans' {A : D} {a b c : Φ.obj A} (h₁ : Φ.le a b) (h₂ : Φ.le b c) : Φ.le a c := by
  have : c - a = (c - b) + (b - a) := by abel
  unfold le at *
  rw [this]
  exact (Φ.pos A).add_mem h₂ h₁

lemma le_iff_mem_sub {A : D} {a b : Φ.obj A} : Φ.le a b ↔ b - a ∈ Φ.pos A := Iff.rfl

lemma le_add_right' {A : D} {a b : Φ.obj A} (hb : b ∈ Φ.pos A) : Φ.le a (a + b) := by
  simpa [le] using hb

lemma le_nsmul_self {A : D} {a : Φ.obj A} (ha : a ∈ Φ.pos A) {n : ℕ} (hn : 0 < n) :
    Φ.le a (n • a) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  have : (0 + k + 1) • a - a = k • a := by rw [zero_add, add_smul, one_smul, add_sub_cancel_right]
  rw [le, this]
  exact (Φ.pos A).nsmul_mem ha k

lemma not_disj_iff {A : D} {a b : Φ.obj A} :
    ¬ Φ.Disj a b ↔ ∃ r ∈ Φ.pos A, Φ.le r a ∧ Φ.le r b ∧ r ≠ 0 := by
  unfold Disj
  push Not
  rfl

lemma disj_comm {A : D} {a b : Φ.obj A} : Φ.Disj a b ↔ Φ.Disj b a :=
  ⟨fun h r hr h₁ h₂ => h r hr h₂ h₁, fun h r hr h₁ h₂ => h r hr h₂ h₁⟩

lemma not_disj_of_le {A : D} {a b : Φ.obj A} (ha : a ∈ Φ.pos A) (h0 : a ≠ 0) (h : Φ.le a b) :
    ¬ Φ.Disj a b :=
  not_disj_iff.mpr ⟨a, ha, Φ.le_refl a, h, h0⟩

/-- **Meeting is transitive through a chain-prime.** -/
lemma not_disj_trans {A : D} {a b c : Φ.obj A} (hb : Φ.IsChainPrime b) (h₁ : ¬ Φ.Disj a b)
    (h₂ : ¬ Φ.Disj b c) : ¬ Φ.Disj a c := by
  obtain ⟨r, hr, hra, hrb, hr0⟩ := not_disj_iff.mp h₁
  obtain ⟨s, hs, hsb, hsc, -⟩ := not_disj_iff.mp h₂
  rcases hb.2.2 r hr s hs hrb hsb with h | h
  · exact not_disj_iff.mpr ⟨r, hr, hra, le_trans' h hsc, hr0⟩
  · obtain ⟨s', hs', hs'b, hs'c, hs0⟩ := not_disj_iff.mp h₂
    rcases hb.2.2 r hr s' hs' hrb hs'b with h' | h'
    · exact not_disj_iff.mpr ⟨r, hr, hra, le_trans' h' hs'c, hr0⟩
    · exact not_disj_iff.mpr ⟨s', hs', le_trans' h' hra, hs'c, hs0⟩

lemma not_disj_of_le_chainPrime {A : D} {a b c : Φ.obj A} (hc : Φ.IsChainPrime c)
    (ha : a ∈ Φ.pos A) (ha0 : a ≠ 0) (hb : b ∈ Φ.pos A) (hb0 : b ≠ 0) (hac : Φ.le a c)
    (hbc : Φ.le b c) : ¬ Φ.Disj a b := by
  rcases hc.2.2 a ha b hb hac hbc with h | h
  · exact not_disj_of_le ha ha0 h
  · exact disj_comm.not.mp (not_disj_of_le hb hb0 h)

/-! #### Pull-backs along isomorphisms -/

section Pb

variable {A A' : D} (h : A ⟶ A') [IsIso h]

lemma pb_mem_iff {x : Φ.obj A'} : Φ.pb h x ∈ Φ.pos A ↔ x ∈ Φ.pos A' :=
  ⟨fun hx => by simpa using Φ.pb_mem (inv h) hx, fun hx => Φ.pb_mem h hx⟩

lemma pb_le_iff {x y : Φ.obj A'} : Φ.le (Φ.pb h x) (Φ.pb h y) ↔ Φ.le x y := by
  unfold le
  rw [← map_sub, pb_mem_iff]

omit [IsIso h] in
lemma pb_eq_zero_iff {x : Φ.obj A'} : Φ.pb h x = 0 ↔ x = 0 :=
  ⟨fun hx => Φ.pb_injective h (by rw [hx, map_zero]), fun hx => by rw [hx, map_zero]⟩

lemma pb_surj (y : Φ.obj A) : ∃ x, Φ.pb h x = y := ⟨Φ.pb (inv h) y, by simp⟩

lemma pb_disj_iff {x y : Φ.obj A'} : Φ.Disj (Φ.pb h x) (Φ.pb h y) ↔ Φ.Disj x y := by
  constructor
  · intro H r hr h₁ h₂
    exact (pb_eq_zero_iff h).mp (H _ (Φ.pb_mem h hr) ((pb_le_iff h).mpr h₁) ((pb_le_iff h).mpr h₂))
  · intro H r hr h₁ h₂
    obtain ⟨r', rfl⟩ := pb_surj h r
    rw [pb_le_iff] at h₁ h₂
    rw [H r' ((pb_mem_iff h).mp hr) h₁ h₂, map_zero]

lemma pb_chainPrime {x : Φ.obj A'} (hx : Φ.IsChainPrime x) : Φ.IsChainPrime (Φ.pb h x) := by
  refine ⟨Φ.pb_mem h hx.1, fun h0 => hx.2.1 ((pb_eq_zero_iff h).mp h0), fun b hb c hc hbx hcx => ?_⟩
  obtain ⟨b', rfl⟩ := pb_surj h b
  obtain ⟨c', rfl⟩ := pb_surj h c
  rw [pb_le_iff] at hbx hcx ⊢
  rw [pb_le_iff]
  exact hx.2.2 b' ((pb_mem_iff h).mp hb) c' ((pb_mem_iff h).mp hc) hbx hcx

end Pb

end DivMonoid

namespace Model

/-! ### Pre-steps in a single model -/

section Single

variable {D : Type u₁} [Category.{v₁} D]
variable {Φ : DivMonoid.{w₁} D} {B : GrpOn.{w₁} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-- The pre-step `(1, id, c, 0) : X → (A_X, α_X + c)`. -/
def stepOf (X : Model Φ B divB) (c : Φ.obj X.base) (hc : c ∈ Φ.pos X.base) :
    X ⟶ ⟨X.base, X.α + c⟩ :=
  mk1 (𝟙 _) c hc 0 (by simp)

lemma stepOf_isPreStep (X : Model Φ B divB) (c : Φ.obj X.base) (hc : c ∈ Φ.pos X.base) :
    IsPreStep 𝐏 (stepOf X c hc) :=
  ⟨rfl, by change IsIso (𝟙 X.base); infer_instance⟩

/-- **Factorization of pre-steps**: if `a, b` are pre-steps out of `X` with `Div(a) ≤ Div(b)`,
then `b` factors through `a`. -/
lemma exists_factor_of_preStep {X Y Y' : Model Φ B divB} (a : X ⟶ Y) (b : X ⟶ Y')
    (ha : IsPreStep 𝐏 a) (hb : IsPreStep 𝐏 b) (h : Φ.le a.div b.div) :
    ∃ t : Y ⟶ Y', a ≫ t = b := by
  have ha1 : a.deg = 1 := ha.1
  have hb1 : b.deg = 1 := hb.1
  haveI : IsIso a.base := ha.2
  refine ⟨mk1 (inv a.base ≫ b.base) (Φ.pb (inv a.base) (b.div - a.div)) (Φ.pb_mem _ h)
    (B.pb (inv a.base) (b.u - a.u)) ?_, ?_⟩
  · apply Φ.pb_injective a.base
    have ra := a.rel
    have rb := b.rel
    rw [ha1, PNat.one_coe, one_smul] at ra
    rw [hb1, PNat.one_coe, one_smul] at rb
    simp only [map_add, map_sub, GrpOn.pb_comp', GrpOn.pb_pb_inv, ← divB.natural] at ra rb ⊢
    linear_combination (norm := module) rb - ra
  · ext
    · simp [ha1, hb1]
    · simp
    · simp
    · simp

end Single

/-! ### The order isomorphisms `τ_X` -/

section Tau

variable {D₁ : Type u₁} [Category.{v₁} D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence]
variable (hpre : Corresp F (fun _ _ φ => IsPreStep (toElem Φ₁ B₁ divB₁) φ)
  (fun _ _ φ => IsPreStep (toElem Φ₂ B₂ divB₂) φ))

open Classical in
/-- **`τ_X : Φ₁(A_X) → Φ₂(A_{F X})`**: the zero divisor of the image of the pre-step
`X → (A_X, α_X + c)` (and `0` off `Φ₁(A_X)`). -/
noncomputable def tau (X : Model Φ₁ B₁ divB₁) (c : Φ₁.obj X.base) : Φ₂.obj (F.obj X).base :=
  if hc : c ∈ Φ₁.pos X.base then (F.map (stepOf X c hc)).div else 0

omit [F.IsEquivalence] in
lemma tau_of_mem (X : Model Φ₁ B₁ divB₁) {c : Φ₁.obj X.base} (hc : c ∈ Φ₁.pos X.base) :
    tau F X c = (F.map (stepOf X c hc)).div := by
  simp [tau, hc]

omit [F.IsEquivalence] in
include hpre in
lemma map_preStep {X Y : Model Φ₁ B₁ divB₁} (s : X ⟶ Y) (hs : IsPreStep 𝐏₁ s) :
    IsPreStep 𝐏₂ (F.map s) := (hpre s).1 hs

omit [F.IsEquivalence] in
/-- **The zero divisor of the image of any pre-step** `s` out of `X` is `τ_X(Div s)`. -/
lemma div_map_preStep_tau {X Y : Model Φ₁ B₁ divB₁} (s : X ⟶ Y) (hs : IsPreStep 𝐏₁ s) :
    (F.map s).div = tau F X s.div := by
  have h1 : s.deg = 1 := hs.1
  haveI : IsIso s.base := hs.2
  let i : (⟨X.base, X.α + s.div⟩ : Model Φ₁ B₁ divB₁) ⟶ Y :=
    mk1 s.base 0 (Φ₁.pos _).zero_mem s.u (by
      have r := s.rel
      rw [h1, PNat.one_coe, one_smul] at r
      simpa using r)
  haveI : IsIso i := isIso_of i rfl (by simp only [i, mk1_base]; infer_instance) rfl
  have hsi : stepOf X s.div s.div_mem ≫ i = s := by
    ext
    · simp [i, stepOf, h1]
    · simp [i, stepOf]
    · simp [i, stepOf]
    · simp [i, stepOf]
  rw [tau_of_mem F X s.div_mem]
  conv_lhs => rw [← hsi, F.map_comp, comp_div]
  have h0 := Div_of_isIso (P := 𝐏₂) (F.map i)
  have hd := degFr_of_isIso (P := 𝐏₂) (F.map i)
  change (F.map i).div = 0 at h0
  change (F.map i).deg = 1 at hd
  rw [h0, hd, map_zero, zero_add, PNat.one_coe, one_smul]

omit [F.IsEquivalence] in
lemma tau_zero (X : Model Φ₁ B₁ divB₁) : tau F X 0 = 0 := by
  have := div_map_preStep_tau F (𝟙 X) ⟨rfl, by change IsIso (𝟙 X.base); infer_instance⟩
  rw [F.map_id] at this
  exact this.symm

omit [F.IsEquivalence] in
lemma tau_mem (X : Model Φ₁ B₁ divB₁) {c : Φ₁.obj X.base} (hc : c ∈ Φ₁.pos X.base) :
    tau F X c ∈ Φ₂.pos (F.obj X).base := by
  rw [tau_of_mem F X hc]
  exact (F.map _).div_mem

omit [F.IsEquivalence] in
include hpre in
lemma tau_mono (X : Model Φ₁ B₁ divB₁) {c c' : Φ₁.obj X.base} (hc : c ∈ Φ₁.pos X.base)
    (h : Φ₁.le c c') : Φ₂.le (tau F X c) (tau F X c') := by
  have hc' : c' ∈ Φ₁.pos X.base := by
    have : c' = (c' - c) + c := by abel
    rw [this]; exact (Φ₁.pos _).add_mem h hc
  let t : (⟨X.base, X.α + c⟩ : Model Φ₁ B₁ divB₁) ⟶ ⟨X.base, X.α + c'⟩ :=
    mk1 (𝟙 _) (c' - c) h 0 (by simp)
  have ht : stepOf X c hc ≫ t = stepOf X c' hc' := by
    ext
    · simp [t, stepOf]
    · simp [t, stepOf]
    · simp [t, stepOf]
    · simp [t, stepOf]
  have hpt : IsPreStep 𝐏₂ (F.map t) :=
    map_preStep F hpre t ⟨rfl, by change IsIso (𝟙 X.base); infer_instance⟩
  have hd : (F.map t).deg = 1 := hpt.1
  rw [tau_of_mem F X hc, tau_of_mem F X hc', ← ht, F.map_comp, comp_div, hd, PNat.one_coe,
    one_smul]
  simpa [DivMonoid.le] using Φ₂.pb_mem _ (F.map t).div_mem

include hpre in
lemma le_of_tau_le (X : Model Φ₁ B₁ divB₁) {c c' : Φ₁.obj X.base} (hc : c ∈ Φ₁.pos X.base)
    (hc' : c' ∈ Φ₁.pos X.base) (h : Φ₂.le (tau F X c) (tau F X c')) : Φ₁.le c c' := by
  rw [tau_of_mem F X hc, tau_of_mem F X hc'] at h
  obtain ⟨t₂, ht₂⟩ := exists_factor_of_preStep _ _ (map_preStep F hpre _ (stepOf_isPreStep X c hc))
    (map_preStep F hpre _ (stepOf_isPreStep X c' hc')) h
  have ht : stepOf X c hc ≫ F.preimage t₂ = stepOf X c' hc' :=
    F.map_injective (by rw [F.map_comp, F.map_preimage, ht₂])
  have hdeg := congrArg Hom.deg ht
  have hdiv := congrArg Hom.div ht
  simp only [comp_deg, comp_div, stepOf, mk1_deg, mk1_div, mk1_base, mul_one] at hdeg hdiv
  rw [hdeg, PNat.one_coe, one_smul, GrpOn.pb_id'] at hdiv
  unfold DivMonoid.le
  rw [← hdiv, add_sub_cancel_right]
  exact (F.preimage t₂).div_mem

include hpre in
lemma tau_le_iff (X : Model Φ₁ B₁ divB₁) {c c' : Φ₁.obj X.base} (hc : c ∈ Φ₁.pos X.base)
    (hc' : c' ∈ Φ₁.pos X.base) : Φ₂.le (tau F X c) (tau F X c') ↔ Φ₁.le c c' :=
  ⟨le_of_tau_le F hpre X hc hc', tau_mono F hpre X hc⟩

include hpre in
lemma tau_surj (X : Model Φ₁ B₁ divB₁) {c₂ : Φ₂.obj (F.obj X).base}
    (hc₂ : c₂ ∈ Φ₂.pos (F.obj X).base) : ∃ c ∈ Φ₁.pos X.base, tau F X c = c₂ := by
  let s₂ := stepOf (F.obj X) c₂ hc₂
  let e := F.objObjPreimageIso (⟨(F.obj X).base, (F.obj X).α + c₂⟩ : Model Φ₂ B₂ divB₂)
  let t := F.preimage (s₂ ≫ e.inv)
  have ht : IsPreStep 𝐏₁ t := by
    refine (hpre t).2 ?_
    rw [F.map_preimage]
    change IsPreStep 𝐏₂ (s₂ ≫ e.symm.hom)
    exact (isPreStep_respIso (toElem Φ₂ B₂ divB₂)).right s₂ e.symm (stepOf_isPreStep _ _ _)
  refine ⟨t.div, t.div_mem, ?_⟩
  rw [← div_map_preStep_tau F t ht, F.map_preimage, comp_div]
  have h0 := Div_of_isIso (P := 𝐏₂) e.inv
  have hd := degFr_of_isIso (P := 𝐏₂) e.inv
  change e.inv.div = 0 at h0
  change e.inv.deg = 1 at hd
  rw [h0, hd, map_zero, zero_add, PNat.one_coe, one_smul]
  rfl

include hpre in
lemma tau_eq_zero_iff (X : Model Φ₁ B₁ divB₁) {c : Φ₁.obj X.base} (hc : c ∈ Φ₁.pos X.base) :
    tau F X c = 0 ↔ c = 0 := by
  constructor
  · intro h
    refine Φ₁.le_antisymm ?_ (Φ₁.zero_le hc)
    refine le_of_tau_le F hpre X hc (Φ₁.pos _).zero_mem ?_
    rw [h, tau_zero F]
    exact Φ₂.le_refl _
  · rintro rfl
    exact tau_zero F X

include hpre in
lemma tau_disj_iff (X : Model Φ₁ B₁ divB₁) {c c' : Φ₁.obj X.base} (hc : c ∈ Φ₁.pos X.base)
    (hc' : c' ∈ Φ₁.pos X.base) : Φ₂.Disj (tau F X c) (tau F X c') ↔ Φ₁.Disj c c' := by
  constructor
  · intro H r hr h₁ h₂
    exact (tau_eq_zero_iff F hpre X hr).mp (H _ (tau_mem F X hr) (tau_mono F hpre X hr h₁)
      (tau_mono F hpre X hr h₂))
  · intro H r hr h₁ h₂
    obtain ⟨r', hr', rfl⟩ := tau_surj F hpre X hr
    rw [tau_le_iff F hpre X hr' hc] at h₁
    rw [tau_le_iff F hpre X hr' hc'] at h₂
    rw [H r' hr' h₁ h₂, tau_zero F]

include hpre in
lemma tau_chainPrime (X : Model Φ₁ B₁ divB₁) {c : Φ₁.obj X.base} (hc : Φ₁.IsChainPrime c) :
    Φ₂.IsChainPrime (tau F X c) := by
  refine ⟨tau_mem F X hc.1, fun h0 => hc.2.1 ((tau_eq_zero_iff F hpre X hc.1).mp h0),
    fun b hb b' hb' hbc hb'c => ?_⟩
  obtain ⟨r, hr, rfl⟩ := tau_surj F hpre X hb
  obtain ⟨r', hr', rfl⟩ := tau_surj F hpre X hb'
  rw [tau_le_iff F hpre X hr hc.1] at hbc
  rw [tau_le_iff F hpre X hr' hc.1] at hb'c
  rw [tau_le_iff F hpre X hr hr', tau_le_iff F hpre X hr' hr]
  exact hc.2.2 r hr r' hr' hbc hb'c

include hpre in
lemma chainPrime_of_tau (X : Model Φ₁ B₁ divB₁) {c : Φ₁.obj X.base} (hc : c ∈ Φ₁.pos X.base)
    (h : Φ₂.IsChainPrime (tau F X c)) : Φ₁.IsChainPrime c := by
  refine ⟨hc, fun h0 => h.2.1 ((tau_eq_zero_iff F hpre X hc).mpr h0),
    fun b hb b' hb' hbc hb'c => ?_⟩
  rw [← tau_le_iff F hpre X hb hc] at hbc
  rw [← tau_le_iff F hpre X hb' hc] at hb'c
  rw [← tau_le_iff F hpre X hb hb', ← tau_le_iff F hpre X hb' hb]
  exact h.2.2 _ (tau_mem F X hb) _ (tau_mem F X hb') hbc hb'c

end Tau

/-! ### Compatibility of base-isomorphisms with `τ` -/

section Compat

variable {D₁ : Type u₁} [Category.{v₁} D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] (c : TypeCorresp F)
variable (hG₁ : Φ₁.GoodDiv) (hG₂ : Φ₂.GoodDiv)

/-- **Compatibility of `γ` with `τ`**: for every chain-prime `d ∈ Φ₁(A_Z)`,
`Base(F γ)^* τ_Z(d)` meets `τ_X(Base(γ)^* d)`. -/
def Compat {X Z : Model Φ₁ B₁ divB₁} (γ : X ⟶ Z) : Prop :=
  ∀ d : Φ₁.obj Z.base, Φ₁.IsChainPrime d →
    ¬ Φ₂.Disj (Φ₂.pb (F.map γ).base (tau F Z d)) (tau F X (Φ₁.pb γ.base d))

omit [F.IsEquivalence] in
include c in
lemma isIso_base_map {X Z : Model Φ₁ B₁ divB₁} (γ : X ⟶ Z) (hγ : IsIso γ.base) :
    IsIso (F.map γ).base :=
  (c.baseIso γ).1 hγ

include c in
lemma compat_comp {X Z W : Model Φ₁ B₁ divB₁} (γ₁ : X ⟶ Z) (γ₂ : Z ⟶ W) (h₁ : IsIso γ₁.base)
    (h₂ : IsIso γ₂.base) (c₁ : Compat F γ₁) (c₂ : Compat F γ₂) : Compat F (γ₁ ≫ γ₂) := by
  intro d hd
  haveI := h₁
  haveI := h₂
  haveI := isIso_base_map F c γ₁ h₁
  have e₁ := c₂ d hd
  rw [← DivMonoid.pb_disj_iff (F.map γ₁).base] at e₁
  have hd' : Φ₁.IsChainPrime (Φ₁.pb γ₂.base d) := DivMonoid.pb_chainPrime _ hd
  have e₂ := c₁ _ hd'
  have hmid : Φ₂.IsChainPrime (Φ₂.pb (F.map γ₁).base (tau F Z (Φ₁.pb γ₂.base d))) :=
    DivMonoid.pb_chainPrime _ (tau_chainPrime F c.preStep Z hd')
  have := DivMonoid.not_disj_trans hmid e₁ e₂
  simpa only [F.map_comp, comp_base, GrpOn.pb_comp'] using this

include c hG₁ hG₂ in
/-- **Pre-steps are compatible with `τ`.** -/
lemma compat_preStep {X Z : Model Φ₁ B₁ divB₁} (σ : X ⟶ Z) (hσ : IsPreStep 𝐏₁ σ) :
    Compat F σ := by
  intro d hd
  have hpre := c.preStep
  have h1 : σ.deg = 1 := hσ.1
  haveI : IsIso σ.base := hσ.2
  have hFσ : IsPreStep 𝐏₂ (F.map σ) := map_preStep F hpre σ hσ
  haveI : IsIso (F.map σ).base := hFσ.2
  set g := (F.map σ).base
  set f := σ.base
  set d' := Φ₁.pb f d
  have hd' : Φ₁.IsChainPrime d' := DivMonoid.pb_chainPrime _ hd
  intro hdisj
  -- `τ_X(k d' + e) = g^* τ_Z(k d) + τ_X(e)`
  have key : ∀ k : ℕ, tau F X (k • d' + σ.div) =
      Φ₂.pb g (tau F Z (k • d)) + tau F X σ.div := by
    intro k
    have hkd : k • d ∈ Φ₁.pos Z.base := (Φ₁.pos _).nsmul_mem hd.1 k
    have hs : IsPreStep 𝐏₁ (σ ≫ stepOf Z (k • d) hkd) := by
      refine ⟨?_, ?_⟩
      · change (σ ≫ stepOf Z (k • d) hkd).deg = 1
        rw [comp_deg, h1]; rfl
      · change IsIso (σ.base ≫ 𝟙 _); infer_instance
    have h2 := div_map_preStep_tau F _ hs
    have hdk : (F.map (stepOf Z (k • d) hkd)).deg = 1 :=
      (map_preStep F hpre _ (stepOf_isPreStep Z _ hkd)).1
    rw [F.map_comp, comp_div, div_map_preStep_tau F σ hσ, hdk, PNat.one_coe, one_smul,
      ← tau_of_mem F Z hkd] at h2
    have h3 : (σ ≫ stepOf Z (k • d) hkd).div = k • d' + σ.div := by
      simp [stepOf, d', f, map_nsmul]
    rw [h3] at h2
    exact h2.symm
  have hk : ∀ k : ℕ, Φ₁.le (k • d') σ.div := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [zero_smul]; exact Φ₁.zero_le σ.div_mem
    have hkd' : Φ₁.IsChainPrime (k • d') := hG₁.1 _ _ _ hd' hk
    have hkd : Φ₁.IsChainPrime (k • d) := hG₁.1 _ _ _ hd hk
    have hle : Φ₂.le (tau F X (k • d')) (Φ₂.pb g (tau F Z (k • d)) + tau F X σ.div) := by
      rw [← key]
      exact tau_mono F hpre X hkd'.1 (DivMonoid.le_add_right' σ.div_mem)
    refine (tau_le_iff F hpre X hkd'.1 σ.div_mem).mp (hG₂.2.1 _ _ _ _ (tau_mem F X hkd'.1)
      (Φ₂.pb_mem _ (tau_mem F Z hkd.1)) (tau_mem F X σ.div_mem) hle ?_)
    by_contra hm
    -- `τ_X(d')` meets `τ_X(k d')`, which meets `g^* τ_Z(k d)`, which meets `g^* τ_Z(d)`
    have m₁ : ¬ Φ₂.Disj (tau F X d') (tau F X (k • d')) :=
      DivMonoid.not_disj_of_le (tau_mem F X hd'.1)
        (fun h0 => hd'.2.1 ((tau_eq_zero_iff F hpre X hd'.1).mp h0))
        (tau_mono F hpre X hd'.1 (DivMonoid.le_nsmul_self hd'.1 hk))
    have m₃ : ¬ Φ₂.Disj (Φ₂.pb g (tau F Z (k • d))) (Φ₂.pb g (tau F Z d)) := by
      rw [DivMonoid.pb_disj_iff, DivMonoid.disj_comm]
      exact DivMonoid.not_disj_of_le (tau_mem F Z hd.1)
        (fun h0 => hd.2.1 ((tau_eq_zero_iff F hpre Z hd.1).mp h0))
        (tau_mono F hpre Z hd.1 (DivMonoid.le_nsmul_self hd.1 hk))
    have m₁₂ := DivMonoid.not_disj_trans (tau_chainPrime F hpre X hkd') m₁ hm
    have m := DivMonoid.not_disj_trans
      (DivMonoid.pb_chainPrime _ (tau_chainPrime F hpre Z hkd)) m₁₂ m₃
    exact m (DivMonoid.disj_comm.mp hdisj)
  exact hd'.2.1 (hG₁.2.2 _ _ _ hd'.1 σ.div_mem hk)

include c hG₂ in
/-- **Morphisms of Frobenius type are compatible with `τ`** (the square of [FrdI],
Proposition 1.10(i)). -/
lemma compat_frob {X Z : Model Φ₁ B₁ divB₁} (γ : X ⟶ Z) (h0 : γ.div = 0) (hb : IsIso γ.base) :
    Compat F γ := by
  intro d hd
  have hpre := c.preStep
  haveI := hb
  haveI := isIso_base_map F c γ hb
  set f := γ.base
  set g := (F.map γ).base
  set n : ℕ := (γ.deg : ℕ)
  set cc := Φ₁.pb f d
  have hcc : Φ₁.IsChainPrime cc := DivMonoid.pb_chainPrime _ hd
  have hnd : n • d ∈ Φ₁.pos Z.base := (Φ₁.pos _).nsmul_mem hd.1 n
  let γ' : (⟨X.base, X.α + cc⟩ : Model Φ₁ B₁ divB₁) ⟶ ⟨Z.base, Z.α + n • d⟩ :=
    mk' γ.deg f 0 (Φ₁.pos _).zero_mem γ.u (by
      have r := γ.rel
      rw [h0, add_zero] at r
      simp only [add_zero, smul_add, map_add, map_nsmul, cc]
      rw [r]
      abel)
  have hsq : stepOf X cc hcc.1 ≫ γ' = γ ≫ stepOf Z (n • d) hnd := by
    ext
    · simp [γ', stepOf]
    · simp [γ', stepOf, f]
    · simp [γ', stepOf, h0, cc, n, f, map_nsmul]
    · simp [γ', stepOf]
  have hγ'fr : IsFrobeniusType 𝐏₁ γ' :=
    (isFrobeniusType_iff _).mpr ⟨rfl, by simp only [γ', mk'_base]; infer_instance⟩
  have hFγ' : (F.map γ').div = 0 := ((isFrobeniusType_iff _).mp ((c.frobType γ').1 hγ'fr)).1
  have hFγ : (F.map γ).div = 0 :=
    ((isFrobeniusType_iff _).mp ((c.frobType γ).1 ((isFrobeniusType_iff _).mpr ⟨h0, hb⟩))).1
  have hdiv := congrArg Hom.div (congrArg F.map hsq)
  rw [F.map_comp, F.map_comp, comp_div, comp_div, hFγ', hFγ, map_zero, zero_add, smul_zero,
    add_zero, ← tau_of_mem F X hcc.1, ← tau_of_mem F Z hnd] at hdiv
  -- `m·τ_X(f^* d) = g^* τ_Z(n·d)`
  set m : ℕ := ((F.map γ').deg : ℕ)
  have hτ := tau_chainPrime F hpre X hcc
  have hy : Φ₂.IsChainPrime (m • tau F X cc) := hG₂.1 _ _ _ hτ (F.map γ').deg.pos
  have hx : Φ₂.IsChainPrime (Φ₂.pb g (tau F Z d)) :=
    DivMonoid.pb_chainPrime _ (tau_chainPrime F hpre Z hd)
  refine DivMonoid.not_disj_of_le_chainPrime hy hx.1 hx.2.1 hτ.1 hτ.2.1 ?_
    (DivMonoid.le_nsmul_self hτ.1 (F.map γ').deg.pos)
  rw [hdiv, DivMonoid.pb_le_iff]
  exact tau_mono F hpre Z hd.1 (DivMonoid.le_nsmul_self hd.1 γ.deg.pos)

include c hG₁ hG₂ in
/-- **Every base-isomorphism is compatible with `τ`**: it is a morphism of Frobenius type
followed by a pre-step. -/
lemma compat_baseIso {X Z : Model Φ₁ B₁ divB₁} (γ : X ⟶ Z) (hb : IsIso γ.base) :
    Compat F γ := by
  let fr : X ⟶ ⟨X.base, (γ.deg : ℕ) • X.α⟩ := mk' γ.deg (𝟙 _) 0 (Φ₁.pos _).zero_mem 0 (by simp)
  let σ : (⟨X.base, (γ.deg : ℕ) • X.α⟩ : Model Φ₁ B₁ divB₁) ⟶ Z :=
    mk1 γ.base γ.div γ.div_mem γ.u γ.rel
  have he : fr ≫ σ = γ := by
    ext
    · simp [fr, σ]
    · simp [fr, σ]
    · simp [fr, σ]
    · simp [fr, σ]
  have hσ : IsPreStep 𝐏₁ σ := ⟨rfl, by simp only [σ]; exact hb⟩
  rw [← he]
  exact compat_comp F c fr σ (by simp only [fr, mk'_base]; infer_instance) hσ.2
    (compat_frob F c hG₂ fr rfl (by simp only [fr, mk'_base]; infer_instance))
    (compat_preStep F c hG₁ hG₂ σ hσ)

include c hG₁ hG₂ in
/-- **[FrdI], Corollary 4.11(ii), the key step**: over a Div-slim base `D₂`, an equivalence of
model Frobenioids maps morphisms with the same base to morphisms with the same base. -/
theorem base_map_eq_of_base_eq_divSlim (hA : Φ₂.AutFaithful) {X Y : Model Φ₁ B₁ divB₁}
    (φ φ' : X ⟶ Y) (h : φ.base = φ'.base) : (F.map φ).base = (F.map φ').base := by
  have hpre := c.preStep
  set f := φ.base
  let γ := facAt φ f rfl
  let γ' := facAt φ' f h.symm
  have e₁ : (F.map φ).base = (F.map γ).base ≫ (F.map (pbAt X Y f)).base := by
    rw [← comp_base, ← F.map_comp, facAt_pbAt]
  have e₂ : (F.map φ').base = (F.map γ').base ≫ (F.map (pbAt X Y f)).base := by
    rw [← comp_base, ← F.map_comp, facAt_pbAt]
  rw [e₁, e₂]
  congr 1
  have hb : IsIso γ.base := by rw [facAt_base]; infer_instance
  have hb' : IsIso γ'.base := by rw [facAt_base]; infer_instance
  haveI := isIso_base_map F c γ hb
  haveI := isIso_base_map F c γ' hb'
  set g := (F.map γ).base
  set g' := (F.map γ').base
  have C₁ := compat_baseIso F c hG₁ hG₂ γ hb
  have C₂ := compat_baseIso F c hG₁ hG₂ γ' hb'
  have hh := hA _ (g ≫ inv g') inferInstance (fun x hx => by
    have hz : Φ₂.IsChainPrime (Φ₂.pb (inv g') x) := DivMonoid.pb_chainPrime _ hx
    obtain ⟨d, hd, hdz⟩ := tau_surj F hpre (pbObj X Y f) hz.1
    have hdc : Φ₁.IsChainPrime d := chainPrime_of_tau F hpre _ hd (hdz ▸ hz)
    have m₁ := C₁ d hdc
    have m₂ := C₂ d hdc
    change ¬ Φ₂.Disj (Φ₂.pb g (tau F _ d)) (tau F X (Φ₁.pb (𝟙 _) d)) at m₁
    change ¬ Φ₂.Disj (Φ₂.pb g' (tau F _ d)) (tau F X (Φ₁.pb (𝟙 _) d)) at m₂
    rw [GrpOn.pb_id'] at m₁ m₂
    rw [hdz, GrpOn.pb_pb_inv] at m₂
    rw [GrpOn.pb_comp', ← hdz]
    exact DivMonoid.not_disj_trans (tau_chainPrime F hpre X hdc) m₁
      (DivMonoid.disj_comm.not.mp m₂))
  rw [← Category.comp_id g, ← IsIso.inv_hom_id g', ← Category.assoc, hh, Category.id_comp]

include c hG₁ hG₂ in
/-- **[FrdI], Corollary 4.11(ii)** for model Frobenioids: an equivalence matching pre-steps,
base-isomorphisms and morphisms of Frobenius type, between model Frobenioids with good divisor
monoids over a Div-slim base `D₂`, lies over a functor of base categories. -/
theorem preservesBase_divSlim (hA : Φ₂.AutFaithful) : PreservesBase 𝐏₁ 𝐏₂ F :=
  preservesBase_of F (fun _ _ ψ h => isIso_base_map F c ψ h)
    (fun _ _ φ φ' h => base_map_eq_of_base_eq_divSlim F c hG₁ hG₂ hA φ φ' h)

end Compat

end Model

end Frobenioid

end Iut
