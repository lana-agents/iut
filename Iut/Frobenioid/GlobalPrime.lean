/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Cor411Rlf

/-!
# Primes of the global realified Frobenioid: `Prime(C^⊩) ≅ V`

[FrdI] §0 (p. 12): `0 ≠ a ∈ M` is *primary* if every `0 ≠ b ≼ a` satisfies `a ≼ b`
(`a ≼ b` iff `a ≤ n·b` for some `n ≥ 1`); a *prime* of `M` is a `≼`-equivalence class of
primary elements. [FrdI], Example 6.3: `Prime(Φ(L)) ≅ V(L)`; IUT I, Example 3.5(i): the set of
primes `Prime(C^⊩_mod)` of the divisor monoid of `C^⊩_mod` is in natural bijection with
`V_mod`. [FrdI], Corollary 4.11(iii) (with Theorem 4.2(ii)): an equivalence induces
`Ψ_Φ` compatible with a bijection `Ψ_Prime` of primes.

For the global realified Frobenioid `C^⊩(K)` (places `Place K = V_fin ⊕ V_∞`):

* `GlobalRealified.preceq_iff`: `a ≼ b ⟺ supp a ⊆ supp b` for effective `a, b`;
* `GlobalRealified.isPrimary_iff`: `a` is primary iff `supp a` is a single place;
* `GlobalRealified.preceq_primary_iff`: two primary elements are `≼`-equivalent iff they are
  supported at the same place, so `Prime(Φ) ≅ Place K` (`primeEquiv`);
* for an equivalence `F : C^⊩(K) ≌ C^⊩(L)`: `psiPhi_isPrimary_iff`, and **`placeEquiv F`** :
  `Place K ≃ Place L` (`Ψ_Prime`) with **`supp_psiPhi`**: `supp(Ψ_Φ z) = Ψ_Prime(supp z)` for every
  effective `z`, i.e. `Ψ_Φ` maps the submonoid `Φ_v` to `Φ_{Ψ_Prime(v)}`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField Arakelov

universe u

namespace GlobalRealified

open scoped Classical

variable {K : Type u} [Field K] [NumberField K]

/-- The places of `K`: finite and infinite. -/
abbrev Place (K : Type u) [Field K] [NumberField K] : Type u :=
  FinitePlace K ⊕ InfinitePlace K

/-- The coordinate of an arithmetic divisor at a place. -/
def coord (x : ArithDiv K) : Place K → ℝ
  | Sum.inl w => x.1 w
  | Sum.inr v => x.2 v

@[simp] lemma coord_inl (x : ArithDiv K) (w : FinitePlace K) : coord x (Sum.inl w) = x.1 w := rfl
@[simp] lemma coord_inr (x : ArithDiv K) (v : InfinitePlace K) : coord x (Sum.inr v) = x.2 v :=
  rfl

@[simp] lemma coord_add (x y : ArithDiv K) (p : Place K) :
    coord (x + y) p = coord x p + coord y p := by cases p <;> simp

@[simp] lemma coord_sub (x y : ArithDiv K) (p : Place K) :
    coord (x - y) p = coord x p - coord y p := by cases p <;> simp

@[simp] lemma coord_nsmul (n : ℕ) (x : ArithDiv K) (p : Place K) :
    coord (n • x) p = n * coord x p := by cases p <;> simp

@[simp] lemma coord_zero (p : Place K) : coord (0 : ArithDiv K) p = 0 := by cases p <;> simp

lemma mem_effCone_iff_coord {x : ArithDiv K} : x ∈ effCone K ↔ ∀ p, 0 ≤ coord x p :=
  ⟨fun h p => by cases p with | inl w => exact h.1 w | inr v => exact h.2 v,
    fun h => ⟨fun w => h (Sum.inl w), fun v => h (Sum.inr v)⟩⟩

lemma eq_iff_coord {x y : ArithDiv K} : x = y ↔ ∀ p, coord x p = coord y p :=
  ⟨fun h _ => h ▸ rfl, fun h => Prod.ext (Finsupp.ext fun w => h (Sum.inl w))
    (funext fun v => h (Sum.inr v))⟩

/-- The support of an arithmetic divisor. -/
def supp (x : ArithDiv K) : Set (Place K) := {p | coord x p ≠ 0}

/-- The divisor `t·[p]`. -/
noncomputable def single : Place K → ℝ → ArithDiv K
  | Sum.inl w, t => (Finsupp.single w t, 0)
  | Sum.inr v, t => (0, Pi.single v t)

lemma coord_single (p : Place K) (t : ℝ) (q : Place K) :
    coord (single p t) q = if q = p then t else 0 := by
  cases p with
  | inl w =>
    cases q with
    | inl w' => simp [single, Finsupp.single_apply, eq_comm]
    | inr v' => simp [single]
  | inr v =>
    cases q with
    | inl w' => simp [single]
    | inr v' => simp [single, Pi.single_apply]

lemma single_mem {p : Place K} {t : ℝ} (ht : 0 ≤ t) : single p t ∈ effCone K := by
  rw [mem_effCone_iff_coord]
  intro q
  rw [coord_single]
  split_ifs <;> simp [ht]

lemma supp_single {p : Place K} {t : ℝ} (ht : t ≠ 0) : supp (single p t) = {p} := by
  ext q
  simp only [supp, Set.mem_setOf_eq, coord_single, Set.mem_singleton_iff]
  split_ifs with h <;> simp [h, ht]

lemma coord_eq_zero_of_not_mem {x : ArithDiv K} {p : Place K} (h : p ∉ supp x) :
    coord x p = 0 := by
  simpa [supp] using h

/-- A finite set of places containing the support. -/
noncomputable def suppFinset (x : ArithDiv K) : Finset (Place K) :=
  x.1.support.map Function.Embedding.inl ∪ Finset.univ.map Function.Embedding.inr

lemma mem_suppFinset {x : ArithDiv K} {p : Place K} (h : coord x p ≠ 0) : p ∈ suppFinset x := by
  classical
  cases p with
  | inl w =>
    refine Finset.mem_union_left _ (Finset.mem_map.mpr ⟨w, ?_, rfl⟩)
    simpa using h
  | inr v => exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩)

/-- `a ≼ b` in the divisor monoid `Φ^rlf`. -/
abbrev Preceq (a b : ArithDiv K) : Prop := (phiRlf K).preceq (A := pt) a b

/-- **`a ≼ b` iff `supp a ⊆ supp b`** (effective `a, b`). -/
theorem preceq_iff {a b : ArithDiv K} (ha : a ∈ effCone K) (hb : b ∈ effCone K) :
    Preceq a b ↔ supp a ⊆ supp b := by
  rw [mem_effCone_iff_coord] at ha hb
  constructor
  · rintro ⟨n, -, hn⟩ p hp
    have h := (mem_effCone_iff_coord.mp hn) p
    rw [coord_sub, coord_nsmul] at h
    intro hb0
    rw [hb0, mul_zero] at h
    exact hp (le_antisymm (by linarith) (ha p))
  · intro hs
    let S := suppFinset a
    let r : Place K → ℝ := fun p => coord a p / coord b p
    have hr : ∀ p, 0 ≤ r p := fun p => div_nonneg (ha p) (hb p)
    let n : ℕ := ⌈∑ p ∈ S, r p⌉₊ + 1
    refine ⟨n, Nat.succ_pos _, mem_effCone_iff_coord.mpr fun p => ?_⟩
    rw [coord_sub, coord_nsmul, sub_nonneg]
    by_cases hp : coord a p = 0
    · rw [hp]; exact mul_nonneg (Nat.cast_nonneg _) (hb p)
    have hbp : coord b p ≠ 0 := hs hp
    have hpS : p ∈ S := mem_suppFinset hp
    have h1 : r p ≤ ∑ q ∈ S, r q := Finset.single_le_sum (fun q _ => hr q) hpS
    have h2 : ∑ q ∈ S, r q ≤ n := by
      have := Nat.le_ceil (∑ q ∈ S, r q)
      push_cast [n]
      linarith
    have hbpos : 0 < coord b p := lt_of_le_of_ne (hb p) (Ne.symm hbp)
    calc coord a p = r p * coord b p := by simp only [r]; field_simp
      _ ≤ n * coord b p := mul_le_mul_of_nonneg_right (h1.trans h2) hbpos.le

/-- **Primary elements are those supported at a single place.** -/
theorem isPrimary_iff {a : ArithDiv K} (ha : a ∈ effCone K) :
    (phiRlf K).IsPrimary (A := pt) a ↔ ∃ p, supp a = {p} := by
  constructor
  · rintro ⟨-, ha0, hp⟩
    obtain ⟨p, hp0⟩ : ∃ p, coord a p ≠ 0 := by
      by_contra h
      simp only [not_exists, ne_eq, not_not] at h
      exact ha0 (eq_iff_coord.mpr fun p => by rw [h p, coord_zero])
    have hb := single_mem (p := p) ((mem_effCone_iff_coord.mp ha) p)
    have hb0 : single p (coord a p) ≠ 0 := fun h => by
      have := congrArg (fun x => coord x p) h
      simp only [coord_single, coord_zero] at this
      exact hp0 this
    have hs : supp (single p (coord a p)) = {p} := supp_single hp0
    have h1 : Preceq (single p (coord a p)) a :=
      (preceq_iff hb ha).mpr (by rw [hs]; simpa [supp] using hp0)
    have h2 := (preceq_iff ha hb).mp (hp _ hb hb0 h1)
    rw [hs] at h2
    exact ⟨p, Set.Subset.antisymm h2 (by simpa [supp] using hp0)⟩
  · rintro ⟨p, hp⟩
    refine ⟨ha, fun h0 => ?_, fun b hb hb0 hba => ?_⟩
    · have : p ∈ supp a := hp ▸ rfl
      exact this (by rw [h0, coord_zero])
    · have h1 := (preceq_iff hb ha).mp hba
      rw [hp] at h1
      obtain ⟨q, hq⟩ : ∃ q, coord b q ≠ 0 := by
        by_contra h
        simp only [not_exists, ne_eq, not_not] at h
        exact hb0 (eq_iff_coord.mpr fun q => by rw [h q, coord_zero])
      have hqp : q = p := h1 hq
      refine (preceq_iff ha hb).mpr ?_
      rw [hp]
      intro r hr
      rw [Set.mem_singleton_iff.mp hr, ← hqp]
      exact hq

/-- **Two primary elements are `≼`-equivalent iff they are supported at the same place.** -/
theorem preceq_primary_iff {a b : ArithDiv K} (ha : a ∈ effCone K) (hb : b ∈ effCone K)
    {p q : Place K} (hpa : supp a = {p}) (hqb : supp b = {q}) : Preceq a b ↔ p = q := by
  rw [preceq_iff ha hb, hpa, hqb, Set.singleton_subset_singleton]

/-- The primary element `[p]`. -/
lemma single_one_isPrimary (p : Place K) :
    (phiRlf K).IsPrimary (A := pt) (single p 1) :=
  (isPrimary_iff (single_mem zero_le_one)).mpr ⟨p, supp_single one_ne_zero⟩

/-- The primary elements of `Φ^rlf`. -/
def Primary (K : Type u) [Field K] [NumberField K] : Type u :=
  {a : ArithDiv K // (phiRlf K).IsPrimary (A := pt) a}

/-- The `≼`-equivalence relation on primary elements. -/
def primarySetoid : Setoid (Primary K) where
  r a b := Preceq a.1 b.1 ∧ Preceq b.1 a.1
  iseqv := by
    refine ⟨fun a => ?_, fun h => ⟨h.2, h.1⟩, fun h₁ h₂ => ?_⟩
    · have := (preceq_iff a.2.1 a.2.1).mpr subset_rfl
      exact ⟨this, this⟩
    · rename_i a b c
      exact ⟨(preceq_iff a.2.1 c.2.1).mpr (((preceq_iff a.2.1 b.2.1).mp h₁.1).trans
          ((preceq_iff b.2.1 c.2.1).mp h₂.1)),
        (preceq_iff c.2.1 a.2.1).mpr (((preceq_iff c.2.1 b.2.1).mp h₂.2).trans
          ((preceq_iff b.2.1 a.2.1).mp h₁.2))⟩

/-- **`Prime(Φ^rlf)`**: the `≼`-classes of primary elements ([FrdI] §0). -/
def Prime (K : Type u) [Field K] [NumberField K] : Type u := Quotient (primarySetoid (K := K))

/-- The place of a primary element. -/
noncomputable def placeOf (a : Primary K) : Place K :=
  ((isPrimary_iff a.2.1).mp a.2).choose

lemma supp_eq_placeOf (a : Primary K) : supp a.1 = {placeOf a} :=
  ((isPrimary_iff a.2.1).mp a.2).choose_spec

/-- **`Prime(C^⊩) ≅ V`** (IUT I, Example 3.5(i); [FrdI], Example 6.3). -/
noncomputable def primeEquiv : Prime K ≃ Place K where
  toFun := Quotient.lift placeOf fun a b h =>
    (preceq_primary_iff a.2.1 b.2.1 (supp_eq_placeOf a) (supp_eq_placeOf b)).mp h.1
  invFun p := Quotient.mk _ ⟨single p 1, single_one_isPrimary p⟩
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h a =>
      refine Quotient.sound ?_
      have hs : supp (single (placeOf a) 1) = {placeOf a} := supp_single one_ne_zero
      exact ⟨(preceq_primary_iff (single_mem zero_le_one) a.2.1 hs (supp_eq_placeOf a)).mpr rfl,
        (preceq_primary_iff a.2.1 (single_mem zero_le_one) (supp_eq_placeOf a) hs).mpr rfl⟩
  right_inv p := by
    change placeOf ⟨single p 1, _⟩ = p
    have h := supp_eq_placeOf ⟨single p 1, single_one_isPrimary p⟩
    rw [supp_single one_ne_zero] at h
    exact (Set.singleton_eq_singleton_iff.mp h).symm

/-! ### `Ψ_Prime` for an equivalence -/

variable {L : Type u} [Field L] [NumberField L]
variable (F : GlobalRealified K ⥤ GlobalRealified L) [F.IsEquivalence]

lemma psiPhi_nsmul (n : ℕ) {z : ArithDiv K} (hz : z ∈ effCone K) :
    psiPhi F (n • z) ((effCone K).nsmul_mem hz n) = n • psiPhi F z hz := by
  induction n with
  | zero => simpa using psiPhi_zero F
  | succ n ih =>
    have := psiPhi_add F ((effCone K).nsmul_mem hz n) hz
    simp only [succ_nsmul]
    rw [this, ih]

lemma psiPhi_preceq_iff {a b : ArithDiv K} (ha : a ∈ effCone K) (hb : b ∈ effCone K) :
    Preceq (psiPhi F a ha) (psiPhi F b hb) ↔ Preceq a b := by
  constructor
  · rintro ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    have h' : psiPhi F (n • b) ((effCone K).nsmul_mem hb n) - psiPhi F a ha ∈ effCone L := by
      rw [psiPhi_nsmul]; exact h
    exact (psiPhi_le_iff F ha _).mp h'
  · rintro ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    have h' := (psiPhi_le_iff F ha ((effCone K).nsmul_mem hb n)).mpr h
    rw [psiPhi_nsmul] at h'
    exact h'

lemma psiPhi_ne_zero_iff {a : ArithDiv K} (ha : a ∈ effCone K) :
    psiPhi F a ha ≠ 0 ↔ a ≠ 0 := by
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · exact psiPhi_injective F ha (effCone K).zero_mem (h.trans (psiPhi_zero F).symm)
  · subst h; exact psiPhi_zero F

/-- **`Ψ_Φ` preserves and reflects primary elements.** -/
theorem psiPhi_isPrimary_iff {a : ArithDiv K} (ha : a ∈ effCone K) :
    (phiRlf L).IsPrimary (A := pt) (psiPhi F a ha) ↔ (phiRlf K).IsPrimary (A := pt) a := by
  constructor
  · rintro ⟨-, h0, h⟩
    refine ⟨ha, (psiPhi_ne_zero_iff F ha).mp h0, fun b hb hb0 hba => ?_⟩
    exact (psiPhi_preceq_iff F ha hb).mp (h _ (psiPhi_mem F b hb)
      ((psiPhi_ne_zero_iff F hb).mpr hb0) ((psiPhi_preceq_iff F hb ha).mpr hba))
  · rintro ⟨-, h0, h⟩
    refine ⟨psiPhi_mem F a ha, (psiPhi_ne_zero_iff F ha).mpr h0, fun y hy hy0 hya => ?_⟩
    obtain ⟨b, hb, rfl⟩ := psiPhi_surjective F hy
    exact (psiPhi_preceq_iff F ha hb).mpr (h b hb ((psiPhi_ne_zero_iff F hb).mp hy0)
      ((psiPhi_preceq_iff F hb ha).mp hya))

/-- The place of `Ψ_Φ([p])`. -/
noncomputable def placeMap (p : Place K) : Place L :=
  placeOf ⟨psiPhi F (single p 1) (single_mem zero_le_one),
    (psiPhi_isPrimary_iff F _).mpr (single_one_isPrimary p)⟩

lemma supp_psiPhi_single (p : Place K) :
    supp (psiPhi F (single p 1) (single_mem zero_le_one)) = {placeMap F p} :=
  supp_eq_placeOf (⟨psiPhi F (single p 1) (single_mem zero_le_one),
    (psiPhi_isPrimary_iff F _).mpr (single_one_isPrimary p)⟩ : Primary L)

/-- **`q ∈ supp(Ψ_Φ z) ⟺ q = Ψ_Prime(p)` for some `p ∈ supp z`.** -/
theorem mem_supp_psiPhi {z : ArithDiv K} (hz : z ∈ effCone K) (p : Place K) :
    placeMap F p ∈ supp (psiPhi F z hz) ↔ p ∈ supp z := by
  have h1 := preceq_iff (single_mem (p := p) zero_le_one) hz
  have h2 := preceq_iff (psiPhi_mem F _ (single_mem (p := p) zero_le_one)) (psiPhi_mem F z hz)
  rw [psiPhi_preceq_iff, supp_psiPhi_single, Set.singleton_subset_iff] at h2
  rw [← h2, h1, supp_single one_ne_zero, Set.singleton_subset_iff]

lemma placeMap_injective : Function.Injective (placeMap F) := by
  intro p p' h
  have := (mem_supp_psiPhi F (single_mem (p := p') zero_le_one) p).mp (by
    rw [h, supp_psiPhi_single]; rfl)
  rw [supp_single one_ne_zero] at this
  exact this

lemma placeMap_surjective : Function.Surjective (placeMap F) := by
  intro q
  obtain ⟨z, hz, hzq⟩ := psiPhi_surjective F (single_mem (K := L) (p := q) zero_le_one)
  have hprim : (phiRlf K).IsPrimary (A := pt) z :=
    (psiPhi_isPrimary_iff F hz).mp (by rw [hzq]; exact single_one_isPrimary q)
  obtain ⟨p, hp⟩ := (isPrimary_iff hz).mp hprim
  refine ⟨p, ?_⟩
  have := (mem_supp_psiPhi F hz p).mpr (by rw [hp]; rfl)
  rw [hzq, supp_single one_ne_zero] at this
  exact this

/-- **`Ψ_Prime : V(K) ≅ V(L)`** induced by an equivalence `C^⊩(K) ≌ C^⊩(L)` ([FrdI], Corollary
4.11(iii) with Theorem 4.2(ii)). -/
noncomputable def placeEquiv : Place K ≃ Place L :=
  Equiv.ofBijective (placeMap F) ⟨placeMap_injective F, placeMap_surjective F⟩

/-- **`supp(Ψ_Φ z) = Ψ_Prime(supp z)`** for every effective `z`: `Ψ_Φ` maps `Φ_v` onto
`Φ_{Ψ_Prime(v)}`. -/
theorem supp_psiPhi {z : ArithDiv K} (hz : z ∈ effCone K) :
    supp (psiPhi F z hz) = placeEquiv F '' supp z := by
  ext q
  obtain ⟨p, rfl⟩ := placeMap_surjective F q
  rw [mem_supp_psiPhi F hz p]
  exact ⟨fun h => ⟨p, h, rfl⟩, fun ⟨p', hp', he⟩ => by
    rw [← placeMap_injective F he]; exact hp'⟩

end GlobalRealified

end Frobenioid

end Iut
