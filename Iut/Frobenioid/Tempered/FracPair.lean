/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.Birat

/-!
# Fraction-pairs ([EtTh], Definition 4.1(i), Proposition 4.2(i),(ii))

[EtTh] §4 ("bi-Kummer theory") works with a tempered Frobenioid `C` of model type and, for
`f ∈ O^×(A^birat)`, with **fraction-pairs** for `f` ([EtTh], Definition 4.1(i)): base-equivalent
pre-steps `s⊓, s⊔ : A → B` with `s⊓ · (s⊔)^{-1} = f ∈ O^×(A^birat)` whose zero divisors
`Div(s⊓)`, `Div(s⊔)` have disjoint supports. Here this is done for an arbitrary model Frobenioid
`C = Model Φ B divB` ([FrdI], Theorem 5.2), with `O^×(A^birat) = B(A_D)` (`Model.birUnitEquiv`,
`Iut/Frobenioid/Tempered/Birat.lean`).

**Disjoint supports.** [EtTh], Definition 4.1(i) refers to [FrdI], Proposition 4.1(iii): for a
perf-factorial `Φ` the zero divisors of two pre-steps `ε, ι` into `F` have disjoint supports iff
every pre-step `ζ` into `F` through which both factor is an isomorphism ("co-primary"). In the
model Frobenioid the pre-steps through which a pre-step factors correspond to the effective
divisors below its zero divisor, so the co-primary condition is the monoid condition
`Coprime a b`: every `c ∈ Φ(A)` with `a − c, b − c ∈ Φ(A)` is `0` (`Model.coprime_iff_coprimary`).
We use `Coprime` as the definition.

**Uniqueness of the divisors** ("`Div(s⊓)`, `Div(s⊔)` are uniquely determined by `f`",
Definition 4.1(i)) uses that a difference `a − b ∈ Φ^gp(A)` with `a, b ∈ Φ(A)` coprime determines
`a` and `b` (`DivMonoid.CoprimeUnique`). This holds for the perfect perf-factorial monoids of
[EtTh] §4 (`Φ` perfect, perf-factorial: [EtTh], Definition 3.6(i) and the hypotheses of §4): there
`Φ^gp(A)` embeds into a product of copies of `ℝ` with `Φ(A)` the nonnegative elements, closed under
coordinatewise minima (`DivMonoid.coprimeUnique_of_lattice`, which is how it is to be verified for
the genuine divisor monoid `Φ^ell_α` of [EtTh], Example 3.9). It is a hypothesis of the theorems
below.

## Main results

* `Model.IsFracPair s t f`: `(s, t)` is a (right) fraction-pair for `f ∈ B(A_D)`;
  `Model.toBirat_fracPair`: in `C^birat`, `s = f · t`, i.e. `s · t^{-1} = f`;
* `Model.div_eq_of_isFracPair`: the zero divisor and the divisor of poles are determined by `f`;
* `Model.isFracPair_iff` (**Proposition 4.2(i)**): `(t⊓, t⊔) : A → C` is a right fraction-pair for
  `f` iff `t⊓ = s⊓ ≫ v`, `t⊔ = s⊔ ≫ v` for an isomorphism `v : B ≅ C`, which is unique
  (`Model.cancel_preStep_left`);
* `Model.leftUnit`, `Model.IsLeftFracPair` and `Model.isLeftFracPair_iff` (**Proposition 4.2(ii)**):
  the same for left fraction-pairs `C → B` for `f|_B ∈ O^×(B^birat)`, with uniqueness from
  `Model.cancel_preStep_right` (pre-steps are monomorphisms).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u

variable {D : Type u} [Category.{v} D]

namespace DivMonoid

variable (Φ : DivMonoid.{w} D)

/-- **Coprime elements** of `Φ(A)` (no common nonzero effective divisor below both): the monoid
form of the co-primary condition of [FrdI], Proposition 4.1(iii) ("disjoint supports"). -/
def Coprime {A : D} (a b : Φ.obj A) : Prop :=
  ∀ c ∈ Φ.pos A, a - c ∈ Φ.pos A → b - c ∈ Φ.pos A → c = 0

/-- **Coprime decompositions are unique** in `Φ^gp(A)`: if `a − b = a' − b'` with `a, b, a', b'`
effective and both pairs coprime, then `a = a'` (hence `b = b'`). -/
def CoprimeUnique (A : D) : Prop :=
  ∀ ⦃a b a' b' : Φ.obj A⦄, a ∈ Φ.pos A → b ∈ Φ.pos A → a' ∈ Φ.pos A → b' ∈ Φ.pos A →
    Φ.Coprime a b → Φ.Coprime a' b' → a - b = a' - b' → a = a'

variable {Φ}

lemma Coprime.symm {A : D} {a b : Φ.obj A} (h : Φ.Coprime a b) : Φ.Coprime b a :=
  fun c hc hb ha => h c hc ha hb

lemma CoprimeUnique.eq {A : D} (h : Φ.CoprimeUnique A) {a b a' b' : Φ.obj A}
    (ha : a ∈ Φ.pos A) (hb : b ∈ Φ.pos A) (ha' : a' ∈ Φ.pos A) (hb' : b' ∈ Φ.pos A)
    (hab : Φ.Coprime a b) (hab' : Φ.Coprime a' b') (e : a - b = a' - b') : a = a' ∧ b = b' := by
  have h₁ := h ha hb ha' hb' hab hab' e
  refine ⟨h₁, ?_⟩
  subst h₁
  exact sub_right_injective e

/-- Coprimality is transported by pull-back along isomorphisms of `D`. -/
lemma coprime_pb_iff {A A' : D} (f : A ⟶ A') [IsIso f] {a b : Φ.obj A'} :
    Φ.Coprime (Φ.pb f a) (Φ.pb f b) ↔ Φ.Coprime a b := by
  have key : ∀ {X Y : D} (g : X ⟶ Y) [IsIso g] {a b : Φ.obj Y},
      Φ.Coprime a b → Φ.Coprime (Φ.pb g a) (Φ.pb g b) := by
    intro X Y g _ a b h c hc ha hb
    have hc' : Φ.pb (inv g) c ∈ Φ.pos Y := Φ.pb_mem _ hc
    have ha' := Φ.pb_mem (inv g) ha
    have hb' := Φ.pb_mem (inv g) hb
    rw [map_sub, GrpOn.pb_inv_pb] at ha' hb'
    have := h _ hc' ha' hb'
    have := congrArg (Φ.pb g) this
    rwa [GrpOn.pb_pb_inv, map_zero] at this
  refine ⟨fun h => ?_, key f⟩
  have := key (inv f) h
  simpa only [GrpOn.pb_inv_pb] using this

/-- **A criterion for `CoprimeUnique`** (the case of the perfect perf-factorial monoids of
[EtTh] §3–§4, [FrdI], Definition 2.4(i)): `Φ^gp(A)` embeds additively into `P → ℝ`, `Φ(A)` is
the set of elements with nonnegative coordinates, and the coordinatewise minimum of two effective
elements is again an element. -/
theorem coprimeUnique_of_lattice {A : D} {P : Type*} (ord : Φ.obj A →+ (P → ℝ))
    (hinj : Function.Injective ord) (hpos : ∀ x, x ∈ Φ.pos A ↔ ∀ p, 0 ≤ ord x p)
    (hmin : ∀ a ∈ Φ.pos A, ∀ b ∈ Φ.pos A, ∃ m, ∀ p, ord m p = min (ord a p) (ord b p)) :
    Φ.CoprimeUnique A := by
  -- coprime effective elements have disjoint supports
  have hdisj : ∀ a ∈ Φ.pos A, ∀ b ∈ Φ.pos A, Φ.Coprime a b →
      ∀ p, ord a p = 0 ∨ ord b p = 0 := by
    intro a ha b hb hab p
    obtain ⟨m, hm⟩ := hmin a ha b hb
    have ha' := (hpos a).1 ha
    have hb' := (hpos b).1 hb
    have hm0 : m = 0 := hab m ((hpos m).2 fun q => by rw [hm]; exact le_min (ha' q) (hb' q))
      ((hpos _).2 fun q => by
        rw [map_sub, Pi.sub_apply, hm]
        exact sub_nonneg.2 (min_le_left _ _))
      ((hpos _).2 fun q => by
        rw [map_sub, Pi.sub_apply, hm]
        exact sub_nonneg.2 (min_le_right _ _))
    have := hm p
    rw [hm0, map_zero, Pi.zero_apply] at this
    rcases le_total (ord a p) (ord b p) with h | h
    · left; rw [min_eq_left h] at this; exact this.symm
    · right; rw [min_eq_right h] at this; exact this.symm
  intro a b a' b' ha hb ha' hb' hab hab' e
  apply hinj
  funext p
  have e' := congrFun (congrArg ord e) p
  simp only [map_sub, Pi.sub_apply] at e'
  have h0a := (hpos a).1 ha p
  have h0b := (hpos b).1 hb p
  have h0a' := (hpos a').1 ha' p
  have h0b' := (hpos b').1 hb' p
  rcases hdisj a ha b hb hab p with h1 | h1 <;> rcases hdisj a' ha' b' hb' hab' p with h2 | h2 <;>
    linarith

end DivMonoid

namespace Model

variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-! ### Pre-steps of a model Frobenioid -/

/-- The relation of a pre-step: `α_X + Div(φ) = Base(φ)^* α_Y + Div_B(u_φ)`. -/
lemma rel_preStep {X Y : Model Φ B divB} {φ : X ⟶ Y} (h : IsPreStep 𝐏 φ) :
    X.α + φ.div = Φ.pb φ.base Y.α + divB.app _ φ.u := by
  have := φ.rel
  rwa [show φ.deg = 1 from h.1, PNat.one_coe, one_smul] at this

/-- **Pre-steps are epimorphisms** (total epimorphicity, in the form used for [EtTh],
Proposition 4.2(i)). -/
theorem cancel_preStep_left {X Y Z : Model Φ B divB} {s : X ⟶ Y} (hs : IsPreStep 𝐏 s)
    {v v' : Y ⟶ Z} (h : s ≫ v = s ≫ v') : v = v' := by
  haveI : IsIso s.base := hs.2
  have hd : s.deg = 1 := hs.1
  have h₁ := congrArg Hom.deg h
  have h₂ := congrArg Hom.base h
  have h₃ := congrArg Hom.div h
  have h₄ := congrArg Hom.u h
  simp only [comp_deg, comp_base, comp_div, comp_u, hd, mul_one] at h₁ h₂ h₃ h₄
  have hb : v.base = v'.base := (cancel_epi s.base).1 h₂
  rw [h₁, add_left_inj] at h₃ h₄
  refine hom_ext h₁ hb ?_ ?_
  · have := congrArg (Φ.pb (inv s.base)) h₃
    simpa only [GrpOn.pb_inv_pb] using this
  · have := congrArg (B.pb (inv s.base)) h₄
    simpa only [GrpOn.pb_inv_pb] using this

/-- **Pre-steps are monomorphisms** ([FrdI], Definition 1.3(v)(a); used for [EtTh],
Proposition 4.2(ii)). -/
theorem cancel_preStep_right {W X Y : Model Φ B divB} {s : X ⟶ Y} (hs : IsPreStep 𝐏 s)
    {v v' : W ⟶ X} (h : v ≫ s = v' ≫ s) : v = v' := by
  haveI : IsIso s.base := hs.2
  have hd : s.deg = 1 := hs.1
  have h₁ := congrArg Hom.deg h
  have h₂ := congrArg Hom.base h
  have h₃ := congrArg Hom.div h
  have h₄ := congrArg Hom.u h
  simp only [comp_deg, comp_base, comp_div, comp_u, hd, one_mul, PNat.one_coe, one_smul]
    at h₁ h₂ h₃ h₄
  have hb : v.base = v'.base := (cancel_mono s.base).1 h₂
  rw [hb, add_right_inj] at h₃ h₄
  exact hom_ext h₁ hb h₃ h₄

lemma isPreStep_comp₀ {X Y Z : Model Φ B divB} {s : X ⟶ Y} {t : Y ⟶ Z} (hs : IsPreStep 𝐏 s)
    (ht : IsPreStep 𝐏 t) : IsPreStep 𝐏 (s ≫ t) := by
  haveI : IsIso s.base := hs.2
  haveI : IsIso t.base := ht.2
  refine ⟨?_, ?_⟩
  · change (s ≫ t).deg = 1
    rw [comp_deg, show s.deg = 1 from hs.1, show t.deg = 1 from ht.1, mul_one]
  · change IsIso (s ≫ t).base
    rw [comp_base]
    infer_instance

lemma isPreStep_of_isIso {X Y : Model Φ B divB} (v : X ⟶ Y) [IsIso v] : IsPreStep 𝐏 v := by
  obtain ⟨h₁, h₂, -⟩ := (isIso_iff v).1 inferInstance
  exact ⟨h₁, h₂⟩

lemma div_of_isIso {X Y : Model Φ B divB} (v : X ⟶ Y) [IsIso v] : v.div = 0 :=
  ((isIso_iff v).1 inferInstance).2.2

/-! ### Fraction-pairs -/

/-- **Fraction-pairs** ([EtTh], Definition 4.1(i)): `s, t : X → Y` form a (right) fraction-pair
for `f ∈ B(X_D) = O^×(X^birat)` if they are base-equivalent pre-steps with `s · t^{-1} = f` (in
the model: `u_s − u_t = f`, see `toBirat_fracPair`) whose zero divisors are coprime
(disjoint supports, [FrdI], Proposition 4.1(iii)). `s` is the zero divisor part, `t` the
divisor of poles. -/
def IsFracPair {X Y : Model Φ B divB} (s t : X ⟶ Y) (f : B.obj X.base) : Prop :=
  IsPreStep 𝐏 s ∧ IsPreStep 𝐏 t ∧ s.base = t.base ∧ s.u - t.u = f ∧ Φ.Coprime s.div t.div

/-- The unit `f ∈ O^×(X^birat)` as an endomorphism of `X` in `C^birat` (`birUnit_eq`). -/
def birUnit (X : Model Φ B divB) (f : B.obj X.base) :
    (toBirat Φ B divB).obj X ⟶ (toBirat Φ B divB).obj X :=
  ⟨1, 𝟙 _, f⟩

@[simp] lemma birUnit_deg (X : Model Φ B divB) (f : B.obj X.base) : (birUnit X f).deg = 1 := rfl
@[simp] lemma birUnit_base (X : Model Φ B divB) (f : B.obj X.base) :
    (birUnit X f).base = 𝟙 _ := rfl
@[simp] lemma birUnit_u (X : Model Φ B divB) (f : B.obj X.base) : (birUnit X f).u = f := rfl

lemma birUnit_eq (X : Model Φ B divB) (f : B.obj X.base) :
    birUnit X f = (birUnitEquiv ((toBirat Φ B divB).obj X) f).1 := rfl

/-- **`s · t^{-1} = f` in `C^birat`**: for base-equivalent pre-steps `s, t` with `u_s − u_t = f`,
the image of `s` in `C^birat` is `f` followed by the image of `t`. -/
theorem toBirat_fracPair {X Y : Model Φ B divB} {s t : X ⟶ Y} (ht : IsPreStep 𝐏 t)
    (hst : s.deg = t.deg) (hb : s.base = t.base) {f : B.obj X.base} (hf : s.u - t.u = f) :
    (toBirat Φ B divB).map s = birUnit X f ≫ (toBirat Φ B divB).map t := by
  have hd : t.deg = 1 := ht.1
  ext
  · simp [hst, hd]
  · simp [hb]
  · change s.u = B.pb (𝟙 X.base) t.u + (t.deg : ℕ) • f
    rw [GrpOn.pb_id', hd, PNat.one_coe, one_smul, ← hf]
    abel

/-- The difference of the zero divisors of base-equivalent pre-steps is the divisor of
`u_s − u_t`. -/
lemma div_sub_div {X Y : Model Φ B divB} {s t : X ⟶ Y} (hs : IsPreStep 𝐏 s) (ht : IsPreStep 𝐏 t)
    (hb : s.base = t.base) : s.div - t.div = divB.app _ (s.u - t.u) := by
  have r₁ := rel_preStep hs
  have r₂ := rel_preStep ht
  rw [hb] at r₁
  rw [map_sub]
  linear_combination (norm := abel) r₁ - r₂

/-- **The divisors of a fraction-pair are determined by `f`** ([EtTh], Definition 4.1(i)). -/
theorem div_eq_of_isFracPair (hΦ : ∀ A, Φ.CoprimeUnique A) {X Y Y' : Model Φ B divB}
    {s t : X ⟶ Y} {s' t' : X ⟶ Y'} {f : B.obj X.base} (h : IsFracPair s t f)
    (h' : IsFracPair s' t' f) : s.div = s'.div ∧ t.div = t'.div := by
  obtain ⟨hs, ht, hb, hf, hc⟩ := h
  obtain ⟨hs', ht', hb', hf', hc'⟩ := h'
  refine (hΦ _).eq s.div_mem t.div_mem s'.div_mem t'.div_mem hc hc' ?_
  rw [div_sub_div hs ht hb, div_sub_div hs' ht' hb', hf, hf']

/-- Composing a fraction-pair with an isomorphism gives a fraction-pair for the same `f`. -/
lemma isFracPair_comp_iso {X Y Y' : Model Φ B divB} {s t : X ⟶ Y} {f : B.obj X.base}
    (h : IsFracPair s t f) (v : Y ⟶ Y') [IsIso v] : IsFracPair (s ≫ v) (t ≫ v) f := by
  obtain ⟨hs, ht, hb, hf, hc⟩ := h
  have hv := isPreStep_of_isIso v
  have hvd : v.deg = 1 := hv.1
  have hv0 := div_of_isIso v
  refine ⟨isPreStep_comp₀ hs hv, isPreStep_comp₀ ht hv, by simp [hb], ?_, ?_⟩
  · simp only [comp_u, hb, hvd, PNat.one_coe, one_smul]
    rw [← hf]
    abel
  · simpa [hv0, hvd] using hc

/-- **[EtTh], Proposition 4.2(i)**: if `(s, t) : X → Y` is a right fraction-pair for `f`, then a
pair `(s', t') : X → Y'` is a right fraction-pair for `f` iff `s' = s ≫ v`, `t' = t ≫ v` for an
isomorphism `v : Y ≅ Y'` (unique by `cancel_preStep_left`). -/
theorem isFracPair_iff (hΦ : ∀ A, Φ.CoprimeUnique A) {X Y Y' : Model Φ B divB} {s t : X ⟶ Y}
    {f : B.obj X.base} (h : IsFracPair s t f) (s' t' : X ⟶ Y') :
    IsFracPair s' t' f ↔ ∃ v : Y ≅ Y', s' = s ≫ v.hom ∧ t' = t ≫ v.hom := by
  constructor
  · intro h'
    obtain ⟨hd₁, hd₂⟩ := div_eq_of_isFracPair hΦ h h'
    obtain ⟨hs, ht, hb, hf, -⟩ := h
    obtain ⟨hs', ht', hb', hf', -⟩ := h'
    haveI : IsIso s.base := hs.2
    have r₁ := rel_preStep hs
    have r₂ := rel_preStep hs'
    let vb : Y.base ⟶ Y'.base := inv s.base ≫ s'.base
    have hvb : s.base ≫ vb = s'.base := by simp [vb]
    haveI : IsIso s'.base := hs'.2
    haveI : IsIso vb := by simp only [vb]; infer_instance
    let v : Y ⟶ Y' := mk1 vb 0 (Φ.pos _).zero_mem (B.pb (inv s.base) (s'.u - s.u)) (by
      apply (show Function.Injective (Φ.pb s.base) from fun a b hab => by
        simpa only [GrpOn.pb_inv_pb] using congrArg (Φ.pb (inv s.base)) hab)
      simp only [add_zero, map_add, divB.natural, ← GrpOn.pb_comp', hvb,
        IsIso.hom_inv_id, GrpOn.pb_id', map_sub]
      rw [hd₁] at r₁
      linear_combination (norm := abel) r₂ - r₁)
    haveI : IsIso v := isIso_of v rfl (by simp only [v, mk1_base]; infer_instance) rfl
    have hs_v : s' = s ≫ v := by
      have hsd : s.deg = 1 := hs.1
      have hs'd : s'.deg = 1 := hs'.1
      ext
      · simp [v, hsd, hs'd]
      · simp [v, hvb]
      · simp [v, hd₁]
      · simp [v, ← GrpOn.pb_comp']
    refine ⟨asIso v, hs_v, ?_⟩
    have htd : t.deg = 1 := ht.1
    have ht'd : t'.deg = 1 := ht'.1
    ext
    · simp [v, htd, ht'd]
    · simp [v, ← hb, ← hb', hvb]
    · simp [v, hd₂]
    · change t'.u = B.pb t.base v.u + (v.deg : ℕ) • t.u
      simp only [v, mk1_u, mk1_deg, PNat.one_coe, one_smul, ← hb, GrpOn.pb_pb_inv]
      rw [← hf'] at hf
      linear_combination (norm := abel) hf
  · rintro ⟨v, rfl, rfl⟩
    exact isFracPair_comp_iso h v.hom

/-! ### Left fraction-pairs -/

/-- **The unit `f|_Y ∈ O^×(Y^birat)` determined by a fraction-pair** `(s, t) : X → Y` ([EtTh],
Definition 4.1(i), [FrdI], Proposition 4.4(iv)): `t^{-1} · s`, i.e. `(Base t^{-1})^*(u_s − u_t)`
(`toBirat_leftUnit`). -/
noncomputable def leftUnit {X Y : Model Φ B divB} (s t : X ⟶ Y) [IsIso t.base] : B.obj Y.base :=
  B.pb (inv t.base) (s.u - t.u)

/-- In `C^birat`, `t ≫ f|_Y = s`, i.e. `f|_Y = t^{-1} · s`. -/
theorem toBirat_leftUnit {X Y : Model Φ B divB} {s t : X ⟶ Y} (ht : IsPreStep 𝐏 t)
    (hst : s.deg = t.deg) (hb : s.base = t.base) :
    haveI : IsIso t.base := ht.2
    (toBirat Φ B divB).map t ≫ birUnit Y (leftUnit s t) = (toBirat Φ B divB).map s := by
  haveI : IsIso t.base := ht.2
  have hd : t.deg = 1 := ht.1
  ext
  · simp [hst, hd]
  · simp [hb]
  · simp only [Birat.comp_u, birUnit_u, toBirat_map_u, toBirat_map_base, leftUnit,
      birUnit_deg, PNat.one_coe, one_smul]
    change B.pb t.base (B.pb (inv t.base) (s.u - t.u)) + t.u = s.u
    rw [GrpOn.pb_pb_inv]
    abel

/-- **Left fraction-pairs** ([EtTh], Definition 4.1(i)): `s, t : X → Y` form a left
fraction-pair for `g ∈ B(Y_D) = O^×(Y^birat)` if they are base-equivalent pre-steps with
coprime zero divisors and `t^{-1} · s = g`. -/
def IsLeftFracPair {X Y : Model Φ B divB} (s t : X ⟶ Y) (g : B.obj Y.base) : Prop :=
  IsPreStep 𝐏 s ∧ IsPreStep 𝐏 t ∧ s.base = t.base ∧ Φ.Coprime s.div t.div ∧
    ∀ _ : IsIso t.base, leftUnit s t = g

/-- A right fraction-pair for `f` is a left fraction-pair for `f|_Y`. -/
lemma IsFracPair.isLeftFracPair {X Y : Model Φ B divB} {s t : X ⟶ Y} {f : B.obj X.base}
    (h : IsFracPair s t f) [IsIso t.base] : IsLeftFracPair s t (leftUnit s t) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2, fun _ => rfl⟩

/-- The divisors of a left fraction-pair, transported to `Y` along the pre-steps, are determined
by `g`. -/
lemma pb_div_eq_of_isLeftFracPair (hΦ : ∀ A, Φ.CoprimeUnique A) {X X' Y : Model Φ B divB}
    {s t : X ⟶ Y} {s' t' : X' ⟶ Y} {g : B.obj Y.base} (h : IsLeftFracPair s t g)
    (h' : IsLeftFracPair s' t' g) [IsIso s.base] [IsIso s'.base] :
    Φ.pb (inv s.base) s.div = Φ.pb (inv s'.base) s'.div ∧
      Φ.pb (inv s.base) t.div = Φ.pb (inv s'.base) t'.div := by
  obtain ⟨hs, ht, hb, hc, hg⟩ := h
  obtain ⟨hs', ht', hb', hc', hg'⟩ := h'
  haveI : IsIso t.base := by rw [← hb]; infer_instance
  haveI : IsIso t'.base := by rw [← hb']; infer_instance
  refine (hΦ _).eq (Φ.pb_mem _ s.div_mem) (Φ.pb_mem _ t.div_mem) (Φ.pb_mem _ s'.div_mem)
    (Φ.pb_mem _ t'.div_mem) ((DivMonoid.coprime_pb_iff _).2 hc)
    ((DivMonoid.coprime_pb_iff _).2 hc') ?_
  have e := hg inferInstance
  have e' := hg' inferInstance
  rw [← map_sub, ← map_sub, div_sub_div hs ht hb, div_sub_div hs' ht' hb', ← divB.natural,
    ← divB.natural]
  congr 1
  rw [← e'] at e
  simpa only [leftUnit, hb, hb'] using e

/-- Precomposing a left fraction-pair with an isomorphism gives a left fraction-pair for the same
`g`. -/
lemma isLeftFracPair_iso_comp {W X Y : Model Φ B divB} {s t : X ⟶ Y} {g : B.obj Y.base}
    (h : IsLeftFracPair s t g) (v : W ⟶ X) [IsIso v] : IsLeftFracPair (v ≫ s) (v ≫ t) g := by
  obtain ⟨hs, ht, hb, hc, hg⟩ := h
  have hv := isPreStep_of_isIso v
  have hvd : v.deg = 1 := hv.1
  have hv0 := div_of_isIso v
  haveI : IsIso v.base := hv.2
  haveI : IsIso t.base := hb ▸ hs.2
  have hsd : s.deg = 1 := hs.1
  have htd : t.deg = 1 := ht.1
  refine ⟨isPreStep_comp₀ hv hs, isPreStep_comp₀ hv ht, by simp [hb], ?_, fun _ => ?_⟩
  · simpa [hv0, hsd, htd] using (DivMonoid.coprime_pb_iff v.base).2 hc
  · rw [← hg inferInstance]
    simp only [leftUnit, comp_u, comp_base, hsd, htd, PNat.one_coe, one_smul]
    rw [IsIso.inv_comp, GrpOn.pb_comp']
    congr 1
    rw [add_sub_add_right_eq_sub, ← map_sub, GrpOn.pb_inv_pb]

/-- **[EtTh], Proposition 4.2(ii)**: if `(s, t) : X → Y` is a left fraction-pair for `g`, then a
pair `(s', t') : X' → Y` is a left fraction-pair for `g` iff `s' = v ≫ s`, `t' = v ≫ t` for an
isomorphism `v : X' ≅ X` (unique by `cancel_preStep_right`). -/
theorem isLeftFracPair_iff (hΦ : ∀ A, Φ.CoprimeUnique A) {X X' Y : Model Φ B divB}
    {s t : X ⟶ Y} {g : B.obj Y.base} (h : IsLeftFracPair s t g) (s' t' : X' ⟶ Y) :
    IsLeftFracPair s' t' g ↔ ∃ v : X' ≅ X, s' = v.hom ≫ s ∧ t' = v.hom ≫ t := by
  constructor
  · intro h'
    have hs := h.1
    have hs' := h'.1
    haveI : IsIso s.base := hs.2
    haveI : IsIso s'.base := hs'.2
    obtain ⟨hd₁, hd₂⟩ := pb_div_eq_of_isLeftFracPair hΦ h h'
    obtain ⟨-, ht, hb, -, hg⟩ := h
    obtain ⟨-, ht', hb', -, hg'⟩ := h'
    haveI : IsIso t.base := by rw [← hb]; infer_instance
    haveI : IsIso t'.base := by rw [← hb']; infer_instance
    let vb : X'.base ⟶ X.base := s'.base ≫ inv s.base
    have hvb : vb ≫ s.base = s'.base := by simp [vb]
    haveI : IsIso vb := by simp only [vb]; infer_instance
    -- the divisors of `s'`, `t'` are the pull-backs of those of `s`, `t`
    have hds : s'.div = Φ.pb vb s.div := by
      have := congrArg (Φ.pb s'.base) hd₁
      rw [GrpOn.pb_pb_inv, ← GrpOn.pb_comp'] at this
      exact this.symm
    have hdt : t'.div = Φ.pb vb t.div := by
      have := congrArg (Φ.pb s'.base) hd₂
      rw [GrpOn.pb_pb_inv, ← GrpOn.pb_comp'] at this
      exact this.symm
    have r₁ := congrArg (Φ.pb vb) (rel_preStep hs)
    have r₂ := rel_preStep hs'
    simp only [map_add, ← GrpOn.pb_comp', hvb, ← divB.natural] at r₁
    let v : X' ⟶ X := mk1 vb 0 (Φ.pos _).zero_mem (s'.u - B.pb vb s.u) (by
      rw [map_sub, hds] at *
      linear_combination (norm := abel) r₂ - r₁)
    haveI : IsIso v := isIso_of v rfl (by simp only [v, mk1_base]; infer_instance) rfl
    have hsd : s.deg = 1 := hs.1
    have hs'd : s'.deg = 1 := hs'.1
    have htd : t.deg = 1 := ht.1
    have ht'd : t'.deg = 1 := ht'.1
    refine ⟨asIso v, ?_, ?_⟩
    · ext
      · simp [v, hsd, hs'd]
      · simp [v, hvb]
      · simp [v, hsd, hds]
      · simp [v, hsd]
    · -- the rational functions: `u_{s'} − u_{t'} = vb^*(u_s − u_t)` (both pairs give `g`)
      have key : s'.u - t'.u = B.pb vb (s.u - t.u) := by
        have e := hg inferInstance
        have e' := hg' inferInstance
        rw [← e'] at e
        simp only [leftUnit] at e
        have e2 := congrArg (B.pb t'.base) e
        rw [GrpOn.pb_pb_inv] at e2
        have hvb' : t'.base ≫ inv t.base = vb := by
          change t'.base ≫ inv t.base = s'.base ≫ inv s.base
          rw [IsIso.comp_inv_eq, Category.assoc, ← hb, IsIso.inv_hom_id, Category.comp_id, hb']
        rw [← e2, ← GrpOn.pb_comp', hvb']
      ext
      · simp [v, htd, ht'd]
      · simp [v, ← hb, ← hb', hvb]
      · simp [v, htd, hdt]
      · change t'.u = B.pb vb t.u + (t.deg : ℕ) • (s'.u - B.pb vb s.u)
        rw [htd, PNat.one_coe, one_smul]
        rw [map_sub] at key
        linear_combination (norm := abel) (-1 : ℤ) • key
  · rintro ⟨v, rfl, rfl⟩
    exact isLeftFracPair_iso_comp h v.hom

/-! ### Co-primary pre-steps -/

/-- The zero divisor of a composite `a ≫ ζ` (with `ζ` linear), transported to the codomain. -/
lemma pushDiv_comp {E Z F : Model Φ B divB} (a : E ⟶ Z) (ζ : Z ⟶ F) [IsIso a.base]
    [IsIso ζ.base] [IsIso (a ≫ ζ).base] (hζd : ζ.deg = 1) :
    Φ.pb (inv (a ≫ ζ).base) (a ≫ ζ).div =
      Φ.pb (inv ζ.base) ζ.div + Φ.pb (inv (a ≫ ζ).base) a.div := by
  have h1 : inv (a ≫ ζ).base = inv ζ.base ≫ inv a.base := IsIso.inv_comp (f := a.base) (h := ζ.base)
  rw [h1, comp_div, hζd, PNat.one_coe, one_smul, GrpOn.pb_comp', GrpOn.pb_comp', map_add, map_add,
    GrpOn.pb_inv_pb]

/-- **The monoid form of "co-primary"** ([FrdI], Proposition 4.1(iii)) in a model Frobenioid:
the zero divisors of two pre-steps `ε : E → F`, `ι : I → F`, transported to `F`, are coprime iff
every pre-step `ζ : Z → F` through which both factor (by pre-steps) is an isomorphism. -/
theorem coprime_iff_coprimary {E I F : Model Φ B divB} {ε : E ⟶ F} {ι : I ⟶ F}
    (hε : IsPreStep 𝐏 ε) (hι : IsPreStep 𝐏 ι) :
    haveI : IsIso ε.base := hε.2
    haveI : IsIso ι.base := hι.2
    Φ.Coprime (Φ.pb (inv ε.base) ε.div) (Φ.pb (inv ι.base) ι.div) ↔
      ∀ (Z : Model Φ B divB) (ζ : Z ⟶ F) (ε' : E ⟶ Z) (ι' : I ⟶ Z), IsPreStep 𝐏 ζ →
        IsPreStep 𝐏 ε' → IsPreStep 𝐏 ι' → ε' ≫ ζ = ε → ι' ≫ ζ = ι → IsIso ζ := by
  haveI : IsIso ε.base := hε.2
  haveI : IsIso ι.base := hι.2
  have hεd : ε.deg = 1 := hε.1
  have hιd : ι.deg = 1 := hι.1
  constructor
  · intro hc Z ζ ε' ι' hζ hε' hι' e₁ e₂
    subst e₁ e₂
    haveI : IsIso ζ.base := hζ.2
    haveI : IsIso ε'.base := hε'.2
    haveI : IsIso ι'.base := hι'.2
    have hζd : ζ.deg = 1 := hζ.1
    -- `Div ζ` transported to `F` lies below both transported divisors
    set c := Φ.pb (inv ζ.base) ζ.div with hcdef
    have hdiv₁ := pushDiv_comp ε' ζ hζd
    have hdiv₂ := pushDiv_comp ι' ζ hζd
    rw [← hcdef] at hdiv₁ hdiv₂
    have hc0 : c = 0 := hc c (Φ.pb_mem _ ζ.div_mem)
      (by rw [hdiv₁, add_sub_cancel_left]; exact Φ.pb_mem _ ε'.div_mem)
      (by rw [hdiv₂, add_sub_cancel_left]; exact Φ.pb_mem _ ι'.div_mem)
    have hζ0 : ζ.div = 0 := by
      have := congrArg (Φ.pb ζ.base) hc0
      rwa [hcdef, GrpOn.pb_pb_inv, map_zero] at this
    exact isIso_of ζ hζd inferInstance hζ0
  · intro hcp c hc ha hb
    -- the pre-step `ζ : (F, α_F − c) → F` with zero divisor `c`
    let Z : Model Φ B divB := ⟨F.base, F.α - c⟩
    let ζ : Z ⟶ F := mk1 (𝟙 _) c hc 0 (by simp [Z])
    have hζ : IsPreStep 𝐏 ζ := isPreStep_mk1 _ _ _ _ _
    -- `ε' : E → Z` with zero divisor `ε.base^*(ε_* Div ε − c)`
    have hε'm : Φ.pb ε.base (Φ.pb (inv ε.base) ε.div - c) ∈ Φ.pos E.base := Φ.pb_mem _ ha
    let ε' : E ⟶ Z := mk1 ε.base _ hε'm ε.u (by
      have r := rel_preStep hε
      simp only [Z, map_sub, ← GrpOn.pb_comp', IsIso.hom_inv_id, GrpOn.pb_id']
      linear_combination (norm := abel) r)
    have hι'm : Φ.pb ι.base (Φ.pb (inv ι.base) ι.div - c) ∈ Φ.pos I.base := Φ.pb_mem _ hb
    let ι' : I ⟶ Z := mk1 ι.base _ hι'm ι.u (by
      have r := rel_preStep hι
      simp only [Z, map_sub, ← GrpOn.pb_comp', IsIso.hom_inv_id, GrpOn.pb_id']
      linear_combination (norm := abel) r)
    have hiso := hcp Z ζ ε' ι' hζ (isPreStep_mk1 _ _ _ _ _) (isPreStep_mk1 _ _ _ _ _)
      (by
        ext
        · simp [ε', ζ, hεd]
        · simp [ε', ζ]
        · simp [ε', ζ, map_sub, ← GrpOn.pb_comp']
        · simp [ε', ζ])
      (by
        ext
        · simp [ι', ζ, hιd]
        · simp [ι', ζ]
        · simp [ι', ζ, map_sub, ← GrpOn.pb_comp']
        · simp [ι', ζ])
    exact div_of_isIso ζ

end Model

end Frobenioid

end Iut
