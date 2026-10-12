/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.ModelFrobenioid
import Iut.Frobenioid.TemperedBase
import TemperedFundamentalGroups.Andre.TateObject

/-!
# Tempered Frobenioids ([EtTh] §3) and the theta divisors of the `ℤ`-covering

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*,
§3 (Definitions 3.1, 3.3, 3.6, Theorem 3.7). For a hyperbolic orbicurve `X^log` over a
`p`-adic field with split stable reduction (in IUT: the Tate orbicurves `X_v`, `v ∈ V^bad`):

* the base category `D₀ = B^temp(Π^tp_X)⁰` is the category of connected tempered coverings,
  i.e. of transitive `Π^tp_X`-sets with open stabilizers;
* `Φ₀(Y)` is a monoid of effective log-divisors supported on the special fibre (and the cusps)
  of combinatorial coverings, `B₀(Y)` a group of log-meromorphic functions, and `B₀ → Φ₀^gp` the
  divisor map;

and the **tempered Frobenioid** is the model Frobenioid of `(D₀, Φ₀, B₀)` ([EtTh], Definition
3.6, Theorem 3.7; [FrdI], Theorem 5.2).

## What is formalised

* `TemperedFrobenioidData G`: for a topological group `G` (the tempered fundamental group),
  the data `(Φ₀, B₀, div₀)` on the **actual** base category `D₀ = OrbitObj G = B^temp(G)⁰`
  (`Iut/Frobenioid/TemperedBase.lean`, which proves that `D₀` is connected and totally
  epimorphic). `TemperedFrobenioidData.isFrobenioid`: the tempered Frobenioid **is a
  Frobenioid** ([EtTh], Theorem 3.7; [FrdI], Theorem 5.2(ii)).
* **The theta instance** `thetaData χ`, for a character `χ : G → ℤ` (the `ℤ`-covering
  `Y → X`, `Gal(Y/X) = ℤ`, whose special fibre is a chain of components labelled by `ℤ`):
  - `divMonoid χ` (`Φ₀`): for an object `G/H`, the `G`-invariant `ℤ`-valued functions on
    `(G/H) × ℤ` — the special-fibre divisors of `Y_H ×_X Y` pulled back from the components of
    `Y` (`G` acts on the labels `ℤ` by translation through `χ`), effective if `≥ 0`;
  - `thetaGrp χ` (`B₀`): the divisors of the theta monomials, the functions of the shape
    `a + b·j + c·j²` in the label `j` of the component — `div(q^{1/2}) = 1`, `div(Ü) = j`,
    `div(Θ̈) = -j²` (the zero/pole orders of `Θ̈ = ∑ (-1)ⁿ q^{n(n+1)/2} Ü^{2n+1}` along the
    components, normalized by `ord(√q) = 1`; [EtTh], §1, the divisor `D_N`);
  - `thetaDiv χ`: the inclusion `B₀ ⊆ Φ₀^gp`.
  `thetaData_isFrobenioid`: the resulting tempered Frobenioid is a Frobenioid.
* On `Y = G/ker χ` (`objY`): `divU`, `divTheta`, `divOne ∈ B₀(Y)` and the **Frobenioid-theoretic
  functional equation** of the theta function `pb_deck_divTheta`: pulled back along the deck
  transformation `τ_d` of `Y` (`χ(d) = a`), `div(Θ̈) ↦ div(Θ̈) + 2a·div(Ü) - a²·div(√q)` — the
  divisor of `Θ̈(s^{-a}Ü) = (-1)^a s^{-a²} Ü^{2a} Θ̈(Ü)` ([EtTh], Prop. 1.4(ii)).
* `tateThetaData`: the theta instance for the tempered fundamental group of the Tate curve
  (`G = temperedPi1 O R A V hV`, `χ = TateObject.character`), so that `isFrobenioid` applies to
  an actual construction from `tempered-fundamental-groups`.

## What is not constructed

The divisors in `Φ₀` are those pulled back from the dual graph of `Y` (components of `Y_H ×_X Y`
over a component of `Y` are not separated), the cusps are omitted, and `B₀` consists of
divisors of theta monomials rather than of meromorphic functions on stable models of the
universal combinatorial coverings `Z^log_∞` (which `tempered-fundamental-groups` does not provide:
it works with projective models of finite levels and covering spaces of special fibres, with no
structure sheaf on infinite coverings). In particular `B₀ → Φ₀^gp` is injective here, while in
[EtTh] its kernel is the group of units `O^×`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe u

/-- **The data of a tempered Frobenioid** ([EtTh], Definitions 3.3, 3.6) on the base category
`D₀ = B^temp(G)⁰ = OrbitObj G` of connected tempered coverings. -/
structure TemperedFrobenioidData (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The divisor monoid `Φ₀` of effective log-divisors. -/
  Φ₀ : DivMonoid.{u} (OrbitObj G)
  /-- The rational function monoid `B₀` of log-meromorphic functions. -/
  B₀ : GrpOn.{u} (OrbitObj G)
  /-- The divisor of zeroes and poles `B₀ → Φ₀^gp`. -/
  div₀ : DivHom B₀ Φ₀.toGrpOn

namespace TemperedFrobenioidData

variable {G : Type u} [Group G] [TopologicalSpace G] (T : TemperedFrobenioidData G)

/-- **The tempered Frobenioid** `C₀` ([EtTh], Definition 3.6): the model Frobenioid of
`(D₀, Φ₀, B₀)`. -/
abbrev Frob : Type u := Model T.Φ₀ T.B₀ T.div₀

/-- **The tempered Frobenioid is a Frobenioid** ([EtTh], Theorem 3.7; [FrdI], Theorem
5.2(ii)): `D₀ = B^temp(G)⁰` is connected and totally epimorphic. -/
theorem isFrobenioid : IsFrobenioid (Model.toElem T.Φ₀ T.B₀ T.div₀) :=
  Model.isFrobenioid

/-- The projection of the tempered Frobenioid to its base category `B^temp(G)⁰`. -/
def toBase : T.Frob ⥤ OrbitObj G := Model.forget T.Φ₀ T.B₀ T.div₀

end TemperedFrobenioidData

/-! ### The divisor monoid of the `ℤ`-covering -/

section Theta

variable {G : Type u} [Group G] [TopologicalSpace G] (χ : G →* Multiplicative ℤ)

/-- **`Φ₀^gp(G/H)`**: the `G`-invariant functions `(G/H) × ℤ → ℤ` (`G` acting on the labels
`ℤ` of the components of `Y` by translation through `χ`). -/
def divGp (A : OrbitObj G) : AddSubgroup ((G ⧸ A.H) × ℤ → ℤ) where
  carrier := {f | ∀ (g : G) (x : G ⧸ A.H) (n : ℤ), f (g • x, n + (χ g).toAdd) = f (x, n)}
  add_mem' {f f'} hf hf' g x n := by
    simp only [Set.mem_setOf_eq, Pi.add_apply] at hf hf' ⊢
    rw [hf, hf']
  zero_mem' _ _ _ := rfl
  neg_mem' {f} hf g x n := by
    simp only [Set.mem_setOf_eq, Pi.neg_apply] at hf ⊢
    rw [hf]

variable {χ}

/-- The pull-back along an equivariant map `G/H → G/H'`. -/
def pbFun {A B : OrbitObj G} (F : G ⧸ A.H → G ⧸ B.H) (hF : ∀ (g : G) x, F (g • x) = g • F x) :
    divGp χ B →+ divGp χ A where
  toFun f := ⟨fun z => f.1 (F z.1, z.2), fun g x n => by
    simp only [hF]
    exact f.2 g (F x) n⟩
  map_zero' := rfl
  map_add' _ _ := rfl

lemma pbFun_apply {A B : OrbitObj G} (F : G ⧸ A.H → G ⧸ B.H) (hF) (f : divGp χ B) (z) :
    (pbFun F hF f).1 z = f.1 (F z.1, z.2) := rfl

lemma pbFun_injective {A B : OrbitObj G} {F : G ⧸ A.H → G ⧸ B.H} (hF)
    (hs : Function.Surjective F) : Function.Injective (pbFun (χ := χ) F hF) := by
  intro f f' h
  apply Subtype.ext
  funext ⟨y, n⟩
  obtain ⟨x, rfl⟩ := hs y
  exact congrFun (congrArg Subtype.val h) (x, n)

/-- The inverse of a bijective equivariant map is equivariant. -/
lemma symm_smul {A B : OrbitObj G} {F : G ⧸ A.H → G ⧸ B.H} (hF : ∀ (g : G) x, F (g • x) = g • F x)
    (hb : Function.Bijective F) (g : G) (y : G ⧸ B.H) :
    (Equiv.ofBijective F hb).symm (g • y) = g • (Equiv.ofBijective F hb).symm y := by
  apply (Equiv.ofBijective F hb).injective
  rw [Equiv.apply_symm_apply, Equiv.ofBijective_apply, hF, ← Equiv.ofBijective_apply F hb,
    Equiv.apply_symm_apply]

lemma pbFun_bijective {A B : OrbitObj G} {F : G ⧸ A.H → G ⧸ B.H} (hF)
    (hb : Function.Bijective F) : Function.Bijective (pbFun (χ := χ) F hF) := by
  refine ⟨pbFun_injective hF hb.2, fun f => ⟨pbFun _ (symm_smul hF hb) f, ?_⟩⟩
  apply Subtype.ext
  funext ⟨x, n⟩
  change f.1 ((Equiv.ofBijective F hb).symm (F x), n) = f.1 (x, n)
  rw [← Equiv.ofBijective_apply F hb, Equiv.symm_apply_apply]

variable [IsTopologicalGroup G]

variable (χ) in
/-- **`Φ₀^gp` as a group-like monoid on `B^temp(G)⁰`.** -/
def divGrp : GrpOn.{u} (OrbitObj G) where
  obj A := divGp χ A
  pb f := pbFun f.toFun f.map_smul
  pb_id _ _ := rfl
  pb_comp _ _ _ := rfl
  pb_injective f := pbFun_injective f.map_smul f.surjective
  pb_bijective_of_fsm _ hf := pbFun_bijective _ (OrbitHom.bijective_of_isFSM hf)

/-- The effective divisors: the nonnegative functions. -/
def nonneg (A : OrbitObj G) : AddSubmonoid (divGp χ A) where
  carrier := {f | ∀ z, 0 ≤ f.1 z}
  add_mem' hf hf' z := add_nonneg (hf z) (hf' z)
  zero_mem' _ := le_refl 0

/-- The positive part `max(f, 0)` of an invariant function. -/
def posPart {A : OrbitObj G} (f : divGp χ A) : divGp χ A :=
  ⟨fun z => max (f.1 z) 0, fun g x n => by simp only [f.2 g x n]⟩

omit [IsTopologicalGroup G] in
lemma sharp_aux {A : OrbitObj G} {x : divGp χ A} (hx : ∀ z, 0 ≤ x.1 z)
    (hx' : ∀ z, 0 ≤ (-x).1 z) : x = 0 := by
  refine Subtype.ext (funext fun z => le_antisymm ?_ (hx z))
  have := hx' z
  simp only [AddSubgroup.coe_neg, Pi.neg_apply, Left.nonneg_neg_iff] at this
  exact this

omit [IsTopologicalGroup G] in
lemma saturated_aux {A : OrbitObj G} {x : divGp χ A} (n : ℕ) (hn : 0 < n)
    (h : ∀ z, 0 ≤ (n • x).1 z) (z) : 0 ≤ x.1 z := by
  have := h z
  simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] at this
  exact nonneg_of_mul_nonneg_right this (by exact_mod_cast hn)

omit [IsTopologicalGroup G] in
lemma generating_aux {A : OrbitObj G} (x : divGp χ A) : x = posPart x - posPart (-x) := by
  refine Subtype.ext (funext fun z => ?_)
  change x.1 z = max (x.1 z) 0 - max (-x.1 z) 0
  rcases le_total (x.1 z) 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    ring
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]
    ring

variable (χ) in
/-- **The divisor monoid `Φ₀`** ([EtTh], Definition 3.3, restricted to the special-fibre divisors
pulled back from the components of `Y`). -/
def divMonoid : DivMonoid.{u} (OrbitObj G) where
  toGrpOn := divGrp χ
  pos A := nonneg A
  pb_mem _ _ hx z := hx _
  sharp hx hx' := sharp_aux hx hx'
  saturated n hn h := saturated_aux n hn h
  generating x := ⟨posPart x, fun _ => le_max_right _ _, posPart (-x),
    fun _ => le_max_right _ _, generating_aux x⟩
  pos_surj_of_fsm {A B} f hf y hy := by
    obtain ⟨x, hx⟩ := (divGrp χ).pb_bijective_of_fsm f hf |>.2 y
    refine ⟨x, fun z => ?_, hx⟩
    obtain ⟨w, hw⟩ := (OrbitHom.bijective_of_isFSM hf).2 z.1
    have := hy (w, z.2)
    rw [← hx] at this
    change 0 ≤ x.1 (f.toFun w, z.2) at this
    rwa [hw] at this

/-! ### The divisors of the theta monomials -/

variable (χ) in
/-- The divisors of shape `a + b·j + c·j²` in the label `j = n - χ(g)` of the component. -/
def IsThetaShape (A : OrbitObj G) (f : (G ⧸ A.H) × ℤ → ℤ) : Prop :=
  ∃ a b c : ℤ, ∀ (g : G) (n : ℤ),
    f (QuotientGroup.mk g, n) = a + b * (n - (χ g).toAdd) + c * (n - (χ g).toAdd) ^ 2

omit [IsTopologicalGroup G] in
lemma isThetaShape_comp {A B : OrbitObj G} (F : G ⧸ A.H → G ⧸ B.H)
    (hF : ∀ (g : G) x, F (g • x) = g • F x) {f : (G ⧸ B.H) × ℤ → ℤ}
    (hf : IsThetaShape χ B f) : IsThetaShape χ A (fun z => f (F z.1, z.2)) := by
  obtain ⟨a, b, c, h⟩ := hf
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective (F (QuotientGroup.mk 1))
  set t := (χ g₀).toAdd
  refine ⟨a - b * t + c * t ^ 2, b - 2 * c * t, c, fun g n => ?_⟩
  have hFg : F (QuotientGroup.mk g) = QuotientGroup.mk (g * g₀) := by
    rw [OrbitHom.mk_eq_smul (A := A), hF, ← hg₀, MulAction.Quotient.smul_mk, smul_eq_mul]
  simp only [hFg, h, map_mul, toAdd_mul]
  ring

variable (χ) in
/-- **`B₀(G/H)`**: the invariant divisors of theta monomials. -/
def thetaGp (A : OrbitObj G) : AddSubgroup (divGp χ A) where
  carrier := {f | IsThetaShape χ A f.1}
  add_mem' {f f'} := by
    rintro ⟨a, b, c, h⟩ ⟨a', b', c', h'⟩
    refine ⟨a + a', b + b', c + c', fun g n => ?_⟩
    simp only [AddSubgroup.coe_add, Pi.add_apply, h, h']
    ring
  zero_mem' := ⟨0, 0, 0, fun _ _ => by simp⟩
  neg_mem' {f} := by
    rintro ⟨a, b, c, h⟩
    refine ⟨-a, -b, -c, fun g n => ?_⟩
    simp only [AddSubgroup.coe_neg, Pi.neg_apply, h]
    ring

/-- The pull-back on theta divisors. -/
def pbTheta {A B : OrbitObj G} (F : G ⧸ A.H → G ⧸ B.H) (hF : ∀ (g : G) x, F (g • x) = g • F x) :
    thetaGp χ B →+ thetaGp χ A where
  toFun f := ⟨pbFun F hF f.1, isThetaShape_comp F hF f.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

variable (χ) in
/-- **The group `B₀` of theta-monomial divisors** on `B^temp(G)⁰`. -/
def thetaGrp : GrpOn.{u} (OrbitObj G) where
  obj A := thetaGp χ A
  pb f := pbTheta f.toFun f.map_smul
  pb_id _ _ := rfl
  pb_comp _ _ _ := rfl
  pb_injective f x y h :=
    Subtype.ext (pbFun_injective f.map_smul f.surjective (congrArg Subtype.val h))
  pb_bijective_of_fsm f hf := by
    have hb := OrbitHom.bijective_of_isFSM hf
    refine ⟨fun x y h => Subtype.ext (pbFun_injective f.map_smul hb.2 (congrArg Subtype.val h)),
      fun y => ⟨pbTheta _ (symm_smul f.map_smul hb) y, ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    funext ⟨x, n⟩
    change y.1.1 ((Equiv.ofBijective f.toFun hb).symm (f.toFun x), n) = y.1.1 (x, n)
    rw [← Equiv.ofBijective_apply f.toFun hb, Equiv.symm_apply_apply]

variable (χ) in
/-- **The divisor map `B₀ → Φ₀^gp`**: the inclusion. -/
def thetaDiv : DivHom (thetaGrp χ) (divMonoid χ).toGrpOn where
  app A := (thetaGp χ A).subtype
  natural _ _ := rfl

variable (χ) in
/-- **The tempered Frobenioid of theta divisors** of the `ℤ`-covering defined by `χ`. -/
def thetaData : TemperedFrobenioidData G where
  Φ₀ := divMonoid χ
  B₀ := thetaGrp χ
  div₀ := thetaDiv χ

variable (χ) in
/-- **The tempered Frobenioid of theta divisors is a Frobenioid.** -/
theorem thetaData_isFrobenioid :
    IsFrobenioid (Model.toElem (thetaData χ).Φ₀ (thetaData χ).B₀ (thetaData χ).div₀) :=
  (thetaData χ).isFrobenioid

/-! ### The `ℤ`-covering `Y` and the divisor of the theta function -/

section Y

variable (hχ : Continuous χ)

omit [IsTopologicalGroup G] in
include hχ in
lemma isOpen_ker : IsOpen (χ.ker : Set G) := (isOpen_discrete ({1} : Set _)).preimage hχ

/-- **The object `Y = G/ker χ`** of `B^temp(G)⁰`: the `ℤ`-covering. -/
abbrev objY : OrbitObj G := ⟨χ.ker, isOpen_ker hχ⟩

/-- The label `j` of the component of `Y` through a point of the fibre (for `n = 0`). -/
def labY (x : G ⧸ χ.ker) : ℤ := (QuotientGroup.kerLift χ x).toAdd

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma labY_smul (g : G) (x : G ⧸ χ.ker) : labY (χ := χ) (g • x) = (χ g).toAdd + labY x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    simp only [labY, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.kerLift_mk,
      map_mul, toAdd_mul]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma labY_mk (g : G) : labY (χ := χ) (QuotientGroup.mk g) = (χ g).toAdd := rfl

/-- A divisor of `Y` given by a function of the label `n - labY x`. -/
def labDiv (φ : ℤ → ℤ) : divGp χ (objY hχ) :=
  ⟨fun z => φ (z.2 - labY z.1), fun g x n => by
    simp only [labY_smul]
    congr 1
    ring⟩

/-- `div(√q) = 1`. -/
def divOne : thetaGp χ (objY hχ) := ⟨labDiv hχ fun _ => 1, ⟨1, 0, 0, fun g n => by
  simp [labDiv]⟩⟩

/-- `div(Ü) = j`. -/
def divU : thetaGp χ (objY hχ) := ⟨labDiv hχ fun j => j, ⟨0, 1, 0, fun g n => by
  simp [labDiv, labY_mk]⟩⟩

/-- **`div(Θ̈) = -j²`** ([EtTh], §1: the zero/pole orders of `Θ̈` along the components of the
special fibre, `ord(√q) = 1`). -/
def divTheta : thetaGp χ (objY hχ) := ⟨labDiv hχ fun j => -j ^ 2, ⟨0, 0, -1, fun g n => by
  simp [labDiv, labY_mk]⟩⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma smul_eq_mk_mul (g : G) (x : G ⧸ χ.ker) : g • x = (QuotientGroup.mk g : G ⧸ χ.ker) * x := by
  induction x using QuotientGroup.induction_on with
  | H a => rfl

/-- **The deck transformation `τ_d` of `Y`** (`d ∈ G`): `x ↦ x·d` on `G/ker χ`. -/
def deck (d : G) : objY hχ ⟶ objY hχ where
  toFun x := x * QuotientGroup.mk d
  map_smul g x := by
    rw [smul_eq_mk_mul, smul_eq_mk_mul, mul_assoc]

/-- **The functional equation of the theta function, divisor form** ([EtTh], Prop. 1.4(ii)):
along the deck transformation `τ_d` (`a = χ(d)`),
`τ_d^* div(Θ̈) = div(Θ̈) + 2a·div(Ü) - a²·div(√q)`, the divisor of
`Θ̈(s^{-a}Ü) = (-1)^a s^{-a²} Ü^{2a} Θ̈(Ü)`. -/
theorem pb_deck_divTheta (d : G) :
    (thetaGrp χ).pb (deck hχ d) (divTheta hχ) =
      divTheta hχ + (2 * (χ d).toAdd) • divU hχ - ((χ d).toAdd ^ 2) • divOne hχ := by
  apply Subtype.ext
  apply Subtype.ext
  funext ⟨x, n⟩
  induction x using QuotientGroup.induction_on with
  | H g =>
    change -(n - labY (QuotientGroup.mk g * QuotientGroup.mk d)) ^ 2 = _
    simp only [AddSubgroup.coe_sub, AddSubgroup.coe_add, AddSubgroup.coe_zsmul, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change _ = -(n - labY (χ := χ) (QuotientGroup.mk g)) ^ 2 +
      2 * (χ d).toAdd * (n - labY (χ := χ) (QuotientGroup.mk g)) - (χ d).toAdd ^ 2 * 1
    rw [← QuotientGroup.mk_mul, labY_mk, labY_mk, map_mul, toAdd_mul]
    ring

end Y

end Theta

/-! ### The tempered fundamental group of the Tate curve -/

section Tate

open TemperedFundamentalGroups

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A] (T : TateObject.Data O R)
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **The tempered Frobenioid of theta divisors of the Tate curve**: `D₀ = B^temp(Π^tp_X)⁰` for
the tempered fundamental group `Π^tp_X = temperedPi1 O R A V hV` of
`tempered-fundamental-groups`, with the theta divisors of its `ℤ`-covering `Y = X₀`
(`TateObject.character`). -/
noncomputable def tateThetaData : TemperedFrobenioidData (temperedPi1 O R A V hV) :=
  thetaData (TateObject.character (A := A) T V hV)

/-- **The tempered Frobenioid of the Tate curve is a Frobenioid.** -/
theorem tateThetaData_isFrobenioid :
    IsFrobenioid (Model.toElem (tateThetaData T V hV).Φ₀ (tateThetaData T V hV).B₀
      (tateThetaData (A := A) T V hV).div₀) :=
  (tateThetaData T V hV).isFrobenioid

/-- The object `Y` (the `ℤ`-covering `X₀`) of `B^temp(Π^tp_X)⁰`; its subgroup is `Π^tp_Y`. -/
noncomputable abbrev tateY : OrbitObj (temperedPi1 O R A V hV) :=
  objY (TateObject.continuous_character (A := A) T V hV)

end Tate

end Frobenioid

end Iut
