/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.ModelFrobenioid
import Iut.Frobenioid.TemperedBase
import TemperedFundamentalGroups.Andre.TateObject
import Iut.Frobenioid.Tempered.EllDiv
import Iut.Frobenioid.Tempered.PrimeDiv

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
* **The theta instance** `thetaData χ hs`, for a character `χ : G → ℤ` (the `ℤ`-covering
  `Y → X`, `Gal(Y/X) = ℤ`, whose special fibre is a chain of components labelled by `ℤ`) and
  the analytic model `Ÿ_∞ = 𝔾_m^an` (coordinate `Ü`) over a complete ultrametric field `K` with
  Tate parameter `t` and `s² = q` (`BAn`, `Tempered/EllDiv.lean`):
  - `ellDivMonoid χ hs` (`Φ₀`) = `PrimeDiv.divMonoid G P ℚ` on the **elliptic prime set**
    `P = ThetaP χ hs = ℤ ⊕ Cusps` (components of the special fibre ⊕ cusps `Ü² ∈ q^ℤ`; [EtTh]
    Prop 3.2(i)), `G` acting through the deck transformations `g ↦ s^{χ(g)}` (`chiDeck`), with
    coefficients `ℚ` (the perfection, [EtTh] Ex 3.9(iii)) normalised by `ord(q) = 1`
    ([EtTh] l.1028–1034);
  - `thetaGrp χ hs` (`B₀`): the divisors of the theta monomials `q^{a/2} Ü^b Θ̈^{-c}`,
    `(a + b·j + c·j²)/2` on the component labelled `j` and `-c` at every cusp;
  - `thetaDiv χ hs`: the inclusion `B₀ ⊆ Φ₀^gp`.
  `thetaData_isFrobenioid`: the resulting tempered Frobenioid is a Frobenioid.
* On `Y = G/ker χ` (`objY`): `ofDiv D` turns a divisor `D : P → ℚ` on `Ÿ_∞` into an element of
  `Φ₀^gp(Y)`; `divOne`, `divU`, `divTheta ∈ B₀(Y)` are `ofDiv` of the **genuine divisors**
  `BAn.ellDiv` of `s = q^{1/2}`, `Ü` and `Θ̈ ∈ Frac E(K)` (`ellDiv_const_s`, `ellDiv_mono`,
  `ellDiv_thetaDd`: `-j²/2` on the components, `1` at the cusps), and the
  **Frobenioid-theoretic functional equation** `pb_deck_divTheta`: pulled back along the deck
  transformation `τ_d` of `Y` (`χ(d) = a`), `div(Θ̈) ↦ div(Θ̈) + 2a·div(Ü) - a²·div(√q)` — the
  divisor of `Θ̈(s^{-a}Ü) = (-1)^a s^{-a²} Ü^{2a} Θ̈(Ü)` ([EtTh], Prop. 1.4(ii)).
* `tateThetaData`: the theta instance for the tempered fundamental group of the Tate curve
  (`G = temperedPi1 O R A V hV`, `χ = TateObject.character`), so that `isFrobenioid` applies to
  an actual construction from `tempered-fundamental-groups`.

## What is not constructed

The `Π^tp`-action on the elliptic prime set is the deck action through `χ` (the identification
of `P` with the components and cusps of the coverings in `tempered-fundamental-groups`, and of
the analytic Tate parameter with that of the Tate curve, is MR18 T7c), and `B₀` consists of the
divisors of theta monomials rather than of the log-meromorphic functions themselves (the
genuine `B₀` with kernel `O^×` is the radical layer of `Tempered/EllDiv.lean` and MR18 T10).
-/

noncomputable section

set_option linter.unusedSectionVars false

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

/-! ### The divisor monoid on the elliptic prime set -/

section Theta

open BAn TateCurvesTheta

variable {G : Type u} [Group G] [TopologicalSpace G] (χ : G →* Multiplicative ℤ)
  {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K} {s : Kˣ} (hs : (s : K) ^ 2 = t.q)

omit [TopologicalSpace G] in
lemma deck_idx_zpow (c : Deck t) (n : ℤ) : Deck.idx (c ^ n) = n * Deck.idx c :=
  Deck.idx_eq (by
    rw [Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val, ← zpow_natCast, ← zpow_mul, mul_comm n,
      zpow_mul, zpow_natCast, Deck.idx_spec, ← zpow_mul, mul_comm])

/-- **The deck action through `χ`**: `g ↦ s^{χ(g)}`, i.e. the `ℤ`-covering `Y → X` acts on
`Ÿ_∞` by `Ü ↦ q^{a/2}Ü` (`a = χ(g)`, [EtTh] Prop 1.4(ii), l.1326–1328). -/
def chiDeck : G →* Deck t := (zpowersHom (Deck t) (Deck.gen t hs)).comp χ

omit [TopologicalSpace G] in
lemma chiDeck_apply (g : G) : chiDeck χ hs g = Deck.gen t hs ^ (χ g).toAdd := rfl

omit [TopologicalSpace G] in
lemma chiDeck_idx (g : G) : Deck.idx (chiDeck χ hs g) = (χ g).toAdd := by
  rw [chiDeck_apply, deck_idx_zpow, Deck.idx_gen, mul_one]

/-- **The prime log-divisors** `P = ℤ ⊕ Cusps` of `Ÿ_∞` (`BAn.EllPrime`), with `G` acting through
the deck transformations `chiDeck χ` (the `Π^tp`-action on the cusps beyond the `ℤ`-translation
is not modelled; MR18 T7c). -/
abbrev ThetaP : Type u := PrimeVia (chiDeck χ hs)

/-- The component labelled `n`. -/
def ThetaP.cmp (n : ℤ) : ThetaP χ hs := (Sum.inl n : EllPrime t)

/-- The cusp `α`. -/
def ThetaP.csp (α : Cusp t) : ThetaP χ hs := (Sum.inr α : EllPrime t)

omit [TopologicalSpace G] in
lemma ThetaP.smul_cmp (g : G) (n : ℤ) :
    g • ThetaP.cmp χ hs n = ThetaP.cmp χ hs (n + (χ g).toAdd) := by
  change (Sum.inl (n + Deck.idx (chiDeck χ hs g)) : EllPrime t) = _
  rw [chiDeck_idx]; rfl

omit [TopologicalSpace G] in
lemma ThetaP.smul_csp (g : G) (α : Cusp t) :
    g • ThetaP.csp χ hs α = ThetaP.csp χ hs (Cusp.smul (chiDeck χ hs g) α) := rfl

omit [TopologicalSpace G] in
lemma ThetaP.cases (p : ThetaP χ hs) : (∃ n, p = ThetaP.cmp χ hs n) ∨ ∃ α, p = ThetaP.csp χ hs α :=
  match p with
  | .inl n => Or.inl ⟨n, rfl⟩
  | .inr α => Or.inr ⟨α, rfl⟩

variable [IsTopologicalGroup G]

/-- **The divisor monoid `Φ₀`** of the theta Frobenioid: `PrimeDiv.divMonoid` on the elliptic
prime set with coefficients `ℚ` ([EtTh] Prop 3.2(i), l.5378–5392; Ex 3.9(iii), l.6109–6111:
the perfection), the component coefficients normalised by `ord(q) = 1` (l.1028–1034). -/
abbrev ellDivMonoid : DivMonoid.{u} (OrbitObj G) := PrimeDiv.divMonoid G (ThetaP χ hs) ℚ

/-! ### The divisors of the theta monomials -/

/-- The divisors of shape `(a + b·j + c·j²)/2` on the component `n` (`j = n - χ(g)` its label
seen from the sheet `g`) and `-c` at every cusp: the divisors of `q^{a/2} Ü^b Θ̈^{-c}`
(`ellDiv_const_s`, `ellDiv_mono`, `ellDiv_thetaDd`). -/
def IsThetaShape (A : OrbitObj G) (f : (G ⧸ A.H) × ThetaP χ hs → ℚ) : Prop :=
  ∃ a b c : ℤ, (∀ (g : G) (n : ℤ), f (QuotientGroup.mk g, ThetaP.cmp χ hs n) =
      ((a + b * (n - (χ g).toAdd) + c * (n - (χ g).toAdd) ^ 2 : ℤ) : ℚ) / 2) ∧
    ∀ (x : G ⧸ A.H) (α : Cusp t), f (x, ThetaP.csp χ hs α) = -c

omit [IsTopologicalGroup G] in
lemma isThetaShape_comp {A B : OrbitObj G} (F : G ⧸ A.H → G ⧸ B.H)
    (hF : ∀ (g : G) x, F (g • x) = g • F x) {f : (G ⧸ B.H) × ThetaP χ hs → ℚ}
    (hf : IsThetaShape χ hs B f) : IsThetaShape χ hs A (fun z => f (F z.1, z.2)) := by
  obtain ⟨a, b, c, h, hc⟩ := hf
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective (F (QuotientGroup.mk 1))
  set t₀ := (χ g₀).toAdd
  refine ⟨a - b * t₀ + c * t₀ ^ 2, b - 2 * c * t₀, c, fun g n => ?_, fun x α => hc _ α⟩
  have hFg : F (QuotientGroup.mk g) = QuotientGroup.mk (g * g₀) := by
    rw [OrbitHom.mk_eq_smul (A := A), hF, ← hg₀, MulAction.Quotient.smul_mk, smul_eq_mul]
  simp only [hFg, h, map_mul, toAdd_mul]
  congr 2
  ring

/-- **`B₀(G/H)`**: the invariant divisors of theta monomials. -/
def thetaGp (A : OrbitObj G) : AddSubgroup (PrimeDiv.divGp G (ThetaP χ hs) ℚ A) where
  carrier := {f | IsThetaShape χ hs A f.1}
  add_mem' {f f'} := by
    rintro ⟨a, b, c, h, hc⟩ ⟨a', b', c', h', hc'⟩
    refine ⟨a + a', b + b', c + c', fun g n => ?_, fun x α => ?_⟩
    · simp only [AddSubgroup.coe_add, Pi.add_apply, h, h']
      push_cast; ring
    · simp only [AddSubgroup.coe_add, Pi.add_apply, hc, hc']
      push_cast; ring
  zero_mem' := ⟨0, 0, 0, fun _ _ => by simp, fun _ _ => by simp⟩
  neg_mem' {f} := by
    rintro ⟨a, b, c, h, hc⟩
    refine ⟨-a, -b, -c, fun g n => ?_, fun x α => ?_⟩
    · simp only [AddSubgroup.coe_neg, Pi.neg_apply, h]
      push_cast; ring
    · simp only [AddSubgroup.coe_neg, Pi.neg_apply, hc]
      push_cast; ring

/-- The pull-back on theta divisors. -/
def pbTheta {A B : OrbitObj G} (F : G ⧸ A.H → G ⧸ B.H) (hF : ∀ (g : G) x, F (g • x) = g • F x) :
    thetaGp χ hs B →+ thetaGp χ hs A where
  toFun f := ⟨PrimeDiv.pbFun F hF f.1, isThetaShape_comp χ hs F hF f.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The group `B₀` of theta-monomial divisors** on `B^temp(G)⁰`. -/
def thetaGrp : GrpOn.{u} (OrbitObj G) where
  obj A := thetaGp χ hs A
  pb f := pbTheta χ hs f.toFun f.map_smul
  pb_id _ _ := rfl
  pb_comp _ _ _ := rfl
  pb_injective f x y h :=
    Subtype.ext (PrimeDiv.pbFun_injective f.map_smul f.surjective (congrArg Subtype.val h))
  pb_bijective_of_fsm f hf := by
    have hb := OrbitHom.bijective_of_isFSM hf
    refine ⟨fun x y h => Subtype.ext
      (PrimeDiv.pbFun_injective f.map_smul hb.2 (congrArg Subtype.val h)),
      fun y => ⟨pbTheta χ hs _ (PrimeDiv.symm_smul f.map_smul hb) y, ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    funext ⟨x, n⟩
    change y.1.1 ((Equiv.ofBijective f.toFun hb).symm (f.toFun x), n) = y.1.1 (x, n)
    rw [← Equiv.ofBijective_apply f.toFun hb, Equiv.symm_apply_apply]

/-- **The divisor map `B₀ → Φ₀^gp`**: the inclusion. -/
def thetaDiv : DivHom (thetaGrp χ hs) (ellDivMonoid χ hs).toGrpOn where
  app A := (thetaGp χ hs A).subtype
  natural _ _ := rfl

/-- **The tempered Frobenioid of theta divisors** of the `ℤ`-covering defined by `χ`, with
`Φ₀` the `ℚ`-divisors on the elliptic prime set. -/
def thetaData : TemperedFrobenioidData G where
  Φ₀ := ellDivMonoid χ hs
  B₀ := thetaGrp χ hs
  div₀ := thetaDiv χ hs

/-- **The tempered Frobenioid of theta divisors is a Frobenioid.** -/
theorem thetaData_isFrobenioid :
    IsFrobenioid (Model.toElem (thetaData χ hs).Φ₀ (thetaData χ hs).B₀ (thetaData χ hs).div₀) :=
  (thetaData χ hs).isFrobenioid

/-! ### The `ℤ`-covering `Y` and the genuine divisors of `q^{1/2}`, `Ü`, `Θ̈` -/

section Y

variable {χ} (hχ : Continuous χ)

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

/-- **The divisor on `Y` of a function on `Ÿ_∞` with divisor `D : P → ℚ`**: at the fibre point
`x` (the sheet `labY x`) the prime `p` is seen through the deck transformation `s^{-labY x}`. -/
def ofDiv (D : EllPrime t → ℚ) : PrimeDiv.divGp G (ThetaP χ hs) ℚ (objY hχ) :=
  ⟨fun z => D ((Deck.gen t hs) ^ (-labY z.1) • (show EllPrime t from z.2)), fun g z => by
    change D ((Deck.gen t hs) ^ (-labY (g • z.1)) • (chiDeck χ hs g • _)) = _
    rw [labY_smul, chiDeck_apply, ← mul_smul, ← zpow_add, neg_add, neg_add_cancel_comm]⟩

omit [IsTopologicalGroup G] in
lemma ofDiv_cmp (D : EllPrime t → ℚ) (g : G) (n : ℤ) :
    (ofDiv hs hχ D).1 (QuotientGroup.mk g, ThetaP.cmp χ hs n) = D (.inl (n - (χ g).toAdd)) := by
  change D ((Deck.gen t hs) ^ (-labY (χ := χ) (QuotientGroup.mk g)) • Sum.inl n) = _
  rw [Deck.smul_inl, deck_idx_zpow, Deck.idx_gen, labY_mk, mul_one, ← sub_eq_add_neg]

omit [IsTopologicalGroup G] in
lemma ofDiv_csp (D : EllPrime t → ℚ) (x : G ⧸ χ.ker) (α : Cusp t) :
    (ofDiv hs hχ D).1 (x, ThetaP.csp χ hs α) =
      D (.inr (Cusp.smul ((Deck.gen t hs) ^ (-labY x)) α)) := rfl

/-- `div(q^{1/2}) = div(s)`: `1/2` on every component. -/
def divOne : thetaGp χ hs (objY hχ) := ⟨ofDiv hs hχ (ellDiv t s (Mero.const (s : K))),
  ⟨1, 0, 0, fun g n => by rw [ofDiv_cmp, ellDiv_const_s hs]; simp,
    fun x α => by rw [ofDiv_csp, ellDiv_const_s hs]; simp⟩⟩

/-- `div(Ü)`: `j/2` on the component labelled `j`. -/
def divU : thetaGp χ hs (objY hχ) := ⟨ofDiv hs hχ (ellDiv t s (Mero.ofE (Entire.mono 1))),
  ⟨0, 1, 0, fun g n => by rw [ofDiv_cmp, ellDiv_mono hs]; simp,
    fun x α => by rw [ofDiv_csp, ellDiv_mono hs]; simp⟩⟩

/-- **`div(Θ̈)`** ([EtTh] Prop 1.4(i), l.1322–1323): `-j²/2` on the component labelled `j` (the
pole divisor `D_1`), `1` at every cusp — the genuine divisor `ellDiv_thetaDd` of `Θ̈ ∈ Mero K`. -/
def divTheta (h2 : (2 : K) ≠ 0) : thetaGp χ hs (objY hχ) :=
  ⟨ofDiv hs hχ (ellDiv t s (Mero.ofE (thetaDd t))),
  ⟨0, 0, -1, fun g n => by rw [ofDiv_cmp, ellDiv_thetaDd h2 hs]; simp,
    fun x α => by rw [ofDiv_csp, ellDiv_thetaDd h2 hs]; simp⟩⟩

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
theorem pb_deck_divTheta (h2 : (2 : K) ≠ 0) (d : G) :
    (thetaGrp χ hs).pb (deck hχ d) (divTheta hs hχ h2) =
      divTheta hs hχ h2 + (2 * (χ d).toAdd) • divU hs hχ - ((χ d).toAdd ^ 2) • divOne hs hχ := by
  apply Subtype.ext
  apply Subtype.ext
  funext ⟨x, p⟩
  induction x using QuotientGroup.induction_on with
  | H g =>
    change (ofDiv hs hχ (ellDiv t s (Mero.ofE (thetaDd t)))).1
        (QuotientGroup.mk g * QuotientGroup.mk d, p) =
      (ofDiv hs hχ (ellDiv t s (Mero.ofE (thetaDd t)))).1 (QuotientGroup.mk g, p) +
        (2 * (χ d).toAdd) • (ofDiv hs hχ (ellDiv t s (Mero.ofE (Entire.mono 1)))).1
          (QuotientGroup.mk g, p) -
        ((χ d).toAdd ^ 2) • (ofDiv hs hχ (ellDiv t s (Mero.const (s : K)))).1
          (QuotientGroup.mk g, p)
    rw [← QuotientGroup.mk_mul]
    rcases ThetaP.cases χ hs p with ⟨n, rfl⟩ | ⟨α, rfl⟩
    · rw [ofDiv_cmp, ofDiv_cmp, ofDiv_cmp, ofDiv_cmp, ellDiv_thetaDd h2 hs, ellDiv_mono hs,
        ellDiv_const_s hs]
      simp only [Sum.elim_inl, map_mul, toAdd_mul, zsmul_eq_mul]
      push_cast
      ring
    · rw [ofDiv_csp, ofDiv_csp, ofDiv_csp, ofDiv_csp, ellDiv_thetaDd h2 hs, ellDiv_mono hs,
        ellDiv_const_s hs]
      simp

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

variable {𝕂 : Type u} [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂] [IsUltrametricDist 𝕂]
  {t : TateCurvesTheta.TateParameter 𝕂} {s : 𝕂ˣ} (hs : (s : 𝕂) ^ 2 = t.q)

/-- **The tempered Frobenioid of theta divisors of the Tate curve**: `D₀ = B^temp(Π^tp_X)⁰` for
the tempered fundamental group `Π^tp_X = temperedPi1 O R A V hV` of
`tempered-fundamental-groups`, with the theta divisors of its `ℤ`-covering `Y = X₀`
(`TateObject.character`) on the elliptic prime set of the analytic model `Ÿ_∞ = 𝔾_m^an` over
`𝕂` with Tate parameter `t` (the identification of `t` with the Tate parameter of `T` is part
of MR18 T7c). -/
def tateThetaData : TemperedFrobenioidData (temperedPi1 O R A V hV) :=
  thetaData (TateObject.character (A := A) T V hV) hs

/-- **The tempered Frobenioid of the Tate curve is a Frobenioid.** -/
theorem tateThetaData_isFrobenioid :
    IsFrobenioid (Model.toElem (tateThetaData T V hV hs).Φ₀ (tateThetaData T V hV hs).B₀
      (tateThetaData (A := A) T V hV hs).div₀) :=
  (tateThetaData T V hV hs).isFrobenioid

/-- The object `Y` (the `ℤ`-covering `X₀`) of `B^temp(Π^tp_X)⁰`; its subgroup is `Π^tp_Y`. -/
abbrev tateY : OrbitObj (temperedPi1 O R A V hV) :=
  objY (TateObject.continuous_character (A := A) T V hV)

end Tate

end Frobenioid

end Iut
