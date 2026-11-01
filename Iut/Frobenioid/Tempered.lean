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
# Tempered Frobenioids ([EtTh] §3) and the elliptic prime set of the `ℤ`-covering

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
* **The elliptic prime set of the `ℤ`-covering**: for a character `χ : G → ℤ` (the `ℤ`-covering
  `Y → X`, `Gal(Y/X) = ℤ`, whose special fibre is a chain of components labelled by `ℤ`) and
  the analytic model `Ÿ_∞ = 𝔾_m^an` (coordinate `Ü`) over a complete ultrametric field `K` with
  Tate parameter `t` and `s² = q` (`BAn`, `Tempered/EllDiv.lean`):
  `ellDivMonoid χ hs` (`Φ₀`) = `PrimeDiv.divMonoid G P ℚ` on `P = ThetaP χ hs = ℤ ⊕ Cusps`
  (components of the special fibre ⊕ cusps `Ü² ∈ q^ℤ`; [EtTh] Prop 3.2(i)), `G` acting
  through the deck transformations `g ↦ s^{χ(g)}` (`chiDeck`), with coefficients `ℚ` (the
  perfection, [EtTh] Ex 3.9(iii)) normalised by `ord(q) = 1` ([EtTh] l.1028–1034).
* On `Y = G/ker χ` (`objY`): `ofDiv D` turns a divisor `D : P → ℚ` on `Ÿ_∞` into an element of
  `Φ₀^gp(Y)`; `deck d`, the deck transformations of `Y`.
* The theta instance itself (`thetaData`, `B₀` = the log-meromorphic functions, the theta
  function `Θ̈ ∈ B₀(Y)` and its functional equation, `tateThetaData`) is in
  `Tempered/EllTheta.lean`, built on `radData` (`Tempered/EllB.lean`).

## What is not constructed

The `Π^tp`-action on the elliptic prime set is the deck action through `χ` (the identification
of `P` with the components and cusps of the coverings in `tempered-fundamental-groups`, and of
the analytic Tate parameter with that of the Tate curve, is MR18 T7c).
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

/-! ### The `ℤ`-covering `Y` -/

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

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma smul_eq_mk_mul (g : G) (x : G ⧸ χ.ker) : g • x = (QuotientGroup.mk g : G ⧸ χ.ker) * x := by
  induction x using QuotientGroup.induction_on with
  | H a => rfl

/-- **The deck transformation `τ_d` of `Y`** (`d ∈ G`): `x ↦ x·d` on `G/ker χ`. -/
def deck (d : G) : objY hχ ⟶ objY hχ where
  toFun x := x * QuotientGroup.mk d
  map_smul g x := by
    rw [smul_eq_mk_mul, smul_eq_mk_mul, mul_assoc]

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

/-- The object `Y` (the `ℤ`-covering `X₀`) of `B^temp(Π^tp_X)⁰`; its subgroup is `Π^tp_Y`. -/
abbrev tateY : OrbitObj (temperedPi1 O R A V hV) :=
  objY (TateObject.continuous_character (A := A) T V hV)

end Tate

end Frobenioid

end Iut
