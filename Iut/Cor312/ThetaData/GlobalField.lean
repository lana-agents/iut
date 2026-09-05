/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.Places

/-!
# Initial Θ-data: global field and punctured elliptic curve (taxis #39)

The global field and elliptic-curve portion of initial Θ-data, IUT I,
Definition 3.1(a)–(b), for the Corollary 3.12 variant statement (taxis #33):

* a number field `F` containing `√−1`, with a chosen algebraic closure `F̄` and absolute
  Galois group `Gal(F̄/F)` (Mathlib's Krull-topologized `F̄ ≃ₐ[F] F̄`);
* an elliptic curve `E_F` (a `WeierstrassCurve F` with `IsElliptic`), with stable
  (= semistable) reduction at every nonarchimedean place of `F`
  (`Iut.HasStableReductionAt`, via Mathlib's minimal-Weierstrass-equation reduction
  theory over the completed local rings);
* the field of moduli `F_mod = ℚ(j(E_F))` (`Iut.fieldOfModuli`), its maximal solvable
  subextension `F_sol ⊆ F̄` (`Iut.solvableClosure`), and `V_mod = V(F_mod)`;
* a nonempty set `V_mod^bad` of nonarchimedean places of odd residue characteristic at
  which `E_F` has bad multiplicative reduction, and the induced good/bad place sets;
* rationality over `F` of the `2·3`-torsion points (`Iut.SixTorsionRational`).

## Design notes and honesty boundary

* **Once-punctured curve and quotient orbicurve.** `X_F = E_F ∖ {0}` and
  `C_F = X_F/{±1}` are hyperbolic orbicurves; they carry no additional *data* beyond
  `E_F` at the level of Definition 3.1(a)–(b) and their formalization belongs to the
  orbicurve module of taxis #41 (whose interface consumes the present data). Per the
  scope of taxis #39 ("without postulating the later orbicurve or local data"), this
  module does not introduce them.
* **Stable reduction.** `Iut.HasStableReductionAt` is a genuine definition through
  Mathlib's `WeierstrassCurve.HasGoodReduction` / `HasMultiplicativeReduction` over the
  valuation ring of the completion at each finite place — not an interface field. Mathlib's
  classes are properties of the *given* Weierstrass model (they extend `IsMinimal`), so the
  predicates quantify over a global change of variables `C • E`: they are properties of the
  curve up to isomorphism, as in Mochizuki's condition (a non-integral model such as the
  Legendre model `y² = x(x−1)(x−λ)` at a denominator of `λ` is not excluded).
  Proving that a given curve satisfies it is out of scope here (taxis #39). The
  elliptic-reduction certificate project (taxis #5) remains the seam for reduction
  *theorems*; the *predicates* need no certificate.
* **Field of moduli.** For an elliptic curve, the field of moduli is `ℚ(j)`; this is
  taken as the definition (IUT I, Definition 3.1(b) introduces `F_mod` as the field of
  moduli of `X_F`, which for the once-punctured curve of `E_F` is `ℚ(j(E_F))`).
* **`F/F_mod` Galois of degree prime to `ℓ`.** Exposed as the predicate
  `Iut.IsGaloisOfDegreePrimeTo`, consumed by the admissible-prime module (taxis #40).
  Following IUT I, Definition 3.1 and Remark 3.1.5, no condition that `K/F_mod` be
  Galois is added anywhere.
-/

namespace Iut

open NumberField IsDedekindDomain WeierstrassCurve IntermediateField

/-! ## Reduction predicates at finite places -/

section Reduction

variable {F : Type*} [Field F] [NumberField F] (E : WeierstrassCurve F)

/-- `E` has **good reduction** at the finite place `w`: some global change of variables
`C • E` of the model, base changed to the `w`-adic completion, has good reduction over its
valuation ring in the sense of Mathlib's minimal Weierstrass equations
(`WeierstrassCurve.HasGoodReduction`). Mathlib's classes refer to the given model (they
extend `IsMinimal`); the predicate is a property of the curve up to isomorphism. -/
def HasGoodReductionAt (w : FinitePlace F) : Prop :=
  ∃ C : VariableChange F,
    ((C • E).baseChange (w.maximalIdeal.adicCompletion F)).HasGoodReduction
      (w.maximalIdeal.adicCompletionIntegers F)

/-- `E` has **(bad) multiplicative reduction** at the finite place `w`, up to a global change
of variables (`WeierstrassCurve.HasMultiplicativeReduction` over the completed local ring for
some model `C • E`; Mathlib's class refers to the given model). -/
def HasMultiplicativeReductionAt (w : FinitePlace F) : Prop :=
  ∃ C : VariableChange F,
    ((C • E).baseChange (w.maximalIdeal.adicCompletion F)).HasMultiplicativeReduction
      (w.maximalIdeal.adicCompletionIntegers F)

/-- `E` has **split multiplicative reduction** at the finite place `w`, up to a global change
of variables (`WeierstrassCurve.HasSplitMultiplicativeReduction` over the completed local ring
for some model `C • E`; Mathlib's class refers to the given model). -/
def HasSplitMultiplicativeReductionAt (w : FinitePlace F) : Prop :=
  ∃ C : VariableChange F,
    ((C • E).baseChange (w.maximalIdeal.adicCompletion F)).HasSplitMultiplicativeReduction
      (w.maximalIdeal.adicCompletionIntegers F)

/-- `E` has **stable (= semistable) reduction** at the finite place `w`: good or
multiplicative reduction (each up to a global change of variables). Stable reduction of the
once-punctured curve `X_F` in IUT I, Definition 3.1(a) is semistable reduction of `E_F`. -/
def HasStableReductionAt (w : FinitePlace F) : Prop :=
  HasGoodReductionAt E w ∨ HasMultiplicativeReductionAt E w

end Reduction

/-! ## The field of moduli and its places -/

section FieldOfModuli

variable (F : Type*) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]

/-- The **field of moduli** `F_mod` of `E`: the subfield `ℚ(j(E)) ⊆ F` generated by the
`j`-invariant (IUT I, Definition 3.1(b)). -/
noncomputable def fieldOfModuli : IntermediateField ℚ F := ℚ⟮E.j⟯

instance : FiniteDimensional ℚ ↥(fieldOfModuli F E) :=
  Module.Finite.left ℚ ↥(fieldOfModuli F E) F

instance : NumberField ↥(fieldOfModuli F E) where

/-- The set of places `V_mod = V(F_mod)` (IUT I, Definition 3.1(b)). -/
abbrev ModPlace : Type _ := Place ↥(fieldOfModuli F E)

/-- The **maximal solvable subextension** `F_sol` of `F̄/F_mod`: the compositum of all
finite solvable Galois subextensions of `F̄/F_mod` (IUT I, Definition 3.1(b)). The
algebra structure of `F̄` over `F_mod` is the restriction of its `F`-algebra structure,
carried as an explicit instance hypothesis. -/
noncomputable def solvableClosure (Fbar : Type*) [Field Fbar]
    [Algebra ↥(fieldOfModuli F E) Fbar] :
    IntermediateField ↥(fieldOfModuli F E) Fbar :=
  ⨆ L ∈ {L : IntermediateField ↥(fieldOfModuli F E) Fbar |
      FiniteDimensional ↥(fieldOfModuli F E) ↥L ∧
      IsGalois ↥(fieldOfModuli F E) ↥L ∧
      IsSolvable (↥L ≃ₐ[↥(fieldOfModuli F E)] ↥L)}, L

/-- `F/F_mod` is Galois of degree prime to `ℓ` (IUT I, Definition 3.1(b)); the form in
which this condition is consumed by the admissible-prime module (taxis #40). -/
def IsGaloisOfDegreePrimeTo (ℓ : ℕ) : Prop :=
  IsGalois ↥(fieldOfModuli F E) F ∧ Nat.Coprime (Module.finrank ↥(fieldOfModuli F E) F) ℓ

end FieldOfModuli

/-! ## Bad places and torsion rationality -/

section Conditions

variable (F : Type*) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type*) [Field Fbar] [Algebra F Fbar]

open scoped Classical in
/-- The `2·3 = 6`-torsion of `E` is **rational over `F`** (IUT I, Definition 3.1(b)):
every `6`-torsion point of `E(F̄)` comes from an `F`-point under base change. -/
def SixTorsionRational : Prop :=
  ∀ P ∈ AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) 6,
    P ∈ (Affine.Point.baseChange (W' := E) F Fbar).range

variable (VBad : Set (FinitePlace ↥(fieldOfModuli F E)))

/-- The set `V(F)^bad` of finite places of `F` lying over `V_mod^bad`. -/
def badPlacesOver : Set (FinitePlace F) :=
  {w | ∃ v ∈ VBad, FinitePlace.LiesOver w v}

/-- `V_mod^bad` as a subset of `V_mod` (nonarchimedean places only, by construction). -/
def badModPlaces : Set (ModPlace F E) := Place.finite '' VBad

/-- `V_mod^good := V_mod ∖ V_mod^bad`, containing in particular all archimedean
places (IUT I, Definition 3.1(b)). -/
def goodModPlaces : Set (ModPlace F E) := (Place.finite '' VBad)ᶜ

/-- **IUT I, Definition 3.1(a)–(b)** for the tuple `(F̄/F, E_F, V_mod^bad)`: the
global-field and elliptic-curve conditions of initial Θ-data. The choice of the prime
`ℓ` and the conditions involving it are in the admissible-prime module (taxis #40); the
orbicurve and local data are in the modules of taxis #41–#42. -/
structure IsInitialThetaGlobalData : Prop where
  /-- `F` contains a square root of `−1` (IUT I, Definition 3.1(a)). -/
  sqrt_neg_one : IsSquare (-1 : F)
  /-- `X_F/E_F` has stable reduction at every nonarchimedean place of `F`
  (IUT I, Definition 3.1(a)). -/
  stable_reduction : ∀ w : FinitePlace F, HasStableReductionAt E w
  /-- The `2·3`-torsion points of `E_F` are rational over `F`
  (IUT I, Definition 3.1(b)). -/
  six_torsion_rational : SixTorsionRational F E Fbar
  /-- `V_mod^bad` is nonempty (IUT I, Definition 3.1(b)). -/
  bad_nonempty : VBad.Nonempty
  /-- Every place of `V_mod^bad` has odd residue characteristic
  (IUT I, Definition 3.1(b)). -/
  bad_odd : ∀ v ∈ VBad, Odd (residueChar v)
  /-- `E_F` has bad multiplicative reduction at every place of `F` over `V_mod^bad`
  (IUT I, Definition 3.1(b)). -/
  bad_multiplicative : ∀ v ∈ VBad, ∀ w : FinitePlace F,
    FinitePlace.LiesOver w v → HasMultiplicativeReductionAt E w

end Conditions

end Iut
