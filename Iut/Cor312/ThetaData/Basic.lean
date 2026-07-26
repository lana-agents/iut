/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.LocalConditions

/-!
# Initial Θ-data (taxis #38; IUT I, Definition 3.1)

The assembled notion of **initial Θ-data**: the tuple

`(F̄/F, X_F, ℓ, C̲_K, V, V_mod^bad, ε)`

of IUT I, Definition 3.1(a)–(f), packaged from the child modules:

* global field and elliptic curve, Definition 3.1(a)–(b): taxis #39
  (`Iut.IsInitialThetaGlobalData`);
* admissible prime and `ℓ`-torsion field, Definition 3.1(b)–(c): taxis #40
  (`Iut.AdmissiblePrimeData`);
* orbicurves, `K`-core, and distinguished cusp, Definition 3.1(d)/(f): taxis #41
  (`Iut.OrbicurveData`);
* valuation section and local conditions, Definition 3.1(e)–(f): taxis #42
  (`Iut.LocalThetaData`, containing `V` as `Iut.ValuationSection`).

## Chosen data vs derived objects

The **chosen data** are exactly the fields of this structure and of its child
structures: `F`, `F̄`, `E_F` (giving `X_F = E_F ∖ {0}` through the anabelian
interface), `V_mod^bad`, `ℓ` with the basis/representation of the `ℓ`-torsion, `C̲_K`
with `X̲_K` and the element of `Q` giving `ε`, the valuation section `V`, and the local
choices (decomposition groups). The **derived objects** are `def`s, never fields:
`F_mod = ℚ(j(E))` (`Iut.fieldOfModuli`), `F_sol` (`Iut.solvableClosure`), `K`
(`AdmissiblePrimeData.torsionField`, the fixed field of the kernel of the mod-`ℓ`
representation), the good/bad place sets (`Iut.badPlacesOver`, `Iut.goodModPlaces`,
`ValuationSection.Vbad`, …), the localizations (`Iut.localize`, `Iut.localCompletion`),
the associated covers' fundamental-group maps (`AnabelianGeometry.pi1Cover`), and the
`Π_v` conventions (`LocalThetaData.PivBad`/`PivGood`).

Existence of initial Θ-data is **not** asserted anywhere (statement project;
taxis #38). No hypothesis beyond Definition 3.1 is imposed; in particular, following
IUT I, Remark 3.1.5, `K/F_mod` is not required to be Galois.

The `NumberField` structure on `K` and the `F_mod`-algebra structure on `K` (with its
scalar-tower compatibility, which pins it uniquely) are carried as instance fields;
the former is provable from the openness of the kernel
(`AdmissiblePrimeData.numberField_torsionField`), and being propositional classes,
carrying them is proof-irrelevant.
-/

namespace Iut

universe u

open NumberField WeierstrassCurve OrbicurveDataSection

/-- **Initial Θ-data** (IUT I, Definition 3.1; taxis #38): the packaged tuple
`(F̄/F, X_F, ℓ, C̲_K, V, V_mod^bad, ε)` relative to an anabelian interface `AG` and
tempered interface `TG`. See the module docstring for the chosen-data/derived-object
inventory and the honesty boundary. -/
structure InitialThetaData (AG : AnabelianGeometry.{u}) (TG : TemperedGeometry AG) :
    Type (u + 1) where
  /-- The number field `F` (IUT I, Definition 3.1(a)). -/
  F : Type u
  /-- `F` is a field. -/
  [fieldF : Field F]
  /-- `F` is a number field. -/
  [numberFieldF : NumberField F]
  /-- The chosen algebraic closure `F̄` of `F` (IUT I, Definition 3.1(a)). -/
  Fbar : Type u
  /-- `F̄` is a field. -/
  [fieldFbar : Field Fbar]
  /-- `F̄` is an `F`-algebra. -/
  [algebraFbar : Algebra F Fbar]
  /-- `F̄` is an algebraic closure of `F`. -/
  [isAlgClosure : IsAlgClosure F Fbar]
  /-- The elliptic curve `E_F/F`, giving the once-punctured curve
  `X_F = E_F ∖ {0}` (IUT I, Definition 3.1(a)). -/
  E : WeierstrassCurve F
  /-- `E_F` is an elliptic curve. -/
  [isElliptic : E.IsElliptic]
  /-- The chosen nonempty set `V_mod^bad` of nonarchimedean places of `F_mod`
  (IUT I, Definition 3.1(b)). -/
  VBad : Set (FinitePlace ↥(fieldOfModuli F E))
  /-- The global conditions of Definition 3.1(a)–(b) (taxis #39). -/
  global : IsInitialThetaGlobalData F E Fbar VBad
  /-- The admissible prime `ℓ` with the mod-`ℓ` representation data and coprimality
  conditions of Definition 3.1(b)–(c) (taxis #40). -/
  prime : AdmissiblePrimeData F E Fbar VBad
  /-- The `NumberField` structure on `K` (provable:
  `AdmissiblePrimeData.numberField_torsionField`; carried for instance availability,
  proof-irrelevant). -/
  [numberFieldK : NumberField ↥prime.torsionField]
  /-- The `F_mod`-algebra structure on `K`. -/
  [algebraModK : Algebra ↥(fieldOfModuli F E) ↥prime.torsionField]
  /-- Compatibility of the `F_mod`-algebra structure with the inclusions
  `F_mod ⊆ F ⊆ K`, pinning it uniquely. -/
  [towerModK : IsScalarTower ↥(fieldOfModuli F E) F ↥prime.torsionField]
  /-- The orbicurve data `C̲_K`, `X̲_K`, `ε` of Definition 3.1(d)/(f) (taxis #41). -/
  orb : OrbicurveData AG F E Fbar VBad prime
  /-- The valuation section `V` and local conditions of Definition 3.1(e)–(f)
  (taxis #42). -/
  localData : LocalThetaData AG TG F E Fbar VBad prime orb

namespace InitialThetaData

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

attribute [instance] fieldF numberFieldF fieldFbar algebraFbar isAlgClosure isElliptic
  numberFieldK algebraModK towerModK

variable (D : InitialThetaData AG TG)

/-- The once-punctured elliptic curve `X_F = E_F ∖ {0}` (derived). -/
noncomputable def X : AG.Orbicurve D.F := AG.oncePunctured D.E

/-- The prime `ℓ` of the Θ-data. -/
def ℓ : ℕ := D.prime.ℓ

/-- The `ℓ`-torsion field `K` (derived: the fixed field of the kernel of the mod-`ℓ`
representation). -/
noncomputable def K : IntermediateField D.F D.Fbar := D.prime.torsionField

/-- The orbicurve `C̲_K` of the Θ-data tuple. -/
def CKu : AG.Orbicurve ↥D.prime.torsionField := D.orb.CKu

/-- The distinguished cusp `ε` of `C̲_K`. -/
def epsilon : AG.Cusp D.orb.CKu := D.orb.epsilon

/-- The valuation section `V ⊆ V(K)`. -/
def V : ValuationSection D.F D.E D.Fbar D.VBad D.prime := D.localData.sect

/-- The absolute Galois group `Gal(F̄/F)` of the Θ-data (Krull topology). -/
def galoisGroup : Type u := D.Fbar ≃ₐ[D.F] D.Fbar

end InitialThetaData

end Iut
