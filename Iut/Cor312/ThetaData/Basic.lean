/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Cor312.ThetaData.LocalConditions
import Iut.Cor312.ThetaData.TateFamily
import Iut.Cor312.ThetaData.TateFamilyOfTorsion
import Iut.Cor312.ThetaData.TateParameterAt
import Iut.Anabelian.Torsion

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
structures: `F`, `F̄`, `E_F` (giving `X_F = E_F ∖ {0}`, the model orbicurve
`Iut.Anabelian.Orbicurve.oncePunctured`), `V_mod^bad`, `ℓ` with the basis/representation of the
`ℓ`-torsion, `C̲_K`
with `X̲_K` and the element of `Q` giving `ε`, the valuation section `V`, and the local
choices (decomposition groups). The **derived objects** are `def`s, never fields:
`F_mod = ℚ(j(E))` (`Iut.fieldOfModuli`), `F_sol` (`Iut.solvableClosure`), `K`
(`AdmissiblePrimeData.torsionField`, the fixed field of the kernel of the mod-`ℓ`
representation), the good/bad place sets (`Iut.badPlacesOver`, `Iut.goodModPlaces`,
`ValuationSection.Vbad`, …), the localizations (`Iut.localize`, `Iut.localCompletion`),
the associated covers' fundamental-group maps (`Iut.Anabelian.genuinePi1Cover`), and the
`Π_v` conventions (`LocalThetaData.PivBad`/`PivGood`).

Existence of initial Θ-data is **not** asserted anywhere (statement project;
taxis #38). No hypothesis beyond Definition 3.1 is imposed; in particular, following
IUT I, Remark 3.1.5, `K/F_mod` is not required to be Galois.

The following objects are **derived** (definitions and theorems below), not fields:

* the `NumberField` structure on `K` (`AdmissiblePrimeData.instNumberFieldTorsionField`, from
  the openness of the kernel of `ρ`), and the `F_mod`-algebra structure on `K` with its scalar
  tower `F_mod ⊆ F ⊆ K` (Mathlib's canonical `IntermediateField` instances);
* the Tate parameter `q_w` of `E` at every `w ∈ V(F)^bad` (`InitialThetaData.tateParam`): the
  unique Tate parameter of `F_w` whose Tate curve has `j`-invariant `j(E)`, which exists by the
  multiplicative reduction of Definition 3.1(b); its normalized order `ord_w(q_w)`
  (`InitialThetaData.qOrder`), positive and independent of the uniformizer
  (`InitialThetaData.qOrder_pos`, `InitialThetaData.orderNat_eq_qOrder`); the condition of
  Definition 3.1(c) that `ℓ` is prime to it is `InitialThetaData.coprime_qOrder`, from the
  choice-free field `AdmissiblePrimeData.q_order_coprime`;
* the Tate uniformizations of `E` over the completions `K_w` of `K` at the places over
  `V_mod^bad` (`InitialThetaData.tate : Iut.TateFamily`), constructed by Tate's theorem from the
  multiplicative reduction over `F` and the rationality of `E[ℓ]` over `K`
  (`Iut.tateFamilyOfTorsion`), with their Galois equivariance a theorem
  (`Iut.TateFamily.ofStructures`).
-/

namespace Iut

universe u

open NumberField WeierstrassCurve OrbicurveDataSection

/-- **Initial Θ-data** (IUT I, Definition 3.1; taxis #38): the packaged tuple
`(F̄/F, X_F, ℓ, C̲_K, V, V_mod^bad, ε)`, stated about the model orbicurves with their genuine
étale fundamental groups, genuine cores and tempered fundamental groups. See the module docstring
for the chosen-data/derived-object
inventory and the honesty boundary. -/
structure InitialThetaData : Type (u + 1) where
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
  /-- The orbicurve data `C̲_K`, `X̲_K`, `ε` of Definition 3.1(d)/(f) (taxis #41). -/
  orb : OrbicurveData F E Fbar VBad prime
  /-- The valuation section `V` and local conditions of Definition 3.1(e)–(f)
  (taxis #42). -/
  localData : LocalThetaData F E Fbar VBad prime orb

namespace InitialThetaData

attribute [instance] fieldF numberFieldF fieldFbar algebraFbar isAlgClosure isElliptic

variable (D : InitialThetaData.{u})

/-- The once-punctured elliptic curve `X_F = E_F ∖ {0}` (derived). -/
noncomputable def X : Anabelian.Orbicurve D.F := Anabelian.Orbicurve.oncePunctured D.E

/-- The prime `ℓ` of the Θ-data. -/
def ℓ : ℕ := D.prime.ℓ

/-- The `ℓ`-torsion field `K` (derived: the fixed field of the kernel of the mod-`ℓ`
representation). -/
noncomputable def K : IntermediateField D.F D.Fbar := D.prime.torsionField

/-- The `ℓ`-torsion field of the Θ-data, as a type. -/
abbrev Kt : Type u := ↥D.prime.torsionField

/-- The orbicurve `C̲_K` of the Θ-data tuple. -/
def CKu : Anabelian.Orbicurve ↥D.prime.torsionField := D.orb.CKu

/-- The distinguished cusp `ε` of `C̲_K`. -/
def epsilon : D.orb.CKu.Cusp := D.orb.epsilon

/-- The valuation section `V ⊆ V(K)`. -/
def V : ValuationSection D.F D.E D.Fbar D.VBad D.prime := D.localData.sect

/-- The absolute Galois group `Gal(F̄/F)` of the Θ-data (Krull topology). -/
def galoisGroup : Type u := D.Fbar ≃ₐ[D.F] D.Fbar

/-! ### Derived objects: the Tate parameters at the bad places -/

/-- `E` has multiplicative reduction at every place of `V(F)^bad` (Definition 3.1(b)). -/
theorem mult_of_mem_bad {w : FinitePlace D.F} (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    HasMultiplicativeReductionAt D.E w := by
  obtain ⟨v, hv, hwv⟩ := hw
  exact D.global.bad_multiplicative v hv w hwv

/-- **The Tate parameter `q_w` of `E` at `w ∈ V(F)^bad`** (derived): the unique Tate parameter
of `F_w` whose Tate curve has `j`-invariant `j(E)` (`Iut.tateParameterAt`). -/
noncomputable def tateParam (w : FinitePlace D.F) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    TateCurvesTheta.TateParameter (localCompletion w) :=
  tateParameterAt D.E (D.mult_of_mem_bad hw)

/-- The Tate curve of `q_w` has `j`-invariant `j(E)`. -/
theorem tateParam_tateJ (w : FinitePlace D.F) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    (D.tateParam w hw).tateJ = FinitePlace.embedding w.maximalIdeal D.E.j :=
  tateParameterAt_tateJ D.E _

/-- **Uniqueness of `q_w`.** -/
theorem eq_tateParam {w : FinitePlace D.F} (hw : w ∈ badPlacesOver D.F D.E D.VBad)
    {t : TateCurvesTheta.TateParameter (localCompletion w)}
    (ht : t.tateJ = FinitePlace.embedding w.maximalIdeal D.E.j) : t = D.tateParam w hw :=
  eq_tateParameterAt D.E _ ht

/-- **The normalized order `ord_w(q_w)`** of the Tate parameter at `w ∈ V(F)^bad` (derived;
`Iut.qOrderAt`). -/
noncomputable def qOrder (w : FinitePlace D.F) (hw : w ∈ badPlacesOver D.F D.E D.VBad) : ℕ :=
  qOrderAt D.E (D.mult_of_mem_bad hw)

lemma qOrder_eq_orderNat (w : FinitePlace D.F) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    D.qOrder w hw = ((D.tateParam w hw).toOrdered (isUniformizer_unifAt w)).orderNat := rfl

/-- `ord_w(q_w) > 0`. -/
theorem qOrder_pos (w : FinitePlace D.F) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    0 < D.qOrder w hw :=
  qOrderAt_pos D.E _

/-- **`ord_w(q_w)` is independent of the uniformizer**, and of the description of `q_w`. -/
theorem orderNat_eq_qOrder {w : FinitePlace D.F} (hw : w ∈ badPlacesOver D.F D.E D.VBad)
    {t : TateCurvesTheta.TateParameter (localCompletion w)}
    (ht : t.tateJ = FinitePlace.embedding w.maximalIdeal D.E.j) {π : localCompletion w}
    (hπ : TateCurvesTheta.IsUniformizer π) : (t.toOrdered hπ).orderNat = D.qOrder w hw :=
  orderNat_eq_qOrderAt D.E _ ht hπ

/-- **`ℓ` is prime to `ord_w(q_w)`** (IUT I, Definition 3.1(c)), for the derived `q_w`. -/
theorem coprime_qOrder (w : FinitePlace D.F) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    Nat.Coprime D.ℓ (D.qOrder w hw) :=
  D.prime.q_order_coprime w hw _ (D.tateParam_tateJ w hw) _ (isUniformizer_unifAt w)

/-! ### Derived objects: the Tate uniformizations over the completions of `K` -/

open scoped Classical in
/-- **The Tate uniformizations of `E` over the completions `K_w`** at the places `w` of `K` over
`V_mod^bad` (derived; IUT I, Definition 3.1(f) refers to them): Tate's theorem at each such place,
from the multiplicative reduction of `E` at the places of `F` over `V_mod^bad` (of odd residue
characteristic) and the rationality of the ℓ-torsion over `K` (`Iut.tateFamilyOfTorsion`). The
Galois equivariance of the family is a theorem (`Iut.TateFamily.ofStructures`). -/
noncomputable def tate : TateFamily D.E D.prime.torsionField D.prime.ℓ D.VBad :=
  tateFamilyOfTorsion D.E D.prime.torsionField D.prime.ℓ
    (fun v hv => by
      have h := D.global.bad_odd v hv
      intro h2
      rw [h2] at h
      exact (Nat.not_odd_iff_even.mpr even_two) h)
    D.global.bad_multiplicative D.prime.ℓ_prime (by have := D.prime.five_le; omega)
    D.prime.TK le_rfl ((sq D.prime.ℓ).symm.le.trans D.prime.card_TK.symm.le)

end InitialThetaData

end Iut
