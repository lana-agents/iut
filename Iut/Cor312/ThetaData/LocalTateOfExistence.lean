/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Cor312.ThetaData.LocalConditions
import Iut.Cor312.ThetaData.TateFamilyOfTorsion
import Iut.Anabelian.Torsion

/-!
# The canonical Tate structures of the local models (IUT I, Definition 3.1(f))

IUT I, Definition 3.1(f) states the conditions at the places `v` of the valuation section over
`V_mod^bad` in terms of the **Tate uniformization** of `E` over the completion `K_v` of the
`ℓ`-torsion field `K`. This uniformization is not a choice: by Tate's theorem it **exists**,
since `E` has multiplicative reduction at the places of `F` over `V_mod^bad` (odd residue
characteristic) and its `ℓ`-torsion is rational over `K`, so that the reduction over `K_v` is
split multiplicative (`Iut.tateFamilyOfTorsion`); and it is **unique up to `±1`**
(`Iut.TateStructureUnique`).

The fields `LocalThetaData.tateX`, `LocalThetaData.tateC` record the Tate structures on the local
models `X̲_v`, `C̲_v`. This module provides the structures given by the existence argument, from
the data available before the local data (global conditions, admissible prime, orbicurves) and a
valuation section, so that these fields can be filled in by existence
(`Iut.InitialThetaData.ofExistence`):

* `Iut.IsInitialThetaGlobalData.tateFamily`: the Galois-equivariant Tate family of `E` over the
  completions of `K` at the places over `V_mod^bad` (the family `Iut.InitialThetaData.tate` of
  initial Θ-data is this family);
* `Iut.TateStructure.ofEq`: transport of a Tate structure along an equality of curves;
* `Iut.IsInitialThetaGlobalData.canonicalTateX`, `Iut.IsInitialThetaGlobalData.canonicalTateC`:
  the Tate structures of the family at `sectFin v`, transported along `X̲_K.E = E_K` and
  `C̲_K.E = E_K` (the curve equalities of the covers `X̲_K → X_K`, `C̲_K → C_K`).

## Source correspondence

IUT I, Definition 3.1(f), p. 71; *The Étale Theta Function*, §1–2 (the Tate curve over `K_v`).
-/

namespace Iut

universe u

open NumberField WeierstrassCurve OrbicurveDataSection Iut.Anabelian

/-- **Transport of a Tate structure along an equality of curves.** -/
def TateStructure.ofEq {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
    [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
    {E E' : WeierstrassCurve k} (h : E = E') (S : TateStructure E) : TateStructure E' :=
  h ▸ S

namespace IsInitialThetaGlobalData

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable (hG : IsInitialThetaGlobalData F E Fbar VBad) (P : AdmissiblePrimeData F E Fbar VBad)
include hG

open scoped Classical in
/-- **The Tate uniformizations of `E` over the completions `K_w`** of the `ℓ`-torsion field at
the places `w` over `V_mod^bad` (IUT I, Definition 3.1(f)): Tate's theorem at each such place,
from the multiplicative reduction of `E` at the places of `F` over `V_mod^bad` (of odd residue
characteristic) and the rationality of the ℓ-torsion over `K` (`Iut.tateFamilyOfTorsion`). It
uses only the global conditions and the admissible prime, not the orbicurve or local data. -/
noncomputable def tateFamily : TateFamily E P.torsionField P.ℓ VBad :=
  tateFamilyOfTorsion E P.torsionField P.ℓ
    (fun v hv => by
      have h := hG.bad_odd v hv
      intro h2
      rw [h2] at h
      exact (Nat.not_odd_iff_even.mpr even_two) h)
    hG.bad_multiplicative P.ℓ_prime (by have := P.five_le; omega)
    P.TK le_rfl ((sq P.ℓ).symm.le.trans P.card_TK.symm.le)

variable {P} (O : OrbicurveData F E Fbar VBad P) (S : ValuationSection F E Fbar VBad P)

open scoped Classical in
omit hG in
/-- The place `sectFin v` of the section over `v ∈ V_mod^bad` is a bad place of `K`. -/
lemma _root_.Iut.ValuationSection.isBadPlace_sectFin {v : FinitePlace ↥(fieldOfModuli F E)}
    (hv : v ∈ VBad) :
    IsBadPlace E P.torsionField VBad (S.sectFin v) :=
  ⟨v, hv, S.sectFin_liesOver v⟩

open scoped Classical in
/-- **The canonical Tate structure on the local model `X̲_v`** at a place `v ∈ V_mod^bad`
(IUT I, Definition 3.1(f)): the Tate uniformization of `E` over `K_v`, which exists and is
unique up to `±1`, given by the Tate family `tateFamily` at `sectFin v` and transported along
the curve equality `X̲_K.E = E_K` of the cover `X̲_K → X_K`. -/
noncomputable def canonicalTateX (v : FinitePlace ↥(fieldOfModuli F E)) (hv : v ∈ VBad) :
    TateStructure (localize (S.sectFin v) O.XKu).E :=
  TateStructure.ofEq (congrArg (·.map (emb P.torsionField (S.sectFin v))) O.XKu_to_XK.E_eq).symm
    ((hG.tateFamily P).S (S.sectFin v) (S.isBadPlace_sectFin hv))

open scoped Classical in
/-- **The canonical Tate structure on the local model `C̲_v`** at a place `v ∈ V_mod^bad`
(IUT I, Definition 3.1(f)): as `canonicalTateX`, transported along the curve equality
`C̲_K.E = E_K` of the cover `C̲_K → C_K`. -/
noncomputable def canonicalTateC (v : FinitePlace ↥(fieldOfModuli F E)) (hv : v ∈ VBad) :
    TateStructure (localize (S.sectFin v) O.CKu).E :=
  TateStructure.ofEq (congrArg (·.map (emb P.torsionField (S.sectFin v))) O.CKu_to_CK.E_eq).symm
    ((hG.tateFamily P).S (S.sectFin v) (S.isBadPlace_sectFin hv))

end IsInitialThetaGlobalData

end Iut
