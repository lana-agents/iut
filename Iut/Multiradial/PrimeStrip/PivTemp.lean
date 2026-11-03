/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Local
import Iut.Frobenioid.Tempered.PiTpONS
import Iut.Anabelian.AdicCompletion
import Pi1.Orbifold.Smooth

/-!
# The tempered `Π_v` is a tempered group (MR21 task 0)

[SemiAnbd], Proposition 3.2 (`Iut.Frobenioid.OrbitObj.exists_continuousMulEquiv_temp`) needs the
source group to be Hausdorff, to have a basis of open normal subgroups, to be complete for them
and to have a countable cofinal chain of them. `Iut/Frobenioid/Tempered/PiTpONS.lean` proves the
first three for tfg's tempered fundamental group of an affine orbifold `[Spec R / A]` with `R` a
smooth domain of dimension `1` and `A` finite, over a field whose canonical valuation is a
complete discrete valuation ring with perfect residue field of mixed characteristic, and the
fourth from a sequence of pointed Galois objects dominating all of them (`hctbl`).

This file instantiates these results at the tempered fundamental group `Orbicurve.temperedPi1`
of the model orbicurves, and at `Π_v` for `v ∈ V^bad` (IUT I, Definition 3.1 (e): the tempered
fundamental group of `X̲_v` over `K_v`):

* `temp_t2`, `temp_hasONSBasis`, `temp_isONSComplete`: unconditional
  over such fields (the presentation in characteristic `0` is the Galois presentation
  `Genuine.orbifold`, with smooth coordinate ring of Krull dimension `1` and finite group, as in
  `Iut.Anabelian.Orbicurve.temperedEquivAndre`);
* **`tempCountable X`**: the countability hypothesis `hctbl` of
  `temperedPi1_hasONSChainO` for this presentation (a sequence of pointed Galois objects
  dominating all of them; [SemiAnbd], Definition 3.1 requires tempered groups to be countably
  indexed); `temp_hasONSChain`;
* at `v ∈ V^bad`: `piv_t2`, `piv_hasONSBasis`, `piv_isONSComplete` (unconditional; `K_v` is the
  completion of a number field, `Iut.Anabelian.AdicCompletion`) and `piv_hasONSChain` from
  **`PivCountable D v`** (= `tempCountable` of `X̲_v`; MR18's debt `hctbl`, the only remaining
  input of `MonoAn.TempRecon`).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open NumberField TemperedFundamentalGroups Iut.Anabelian Iut.Frobenioid IsLocalRing

universe u

-- the decidability instances of `Iut.Anabelian.Model` (points of `E` need `DecidableEq k`)
attribute [local instance low] Classical.propDecidable

/-! ### Tempered fundamental groups of model orbicurves over complete discretely valued fields -/

section Generic

variable {k : Type u} [Field k] [CharZero k]

/-- The coordinate ring of the Galois presentation is smooth (`lana-agents/pi1`). -/
instance genuineOrbifold_smooth (E : WeierstrassCurve k) [E.IsElliptic] (ℓ : ℕ)
    (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Algebra.Smooth k (Genuine.orbifold E ℓ M pm).R :=
  Pi1.Orbifold.GaloisData.smooth_R (Genuine.galoisData E ℓ M pm)

instance genuineOrbifold_isDomain (E : WeierstrassCurve k) [E.IsElliptic] (ℓ : ℕ)
    (M : AddSubgroup E.toAffine.Point) (pm : Bool) : IsDomain (Genuine.orbifold E ℓ M pm).R :=
  inferInstanceAs (IsDomain (Genuine.galoisData E ℓ M pm).R)

instance genuineOrbifold_finite (E : WeierstrassCurve k) [E.IsElliptic] (ℓ : ℕ)
    (M : AddSubgroup E.toAffine.Point) (pm : Bool) : Finite (Genuine.orbifold E ℓ M pm).A :=
  inferInstanceAs (Finite (Genuine.galoisData E ℓ M pm).A)

instance genuineOrbifold_isAlgClosed (E : WeierstrassCurve k) [E.IsElliptic] (ℓ : ℕ)
    (M : AddSubgroup E.toAffine.Point) (pm : Bool) : IsAlgClosed (Genuine.orbifold E ℓ M pm).Ω :=
  inferInstanceAs (IsAlgClosed (Genuine.Ω E))

lemma genuineOrbifold_dim (E : WeierstrassCurve k) [E.IsElliptic] (ℓ : ℕ)
    (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    ringKrullDim (Genuine.orbifold E ℓ M pm).R = 1 :=
  Pi1.Orbifold.GaloisData.ringKrullDim_R (Genuine.galoisData E ℓ M pm)

variable [IsDiscreteValuationRing (canonicalValuationSubring k)]
  [IsAdicComplete (maximalIdeal (canonicalValuationSubring k)) (canonicalValuationSubring k)]
  [PerfectField (ResidueField (canonicalValuationSubring k))]

/-- **Countability of the pointed Galois objects** of the Galois presentation of `X` (the
hypothesis `hctbl` of `temperedPi1_hasONSChainO`): a sequence of pointed orbifold Galois objects
dominating all of them ([SemiAnbd], Definition 3.1: tempered groups are countably indexed). -/
def tempCountable (X : Orbicurve k) : Prop :=
  ∃ s : ℕ → GaloisLimit.PtGal
      (tempFibre (canonicalValuationSubring k) (Genuine.orbifold X.E X.level X.M X.pm).R
        (Genuine.orbifold X.E X.level X.M X.pm).A
        ((Genuine.orbifold X.E X.level X.M X.pm).V (canonicalValuationSubring k))
        ((Genuine.orbifold X.E X.level X.M X.pm).V_comap (canonicalValuationSubring k)))
      (galO (canonicalValuationSubring k) (Genuine.orbifold X.E X.level X.M X.pm).R
        (Genuine.orbifold X.E X.level X.M X.pm).A (Genuine.orbifold X.E X.level X.M X.pm).Ω),
    ∀ q, ∃ n, Nonempty (s n ⟶ q)

variable (hp : ∃ p : ℕ, p.Prime ∧ (p : canonicalValuationSubring k) ∈ maximalIdeal _)

include hp in
/-- The properties of `PiTpONS.lean` for an affine orbifold equal to a Galois presentation. -/
lemma genuineTemp_props (E : WeierstrassCurve k) [E.IsElliptic] (ℓ : ℕ)
    (M : AddSubgroup E.toAffine.Point) (pm : Bool) (Y : AffineOrbifold k)
    (hY : Y = Genuine.orbifold E ℓ M pm) :
    T2Space Y.canonicalTemperedPi1 ∧ HasONSBasis Y.canonicalTemperedPi1 ∧
      IsONSComplete Y.canonicalTemperedPi1 := by
  subst hY
  exact ⟨temperedPi1_t2SpaceO _ _ hp (genuineOrbifold_dim E ℓ M pm),
    temperedPi1_hasONSBasisO _ _ hp (genuineOrbifold_dim E ℓ M pm),
    temperedPi1_isONSCompleteO _ _ hp (genuineOrbifold_dim E ℓ M pm)⟩

include hp in
/-- The countable chain for an affine orbifold equal to a Galois presentation. -/
lemma genuineTemp_chain (E : WeierstrassCurve k) [E.IsElliptic] (ℓ : ℕ)
    (M : AddSubgroup E.toAffine.Point) (pm : Bool) (Y : AffineOrbifold k)
    (hY : Y = Genuine.orbifold E ℓ M pm)
    (hctbl : ∃ s : ℕ → GaloisLimit.PtGal
      (tempFibre (canonicalValuationSubring k) (Genuine.orbifold E ℓ M pm).R
        (Genuine.orbifold E ℓ M pm).A
        ((Genuine.orbifold E ℓ M pm).V (canonicalValuationSubring k))
        ((Genuine.orbifold E ℓ M pm).V_comap (canonicalValuationSubring k)))
      (galO (canonicalValuationSubring k) (Genuine.orbifold E ℓ M pm).R
        (Genuine.orbifold E ℓ M pm).A (Genuine.orbifold E ℓ M pm).Ω),
      ∀ q, ∃ n, Nonempty (s n ⟶ q)) :
    HasONSChain Y.canonicalTemperedPi1 := by
  subst hY
  exact temperedPi1_hasONSChainO _ _ hp (genuineOrbifold_dim E ℓ M pm) hctbl

include hp in
/-- **The tempered fundamental group of a model orbicurve is Hausdorff.** -/
theorem temp_t2 (X : Orbicurve k) : T2Space X.temperedPi1 :=
  (genuineTemp_props hp X.E X.level X.M X.pm _
    (congrArg Sigma.fst X.temperedPresentation_of_charZero)).1

include hp in
/-- **The tempered fundamental group of a model orbicurve has a basis of open normal
subgroups.** -/
theorem temp_hasONSBasis (X : Orbicurve k) : HasONSBasis X.temperedPi1 :=
  (genuineTemp_props hp X.E X.level X.M X.pm _
    (congrArg Sigma.fst X.temperedPresentation_of_charZero)).2.1

include hp in
/-- **The tempered fundamental group of a model orbicurve is complete for its open normal
subgroups.** -/
theorem temp_isONSComplete (X : Orbicurve k) : IsONSComplete X.temperedPi1 :=
  (genuineTemp_props hp X.E X.level X.M X.pm _
    (congrArg Sigma.fst X.temperedPresentation_of_charZero)).2.2

include hp in
/-- **A countable cofinal chain of open normal subgroups** of the tempered fundamental group of a
model orbicurve, given the countability of its pointed Galois objects. -/
theorem temp_hasONSChain (X : Orbicurve k) (hc : tempCountable X) :
    HasONSChain X.temperedPi1 :=
  genuineTemp_chain hp X.E X.level X.M X.pm _
    (congrArg Sigma.fst X.temperedPresentation_of_charZero) hc

end Generic

/-! ### `Π_v` at `v ∈ V^bad` -/

section Theta

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-- **The countability input at `v`** (MR18's debt `hctbl`): the pointed Galois objects of the
presentation of `X̲_v` have a dominating sequence (`tempCountable` of `X̲_v` over
`K_v`). -/
def PivCountable : Prop := tempCountable (Xv D v)

/-- **At `v ∈ V^bad`, `Π_v` is Hausdorff, has a basis of open normal subgroups and is complete
for them**; with `PivCountable D v` it has a countable cofinal chain of them. -/
theorem piv_temp (hv : v ∈ D.VBad) :
    T2Space (Piv D v).carrier ∧ HasONSBasis (Piv D v).carrier ∧
      IsONSComplete (Piv D v).carrier ∧ (PivCountable D v → HasONSChain (Piv D v).carrier) := by
  have hp := AdicCompletion.exists_prime_canonical (D.V.sectFin v).maximalIdeal
  unfold Piv piData
  rw [if_pos hv]
  exact ⟨temp_t2 hp (Xv D v), temp_hasONSBasis hp (Xv D v), temp_isONSComplete hp (Xv D v),
    temp_hasONSChain hp (Xv D v)⟩

end Theta

end PrimeStrip

end Multiradial

end Iut
