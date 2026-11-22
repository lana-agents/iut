/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.Theater.GenuineBaseChange
import Iut.Multiradial.Theater.Global
import Iut.Multiradial.PrimeStrip.Components

/-!
# The local-to-global homomorphisms `Π_v → π₁(X̲_K) → π₁(C̲_K)` (MR22 T3, part 3)

IUT I, Definition 3.1 (e) (l.4199 ff. of `~/iut-scratch/papers/txt/Inter-universal Teichmuller
Theory I.txt`): `X̲_v = X̲_K ×_K K_v`, and Example 4.3 (ii) (l.6631): the restriction functor along
`X̲_v → X̲_K → C̲_K` gives the natural morphism `φ^NF_{•,v} : D_v → D^⊚`. Group-theoretically
(IUT I, §0) this is the outer homomorphism `Π_v → π₁(C̲_K)`:

* `piXvToXK D v : π₁(X̲_v) → π₁(X̲_K)` (`genuinePi1BaseChange` along `K → K_v`), continuous;
* `piToXK D v : Π_v → π₁(X̲_K)` (through `π₁^temp(X̲_v) → π₁(X̲_v)` at `V^bad`), continuous;
* `piToCK D v : Π_v → π₁(C̲_K)` (composed with the covering `X̲_K → C̲_K`), continuous;
* `phiNFDot D v : D_v → D^⊚`, the morphism of the models `B(Π_v)⁰ → B(C̲_K)⁰`
  (`GalMor`, IUT I, §0).

At `v ∈ V^good` IUT uses the cover `X→_v` of `X̲_v` rather than `X̲_v` itself (debt H7 of
`MR22-plan.md`, task T4); `Π_v` here is MR20's `Piv` (`π₁(X̲_v)`).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace Theater

open CategoryTheory NumberField Iut.Frobenioid Iut.Anabelian PrimeStrip

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-- **`π₁(X̲_v) → π₁(X̲_K)`** (base change along `K → K_v`; IUT I, Definition 3.1 (e)). -/
def piXvToXK : (Xv D v).genuinePi1 →* PiXK D :=
  genuinePi1BaseChange (FinitePlace.embedding (D.V.sectFin v).maximalIdeal) D.orb.XKu
    D.orb.XKu_type

lemma continuous_piXvToXK : Continuous (piXvToXK D v) := by
  unfold piXvToXK genuinePi1BaseChange
  exact GaloisPi1Map.continuous_pi1MapOfHom _ _ _ _ _ _

lemma piv_of_bad (hv : v ∈ D.VBad) : Piv D v = ⟨(Xv D v).temperedPi1⟩ := by
  classical
  unfold Piv piData
  rw [if_pos hv]

lemma piv_of_good (hv : v ∉ D.VBad) : Piv D v = ⟨(Xv D v).genuinePi1⟩ := by
  classical
  unfold Piv piData
  rw [if_neg hv]

/-- `Π_v → π₁(X̲_K)` together with its continuity. -/
def piToXKData : {f : (Piv D v).carrier →* PiXK D // Continuous f} := by
  classical
  by_cases hv : v ∈ D.VBad
  · rw [piv_of_bad D v hv]
    exact ⟨(piXvToXK D v).comp (Xv D v).tempToEtale,
      (continuous_piXvToXK D v).comp (Xv D v).continuous_tempToEtale⟩
  · rw [piv_of_good D v hv]
    exact ⟨piXvToXK D v, continuous_piXvToXK D v⟩

/-- **`Π_v → π₁(X̲_K)`** (tempered-to-étale at `V^bad`, then base change). -/
def piToXK : (Piv D v).carrier →ₜ* PiXK D :=
  ⟨(piToXKData D v).1, (piToXKData D v).2⟩

/-- **`Π_v → π₁(C̲_K)`** (IUT I, Example 4.3 (ii): along `X̲_v → X̲_K → C̲_K`). -/
def piToCK : (Piv D v).carrier →ₜ* PiCK D := (piXKToCK D).comp (piToXK D v)

/-- **`φ^NF_{•,v} : D_v → D^⊚`** on the models (IUT I, Example 4.3 (ii); a morphism of Galois
categories in the sense of IUT I, §0). -/
def phiNFDot : GalMor (Dv D v) (dCircModel D) (Piv D v).carrier (PiCK D) :=
  GalMor.mk ⟨CategoryTheory.Equivalence.refl, CategoryTheory.Equivalence.refl, piToCK D v⟩

/-- **`φ^{Θell}_{•,v} : D_v → D^⊚±`** on the models (IUT I, Example 6.3 (i): along
`X̲_v → X̲_K`). -/
def phiEllDot : GalMor (Dv D v) (dCircPmModel D) (Piv D v).carrier (PiXK D) :=
  GalMor.mk ⟨CategoryTheory.Equivalence.refl, CategoryTheory.Equivalence.refl, piToXK D v⟩

end Theater

end Multiradial

end Iut
