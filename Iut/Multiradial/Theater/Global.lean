/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.Theater.GalMor
import Iut.Cor312.ThetaData.Basic

/-!
# The global categories `D^⊚ = B(C̲_K)⁰` and `D^⊚± = B(X̲_K)⁰` (MR22 T2)

IUT I, Definition 4.1 (v) (l.6450 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory
I.txt`): `D^⊚ = B(C̲_K)⁰`, and a **`D^⊚`** is a category isomorphic to it; Definition 6.1 (v)
(l.10663): `D^⊚± = B(X̲_K)⁰` (both underlined, checked on the rendered PDF, see `MR22-plan.md`).
Here `B(X)⁰` is `OrbitObj π₁(X)` for the genuine étale fundamental group `π₁(X)` of the model
orbicurve (`Orbicurve.genuinePi1`); `C̲_K`, `X̲_K` are `D.orb.CKu`, `D.orb.XKu` (IUT I, Definition
3.1 (d)).

* `PiCK D = π₁(C̲_K)`, `PiXK D = π₁(X̲_K)`; `dCircModel D = B(C̲_K)⁰`,
  `dCircPmModel D = B(X̲_K)⁰`;
* `DCircCat D`, `DCircPmCat D`: categories with an equivalence to the models (a `D^⊚`, a `D^⊚±`);
  isomorphisms are equivalences (classes: `PrimeStrip.CatIsom`);
* `π₁(X̲_K) → π₁(C̲_K)` (the open immersion of the covering `X̲_K → C̲_K`, `piXKToCK`) and the
  induced morphism `D^⊚± → D^⊚` of the models (`dCircPmToDCirc`; IUT I, §0: a morphism of
  Galois categories is a transported outer homomorphism, `GalMor`);
* the functorial reconstruction for these profinite groups (`orbitEquivRecon_piCK`, …) and their
  rigidity inputs (`hasONSBasis_piCK`, `isONSComplete_piCK`, …), so that composites of morphisms
  and the morphisms induced by equivalences exist and are unique (`GalMor.lean`).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace Theater

open CategoryTheory Iut.Frobenioid Iut.Anabelian

variable (D : InitialThetaData.{0})

/-- **`π₁(C̲_K)`**, the genuine étale fundamental group of `C̲_K`. -/
abbrev PiCK : Type := D.orb.CKu.genuinePi1

/-- **`π₁(X̲_K)`**, the genuine étale fundamental group of `X̲_K`. -/
abbrev PiXK : Type := D.orb.XKu.genuinePi1

/-- **`D^⊚ = B(C̲_K)⁰`** (IUT I, Definition 4.1 (v)). -/
abbrev dCircModel : Type := OrbitObj (PiCK D)

/-- **`D^⊚± = B(X̲_K)⁰`** (IUT I, Definition 6.1 (v)). -/
abbrev dCircPmModel : Type := OrbitObj (PiXK D)

/-- **A `D^⊚`** (IUT I, Definition 4.1 (v)): a category admitting an equivalence with
`B(C̲_K)⁰`. -/
structure DCircCat : Type 1 where
  /-- The category `†D^⊚`. -/
  C : Cat.{0, 0}
  /-- It admits an equivalence with `B(C̲_K)⁰`. -/
  equiv_model : Nonempty (C ≌ dCircModel D)

/-- **A `D^⊚±`** (IUT I, Definition 6.1 (v)): a category admitting an equivalence with
`B(X̲_K)⁰`. -/
structure DCircPmCat : Type 1 where
  /-- The category `†D^⊚±`. -/
  C : Cat.{0, 0}
  /-- It admits an equivalence with `B(X̲_K)⁰`. -/
  equiv_model : Nonempty (C ≌ dCircPmModel D)

/-- The model `D^⊚` built from `D`. -/
def DCircCat.ofThetaData : DCircCat D :=
  ⟨Cat.of (dCircModel D), ⟨CategoryTheory.Equivalence.refl⟩⟩

/-- The model `D^⊚±` built from `D`. -/
def DCircPmCat.ofThetaData : DCircPmCat D :=
  ⟨Cat.of (dCircPmModel D), ⟨CategoryTheory.Equivalence.refl⟩⟩

variable {D}

/-- Any two `D^⊚` are equivalent. -/
lemma DCircCat.nonempty_equiv (A B : DCircCat D) : Nonempty (A.C ≌ B.C) :=
  ⟨A.equiv_model.some.trans B.equiv_model.some.symm⟩

/-- Any two `D^⊚±` are equivalent. -/
lemma DCircPmCat.nonempty_equiv (A B : DCircPmCat D) : Nonempty (A.C ≌ B.C) :=
  ⟨A.equiv_model.some.trans B.equiv_model.some.symm⟩

/-! ### Reconstruction and rigidity inputs for the profinite groups `π₁(C̲_K)`, `π₁(X̲_K)` -/

/-- Profinite groups have a basis of open normal subgroups. -/
lemma hasONSBasis_profinite (G : ProfiniteGrp.{0}) : HasONSBasis G := fun _ hU h1 =>
  ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1

/-- Profinite groups are complete for their open normal subgroups. -/
lemma isONSComplete_profinite (G : ProfiniteGrp.{0}) : IsONSComplete G :=
  isONSComplete_of_compact

/-- Equivalences between the `B(−)⁰` of profinite groups come from isomorphisms. -/
lemma orbitEquivRecon_profinite (G₁ G₂ : ProfiniteGrp.{0}) : OrbitEquivRecon G₁ G₂ :=
  orbitEquivRecon_of_profinite

variable (D)

/-- **`π₁(X̲_K) → π₁(C̲_K)`** (the covering `X̲_K → C̲_K`, IUT I, Definition 3.1 (d)). -/
def piXKToCK : PiXK D →ₜ* PiCK D :=
  ⟨D.orb.pi1XKu_to_CKu, D.orb.pi1XKu_to_CKu_isOpenEmbedding.continuous⟩

/-- **The morphism `D^⊚± → D^⊚` of the models** induced by `X̲_K → C̲_K` (IUT I, §0). -/
def dCircPmToDCirc : GalMor (dCircPmModel D) (dCircModel D) (PiXK D) (PiCK D) :=
  GalMor.mk ⟨CategoryTheory.Equivalence.refl, CategoryTheory.Equivalence.refl, piXKToCK D⟩

end Theater

end Multiradial

end Iut
