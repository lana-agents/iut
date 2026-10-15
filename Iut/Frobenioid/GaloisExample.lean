/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GaloisSlim
import Iut.Frobenioid.Counterexample

/-!
# A model Frobenioid over `B(G)⁰` satisfying the hypotheses of Theorem 3.4

To check that the hypotheses of `Model.thm34_galois` and `Model.thm34_galois_preservesBase` are
consistent on a genuine Galois base category, we build the model Frobenioid over `B(G)⁰` with the
monoids that do not depend on the object (`Φ = ℤ_{≥0}`, `B = ∏_n ℤ/n`, `Div_B = 0`, identity
pull-backs; these are monoids on `B(G)⁰` in the sense of [FrdI], Definition 1.1(ii)) and record
that every autoequivalence of it preserves the Frobenius structure, and lies over an
autoequivalence of `B(G)⁰` when `G` is slim profinite.

The Frobenioids of IUT over `B(G_v)⁰` (with `B(G/H) = (K̄^H)^×`) are constructed in milestone
MR17.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe u

/-- The group-like monoid on `D` with fixed value `V` and identity pull-backs. -/
abbrev fixedGrpOn (D : Type u) [Category D] (V : Type) [AddCommGroup V] : GrpOn.{0} D where
  obj _ := V
  pb _ := AddMonoidHom.id V
  pb_id _ _ := rfl
  pb_comp _ _ _ := rfl
  pb_injective _ := Function.injective_id
  pb_bijective_of_fsm _ _ := Function.bijective_id

/-- The divisorial monoid on `D` with fixed value `ℤ_{≥0} ⊆ ℤ` and identity pull-backs. -/
abbrev fixedPhiNat (D : Type u) [Category D] : DivMonoid.{0} D where
  toGrpOn := fixedGrpOn D (ULift.{0} ℤ)
  pos _ := natCone.{0}
  pb_mem _ _ h := h
  sharp h h' := Counterexample.PhiN.sharp (A := pt) h h'
  saturated n hn h := Counterexample.PhiN.saturated (A := pt) n hn h
  generating x := Counterexample.PhiN.generating (A := pt) x
  pos_surj_of_fsm _ _ y hy := ⟨y, hy, rfl⟩

namespace GaloisExample

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- `B = ∏_n ℤ/n` on `B(G)⁰`. -/
abbrev bG : GrpOn.{0} (OrbitObj G) := fixedGrpOn (OrbitObj G) Counterexample.Tors

/-- `Div_B = 0`. -/
abbrev divG : DivHom (bG G) (fixedPhiNat (OrbitObj G)).toGrpOn := ⟨fun _ => 0, fun _ _ => rfl⟩

/-- **The model Frobenioid over `B(G)⁰`.** -/
abbrev Ex : Type u := Model (fixedPhiNat (OrbitObj G)) (bG G) (divG G)

omit [IsTopologicalGroup G] [CompactSpace G] in
lemma hasAllTorsion : HasAllTorsion (bG G) :=
  fun A n hn => ⟨A, 𝟙 A, Pi.single n 1, Counterexample.tors_spec n hn⟩

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- `Ex G` is a Frobenioid ([FrdI], Theorem 5.2(ii)). -/
theorem isFrobenioid :
    IsFrobenioid (Model.toElem (fixedPhiNat (OrbitObj G)) (bG G) (divG G)) :=
  Model.isFrobenioid

/-- **Every autoequivalence of `Ex G` preserves the Frobenius structure** ([FrdI], Theorem
3.4(iii)). -/
theorem thm34 (F : Ex G ⥤ Ex G) [F.IsEquivalence] :
    PreservesFrobeniusStructure (Model.toElem (fixedPhiNat (OrbitObj G)) (bG G) (divG G))
      (Model.toElem (fixedPhiNat (OrbitObj G)) (bG G) (divG G)) F :=
  Model.thm34_galois (hasAllTorsion G) (hasAllTorsion G) F

/-- **For `G` slim profinite, every autoequivalence of `Ex G` lies over a functor
`B(G)⁰ → B(G)⁰`** ([FrdI], Theorem 3.4(v)). -/
theorem thm34_base [TotallyDisconnectedSpace G] [T2Space G] (hG : IsSlimGroup G)
    (F : Ex G ⥤ Ex G) [F.IsEquivalence] :
    PreservesBase (Model.toElem (fixedPhiNat (OrbitObj G)) (bG G) (divG G))
      (Model.toElem (fixedPhiNat (OrbitObj G)) (bG G) (divG G)) F :=
  Model.thm34_galois_preservesBase hG (hasAllTorsion G) (hasAllTorsion G) F

end GaloisExample

end Frobenioid

end Iut
