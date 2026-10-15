/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.TemperedBase
import Iut.Frobenioid.Thm34
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The Galois base categories `B(G)⁰` satisfy the hypotheses of [FrdI], Theorem 3.4

For a topological group `G`, `OrbitObj G` is the category of connected objects `G/H` (`H` open)
of `B(G)` (`Iut/Frobenioid/TemperedBase.lean`). For a profinite (more generally compact) `G` this
is the base category `B(G)⁰` of the `p`-adic Frobenioids of IUT ([FrdII], Example 1.1;
IUT I, Example 3.3: `G = G_v`) and of [FrdI], Example 6.3.

* `OrbitHom.isIso_of_bijective`: a bijective equivariant map is an isomorphism;
* `OrbitObj.isIso_of_isFSM`: `B(G)⁰` is of **FSM-type** (any topological group);
* `OrbitObj.isIso_endo`: for compact `G`, `B(G)⁰` is of **Aut-type** (the sets `G/H` are finite,
  and equivariant self-maps are surjective);
* `OrbitObj.baseHyp`: hence `BaseHyp (OrbitObj G)` for compact `G`;
* `Model.thm34_galois`: [FrdI], Theorem 3.4(iii) for model Frobenioids over `B(G₁)⁰`, `B(G₂)⁰`
  whose rational functions have torsion of every order.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe u u'

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **A bijective morphism of `B(G)⁰` is an isomorphism** (the inverse map is equivariant). -/
lemma OrbitHom.isIso_of_bijective {A B : OrbitObj G} (f : A ⟶ B)
    (hf : Function.Bijective f.toFun) : IsIso f := by
  let e := Equiv.ofBijective _ hf
  refine ⟨⟨⟨e.symm, fun g x => e.injective ?_⟩, ?_, ?_⟩⟩
  · change f.toFun (e.symm (g • x)) = f.toFun (g • e.symm x)
    rw [f.map_smul]
    change e (e.symm (g • x)) = g • e (e.symm x)
    simp
  · ext x
    exact e.symm_apply_apply x
  · ext x
    exact e.apply_symm_apply x

/-- **`B(G)⁰` is of FSM-type** ([FrdI] §0, p. 14): every FSM-morphism is an isomorphism. -/
theorem OrbitObj.isIso_of_isFSM [IsTopologicalGroup G] {A B : OrbitObj G} (f : A ⟶ B)
    (hf : IsFSM f) : IsIso f :=
  OrbitHom.isIso_of_bijective f (OrbitHom.bijective_of_isFSM hf)

/-- **For compact `G`, `B(G)⁰` is of Aut-type** ([FrdI] §0, p. 14): every endomorphism is an
automorphism. -/
theorem OrbitObj.isIso_endo [IsTopologicalGroup G] [CompactSpace G] {A : OrbitObj G}
    (f : A ⟶ A) : IsIso f := by
  haveI := Subgroup.quotient_finite_of_isOpen A.H A.isOpen
  exact OrbitHom.isIso_of_bijective f
    ⟨Finite.injective_iff_surjective.mpr f.surjective, f.surjective⟩

/-- `B(G)⁰` satisfies the hypotheses `BaseHyp` (FSM-type, Aut-type) for compact `G`. -/
theorem OrbitObj.baseHyp [IsTopologicalGroup G] [CompactSpace G] : BaseHyp (OrbitObj G) :=
  ⟨fun _ _ f hf => OrbitObj.isIso_of_isFSM f hf, fun _ f => OrbitObj.isIso_endo f⟩

namespace Model

variable {G₁ : Type u} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [CompactSpace G₁]
variable {G₂ : Type u'} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  [CompactSpace G₂]
variable {Φ₁ : DivMonoid (OrbitObj G₁)} {B₁ : GrpOn (OrbitObj G₁)}
  {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {Φ₂ : DivMonoid (OrbitObj G₂)} {B₂ : GrpOn (OrbitObj G₂)}
  {divB₂ : DivHom B₂ Φ₂.toGrpOn}

/-- **[FrdI], Theorem 3.4(iii) over the Galois base categories `B(G)⁰`**: for compact
(e.g. profinite) `G₁`, `G₂` and model Frobenioids over `B(G₁)⁰`, `B(G₂)⁰` whose rational function
monoids contain torsion of every order (e.g. `μ(K̄) ⊆ (K̄^H)^×`), every equivalence of categories
preserves the Frobenius structure. -/
theorem thm34_galois (hB₁ : HasAllTorsion B₁) (hB₂ : HasAllTorsion B₂)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] :
    PreservesFrobeniusStructure (toElem Φ₁ B₁ divB₁) (toElem Φ₂ B₂ divB₂) F :=
  thm34_preservesFrobeniusStructure OrbitObj.baseHyp hB₁ OrbitObj.baseHyp hB₂ F

end Model

end Frobenioid

end Iut
