/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Torsion
import Mathlib.Algebra.Group.Pi.Basic

/-!
# The output types of IUT III, Theorem 3.11 (multiradial roadmap, MR0)

This file fixes, as Lean types, what the output of the multiradial algorithm of IUT III,
Theorem 3.11 is, and what the phrases

* "an algorithm in the procession of `D⊢`-prime-strips `Prc(n,∘D⊢_T)` that is *functorial with
  respect to isomorphisms of processions*" (Theorem 3.11(i)), and
* "regarded up to the indeterminacies (Ind1), (Ind2)" (Theorem 3.11(i)), "(Ind3)"
  (Theorem 3.11(ii)), and "up to roots of unity" (Remark 3.11.4(i))

mean formally. It contains no IUT object: everything is stated for an arbitrary groupoid of inputs
and an arbitrary raw-output functor. The genuine instance (inputs the processions of
`D⊢`-prime-strips of IUT I, Proposition 6.9(ii), raw output the data (a)–(c) of Theorem 3.11(i)) is
milestone MR30 (`Plans/MultiradialTarget.md`).

## The reading of Theorem 3.11 that is formalised

* **Inputs** (Theorem 3.11(i); Remark 3.11.1(ii), (v)): the input of the algorithm is an object of a
  groupoid `G`, "regarded up to isomorphism"; for Theorem 3.11 it is the procession `Prc(n,∘D⊢_T)`
  of IUT I, Definition 4.10 / Proposition 6.9(ii), and `G` is the groupoid of processions of
  `D⊢`-prime-strips (`Procession`).
* **Raw output** (Theorem 3.11(i)(a)–(c)): a functor `R.F : G ⥤ Type` (the data (a), (b), (c) built
  from the input) together with a natural action of the (Ind2)-group `A` (`RawOutput`). In
  Theorem 3.11(ii) these are "data which has not yet been subjected to the indeterminacies (Ind1),
  (Ind2)".
* **(Ind1)** "the indeterminacies induced by the automorphisms of the procession": the action of
  `Aut P` on `R.F.obj P` through the functor.
* **(Ind2)** "independent copies of `Ism`" (respectively, of the automorphisms of order 2) "on each
  of the direct summands of the `j+1` factors" of the tensor packet at `v_ℚ`: the product group
  `Ind2Group` acting on the raw output.
* **The output** `n,∘R^LGP` is the raw output regarded up to (Ind1) and (Ind2): the **orbit type**
  `MRRep R P` of `R.F.obj P` under `Aut P × A` (`Ind12Action`).
* **Functoriality** in isomorphisms of processions: an isomorphism `f : P ⟶ Q` induces
  `MRRep.transport f : MRRep R P → MRRep R Q`, which does **not depend on `f`**
  (`MRRep.transport_eq_transport`): (Ind1) is exactly what makes the output independent of the
  choice of isomorphism. An algorithm is a choice `alg P : MRRep R P` for every input with
  `transport f (alg P) = alg Q` (`IsFunctorialAlg`). The étale-picture permutation symmetries of
  Theorem 3.11(i) are poly-isomorphisms `Prc(n,∘D⊢_T) ⥲ Prc(n',∘D⊢_T)`; every member of a
  poly-isomorphism carries `alg P` to `alg Q` (`IsFunctorialAlg.polyIso_compat`). This is why the
  last sentences of Theorem 3.11(i) "follow immediately from the definitions".
* **(Ind3)** (Theorem 3.11(ii); IUT III, Proposition 3.5(ii)(a), (b)): the isomorphisms of (a) are
  only *upper semi-compatible* along the log-links: a region `S` is acceptable for the coric region
  `R` when `S ⊆ R` (`UpperSemi`); a vertical family of regions is upper semi-compatible when every
  member is (`UpperSemiCompatible`). Modulo (Ind3), a region `R` stands for all its subregions
  (`ind3Possible R = Set.Iic R`), whose union is `R` again (`sUnion_ind3Possible`). The *possible
  images* of an output are the union over the (Ind1)×(Ind2)-orbit (`MRRep.possibleRegion`), and
  every region obtained modulo (Ind3) from a representative lies in it
  (`MRRep.subset_possibleRegion`); these are the "possible images" of IUT III, Corollary 3.12,
  Steps (iv), (x).
* **Roots of unity** (Remark 3.11.4(i)): the data of Theorem 3.11(ii)(b), (c) may only be
  considered up to multiplication by roots of unity: the orbit type `ModMu M` of a commutative
  monoid under its torsion units, on which the theta values and the number fields `F_mod` live
  (`ModMu.mk_eq_mk_iff`); a set stable under multiplication by a root of unity is a union of
  orbits (`ModMu.mem_iff_of_stable`), Remark 3.11.4(i)'s "the entire set … is stabilized".

## Processions (IUT I, §0 and Definition 4.10)

A capsule of objects of `C` is a finite family `{A_t}_{t ∈ J}`; an `n`-procession is a diagram
`P_1 ↪ ⋯ ↪ P_n` of a `j`-capsule `P_j` for each `j`, where each arrow is the collection of *all*
capsule-full poly-morphisms, so it carries no data. A morphism of `n`-processions consists of an
order-preserving injection `{1,…,n} ↪ {1,…,n}` — necessarily the identity — and, for each `j`, a
capsule-full poly-morphism `P_j → Q_j`, i.e. an injection (here a bijection) of index sets together
with isomorphisms of the components. We take the index set of the `(j+1)`-st capsule to be the
naked set `Fin (j + 1)`: by Remark 3.11.2(ii) these index sets are "just naked sets which are
determined, up to isomorphism, by their cardinality", and the morphisms below permute them
arbitrarily. An isomorphism of processions (`Procession.Hom`) records one member of the
capsule-full poly-isomorphism (a bijection and isomorphisms of the components); the
poly-isomorphism itself is the set of all of them with the same bijections, and its induced
indeterminacy is (Ind1).
-/

namespace Iut.Multiradial

open CategoryTheory

universe u v w w'

/-! ### Raw outputs, (Ind1), (Ind2) and the orbit type `MRRep` -/

section General

variable {G : Type u} [Groupoid.{v} G]

/-- The automorphism group `Aut P` of an input acts on the raw output `F.obj P` through the
functor: the **(Ind1)** indeterminacy of IUT III, Theorem 3.11(i). -/
instance autAction (F : G ⥤ Type w) (P : G) : MulAction (Aut P) (F.obj P) where
  smul σ x := F.map σ.hom x
  one_smul x := Functor.map_id_apply F P x
  mul_smul σ τ x := by
    change F.map (τ.hom ≫ σ.hom) x = F.map σ.hom (F.map τ.hom x)
    exact Functor.map_comp_apply F τ.hom σ.hom x

lemma autAction_smul_def (F : G ⥤ Type w) {P : G} (σ : Aut P) (x : F.obj P) :
    σ • x = F.map σ.hom x := rfl

/-- **The raw output of a multiradial algorithm** (the data (a), (b), (c) of IUT III,
Theorem 3.11(i), "which has not yet been subjected to the indeterminacies (Ind1), (Ind2)",
Theorem 3.11(ii)): a functor from the groupoid of inputs to types, with an action of the
**(Ind2)-group** `A` on each output that commutes with the transport along isomorphisms of
inputs. -/
structure RawOutput (G : Type u) [Groupoid.{v} G] (A : Type w') [Group A] where
  /-- The raw output, functorial in isomorphisms of inputs. -/
  F : G ⥤ Type w
  /-- The (Ind2)-action on the raw output of each input. -/
  act : ∀ P, MulAction A (F.obj P)
  /-- The (Ind2)-action commutes with the transport along isomorphisms of inputs (the copies of
  `Ism` act on the tensor packets, which are built functorially from the input). -/
  natural : ∀ ⦃P Q : G⦄ (f : P ⟶ Q) (a : A) (x : F.obj P),
    F.map f ((act P).smul a x) = (act Q).smul a (F.map f x)

namespace RawOutput

variable {A : Type w'} [Group A] (R : RawOutput.{u, v, w} G A)

attribute [instance] act

lemma map_smul {P Q : G} (f : P ⟶ Q) (a : A) (x : R.F.obj P) :
    R.F.map f (a • x) = a • R.F.map f x :=
  R.natural f a x

lemma aut_smul_comm {P : G} (σ : Aut P) (a : A) (x : R.F.obj P) :
    σ • (a • x) = a • (σ • x) :=
  R.map_smul σ.hom a x

/-- **The combined (Ind1)×(Ind2)-action** of IUT III, Theorem 3.11(i): `(σ, a) • x = σ • (a • x)`
on the raw output of an input `P`, for `σ ∈ Aut P` (Ind1) and `a` in the (Ind2)-group. -/
abbrev Ind12Action (P : G) : MulAction (Aut P × A) (R.F.obj P) where
  smul g x := g.1 • (g.2 • x)
  one_smul x := by
    change (1 : Aut P) • ((1 : A) • x) = x
    rw [one_smul, one_smul]
  mul_smul g h x := by
    change (g.1 * h.1) • ((g.2 * h.2) • x) = g.1 • (g.2 • (h.1 • (h.2 • x)))
    rw [mul_smul, mul_smul, R.aut_smul_comm h.1 g.2]

attribute [local instance] Ind12Action

lemma ind12_smul_def {P : G} (g : Aut P × A) (x : R.F.obj P) : g • x = g.1 • (g.2 • x) := rfl

end RawOutput

/-- **The multiradial representation** `n,∘R^LGP` of IUT III, Theorem 3.11(i): the raw output of
the input `P`, "regarded up to the indeterminacies (Ind1), (Ind2)", i.e. an orbit of the
(Ind1)×(Ind2)-action `RawOutput.Ind12Action`. -/
structure MRRep {A : Type w'} [Group A] (R : RawOutput.{u, v, w} G A) (P : G) where
  /-- The multiradial representation given by an orbit. -/
  ofOrbit ::
  /-- The (Ind1)×(Ind2)-orbit. -/
  orbit : @MulAction.orbitRel.Quotient (Aut P × A) (R.F.obj P) _ (R.Ind12Action P)

namespace MRRep

variable {A : Type w'} [Group A] {R : RawOutput.{u, v, w} G A}

attribute [local instance] RawOutput.Ind12Action

/-- The multiradial representation of a representative of the raw output. -/
def mk {P : G} (x : R.F.obj P) : MRRep R P := ⟨⟦x⟧⟩

lemma mk_eq_mk_iff {P : G} (x y : R.F.obj P) :
    mk (R := R) x = mk y ↔ ∃ (σ : Aut P) (a : A), y = σ • (a • x) := by
  constructor
  · intro h
    have h' : (⟦x⟧ : MulAction.orbitRel.Quotient (Aut P × A) (R.F.obj P)) = ⟦y⟧ :=
      congrArg MRRep.orbit h
    obtain ⟨g, hg⟩ := Quotient.exact h'
    change g • y = x at hg
    refine ⟨g⁻¹.1, g⁻¹.2, ?_⟩
    change y = g⁻¹ • x
    rw [← hg, inv_smul_smul]
  · rintro ⟨σ, a, rfl⟩
    refine congrArg MRRep.ofOrbit (Quotient.sound ⟨(σ, a)⁻¹, ?_⟩)
    change (σ, a)⁻¹ • ((σ, a) • x) = x
    exact inv_smul_smul _ _

lemma exists_mk {P : G} (r : MRRep R P) : ∃ x, mk x = r := by
  obtain ⟨o⟩ := r
  induction o using Quotient.inductionOn with
  | h x => exact ⟨x, rfl⟩

/-- Conjugating an automorphism of `P` by an isomorphism `f : P ⟶ Q`. -/
noncomputable def conjAut {P Q : G} (f : P ⟶ Q) (σ : Aut P) : Aut Q :=
  asIso (Groupoid.inv f ≫ σ.hom ≫ f)

lemma map_aut_smul {P Q : G} (f : P ⟶ Q) (σ : Aut P) (x : R.F.obj P) :
    R.F.map f (σ • x) = conjAut f σ • R.F.map f x := by
  change R.F.map f (R.F.map σ.hom x) = R.F.map (Groupoid.inv f ≫ σ.hom ≫ f) (R.F.map f x)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  congr 1
  simp

/-- The representative-level transport respects the (Ind1)×(Ind2)-orbits. -/
lemma map_mem_orbit {P Q : G} (f : P ⟶ Q) {x y : R.F.obj P} (h : mk (R := R) x = mk y) :
    mk (R := R) (R.F.map f x) = mk (R.F.map f y) := by
  obtain ⟨σ, a, rfl⟩ := (mk_eq_mk_iff x y).1 h
  rw [mk_eq_mk_iff, map_aut_smul, R.map_smul]
  exact ⟨conjAut f σ, a, rfl⟩

/-- **Transport of multiradial representations** along an isomorphism of inputs. -/
noncomputable def transport {P Q : G} (f : P ⟶ Q) (r : MRRep R P) : MRRep R Q :=
  ⟨Quotient.lift (fun x => (mk (R.F.map f x)).orbit)
    (fun _ _ hxy => congrArg MRRep.orbit
      (map_mem_orbit f (congrArg MRRep.ofOrbit (Quotient.sound hxy)))) r.orbit⟩

@[simp]
lemma transport_mk {P Q : G} (f : P ⟶ Q) (x : R.F.obj P) :
    transport f (mk (R := R) x) = mk (R.F.map f x) := rfl

lemma transport_id {P : G} (r : MRRep R P) : transport (𝟙 P) r = r := by
  obtain ⟨x, rfl⟩ := exists_mk r
  rw [transport_mk, Functor.map_id_apply]

lemma transport_comp {P Q S : G} (f : P ⟶ Q) (g : Q ⟶ S) (r : MRRep R P) :
    transport (f ≫ g) r = transport g (transport f r) := by
  obtain ⟨x, rfl⟩ := exists_mk r
  rw [transport_mk, transport_mk, transport_mk, Functor.map_comp_apply]

/-- **(Ind1) makes the output independent of the choice of isomorphism**: any two isomorphisms
`P ⟶ Q` of inputs induce the same transport of multiradial representations. This is the formal
content of "functorial with respect to isomorphisms of processions" in IUT III,
Theorem 3.11(i): the output depends on the input only up to isomorphism (Remark 3.11.1(ii),
(v)). -/
theorem transport_eq_transport {P Q : G} (f g : P ⟶ Q) : transport (R := R) f = transport g := by
  funext r
  obtain ⟨x, rfl⟩ := exists_mk r
  rw [transport_mk, transport_mk, mk_eq_mk_iff]
  refine ⟨asIso (Groupoid.inv f ≫ g), 1, ?_⟩
  rw [one_smul, autAction_smul_def, asIso_hom, ← Functor.map_comp_apply]
  simp

/-- Transport along an isomorphism is a bijection. -/
noncomputable def transportEquiv {P Q : G} (f : P ⟶ Q) : MRRep R P ≃ MRRep R Q where
  toFun := transport f
  invFun := transport (Groupoid.inv f)
  left_inv r := by rw [← transport_comp, Groupoid.comp_inv, transport_id]
  right_inv r := by rw [← transport_comp, Groupoid.inv_comp, transport_id]

/-- **The possible images** of a multiradial representation, for a region-valued
construction `reg` on the raw output: the union of the regions of all representatives of the
(Ind1)×(Ind2)-orbit (IUT III, Corollary 3.12, Steps (iv), (x): "the union of the possible
images"). -/
def possibleRegion {P : G} {X : Type*} (reg : R.F.obj P → Set X) (r : MRRep R P) : Set X :=
  ⋃ (x : R.F.obj P) (_ : mk x = r), reg x

lemma reg_subset_possibleRegion {P : G} {X : Type*} (reg : R.F.obj P → Set X)
    (x : R.F.obj P) : reg x ⊆ possibleRegion reg (mk (R := R) x) :=
  Set.subset_biUnion_of_mem (u := fun y => reg y) (show x ∈ {y | mk y = mk x} from rfl)

end MRRep

/-- **An algorithm functorial with respect to isomorphisms of the input** (IUT III,
Theorem 3.11(i); Remark 3.11.1(ii), (v)): an output `alg P` for every input `P`, compatible with
the transport along every isomorphism of inputs. -/
def IsFunctorialAlg {A : Type w'} [Group A] (R : RawOutput.{u, v, w} G A)
    (alg : ∀ P, MRRep R P) : Prop :=
  ∀ ⦃P Q : G⦄ (f : P ⟶ Q), MRRep.transport f (alg P) = alg Q

namespace IsFunctorialAlg

variable {A : Type w'} [Group A] {R : RawOutput.{u, v, w} G A} {alg : ∀ P, MRRep R P}

/-- **Compatibility with poly-isomorphisms** (the étale-picture permutation symmetries
`Prc(n,∘D⊢_T) ⥲ Prc(n',∘D⊢_T)` and `n,∘R^LGP ⥲ n',∘R^LGP` of IUT III, Theorem 3.11(i)): every
member `f` of a poly-isomorphism `Φ ⊆ (P ⟶ Q)` carries `alg P` to `alg Q`, and all members
induce the same map. -/
theorem polyIso_compat (h : IsFunctorialAlg R alg) {P Q : G} (Φ : Set (P ⟶ Q)) :
    (∀ f ∈ Φ, MRRep.transport f (alg P) = alg Q) ∧
      ∀ f ∈ Φ, ∀ g ∈ Φ, MRRep.transport (R := R) f = MRRep.transport g :=
  ⟨fun f _ => h f, fun f _ g _ => MRRep.transport_eq_transport f g⟩

/-- A raw construction that is natural on the nose (a section of the raw-output functor) gives
a functorial algorithm. -/
theorem of_section (s : R.F.sections) : IsFunctorialAlg R fun P => MRRep.mk (s.val P) :=
  fun _ _ f => by rw [MRRep.transport_mk, s.property f]

/-- A raw construction `run` gives a functorial algorithm as soon as it is natural **up to the
indeterminacies** (Ind1), (Ind2): this is the form in which functoriality is proved for a
construction that involves choices (labels, rigidifications). -/
theorem of_run (run : ∀ P, R.F.obj P)
    (hrun : ∀ ⦃P Q : G⦄ (f : P ⟶ Q), ∃ (σ : Aut Q) (a : A),
      R.F.map f (run P) = σ • (a • run Q)) :
    IsFunctorialAlg R fun P => MRRep.mk (run P) := by
  intro P Q f
  rw [MRRep.transport_mk]
  obtain ⟨σ, a, h⟩ := hrun f
  rw [h, MRRep.mk_eq_mk_iff]
  refine ⟨σ⁻¹, a⁻¹, ?_⟩
  rw [RawOutput.aut_smul_comm, smul_smul, inv_mul_cancel, one_smul, inv_smul_smul]

/-- The output of a functorial algorithm on isomorphic inputs determines each other. -/
theorem eq_of_iso (h : IsFunctorialAlg R alg) {P Q : G} (f : P ⟶ Q) :
    alg Q = MRRep.transportEquiv f (alg P) :=
  (h f).symm

end IsFunctorialAlg

/-- **The shape of IUT III, Theorem 3.11(i)** for the inputs `P n` of the vertical lines `n ∈ ℤ`
(the processions `Prc(n,∘D⊢_T)`) and the étale-picture permutation symmetries, given as
poly-isomorphisms `Φ n n' ⊆ (P n ⟶ P n')`: the algorithm is functorial in isomorphisms of inputs
and the poly-isomorphisms `Prc(n,∘D⊢_T) ⥲ Prc(n',∘D⊢_T)` induce compatible poly-isomorphisms
`n,∘R^LGP ⥲ n',∘R^LGP`. -/
def Thm311iShape {A : Type w'} [Group A] (R : RawOutput.{u, v, w} G A) (alg : ∀ P, MRRep R P)
    (P : ℤ → G) (Φ : ∀ n n' : ℤ, Set (P n ⟶ P n')) : Prop :=
  IsFunctorialAlg R alg ∧ ∀ n n' : ℤ, ∀ f ∈ Φ n n', MRRep.transport f (alg (P n)) = alg (P n')

/-- The étale-picture part of Theorem 3.11(i) follows from functoriality ("follow immediately
from the definitions", proof of Theorem 3.11). -/
theorem thm311iShape_of_isFunctorial {A : Type w'} [Group A] {R : RawOutput.{u, v, w} G A}
    {alg : ∀ P, MRRep R P} (h : IsFunctorialAlg R alg) (P : ℤ → G)
    (Φ : ∀ n n' : ℤ, Set (P n ⟶ P n')) : Thm311iShape R alg P Φ :=
  ⟨h, fun _ _ f _ => h f⟩

end General

/-! ### The (Ind2)-group -/

/-- **The (Ind2)-group** of IUT III, Theorem 3.11(i): independent copies of the local
indeterminacy group `Ism v` (Proposition 1.2(vi); at archimedean places, the group of order 2 of
Proposition 1.2(vii)) acting on each direct summand `v ∣ v_ℚ` of each of the `j + 1` tensor factors
of the packet `I_ℚ(S^±_{j+1}; D⊢_{v_ℚ})`, `j = 0, …, ℓ*`. The direct summands over all `v_ℚ` are
indexed by `v ∈ V`, so the group is `∏_{j ≤ ℓ*} ∏_{i ≤ j} ∏_{v ∈ V} Ism v`. -/
abbrev Ind2Group (lstar : ℕ) (V : Type*) (Ism : V → Type*) [∀ v, Group (Ism v)] :=
  ∀ (j : Fin (lstar + 1)) (_ : Fin (j + 1)) (v : V), Ism v

/-- The local indeterminacy groups at `V = V^non ⊔ V^arc`: `Ism v` at nonarchimedean places, the
group `ℤ/2` (generated by the automorphism of order 2 of Proposition 1.2(vii)) at archimedean
places. -/
def IsmFamily {Vnon Varc : Type*} (IsmNon : Vnon → Type*) : Vnon ⊕ Varc → Type _
  | Sum.inl v => ULift (IsmNon v)
  | Sum.inr _ => ULift (Multiplicative (ZMod 2))

instance {Vnon Varc : Type*} (IsmNon : Vnon → Type*) [∀ v, Group (IsmNon v)] :
    ∀ v, Group (IsmFamily (Varc := Varc) IsmNon v)
  | Sum.inl _ => inferInstanceAs (Group (ULift _))
  | Sum.inr _ => inferInstanceAs (Group (ULift _))

/-- The archimedean copies have order 2. -/
lemma card_ismFamily_inr {Vnon Varc : Type*} (IsmNon : Vnon → Type*) (v : Varc) :
    Nat.card (IsmFamily (Varc := Varc) IsmNon (Sum.inr v)) = 2 := by
  change Nat.card (ULift (Multiplicative (ZMod 2))) = 2
  rw [Nat.card_ulift, Nat.card_eq_fintype_card]
  rfl

/-- **Independence of the copies**: an element of the (Ind2)-group acting only on the direct
summand `v` of the factor `i` of the packet `j` (and trivially elsewhere). -/
def Ind2Group.single {lstar : ℕ} {V : Type*} [DecidableEq V] {Ism : V → Type*}
    [∀ v, Group (Ism v)] (j : Fin (lstar + 1)) (i : Fin (j + 1)) (v : V) (g : Ism v) :
    Ind2Group lstar V Ism :=
  fun j' i' v' =>
    if h : j' = j ∧ (i' : ℕ) = i ∧ v' = v then h.2.2 ▸ g else 1

lemma Ind2Group.single_apply_self {lstar : ℕ} {V : Type*} [DecidableEq V] {Ism : V → Type*}
    [∀ v, Group (Ism v)] (j : Fin (lstar + 1)) (i : Fin (j + 1)) (v : V) (g : Ism v) :
    Ind2Group.single j i v g j i v = g := by
  simp [Ind2Group.single]

/-! ### (Ind3): upper semi-compatibility -/

section Ind3

variable {X : Type*}

/-- **Upper semi-compatibility** of a region `S` with the coric region `R` (IUT III,
Proposition 3.5(ii)(a), (b); the indeterminacy (Ind3) of Theorem 3.11(ii)): the natural inclusion
`S ⊆ R` (at `v_ℚ ∈ V^non`; at `v_ℚ ∈ V^arc` the natural surjections, read on the regions they
determine). -/
def UpperSemi (R S : Set X) : Prop := S ⊆ R

/-- A vertical family of regions (indexed by the vertical coordinate `m ∈ ℤ` of the log-theta
lattice, e.g. the images of the isomorphisms of Theorem 3.11(ii)(a) together with their iterated
log-link images) is **upper semi-compatible** with the coric region `R`. -/
def UpperSemiCompatible (img : ℤ → Set X) (R : Set X) : Prop := ∀ m, UpperSemi R (img m)

/-- **A region modulo (Ind3)**: a region `R` stands for every region that is upper
semi-compatible with it. -/
def ind3Possible (R : Set X) : Set (Set X) := {S | UpperSemi R S}

lemma ind3Possible_eq_Iic (R : Set X) : ind3Possible R = Set.Iic R := rfl

/-- The union of the possible regions modulo (Ind3) is the region itself: (Ind3) does not
enlarge the union of possible images. -/
theorem sUnion_ind3Possible (R : Set X) : ⋃₀ ind3Possible R = R :=
  Set.sUnion_eq_of_mem (fun _ h => h) (subset_refl R)
where
  /-- Auxiliary: a family of subsets of `R` containing `R` has union `R`. -/
  Set.sUnion_eq_of_mem {𝒮 : Set (Set X)} (h₁ : ∀ S ∈ 𝒮, S ⊆ R) (h₂ : R ∈ 𝒮) : ⋃₀ 𝒮 = R :=
    subset_antisymm (Set.sUnion_subset h₁) (Set.subset_sUnion_of_mem h₂)

lemma UpperSemiCompatible.iUnion_subset {img : ℤ → Set X} {R : Set X}
    (h : UpperSemiCompatible img R) : (⋃ m, img m) ⊆ R :=
  Set.iUnion_subset h

lemma UpperSemi.trans {R S T : Set X} (h₁ : UpperSemi R S) (h₂ : UpperSemi S T) :
    UpperSemi R T :=
  Set.Subset.trans h₂ h₁

end Ind3

/-- **(Ind3) inside the possible images**: every region that is upper semi-compatible with the
region of a representative lies in the possible images of the multiradial representation. -/
theorem MRRep.subset_possibleRegion {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]
    {R : RawOutput.{u, v, w} G A} {P : G} {X : Type*} (reg : R.F.obj P → Set X)
    (x : R.F.obj P) {S : Set X} (hS : S ∈ ind3Possible (reg x)) :
    S ⊆ MRRep.possibleRegion reg (MRRep.mk (R := R) x) :=
  Set.Subset.trans (show S ⊆ reg x from hS) (MRRep.reg_subset_possibleRegion reg x)

/-! ### Roots of unity (Remark 3.11.4) -/

section ModMu

variable (M : Type*) [CommMonoid M]

/-- **Data up to roots of unity** (IUT III, Remark 3.11.4(i)): the orbit type of a commutative
monoid `M` under multiplication by its roots of unity (the torsion subgroup of `Mˣ`); the data of
Theorem 3.11(ii)(b), (c) (theta values, copies of `F_mod^×`) "may only be considered up to
multiplication by roots of unity". -/
abbrev ModMu : Type _ := MulAction.orbitRel.Quotient (CommGroup.torsion Mˣ) M

variable {M}

/-- The class of `x` modulo roots of unity. -/
def ModMu.mk (x : M) : ModMu M := ⟦x⟧

theorem ModMu.mk_eq_mk_iff (x y : M) :
    ModMu.mk x = ModMu.mk y ↔ ∃ ζ : Mˣ, IsOfFinOrder ζ ∧ (ζ : M) * x = y := by
  constructor
  · intro h
    obtain ⟨⟨ζ, hζ⟩, hζx⟩ := Quotient.exact h
    change (ζ : M) * y = x at hζx
    refine ⟨ζ⁻¹, ((CommGroup.mem_torsion ζ).1 hζ).inv, ?_⟩
    rw [← hζx, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  · rintro ⟨ζ, hζ, rfl⟩
    refine Quotient.sound ⟨⟨ζ⁻¹, (CommGroup.mem_torsion _).2 hζ.inv⟩, ?_⟩
    change ((ζ⁻¹ : Mˣ) : M) * ((ζ : M) * x) = x
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- **A set stable under multiplication by roots of unity is a union of orbits** (Remark
3.11.4(i): constructions that only use "the entire set constituted by the number field", which is
stabilized by multiplication by roots of unity, are insensitive to this indeterminacy). -/
theorem ModMu.mem_iff_of_stable {S : Set M}
    (hS : ∀ ζ : Mˣ, IsOfFinOrder ζ → ∀ x ∈ S, (ζ : M) * x ∈ S) {x y : M}
    (h : ModMu.mk x = ModMu.mk y) : x ∈ S ↔ y ∈ S := by
  obtain ⟨ζ, hζ, rfl⟩ := (ModMu.mk_eq_mk_iff x y).1 h
  refine ⟨hS ζ hζ x, fun hy => ?_⟩
  have := hS ζ⁻¹ hζ.inv _ hy
  rwa [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at this

end ModMu

/-! ### Processions (IUT I, Definition 4.10) -/

/-- **An `n`-procession** of objects of `C` (IUT I, Definition 4.10; Proposition 6.9(ii) for the
processions `Prc(n,∘D⊢_T)` of Theorem 3.11): for each `j < n`, a `(j+1)`-capsule, with index set
the naked set `Fin (j + 1)`. The arrows `P_j ↪ P_{j+1}` of a procession are the collections of
all capsule-full poly-morphisms, so they carry no data. -/
structure Procession (C : Type u) (n : ℕ) where
  /-- The component `t` of the capsule `j`. -/
  obj : (j : Fin n) → Fin (j + 1) → C

namespace Procession

variable {C : Type u} [Category.{v} C] {n : ℕ}

/-- **An isomorphism of `n`-processions** (IUT I, Definition 4.10): the order-preserving injection
of index sets is the identity of `{1, …, n}`; for each capsule, a bijection of its index set and
isomorphisms of the components. It is a member of the capsule-full poly-isomorphism with the same
bijections. -/
structure Hom (P Q : Procession C n) where
  /-- The bijection of the index set of the capsule `j`. -/
  perm : (j : Fin n) → Equiv.Perm (Fin (j + 1))
  /-- The isomorphisms of the components. -/
  iso : (j : Fin n) → (t : Fin (j + 1)) → (P.obj j t ≅ Q.obj j (perm j t))

namespace Hom

variable {P Q S T : Procession C n}

/-- Two isomorphisms of processions with the same bijections and the same component maps are
equal. -/
theorem ext' {f g : Hom P Q} (hp : f.perm = g.perm)
    (hi : ∀ j t, (f.iso j t).hom ≫ eqToHom (by rw [hp]) = (g.iso j t).hom) : f = g := by
  obtain ⟨fp, fi⟩ := f
  obtain ⟨gp, gi⟩ := g
  change fp = gp at hp
  subst hp
  simp only [eqToHom_refl, Category.comp_id] at hi
  congr
  funext j t
  exact Iso.ext (hi j t)

/-- The identity. -/
def id (P : Procession C n) : Hom P P := ⟨fun _ => Equiv.refl _, fun _ _ => Iso.refl _⟩

/-- Composition. -/
def comp (f : Hom P Q) (g : Hom Q S) : Hom P S :=
  ⟨fun j => (f.perm j).trans (g.perm j), fun j t => f.iso j t ≪≫ g.iso j (f.perm j t)⟩

/-- The inverse. -/
def inv (f : Hom P Q) : Hom Q P :=
  ⟨fun j => (f.perm j).symm, fun j t =>
    eqToIso (congrArg (Q.obj j) (Equiv.apply_symm_apply (f.perm j) t).symm) ≪≫
      (f.iso j ((f.perm j).symm t)).symm⟩

end Hom

/-- **The groupoid of `n`-processions** of objects of `C` and their isomorphisms (IUT I,
Definition 4.10, restricted to isomorphisms; the input groupoid of IUT III, Theorem 3.11(i)). -/
instance groupoid : Groupoid (Procession C n) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext' rfl fun j t => by simp [Hom.comp, Hom.id]
  comp_id f := Hom.ext' rfl fun j t => by simp [Hom.comp, Hom.id]
  assoc f g h := Hom.ext' rfl fun j t => by simp [Hom.comp]
  inv := Hom.inv
  inv_comp f := Hom.ext' (by funext j; exact Equiv.symm_trans_self _) fun j t => by
    simp [Hom.comp, Hom.inv, Hom.id]
  comp_inv f := Hom.ext' (by funext j; exact Equiv.self_trans_symm _) fun j t => by
    simp [Hom.comp, Hom.inv, Hom.id]

@[simp]
lemma id_iso (P : Procession C n) (j : Fin n) (t : Fin (j + 1)) :
    Hom.iso (𝟙 P : P ⟶ P) j t = Iso.refl _ := rfl

@[simp]
lemma comp_iso {P Q S : Procession C n} (f : P ⟶ Q) (g : Q ⟶ S) (j : Fin n) (t : Fin (j + 1)) :
    Hom.iso (f ≫ g) j t = Hom.iso f j t ≪≫ Hom.iso g j (Hom.perm f j t) := rfl

/-- The bijections of index sets of an automorphism of a procession: the label indeterminacy
part of (Ind1) (IUT III, Remark 3.11.2(ii)). -/
def labelPerm {P : Procession C n} (σ : Aut P) (j : Fin n) : Equiv.Perm (Fin (j + 1)) :=
  Hom.perm σ.hom j

/-- **Every relabelling is an automorphism** of a procession whose capsules consist of
isomorphic objects (as for `Prc(n,∘D⊢_T)`, whose components are isomorphs of one
`D⊢`-prime-strip): for any bijections of the index sets there is an automorphism inducing them. So
the label part of (Ind1) is the full group `∏_j 𝔖_{j+1}` (IUT III, Remark 3.11.2(ii)). -/
theorem exists_aut_labelPerm {P : Procession C n}
    (hiso : ∀ j t t', Nonempty (P.obj j t ≅ P.obj j t'))
    (π : (j : Fin n) → Equiv.Perm (Fin (j + 1))) : ∃ σ : Aut P, ∀ j, labelPerm σ j = π j := by
  let h : P ⟶ P := (⟨π, fun j t => (hiso j t (π j t)).some⟩ : Hom P P)
  exact ⟨asIso h, fun _ => rfl⟩

/-- **Change of the category of components** (e.g. the mono-analyticization `D ↦ D⊢` of IUT I,
Definition 4.1(iv), which turns the holomorphic processions of Proposition 6.9(i) into the
mono-analytic processions `Prc(D⊢_T)` of Proposition 6.9(ii)): a functor `C ⥤ D` induces a functor
of processions. -/
def map {D : Type u} [Category.{v} D] (F : C ⥤ D) : Procession C n ⥤ Procession D n where
  obj P := ⟨fun j t => F.obj (P.obj j t)⟩
  map f := (⟨Hom.perm f, fun j t => F.mapIso (Hom.iso f j t)⟩ : Hom _ _)
  map_id P := Hom.ext' rfl fun j t => by
    simp only [id_iso, Functor.mapIso_hom, Iso.refl_hom]
    erw [eqToHom_refl, Category.comp_id, F.map_id]
  map_comp f g := Hom.ext' rfl fun j t => by
    simp only [comp_iso, Functor.mapIso_hom, Iso.trans_hom]
    erw [eqToHom_refl, Category.comp_id, F.map_comp]; rfl

end Procession

end Iut.Multiradial
