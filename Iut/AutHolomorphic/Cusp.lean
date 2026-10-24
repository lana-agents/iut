/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Morphism
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Covering.Basic

/-!
# Holomorphic elliptic cuspidalisation ([AbsTopIII] Corollary 2.7 (b), (c))

Model-implicit constructions on an Aut-holomorphic space `(E, A)` (for Corollary 2.7: the
Aut-holomorphic space of a once-punctured elliptic curve, Corollary 2.7 (a)), using only `E^top`
and `A`:

* `IsEllCusp A U q`: an **elliptic cuspidalisation diagram** `E ⊇ U → E` ([AbsTopIII]
  Corollary 2.7 (b), after [AbsTopII] Example 3.2 (i)): `U ⊆ E` is open with finite complement
  (the open immersion `E ← U`), and `q : U → E` is a morphism of Aut-holomorphic spaces which is
  a covering that extends to a covering of the one-point compactification (`cuspExt U q`: `q` on
  `U`, `∞` elsewhere) and is Galois with abelian group `deck q = Gal(U/E)`;
* `cuspTors A`: **the torsion points** — `∞` and the points of `E` outside some such `U`;
* `CuspLim U g y`: the extension of a deck transformation `g` to the one-point compactification
  sends `∞` to `y`; `CuspSum A x y z`: `z` corresponds to `g h ∈ Gal(U/E)` when `x`, `y`
  correspond to `g`, `h` (**the group structure on the torsion points induced by `Gal(U/E)`**);
* `IsRecAdd A μ`: `μ` is a continuous binary operation on the one-point compactification that
  extends the group law of the torsion points (Corollary 2.7 (c)); `recAdd A`: the operation of
  Corollary 2.7 (c) (a chosen such `μ`; it is unique in the model, `Elliptic/CuspModel.lean`).

**Deviations.**

* The condition "`E ← U`, `U → E` are co-holomorphic" ([AbsTopIII] Definition 2.1 (iv),
  via co-orientations `Orn(-)`) is not imposed. The classification of the diagrams of the model
  (`Elliptic/CuspModel.lean`) shows that dropping it does not change the torsion points or their
  group law: an antiholomorphic `q` also has the form `x ↦ a x̄` and the same deck group.
* "which necessarily extends to a covering of the one-point compactification" is imposed as a
  condition (`IsCoveringMap (cuspExt U q)`) instead of being derived.
* Corollary 2.7 (c) asks for "the unique topological group structure" extending the torsion law;
  `IsRecAdd` asks for a continuous binary operation, a weaker condition, which still determines the
  law uniquely in the model.
-/

namespace Iut

namespace AutHol

open Set Topology Filter TopologicalSpace OnePoint

variable {E : Type*} [TopologicalSpace E]

open Classical in
/-- The extension of `q : U → E` to the one-point compactification: `q` on `U`, `∞` elsewhere. -/
noncomputable def cuspExt (U : Opens E) (q : U → E) (x : OnePoint E) : OnePoint E :=
  x.elim ∞ fun y => if h : y ∈ U then ((q ⟨y, h⟩ : E) : OnePoint E) else ∞

@[simp]
theorem cuspExt_infty (U : Opens E) (q : U → E) : cuspExt U q ∞ = ∞ := rfl

open Classical in
theorem cuspExt_of_mem (U : Opens E) (q : U → E) (x : U) :
    cuspExt U q ((x : E) : OnePoint E) = ((q x : E) : OnePoint E) := by
  change (if h : (x : E) ∈ U then ((q ⟨x, h⟩ : E) : OnePoint E) else ∞) = _
  rw [dif_pos x.2]

open Classical in
theorem cuspExt_of_notMem (U : Opens E) (q : U → E) {y : E} (hy : y ∉ U) :
    cuspExt U q (y : OnePoint E) = ∞ := by
  change (if h : y ∈ U then ((q ⟨y, h⟩ : E) : OnePoint E) else ∞) = _
  rw [dif_neg hy]

/-- **The deck transformations** `Gal(U/E)` of `q : U → E`. -/
def deck {U : Opens E} (q : U → E) : Subgroup (U ≃ₜ U) where
  carrier := {g | ∀ x, q (g x) = q x}
  mul_mem' := by
    intro g h hg hh x
    change q (g (h x)) = q x
    rw [hg, hh]
  one_mem' := fun _ => rfl
  inv_mem' := by
    intro g hg x
    change q (g.symm x) = q x
    conv_rhs => rw [← g.apply_symm_apply x]
    rw [hg]

theorem mem_deck {U : Opens E} {q : U → E} {g : U ≃ₜ U} : g ∈ deck q ↔ ∀ x, q (g x) = q x :=
  Iff.rfl

/-- **An elliptic cuspidalisation diagram** `E ⊇ U → E` ([AbsTopIII] Corollary 2.7 (b)):
`U` has finite complement, `q` is a morphism of Aut-holomorphic spaces whose extension to the
one-point compactification is a covering map, and `q` is Galois with abelian group `deck q`. -/
def IsEllCusp (A : AutHolStr E) (U : Opens E) (q : U → E) : Prop :=
  (U : Set E)ᶜ.Finite ∧ IsMorphism (A.restrict U) A q ∧ IsCoveringMap (cuspExt U q) ∧
    (∀ x y : U, q x = q y → ∃ g ∈ deck q, g x = y) ∧
    ∀ g ∈ deck q, ∀ h ∈ deck q, g * h = h * g

/-- The extension of a self-map `g` of `U` to the one-point compactification sends `∞` to `y`:
`g x → y` as `x → ∞` in `U`. -/
def CuspLim (U : Opens E) (g : U → U) (y : OnePoint E) : Prop :=
  Tendsto (fun x : U => ((g x : E) : OnePoint E))
    (comap (fun x : U => ((x : E) : OnePoint E)) (𝓝 ∞)) (𝓝 y)

/-- **The torsion points** ([AbsTopIII] Corollary 2.7 (b)): `∞` (the origin) and the points in the
complement of the image of some elliptic cuspidalisation diagram. -/
def cuspTors (A : AutHolStr E) : Set (OnePoint E) :=
  {y | y = ∞ ∨ ∃ (U : Opens E) (q : U → E), IsEllCusp A U q ∧ ∃ x : E, x ∉ U ∧ y = x}

/-- **The group law on the torsion points induced by `Gal(U/E)`**: `x + y = z` if, for some
diagram, `x`, `y`, `z` are the images of `∞` under deck transformations `g`, `h`, `g h`. -/
def CuspSum (A : AutHolStr E) (x y z : OnePoint E) : Prop :=
  ∃ (U : Opens E) (q : U → E), IsEllCusp A U q ∧ ∃ g ∈ deck q, ∃ h ∈ deck q,
    CuspLim U g x ∧ CuspLim U h y ∧ CuspLim U (g * h) z

/-- `μ` is **a continuous operation extending the group law of the torsion points**
([AbsTopIII] Corollary 2.7 (c)). -/
def IsRecAdd (A : AutHolStr E) (μ : OnePoint E → OnePoint E → OnePoint E) : Prop :=
  Continuous (fun p : OnePoint E × OnePoint E => μ p.1 p.2) ∧
    ∀ x ∈ cuspTors A, ∀ y ∈ cuspTors A, CuspSum A x y (μ x y)

open Classical in
/-- **The group law on the one-point compactification** ([AbsTopIII] Corollary 2.7 (c)): an
operation satisfying `IsRecAdd A` (unique in the model, `recAdd_ellStr`). -/
noncomputable def recAdd (A : AutHolStr E) : OnePoint E → OnePoint E → OnePoint E :=
  if h : ∃ μ, IsRecAdd A μ then h.choose else fun x _ => x

theorem recAdd_eq {A : AutHolStr E} {μ : OnePoint E → OnePoint E → OnePoint E}
    (hμ : IsRecAdd A μ) (huniq : ∀ ν, IsRecAdd A ν → ν = μ) : recAdd A = μ := by
  have h : ∃ μ, IsRecAdd A μ := ⟨μ, hμ⟩
  rw [recAdd, dif_pos h]
  exact huniq _ h.choose_spec

end AutHol

end Iut
