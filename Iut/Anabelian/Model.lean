/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.Orbicurve
import Iut.Cor312.ThetaData.PointMap

/-!
# The linear-algebraic model of the anabelian interface (taxis #276)

This module constructs the **model orbicurves** behind a term of `Iut.AnabelianGeometry` —
the interface behind the initial Θ-data of IUT I, Definition 3.1 — together with a
residual interface for their fundamental groups. The term itself is assembled in
`Iut.Anabelian.Geometry`.

## The model

IUT I, Definition 3.1 and *The Étale Theta Function*, Definition 2.1 only ever use
orbicurves of the following shape: for an elliptic curve `E/k`, a positive integer `ℓ`
and a subgroup `M ⊆ E(k)[ℓ]`, the once-punctured curve
`X_M := (E/M) ∖ (E[ℓ]/M)` (the cyclic étale cover of `X = E ∖ {0}` obtained from the
quotient `E[ℓ] → E[ℓ]/M`, cf. the multiplication-by-`ℓ` factorization
`E → E/M → E`), and its quotient `X_M/{±1}`. The model orbicurve `Iut.Anabelian.Orbicurve`
records exactly this data: `(E, ℓ, M, ±)`. Then

* the **cusps** of `X_M` are the points of `E[ℓ]/M` (rational cusps: `E(k)[ℓ]/M`), and
  those of `X_M/{±1}` are their `±`-classes;
* a **cover** `(E, ℓ, M, ε) → (E, ℓ', M', ε')` is the map induced by `[n] : E → E` when
  `ℓ = n·ℓ'`, `[n](M) ⊆ M'` and `ε ≤ ε'`;
* **base change** along `k → K` maps `E`, `M` and the cusps along the field embedding;
* the **rank-one quotient** of `(E, ℓ, M, ±)` is `E(k)[ℓ]/M`, and the cusp of an element
  is its class;
* the types `(1, ℓ-tors)` and `(1, ℓ-tors)^±` are the data with `ℓ` prime, `E(k)[ℓ]` of
  order `ℓ²` and `M` of order `ℓ`, without and with the `±`;
* the **cartesian squares** recognized by the model are the `±`-quotient squares
  `X_M → X_{M'}`, `X_M/± → X_{M'}/±` (the only ones used by the Θ-data);
* the type `(1, ℤ/ℓℤ)^±` over a valued field, the theta-root models and the canonical
  graph cusp are defined in `Iut.Anabelian.Local` from minimal Weierstrass models.

## The residual interface

Étale fundamental groups of the model orbicurves, the open immersions attached to
covers, and the notion of `k`-core (with its two stability properties: orbicurves related
by a finite étale cover have the same cores, and cores are compatible with base change)
are the content of `Iut.Anabelian.EtalePi1Theory`, an explicit residual interface (taxis
#276, #7, #10): the model only records the shapes on which these are evaluated. Every
other field of `Iut.AnabelianGeometry` is constructed.
-/

namespace Iut.Anabelian

universe u

open WeierstrassCurve
open scoped Classical

noncomputable section

/-! ## Model orbicurves -/

/-- **A model orbicurve** over `k`: the data `(E, ℓ, M, ±)` of an elliptic curve `E/k`, a
level `ℓ`, a subgroup `M ⊆ E(k)[ℓ]` and a `±`-flag, standing for the orbicurve
`(E/M) ∖ (E[ℓ]/M)` (with `ℓ = 1`, `M = 0`: `X = E ∖ {0}` itself), or its quotient by
`{±1}` when the flag is set. -/
structure Orbicurve (k : Type u) [Field k] : Type u where
  /-- The elliptic curve. -/
  E : WeierstrassCurve k
  /-- `E` is an elliptic curve. -/
  [isElliptic : E.IsElliptic]
  /-- The level `ℓ`. -/
  level : ℕ
  /-- The subgroup `M ⊆ E(k)[ℓ]`. -/
  M : AddSubgroup E.toAffine.Point
  /-- The `±`-flag: whether the orbicurve is the quotient by `{±1}`. -/
  pm : Bool

namespace Orbicurve

attribute [instance] isElliptic

variable {k K L : Type u} [Field k] [Field K] [Field L]

/-- The `ℓ`-torsion of `E(k)`. -/
abbrev torsion (X : Orbicurve k) : AddSubgroup X.E.toAffine.Point :=
  AddSubgroup.torsionBy X.E.toAffine.Point X.level

/-- **The rank-one quotient** `Q = E(k)[ℓ]/M` (IUT I, Definition 3.1(f)); the set of
rational cusps of `(E/M) ∖ (E[ℓ]/M)`. -/
abbrev Q (X : Orbicurve k) : Type u := ↥X.torsion ⧸ X.M.addSubgroupOf X.torsion

/-- The class of a torsion point in the rank-one quotient. -/
abbrev toQ (X : Orbicurve k) : ↥X.torsion →+ X.Q :=
  QuotientAddGroup.mk' (X.M.addSubgroupOf X.torsion)

/-- The relation identifying `q` with `-q` when the `±`-flag is set. -/
def cuspRel (X : Orbicurve k) (a b : X.Q) : Prop := a = b ∨ (X.pm = true ∧ a = -b)

/-- **The cusps** of a model orbicurve: the rank-one quotient, modulo `±` when the flag is
set. -/
def Cusp (X : Orbicurve k) : Type u := Quot X.cuspRel

/-- The cusp of an element of the rank-one quotient (IUT I, Definition 3.1(f)). -/
def cuspOf (X : Orbicurve k) (q : X.Q) : X.Cusp := Quot.mk _ q

lemma cuspOf_neg (X : Orbicurve k) (hpm : X.pm = true) (q : X.Q) :
    X.cuspOf (-q) = X.cuspOf q :=
  Quot.sound (Or.inr ⟨hpm, rfl⟩)

/-- The once-punctured elliptic curve `X = E ∖ {0}`: level `1`, `M = 0`. -/
def oncePunctured (E : WeierstrassCurve k) [E.IsElliptic] : Orbicurve k :=
  ⟨E, 1, ⊥, false⟩

/-- The quotient by `{±1}`. -/
def pmQuotient (X : Orbicurve k) : Orbicurve k := { X with pm := true }

/-- **Base change** along a field embedding: `E`, `M` and the level are transported. -/
noncomputable def baseChange (f : k →+* K) (X : Orbicurve k) : Orbicurve K :=
  ⟨X.E.map f, X.level, X.M.map (pointMap X.E f), X.pm⟩

lemma baseChange_E (f : k →+* K) (X : Orbicurve k) : (X.baseChange f).E = X.E.map f := rfl
lemma baseChange_level (f : k →+* K) (X : Orbicurve k) :
    (X.baseChange f).level = X.level := rfl
lemma baseChange_M (f : k →+* K) (X : Orbicurve k) :
    (X.baseChange f).M = X.M.map (pointMap X.E f) := rfl
lemma baseChange_pm (f : k →+* K) (X : Orbicurve k) : (X.baseChange f).pm = X.pm := rfl

/-- Torsion points map to torsion points. -/
lemma pointMap_mem_torsion (f : k →+* K) (X : Orbicurve k) {P : X.E.toAffine.Point}
    (hP : P ∈ X.torsion) :
    pointMap X.E f P ∈ AddSubgroup.torsionBy (X.E.map f).toAffine.Point X.level := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

/-- The map on torsion induced by base change. -/
def mapTorsion (f : k →+* K) (X : Orbicurve k) :
    ↥X.torsion →+ ↥(X.baseChange f).torsion :=
  ((pointMap X.E f).restrict X.torsion).codRestrict _ fun P => by
    exact X.pointMap_mem_torsion f P.2

@[simp] lemma coe_mapTorsion (f : k →+* K) (X : Orbicurve k) (P : ↥X.torsion) :
    ((X.mapTorsion f P : ↥(X.baseChange f).torsion) : (X.baseChange f).E.toAffine.Point) =
      pointMap X.E f P := rfl

/-- The map on rank-one quotients induced by base change. -/
def mapQ (f : k →+* K) (X : Orbicurve k) : X.Q →+ (X.baseChange f).Q :=
  QuotientAddGroup.map _ _ (X.mapTorsion f) (by
    intro P hP
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, coe_mapTorsion]
    rw [AddSubgroup.mem_addSubgroupOf] at hP
    exact AddSubgroup.mem_map_of_mem _ hP)

lemma mapQ_toQ (f : k →+* K) (X : Orbicurve k) (P : ↥X.torsion) :
    X.mapQ f (X.toQ P) = (X.baseChange f).toQ (X.mapTorsion f P) := rfl

/-- The map on cusps induced by base change. -/
def cuspBaseChange (f : k →+* K) (X : Orbicurve k) :
    X.Cusp → (X.baseChange f).Cusp :=
  Quot.map (X.mapQ f) (by
    rintro a b (h | ⟨hpm, h⟩)
    · exact Or.inl (congrArg _ h)
    · exact Or.inr ⟨hpm, by rw [h, map_neg]⟩)

lemma cuspBaseChange_cuspOf (f : k →+* K) (X : Orbicurve k) (q : X.Q) :
    X.cuspBaseChange f (X.cuspOf q) = (X.baseChange f).cuspOf (X.mapQ f q) := rfl

/-! ### Covers -/

/-- Transport of a subgroup of points along an equality of curves. -/
def transportM {E E' : WeierstrassCurve k} (h : E = E')
    (M : AddSubgroup E.toAffine.Point) : AddSubgroup E'.toAffine.Point := h ▸ M

@[simp] lemma transportM_rfl {E : WeierstrassCurve k} (M : AddSubgroup E.toAffine.Point) :
    transportM rfl M = M := rfl

/-- **A cover** `(E, ℓ, M, ε) → (E, ℓ', M', ε')` of model orbicurves: the map
`(E/M) ∖ (E[ℓ]/M) → (E/M') ∖ (E[ℓ']/M')` induced by `[n]`, where `ℓ = n·ℓ'`, which
exists when `[n](M) ⊆ M'` and the `±`-flags are compatible. -/
structure Cover (X Y : Orbicurve k) : Type u where
  /-- The underlying elliptic curves agree. -/
  E_eq : X.E = Y.E
  /-- The degree `n` of the isogeny `[n]`. -/
  n : ℕ
  /-- `ℓ = n·ℓ'`. -/
  mul : n * Y.level = X.level
  /-- `[n](M) ⊆ M'`. -/
  M_le : ∀ P ∈ X.M, n • P ∈ transportM E_eq.symm Y.M
  /-- The `±`-flags are compatible. -/
  pm_le : X.pm = true → Y.pm = true

/-- Transport along equalities of curves: the composite of two level maps. -/
lemma transport_comp {E E' E'' : WeierstrassCurve k} (h : E = E') (h' : E' = E'')
    (n n' : ℕ) {M : AddSubgroup E.toAffine.Point} {M' : AddSubgroup E'.toAffine.Point}
    {M'' : AddSubgroup E''.toAffine.Point}
    (hM : ∀ P ∈ M, n • P ∈ transportM h.symm M')
    (hM' : ∀ P ∈ M', n' • P ∈ transportM h'.symm M'') :
    ∀ P ∈ M, (n * n') • P ∈ transportM (h.trans h').symm M'' := by
  subst h h'
  intro P hP
  rw [mul_comm, mul_smul]
  exact hM' _ (hM P hP)

/-- Composition of covers. -/
def Cover.comp {X Y Z : Orbicurve k} (f : Cover X Y) (g : Cover Y Z) : Cover X Z where
  E_eq := f.E_eq.trans g.E_eq
  n := f.n * g.n
  mul := by rw [mul_assoc, g.mul, f.mul]
  M_le := transport_comp f.E_eq g.E_eq f.n g.n f.M_le g.M_le
  pm_le := fun h => g.pm_le (f.pm_le h)

/-- Transport along equalities of curves: base change of the level map. -/
lemma transport_baseChange (f : k →+* K) {E E' : WeierstrassCurve k} (h : E = E') (n : ℕ)
    {M : AddSubgroup E.toAffine.Point} {M' : AddSubgroup E'.toAffine.Point}
    (hM : ∀ P ∈ M, n • P ∈ transportM h.symm M') :
    ∀ P ∈ M.map (pointMap E f),
      n • P ∈ transportM (congrArg (WeierstrassCurve.map · f) h).symm (M'.map (pointMap E' f)) := by
  subst h
  rintro _ ⟨P, hP, rfl⟩
  show n • pointMap E f P ∈ M'.map (pointMap E f)
  rw [← map_nsmul]
  exact AddSubgroup.mem_map_of_mem _ (hM P hP)

/-- Base change of a cover. -/
def Cover.baseChange (f : k →+* K) {X Y : Orbicurve k} (c : Cover X Y) :
    Cover (X.baseChange f) (Y.baseChange f) where
  E_eq := congrArg (WeierstrassCurve.map · f) c.E_eq
  n := c.n
  mul := c.mul
  M_le := transport_baseChange f c.E_eq c.n c.M_le
  pm_le := c.pm_le

/-- **The cartesian squares recognized by the model**: the `±`-quotient squares
`A = X_M → B = X_{M'}`, `C = X_M/± → D = X_{M'}/±` (IUT I, Definition 3.1(d), (e): the
diagram `X̲ → X`, `X̲ → C̲`, `X → C`, `C̲ → C` and its base changes). -/
def IsCartesianSquare {A B C D : Orbicurve k} (_f : Cover A B) (g : Cover B D)
    (h : Cover A C) (_i : Cover C D) : Prop :=
  A.pm = false ∧ B.pm = false ∧ C.pm = true ∧ D.pm = true ∧
    A.level = C.level ∧ B.level = D.level ∧
    transportM h.E_eq A.M = C.M ∧ transportM g.E_eq B.M = D.M

/-! ### Orbicurve types -/

/-- **Type `(1, ℓ-tors)`** (*Étale Theta*, Definition 2.1): level a prime `ℓ`, no `±`,
`E(k)[ℓ]` of order `ℓ²` and `M ⊆ E(k)[ℓ]` of order `ℓ`. -/
def IsTypeOneEllTors (ℓ : ℕ) (X : Orbicurve k) : Prop :=
  ℓ.Prime ∧ X.level = ℓ ∧ X.pm = false ∧ X.M ≤ X.torsion ∧ Nat.card X.M = ℓ ∧
    Nat.card X.torsion = ℓ ^ 2

/-- **Type `(1, ℓ-tors)^±`** (*Étale Theta*, Definition 2.1): as `IsTypeOneEllTors`, with
the `±`. -/
def IsTypeOneEllTorsPM (ℓ : ℕ) (X : Orbicurve k) : Prop :=
  ℓ.Prime ∧ X.level = ℓ ∧ X.pm = true ∧ X.M ≤ X.torsion ∧ Nat.card X.M = ℓ ∧
    Nat.card X.torsion = ℓ ^ 2

end Orbicurve

end

/-! ## The residual interface: étale fundamental groups -/

/-- **Étale fundamental groups of the model orbicurves** (residual interface of taxis #276,
#7, #10): the profinite étale fundamental group of each model orbicurve, the open
immersions induced by covers, and the `k`-core relation with its two stability
properties (a finite étale cover of `X` has the same core as `X`; cores are compatible
with base change). -/
structure EtalePi1Theory : Type (u + 1) where
  /-- The arithmetic étale fundamental group (basepoint suppressed). -/
  pi1 : {k : Type u} → [Field k] → Orbicurve k → ProfiniteGrp.{u}
  /-- The homomorphism induced by a cover. -/
  pi1Cover : {k : Type u} → [Field k] → {X Y : Orbicurve k} → Orbicurve.Cover X Y →
    (pi1 X →* pi1 Y)
  /-- The induced homomorphisms are continuous. -/
  pi1Cover_continuous : ∀ {k : Type u} [Field k] {X Y : Orbicurve k}
    (f : Orbicurve.Cover X Y), Continuous (pi1Cover f)
  /-- The induced homomorphisms are open immersions. -/
  pi1Cover_isOpenEmbedding : ∀ {k : Type u} [Field k] {X Y : Orbicurve k}
    (f : Orbicurve.Cover X Y), Topology.IsOpenEmbedding (pi1Cover f)
  /-- `C` is the `k`-core of `X`. -/
  HasCore : {k : Type u} → [Field k] → Orbicurve k → Orbicurve k → Prop
  /-- Orbicurves related by a finite étale cover have the same cores. -/
  hasCore_iff_of_cover : ∀ {k : Type u} [Field k] {X Y C : Orbicurve k},
    Orbicurve.Cover X Y → (HasCore X C ↔ HasCore Y C)
  /-- Cores are compatible with base change. -/
  hasCore_baseChange : ∀ {k K : Type u} [Field k] [Field K] (f : k →+* K)
    {X C : Orbicurve k}, HasCore X C → HasCore (X.baseChange f) (C.baseChange f)

end Iut.Anabelian
