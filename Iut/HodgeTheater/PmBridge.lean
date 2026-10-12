/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.Bridge

/-!
# `D-Θ^±-`, `D-Θ^ell`-bridges and `D-Θ^{±ell}`-Hodge theaters: the label layer (IUT I, §6)

The additive combinatorics of IUT I, Definitions 6.1, 6.4, Examples 6.2, 6.3, Propositions
6.5–6.9 (see `README.md`, "Scope decisions"). A `D`-prime-strip is recorded by its `±`-label
classes: `LStrip V = V → PmGroup ℓ` (`LabCusp^±(†D_v)` with its `F_ℓ^±`-group structure, Definition
6.1(iii)); a `+`-full poly-isomorphism `†D_v ≅ ‡D_v` (an `Aut^+`-orbit of isomorphisms) is an
isomorphism of these `F_ℓ^±`-groups (`GrpIso`), whose sign is its sign (Definition 6.1(iii), (iv)).

* **`D-Θ^±`-bridge** `†D_T → †D_≻` (Definition 6.4(i), Example 6.2): an `F_ℓ^±`-group `T`, the
  capsule `†D_T`, the target `†D_≻` and the `+`-full poly-isomorphisms `φ^{Θ^±}_t`.
* **`D-Θ^ell`-bridge** `†D_T → †D^⊚±` (Definition 6.4(ii), Example 6.3): an `F_ℓ^±`-torsor `T`, the
  capsule, the `F_ℓ^±`-torsor `LabCusp^±(†D^⊚±)` (`glob`), the identification `ε` of `T` with it,
  and the maps `θ_{t,v}` induced by `φ^{Θell}_{t,v}` on `±`-labels (in the model, the translation by
  `t`; `θ_zero`: the zero label of `†D_t` goes to `ε(t)`).
* **`D-Θ^{±ell}`-Hodge theater** (Definition 6.4(iii)): both on one capsule (`T` an
  `F_ℓ^±`-group), isomorphic to the model; the condition (`pos`) is that, at every `v`, the sign
  of `θ_{t,v} ∘ φ_{t,v}^{-1}` does not depend on `t` (in the model, `φ = id` and `θ_t` are positive
  translations).

Proved:

* **Proposition 6.6(i)** `DThetaPmBridge.isoEquiv : Iso A B ≃ {±1} × {±1}^V`;
* **Proposition 6.6(ii)** `DThetaEllBridge.isoEquiv : Iso A B ≃ F_ℓ^{⋊±}`;
* **Proposition 6.6(iii)** `DThetaPmEllHT.isoEquiv : Iso A B ≃ {±1}` (and it is the sign of the
  induced isomorphism of `F_ℓ^±`-groups of index sets);
* **Proposition 6.7**: the `D-Θ`-bridge of a `D-Θ^±`-bridge (`DThetaPmBridge.toTheta`, on the index
  set `T^* = |T| \ {0}`), the map `t ↦ |t|` being two-to-one on `T \ {0}` (`card_fiber_toAbs`);
* **Proposition 6.8(i)** `DThetaEllBridge.card_aut_apply`: the `F_ℓ^{⋊±}`-symmetry acts
  transitively on `T` with stabilizers of order two; **6.8(ii)** `card_absT = ℓ±`;
* the models of Examples 6.2, 6.3 (`DThetaPmEllHT.model`).
-/

namespace Iut

namespace HodgeTheater

open PmTorsor

variable {ℓ : ℕ} [OddPrime ℓ]

/-! ### Signs of isomorphisms -/

lemma units_mul_cancel_left (a b : ℤˣ) : a * (a * b) = b := by
  rw [← mul_assoc, Int.units_mul_self, one_mul]

namespace PmTorsor

variable {A B C : PmGroup ℓ}

lemma GrpIso.ext_sign {f g : GrpIso A B} (h : f.1.sign = g.1.sign) : f = g :=
  Subtype.ext (Iso.ext_sign h (f.2.trans g.2.symm))

@[simp] lemma GrpIso.equiv_symm_sign (s : ℤˣ) : ((GrpIso.equiv A B).symm s).1.sign = s := rfl

@[simp] lemma GrpIso.trans_val (f : GrpIso A B) (g : GrpIso B C) :
    (f.trans g).1 = f.1.trans g.1 := rfl

@[simp] lemma GrpIso.symm_val (f : GrpIso A B) : f.symm.1 = f.1.symm := rfl

/-- Two isomorphisms of torsors between `F_ℓ^±`-groups that preserve zero and have the same sign
agree. -/
lemma Iso.eq_of_zero {f g : Iso A B} (hf : f.shift = 0) (hg : g.shift = 0)
    (h : f.sign = g.sign) : f = g :=
  Iso.ext_sign h (hf.trans hg.symm)

@[simp] lemma Iso.symm_apply_eq {A B : PmTorsor ℓ} (f : Iso A B) {a : A.carrier} {b : B.carrier} :
    f.symm b = a ↔ b = f a :=
  f.toEquiv.symm_apply_eq

end PmTorsor

/-- The `±`-label classes of a `D`-prime-strip (label layer, IUT I, Definition 6.1(iii)). -/
abbrev LStrip (ℓ : ℕ) (V : Type) : Type 1 := V → PmGroup ℓ

variable {V : Type}

/-! ### `D-Θ^±`-bridges -/

variable (ℓ V) in
/-- **A `D-Θ^±`-bridge, label layer** (IUT I, Definition 6.4(i)). -/
structure DThetaPmBridge where
  /-- The index set, an `F_ℓ^±`-group. -/
  T : PmGroup ℓ
  /-- The capsule `†D_T`. -/
  cap : T.carrier → LStrip ℓ V
  /-- The target `†D_≻`. -/
  tgt : LStrip ℓ V
  /-- The `+`-full poly-isomorphisms `†φ^{Θ^±}_{t,v}`. -/
  φ : ∀ t v, GrpIso (cap t v) (tgt v)

/-- **An isomorphism of `D-Θ^±`-bridges**: a capsule-`+`-full poly-isomorphism whose map of index
sets is an isomorphism of `F_ℓ^±`-groups, and a `+`-full poly-isomorphism of the targets,
compatible with `φ^{Θ^±}`. -/
structure DThetaPmBridge.Iso (A B : DThetaPmBridge ℓ V) where
  /-- The isomorphism of index sets. -/
  σ : GrpIso A.T B.T
  /-- The components of the capsule-`+`-full poly-isomorphism. -/
  α : ∀ t v, GrpIso (A.cap t v) (B.cap (σ.1 t) v)
  /-- The `+`-full poly-isomorphism of the targets. -/
  β : ∀ v, GrpIso (A.tgt v) (B.tgt v)
  compat : ∀ t v, (α t v).trans (B.φ (σ.1 t) v) = (A.φ t v).trans (β v)

namespace DThetaPmBridge

variable {A B : DThetaPmBridge ℓ V}

lemma Iso.ext {f g : A.Iso B} (hσ : f.σ = g.σ) (hβ : f.β = g.β) : f = g := by
  obtain ⟨σ, α, β, hc⟩ := f
  obtain ⟨σ', α', β', hc'⟩ := g
  simp only at hσ hβ
  subst hσ hβ
  have : α = α' := by
    funext t v
    apply Subtype.ext
    apply PmTorsor.Iso.ext
    intro a
    apply (B.φ (σ.1 t) v).1.toEquiv.injective
    have h1 := congrArg (fun f : GrpIso _ _ => f.1 a) (hc t v)
    have h2 := congrArg (fun f : GrpIso _ _ => f.1 a) (hc' t v)
    exact h1.trans h2.symm
  subst this
  rfl

/-- The isomorphism with signs `s` (on index sets) and `b` (on the targets). -/
def Iso.ofSigns (A B : DThetaPmBridge ℓ V) (s : ℤˣ) (b : V → ℤˣ) : A.Iso B where
  σ := (GrpIso.equiv A.T B.T).symm s
  β v := (GrpIso.equiv _ _).symm (b v)
  α t v := ((A.φ t v).trans ((GrpIso.equiv _ _).symm (b v))).trans
    (B.φ (((GrpIso.equiv A.T B.T).symm s).1 t) v).symm
  compat t v := Subtype.ext (PmTorsor.Iso.ext fun a => by simp)

/-- **IUT I, Proposition 6.6(i)**: the isomorphisms between two `D-Θ^±`-bridges form a torsor
over `{±1} × {±1}^V` (the first factor: the induced isomorphism of `F_ℓ^±`-groups of index sets;
the second: the signs of the `+`-full poly-isomorphisms at the `v ∈ V`). -/
def isoEquiv (A B : DThetaPmBridge ℓ V) : A.Iso B ≃ ℤˣ × (V → ℤˣ) where
  toFun f := (f.σ.1.sign, fun v => (f.β v).1.sign)
  invFun p := Iso.ofSigns A B p.1 p.2
  left_inv _ := Iso.ext (GrpIso.ext_sign rfl) (funext fun _ => GrpIso.ext_sign rfl)
  right_inv _ := rfl

variable (ℓ V) in
/-- **The model `D-Θ^±`-bridge** (Example 6.2(i)): `T = F_ℓ`, all strips tautological, `φ = id`. -/
def model : DThetaPmBridge ℓ V where
  T := PmTorsor.std ℓ
  cap _ _ := PmTorsor.std ℓ
  tgt _ := PmTorsor.std ℓ
  φ _ _ := GrpIso.refl _

/-! #### The `D-Θ`-bridge of a `D-Θ^±`-bridge (IUT I, Proposition 6.7) -/

/-- The class `|t| ∈ |F_ℓ|` of an element of an `F_ℓ^±`-group (well defined: the chart is defined
up to sign). -/
def _root_.Iut.HodgeTheater.PmTorsor.toAbs (T : PmGroup ℓ) (t : T.carrier) : AbsFl ℓ :=
  AbsFl.mk (T.chart t)

lemma _root_.Iut.HodgeTheater.PmTorsor.toAbs_grpIso {T T' : PmGroup ℓ} (σ : GrpIso T T')
    (t : T.carrier) : PmTorsor.toAbs T' (σ.1 t) = PmTorsor.toAbs T t := by
  unfold PmTorsor.toAbs
  rw [σ.1.chart_apply, σ.2, add_zero]
  rcases Int.units_eq_one_or σ.1.sign with h | h <;> rw [h]
  · simp
  · simp

lemma zmod_two_ne_zero : (2 : ZMod ℓ) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd two_pos h2
  have := two_lt ℓ
  omega

lemma ne_neg_self {z : ZMod ℓ} (hz : z ≠ 0) : z ≠ -z := by
  intro h
  have : (2 : ZMod ℓ) * z = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · exact zmod_two_ne_zero h'
  · exact hz h'

/-- **IUT I, Proposition 6.7**: the map `T \ {0} → T^*`, `t ↦ |t|`, maps precisely two indices
to each element of `T^*`. -/
theorem card_fiber_toAbs (T : PmGroup ℓ) (a : {a : AbsFl ℓ // a ≠ 0}) :
    Nat.card {t : T.carrier // PmTorsor.toAbs T t = a} = 2 := by
  obtain ⟨z, hz⟩ := AbsFl.mk_surjective a.1
  have hz0 : z ≠ 0 := fun h => a.2 (by rw [← hz, h]; rfl)
  have e : {t : T.carrier // PmTorsor.toAbs T t = a} ≃ ({z, -z} : Set (ZMod ℓ)) :=
    { toFun t := ⟨T.chart t.1, by
        have h := AbsFl.mk_eq_mk.mp (t.2.trans hz.symm)
        simpa [Set.mem_insert_iff] using h⟩
      invFun w := ⟨T.chart.symm w.1, by
        unfold PmTorsor.toAbs
        rw [Equiv.apply_symm_apply, ← hz]
        rcases w.2 with h | h <;> rw [h]
        simp⟩
      left_inv t := Subtype.ext (by simp)
      right_inv w := Subtype.ext (by simp) }
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_pair (ne_neg_self hz0)]

/-- **IUT I, Proposition 6.7**: the `D-Θ`-bridge `†D_{T^*} → †D_>` associated to a
`D-Θ^±`-bridge: the index set `T^* = |T| \ {0}` (identified, through the `F_ℓ^±`-group structure
of `T`, with the nonzero elements of `|F_ℓ|`), with the labels `T^* ≅ F_ℓ^*`. -/
noncomputable def toTheta (_A : DThetaPmBridge ℓ V) : DThetaBridge ℓ :=
  ⟨{a : AbsFl ℓ // a ≠ 0}, nonzeroAbsEquiv ℓ⟩

/-- The functoriality of Proposition 6.7 (the induced isomorphism of `D-Θ`-bridges is the unique
one, Proposition 4.8(ii)). -/
noncomputable def toThetaIso (_f : A.Iso B) : A.toTheta.Iso B.toTheta := default

/-- The induced isomorphism is the identity of `T^*`: isomorphisms of `F_ℓ^±`-groups act
trivially on `|T|` (`toAbs_grpIso`). -/
theorem toThetaIso_σ (f : A.Iso B) (a : A.toTheta.J) : (toThetaIso f).σ a = a := by
  have := (toThetaIso f).compat a
  exact (nonzeroAbsEquiv ℓ).injective this

/-- **IUT I, Proposition 6.8(ii)**: `|T|` has `ℓ±` elements. -/
theorem card_absT : Nat.card (AbsFl ℓ) = ellPm ℓ := card_absFl ℓ

end DThetaPmBridge

/-! ### `D-Θ^ell`-bridges -/

variable (ℓ V) in
/-- **A `D-Θ^ell`-bridge, label layer** (IUT I, Definition 6.4(ii), Example 6.3). -/
structure DThetaEllBridge where
  /-- The index set, an `F_ℓ^±`-torsor. -/
  T : PmTorsor ℓ
  /-- The capsule `†D_T`. -/
  cap : T.carrier → LStrip ℓ V
  /-- `LabCusp^±(†D^⊚±)`, an `F_ℓ^±`-torsor. -/
  glob : PmTorsor ℓ
  /-- The identification of the index set with the `±`-label classes of `†D^⊚±`. -/
  ε : PmTorsor.Iso T glob
  /-- The maps on `±`-label classes induced by `†φ^{Θell}_{t,v}`. -/
  θ : ∀ t v, PmTorsor.Iso (cap t v) glob
  θ_zero : ∀ t v, θ t v (cap t v).zero = ε t

/-- **An isomorphism of `D-Θ^ell`-bridges**: a capsule-`+`-full poly-isomorphism whose map of
index sets is an isomorphism of `F_ℓ^±`-torsors, and an `Aut_csp`-orbit of isomorphisms
`†D^⊚± ≅ ‡D^⊚±` (acting on `±`-label classes), compatible with `φ^{Θell}`. -/
structure DThetaEllBridge.Iso (A B : DThetaEllBridge ℓ V) where
  /-- The isomorphism of index sets. -/
  σ : PmTorsor.Iso A.T B.T
  /-- The components of the capsule-`+`-full poly-isomorphism. -/
  α : ∀ t v, GrpIso (A.cap t v) (B.cap (σ t) v)
  /-- The action on `LabCusp^±(†D^⊚±)`. -/
  γ : PmTorsor.Iso A.glob B.glob
  compat_ε : ∀ t, B.ε (σ t) = γ (A.ε t)
  compat_θ : ∀ t v, (α t v).1.trans (B.θ (σ t) v) = (A.θ t v).trans γ

namespace DThetaEllBridge

variable {A B : DThetaEllBridge ℓ V}

lemma Iso.ext {f g : A.Iso B} (hσ : f.σ = g.σ) : f = g := by
  obtain ⟨σ, α, γ, hε, hθ⟩ := f
  obtain ⟨σ', α', γ', hε', hθ'⟩ := g
  simp only at hσ
  subst hσ
  have hγ : γ = γ' := PmTorsor.Iso.ext fun x => by
    obtain ⟨t, rfl⟩ := A.ε.toEquiv.surjective x
    exact (hε t).symm.trans (hε' t)
  subst hγ
  have : α = α' := by
    funext t v
    apply Subtype.ext
    apply PmTorsor.Iso.ext
    intro a
    apply (B.θ (σ t) v).toEquiv.injective
    have h1 := congrArg (fun f : PmTorsor.Iso _ _ => f a) (hθ t v)
    have h2 := congrArg (fun f : PmTorsor.Iso _ _ => f a) (hθ' t v)
    exact h1.trans h2.symm
  subst this
  rfl

/-- The action on `LabCusp^±(†D^⊚±)` determined by an isomorphism of index sets. -/
def γOf (σ : PmTorsor.Iso A.T B.T) : PmTorsor.Iso A.glob B.glob := (A.ε.symm.trans σ).trans B.ε

lemma γOf_apply_ε (σ : PmTorsor.Iso A.T B.T) (t : A.T.carrier) : γOf σ (A.ε t) = B.ε (σ t) := by
  simp [γOf]

/-- The components determined by an isomorphism of index sets. -/
def αOf (σ : PmTorsor.Iso A.T B.T) (t : A.T.carrier) (v : V) :
    GrpIso (A.cap t v) (B.cap (σ t) v) :=
  PmTorsor.Iso.toGrpIso (((A.θ t v).trans (γOf σ)).trans (B.θ (σ t) v).symm) (by
    simp only [PmTorsor.Iso.trans_apply, A.θ_zero, γOf_apply_ε, PmTorsor.Iso.symm_apply_eq]
    exact (B.θ_zero _ _).symm)

/-- The isomorphism of `D-Θ^ell`-bridges determined by an isomorphism of index sets. -/
def Iso.ofσ (σ : PmTorsor.Iso A.T B.T) : A.Iso B where
  σ := σ
  α := αOf σ
  γ := γOf σ
  compat_ε t := (γOf_apply_ε σ t).symm
  compat_θ t v := PmTorsor.Iso.ext fun a => by simp [αOf, PmTorsor.Iso.toGrpIso]

/-- **IUT I, Proposition 6.6(ii)**: the isomorphisms between two `D-Θ^ell`-bridges map bijectively
to the isomorphisms of `F_ℓ^±`-torsors of index sets, hence form an `F_ℓ^{⋊±}`-torsor. -/
def isoEquivT (A B : DThetaEllBridge ℓ V) : A.Iso B ≃ PmTorsor.Iso A.T B.T where
  toFun f := f.σ
  invFun σ := Iso.ofσ σ
  left_inv _ := Iso.ext rfl
  right_inv _ := rfl

/-- **IUT I, Proposition 6.6(ii)**. -/
noncomputable def isoEquiv (A B : DThetaEllBridge ℓ V) : A.Iso B ≃ FlSemi ℓ :=
  (isoEquivT A B).trans (PmTorsor.isoEquivSemi _ _)

theorem card_iso (A B : DThetaEllBridge ℓ V) : Nat.card (A.Iso B) = 2 * ℓ := by
  rw [Nat.card_congr (isoEquivT A B), PmTorsor.card_iso]

/-- **IUT I, Proposition 6.8(i)**: the `F_ℓ^{⋊±}`-symmetry of a `D-Θ^ell`-bridge acts on the index
set transitively with stabilizers of order two: for `t, t' ∈ T` exactly two automorphisms carry
`t` to `t'`. -/
theorem card_aut_apply (A : DThetaEllBridge ℓ V) (t t' : A.T.carrier) :
    Nat.card {f : A.Iso A // f.σ t = t'} = 2 := by
  have e : {f : A.Iso A // f.σ t = t'} ≃ ℤˣ :=
    { toFun f := f.1.σ.sign
      invFun s := ⟨Iso.ofσ (PmTorsor.Iso.mk' A.T A.T s
        (A.T.chart t' - sgn ℓ s * A.T.chart t)), by
          apply A.T.chart.injective
          change A.T.chart (A.T.chart.symm _) = _
          simp⟩
      left_inv f := by
        apply Subtype.ext
        apply Iso.ext
        refine PmTorsor.Iso.ext_sign rfl ?_
        have h := congrArg A.T.chart f.2
        rw [f.1.σ.chart_apply] at h
        change A.T.chart t' - sgn ℓ f.1.σ.sign * A.T.chart t = _
        rw [← h]
        ring
      right_inv _ := rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  rfl

variable (ℓ V) in
/-- **The model `D-Θ^ell`-bridge** (Example 6.3(i)): `T = F_ℓ`, `θ_{t,v}` the translation by `t`. -/
def model : DThetaEllBridge ℓ V where
  T := PmTorsor.std ℓ
  cap _ _ := PmTorsor.std ℓ
  glob := PmTorsor.std ℓ
  ε := PmTorsor.Iso.refl _
  θ t _ := PmTorsor.Iso.mk' _ _ 1 t
  θ_zero t _ := by simp [PmTorsor.Iso.mk', PmTorsor.zero, PmTorsor.Iso.refl]

end DThetaEllBridge

/-! ### `D-Θ^{±ell}`-Hodge theaters -/

variable (ℓ V) in
/-- **A `D-Θ^{±ell}`-Hodge theater, label layer** (IUT I, Definition 6.4(iii)). -/
structure DThetaPmEllHT where
  /-- The index set, an `F_ℓ^±`-group. -/
  T : PmGroup ℓ
  /-- The capsule `†D_T`. -/
  cap : T.carrier → LStrip ℓ V
  /-- The target `†D_≻` of the `D-Θ^±`-bridge. -/
  tgt : LStrip ℓ V
  /-- The `D-Θ^±`-bridge. -/
  φ : ∀ t v, GrpIso (cap t v) (tgt v)
  /-- `LabCusp^±(†D^⊚±)`. -/
  glob : PmTorsor ℓ
  /-- The `D-Θ^ell`-bridge: the index set and the `±`-label classes of `†D^⊚±`. -/
  ε : PmTorsor.Iso T glob
  /-- The `D-Θ^ell`-bridge: the maps on `±`-labels. -/
  θ : ∀ t v, PmTorsor.Iso (cap t v) glob
  θ_zero : ∀ t v, θ t v (cap t v).zero = ε t
  /-- The sign of `θ_{t,v} ∘ φ_{t,v}^{-1}`, independent of `t`. -/
  κ : V → ℤˣ
  pos : ∀ t v, ((φ t v).1.symm.trans (θ t v)).sign = κ v

/-- **An isomorphism of `D-Θ^{±ell}`-Hodge theaters**: isomorphisms of the `D-Θ^±`- and
`D-Θ^ell`-bridges inducing the same poly-isomorphism of capsules. -/
structure DThetaPmEllHT.Iso (A B : DThetaPmEllHT ℓ V) where
  /-- The isomorphism of index sets. -/
  σ : GrpIso A.T B.T
  /-- The capsule-`+`-full poly-isomorphism. -/
  α : ∀ t v, GrpIso (A.cap t v) (B.cap (σ.1 t) v)
  /-- The `+`-full poly-isomorphism of the targets. -/
  β : ∀ v, GrpIso (A.tgt v) (B.tgt v)
  /-- The action on `LabCusp^±(†D^⊚±)`. -/
  γ : PmTorsor.Iso A.glob B.glob
  compat_φ : ∀ t v, (α t v).trans (B.φ (σ.1 t) v) = (A.φ t v).trans (β v)
  compat_ε : ∀ t, B.ε (σ.1 t) = γ (A.ε t)
  compat_θ : ∀ t v, (α t v).1.trans (B.θ (σ.1 t) v) = (A.θ t v).trans γ

namespace DThetaPmEllHT

variable {A B : DThetaPmEllHT ℓ V}

/-- The underlying `D-Θ^±`-bridge. -/
def toPm (A : DThetaPmEllHT ℓ V) : DThetaPmBridge ℓ V := ⟨A.T, A.cap, A.tgt, A.φ⟩

/-- The underlying `D-Θ^ell`-bridge (relative to the `F_ℓ^±`-torsor structure of `T`). -/
def toEll (A : DThetaPmEllHT ℓ V) : DThetaEllBridge ℓ V := ⟨A.T, A.cap, A.glob, A.ε, A.θ, A.θ_zero⟩

/-- The underlying isomorphism of `D-Θ^±`-bridges. -/
def Iso.toPm (f : A.Iso B) : A.toPm.Iso B.toPm := ⟨f.σ, f.α, f.β, f.compat_φ⟩

/-- The underlying isomorphism of `D-Θ^ell`-bridges (IUT I, Proposition 6.8(i)). -/
def Iso.toEll (f : A.Iso B) : A.toEll.Iso B.toEll := ⟨f.σ.1, f.α, f.γ, f.compat_ε, f.compat_θ⟩

lemma Iso.ext {f g : A.Iso B} (hσ : f.σ = g.σ) : f = g := by
  have h := DThetaEllBridge.Iso.ext (f := f.toEll) (g := g.toEll) (congrArg Subtype.val hσ)
  obtain ⟨σ, α, β, γ, hφ, hε, hθ⟩ := f
  obtain ⟨σ', α', β', γ', hφ', hε', hθ'⟩ := g
  simp only at hσ
  subst hσ
  simp only [Iso.toEll, DThetaEllBridge.Iso.mk.injEq, heq_eq_eq, true_and] at h
  obtain ⟨rfl, rfl⟩ := h
  have : β = β' := by
    funext v
    apply GrpIso.ext_sign
    have h1 := congrArg (fun f : GrpIso _ _ => f.1.sign) (hφ A.T.zero v)
    have h2 := congrArg (fun f : GrpIso _ _ => f.1.sign) (hφ' A.T.zero v)
    simp only [GrpIso.trans_val, PmTorsor.Iso.trans_sign] at h1 h2
    have := h1.symm.trans h2
    exact mul_right_cancel this
  subst this
  rfl

lemma sign_θ (A : DThetaPmEllHT ℓ V) (t : A.T.carrier) (v : V) :
    (A.θ t v).sign = A.κ v * (A.φ t v).1.sign := by
  have := A.pos t v
  simp only [PmTorsor.Iso.trans_sign, PmTorsor.Iso.symm_sign] at this
  rw [← this, mul_assoc, Int.units_mul_self, mul_one]

/-- The isomorphism of `D-Θ^{±ell}`-Hodge theaters with given isomorphism of index sets. -/
def Iso.ofσ (A B : DThetaPmEllHT ℓ V) (σ : GrpIso A.T B.T) : A.Iso B where
  σ := σ
  α := DThetaEllBridge.αOf (A := A.toEll) (B := B.toEll) σ.1
  β v := ((A.φ A.T.zero v).symm.trans
    (DThetaEllBridge.αOf (A := A.toEll) (B := B.toEll) σ.1 A.T.zero v)).trans
      (B.φ (σ.1 A.T.zero) v)
  γ := DThetaEllBridge.γOf (A := A.toEll) (B := B.toEll) σ.1
  compat_φ t v := by
    apply GrpIso.ext_sign
    simp only [GrpIso.trans_val, GrpIso.symm_val, PmTorsor.Iso.trans_sign,
      PmTorsor.Iso.symm_sign, DThetaEllBridge.αOf, PmTorsor.Iso.toGrpIso]
    change (B.φ (σ.1 t) v).1.sign * ((B.θ (σ.1 t) v).sign *
        ((DThetaEllBridge.γOf (A := A.toEll) (B := B.toEll) σ.1).sign * (A.θ t v).sign)) =
      (B.φ (σ.1 A.T.zero) v).1.sign * ((B.θ (σ.1 A.T.zero) v).sign *
        ((DThetaEllBridge.γOf (A := A.toEll) (B := B.toEll) σ.1).sign *
          (A.θ A.T.zero v).sign) * (A.φ A.T.zero v).1.sign) * (A.φ t v).1.sign
    rw [sign_θ A t v, sign_θ A A.T.zero v, sign_θ B (σ.1 t) v, sign_θ B (σ.1 A.T.zero) v]
    generalize (B.φ (σ.1 t) v).1.sign = a
    generalize (B.φ (σ.1 A.T.zero) v).1.sign = b
    generalize (A.φ t v).1.sign = c
    generalize (A.φ A.T.zero v).1.sign = d
    generalize (DThetaEllBridge.γOf (A := A.toEll) (B := B.toEll) σ.1).sign = g
    rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;>
      rcases Int.units_eq_one_or c with rfl | rfl <;>
      rcases Int.units_eq_one_or d with rfl | rfl <;>
      rcases Int.units_eq_one_or (A.κ v) with h | h <;> rw [h] <;>
      rcases Int.units_eq_one_or (B.κ v) with h' | h' <;> rw [h'] <;>
      rcases Int.units_eq_one_or g with rfl | rfl <;> decide
  compat_ε t := (DThetaEllBridge.γOf_apply_ε (A := A.toEll) (B := B.toEll) σ.1 t).symm
  compat_θ t v := ((DThetaEllBridge.Iso.ofσ (A := A.toEll) (B := B.toEll) σ.1).compat_θ t v)

/-- **IUT I, Proposition 6.6(iii)**: the isomorphisms between two `D-Θ^{±ell}`-Hodge theaters form
a `{±1}`-torsor, mapping bijectively to the isomorphisms of `F_ℓ^±`-groups of index sets. -/
def isoEquiv (A B : DThetaPmEllHT ℓ V) : A.Iso B ≃ ℤˣ where
  toFun f := f.σ.1.sign
  invFun s := Iso.ofσ A B ((GrpIso.equiv A.T B.T).symm s)
  left_inv _ := Iso.ext (GrpIso.ext_sign rfl)
  right_inv _ := rfl

theorem card_iso (A B : DThetaPmEllHT ℓ V) : Nat.card (A.Iso B) = 2 := by
  rw [Nat.card_congr (isoEquiv A B), Nat.card_eq_fintype_card]
  rfl

variable (ℓ V) in
/-- **The model `D-Θ^{±ell}`-Hodge theater** (Examples 6.2, 6.3). -/
def model : DThetaPmEllHT ℓ V where
  T := PmTorsor.std ℓ
  cap _ _ := PmTorsor.std ℓ
  tgt _ := PmTorsor.std ℓ
  φ _ _ := GrpIso.refl _
  glob := PmTorsor.std ℓ
  ε := PmTorsor.Iso.refl _
  θ t _ := PmTorsor.Iso.mk' _ _ 1 t
  θ_zero t _ := by simp [PmTorsor.Iso.mk', PmTorsor.zero, PmTorsor.Iso.refl]
  κ _ := 1
  pos _ _ := by simp [GrpIso.refl, PmTorsor.Iso.mk', PmTorsor.Iso.refl]

end DThetaPmEllHT

end HodgeTheater

end Iut
