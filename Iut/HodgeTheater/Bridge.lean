/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.Procession

/-!
# `D-NF-`, `D-Θ`-bridges and `D-ΘNF`-Hodge theaters: the label layer (IUT I, §4)

The multiplicative combinatorics of IUT I, Definition 4.6, Examples 4.3, 4.4, Propositions 4.7–4.9,
4.11 (see `README.md`, "Scope decisions"): a bridge is recorded by its capsule index set and the
labels determined by its poly-morphisms; the prime-strips themselves are attached in
`HodgeTheater.lean`, and full poly-isomorphisms (which are unique) are not recorded.

* **`D-Θ`-bridge** `†D_J → †D_>` (Definition 4.6(ii); Example 4.4): the index set `J` with the
  bijection `†χ : J ≃ F_ℓ^*` of Proposition 4.7(i) (the label of the evaluation sections of
  `φ^Θ_j`). An isomorphism is a capsule-full poly-isomorphism (a bijection of index sets) compatible
  with the labels.
* **`D-NF`-bridge** `†D_J → †D^⊚` (Definition 4.6(i); Example 4.3): `J`, the `F_ℓ^*`-torsor
  `LabCusp(†D^⊚)` and the bijection `J ≃ LabCusp(†D^⊚)` given by the poly-morphisms `φ^NF_j`. An
  isomorphism is a bijection of index sets and an isomorphism of `F_ℓ^*`-torsors (the action of an
  `Aut_ε`-orbit of isomorphisms `†D^⊚ ≅ ‡D^⊚` on label classes of cusps), compatible.
* **`D-ΘNF`-Hodge theater** (Definition 4.6(iii)): the two bridges on one capsule, such that the
  whole is isomorphic to the model (`IsHT`: the labels `χ` form an isomorphism of `F_ℓ^*`-torsors).

Proved:

* **Proposition 4.8(i)** `DNFBridge.isoEquiv : Iso A B ≃ F_ℓ^*`;
* **Proposition 4.8(ii)** `DThetaBridge.Iso` and `DThetaNFHT.Iso` are `Unique`;
* **Proposition 4.8(iii)** `DThetaNFHT.glueEquiv`: the gluings of a `D-NF`- and a `D-Θ`-bridge form
  an `F_ℓ^*`-torsor;
* **Proposition 4.9(i)** `DNFBridge.existsUnique_aut`: `F_ℓ^* = Aut(D-NF-bridge)` acts simply
  transitively on `J`; **4.9(ii)** `DThetaNFHT.card_J = ℓ*` (forgetting the labels, an index has
  `ℓ*` possible labels);
* **Proposition 4.11(i)** `DThetaBridge.prc`: the procession `Prc(†D_J)` of a `D-Θ`-bridge, with
  `prc_capsule_card` and its functoriality `prc_map`.
-/

namespace Iut

namespace HodgeTheater

variable (ℓ : ℕ) [OddPrime ℓ]

/-! ### `D-Θ`-bridges -/

/-- **A `D-Θ`-bridge, label layer** (IUT I, Definition 4.6(ii), Proposition 4.7(i)). -/
structure DThetaBridge where
  /-- The index set of the capsule `†D_J`. -/
  J : Type
  /-- The labels `†χ : J ≃ F_ℓ^*` determined by `†φ^Θ_*`. -/
  χ : J ≃ FlStar ℓ

variable {ℓ}

/-- **An isomorphism of `D-Θ`-bridges**: a capsule-full poly-isomorphism (a bijection of index
sets, each component the full poly-isomorphism) and the full poly-isomorphism of the targets,
compatible with `φ^Θ_*`, i.e. with the labels. -/
structure DThetaBridge.Iso (A B : DThetaBridge ℓ) where
  /-- The bijection of index sets. -/
  σ : A.J ≃ B.J
  compat : ∀ j, B.χ (σ j) = A.χ j

namespace DThetaBridge

variable {A B C : DThetaBridge ℓ}

lemma Iso.ext {f g : A.Iso B} (h : f.σ = g.σ) : f = g := by
  cases f; cases g; cases h; rfl

/-- The isomorphism (`σ = B.χ⁻¹ ∘ A.χ`). -/
def Iso.mk' (A B : DThetaBridge ℓ) : A.Iso B := ⟨A.χ.trans B.χ.symm, fun j => by simp⟩

/-- **IUT I, Proposition 4.8(ii)**: the set of isomorphisms between two `D-Θ`-bridges has
cardinality one. -/
instance (A B : DThetaBridge ℓ) : Unique (A.Iso B) where
  default := Iso.mk' A B
  uniq f := Iso.ext (Equiv.ext fun j => B.χ.injective (by simp [Iso.mk', f.compat]))

/-- The composite. -/
def Iso.trans (f : A.Iso B) (g : B.Iso C) : A.Iso C :=
  ⟨f.σ.trans g.σ, fun j => by simp [g.compat, f.compat]⟩

/-- **The model `D-Θ`-bridge** `D_* → D_>` (Example 4.4(iv)): `J = F_ℓ^*`, `χ = id`. -/
def model (ℓ : ℕ) [OddPrime ℓ] : DThetaBridge ℓ := ⟨FlStar ℓ, Equiv.refl _⟩

/-- `|J| = ℓ*`. -/
theorem card_J (A : DThetaBridge ℓ) : Nat.card A.J = ellStar ℓ := by
  rw [Nat.card_congr A.χ, card_flStar]

open scoped Classical in
/-- **The procession `Prc(†D_J)` of a `D-Θ`-bridge** (IUT I, Proposition 4.11(i)): the
subcapsules of `†D_J` corresponding to `S^*_1 ⊆ ⋯ ⊆ S^*_{ℓ*}` via `†χ`. -/
noncomputable def prc (A : DThetaBridge ℓ) : Procession A.J where
  length := ellStar ℓ
  capsule i := ⟨(sStar ℓ (i + 1)).map A.χ.symm.toEmbedding⟩
  labels_mono _ _ h := Finset.map_subset_map.mpr (sStar_mono ℓ (Nat.add_le_add_right h 1))

/-- The `n`-th capsule of the procession is an `n`-capsule (`n = i + 1`). -/
theorem prc_capsule_card (A : DThetaBridge ℓ) (i : Fin A.prc.length) :
    (A.prc.capsule i).card = i + 1 := by
  change (Finset.map _ _).card = _
  rw [Finset.card_map]
  exact card_sStar ℓ (by have := i.2; change (i : ℕ) < ellStar ℓ at this; omega)

/-- **Functoriality of `Prc`** (IUT I, Proposition 4.11(i)): an isomorphism of `D-Θ`-bridges maps
the capsules of `Prc(†D_J)` to those of `Prc(‡D_J)`. -/
theorem prc_map (f : A.Iso B) (i : Fin (ellStar ℓ)) :
    (A.prc.capsule i).labels.map f.σ.toEmbedding = (B.prc.capsule i).labels := by
  classical
  change ((sStar ℓ (i + 1)).map A.χ.symm.toEmbedding).map f.σ.toEmbedding =
    (sStar ℓ (i + 1)).map B.χ.symm.toEmbedding
  rw [Finset.map_map]
  congr 1
  ext x
  change f.σ (A.χ.symm x) = B.χ.symm x
  rw [Equiv.eq_symm_apply, f.compat, Equiv.apply_symm_apply]

end DThetaBridge

/-! ### `D-NF`-bridges -/

variable (ℓ) in
/-- **A `D-NF`-bridge, label layer** (IUT I, Definition 4.6(i), Example 4.3). -/
structure DNFBridge where
  /-- The index set of the capsule `†D_J`. -/
  J : Type
  /-- The `F_ℓ^*`-torsor `LabCusp(†D^⊚)`. -/
  lab : StarTorsor ℓ
  /-- The label classes determined by the poly-morphisms `†φ^NF_j : †D_j → †D^⊚`. -/
  ν : J ≃ lab.carrier

/-- **An isomorphism of `D-NF`-bridges**: a capsule-full poly-isomorphism and an
`Aut_ε`-orbit of isomorphisms `†D^⊚ ≅ ‡D^⊚` (acting on label classes of cusps by an isomorphism
of `F_ℓ^*`-torsors), compatible with `φ^NF_*`. -/
structure DNFBridge.Iso (A B : DNFBridge ℓ) where
  /-- The bijection of index sets. -/
  σ : A.J ≃ B.J
  /-- The induced isomorphism of label classes of cusps. -/
  γ : StarTorsor.Iso A.lab B.lab
  compat : ∀ j, B.ν (σ j) = γ (A.ν j)

namespace DNFBridge

variable {A B : DNFBridge ℓ}

lemma Iso.ext {f g : A.Iso B} (hσ : f.σ = g.σ) (hγ : f.γ = g.γ) : f = g := by
  cases f; cases g; cases hσ; cases hγ; rfl

/-- The isomorphism with given action on label classes. -/
def Iso.ofγ (γ : StarTorsor.Iso A.lab B.lab) : A.Iso B :=
  ⟨A.ν.trans (γ.toEquiv.trans B.ν.symm), γ, fun j => by simp⟩

lemma Iso.eq_ofγ (f : A.Iso B) : f = Iso.ofγ f.γ :=
  Iso.ext (Equiv.ext fun j => B.ν.injective (by rw [f.compat]; simp [Iso.ofγ])) rfl

/-- **IUT I, Proposition 4.8(i)**: the isomorphisms between two `D-NF`-bridges form an
`F_ℓ^*`-torsor. -/
def isoEquiv (A B : DNFBridge ℓ) : A.Iso B ≃ FlStar ℓ :=
  { toFun f := f.γ.mult
    invFun g := Iso.ofγ (StarTorsor.Iso.mk' A.lab B.lab g)
    left_inv f := by
      dsimp only
      rw [show StarTorsor.Iso.mk' A.lab B.lab f.γ.mult = f.γ from StarTorsor.Iso.ext_mult rfl]
      exact (Iso.eq_ofγ f).symm
    right_inv _ := rfl }

theorem card_iso (A B : DNFBridge ℓ) : Nat.card (A.Iso B) = ellStar ℓ := by
  rw [Nat.card_congr (isoEquiv A B), card_flStar]

variable (ℓ) in
/-- **The model `D-NF`-bridge** `D_* → D^⊚` (Example 4.3(iv)). -/
def model : DNFBridge ℓ := ⟨FlStar ℓ, StarTorsor.std ℓ, Equiv.refl _⟩

/-- The automorphism of a `D-NF`-bridge acting on label classes by `γ`. -/
def aut (A : DNFBridge ℓ) (γ : StarTorsor.Iso A.lab A.lab) : A.Iso A := Iso.ofγ γ

/-- **IUT I, Proposition 4.9(i)**: the `F_ℓ^*`-symmetry of a `D-NF`-bridge acts simply
transitively on the index set `J`. -/
theorem existsUnique_aut (A : DNFBridge ℓ) (j j' : A.J) : ∃! f : A.Iso A, f.σ j = j' := by
  refine ⟨Iso.ofγ (StarTorsor.Iso.ofPoints _ _ (A.ν j) (A.ν j')), ?_, fun f hf => ?_⟩
  · change A.ν.symm _ = j'
    rw [StarTorsor.Iso.ofPoints_apply, Equiv.symm_apply_apply]
  · have hγ : f.γ = StarTorsor.Iso.ofPoints _ _ (A.ν j) (A.ν j') := by
      apply StarTorsor.Iso.eq_of_apply_eq (A.ν j)
      rw [StarTorsor.Iso.ofPoints_apply, ← f.compat, hf]
    refine Iso.ext (Equiv.ext fun i => A.ν.injective ?_) hγ
    rw [f.compat, hγ]
    simp [Iso.ofγ]

theorem card_J (A : DNFBridge ℓ) : Nat.card A.J = ellStar ℓ := by
  rw [Nat.card_congr (A.ν.trans A.lab.chart), card_flStar]

end DNFBridge

/-! ### `D-ΘNF`-Hodge theaters -/

variable (ℓ) in
/-- **A `D-ΘNF`-Hodge theater, label layer** (IUT I, Definition 4.6(iii)): a `D-NF`-bridge and a
`D-Θ`-bridge on the same capsule, isomorphic to the model: the labels `χ` and the label classes
`ν` differ by an isomorphism of `F_ℓ^*`-torsors `F_ℓ^* ≅ LabCusp(†D^⊚)` (`γ₀`). -/
structure DThetaNFHT where
  /-- The index set of the capsule. -/
  J : Type
  /-- `LabCusp(†D^⊚)`. -/
  lab : StarTorsor ℓ
  /-- The `D-NF`-bridge. -/
  ν : J ≃ lab.carrier
  /-- The `D-Θ`-bridge. -/
  χ : J ≃ FlStar ℓ
  /-- The isomorphism with the model. -/
  γ₀ : StarTorsor.Iso (StarTorsor.std ℓ) lab
  γ₀_apply : ∀ x, γ₀ x = ν (χ.symm x)

/-- **An isomorphism of `D-ΘNF`-Hodge theaters**: isomorphisms of the `D-NF`- and `D-Θ`-bridges
inducing the same bijection of index sets. -/
structure DThetaNFHT.Iso (A B : DThetaNFHT ℓ) where
  /-- The bijection of index sets. -/
  σ : A.J ≃ B.J
  /-- The action on label classes of cusps. -/
  γ : StarTorsor.Iso A.lab B.lab
  compat_ν : ∀ j, B.ν (σ j) = γ (A.ν j)
  compat_χ : ∀ j, B.χ (σ j) = A.χ j

namespace DThetaNFHT

variable {A B : DThetaNFHT ℓ}

/-- The underlying `D-NF`-bridge (IUT I, Proposition 4.9(i)). -/
def toNF (A : DThetaNFHT ℓ) : DNFBridge ℓ := ⟨A.J, A.lab, A.ν⟩

/-- The underlying `D-Θ`-bridge. -/
def toTheta (A : DThetaNFHT ℓ) : DThetaBridge ℓ := ⟨A.J, A.χ⟩

lemma Iso.ext {f g : A.Iso B} (hσ : f.σ = g.σ) (hγ : f.γ = g.γ) : f = g := by
  cases f; cases g; cases hσ; cases hγ; rfl

/-- The isomorphism. -/
def Iso.mk' (A B : DThetaNFHT ℓ) : A.Iso B where
  σ := A.χ.trans B.χ.symm
  γ := A.γ₀.symm.trans B.γ₀
  compat_ν j := by
    change B.ν (B.χ.symm (A.χ j)) = B.γ₀ (A.γ₀.symm (A.ν j))
    rw [B.γ₀_apply]
    congr 2
    apply (StarTorsor.std ℓ).chart.injective
    change _ = A.γ₀.toEquiv.symm (A.ν j)
    rw [Equiv.eq_symm_apply]
    exact (A.γ₀_apply _).trans (by simp [StarTorsor.std])
  compat_χ j := by simp

/-- **IUT I, Proposition 4.8(ii)**: the set of isomorphisms between two `D-ΘNF`-Hodge theaters
has cardinality one. -/
instance (A B : DThetaNFHT ℓ) : Unique (A.Iso B) where
  default := Iso.mk' A B
  uniq f := by
    have hσ : f.σ = (Iso.mk' A B).σ :=
      Equiv.ext fun j => B.χ.injective (by simp [Iso.mk', f.compat_χ])
    refine Iso.ext hσ (StarTorsor.Iso.ext fun x => ?_)
    obtain ⟨j, rfl⟩ := A.ν.surjective x
    rw [← f.compat_ν, ← (Iso.mk' A B).compat_ν, hσ]

/-- **The model `D-ΘNF`-Hodge theater** (Examples 4.3, 4.4). -/
def model (ℓ : ℕ) [OddPrime ℓ] : DThetaNFHT ℓ where
  J := FlStar ℓ
  lab := StarTorsor.std ℓ
  ν := Equiv.refl _
  χ := Equiv.refl _
  γ₀ := StarTorsor.Iso.refl _
  γ₀_apply _ := rfl

/-- **IUT I, Proposition 4.9(ii)**: the underlying capsule is an `ℓ*`-capsule (so, forgetting the
labels, an index has `ℓ*` possible labels). -/
theorem card_J (A : DThetaNFHT ℓ) : Nat.card A.J = ellStar ℓ := A.toTheta.card_J

/-! #### Gluing (IUT I, Proposition 4.8(iii)) -/

/-- The data obtained by gluing a `D-NF`-bridge and a `D-Θ`-bridge along a bijection `σ` of their
index sets, together with the condition that it is a `D-ΘNF`-Hodge theater. -/
def Glue (N : DNFBridge ℓ) (T : DThetaBridge ℓ) : Type :=
  {σ : N.J ≃ T.J // ∃ γ : StarTorsor.Iso (StarTorsor.std ℓ) N.lab,
    ∀ x, γ x = N.ν ((σ.trans T.χ).symm x)}

/-- The `D-ΘNF`-Hodge theater of a gluing. -/
noncomputable def ofGlue {N : DNFBridge ℓ} {T : DThetaBridge ℓ} (g : Glue N T) : DThetaNFHT ℓ where
  J := N.J
  lab := N.lab
  ν := N.ν
  χ := g.1.trans T.χ
  γ₀ := g.2.choose
  γ₀_apply := g.2.choose_spec

lemma glueOfγ_spec {N : DNFBridge ℓ} {T : DThetaBridge ℓ}
    (γ : StarTorsor.Iso (StarTorsor.std ℓ) N.lab) (x : FlStar ℓ) :
    γ x = N.ν (((N.ν.trans (γ.symm.toEquiv.trans T.χ.symm)).trans T.χ).symm x) := by
  simp [StarTorsor.Iso.symm]

/-- The gluing determined by an isomorphism `F_ℓ^* ≅ LabCusp(†D^⊚)`. -/
def glueOfγ {N : DNFBridge ℓ} {T : DThetaBridge ℓ}
    (γ : StarTorsor.Iso (StarTorsor.std ℓ) N.lab) : Glue N T :=
  ⟨N.ν.trans (γ.symm.toEquiv.trans T.χ.symm), γ, glueOfγ_spec γ⟩

lemma glue_γ_unique {N : DNFBridge ℓ} {T : DThetaBridge ℓ} (σ : N.J ≃ T.J)
    {γ γ' : StarTorsor.Iso (StarTorsor.std ℓ) N.lab}
    (h : ∀ x, γ x = N.ν ((σ.trans T.χ).symm x)) (h' : ∀ x, γ' x = N.ν ((σ.trans T.χ).symm x)) :
    γ = γ' :=
  StarTorsor.Iso.ext fun x => (h x).trans (h' x).symm

/-- **IUT I, Proposition 4.8(iii)**: the gluings of a `D-NF`-bridge and a `D-Θ`-bridge into a
`D-ΘNF`-Hodge theater form an `F_ℓ^*`-torsor. -/
noncomputable def glueEquiv (N : DNFBridge ℓ) (T : DThetaBridge ℓ) : Glue N T ≃ FlStar ℓ :=
  (show Glue N T ≃ StarTorsor.Iso (StarTorsor.std ℓ) N.lab from
    { toFun g := g.2.choose
      invFun γ := glueOfγ γ
      left_inv g := by
        apply Subtype.ext
        apply Equiv.ext
        intro j
        apply T.χ.injective
        change T.χ (T.χ.symm (g.2.choose.symm (N.ν j))) = T.χ (g.1 j)
        rw [Equiv.apply_symm_apply]
        apply g.2.choose.toEquiv.injective
        rw [StarTorsor.Iso.apply_symm_apply, g.2.choose_spec]
        simp
      right_inv γ := glue_γ_unique _ (glueOfγ (T := T) γ).2.choose_spec (glueOfγ_spec γ) }).trans
    (StarTorsor.isoEquiv _ _)

end DThetaNFHT

end HodgeTheater

end Iut
