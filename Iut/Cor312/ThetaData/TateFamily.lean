/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.TateStructure
import Iut.Cor312.ThetaData.PlacesOver
import Iut.Cor312.ThetaData.AdmissiblePrime

/-!
# Tate uniformizations of `E` over the completions of the torsion field

The local conditions of IUT I, Definition 3.1(f) at a place `v ∈ V_mod^bad` are conditions
on the Tate uniformization of `E` over the completion `K_v` of the ℓ-torsion field `K`
(*The Étale Theta Function*, §1–2: `E` is a Tate curve over `K_v`, with parameter `q_v`).
`Iut.TateFamily F E F̄ ℓ K V_mod^bad` records these uniformizations as **chosen data**
pinned by the coordinates of the Tate parametrization (`Iut.TateStructure`), one at every
finite place `w` of `K` over `V_mod^bad`, together with their **Galois equivariance**: for
`σ ∈ Gal(K/F)`, the graph line and the canonical generators at `σ·w`, read on `E(K)`, are
the images under `σ` of those at `w`. Both the existence of the uniformizations (Tate's
theorem: the reduction at `w` is split multiplicative since `E[ℓ] ⊆ E(K)`) and their
equivariance (uniqueness of the uniformization and naturality of the Tate parametrization)
are theorems; as the uniformizations are uniquely determined by the pinning, carrying
them as data does not change the mathematical content of the Θ-data.

The objects on `E(K)`:

* `Iut.curveK E K = E ×_F K`, `Iut.galK σ` the action of `σ ∈ Gal(K/F)` on `E(K)`;
* `Iut.emb K w : K → K_w`, `Iut.curveKw E K w = E ×_F K_w`;
* `TateFamily.graphLineAt w`: the graph line at `w` pulled back to `E(K)`;
* `TateFamily.IsCanonicalAt w R`: `R ∈ E(K)` maps to a canonical generator at `w`.
-/

namespace Iut

open WeierstrassCurve NumberField Iut.Anabelian
open scoped Classical

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]

/-- The classical decidable equality on `K`, as used by the model orbicurves. -/
local instance (priority := 1100) instDecidableEqIntermediateField : DecidableEq ↥K :=
  fun a b => Classical.propDecidable (a = b)

/-- The curve `E` over `K`. -/
abbrev curveK : WeierstrassCurve ↥K := E.map (algebraMap F ↥K)

/-- The embedding `K → K_w` into the completion at a finite place. -/
abbrev emb (w : FinitePlace ↥K) : ↥K →+* localCompletion w :=
  FinitePlace.embedding w.maximalIdeal

/-- The curve `E` over `K_w`. -/
abbrev curveKw (w : FinitePlace ↥K) : WeierstrassCurve (localCompletion w) :=
  (curveK E K).map (emb K w)

/-- The action of `σ ∈ Gal(K/F)` on `E(K)`. -/
def galK (σ : ↥K ≃ₐ[F] ↥K) : (curveK E K).toAffine.Point →+ (curveK E K).toAffine.Point :=
  Affine.Point.map (W' := E) (S := F) (σ : ↥K →ₐ[F] ↥K)

variable (ℓ : ℕ) (VBad : Set (FinitePlace ↥(fieldOfModuli F E)))

/-- A finite place of `K` over `V_mod^bad`. -/
def IsBadPlace (w : FinitePlace ↥K) : Prop := ∃ v ∈ VBad, FinitePlace.LiesOver w v

lemma isBadPlace_galPlace {w : FinitePlace ↥K} (hw : IsBadPlace E K VBad w)
    (σ : ↥K ≃ₐ[F] ↥K) : IsBadPlace E K VBad (galPlace σ w) := by
  obtain ⟨v, hv, hwv⟩ := hw
  exact ⟨v, hv, galPlace_liesOver (fun _ => rfl) σ hwv⟩

/-- **The family of Tate uniformizations** of `E` over the completions `K_w` at the finite
places `w` of `K` over `V_mod^bad`, Galois-equivariant on the ℓ-torsion (IUT I, Definition
3.1(f); *The Étale Theta Function*, §1–2). -/
structure TateFamily : Type u where
  /-- The Tate structure of `E` over `K_w` at each bad place `w`. -/
  S : ∀ w : FinitePlace ↥K, IsBadPlace E K VBad w → TateStructure (curveKw E K w)
  /-- **Galois equivariance of the graph line**: the graph line at `σ·w`, on `E(K)`, is
  the image under `σ` of the graph line at `w`. -/
  graphLine_galPlace : ∀ (w : FinitePlace ↥K) (hw : IsBadPlace E K VBad w) (σ : ↥K ≃ₐ[F] ↥K),
    ((S (galPlace σ w) (isBadPlace_galPlace E K VBad hw σ)).graphLine ℓ).comap
        (pointMap (curveK E K) (emb K (galPlace σ w))) =
      (((S w hw).graphLine ℓ).comap (pointMap (curveK E K) (emb K w))).map (galK E K σ)
  /-- **Galois equivariance of the canonical generators.** -/
  isCanonical_galPlace : ∀ (w : FinitePlace ↥K) (hw : IsBadPlace E K VBad w)
    (σ : ↥K ≃ₐ[F] ↥K) (R : (curveK E K).toAffine.Point),
    (S (galPlace σ w) (isBadPlace_galPlace E K VBad hw σ)).IsCanonical ℓ
        (pointMap (curveK E K) (emb K (galPlace σ w)) (galK E K σ R)) ↔
      (S w hw).IsCanonical ℓ (pointMap (curveK E K) (emb K w) R)

namespace TateFamily

variable {E K ℓ VBad} (TF : TateFamily E K ℓ VBad)

/-- The graph line at `w`, pulled back to `E(K)`. -/
def graphLineAt (w : FinitePlace ↥K) (hw : IsBadPlace E K VBad w) :
    AddSubgroup (curveK E K).toAffine.Point :=
  ((TF.S w hw).graphLine ℓ).comap (pointMap (curveK E K) (emb K w))

/-- `R ∈ E(K)` maps to a canonical generator of the graph quotient at `w`. -/
def IsCanonicalAt (w : FinitePlace ↥K) (hw : IsBadPlace E K VBad w)
    (R : (curveK E K).toAffine.Point) : Prop :=
  (TF.S w hw).IsCanonical ℓ (pointMap (curveK E K) (emb K w) R)

end TateFamily

end

end Iut
