/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.KummerGalois
import LocalClassFieldTheory.Brauer.ContH2

/-!
# `(N, H)`-saturated objects and `F_N(A)` ([FrdII], Definition 2.2)

[FrdII], Definition 2.2(ii): "We shall say that `A` is `(N, H)`-saturated if the following
conditions are satisfied: (a) `A` is `μ_N`-saturated; (b) `A_D` is Galois; (c) the natural
surjective homomorphism `H ↠ H_A` induces isomorphisms on first cohomology modules
`H¹(H_A, μ_N(A)) ≅ H¹(H, μ_N(A))`; `H¹(H_A, ℤ/Nℤ) ≅ H¹(H, ℤ/Nℤ)` and a surjection on second
cohomology modules `H²(H_A, μ_N(A)) ↠ H²(H, μ_N(A))` […]. In this situation, we shall write
`F_N(A) := H²(H_A, μ_N(A))/Ker(H²(H_A, μ_N(A)) ↠ H²(H, μ_N(A)))`."
Definition 2.1(i): "We shall say that `A` is `μ_N`-saturated if the abstract group `μ_N(A)` is
isomorphic to `ℤ/Nℤ`."

Generic part (`Saturation`): for `φ : H →* Q`, `Pull φ M` is a `Q`-module `M` regarded as an
`H`-module through `φ`, and `infl₁ φ`, `infl₂ φ` are the maps `H^i(Q, M) → H^i(H, M)` induced by
`φ` (inflation when `φ` is a quotient map); `ZTriv n` is `ℤ/n` with the trivial action.

`p`-adic part: for the `p`-adic Frobenioid `C^⊢(E)`, `X = (G_E/N, a)` (whose base `G_E/N` is
Galois, condition (b)) and a subgroup `H ⊆ G_E`, `H_A = galHom(H) ⊆ Aut_C(X)` (`subA`; the image
of `H` in `G_A ≅ galHom(G_E)`, [FrdII], Definition 2.2(i)), `H ↠ H_A` (`subHom`),
**`IsSaturated`** (conditions (a), (c)) and **`FN`** `= F_N(X)`.
-/

namespace Iut

namespace Frobenioid

namespace Saturation

/-- A `Q`-module `M`, regarded as an `H`-module through `φ : H →* Q`. -/
@[nolint unusedArguments]
def Pull {H Q : Type*} [Group H] [Group Q] (_φ : H →* Q) (M : Type*) : Type _ := M

section Pull

variable {H Q : Type*} [Group H] [Group Q] (φ : H →* Q) (M : Type*) [CommGroup M]
  [MulDistribMulAction Q M]

instance : CommGroup (Pull φ M) := inferInstanceAs (CommGroup M)

instance [TopologicalSpace M] : TopologicalSpace (Pull φ M) :=
  inferInstanceAs (TopologicalSpace M)

instance [TopologicalSpace M] [IsTopologicalGroup M] : IsTopologicalGroup (Pull φ M) :=
  inferInstanceAs (IsTopologicalGroup M)

instance [TopologicalSpace M] [DiscreteTopology M] : DiscreteTopology (Pull φ M) :=
  inferInstanceAs (DiscreteTopology M)

instance : MulDistribMulAction H (Pull φ M) :=
  MulDistribMulAction.compHom M φ

/-- `M → Pull φ M` (the identity). -/
def toPull : M →* Pull φ M := MonoidHom.id M

variable {φ M} in
lemma toPull_smul (h : H) (m : M) : toPull φ M (φ h • m) = h • toPull φ M m := rfl

end Pull

/-- `ℤ/n` with the discrete topology, regarded as a module with trivial action. -/
def ZTriv (n : ℕ) : Type := Multiplicative (ZMod n)

namespace ZTriv

variable (n : ℕ)

instance : CommGroup (ZTriv n) := inferInstanceAs (CommGroup (Multiplicative (ZMod n)))
instance : TopologicalSpace (ZTriv n) := ⊥
instance : DiscreteTopology (ZTriv n) := ⟨rfl⟩
instance : IsTopologicalGroup (ZTriv n) where
  continuous_mul := continuous_of_discreteTopology
  continuous_inv := continuous_of_discreteTopology

/-- The trivial action. -/
instance {G : Type*} [Monoid G] : MulDistribMulAction G (ZTriv n) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

@[simp] lemma smul_eq {G : Type*} [Monoid G] (g : G) (x : ZTriv n) : g • x = x := rfl

end ZTriv

section Infl

variable {H Q : Type*} [Group H] [TopologicalSpace H] [Group Q] [TopologicalSpace Q]
  (φ : H →* Q) (hφ : Continuous φ)

/-- `H¹(Q, M) → H¹(H, M)` along `φ : H →* Q` (inflation for a quotient map `φ`). -/
noncomputable def infl₁ (M : Type*) [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M]
    [MulDistribMulAction Q M] : ContH1 Q M →* ContH1 H (Pull φ M) :=
  ContH1.map φ hφ (toPull φ M) continuous_id fun _ _ => rfl

/-- `H¹(Q, ℤ/n) → H¹(H, ℤ/n)` along `φ` (trivial actions). -/
noncomputable def infl₁Z (n : ℕ) : ContH1 Q (ZTriv n) →* ContH1 H (ZTriv n) :=
  ContH1.map φ hφ (MonoidHom.id _) continuous_id fun _ _ => rfl

/-- `H²(Q, M) → H²(H, M)` along `φ : H →* Q` (inflation for a quotient map `φ`). -/
noncomputable def infl₂ (M : Type*) [CommGroup M] [MulDistribMulAction Q M] :
    ContH2 Q M →* ContH2 H (Pull φ M) :=
  ContH2.map φ hφ (toPull φ M) fun _ _ => rfl

end Infl

end Saturation

namespace PAdicGalois

open Saturation CategoryTheory

variable {p : ℕ} [hp : Fact p.Prime] {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable {Γ : AddSubgroup ℝ}
variable (N : OpenNormalSubgroup (GK p E)) (a : Γ) (H : Subgroup (GK p E))

local notation "W" => WithDisc (Aut (XN N a))

/-- **`H_A`**: the image of `H` in `Aut_C(X)` under `σ ↦ galAut σ⁻¹` ([FrdII], Definition 2.2(i):
`H ↠ H_A := Im(H) ⊆ G_A`). -/
noncomputable abbrev subA : Subgroup W := H.map (galHom N a)

/-- **`H ↠ H_A`**. -/
noncomputable def subHom : H →* subA N a H := (galHom N a).subgroupMap H

lemma subHom_surjective : Function.Surjective (subHom N a H) :=
  (galHom N a).subgroupMap_surjective H

lemma continuous_subHom : Continuous (subHom N a H) :=
  Continuous.subtype_mk ((continuous_galHom N a).comp continuous_subtype_val) _

/-- `μ_n(X) ⊆ O^×(X)`. -/
noncomputable abbrev muX (n : ℕ) : Subgroup (Model.ouAut (XN N a)) :=
  KummerClass.mu (Model.ouAut (XN N a)) n

/-- **`(n, H)`-saturation** of `X = (G_E/N, a)` ([FrdII], Definition 2.2(ii); condition (b),
"`A_D` is Galois", holds since the base `G_E/N` of `X` is Galois): (a) `μ_n(X) ≅ ℤ/n`;
(c) `H ↠ H_A` induces isomorphisms `H¹(H_A, μ_n(X)) ≅ H¹(H, μ_n(X))`,
`H¹(H_A, ℤ/n) ≅ H¹(H, ℤ/n)` and a surjection `H²(H_A, μ_n(X)) ↠ H²(H, μ_n(X))`. -/
structure IsSaturated (n : ℕ) : Prop where
  /-- (a) `X` is `μ_n`-saturated. -/
  muSat : Nonempty (muX N a n ≃* Multiplicative (ZMod n))
  /-- (c) `H¹(H_A, μ_n(X)) ≅ H¹(H, μ_n(X))`. -/
  h1Mu : Function.Bijective (infl₁ (subHom N a H) (continuous_subHom N a H) (muX N a n))
  /-- (c) `H¹(H_A, ℤ/n) ≅ H¹(H, ℤ/n)`. -/
  h1Z : Function.Bijective (infl₁Z (subHom N a H) (continuous_subHom N a H) n)
  /-- (c) `H²(H_A, μ_n(X)) ↠ H²(H, μ_n(X))`. -/
  h2Mu : Function.Surjective (infl₂ (subHom N a H) (continuous_subHom N a H) (muX N a n))

/-- **`F_N(X) = H²(H_A, μ_N(X)) / Ker(H²(H_A, μ_N(X)) → H²(H, μ_N(X)))`** ([FrdII],
Definition 2.2(ii)). -/
noncomputable abbrev FN (n : ℕ) : Type :=
  ContH2 (subA N a H) (muX N a n) ⧸ (infl₂ (subHom N a H) (continuous_subHom N a H) (muX N a n)).ker

/-- Under (c), `F_N(X) ≅ H²(H, μ_N(X))`. -/
noncomputable def fnEquivH2 (n : ℕ) (hs : IsSaturated N a H n) :
    FN N a H n ≃* ContH2 H (Pull (subHom N a H) (muX N a n)) :=
  QuotientGroup.quotientKerEquivOfSurjective _ hs.h2Mu

end PAdicGalois

end Frobenioid

end Iut
