/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.GlobalField
import TateCurvesTheta

/-!
# Initial Θ-data: admissible prime and ℓ-torsion field (taxis #40)

The admissible prime and torsion-field portion of initial Θ-data, IUT I,
Definition 3.1(b)–(c), for the Corollary 3.12 variant statement (taxis #33):

* a prime `ℓ ≥ 5`;
* the mod-`ℓ` representation `ρ : Gal(F̄/F) →* GL₂(𝔽_ℓ)` on the `ℓ`-torsion `E_F[ℓ]`,
  pinned to the genuine Galois action on torsion points of `E(F̄)` by the
  characterizing field `rep_spec` (see below);
* the condition that the image of `ρ` contains `SL₂(𝔽_ℓ)`;
* the finite Galois extension `K/F` cut out by the kernel of `ρ` — **defined** as the
  fixed field of `ker ρ` (`AdmissiblePrimeData.torsionField`), not supplied as
  unrelated field data;
* the condition that `F/F_mod` is Galois of degree prime to `ℓ`
  (`Iut.IsGaloisOfDegreePrimeTo`, from taxis #39);
* coprimality of `ℓ` with the residue characteristics of `V_mod^bad` and with the
  normalized orders of the Tate `q`-parameters of `E_F` at the places of `V(F)^bad`,
  through the `q`-parameter interface of taxis #37
  (`lana-agents/tate-curves-theta`: `TateParameter`, `IsUniformizer`,
  `OrderedTateParameter.PrimeToOrder`).

## Design notes and honesty boundary

* **The representation is data with a characterizing property, not opaque data.** The
  Galois action of `σ : Gal(F̄/F)` on points of `E(F̄)` is the genuine functorial map
  `Iut.galPointMap` (Mathlib's `WeierstrassCurve.Affine.Point.map` along
  `σ : F̄ →ₐ[F] F̄`), which preserves the `ℓ`-torsion (`Iut.galPointMap_torsionBy`,
  proved). The structure carries a chosen `𝔽_ℓ`-basis of `E(F̄)[ℓ]` (as an additive
  equivalence with `Fin 2 → ZMod ℓ`; `ZMod ℓ`-linearity is automatic for additive
  maps) and the field `rep_spec` states that `ρ` is *the matrix of the genuine Galois
  action in this basis*. IUT I fixes the representation up to conjugation; the choice
  of basis is chosen data, and every condition imposed below is conjugation-invariant.
* **Continuity.** The topological condition on `ρ` is recorded as openness of its
  kernel in the Krull topology (`ker_isOpen`), which for the profinite group
  `Gal(F̄/F)` is equivalent to continuity with respect to the discrete topology on the
  finite group `GL₂(𝔽_ℓ)`, and makes `K/F` finite.
* **Tate parameters at bad places.** At each place `w ∈ V(F)^bad` the structure
  carries a Tate parameter `q_w` of the completed local field `F_w`, pinned to `E` by
  the requirement that the `j`-invariant of its Tate curve is the image of `j(E)` in
  `F_w` (`tateJ_eq`); by the uniqueness theorem of taxis #37
  (`TateCurvesTheta.TateParameter.existsUnique_splitMultiplicative_tateParameter`)
  this determines `q_w` uniquely. A uniformizer of `F_w` normalizes its integer order
  (`TateCurvesTheta.IsUniformizer`, `TateParameter.toOrdered`), and the coprimality
  condition of Definition 3.1(c) is `OrderedTateParameter.PrimeToOrder ℓ`, exactly the
  predicate exposed by taxis #37.
* Following IUT I, Remark 3.1.5, **no hypothesis that `K/F_mod` is Galois is added**:
  it is a later consequence, not a field of the definition.
-/

namespace Iut

open NumberField IsDedekindDomain WeierstrassCurve TateCurvesTheta

section GaloisAction

variable (F : Type*) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type*) [Field Fbar] [Algebra F Fbar]

open scoped Classical in
/-- The action of `σ ∈ Gal(F̄/F)` on the points of `E(F̄)`: the functorial map of
nonsingular points along `σ : F̄ →ₐ[F] F̄`. -/
noncomputable def galPointMap (σ : Fbar ≃ₐ[F] Fbar) :
    Affine.Point (Affine.baseChange E Fbar) →+ Affine.Point (Affine.baseChange E Fbar) :=
  Affine.Point.map (W' := E) σ.toAlgHom

omit [NumberField F] [E.IsElliptic] in
open scoped Classical in
/-- The Galois action on points preserves the `n`-torsion. -/
lemma galPointMap_torsionBy (σ : Fbar ≃ₐ[F] Fbar) {n : ℕ}
    {P : Affine.Point (Affine.baseChange E Fbar)}
    (hP : P ∈ AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) n) :
    galPointMap F E Fbar σ P ∈
      AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) n := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

end GaloisAction

section LocalCompletion

variable {F : Type*} [Field F] [NumberField F]

/-- The completed local field `F_w` of `F` at a finite place `w`, with the normed-field
structure induced by the `w`-adic valuation. -/
noncomputable abbrev localCompletion (w : FinitePlace F) : Type _ :=
  w.maximalIdeal.adicCompletion F

end LocalCompletion

section Data

variable (F : Type*) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type*) [Field Fbar] [Algebra F Fbar]
variable (VBad : Set (FinitePlace ↥(fieldOfModuli F E)))

open scoped Classical in
/-- **IUT I, Definition 3.1(b)–(c)**: the admissible prime `ℓ`, the mod-`ℓ`
representation on `E_F[ℓ]` with image containing `SL₂(𝔽_ℓ)`, and the coprimality
conditions, packaged over the global data of taxis #39. The torsion field `K` is
*derived* from the representation: see `AdmissiblePrimeData.torsionField`. -/
structure AdmissiblePrimeData : Type _ where
  /-- The prime `ℓ` of the initial Θ-data. -/
  ℓ : ℕ
  /-- `ℓ` is prime. -/
  ℓ_prime : ℓ.Prime
  /-- `ℓ ≥ 5` (IUT I, Definition 3.1(b)). -/
  five_le : 5 ≤ ℓ
  /-- A chosen `𝔽_ℓ`-basis of the `ℓ`-torsion `E(F̄)[ℓ]`, as an additive equivalence
  with `Fin 2 → ZMod ℓ`. (Additive maps between `ZMod ℓ`-modules are automatically
  `ZMod ℓ`-linear, so no linearity field is needed.) Chosen data: the conditions below
  are invariant under this choice. -/
  torsionBasis :
    AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ℓ ≃+
      (Fin 2 → ZMod ℓ)
  /-- The mod-`ℓ` representation `ρ : Gal(F̄/F) →* GL₂(𝔽_ℓ)`. -/
  rep : (Fbar ≃ₐ[F] Fbar) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod ℓ)
  /-- Characterizing property: `ρ σ` is the matrix, in the chosen basis, of the
  genuine Galois action of `σ` on the `ℓ`-torsion of `E(F̄)`. This pins `rep` to the
  action on `E_F[ℓ]` (IUT I, Definition 3.1(c)). -/
  rep_spec : ∀ (σ : Fbar ≃ₐ[F] Fbar)
    (P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ℓ),
    torsionBasis ⟨galPointMap F E Fbar σ P.1, galPointMap_torsionBy F E Fbar σ P.2⟩ =
      (rep σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).mulVec (torsionBasis P)
  /-- The image of `ρ` contains `SL₂(𝔽_ℓ)` (IUT I, Definition 3.1(c)). -/
  sl_le_range : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ rep.range
  /-- The kernel of `ρ` is open in the Krull topology: `ρ` is continuous for the
  discrete topology on `GL₂(𝔽_ℓ)`, and the extension it cuts out is finite. -/
  ker_isOpen : IsOpen (rep.ker : Set (Fbar ≃ₐ[F] Fbar))
  /-- `F/F_mod` is Galois of degree prime to `ℓ` (IUT I, Definition 3.1(b); predicate
  from taxis #39). -/
  galois_deg_prime : IsGaloisOfDegreePrimeTo F E ℓ
  /-- `ℓ` is prime to the residue characteristics of the places of `V_mod^bad`
  (IUT I, Definition 3.1(c)). -/
  residueChar_coprime : ∀ v ∈ VBad, Nat.Coprime ℓ (residueChar v)
  /-- The Tate parameter `q_w ∈ F_wˣ` of `E` at each bad place `w ∈ V(F)^bad`
  (taxis #37 interface). -/
  tate : ∀ w ∈ badPlacesOver F E VBad, TateParameter (localCompletion w)
  /-- The Tate parameter is *the* parameter of `E` at `w`: the `j`-invariant of its
  Tate curve is the image of `j(E)` in the completion. By taxis #37
  (`existsUnique_splitMultiplicative_tateParameter`) this determines it uniquely. -/
  tateJ_eq : ∀ w (hw : w ∈ badPlacesOver F E VBad),
    (tate w hw).tateJ = FinitePlace.embedding w.maximalIdeal E.j
  /-- A chosen uniformizer of each bad completed local field, normalizing the integer
  order of the Tate parameter (the seam shared with the normalized-valuation
  infrastructure of taxis #4, as documented in taxis #37). -/
  unif : ∀ w ∈ badPlacesOver F E VBad, localCompletion w
  /-- The chosen elements are uniformizers. -/
  unif_isUniformizer : ∀ w (hw : w ∈ badPlacesOver F E VBad),
    IsUniformizer (unif w hw)
  /-- `ℓ` is prime to the normalized orders of the bad-place `q`-parameters
  (IUT I, Definition 3.1(c)), via the `PrimeToOrder` predicate of taxis #37. -/
  q_order_coprime : ∀ w (hw : w ∈ badPlacesOver F E VBad),
    ((tate w hw).toOrdered (unif_isUniformizer w hw)).PrimeToOrder ℓ

namespace AdmissiblePrimeData

variable {F E Fbar VBad} (D : AdmissiblePrimeData F E Fbar VBad)

/-- The **`ℓ`-torsion field** `K`: the finite Galois extension of `F` cut out by the
kernel of the mod-`ℓ` representation, *defined* as the fixed field of `ker ρ` in `F̄`
(IUT I, Definition 3.1(c)). -/
noncomputable def torsionField : IntermediateField F Fbar :=
  IntermediateField.fixedField D.rep.ker

/-- The normalized order of the Tate parameter at a bad place, as a positive integer
(taxis #37: `OrderedTateParameter.orderNat`). -/
noncomputable def qOrder (w : FinitePlace F) (hw : w ∈ badPlacesOver F E VBad) : ℕ :=
  ((D.tate w hw).toOrdered (D.unif_isUniformizer w hw)).orderNat

lemma qOrder_pos (w : FinitePlace F) (hw : w ∈ badPlacesOver F E VBad) :
    0 < D.qOrder w hw :=
  ((D.tate w hw).toOrdered (D.unif_isUniformizer w hw)).orderNat_pos

end AdmissiblePrimeData

end Data

end Iut
