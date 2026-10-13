/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.GalKummer
import Iut.HodgeTheater.StripLift

/-!
# Kummer data with the Galois automorphisms read off the `D^⊢`-prime-strips

In `GalKummer.lean` the Kummer identification of the container of a vertex of the
log-theta-lattice is Galois-induced: each factor scaling is the identification
`compGalLogEquiv φ` induced by **some** topological automorphism `φ` of `G_v = Gal(K̄_v/K_v)`,
and `φ` is part of the data (an existential). Here the automorphisms are **read off the
`D^⊢`-prime-strips** (IUT I, Corollary 5.3(ii) in the model, `Iut/HodgeTheater/StripLift.lean`):
every vertex carries a rigidified `D^⊢`-prime-strip, an isomorphism to a coric rigidified
`D^⊢`-prime-strip, and the Galois automorphism at `v` is
`φ_v = RigidDGalStrip.gal (link a) v = κ^coric_v ∘ (link a)_v ∘ (κ^a_v)⁻¹`. This isomorphism of
`D^⊢`-prime-strips lifts to an isomorphism of the reconstructed `F^⊢`-prime-strips whose
Frobenioid portion is induced by `φ_v` (`StripKummer.liftIso`, `forget_liftIso`); it acts on the
units `𝒪_vˣ` of the Frobenioid by the P17 automorphism `compGalUnits φ_v`
(`galMult_coe_units`), whose transport along the logarithm is the Kummer identification
`compGalLogEquiv φ_v` of the factor (`compGalLogEquiv_eq_units`).

## Main results

* `factorGal`: the strip automorphism at the place `v_j` of a factor of a tensor component
  (transport along `tuple_finite`), `factorGal_refl`;
* `StripScaling φ s`: every factor scaling of `s` is the identification induced by the strip
  automorphism `φ_{v_j}`; **`StripScaling.galInduced`** (hence `.anabelian`, `.unitInduced`,
  `.shift_eq_zero`); `stripScaling_one`;
* `StripKummer L`: Kummer data whose Galois automorphisms are read off the strips;
  **`toGalKummer`**, `toLatticeKummer`, `distortion_eq_zero`, **`xi_iff_ss`**,
  `kum_ne_qScale_zpow`, `liftIso`, `forget_liftIso`, `liftIso_functor`; `StripKummer.trivial`
  (tautological strips, identity isomorphisms; `trivial_toLatticeKummer`);
  `classicalABC_of_thm311_strip`, `classicalABC_of_xi_strip`;
* `galMult_coe_units`, `compGalLogEquiv_eq_units`: the lifted Frobenioid equivalence acts on
  `𝒪_vˣ` by `compGalUnits φ_v`, and `compGalLogEquiv φ_v` is its transport along `log`.

## What remains an input

* The rigidified `D^⊢`-prime-strips of the vertices and the coric strip, with the isomorphisms
  `link a`, are data: the Hodge theaters of the model (`ThetaPmEllNFHT`) carry `F`-prime-strips
  recorded by categories up to equivalence, without bases `G_v`, so the strips are not extracted
  from the theaters of a lattice; the rigidifications `κ_v` (the Kummer structures) are data.
* The equation "the factor scaling **is** `compGalLogEquiv φ_v`" (the identification is a
  scaling, the form of the model's Kummer identifications) remains an input, as in
  `GalKummer.lean`.
* Only `v ∈ V^non`; P19's alien `x ↦ −x` (inversion of the units) is `F^{⊢×μ}`-data, not
  `D^⊢`-data, and is not of the form `StripScaling` (`AnabelianKummer.alt` is not restated).
-/

namespace Iut

namespace LogLink

open LocalConstruct NumberField Wall ThetaLink HodgeTheater PadicField Reconstruction
open Frobenioid Frobenioid.PAdic CategoryTheory

noncomputable section

/-! ### The lifted Frobenioid equivalence on the units -/

section Units

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] {w : FinitePlace K}
  (hw : residueChar w = p)

/-- **The lift acts on `𝒪_wˣ` by P17's `compGalUnits`**: the automorphism `galMult φ` of
`K_wˣ` (by which `galFrob φ` acts on rational functions, `galFrob_map_u`) restricts on the units
to `compGalUnits φ`. -/
theorem galMult_coe_units (φ : CompGal w ≃ₜ* CompGal w) (u : CompUnits hw) :
    galMult hw φ (u : (completionAt K w)ˣ) = ((compGalUnits hw φ u : CompUnits hw) :
      (completionAt K w)ˣ) :=
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  haveI : Algebra.IsAlgebraic ℚ_[p] (AlgebraicClosure (completionAt K w)) :=
    Algebra.IsAlgebraic.trans ℚ_[p] (completionAt K w) _
  (coe_galUnitsEquiv φ u).symm

/-- **The Galois-induced identification is the log-transport of the action of the lifted
Frobenioid equivalence on the units.** -/
theorem compGalLogEquiv_eq_units (φ : CompGal w ≃ₜ* CompGal w) :
    compGalLogEquiv hw φ = compUnitLogEquiv hw (compGalUnits hw φ) :=
  rfl

end Units

/-! ### The strip automorphisms at the factors -/

variable {D : InitialThetaData.{0}}

/-- The equation `σ(w_j) = v_j` of the place of a factor (`tuple_finite`). -/
theorem sectFin_fiberPlace_eq {p : Nat.Primes} {ι : Type}
    (c : ι → LocalTheory.Fiber D.Fmod (.finite p)) (j : ι) :
    D.V.sectFin (LocalTheory.fiberPlace D.Fmod (c j)) =
      finPart D.Kt (LocalTheory.tuple D.placeSect _ c j) := by
  rw [LocalTheory.tuple_finite D.placeSect c j]
  rfl

/-- **The strip automorphism at the place `v_j` of a factor**: `φ_{w_j}` for the place `w_j` of
`F_mod` underlying `v_j = σ(w_j)`, transported along `σ(w_j) = v_j`. -/
def factorGal (φ : ∀ w : Vnon D, LocGal (D.V.sectFin w) ≃ₜ* LocGal (D.V.sectFin w))
    {p : Nat.Primes} {ι : Type} (c : ι → LocalTheory.Fiber D.Fmod (.finite p)) (j : ι) :
    CompGal (finPart D.Kt (LocalTheory.tuple D.placeSect _ c j)) ≃ₜ*
      CompGal (finPart D.Kt (LocalTheory.tuple D.placeSect _ c j)) :=
  Eq.rec (motive := fun x _ => CompGal x ≃ₜ* CompGal x)
    (φ (LocalTheory.fiberPlace D.Fmod (c j))) (sectFin_fiberPlace_eq c j)

theorem eqRec_refl_compGal {x y : FinitePlace D.Kt} (h : x = y) :
    Eq.rec (motive := fun x _ => CompGal x ≃ₜ* CompGal x) (ContinuousMulEquiv.refl _) h =
      ContinuousMulEquiv.refl (CompGal y) := by
  subst h
  rfl

theorem factorGal_refl {p : Nat.Primes} {ι : Type}
    (c : ι → LocalTheory.Fiber D.Fmod (.finite p)) (j : ι) :
    factorGal (fun _ => ContinuousMulEquiv.refl _) c j = ContinuousMulEquiv.refl _ :=
  eqRec_refl_compGal _

variable (D) in
/-- **A Kummer identification induced by a family of strip automorphisms** `φ`: at every
capsule `i`, prime `p` and tuple `c`, the unit of the tensor component is an elementary tensor of
factor scalings `b_j` with `compGalLogEquiv φ_{v_j} = scale b_j` (the Galois automorphism is
**the** one read off the strips, not an existential). -/
def StripScaling (φ : ∀ w : Vnon D, LocGal (D.V.sectFin w) ≃ₜ* LocGal (D.V.sectFin w))
    (s : Scaling D) : Prop :=
  ∀ (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)),
    ∃ a : ∀ j, Factor D.Kt p (LocalTheory.tuple D.placeSect _ c j),
      ((s.u i p c : (Comp D i p c)ˣ) : Comp D i p c) = PiTensorProduct.tprod ℚ_[p] a ∧
        ∀ j, ∃ b : (completionAt D.Kt (finPart D.Kt (LocalTheory.tuple D.placeSect _ c j)))ˣ,
          factorMk p _ b = a j ∧ ∀ h : IsOver D.Kt p (LocalTheory.tuple D.placeSect _ c j),
            compGalLogEquiv h.residueChar_finPart (factorGal φ c j) = scale b

/-- **A strip-induced Kummer identification is Galois-induced.** -/
theorem StripScaling.galInduced {φ : ∀ w : Vnon D, LocGal (D.V.sectFin w) ≃ₜ* _}
    {s : Scaling D} (h : StripScaling D φ s) : GalInducedScaling D s := fun i p c => by
  obtain ⟨a, ha, hj⟩ := h i p c
  refine ⟨a, ha, fun j => ?_⟩
  obtain ⟨b, hb, hφ⟩ := hj j
  exact ⟨b, hb, fun hov => ⟨_, hφ hov⟩⟩

theorem StripScaling.unitInduced {φ : ∀ w : Vnon D, LocGal (D.V.sectFin w) ≃ₜ* _}
    {s : Scaling D} (h : StripScaling D φ s) : UnitInducedScaling D s :=
  h.galInduced.unitInduced

/-- **Strip-induced Kummer identifications do not distort log-volumes.** -/
theorem StripScaling.shift_eq_zero {φ : ∀ w : Vnon D, LocGal (D.V.sectFin w) ≃ₜ* _}
    {s : Scaling D} (h : StripScaling D φ s) : shift D s = 0 :=
  h.galInduced.anabelian.shift_eq_zero

variable (D) in
/-- The identity scaling is induced by the identity automorphisms. -/
theorem stripScaling_one : StripScaling D (fun _ => ContinuousMulEquiv.refl _) 1 :=
  fun i p c => ⟨1, by rw [Scaling.one_u, Units.val_one]; rfl, fun j => ⟨1, map_one _,
    fun h => by
      rw [factorGal_refl, compGalLogEquiv_refl]
      ext x
      simp⟩⟩

/-! ### Kummer data read off the strips -/

/-- **Kummer data whose Galois automorphisms are read off the `D^⊢`-prime-strips**: rigidified
`D^⊢`-prime-strips at the vertices, isomorphisms to a coric rigidified `D^⊢`-prime-strip, and
Kummer identifications induced by the Galois automorphisms `gal (link a)` of these isomorphisms. -/
structure StripKummer (L : LogThetaLattice D) where
  /-- The rigidified `D^⊢`-prime-strip of the vertex `(n, m)`. -/
  strip : ℤ × ℤ → RigidDGalStrip D
  /-- The coric rigidified `D^⊢`-prime-strip. -/
  coric : RigidDGalStrip D
  /-- The isomorphisms of `D^⊢`-prime-strips to the coric strip. -/
  link : ∀ a, (strip a).strip.Iso coric.strip
  /-- The Kummer identification of the container of the vertex `(n, m)`. -/
  kum : ℤ × ℤ → Scaling D
  /-- It is induced by the Galois automorphisms read off `link a`. -/
  scale : ∀ a, StripScaling D (RigidDGalStrip.gal (link a)) (kum a)

namespace StripKummer

variable {L : LogThetaLattice D} (K : StripKummer L)

/-- **The Galois automorphisms read off the strips.** -/
def gal (a : ℤ × ℤ) (w : Vnon D) : LocGal (D.V.sectFin w) ≃ₜ* LocGal (D.V.sectFin w) :=
  RigidDGalStrip.gal (K.link a) w

/-- **The `GalKummer` data, with the Galois part derived from the strips.** -/
def toGalKummer : GalKummer L := ⟨K.kum, fun a => (K.scale a).galInduced⟩

/-- The `LatticeKummer` data (unit-inducedness discharged). -/
def toLatticeKummer : LatticeKummer L := K.toGalKummer.toLatticeKummer

theorem distortion_eq_zero (a b : ℤ × ℤ) : K.toLatticeKummer.model.distortion a b = 0 :=
  K.toGalKummer.distortion_eq_zero a b

/-- **Step (xi) is the Scholze–Stix inequality** for Kummer data read off the strips. -/
theorem xi_iff_ss : XiPrinciple K.toLatticeKummer ↔ SSIneq D :=
  K.toGalKummer.xi_iff_ss

theorem kum_ne_qScale_zpow (a : ℤ × ℤ) {m : ℤ} (hm : m ≠ 0) : K.kum a ≠ qScale D ^ m :=
  K.toGalKummer.kum_ne_qScale_zpow a hm

/-- **The lift of `link a` to the reconstructed `F^⊢`-prime-strips** (IUT I, Corollary 5.3(ii)
in the model). -/
def liftIso (a : ℤ × ℤ) : (K.strip a).toF.Iso K.coric.toF :=
  RigidDGalStrip.liftIso (K.link a)

theorem forget_liftIso (a : ℤ × ℤ) : FGalStrip.forget (K.liftIso a) = K.link a := rfl

/-- **The Frobenioid portion of the lift is induced by the Galois automorphism of the Kummer
identification.** -/
theorem liftIso_functor (a : ℤ × ℤ) (w : Vnon D) :
    (K.liftIso a w).1.functor = (galFrobAt D w (K.gal a w)).functor := rfl

variable (L) in
/-- **The trivial Kummer data read off the tautological strips** (identity isomorphisms). -/
def trivial : StripKummer L where
  strip _ := RigidDGalStrip.taut D
  coric := RigidDGalStrip.taut D
  link _ := PrimeStrip.Iso.refl _
  kum _ := 1
  scale _ := by
    have h : RigidDGalStrip.gal (PrimeStrip.Iso.refl (RigidDGalStrip.taut D).strip) =
        fun _ => ContinuousMulEquiv.refl _ := funext (RigidDGalStrip.gal_refl _)
    rw [h]
    exact stripScaling_one D

theorem trivial_toLatticeKummer : (trivial L).toLatticeKummer = LatticeKummer.trivial L := rfl

end StripKummer

/-- **`classicalABC_of_thm311` for Kummer data read off the strips.** -/
theorem classicalABC_of_thm311_strip (L : ∀ D : InitialThetaData.{0}, LogThetaLattice D)
    (K : ∀ D, StripKummer (L D)) (h : ∀ D, Thm311 (L D) (K D).toLatticeKummer)
    (hx : ∀ D, XiPrinciple (K D).toLatticeKummer) : ClassicalABC :=
  classicalABC_of_thm311 L (fun D => (K D).toLatticeKummer) h hx

/-- Step (xi) for lattices with Kummer data read off the strips implies `ClassicalABC`; by
`StripKummer.xi_iff_ss` this hypothesis is `SSIneq`. -/
theorem classicalABC_of_xi_strip
    (hx : ∀ D : InitialThetaData.{0}, ∃ (L : LogThetaLattice D) (K : StripKummer L),
      XiPrinciple K.toLatticeKummer) : ClassicalABC :=
  classicalABC_of_xi fun D => by
    obtain ⟨L, K, h⟩ := hx D
    exact ⟨L, K.toLatticeKummer, h⟩

end

end LogLink

end Iut
