/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Thm311
import Iut.LogLink.Galois
import Iut.Reconstruction.Local.LogVolumeCompletion

/-!
# Kummer data from the anabelian reconstruction: unit-inducedness as a theorem

P20 (`Iut/LogLink/Kummer.lean`) derived the log-shell compatibility and the vanishing of the
volume distortion of the Kummer identifications from their **unit-inducedness**
(`UnitInducedScaling`), an input field of `LatticeKummer`. Here the Kummer identifications are
described by their **origin** in the anabelian reconstruction, and their unit-inducedness is a
theorem (`Iut/LogLink/Galois.lean` for the local statement).

In IUT III the Kummer isomorphisms of the log-shell containers (Theorem 3.11(ii)(a)) are tensor
products (Proposition 3.2) of the local identifications `log(D^⊢_v) ≅ log(F^{⊢×μ}_v) ≅ log(F_v)`
(Proposition 1.2(vi), (viii); Theorem 1.5(iii), (iv)), constructed from

* the `D^⊢`-data, i.e. the topological group `G_v`: an isomorphism of the Galois groups
  induces, by [AbsTopIII], Proposition 5.8 (P17), an isomorphism of `𝒪^×(G_v) ≅ 𝒪_vˣ` and of
  the log-shell `monoLogShell(G_v) ≅ 𝓘_v` (`FactorGalInduced`);
* the `F^{⊢×μ}`-data, i.e. `𝒪^{×μ}` up to `Ism`: an automorphism of the unit group
  (`FactorUnitsAut`; this covers the Galois case and the inversion of the units, which induces
  P19's alien identification `x ↦ −x`).

In the model a Kummer identification is a `Wall.Scaling` (a unit of each tensor component,
acting by multiplication). The data below record, for each factor, a unit `b` of the completion
whose scaling **is** the identification induced by a Galois automorphism (resp. by an
automorphism of `𝒪_vˣ`). This equation (the identification is a scaling of the factor) is the
form the model imposes on Kummer identifications; unit-inducedness, log-shell compatibility and
volume neutrality are then theorems.

## Main results

* `compGalLogEquiv`, `compUnitLogEquiv`: the identifications of a completion `K_w` (with its
  `ℚ_p`-structure `padicAlgebra`) induced by a topological automorphism of
  `G_w = Gal(K̄_w/K_w)`, resp. by an automorphism of `𝒪_{K_w}ˣ`; **`unitInduced_compGalLogEquiv`,
  `unitInduced_compUnitLogEquiv`**, `compGalLogEquiv_image_logShell`;
* `FactorGalInduced`, `FactorUnitsAut`, **`FactorUnitsAut.factorUnitInduced`**;
  `exists_factorGalInduced_of_linear` (a `K_v`-linear Galois-induced identification is the
  scaling by `b = ψ(1)`, which is then Galois-induced);
  `factorGalInduced_one`, `factorUnitsAut_neg_one`; `norm_eq_one_of_factorUnitsAut`;
* `GalInducedScaling`, `AnabelianScaling`; **`AnabelianScaling.unitInduced`**,
  `GalInducedScaling.anabelian`, `galInducedScaling_one`, `anabelianScaling_negScale`;
* (3) obstructions: **`not_anabelianScaling_of_shift_ne_zero`** (an identification arising from
  the reconstruction does not distort volumes), `not_anabelianScaling_qScale_zpow`,
  `not_galInducedScaling_qScale_zpow`;
* the lattice: `AnabelianKummer`, `GalKummer` (Kummer data by origin), **`toLatticeKummer`**
  (the field `unit` of `LatticeKummer` discharged), `GalKummer.trivial`, `AnabelianKummer.alt`
  (the P20 data `LatticeKummer.trivial`, `LatticeKummer.alt` arise from the reconstruction,
  `trivial_toLatticeKummer`, `alt_toLatticeKummer`); restated with the unit-inducedness field
  discharged: `distortion_eq_zero`, `xi_iff_ss`, `classicalABC_of_thm311`, `classicalABC_of_xi`,
  `kum_ne_qScale_zpow`.

## What remains an input

* that the Kummer identifications of the model are scalings (the equation in the data);
* the archimedean places (not in the model);
* the lift of isomorphisms of `D`-prime-strips to `F`-prime-strips (IUT I, Corollary 5.3(ii)),
  i.e. that the identifications of the containers are those induced by the `D^⊢`/`F^{⊢×μ}`-data
  of the strips: the Hodge theaters of the model carry no `G_v` (P18's `F`-prime-strips record
  Frobenioids), so the Galois automorphisms are data of the Kummer structure, not read off from
  the strips;
* which automorphisms of `G_v` exist (and whether their identifications are scalings) is not
  decided here; the obstructions above hold for all of them.
-/

namespace Iut

namespace LogLink

open LocalConstruct NumberField Wall ThetaLink HodgeTheater PadicField Reconstruction

noncomputable section

/-! ### The completions -/

section Completion

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] {w : FinitePlace K}

variable (w) in
/-- **The local Galois group** `G_w = Gal(K̄_w/K_w)` of the completion. -/
abbrev CompGal : Type :=
  AlgebraicClosure (completionAt K w) ≃ₐ[completionAt K w] AlgebraicClosure (completionAt K w)

variable (hw : residueChar w = p)

/-- **The units `𝒪_{K_w}ˣ`** (for the `ℚ_p`-structure `padicAlgebra hw`). -/
abbrev CompUnits : Type :=
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  unitGroup p (completionAt K w)

/-- **The identification of `K_w` induced by an automorphism of `𝒪_{K_w}ˣ`.** -/
def compUnitLogEquiv (β : CompUnits hw ≃* CompUnits hw) :
    completionAt K w ≃+ completionAt K w :=
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  unitLogEquiv (hball_completionAt hw) β

/-- The automorphism of `𝒪_{K_w}ˣ` reconstructed from a topological automorphism of `G_w`. -/
def compGalUnits (φ : CompGal w ≃ₜ* CompGal w) : CompUnits hw ≃* CompUnits hw :=
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  haveI : Algebra.IsAlgebraic ℚ_[p] (AlgebraicClosure (completionAt K w)) :=
    Algebra.IsAlgebraic.trans ℚ_[p] (completionAt K w) _
  galUnitsEquiv p φ

/-- **The identification of `K_w` induced by a topological automorphism of `G_w`.** -/
def compGalLogEquiv (φ : CompGal w ≃ₜ* CompGal w) : completionAt K w ≃+ completionAt K w :=
  compUnitLogEquiv hw (compGalUnits hw φ)

theorem compGalLogEquiv_eq (φ : CompGal w ≃ₜ* CompGal w) :
    letI := padicAlgebra hw
    haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
    haveI : Algebra.IsAlgebraic ℚ_[p] (AlgebraicClosure (completionAt K w)) :=
      Algebra.IsAlgebraic.trans ℚ_[p] (completionAt K w) _
    compGalLogEquiv hw φ = galLogEquiv (hball_completionAt hw) φ :=
  rfl

/-- **Identifications induced by automorphisms of `𝒪_{K_w}ˣ` are unit-induced.** -/
theorem unitInduced_compUnitLogEquiv (β : CompUnits hw ≃* CompUnits hw) :
    UnitInduced (compUnitLogEquiv hw β) :=
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  unitInduced_unitLogEquiv (hball_completionAt hw) β

/-- **Identifications induced by Galois automorphisms are unit-induced.** -/
theorem unitInduced_compGalLogEquiv (φ : CompGal w ≃ₜ* CompGal w) :
    UnitInduced (compGalLogEquiv hw φ) :=
  unitInduced_compUnitLogEquiv hw _

/-- They preserve the log-shell (read off from the group-theoretic log-shell
`monoLogShell (G_w)`, `galLogEquiv_image_logShell`). -/
theorem compGalLogEquiv_image_logShell (φ : CompGal w ≃ₜ* CompGal w) :
    compGalLogEquiv hw φ '' Iut.logShell (completionAt K w) p = Iut.logShell (completionAt K w) p :=
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  haveI : Algebra.IsAlgebraic ℚ_[p] (AlgebraicClosure (completionAt K w)) :=
    Algebra.IsAlgebraic.trans ℚ_[p] (completionAt K w) _
  galLogEquiv_image_logShell (hball_completionAt hw) φ

theorem compGalLogEquiv_refl : compGalLogEquiv hw (ContinuousMulEquiv.refl (CompGal w)) =
    AddEquiv.refl _ :=
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  haveI : Algebra.IsAlgebraic ℚ_[p] (AlgebraicClosure (completionAt K w)) :=
    Algebra.IsAlgebraic.trans ℚ_[p] (completionAt K w) _
  galLogEquiv_refl (hball_completionAt hw)

/-- **The inversion of the units induces `x ↦ −x`.** -/
theorem compUnitLogEquiv_inv : compUnitLogEquiv hw (MulEquiv.inv (CompUnits hw)) =
    AddEquiv.neg _ :=
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  unitLogEquiv_inv (hball_completionAt hw)

end Completion

/-! ### Factor scalings from the reconstruction -/

section Factor

variable {K : Type} [Field K] [NumberField K] {p : Nat.Primes} {v : Place K}

/-- **A factor scaling induced by a Galois isomorphism** (`D^⊢`-data): the image of a unit `b`
of the completion whose scaling is the identification induced by a topological automorphism of
`G_v` (when `v` lies over `p`; otherwise the factor is the zero ring). -/
def FactorGalInduced (a : Factor K p v) : Prop :=
  ∃ b : (completionAt K (finPart K v))ˣ, factorMk p v b = a ∧
    ∀ h : IsOver K p v, ∃ φ : CompGal (finPart K v) ≃ₜ* CompGal (finPart K v),
      compGalLogEquiv h.residueChar_finPart φ = scale b

/-- **A factor scaling induced by an automorphism of the units** (`F^{⊢×μ}`-data): the image of
a unit `b` of the completion whose scaling is the identification induced by an automorphism of
`𝒪_vˣ`. -/
def FactorUnitsAut (a : Factor K p v) : Prop :=
  ∃ b : (completionAt K (finPart K v))ˣ, factorMk p v b = a ∧
    ∀ h : IsOver K p v, ∃ β : CompUnits h.residueChar_finPart ≃* CompUnits h.residueChar_finPart,
      compUnitLogEquiv h.residueChar_finPart β = scale b

theorem FactorGalInduced.unitsAut {a : Factor K p v} (h : FactorGalInduced a) :
    FactorUnitsAut a := by
  obtain ⟨b, hb, hφ⟩ := h
  refine ⟨b, hb, fun hov => ?_⟩
  obtain ⟨φ, hφ⟩ := hφ hov
  exact ⟨compGalUnits hov.residueChar_finPart φ, hφ⟩

/-- **A factor scaling arising from the reconstruction is unit-induced** (P20's
`FactorUnitInduced`). -/
theorem FactorUnitsAut.factorUnitInduced {a : Factor K p v} (h : FactorUnitsAut a) :
    FactorUnitInduced a := by
  obtain ⟨b, hb, hβ⟩ := h
  by_cases hov : IsOver K p v
  · obtain ⟨β, hβ⟩ := hβ hov
    exact ⟨b, hb, hβ ▸ unitInduced_compUnitLogEquiv _ β⟩
  · haveI := subsingleton_factor p v hov
    exact ⟨1, Subsingleton.elim _ _, ⟨MulEquiv.refl _, fun u => by simp⟩⟩

theorem FactorGalInduced.factorUnitInduced {a : Factor K p v} (h : FactorGalInduced a) :
    FactorUnitInduced a :=
  h.unitsAut.factorUnitInduced

/-- **The scaling is constructed from the Galois automorphism**: if the identification `ψ`
induced by a topological automorphism `φ` of `G_v` is `K_v`-linear (i.e. it is a scaling of the
factor, the form of the model's Kummer identifications), then `ψ` is the scaling by `b = ψ(1)`,
and its image in the factor is Galois-induced. -/
theorem exists_factorGalInduced_of_linear (hov : IsOver K p v)
    (φ : CompGal (finPart K v) ≃ₜ* CompGal (finPart K v))
    (hlin : ∀ x y, compGalLogEquiv hov.residueChar_finPart φ (x * y) =
      x * compGalLogEquiv hov.residueChar_finPart φ y) :
    ∃ b : (completionAt K (finPart K v))ˣ,
      (b : completionAt K (finPart K v)) = compGalLogEquiv hov.residueChar_finPart φ 1 ∧
        compGalLogEquiv hov.residueChar_finPart φ = scale b ∧
          FactorGalInduced (factorMk p v b) := by
  set ψ := compGalLogEquiv hov.residueChar_finPart φ
  have h1 : ψ 1 ≠ 0 := fun h0 => one_ne_zero (ψ.injective (h0.trans (map_zero ψ).symm))
  have hs : ψ = scale (Units.mk0 (ψ 1) h1) := by
    ext x
    rw [scale_apply, Units.val_mk0, mul_comm, ← hlin, mul_one]
  exact ⟨Units.mk0 (ψ 1) h1, rfl, hs, ⟨_, rfl, fun h => ⟨φ, hs⟩⟩⟩

/-- `1` is induced by the identity of `G_v`. -/
theorem factorGalInduced_one : FactorGalInduced (1 : Factor K p v) :=
  ⟨1, map_one _, fun h => ⟨ContinuousMulEquiv.refl _, by
    rw [compGalLogEquiv_refl]
    ext x
    simp⟩⟩

/-- `−1` is induced by the inversion of the units. -/
theorem factorUnitsAut_neg_one : FactorUnitsAut (-1 : Factor K p v) :=
  ⟨-1, by simp, fun h => ⟨MulEquiv.inv _, by
    rw [compUnitLogEquiv_inv]
    ext x
    simp⟩⟩

/-- **A factor scaling `b` arising from the reconstruction has `‖b‖ = 1`**: a nonzero power
of a Tate parameter does not arise. -/
theorem norm_eq_one_of_factorUnitsAut (hov : IsOver K p v) {b : (completionAt K (finPart K v))ˣ}
    (h : FactorUnitsAut (factorMk p v b)) : ‖(b : completionAt K (finPart K v))‖ = 1 := by
  obtain ⟨b', hb', hu⟩ := h.factorUnitInduced
  have hbb : b' = b := Units.ext (factorMk_injective p v hov hb')
  subst hbb
  exact norm_eq_one_of_unitInduced_scale p.2
    (norm_natCast_lt_one_completion hov.residueChar_finPart) hu

end Factor

/-! ### Kummer identifications from the reconstruction -/

variable (D : InitialThetaData.{0})

/-- **A Kummer identification arising from the reconstruction** (`F^{⊢×μ}`-data): at every
capsule `i`, prime `p` and tuple `c`, the unit of the tensor component is an elementary tensor of
factor scalings induced by automorphisms of the unit groups. -/
def AnabelianScaling (w : Scaling D) : Prop :=
  ∀ (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)),
    ∃ a : ∀ j, Factor D.Kt p (LocalTheory.tuple D.placeSect _ c j),
      ((w.u i p c : (Comp D i p c)ˣ) : Comp D i p c) = PiTensorProduct.tprod ℚ_[p] a ∧
        ∀ j, FactorUnitsAut (a j)

/-- **A Kummer identification induced by Galois isomorphisms** (`D^⊢`-data): the factors are
induced by topological automorphisms of the local Galois groups. -/
def GalInducedScaling (w : Scaling D) : Prop :=
  ∀ (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)),
    ∃ a : ∀ j, Factor D.Kt p (LocalTheory.tuple D.placeSect _ c j),
      ((w.u i p c : (Comp D i p c)ˣ) : Comp D i p c) = PiTensorProduct.tprod ℚ_[p] a ∧
        ∀ j, FactorGalInduced (a j)

variable {D}

theorem GalInducedScaling.anabelian {w : Scaling D} (h : GalInducedScaling D w) :
    AnabelianScaling D w := fun i p c => by
  obtain ⟨a, ha, hj⟩ := h i p c
  exact ⟨a, ha, fun j => (hj j).unitsAut⟩

/-- **Kummer identifications arising from the reconstruction are unit-induced** (the input of
P20's `logShellCompat_of_unitInduced`, now a theorem). -/
theorem AnabelianScaling.unitInduced {w : Scaling D} (h : AnabelianScaling D w) :
    UnitInducedScaling D w := fun i p c => by
  obtain ⟨a, ha, hj⟩ := h i p c
  exact ⟨a, ha, fun j => (hj j).factorUnitInduced⟩

theorem GalInducedScaling.unitInduced {w : Scaling D} (h : GalInducedScaling D w) :
    UnitInducedScaling D w :=
  h.anabelian.unitInduced

/-- **They are log-shell compatible.** -/
theorem AnabelianScaling.logShellCompat {w : Scaling D} (h : AnabelianScaling D w) :
    LogShellCompat D w :=
  logShellCompat_of_unitInduced D h.unitInduced

/-- **They do not distort log-volumes.** -/
theorem AnabelianScaling.shift_eq_zero {w : Scaling D} (h : AnabelianScaling D w) :
    shift D w = 0 :=
  shift_eq_zero_of_unitInduced D h.unitInduced

variable (D)

theorem galInducedScaling_one : GalInducedScaling D 1 := fun _ _ _ =>
  ⟨1, by rw [Scaling.one_u, Units.val_one]; rfl, fun _ => factorGalInduced_one⟩

/-- **P19's alien identification `x ↦ −x` arises from the inversion of the units.** -/
theorem anabelianScaling_negScale : AnabelianScaling D (negScale D) := by
  classical
  intro i p c
  by_cases hp : (p : ℕ) ∈ D.badChars
  · refine ⟨Pi.mulSingle (labOne D i) (-1), ?_, fun j => ?_⟩
    · change ((if (p : ℕ) ∈ D.badChars then (-1 : (Comp D i p c)ˣ) else 1 : (Comp D i p c)ˣ) :
        Comp D i p c) = _
      rw [if_pos hp, Units.val_neg, Units.val_one]
      have := map_neg (PiTensorProduct.singleAlgHom (R := ℚ_[p])
        (A := fun j => Factor D.Kt p (LocalTheory.tuple D.placeSect _ c j)) (labOne D i)) 1
      rw [map_one] at this
      rw [← this]
      rfl
    · by_cases hj : j = labOne D i
      · subst hj
        rw [Pi.mulSingle_eq_same]
        exact factorUnitsAut_neg_one
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact factorGalInduced_one.unitsAut
  · refine ⟨1, ?_, fun _ => factorGalInduced_one.unitsAut⟩
    change ((if (p : ℕ) ∈ D.badChars then (-1 : (Comp D i p c)ˣ) else 1 : (Comp D i p c)ˣ) :
      Comp D i p c) = _
    rw [if_neg hp, Units.val_one]
    rfl

/-! ### (3) Identifications that do not arise from the reconstruction -/

/-- **A Kummer identification that distorts log-volumes does not arise from the
reconstruction** (neither from Galois isomorphisms nor from automorphisms of the unit groups). -/
theorem not_anabelianScaling_of_shift_ne_zero {w : Scaling D} (h : shift D w ≠ 0) :
    ¬ AnabelianScaling D w := fun h' => h h'.shift_eq_zero

/-- **The `q`-power identifications of the drifting M3 rows do not arise from the
reconstruction.** -/
theorem not_anabelianScaling_qScale_zpow {m : ℤ} (hm : m ≠ 0) :
    ¬ AnabelianScaling D (qScale D ^ m) := fun h =>
  not_unitInducedScaling_qScale_zpow D hm h.unitInduced

theorem not_galInducedScaling_qScale_zpow {m : ℤ} (hm : m ≠ 0) :
    ¬ GalInducedScaling D (qScale D ^ m) := fun h =>
  not_anabelianScaling_qScale_zpow D hm h.anabelian

/-! ### Kummer data on the log-theta-lattice -/

variable {D}

/-- **Kummer data arising from the reconstruction** (`F^{⊢×μ}`-data) at every vertex of a
log-theta-lattice. -/
structure AnabelianKummer (L : LogThetaLattice D) where
  /-- The Kummer identification of the container of the vertex `(n, m)`. -/
  kum : ℤ × ℤ → Scaling D
  /-- It is induced by automorphisms of the unit groups. -/
  anab : ∀ a, AnabelianScaling D (kum a)

/-- **Kummer data induced by Galois isomorphisms** (`D^⊢`-data) at every vertex. -/
structure GalKummer (L : LogThetaLattice D) where
  /-- The Kummer identification of the container of the vertex `(n, m)`. -/
  kum : ℤ × ℤ → Scaling D
  /-- It is induced by topological automorphisms of the local Galois groups. -/
  gal : ∀ a, GalInducedScaling D (kum a)

namespace AnabelianKummer

variable {L : LogThetaLattice D} (K : AnabelianKummer L)

/-- **The unit-inducedness field of `LatticeKummer` is discharged.** -/
def toLatticeKummer : LatticeKummer L := ⟨K.kum, fun a => (K.anab a).unitInduced⟩

theorem distortion_eq_zero (a b : ℤ × ℤ) : K.toLatticeKummer.model.distortion a b = 0 :=
  K.toLatticeKummer.distortion_eq_zero a b

/-- **Step (xi) is the Scholze–Stix inequality**, unconditionally on the Kummer data (Theorem
3.11 holds in the model, `thm311_model`). -/
theorem xi_iff_ss : XiPrinciple K.toLatticeKummer ↔ SSIneq D :=
  LogLink.xi_iff_ss (thm311_model L K.toLatticeKummer)

/-- **No Kummer identification of the lattice is a `q`-power identification.** -/
theorem kum_ne_qScale_zpow (a : ℤ × ℤ) {m : ℤ} (hm : m ≠ 0) : K.kum a ≠ qScale D ^ m :=
  fun h => not_anabelianScaling_qScale_zpow D hm (h ▸ K.anab a)

variable (L) in
/-- **P20's alien Kummer data arise from the reconstruction**: `x ↦ −x` (by the inversion of the
units) at the vertices with `n + m` odd, the identity elsewhere. -/
def alt : AnabelianKummer L :=
  ⟨(LatticeKummer.alt L).kum, fun a => by
    classical
    change AnabelianScaling D (if Even (a.1 + a.2) then 1 else negScale D)
    split_ifs
    · exact (galInducedScaling_one D).anabelian
    · exact anabelianScaling_negScale D⟩

theorem alt_toLatticeKummer : (alt L).toLatticeKummer = LatticeKummer.alt L := rfl

end AnabelianKummer

namespace GalKummer

variable {L : LogThetaLattice D} (K : GalKummer L)

def toAnabelianKummer : AnabelianKummer L := ⟨K.kum, fun a => (K.gal a).anabelian⟩

/-- **The unit-inducedness field of `LatticeKummer` is discharged.** -/
def toLatticeKummer : LatticeKummer L := K.toAnabelianKummer.toLatticeKummer

theorem distortion_eq_zero (a b : ℤ × ℤ) : K.toLatticeKummer.model.distortion a b = 0 :=
  K.toAnabelianKummer.distortion_eq_zero a b

theorem xi_iff_ss : XiPrinciple K.toLatticeKummer ↔ SSIneq D :=
  K.toAnabelianKummer.xi_iff_ss

theorem kum_ne_qScale_zpow (a : ℤ × ℤ) {m : ℤ} (hm : m ≠ 0) : K.kum a ≠ qScale D ^ m :=
  K.toAnabelianKummer.kum_ne_qScale_zpow a hm

variable (L) in
/-- **The trivial Kummer data are induced by the identity of the Galois groups.** -/
def trivial : GalKummer L := ⟨fun _ => 1, fun _ => galInducedScaling_one D⟩

theorem trivial_toLatticeKummer : (trivial L).toLatticeKummer = LatticeKummer.trivial L := rfl

end GalKummer

/-- **`classicalABC_of_thm311` with the unit-inducedness field discharged**: Theorem 3.11 and
Step (xi) for lattices with Kummer data arising from the reconstruction imply `ClassicalABC`. -/
theorem classicalABC_of_thm311_anabelian (L : ∀ D : InitialThetaData.{0}, LogThetaLattice D)
    (K : ∀ D, AnabelianKummer (L D)) (h : ∀ D, Thm311 (L D) (K D).toLatticeKummer)
    (hx : ∀ D, XiPrinciple (K D).toLatticeKummer) : ClassicalABC :=
  classicalABC_of_thm311 L (fun D => (K D).toLatticeKummer) h hx

/-- The same for Kummer data induced by Galois isomorphisms. -/
theorem classicalABC_of_thm311_gal (L : ∀ D : InitialThetaData.{0}, LogThetaLattice D)
    (K : ∀ D, GalKummer (L D)) (h : ∀ D, Thm311 (L D) (K D).toLatticeKummer)
    (hx : ∀ D, XiPrinciple (K D).toLatticeKummer) : ClassicalABC :=
  classicalABC_of_thm311 L (fun D => (K D).toLatticeKummer) h hx

/-- Since Theorem 3.11 holds in the model, Step (xi) for lattices with Galois-induced Kummer
data alone implies `ClassicalABC`; by `GalKummer.xi_iff_ss` this hypothesis is `SSIneq`. -/
theorem classicalABC_of_xi_gal
    (hx : ∀ D : InitialThetaData.{0}, ∃ (L : LogThetaLattice D) (K : GalKummer L),
      XiPrinciple K.toLatticeKummer) : ClassicalABC :=
  classicalABC_of_xi fun D => by
    obtain ⟨L, K, h⟩ := hx D
    exact ⟨L, K.toLatticeKummer, h⟩

end

end LogLink

end Iut
