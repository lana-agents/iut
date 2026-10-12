/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Lattice
import Iut.ThetaLink.Wall

/-!
# Log-shell compatibility of the Kummer identifications, derived

P19 (`Iut/ThetaLink/Wall.lean`) required the Kummer identifications `κ_h` of the log-shell
containers of the Hodge theaters with the coric container to be **log-shell compatible**
(`ThetaLink.LogShellCompat`: `κ_h(VC(I)) = VC(I)`), as a hypothesis field of `LinkedChain`. Here
this is **derived** from the structure that the log-link gives to the Kummer identifications.

In IUT III the Kummer isomorphisms of the log-shell containers (Theorem 3.11(ii)(a)) are tensor
products, over the labels of a capsule (Proposition 3.2), of local isomorphisms
`log(D^⊢_v) ≅ log(F^{⊢×μ}_v) ≅ log(F_v)` which are constructed from the `F^{⊢×μ}`-data, i.e.
through the logarithm from isomorphisms of the unit groups (Proposition 1.2(vi), (viii);
Theorem 1.5(iii), (iv)). In the model (`Wall.Scaling`) a Kummer identification is a unit `u` of
every tensor component; it is **unit-induced** (`UnitInducedScaling`) if every component is an
elementary tensor `⊗_j a_j` of factor units `a_j` whose scalings are unit-induced
(`FactorUnitInduced`, from `LogLink.UnitInduced`).

## Results

* `tprod_mul_mem_tensorLogShell`, `tprod_image_tensorLogShell`: elementary tensors of
  log-shell-preserving factor scalings preserve the tensor product of the log-shells `⊗_j 𝓘_j`;
* `FactorUnitInduced.image_eq`: a unit-induced factor scaling preserves the factor log-shell
  (`LogLink.image_logShell_of_unitInduced`);
* **`logShellCompat_of_unitInduced`: unit-induced Kummer identifications are log-shell
  compatible**, hence volume compatible (`shift_eq_zero_of_unitInduced`);
* examples: `unitInducedScaling_one`, **`unitInducedScaling_negScale`** (P19's alien
  identification `x ↦ −x` at the bad primes is unit-induced, by the inversion of the units), and
  `not_unitInducedScaling_qScale_zpow` (the `q`-power identifications of the drifting M3 rows
  are not: they move value-group data into the unit portion);
* **`LatticeKummer`**: unit-induced Kummer identifications at every vertex of a log-theta-lattice;
  its rows are P19 `LinkedChain`s (`toLinkedChain`), and in its multi-container model
  (`model`: P18's η-algorithm over the vertices) the distortion of the transport between any two
  vertices is `0` (`distortion_eq_zero`), along horizontal (Θ-link) and vertical (log-link)
  arrows alike.

**What further input is needed.** The derivation uses exactly the hypothesis that each Kummer
identification is unit-induced in the sense above (the structure of IUT III, Proposition 1.2(vi),
(viii), Theorem 1.5(iii), (iv)). The upper semi-compatibility of the log-Kummer correspondence
(`LogColumn.upperSemiCompat`) alone does not suffice: it is an inclusion of the images of units
and of their iterated logarithms into the log-shell, which holds for every holomorphic Kummer
isomorphism (`LogColumn.upperSemiCompat` is proved for an arbitrary column) and so does not
constrain the mono-analytic scalings of the containers. Whether the Kummer identifications are
unit-induced is not a consequence of the model; in IUT it is the content of the construction
of the mono-analytic log-shells from `F^{⊢×μ}` (Proposition 1.2(vi)). **This construction is
formalised in `Iut/LogLink/Galois.lean` and `Iut/LogLink/GalKummer.lean`**: identifications
induced by Galois isomorphisms or by automorphisms of the unit groups are unit-induced
(`unitInduced_galLogEquiv`, `AnabelianScaling.unitInduced`), and Kummer data given by their
origin (`AnabelianKummer`, `GalKummer`) yield `LatticeKummer` data (`toLatticeKummer`).
-/

namespace Iut

namespace LogLink

open LocalConstruct NumberField Wall ThetaLink HodgeTheater
open scoped Pointwise Valued

noncomputable section

/-! ### Elementary tensors of factor scalings -/

section Tensor

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (p : Nat.Primes)
  (c : ι → Place K)

/-- **An elementary tensor of factor scalings that preserve the factor log-shells preserves the
tensor product of the log-shells.** -/
theorem tprod_mul_mem_tensorLogShell (a : ∀ j, Factor K p (c j))
    (ha : ∀ j, ∀ y ∈ factorLogShell p (c j), a j * y ∈ factorLogShell p (c j))
    {x : Tensor K (.finite p) c} (hx : x ∈ tensorLogShell p c) :
    PiTensorProduct.tprod ℚ_[p] a * x ∈ tensorLogShell p c := by
  unfold tensorLogShell at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun j => ⟨a j * b j, ha j _ (b j).2⟩, ?_⟩
    exact (PiTensorProduct.tprod_mul_tprod _ _).symm
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx =>
    change _ * ((r : ℚ_[p]) • x) ∈ _
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ r hx

/-- **Elementary tensors of invertible factor scalings preserving the factor log-shells map the
tensor product of the log-shells onto itself.** -/
theorem tprod_image_tensorLogShell (a b : ∀ j, Factor K p (c j)) (hab : ∀ j, a j * b j = 1)
    (ha : ∀ j, (fun y => a j * y) '' factorLogShell p (c j) = factorLogShell p (c j)) :
    (fun x => PiTensorProduct.tprod ℚ_[p] a * x) '' tensorLogShell p c = tensorLogShell p c := by
  have ha' : ∀ j, ∀ y ∈ factorLogShell p (c j), a j * y ∈ factorLogShell p (c j) :=
    fun j y hy => by rw [← ha j]; exact ⟨y, hy, rfl⟩
  have hb' : ∀ j, ∀ y ∈ factorLogShell p (c j), b j * y ∈ factorLogShell p (c j) := by
    intro j y hy
    rw [← ha j] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rwa [← mul_assoc, mul_comm (b j), hab j, one_mul]
  have hone : PiTensorProduct.tprod ℚ_[p] a * PiTensorProduct.tprod ℚ_[p] b = 1 := by
    rw [PiTensorProduct.tprod_mul_tprod, PiTensorProduct.one_def]
    congr 1
    funext j
    exact hab j
  refine Set.Subset.antisymm ?_ fun x hx => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact tprod_mul_mem_tensorLogShell p c a ha' hx
  · refine ⟨PiTensorProduct.tprod ℚ_[p] b * x, tprod_mul_mem_tensorLogShell p c b hb' hx, ?_⟩
    dsimp only
    rw [← mul_assoc, hone, one_mul]

/-! ### Unit-induced factor scalings -/

variable {p} {v : Place K}

/-- **A unit-induced factor scaling**: the image of a unit `b` of the completion whose scaling is
unit-induced (`LogLink.UnitInduced`). -/
def FactorUnitInduced (a : Factor K p v) : Prop :=
  ∃ b : (completionAt K (finPart K v))ˣ, factorMk p v b = a ∧ UnitInduced (scale b)

/-- A scaling of the completion preserving the log-shell induces a scaling of the factor
preserving the factor log-shell. -/
theorem factorMk_image_factorLogShell {b : completionAt K (finPart K v)}
    (hb : (fun x => b * x) '' Iut.logShell (completionAt K (finPart K v)) p =
      Iut.logShell (completionAt K (finPart K v)) p) :
    (fun y => factorMk p v b * y) '' factorLogShell p v = factorLogShell p v := by
  unfold factorLogShell
  rw [Set.image_image]
  conv_rhs => rw [← hb, Set.image_image]
  simp only [map_mul]

/-- **A unit-induced factor scaling preserves the factor log-shell.** -/
theorem FactorUnitInduced.image_eq {a : Factor K p v} (h : FactorUnitInduced a) :
    (fun y => a * y) '' factorLogShell p v = factorLogShell p v := by
  obtain ⟨b, rfl, hb⟩ := h
  by_cases hov : IsOver K p v
  · exact factorMk_image_factorLogShell (image_logShell_of_unitInduced p.2 hb)
  · haveI := subsingleton_factor p v hov
    have h0 : (0 : Factor K p v) ∈ factorLogShell p v :=
      ⟨0, zero_mem_logShell, map_zero _⟩
    ext y
    rw [Subsingleton.elim y 0]
    exact ⟨fun _ => h0, fun _ => ⟨0, h0, Subsingleton.elim _ _⟩⟩

/-- The inverse of a unit-induced factor scaling. -/
theorem FactorUnitInduced.exists_inv {a : Factor K p v} (h : FactorUnitInduced a) :
    ∃ a' : Factor K p v, a * a' = 1 := by
  obtain ⟨b, rfl, -⟩ := h
  exact ⟨factorMk p v (b⁻¹ : (completionAt K (finPart K v))ˣ), by
    rw [← map_mul, Units.mul_inv, map_one]⟩

theorem factorUnitInduced_one : FactorUnitInduced (1 : Factor K p v) :=
  ⟨1, map_one _, ⟨MulEquiv.refl _, fun u => by simp⟩⟩

/-- `−1` is unit-induced (by the inversion of the units). -/
theorem factorUnitInduced_neg_one : FactorUnitInduced (-1 : Factor K p v) := by
  by_cases hov : IsOver K p v
  · refine ⟨-1, by simp, ?_⟩
    have hpk := norm_natCast_lt_one_completion hov.residueChar_finPart
    obtain ⟨α, hα⟩ := unitInduced_neg (k := completionAt K (finPart K v)) p.2 hpk
    exact ⟨α, fun u => by rw [← hα u]; simp⟩
  · haveI := subsingleton_factor p v hov
    exact ⟨1, Subsingleton.elim _ _, ⟨MulEquiv.refl _, fun u => by simp⟩⟩

/-- **A tensor of unit-induced factor scalings preserves `⊗_j 𝓘_j`.** -/
theorem tprod_image_tensorLogShell_of_unitInduced (a : ∀ j, Factor K p (c j))
    (ha : ∀ j, FactorUnitInduced (a j)) :
    (fun x => PiTensorProduct.tprod ℚ_[p] a * x) '' tensorLogShell p c = tensorLogShell p c := by
  choose b hb using fun j => (ha j).exists_inv
  exact tprod_image_tensorLogShell p c a b hb fun j => (ha j).image_eq

end Tensor

/-! ### Unit-induced Kummer identifications -/

variable (D : InitialThetaData.{0})

/-- **A unit-induced Kummer identification**: at every capsule `i`, prime `p` and tuple `c`, the
unit of the tensor component is an elementary tensor of unit-induced factor scalings. -/
def UnitInducedScaling (w : Scaling D) : Prop :=
  ∀ (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)),
    ∃ a : ∀ j, Factor D.Kt p (LocalTheory.tuple D.placeSect _ c j),
      ((w.u i p c : (Comp D i p c)ˣ) : Comp D i p c) = PiTensorProduct.tprod ℚ_[p] a ∧
        ∀ j, FactorUnitInduced (a j)

/-- **Unit-induced Kummer identifications are log-shell compatible** (the derivation of P19's
`LogShellCompat`). -/
theorem logShellCompat_of_unitInduced {w : Scaling D} (hw : UnitInducedScaling D w) :
    LogShellCompat D w := by
  refine logShellCompat_of_comp D w fun i p c => ?_
  obtain ⟨a, ha, hu⟩ := hw i p c
  rw [ha, ← Set.image_smul]
  exact tprod_image_tensorLogShell_of_unitInduced _ a hu

/-- Unit-induced Kummer identifications preserve log-volume (C11). -/
theorem shift_eq_zero_of_unitInduced {w : Scaling D} (hw : UnitInducedScaling D w) :
    shift D w = 0 :=
  shift_eq_zero_of_logShellCompat D (logShellCompat_of_unitInduced D hw)

theorem unitInducedScaling_one : UnitInducedScaling D 1 := fun _ _ _ =>
  ⟨1, by rw [Scaling.one_u, Units.val_one]; rfl, fun _ => factorUnitInduced_one⟩

/-- **The alien identification `x ↦ −x` at the bad primes is unit-induced** (by the inversion
`u ↦ u⁻¹` of the units in the factor of the label `1`). -/
theorem unitInducedScaling_negScale : UnitInducedScaling D (negScale D) := by
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
        exact factorUnitInduced_neg_one
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact factorUnitInduced_one
  · refine ⟨1, ?_, fun _ => factorUnitInduced_one⟩
    change ((if (p : ℕ) ∈ D.badChars then (-1 : (Comp D i p c)ˣ) else 1 : (Comp D i p c)ˣ) :
      Comp D i p c) = _
    rw [if_neg hp, Units.val_one]
    rfl

/-- **The `q`-power identifications are not unit-induced.** -/
theorem not_unitInducedScaling_qScale_zpow {m : ℤ} (hm : m ≠ 0) :
    ¬ UnitInducedScaling D (qScale D ^ m) := fun h =>
  not_logShellCompat_qScale_zpow D hm (logShellCompat_of_unitInduced D h)

/-! ### Kummer data on the log-theta-lattice -/

variable {D}

/-- **Unit-induced Kummer identifications at every vertex of a log-theta-lattice** (the Kummer
isomorphisms of IUT III, Theorem 3.11(ii)(a), in the model). -/
structure LatticeKummer (L : LogThetaLattice D) where
  /-- The Kummer identification of the container of the vertex `(n, m)`. -/
  kum : ℤ × ℤ → Scaling D
  /-- It is unit-induced. -/
  unit : ∀ a, UnitInducedScaling D (kum a)

namespace LatticeKummer

variable {L : LogThetaLattice D} (K : LatticeKummer L)

/-- The Kummer identifications are log-shell compatible. -/
theorem logShellCompat (a : ℤ × ℤ) : LogShellCompat D (K.kum a) :=
  logShellCompat_of_unitInduced D (K.unit a)

/-- **The `m`-th row as a P19 `LinkedChain`**: the hypothesis field `logShell` of P19 is now
derived. -/
def toLinkedChain (m : ℤ) : LinkedChain D :=
  ⟨L.row m, fun n => K.kum (n, m), fun n => K.logShellCompat (n, m)⟩

/-- **The multi-container model of the lattice**: P18's η-algorithm whose sides are the vertices
of the lattice, with the Kummer identifications `K.kum`. -/
def model : MultiContainer D := ⟨theaterAlg D L.H, K.kum⟩

theorem model_kummerVolCompat : K.model.KummerVolCompat := fun a =>
  shift_eq_zero_of_unitInduced D (K.unit a)

theorem model_volCompat : K.model.VolCompat :=
  K.model.volCompat_of_kummerVolCompat K.model_kummerVolCompat

/-- **The distortion between any two vertices is `0`**: along the Θ-links (horizontal), the
log-links (vertical), and any composite. -/
theorem distortion_eq_zero (a b : ℤ × ℤ) : K.model.distortion a b = 0 :=
  K.model.distortion_eq_zero_of_volCompat K.model_volCompat a b

theorem distortion_horiz (n m : ℤ) : K.model.distortion (n, m) (n + 1, m) = 0 :=
  K.distortion_eq_zero _ _

theorem distortion_vert (n m : ℤ) : K.model.distortion (n, m) (n, m + 1) = 0 :=
  K.distortion_eq_zero _ _

/-- The rows' models are the row restrictions of the lattice model. -/
theorem toLinkedChain_toModel_kum (m n : ℤ) :
    (K.toLinkedChain m).toModel.kum n = K.model.kum (n, m) := rfl

variable (L) in
/-- The trivial Kummer data (identity identifications). -/
def trivial : LatticeKummer L := ⟨fun _ => 1, fun _ => unitInducedScaling_one D⟩

open scoped Classical in
variable (L) in
/-- **Alien Kummer data**: `x ↦ −x` at the vertices with `n + m` odd, the identity elsewhere. The
transports along all arrows of the lattice are not ring isomorphisms, yet unit-induced. -/
def alt : LatticeKummer L :=
  ⟨fun a => if Even (a.1 + a.2) then 1 else negScale D, fun a => by
    split_ifs
    · exact unitInducedScaling_one D
    · exact unitInducedScaling_negScale D⟩

end LatticeKummer

end

end LogLink

end Iut
