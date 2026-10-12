/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.ThetaLink.PrimeStrip

/-!
# The Θ-link between `Θ^{±ell}NF`-Hodge theaters (IUT II, Corollary 4.10; IUT III, Def. 3.8)

IUT II, Corollary 4.10(iii) defines the `Θ^{×μ}_gau`-link `†HT → ‡HT` as **the full
poly-isomorphism** `†F^{⊩▶×μ}_gau ≅ ‡F^{⊩▶×μ}_Δ` of `F^{⊩▶×μ}`-prime-strips, and IUT III,
Definition 3.8(ii), the `Θ^{×μ}_LGP`-link in the same way with `†F^{⊩▶×μ}_LGP`. Both "map Θ-pilot
objects to `q`-pilot objects" (IUT III, Remark 3.8.1).

Here: `ThetaLinkIso H₁ H₂ := (gauStrip D H₁).Iso (qStrip D H₂)`, the set of all isomorphisms
(the full poly-isomorphism) from the Gaussian strip of `H₁` to the `q`-pilot strip of `H₂`.
In the model the LGP- and Gaussian strips coincide (their value-group portions are the same
realified Gaussian line; the LGP-monoids differ in their unit portions by the log-shells, which
the strips do not record), so `ThetaLinkLGP := ThetaLinkIso` (documented simplification;
IUT III, Remark 3.8.2: the results "generalize immediately").

## Results

* **It is a nonempty poly-isomorphism** (`nonempty_thetaLink`), as IUT II, Corollary 4.10(iii)
  ("[nonempty!] sets of isomorphisms").
* **Its indeterminacy is exactly the unit portion**: `unitEquiv : ThetaLinkIso H₁ H₂ ≃
  H₁.Fmu.Iso H₂.Fmu` — every element is determined by its unit portion, and the unit portions of
  the elements are *all* isomorphisms of the `F^{⊢×μ}`-prime-strips (IUT II, Corollary 4.10(iv):
  the poly-isomorphism induced on `F^{⊢×μ}` "coincides with the full poly-isomorphism"); the
  value-group portion is unique and equal to the wall's `Wall.thetaLink` (`val_eq`).
* **The value-group portion maps the Θ-pilot to the `q`-pilot** (`map_pilot`) and **rescales
  degrees by `1/s`**: `deg_q(λ x) = s⁻¹·deg_Θ(x)` (`val_apply`, from
  `Wall.degTheta_eq_smul_thetaLink`); on pilots, `deg_Θ(Θ-pilot) = s·|log q|` and
  `deg_q(q-pilot) = |log q|` (`pilot_degrees`).
* **Frobenioid realization** (P15): the realified Frobenioid degrees of the Θ- and `q`-pilot
  objects of `C^⊩` are the degrees of the two pilots (`frobenioid_degrees`); the pilot objects
  are not isomorphic in `C^⊩` (`not_iso_in_frobenioid`), and among the `ℝ_{>0}`-scalings of
  `C^⊩` exactly `1/s` carries the Θ-pilot object to the `q`-pilot object
  (`scaling_iff`). So the value-group portion of the Θ-link is *not* an isomorphism inside one
  Frobenioid; it is the `1/s`-scaling ("a sort of Frobenius morphism", IUT II, Remark
  4.10.3(ii)).
* **The `D-Θ^{±ell}NF`-link** (IUT II, Corollary 4.10(iv)): `dLink λ := λ.unit`, the full
  poly-isomorphism of unit portions (`dLink_surjective`).
* **Compatibility with isomorphisms of Hodge theaters** (symmetries): isomorphisms
  `H₁ ≅ H₁'`, `H₂ ≅ H₂'` induce a bijection of Θ-links (`congr`), compatible with the
  `D`-links (`dLink_congr`). The Θ-link from `H₁` to `H₂` only depends on `H₁`, `H₂` up to
  isomorphism (`Nonempty` of `congr`).
* **The BPS-level Θ-link of the wall** is induced (`toWallLink`): every Θ-link between
  theaters `H h₁`, `H h₂` gives a BPS isomorphism `thetaBPS h₁ ≅ qBPS h₂` of the η-algorithm
  `HodgeTheater.theaterAlg D H`.
* **Frobenius-pictures** (IUT II, Corollary 4.10(vi)): `FrobeniusPicture D`, a chain
  `n ↦ ⁿHT` with Θ-links `ⁿHT → ⁿ⁺¹HT`; one exists over the theaters built from `D`
  (`FrobeniusPicture.ofData`); its oriented graph `n → n + 1` has only translation
  symmetries (`arrow_aut_eq_add`), in particular no automorphism switching two adjacent
  vertices (`not_swap_adjacent`).
-/

noncomputable section

namespace Iut

namespace ThetaLink

open HodgeTheater Wall NumberField CategoryTheory Frobenioid

variable (D : InitialThetaData.{0})

/-- **The `Θ^{×μ}_gau`-link** `H₁ → H₂` (IUT II, Corollary 4.10(iii)): the full poly-isomorphism
`†F^{⊩▶×μ}_gau ≅ ‡F^{⊩▶×μ}_Δ`, i.e. the set of all its constituent isomorphisms. -/
abbrev ThetaLinkIso (H₁ H₂ : ThetaPmEllNFHT D) : Type := (gauStrip D H₁).Iso (qStrip D H₂)

/-- **The `Θ^{×μ}_LGP`-link** (IUT III, Definition 3.8(ii)); in the model it is the
`Θ^{×μ}_gau`-link (see the module docstring). -/
abbrev ThetaLinkLGP (H₁ H₂ : ThetaPmEllNFHT D) : Type := ThetaLinkIso D H₁ H₂

variable {D}

/-- **The Θ-link is a nonempty poly-isomorphism.** -/
theorem nonempty_thetaLink (H₁ H₂ : ThetaPmEllNFHT D) : Nonempty (ThetaLinkIso D H₁ H₂) :=
  (RlfMuStrip.nonempty_iso_iff _ _).mpr (PF_thetaVal D.bpsDegrees D.wallS_ne_zero)

namespace ThetaLinkIso

variable {H₁ H₂ : ThetaPmEllNFHT D}

/-- **The indeterminacy of the Θ-link is exactly the unit portion**: the Θ-links correspond to
the isomorphisms of the `F^{⊢×μ}`-prime-strips. -/
def unitEquiv (H₁ H₂ : ThetaPmEllNFHT D) : ThetaLinkIso D H₁ H₂ ≃ H₁.Fmu.Iso H₂.Fmu :=
  RlfMuStrip.isoEquivUnit (nonempty_thetaLink H₁ H₂)

/-- **The value-group portion of every Θ-link is the wall's `thetaLink`.** -/
theorem val_eq (lk : ThetaLinkIso D H₁ H₂) :
    lk.val = Wall.thetaLink D.bpsDegrees D.wallS_ne_zero :=
  (ValBPS.valIso_subsingleton _ _).elim _ _

/-- **The Θ-link maps the Θ-pilot to the `q`-pilot** (IUT III, Remark 3.8.1). -/
theorem map_pilot (lk : ThetaLinkIso D H₁ H₂) :
    lk.val.toLinearEquiv (gauStrip D H₁).pilot = (qStrip D H₂).pilot :=
  RlfMuStrip.Iso.map_pilot lk

/-- The coordinate of the `q`-pilot line `C = ℝ`. -/
def qCoord {H : ThetaPmEllNFHT D} (y : (qStrip D H).val.C) : ℝ := y

/-- **The value-group portion rescales degrees by `1/s`**: in the degree coordinate of the
Θ-pilot line (`Wall.degTheta`) and the coordinate of the `q`-pilot line `ℝ`,
`λ x = s⁻¹·deg_Θ(x)`. -/
theorem val_apply (lk : ThetaLinkIso D H₁ H₂) (x : (gauStrip D H₁).val.C) :
    qCoord (lk.val.toLinearEquiv x) = D.wallS⁻¹ * degTheta D.bpsDegrees D.wallS_ne_zero x := by
  have h := LinearMap.congr_fun (degTheta_eq_smul_thetaLink D.bpsDegrees D.wallS_ne_zero) x
  rw [val_eq]
  change degTheta D.bpsDegrees D.wallS_ne_zero x = D.wallS *
    qCoord (H := H₂) ((Wall.thetaLink D.bpsDegrees D.wallS_ne_zero).toLinearEquiv x) at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ D.wallS_ne_zero, one_mul]
  rfl

/-- **The pilot degrees on the two sides of the Θ-link**: `s·|log q|` on the Θ-side,
`|log q|` on the `q`-side. -/
theorem pilot_degrees (lk : ThetaLinkIso D H₁ H₂) :
    degTheta D.bpsDegrees D.wallS_ne_zero (gauStrip D H₁).pilot = D.wallS * D.qPilot.absLogQ ∧
      qCoord (lk.val.toLinearEquiv (gauStrip D H₁).pilot) = D.qPilot.absLogQ := by
  refine ⟨degTheta_pilot_gauStrip D H₁, ?_⟩
  rw [map_pilot]
  exact pilot_qStrip D H₂

/-- **The value-group portion does not preserve degrees** (`s ≠ 1`): no Θ-link is compatible
with the degree maps of the two lines. -/
theorem val_not_degree_preserving (lk : ThetaLinkIso D H₁ H₂) :
    ¬ ∀ x, qCoord (lk.val.toLinearEquiv x) = degTheta D.bpsDegrees D.wallS_ne_zero x := by
  intro h
  have h1 := h (gauStrip D H₁).pilot
  rw [(pilot_degrees lk).1, (pilot_degrees lk).2] at h1
  have hq := Frobenioid.absLogQ_pos D
  have hs := D.one_lt_wallS
  nlinarith [mul_lt_mul_of_pos_right hs hq]

/-- **The `D-Θ^{±ell}NF`-link** (IUT II, Corollary 4.10(iv)): the induced isomorphism of the
coric `F^{⊢×μ}`-prime-strips. -/
def dLink (lk : ThetaLinkIso D H₁ H₂) : H₁.Fmu.Iso H₂.Fmu := lk.unit

/-- **The `D`-links of the Θ-links form the full poly-isomorphism of `F^{⊢×μ}`-prime-strips.** -/
theorem dLink_surjective : Function.Surjective (dLink : ThetaLinkIso D H₁ H₂ → _) :=
  (unitEquiv H₁ H₂).surjective

/-- **Compatibility with isomorphisms of Hodge theaters**: `f : H₁ ≅ H₁'`, `g : H₂ ≅ H₂'` carry
Θ-links `H₁ → H₂` bijectively to Θ-links `H₁' → H₂'`. -/
def congr {H₁' H₂' : ThetaPmEllNFHT D} (f : H₁.Iso H₁') (g : H₂.Iso H₂') :
    ThetaLinkIso D H₁ H₂ ≃ ThetaLinkIso D H₁' H₂' where
  toFun lk := ⟨PrimeStrip.Iso.trans f.Fmu.symm (PrimeStrip.Iso.trans lk.unit g.Fmu), lk.val⟩
  invFun μ := ⟨PrimeStrip.Iso.trans f.Fmu (PrimeStrip.Iso.trans μ.unit g.Fmu.symm), μ.val⟩
  left_inv lk := by
    obtain ⟨u, v⟩ := lk
    simp only [RlfMuStrip.Iso.mk.injEq, and_true]
    exact FMuIso.conj_cancel f.Fmu g.Fmu u
  right_inv μ := by
    obtain ⟨u, v⟩ := μ
    simp only [RlfMuStrip.Iso.mk.injEq, and_true]
    exact FMuIso.conj_cancel' f.Fmu g.Fmu u

/-- The `D`-link of the transported Θ-link is the transported `D`-link. -/
theorem dLink_congr {H₁' H₂' : ThetaPmEllNFHT D} (f : H₁.Iso H₁') (g : H₂.Iso H₂')
    (lk : ThetaLinkIso D H₁ H₂) :
    dLink (congr f g lk) =
      PrimeStrip.Iso.trans f.Fmu.symm (PrimeStrip.Iso.trans (dLink lk) g.Fmu) :=
  rfl

/-- **The Θ-link depends on the theaters only up to isomorphism.** -/
theorem nonempty_congr (H₁' H₂' : ThetaPmEllNFHT D) :
    Nonempty (ThetaLinkIso D H₁ H₂ ≃ ThetaLinkIso D H₁' H₂') :=
  ⟨congr (ThetaPmEllNFHT.nonempty_iso H₁ H₁').some (ThetaPmEllNFHT.nonempty_iso H₂ H₂').some⟩

/-- **The BPS-level Θ-link of the wall induced by a Θ-link** between theaters of a family. -/
def toWallLink {σ : Type} [Nonempty σ] (H : σ → ThetaPmEllNFHT D) {h₁ h₂ : σ}
    (lk : ThetaLinkIso D (H h₁) (H h₂)) :
    BPS.Iso ((theaterAlg D H).thetaBPS h₁) ((theaterAlg D H).qBPS h₂) :=
  lk.toBPS

/-- The induced BPS isomorphism has the wall's `thetaLink` as value-group portion. -/
theorem toWallLink_val {σ : Type} [Nonempty σ] (H : σ → ThetaPmEllNFHT D) {h₁ h₂ : σ}
    (lk : ThetaLinkIso D (H h₁) (H h₂)) :
    (toWallLink H lk).val = Wall.thetaLink D.bpsDegrees D.wallS_ne_zero :=
  val_eq lk

end ThetaLinkIso

/-! ### Frobenioid realization of the pilots (P15) -/

variable (D)

/-- **The realified Frobenioid degrees of the pilot objects are the degrees of the pilots**:
`deg(Θ-pilot object) = deg_Θ(Θ-pilot)`, `deg(q-pilot object) = q-pilot`. -/
theorem frobenioid_degrees (H₁ H₂ : ThetaPmEllNFHT D) :
    (thetaPilotObj D).degreeNorm = degTheta D.bpsDegrees D.wallS_ne_zero (gauStrip D H₁).pilot ∧
      (qPilotObj D).degreeNorm = (qStrip D H₂).pilot :=
  ⟨degreeNorm_thetaPilotObj_eq_degTheta D, degreeNorm_qPilotObj_eq_pilot D⟩

/-- **The Θ-pilot and `q`-pilot objects are not isomorphic in the global realified Frobenioid**:
the Θ-link is not realized by an isomorphism inside one `C^⊩`. -/
theorem not_iso_in_frobenioid : IsEmpty (thetaPilotObj D ≅ qPilotObj D) :=
  isEmpty_iso_thetaPilot_qPilot D

/-- **Exactly the `ℝ_{>0}`-scaling `1/s` carries the Θ-pilot object to the `q`-pilot object**
(IUT II, Corollary 4.10(v): the `ℝ_{>0}`-orbits of the identifications of the global realified
Frobenioids). -/
theorem scaling_iff (c : ℝ) (hc : 0 < c) :
    Nonempty ((GlobalRealified.scale c hc).obj (thetaPilotObj D) ≅ qPilotObj D) ↔
      c = (D.wallS)⁻¹ :=
  nonempty_iso_scale_iff D c hc

/-! ### Frobenius-pictures (IUT II, Corollary 4.10(vi)) -/

/-- **A Frobenius-picture**: a chain of `Θ^{±ell}NF`-Hodge theaters `n ↦ ⁿHT` (`n ∈ ℤ`) with
Θ-links `ⁿHT → ⁿ⁺¹HT`. -/
structure FrobeniusPicture where
  /-- The Hodge theaters. -/
  H : ℤ → ThetaPmEllNFHT D
  /-- The Θ-links. -/
  link : ∀ n, ThetaLinkIso D (H n) (H (n + 1))

/-- **The Frobenius-picture over the theaters built from `D`** (`HodgeTheater.chain`). -/
def FrobeniusPicture.ofData : FrobeniusPicture D :=
  ⟨chain D, fun n => (nonempty_thetaLink (chain D n) (chain D (n + 1))).some⟩

/-- **The oriented graph `… → • → • → …` has only translations**: a permutation of `ℤ`
carrying arrows `n → n + 1` to arrows is `n ↦ n + σ 0`. -/
theorem arrow_aut_eq_add (σ : ℤ ≃ ℤ) (hσ : ∀ n, σ (n + 1) = σ n + 1) (n : ℤ) : σ n = n + σ 0 := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih => rw [hσ, ih]; ring
  | pred k ih =>
    have h := hσ (-(k : ℤ) - 1)
    rw [show -(k : ℤ) - 1 + 1 = -k by ring, ih] at h
    linarith

/-- **No symmetry switches two adjacent vertices** (IUT II, Corollary 4.10(vi)). -/
theorem not_swap_adjacent (σ : ℤ ≃ ℤ) (hσ : ∀ n, σ (n + 1) = σ n + 1) (m : ℤ) :
    ¬ (σ m = m + 1 ∧ σ (m + 1) = m) := by
  rintro ⟨h1, h2⟩
  rw [hσ, h1] at h2
  linarith

end ThetaLink

end Iut
