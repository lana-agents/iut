/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.PmBridge
import Iut.HodgeTheater.PrimeStrip

/-!
# `Θ^{±ell}NF`-Hodge theaters (IUT I, Definitions 6.11, 6.13; Remark 6.12.2)

* **`D-Θ^{±ell}NF`-Hodge theaters, label layer** (`DThetaPmEllNFHT`, Definition 6.13(ii)): a
  `D-Θ^{±ell}`-Hodge theater and a `D-NF`-bridge on the index set `T^* = |T| \ {0}` which, together
  with the `D-Θ`-bridge constructed from the `D-Θ^±`-bridge by Proposition 6.7, form a
  `D-ΘNF`-Hodge theater (`toThetaNF`); the gluing isomorphism is unique (Remark 6.12.2(ii),
  Proposition 4.8(ii)). Isomorphisms: `DThetaPmEllNFHT.isoEquiv : Iso A B ≃ {±1}` (the analogue of
  Proposition 6.6(iii), Remark 6.12.2(ii)).
* **`Θ^{±ell}NF`-Hodge theaters** (`ThetaPmEllNFHT D`, Definition 6.13(i)) relative to initial
  Θ-data `D`: the label layer, with the objects built from `D` (`PrimeStrip.lean`) attached:
  `F`-prime-strips `†F_t` (`t ∈ T`), `†F_≻` and `†F_>`, the global `†D^⊚`, `†D^⊚±`, the
  `F^⊩`-prime-strip of the `ΘNF`-part and the `F^{⊢×μ}`-prime-strip of `†F_≻` (IUT II, Definition
  4.9, used by the Θ-link). Isomorphisms: an isomorphism of the label layers with isomorphisms of
  the attached objects along it; **every isomorphism of the associated `D-Θ^{±ell}NF`-Hodge
  theaters lifts** (`toLabels_surjective`; the surjectivity half of IUT I, Corollaries 5.6(ii),
  6.12(i); uniqueness of the lift is Frobenioid-theoretic, [FrdI] / IUT I Corollary 5.3, and is not
  claimed, since the objects are recorded up to equivalence).
* **The theater built from `D`** (`ofData D`): the models of Examples 4.3, 4.4, 6.2, 6.3 and the
  tautological prime-strips; any two theaters are isomorphic (`nonempty_iso`).
* Its processions: `procPm` (the `±`-label procession, Proposition 6.9) and `procStar` (the
  procession of the `D-Θ`-bridge, Proposition 4.11), related by `starToPm` (Proposition 6.9(iii)).
-/

namespace Iut

namespace HodgeTheater

open PmTorsor

universe u

/-- The prime `ℓ` of initial Θ-data is an odd prime (`≥ 5`). -/
instance (D : InitialThetaData.{u}) : OddPrime D.ℓ :=
  ⟨D.prime.ℓ_prime, by have := D.prime.five_le; change 2 < D.prime.ℓ; omega⟩

variable {ℓ : ℕ} [OddPrime ℓ] {V : Type u}

/-! ### `D-Θ^{±ell}NF`-Hodge theaters -/

variable (ℓ V) in
/-- **A `D-Θ^{±ell}NF`-Hodge theater, label layer** (IUT I, Definition 6.13(ii)). -/
structure DThetaPmEllNFHT where
  /-- The `D-Θ^{±ell}`-Hodge theater. -/
  toPmEll : DThetaPmEllHT ℓ V
  /-- `LabCusp(†D^⊚)` of the `D-NF`-bridge. -/
  lab : StarTorsor ℓ
  /-- The `D-NF`-bridge on `T^* = |T| \ {0}`. -/
  ν : {a : AbsFl ℓ // a ≠ 0} ≃ lab.carrier
  /-- The `D-ΘNF`-Hodge theater condition, relative to the `D-Θ`-bridge of Proposition 6.7. -/
  γ₀ : StarTorsor.Iso (StarTorsor.std ℓ) lab
  γ₀_apply : ∀ x, γ₀ x = ν ((nonzeroAbsEquiv ℓ).symm x)

namespace DThetaPmEllNFHT

variable {A B : DThetaPmEllNFHT ℓ V}

/-- **The glued `D-ΘNF`-Hodge theater** (Remark 6.12.2): the `D-NF`-bridge with the `D-Θ`-bridge
constructed from the `D-Θ^±`-bridge (Proposition 6.7). -/
noncomputable def toThetaNF (A : DThetaPmEllNFHT ℓ V) : DThetaNFHT ℓ :=
  ⟨{a : AbsFl ℓ // a ≠ 0}, A.lab, A.ν, nonzeroAbsEquiv ℓ, A.γ₀, A.γ₀_apply⟩

/-- The `D-Θ`-bridge of the glued theater is the one of Proposition 6.7. -/
theorem toThetaNF_toTheta (A : DThetaPmEllNFHT ℓ V) :
    A.toThetaNF.toTheta = A.toPmEll.toPm.toTheta := rfl

/-- **An isomorphism of `D-Θ^{±ell}NF`-Hodge theaters**: an isomorphism of the
`D-Θ^{±ell}`-Hodge theaters and one of the glued `D-ΘNF`-Hodge theaters, compatible with the
gluing (the latter induces on `T^*` the map induced by the former, i.e. the identity of `T^*`,
`DThetaPmBridge.toThetaIso_σ`). -/
structure Iso (A B : DThetaPmEllNFHT ℓ V) where
  /-- The isomorphism of `D-Θ^{±ell}`-Hodge theaters. -/
  pmEll : A.toPmEll.Iso B.toPmEll
  /-- The isomorphism of `D-ΘNF`-Hodge theaters. -/
  nf : A.toThetaNF.Iso B.toThetaNF
  glue : ∀ a, nf.σ a = a

/-- The gluing isomorphism is unique, and compatible (Remark 6.12.2(ii)). -/
theorem nf_σ (f : A.toThetaNF.Iso B.toThetaNF) (a : A.toThetaNF.J) : f.σ a = a :=
  (nonzeroAbsEquiv ℓ).injective (f.compat_χ a)

/-- **Isomorphisms of `D-Θ^{±ell}NF`-Hodge theaters form a `{±1}`-torsor** (the analogue of IUT I,
Proposition 6.6(iii), Remark 6.12.2(ii)). -/
noncomputable def isoEquivPmEll (A B : DThetaPmEllNFHT ℓ V) :
    A.Iso B ≃ A.toPmEll.Iso B.toPmEll where
  toFun f := f.pmEll
  invFun g := ⟨g, default, nf_σ default⟩
  left_inv f := by
    obtain ⟨g, n, h⟩ := f
    simp only [Iso.mk.injEq, true_and]
    exact Subsingleton.elim _ _
  right_inv _ := rfl

/-- **IUT I, Proposition 6.6(iii) for `D-Θ^{±ell}NF`-Hodge theaters.** -/
noncomputable def isoEquiv (A B : DThetaPmEllNFHT ℓ V) : A.Iso B ≃ ℤˣ :=
  (isoEquivPmEll A B).trans (DThetaPmEllHT.isoEquiv _ _)

theorem card_iso (A B : DThetaPmEllNFHT ℓ V) : Nat.card (A.Iso B) = 2 := by
  rw [Nat.card_congr (isoEquiv A B), Nat.card_eq_fintype_card]
  rfl

variable (ℓ V) in
/-- **The model `D-Θ^{±ell}NF`-Hodge theater** (Examples 4.3, 4.4, 6.2, 6.3). -/
noncomputable def model : DThetaPmEllNFHT ℓ V where
  toPmEll := DThetaPmEllHT.model ℓ V
  lab := StarTorsor.std ℓ
  ν := nonzeroAbsEquiv ℓ
  γ₀ := StarTorsor.Iso.refl _
  γ₀_apply x := by simp [StarTorsor.Iso.refl]

/-- **The `ℓ±`-procession of a `D-Θ^{±ell}NF`-Hodge theater** (IUT I, Proposition 6.9(i)): the
capsules of `±`-labels `S^±_1 ⊆ ⋯ ⊆ S^±_{ℓ±}` of `|T| ≅ |F_ℓ|`. -/
noncomputable def procPm (_A : DThetaPmEllNFHT ℓ V) : Procession (AbsFl ℓ) := prcPm ℓ

/-- **The `ℓ*`-procession of its `D-Θ`-bridge** (IUT I, Proposition 4.11(i)). -/
noncomputable def procStar (A : DThetaPmEllNFHT ℓ V) : Procession A.toThetaNF.J :=
  A.toThetaNF.toTheta.prc

/-- **IUT I, Proposition 6.9(iii)**: the `ℓ*`-procession of the `D-Θ`-bridge maps to the
`ℓ±`-procession, `S^*_j ↪ S^±_{j+1}`, by the inclusion `T^* ⊆ |T|`. -/
theorem procStar_subset_procPm (A : DThetaPmEllNFHT ℓ V) (j : Fin (ellStar ℓ)) :
    ∀ a ∈ (A.procStar.capsule j).labels,
      a.1 ∈ (A.procPm.capsule (succEmb (ellStar ℓ) j)).labels := by
  intro a ha
  classical
  change a ∈ (sStar ℓ (j + 1)).map (nonzeroAbsEquiv ℓ).symm.toEmbedding at ha
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
  have h := starToAbs_nonzeroAbsEquiv ℓ ((nonzeroAbsEquiv ℓ).symm x)
  rw [Equiv.apply_symm_apply] at h
  change ((nonzeroAbsEquiv ℓ).symm x).1 ∈ _
  rw [← h]
  exact (starToPm ℓ).maps_to j x hx

end DThetaPmEllNFHT

/-! ### `Θ^{±ell}NF`-Hodge theaters relative to initial Θ-data -/

variable (D : InitialThetaData.{u})

/-- **A `Θ^{±ell}NF`-Hodge theater** relative to initial Θ-data `D` (IUT I, Definition 6.13(i);
see the module docstring for the encoding). -/
structure ThetaPmEllNFHT where
  /-- The associated `D-Θ^{±ell}NF`-Hodge theater (label layer). -/
  labels : DThetaPmEllNFHT D.ℓ (Vp D)
  /-- The `F`-prime-strips `†F_t` of the capsule of the `Θ^±`-bridge (Definition 6.11(i)). -/
  F : labels.toPmEll.T.carrier → FStrip D
  /-- The target `†F_≻` of the `Θ^±`-bridge. -/
  Fsucc : FStrip D
  /-- The target `†F_>` of the `Θ`-bridge (glued to `†F_≻` by Proposition 6.7). -/
  Fgt : FStrip D
  /-- `†D^⊚` of the `NF`-bridge. -/
  Dcirc : DCirc D
  /-- `†D^⊚±` of the `Θ^ell`-bridge. -/
  DcircPm : DCircPm D
  /-- The `F^⊩`-prime-strip of the `ΘNF`-part (IUT I, Definition 5.5). -/
  Frlf : FRlfStrip D
  /-- The `F^{⊢×μ}`-prime-strip of `†F_≻` (IUT II, Definition 4.9). -/
  Fmu : FMuStrip D

namespace ThetaPmEllNFHT

variable {D}

/-- **An isomorphism of `Θ^{±ell}NF`-Hodge theaters**: an isomorphism of the associated
`D-Θ^{±ell}NF`-Hodge theaters with isomorphisms of the attached objects along it. -/
structure Iso (A B : ThetaPmEllNFHT D) where
  /-- The isomorphism of the label layers. -/
  labels : A.labels.Iso B.labels
  /-- The capsule of `F`-prime-strips, along the map of index sets. -/
  F : ∀ t, (A.F t).Iso (B.F (labels.pmEll.σ.1 t))
  /-- `†F_≻ ≅ ‡F_≻`. -/
  Fsucc : A.Fsucc.Iso B.Fsucc
  /-- `†F_> ≅ ‡F_>`. -/
  Fgt : A.Fgt.Iso B.Fgt
  /-- `†D^⊚ ≅ ‡D^⊚`. -/
  Dcirc : A.Dcirc.G.carrier ≃ₜ* B.Dcirc.G.carrier
  /-- `†D^⊚± ≅ ‡D^⊚±`. -/
  DcircPm : A.DcircPm.G.carrier ≃ₜ* B.DcircPm.G.carrier
  /-- `†C^⊩ ≃ ‡C^⊩`. -/
  Crlf : A.Frlf.C ≌ B.Frlf.C
  /-- The `F^⊢`-prime-strips of the `F^⊩`-prime-strips. -/
  Frlf : A.Frlf.strip.Iso B.Frlf.strip
  /-- The `F^{⊢×μ}`-prime-strips. -/
  Fmu : A.Fmu.Iso B.Fmu

/-- **Every isomorphism of the associated `D-Θ^{±ell}NF`-Hodge theaters lifts to an isomorphism of
`Θ^{±ell}NF`-Hodge theaters** (IUT I, Corollaries 5.6(ii), 6.12(i), surjectivity). -/
theorem toLabels_surjective (A B : ThetaPmEllNFHT D) :
    Function.Surjective (fun f : A.Iso B => f.labels) := by
  intro g
  refine ⟨⟨g, fun t => (PrimeStrip.nonempty_iso _ _).some,
    (PrimeStrip.nonempty_iso _ _).some, (PrimeStrip.nonempty_iso _ _).some,
    (A.Dcirc.iso_model.some.trans B.Dcirc.iso_model.some.symm),
    (A.DcircPm.iso_model.some.trans B.DcircPm.iso_model.some.symm),
    (A.Frlf.equiv_model.some.trans B.Frlf.equiv_model.some.symm),
    (PrimeStrip.nonempty_iso _ _).some, (PrimeStrip.nonempty_iso _ _).some⟩, rfl⟩

/-- **Any two `Θ^{±ell}NF`-Hodge theaters are isomorphic**, and the isomorphisms induce exactly the
two (`{±1}`) isomorphisms of the associated `D-Θ^{±ell}NF`-Hodge theaters. -/
theorem nonempty_iso (A B : ThetaPmEllNFHT D) : Nonempty (A.Iso B) := by
  obtain ⟨f, -⟩ := toLabels_surjective A B ((DThetaPmEllNFHT.isoEquiv _ _).symm 1)
  exact ⟨f⟩

variable (D) in
/-- **The `Θ^{±ell}NF`-Hodge theater built from `D`**: the model label layer (Examples 4.3, 4.4,
6.2, 6.3) with the tautological prime-strips and global objects. -/
noncomputable def ofData : ThetaPmEllNFHT D where
  labels := DThetaPmEllNFHT.model D.ℓ (Vp D)
  F _ := PrimeStrip.tautological _ _
  Fsucc := PrimeStrip.tautological _ _
  Fgt := PrimeStrip.tautological _ _
  Dcirc := DCirc.tautological D
  DcircPm := DCircPm.tautological D
  Frlf := FRlfStrip.tautological D
  Fmu := PrimeStrip.tautological _ _

/-- The index set of the theater built from `D` is `F_ℓ`; its `ℓ±`-procession has `ℓ±` capsules
and its last capsule is `|F_ℓ|` (`prcPm_last`). -/
theorem ofData_procPm_length : (ofData D).labels.procPm.length = ellPm D.ℓ := rfl

end ThetaPmEllNFHT

end HodgeTheater

end Iut
