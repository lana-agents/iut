/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.AutRigid
import Iut.Multiradial.PrimeStrip.KummerRigid
import Iut.Multiradial.PrimeStrip.OrbitIsoRecon
import Iut.Multiradial.PrimeStrip.KummerLiftPf
import Iut.Multiradial.PrimeStrip.Black

/-!
# IUT I, Corollary 5.3 (ii) at `V^non`: bijectivity (MR21 R3)

IUT I, Corollary 5.3 (ii) (l.9891–9894 of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`): for `F`-prime-strips
`¹F`, `²F` with associated `D`-prime-strips `¹D`, `²D`, the natural map
`Isom(¹F, ²F) → Isom(¹D, ²D)` is bijective; the proof (l.9937–9940) cites [AbsTopIII],
Proposition 3.2 (iv).

* **Injectivity** (`FStripNon.isoClassToD_injective_of_h3`): `C_v` satisfies `FrobCat.AutRigid`
  (`cvFrob_autRigid`, from `galFrob_autRigid` of `AutRigid.lean` with `Γ = ℚ`,
  `ord(\bar{ℚ}_p^×) ⊆ ℚ`, open stabilizers of elements of `\bar{ℚ}_p^×` in `Π_v`, `ord(p) = 1`,
  and `KummerRigid D v`, `KummerRigid.lean`), given the surjectivity of `Π_v → G_v` (debt H3).
* **Bijectivity** (`FStripNon.isoClassToD_bijective`): with the surjectivity of
  `OrbitIsoRecon.lean` (`PivCountable` at `V^bad` = MR18 `hctbl`) and MR9's `kummerLift`
  (AbsTopIII Proposition 3.2 (iv), from `DeltaCharacteristic` and H3).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

/-- Elements of `\bar{ℚ}_p^×` have open stabilizers in `G_K`. -/
theorem PAdicGalois.mul_stabilizer_isOpen {p : ℕ} [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (m : PAdicGalois.Mul p) :
    IsOpen (MulAction.stabilizer (PAdicGalois.GK p K) m : Set (PAdicGalois.GK p K)) := by
  have hst : (MulAction.stabilizer (PAdicGalois.GK p K) m : Set (PAdicGalois.GK p K)) =
      MulAction.stabilizer (PAdicGalois.GK p K)
        ((Additive.toMul m : (PadicAlgCl p)ˣ) : PadicAlgCl p) := by
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      have := congrArg (fun x : PAdicGalois.Mul p => ((Additive.toMul x : (PadicAlgCl p)ˣ) :
        PadicAlgCl p)) h
      simpa [PAdicGalois.smul_toMul] using this
    · intro h
      apply Additive.toMul.injective
      exact Units.ext (by simpa [PAdicGalois.smul_toMul] using h)
  rw [hst]
  exact stabilizer_isOpen_of_isIntegral _

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-- Elements of `\bar{ℚ}_p^×` have open stabilizers in `Π_v`. -/
theorem piMul_stabilizer_isOpen (m : PiMul D v) :
    IsOpen (MulAction.stabilizer (Piv D v).carrier m : Set (Piv D v).carrier) := by
  have : (MulAction.stabilizer (Piv D v).carrier m : Set (Piv D v).carrier) =
      piToG D v ⁻¹' (MulAction.stabilizer (Gv D v) (show PAdicGalois.Mul (pv D v) from m) :
        Set (Gv D v)) := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage]
    rfl
  rw [this]
  exact (PAdicGalois.mul_stabilizer_isOpen (Lv D v) m).preimage (continuous_piToG D v)

/-- **Rigidity of `C_v`** (IUT I, Corollary 5.3 (ii), injectivity at `v ∈ V^non`): every
automorphism of `C_v` whose base functor is isomorphic to the identity is 2-isomorphic to the
identity, given the surjectivity of `Π_v → G_v` (debt H3). -/
theorem cvFrob_autRigid (h3 : Function.Surjective (piToG D v)) : (cvFrob D v).AutRigid :=
  galFrob_autRigid (G := (Piv D v).carrier) (ℓ := ordPi D v) (hℓ := ordPi_smul D v)
    (Γ := PAdicGalois.gammaQ)
    (fun m => PAdicGalois.ord_mem_gammaQ (p := pv D v) (Additive.toMul m))
    (piMul_stabilizer_isOpen D v) (m0 := pMul D v)
    (by change (0 : ℝ) < PAdicGalois.ord (pv D v) (pMul D v); rw [ord_pMul]; exact one_pos)
    (fun g => pMul_fixed D v (piToG D v g)) gammaQ_scaling (kummerRigid D v h3)

variable {D}

/-- **IUT I, Corollary 5.3 (ii), injectivity** (non-archimedean part): `Isom(¹F, ²F) →
Isom(¹D, ²D)` is injective, given the surjectivity of `Π_v → G_v` at every `v ∈ V^non`
(debt H3). -/
theorem FStripNon.isoClassToD_injective_of_h3 (h3 : ∀ v : Vnon D, PiToGQuotient D v)
    (P Q : FStripNon D) :
    Function.Injective (FStripNon.isoClassToD : P.IsoClass Q → P.toD.IsoClass Q.toD) :=
  FStripNon.isoClassToD_injective (fun v => cvFrob_autRigid D v (h3 v).1) P Q

/-- **IUT I, Corollary 5.3 (ii)** (non-archimedean part): `Isom(¹F, ²F) → Isom(¹D, ²D)` is
bijective, given `DeltaCharacteristic` ([AbsAnab], Lemma 1.3.8), the quotient property of
`Π_v → G_v` (debt H3) and, at `v ∈ V^bad`, `PivCountable` (MR18 `hctbl`); `KummerLift` is
`kummerLift` (MR9, `KummerLiftPf.lean`). -/
theorem FStripNon.isoClassToD_bijective (hΔ : ∀ v : Vnon D, DeltaCharacteristic D v)
    (h3 : ∀ v : Vnon D, PiToGQuotient D v) (hc : ∀ v : Vnon D, v ∈ D.VBad → PivCountable D v)
    (P Q : FStripNon D) :
    Function.Bijective (FStripNon.isoClassToD : P.IsoClass Q → P.toD.IsoClass Q.toD) :=
  ⟨FStripNon.isoClassToD_injective_of_h3 h3 P Q,
    FStripNon.isoClassToD_surjective_of_kummerLift hc (fun v => kummerLift D v (hΔ v) (h3 v)) P Q⟩

end PrimeStrip

end Multiradial

end Iut
