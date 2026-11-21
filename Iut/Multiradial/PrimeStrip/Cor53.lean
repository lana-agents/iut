/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Transport

/-!
# IUT I, Corollary 5.3 (ii): surjectivity at `V^non` from two named inputs (MR21 R4, part)

IUT I, Corollary 5.3 (ii) (l.9891–9894 of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`): for `F`-prime-strips
`¹F`, `²F` with associated `D`-prime-strips `¹D`, `²D`, the natural map
`Isom(¹F, ²F) → Isom(¹D, ²D)` is bijective. The paper's proof cites [AbsTopIII],
Proposition 3.2 (iv) (`Topics in Absolute Anabelian Geometry III.txt` l.4111–4124: for an
MLF-Galois `TM`-pair `(Π ↷ M)` — `M ≅ O^▷` of an algebraic closure of a `p`-adic field —
`Isom_{C^MLF_TM}((Π ↷ M), (Π* ↷ M*)) → Isom_TG(Π, Π*)` is a bijection).

This file proves the **surjectivity** at `V^non` (`FStripNon.isoClassToD_surjective_of`) from:

* **`OrbitIsoRecon Π_v`**: every self-equivalence of `D_v = B^{(temp)}(Π_v)⁰` is isomorphic to the
  functor `Π_v/H ↦ Π_v/σ(H)` of an automorphism `σ` of the topological group `Π_v`. This is
  [Mzk2], Proposition 3.2 / [SemiAnbd], Proposition 3.2 in functorial form; the group
  isomorphism with compatible base points is formalised (`OrbitObj.exists_continuousMulEquiv`,
  profinite; `exists_continuousMulEquiv_temp`, tempered, given `PivCountable`), the passage from
  the base points to a natural isomorphism of functors is not yet (**MR21 debt R4a**);
* **`KummerLift D v`**: every automorphism `σ` of `Π_v` lifts to a `σ`-equivariant automorphism
  of the `Π_v`-module `\bar{ℚ}_p^×` (acting through `Π_v → G_v`) preserving `ord` — the
  surjectivity in [AbsTopIII], Proposition 3.2 (iv) for `T = TM` (an automorphism of
  `(Π_v ↷ O^▷_{\bar{ℚ}_p})` extends to the groupification `\bar{ℚ}_p^×`; it preserves `ord`, since
  it maps `O^▷` onto itself, hence scales `ord` by some `λ > 0`, and maps the `Π_v`-invariants
  `K_v^×` onto themselves, so `λ · ord(K_v^×) = ord(K_v^×)` forces `λ = 1`). A named input
  (lead decision 2026-11-03: AbsTopIII Prop 3.2 (iv) / Cor 1.10 at all levels is an MR9
  follow-up deliverable; **MR21 debt R4b**).

Given these, `cvFrob_autLift`: every automorphism of `D_v` lifts to an automorphism of the
Frobenioid `C_v` (`GaloisModel.isoOf σ ψ`, `Transport.lean`), and the surjectivity for all
`F`-prime-strips follows from the conjugation invariance `FrobCat.autLift_of_iso`.
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

/-- **Functorial reconstruction of automorphisms** ([Mzk2], Proposition 3.2; [SemiAnbd],
Proposition 3.2): every self-equivalence of `B(Γ)⁰` is isomorphic to the functor
`Γ/H ↦ Γ/σ(H)` of an automorphism `σ` of the topological group `Γ`. -/
def OrbitIsoRecon (Γ : Type) [Group Γ] [TopologicalSpace Γ] : Prop :=
  ∀ e : OrbitObj Γ ≌ OrbitObj Γ, ∃ σ : Γ ≃ₜ* Γ, Nonempty (e.functor ≅ OrbitObj.isoFunctor σ)

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-- **Lifting automorphisms of `Π_v` to the Kummer data** ([AbsTopIII], Proposition 3.2 (iv),
`T = TM`, surjectivity; see the module docstring): every automorphism `σ` of the topological
group `Π_v` admits a `σ`-equivariant automorphism `ψ` of `\bar{ℚ}_p^×` with `ord ∘ ψ = ord`. -/
def KummerLift : Prop :=
  ∀ σ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier, ∃ ψ : PiMul D v ≃+ PiMul D v,
    (∀ (g : (Piv D v).carrier) (m : PiMul D v), ψ (g • m) = σ g • ψ m) ∧
      ∀ m, ordPi D v (ψ m) = ordPi D v m

/-- **Automorphisms of `D_v` lift to `C_v`** (from `OrbitIsoRecon Π_v` and `KummerLift`). -/
theorem cvFrob_autLift (hrec : OrbitIsoRecon (Piv D v).carrier) (hk : KummerLift D v) :
    (cvFrob D v).AutLift := by
  intro e
  obtain ⟨σ, ⟨β⟩⟩ := hrec e
  obtain ⟨ψ, hψ, hψℓ⟩ := hk σ
  exact ⟨GaloisModel.isoOf (Γ := PAdicGalois.gammaQ) σ ψ hψ hψℓ, ⟨β.symm⟩⟩

variable {D}

/-- **IUT I, Corollary 5.3 (ii), surjectivity** (non-archimedean part), from the named inputs
`OrbitIsoRecon Π_v` (debt R4a) and `KummerLift` (debt R4b) at every `v ∈ V^non`:
`Isom(¹F, ²F) → Isom(¹D, ²D)` is surjective. -/
theorem FStripNon.isoClassToD_surjective_of
    (hrec : ∀ v : Vnon D, OrbitIsoRecon (Piv D v).carrier) (hk : ∀ v : Vnon D, KummerLift D v)
    (P Q : FStripNon D) :
    Function.Surjective (FStripNon.isoClassToD : P.IsoClass Q → P.toD.IsoClass Q.toD) :=
  FStripNon.isoClassToD_surjective (fun v => cvFrob_autLift D v (hrec v) (hk v)) P Q

end PrimeStrip

end Multiradial

end Iut
