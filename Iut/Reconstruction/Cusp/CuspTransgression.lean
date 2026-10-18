/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.CuspCentral
import LocalClassFieldTheory.Cohomology.CentralTransgression
import Pi1.Orbicurve.GaloisPi1

/-!
# The transgression of the cuspidally central extension ([AbsTopIII], Proposition 1.4(ii))

[AbsTopIII], Proposition 1.4(ii) (l.1771–1801 of `~/iut-scratch/papers/txt/Topics in Absolute
Anabelian Geometry III.txt`): "we have a natural exact sequence of profinite groups
`1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1` […]. Moreover, applying the differential of the
"`E₂`-term" of the Leray spectral sequence associated to this group extension to the element
`1 ∈ Ẑ = Hom(I_x, I_x) = H⁰(Δ_X, H¹(I_x, I_x))` yields an element
`∈ H²(Δ_X, H⁰(I_x, I_x)) = Hom(M_X, I_x)` […]; this last element corresponds to the natural
isomorphism `M_X ≅ I_x`". "In particular, this yields a "purely group-theoretic algorithm" […]
for constructing this isomorphism from the surjection `Δ_{U_x} ↠ Δ_X`."

For a profinite group `Δ` and a continuous homomorphism `π : Δ → Q` to a `T1` group, with
`Δ^{c-cn} = CuspCentral π` (`Iut/Reconstruction/Cusp/CuspCentral.lean`), this file builds, from
`π` alone:

* `cuspInertia π hπ = Ker(Δ^{c-cn} → Q)` (the image of `Ker π`: `cuspInertia_eq_map`), closed and
  central, and the exact sequence `1 → I → Δ^{c-cn} → Q → 1` (`cuspCentralMap_surjective`);
  `Δ^{c-cn}/I ≃ₜ* Q` (`cuspQuotEquiv`) for `Q` Hausdorff and `π` surjective;
* **the transgression** `cuspTg : Hom_cont(I, A) → H²(Δ^{c-cn}/I, A)` for every discrete
  `A` with trivial action (the differential `d₂` of the statement, LCFT `FiveTerm.tgCentral`),
  with its exactness properties (`cuspTg_eq_one_iff`, `exists_cuspTg_eq_of_inf₂_eq_one`) and
  naturality in `A` (`cuspTg_comp`);
* **the transgression of `1 ∈ Hom(I, I)` at finite level**: for an open subgroup `N ≤ I`, the
  class `cuspClass π hπ N = d₂(I ↠ I/N) ∈ H²(Δ^{c-cn}/I, I/N)` (the extension class modulo `N`).

**The Θ-approach** ([IUTchI], Remark 3.1.2(iii), l.4196–4213 of `… Inter-universal Teichmuller
Theory I.txt`): "the tautological extension `1 → Δ_Θ → Δ^Θ_X → Δ^ell_X → 1` — where
`Δ_Θ = [Δ_X, Δ_X]/[Δ_X, [Δ_X, Δ_X]]`; `Δ^Θ_X = Δ_X/[Δ_X, [Δ_X, Δ_X]]`; `Δ^ell_X = Δ^ab_X`. The
extension class `∈ H²(Δ^ell_X, Δ_Θ)` of this extension determines a tautological isomorphism
`M_X ≅ Δ_Θ`". This is the case `π = Δ ↠ Δ^ab` of the construction above: `thetaMap`,
`cuspCentralKer_thetaMap` (`Δ^Θ = Δ/cl⁅cl⁅Δ, Δ⁆, Δ⁆`), `thetaInertia_eq_map` (`Δ_Θ` is the image
of `cl⁅Δ, Δ⁆`), and `thetaClass N ∈ H²(Δ^Θ/Δ_Θ, Δ_Θ/N)`.

The identifications `H²(Π̂_{g,0}, Ẑ) ≅ Ẑ` and `M_X = Hom(H²(Δ_X, Ẑ), Ẑ) ≅ I_x` for the closed
surface group are in `Iut/Reconstruction/Cusp/SurfaceH2.lean`.
-/

namespace Iut.Reconstruction

open FiveTerm

/-! ### Trivial coefficients -/

/-- A type synonym of `A` on which every group acts trivially. -/
def TrivCoeff (A : Type*) : Type _ := A

namespace TrivCoeff

variable {A : Type*}

instance [CommGroup A] : CommGroup (TrivCoeff A) := inferInstanceAs (CommGroup A)
instance [TopologicalSpace A] : TopologicalSpace (TrivCoeff A) :=
  inferInstanceAs (TopologicalSpace A)
instance [TopologicalSpace A] [DiscreteTopology A] : DiscreteTopology (TrivCoeff A) :=
  inferInstanceAs (DiscreteTopology A)
instance [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] :
    IsTopologicalGroup (TrivCoeff A) := inferInstanceAs (IsTopologicalGroup A)

/-- The identity `A → TrivCoeff A`. -/
def of : A ≃ TrivCoeff A := Equiv.refl A

instance (E : Type*) [Monoid E] [CommGroup A] : MulDistribMulAction E (TrivCoeff A) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

lemma smul_eq (E : Type*) [Monoid E] [CommGroup A] (e : E) (a : TrivCoeff A) : e • a = a := rfl

instance (E : Type*) [Monoid E] [TopologicalSpace E] [CommGroup A] [TopologicalSpace A] :
    ContinuousSMul E (TrivCoeff A) := ⟨continuous_snd⟩

/-- A continuous homomorphism `B → A` as one into `TrivCoeff A`. -/
def homOf {B : Type*} [Group B] [TopologicalSpace B] [CommGroup A] [TopologicalSpace A]
    (φ : ContinuousMonoidHom B A) : ContinuousMonoidHom B (TrivCoeff A) := φ

end TrivCoeff

/-! ### The cuspidal inertia of `Δ^{c-cn}` -/

variable {Δ Q : Type*} [Group Δ] [TopologicalSpace Δ] [IsTopologicalGroup Δ] [Group Q]
  [TopologicalSpace Q] [T1Space Q] (π : Δ →* Q) (hπ : Continuous π)

lemma continuous_cuspCentralMap : Continuous (cuspCentralMap π hπ) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr hπ

/-- **`I = Ker(Δ^{c-cn} → Q)`**, the cuspidal part of the maximal cuspidally central quotient
(`I_x` in [AbsTopIII], Proposition 1.4(ii)). -/
abbrev cuspInertia : Subgroup (CuspCentral π) := (cuspCentralMap π hπ).ker

lemma isClosed_cuspInertia : IsClosed (cuspInertia π hπ : Set (CuspCentral π)) :=
  isClosed_ker _ (continuous_cuspCentralMap π hπ)

lemma cuspInertia_central : ∀ i ∈ cuspInertia π hπ, ∀ e : CuspCentral π, e * i = i * e :=
  fun _ hi e => (Subgroup.mem_center_iff.mp (ker_cuspCentralMap_le_center π hπ hi) e)

/-- `I` is the image of `Ker π`. -/
theorem cuspInertia_eq_map : cuspInertia π hπ = π.ker.map (QuotientGroup.mk' _) := by
  ext x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [MonoidHom.mem_ker, cuspCentralMap_mk, Subgroup.mem_map, QuotientGroup.mk'_apply]
  constructor
  · exact fun h => ⟨a, h, rfl⟩
  · rintro ⟨b, hb, hba⟩
    rw [QuotientGroup.eq] at hba
    have := cuspCentralKer_le_ker_self π hπ hba
    rw [MonoidHom.mem_ker, map_mul, map_inv, hb, inv_one, one_mul] at this
    exact this

/-- `Δ^{c-cn} → Q` is surjective if `π` is: the sequence `1 → I → Δ^{c-cn} → Q → 1` is exact. -/
theorem cuspCentralMap_surjective (hs : Function.Surjective π) :
    Function.Surjective (cuspCentralMap π hπ) := fun q => by
  obtain ⟨a, rfl⟩ := hs q
  exact ⟨QuotientGroup.mk a, rfl⟩

/-- `I` is abelian (it is central). -/
instance cuspInertia_isMulCommutative : IsMulCommutative (cuspInertia π hπ) :=
  ⟨⟨fun a b => Subtype.ext (cuspInertia_central π hπ b b.2 a)⟩⟩

open scoped IsMulCommutative

section Profinite

variable [CompactSpace Δ] [TotallyDisconnectedSpace Δ]

instance : TotallyDisconnectedSpace (CuspCentral π) :=
  QuotientGroup.totallyDisconnectedSpace_of_isClosed _ (Subgroup.isClosed_topologicalClosure _)

/-- **`Δ^{c-cn}/I ≃ₜ* Q`** for `π` surjective onto a Hausdorff `Q`. -/
noncomputable def cuspQuotEquiv [T2Space Q] (hs : Function.Surjective π) :
    (CuspCentral π ⧸ cuspInertia π hπ) ≃ₜ* Q :=
  let e := QuotientGroup.quotientKerEquivOfSurjective _ (cuspCentralMap_surjective π hπ hs)
  have hc : Continuous e :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (continuous_cuspCentralMap π hπ)
  { e with
    continuous_toFun := hc
    continuous_invFun := by
      let h := hc.homeoOfEquivCompactToT2 (f := e.toEquiv)
      exact h.symm.continuous }

omit [TotallyDisconnectedSpace Δ] in
@[simp] lemma cuspQuotEquiv_mk [T2Space Q] (hs : Function.Surjective π) (a : Δ) :
    cuspQuotEquiv π hπ hs (QuotientGroup.mk (QuotientGroup.mk a)) = π a := rfl

/-! ### The transgression -/

variable (A : Type*) [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [IsTopologicalGroup A]

/-- **The transgression** of the cuspidally central extension `1 → I → Δ^{c-cn} → Q → 1`:
`d₂ : Hom_cont(I, A) → H²(Δ^{c-cn}/I, A)` for trivial coefficients `A` (`A^I = A`). -/
noncomputable def cuspTg : ContinuousMonoidHom (cuspInertia π hπ) (TrivCoeff A) →*
    ContH2 (CuspCentral π ⧸ cuspInertia π hπ) (fixedPts (cuspInertia π hπ) (TrivCoeff A)) :=
  tgCentral (cuspInertia_central π hπ) (TrivCoeff.smul_eq _) (isClosed_cuspInertia π hπ)

/-- **Exactness at `Hom(I, A)`**: `d₂ φ = 1` iff `φ` extends to a continuous homomorphism
(`1`-cocycle for the trivial action) `Δ^{c-cn} → A`. -/
theorem cuspTg_eq_one_iff (φ : ContinuousMonoidHom (cuspInertia π hπ) (TrivCoeff A)) :
    cuspTg π hπ A φ = 1 ↔
      ∃ χ : ContH1.cocycles (CuspCentral π) (TrivCoeff A), ∀ i : cuspInertia π hπ, χ i = φ i :=
  tgCentral_eq_one_iff _ _ _ φ

/-- **Exactness at `H²(Δ^{c-cn}/I, A)`**: the kernel of inflation is the image of `d₂`. -/
theorem exists_cuspTg_eq_of_inf₂_eq_one
    {z : ContH2 (CuspCentral π ⧸ cuspInertia π hπ) (fixedPts (cuspInertia π hπ) (TrivCoeff A))}
    (hz : inf₂ (cuspInertia π hπ) (TrivCoeff A) z = 1) : ∃ φ, cuspTg π hπ A φ = z :=
  exists_tgCentral_eq_of_inf₂_eq_one _ _ _ hz

/-- `inf₂ ∘ d₂ = 1`. -/
theorem inf₂_cuspTg (φ : ContinuousMonoidHom (cuspInertia π hπ) (TrivCoeff A)) :
    inf₂ (cuspInertia π hπ) (TrivCoeff A) (cuspTg π hπ A φ) = 1 :=
  inf₂_tgCentral _ _ _ φ

/-- **Naturality of `d₂` in the coefficients**: `d₂(ψ ∘ φ) = ψ_* d₂(φ)`. -/
theorem cuspTg_comp {A' : Type*} [CommGroup A'] [TopologicalSpace A'] [DiscreteTopology A']
    [IsTopologicalGroup A'] (φ : ContinuousMonoidHom (cuspInertia π hπ) (TrivCoeff A))
    (ψ : ContinuousMonoidHom (TrivCoeff A) (TrivCoeff A')) :
    cuspTg π hπ A' (ψ.comp φ) =
      ContH2.map (MonoidHom.id _) continuous_id
        (fixedPtsMap (ψ : TrivCoeff A →* TrivCoeff A') (fun _ _ => rfl))
        (fixedPtsMap_smul _ _) (cuspTg π hπ A φ) :=
  tgCentral_comp _ (TrivCoeff.smul_eq _) (TrivCoeff.smul_eq _) _ φ ψ

/-! ### The transgression of `1 ∈ Hom(I, I)` at finite level -/

variable (N : Subgroup (cuspInertia π hπ))

/-- The finite quotient `I/N` for an open subgroup `N ≤ I`. -/
abbrev cuspInertiaQuot : Type _ := cuspInertia π hπ ⧸ N

omit [CompactSpace Δ] [TotallyDisconnectedSpace Δ] in
lemma discreteTopology_cuspInertiaQuot (hN : IsOpen (N : Set (cuspInertia π hπ))) :
    DiscreteTopology (cuspInertiaQuot π hπ N) :=
  QuotientGroup.discreteTopology hN

/-- The projection `I ↠ I/N` ("`1 ∈ Hom(I, I)`" modulo `N`). -/
noncomputable def cuspInertiaProj :
    ContinuousMonoidHom (cuspInertia π hπ) (TrivCoeff (cuspInertiaQuot π hπ N)) :=
  TrivCoeff.homOf
    { toMonoidHom := QuotientGroup.mk' N
      continuous_toFun := QuotientGroup.continuous_mk }

/-- **The class of the cuspidally central extension modulo `N`**:
`d₂(I ↠ I/N) ∈ H²(Δ^{c-cn}/I, I/N)` — the element of [AbsTopIII], Proposition 1.4(ii),
obtained from `1 ∈ Hom(I_x, I_x)`, at the finite level `N`. -/
noncomputable def cuspClass (hN : IsOpen (N : Set (cuspInertia π hπ))) :
    ContH2 (CuspCentral π ⧸ cuspInertia π hπ)
      (fixedPts (cuspInertia π hπ) (TrivCoeff (cuspInertiaQuot π hπ N))) :=
  haveI := discreteTopology_cuspInertiaQuot π hπ N hN
  cuspTg π hπ _ (cuspInertiaProj π hπ N)

/-- `cuspClass N = 1` iff `I ↠ I/N` extends to a continuous homomorphism on `Δ^{c-cn}` (i.e. the
extension splits modulo `N`). -/
theorem cuspClass_eq_one_iff (hN : IsOpen (N : Set (cuspInertia π hπ))) :
    cuspClass π hπ N hN = 1 ↔
      ∃ χ : ContH1.cocycles (CuspCentral π) (TrivCoeff (cuspInertiaQuot π hπ N)),
        ∀ i : cuspInertia π hπ, χ i = TrivCoeff.of (QuotientGroup.mk i : cuspInertiaQuot π hπ N) :=
  haveI := discreteTopology_cuspInertiaQuot π hπ N hN
  cuspTg_eq_one_iff π hπ _ _

end Profinite

/-! ### The Θ-approach: `Δ_Θ ⊆ Δ^Θ = Δ/cl⁅cl⁅Δ, Δ⁆, Δ⁆` over `Δ^ell = Δ^ab` -/

section Theta

variable (Δ)

/-- The closure of the commutator subgroup, `cl⁅Δ, Δ⁆`. -/
abbrev thetaComm : Subgroup Δ := (⁅(⊤ : Subgroup Δ), ⊤⁆ : Subgroup Δ).topologicalClosure

instance thetaComm_normal : (thetaComm Δ).Normal := Subgroup.is_normal_topologicalClosure _

instance : IsClosed (thetaComm Δ : Set Δ) := Subgroup.isClosed_topologicalClosure _

/-- `Δ ↠ Δ^ell = Δ^ab = Δ/cl⁅Δ, Δ⁆`. -/
abbrev thetaMap : Δ →* Δ ⧸ thetaComm Δ := QuotientGroup.mk' _

lemma continuous_thetaMap : Continuous (thetaMap Δ) := QuotientGroup.continuous_mk

/-- **`Δ^Θ = Δ/cl⁅cl⁅Δ, Δ⁆, Δ⁆`**: the maximal cuspidally central quotient over `Δ^ab`. -/
theorem cuspCentralKer_thetaMap :
    cuspCentralKer (thetaMap Δ) = (⁅thetaComm Δ, ⊤⁆ : Subgroup Δ).topologicalClosure := by
  rw [cuspCentralKer, QuotientGroup.ker_mk']

/-- **`Δ_Θ = cl⁅Δ, Δ⁆ / cl⁅cl⁅Δ, Δ⁆, Δ⁆`**: the kernel of `Δ^Θ ↠ Δ^ell` is the image of
`cl⁅Δ, Δ⁆`; it is central in `Δ^Θ` (`cuspInertia_central`). -/
theorem thetaInertia_eq_map :
    cuspInertia (thetaMap Δ) (continuous_thetaMap Δ) =
      (thetaComm Δ).map (QuotientGroup.mk' _) := by
  rw [cuspInertia_eq_map, QuotientGroup.ker_mk']

variable [CompactSpace Δ] [TotallyDisconnectedSpace Δ]

/-- **The extension class of `1 → Δ_Θ → Δ^Θ → Δ^ell → 1` modulo an open `N ≤ Δ_Θ`**
([IUTchI], Remark 3.1.2(iii): "the extension class `∈ H²(Δ^ell_X, Δ_Θ)`"), at finite level. -/
noncomputable def thetaClass (N : Subgroup (cuspInertia (thetaMap Δ) (continuous_thetaMap Δ)))
    (hN : IsOpen (N : Set (cuspInertia (thetaMap Δ) (continuous_thetaMap Δ)))) :=
  cuspClass (thetaMap Δ) (continuous_thetaMap Δ) N hN

end Theta

end Iut.Reconstruction
