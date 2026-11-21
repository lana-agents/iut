/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Cor53
import Iut.Multiradial.PrimeStrip.MonoAn
import Iut.Reconstruction.Local.MulLiftOrd

/-!
# `KummerLift` at `v ∈ V^non` ([AbsTopIII], Proposition 3.2 (iv), surjectivity; MR21 R4b)

[AbsTopIII], Proposition 3.2 (iv) (`Topics in Absolute Anabelian Geometry III.txt`,
l.4111–4124): for MLF-Galois `TM`-pairs, `Isom((Π ↷ M), (Π* ↷ M*)) → Isom(Π, Π*)` is a
bijection. IUT I, Corollary 5.3 (ii) (l.9891–9894 of `Inter-universal Teichmuller Theory I.txt`)
cites it for the Frobenioids `C_v` at `v ∈ V^non`. Here we instantiate the `G_v`-level results
of `Reconstruction/Local/MulLiftOrd.lean` at the local data `Π_v → G_v ↷ \bar{ℚ}_p^×` of
`Multiradial/PrimeStrip`:

* **`kummerLift`**: MR21's named input `KummerLift D v` (`Cor53.lean`, debt R4b) holds, given
  MR20's named input `DeltaCharacteristic D v` ([AbsAnab] Lemma 1.3.8 for `Π_v`) and debt H3
  (`PiToGQuotient D v`): an automorphism `σ` of `Π_v` descends to an automorphism `σ'` of the
  topological group `G_v` (`exists_descend`; `Π_v → G_v` is open because `Π_v` has a basis of
  open subgroups, `piv_hasONSBasis`), and `σ'` lifts to `\bar{ℚ}_p^×` (`exists_mulLift`).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open NumberField Iut.Frobenioid Iut.Frobenioid.PAdicGalois

/-! ### Descending automorphisms along an open quotient map -/

section Descend

variable {Γ G : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- A homomorphism mapping open subgroups to open sets is open, if the source has a basis of
open (normal) subgroups at `1`. -/
theorem isOpenMap_of_hasONSBasis (f : Γ →* G) (hb : HasONSBasis Γ)
    (hopen : ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → IsOpen (U.map f : Set G)) :
    IsOpenMap f := by
  intro W hW
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  have h1 : IsOpen ((fun z => x * z) ⁻¹' W) := hW.preimage (continuous_const_mul x)
  obtain ⟨N, hN⟩ := hb h1 (by simpa using hx)
  refine ⟨(fun y => f x * y) '' (N.toSubgroup.map f : Set G), ?_,
    isOpenMap_mul_left (f x) _ (hopen _ N.toOpenSubgroup.isOpen),
    ⟨1, ⟨1, N.one_mem, map_one f⟩, mul_one _⟩⟩
  rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
  exact ⟨x * n, hN hn, by simp⟩

omit [IsTopologicalGroup Γ] [IsTopologicalGroup G] in
/-- **Descent of automorphisms**: an automorphism `σ` of `Γ` preserving `ker f`, for an open
continuous surjection `f : Γ → G`, induces an automorphism `σ'` of the topological group `G`
with `f ∘ σ = σ' ∘ f`. -/
theorem exists_descend (f : Γ →* G) (hf : Continuous f) (hs : Function.Surjective f)
    (ho : IsOpenMap f) (σ : Γ ≃ₜ* Γ) (hσ : f.ker.map (σ : Γ →* Γ) = f.ker) :
    ∃ σ' : G ≃ₜ* G, ∀ g, f (σ g) = σ' (f g) := by
  have hq : Topology.IsQuotientMap f := (IsOpenQuotientMap.mk hs hf ho).isQuotientMap
  have hker : ∀ g, g ∈ f.ker ↔ σ g ∈ f.ker := fun g => by
    constructor
    · intro hg
      rw [← hσ]
      exact ⟨g, hg, rfl⟩
    · intro hg
      rw [← hσ] at hg
      obtain ⟨h, hh, hhg⟩ := hg
      rwa [← σ.injective hhg]
  have hwd : ∀ g h, f g = f h → f (σ g) = f (σ h) := fun g h hgh => by
    have : g⁻¹ * h ∈ f.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]
    have h2 := (hker _).1 this
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hwd' : ∀ g h, f g = f h → f (σ.symm g) = f (σ.symm h) := fun g h hgh => by
    have : g⁻¹ * h ∈ f.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]
    have h2 : σ.symm (g⁻¹ * h) ∈ f.ker := by
      rw [hker, ContinuousMulEquiv.apply_symm_apply]
      exact this
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one] at h2
    exact h2
  let s := Function.surjInv hs
  have hs' : ∀ y, f (s y) = y := Function.surjInv_eq hs
  let e : G ≃* G :=
    { toFun := fun y => f (σ (s y))
      invFun := fun y => f (σ.symm (s y))
      left_inv := fun y => by
        change f (σ.symm (s (f (σ (s y))))) = y
        rw [hwd' _ _ (hs' _), ContinuousMulEquiv.symm_apply_apply, hs']
      right_inv := fun y => by
        change f (σ (s (f (σ.symm (s y))))) = y
        rw [hwd _ _ (hs' _), ContinuousMulEquiv.apply_symm_apply, hs']
      map_mul' := fun y z => by
        rw [← map_mul, ← map_mul]
        exact hwd _ _ (by rw [map_mul, hs', hs', hs']) }
  have he : ∀ g, e (f g) = f (σ g) := fun g => hwd _ _ (hs' _)
  have he' : ∀ g, e.symm (f g) = f (σ.symm g) := fun g => hwd' _ _ (hs' _)
  refine ⟨{ toMulEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ },
    fun g => (he g).symm⟩
  · rw [hq.continuous_iff]
    have : (e ∘ f) = f ∘ σ := funext he
    change Continuous (e ∘ f)
    rw [this]
    exact hf.comp σ.continuous
  · rw [hq.continuous_iff]
    have : (e.symm ∘ f) = f ∘ σ.symm := funext he'
    change Continuous (e.symm ∘ f)
    rw [this]
    exact hf.comp σ.symm.continuous

end Descend

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-! ### The local data -/

instance finiteDimensional_Lv : FiniteDimensional ℚ_[pv D v] (Lv D v) := by
  letI := padicAlg D v
  haveI := isAlgebraic_padicAlg D v
  haveI : FiniteDimensional ℚ_[pv D v] (Kv D v) :=
    LocalConstruct.finite_padicAlgebra (p := pv D v) rfl
  exact LinearEquiv.finiteDimensional (eL (pv D v) (Kv D v)).toLinearEquiv

/-- **`Π_v` has a basis of open normal subgroups** (profinite at `V^good`, `piv_temp` at
`V^bad`). -/
theorem piv_hasONSBasis : HasONSBasis (Piv D v).carrier := by
  by_cases hv : v ∈ D.VBad
  · exact (piv_temp D v hv).2.1
  · obtain ⟨h1, h2, -⟩ := piv_profinite D v hv
    intro U hU h1U
    exact ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1U

/-- **Automorphisms of `Π_v` descend to `G_v`** (from Lemma 1.3.8 and H3). -/
theorem exists_descend_piv (hΔ : DeltaCharacteristic D v) (h3 : PiToGQuotient D v)
    (σ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier) :
    ∃ σ' : Gv D v ≃ₜ* Gv D v, ∀ g, piToG D v (σ g) = σ' (piToG D v g) :=
  exists_descend (piToG D v) (continuous_piToG D v) h3.1
    (isOpenMap_of_hasONSBasis _ (piv_hasONSBasis D v) h3.2) σ (hΔ σ)

/-- **[AbsTopIII], Proposition 3.2 (iv), surjectivity, at `v`**: MR21's named input
`KummerLift D v` (debt R4b) from [AbsAnab] Lemma 1.3.8 for `Π_v` (`DeltaCharacteristic`) and H3. -/
theorem kummerLift (hΔ : DeltaCharacteristic D v) (h3 : PiToGQuotient D v) : KummerLift D v := by
  intro σ
  obtain ⟨σ', hσ'⟩ := exists_descend_piv D v hΔ h3 σ
  obtain ⟨ψ, hψ, hψo⟩ := exists_mulLift (E := Lv D v) σ'
  refine ⟨ψ, fun g m => ?_, hψo⟩
  rw [piMul_smul, piMul_smul, hσ']
  exact hψ _ m

end PrimeStrip

end Multiradial

end Iut
