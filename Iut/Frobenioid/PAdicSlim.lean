/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.PAdicGalois
import LocalClassFieldTheory.Reciprocity.ArtinNaturality
import LocalClassFieldTheory.Reciprocity.ArtinInertia

/-!
# The absolute Galois group of a `p`-adic field is slim

[FrdII], Example 1.1 (citing [Mzk1], Theorem 1.1.1(ii)): for a finite extension `E` of `ℚ_p`,
`G_E = Gal(K̄/E)` is **slim**: the centralizer of every open subgroup is trivial
(`PAdicGalois.isSlimGroup`). Hence [FrdI], Theorem 3.4(v) holds for the `p`-adic Frobenioids
over `B(G_E)⁰` (`PAdicGalois.thm34_base`, `thm34Pf_base`), and `B(G_E)⁰` is a slim category.

Proof (local class field theory): let `m` commute with an open subgroup `U`, and `x ∈ K̄`. Choose
a finite Galois `M/E` containing `x` with `Gal(K̄/M) ⊆ U`. Then `m(M) = M`, and for `a ∈ M^×`,
naturality of the Artin map (`PadicField.artin_naturality`) and `m ρ = ρ m` for lifts
`ρ ∈ Gal(K̄/M)` of `artin_M(a)` give `artin_M(m a) = artin_M(a)`; the Artin map is injective
(`PadicField.artin_injective`), so `m a = a`. Hence `m` fixes `x`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory IntermediateField

namespace PAdicGalois

variable {p : ℕ} [hp : Fact p.Prime]

local notation "Kbar" => PadicAlgCl


section Slim

variable {E : IntermediateField ℚ_[p] (Kbar p)} [FiniteDimensional ℚ_[p] E]

/-- `m` fixes a finite Galois `M/E` pointwise if it commutes with `Gal(K̄/M)`. -/
theorem fixes_of_commute (M : IntermediateField E (Kbar p)) [FiniteDimensional E M]
    [Normal E M] (m : GK p E) (hm : ∀ v ∈ M.fixingSubgroup, m * v = v * m) (a : M) :
    m (a : Kbar p) = a := by
  -- `M` as a finite extension of `ℚ_p`
  haveI : FiniteDimensional ℚ_[p] M := Module.Finite.trans E M
  have hmM : ∀ y : (Kbar p), y ∈ M → m y ∈ M := fun y hy => by
    rw [show m y = ((m.restrictNormal M ⟨y, hy⟩ : M) : PadicAlgCl p) from
      (AlgEquiv.restrictNormal_commutes m M ⟨y, hy⟩).symm]
    exact SetLike.coe_mem _
  have hmM' : ∀ y : (Kbar p), y ∈ M → m.symm y ∈ M := fun y hy => by
    rw [show m.symm y = ((m.symm.restrictNormal M ⟨y, hy⟩ : M) : PadicAlgCl p) from
      (AlgEquiv.restrictNormal_commutes m.symm M ⟨y, hy⟩).symm]
    exact SetLike.coe_mem _
  -- `τ = m|_M : M ≃ M` over `ℚ_p`
  let τ : M ≃ₐ[ℚ_[p]] M :=
    { toFun := fun y => ⟨m y, hmM y y.2⟩
      invFun := fun y => ⟨m.symm y, hmM' y y.2⟩
      left_inv := fun y => Subtype.ext (m.symm_apply_apply y)
      right_inv := fun y => Subtype.ext (m.apply_symm_apply y)
      map_mul' := fun x y => Subtype.ext (map_mul m (x : (Kbar p)) y)
      map_add' := fun x y => Subtype.ext (map_add m (x : (Kbar p)) y)
      commutes' := fun c => Subtype.ext (by
        change m (algebraMap ℚ_[p] (Kbar p) c) = algebraMap ℚ_[p] (Kbar p) c
        exact (m.restrictScalars ℚ_[p]).commutes c) }
  let σ : (Kbar p) ≃+* (Kbar p) := m.toRingEquiv
  have hσ : ∀ c : M, σ (algebraMap M (Kbar p) c) = algebraMap M (Kbar p) (τ c) :=
    fun _ => rfl
  by_cases ha : (a : (Kbar p)) = 0
  · rw [ha, map_zero]
  let u : Mˣ := Units.mk0 ⟨a, a.2⟩ (fun h => ha (congrArg Subtype.val h))
  -- the Artin images of `u` and `τ u` agree
  have key : PadicField.artin p M (Kbar p) (Units.map (τ : M →* M) u) =
      PadicField.artin p M (Kbar p) u := by
    ext y
    -- `y = σ y₀`
    obtain ⟨y₀, rfl⟩ := (PadicField.maxAbelianRingEquiv τ σ hσ).surjective y
    have hnat := PadicField.artin_naturality (p := p) τ σ hσ u y₀
    rw [hnat]
    -- lift `artin u` to `ρ ∈ Gal(K̄/M)`
    let ρ : Kbar p ≃ₐ[M] Kbar p := (PadicField.artin p M (Kbar p) u).liftNormal (Kbar p)
    have hρ : ∀ z : PadicField.maxAbelian M (Kbar p),
        ρ (z : Kbar p) = (PadicField.artin p M (Kbar p) u z : Kbar p) :=
      fun z => AlgEquiv.liftNormal_commutes _ (Kbar p) z
    let ρE : GK p E := ρ.restrictScalars E
    have hρE : ρE ∈ M.fixingSubgroup := fun z => ρ.commutes (⟨(z : (Kbar p)), z.2⟩ : M)
    have hc := hm ρE hρE
    have h1 := congrArg (fun g : GK p E => g (y₀ : (Kbar p))) hc
    simp only [AlgEquiv.mul_apply] at h1
    change σ (PadicField.artin p M (Kbar p) u y₀ : (Kbar p)) =
      (PadicField.artin p M (Kbar p) u (PadicField.maxAbelianRingEquiv τ σ hσ y₀) : Kbar p)
    rw [← hρ, ← hρ, PadicField.coe_maxAbelianRingEquiv]
    exact h1
  have hu := PadicField.artin_injective (p := p) (Ω := (Kbar p)) key
  have := congrArg (fun w : Mˣ => ((w : M) : (Kbar p))) hu
  exact this

/-- **`G_E = Gal(K̄/E)` is slim** for every finite extension `E/ℚ_p`. -/
theorem isSlimGroup : IsSlimGroup (GK p E) := by
  intro U hU m hm
  obtain ⟨F, hF, hFn, hFU⟩ := (krullTopology_mem_nhds_one_iff_of_normal E (Kbar p) U).mp
    (hU.mem_nhds U.one_mem)
  ext x
  -- a finite Galois `M ⊇ F(x)`
  let L0 : IntermediateField E (Kbar p) := F ⊔ IntermediateField.adjoin E {x}
  haveI : FiniteDimensional E (IntermediateField.adjoin E {x}) :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := E) x)
  haveI : FiniteDimensional E L0 := IntermediateField.finiteDimensional_sup _ _
  let M : IntermediateField E (Kbar p) := IntermediateField.normalClosure E L0 (Kbar p)
  haveI : FiniteDimensional E M := normalClosure.is_finiteDimensional E L0 (Kbar p)
  haveI : Normal E M := normalClosure.normal E L0 (Kbar p)
  have hL0 : L0 ≤ M := L0.le_normalClosure
  have hFM : F ≤ M := le_sup_left.trans hL0
  have hxM : x ∈ M := hL0 (le_sup_right (a := F) (mem_adjoin_simple_self E x))
  have hV : ∀ v ∈ M.fixingSubgroup, m * v = v * m := fun v hv =>
    hm v (hFU (fixingSubgroup_antitone hFM hv))
  exact fixes_of_commute M m hV ⟨x, hxM⟩

instance : T2Space (GK p E) := krullTopology_t2

/-- **[FrdI], Theorem 3.4(v) for `C^⊢_v` over `B(G_E)⁰`**: every autoequivalence lies over an
autoequivalence of the base category. -/
theorem thm34_base (F : Frob p E ⥤ Frob p E) [F.IsEquivalence] :
    PreservesBase
      (Model.toElem (constPhi (OrbitObj (GK p E)) gammaZ)
        (bGal (GK p E) (ord p) (ord_smul p E) gammaZ)
        (divGal (GK p E) (ord p) (ord_smul p E) gammaZ))
      (Model.toElem (constPhi (OrbitObj (GK p E)) gammaZ)
        (bGal (GK p E) (ord p) (ord_smul p E) gammaZ)
        (divGal (GK p E) (ord p) (ord_smul p E) gammaZ)) F :=
  GaloisModel.thm34_base isSlimGroup (torsion p E) F

/-- **[FrdI], Theorem 3.4(v) for `C_v` over `B(G_E)⁰`**. -/
theorem thm34Pf_base (F : FrobPf p E ⥤ FrobPf p E) [F.IsEquivalence] :
    PreservesBase
      (Model.toElem (constPhi (OrbitObj (GK p E)) gammaQ)
        (bGal (GK p E) (ord p) (ord_smul p E) gammaQ)
        (divGal (GK p E) (ord p) (ord_smul p E) gammaQ))
      (Model.toElem (constPhi (OrbitObj (GK p E)) gammaQ)
        (bGal (GK p E) (ord p) (ord_smul p E) gammaQ)
        (divGal (GK p E) (ord p) (ord_smul p E) gammaQ)) F :=
  GaloisModel.thm34_base isSlimGroup (torsion p E) F

/-- **`B(G_E)⁰` is a slim category.** -/
theorem orbitObj_isSlim : IsSlim (OrbitObj (GK p E)) := OrbitObj.isSlim isSlimGroup

end Slim

end PAdicGalois

end Frobenioid

end Iut
