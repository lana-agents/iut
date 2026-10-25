/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.HemiSelfComm
import Iut.Reconstruction.Cusp.EtLocChainIso
import CurvesJacobian.Cusp.HemiConstArith

/-!
# [AbsTopII] Cor. 3.3 (i) for `G′ ≠ G`: the `k′`-core of `X_{k′}` (MR8)

[AbsTopII] Cor. 3.3 (i) (`Topics in Absolute Anabelian Geometry II.txt`, l.4436–4447): for a
normal open subgroup `G′ ⊆ G` corresponding to a finite extension `k′ ⊆ k̄` of `k`,
`Π′ = Π ×_G G′`, and `C` a `k′`-core of `X_{k′} = X ×_k k′`, the chain `Π′ ⇝ Π_C` is the unique
length-one `⋎`-chain of `Chain(Π′)` that is terminal in `ÉtLoc(Π′)`. `Iut.Reconstruction.HemiCore`
(`HemiSelfComm`) treats `G′ = G` for `X = E ∖ {O}` and `C = [X / ±1]`. Here: `k′ = M ⊆ k̄` finite
Galois over the number field `K`, `X_M = (E ∖ {O})_M = E_M ∖ {O}`, whose `M`-core is the
hemi-elliptic orbicurve of `E_M`.

* **`hemiBaseChangeEmb`**, **`range_hemiBaseChangeEmb`**, **`hemiGkEquiv_pr_hemiBaseChangeEmb`**:
  cj's arithmetic `π₁` of `X_M` over `M` (`hemiMPiXGal`) embeds openly into the one of `X` over
  `K` (`hemiPiXGal`), with image exactly `Π′ = Π ×_G G′ = pr⁻¹(G′)`, `G′ ⊆ G_K` the subgroup
  corresponding to `Gal(k̄ / M)` under `hemiGkEquiv` (`hemiGprime`), compatibly with the
  projections (`G_M ≅ Gal(k̄ / M) ⊆ Gal(k̄ / K) ≅ G_K`); `hemiBaseChangeEquiv : Π_{X_M} ≃ₜ* Π′`.
  Galois form: `mem_range_infInclX₃_iff` (`Π_{X_M} ⊆ Π_X` is the preimage of `Gal(k̄ / M)`).
* **`hemi_cor33i_terminal_baseChange`**: the chain `Π_{X_M} ⇝ Π_{C_M}` is terminal in
  `ÉtLoc(Π_{X_M})` (`hemi_cor33i_terminal` for `E_M` over the number field `M`; `j(E_M) = j(E)`).
* **`hemi_cor33i_unique`**, **`hemi_cor33i_unique_baseChange`**: uniqueness up to isomorphism in
  `Chain(Π′)` (belyi's `PiChain.Iso`) of the terminal length-one `⋎`-chain
  (`Iut.Reconstruction.EtLocChain.nonempty_iso_of_isTerminalEtLoc`).

**Input:** `hDGC` (existence half of the rel-isom-DGC over number fields), as in
`hemi_cor33i_terminal`.
-/

open CategoryTheory AlgebraicGeometry Topology Belyi Belyi.Anabelian CurvesJacobian
  CurvesJacobian.Cusp Pi1.Orbifold AffOrbicurve

noncomputable section

namespace Iut.Reconstruction.HemiCore

universe u

section Galois

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [CharZero k] {t : Ω}
  [IsGalois (K₀ k t) Ω] (D : GaloisData k t) (M : IntermediateField k (ConstField₂ k Ω))
  [FiniteDimensional k M] [IsGalois k M]

/-- **`Π_{X_M} ⊆ Π_X` is the preimage of `Gal(k̄ / M)`** (Galois form). -/
theorem mem_range_infInclX₃_iff (x : GaloisPi1.pi1 D.HL D.S D.isClosed_HL) :
    x ∈ (infInclX₃ D (constFixer₃ t M) (isOpen_constFixer₃ M)
      (constFixer₃_normal M)).toMonoidHom.range ↔ piConstX D x ∈ M.fixingSubgroup := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    change galResConst t (y : Ω ≃ₐ[K₀ k t] Ω) ∈ M.fixingSubgroup
    exact y.2.2
  · intro hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : piConstX D (QuotientGroup.mk h) = galResConst t (h : Ω ≃ₐ[K₀ k t] Ω) := rfl
    rw [h1] at hx
    exact ⟨QuotientGroup.mk (⟨(h : Ω ≃ₐ[K₀ k t] Ω), h.2, hx⟩ :
      (galoisDataConst₃ D M).HL), rfl⟩

end Galois

section BaseChange

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]
  (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E)))) [FiniteDimensional K M]
  [IsGalois K M]
  (Ω' : Type) [Field Ω'] [Algebra K Ω'] [IsAlgClosed Ω'] [Algebra.IsAlgebraic K Ω'] [CharZero Ω']
  (Ω'' : Type) [Field Ω''] [Algebra M Ω''] [IsAlgClosed Ω''] [Algebra.IsAlgebraic M Ω'']
  [CharZero Ω'']

/-- `G′ ⊆ G_K`: the subgroup corresponding to `Gal(k̄ / M)` (`hemiGkEquiv`). -/
def hemiGprime : Subgroup (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).G :=
  M.fixingSubgroup.comap (hemiGkEquiv E Ω').toMulEquiv.toMonoidHom

/-- `Π′ = Π ×_G G′ = pr⁻¹(G′) ⊆ Π_X`. -/
def hemiPiPrime : Subgroup (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi :=
  (hemiGprime E M Ω').comap
    ((arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).pr :
      (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi →*
        (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).G)

/-- `Π_{X_M} → Π_X`: `hemiMPiXGal`, `Π_{X_M} ⊆ Π_X` in Galois form, `hemiPiXGal⁻¹`. -/
def hemiBaseChangeEmb :
    (arithmeticExt Ω'' (hypCurveX (E.baseChange M)) (compl_XE_nonempty (E.baseChange M))).Pi →ₜ*
      (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi :=
  (ContinuousMonoidHom.toContinuousMonoidHom (hemiPiXGal E Ω').symm).comp
    ((infInclX₃ (hemiData E) _ (isOpen_constFixer₃ M) (constFixer₃_normal M)).comp
      (ContinuousMonoidHom.toContinuousMonoidHom (hemiMPiXGal E M Ω'')))

lemma hemiPiXGal_hemiBaseChangeEmb (γ : (arithmeticExt Ω'' (hypCurveX (E.baseChange M))
    (compl_XE_nonempty (E.baseChange M))).Pi) :
    hemiPiXGal E Ω' (hemiBaseChangeEmb E M Ω' Ω'' γ) =
      infInclX₃ (hemiData E) _ (isOpen_constFixer₃ M) (constFixer₃_normal M)
        (hemiMPiXGal E M Ω'' γ) :=
  (hemiPiXGal E Ω').apply_symm_apply _

theorem isOpenEmbedding_hemiBaseChangeEmb : IsOpenEmbedding (hemiBaseChangeEmb E M Ω' Ω'') :=
  (hemiPiXGal E Ω').symm.toHomeomorph.isOpenEmbedding.comp
    ((isOpenEmbedding_infInclX₃ (S_subset_constFixer₃ (hemiData E) M)).comp
      (hemiMPiXGal E M Ω'').toHomeomorph.isOpenEmbedding)

/-- **Compatibility with the projections**: `G_M ≅ Gal(k̄ / M) ⊆ Gal(k̄ / K) ≅ G_K`. -/
theorem hemiGkEquiv_pr_hemiBaseChangeEmb (γ : (arithmeticExt Ω'' (hypCurveX (E.baseChange M))
    (compl_XE_nonempty (E.baseChange M))).Pi) :
    hemiGkEquiv E Ω' ((arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).pr
      (hemiBaseChangeEmb E M Ω' Ω'' γ)) =
      (hemiMGkEquiv E M Ω'' ((arithmeticExt Ω'' (hypCurveX (E.baseChange M))
        (compl_XE_nonempty (E.baseChange M))).pr γ)).restrictScalars K := by
  rw [hemiGkEquiv_pr, hemiPiXGal_hemiBaseChangeEmb, hemiMGkEquiv_pr]
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (hemiMPiXGal E M Ω'' γ)
  rw [← hy]
  rfl

/-- **The image of `Π_{X_M}` is `Π′ = Π ×_G G′`.** -/
theorem range_hemiBaseChangeEmb :
    (hemiBaseChangeEmb E M Ω' Ω'').toMonoidHom.range = hemiPiPrime E M Ω' := by
  ext x
  change x ∈ (hemiBaseChangeEmb E M Ω' Ω'').toMonoidHom.range ↔
    hemiGkEquiv E Ω' ((arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).pr x) ∈
      M.fixingSubgroup
  rw [hemiGkEquiv_pr, ← mem_range_infInclX₃_iff]
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨hemiMPiXGal E M Ω'' γ, (hemiPiXGal_hemiBaseChangeEmb E M Ω' Ω'' γ).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨(hemiMPiXGal E M Ω'').symm y, (hemiPiXGal E Ω').injective ?_⟩
    change hemiPiXGal E Ω' (hemiBaseChangeEmb E M Ω' Ω'' _) = _
    rw [hemiPiXGal_hemiBaseChangeEmb, ContinuousMulEquiv.apply_symm_apply]
    exact hy

/-- **`Π_{X_M} ≃* Π′ = Π ×_G G′`.** -/
def hemiBaseChangeEquiv :
    (arithmeticExt Ω'' (hypCurveX (E.baseChange M)) (compl_XE_nonempty (E.baseChange M))).Pi ≃*
      hemiPiPrime E M Ω' :=
  (MonoidHom.ofInjective (isOpenEmbedding_hemiBaseChangeEmb E M Ω' Ω'').injective).trans
    (MulEquiv.subgroupCongr (range_hemiBaseChangeEmb E M Ω' Ω''))

lemma hemiBaseChangeEquiv_apply (γ : (arithmeticExt Ω'' (hypCurveX (E.baseChange M))
    (compl_XE_nonempty (E.baseChange M))).Pi) :
    (hemiBaseChangeEquiv E M Ω' Ω'' γ : (arithmeticExt Ω' (hypCurveX E)
      (compl_XE_nonempty E)).Pi) = hemiBaseChangeEmb E M Ω' Ω'' γ := rfl

omit [FiniteDimensional K M] [IsGalois K M] in
/-- The `j`-invariant condition is inherited by `E_M`. -/
theorem baseChange_j_notMem_excJ (hj : ∀ c ∈ AffOrbicurve.excJ, E.j ≠ (c : K)) :
    ∀ c ∈ AffOrbicurve.excJ, (E.baseChange M).j ≠ (c : M) := fun c hc h => by
  refine hj c hc ((algebraMap K M).injective ?_)
  rw [map_ratCast]
  rw [← h]
  exact (WeierstrassCurve.map_j E (algebraMap K M)).symm

omit [IsGalois K M] in
/-- **[AbsTopII] Cor. 3.3 (i) for `G′ ≠ G`** (`G′ = Gal(k̄ / M)`, `M/K` finite Galois): the
`⋎`-chain `Π′ ⇝ Π_{C_M}` from `Π′ = Π_{X_M}` (`≅ Π ×_G G′`, `hemiBaseChangeEquiv`,
`hemiGkEquiv_pr_hemiBaseChangeEmb`) to the group of the `M`-core `C_M = [X_M / ±1]` of `X_M` is
terminal in `ÉtLoc(Π′)`. -/
theorem hemi_cor33i_terminal_baseChange
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, E.j ≠ (c : K)) :
    (hemiCoreChain (E.baseChange M) Ω'').IsTerminalEtLoc :=
  hemi_cor33i_terminal (E.baseChange M) Ω'' hDGC (baseChange_j_notMem_excJ E M hj)

omit [IsGalois K M] in
/-- **[AbsTopII] Cor. 3.3 (i) for `G′ ≠ G`, uniqueness in `Chain(Π′)`**: every length-one chain of
type `[⋎]` from `Π′ = Π_{X_M}` that is terminal in `ÉtLoc(Π′)` is isomorphic in `Chain(Π′)`
(belyi's `PiChain.Iso`) to `Π′ ⇝ Π_{C_M}`. -/
theorem hemi_cor33i_unique_baseChange
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, E.j ≠ (c : K))
    (c : PiChain (arithmeticExt Ω'' (hypCurveX (E.baseChange M))
      (compl_XE_nonempty (E.baseChange M))))
    (hq : c.typeChain = [OpKind.quot]) (hc : c.IsTerminalEtLoc) :
    Nonempty (c.Iso (hemiCoreChain (E.baseChange M) Ω'')) :=
  EtLocChain.nonempty_iso_of_isTerminalEtLoc (hemiCoreChain_typeChain _ _) hq
    (hemi_cor33i_terminal_baseChange E M Ω'' hDGC hj) hc

end BaseChange

section Unique

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]
  (Ω' : Type) [Field Ω'] [Algebra K Ω'] [IsAlgClosed Ω'] [Algebra.IsAlgebraic K Ω'] [CharZero Ω']

/-- **[AbsTopII] Cor. 3.3 (i), uniqueness in `Chain(Π)`** (`G′ = G`): every length-one chain of
type `[⋎]` from `Π_X` that is terminal in `ÉtLoc(Π_X)` is isomorphic in `Chain(Π_X)` (belyi's
`PiChain.Iso`, compatible with the rigidifying homomorphisms) to the chain `Π_X ⇝ Π_C` of the
hemi-elliptic core (`hemiCoreChain`). -/
theorem hemi_cor33i_unique
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, E.j ≠ (c : K))
    (c : PiChain (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)))
    (hq : c.typeChain = [OpKind.quot]) (hc : c.IsTerminalEtLoc) :
    Nonempty (c.Iso (hemiCoreChain E Ω')) :=
  EtLocChain.nonempty_iso_of_isTerminalEtLoc (hemiCoreChain_typeChain E Ω') hq
    (hemi_cor33i_terminal E Ω' hDGC hj) hc

end Unique

end Iut.Reconstruction.HemiCore
