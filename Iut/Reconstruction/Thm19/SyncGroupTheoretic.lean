/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.CycloIso

/-!
# The synchronisation `I_x ≅ M_X` of [AbsTopIII] Prop 1.4 (ii) is group-theoretic

[AbsTopIII] Prop 1.4 (ii) (`Topics in Absolute Anabelian Geometry III.txt` l.1771–1803): the
`E₂`-differential of the extension `1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1` gives the natural
isomorphism `M_X ≅ I_x` (`M_X = Hom(H²(Δ_X, Ẑ), Ẑ)`), and "in particular, this yields a 'purely
group-theoretic algorithm' […] for constructing this isomorphism from the surjection
`Δ_{U_x} ↠ Δ_X`" (l.1800–1803). curves-jacobian constructs the synchronisation
`syncEquiv : I_x ≃* M_X` (`Kummer/SyncZHat.lean`) through the tame character and the Chern class
of a degree-`1` line bundle; here it is shown to depend only on the group theory of
`Δ_{U_x} ↠ Δ_X`:

* **(S1)** `h2EquivAny_comap`, `eZ_h2Triv`, **`mxModMap_phi0`**, `mxModMap_phi0_symm`: the
  relator-value isomorphism `H²(G, M) ≅ M` of an orientation `e : G' ≃ₜ* Π̂_{g,0}` is natural in
  the group, hence `M_X/n(f) (φ₀(f ∘ e)) = φ₀(e)` for `f : G ≃ₜ* G'`;
* **(S2)** **`proj_syncEquiv_cuspHat`** (and `proj_syncEquivBar_cuspHat` for `X_{k̄}`): for every
  pair of orientations `Θ : Δ_{U_x} ≃ₜ* Π̂_{G,1}`, `Θ₀ : Δ_X ≃ₜ* Π̂_{G,0}` compatible with the
  filling maps and with `Θ⁻¹(c) ∈ I_x` (`c` the cusp generator), the level-`n` component of the
  synchronisation at `Θ⁻¹(c)` is `φ₀(Θ₀)⁻¹`, where `φ₀(Θ₀) ∈ M_X/n` is the relator value of `Θ₀`
  (`TopClass.phi0`): a purely group-theoretic formula;
* **(S3)** `monoidHom_eq_of_cuspHat`: continuous homomorphisms out of `I` with `Θ(I) = ⟨c⟩‾`
  agree once they agree on `Θ⁻¹(c)`; `continuous_syncEquiv`, **`eq_syncEquiv_of_cuspHat`**,
  `eq_syncEquiv_of_proj`;
* **`mxHatCongr_syncEquiv`** (and `mxHatCongr_syncEquivBar`): **transport** — for isomorphisms
  `Ξ : Δ_{U_x} ≃ₜ* Δ_{U'_{x'}}`, `Ξ₀ : Δ_X ≃ₜ* Δ_{X'}` compatible with the filling maps and with
  `Ξ(I_x) = I_{x'}`, the synchronisations correspond: `M_X(Ξ₀) ∘ sync_x = sync_{x'} ∘ Ξ`.
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Topology Pi1 Pi1.Orbifold
  Pi1.Profinite Pi1.SurfaceGroup KummerTheory KummerTheory.Curve AffOrbicurve CurvesJacobian
  CurvesJacobian.TopClass CurvesJacobian.Kummer CurvesJacobian.ChernClass CurvesJacobian.Cusp
  Belyi

noncomputable section

namespace Iut.Reconstruction.Thm19

/-! ### (S1) Naturality of the relator value in the group -/

section Naturality

variable {G G' M : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  [CommGroup M] [Finite M] [MulDistribMulAction G M] [MulDistribMulAction G' M] {g : ℕ}

/-- **`H²(G, M) ≅ M` is natural in the group**: for `f : G ≃ₜ* G'` and an orientation
`e : G' ≃ₜ* Π̂_{g,0}`, the relator value of `f ∘ e` on `f^* c` is that of `e` on `c`. -/
theorem h2EquivAny_comap (hg : 0 < g) (f : G ≃ₜ* G') (e : G' ≃ₜ* ProfiniteSurfaceGroup g 0)
    (htriv : ∀ (γ : G) (m : M), γ • m = m) (htriv' : ∀ (γ : G') (m : M), γ • m = m)
    (c : H2lc G' M) :
    h2EquivAny hg (f.trans e) htriv
        (H2lc.comap f.toMulEquiv.toMonoidHom f.continuous
          (fun γ m ↦ (htriv' (f γ) m).trans (htriv γ m).symm) c) =
      h2EquivAny hg e htriv' c := by
  letI := trivialAction G (Shrink.{0} M)
  letI := trivialAction G' (Shrink.{0} M)
  letI := trivialAction (ProfiniteSurfaceGroup g 0) (Shrink.{0} M)
  haveI : Finite (Shrink.{0} M) :=
    Finite.of_equiv _ (Shrink.mulEquiv.symm : M ≃* Shrink.{0} M).toEquiv
  let s : M ≃* Shrink.{0} M := Shrink.mulEquiv.symm
  have key : H2lc.congr (f.trans e) (fun _ _ ↦ rfl)
      (h2MapEquiv s (fun γ m ↦ by rw [htriv]; rfl)
        (H2lc.comap f.toMulEquiv.toMonoidHom f.continuous
          (fun γ m ↦ (htriv' (f γ) m).trans (htriv γ m).symm) c)) =
      H2lc.congr e (fun _ _ ↦ rfl) (h2MapEquiv s (fun γ m ↦ by rw [htriv']; rfl) c) := by
    induction c using QuotientGroup.induction_on with
    | H z =>
      refine congrArg QuotientGroup.mk (Subtype.ext (funext fun p ↦ ?_))
      change s (z.1 (f ((f.trans e).symm p.1), f ((f.trans e).symm p.2))) =
        s (z.1 (e.symm p.1, e.symm p.2))
      exact congrArg s (congrArg z.1 (Prod.ext (f.apply_symm_apply _) (f.apply_symm_apply _)))
  exact congrArg (fun y ↦ Shrink.mulEquiv (h2Equiv hg (fun _ _ ↦ rfl) y)) key

/-- (S1) for `ℤ/n`: `e_{f ∘ e}(f^* u) = e_e(u)`. -/
theorem eZ_h2Triv {n : ℕ} [NeZero n] (hg : 0 < g) (f : G ≃ₜ* G')
    (e : G' ≃ₜ* ProfiniteSurfaceGroup g 0) (u : H2lc G' (TrivZ G' n)) :
    eZ hg (f.trans e) (h2Triv f.toMulEquiv.toMonoidHom f.continuous u) = eZ hg e u := by
  letI : MulDistribMulAction G (TrivZ G' n) := trivialAction G _
  exact h2EquivAny_comap (M := TrivZ G' n) hg f e (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) u

/-- **(S1) for `M_X/n`**: `M_X/n(f)` sends the relator value `φ₀(f ∘ e)` of `G` to the relator
value `φ₀(e)` of `G'`. -/
theorem mxModMap_phi0 {n : ℕ} [NeZero n] (hg : 0 < g) (f : G ≃ₜ* G')
    (e : G' ≃ₜ* ProfiniteSurfaceGroup g 0) :
    mxModMap (n := n) f.toMulEquiv.toMonoidHom f.continuous (phi0 hg (f.trans e)) =
      phi0 hg e := by
  apply (MXmod.toHom G' n).injective
  refine MonoidHom.ext fun u ↦ ?_
  exact eZ_h2Triv hg f e u

/-- (S1), second form: `M_X/n(f)(φ₀(e₀)) = φ₀(f⁻¹ ∘ e₀)` for an orientation `e₀` of `G`. -/
theorem mxModMap_phi0_symm {n : ℕ} [NeZero n] (hg : 0 < g) (f : G ≃ₜ* G')
    (e₀ : G ≃ₜ* ProfiniteSurfaceGroup g 0) :
    mxModMap (n := n) f.toMulEquiv.toMonoidHom f.continuous (phi0 hg e₀) =
      phi0 hg (f.symm.trans e₀) := by
  have h : f.trans (f.symm.trans e₀) = e₀ :=
    ContinuousMulEquiv.ext fun γ ↦ congrArg e₀ (f.symm_apply_apply γ)
  have := mxModMap_phi0 (n := n) hg f (f.symm.trans e₀)
  rw [h] at this
  exact this

end Naturality

/-! ### (S3) Homomorphisms out of a cuspidal inertia group -/

section Generation

/-- **(S3) generation**: let `I ≤ Δ` with `Θ(I) = ⟨c⟩‾` for an isomorphism
`Θ : Δ ≃ₜ* Π̂_{G,1}` (`c` the cusp generator). Two continuous homomorphisms from `I` to a
Hausdorff group which agree on `Θ⁻¹(c)` are equal. -/
theorem monoidHom_eq_of_cuspHat {Δ : Type*} [Group Δ] [TopologicalSpace Δ] {G : ℕ}
    (I : Subgroup Δ) (Θ : Δ ≃ₜ* ProfiniteSurfaceGroup G 1)
    (hI : I.map Θ.toMulEquiv.toMonoidHom = inertia 0)
    (hc : Θ.symm (CuspCentral.cuspHat G) ∈ I) {A : Type*} [Group A] [TopologicalSpace A]
    [T2Space A] {f₁ f₂ : I →* A} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (h : f₁ ⟨_, hc⟩ = f₂ ⟨_, hc⟩) : f₁ = f₂ := by
  have hIset : (I : Set Δ) = Θ ⁻¹' (inertia (g := G) (r := 1) 0 : Set _) := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_preimage, SetLike.mem_coe, ← hI]
      exact Subgroup.mem_map_of_mem _ hy
    · intro hy
      rw [Set.mem_preimage, SetLike.mem_coe, ← hI] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have : z = y := Θ.injective hzy
      rw [← this]
      exact hz
  have hIc : IsClosed (I : Set Δ) := by
    rw [hIset]
    exact (Subgroup.isClosed_topologicalClosure _).preimage Θ.continuous
  let E : Subgroup I := MonoidHom.eqLocus f₁ f₂
  have hEc : IsClosed (E : Set I) := isClosed_eq h₁ h₂
  let T : Subgroup (ProfiniteSurfaceGroup G 1) :=
    (E.map I.subtype).map Θ.toMulEquiv.toMonoidHom
  have hTc : IsClosed (T : Set (ProfiniteSurfaceGroup G 1)) := by
    rw [Subgroup.coe_map, Subgroup.coe_map]
    exact Θ.toHomeomorph.isClosedMap _ (hIc.isClosedEmbedding_subtypeVal.isClosedMap _ hEc)
  have hcT : CuspCentral.cuspHat G ∈ T :=
    ⟨Θ.symm (CuspCentral.cuspHat G), ⟨⟨_, hc⟩, h, rfl⟩, Θ.apply_symm_apply _⟩
  have hIT : inertia (g := G) (r := 1) 0 ≤ T :=
    Subgroup.topologicalClosure_minimal _ ((Subgroup.zpowers_le).2 hcT) hTc
  refine MonoidHom.ext fun i ↦ ?_
  have h1 : Θ.toMulEquiv.toMonoidHom (i : Δ) ∈ T :=
    hIT (by rw [← hI]; exact Subgroup.mem_map_of_mem _ i.2)
  obtain ⟨y, ⟨j, hj, rfl⟩, hy⟩ := h1
  have : j = i := Subtype.ext (Θ.injective hy)
  rw [← this]
  exact hj

end Generation

/-! ### (S2) The relator formula for the synchronisation -/

section Sync

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L} {hH : D.H ≤ D.HL}
  [Nonempty (⊤ : X.Opens)]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {U : X.Opens} [Nonempty U] {W₀ : ValuationSubring Ω} {x : X} {π : (F D)ˣ}

attribute [local instance] instTrivMu

include hk hτ in
/-- **(S2) The synchronisation at the cusp generator is the inverse relator value**: for
orientations `Θ : Δ_{U_x} ≃ₜ* Π̂_{G,1}`, `Θ₀ : Δ_X ≃ₜ* Π̂_{G,0}` compatible with the filling
maps and with `Θ⁻¹(c) ∈ I_x`, the component of `syncEquiv (Θ⁻¹ c) ∈ M_X` at every Kummer index
`n` is `φ₀(Θ₀)⁻¹`, the inverse of the relator-value map `H²(Δ_X, ℤ/n) ≅ ℤ/n` of `Θ₀`.
(From `h2EquivAny_mk`: `e_{Θ₀}[Φ] = χ_n(c)⁻¹` for a cusp pushout `(Φ, Ψ)` along `χ_n`;
`mk_eq_natIso`: `[Φ] = natIso_*(taut)`; `h2EquivAny_h2Map`, `eMX_isTaut`:
`natIso(φ₀) = χ_n(c)⁻¹`; `natIso_syncEquiv`.) -/
theorem proj_syncEquiv_cuspHat (hgen : 0 < (curveGenus k X).toNat) (hUx : (U : Set X)ᶜ = {x})
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    {G : ℕ} (hG : 0 < G)
    (Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ* ProfiniteSurfaceGroup G 1)
    (Θ₀ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ* ProfiniteSurfaceGroup G 0)
    (hfill : ∀ γ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U),
      Θ₀ (fundamentalGroupMap (X.homOfLE le_top) (specPoint_genericL_homOfLE D X eL le_top) γ) =
        CuspCentral.fillHat G (Θ γ))
    (hc : Θ.symm (CuspCentral.cuspHat G) ∈ cuspInertia D X eL hH U W₀)
    (i : KummerIndex (F D)) :
    MXHat.proj i (syncEquiv hH hk hτ U hgen hUx hW₀ hW₀U hπW hπ ⟨_, hc⟩) =
      (phi0 hG Θ₀)⁻¹ := by
  obtain ⟨-, -, -, ⟨Φ, Ψ, hΦ, hΦΨ⟩, -⟩ :=
    cuspCentral_class_eq_chernClass hk hτ (n := i.n) hgen hUx hW₀ hW₀U hπW hπ
  haveI := finite_mxmod (n := i.n) hG Θ₀
  have e1 : natIso hH hk hτ i.n hgen (phi0 hG Θ₀) =
      (chiN hH hk hτ i.n U hgen hUx hW₀ hW₀U hπW hπ ⟨_, hc⟩)⁻¹ :=
    (congrArg (natIso hH hk hτ i.n hgen) (eMX_isTaut hG Θ₀ (isTaut_tautX hk hτ hgen))).symm.trans
      ((h2EquivAny_h2Map hG Θ₀ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (natIso hH hk hτ i.n hgen).toMonoidHom (tautX hH hk hτ i.n hgen)).symm.trans
        ((congrArg (h2EquivAny hG Θ₀ (fun _ _ ↦ rfl))
          (IsCuspPushout.mk_eq_natIso hk hτ hgen hUx hW₀ hW₀U hπW hπ hΦ hΦΨ)).symm.trans
          (hΦΨ.h2EquivAny_mk hG Θ Θ₀ hfill hc hΦ)))
  apply (natIso hH hk hτ i.n hgen).injective
  calc natIso hH hk hτ i.n hgen
        (MXHat.proj i (syncEquiv hH hk hτ U hgen hUx hW₀ hW₀U hπW hπ ⟨_, hc⟩))
      = chiN hH hk hτ i.n U hgen hUx hW₀ hW₀U hπW hπ ⟨_, hc⟩ :=
        natIso_syncEquiv hk hτ hgen hUx hW₀ hW₀U hπW hπ i.n ⟨_, hc⟩
    _ = ((chiN hH hk hτ i.n U hgen hUx hW₀ hW₀U hπW hπ ⟨_, hc⟩)⁻¹)⁻¹ := (inv_inv _).symm
    _ = (natIso hH hk hτ i.n hgen (phi0 hG Θ₀))⁻¹ := congrArg (·⁻¹) e1.symm
    _ = natIso hH hk hτ i.n hgen (phi0 hG Θ₀)⁻¹ := (map_inv _ _).symm

/-- `syncEquiv` is continuous (each component is `natIso_n⁻¹ ∘ χ_n`, into a discrete group). -/
theorem continuous_syncEquiv (hgen : 0 < (curveGenus k X).toNat) (hUx : (U : Set X)ᶜ = {x})
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω)) :
    Continuous (syncEquiv hH hk hτ U hgen hUx hW₀ hW₀U hπW hπ) := by
  refine continuous_induced_rng.2 (continuous_pi fun i ↦ ?_)
  exact (continuous_of_discreteTopology (f := fun z : Mu i.n Ω ↦
      ((natIso hH hk hτ i.n hgen).symm z :
        MXmod π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) i.n))).comp
    ((ZHatOne.continuous_proj i).comp
      (CuspCentral.cuspInertiaZHatEquiv hk hτ hgen U hUx hW₀ hW₀U hπW hπ).continuous)

/-- **(S3) for the synchronisation**: a continuous homomorphism `I_x → M_X` agreeing with
`syncEquiv` at `Θ⁻¹(c)` (`Θ(I_x) = ⟨c⟩‾`) is `syncEquiv`. -/
theorem eq_syncEquiv_of_cuspHat (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    {G : ℕ} (Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ* ProfiniteSurfaceGroup G 1)
    (hI : (cuspInertia D X eL hH U W₀).map Θ.toMulEquiv.toMonoidHom = inertia 0)
    (ι : cuspInertia D X eL hH U W₀ →* MXHat π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (F D))
    (hι : Continuous ι)
    (h : ι ⟨_, cuspHat_mem Θ hI⟩ =
      syncEquiv hH hk hτ U hgen hUx hW₀ hW₀U hπW hπ ⟨_, cuspHat_mem Θ hI⟩) :
    ι = (syncEquiv hH hk hτ U hgen hUx hW₀ hW₀U hπW hπ).toMonoidHom :=
  monoidHom_eq_of_cuspHat _ Θ hI (cuspHat_mem Θ hI) hι
    (continuous_syncEquiv hk hτ hgen hUx hW₀ hW₀U hπW hπ) h

include hk hτ in
/-- **(S2) + (S3)**: a continuous homomorphism `ι : I_x → M_X` whose value at `Θ⁻¹(c)` has every
component `φ₀(Θ₀)⁻¹` is the synchronisation. -/
theorem eq_syncEquiv_of_proj (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    {G : ℕ} (hG : 0 < G)
    (Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ* ProfiniteSurfaceGroup G 1)
    (Θ₀ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ* ProfiniteSurfaceGroup G 0)
    (hI : (cuspInertia D X eL hH U W₀).map Θ.toMulEquiv.toMonoidHom = inertia 0)
    (hfill : ∀ γ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U),
      Θ₀ (fundamentalGroupMap (X.homOfLE le_top) (specPoint_genericL_homOfLE D X eL le_top) γ) =
        CuspCentral.fillHat G (Θ γ))
    (ι : cuspInertia D X eL hH U W₀ →* MXHat π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (F D))
    (hι : Continuous ι)
    (h : ∀ i : KummerIndex (F D), MXHat.proj i (ι ⟨_, cuspHat_mem Θ hI⟩) = (phi0 hG Θ₀)⁻¹) :
    ι = (syncEquiv hH hk hτ U hgen hUx hW₀ hW₀U hπW hπ).toMonoidHom :=
  eq_syncEquiv_of_cuspHat hk hτ hgen hUx hW₀ hW₀U hπW hπ Θ hI ι hι
    (Subtype.ext (funext fun i ↦ (h i).trans
      (proj_syncEquiv_cuspHat hk hτ hgen hUx hW₀ hW₀U hπW hπ hG Θ Θ₀ hfill
        (cuspHat_mem Θ hI) i).symm))

/-! ### Transport of the synchronisation along isomorphisms of the group-theoretic data -/

variable {k' Ω' : Type u} [Field k'] [IsAlgClosed k'] [CharZero k']
  [Field Ω'] [Algebra k' Ω'] [IsSepClosed Ω'] {t' : Ω'} [IsGalois (K₀ k' t') Ω']
  {D' : GaloisData k' t'}
  {X' : Scheme.{u}} [X'.Over (Spec (.of k'))] [IsCurveOver k' X'] [IsIntegral X']
  {eL' : X'.functionField ≃+* D'.L} {hH' : D'.H ≤ D'.HL}
  [Nonempty (⊤ : X'.Opens)]
  (hk' : ∀ c : k', ((eL' (algebraMap k' X'.functionField c) : D'.L) : Ω') = algebraMap k' Ω' c)
  {τ' : X'.functionField} (hτ' : ((eL' τ' : D'.L) : Ω') = t')
  {U' : X'.Opens} [Nonempty U'] {W₀' : ValuationSubring Ω'} {x' : X'} {π' : (F D')ˣ}

include hk hτ hk' hτ' in
/-- **The synchronisation is transported by isomorphisms of the group-theoretic data**: let
`Ξ : Δ_{U_x} ≃ₜ* Δ_{U'_{x'}}` and `Ξ₀ : Δ_X ≃ₜ* Δ_{X'}` be compatible with the filling maps and
with the cuspidal inertia groups (`Ξ(I_x) = I_{x'}`). Then `M_X(Ξ₀) ∘ sync_x = sync_{x'} ∘ Ξ` on
`I_x` ([AbsTopIII] Prop 1.4 (ii): the synchronisation is constructed group-theoretically from
`Δ_{U_x} ↠ Δ_X`). Proof: orientations `Θ', Θ₀'` of the target (`exists_cuspCentral_equiv`)
pull back to `Θ = Θ' ∘ Ξ`, `Θ₀ = Θ₀' ∘ Ξ₀`; (S2) on both sides, (S1) for `Ξ₀`, and (S3). -/
theorem mxHatCongr_syncEquiv [CharZero Ω] [CharZero Ω']
    (hgen : 0 < (curveGenus k X).toNat) (hUx : (U : Set X)ᶜ = {x})
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    (hgen' : 0 < (curveGenus k' X').toNat) (hUx' : (U' : Set X')ᶜ = {x'})
    (hW₀' : IsCentredOn D' X' eL' ⊤ W₀') (hW₀U' : ¬ IsCentredOn D' X' eL' U' W₀')
    (hπW' : W₀'.valuation ((π' : F D') : Ω') < 1)
    (hπ' : ∀ f ∈ F D', W₀'.valuation f < 1 → W₀'.valuation f ≤ W₀'.valuation ((π' : F D') : Ω'))
    (Ξ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' X' eL' U'))
    (Ξ₀ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' X' eL' ⊤))
    (hfill : ∀ γ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U),
      Ξ₀ (fundamentalGroupMap (X.homOfLE le_top) (specPoint_genericL_homOfLE D X eL le_top) γ) =
        fundamentalGroupMap (X'.homOfLE le_top) (specPoint_genericL_homOfLE D' X' eL' le_top)
          (Ξ γ))
    (hI : (cuspInertia D X eL hH U W₀).map Ξ.toMulEquiv.toMonoidHom =
      cuspInertia D' X' eL' hH' U' W₀')
    (σ : cuspInertia D X eL hH U W₀)
    (hσ : Ξ (σ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) ∈ cuspInertia D' X' eL' hH' U' W₀') :
    mxHatCongr (F D) (F D') Ξ₀ (syncEquiv hH hk hτ U hgen hUx hW₀ hW₀U hπW hπ σ) =
      syncEquiv hH' hk' hτ' U' hgen' hUx' hW₀' hW₀U' hπW' hπ' ⟨_, hσ⟩ := by
  obtain ⟨Θ', Θ₀', hI', hfill', -, -⟩ :=
    CuspCentral.exists_cuspCentral_equiv D' eL' hH' hk' hτ' U' hUx' hW₀' hW₀U'
  let Θ := Ξ.trans Θ'
  let Θ₀ := Ξ₀.trans Θ₀'
  have hfillΘ : ∀ γ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U),
      Θ₀ (fundamentalGroupMap (X.homOfLE le_top) (specPoint_genericL_homOfLE D X eL le_top) γ) =
        CuspCentral.fillHat _ (Θ γ) :=
    fun γ ↦ (congrArg Θ₀' (hfill γ)).trans (hfill' (Ξ γ))
  have hIΘ : (cuspInertia D X eL hH U W₀).map Θ.toMulEquiv.toMonoidHom = inertia 0 :=
    (Subgroup.map_map (cuspInertia D X eL hH U W₀) Θ'.toMulEquiv.toMonoidHom
      Ξ.toMulEquiv.toMonoidHom).symm.trans
      ((congrArg (Subgroup.map Θ'.toMulEquiv.toMonoidHom) hI).trans hI')
  have hc := cuspHat_mem Θ hIΘ
  have hc' := cuspHat_mem Θ' hI'
  have hmem : ∀ σ : cuspInertia D X eL hH U W₀,
      Ξ.toMulEquiv.toMonoidHom.comp (cuspInertia D X eL hH U W₀).subtype σ ∈
        cuspInertia D' X' eL' hH' U' W₀' :=
    fun σ ↦ hI ▸ Subgroup.mem_map_of_mem _ σ.2
  let f₁ : cuspInertia D X eL hH U W₀ →*
      MXHat π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' X' eL' ⊤) (F D') :=
    (mxHatCongr (F D) (F D') Ξ₀).toMulEquiv.toMonoidHom.comp
      (syncEquiv hH hk hτ U hgen hUx hW₀ hW₀U hπW hπ).toMonoidHom
  let f₂ : cuspInertia D X eL hH U W₀ →*
      MXHat π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' X' eL' ⊤) (F D') :=
    (syncEquiv hH' hk' hτ' U' hgen' hUx' hW₀' hW₀U' hπW' hπ').toMonoidHom.comp
      ((Ξ.toMulEquiv.toMonoidHom.comp (cuspInertia D X eL hH U W₀).subtype).codRestrict _ hmem)
  have hf₁ : Continuous f₁ := (mxHatCongr (F D) (F D') Ξ₀).continuous.comp
    (continuous_syncEquiv hk hτ hgen hUx hW₀ hW₀U hπW hπ)
  have hf₂ : Continuous f₂ := (continuous_syncEquiv hk' hτ' hgen' hUx' hW₀' hW₀U' hπW' hπ').comp
    ((Ξ.continuous.comp continuous_subtype_val).subtype_mk _)
  have h4 : (⟨Ξ (Θ.symm (CuspCentral.cuspHat _)), hmem ⟨_, hc⟩⟩ :
      cuspInertia D' X' eL' hH' U' W₀') = ⟨_, hc'⟩ := Subtype.ext (Ξ.apply_symm_apply _)
  have hval : f₁ ⟨_, hc⟩ = f₂ ⟨_, hc⟩ := by
    refine Subtype.ext (funext fun i ↦ ?_)
    have h1 := proj_syncEquiv_cuspHat hk hτ hgen hUx hW₀ hW₀U hπW hπ hgen' Θ Θ₀ hfillΘ hc
      (⟨i.n, Nat.cast_ne_zero.2 i.n_ne_zero⟩ : KummerIndex (F D))
    have h2 := proj_syncEquiv_cuspHat hk' hτ' hgen' hUx' hW₀' hW₀U' hπW' hπ' hgen' Θ' Θ₀'
      hfill' hc' i
    have h3 := mxModMap_phi0 (n := i.n) hgen' Ξ₀ Θ₀'
    calc ((f₁ ⟨_, hc⟩ : MXHat _ (F D')) : ∀ i : KummerIndex (F D'), MXmod _ i.n) i
        = mxModMap Ξ₀.toMulEquiv.toMonoidHom Ξ₀.continuous
            (MXHat.proj ⟨i.n, Nat.cast_ne_zero.2 i.n_ne_zero⟩
              (syncEquiv hH hk hτ U hgen hUx hW₀ hW₀U hπW hπ ⟨_, hc⟩)) := rfl
      _ = mxModMap Ξ₀.toMulEquiv.toMonoidHom Ξ₀.continuous (phi0 (n := i.n) hgen' Θ₀)⁻¹ :=
        congrArg _ h1
      _ = (phi0 (n := i.n) hgen' Θ₀')⁻¹ := (map_inv _ _).trans (congrArg (·⁻¹) h3)
      _ = MXHat.proj i (syncEquiv hH' hk' hτ' U' hgen' hUx' hW₀' hW₀U' hπW' hπ' ⟨_, hc'⟩) :=
        h2.symm
      _ = ((f₂ ⟨_, hc⟩ : MXHat _ (F D')) : ∀ i : KummerIndex (F D'), MXmod _ i.n) i :=
        congrArg (fun s ↦ MXHat.proj i
          (syncEquiv hH' hk' hτ' U' hgen' hUx' hW₀' hW₀U' hπW' hπ' s)) h4.symm
  exact DFunLike.congr_fun (monoidHom_eq_of_cuspHat _ Θ hIΘ hc hf₁ hf₂ hval) σ

end Sync

/-! ### The case of `X_{k̄}` (`syncEquivBar`) -/

section Bar

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} {hτ : Transcendental k τ}
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  {U : (baseChangeKbar k X).Opens} [Nonempty U] {x : baseChangeKbar k X}
  {W₀ : ValuationSubring (FFClosure X)} {π : (F (barData k hτ))ˣ}

/-- **(S2) for `X_{k̄}`**: the component of `syncEquivBar (Θ⁻¹ c)` at every Kummer index is
`φ₀(Θ₀)⁻¹`, for orientations compatible with the filling maps and with `Θ⁻¹(c) ∈ I_x`. -/
theorem proj_syncEquivBar_cuspHat (hg : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set (baseChangeKbar k X))ᶜ = {x})
    (hW₀ : IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ W₀)
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U W₀)
    (hπW : W₀.valuation ((π : F (barData k hτ)) : FFClosure X) < 1)
    (hπ : ∀ f ∈ F (barData k hτ), W₀.valuation f < 1 →
      W₀.valuation f ≤ W₀.valuation ((π : F (barData k hτ)) : FFClosure X))
    {G : ℕ} (hG : 0 < G) (Θ : DeltaBar k hτ U ≃ₜ* ProfiniteSurfaceGroup G 1)
    (Θ₀ : DeltaBarX k hτ ≃ₜ* ProfiniteSurfaceGroup G 0)
    (hfill : ∀ γ : DeltaBar k hτ U,
      Θ₀ (fundamentalGroupMap ((baseChangeKbar k X).homOfLE le_top)
        (specPoint_genericL_homOfLE (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) le_top)
          γ) = CuspCentral.fillHat G (Θ γ))
    (hc : Θ.symm (CuspCentral.cuspHat G) ∈
      cuspInertia (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barData_H_le k hτ) U W₀)
    (i : KummerIndex (F (barData k hτ))) :
    MXHat.proj i (syncEquivBar hg hUx hW₀ hW₀U hπW hπ ⟨_, hc⟩) = (phi0 hG Θ₀)⁻¹ :=
  proj_syncEquiv_cuspHat (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ) (genus_bar_pos hg)
    hUx hW₀ hW₀U hπW hπ hG Θ Θ₀ hfill hc i

variable {k' : Type u} [Field k'] [CharZero k'] {X' : Scheme.{u}} [X'.Over (Spec (.of k'))]
  [IsCurveOver k' X'] [IsIntegral X'] {τ' : X'.functionField} {hτ' : Transcendental k' τ'}
  [IsGalois (K₀ k' (coordT τ')) (FFClosure X')]
  {U' : (baseChangeKbar k' X').Opens} [Nonempty U'] {x' : baseChangeKbar k' X'}
  {W₀' : ValuationSubring (FFClosure X')} {π' : (F (barData k' hτ'))ˣ}

set_option synthInstance.maxHeartbeats 400000 in
-- the fundamental groups of `U_{k̄}`, `X_{k̄}` are slow for unification
set_option maxHeartbeats 1600000 in
-- the fundamental groups of `U_{k̄}`, `X_{k̄}` are slow for unification
/-- **Transport of the synchronisation for `X_{k̄}`, `X'_{k̄'}`**: for
`Ξ : Δ_{U_x} ≃ₜ* Δ_{U'_{x'}}`, `Ξ₀ : Δ_X ≃ₜ* Δ_{X'}` compatible with the filling maps and with
`Ξ(I_x) = I_{x'}`, `M_X(Ξ₀) ∘ syncEquivBar_x = syncEquivBar_{x'} ∘ Ξ` (`mxHatCongr_syncEquiv`). -/
theorem mxHatCongr_syncEquivBar [CharZero (FFClosure X)] [CharZero (FFClosure X')]
    (hg : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set (baseChangeKbar k X))ᶜ = {x})
    (hW₀ : IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ W₀)
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U W₀)
    (hπW : W₀.valuation ((π : F (barData k hτ)) : FFClosure X) < 1)
    (hπ : ∀ f ∈ F (barData k hτ), W₀.valuation f < 1 →
      W₀.valuation f ≤ W₀.valuation ((π : F (barData k hτ)) : FFClosure X))
    (hg' : 0 < (curveGenus k' X').toNat)
    (hUx' : (U' : Set (baseChangeKbar k' X'))ᶜ = {x'})
    (hW₀' : IsCentredOn (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ') ⊤ W₀')
    (hW₀U' : ¬ IsCentredOn (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ') U' W₀')
    (hπW' : W₀'.valuation ((π' : F (barData k' hτ')) : FFClosure X') < 1)
    (hπ' : ∀ f ∈ F (barData k' hτ'), W₀'.valuation f < 1 →
      W₀'.valuation f ≤ W₀'.valuation ((π' : F (barData k' hτ')) : FFClosure X'))
    (Ξ : DeltaBar k hτ U ≃ₜ* DeltaBar k' hτ' U') (Ξ₀ : DeltaBarX k hτ ≃ₜ* DeltaBarX k' hτ')
    (hfill : ∀ γ : DeltaBar k hτ U,
      Ξ₀ (fundamentalGroupMap ((baseChangeKbar k X).homOfLE le_top)
        (specPoint_genericL_homOfLE (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) le_top)
          γ) =
        fundamentalGroupMap ((baseChangeKbar k' X').homOfLE le_top)
          (specPoint_genericL_homOfLE (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ')
            le_top) (Ξ γ))
    (hI : (cuspInertia (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barData_H_le k hτ)
        U W₀).map Ξ.toMulEquiv.toMonoidHom =
      cuspInertia (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ')
        (barData_H_le k' hτ') U' W₀')
    (σ : cuspInertia (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barData_H_le k hτ)
      U W₀)
    (hσ : Ξ (σ : DeltaBar k hτ U) ∈ cuspInertia (barData k' hτ') (baseChangeKbar k' X')
      (barEquivL k' hτ') (barData_H_le k' hτ') U' W₀') :
    mxHatCongr (F (barData k hτ)) (F (barData k' hτ')) Ξ₀
        (syncEquivBar hg hUx hW₀ hW₀U hπW hπ σ) =
      syncEquivBar hg' hUx' hW₀' hW₀U' hπW' hπ' ⟨_, hσ⟩ :=
  mxHatCongr_syncEquiv (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ)
    (barEquivL_algebraMap k' hτ') (barEquivL_tau k' hτ') (genus_bar_pos hg) hUx hW₀ hW₀U hπW hπ
    (genus_bar_pos hg') hUx' hW₀' hW₀U' hπW' hπ' Ξ Ξ₀ hfill hI σ hσ

end Bar

end Iut.Reconstruction.Thm19
