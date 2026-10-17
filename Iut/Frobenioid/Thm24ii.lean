/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.InvCompat
import Iut.Frobenioid.KummerTransportGalois
import Iut.Frobenioid.ReciprocityTransport

/-!
# Towards [FrdII], Theorem 2.4(ii): `F_N(X) ≅ F_N(Ψ X)` on the Galois side

[FrdII], Theorem 2.4(ii): "if `Φ₁`, `Φ₂` are fieldwise saturated, then the isomorphism
`F_N(A₁) ≅ F_N(A₂)` of (i) is compatible with the natural isomorphisms `F_N(A_i) ≅ ℤ/Nℤ`".

For `Ψ : GFrob p E Γ ≌ GFrob p E' Γ`, `α : G_E ≃ₜ* G_{E'}` and `τ ∈ G_{E'}` with the twisted
rational functions `ρ = ratFunTw τ` of `Ψ X` equivariant for `jΨ` (as provided by
`exists_galHom_compat`), and an `(n, H)`-saturated `X = (G_E/N, a)` with `H`, `α(H)` open
(`L = K̄^H`, `L' = K̄^{α(H)}`):

* `galPairEquiv : Gal(K̄/L) ≃ₜ* Gal(K̄/L')` (through `H ≅ α(H)`);
* `betaPsi : μ_N(K̄) → μ_N(K̄)`, `ζ ↦ ρ(Ψ(γ⁻¹ ζ))` (`γ` the rational functions of `X`), equivariant
  for `galPairEquiv` (`betaPsi_smul`);
* `fnPsi : F_N(Ψ X) → H²(L', μ_N)` (via `ρ`), and **`fnPsi_fngEquiv`**: `fnPsi ∘ fngEquiv` is
  `Φ₂ ∘ fnEquivH2L`, `Φ₂ = PairCompat.h2PairMap galPairEquiv betaPsi`;
* **`thm24ii_of_pairing`**: if one pairing value `⟨χ, ζ⟩ ∈ (ℤ/N)^×` over `L` is preserved by
  `(galPairEquiv, betaPsi)`, then `h2MuEquiv_{L'} ∘ fnPsi ∘ fngEquiv = fnEquiv`, i.e. Theorem
  2.4(ii) for `X`. Verifying the pairing condition for `C_v` (`Γ = ℚ`) is the remaining arithmetic
  input (`Plans/MR17Handoff.md`); it fails in general for `C^⊢_v` (Remark 2.4.2).
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

namespace ContH2Aux

variable {G₁ G₂ G₃ M₁ M₂ M₃ : Type*} [Group G₁] [TopologicalSpace G₁] [Group G₂]
  [TopologicalSpace G₂] [Group G₃] [TopologicalSpace G₃] [CommGroup M₁] [CommGroup M₂]
  [CommGroup M₃] [MulDistribMulAction G₁ M₁] [MulDistribMulAction G₂ M₂]
  [MulDistribMulAction G₃ M₃]

/-- Composition of the maps on `H²`, with a given composite. -/
theorem map_map_eq (φ₁ : G₂ →* G₁) (hφ₁ : Continuous φ₁) (ψ₁ : M₁ →* M₂)
    (h₁ : ∀ (g : G₂) (m : M₁), ψ₁ (φ₁ g • m) = g • ψ₁ m) (φ₂ : G₃ →* G₂) (hφ₂ : Continuous φ₂)
    (ψ₂ : M₂ →* M₃) (h₂ : ∀ (g : G₃) (m : M₂), ψ₂ (φ₂ g • m) = g • ψ₂ m) (φ : G₃ →* G₁)
    (hφ : Continuous φ) (ψ : M₁ →* M₃) (h : ∀ (g : G₃) (m : M₁), ψ (φ g • m) = g • ψ m)
    (hφeq : ∀ g, φ₁ (φ₂ g) = φ g) (hψeq : ∀ m, ψ₂ (ψ₁ m) = ψ m) (x : ContH2 G₁ M₁) :
    ContH2.map φ₂ hφ₂ ψ₂ h₂ (ContH2.map φ₁ hφ₁ ψ₁ h₁ x) = ContH2.map φ hφ ψ h x := by
  induction x using ContH2.induction_on with | h c => ?_
  rw [ContH2.map_mk, ContH2.map_mk, ContH2.map_mk]
  congr 1
  refine ContH2.cocycles_ext fun g g' => ?_
  rw [ContH2.cocyclesMap_apply, ContH2.cocyclesMap_apply, ContH2.cocyclesMap_apply, hφeq, hφeq,
    hψeq]

end ContH2Aux

lemma comp_symm_apply {A B C D : Type*} [Monoid A] [Monoid B] [Monoid C] [Monoid D] (e : A ≃* B)
    (f : A →* C) (g : C →* D) (a : A) :
    (g.comp (f.comp e.symm.toMonoidHom)) (e a) = g (f a) := by
  simp

namespace Saturation

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] {U : Subgroup G}
  [U.Normal] [IsMulCommutative U] {K : Type*} [Group K] [TopologicalSpace K] {j : K →* G}
  (hj : Continuous j) (H : Subgroup K) (n : ℕ) {Q : Type*} [Group Q] [TopologicalSpace Q]
  {M : Type*} [CommGroup M] [MulDistribMulAction Q M]

include hj in
/-- A map out of `H²(H_A, μ_n(U))` along `Q → H ↠ H_A` kills
`Ker(H²(H_A, μ_n(U)) → H²(H, μ_n(U)))`. -/
lemma ker_infl₂_le_map (g : Q →* H) (hg : Continuous g) (r : KummerClass.mu U n →* M)
    (hr : ∀ (k : Q) (m : KummerClass.mu U n), r (subHomG j H (g k) • m) = k • r m)
    (hφ : Continuous ((subHomG j H).comp g)) :
    (infl₂ (subHomG j H) (continuous_subHomG j hj H) (KummerClass.mu U n)).ker ≤
      (ContH2.map ((subHomG j H).comp g) hφ r hr).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [← ContH2Aux.map_map_eq (subHomG j H) (continuous_subHomG j hj H)
    (toPull (subHomG j H) (KummerClass.mu U n)) (fun _ _ => rfl) g hg
    (r : Pull (subHomG j H) (KummerClass.mu U n) →* M) (fun k m => hr k m)
    ((subHomG j H).comp g) hφ r hr (fun _ => rfl) (fun _ => rfl) x]
  change ContH2.map _ _ _ _ (infl₂ _ _ _ x) = 1
  rw [hx, map_one]

section PairGen

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] {U : Subgroup G}
  [U.Normal] [IsMulCommutative U] {K : Type*} [Group K] [TopologicalSpace K] {j : K →* G}
  (H : Subgroup K) (n : ℕ)
variable {G' : Type*} [Group G'] [TopologicalSpace G'] [DiscreteTopology G'] {U' : Subgroup G'}
  [U'.Normal] [IsMulCommutative U'] {K' : Type*} [Group K'] [TopologicalSpace K'] {j' : K' →* G'}
variable (φ : G ≃* G') (hU : ∀ u, u ∈ U ↔ φ u ∈ U') (α : K ≃ₜ* K')
  (hjα : ∀ k, j' (α k) = φ (j k))
variable {Q Q' : Type*} [Group Q] [TopologicalSpace Q] [Group Q'] [TopologicalSpace Q']
  (g : Q →* H) (g' : Q' →* H.map (α : K →* K')) (αQ : Q ≃ₜ* Q')
  (hαQ : ∀ q, subKEquiv H α (g q) = g' (αQ q))
  {M M' : Type*} [CommGroup M] [MulDistribMulAction Q M] [CommGroup M']
  [MulDistribMulAction Q' M'] (r : KummerClass.mu U n →* M)
  (hr : ∀ (q : Q) (m : KummerClass.mu U n), r (subHomG j H (g q) • m) = q • r m)
  (r' : KummerClass.mu U' n →* M')
  (hr' : ∀ (q : Q') (m : KummerClass.mu U' n),
    r' (subHomG j' (H.map (α : K →* K')) (g' q) • m) = q • r' m)
  (β : M →* M') (hβr : ∀ m, β (r m) = r' (muEquiv n φ hU m))

include hjα hαQ hr hr' hβr in
/-- `β` is `αQ`-equivariant if `β ∘ r = r' ∘ muEquiv` and `r` is surjective. -/
lemma pair_smul (hrs : Function.Surjective r) (q : Q) (x : M) : β (q • x) = αQ q • β x := by
  obtain ⟨m, rfl⟩ := hrs x
  rw [← hr, hβr, hβr, muEquiv_smul H n φ hU α hjα, ← subHomG_subKEquiv H φ α hjα, hαQ, hr']

include hαQ hβr in
/-- **Transport of `F_N` on the Galois side**: along `r`, `r'`, the map `h2Equiv` becomes
`(αQ⁻¹, β)_*`. -/
theorem map_h2Equiv_eq (hg : Continuous ((subHomG j H).comp g))
    (hg' : Continuous ((subHomG j' (H.map (α : K →* K'))).comp g'))
    (hβ' : ∀ (q : Q') (x : M), β (αQ.symm q • x) = q • β x)
    (y : ContH2 (subAG j H) (KummerClass.mu U n)) :
    ContH2.map ((subHomG j' (H.map (α : K →* K'))).comp g') hg' r' hr'
        (h2Equiv H n φ hU α hjα y) =
      ContH2.map (αQ.symm : Q' →* Q) αQ.symm.continuous β hβ'
        (ContH2.map ((subHomG j H).comp g) hg r hr y) := by
  have hcomp : ∀ (q : Q') (m : KummerClass.mu U n),
      (r'.comp (muEquiv n φ hU).toMonoidHom)
        ((((subHomG j H).comp g).comp (αQ.symm : Q' →* Q)) q • m) =
        q • (r'.comp (muEquiv n φ hU).toMonoidHom) m := fun q m => by
    change r' (muEquiv n φ hU (subHomG j H (g (αQ.symm q)) • m)) = q • r' (muEquiv n φ hU m)
    rw [muEquiv_smul H n φ hU α hjα, ← subHomG_subKEquiv H φ α hjα, hαQ,
      ContinuousMulEquiv.apply_symm_apply, hr']
  have hφ : ∀ q : Q', ((subATEquiv H φ α hjα).symm : _ →* subAG j H)
      ((subHomG j' (H.map (α : K →* K'))).comp g' q) =
        (((subHomG j H).comp g).comp (αQ.symm : Q' →* Q)) q :=
    fun q => by
      change (subAEquiv H φ α hjα).symm (subHomG j' (H.map (α : K →* K')) (g' q)) =
        subHomG j H (g (αQ.symm q))
      rw [MulEquiv.symm_apply_eq, ← subHomG_subKEquiv H φ α hjα, hαQ,
        ContinuousMulEquiv.apply_symm_apply]
  have hcont : Continuous (((subHomG j H).comp g).comp (αQ.symm : Q' →* Q)) :=
    hg.comp αQ.symm.continuous
  refine (ContH2Aux.map_map_eq _ _ _ _ _ hg' r' hr' _ hcont
    (r'.comp (muEquiv n φ hU).toMonoidHom) hcomp hφ (fun _ => rfl) y).trans ?_
  exact (ContH2Aux.map_map_eq _ hg r hr _ αQ.symm.continuous β hβ' _ hcont
    (r'.comp (muEquiv n φ hU).toMonoidHom) hcomp (fun _ => rfl) hβr y).symm

end PairGen

end Saturation

namespace PAdicGalois

open Saturation CategoryTheory IntermediateField

variable {p : ℕ} [hp : Fact p.Prime] {Γ : AddSubgroup ℝ}
variable {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']

local notation "K̄" => PadicAlgCl p

variable (F : GFrob p E Γ ⥤ GFrob p E' Γ) [F.IsEquivalence] (α : GK p E ≃ₜ* GK p E')
  (τ : GK p E') (N : OpenNormalSubgroup (GK p E)) (a : Γ)
  (hρ : ∀ (σ' : GK p E') (v : Model.ouAut (F.obj (XN N a))),
    ratFunTw τ (KummerClass.conjU (Model.ouAut (F.obj (XN N a))) (jPsi F N a α σ') v) =
      σ' • ratFunTw τ v)
  (H : Subgroup (GK p E)) (hH : IsOpen (H : Set (GK p E)))
  (hH' : IsOpen ((H.map (α : GK p E →* GK p E')) : Set (GK p E')))

/-- `Gal(K̄/L) ≅ H ≅ α(H) ≅ Gal(K̄/L')`. -/
noncomputable def galPairEquiv :
    (K̄ ≃ₐ[fixL H] K̄) ≃ₜ* (K̄ ≃ₐ[fixL (H.map (α : GK p E →* GK p E'))] K̄) :=
  (galFixEquiv H hH).trans
    ((subKEquiv H α).trans (galFixEquiv (H.map (α : GK p E →* GK p E')) hH').symm)

lemma galFixEquiv_galPairEquiv (σ : K̄ ≃ₐ[fixL H] K̄) :
    galFixEquiv (H.map (α : GK p E →* GK p E')) hH' (galPairEquiv α H hH hH' σ) =
      subKEquiv H α (galFixEquiv H hH σ) :=
  ContinuousMulEquiv.apply_symm_apply _ _

/-- `H_A ≅ α(H)_{Ψ X}` intertwines `Gal(K̄/L) ↠ H_A` and `Gal(K̄/L') ↠ α(H)_{Ψ X}`. -/
lemma subAEquiv_galLA (σ : K̄ ≃ₐ[fixL H] K̄) :
    subAEquiv H (Model.autEquiv F (XN N a)) α (jPsi_apply F N a α) (galLA N a H hH σ) =
      galLAG (jPsi F N a α) (H.map (α : GK p E →* GK p E')) hH'
        (galPairEquiv α H hH hH' σ) := by
  change _ = subHomG (jPsi F N a α) (H.map (α : GK p E →* GK p E'))
    (galFixEquiv (H.map (α : GK p E →* GK p E')) hH' (galPairEquiv α H hH hH' σ))
  rw [galFixEquiv_galPairEquiv α H hH hH' σ,
    subHomG_subKEquiv H (Model.autEquiv F (XN N a)) α (jPsi_apply F N a α)]
  rfl

variable (n : ℕ) [NeZero n] (hs : IsSaturated N a H n)

/-- `μ_N(X) ≅ μ_N(K̄)` (rational functions; `μ_N`-saturation). -/
noncomputable abbrev uMuE : muX N a n ≃* KummerTheory.Mu n K̄ :=
  MulEquiv.ofBijective (uMu N a n) (uMu_bijective N a n hs.muSat)

/-- **`β_Ψ : μ_N(K̄) → μ_N(K̄)`**, `ζ ↦ ρ(Ψ(γ⁻¹ ζ))`. -/
noncomputable def betaPsi : KummerTheory.Mu n K̄ →* KummerTheory.Mu n K̄ :=
  (muRho (Model.ouAut (F.obj (XN N a))) (ratFunTw τ) n).comp
    ((muEquiv n (Model.autEquiv F (XN N a)) (mem_ouAut_iff F (XN N a))).toMonoidHom.comp
      (uMuE N a H n hs).symm.toMonoidHom)

lemma betaPsi_uMu (m : muX N a n) :
    betaPsi F τ N a H n hs (uMu N a n m) =
      muRho (Model.ouAut (F.obj (XN N a))) (ratFunTw τ) n
        (muEquiv n (Model.autEquiv F (XN N a)) (mem_ouAut_iff F (XN N a)) m) :=
  comp_symm_apply (uMuE N a H n hs)
    (muEquiv n (Model.autEquiv F (XN N a)) (mem_ouAut_iff F (XN N a))).toMonoidHom
    (muRho (Model.ouAut (F.obj (XN N a))) (ratFunTw τ) n) m

lemma galFixMulEquiv_galPairEquiv (σ : K̄ ≃ₐ[fixL H] K̄) :
    subKEquiv H α (galFixMulEquiv H hH σ) =
      galFixMulEquiv (H.map (α : GK p E →* GK p E')) hH' (galPairEquiv α H hH hH' σ) :=
  (galFixEquiv_galPairEquiv α H hH hH' σ).symm

include hρ in
/-- **`β_Ψ` is `galPairEquiv`-equivariant.** -/
lemma betaPsi_smul (σ : K̄ ≃ₐ[fixL H] K̄) (ζ : KummerTheory.Mu n K̄) :
    betaPsi F τ N a H n hs (σ • ζ) = galPairEquiv α H hH hH' σ • betaPsi F τ N a H n hs ζ :=
  pair_smul H n (Model.autEquiv F (XN N a)) (mem_ouAut_iff F (XN N a)) α (jPsi_apply F N a α)
    (galFixMulEquiv H hH).toMonoidHom
    (galFixMulEquiv (H.map (α : GK p E →* GK p E')) hH').toMonoidHom (galPairEquiv α H hH hH')
    (galFixMulEquiv_galPairEquiv α H hH hH') (uMu N a n) (uMu_smul_L N a H hH n)
    (muRho (Model.ouAut (F.obj (XN N a))) (ratFunTw τ) n) (muRho_smul _ _ _ hH' _ hρ n)
    (betaPsi F τ N a H n hs) (betaPsi_uMu F τ N a H n hs) (uMu_bijective N a n hs.muSat).2 σ ζ

include hρ in
/-- **`F_N(Ψ X) → H²(L', μ_N)`** via the twisted rational functions `ρ` of `Ψ X`. -/
noncomputable def fnPsi :
    FNG (Model.ouAut (F.obj (XN N a))) (jPsi F N a α) (continuous_jPsi F N a α)
      (H.map (α : GK p E →* GK p E')) n →*
      Brauer.H2Mu (fixL (H.map (α : GK p E →* GK p E'))) K̄ n :=
  QuotientGroup.lift _ (ContH2.map (galLAG (jPsi F N a α) (H.map (α : GK p E →* GK p E')) hH')
      (continuous_galLAG _ (continuous_jPsi F N a α) _ hH')
      (muRho (Model.ouAut (F.obj (XN N a))) (ratFunTw τ) n) (muRho_smul _ _ _ hH' _ hρ n))
    (ker_infl₂_le_map (continuous_jPsi F N a α) (H.map (α : GK p E →* GK p E')) n
      (galFixMulEquiv (H.map (α : GK p E →* GK p E')) hH').toMonoidHom
      (continuous_galFixMulEquiv _ hH') _ (muRho_smul _ _ _ hH' _ hρ n)
      (continuous_galLAG _ (continuous_jPsi F N a α) _ hH'))

include hρ in
/-- `Φ₂ : H²(L, μ_N) → H²(L', μ_N)` induced by `(galPairEquiv, β_Ψ)`. -/
noncomputable abbrev h2Psi :
    Brauer.H2Mu (fixL H) K̄ n →* Brauer.H2Mu (fixL (H.map (α : GK p E →* GK p E'))) K̄ n :=
  PairCompat.h2PairMap n (galPairEquiv α H hH hH') (betaPsi F τ N a H n hs)
    (betaPsi_smul F α τ N a hρ H hH hH' n hs)

/-- **`F_N(X) ≅ F_N(Ψ X)` on the Galois side**: `fnPsi ∘ fngEquiv = Φ₂ ∘ fnEquivH2L`. -/
theorem fnPsi_fngEquiv (x : FN N a H n) :
    fnPsi F α τ N a hρ H hH' n (fngEquiv (continuous_galHom N a) H n (continuous_jPsi F N a α)
        (Model.autEquiv F (XN N a)) (mem_ouAut_iff F (XN N a)) α (jPsi_apply F N a α) x) =
      h2Psi F α τ N a hρ H hH hH' n hs (fnEquivH2L N a H hH n hs x) := by
  induction x using QuotientGroup.induction_on with | H y => ?_
  refine Eq.trans ?_ (congrArg _ (fnEquivH2L_mk N a H hH n hs y).symm)
  exact map_h2Equiv_eq H n (Model.autEquiv F (XN N a)) (mem_ouAut_iff F (XN N a)) α
    (jPsi_apply F N a α) (galFixMulEquiv H hH).toMonoidHom
    (galFixMulEquiv (H.map (α : GK p E →* GK p E')) hH').toMonoidHom (galPairEquiv α H hH hH')
    (galFixMulEquiv_galPairEquiv α H hH hH') (uMu N a n) (uMu_smul_L N a H hH n)
    (muRho (Model.ouAut (F.obj (XN N a))) (ratFunTw τ) n) (muRho_smul _ _ _ hH' _ hρ n)
    (betaPsi F τ N a H n hs) (betaPsi_uMu F τ N a H n hs) (continuous_galLA N a H hH)
    (continuous_galLAG _ (continuous_jPsi F N a α) _ hH')
    (PairCompat.smul_compat_symm n (galPairEquiv α H hH hH') (betaPsi F τ N a H n hs)
      (betaPsi_smul F α τ N a hρ H hH hH' n hs)) y

/-- **[FrdII], Theorem 2.4(ii), reduced to one pairing value**: if for some character `χ` and
class `ζ` over `L` the pairing `⟨χ, ζ⟩ ∈ (ℤ/N)^×` is preserved by `(galPairEquiv, β_Ψ)`, then
`F_N(X) ≅ F_N(Ψ X)` is compatible with `F_N(X) ≅ ℤ/N` (`fnEquiv`) and
`F_N(Ψ X) → H²(L', μ_N) ≅ ℤ/N` (`fnPsi`, `h2MuEquiv`). -/
theorem thm24ii_of_pairing (χ : Brauer.LocChar (fixL H) K̄ n)
    (ζ : ContH1 (K̄ ≃ₐ[fixL H] K̄) (KummerTheory.Mu n K̄))
    (hpair :
      haveI := finiteDimensional_fixL_padic H hH
      haveI := finiteDimensional_fixL_padic _ hH'
      PadicField.pairingH1 (p := p) n (PairCompat.charPair n (galPairEquiv α H hH hH') χ)
        (PairCompat.h1PairMap n (galPairEquiv α H hH hH') (betaPsi F τ N a H n hs)
          (betaPsi_smul F α τ N a hρ H hH hH' n hs) ζ) =
        PadicField.pairingH1 (p := p) n χ ζ)
    (hunit :
      haveI := finiteDimensional_fixL_padic H hH
      IsUnit (PadicField.pairingH1 (p := p) n χ ζ))
    (x : FN N a H n) :
    haveI := finiteDimensional_fixL_padic _ hH'
    PadicField.h2MuEquiv p (fixL (H.map (α : GK p E →* GK p E'))) K̄
        (Nat.pos_of_ne_zero (NeZero.ne n))
        (fnPsi F α τ N a hρ H hH' n (fngEquiv (continuous_galHom N a) H n
          (continuous_jPsi F N a α) (Model.autEquiv F (XN N a)) (mem_ouAut_iff F (XN N a)) α
          (jPsi_apply F N a α) x)) =
      fnEquiv N a H hH n hs x := by
  haveI := finiteDimensional_fixL_padic H hH
  haveI := finiteDimensional_fixL_padic _ hH'
  refine (congrArg (PadicField.h2MuEquiv p (fixL (H.map (α : GK p E →* GK p E'))) K̄
    (Nat.pos_of_ne_zero (NeZero.ne n))) (fnPsi_fngEquiv F α τ N a hρ H hH hH' n hs x)).trans ?_
  exact PairCompat.h2MuEquiv_h2PairMap n _ _ _ χ ζ hpair hunit (fnEquivH2L N a H hH n hs x)

end PAdicGalois

end Frobenioid

end Iut
