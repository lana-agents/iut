/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm24Saturated

/-!
# Kummer classes under `Ψ`, on the Galois side ([FrdII], Theorem 2.4(i))

[FrdII], Theorem 2.4(i): the isomorphisms induced by `Ψ` are "compatible with the respective Kummer
[…] maps". `Thm24Saturated.lean` transports `H¹(H_A, μ_N(X)) ≅ H¹(α(H)_{Ψ X}, μ_N(Ψ X))`
(`Saturation.h1Equiv`); here we identify both sides with Galois cohomology of local fields.

* `PAdicGalois.toLG`: for a discrete group `G` with normal commutative `U`, a continuous
  `j : G_{E'} →* G`, an open `H ⊆ G_{E'}` and a `j`-equivariant "rational function" homomorphism
  `ρ : U →* K̄^×` (`ρ(j(σ) u j(σ)⁻¹) = σ ρ(u)`), the map `H¹(j(H), μ_N(U)) → H¹(L, μ_N)`,
  `L = K̄^H`; **`toLG_kummerClass`**: it sends the Kummer class of `g` with `ρ(g)^N = y ∈ L^×` to
  `KummerTheory.kummer N L K̄ y`;
* `Saturation.h1Equiv_kummerClass`: `h1Equiv` maps Kummer classes to Kummer classes;
* **`PAdicGalois.thm24_kummer_galois`**: for `Ψ : C^⊢(E) ≌ C^⊢(E')` there is `α : G_E ≃ₜ* G_{E'}`
  such that each `Ψ X` (`X = (G_E/N, a)`, Galois structure `jΨ`) carries an equivariant rational
  function homomorphism `ρ = τ⁻¹ · γ` (a `G_{E'}`-translate of the rational functions of `Ψ X`), and
  for `g ∈ O^×(X)` the transported Kummer class `h1Equiv κ_g` is, over `L' = K̄^{α(H)}`, the
  Kummer class of `ρ(Ψ g)^N`, while `κ_g` itself is, over `L = K̄^H`, the Kummer class of
  `γ_g^N` (`toL_kummerClass`).
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

namespace Saturation

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] {U : Subgroup G}
  [U.Normal] [IsMulCommutative U] {K : Type*} [Group K] [TopologicalSpace K] {j : K →* G}
  (H : Subgroup K) (n : ℕ)
variable {G' : Type*} [Group G'] [TopologicalSpace G'] [DiscreteTopology G'] {U' : Subgroup G'}
  [U'.Normal] [IsMulCommutative U'] {K' : Type*} [Group K'] [TopologicalSpace K'] {j' : K' →* G'}
variable (φ : G ≃* G') (hU : ∀ u, u ∈ U ↔ φ u ∈ U') (α : K ≃ₜ* K')
  (hjα : ∀ k, j' (α k) = φ (j k))

lemma phi_subAEquiv_symm (h : subAG j' (H.map (α : K →* K'))) :
    φ (((subAEquiv H φ α hjα).symm h : subAG j H) : G) = h := by
  rw [← coe_subAEquiv H φ α hjα, MulEquiv.apply_symm_apply]

/-- **`h1Equiv` maps Kummer classes to Kummer classes.** -/
theorem h1Equiv_kummerClass (g : U)
    (hg : ∀ h ∈ subAG j H, KummerClass.conjU U h (g ^ n) = g ^ n) :
    h1Equiv H n φ hU α hjα (KummerClass.kummerClass U (subAG j H) n g hg) =
      KummerClass.kummerClass U' (subAG j' (H.map (α : K →* K'))) n ⟨φ g, (hU g).mp g.2⟩
        (KummerClass.fixed_map U (subAG j H) n φ (fun u hu => (hU u).mp hu)
          (map_subAG H φ α hjα) g hg) := by
  change ContH1.map _ _ _ _ _ (ContH1.mk _) = ContH1.mk _
  rw [ContH1.map_mk]
  congr 1
  apply Subtype.ext
  funext h
  change muEquiv n φ hU (KummerClass.kfun U (subAG j H) n g hg
    ((subAEquiv H φ α hjα).symm h)) = KummerClass.kfun U' _ n ⟨φ g, (hU g).mp g.2⟩
      (KummerClass.fixed_map U (subAG j H) n φ (fun u hu => (hU u).mp hu)
        (map_subAG H φ α hjα) g hg) h
  apply Subtype.ext; apply Subtype.ext
  rw [coe_muEquiv]
  simp only [KummerClass.coe_kfun, map_mul, map_inv, Subgroup.coe_inv,
    phi_subAEquiv_symm H φ α hjα]

end Saturation

namespace PAdicGalois

open Saturation CategoryTheory IntermediateField

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K̄" => PadicAlgCl p

section Gen

variable {E' : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] (U : Subgroup G)
  [U.Normal] [IsMulCommutative U] (j : GK p E' →* G) (hj : Continuous j)
  (H : Subgroup (GK p E')) (hH : IsOpen (H : Set (GK p E'))) (ρ : U →* (PadicAlgCl p)ˣ)
  (hρ : ∀ (σ : GK p E') (u : U), ρ (KummerClass.conjU U (j σ) u) = σ • ρ u)

/-- `μ_n(U) → μ_n(K̄)` along `ρ`. -/
noncomputable def muRho (n : ℕ) : KummerClass.mu U n →* KummerTheory.Mu n (PadicAlgCl p) where
  toFun u := KummerTheory.Mu.mk (ρ u) (by rw [← map_pow, KummerClass.mem_mu.mp u.2, map_one])
  map_one' := KummerTheory.Mu.ext (map_one ρ)
  map_mul' u v := KummerTheory.Mu.ext (map_mul ρ _ _)

/-- `Gal(K̄/L) ≅ H ↠ j(H)`. -/
noncomputable def galLAG : (K̄ ≃ₐ[fixL H] K̄) →* subAG j H :=
  (subHomG j H).comp (galFixMulEquiv H hH).toMonoidHom

include hj in
lemma continuous_galLAG : Continuous (galLAG j H hH) :=
  (continuous_subHomG j hj H).comp (continuous_galFixMulEquiv H hH)

include hρ in
lemma muRho_smul (n : ℕ) (k : K̄ ≃ₐ[fixL H] K̄) (m : KummerClass.mu U n) :
    muRho U ρ n (galLAG j H hH k • m) = k • muRho U ρ n m := by
  apply KummerTheory.Mu.ext
  rw [KummerTheory.Mu.val_smul]
  exact hρ (Brauer.resScalars (fixL H) k) m

include hj hρ in
/-- **`H¹(j(H), μ_N(U)) → H¹(L, μ_N)`** along `Gal(K̄/L) ≅ H ↠ j(H)` and `ρ`. -/
noncomputable def toLG (n : ℕ) :
    ContH1 (subAG j H) (KummerClass.mu U n) →* ContH1 (K̄ ≃ₐ[fixL H] K̄) (KummerTheory.Mu n K̄) :=
  ContH1.map (galLAG j H hH) (continuous_galLAG j hj H hH) (muRho U ρ n)
    continuous_of_discreteTopology (muRho_smul U j H hH ρ hρ n)

include hρ in
lemma rho_kfun (n : ℕ) (g : U) (hg : ∀ h ∈ subAG j H, KummerClass.conjU U h (g ^ n) = g ^ n)
    (k : K̄ ≃ₐ[fixL H] K̄) :
    ρ (KummerClass.kfun U (subAG j H) n g hg (galLAG j H hH k)) = k • ρ g / ρ g := by
  change ρ (KummerClass.conjU U (j (Brauer.resScalars (fixL H) k)) g / g) = _
  rw [map_div, hρ]
  rfl

/-- **The Kummer class of `g` over `j(H)` is the Kummer class of `ρ(g)^N` over `L`.** -/
theorem toLG_kummerClass (n : ℕ) [NeZero (n : fixL H)] (g : U)
    (hg : ∀ h ∈ subAG j H, KummerClass.conjU U h (g ^ n) = g ^ n) (y : (fixL H)ˣ)
    (hy : ρ g ^ n = Units.map (algebraMap (fixL H) K̄ : fixL H →* K̄) y) :
    toLG U j hj H hH ρ hρ n (KummerClass.kummerClass U (subAG j H) n g hg) =
      KummerTheory.kummer n (fixL H) K̄ y := by
  have hγ : ∀ σ : K̄ ≃ₐ[fixL H] K̄, σ • ρ g ^ n = ρ g ^ n := fun σ => by
    rw [hy]
    exact Units.ext (σ.commutes (y : fixL H))
  refine (KummerClass.map_kummerClass_eq_mk (g := g) (hg := hg)
    (c := KummerTheory.kummerCocycle (ρ g) hγ)
    (hc := fun k => KummerTheory.Mu.ext (rho_kfun U j H hH ρ hρ n g hg k)) ..).trans
    (KummerTheory.kummer_eq y _ hy).symm

end Gen

section Psi

variable {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)}

lemma ratFunY_mul {Y : Frob p E'} (u v : Model.ouAut Y) :
    ratFunY (u * v) = ratFunY u * ratFunY v := by
  have h := Model.ounits_comp_u v.2 u.2
  unfold ratFunY
  change Additive.toMul (((show Aut Y from (v : WithDisc (Aut Y))).hom ≫
    (show Aut Y from (u : WithDisc (Aut Y))).hom).u.1) = _
  rw [h]
  change Additive.toMul (_ + _) = _
  rw [toMul_add, mul_comm]

/-- The rational functions of the units of `Y`, translated by `τ⁻¹`. -/
noncomputable def ratFunTw {Y : Frob p E'} (τ : GK p E') : Model.ouAut Y →* K̄ˣ where
  toFun v := τ⁻¹ • ratFunY v
  map_one' := by
    change τ⁻¹ • ratFunY (1 : Model.ouAut Y) = 1
    have : ratFunY (1 : Model.ouAut Y) = 1 := by
      have h := ratFunY_mul (1 : Model.ouAut Y) 1
      rw [mul_one] at h
      exact left_eq_mul.mp h
    rw [this, smul_one]
  map_mul' u v := by
    change τ⁻¹ • ratFunY (u * v) = τ⁻¹ • ratFunY u * τ⁻¹ • ratFunY v
    rw [ratFunY_mul, smul_mul']

variable [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']

/-- `Ψ g ∈ O^×(Ψ X)`. -/
noncomputable def psiU (F : Frob p E ⥤ Frob p E') [F.IsEquivalence] (X : Frob p E)
    (g : Model.ouAut X) : Model.ouAut (F.obj X) :=
  ⟨Model.autEquiv F X g, (mem_ouAut_iff F X g).mp g.2⟩

/-- **[FrdII], Theorem 2.4(i), Kummer classes on the Galois side, for `C^⊢`.** For
`Ψ : C^⊢(E) ≌ C^⊢(E')` there is `α : G_E ≃ₜ* G_{E'}` such that for every `X = (G_E/N, a)` the
units of `Ψ X` carry a "rational function" homomorphism `ρ : O^×(Ψ X) → K̄^×` (a
`G_{E'}`-translate of the rational functions) equivariant for the Galois structure
`jΨ = Ψ ∘ galHom ∘ α⁻¹`, and for `H ⊆ G_E` with `α(H)` open, `g ∈ O^×(X)` with `g^N` fixed by
`H_A` and `ρ(Ψ g)^N = y ∈ (K̄^{α(H)})^×`, the image `h1Equiv κ_g` of the Kummer class of `g`
(`Saturation.h1Equiv`, [FrdII], Theorem 2.4(i)) is, over `L' = K̄^{α(H)}`, the Kummer class of
`y` (`KummerTheory.kummer`). (Over `L = K̄^H`, `κ_g` is the Kummer class of `γ_g^N`:
`toL_kummerClass`.) -/
theorem thm24_kummer_galois (F : Frob p E ⥤ Frob p E') [F.IsEquivalence] :
    ∃ α : GK p E ≃ₜ* GK p E', ∀ (N : OpenNormalSubgroup (GK p E)) (a : gammaZ),
      ∃ (ρ : Model.ouAut (F.obj (XN N a)) →* K̄ˣ)
        (hρ : ∀ (σ' : GK p E') (v : Model.ouAut (F.obj (XN N a))),
          ρ (KummerClass.conjU (Model.ouAut (F.obj (XN N a))) (jPsi F N a α σ') v) = σ' • ρ v),
        ∀ (H : Subgroup (GK p E)) (hH' : IsOpen ((H.map (α : GK p E →* GK p E')) :
            Set (GK p E'))) (n : ℕ) [NeZero (n : fixL (H.map (α : GK p E →* GK p E')))]
          (g : Model.ouAut (XN N a))
          (hg : ∀ h ∈ subA N a H, KummerClass.conjU (Model.ouAut (XN N a)) h (g ^ n) = g ^ n)
          (y : (fixL (H.map (α : GK p E →* GK p E')))ˣ)
          (_hy : ρ (psiU F (XN N a) g) ^ n = Units.map (algebraMap
            (fixL (H.map (α : GK p E →* GK p E'))) K̄ :
            fixL (H.map (α : GK p E →* GK p E')) →* K̄) y),
          toLG (Model.ouAut (F.obj (XN N a))) (jPsi F N a α) (continuous_jPsi F N a α)
              (H.map (α : GK p E →* GK p E')) hH' ρ hρ n
              (h1Equiv H n (Model.autEquiv F (XN N a)) (mem_ouAut_iff F (XN N a)) α
                (jPsi_apply F N a α) (Model.frobKummerClass (XN N a) (subA N a H) n g hg)) =
            KummerTheory.kummer n (fixL (H.map (α : GK p E →* GK p E'))) K̄ y := by
  refine (exists_galHom_compat F).elim fun α hα => ⟨α, fun N a => ?_⟩
  refine (hα N a).elim fun τ hτ => ?_
  have hρ : ∀ (σ' : GK p E') (v : Model.ouAut (F.obj (XN N a))),
      ratFunTw τ (KummerClass.conjU (Model.ouAut (F.obj (XN N a))) (jPsi F N a α σ') v) =
        σ' • ratFunTw τ v := fun σ' v => by
    have h := hτ (α.symm σ') v
    rw [ContinuousMulEquiv.apply_symm_apply] at h
    change τ⁻¹ • ratFunY (KummerClass.conjU (Model.ouAut (F.obj (XN N a)))
      (Model.autEquiv F (XN N a) (galHom N a (α.symm σ'))) v) = σ' • τ⁻¹ • ratFunY v
    rw [h, smul_smul, smul_smul]
    congr 1
    group
  refine ⟨ratFunTw τ, hρ, fun H hH' n _ g hg y hy => ?_⟩
  refine (congrArg _ (h1Equiv_kummerClass H n (Model.autEquiv F (XN N a))
    (mem_ouAut_iff F (XN N a)) α (jPsi_apply F N a α) g hg)).trans ?_
  exact toLG_kummerClass _ _ _ _ hH' _ hρ n _ _ y hy

end Psi

end PAdicGalois

end Frobenioid

end Iut
