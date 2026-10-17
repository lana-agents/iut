/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.KummerGalois
import Iut.Frobenioid.PAdicRecon

/-!
# `Ψ` and the Galois action on units ([FrdII], Theorem 2.4(i))

[FrdII], Theorem 2.4: an equivalence `Ψ : C₁ ≅ C₂` of `p`-adic Frobenioids induces "an outer
isomorphism of topological groups `G₁ ≅ G₂`", and the isomorphisms of (i) are "compatible with
[…] the various natural actions of `(G₁)_{A₁}/(H₁)_{A₁}`, `(G₂)_{A₂}/(H₂)_{A₂}`".

For `C^⊢(E)` and `X = (G_E/N, a)`, the Galois action on `O^×(X)` is conjugation by
`galHom σ = galAut σ⁻¹` (`KummerGalois.lean`: it acts on rational functions by `σ`). Here:

* `OrbitObj.rep_conj_mem`: the representative of `θ ∘ f ∘ θ⁻¹` for an orbit-category isomorphism
  `θ` and an endomorphism `f` acting on a point `ξ` by `ξ ↦ sξ` is `τ s τ⁻¹` (`τ = rep(θ) ξ⁻¹`);
* **`PAdicGalois.exists_galHom_compat`**: for `Ψ : C^⊢(E) ≌ C^⊢(E')` there is
  `α : G_E ≃ₜ* G_{E'}` (from `B(G_E)⁰ ≌ B(G_{E'})⁰`, `OrbitObj.exists_continuousMulEquiv`) such
  that, for each `X = (G_E/N, a)`, some `τ ∈ G_{E'}` satisfies: `Ψ(galHom σ)` acts on the
  rational functions of the units of `Ψ(X)` by `τ α(σ) τ⁻¹`. So `Ψ` intertwines the Galois action
  of `G_E` on `O^×(X)` with that of `G_{E'}` on `O^×(Ψ X)` along `α` up to an inner automorphism
  (the outer indeterminacy of [FrdII], Theorem 2.4).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

namespace OrbitObj

variable {G : Type} [Group G] [TopologicalSpace G]

/-- For `θ : B ≅ C` and `f : C ⟶ C` with `f(ξ) = sξ`, the composite `θ⁻¹ ∘ f ∘ θ` is right
multiplication by `τ s τ⁻¹` (`τ = rep(θ) ξ⁻¹`) modulo `B.H`. -/
lemma rep_conj_mem {B C : OrbitObj G} (θ : B ≅ C) (f : C ⟶ C) (ξ s : G)
    (hf : f.toFun (QuotientGroup.mk ξ) = QuotientGroup.mk (s * ξ)) :
    (OrbitHom.rep θ.hom * ξ⁻¹ * s * (OrbitHom.rep θ.hom * ξ⁻¹)⁻¹)⁻¹ *
      OrbitHom.rep (θ.hom ≫ f ≫ θ.inv) ∈ B.H := by
  set t := OrbitHom.rep θ.hom
  have ht : θ.hom.toFun (QuotientGroup.mk 1) = QuotientGroup.mk t :=
    (OrbitHom.mk_rep θ.hom).symm
  have h1 : f.toFun (QuotientGroup.mk t) = QuotientGroup.mk (t * ξ⁻¹ * s * ξ) := by
    have e : (QuotientGroup.mk t : G ⧸ C.H) = (t * ξ⁻¹) • QuotientGroup.mk ξ := by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel_right]
    rw [e, f.map_smul, hf, MulAction.Quotient.smul_mk, smul_eq_mul]
    congr 1
    group
  have h2 : θ.inv.toFun (QuotientGroup.mk t) = QuotientGroup.mk 1 := by
    rw [← ht]
    change (θ.hom ≫ θ.inv).toFun _ = _
    rw [θ.hom_inv_id]
    rfl
  have h3 : θ.inv.toFun (QuotientGroup.mk (t * ξ⁻¹ * s * ξ)) =
      QuotientGroup.mk (t * ξ⁻¹ * s * ξ * t⁻¹) := by
    have e : (QuotientGroup.mk (t * ξ⁻¹ * s * ξ) : G ⧸ C.H) =
        (t * ξ⁻¹ * s * ξ * t⁻¹) • QuotientGroup.mk t := by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel_right]
    rw [e, θ.inv.map_smul, h2, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have hc : (θ.hom ≫ f ≫ θ.inv).toFun (QuotientGroup.mk 1) =
      QuotientGroup.mk (t * ξ⁻¹ * s * (t * ξ⁻¹)⁻¹) := by
    change θ.inv.toFun (f.toFun (θ.hom.toFun _)) = _
    rw [ht, h1, h3]
    congr 1
    group
  have := OrbitHom.mk_rep (θ.hom ≫ f ≫ θ.inv)
  rw [hc] at this
  exact QuotientGroup.eq.mp this.symm

end OrbitObj

namespace PAdicGalois

variable {p : ℕ} [hp : Fact p.Prime]
variable {Γ : AddSubgroup ℝ}
variable {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "𝐏E" => Model.toElem (constPhi (OrbitObj (GK p E)) Γ)
  (bGal (GK p E) (ord p) (ord_smul p E) Γ) (divGal (GK p E) (ord p) (ord_smul p E) Γ)

local notation "𝐏E'" => Model.toElem (constPhi (OrbitObj (GK p E')) Γ)
  (bGal (GK p E') (ord p) (ord_smul p E') Γ)
  (divGal (GK p E') (ord p) (ord_smul p E') Γ)

/-- The rational function `γ_u ∈ K̄^×` of a unit `u ∈ O^×(Y)` of any object `Y` of `C^⊢(E')`. -/
noncomputable def ratFunY {Y : GFrob p E' Γ} (u : Model.ouAut Y) : (PadicAlgCl p)ˣ :=
  ((show Aut Y from (u : WithDisc (Aut Y))).hom.u.1).toMul

/-- An automorphism `β` of `Y` acts on rational functions of units through the representative
of the base of `β⁻¹`. -/
lemma ratFunY_conjU {Y : GFrob p E' Γ} (β : WithDisc (Aut Y)) (u : Model.ouAut Y) :
    ratFunY (KummerClass.conjU (Model.ouAut Y) β u) =
      OrbitHom.rep (show Aut Y from β).inv.base • ratFunY u := by
  have hu := u.2
  rw [Model.mem_ouAut] at hu
  unfold ratFunY
  rw [KummerClass.coe_conjU, Model.conj_hom, Model.conj_u _ hu]
  rfl

variable [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']

/-- **`Ψ` intertwines the Galois actions on units** ([FrdII], Theorem 2.4(i)): for an equivalence
`Ψ : C^⊢(E) ≌ C^⊢(E')` there is `α : G_E ≃ₜ* G_{E'}` (induced by `Ψ_Base`) such that for
every `X = (G_E/N, a)` there is `τ ∈ G_{E'}` with: `Ψ(galHom σ)` acts on the rational functions
of the units of `Ψ(X)` by `τ α(σ) τ⁻¹`. -/
theorem exists_galHom_compat (F : GFrob p E Γ ⥤ GFrob p E' Γ) [F.IsEquivalence] :
    ∃ α : GK p E ≃ₜ* GK p E',
      ∀ (N : OpenNormalSubgroup (GK p E)) (a : Γ), ∃ τ : GK p E',
        ∀ (σ : GK p E) (v : Model.ouAut (F.obj (XN N a))),
          ratFunY (KummerClass.conjU (Model.ouAut (F.obj (XN N a)))
            (Model.autEquiv F (XN N a) (galHom N a σ)) v) =
            (τ * α σ * τ⁻¹) • ratFunY v := by
  obtain ⟨G, ⟨θ⟩⟩ := Model.thm34_galois_preservesBase isSlimGroup
    (GaloisModel.hasAllTorsion (torsion p E)) (GaloisModel.hasAllTorsion (torsion p E')) F
  obtain ⟨G', ⟨θ'⟩⟩ := Model.thm34_galois_preservesBase isSlimGroup
    (GaloisModel.hasAllTorsion (torsion p E')) (GaloisModel.hasAllTorsion (torsion p E)) F.inv
  haveI : G.IsEquivalence :=
    isEquivalence_base (GaloisModel.isFrobenioid _ _ _ _) (GaloisModel.isFrobenioid _ _ _ _)
      F G G' θ θ'
  obtain ⟨α, x, -, -, hx⟩ := OrbitObj.exists_continuousMulEquiv G
  refine ⟨α, fun N a => ?_⟩
  let θX : (F.obj (XN N a)).base ≅ G.obj (OrbitObj.ofONS N) := θ.app (XN N a)
  let ξ : GK p E' := (x N).out
  refine ⟨OrbitHom.rep θX.hom * ξ⁻¹, fun σ v => ?_⟩
  rw [ratFunY_conjU]
  have hbase : (show Aut (F.obj (XN N a)) from
      Model.autEquiv F (XN N a) (galHom N a σ)).inv.base =
      θX.hom ≫ G.map (OrbitObj.rmul N σ⁻¹⁻¹) ≫ θX.inv := by
    have nat := θ.hom.naturality (GaloisModel.galAut (ℓ := ord p) (hℓ := ord_smul p E)
      N a σ⁻¹).inv
    rw [← Category.assoc]
    exact (θX.eq_comp_inv).mpr nat
  have hf : (G.map (OrbitObj.rmul N σ⁻¹⁻¹)).toFun (QuotientGroup.mk ξ) =
      QuotientGroup.mk (α σ⁻¹⁻¹ * ξ) := by
    have e : (QuotientGroup.mk ξ : GK p E' ⧸ (G.obj (OrbitObj.ofONS N)).H) = x N :=
      QuotientGroup.out_eq' _
    rw [e, hx, ← e, MulAction.Quotient.smul_mk, smul_eq_mul]
  have hmem := OrbitObj.rep_conj_mem θX _ ξ _ hf
  rw [inv_inv] at hmem hbase
  have hv := ((show Aut (F.obj (XN N a)) from (v : WithDisc (Aut (F.obj (XN N a))))).hom.u).2
  have key := fixed_smul_eq_of_mem _ hv hmem
  rw [hbase]
  exact congrArg Additive.toMul key

end PAdicGalois

end Frobenioid

end Iut
