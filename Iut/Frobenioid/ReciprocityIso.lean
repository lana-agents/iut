/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Reciprocity

/-!
# The reciprocity map is injective ([FrdII], Remark 2.2.1)

[FrdII], Remark 2.2.1: the cup product gives "an isomorphism `H¹(H, μ_N(A)) ≅ H^ab ⊗ H²(H, μ_N(A))`
hence [in light of the condition of Definition 2.2, (ii), (c)] an isomorphism
`H¹(H_A, μ_N(A)) ≅ H_A^ab ⊗ F_N(A)`". For an `(N, H)`-saturated `X` of the `p`-adic Frobenioid
`C^⊢(E)`:

* `ContH1Aux.mapEquiv`: `H¹` along a topological group isomorphism and an equivariant
  isomorphism of coefficients;
* **`toL_bijective`**: `H¹(H_A, μ_N(X)) ≅ H¹(L, μ_N)` (`L = K̄^H`), from condition (c) on `μ_N`;
* **`exists_charL`**: every character of `Gal(K̄/L)` of order dividing `N` comes from a character
  of `H_A`, from condition (c) on `ℤ/N`;
* **`recip_injective`**: `κ ↦ η(κ) = (χ ↦ χ ∪ κ)` is injective on `H¹(H_A, μ_N(X))`, by local
  duality (`PadicField.eq_one_of_forall_pairingH1_eq_zero'`).
-/

namespace Iut

namespace Frobenioid

namespace ContH1Aux

variable {G G' M M' : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M] [Group G'] [TopologicalSpace G']
  [CommGroup M'] [TopologicalSpace M'] [IsTopologicalGroup M'] [MulDistribMulAction G' M']

/-- `H¹(G, M) ≅ H¹(G', M')` along `e : G' ≃ₜ* G` and a compatible `f : M ≃* M'`. -/
noncomputable def mapEquiv (e : G' ≃ₜ* G) (f : M ≃* M') (hf : Continuous f)
    (hf' : Continuous f.symm) (h : ∀ (g : G') (m : M), f (e g • m) = g • f m) :
    ContH1 G M ≃* ContH1 G' M' where
  toFun := ContH1.map (e : G' →* G) e.continuous f.toMonoidHom hf h
  invFun := ContH1.map (e.symm : G →* G') e.symm.continuous f.symm.toMonoidHom hf' fun g m => by
    apply f.injective
    change f (f.symm (e.symm g • m)) = f (g • f.symm m)
    rw [MulEquiv.apply_symm_apply]
    conv_rhs => rw [← e.apply_symm_apply g]
    change _ = f ((e : G' →* G) (e.symm g) • f.symm m)
    rw [show ((e : G' →* G) (e.symm g)) = e (e.symm g) from rfl, h, MulEquiv.apply_symm_apply]
  left_inv x := by
    induction x using ContH1.induction_on with | h c => ?_
    simp only [ContH1.map_mk]
    congr 1
    exact Subtype.ext (funext fun g => by simp)
  right_inv x := by
    induction x using ContH1.induction_on with | h c => ?_
    simp only [ContH1.map_mk]
    congr 1
    exact Subtype.ext (funext fun g => by simp)
  map_mul' := map_mul _

end ContH1Aux

namespace DualityAux

/-- **Local duality**: classes in `H¹(K, μ_n)` with the same cup products with all characters
are equal. -/
theorem eq_of_forall_cupH1_eq (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω]
    [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] [IsGalois K Ω] (n : ℕ) [NeZero n]
    (ζ ζ' : ContH1 (Ω ≃ₐ[K] Ω) (KummerTheory.Mu n Ω))
    (h : ∀ χ, Brauer.cupH1 n χ ζ = Brauer.cupH1 n χ ζ') : ζ = ζ' := by
  rw [← div_eq_one]
  refine PadicField.eq_one_of_forall_pairingH1_eq_zero' (p := p) n _ fun χ => ?_
  rw [PadicField.pairingH1, map_div, h χ, div_self', map_one, toAdd_one]

end DualityAux

namespace PAdicGalois

open Saturation CategoryTheory IntermediateField

variable {p : ℕ} [hp : Fact p.Prime] {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable {Γ : AddSubgroup ℝ}
variable (N : OpenNormalSubgroup (GK p E)) (a : Γ) (H : Subgroup (GK p E))
  (hH : IsOpen (H : Set (GK p E)))

local notation "K̄" => PadicAlgCl p

/-- `H¹(H, μ_N(X)) ≅ H¹(L, μ_N)` (`Gal(K̄/L) ≅ H`, `μ_N(X) ≅ μ_N(K̄)`). -/
noncomputable def h1HEquiv (n : ℕ) [NeZero n]
    (hs : Nonempty (muX N a n ≃* Multiplicative (ZMod n))) :
    ContH1 H (Pull (subHom N a H) (muX N a n)) ≃*
      ContH1 (K̄ ≃ₐ[fixL H] K̄) (KummerTheory.Mu n K̄) :=
  ContH1Aux.mapEquiv (galFixEquiv H hH) (uMuEquiv N a H n hs)
    (continuous_of_discreteTopology (α := muX N a n)) continuous_of_discreteTopology
    fun k m => uMuEquiv_smul N a H n hs (galFixEquiv H hH k) m

lemma toL_eq (n : ℕ) [NeZero n] (hs : Nonempty (muX N a n ≃* Multiplicative (ZMod n)))
    (κ : ContH1 (subA N a H) (muX N a n)) :
    toL N a H hH n κ =
      h1HEquiv N a H hH n hs (infl₁ (subHom N a H) (continuous_subHom N a H) (muX N a n) κ) := by
  induction κ using ContH1.induction_on with | h c => rfl

/-- **`H¹(H_A, μ_N(X)) ≅ H¹(L, μ_N)`** for an `(N, H)`-saturated `X`. -/
theorem toL_bijective (n : ℕ) [NeZero n] (hs : IsSaturated N a H n) :
    Function.Bijective (toL N a H hH n) := by
  have e : ⇑(toL N a H hH n) = h1HEquiv N a H hH n hs.muSat ∘
      infl₁ (subHom N a H) (continuous_subHom N a H) (muX N a n) :=
    funext (toL_eq N a H hH n hs.muSat)
  rw [e]
  exact (h1HEquiv N a H hH n hs.muSat).bijective.comp hs.h1Mu

/-- **Every character of `Gal(K̄/L)` of order dividing `N` comes from `H_A`**, by condition (c)
on `H¹(−, ℤ/N)`. -/
theorem exists_charL (n : ℕ) (hs : IsSaturated N a H n)
    (ψ : Brauer.LocChar (fixL H) K̄ n) : ∃ χ, charL N a H hH n χ = ψ := by
  let cf : H → ZTriv n := fun h => ψ.1 ((galFixEquiv H hH).symm h)
  have hcf : Continuous cf :=
    (ψ.2.comp_continuous (galFixEquiv H hH).symm.continuous).continuous
  have hcc : groupCohomology.IsMulCocycle₁ cf := fun g h => by
    change ψ.1 ((galFixEquiv H hH).symm (g * h)) =
      ψ.1 ((galFixEquiv H hH).symm h) * ψ.1 ((galFixEquiv H hH).symm g)
    rw [map_mul, map_mul, mul_comm]
  obtain ⟨κ, hκ⟩ := hs.h1Z.2 (ContH1.mk ⟨cf, hcf, hcc⟩)
  induction κ using ContH1.induction_on with | h d => ?_
  have hκ' : ContH1.mk (ContH1.cocyclesMap (subHom N a H) (continuous_subHom N a H)
      (MonoidHom.id (ZTriv n)) continuous_id (fun _ _ => rfl) d) =
      ContH1.mk ⟨cf, hcf, hcc⟩ := hκ
  obtain ⟨m, hm⟩ := (ContH1.mk_eq_mk_iff _ _).mp hκ'
  have hd : ∀ h : H, (d : subA N a H → ZTriv n) (subHom N a H h) = cf h := fun h =>
    div_eq_one.mp ((hm h).symm.trans (show h • m / m = 1 from div_self' m))
  let χ : subA N a H →* Multiplicative (ZMod n) :=
    { toFun := fun x => (d : subA N a H → ZTriv n) x
      map_one' := ContH1.map_one_eq d
      map_mul' := fun x y => by
        change (d : subA N a H → ZTriv n) (x * y) = (d : subA N a H → ZTriv n) x *
          (d : subA N a H → ZTriv n) y
        exact (ContH1.isMulCocycle₁ d x y).trans (mul_comm _ _) }
  refine ⟨χ, Subtype.ext (MonoidHom.ext fun k => ?_)⟩
  change (d : subA N a H → ZTriv n) (subHom N a H (galFixMulEquiv H hH k)) = ψ.1 k
  rw [hd]
  change ψ.1 ((galFixEquiv H hH).symm (galFixEquiv H hH k)) = ψ.1 k
  rw [ContinuousMulEquiv.symm_apply_apply]

/-- **The reciprocity map is injective** ([FrdII], Remark 2.2.1: `H¹(H_A, μ_N(A)) ≅
H_A^ab ⊗ F_N(A)`), by condition (c) and local duality. -/
theorem recip_injective [FiniteDimensional ℚ_[p] E] (n : ℕ) [NeZero n]
    (hs : IsSaturated N a H n) : Function.Injective (recip N a H hH n hs) := by
  intro κ κ' h
  haveI := finiteDimensional_fixL_padic H hH
  apply (toL_bijective N a H hH n hs).1
  refine DualityAux.eq_of_forall_cupH1_eq p n _ _ fun ψ => ?_
  refine (exists_charL N a H hH n hs ψ).elim fun χ hχ => ?_
  rw [← hχ]
  exact (fnEquivH2L N a H hH n hs).symm.injective (congrFun h χ)

end PAdicGalois

end Frobenioid

end Iut
