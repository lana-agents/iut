/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Saturation
import LocalClassFieldTheory.Brauer.KummerH2
import LocalClassFieldTheory.Brauer.Restriction

/-!
# `F_N(A) ≅ ℤ/N` ([FrdII], Definition 2.2(ii))

[FrdII], Definition 2.2(ii): "`F_N(A) := H²(H_A, μ_N(A))/Ker(H²(H_A, μ_N(A)) ↠ H²(H, μ_N(A)))`
— so `F_N(A) ≅ H²(H, μ_N(A)) ≅ ℤ/Nℤ` [cf., e.g., [NSW], Chapter 7, Theorem 7.2.6]."

For the `p`-adic Frobenioid `C^⊢(E)` (`E/ℚ_p` finite), `X = (G_E/N, a)` and an open subgroup
`H ⊆ G_E` with fixed field `L = K̄^H`:

* `galFixEquiv`: `Gal(K̄/L) ≃ₜ* H` (`σ ↦ σ`; Krull: `H` is closed, compact-to-Hausdorff);
* `h2HEquiv`: `H²(H, μ_N(K̄)) ≃ H²(L, μ_N) = Brauer.H2Mu L K̄ N`;
* `uMu_bijective`: if `X` is `μ_N`-saturated, `μ_N(X) → μ_N(K̄)` (rational functions) is bijective,
  so `μ_N(X) ≅ μ_N(K̄)` as `H`-modules (`uMuEquiv`);
* **`fnEquiv`**: for an `(N, H)`-saturated `X`,
  `F_N(X) ≅ H²(H, μ_N(X)) ≅ H²(H, μ_N(K̄)) ≅ H²(L, μ_N) ≅ ℤ/N`, the last isomorphism being local
  class field theory's canonical `PadicField.h2MuEquiv` (`β ↦ k` with `inv(β) = k/N`).
-/

namespace Iut

namespace Frobenioid

namespace ContH2Aux

variable {G M M' : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]
  [CommGroup M'] [MulDistribMulAction G M']

/-- `H²(G, M) ≅ H²(G, M')` for a `G`-equivariant isomorphism `M ≅ M'`. -/
noncomputable def mapCoeff (e : M ≃* M') (he : ∀ (g : G) (m : M), e (g • m) = g • e m) :
    ContH2 G M ≃* ContH2 G M' where
  toFun := ContH2.map (MonoidHom.id G) continuous_id e.toMonoidHom he
  invFun := ContH2.map (MonoidHom.id G) continuous_id e.symm.toMonoidHom fun g m => by
    apply e.injective
    change e (e.symm (g • m)) = e (g • e.symm m)
    rw [he, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  left_inv x := by
    induction x using ContH2.induction_on with | h f => ?_
    simp only [ContH2.map_mk]
    congr 1
    exact ContH2.cocycles_ext fun a b => by simp
  right_inv x := by
    induction x using ContH2.induction_on with | h f => ?_
    simp only [ContH2.map_mk]
    congr 1
    exact ContH2.cocycles_ext fun a b => by simp
  map_mul' := map_mul _

end ContH2Aux

namespace PAdicGalois

open Saturation CategoryTheory IntermediateField

variable {p : ℕ} [hp : Fact p.Prime] {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable {Γ : AddSubgroup ℝ}

section Fix

variable (H : Subgroup (GK p E)) (hH : IsOpen (H : Set (GK p E)))

/-- The fixed field `L = K̄^H`. -/
noncomputable abbrev fixL : IntermediateField E (PadicAlgCl p) := fixedField H

include hH in
lemma fixingSubgroup_fixL : (fixL H).fixingSubgroup = H :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨H, Subgroup.isClosed_of_isOpen H hH⟩

/-- `Gal(K̄/L) ≃* H`. -/
noncomputable def galFixMulEquiv : (PadicAlgCl p ≃ₐ[fixL H] PadicAlgCl p) ≃* H :=
  (fixingSubgroupEquiv (fixL H)).symm.trans (MulEquiv.subgroupCongr (fixingSubgroup_fixL H hH))

lemma coe_galFixMulEquiv (σ : PadicAlgCl p ≃ₐ[fixL H] PadicAlgCl p) :
    ((galFixMulEquiv H hH σ : H) : GK p E) = Brauer.resScalars (fixL H) σ := rfl

lemma continuous_galFixMulEquiv : Continuous (galFixMulEquiv H hH) :=
  Continuous.subtype_mk (Brauer.continuous_resScalars (fixL H)) _

/-- **`Gal(K̄/L) ≃ₜ* H`** for `L = K̄^H`. -/
noncomputable def galFixEquiv : (PadicAlgCl p ≃ₐ[fixL H] PadicAlgCl p) ≃ₜ* H where
  toMulEquiv := galFixMulEquiv H hH
  continuous_toFun := continuous_galFixMulEquiv H hH
  continuous_invFun :=
    ((continuous_galFixMulEquiv H hH).homeoOfEquivCompactToT2
      (f := (galFixMulEquiv H hH).toEquiv)).symm.continuous

/-- **`H²(H, μ_n(K̄)) ≅ H²(L, μ_n)`**. -/
noncomputable def h2HEquiv (n : ℕ) :
    ContH2 H (KummerTheory.Mu n (PadicAlgCl p)) ≃* Brauer.H2Mu (fixL H) (PadicAlgCl p) n :=
  ContH2.mapEquiv (galFixMulEquiv H hH) (continuous_galFixMulEquiv H hH)
    (galFixEquiv H hH).symm.continuous fun _ _ => rfl

include hH in
lemma finiteDimensional_fixL : FiniteDimensional E (fixL H) :=
  (InfiniteGalois.isOpen_iff_finite (fixL H)).mp (by
    change IsOpen ((fixL H).fixingSubgroup : Set (GK p E))
    rw [fixingSubgroup_fixL H hH]
    exact hH)

end Fix

section UMu

variable (N : OpenNormalSubgroup (GK p E)) (a : Γ)

lemma ratFun_injective : Function.Injective (ratFun N a) := by
  intro u v h
  have hu := u.2
  have hv := v.2
  rw [Model.mem_ouAut] at hu hv
  apply Subtype.ext
  change (show WithDisc (Aut (XN N a)) from (u : WithDisc (Aut (XN N a)))) =
    (v : WithDisc (Aut (XN N a)))
  apply Iso.ext
  refine Model.hom_ext ?_ ?_ ?_ ?_
  · rw [Model.ounits_deg hu, Model.ounits_deg hv]
  · rw [Model.ounits_base hu, Model.ounits_base hv]
  · rw [Model.ounits_div hu, Model.ounits_div hv]
  · apply Subtype.ext
    exact congrArg Additive.ofMul h

lemma uMu_injective (n : ℕ) : Function.Injective (uMu N a n) := by
  intro u v h
  have h' : ratFun N a u = ratFun N a v := congrArg KummerTheory.Mu.val h
  exact Subtype.ext (ratFun_injective N a h')

/-- **`μ_n`-saturation identifies `μ_n(X)` with `μ_n(K̄)`** (via rational functions). -/
lemma uMu_bijective (n : ℕ) [NeZero n] (hs : Nonempty (muX N a n ≃* Multiplicative (ZMod n))) :
    Function.Bijective (uMu N a n) := by
  obtain ⟨e⟩ := hs
  haveI : Finite (muX N a n) := Finite.of_equiv _ e.symm.toEquiv
  haveI : NeZero (n : PadicAlgCl p) := ⟨by exact_mod_cast NeZero.ne n⟩
  have h1 : Nat.card (KummerTheory.Mu n (PadicAlgCl p)) = n :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity (PadicAlgCl p) n
  have h2 : Nat.card (muX N a n) = n := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  haveI : Finite (KummerTheory.Mu n (PadicAlgCl p)) :=
    Nat.finite_of_card_ne_zero (by rw [h1]; exact NeZero.ne n)
  exact (uMu_injective N a n).bijective_of_nat_card_le (by rw [h1, h2])

variable (H : Subgroup (GK p E))

/-- `μ_n(X) ≅ μ_n(K̄)` as `H`-modules (`H` acting on `μ_n(X)` through `H_A`). -/
noncomputable def uMuEquiv (n : ℕ) [NeZero n]
    (hs : Nonempty (muX N a n ≃* Multiplicative (ZMod n))) :
    Pull (subHom N a H) (muX N a n) ≃* KummerTheory.Mu n (PadicAlgCl p) :=
  MulEquiv.ofBijective (uMu N a n) (uMu_bijective N a n hs)

lemma uMuEquiv_smul (n : ℕ) [NeZero n] (hs : Nonempty (muX N a n ≃* Multiplicative (ZMod n)))
    (h : H) (m : Pull (subHom N a H) (muX N a n)) :
    uMuEquiv N a H n hs (h • m) = h • uMuEquiv N a H n hs m :=
  uMu_smul N a n (h : GK p E) m

end UMu

variable (N : OpenNormalSubgroup (GK p E)) (a : Γ)
  (H : Subgroup (GK p E)) (hH : IsOpen (H : Set (GK p E)))

include hH in
lemma finiteDimensional_fixL_padic [FiniteDimensional ℚ_[p] E] :
    FiniteDimensional ℚ_[p] (fixL H) := by
  haveI := finiteDimensional_fixL H hH
  exact Module.Finite.trans E (fixL H)

/-- `F_N(X) ≅ H²(H, μ_N(X)) ≅ H²(H, μ_N(K̄)) ≅ H²(L, μ_N)` for an `(N, H)`-saturated `X`. -/
noncomputable def fnEquivH2L (n : ℕ) [NeZero n] (hs : IsSaturated N a H n) :
    FN N a H n ≃* Brauer.H2Mu (fixL H) (PadicAlgCl p) n :=
  (fnEquivH2 N a H n hs).trans <|
    (ContH2Aux.mapCoeff (uMuEquiv N a H n hs.muSat) (uMuEquiv_smul N a H n hs.muSat)).trans <|
      h2HEquiv H hH n

/-- **`F_N(X) ≅ ℤ/N`** for an `(N, H)`-saturated `X` ([FrdII], Definition 2.2(ii):
`F_N(A) ≅ H²(H, μ_N(A)) ≅ ℤ/Nℤ`): through `H²(H, μ_N(X)) ≅ H²(H, μ_N(K̄)) ≅ H²(L, μ_N)` and the
canonical invariant isomorphism `PadicField.h2MuEquiv` of local class field theory. -/
noncomputable def fnEquiv [FiniteDimensional ℚ_[p] E] (n : ℕ) [NeZero n]
    (hs : IsSaturated N a H n) :
    FN N a H n ≃* Multiplicative (ZMod n) :=
  haveI := finiteDimensional_fixL_padic H hH
  (fnEquivH2L N a H hH n hs).trans <|
    PadicField.h2MuEquiv p (fixL H) (PadicAlgCl p) (Nat.pos_of_ne_zero (NeZero.ne n))

end PAdicGalois

end Frobenioid

end Iut
