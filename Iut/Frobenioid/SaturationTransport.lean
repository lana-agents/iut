/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.ReciprocityIso

/-!
# Transport of saturation and of `F_N` ([FrdII], Theorem 2.4(i))

[FrdII], Theorem 2.4(i): "`Ψ` maps `(N, H₁)`-saturated objects to `(N, H₂)`-saturated objects and
induces isomorphisms […] `(H₁)_{A₁} ≅ (H₂)_{A₂}`; […] `H¹((H₁)_{A₁}, μ_N(A₁)) ≅ H¹((H₂)_{A₂},
μ_N(A₂))`; `F_N(A₁) ≅ F_N(A₂)`". The proof: "The remainder of assertion (i) follows immediately
from the fact […] that `Ψ` preserves `O^▷(−)`, together with the 'manifestly
group- or category-theoretic' construction given above of the Kummer and reciprocity maps."

This file makes the group-theoretic construction explicit. For a group `G` (discrete) with a
commutative normal subgroup `U` (`O^×(A)` in `Aut_C(A)`), a topological group `K` with a continuous
`j : K →* G` and `H ≤ K` (`H_A = j(H)`): `Saturation.IsSat U j hj H n` (Definition 2.2(ii)(a),(c))
and `Saturation.FNG U j hj H n` (`F_N`). **`IsSat.transport`**, **`fngEquiv`**: an isomorphism
`φ : G ≅ G'` with `φ(U) = U'` and `α : K ≅ K'` with `j' ∘ α = φ ∘ j` transport saturation and
`F_N`; `subAEquiv` (`H_A ≅ H'_{A'}`), `h1Equiv` (`H¹(H_A, μ_N) ≅ H¹(H'_{A'}, μ_N')`).
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

namespace ContH2Aux

variable {G G' M M' : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]
  [Group G'] [TopologicalSpace G'] [CommGroup M'] [MulDistribMulAction G' M']

/-- `H²(G, M) ≅ H²(G', M')` along `e : G' ≃ₜ* G` and a compatible `f : M ≃* M'`. -/
noncomputable def mapEquiv2 (e : G' ≃ₜ* G) (f : M ≃* M')
    (h : ∀ (g : G') (m : M), f (e g • m) = g • f m) : ContH2 G M ≃* ContH2 G' M' where
  toFun := ContH2.map (e : G' →* G) e.continuous f.toMonoidHom h
  invFun := ContH2.map (e.symm : G →* G') e.symm.continuous f.symm.toMonoidHom fun g m => by
    apply f.injective
    change f (f.symm (e.symm g • m)) = f (g • f.symm m)
    rw [MulEquiv.apply_symm_apply]
    conv_rhs => rw [← e.apply_symm_apply g]
    change _ = f ((e : G' →* G) (e.symm g) • f.symm m)
    rw [show ((e : G' →* G) (e.symm g)) = e (e.symm g) from rfl, h, MulEquiv.apply_symm_apply]
  left_inv x := by
    induction x using ContH2.induction_on with | h c => ?_
    simp only [ContH2.map_mk]
    congr 1
    exact ContH2.cocycles_ext fun a b => by simp
  right_inv x := by
    induction x using ContH2.induction_on with | h c => ?_
    simp only [ContH2.map_mk]
    congr 1
    exact ContH2.cocycles_ext fun a b => by simp
  map_mul' := map_mul _

end ContH2Aux

namespace Saturation

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] (U : Subgroup G)
  [U.Normal] [IsMulCommutative U] {K : Type*} [Group K] [TopologicalSpace K] (j : K →* G)
  (hj : Continuous j) (H : Subgroup K) (n : ℕ)

/-- `H_A = j(H)`. -/
abbrev subAG : Subgroup G := H.map j

/-- `H ↠ H_A`. -/
def subHomG : H →* subAG j H := j.subgroupMap H

include hj in
lemma continuous_subHomG : Continuous (subHomG j H) :=
  Continuous.subtype_mk (hj.comp continuous_subtype_val) _

/-- **`(n, H)`-saturation** ([FrdII], Definition 2.2(ii)(a),(c)) for the datum `(U, j, H)`. -/
structure IsSat : Prop where
  /-- (a) `μ_n(U) ≅ ℤ/n`. -/
  muSat : Nonempty (KummerClass.mu U n ≃* Multiplicative (ZMod n))
  /-- (c) `H¹(H_A, μ_n(U)) ≅ H¹(H, μ_n(U))`. -/
  h1Mu : Function.Bijective
    (infl₁ (subHomG j H) (continuous_subHomG j hj H) (KummerClass.mu U n))
  /-- (c) `H¹(H_A, ℤ/n) ≅ H¹(H, ℤ/n)`. -/
  h1Z : Function.Bijective (infl₁Z (subHomG j H) (continuous_subHomG j hj H) n)
  /-- (c) `H²(H_A, μ_n(U)) ↠ H²(H, μ_n(U))`. -/
  h2Mu : Function.Surjective
    (infl₂ (subHomG j H) (continuous_subHomG j hj H) (KummerClass.mu U n))

/-- **`F_N`** for the datum `(U, j, H)`. -/
abbrev FNG : Type _ :=
  ContH2 (subAG j H) (KummerClass.mu U n) ⧸
    (infl₂ (subHomG j H) (continuous_subHomG j hj H) (KummerClass.mu U n)).ker

end Gen

section Transport

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] {U : Subgroup G}
  [U.Normal] [IsMulCommutative U] {K : Type*} [Group K] [TopologicalSpace K] {j : K →* G}
  (hj : Continuous j) (H : Subgroup K) (n : ℕ)
variable {G' : Type*} [Group G'] [TopologicalSpace G'] [DiscreteTopology G'] {U' : Subgroup G'}
  [U'.Normal] [IsMulCommutative U'] {K' : Type*} [Group K'] [TopologicalSpace K'] {j' : K' →* G'}
  (hj' : Continuous j')
variable (φ : G ≃* G') (hU : ∀ u, u ∈ U ↔ φ u ∈ U') (α : K ≃ₜ* K')
  (hjα : ∀ k, j' (α k) = φ (j k))

include hjα in
lemma map_subAG : (subAG j H).map (φ : G →* G') = subAG j' (H.map (α : K →* K')) := by
  change _ = (H.map (α : K →* K')).map j'
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext k
  exact (hjα k).symm

/-- **`H_A ≅ H'_{A'}`**. -/
noncomputable def subAEquiv : subAG j H ≃* subAG j' (H.map (α : K →* K')) :=
  (φ.subgroupMap (subAG j H)).trans (MulEquiv.subgroupCongr (map_subAG H φ α hjα))

lemma coe_subAEquiv (x : subAG j H) : (subAEquiv H φ α hjα x : G') = φ x := rfl

/-- `H_A ≅ H'_{A'}` as topological groups (both discrete). -/
noncomputable def subATEquiv : subAG j H ≃ₜ* subAG j' (H.map (α : K →* K')) where
  toMulEquiv := subAEquiv H φ α hjα
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- `H ≅ α(H)`. -/
noncomputable def subKEquiv : H ≃ₜ* H.map (α : K →* K') where
  toMulEquiv := (α.toMulEquiv).subgroupMap H
  continuous_toFun := Continuous.subtype_mk (α.continuous.comp continuous_subtype_val) _
  continuous_invFun := by
    refine Continuous.subtype_mk (α.symm.continuous.comp continuous_subtype_val) ?_

lemma coe_subKEquiv (h : H) : (subKEquiv H α h : K') = α h := rfl

include hjα in
lemma subHomG_subKEquiv (h : H) :
    subHomG j' (H.map (α : K →* K')) (subKEquiv H α h) = subAEquiv H φ α hjα (subHomG j H h) :=
  Subtype.ext (hjα h)

/-- `μ_n(U) ≅ μ_n(U')`. -/
noncomputable def muEquiv : KummerClass.mu U n ≃* KummerClass.mu U' n where
  toFun := KummerClass.muMap U n φ fun u hu => (hU u).mp hu
  invFun := KummerClass.muMap U' n φ.symm fun u hu => (hU _).mpr (by simpa using hu)
  left_inv m := Subtype.ext (Subtype.ext (φ.symm_apply_apply _))
  right_inv m := Subtype.ext (Subtype.ext (φ.apply_symm_apply _))
  map_mul' := map_mul _

lemma coe_muEquiv (m : KummerClass.mu U n) : ((muEquiv n φ hU m : U') : G') = φ m := rfl

lemma muEquiv_smul (x : subAG j H) (m : KummerClass.mu U n) :
    muEquiv n φ hU (x • m) = subAEquiv H φ α hjα x • muEquiv n φ hU m := by
  apply Subtype.ext; apply Subtype.ext
  change φ ((x : G) * m * (x : G)⁻¹) = φ x * φ m * (φ x)⁻¹
  simp

/-- **`H¹(H_A, μ_n(U)) ≅ H¹(H'_{A'}, μ_n(U'))`**. -/
noncomputable def h1Equiv :
    ContH1 (subAG j H) (KummerClass.mu U n) ≃*
      ContH1 (subAG j' (H.map (α : K →* K'))) (KummerClass.mu U' n) :=
  ContH1Aux.mapEquiv (subATEquiv H φ α hjα).symm (muEquiv n φ hU) continuous_of_discreteTopology
    continuous_of_discreteTopology fun x m => by
      rw [muEquiv_smul H n φ hU α hjα]
      congr 1
      exact (subAEquiv H φ α hjα).apply_symm_apply x

/-- `H¹(H, μ_n(U)) ≅ H¹(α(H), μ_n(U'))` (actions through `H_A`, `H'_{A'}`). -/
noncomputable def h1PullEquiv :
    ContH1 H (Pull (subHomG j H) (KummerClass.mu U n)) ≃*
      ContH1 (H.map (α : K →* K')) (Pull (subHomG j' (H.map (α : K →* K')))
        (KummerClass.mu U' n)) :=
  ContH1Aux.mapEquiv (subKEquiv H α).symm (muEquiv n φ hU)
    (continuous_of_discreteTopology (α := KummerClass.mu U n))
    (continuous_of_discreteTopology (α := KummerClass.mu U' n)) fun h m =>
      (muEquiv_smul H n φ hU α hjα (subHomG j H ((subKEquiv H α).symm h)) m).trans (by
        rw [← subHomG_subKEquiv H φ α hjα, ContinuousMulEquiv.apply_symm_apply]
        rfl)

lemma subAEquiv_symm_subHomG (h' : H.map (α : K →* K')) :
    (subAEquiv H φ α hjα).symm (subHomG j' (H.map (α : K →* K')) h') =
      subHomG j H ((subKEquiv H α).symm h') := by
  rw [MulEquiv.symm_apply_eq, ← subHomG_subKEquiv H φ α hjα,
    ContinuousMulEquiv.apply_symm_apply]

lemma infl₁_h1Equiv (x : ContH1 (subAG j H) (KummerClass.mu U n)) :
    infl₁ (subHomG j' (H.map (α : K →* K'))) (continuous_subHomG j' hj' _) (KummerClass.mu U' n)
      (h1Equiv H n φ hU α hjα x) =
      h1PullEquiv H n φ hU α hjα (infl₁ (subHomG j H) (continuous_subHomG j hj H)
        (KummerClass.mu U n) x) := by
  induction x using ContH1.induction_on with | h c => ?_
  change ContH1.mk _ = ContH1.mk _
  congr 1
  refine Subtype.ext (funext fun h' => ?_)
  change muEquiv n φ hU ((c : subAG j H → KummerClass.mu U n)
      ((subAEquiv H φ α hjα).symm (subHomG j' (H.map (α : K →* K')) h'))) =
    muEquiv n φ hU ((c : subAG j H → KummerClass.mu U n)
      (subHomG j H ((subKEquiv H α).symm h')))
  rw [subAEquiv_symm_subHomG]

/-- `H¹(H_A, ℤ/n) ≅ H¹(H'_{A'}, ℤ/n)`. -/
noncomputable def h1ZEquiv :
    ContH1 (subAG j H) (ZTriv n) ≃* ContH1 (subAG j' (H.map (α : K →* K'))) (ZTriv n) :=
  ContH1Aux.mapEquiv (subATEquiv H φ α hjα).symm (MulEquiv.refl (ZTriv n)) continuous_id
    continuous_id fun _ _ => rfl

/-- `H¹(H, ℤ/n) ≅ H¹(α(H), ℤ/n)`. -/
noncomputable def h1ZKEquiv :
    ContH1 H (ZTriv n) ≃* ContH1 (H.map (α : K →* K')) (ZTriv n) :=
  ContH1Aux.mapEquiv (subKEquiv H α).symm (MulEquiv.refl (ZTriv n)) continuous_id
    continuous_id fun _ _ => rfl

lemma infl₁Z_h1ZEquiv (x : ContH1 (subAG j H) (ZTriv n)) :
    infl₁Z (subHomG j' (H.map (α : K →* K'))) (continuous_subHomG j' hj' _) n
      (h1ZEquiv H n φ α hjα x) =
      h1ZKEquiv H n α (infl₁Z (subHomG j H) (continuous_subHomG j hj H) n x) := by
  induction x using ContH1.induction_on with | h c => ?_
  change ContH1.mk _ = ContH1.mk _
  congr 1
  refine Subtype.ext (funext fun h' => ?_)
  change (c : subAG j H → ZTriv n)
      ((subAEquiv H φ α hjα).symm (subHomG j' (H.map (α : K →* K')) h')) =
    (c : subAG j H → ZTriv n) (subHomG j H ((subKEquiv H α).symm h'))
  rw [subAEquiv_symm_subHomG]

/-- `H²(H_A, μ_n(U)) ≅ H²(H'_{A'}, μ_n(U'))`. -/
noncomputable def h2Equiv :
    ContH2 (subAG j H) (KummerClass.mu U n) ≃*
      ContH2 (subAG j' (H.map (α : K →* K'))) (KummerClass.mu U' n) :=
  ContH2Aux.mapEquiv2 (subATEquiv H φ α hjα).symm (muEquiv n φ hU) fun x m => by
    rw [muEquiv_smul H n φ hU α hjα]
    congr 1
    exact (subAEquiv H φ α hjα).apply_symm_apply x

/-- `H²(H, μ_n(U)) ≅ H²(α(H), μ_n(U'))`. -/
noncomputable def h2PullEquiv :
    ContH2 H (Pull (subHomG j H) (KummerClass.mu U n)) ≃*
      ContH2 (H.map (α : K →* K')) (Pull (subHomG j' (H.map (α : K →* K')))
        (KummerClass.mu U' n)) :=
  ContH2Aux.mapEquiv2 (subKEquiv H α).symm (muEquiv n φ hU) fun h m =>
    (muEquiv_smul H n φ hU α hjα (subHomG j H ((subKEquiv H α).symm h)) m).trans (by
      rw [← subHomG_subKEquiv H φ α hjα, ContinuousMulEquiv.apply_symm_apply]
      rfl)

lemma infl₂_h2Equiv (x : ContH2 (subAG j H) (KummerClass.mu U n)) :
    infl₂ (subHomG j' (H.map (α : K →* K'))) (continuous_subHomG j' hj' _) (KummerClass.mu U' n)
      (h2Equiv H n φ hU α hjα x) =
      h2PullEquiv H n φ hU α hjα (infl₂ (subHomG j H) (continuous_subHomG j hj H)
        (KummerClass.mu U n) x) := by
  induction x using ContH2.induction_on with | h c => ?_
  change ContH2.mk _ = ContH2.mk _
  congr 1
  refine ContH2.cocycles_ext fun h' h'' => ?_
  change muEquiv n φ hU ((c : subAG j H × subAG j H → KummerClass.mu U n)
      ((subAEquiv H φ α hjα).symm (subHomG j' (H.map (α : K →* K')) h'),
        (subAEquiv H φ α hjα).symm (subHomG j' (H.map (α : K →* K')) h''))) =
    muEquiv n φ hU ((c : subAG j H × subAG j H → KummerClass.mu U n)
      (subHomG j H ((subKEquiv H α).symm h'), subHomG j H ((subKEquiv H α).symm h'')))
  rw [subAEquiv_symm_subHomG, subAEquiv_symm_subHomG]

include hU hjα in
/-- **Transport of saturation** ([FrdII], Theorem 2.4(i): "`Ψ` maps `(N, H₁)`-saturated objects to
`(N, H₂)`-saturated objects"). -/
theorem IsSat.transport (hs : IsSat U j hj H n) : IsSat U' j' hj' (H.map (α : K →* K')) n where
  muSat := hs.muSat.map fun e => (muEquiv n φ hU).symm.trans e
  h1Mu := by
    have e : ⇑(infl₁ (subHomG j' (H.map (α : K →* K'))) (continuous_subHomG j' hj' _)
        (KummerClass.mu U' n)) = h1PullEquiv H n φ hU α hjα ∘
          infl₁ (subHomG j H) (continuous_subHomG j hj H) (KummerClass.mu U n) ∘
            (h1Equiv H n φ hU α hjα).symm := funext fun y => by
      rw [Function.comp_apply, Function.comp_apply, ← infl₁_h1Equiv hj H n hj' φ hU α hjα,
        MulEquiv.apply_symm_apply]
    rw [e]
    exact (h1PullEquiv H n φ hU α hjα).bijective.comp
      (hs.h1Mu.comp (h1Equiv H n φ hU α hjα).symm.bijective)
  h1Z := by
    have e : ⇑(infl₁Z (subHomG j' (H.map (α : K →* K'))) (continuous_subHomG j' hj' _) n) =
        h1ZKEquiv H n α ∘ infl₁Z (subHomG j H) (continuous_subHomG j hj H) n ∘
          (h1ZEquiv H n φ α hjα).symm := funext fun y => by
      rw [Function.comp_apply, Function.comp_apply, ← infl₁Z_h1ZEquiv hj H n hj' φ α hjα,
        MulEquiv.apply_symm_apply]
    rw [e]
    exact (h1ZKEquiv H n α).bijective.comp (hs.h1Z.comp (h1ZEquiv H n φ α hjα).symm.bijective)
  h2Mu := by
    have e : ⇑(infl₂ (subHomG j' (H.map (α : K →* K'))) (continuous_subHomG j' hj' _)
        (KummerClass.mu U' n)) = h2PullEquiv H n φ hU α hjα ∘
          infl₂ (subHomG j H) (continuous_subHomG j hj H) (KummerClass.mu U n) ∘
            (h2Equiv H n φ hU α hjα).symm := funext fun y => by
      rw [Function.comp_apply, Function.comp_apply, ← infl₂_h2Equiv hj H n hj' φ hU α hjα,
        MulEquiv.apply_symm_apply]
    rw [e]
    exact (h2PullEquiv H n φ hU α hjα).surjective.comp
      (hs.h2Mu.comp (h2Equiv H n φ hU α hjα).symm.surjective)

include hj' in
lemma map_ker_infl₂ :
    (infl₂ (subHomG j H) (continuous_subHomG j hj H) (KummerClass.mu U n)).ker.map
      (h2Equiv H n φ hU α hjα).toMonoidHom =
      (infl₂ (subHomG j' (H.map (α : K →* K'))) (continuous_subHomG j' hj' _)
        (KummerClass.mu U' n)).ker := by
  ext y
  rw [Subgroup.mem_map_equiv, MonoidHom.mem_ker, MonoidHom.mem_ker]
  have := infl₂_h2Equiv hj H n hj' φ hU α hjα ((h2Equiv H n φ hU α hjα).symm y)
  rw [MulEquiv.apply_symm_apply] at this
  rw [this, MulEquiv.map_eq_one_iff]

/-- **`F_N(A) ≅ F_N(A')`** ([FrdII], Theorem 2.4(i)). -/
noncomputable def fngEquiv :
    FNG U j hj H n ≃* FNG U' j' hj' (H.map (α : K →* K')) n :=
  QuotientGroup.congr _ _ (h2Equiv H n φ hU α hjα) (map_ker_infl₂ hj H n hj' φ hU α hjα)

end Transport

end Saturation

end Frobenioid

end Iut
