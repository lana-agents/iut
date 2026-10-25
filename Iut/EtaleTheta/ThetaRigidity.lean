/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaCohomology

/-!
# Reducing the indeterminacy by evaluation at a section ([EtTh], Thm. 1.6(iii), last step)

The proof of [EtTh], Thm. 1.6(iii) (l.1602–1611), reduces the indeterminacy of the theta classes
from `(K̈^×)^∧ = F2` to `O^×_K̈` "by evaluating the classes `η̈^Θ` at a cusp ... via the canonical
integral structure": restricting along a section `G_K → Π` of the projection (the decomposition
group of a cusp with its canonical integral structure, [EtTh], Prop. 1.4(iii)).

Group-theoretic content: for `D ⊴ G` acting trivially on `M` and a continuous section
`σ : G ⧸ D → G` of the projection, restriction along `σ` is a left inverse of inflation
(`resSection_inflation`). Hence two classes that differ by `F2` and have restrictions along `σ`
differing by an element of a subgroup `U ≤ H¹(G ⧸ D, M)` differ by the inflation of an element of
`U` (`div_mem_inflation_map_of_resSection`); in particular the theta class is determined by its
value along `σ` (`eq_of_mem_thetaClassSet_of_resSection_eq`).
-/

namespace ContH1

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]
  (D : Subgroup G) [D.Normal] (hD : ∀ d ∈ D, ∀ m : M, d • m = m)

/-- Restriction along a continuous section `σ : G ⧸ D → G` of the projection. -/
def resSection (σ : G ⧸ D →* G) (hσc : Continuous σ) (hσ : ∀ x, (σ x : G ⧸ D) = x) :
    letI := MulDistribMulAction.quotientOfLeKer D hD
    ContH1 G M →* ContH1 (G ⧸ D) M :=
  letI := MulDistribMulAction.quotientOfLeKer D hD
  map σ hσc (MonoidHom.id M) continuous_id fun x m => by
    change σ x • m = x • m
    conv_rhs => rw [← hσ x]
    rfl

/-- **Restriction along a section is a left inverse of inflation.** -/
theorem resSection_inflation (σ : G ⧸ D →* G) (hσc : Continuous σ)
    (hσ : ∀ x, (σ x : G ⧸ D) = x) :
    letI := MulDistribMulAction.quotientOfLeKer D hD
    ∀ z : ContH1 (G ⧸ D) M,
      resSection D hD σ hσc hσ
        (inflation D (fun g m => MulDistribMulAction.quotientOfLeKer_smul D hD g m) z) = z := by
  letI := MulDistribMulAction.quotientOfLeKer D hD
  intro z
  induction z using induction_on with
  | h c =>
    change mk _ = mk c
    congr 1
    apply Subtype.ext
    funext x
    change c ((σ x : G) : G ⧸ D) = c x
    rw [hσ x]

/-- **Reduction of the indeterminacy** ([EtTh], Thm. 1.6(iii), last step): if `x / y ∈ F2` and
the restrictions of `x` and `y` along the section `σ` differ by an element of `U`, then `x / y` is
the inflation of an element of `U`. -/
theorem div_mem_inflation_map_of_resSection (σ : G ⧸ D →* G) (hσc : Continuous σ)
    (hσ : ∀ x, (σ x : G ⧸ D) = x) :
    letI := MulDistribMulAction.quotientOfLeKer D hD
    ∀ (U : Subgroup (ContH1 (G ⧸ D) M)) (x y : ContH1 G M), x / y ∈ F2 hD →
      resSection D hD σ hσc hσ x / resSection D hD σ hσc hσ y ∈ U →
      x / y ∈ U.map (inflation D fun g m => MulDistribMulAction.quotientOfLeKer_smul D hD g m) := by
  letI := MulDistribMulAction.quotientOfLeKer D hD
  intro U x y hF2 hU
  have hrange := ker_resTriv_eq_range_inflation D hD
  rw [F2] at hF2
  rw [hrange] at hF2
  obtain ⟨z, hz⟩ := hF2
  refine ⟨z, ?_, hz⟩
  have := resSection_inflation D hD σ hσc hσ z
  rw [hz, map_div] at this
  rwa [← this]

/-- **The theta class is determined by its restriction along a section**: two theta classes
(`thetaClassSet`) with the same restriction along `σ` are equal. -/
theorem eq_of_mem_thetaClassSet_of_resSection_eq {DΘ : Subgroup G} (hle : DΘ ≤ D)
    (σ : G ⧸ D →* G) (hσc : Continuous σ) (hσ : ∀ x, (σ x : G ⧸ D) = x)
    (lam : DΘ →* M) (ι : G ≃ₜ* G) (f : M ≃* M) (hf : Continuous f)
    (hcomp : ∀ (g : G) (m : M), f (g • m) = ι g • f m) (hιD : ∀ d ∈ D, ι d ∈ D)
    (hno : NoInvariantHom (DΘ := DΘ) ι f hιD) {x y : ContH1 G M}
    (hx : x ∈ thetaClassSet hle hD lam ι f hf hcomp)
    (hy : y ∈ thetaClassSet hle hD lam ι f hf hcomp)
    (hxy : resSection D hD σ hσc hσ x = resSection D hD σ hσc hσ y) : x = y := by
  letI := MulDistribMulAction.quotientOfLeKer D hD
  have h := div_mem_inflation_map_of_resSection D hD σ hσc hσ ⊥ x y
    (div_mem_F2_of_mem_thetaClassSet hle hD lam ι f hf hcomp hιD hno hx hy)
    (by rw [hxy, div_self', Subgroup.mem_bot])
  rw [Subgroup.map_bot, Subgroup.mem_bot, div_eq_one] at h
  exact h

end ContH1
