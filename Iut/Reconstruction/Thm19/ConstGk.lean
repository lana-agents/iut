/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ResKer
import Iut.Reconstruction.Thm19.ConstExtThmC
import Iut.Reconstruction.Thm19.StageNF

/-!
# `G_{K₁} ≃ₜ* G_{K₁'}` for the stage isomorphisms (MR9 item 4, step 3)

The stage isomorphisms `constIso e ψ K : Π_{U_K} ≃ₜ* Π_{U'_{K'}}` (`G_{K'} = ψ(G_K)`) lie over an
isomorphism of the absolute Galois groups of the fields of constants `K`, `K'`; the classes
`η_D ∈ H¹(G_K, Δ_X^{ab})` of [AbsTopIII] Prop 1.6 (ii) (`Topics in Absolute Anabelian Geometry
III.txt` l.1993–2000) at the stage live over `G_K`. Here:

* `galRestrict_kbar_injective`: `G_K → G_k` is injective (`K̄ = k̄`, `mem_kbar_stage_iff`);
* `piToGk_constExt_eq_one_iff`: `Π_{U_K} → G_K` and `Π_{U_K} → Π_U → G_k` have the same kernel;
* **`gkConstIso`**: `G_K ≃ₜ* G_{K'}` (descent of `constIso` along `Π_{U_K} ↠ G_K`,
  `descendCongr`), with **`piToGk_constIso`**.
-/

open KummerTheory Curve AffOrbicurve CurvesJacobian CurvesJacobian.Kummer Pi1.Orbifold

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section Restrict

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {K : IntermediateField k Ω}
  [Algebra.IsAlgebraic k K] {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω]
  [IsAlgClosed Ω] [CharZero Ω]

attribute [local instance] algebraFRes algebraKbarRes

/-- **`G_K → G_k` is injective** (`K / k` algebraic: `K̄ = k̄`). -/
lemma galRestrict_kbar_injective :
    Function.Injective (galRestrict k K (kbar k Ω) (kbar K Ω)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine AlgEquiv.ext fun y => Subtype.ext ?_
  have hy : (y : Ω) ∈ kbar k Ω := (mem_kbar_stage_iff K).1 y.2
  have h1 := coe_galRestrict_kbar (K := K) g ⟨y, hy⟩
  rw [hg, AlgEquiv.one_apply] at h1
  have h2 : algebraMap (kbar k Ω) (kbar K Ω) ⟨y, hy⟩ = y := Subtype.ext rfl
  rw [h2] at h1
  rw [AlgEquiv.one_apply]
  exact h1.symm

/-- `Π_{U_K} → G_K` and `Π_{U_K} → Π_U → G_k` have the same kernel. -/
lemma piToGk_constExt_eq_one_iff (p : Pi (constExt K D)) :
    piToGk (constExt K D) p = 1 ↔ piToGk D (piRes K D p) = 1 := by
  rw [piToGk_piRes, map_eq_one_iff _ galRestrict_kbar_injective]

end Restrict

section Iso

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] [CharZero Ω]
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω'] [CharZero Ω']
  (e : Pi D ≃ₜ* Pi D') (ψ : Gk k Ω ≃* Gk k' Ω')
  (he : ∀ p, piToGk D' (e p) = ψ (piToGk D p)) (hs : Function.Surjective (piToGk D))
  (K : IntermediateField k Ω) [FiniteDimensional k K] [FiniteDimensional k' (constField ψ K)]
  (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
  (hk' : ∀ x : F D', IsAlgebraic k' x → x ∈ Set.range (algebraMap k' (F D')))

/-- **`G_K ≃ₜ* G_{K'}`** under the stage isomorphism `constIso e ψ K` (`G_{K'} = ψ(G_K)`). -/
def gkConstIso : Gk K Ω ≃ₜ* Gk (constField ψ K) Ω' :=
  descendCongr (piToGk (constExt K D)) (piToGk (constExt (constField ψ K) D'))
    (continuous_piToGk _) (continuous_piToGk _)
    (piToGk_surjective _ (mem_range_of_isAlgebraic_F_constExt K hk))
    (piToGk_surjective _ (mem_range_of_isAlgebraic_F_constExt (constField ψ K) hk'))
    (constIso e ψ he hs K) fun p => by
      rw [piToGk_constExt_eq_one_iff, piToGk_constExt_eq_one_iff, piRes_constIso, he,
        map_eq_one_iff _ ψ.injective]

/-- **`constIso` lies over `gkConstIso`.** -/
lemma piToGk_constIso (p : Pi (constExt K D)) :
    piToGk (constExt (constField ψ K) D') (constIso e ψ he hs K p) =
      gkConstIso e ψ he hs K hk hk' (piToGk (constExt K D) p) :=
  (descendCongr_apply _ _ _ _ _ _ _ _ p).symm

end Iso

end Iut.Reconstruction.Thm19
