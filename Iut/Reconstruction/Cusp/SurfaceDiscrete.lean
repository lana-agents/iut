/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.SurfaceH2

/-!
# The model `Π̂_{g,0}` is the profinite completion of the discrete surface group

`SurfaceH2.lean` models the profinite closed surface group as `SurfGrp g = F̂ / cl⟨⟨∏ᵢ ⁅aᵢ, bᵢ⁆⟩⟩`,
a quotient of the profinite completion `F̂` of the free group on `a₁, b₁, …, a_g, b_g`.
`pi1` (lana-agents/pi1, `Pi1.ProfiniteSurfaceGroup g 0`, from revision `98c77bc` on) and the
geometric comparison theorems of `curves-jacobian` (`π₁ᵉᵗ(X) ≃ₜ* Π̂_{g,0}`) use instead the
**profinite completion of the discrete one-relator group**
`Π_{g,0} = ⟨a₁, b₁, …, a_g, b_g | ∏ᵢ ⁅aᵢ, bᵢ⁆⟩`.

This file proves that the two agree:

* `SurfDisc g = ⟨a, b | rel g⟩` (Mathlib's `PresentedGroup`) and its completion `SurfCompl g`;
* **`surfComplEquiv g : SurfGrp g ≃ₜ* SurfCompl g`**, sending the class of each free generator
  to the image of the same generator (`surfComplEquiv_surfMap_eta_of`), with inverse described
  on the dense image of `SurfDisc g` (`surfComplEquiv_symm_eta`).

With `pi1`'s relabelling `SurfaceGen g 0 ≃ Gen g` (`a i ↦ inl i`, `b i ↦ inr i`, whose relator
`commProd a b · ordProd ∅` is `rel g`) this is the identification of `SurfGrp g` with `pi1`'s
`Π̂_{g,0}`; that last step needs only the `pi1` pin bump.
-/

namespace Iut.Reconstruction.SurfaceH2

open CategoryTheory ProfiniteGrp

variable (g : ℕ)

/-- **The discrete closed surface group** `Π_{g,0} = ⟨a₁, b₁, …, a_g, b_g | ∏ᵢ ⁅aᵢ, bᵢ⁆⟩`. -/
abbrev SurfDisc : Type := PresentedGroup ({rel g} : Set (FreeGroup (Gen g)))

/-- The profinite completion of the discrete closed surface group. -/
noncomputable abbrev SurfCompl : ProfiniteGrp.{0} :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (SurfDisc g))

/-- `Π_{g,0} → Π̂_{g,0}`. -/
noncomputable def etaC : SurfDisc g →* SurfCompl g :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (SurfDisc g))).hom

instance : T2Space (SurfGrp g) := inferInstance

instance : TotallyDisconnectedSpace (SurfGrp g) :=
  QuotientGroup.totallyDisconnectedSpace_of_isClosed _ inferInstance

/-- The model `SurfGrp g` as an object of `ProfiniteGrp`. -/
noncomputable abbrev surfGrpP : ProfiniteGrp.{0} := ProfiniteGrp.of (SurfGrp g)

lemma surfMap_eta_rel : surfMap g (eta g (rel g)) = 1 := by
  rw [← MonoidHom.mem_ker, ker_surfMap]
  exact eta_rel_mem g

/-- `F → F̂ → SurfGrp g` as a function on the generators. -/
lemma lift_surfMap_eta : FreeGroup.lift (fun x => surfMap g (eta g (FreeGroup.of x))) =
    (surfMap g).comp (eta g) :=
  FreeGroup.ext_hom _ _ fun x => by simp

/-- `Π_{g,0} → SurfGrp g` (generators to generators). -/
noncomputable def discToSurf : SurfDisc g →* SurfGrp g :=
  PresentedGroup.toGroup (f := fun x => surfMap g (eta g (FreeGroup.of x))) (by
    rintro r rfl
    rw [lift_surfMap_eta, MonoidHom.comp_apply, surfMap_eta_rel])

lemma discToSurf_of (x : Gen g) :
    discToSurf g (PresentedGroup.of x) = surfMap g (eta g (FreeGroup.of x)) :=
  PresentedGroup.toGroup.of _

/-- `F̂ → Π̂_{g,0}` extending `F → Π_{g,0} → Π̂_{g,0}`. -/
noncomputable def fhatToCompl : Fhat g →ₜ* SurfCompl g :=
  liftF ((etaC g).comp (PresentedGroup.mk _))

lemma fhatToCompl_eta (x : FreeGroup (Gen g)) :
    fhatToCompl g (eta g x) = etaC g (PresentedGroup.mk _ x) :=
  liftF_eta _ x

lemma relSub_le_ker : relSub g ≤ (fhatToCompl g).toMonoidHom.ker := by
  haveI : IsClosed (((fhatToCompl g).toMonoidHom.ker : Subgroup (Fhat g)) : Set (Fhat g)) :=
    isClosed_singleton.preimage (fhatToCompl g).continuous
  refine relSub_le g this ?_
  rw [MonoidHom.mem_ker]
  change fhatToCompl g (eta g (rel g)) = 1
  rw [fhatToCompl_eta, show PresentedGroup.mk ({rel g} : Set (FreeGroup (Gen g))) (rel g) = 1 from
    PresentedGroup.mk_eq_one_iff.2 (Subgroup.subset_normalClosure (Set.mem_singleton _)), map_one]

/-- `SurfGrp g → Π̂_{g,0}`. -/
noncomputable def surfToCompl : SurfGrp g →* SurfCompl g :=
  QuotientGroup.lift (relSub g) (fhatToCompl g).toMonoidHom (relSub_le_ker g)

lemma surfToCompl_surfMap (f : Fhat g) : surfToCompl g (surfMap g f) = fhatToCompl g f := rfl

lemma continuous_surfToCompl : Continuous (surfToCompl g) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (fhatToCompl g).continuous

/-- `Π̂_{g,0} → SurfGrp g`, the universal property of the completion. -/
noncomputable def complToSurf : SurfCompl g →ₜ* SurfGrp g :=
  (ProfiniteGrp.ProfiniteCompletion.lift (P := surfGrpP g) (GrpCat.ofHom (discToSurf g))).hom

lemma complToSurf_etaC (y : SurfDisc g) : complToSurf g (etaC g y) = discToSurf g y := by
  have h := ProfiniteGrp.ProfiniteCompletion.lift_eta (P := surfGrpP g)
    (GrpCat.ofHom (discToSurf g))
  exact ConcreteCategory.congr_hom h y

lemma complToSurf_surfToCompl (x : SurfGrp g) : complToSurf g (surfToCompl g x) = x := by
  have h : ((complToSurf g).toMonoidHom.comp (surfToCompl g)).comp (surfMap g) =
      (MonoidHom.id _).comp (surfMap g) := by
    refine hom_ext ((complToSurf g).continuous.comp
      ((continuous_surfToCompl g).comp (continuous_surfMap g))) (continuous_surfMap g)
      fun x => ?_
    change complToSurf g (surfToCompl g (surfMap g _)) = surfMap g _
    rw [surfToCompl_surfMap, fhatToCompl_eta, complToSurf_etaC]
    exact discToSurf_of g x
  obtain ⟨f, rfl⟩ := surfMap_surjective g x
  exact DFunLike.congr_fun h f

lemma surfToCompl_complToSurf (y : SurfCompl g) : surfToCompl g (complToSurf g y) = y := by
  have hd : (surfToCompl g).comp (discToSurf g) = etaC g := by
    refine PresentedGroup.ext fun x => ?_
    rw [MonoidHom.comp_apply, discToSurf_of, surfToCompl_surfMap, fhatToCompl_eta]
    rfl
  have h := (ProfiniteGrp.ProfiniteCompletion.denseRange (GrpCat.of (SurfDisc g))).equalizer
    ((continuous_surfToCompl g).comp (complToSurf g).continuous) continuous_id
    (funext fun z => by
      change surfToCompl g (complToSurf g (etaC g z)) = etaC g z
      rw [complToSurf_etaC]
      exact DFunLike.congr_fun hd z)
  exact congrFun h y

/-- **The model `Π̂_{g,0} = F̂ / cl⟨⟨∏ᵢ ⁅aᵢ, bᵢ⁆⟩⟩` is the profinite completion of the discrete
closed surface group** `⟨a, b | ∏ᵢ ⁅aᵢ, bᵢ⁆⟩`, as topological groups. -/
noncomputable def surfComplEquiv : SurfGrp g ≃ₜ* SurfCompl g where
  toFun := surfToCompl g
  invFun := complToSurf g
  left_inv := complToSurf_surfToCompl g
  right_inv := surfToCompl_complToSurf g
  map_mul' := map_mul _
  continuous_toFun := continuous_surfToCompl g
  continuous_invFun := (complToSurf g).continuous

/-- Generators go to generators. -/
lemma surfComplEquiv_surfMap_eta_of (x : Gen g) :
    surfComplEquiv g (surfMap g (eta g (FreeGroup.of x))) = etaC g (PresentedGroup.of x) := by
  exact (surfToCompl_surfMap g _).trans (fhatToCompl_eta g _)

lemma surfComplEquiv_symm_eta (y : SurfDisc g) :
    (surfComplEquiv g).symm (etaC g y) = discToSurf g y :=
  complToSurf_etaC g y

end Iut.Reconstruction.SurfaceH2
