/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Env.Shift

/-!
# Bi-theta environments ([EtTh], Def. 2.13(iii))

[EtTh], Def. 2.13(iii): a (mod `N`) **model bi-theta environment** consists of the data (a)–(c)
of a model mono-theta environment together with
(d) the `μ_N`-conjugacy class of subgroups of `Π^tp_Y̲[μ_N]` determined by the image of the
algebraic section `s^alg_Ÿ̲`;
a **bi-theta environment** is a collection `(Π, D_Π, s^Θ_Π, s^alg_Π)` isomorphic to a model one,
and an isomorphism of bi-theta environments is an isomorphism of topological groups mapping
`D`, `s^Θ` and `s^alg` to their counterparts.

* `BiThetaEnv`, `BiThetaEnv.Iso` (with `refl`, `trans`, `symm`) and the forgetful map
  `BiThetaEnv.Iso.toMono` to isomorphisms of the underlying mono-theta environments;
* `modelBiEnv`: the model bi-theta environment of the abstract theta setting (`Env/Model.lean`;
  datum (d) is `algSubgroups`), whose underlying mono-theta environment is `modelEnv`;
* `algSubgroups_eq_thetaSubgroups_one`: datum (d) is datum (c) for the trivial cocycle, so the
  results on datum (c) apply to it;
* `modelBiEnv_eq_of_cohomologous` (cohomologous cocycles give the same bi-theta environment);
* `shiftBiIso`: a shifting automorphism `α_δ` ([EtTh], Prop. 2.14(ii)) is an isomorphism of
  *bi*-theta environments as soon as `δ|_{Π_Ÿ̲}` is a coboundary; in general it moves datum (d)
  to the class of `-δ` (`image_algSubgroups_shift`) — which is why the automorphism groups of
  bi-theta environments are smaller ([EtTh], Prop. 2.14(iii), Rem. 2.18.1).
-/

namespace Iut.EtaleTheta

universe u

/-- **A bi-theta environment** ([EtTh], Def. 2.13(iii)): a mono-theta environment together with
a collection of subgroups (the `μ_N`-conjugacy class of the image of the algebraic section). -/
structure BiThetaEnv extends MonoThetaEnv.{u} where
  /-- Datum (d): the algebraic subgroups. -/
  algSubgroups : Set (Subgroup G)

namespace BiThetaEnv

/-- **An isomorphism of bi-theta environments** ([EtTh], Def. 2.13(iii)): an isomorphism of the
underlying mono-theta environments mapping datum (d) onto datum (d). -/
structure Iso (B B' : BiThetaEnv.{u}) where
  /-- The isomorphism of the underlying mono-theta environments. -/
  toMono : MonoThetaEnv.Iso B.toMonoThetaEnv B'.toMonoThetaEnv
  map_alg : Subgroup.map toMono.e.toMulEquiv.toMonoidHom '' B.algSubgroups = B'.algSubgroups

lemma map_refl_image {G : Type*} [Group G] (S : Set (Subgroup G)) :
    Subgroup.map (MulEquiv.refl G).toMonoidHom '' S = S := by
  convert Set.image_id S using 2 with H
  ext x
  simp

/-- The identity isomorphism. -/
def Iso.refl (B : BiThetaEnv.{u}) : Iso B B where
  toMono := MonoThetaEnv.Iso.refl B.toMonoThetaEnv
  map_alg := map_refl_image B.algSubgroups

/-- Composition of isomorphisms. -/
def Iso.trans {B B' B'' : BiThetaEnv.{u}} (f : Iso B B') (g : Iso B' B'') : Iso B B'' where
  toMono := f.toMono.trans g.toMono
  map_alg := by
    rw [← g.map_alg, ← f.map_alg, Set.image_image]
    refine Set.image_congr fun H _ => ?_
    rw [Subgroup.map_map]
    rfl

/-- The inverse isomorphism. -/
def Iso.symm {B B' : BiThetaEnv.{u}} (f : Iso B B') : Iso B' B where
  toMono := f.toMono.symm
  map_alg := by
    rw [← f.map_alg, Set.image_image]
    convert Set.image_id B.algSubgroups using 2 with H
    ext x
    simp only [Subgroup.mem_map, id]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      convert hz
      exact f.toMono.e.symm_apply_apply z
    · intro hx
      exact ⟨f.toMono.e x, ⟨x, hx, rfl⟩, f.toMono.e.symm_apply_apply x⟩

end BiThetaEnv

namespace Env

universe v

variable {PX G μ : Type v} [Group PX] [Group G] [CommGroup μ] (aug : PX →* G)
  (ψ : G →* MulAut μ)

section Alg

variable {PY PYdd : Subgroup PX} (hle : PYdd ≤ PY)

/-- **Datum (d) is datum (c) for the trivial cocycle.** -/
theorem algSubgroups_eq_thetaSubgroups_one :
    algSubgroups aug ψ hle = thetaSubgroups aug ψ hle (isCocycle_one (φ := actDD aug ψ PYdd)) := by
  unfold algSubgroups thetaSubgroups
  congr 2
  funext g
  simp [thetaCocycle]

end Alg

section Model

variable [TopologicalSpace PX] [IsTopologicalGroup PX] [TopologicalSpace μ] [DiscreteTopology μ]
  (Kum : Subgroup (G → μ)) {PY PYdd : Subgroup PX} (hle : PYdd ≤ PY)
  (hψ : IsOpen ((act aug ψ).ker : Set PX)) (hKum : ∀ κ ∈ Kum, IsCocycle ψ κ)

/-- **The model bi-theta environment** ([EtTh], Def. 2.13(iii)): the model mono-theta environment
together with the `μ`-conjugacy class of the image of the algebraic section. -/
def modelBiEnv {η : PYdd → μ} (hη : IsCocycle (actDD aug ψ PYdd) η) : BiThetaEnv.{v} where
  toMonoThetaEnv := modelEnv aug ψ Kum hle hψ hKum hη
  algSubgroups := algSubgroups aug ψ hle

@[simp] lemma modelBiEnv_toMonoThetaEnv {η : PYdd → μ} (hη : IsCocycle (actDD aug ψ PYdd) η) :
    (modelBiEnv aug ψ Kum hle hψ hKum hη).toMonoThetaEnv = modelEnv aug ψ Kum hle hψ hKum hη :=
  rfl

/-- **Cohomologous cocycles give the same model bi-theta environment.** -/
theorem modelBiEnv_eq_of_cohomologous {η η' : PYdd → μ} (hη : IsCocycle (actDD aug ψ PYdd) η)
    (hη' : IsCocycle (actDD aug ψ PYdd) η') (h : Cohomologous (actDD aug ψ PYdd) η η') :
    modelBiEnv aug ψ Kum hle hψ hKum hη = modelBiEnv aug ψ Kum hle hψ hKum hη' := by
  have e := (thetaSubgroups_eq_iff aug ψ hle hη hη').2 h
  simp only [modelBiEnv, modelEnv]
  rw [e]

variable [PY.Normal] {δY : PY → μ} (hδY : IsCocycle (actY aug ψ PY) δY)

omit [TopologicalSpace PX] [IsTopologicalGroup PX] [TopologicalSpace μ] [DiscreteTopology μ]
  [PY.Normal] in
/-- **A shift moves datum (d) to the class of `-δ`.** -/
theorem image_algSubgroups_shift :
    Subgroup.map (shift aug ψ δY hδY).toMonoidHom '' algSubgroups aug ψ hle =
      thetaSubgroups aug ψ hle (isCocycle_mul_inv_resDD aug ψ hδY hle
        (isCocycle_one (φ := actDD aug ψ PYdd))) := by
  rw [algSubgroups_eq_thetaSubgroups_one]
  exact image_thetaSubgroups_shift aug ψ hδY hle _

/-- **Shifts by cocycles that are coboundaries on `Π_Ÿ̲` are isomorphisms of bi-theta
environments** ([EtTh], Prop. 2.14(ii),(iii)): under the hypotheses of `shiftIso`, if moreover
`δ|_{Π_Ÿ̲}` is a coboundary, `α_δ` also maps datum (d) onto datum (d). -/
def shiftBiIso (hδc : Continuous δY) (hconj : ShiftConj aug ψ Kum δY)
    (hcob : Cohomologous (actDD aug ψ PYdd) (fun g => 1 * (resDD hle δY g)⁻¹) (fun _ => 1))
    {η : PYdd → μ} (hη : IsCocycle (actDD aug ψ PYdd) η) :
    BiThetaEnv.Iso (modelBiEnv aug ψ Kum hle hψ hKum hη)
      (modelBiEnv aug ψ Kum hle hψ hKum (isCocycle_mul_inv_resDD aug ψ hδY hle hη)) where
  toMono := shiftIso aug ψ Kum hle hψ hKum hδY hδc hconj hη
  map_alg := by
    change Subgroup.map (shift aug ψ δY hδY).toMonoidHom '' algSubgroups aug ψ hle =
      algSubgroups aug ψ hle
    rw [image_algSubgroups_shift, algSubgroups_eq_thetaSubgroups_one]
    exact (thetaSubgroups_eq_iff aug ψ hle _ _).2 hcob

end Model

end Env

end Iut.EtaleTheta
