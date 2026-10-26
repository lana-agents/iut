/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Env.AutKernel

/-!
# Functoriality of the model environment in the theta setting ([EtTh], Cor. 2.18(ii),(iv))

[EtTh], proof of Cor. 2.18(iv): the surjectivity of `Isom^μ(M_α, M_β) → Isom(Π_X̲α, Π_X̲β)`
"follows by applying the functorial group-theoretic algorithm of (ii)", i.e. by transporting the
whole construction of the model environment along an isomorphism of the underlying data. This
file proves the transport for the abstract theta setting of `Env/Model.lean`:

* `mapX`: an isomorphism `(φ, σ, u)` of theta data (`φ : Π_X ≅ Π_X'`, `σ : G ≅ G'`, `u : μ ≅ μ'`,
  compatible with the augmentations and the actions) induces `Π_X[μ] ≅ Π_X'[μ']`; it carries
  Kummer twists to Kummer twists (`mapX_twist`, `kumMap`) and inner automorphisms to inner ones;
* `map_DY`, `image_thetaSubgroups_mapY`: if moreover `φ` maps `Π_Y`, `Π_Ÿ` onto `Π_Y'`, `Π_Ÿ'`, the
  Kummer cocycles onto the Kummer cocycles and `η` to `η'`, the induced `Π_Y[μ] ≅ Π_Y'[μ']`
  maps `D_Y` onto `D_Y'` and datum (c) onto datum (c);
* **`mapIso`**: the resulting isomorphism of model environments, lying over `φ` on `Π_Y`
  (`rightPY_mapIso`);
* **`exists_aut_autPY_eq`** (the lifting statement behind the surjectivity half of
  Cor. 2.18(iv)): an automorphism `(φ, σ, u)` of the theta data which preserves `Π_Y` and `Π_Ÿ`,
  preserves the Kummer cocycles, and maps the class of `η` to a class differing from it by a
  Kummer class and the restriction of an admissible shift cocycle (as in `shiftIso`), is induced
  on `Π_Y` by an automorphism of the model environment: `autPY a = φ|_{Π_Y}`.

So the hypothesis `hlift` of `discreteRigidity_env` (`Env/Tower.lean`) reduces to: every
automorphism of `Π_Y` induced by the level-`0` model extends, at every level, to an automorphism of
the theta data with this property — in [EtTh] this is Cor. 2.18(i) (`Π_Y̲`, `Π_Ÿ̲` are
characteristic) together with the rigidity of the theta class (Cor. 2.19(iii), Thm. 1.10), Layer B.
-/

namespace Iut.EtaleTheta.Env

open SemidirectProduct
open scoped Envelope

universe u

section Map

variable {PX G μ PX' G' μ' : Type u} [Group PX] [Group G] [CommGroup μ] [Group PX'] [Group G']
  [CommGroup μ'] {aug : PX →* G} {ψ : G →* MulAut μ} {aug' : PX' →* G'} {ψ' : G' →* MulAut μ'}
  (φ : PX ≃* PX') (σ : G ≃* G') (u : μ ≃* μ')
  (haug : ∀ x, aug' (φ x) = σ (aug x)) (hu : ∀ g m, u (ψ g m) = ψ' (σ g) (u m))

include haug hu in
/-- **The induced isomorphism** `Π_X[μ] ≅ Π_X'[μ']`, `(m, x) ↦ (u m, φ x)`. -/
def mapX : EnvX aug ψ ≃* EnvX aug' ψ' where
  toFun x := ⟨u x.left, φ x.right⟩
  invFun y := ⟨u.symm y.left, φ.symm y.right⟩
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp
  map_mul' x y := by
    refine SemidirectProduct.ext ?_ ?_
    · change u ((x * y).left) = u x.left * ψ' (aug' (φ x.right)) (u y.left)
      rw [mul_left, map_mul, haug, ← hu]
      rfl
    · exact map_mul φ x.right y.right

@[simp] lemma mapX_left (x : EnvX aug ψ) : (mapX φ σ u haug hu x).left = u x.left := rfl

@[simp] lemma mapX_right (x : EnvX aug ψ) : (mapX φ σ u haug hu x).right = φ x.right := rfl

@[simp] lemma mapX_symm_left (y : EnvX aug' ψ') :
    ((mapX φ σ u haug hu).symm y).left = u.symm y.left := rfl

@[simp] lemma mapX_symm_right (y : EnvX aug' ψ') :
    ((mapX φ σ u haug hu).symm y).right = φ.symm y.right := rfl

lemma mapX_inl (m : μ) : mapX φ σ u haug hu (inl m) = inl (u m) := by
  ext <;> simp

/-- Transport of Kummer cocycles: `κ ↦ u ∘ κ ∘ σ⁻¹`. -/
def kumMap : (G → μ) →* (G' → μ') where
  toFun κ s := u (κ (σ.symm s))
  map_one' := by funext s; simp
  map_mul' κ κ' := by funext s; simp

include hu in
lemma isCocycle_kumMap {κ : G → μ} (hκ : IsCocycle ψ κ) : IsCocycle ψ' (kumMap σ u κ) := by
  intro s t
  change u (κ (σ.symm (s * t))) = u (κ (σ.symm s)) * ψ' s (u (κ (σ.symm t)))
  rw [map_mul, hκ, map_mul, hu, MulEquiv.apply_symm_apply]

include haug in
lemma aug_symm (y : PX') : aug (φ.symm y) = σ.symm (aug' y) := by
  rw [MulEquiv.eq_symm_apply, ← haug, MulEquiv.apply_symm_apply]

/-- `mapX` carries Kummer twists to Kummer twists. -/
lemma mapX_twist {κ : G → μ} (hκ : IsCocycle ψ κ) (x : EnvX aug ψ) :
    mapX φ σ u haug hu (twist κ hκ x) =
      twist (kumMap σ u κ) (isCocycle_kumMap σ u hu hκ) (mapX φ σ u haug hu x) := by
  refine SemidirectProduct.ext ?_ rfl
  change u (κ (aug x.right) * x.left) = u (κ (σ.symm (aug' (φ x.right)))) * u x.left
  rw [map_mul, haug, MulEquiv.symm_apply_apply]

/-- `mapX` conjugates `twist κ ∘ inn(x)` to `twist (kumMap κ) ∘ inn(mapX x)`. -/
lemma conjAut_mapX_twist_conj {κ : G → μ} (hκ : IsCocycle ψ κ) (x : EnvX aug ψ) :
    MonoThetaEnv.conjAut (mapX φ σ u haug hu) (twist κ hκ * MulAut.conj x) =
      twist (kumMap σ u κ) (isCocycle_kumMap σ u hu hκ) * MulAut.conj (mapX φ σ u haug hu x) := by
  refine MulEquiv.ext fun y => ?_
  rw [MonoThetaEnv.conjAut_apply, MulAut.mul_apply, MulAut.conj_apply, mapX_twist,
    MulAut.mul_apply, MulAut.conj_apply]
  congr 1
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

variable {PY : Subgroup PX} {PY' : Subgroup PX'} (hPY : ∀ x, φ x ∈ PY' ↔ x ∈ PY)

include hPY in
/-- The induced isomorphism `Π_Y[μ] ≅ Π_Y'[μ']`. -/
def mapY : envY aug ψ PY ≃* envY aug' ψ' PY' where
  toFun z := ⟨mapX φ σ u haug hu z, (hPY _).2 z.2⟩
  invFun w := ⟨(mapX φ σ u haug hu).symm w, by
    rw [mem_envY, mapX_symm_right, ← hPY, MulEquiv.apply_symm_apply]
    exact w.2⟩
  left_inv z := Subtype.ext ((mapX φ σ u haug hu).symm_apply_apply z)
  right_inv w := Subtype.ext ((mapX φ σ u haug hu).apply_symm_apply w)
  map_mul' z z' := Subtype.ext (map_mul (mapX φ σ u haug hu) (z : EnvX aug ψ) z')

@[simp] lemma coe_mapY (z : envY aug ψ PY) :
    (mapY φ σ u haug hu hPY z : EnvX aug' ψ') = mapX φ σ u haug hu z := rfl

@[simp] lemma coe_mapY_symm (w : envY aug' ψ' PY') :
    ((mapY φ σ u haug hu hPY).symm w : EnvX aug ψ) = (mapX φ σ u haug hu).symm w := rfl

lemma rightPY_mapY (z : envY aug ψ PY) :
    (rightPY aug' ψ' PY' (mapY φ σ u haug hu hPY z) : PX') = φ (rightPY aug ψ PY z) := rfl

lemma mapY_inlY (m : μ) : mapY φ σ u haug hu hPY (inlY aug ψ PY m) = inlY aug' ψ' PY' (u m) :=
  Subtype.ext (mapX_inl φ σ u haug hu m)

variable (Kum : Subgroup (G → μ)) (hKum : ∀ κ ∈ Kum, IsCocycle ψ κ)
  (Kum' : Subgroup (G' → μ')) (hKum' : ∀ κ ∈ Kum', IsCocycle ψ' κ)
  (hKumMap : Kum.map (kumMap σ u) = Kum')

include hKumMap in
/-- **`mapY` maps `D_Y` onto `D_Y'`.** -/
theorem map_DY :
    (DY aug ψ Kum PY hKum).map (MonoThetaEnv.conjAut (mapY φ σ u haug hu hPY)) =
      DY aug' ψ' Kum' PY' hKum' := by
  have hcoe : ∀ (γ : MulAut (envY aug ψ PY)) (w : envY aug' ψ' PY'),
      (MonoThetaEnv.conjAut (mapY φ σ u haug hu hPY) γ w : EnvX aug' ψ') =
        mapX φ σ u haug hu (γ ((mapY φ σ u haug hu hPY).symm w)) := fun _ _ => rfl
  ext γ'
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨γ, ⟨β, ⟨κ, hκ, x, rfl⟩, hγβ⟩, rfl⟩
    have hκ' : kumMap σ u κ ∈ Kum' := hKumMap ▸ ⟨κ, hκ, rfl⟩
    refine ⟨_, ⟨kumMap σ u κ, hκ', mapX φ σ u haug hu x, rfl⟩, fun w => ?_⟩
    rw [hcoe, hγβ, coe_mapY_symm, ← conjAut_mapX_twist_conj φ σ u haug hu (hKum κ hκ)]
    rfl
  · rintro ⟨β', ⟨κ', hκ', x', rfl⟩, hγβ'⟩
    rw [← hKumMap] at hκ'
    obtain ⟨κ, hκ, rfl⟩ := hκ'
    refine ⟨MonoThetaEnv.conjAut (mapY φ σ u haug hu hPY).symm γ',
      ⟨twist κ (hKum κ hκ) * MulAut.conj ((mapX φ σ u haug hu).symm x'),
        ⟨κ, hκ, _, rfl⟩, fun z => ?_⟩, ?_⟩
    · change (mapX φ σ u haug hu).symm (γ' (mapY φ σ u haug hu hPY z) : EnvX aug' ψ') = _
      rw [hγβ', coe_mapY, MulEquiv.symm_apply_eq]
      have e := DFunLike.congr_fun (conjAut_mapX_twist_conj φ σ u haug hu (hKum κ hκ)
        ((mapX φ σ u haug hu).symm x')) (mapX φ σ u haug hu z)
      rw [MonoThetaEnv.conjAut_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply] at e
      exact e.symm
    · refine MulEquiv.ext fun w => ?_
      simp [MonoThetaEnv.conjAut_apply]

variable {PYdd : Subgroup PX} {PYdd' : Subgroup PX'} (hle : PYdd ≤ PY) (hle' : PYdd' ≤ PY')
  (hPYdd : ∀ x, φ x ∈ PYdd' ↔ x ∈ PYdd)
  {η : PYdd → μ} (hη : IsCocycle (actDD aug ψ PYdd) η)
  {η' : PYdd' → μ'} (hη' : IsCocycle (actDD aug' ψ' PYdd') η')
  (hηφ : ∀ g : PYdd, η' ⟨φ g, (hPYdd _).2 g.2⟩ = u (η g))

include hηφ in
lemma mapY_thetaSection (g : PYdd) :
    mapY φ σ u haug hu hPY (thetaSection aug ψ hle hη g) =
      thetaSection aug' ψ' hle' hη' ⟨φ g, (hPYdd _).2 g.2⟩ := by
  apply Subtype.ext
  refine SemidirectProduct.ext ?_ rfl
  change u (η g)⁻¹ = (η' ⟨φ g, _⟩)⁻¹
  rw [hηφ, map_inv]

include hηφ in
/-- **`mapY` maps datum (c) onto datum (c).** -/
theorem image_thetaSubgroups_mapY :
    Subgroup.map (mapY φ σ u haug hu hPY).toMonoidHom '' thetaSubgroups aug ψ hle hη =
      thetaSubgroups aug' ψ' hle' hη' := by
  have hrange : (thetaSection aug ψ hle hη).range.map (mapY φ σ u haug hu hPY).toMonoidHom =
      (thetaSection aug' ψ' hle' hη').range := by
    ext w
    simp only [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨_, (mapY_thetaSection φ σ u haug hu hPY hle hle' hPYdd hη hη' hηφ g).symm⟩
    · rintro ⟨g', rfl⟩
      let g : PYdd := ⟨φ.symm g', by rw [← hPYdd, MulEquiv.apply_symm_apply]; exact g'.2⟩
      refine ⟨_, ⟨g, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, mapY_thetaSection φ σ u haug hu hPY hle hle' hPYdd hη hη' hηφ g]
      congr 1
      exact Subtype.ext (MulEquiv.apply_symm_apply φ g')
  have key : ∀ ζ : μ, ((thetaSection aug ψ hle hη).range.map
      (MulAut.conj (inlY aug ψ PY ζ)).toMonoidHom).map (mapY φ σ u haug hu hPY).toMonoidHom =
      (thetaSection aug' ψ' hle' hη').range.map
        (MulAut.conj (inlY aug' ψ' PY' (u ζ))).toMonoidHom := by
    intro ζ
    rw [← hrange, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun z => ?_
    simp [MulAut.conj_apply, mapY_inlY]
  ext H
  simp only [Set.mem_image, mem_thetaSubgroups_iff]
  constructor
  · rintro ⟨_, ⟨ζ, rfl⟩, rfl⟩
    exact ⟨u ζ, key ζ⟩
  · rintro ⟨ζ', rfl⟩
    refine ⟨_, ⟨u.symm ζ', rfl⟩, ?_⟩
    rw [key, MulEquiv.apply_symm_apply]

end Map

/-! ### The isomorphism of model environments -/

section MapIso

variable {PX G μ PX' G' μ' : Type u} [Group PX] [Group G] [CommGroup μ] [Group PX'] [Group G']
  [CommGroup μ'] [TopologicalSpace PX] [IsTopologicalGroup PX] [TopologicalSpace μ]
  [DiscreteTopology μ] [TopologicalSpace PX'] [IsTopologicalGroup PX'] [TopologicalSpace μ']
  [DiscreteTopology μ']
  {aug : PX →* G} {ψ : G →* MulAut μ} {aug' : PX' →* G'} {ψ' : G' →* MulAut μ'}
  (φ : PX ≃ₜ* PX') (σ : G ≃* G') (u : μ ≃* μ')
  (haug : ∀ x, aug' (φ x) = σ (aug x)) (hu : ∀ g m, u (ψ g m) = ψ' (σ g) (u m))
  {PY : Subgroup PX} {PY' : Subgroup PX'} (hPY : ∀ x, φ x ∈ PY' ↔ x ∈ PY)
  {Kum : Subgroup (G → μ)} (hKum : ∀ κ ∈ Kum, IsCocycle ψ κ)
  {Kum' : Subgroup (G' → μ')} (hKum' : ∀ κ ∈ Kum', IsCocycle ψ' κ)
  (hKumMap : Kum.map (kumMap σ u) = Kum')
  {PYdd : Subgroup PX} {PYdd' : Subgroup PX'} (hle : PYdd ≤ PY) (hle' : PYdd' ≤ PY')
  (hPYdd : ∀ x, φ x ∈ PYdd' ↔ x ∈ PYdd)
  (hψ : IsOpen ((act aug ψ).ker : Set PX)) (hψ' : IsOpen ((act aug' ψ').ker : Set PX'))
  {η : PYdd → μ} (hη : IsCocycle (actDD aug ψ PYdd) η)
  {η' : PYdd' → μ'} (hη' : IsCocycle (actDD aug' ψ' PYdd') η')
  (hηφ : ∀ g : PYdd, η' ⟨φ g, (hPYdd _).2 g.2⟩ = u (η g))

omit [IsTopologicalGroup PX] [IsTopologicalGroup PX'] [DiscreteTopology μ'] in
lemma continuous_mapY :
    Continuous (mapY φ.toMulEquiv σ u haug hu hPY) := by
  refine Continuous.subtype_mk ?_ _
  refine Envelope.continuous_mk ?_ ?_
  · exact (continuous_of_discreteTopology (f := u)).comp
      (Envelope.continuous_left.comp continuous_subtype_val)
  · exact φ.continuous.comp (Envelope.continuous_right.comp continuous_subtype_val)

omit [IsTopologicalGroup PX] [IsTopologicalGroup PX'] [DiscreteTopology μ] in
lemma continuous_mapY_symm :
    Continuous (mapY φ.toMulEquiv σ u haug hu hPY).symm := by
  refine Continuous.subtype_mk ?_ _
  refine Envelope.continuous_mk ?_ ?_
  · exact (continuous_of_discreteTopology (f := u.symm)).comp
      (Envelope.continuous_left.comp continuous_subtype_val)
  · exact φ.symm.continuous.comp (Envelope.continuous_right.comp continuous_subtype_val)

/-- **The isomorphism of model environments induced by an isomorphism of theta data**
([EtTh], Cor. 2.18(ii): functoriality of the construction). -/
def mapIso :
    MonoThetaEnv.Iso (modelEnv aug ψ Kum hle hψ hKum hη)
      (modelEnv aug' ψ' Kum' hle' hψ' hKum' hη') where
  e := { toMulEquiv := mapY φ.toMulEquiv σ u haug hu hPY
         continuous_toFun := continuous_mapY φ σ u haug hu hPY
         continuous_invFun := continuous_mapY_symm φ σ u haug hu hPY }
  map_D := map_DY φ.toMulEquiv σ u haug hu hPY Kum hKum Kum' hKum' hKumMap
  map_theta := image_thetaSubgroups_mapY φ.toMulEquiv σ u haug hu hPY hle hle' hPYdd hη hη' hηφ

/-- `mapIso` lies over `φ` on `Π_Y`. -/
theorem rightPY_mapIso (z : envY aug ψ PY) :
    (rightPY aug' ψ' PY' ((mapIso φ σ u haug hu hPY hKum hKum' hKumMap hle hle' hPYdd hψ hψ' hη
      hη' hηφ).e z) : PX') = φ (rightPY aug ψ PY z) := rfl

end MapIso

/-! ### Lifting automorphisms of the theta data -/

section Lift

variable {PX G μ : Type u} [Group PX] [Group G] [CommGroup μ] [TopologicalSpace PX]
  [IsTopologicalGroup PX] [TopologicalSpace μ] [DiscreteTopology μ]
  {aug : PX →* G} {ψ : G →* MulAut μ} {Kum : Subgroup (G → μ)}
  {PY PYdd : Subgroup PX} {η : PYdd → μ}
  (φ : PX ≃ₜ* PX) (σ : G ≃* G) (u : μ ≃* μ)
  (haug : ∀ x, aug (φ x) = σ (aug x)) (hu : ∀ g m, u (ψ g m) = ψ (σ g) (u m))
  (hPYdd : ∀ x, φ x ∈ PYdd ↔ x ∈ PYdd)

/-- The pulled-back cocycle `u⁻¹ ∘ η ∘ φ` on `Π_Ÿ`. -/
def pullEta (η : PYdd → μ) (g : PYdd) : μ := u.symm (η ⟨φ g, (hPYdd _).2 g.2⟩)

omit [IsTopologicalGroup PX] [TopologicalSpace μ] [DiscreteTopology μ] in
include haug hu in
lemma isCocycle_pullEta (hη : IsCocycle (actDD aug ψ PYdd) η) :
    IsCocycle (actDD aug ψ PYdd) (pullEta φ u hPYdd η) := by
  intro g h
  have e := hη ⟨φ g, (hPYdd _).2 g.2⟩ ⟨φ h, (hPYdd _).2 h.2⟩
  have hgh : (⟨φ ((g * h : PYdd) : PX), (hPYdd _).2 (g * h).2⟩ : PYdd) =
      ⟨φ g, (hPYdd _).2 g.2⟩ * ⟨φ h, (hPYdd _).2 h.2⟩ :=
    Subtype.ext (map_mul φ (g : PX) h)
  change u.symm (η ⟨φ ((g * h : PYdd) : PX), _⟩) =
    u.symm (η ⟨φ g, _⟩) * ψ (aug g) (u.symm (η ⟨φ h, _⟩))
  rw [hgh, e, map_mul]
  congr 1
  change u.symm (ψ (aug (φ g)) _) = ψ (aug g) (u.symm _)
  rw [MulEquiv.symm_apply_eq, hu, MulEquiv.apply_symm_apply, haug]

variable [Finite μ] [PY.Normal] (hKum : ∀ κ ∈ Kum, IsCocycle ψ κ)
  (hKc : ∀ κ ∈ Kum, Continuous fun g : PX => κ (aug g))
  (hle : PYdd ≤ PY) (hψ : IsOpen ((act aug ψ).ker : Set PX))
  (hη : IsCocycle (actDD aug ψ PYdd) η) (hPYfi : Envelope.FISlim PY)
  (hPY : ∀ x, φ x ∈ PY ↔ x ∈ PY) (hKumMap : Kum.map (kumMap σ u) = Kum)

include haug hu hKc hPY hKumMap in
/-- **Lifting automorphisms of the theta data** ([EtTh], proof of Cor. 2.18(iv), surjectivity):
an automorphism `(φ, σ, u)` of the theta data preserving `Π_Y`, `Π_Ÿ` and the Kummer cocycles,
which maps the class of `η` to the class of `η · κ · δ⁻¹` for a Kummer cocycle `κ` and an
admissible shift cocycle `δ` (the hypotheses of `shiftIso`), is induced on `Π_Y` by an
automorphism of the model environment. -/
theorem exists_aut_autPY_eq {κ : G → μ} (hκ : κ ∈ Kum) {δY : PY → μ}
    (hδY : IsCocycle (actY aug ψ PY) δY) (hδc : Continuous δY) (hconj : ShiftConj aug ψ Kum δY)
    (hcoh : Cohomologous (actDD aug ψ PYdd)
      (fun g => η g * κ (aug g) * (resDD hle δY g)⁻¹) (pullEta φ u hPYdd η)) :
    ∃ a : CategoryTheory.Aut (modelEnv aug ψ Kum hle hψ hKum hη),
      ∀ h : PY, (autPY aug ψ Kum hle hψ hKum hη hPYfi a h : PX) = φ h := by
  -- the chain `η → η·κ → η·κ·δ⁻¹ ~ pullEta → η`
  let hηκ := isCocycle_mul_kummer hη (hKum κ hκ)
  let k := kummerIso aug ψ Kum hle hψ hKum hKc hη (Kum.inv_mem (Kum.inv_mem hκ))
  have hηκ' : IsCocycle (actDD aug ψ PYdd) (fun g => η g * κ⁻¹⁻¹ (aug g)) := by
    simpa only [inv_inv] using hηκ
  let s := shiftIso aug ψ Kum hle hψ hKum hδY hδc hconj hηκ'
  have hpull := isCocycle_pullEta φ σ u haug hu hPYdd hη
  have hθ : thetaSubgroups aug ψ hle (isCocycle_mul_inv_resDD aug ψ hδY hle hηκ') =
      thetaSubgroups aug ψ hle hpull := by
    refine (thetaSubgroups_eq_iff aug ψ hle _ _).2 ?_
    simpa only [inv_inv] using hcoh
  let c : MonoThetaEnv.Iso
      (modelEnv aug ψ Kum hle hψ hKum (isCocycle_mul_inv_resDD aug ψ hδY hle hηκ'))
      (modelEnv aug ψ Kum hle hψ hKum hpull) :=
    isoOfMemDY aug ψ Kum hle hψ hKum _ hpull (ContinuousMulEquiv.refl _)
      (DY aug ψ Kum PY hKum).one_mem (by
        rw [← hθ]
        have hmapid : ∀ K : Subgroup (envY aug ψ PY),
            Subgroup.map (ContinuousMulEquiv.refl (envY aug ψ PY)).toMulEquiv.toMonoidHom K = K :=
          fun K => Subgroup.ext fun y => ⟨fun ⟨z, hz, e⟩ => e ▸ hz, fun hy => ⟨y, hy, rfl⟩⟩
        simp only [hmapid, Set.image_id'])
  let m := mapIso φ σ u haug hu hPY hKum hKum hKumMap hle hle hPYdd hψ hψ hpull hη
    (fun g => (MulEquiv.apply_symm_apply u _).symm)
  refine ⟨(k.trans (s.trans (c.trans m))).toCatIso, fun h => ?_⟩
  rw [autPY_apply, indPY_apply]
  change (rightPY aug ψ PY (m.e (c.e (s.e (k.e (salg aug ψ PY h))))) : PX) = φ h
  rw [rightPY_mapIso]
  rfl

/-- The restriction of `φ` to an automorphism of `Π_Y`. -/
def restrictPY : MulAut PY where
  toFun h := ⟨φ h, (hPY _).2 h.2⟩
  invFun h := ⟨φ.symm h, by rw [← hPY, ContinuousMulEquiv.apply_symm_apply]; exact h.2⟩
  left_inv h := Subtype.ext (φ.symm_apply_apply h)
  right_inv h := Subtype.ext (φ.apply_symm_apply h)
  map_mul' h h' := Subtype.ext (map_mul φ (h : PX) h')

include haug hu hKc hKumMap in
/-- **`φ|_{Π_Y}` lies in the image of `Aut(modelEnv) → Aut(Π_Y)`** under the hypotheses of
`exists_aut_autPY_eq`; this is the form in which the hypothesis `hlift` of
`discreteRigidity_env` is discharged levelwise. -/
theorem restrictPY_mem_range {κ : G → μ} (hκ : κ ∈ Kum) {δY : PY → μ}
    (hδY : IsCocycle (actY aug ψ PY) δY) (hδc : Continuous δY) (hconj : ShiftConj aug ψ Kum δY)
    (hcoh : Cohomologous (actDD aug ψ PYdd)
      (fun g => η g * κ (aug g) * (resDD hle δY g)⁻¹) (pullEta φ u hPYdd η)) :
    restrictPY φ hPY ∈ (autPY aug ψ Kum hle hψ hKum hη hPYfi).range := by
  obtain ⟨a, ha⟩ := exists_aut_autPY_eq φ σ u haug hu hPYdd hKum hKc hle hψ hη hPYfi hPY hKumMap
    hκ hδY hδc hconj hcoh
  exact ⟨a, MulEquiv.ext fun h => Subtype.ext (ha h)⟩

end Lift

end Iut.EtaleTheta.Env
