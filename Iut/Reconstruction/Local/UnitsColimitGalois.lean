/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.UnitsColimit
import Iut.Reconstruction.Local.LogShellGalois
import Iut.Reconstruction.Local.AbelianZHat
import LocalClassFieldTheory.Brauer.ArtinTransfer
import LocalClassFieldTheory.Reciprocity.ArtinNaturality

/-!
# `𝒪^×_{k̄}(G_k)` is `𝒪^×_{k̄}` (roadmap MR11)

For `G = G_k = Gal(Ω/k)` we compare the group-theoretic `unitsBar G` (`UnitsColimit.lean`, the
colimit of the images of inertia in `U^ab` along the transfer) with the units `𝒪^×_Ω`
(`unitsΩ`, `LogShellGalois.lean`):

* for an open `U ⊆ G` with fixed field `E_U` (`fld`), `U ≃ₜ* Gal(Ω/E_U)` (`galEquiv`) and local
  class field theory identify `abUnits U` with `𝒪^×_{E_U}` (`unitsMap U`);
* **`mem_abUnits_verAb`, `unitsMap_verAb`** (*compatibility with inertia*): the transfer
  `Ver : U^ab → V^ab` maps `abUnits U` into `abUnits V`, and corresponds to the inclusion
  `𝒪^×_{E_U} ⊆ 𝒪^×_{E_V}` — this is the transfer property of the Artin map
  (`PadicField.artin_transfer`, [AbsTopIII], Proposition 5.8 (i));
* **`unitsBarEquiv : unitsBar G_k ≃* 𝒪^×_Ω`**, which is **`G_k`-equivariant**
  (`unitsBarEquiv_barConj`, from the Galois naturality of the Artin map
  `PadicField.artin_naturality`).
-/

namespace Iut.Reconstruction

open PadicField IntermediateField MonoidHom

set_option linter.unusedSectionVars false

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type*} [Field k] [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]
variable {Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

/-- The fixed field `E_U` of an open subgroup `U ⊆ G_k`. -/
def fld (i : OpenIdx (Ω ≃ₐ[k] Ω)) : IntermediateField k Ω := fixedField (sg i)

theorem isClosed_sg (i : OpenIdx (Ω ≃ₐ[k] Ω)) : IsClosed (sg i : Set (Ω ≃ₐ[k] Ω)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_sg i)

theorem fixingSubgroup_fld (i : OpenIdx (Ω ≃ₐ[k] Ω)) : (fld i).fixingSubgroup = sg i :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨sg i, isClosed_sg i⟩

instance finiteDimensional_fld (i : OpenIdx (Ω ≃ₐ[k] Ω)) : FiniteDimensional k (fld i) :=
  (InfiniteGalois.isOpen_iff_finite _).1 (by
    change IsOpen ((fld i).fixingSubgroup : Set (Ω ≃ₐ[k] Ω))
    rw [fixingSubgroup_fld]
    exact isOpen_sg i)

instance finiteDimensional_fld' (i : OpenIdx (Ω ≃ₐ[k] Ω)) : FiniteDimensional ℚ_[p] (fld i) :=
  Module.Finite.trans k (fld i)

instance isGalois_fld (i : OpenIdx (Ω ≃ₐ[k] Ω)) : IsGalois (fld i) Ω :=
  IsGalois.tower_top_of_isGalois k (fld i) Ω

/-- A topological isomorphism between equal subgroups. -/
def subgroupCongrCont {X : Type*} [Group X] [TopologicalSpace X] {A B : Subgroup X}
    (h : A = B) : A ≃ₜ* B :=
  { toMulEquiv := MulEquiv.subgroupCongr h
    continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
    continuous_invFun := Continuous.subtype_mk continuous_subtype_val _ }

/-- **`U ≃ₜ* Gal(Ω/E_U)`.** -/
def galEquiv (i : OpenIdx (Ω ≃ₐ[k] Ω)) : sg i ≃ₜ* (Ω ≃ₐ[fld i] Ω) :=
  (subgroupCongrCont (fixingSubgroup_fld i).symm).trans (fixingSubgroupContEquiv (fld i))

theorem galEquiv_apply (i : OpenIdx (Ω ≃ₐ[k] Ω)) (u : sg i) (x : Ω) :
    galEquiv i u x = (u : Ω ≃ₐ[k] Ω) x := rfl

variable (p) in
/-- **`abUnits U ≃ 𝒪^×_{E_U} → 𝒪^×_Ω`** (local class field theory for `E_U`). -/
def unitsMap (i : OpenIdx (Ω ≃ₐ[k] Ω)) : abUnits (sg i) →* unitsΩ p Ω :=
  (unitsΩOf (IsScalarTower.toAlgHom ℚ_[p] (fld i) Ω)).comp
    ((unitsAbEquiv p (fld i) Ω).symm.toMonoidHom.comp (abUnitsEquiv (galEquiv i)).toMonoidHom)

theorem unitsMap_injective (i : OpenIdx (Ω ≃ₐ[k] Ω)) : Function.Injective (unitsMap p i) := by
  intro x y h
  apply (abUnitsEquiv (galEquiv i)).injective
  apply (unitsAbEquiv p (fld i) Ω).symm.injective
  apply Subtype.ext
  apply Units.ext
  have := congrArg (fun z : unitsΩ p Ω => ((z : Ωˣ) : Ω)) h
  exact Subtype.ext this

theorem fld_mono {i j : OpenIdx (Ω ≃ₐ[k] Ω)} (h : i ≤ j) : fld i ≤ fld j := by
  intro x hx
  rw [fld, IntermediateField.mem_fixedField_iff] at hx ⊢
  exact fun σ hσ => hx σ (sg_le h hσ)

theorem coe_abUnitsEquiv {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] (ψ : G ≃ₜ* G') (u : abUnits G) :
    ((abUnitsEquiv ψ u : abUnits G') : TopologicalAbelianization G') = abEquiv ψ u := rfl

set_option maxHeartbeats 2000000 in
-- unifying `Gal(Ω/E_V)` with `Gal(Ω/F)` for `F = extendScalars` (definitionally equal) is slow
/-- **Compatibility of the transfer with inertia** ([AbsTopIII], Proposition 5.8 (i)): for open
`V ⊆ U` the transfer `U^ab → V^ab` maps `𝒪^×(U)` into `𝒪^×(V)`, compatibly with the inclusion
`𝒪^×_{E_U} ⊆ 𝒪^×_{E_V}` — from the transfer property of the Artin map. -/
theorem verAb_units {i j : OpenIdx (Ω ≃ₐ[k] Ω)} (h : i ≤ j) (u : abUnits (sg i)) :
    ∃ hu : verAb (sg_le h) (isOpen_sg j) (u : TopologicalAbelianization (sg i)) ∈ abUnits (sg j),
      unitsMap p j ⟨_, hu⟩ = unitsMap p i u := by
  obtain ⟨g0, hg0⟩ := QuotientGroup.mk'_surjective _ (u : TopologicalAbelianization (sg i))
  set F : IntermediateField (fld i) Ω := extendScalars (fld_mono h)
  haveI : Module.Finite k F := (inferInstance : FiniteDimensional k (fld j))
  haveI : FiniteDimensional (fld i) F := Module.Finite.of_restrictScalars_finite k (fld i) F
  set a : unitGroup p (fld i) := (unitsAbEquiv p (fld i) Ω).symm (abUnitsEquiv (galEquiv i) u)
  -- `g = galEquiv i g0` lifts `artin(a)`
  have hg : AlgEquiv.restrictNormalHom (maxAbelian (fld i) Ω) (galEquiv i g0) =
      artin p (fld i) Ω (a : (fld i)ˣ) := by
    rw [← galAbEquiv_unitsAbEquiv, MulEquiv.apply_symm_apply, coe_abUnitsEquiv, ← hg0]
    rfl
  have hT := artin_transfer (p := p) F (a : (fld i)ˣ) (galEquiv i g0) hg
  -- `Ver` on Galois groups is `verAb`
  set e : sg i ≃* (Ω ≃ₐ[fld i] Ω) := (galEquiv i).toMulEquiv
  have hmap : ((sg j).subgroupOf (sg i)).map e.toMonoidHom = F.fixingSubgroup := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← fixingSubgroup_fld j] at hy
      intro z
      exact hy ⟨z, z.2⟩
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      rw [← fixingSubgroup_fld j]
      intro z
      have := hx ⟨z, z.2⟩
      change e (e.symm x) z = z at this
      exact this
  letI := galAbCommGroup p F Ω
  have hver : ver p F (galEquiv i g0) =
      galAbEquiv p F Ω (abEquiv (galEquiv j) (verAb (sg_le h) (isOpen_sg j) (abMk _ g0))) := by
    rw [verAb_mk, ver]
    change ((AlgEquiv.restrictNormalHom (maxAbelian F Ω)).comp
      (fixingSubgroupEquiv F).toMonoidHom).transfer (e g0) = _
    rw [MonoidHom.transfer_map_equiv e hmap]
    set f : TopologicalAbelianization (sg j) →* (maxAbelian F Ω ≃ₐ[F] maxAbelian F Ω) :=
      (galAbEquiv p F Ω).toMulEquiv.toMonoidHom.comp (abEquiv (galEquiv j)).toMonoidHom
    rw [show galAbEquiv p F Ω (abEquiv (galEquiv j) ((abMkOf (sg_le h)).transfer g0)) =
      f ((abMkOf (sg_le h)).transfer g0) from rfl, ← transfer_comp_hom]
    congr 1
  -- the image of `a` in `𝒪_F^×`
  set a' : unitGroup p F := ⟨Units.map (algebraMap (fld i) F : fld i →* F) (a : (fld i)ˣ), by
    rw [mem_unitGroup, Units.coe_map]
    change nrm p F (algebraMap (fld i) F _) = 1
    rw [nrm_algebraMap_tower]
    exact a.2⟩
  have h3 : abEquiv (galEquiv j) (verAb (sg_le h) (isOpen_sg j) (abMk _ g0)) =
      (show TopologicalAbelianization (Ω ≃ₐ[fld j] Ω) from
        Subtype.val (unitsAbEquiv p F Ω a')) := by
    apply (galAbEquiv p F Ω).injective
    rw [galAbEquiv_unitsAbEquiv, ← hver, ← hT]
  have hu : verAb (sg_le h) (isOpen_sg j) (u : TopologicalAbelianization (sg i)) ∈
      abUnits (sg j) := by
    rw [← hg0, ← abEquiv_mem_abUnits_iff (galEquiv j)]
    change abEquiv (galEquiv j) (verAb (sg_le h) (isOpen_sg j) (abMk _ g0)) ∈ _
    rw [h3]
    exact (unitsAbEquiv p F Ω a').2
  refine ⟨hu, ?_⟩
  have h4 : abUnitsEquiv (galEquiv j) ⟨_, hu⟩ = unitsAbEquiv p F Ω a' := by
    apply Subtype.ext
    rw [coe_abUnitsEquiv]
    change abEquiv (galEquiv j) (verAb (sg_le h) (isOpen_sg j)
      (u : TopologicalAbelianization (sg i))) = _
    rw [← hg0]
    exact h3
  apply Subtype.ext
  apply Units.ext
  change (((((unitsAbEquiv p (fld j) Ω).symm (abUnitsEquiv (galEquiv j) ⟨_, hu⟩) :
    unitGroup p (fld j)) : (fld j)ˣ) : fld j) : Ω) = (((a : (fld i)ˣ) : fld i) : Ω)
  rw [h4]
  change (((((unitsAbEquiv p F Ω).symm (unitsAbEquiv p F Ω a') : unitGroup p F) : Fˣ) : F) :
    Ω) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

variable (k Ω) in
/-- The group `G_k`. -/
abbrev GalK : Type _ := Ω ≃ₐ[k] Ω

include hp in
theorem abTrans_mem_abUnits {i j : OpenIdx (Ω ≃ₐ[k] Ω)} (h : i ≤ j) {x : AbFam _ i}
    (hx : x ∈ abUnits (sg i)) : abTrans _ i j h x ∈ abUnits (sg j) :=
  (verAb_units (p := p) h ⟨x, hx⟩).1

include hp in
theorem unitsMap_abTrans {i j : OpenIdx (Ω ≃ₐ[k] Ω)} (h : i ≤ j) (x : abUnits (sg i)) :
    unitsMap p j ⟨abTrans _ i j h x, abTrans_mem_abUnits (p := p) h x.2⟩ = unitsMap p i x :=
  (verAb_units (p := p) h x).2

include hp in
/-- **For `G_k`, `𝒪^×_{k̄}(G_k)` is the union of the images of the `𝒪^×(U)`.** -/
theorem mem_unitsBar_iff (z : AbBar (Ω ≃ₐ[k] Ω)) :
    z ∈ unitsBar (Ω ≃ₐ[k] Ω) ↔
      ∃ i, ∃ x ∈ abUnits (sg i), z = toBar (Ω ≃ₐ[k] Ω) i x := by
  constructor
  · intro hz
    refine Subgroup.iSup_induction (C := fun z => ∃ i, ∃ x ∈ abUnits (sg i),
      z = toBar (Ω ≃ₐ[k] Ω) i x) _ hz ?_ ?_ ?_
    · rintro i _ ⟨x, hx, rfl⟩
      exact ⟨i, x, hx, rfl⟩
    · obtain ⟨i⟩ := (inferInstance : Nonempty (OpenIdx (Ω ≃ₐ[k] Ω)))
      exact ⟨i, 1, Subgroup.one_mem _, (map_one _).symm⟩
    · rintro _ _ ⟨i, x, hx, rfl⟩ ⟨j, y, hy, rfl⟩
      obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
      refine ⟨l, abTrans _ i l hil x * abTrans _ j l hjl y,
        Subgroup.mul_mem _ (abTrans_mem_abUnits (p := p) hil hx)
          (abTrans_mem_abUnits (p := p) hjl hy), ?_⟩
      rw [map_mul, toBar_abTrans, toBar_abTrans]
  · rintro ⟨i, x, hx, rfl⟩
    exact Subgroup.mem_iSup_of_mem i ⟨x, hx, rfl⟩

include hp in
theorem unitsMap_eq_of_toBar_eq {i j : OpenIdx (Ω ≃ₐ[k] Ω)} (x : abUnits (sg i))
    (y : abUnits (sg j)) (hxy : toBar _ i (x : AbFam _ i) = toBar _ j (y : AbFam _ j)) :
    unitsMap p i x = unitsMap p j y := by
  obtain ⟨l, hil, hjl, hl⟩ := Quotient.exact hxy
  rw [← unitsMap_abTrans (p := p) hil x, ← unitsMap_abTrans (p := p) hjl y]
  congr 1
  exact Subtype.ext hl

variable (p) in
/-- The map `𝒪^×_{k̄}(G_k) → 𝒪^×_Ω`. -/
def unitsBarFun (z : unitsBar (Ω ≃ₐ[k] Ω)) : unitsΩ p Ω :=
  have h := (mem_unitsBar_iff (p := p) z.1).1 z.2
  unitsMap p h.choose ⟨h.choose_spec.choose, h.choose_spec.choose_spec.1⟩

theorem unitsBarFun_eq (z : unitsBar (Ω ≃ₐ[k] Ω)) (i : OpenIdx (Ω ≃ₐ[k] Ω))
    (x : abUnits (sg i)) (hz : (z : AbBar _) = toBar _ i (x : AbFam _ i)) :
    unitsBarFun p z = unitsMap p i x := by
  have h := (mem_unitsBar_iff (p := p) z.1).1 z.2
  exact unitsMap_eq_of_toBar_eq _ _ (h.choose_spec.choose_spec.2.symm.trans hz)

variable (p) in
/-- The homomorphism `𝒪^×_{k̄}(G_k) → 𝒪^×_Ω`. -/
def unitsBarHom : unitsBar (Ω ≃ₐ[k] Ω) →* unitsΩ p Ω where
  toFun := unitsBarFun p
  map_one' := by
    obtain ⟨i⟩ := (inferInstance : Nonempty (OpenIdx (Ω ≃ₐ[k] Ω)))
    rw [unitsBarFun_eq 1 i 1 (by simp), map_one]
  map_mul' z w := by
    obtain ⟨i, x, hx, hz⟩ := (mem_unitsBar_iff (p := p) z.1).1 z.2
    obtain ⟨j, y, hy, hw⟩ := (mem_unitsBar_iff (p := p) w.1).1 w.2
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
    have hx' := abTrans_mem_abUnits (p := p) hil hx
    have hy' := abTrans_mem_abUnits (p := p) hjl hy
    rw [unitsBarFun_eq z l ⟨_, hx'⟩ (by rw [hz]; exact (toBar_abTrans _ hil x).symm),
      unitsBarFun_eq w l ⟨_, hy'⟩ (by rw [hw]; exact (toBar_abTrans _ hjl y).symm),
      unitsBarFun_eq (z * w) l (⟨_, hx'⟩ * ⟨_, hy'⟩) (by
        change (z : AbBar (Ω ≃ₐ[k] Ω)) * (w : AbBar (Ω ≃ₐ[k] Ω)) = _
        rw [hz, hw, ← toBar_abTrans _ hil x, ← toBar_abTrans _ hjl y, ← map_mul]
        rfl), map_mul]

theorem unitsBarHom_toBar (i : OpenIdx (Ω ≃ₐ[k] Ω)) (x : abUnits (sg i)) :
    unitsBarHom p ⟨toBar _ i (x : AbFam _ i),
      (mem_unitsBar_iff (p := p) _).2 ⟨i, x, x.2, rfl⟩⟩ = unitsMap p i x :=
  unitsBarFun_eq _ i x rfl

theorem unitsBarHom_injective : Function.Injective (unitsBarHom (k := k) (Ω := Ω) p) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨i, x, hx, hzx⟩ := (mem_unitsBar_iff (p := p) z.1).1 z.2
  have h1 : unitsMap p i ⟨x, hx⟩ = unitsMap p i 1 := by
    rw [map_one, ← hz]
    exact (unitsBarFun_eq z i ⟨x, hx⟩ hzx).symm
  have h2 := unitsMap_injective i h1
  apply Subtype.ext
  rw [hzx]
  have : x = 1 := congrArg Subtype.val h2
  rw [this, map_one]
  rfl

theorem unitsBarHom_surjective : Function.Surjective (unitsBarHom (k := k) (Ω := Ω) p) := by
  intro u
  set E : IntermediateField k Ω := k⟮((u : Ωˣ) : Ω)⟯
  haveI : FiniteDimensional k E :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ((u : Ωˣ) : Ω))
  set i : OpenIdx (Ω ≃ₐ[k] Ω) := OrderDual.toDual ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩
  have hfi : fld i = E := InfiniteGalois.fixedField_fixingSubgroup E
  have hu : ((u : Ωˣ) : Ω) ∈ fld i := by rw [hfi]; exact mem_adjoin_simple_self k _
  set a : unitGroup p (fld i) := ⟨Units.mk0 ⟨_, hu⟩ fun h0 => (u : Ωˣ).ne_zero
      (congrArg Subtype.val h0), by
    rw [mem_unitGroup]
    change nrm p (fld i) ⟨_, hu⟩ = 1
    rw [← nrm_map (IsScalarTower.toAlgHom ℚ_[p] (fld i) Ω)]
    exact u.2⟩
  set x : abUnits (sg i) := (abUnitsEquiv (galEquiv i)).symm (unitsAbEquiv p (fld i) Ω a)
  refine ⟨_, (unitsBarHom_toBar i x).trans ?_⟩
  apply Subtype.ext
  apply Units.ext
  change (((((unitsAbEquiv p (fld i) Ω).symm (abUnitsEquiv (galEquiv i) x) :
    unitGroup p (fld i)) : (fld i)ˣ) : fld i) : Ω) = ((u : Ωˣ) : Ω)
  rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  rfl

variable (p k Ω) in
/-- **`𝒪^×_{k̄}(G_k) ≃ 𝒪^×_{k̄}`**: the units constructed from `G_k` alone (colimit along the
transfer of the images of inertia, [AbsTopIII], Proposition 5.8 (i), (ii)) are the units of
`Ω`. -/
def unitsBarEquiv : unitsBar (Ω ≃ₐ[k] Ω) ≃* unitsΩ p Ω :=
  MulEquiv.ofBijective (unitsBarHom p) ⟨unitsBarHom_injective, unitsBarHom_surjective⟩

theorem unitsBarEquiv_toBar (i : OpenIdx (Ω ≃ₐ[k] Ω)) (x : abUnits (sg i)) :
    unitsBarEquiv p k Ω ⟨toBar _ i (x : AbFam _ i),
      (mem_unitsBar_iff (p := p) _).2 ⟨i, x, x.2, rfl⟩⟩ = unitsMap p i x :=
  unitsBarHom_toBar i x

/-! ### `G_k`-equivariance -/

section Equivariance

variable (σ : Ω ≃ₐ[k] Ω) (i : OpenIdx (Ω ≃ₐ[k] Ω))

theorem mem_sg_conj_iff (g : Ω ≃ₐ[k] Ω) :
    g ∈ sg (idxMap (conjCont σ) i) ↔ σ⁻¹ * g * σ ∈ sg i := by
  rw [sg_idxMap, Subgroup.mem_comap]
  have : (conjCont σ).symm g = σ⁻¹ * g * σ := by
    rw [ContinuousMulEquiv.symm_apply_eq]
    simp [conjCont_apply, mul_assoc]
  change (conjCont σ).symm g ∈ sg i ↔ _
  rw [this]

theorem map_mem_fld_conj {x : Ω} (hx : x ∈ fld i) : σ x ∈ fld (idxMap (conjCont σ) i) := by
  rw [fld, IntermediateField.mem_fixedField_iff] at hx ⊢
  intro g hg
  have h := hx _ ((mem_sg_conj_iff σ i g).1 hg)
  have h2 : σ.symm (g (σ x)) = x := h
  calc g (σ x) = σ (σ.symm (g (σ x))) := (σ.apply_symm_apply _).symm
    _ = σ x := by rw [h2]

theorem symm_mem_fld_conj {y : Ω} (hy : y ∈ fld (idxMap (conjCont σ) i)) :
    σ.symm y ∈ fld i := by
  rw [fld, IntermediateField.mem_fixedField_iff] at hy ⊢
  intro g hg
  have hg' : σ * g * σ⁻¹ ∈ sg (idxMap (conjCont σ) i) := by
    rw [mem_sg_conj_iff]
    simpa [mul_assoc] using hg
  have h := hy _ hg'
  change σ (g (σ⁻¹ y)) = y at h
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply]
  exact h

/-- `σ : E_U ≃ E_{σUσ⁻¹}`. -/
def fldConj : fld i ≃ₐ[ℚ_[p]] fld (idxMap (conjCont σ) i) where
  toFun x := ⟨σ x, map_mem_fld_conj σ i x.2⟩
  invFun y := ⟨σ.symm y, symm_mem_fld_conj σ i y.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply (x : Ω))
  right_inv y := Subtype.ext (σ.apply_symm_apply (y : Ω))
  map_mul' x y := Subtype.ext (map_mul σ (x : Ω) y)
  map_add' x y := Subtype.ext (map_add σ (x : Ω) y)
  commutes' c := Subtype.ext ((σ.restrictScalars ℚ_[p]).commutes c)

theorem fldConj_compat (c : fld i) :
    σ.toRingEquiv (algebraMap (fld i) Ω c) =
      algebraMap (fld (idxMap (conjCont σ) i)) Ω (fldConj (p := p) σ i c) := rfl

/-- **`G_k`-equivariance on generators**: conjugation by `σ` on `𝒪^×(U)` corresponds to `σ` on
`𝒪^×_{E_U} → 𝒪^×_{E_{σUσ⁻¹}}` (the Galois naturality of the Artin map,
`PadicField.artin_naturality`). -/
theorem unitsMap_conj (x : abUnits (sg i)) :
    ((unitsMap p (idxMap (conjCont σ) i)
        ⟨abFamEquiv (conjCont σ) i x, (abEquiv_mem_abUnits_iff _ _).2 x.2⟩ : Ωˣ) : Ω) =
      σ ((unitsMap p i x : Ωˣ) : Ω) := by
  set j := idxMap (conjCont σ) i
  set τ := fldConj (p := p) σ i
  obtain ⟨g0, hg0⟩ := QuotientGroup.mk'_surjective _ (x : TopologicalAbelianization (sg i))
  set a : unitGroup p (fld i) := (unitsAbEquiv p (fld i) Ω).symm (abUnitsEquiv (galEquiv i) x)
  have hg : AlgEquiv.restrictNormalHom (maxAbelian (fld i) Ω) (galEquiv i g0) =
      artin p (fld i) Ω (a : (fld i)ˣ) := by
    rw [← galAbEquiv_unitsAbEquiv, MulEquiv.apply_symm_apply, coe_abUnitsEquiv, ← hg0]
    rfl
  -- the conjugate unit in `𝒪_{E_j}`
  set b : unitGroup p (fld j) := ⟨Units.map (τ : fld i →* fld j) (a : (fld i)ˣ), by
    rw [mem_unitGroup, Units.coe_map]
    change nrm p (fld j) (τ _) = 1
    rw [nrm_algEquiv']
    exact a.2⟩
  set x' : abUnits (sg j) := ⟨abFamEquiv (conjCont σ) i x, (abEquiv_mem_abUnits_iff _ _).2 x.2⟩
  have hx' : abUnitsEquiv (galEquiv j) x' = unitsAbEquiv p (fld j) Ω b := by
    apply Subtype.ext
    apply (galAbEquiv p (fld j) Ω).injective
    rw [galAbEquiv_unitsAbEquiv, coe_abUnitsEquiv]
    change galAbEquiv p (fld j) Ω (abEquiv (galEquiv j) (abFamEquiv (conjCont σ) i
      (x : TopologicalAbelianization (sg i)))) = _
    rw [← hg0]
    change galAbEquiv p (fld j) Ω (abEquiv (galEquiv j)
      (QuotientGroup.mk (sgEquiv (conjCont σ) i g0))) = _
    rw [abEquiv_mk, galAbEquiv_mk]
    ext y'
    obtain ⟨y, rfl⟩ := (maxAbelianRingEquiv τ σ.toRingEquiv (fldConj_compat σ i)).surjective y'
    have hN := artin_naturality τ σ.toRingEquiv (fldConj_compat σ i) (a : (fld i)ˣ) y
    change _ = (artin p (fld j) Ω (Units.map (τ : fld i →* fld j) (a : (fld i)ˣ))
      (maxAbelianRingEquiv τ σ.toRingEquiv (fldConj_compat σ i) y) : Ω)
    rw [hN, ← hg]
    have hc := AlgEquiv.restrictNormal_commutes (galEquiv i g0) (maxAbelian (fld i) Ω) y
    change _ = σ (algebraMap (maxAbelian (fld i) Ω) Ω ((galEquiv i g0).restrictNormal _ y))
    rw [hc]
    have hc' := AlgEquiv.restrictNormal_commutes (galEquiv j (sgEquiv (conjCont σ) i g0))
      (maxAbelian (fld j) Ω) (maxAbelianRingEquiv τ σ.toRingEquiv (fldConj_compat σ i) y)
    change algebraMap (maxAbelian (fld j) Ω) Ω
      ((galEquiv j (sgEquiv (conjCont σ) i g0)).restrictNormal _
        (maxAbelianRingEquiv τ σ.toRingEquiv (fldConj_compat σ i) y)) = _
    rw [hc']
    change (galEquiv j (sgEquiv (conjCont σ) i g0)) (σ (y : Ω)) = σ (galEquiv i g0 (y : Ω))
    rw [galEquiv_apply, galEquiv_apply, coe_sgEquiv, conjCont_apply]
    change σ ((g0 : Ω ≃ₐ[k] Ω) (σ⁻¹ (σ (y : Ω)))) = _
    rw [show σ⁻¹ (σ (y : Ω)) = (y : Ω) from σ.symm_apply_apply _]
  change (((((unitsAbEquiv p (fld j) Ω).symm (abUnitsEquiv (galEquiv j) x')) :
    unitGroup p (fld j)) : (fld j)ˣ) : fld j) = σ ((((a : unitGroup p (fld i)) : (fld i)ˣ) :
      fld i) : Ω)
  rw [hx', MulEquiv.symm_apply_apply]
  rfl

/-- **`unitsBarEquiv` is `G_k`-equivariant**: the action `barConj σ` of `σ ∈ G_k` on the
group-theoretic `𝒪^×_{k̄}(G_k)` corresponds to the Galois action of `σ` on `𝒪^×_Ω`. -/
theorem unitsBarEquiv_barConj (z : unitsBar (Ω ≃ₐ[k] Ω)) :
    unitsBarEquiv p k Ω ⟨barConj _ σ z, (map_barConj_unitsBar σ).le ⟨z, z.2, rfl⟩⟩ =
      unitsΩMap (σ.restrictScalars ℚ_[p]).toAlgHom (unitsBarEquiv p k Ω z) := by
  obtain ⟨i, x, hx, hz⟩ := (mem_unitsBar_iff (p := p) z.1).1 z.2
  have hz' : z = ⟨toBar _ i x, (mem_unitsBar_iff (p := p) _).2 ⟨i, x, hx, rfl⟩⟩ := Subtype.ext hz
  subst hz'
  have h1 : barConj _ σ (toBar (Ω ≃ₐ[k] Ω) i x) =
      toBar _ (idxMap (conjCont σ) i) (abFamEquiv (conjCont σ) i x) := rfl
  apply Subtype.ext
  apply Units.ext
  have e1 := unitsBarEquiv_toBar (p := p) i ⟨x, hx⟩
  have e2 := unitsBarEquiv_toBar (p := p) (idxMap (conjCont σ) i)
    ⟨abFamEquiv (conjCont σ) i x, (abEquiv_mem_abUnits_iff _ _).2 hx⟩
  simp only [h1]
  rw [e2, coe_unitsΩMap, e1]
  exact unitsMap_conj σ i ⟨x, hx⟩

end Equivariance

end

end Iut.Reconstruction
