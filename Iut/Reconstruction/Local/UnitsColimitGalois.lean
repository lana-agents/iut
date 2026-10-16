/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.UnitsColimit
import Iut.Reconstruction.Local.LogShellGalois
import Iut.Reconstruction.Local.AbelianZHat
import LocalClassFieldTheory.Brauer.ArtinTransfer

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
* **`unitsBarEquiv : unitsBar G_k ≃* 𝒪^×_Ω`**.
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

end

end Iut.Reconstruction
