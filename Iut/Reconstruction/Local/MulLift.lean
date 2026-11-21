/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Cor110WeilBar
import Iut.Reconstruction.Local.Valuation

/-!
# Lifting isomorphisms of `G_k` to `k̄^×` ([AbsTopIII], Proposition 3.2 (iv), surjectivity)

[AbsTopIII], Proposition 3.2 (iv) (`Topics in Absolute Anabelian Geometry III.txt`,
l.4111–4124) says that for MLF-Galois `TM`-pairs the natural map
`Isom((Π ↷ M), (Π* ↷ M*)) → Isom(Π, Π*)` is a bijection. The proof of the surjectivity
(l.4150–4155) considers "the copy of `M_TM ≅ O^▷_k` embedded in abelianizations of open subgroups
of `G ≅ G_k` via local class field theory" ([Mzk9], Proposition 1.2.1 (iii), (iv)), together with
Corollary 1.10 (b). In `Cor110WeilBar.lean` this copy is `weilBar G ⊆ lim→_U U^ab` (the colimit
along the transfer of the Weil parts of the `U^ab`, i.e. `k̄^×(G)` at all levels), which is
group-theoretic (`barMap_mem_weilBar`), and `weilBarEquiv : weilBar G_k ≃* Ωˣ` is
`G_k`-equivariant. Here, for finite extensions `k, k'` of `ℚ_p` inside one algebraically closed
`Ω` and an isomorphism of topological groups `φ : Gal(Ω/k) ≃ₜ* Gal(Ω/k')`:

* **`mulLift φ : Ωˣ ≃* Ωˣ`**, the transport of `barMap φ` along `weilBarEquiv`;
* **`mulLift_smul`**: it is `φ`-equivariant, `ψ(g x) = φ(g) ψ(x)`;
* **`mulLift_mem_unitsΩ_iff`**: it maps `𝒪^×_Ω` onto itself;
* **`mulLift_algebraMap`**: on `k^×` it is `galEquiv_multEquiv φ` (P17), so it preserves the
  normalised valuation of `k` (`v_mulLift_algebraMap`) and the norm (`nrm_mulLift_algebraMap`).

The norm on all of `Ωˣ` is treated for `Ω = \bar{ℚ}_p` in `MulRigid.lean` (`ord(Ωˣ) ⊆ ℚ`).
-/

open PadicField IntermediateField

set_option linter.unusedSectionVars false

noncomputable section

namespace Iut.Reconstruction

section MulLift

variable {p : ℕ} [hp : Fact p.Prime]
variable {k k' : Type*} [Field k] [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]
  [Field k'] [Algebra ℚ_[p] k'] [FiniteDimensional ℚ_[p] k']
variable {Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra k' Ω] [Algebra ℚ_[p] Ω]
  [IsScalarTower ℚ_[p] k Ω] [IsScalarTower ℚ_[p] k' Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [IsGalois k' Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

/-- `barMap φ` restricted to the Weil parts `k̄^×(G)`. -/
def weilBarMap (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k'] Ω)) :
    weilBar (Ω ≃ₐ[k] Ω) ≃* weilBar (Ω ≃ₐ[k'] Ω) where
  toFun z := ⟨barMap φ z, barMap_mem_weilBar φ z.2⟩
  invFun z := ⟨barMap φ.symm z, barMap_mem_weilBar φ.symm z.2⟩
  left_inv z := Subtype.ext ((barEquiv φ).symm_apply_apply z.1)
  right_inv z := Subtype.ext ((barEquiv φ).apply_symm_apply z.1)
  map_mul' z w := Subtype.ext ((barMap φ).map_mul z.1 w.1)

theorem coe_weilBarMap (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k'] Ω)) (z : weilBar (Ω ≃ₐ[k] Ω)) :
    (weilBarMap φ z : AbBar (Ω ≃ₐ[k'] Ω)) = barMap φ z := rfl

theorem weilBarMap_symm_weilBarMap (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k'] Ω))
    (z : weilBar (Ω ≃ₐ[k] Ω)) : weilBarMap φ.symm (weilBarMap φ z) = z :=
  Subtype.ext ((barEquiv φ).symm_apply_apply z.1)

variable (p) in
/-- **The lift `ψ : Ωˣ ≃* Ωˣ` of `φ : G_k ≃ₜ* G_{k'}`** ([AbsTopIII], Proposition 3.2 (iv),
`T = TM`; [Mzk9], Proposition 1.2.1 (iii), (iv)): `barMap φ` on `k̄^×(G)`, transported along
`weilBarEquiv`. -/
def mulLift (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k'] Ω)) : Ωˣ ≃* Ωˣ :=
  (weilBarEquiv p k Ω).symm.trans ((weilBarMap φ).trans (weilBarEquiv p k' Ω))

theorem mulLift_apply (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k'] Ω)) (x : Ωˣ) :
    mulLift p φ x = weilBarHom p (weilBarMap φ ((weilBarEquiv p k Ω).symm x)) := rfl

/-- **`mulLift φ` is `φ`-equivariant**: `ψ(g x) = φ(g) ψ(x)`. -/
theorem mulLift_smul (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k'] Ω)) (g : Ω ≃ₐ[k] Ω) (x y : Ωˣ)
    (hy : (y : Ω) = g (x : Ω)) :
    ((mulLift p φ y : Ωˣ) : Ω) = φ g ((mulLift p φ x : Ωˣ) : Ω) := by
  set z := (weilBarEquiv p k Ω).symm x with hz
  have hzx : weilBarHom p z = x := (weilBarEquiv p k Ω).apply_symm_apply x
  have hgz : (weilBarEquiv p k Ω).symm y = ⟨barConj _ g z, barConj_mem_weilBar g z.2⟩ := by
    rw [MulEquiv.symm_apply_eq, weilBarEquiv_apply]
    apply Units.ext
    rw [weilBarHom_barConj, hzx, hy]
  rw [mulLift_apply, mulLift_apply, hgz, ← hz]
  have h1 : weilBarMap φ ⟨barConj _ g z, barConj_mem_weilBar g z.2⟩ =
      ⟨barConj _ (φ g) (weilBarMap φ z), barConj_mem_weilBar (φ g) (weilBarMap φ z).2⟩ :=
    Subtype.ext (barMap_barConj φ g z)
  rw [h1, weilBarHom_barConj]

/-- `weilBarHom` detects `𝒪^×(G)`. -/
theorem mem_unitsBar_of_weilBarHom (z : weilBar (Ω ≃ₐ[k] Ω))
    (hz : weilBarHom p z ∈ unitsΩ p Ω) : (z : AbBar (Ω ≃ₐ[k] Ω)) ∈ unitsBar (Ω ≃ₐ[k] Ω) := by
  obtain ⟨u, hu⟩ := (unitsBarEquiv p k Ω).surjective ⟨_, hz⟩
  have h := weilBarHom_eq_unitsBarEquiv (p := p) u
  rw [hu] at h
  have := weilBarHom_injective (k := k) (Ω := Ω) (p := p) h
  rw [← this]
  exact u.2

/-- `mulLift φ` maps units to units. -/
theorem mulLift_mem_unitsΩ (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k'] Ω)) {x : Ωˣ}
    (hx : x ∈ unitsΩ p Ω) : mulLift p φ x ∈ unitsΩ p Ω := by
  set z := (weilBarEquiv p k Ω).symm x
  have hzx : weilBarHom p z = x := (weilBarEquiv p k Ω).apply_symm_apply x
  have hz : (z : AbBar _) ∈ unitsBar (Ω ≃ₐ[k] Ω) :=
    mem_unitsBar_of_weilBarHom z (by rw [hzx]; exact hx)
  have hw : (weilBarMap φ z : AbBar _) ∈ unitsBar (Ω ≃ₐ[k'] Ω) := by
    rw [coe_weilBarMap, ← map_unitsBar φ]
    exact Subgroup.mem_map_of_mem _ hz
  rw [mulLift_apply,
    show weilBarMap φ z = ⟨(⟨_, hw⟩ : unitsBar (Ω ≃ₐ[k'] Ω)),
      unitsBar_le_weilBar (Ω ≃ₐ[k'] Ω) hw⟩ from rfl,
    weilBarHom_eq_unitsBarEquiv]
  exact (unitsBarEquiv p k' Ω _).2

/-- **`mulLift φ` maps `𝒪^×_Ω` onto itself.** -/
theorem mulLift_mem_unitsΩ_iff (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k'] Ω)) (x : Ωˣ) :
    mulLift p φ x ∈ unitsΩ p Ω ↔ x ∈ unitsΩ p Ω := by
  refine ⟨fun h => ?_, mulLift_mem_unitsΩ φ⟩
  have h2 := mulLift_mem_unitsΩ (p := p) φ.symm h
  have hinv : mulLift p φ.symm (mulLift p φ x) = x := by
    simp only [mulLift, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [weilBarMap_symm_weilBarMap, MulEquiv.apply_symm_apply]
  rwa [hinv] at h2

set_option maxHeartbeats 1000000 in
-- elaborating the fixed fields of open subgroups and their Galois groups is slow
/-- **On `k^×`, `mulLift φ` is the P17 isomorphism `galEquiv_multEquiv φ : k^× ≃* k'^×`.** -/
theorem mulLift_algebraMap (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k'] Ω)) (a : kˣ) :
    mulLift p φ (Units.map (algebraMap k Ω).toMonoidHom a) =
      Units.map (algebraMap k' Ω).toMonoidHom (galEquiv_multEquiv p p φ a) := by
  have h1 := weilBarHom_topBar (p := p) (Ω := Ω) a
  have h2 := weilBarHom_topBar (p := p) (Ω := Ω) (galEquiv_multEquiv p p φ a)
  have hs : (weilBarEquiv p k Ω).symm (Units.map (algebraMap k Ω).toMonoidHom a) =
      ⟨topBar _ (multAbEquiv p k Ω a), topBar_mem_weilBar (multAbEquiv p k Ω a).2⟩ := by
    rw [MulEquiv.symm_apply_eq, weilBarEquiv_apply, h1]
  rw [mulLift_apply, hs, ← h2]
  congr 1
  apply Subtype.ext
  rw [coe_weilBarMap]
  change barMap φ (topBar _ _) = topBar _ _
  rw [barMap_topBar, multAbEquiv_galEquiv_multEquiv]

/-- **`mulLift φ` preserves the normalised valuation on `k^×`.** -/
theorem v_mulLift_algebraMap (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k'] Ω)) (a : kˣ) :
    v p ((galEquiv_multEquiv p p φ a : k'ˣ) : k') = v p (a : k) :=
  v_galEquiv_multEquiv φ a

/-- **`mulLift φ` preserves the norm of `ι(a)` for `a ∈ k^×` when `k' = k`.** -/
theorem nrm_mulLift_algebraMap (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k] Ω)) (a : kˣ) :
    nrm p Ω ((mulLift p φ (Units.map (algebraMap k Ω).toMonoidHom a) : Ωˣ) : Ω) =
      nrm p Ω (algebraMap k Ω (a : k)) := by
  rw [mulLift_algebraMap]
  change nrm p Ω (algebraMap k Ω ((galEquiv_multEquiv p p φ a : kˣ) : k)) = _
  rw [nrm_apply, nrm_apply, ← spectralNorm.eq_of_tower, ← spectralNorm.eq_of_tower,
    ← nrm_apply, ← nrm_apply]
  exact (nrm_eq_iff_v_eq (Units.ne_zero _) (Units.ne_zero _)).2 (v_galEquiv_multEquiv φ a)

end MulLift

end Iut.Reconstruction

end
