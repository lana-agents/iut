/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Belyi cuspidalisation: the group-theoretic skeleton (roadmap P17, M4c)

[AbsTopIII], Theorem 1.9 (a) (via [AbsTopII], Corollary 3.7): for a hyperbolic curve `Y` of
strictly Belyi type and an open `U = Y \ S` obtained by removing finitely many NF-points, the
surjection `Π_U ↠ Π_Y` and the decomposition groups of the NF-points are constructed
group-theoretically. The construction runs as follows:

1. a Belyi map `β : Y → ℙ¹` unramified over `ℙ¹ \ {0, 1, ∞}` with `S ⊆ β⁻¹{0, 1, ∞}` exhibits
   `Π_W`, `W = Y \ β⁻¹{0,1,∞}`, as an open subgroup of the tripod group `Π_{ℙ¹ \ {0,1,∞}}`; the
   existence of `β` (Belyi) and the group-theoretic characterisation of the open immersions
   arising this way (the Grothendieck conjecture over sub-`p`-adic fields, [AbsTopII], Cor. 3.7)
   are the deep inputs — not formalised;
2. the cusps of `W` correspond to conjugacy classes of cuspidal inertia subgroups `I_c ≤ Π_W`
   ([AbsTopI], Lemma 4.5 (v));
3. **filling in cusps**: `Π_U = Π_W / ⟨⟨I_c : c ∉ S⟩⟩` and `Π_Y = Π_W / ⟨⟨I_c : all c⟩⟩`, and
   `Π_U ↠ Π_Y` is the induced surjection.

Step 3 is pure group theory and is formalised here, together with its **functoriality**: an
isomorphism of the data of step 2 (an isomorphism `Π_W ≃ Π_W'` carrying the family of cuspidal
inertia subgroups onto the other family) induces compatible isomorphisms of the filled groups.

## Main definitions and results

* `Iut.Reconstruction.CuspData`: a group with a family of (cuspidal inertia) subgroups;
* `Iut.Reconstruction.CuspData.kernel D S = ⟨⟨I_c : c ∉ S⟩⟩`, `CuspData.Filled D S`;
* `Iut.Reconstruction.CuspData.fillMap` (`Π_{Y∖S} ↠ Π_{Y∖S'}` for `S' ⊆ S`) and
  `fillMap_surjective`;
* `Iut.Reconstruction.CuspData.Iso`, `CuspData.map_kernel`, `CuspData.filledEquiv`
  (functoriality) and `filledEquiv_fillMap` (compatibility with filling).
-/

namespace Iut.Reconstruction

/-- A group `Γ_W` with a family of subgroups (the cuspidal inertia subgroups `I_c`). -/
structure CuspData (Γ : Type*) [Group Γ] (ι : Type*) where
  /-- The cuspidal inertia subgroup at the cusp `c`. -/
  inertia : ι → Subgroup Γ

namespace CuspData

variable {Γ : Type*} [Group Γ] {ι : Type*} (D : CuspData Γ ι)

/-- The kernel `⟨⟨I_c : c ∉ S⟩⟩` of filling in all cusps outside `S`. -/
def kernel (S : Set ι) : Subgroup Γ :=
  Subgroup.normalClosure (⋃ c ∈ Sᶜ, (D.inertia c : Set Γ))

instance kernel_normal (S : Set ι) : (D.kernel S).Normal :=
  Subgroup.normalClosure_normal

/-- The fundamental group `Γ_{W ∪ (cusps ∖ S)}` obtained by filling in the cusps not in `S`. -/
abbrev Filled (S : Set ι) : Type _ := Γ ⧸ D.kernel S

theorem kernel_anti {S S' : Set ι} (h : S' ⊆ S) : D.kernel S ≤ D.kernel S' := by
  refine Subgroup.normalClosure_mono ?_
  refine Set.iUnion₂_subset fun c hc => ?_
  exact Set.subset_iUnion₂_of_subset c (fun hc' => hc (h hc')) le_rfl

/-- Filling in more cusps: `Γ_{W ∪ (cusps ∖ S)} ↠ Γ_{W ∪ (cusps ∖ S')}` for `S' ⊆ S`. -/
def fillMap {S S' : Set ι} (h : S' ⊆ S) : D.Filled S →* D.Filled S' :=
  QuotientGroup.map _ _ (MonoidHom.id Γ) (D.kernel_anti h)

theorem fillMap_surjective {S S' : Set ι} (h : S' ⊆ S) : Function.Surjective (D.fillMap h) := by
  intro x
  induction x using QuotientGroup.induction_on with | H g => exact ⟨QuotientGroup.mk g, rfl⟩

theorem inertia_le_kernel {S : Set ι} {c : ι} (hc : c ∉ S) : D.inertia c ≤ D.kernel S :=
  fun _ hx => Subgroup.subset_normalClosure (Set.mem_iUnion₂.2 ⟨c, hc, hx⟩)

/-- The cuspidal inertia subgroups of the filled cusps die in the filled group. -/
theorem mk_inertia {S : Set ι} {c : ι} (hc : c ∉ S) {x : Γ} (hx : x ∈ D.inertia c) :
    (QuotientGroup.mk x : D.Filled S) = 1 :=
  (QuotientGroup.eq_one_iff x).2 (D.inertia_le_kernel hc hx)

variable {Γ' : Type*} [Group Γ'] {ι' : Type*} (D' : CuspData Γ' ι')

/-- An isomorphism of cusp data: a group isomorphism carrying `I_c` onto `I'_{σ c}`. -/
structure Iso where
  /-- The isomorphism of groups. -/
  toMulEquiv : Γ ≃* Γ'
  /-- The bijection of cusps. -/
  cusps : ι ≃ ι'
  map_inertia : ∀ c, (D.inertia c).map toMulEquiv.toMonoidHom = D'.inertia (cusps c)

variable {D D'}

theorem map_kernel (φ : D.Iso D') (S : Set ι) :
    (D.kernel S).map φ.toMulEquiv.toMonoidHom = D'.kernel (φ.cusps '' S) := by
  rw [kernel, kernel, Subgroup.map_normalClosure _ _ φ.toMulEquiv.surjective, Set.image_iUnion₂]
  congr 1
  ext x
  simp only [Set.mem_iUnion, Set.mem_compl_iff, exists_prop]
  constructor
  · rintro ⟨c, hc, hx⟩
    refine ⟨φ.cusps c, fun h => hc ?_, ?_⟩
    · obtain ⟨c', hc', he⟩ := h
      rwa [← φ.cusps.injective he]
    · rw [← φ.map_inertia c]
      exact hx
  · rintro ⟨c', hc', hx⟩
    refine ⟨φ.cusps.symm c', fun h => hc' ⟨_, h, by simp⟩, ?_⟩
    have := φ.map_inertia (φ.cusps.symm c')
    rw [Equiv.apply_symm_apply] at this
    rw [← this] at hx
    exact hx

/-- **Functoriality of filling in cusps**: an isomorphism of cusp data induces an isomorphism
of the filled groups. -/
noncomputable def filledEquiv (φ : D.Iso D') (S : Set ι) :
    D.Filled S ≃* D'.Filled (φ.cusps '' S) :=
  QuotientGroup.congr _ _ φ.toMulEquiv (map_kernel φ S)

theorem filledEquiv_mk (φ : D.Iso D') (S : Set ι) (x : Γ) :
    filledEquiv φ S (QuotientGroup.mk x) = QuotientGroup.mk (φ.toMulEquiv x) := rfl

/-- The isomorphisms of filled groups are compatible with filling in more cusps. -/
theorem filledEquiv_fillMap (φ : D.Iso D') {S S' : Set ι} (h : S' ⊆ S) (x : D.Filled S) :
    filledEquiv φ S' (D.fillMap h x) =
      D'.fillMap (Set.image_mono h) (filledEquiv φ S x) := by
  induction x using QuotientGroup.induction_on with | H g => rfl

end CuspData

end Iut.Reconstruction
