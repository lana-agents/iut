/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Commutator
import Mathlib.Tactic.Group

/-!
# The maximal cuspidally central quotient ([AbsTopIII], Proposition 1.4(ii))

[AbsTopIII], Proposition 1.4(ii) (l.1771–1781 of `~/iut-scratch/papers/txt/Topics in Absolute
Anabelian Geometry III.txt`): "`Δ_{U_x} ↠ Δ^{c-cn}_{U_x}` for the maximal cuspidally central
quotient of `Δ_{U_x}` [i.e., the maximal intermediate quotient `Δ_{U_x} ↠ Q ↠ Δ_X` such that
`Ker(Q ↠ Δ_X)` lies in the center of `Q` — cf. [Mzk19], Definition 1.1, (i)]".

For a continuous surjection `π : Δ → Q` of topological groups (`Q` with closed points), this file
constructs `Δ^{c-cn} = Δ / cl⁅Ker π, Δ⁆` (`CuspCentral π`) with the induced map `cuspCentralMap`
to `Q`, and proves:

* `ker_cuspCentralMap_le_center`: `Ker(Δ^{c-cn} → Q)` is central;
* **`cuspCentralKer_le_ker`**, `cuspCentralLift`, `cuspCentralLift_mk`, `cuspCentralLift_unique`:
  every intermediate quotient `ρ : Δ → Q'`, `τ : Q' → Q`, `τ ∘ ρ = π`, with `Ker τ` central and
  `ρ` continuous into a `T1` group, factors uniquely through `Δ^{c-cn}` (maximality).

This is the group-theoretic part of MR9 step C1 (`Plans/MR9Plan.md`); the transgression
`M_X ≅ I_x` needs `H²` of the surface group (not here).
-/

namespace Iut.Reconstruction

variable {Δ Q : Type*} [Group Δ] [TopologicalSpace Δ] [IsTopologicalGroup Δ] [Group Q]
  [TopologicalSpace Q] [T1Space Q] (π : Δ →* Q)

/-- `cl⁅Ker π, Δ⁆`, the kernel of the maximal cuspidally central quotient. -/
def cuspCentralKer : Subgroup Δ := (⁅π.ker, ⊤⁆ : Subgroup Δ).topologicalClosure

instance cuspCentralKer_normal : (cuspCentralKer π).Normal :=
  Subgroup.is_normal_topologicalClosure _

/-- **The maximal cuspidally central quotient** `Δ^{c-cn} = Δ / cl⁅Ker π, Δ⁆`. -/
abbrev CuspCentral : Type _ := Δ ⧸ cuspCentralKer π

omit [IsTopologicalGroup Δ] in
/-- The kernel of a continuous homomorphism to a `T1` group is closed. -/
lemma isClosed_ker {Q' : Type*} [Group Q'] [TopologicalSpace Q'] [T1Space Q'] (ρ : Δ →* Q')
    (hρ : Continuous ρ) : IsClosed (ρ.ker : Set Δ) := by
  have : (ρ.ker : Set Δ) = ρ ⁻¹' {1} := by ext; simp
  rw [this]
  exact isClosed_singleton.preimage hρ

omit [TopologicalSpace Q] [T1Space Q] in
/-- **Maximality**: for an intermediate quotient `Δ → Q' → Q` with central kernel `Ker(Q' → Q)`,
`cl⁅Ker π, Δ⁆ ⊆ Ker(Δ → Q')`. -/
theorem cuspCentralKer_le_ker {Q' : Type*} [Group Q'] [TopologicalSpace Q'] [T1Space Q']
    (ρ : Δ →* Q') (hρ : Continuous ρ) (τ : Q' →* Q) (hτ : τ.comp ρ = π)
    (hcent : τ.ker ≤ Subgroup.center Q') : cuspCentralKer π ≤ ρ.ker := by
  refine Subgroup.topologicalClosure_minimal _ ?_ (isClosed_ker ρ hρ)
  rw [Subgroup.commutator_le]
  intro a ha b _
  have ha' : ρ a ∈ τ.ker := by
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hτ]
    exact ha
  have hc := Subgroup.mem_center_iff.mp (hcent ha') (ρ b)
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, ← hc,
    mul_inv_cancel_right, mul_inv_cancel]

lemma cuspCentralKer_le_ker_self (hπ : Continuous π) : cuspCentralKer π ≤ π.ker :=
  cuspCentralKer_le_ker π π hπ (MonoidHom.id Q) (MonoidHom.id_comp π) (by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
    rw [hx]
    exact Subgroup.one_mem _)

/-- The induced map `Δ^{c-cn} → Q`. -/
def cuspCentralMap (hπ : Continuous π) : CuspCentral π →* Q :=
  QuotientGroup.lift _ π (cuspCentralKer_le_ker_self π hπ)

@[simp] lemma cuspCentralMap_mk (hπ : Continuous π) (a : Δ) :
    cuspCentralMap π hπ (QuotientGroup.mk a) = π a := rfl

/-- **`Ker(Δ^{c-cn} → Q)` is central.** -/
theorem ker_cuspCentralMap_le_center (hπ : Continuous π) :
    (cuspCentralMap π hπ).ker ≤ Subgroup.center (CuspCentral π) := by
  intro x hx
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have ha : a ∈ π.ker := hx
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  apply Subgroup.le_topologicalClosure
  have hmem := Subgroup.commutator_mem_commutator (inv_mem ha) (Subgroup.mem_top b⁻¹)
  rw [commutatorElement_def, inv_inv, inv_inv] at hmem
  convert hmem using 1
  group

/-- **The factorisation** through `Δ^{c-cn}` of an intermediate quotient with central kernel. -/
def cuspCentralLift {Q' : Type*} [Group Q'] [TopologicalSpace Q'] [T1Space Q']
    (ρ : Δ →* Q') (hρ : Continuous ρ) (τ : Q' →* Q) (hτ : τ.comp ρ = π)
    (hcent : τ.ker ≤ Subgroup.center Q') : CuspCentral π →* Q' :=
  QuotientGroup.lift _ ρ (cuspCentralKer_le_ker π ρ hρ τ hτ hcent)

omit [TopologicalSpace Q] [T1Space Q] in
@[simp] lemma cuspCentralLift_mk {Q' : Type*} [Group Q'] [TopologicalSpace Q'] [T1Space Q']
    (ρ : Δ →* Q') (hρ : Continuous ρ) (τ : Q' →* Q) (hτ : τ.comp ρ = π)
    (hcent : τ.ker ≤ Subgroup.center Q') (a : Δ) :
    cuspCentralLift π ρ hρ τ hτ hcent (QuotientGroup.mk a) = ρ a := rfl

omit [TopologicalSpace Q] [T1Space Q] in
/-- **Uniqueness of the factorisation.** -/
theorem cuspCentralLift_unique {Q' : Type*} [Group Q'] (ρ : Δ →* Q') (f g : CuspCentral π →* Q')
    (hf : f.comp (QuotientGroup.mk' _) = ρ) (hg : g.comp (QuotientGroup.mk' _) = ρ) : f = g := by
  ext a
  have h1 := congrArg (fun h : Δ →* Q' => h a) hf
  have h2 := congrArg (fun h : Δ →* Q' => h a) hg
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply] at h1 h2 ⊢
  rw [h1, h2]

end Iut.Reconstruction
