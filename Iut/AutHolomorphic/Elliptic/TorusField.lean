/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Elliptic.LinearHol
import Mathlib.Algebra.Field.TransferInstance

/-!
# The field `A_p ∪ {0}` of a complex torus ([AbsTopIII] Corollary 2.7 (e), Definition 4.1 (i))

For the complex torus `T_Λ` with its Aut-holomorphic structure `torusStr L` and `p = mk q`:

* `mem_apSet_iff`: **`A_p` consists of the maps `c ↦ b c`, `b ≠ 0`, of `Lie T_Λ ≅ ℂ`**
  ([AbsTopIII] Proposition 2.6 (a): "a natural isomorphism of topological groups `ℂ^× ≅ A_p`
  induced by the tautological action"); it does not depend on `p`.
* `TorusField L q = A_p ∪ {0}` (the model-implicit set `fieldSet`), with the topology of pointwise
  convergence on `Lie T_Λ` (itself with the compact-open topology);
* its field structure: **addition is addition of endomorphisms (`add_val`), multiplication is
  composition (`mul_val`)**;
* `torusEquiv : TorusField L q ≃+* ℂ`, a homeomorphism (`continuous_torusEquiv`,
  `continuous_torusEquiv_symm`): `A_p ∪ {0}` is a topological field isomorphic to `ℂ`, i.e. the
  CAF `A_{X_ell}` of Definition 4.1 (i) for the once-punctured elliptic curve `T_Λ ∖ {0}`.
-/

namespace Iut

namespace AutHol

namespace Ell

open Set Topology ComplexConjugate Complex Torus

variable {L : PeriodPair}

/-- Multiplication by `b` on `Lie T_Λ`, in the coordinate `Lie T_Λ ≅ ℂ`. -/
noncomputable def mulMap (b : ℂ) : Lie (Torus L) →ₗ[ℝ] Lie (Torus L) :=
  (lieEquiv (L := L)).toLinearMap ∘ₗ (LinearMap.mulLeft ℝ b) ∘ₗ
    (lieEquiv (L := L)).symm.toLinearMap

theorem line_zero : line (L := L) 0 = 0 := map_zero (lieEquiv (L := L))

theorem mulMap_line (b c : ℂ) : mulMap (L := L) b (line c) = line (b * c) := by
  simp [mulMap, ← lieEquiv_apply]

theorem linearMap_ext_line {M M' : Lie (Torus L) →ₗ[ℝ] Lie (Torus L)}
    (h : ∀ c, M (line c) = M' (line c)) : M = M' := by
  ext1 f
  obtain ⟨c, rfl⟩ := exists_line f
  exact h c

/-- The automorphism `c ↦ a c` of `Lie T_Λ` for `a ≠ 0`. -/
noncomputable def mulEquiv' {a : ℂ} (ha : a ≠ 0) : Lie (Torus L) ≃ₗ[ℝ] Lie (Torus L) :=
  (lieEquiv (L := L)).symm.trans
    (((LinearEquiv.smulOfNeZero ℂ ℂ a ha).restrictScalars ℝ).trans lieEquiv)

theorem mulEquiv'_line {a : ℂ} (ha : a ≠ 0) (c : ℂ) :
    mulEquiv' (L := L) ha (line c) = line (a * c) := by
  simp [mulEquiv', ← lieEquiv_apply]

/-- **`A_p` for the complex torus**: the maps `c ↦ b c`, `b ≠ 0`. -/
theorem mem_apSet_iff (q : ℂ) (M : Lie (Torus L) →ₗ[ℝ] Lie (Torus L)) :
    M ∈ apSet (torusStr L) (mk L q) ↔ ∃ b, b ≠ 0 ∧ M = mulMap b := by
  constructor
  · rintro ⟨N, hN, rfl⟩
    obtain ⟨a, ε, ha, hNa⟩ := (isLinHol_iff q N).1 hN
    obtain ⟨b, hb, hbz⟩ := rc_sq a ε
    refine ⟨b, hb.resolve_right ha, linearMap_ext_line fun c => ?_⟩
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, hNa, mulMap_line, hbz]
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha⟩ := exists_sq_eq b
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hb
      simpa [rc] using (ha 1).symm
    refine ⟨mulEquiv' ha0, ?_, linearMap_ext_line fun c => ?_⟩
    · exact isLinHol_of_rc q _ ha0 false fun c => by
        rw [LinearEquiv.coe_coe, mulEquiv'_line]; rfl
    · simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, mulEquiv'_line, mulMap_line]
      rw [← ha c]
      rfl

theorem mem_fieldSet_iff (q : ℂ) (M : Lie (Torus L) →ₗ[ℝ] Lie (Torus L)) :
    M ∈ fieldSet (torusStr L) (mk L q) ↔ ∃ b, M = mulMap b := by
  rw [fieldSet, mem_union, mem_apSet_iff, mem_singleton_iff]
  constructor
  · rintro (⟨b, -, rfl⟩ | rfl)
    · exact ⟨b, rfl⟩
    · exact ⟨0, linearMap_ext_line fun c => by simp [mulMap_line, line_zero]⟩
  · rintro ⟨b, rfl⟩
    by_cases hb : b = 0
    · right
      subst hb
      exact linearMap_ext_line fun c => by simp [mulMap_line, line_zero]
    · exact Or.inl ⟨b, hb, rfl⟩

theorem mulMap_injective : Function.Injective (mulMap (L := L)) := by
  intro b b' h
  have := LinearMap.congr_fun h (line 1)
  rw [mulMap_line, mulMap_line] at this
  simpa using line_injective this

/-- **`A_p ∪ {0}`** for the complex torus `T_Λ` at `p = mk q`. -/
noncomputable def TorusField (L : PeriodPair) (q : ℂ) : Type :=
  fieldSet (torusStr L) (mk L q)

/-- The topology of pointwise convergence on `Lie T_Λ`. -/
noncomputable instance (q : ℂ) : TopologicalSpace (TorusField L q) :=
  TopologicalSpace.induced (fun M : TorusField L q => (M.1 : Lie (Torus L) → Lie (Torus L)))
    inferInstance

namespace TorusField

variable {q : ℂ}

/-- The underlying endomorphism of `Lie T_Λ`. -/
def val (M : TorusField L q) : Lie (Torus L) →ₗ[ℝ] Lie (Torus L) := M.1

theorem val_injective : Function.Injective (val : TorusField L q → _) := Subtype.val_injective

/-- The coefficient equivalence `A_p ∪ {0} ≃ ℂ`. -/
noncomputable def coeffEquiv (L : PeriodPair) (q : ℂ) : TorusField L q ≃ ℂ where
  toFun M := lieEquiv.symm (M.1 (line 1))
  invFun b := ⟨mulMap b, (mem_fieldSet_iff q _).2 ⟨b, rfl⟩⟩
  left_inv M := by
    obtain ⟨b, hb⟩ := (mem_fieldSet_iff q M.1).1 M.2
    apply Subtype.ext
    simp only
    rw [hb, mulMap_line, mul_one, ← lieEquiv_apply, LinearEquiv.symm_apply_apply]
  right_inv b := by
    change lieEquiv.symm (mulMap b (line 1)) = b
    rw [mulMap_line, mul_one, ← lieEquiv_apply, LinearEquiv.symm_apply_apply]

theorem coeffEquiv_symm_val (b : ℂ) : ((coeffEquiv L q).symm b).val = mulMap b := rfl

theorem val_eq_mulMap (M : TorusField L q) : M.val = mulMap (coeffEquiv L q M) := by
  have := congrArg val ((coeffEquiv L q).symm_apply_apply M)
  rw [coeffEquiv_symm_val] at this
  exact this.symm

noncomputable instance : Field (TorusField L q) := (coeffEquiv L q).field

theorem mulMap_add (b b' : ℂ) : mulMap (L := L) (b + b') = mulMap b + mulMap b' :=
  linearMap_ext_line fun c => by
    rw [LinearMap.add_apply, mulMap_line, mulMap_line, mulMap_line, add_mul, line_add]

theorem mulMap_mul (b b' : ℂ) : mulMap (L := L) (b * b') = mulMap b * mulMap b' :=
  linearMap_ext_line fun c => by
    simp only [mulMap_line, Module.End.mul_apply, mul_assoc]

/-- **Addition in `A_p ∪ {0}` is addition of endomorphisms of the tangent space.** -/
theorem add_val (M M' : TorusField L q) : (M + M').val = M.val + M'.val := by
  change ((coeffEquiv L q).symm (coeffEquiv L q M + coeffEquiv L q M')).val = _
  rw [coeffEquiv_symm_val, mulMap_add, ← val_eq_mulMap, ← val_eq_mulMap]

/-- **Multiplication in `A_p ∪ {0}` is composition.** -/
theorem mul_val (M M' : TorusField L q) : (M * M').val = M.val * M'.val := by
  change ((coeffEquiv L q).symm (coeffEquiv L q M * coeffEquiv L q M')).val = _
  rw [coeffEquiv_symm_val, mulMap_mul, ← val_eq_mulMap, ← val_eq_mulMap]

theorem zero_val : (0 : TorusField L q).val = 0 := by
  change ((coeffEquiv L q).symm 0).val = _
  rw [coeffEquiv_symm_val]
  exact linearMap_ext_line fun c => by simp [mulMap_line, line_zero]

theorem one_val : (1 : TorusField L q).val = 1 := by
  change ((coeffEquiv L q).symm 1).val = _
  rw [coeffEquiv_symm_val]
  exact linearMap_ext_line fun c => by simp [mulMap_line]

/-- **`A_p ∪ {0} ≅ ℂ` as fields.** -/
noncomputable def torusEquiv (L : PeriodPair) (q : ℂ) : TorusField L q ≃+* ℂ where
  toEquiv := coeffEquiv L q
  map_add' _ _ := (coeffEquiv L q).apply_symm_apply _
  map_mul' _ _ := (coeffEquiv L q).apply_symm_apply _

theorem torusEquiv_apply (M : TorusField L q) :
    torusEquiv L q M = lieEquiv.symm (M.val (line 1)) := rfl

theorem continuous_torusEquiv : Continuous (torusEquiv L q) := by
  have h1 : Continuous fun M : TorusField L q => M.val (line 1) :=
    (continuous_apply (line 1)).comp continuous_induced_dom
  exact continuous_lieEquiv_symm.comp h1

theorem continuous_torusEquiv_symm : Continuous (torusEquiv L q).symm := by
  refine continuous_induced_rng.2 (continuous_pi fun f => ?_)
  obtain ⟨c, rfl⟩ := exists_line f
  change Continuous fun b : ℂ => mulMap (L := L) b (line c)
  simp only [mulMap_line]
  exact continuous_line.comp (continuous_id.mul continuous_const)

/-- **`A_p ∪ {0}` is a topological field homeomorphic to `ℂ`.** -/
noncomputable def torusHomeo (L : PeriodPair) (q : ℂ) : TorusField L q ≃ₜ ℂ where
  toEquiv := (torusEquiv L q).toEquiv
  continuous_toFun := continuous_torusEquiv
  continuous_invFun := continuous_torusEquiv_symm

end TorusField

end Ell

end AutHol

end Iut
