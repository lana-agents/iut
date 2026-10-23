/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Complex tori and their torsion points ([AbsTopIII] Corollary 2.7 (b), (c))

For a period pair `L` (Mathlib's `PeriodPair`: two `ℝ`-independent periods `ω₁, ω₂`, spanning the
lattice `Λ`), the **complex torus** `T_Λ = ℂ ⧸ Λ` is the one-point compactification of the
once-punctured elliptic curve `E = T_Λ ∖ {0}` of [AbsTopIII] Corollary 2.7 (a)–(c).

## Contents

* `Torus L`: the quotient `ℂ ⧸ Λ` with the quotient topology (a Hausdorff topological group),
  `Torus.mk : ℂ → Torus L`.
* `torsion L`: the torsion points; `dense_torsion`: they are dense ("since the torsion points of
  (b) are dense in `E^top`", Corollary 2.7 (c)).
* `eq_add_of_continuous`: **the group law of `T_Λ` is the unique continuous binary operation that
  extends the group law on the torsion points** (Corollary 2.7 (c): "one may construct the group
  structure on [the one-point compactification of] `E^top` … as the unique topological group
  structure that extends the group structure on the torsion points of (b)").
-/

namespace Iut

namespace AutHol

namespace Ell

open Set Topology

variable (L : PeriodPair)

instance : IsClosed (L.lattice.toAddSubgroup : Set ℂ) := ⟨L.isClosed_lattice.isOpen_compl⟩

/-- **The complex torus** `T_Λ = ℂ ⧸ Λ`. -/
abbrev Torus : Type := ℂ ⧸ L.lattice.toAddSubgroup

namespace Torus

/-- The projection `ℂ → T_Λ`. -/
def mk : ℂ → Torus L := QuotientAddGroup.mk

variable {L}

theorem mk_add (z w : ℂ) : mk L (z + w) = mk L z + mk L w := rfl

theorem mk_zero : mk L 0 = 0 := rfl

theorem mk_eq_mk {z w : ℂ} : mk L z = mk L w ↔ z - w ∈ L.lattice := by
  change ((z : ℂ) : Torus L) = (w : Torus L) ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  rfl

theorem mk_eq_zero {z : ℂ} : mk L z = 0 ↔ z ∈ L.lattice := by
  rw [← mk_zero, mk_eq_mk, sub_zero]

theorem mk_surjective : Function.Surjective (mk L) := QuotientAddGroup.mk_surjective

theorem continuous_mk : Continuous (mk L) := continuous_quot_mk

theorem isOpenMap_mk : IsOpenMap (mk L) := QuotientAddGroup.isOpenMap_coe

theorem mk_nsmul (n : ℕ) (z : ℂ) : mk L ((n : ℂ) * z) = n • mk L z := by
  change (((n : ℂ) * z : ℂ) : Torus L) = n • (z : Torus L)
  rw [← nsmul_eq_mul, QuotientAddGroup.mk_nsmul]

end Torus

/-! ### Torsion points -/

/-- **The torsion points** of `T_Λ`. -/
def torsion : Set (Torus L) := {x | IsOfFinAddOrder x}

variable {L}

theorem zero_mem_torsion : (0 : Torus L) ∈ torsion L :=
  isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨1, one_pos, by simp⟩

theorem add_mem_torsion {x y : Torus L} (hx : x ∈ torsion L) (hy : y ∈ torsion L) :
    x + y ∈ torsion L := IsOfFinAddOrder.add hx hy

theorem neg_mem_torsion {x : Torus L} (hx : x ∈ torsion L) : -x ∈ torsion L :=
  IsOfFinAddOrder.neg hx

/-- The points `α ω₁ + β ω₂` with `α, β ∈ ℚ` map to torsion points. -/
theorem mk_rat_mem_torsion (α β : ℚ) :
    Torus.mk L ((α : ℂ) * L.ω₁ + (β : ℂ) * L.ω₂) ∈ torsion L := by
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨α.den * β.den, Nat.mul_pos α.den_pos β.den_pos, ?_⟩
  rw [← Torus.mk_nsmul, Torus.mk_eq_zero, PeriodPair.mem_lattice]
  refine ⟨α.num * β.den, β.num * α.den, ?_⟩
  have hα : (α : ℂ) * α.den = α.num := by exact_mod_cast Rat.mul_den_eq_num α
  have hβ : (β : ℂ) * β.den = β.num := by exact_mod_cast Rat.mul_den_eq_num β
  push_cast
  linear_combination (-(β.den * L.ω₁) : ℂ) * hα + (-(α.den * L.ω₂) : ℂ) * hβ

/-- The rational points `ℚ ω₁ + ℚ ω₂` are dense in `ℂ`. -/
theorem dense_rat_span :
    Dense (range fun q : ℚ × ℚ => (q.1 : ℂ) * L.ω₁ + (q.2 : ℂ) * L.ω₂) := by
  let f : ℝ × ℝ → ℂ := fun a => (a.1 : ℂ) * L.ω₁ + (a.2 : ℂ) * L.ω₂
  have hf : Continuous f := by fun_prop
  have hfs : Function.Surjective f := by
    intro z
    refine ⟨(L.basis.repr z 0, L.basis.repr z 1), ?_⟩
    have := L.basis.sum_repr z
    rw [Fin.sum_univ_two, PeriodPair.basis_zero, PeriodPair.basis_one] at this
    simp only [f]
    rw [← Complex.real_smul, ← Complex.real_smul]
    exact this
  have hg : DenseRange fun q : ℚ × ℚ => ((q.1 : ℝ), (q.2 : ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have h := hfs.denseRange.comp hg hf
  unfold DenseRange at h
  convert h using 2
  funext q
  simp [f]

/-- **The torsion points are dense** in `T_Λ` ([AbsTopIII] Corollary 2.7 (c)). -/
theorem dense_torsion : Dense (torsion L) := by
  have h := (Torus.mk_surjective (L := L)).denseRange.dense_image Torus.continuous_mk
    (dense_rat_span (L := L))
  refine h.mono ?_
  rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
  exact mk_rat_mem_torsion q.1 q.2

/-- **[AbsTopIII] Corollary 2.7 (c), uniqueness**: a continuous binary operation on `T_Λ` that
agrees with the group law on pairs of torsion points is the group law. -/
theorem eq_add_of_continuous {μ : Torus L → Torus L → Torus L}
    (hμ : Continuous fun p : Torus L × Torus L => μ p.1 p.2)
    (h : ∀ x ∈ torsion L, ∀ y ∈ torsion L, μ x y = x + y) : μ = (· + ·) := by
  have := Continuous.ext_on (dense_torsion.prod dense_torsion) hμ continuous_add
    (fun p hp => h p.1 hp.1 p.2 hp.2)
  funext x y
  exact congrFun this (x, y)

/-- Uniqueness of the inverse: a continuous map agreeing with `-` on torsion points is `-`. -/
theorem eq_neg_of_continuous {ν : Torus L → Torus L} (hν : Continuous ν)
    (h : ∀ x ∈ torsion L, ν x = -x) : ν = Neg.neg :=
  Continuous.ext_on dense_torsion hν continuous_neg h

end Ell

end AutHol

end Iut
