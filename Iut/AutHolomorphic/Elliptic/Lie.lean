/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Elliptic.Torus
import Mathlib.Topology.Algebra.Group.CompactOpen
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Convex.Contractible

/-!
# One-parameter subgroups: the tangent space of a topological group ([AbsTopIII] Cor 2.7 (c))

[AbsTopIII] Corollary 2.7 (c) constructs line segments of `E^top` "by considering one-parameter
subgroups of these local additive group structures"; Remark 2.7.2 describes `A_p` as "the linear
holomorphic automorphisms of the tangent space to a point". Here:

* `Lie Y = (ℝ →ₜ+ Y)`: the continuous one-parameter subgroups of a commutative topological group
  `Y`, with the compact-open topology (Mathlib's topology on `ContinuousAddMonoidHom`), the
  pointwise group structure, and the `ℝ`-module structure `(r • f)(t) = f (r t)`;
* `expAt p f = p + f 1`: the exponential map at `p`.

For the complex torus `T_Λ` (`Torus.lean`):

* `Torus.line c : ℝ →ₜ+ T_Λ`, `t ↦ mk (t c)`;
* `Torus.lieEquiv : ℂ ≃ₗ[ℝ] Lie T_Λ`: **every one-parameter subgroup of `T_Λ` is `t ↦ mk (t c)`
  for a unique `c`** (lifting through the covering `ℂ → T_Λ`);
* `Torus.lieHomeo : ℂ ≃ₜ Lie T_Λ`: it is a homeomorphism for the compact-open topology.
-/

namespace Iut

namespace AutHol

namespace Ell

open Set Topology Filter

section Generic

variable (Y : Type*) [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]

/-- **The continuous one-parameter subgroups** `ℝ → Y` (the tangent space of `Y` at `0`). -/
abbrev Lie : Type _ := ContinuousAddMonoidHom ℝ Y

/-- Multiplication by `r` on `ℝ`, as a continuous additive homomorphism. -/
def mulLeftHom (r : ℝ) : ContinuousAddMonoidHom ℝ ℝ :=
  ⟨AddMonoidHom.mulLeft r, continuous_const.mul continuous_id⟩

@[simp]
theorem mulLeftHom_apply (r t : ℝ) : mulLeftHom r t = r * t := rfl

instance : Module ℝ (Lie Y) where
  smul r f := f.comp (mulLeftHom r)
  one_smul f := by ext t; change f (1 * t) = f t; rw [one_mul]
  mul_smul r s f := by ext t; change f (r * s * t) = f (s * (r * t)); ring_nf
  smul_zero r := by ext t; rfl
  smul_add r f g := by ext t; rfl
  add_smul r s f := by
    ext t
    change f ((r + s) * t) = f (r * t) + f (s * t)
    rw [add_mul, map_add]
  zero_smul f := by ext t; change f (0 * t) = 0; rw [zero_mul, map_zero]

variable {Y}

@[simp]
theorem lie_smul_apply (r : ℝ) (f : Lie Y) (t : ℝ) : (r • f) t = f (r * t) := rfl

@[simp]
theorem lie_add_apply (f g : Lie Y) (t : ℝ) : (f + g) t = f t + g t := rfl

/-- **The exponential map at `p`**: `f ↦ p + f 1`. -/
def expAt (p : Y) (f : Lie Y) : Y := p + f 1

theorem continuous_expAt (p : Y) : Continuous (expAt p : Lie Y → Y) :=
  continuous_const.add (continuous_eval_const 1)

end Generic

/-! ### The one-parameter subgroups of a complex torus -/

variable {L : PeriodPair}

namespace Torus

/-- The one-parameter subgroup `t ↦ mk (t c)` of `T_Λ`. -/
def line (c : ℂ) : Lie (Torus L) :=
  ⟨AddMonoidHom.mk' (fun t : ℝ => mk L ((t : ℂ) * c)) (fun s t => by
      rw [← mk_add]; push_cast; ring_nf),
    continuous_mk.comp (Complex.continuous_ofReal.mul continuous_const)⟩

@[simp]
theorem line_apply (c : ℂ) (t : ℝ) : line (L := L) c t = mk L ((t : ℂ) * c) := rfl

theorem line_add (c c' : ℂ) : line (L := L) (c + c') = line c + line c' := by
  ext t
  simp only [line_apply, lie_add_apply, ← mk_add, mul_add]

theorem line_smul (r : ℝ) (c : ℂ) : line (L := L) (r • c) = r • line c := by
  ext t
  simp only [line_apply, lie_smul_apply, Complex.real_smul]
  push_cast
  ring_nf

/-- A continuous map from a connected space into `ℂ` with values in `Λ` takes a single value. -/
theorem eq_of_mem_lattice {Z : Type*} [TopologicalSpace Z] [PreconnectedSpace Z] {g : Z → ℂ}
    (hg : Continuous g) (hΛ : ∀ z, g z ∈ L.lattice) (a b : Z) : g a = g b := by
  let g' : Z → L.lattice := fun z => ⟨g z, hΛ z⟩
  have hg' : Continuous g' := hg.subtype_mk _
  have := (isPreconnected_range hg').subsingleton ⟨a, rfl⟩ ⟨b, rfl⟩
  exact congrArg Subtype.val this

theorem line_injective : Function.Injective (line (L := L)) := by
  intro c c' h
  have hΛ : ∀ t : ℝ, (t : ℂ) * c - (t : ℂ) * c' ∈ L.lattice := fun t => by
    rw [← mk_eq_mk]
    exact DFunLike.congr_fun h t
  have := eq_of_mem_lattice (Z := ℝ) (by fun_prop) hΛ 1 0
  simpa [sub_eq_zero] using this

/-- `mk : ℂ → T_Λ` is a covering map. -/
theorem isCoveringMap_mk : IsCoveringMap (mk L) := by
  have : DiscreteTopology L.lattice.toAddSubgroup := (inferInstance : DiscreteTopology L.lattice)
  exact (AddSubgroup.isAddQuotientCoveringMap_of_comm _ DiscreteTopology.isDiscrete).isCoveringMap

/-- **Every one-parameter subgroup of `T_Λ` is a line `t ↦ mk (t c)`.** -/
theorem exists_line (f : Lie (Torus L)) : ∃ c, line c = f := by
  obtain ⟨F, ⟨hF0, hFf⟩, -⟩ := isCoveringMap_mk.existsUnique_continuousMap_lifts
    (⟨f, f.continuous⟩ : C(ℝ, Torus L)) 0 0 (by simp [mk_zero])
  have hF : ∀ t, mk L (F t) = f t := fun t => congrFun hFf t
  have hadd : ∀ s t, F (s + t) = F s + F t := by
    intro s t
    have hΛ : ∀ q : ℝ × ℝ, F (q.1 + q.2) - F q.1 - F q.2 ∈ L.lattice := by
      intro q
      rw [← mk_eq_zero]
      have e : mk L (F (q.1 + q.2) - F q.1 - F q.2) = f (q.1 + q.2) - f q.1 - f q.2 := by
        rw [← hF, ← hF, ← hF]
        simp [mk, QuotientAddGroup.mk_sub]
      rw [e, map_add]
      abel
    have := eq_of_mem_lattice (Z := ℝ × ℝ) (by fun_prop) hΛ (s, t) (0, 0)
    simp only [add_zero, hF0, sub_self] at this
    linear_combination this
  let Fh : ℝ →+ ℂ := ⟨⟨F, by simpa using hF0⟩, hadd⟩
  refine ⟨F 1, ?_⟩
  ext t
  have : F t = t • F 1 := by
    have := map_real_smul Fh F.continuous t 1
    simpa [Fh] using this
  rw [line_apply, ← hF, this, Complex.real_smul]

/-- **The one-parameter subgroups of `T_Λ` form a real vector space isomorphic to `ℂ`.** -/
noncomputable def lieEquiv : ℂ ≃ₗ[ℝ] Lie (Torus L) :=
  LinearEquiv.ofBijective
    { toFun := line
      map_add' := line_add
      map_smul' := line_smul }
    ⟨line_injective, fun f => exists_line f⟩

@[simp]
theorem lieEquiv_apply (c : ℂ) : lieEquiv (L := L) c = line c := rfl


/-! ### Topology -/

/-- **The lattice is uniformly discrete**: some ball around `0` meets `Λ` only in `0`. -/
theorem exists_sep (L : PeriodPair) :
    ∃ r > 0, ∀ l ∈ L.lattice, l ≠ 0 → r ≤ ‖l‖ := by
  have h0 : IsOpen ({0} : Set L.lattice) := isOpen_discrete _
  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.1 h0
  have h0t : (0 : ℂ) ∈ t := by
    have : (0 : L.lattice) ∈ Subtype.val ⁻¹' t := by rw [hteq]; rfl
    exact this
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 ht 0 h0t
  refine ⟨r, hr, fun l hl hl0 => ?_⟩
  by_contra hlt
  have hlt := lt_of_not_ge hlt
  have hlt' : (⟨l, hl⟩ : L.lattice) ∈ Subtype.val ⁻¹' t :=
    hball (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
  rw [hteq] at hlt'
  exact hl0 (congrArg Subtype.val hlt')

theorem continuous_line : Continuous (line (L := L)) := by
  refine (ContinuousAddMonoidHom.isInducing_toContinuousMap ℝ (Torus L)).continuous_iff.2 ?_
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  change Continuous fun p : ℂ × ℝ => mk L ((p.2 : ℂ) * p.1)
  exact continuous_mk.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_fst)

/-- If `t ↦ mk (t c)` maps `[0, 1]` into `mk (B(0, δ))` with `δ` less than a third of the
separation of `Λ`, then `‖c‖ < δ`. -/
theorem norm_lt_of_mapsTo {r δ : ℝ} (hr : ∀ l ∈ L.lattice, l ≠ 0 → r ≤ ‖l‖) (hδ : 3 * δ < r)
    {c : ℂ} (hc : MapsTo (line (L := L) c) (Icc 0 1) (mk L '' Metric.ball 0 δ)) : ‖c‖ < δ := by
  let S : Set ℂ := (fun t : ℝ => (t : ℂ) * c) '' Icc 0 1
  have hS : IsPreconnected S :=
    (isPreconnected_Icc).image _ (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * c).continuousOn
  have hsub : S ⊆ Metric.ball 0 δ ∪ {z | δ < ‖z‖} := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨w, hw, hwt⟩ := hc ht
    rw [line_apply, mk_eq_mk] at hwt
    rw [Metric.mem_ball, dist_zero_right] at hw
    by_cases hl : w - (t : ℂ) * c = 0
    · left
      change (t : ℂ) * c ∈ Metric.ball 0 δ
      rw [← sub_eq_zero.1 hl, Metric.mem_ball, dist_zero_right]
      exact hw
    · right
      have h1 := hr _ hwt hl
      have h2 : ‖w - (t : ℂ) * c‖ ≤ ‖w‖ + ‖(t : ℂ) * c‖ := norm_sub_le _ _
      change δ < ‖(t : ℂ) * c‖
      have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hw.le
      linarith
  have hdisj : Disjoint (Metric.ball (0 : ℂ) δ) {z | δ < ‖z‖} := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact lt_asymm hz hz'
  have hδ0 : 0 < δ := by
    obtain ⟨w, hw, -⟩ := hc ⟨le_refl (0 : ℝ), zero_le_one⟩
    exact lt_of_le_of_lt (norm_nonneg _) (by simpa [dist_zero_right] using hw)
  have hne : (S ∩ Metric.ball 0 δ).Nonempty :=
    ⟨0, ⟨0, ⟨le_refl _, zero_le_one⟩, by simp⟩, by simpa using hδ0⟩
  have := IsPreconnected.subset_left_of_subset_union Metric.isOpen_ball
    (isOpen_lt continuous_const continuous_norm) hdisj hsub hne hS
  have hc1 : c ∈ S := ⟨1, ⟨zero_le_one, le_refl _⟩, by simp⟩
  simpa [dist_zero_right] using this hc1

theorem continuous_lieEquiv_symm : Continuous (lieEquiv (L := L)).symm := by
  obtain ⟨r, hr0, hr⟩ := exists_sep L
  let φ : Lie (Torus L) →+ ℂ := (lieEquiv (L := L)).symm.toLinearMap.toAddMonoidHom
  change Continuous φ
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  set δ := min ε (r / 4) with hδ
  have hδ0 : 0 < δ := lt_min hε (by positivity)
  have hN : IsOpen {f : Lie (Torus L) | MapsTo f (Icc 0 1) (mk L '' Metric.ball 0 δ)} := by
    have := ContinuousMap.isOpen_setOf_mapsTo (X := ℝ) (Y := Torus L) (K := Icc (0 : ℝ) 1)
      (U := mk L '' Metric.ball 0 δ) isCompact_Icc
      (isOpenMap_mk _ Metric.isOpen_ball)
    exact this.preimage (ContinuousAddMonoidHom.isInducing_toContinuousMap ℝ (Torus L)).continuous
  have h0 : (0 : Lie (Torus L)) ∈
      {f : Lie (Torus L) | MapsTo f (Icc 0 1) (mk L '' Metric.ball 0 δ)} :=
    fun t _ => ⟨0, by simpa using hδ0, by simp [mk_zero]⟩
  filter_upwards [hN.mem_nhds h0] with f hf
  have hf' : line (L := L) (φ f) = f := (lieEquiv (L := L)).apply_symm_apply f
  rw [← hf'] at hf
  have := norm_lt_of_mapsTo hr (by rw [hδ]; linarith [min_le_right ε (r / 4)]) hf
  rw [dist_zero_right]
  exact lt_of_lt_of_le this (min_le_left _ _)

/-- **The one-parameter subgroups of `T_Λ` form a space homeomorphic to `ℂ`.** -/
noncomputable def lieHomeo : ℂ ≃ₜ Lie (Torus L) where
  toEquiv := (lieEquiv (L := L)).toEquiv
  continuous_toFun := continuous_line
  continuous_invFun := continuous_lieEquiv_symm

end Torus

end Ell

end AutHol

end Iut
