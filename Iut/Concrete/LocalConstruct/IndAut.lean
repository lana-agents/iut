/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.LogShell
import Iut.Concrete.LocalConstruct.ArchPrimitive

/-!
# The indeterminacy automorphisms of the tensor packets (IUT IV, Propositions 1.2, 1.5)

The indeterminacies (Ind1), (Ind2) act on a packet `⊗_j K_{c j}` through the automorphisms `φ`
of IUT IV, Proposition 1.2: at a prime `p`, **every** automorphism of the finite-dimensional
`ℚ_p`-vector space `log_p(R_I^×) ⊗ ℚ_p` (the packet) that induces an automorphism of the
submodule `log_p(R_I^×) = ⊗_{ℤ_p} log_p(R_i^×)`. Since the factor log-shells are
`𝓘_i = (2p)⁻¹·log_p(R_i^×)`, the lattice `log_p(R_I^×)` is `(2p)^{|I|}` times the tensor
product of the log-shells `⊗_j 𝓘_{c j}` (`tensorLogShell`), and a linear automorphism preserves
one iff it preserves the other. So the class is

`indAut (.finite p) c = {φ | φ is a ℚ_p-linear automorphism with φ(⊗_j 𝓘_{c j}) = ⊗_j 𝓘_{c j}}`.

These are not ring homomorphisms; they contain the Galois automorphisms `⊗_j σ_j` (`galAut`),
but are much larger (an open compact subgroup `≅ GL_n(ℤ_p)`). At the archimedean place the class
is `primAut` (IUT IV, Proposition 1.5): the maps induced by the primitive automorphisms of the
factors (complex conjugation and multiplication by `±1`, `±√−1`), which preserve `B_I`.

This file proves that `indAut` contains the identity, consists of continuous maps, and that the
union of the images of a bounded open region is admissible (it lies in a scaled lattice
`p^{-k}·⊗_j 𝓘_{c j}`, which is bounded).
-/

namespace Iut

namespace LocalConstruct

open NumberField MeasureTheory
open scoped TensorProduct Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]

section Finite

variable (p : Nat.Primes) (c : ι → Place K)

/-- **The lattice automorphisms of a packet at a prime** (IUT IV, Proposition 1.2): the
`ℚ_p`-linear automorphisms of the packet preserving `⊗_j 𝓘_{c j}`. -/
def latticeAut : Set (Tensor K (.finite p) c → Tensor K (.finite p) c) :=
  {φ | ∃ e : Tensor K (.finite p) c ≃ₗ[ℚ_[p]] Tensor K (.finite p) c,
    ⇑e = φ ∧ e '' tensorLogShell p c = tensorLogShell p c}

lemma id_mem_latticeAut : id ∈ latticeAut p c :=
  ⟨LinearEquiv.refl _ _, rfl, by simp⟩

variable {p c}

lemma continuous_of_mem_latticeAut {φ : Tensor K (.finite p) c → Tensor K (.finite p) c}
    (hφ : φ ∈ latticeAut p c) : Continuous φ := by
  obtain ⟨e, rfl, -⟩ := hφ
  exact LinearMap.continuous_of_finiteDimensional e.toLinearMap

/-- A lattice automorphism maps the scaled lattice `t • ⊗_j 𝓘_{c j}` onto itself. -/
lemma image_smul_tensorLogShell {φ : Tensor K (.finite p) c → Tensor K (.finite p) c}
    (hφ : φ ∈ latticeAut p c) (t : ℚ_[p]) :
    φ '' (t • tensorLogShell p c) = t • tensorLogShell p c := by
  obtain ⟨e, rfl, he⟩ := hφ
  ext x
  simp only [Set.mem_image, Set.mem_smul_set]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have : e y ∈ tensorLogShell p c := he ▸ ⟨y, hy, rfl⟩
    exact ⟨e y, this, (map_smul e t y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    rw [← he] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨t • y', ⟨y', hy', rfl⟩, map_smul e t y'⟩

variable (p c)

/-- A bounded set lies in a scaled lattice `(p^k)⁻¹ • ⊗_j 𝓘_{c j}`. -/
lemma exists_subset_inv_pow_smul_tensorLogShell {S : Set (Tensor K (.finite p) c)}
    (hS : Bornology.IsBounded S) :
    ∃ k : ℕ, S ⊆ (((p : ℕ) : ℚ_[p]) ^ k)⁻¹ • tensorLogShell p c := by
  obtain ⟨r, hr, hball⟩ := exists_closedBall_subset_order p c
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hS
  have hp1 : ‖((p : ℕ) : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
  have hp0 : 0 < ‖((p : ℕ) : ℚ_[p])‖ := by
    rw [Padic.norm_p]; exact inv_pos.mpr (by exact_mod_cast p.2.pos)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hr (lt_max_of_lt_right one_pos :
    (0 : ℝ) < max R 1)) hp1
  refine ⟨k, fun x hx => ?_⟩
  have hpk : (((p : ℕ) : ℚ_[p]) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast p.2.ne_zero)
  refine ⟨((p : ℕ) : ℚ_[p]) ^ k • x, ?_, by
    change (((p : ℕ) : ℚ_[p]) ^ k)⁻¹ • (((p : ℕ) : ℚ_[p]) ^ k • x) = x
    rw [smul_smul, inv_mul_cancel₀ hpk, one_smul]⟩
  apply order_subset_tensorLogShell p c
  apply hball
  have hxR : ‖x‖ ≤ max R 1 := by
    have := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_pow]
  calc ‖((p : ℕ) : ℚ_[p])‖ ^ k * ‖x‖ ≤ ‖((p : ℕ) : ℚ_[p])‖ ^ k * max R 1 :=
        mul_le_mul_of_nonneg_left hxR (pow_nonneg hp0.le _)
    _ ≤ r / max R 1 * max R 1 :=
        mul_le_mul_of_nonneg_right hk.le (le_trans zero_le_one (le_max_right _ _))
    _ = r := div_mul_cancel₀ _ (lt_max_of_lt_right one_pos).ne'

/-- The tensor product of the log-shells is bounded. -/
lemma isBounded_tensorLogShell : Bornology.IsBounded (tensorLogShell p c) :=
  (isBounded_logShell p c).subset (tensorLogShell_subset_logShell p c)

/-- **The union of the images of a bounded set under the lattice automorphisms is
bounded**: it lies in `(p^k)⁻¹ • ⊗_j 𝓘_{c j}`. -/
theorem isBounded_iUnion_latticeAut {S : Set (Tensor K (.finite p) c)}
    (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (⋃ φ ∈ latticeAut p c, φ '' S) := by
  obtain ⟨k, hk⟩ := exists_subset_inv_pow_smul_tensorLogShell p c hS
  refine ((isBounded_tensorLogShell p c).smul₀ ((((p : ℕ) : ℚ_[p]) ^ k)⁻¹)).subset ?_
  refine Set.iUnion₂_subset fun φ hφ => ?_
  rw [← image_smul_tensorLogShell hφ]
  exact Set.image_mono hk

/-- **The union of the images of a bounded open set of positive measure under the lattice
automorphisms is admissible.** -/
theorem iUnion_latticeAut_admissible {S : Set (Tensor K (.finite p) c)}
    (hb : Bornology.IsBounded S) (ho : IsOpen S) (hpos : 0 < haar (.finite p) c S) :
    (⋃ φ ∈ latticeAut p c, φ '' S) ∈ admissible (.finite p) c := by
  have hsub : S ⊆ ⋃ φ ∈ latticeAut p c, φ '' S := fun x hx =>
    Set.mem_iUnion₂.mpr ⟨id, id_mem_latticeAut p c, ⟨x, hx, rfl⟩⟩
  have hB := isBounded_iUnion_latticeAut p c hb
  have hopen : IsOpen (⋃ φ ∈ latticeAut p c, φ '' S) := by
    refine isOpen_biUnion fun φ hφ => ?_
    obtain ⟨e, rfl, -⟩ := hφ
    exact (LinearEquiv.toContinuousLinearEquiv e).toHomeomorph.isOpenMap S ho
  refine ⟨?_, hB.isCompact_closure, hopen.measurableSet,
    lt_of_lt_of_le hpos (measure_mono hsub), ?_⟩
  · obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
    exact ⟨x, hsub hx⟩
  · exact lt_of_le_of_lt (measure_mono subset_closure) hB.isCompact_closure.measure_lt_top

/-- The union of the images of a scaled integral structure `s·(R_I)^∼` (`s` a unit) under the
lattice automorphisms is admissible. -/
theorem latticeAut_theta_admissible (s : Tensor K (.finite p) c) (hs : IsUnit s) :
    (⋃ φ ∈ latticeAut p c, φ '' (s • integral p c)) ∈ admissible (.finite p) c := by
  refine iUnion_latticeAut_admissible p c ?_ ?_ (haar_smul_integralAt_pos (vQ := .finite p) hs)
  · exact (isCompact_smul_integralAt (vQ := .finite p) (c := c) s).isBounded
  · exact isOpen_smul_of_isUnit (vQ := .finite p) hs (isOpen_integral p c)

/-- The union of the images of the log-shell `𝓘_I` under the lattice automorphisms is
admissible. -/
theorem latticeAut_thetaShell_admissible :
    (⋃ φ ∈ latticeAut p c, φ '' logShell p c) ∈ admissible (.finite p) c :=
  iUnion_latticeAut_admissible p c (isBounded_logShell p c) (isOpen_logShell p c)
    (haar_logShell_pos p c)

end Finite

/-! ### The indeterminacy automorphisms, uniformly in the rational place -/

variable (vQ : RationalPlace) (c : ι → Place K)

/-- **The indeterminacy automorphisms** of a packet (`LocalTheory.indAut`; IUT IV,
Propositions 1.2 and 1.5): the lattice automorphisms at a prime, the primitive automorphisms at
the archimedean place. -/
def indAut : ∀ (vQ : RationalPlace) (c : ι → Place K), Set (Tensor K vQ c → Tensor K vQ c)
  | .finite p, c => latticeAut p c
  | .infinite, c => primAut c

lemma indAut_finite_eq (p : Nat.Primes) : indAut (.finite p) c = latticeAut p c := rfl

lemma indAut_infinite_eq : indAut .infinite c = primAut c := rfl

lemma id_mem_indAut : id ∈ indAut vQ c := by
  cases vQ with
  | finite p => exact id_mem_latticeAut p c
  | infinite => exact id_mem_primAut c

/-- **`LocalTheory.theta_admissible`**: the union of the images of a scaled integral
structure under the indeterminacy automorphisms is admissible. -/
theorem theta_admissible (s : Tensor K vQ c) (hs : IsUnit s) :
    (⋃ φ ∈ indAut vQ c, φ '' (s • integralAt vQ c)) ∈ admissible vQ c := by
  cases vQ with
  | finite p => exact latticeAut_theta_admissible p c s hs
  | infinite => exact primAut_theta_admissible c s hs

end LocalConstruct

end Iut
