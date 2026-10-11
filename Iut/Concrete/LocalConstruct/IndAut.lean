/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.LogShell
import Iut.Concrete.LocalConstruct.ArchPrimitive

/-!
# The indeterminacy automorphisms of the tensor packets (IUT III, Theorem 3.11; IUT IV, 1.2, 1.5)

The indeterminacy (Ind2) of IUT III, Theorem 3.11 acts on a tensor packet
`⊗_{j ∈ S} (⊕_{v ∣ v_ℚ} K_v)` through *independent copies of `Ism`* — the automorphisms of the
`ℤ_p`-modules `log_p(𝓞_v^×)`, equivalently of the log-shells `𝓘_v = (2p)⁻¹·log_p(𝓞_v^×)` —
*on each direct summand of each tensor factor*. On the tuple component `⊗_j K_{c j}` of the
packet this is the class `tensorAut p c` of tensor products `⊗_j g_j` with `g_j` a
`ℚ_p`-linear automorphism of `K_{c j}` preserving `𝓘_{c j}` (`factorAut`). The field
automorphisms of the factors (part of (Ind1)) preserve the log-shells and are among them.

The class `latticeAut p c` of *all* `ℚ_p`-linear automorphisms preserving `⊗_j 𝓘_j`, the
automorphisms `φ` of IUT IV, Proposition 1.2, is much larger; it is used here only as an
auxiliary class (`tensorAut_subset_latticeAut`): its members are continuous, and the union of
the images of a bounded set lies in a scaled lattice `p^{-k}·⊗_j 𝓘_{c j}`, hence is bounded.

At the archimedean place the class is `primAut` (`ArchPrimitive.lean`).
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

/-- The tensor product of the log-shells is open (an additive subgroup containing a ball). -/
lemma isOpen_tensorLogShell : IsOpen (tensorLogShell p c) := by
  obtain ⟨r, hr, hsub⟩ := exists_closedBall_subset_order p c
  let G : AddSubgroup (Tensor K (.finite p) c) :=
    (Submodule.span ℤ_[p] (logShellSet p c)).toAddSubgroup
  change IsOpen (G : Set (Tensor K (.finite p) c))
  exact AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 hr)
    (hsub.trans (order_subset_tensorLogShell p c)))

/-- The tensor product of the log-shells is bounded. -/
lemma isBounded_tensorLogShell : Bornology.IsBounded (tensorLogShell p c) :=
  (isBounded_logShell p c).subset (tensorLogShell_subset_logShell p c)

/-- Scaled tensor products of log-shells `s·⊗_j 𝓘_j` (`s` a unit) are bounded open sets of
positive Haar measure. -/
lemma smul_tensorLogShell_bounded_open_pos (s : Tensor K (.finite p) c) (hs : IsUnit s) :
    Bornology.IsBounded (s • tensorLogShell p c) ∧ IsOpen (s • tensorLogShell p c) ∧
      0 < haar (.finite p) c (s • tensorLogShell p c) := by
  have ho : IsOpen (s • tensorLogShell p c) :=
    isOpen_smul_of_isUnit (vQ := .finite p) hs (isOpen_tensorLogShell p c)
  refine ⟨?_, ho, ho.measure_pos _ ⟨s • 0, Set.smul_mem_smul_set
    (Submodule.zero_mem (Submodule.span ℤ_[p] (logShellSet p c)))⟩⟩
  have hcont : Continuous fun z : Tensor K (.finite p) c => s * z :=
    continuous_const.mul continuous_id
  rw [smul_set_eq_image]
  exact (((isBounded_tensorLogShell p c).isCompact_closure.image hcont).isBounded).subset
    (Set.image_mono subset_closure)

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

/-! ### The indeterminacy (Ind2) of IUT III, Theorem 3.11: tensor products of `Ism`-actions -/

variable {p c} in
/-- A `ℚ_p`-linear automorphism of the packet maps `⊗_j 𝓘_j` into itself as soon as it maps
the elementary tensors of log-shell elements into `⊗_j 𝓘_j`. -/
lemma image_tensorLogShell_subset (e : Tensor K (.finite p) c ≃ₗ[ℚ_[p]] Tensor K (.finite p) c)
    (he : ∀ x ∈ logShellSet p c, e x ∈ tensorLogShell p c) :
    e '' tensorLogShell p c ⊆ tensorLogShell p c := by
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact he x hx
  | zero => rw [map_zero]; exact (Submodule.span ℤ_[p] _).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (Submodule.span ℤ_[p] _).add_mem hx hy
  | smul r x _ hx =>
    rw [padicInt_smul_def, map_smul, ← padicInt_smul_def]
    exact (Submodule.span ℤ_[p] _).smul_mem r hx

/-- **The `Ism`-indeterminacy of a factor** (IUT III, Proposition 1.2(vi) and Theorem
3.11 (Ind2); for `v` over `p`): the automorphisms of the `ℤ_p`-module `𝓘_v`
(equivalently of `log_p(𝓞_v^×)`), extended `ℚ_p`-linearly to `K_v`. -/
def factorAut (v : Place K) : Set (Factor K p v ≃ₗ[ℚ_[p]] Factor K p v) :=
  {g | g '' factorLogShell p v = factorLogShell p v}

/-- **The indeterminacy automorphisms of a packet at a prime** (IUT III, Theorem 3.11,
(Ind2)): the tensor products `⊗_j g_j` of independent automorphisms `g_j ∈ Ism` of the log-shells
of the factors (one for each direct summand of each tensor factor; in the tuple component
`⊗_j K_{c j}` of the packet these act through the summands `K_{c j}`). The automorphisms of the
factors as fields (part of (Ind1)) preserve the log-shells, hence are among them. -/
def tensorAut : Set (Tensor K (.finite p) c → Tensor K (.finite p) c) :=
  {φ | ∃ g : ∀ j, Factor K p (c j) ≃ₗ[ℚ_[p]] Factor K p (c j),
    (∀ j, g j ∈ factorAut p (c j)) ∧ ⇑(PiTensorProduct.congr g) = φ}

variable {p c} in
lemma congr_mem_logShellSet {g : ∀ j, Factor K p (c j) ≃ₗ[ℚ_[p]] Factor K p (c j)}
    (hg : ∀ j, g j '' factorLogShell p (c j) ⊆ factorLogShell p (c j))
    {x : Tensor K (.finite p) c} (hx : x ∈ logShellSet p c) :
    PiTensorProduct.congr g x ∈ logShellSet p c := by
  obtain ⟨b, rfl⟩ := hx
  rw [PiTensorProduct.congr_tprod]
  exact ⟨fun j => ⟨g j (b j), hg j ⟨_, (b j).2, rfl⟩⟩, rfl⟩

/-- The tensor products of `Ism`-automorphisms are lattice automorphisms. -/
theorem tensorAut_subset_latticeAut : tensorAut p c ⊆ latticeAut p c := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨PiTensorProduct.congr g, rfl, Set.Subset.antisymm ?_ ?_⟩
  · exact image_tensorLogShell_subset _ fun x hx =>
      Submodule.subset_span (congr_mem_logShellSet (fun j => (hg j).le) hx)
  · intro x hx
    have hsymm : ∀ j, (g j).symm '' factorLogShell p (c j) ⊆ factorLogShell p (c j) := by
      intro j y hy
      have := (hg j).symm ▸ hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [← (hg j)] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      simpa using hw
    have hs : (PiTensorProduct.congr g).symm '' tensorLogShell p c ⊆ tensorLogShell p c := by
      refine image_tensorLogShell_subset _ fun y hy => Submodule.subset_span ?_
      obtain ⟨b, rfl⟩ := hy
      rw [PiTensorProduct.congr_symm_tprod]
      exact ⟨fun j => ⟨(g j).symm (b j), hsymm j ⟨_, (b j).2, rfl⟩⟩, rfl⟩
    exact ⟨(PiTensorProduct.congr g).symm x, hs ⟨x, hx, rfl⟩, by simp⟩

lemma id_mem_tensorAut : id ∈ tensorAut p c :=
  ⟨fun _ => LinearEquiv.refl _ _, fun _ => by simp [factorAut], by
    ext x
    change PiTensorProduct.congr (fun _ => LinearEquiv.refl _ _) x = x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r m => rw [map_smul, PiTensorProduct.congr_tprod]; rfl
    | add x y hx hy => rw [map_add, hx, hy]⟩

/-- The union of the images of a bounded open set of positive measure under the tensor
products of `Ism`-automorphisms is admissible. -/
theorem iUnion_tensorAut_admissible {S : Set (Tensor K (.finite p) c)}
    (hb : Bornology.IsBounded S) (ho : IsOpen S) (hpos : 0 < haar (.finite p) c S) :
    (⋃ φ ∈ tensorAut p c, φ '' S) ∈ admissible (.finite p) c := by
  have hsub : S ⊆ ⋃ φ ∈ tensorAut p c, φ '' S := fun x hx =>
    Set.mem_iUnion₂.mpr ⟨id, id_mem_tensorAut p c, ⟨x, hx, rfl⟩⟩
  have hB : Bornology.IsBounded (⋃ φ ∈ tensorAut p c, φ '' S) :=
    (isBounded_iUnion_latticeAut p c hb).subset (Set.biUnion_subset_biUnion_left
      (tensorAut_subset_latticeAut p c))
  have hopen : IsOpen (⋃ φ ∈ tensorAut p c, φ '' S) := by
    refine isOpen_biUnion fun φ hφ => ?_
    obtain ⟨e, rfl, -⟩ := tensorAut_subset_latticeAut p c hφ
    exact (LinearEquiv.toContinuousLinearEquiv e).toHomeomorph.isOpenMap S ho
  refine ⟨?_, hB.isCompact_closure, hopen.measurableSet,
    lt_of_lt_of_le hpos (measure_mono hsub), ?_⟩
  · obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
    exact ⟨x, hsub hx⟩
  · exact lt_of_le_of_lt (measure_mono subset_closure) hB.isCompact_closure.measure_lt_top

/-- The union of the images of the log-shell `𝓘_I` under the indeterminacy automorphisms at a
prime is admissible. -/
theorem tensorAut_thetaShell_admissible :
    (⋃ φ ∈ tensorAut p c, φ '' logShell p c) ∈ admissible (.finite p) c :=
  iUnion_tensorAut_admissible p c (isBounded_logShell p c) (isOpen_logShell p c)
    (haar_logShell_pos p c)

end Finite

/-! ### The indeterminacy automorphisms, uniformly in the rational place -/

variable (vQ : RationalPlace) (c : ι → Place K)

/-- **The indeterminacy automorphisms** of a packet (`LocalTheory.indAut`; IUT IV,
Propositions 1.2 and 1.5): the lattice automorphisms at a prime, the primitive automorphisms at
the archimedean place. -/
def indAut : ∀ (vQ : RationalPlace) (c : ι → Place K), Set (Tensor K vQ c → Tensor K vQ c)
  | .finite p, c => tensorAut p c
  | .infinite, c => primAut c

lemma indAut_finite_eq (p : Nat.Primes) : indAut (.finite p) c = tensorAut p c := rfl

lemma indAut_infinite_eq : indAut .infinite c = primAut c := rfl

lemma id_mem_indAut : id ∈ indAut vQ c := by
  cases vQ with
  | finite p => exact id_mem_tensorAut p c
  | infinite => exact id_mem_primAut c

/-- **`LocalTheory.theta_admissible`**: the union of the images of a scaled integral
structure under the indeterminacy automorphisms is admissible. -/
theorem theta_admissible (s : Tensor K vQ c) (hs : IsUnit s) :
    (⋃ φ ∈ indAut vQ c, φ '' (s • integralAt vQ c)) ∈ admissible vQ c := by
  cases vQ with
  | finite p =>
    exact iUnion_tensorAut_admissible p c
      (isCompact_smul_integralAt (vQ := .finite p) (c := c) s).isBounded
      (isOpen_smul_of_isUnit (vQ := .finite p) hs (isOpen_integral p c))
      (haar_smul_integralAt_pos (vQ := .finite p) hs)
  | infinite => exact primAut_theta_admissible c s hs

end LocalConstruct

end Iut
