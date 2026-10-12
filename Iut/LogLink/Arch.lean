/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Local
import Iut.Concrete.LocalConstruct.ArchLogShell
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Archimedean log-links (IUT III, Definition 1.1(ii), Propositions 1.2(vii), 3.5(ii)(b))

At `v ∈ V^arc` the local field is `ℂ`. IUT III, Definition 1.1(ii), constructs the log-link from
the **universal covering** `Ψ^∼ ↠ Ψ^gp` of the multiplicative group (regarded as a pointed
universal covering of `Ψ^gp/μ_N`), on which the complex logarithm defines a field structure. In the
model:

* the universal covering is `exp : (ℂ, +) → ℂˣ`, with deck transformations `2πiℤ`
  (`Complex.exp_eq_one_iff`);
* a **local archimedean log-link** (`ArchLogLink`) is the principal logarithm on the domain
  followed by a continuous ring automorphism `φ` of `ℂ` (the poly-isomorphism `log(†F_v) ≅ ‡F_v`;
  `φ` is the identity or complex conjugation, `norm_ringEquiv`).

## Results

* **The log-link is a homomorphism up to the deck transformations** (`log_mul_sub_mem`, Proposition
  1.2(ii) at `v ∈ V^arc`): `log(uv) − log u − log v ∈ 2πiℤ`; on roots of unity it takes values in
  the deck group of the covering of `Ψ^gp/μ_N` (`natCast_mul_log_root`, Definition 1.1(ii): the
  quotient by `Ψ^{μ_N}`); `exp ∘ φ⁻¹` inverts it on `ℂˣ` (`exp_symm_toFun`).
* **The archimedean log-shell** (Proposition 1.2(vii)): the images of the units lie in the closed
  disc of radius `π` (`norm_log_le_pi`, `toFun_mem_closedBall`), which is preserved by the
  Kummer isomorphisms (`image_closedBall`) and by the order-two automorphisms `z ↦ −z`, `z ↦ z̄` of
  (Ind2) at `v ∈ V^arc`; these are induced by the inversion and the conjugation of the units
  (`exp_neg_log`, `exp_conj_log`).
* **Kummer non-compatibility** (`not_ringHom_eq_toFun`, Proposition 1.2(iv)).
* **Vertical lines** (`ArchColumn`) and **upper semi-compatibility at `v ∈ V^arc`** (Proposition
  3.5(ii)(b); Theorem 3.11(ii), (Ind3)): the Kummer images of the units and of the closed balls of
  radius `π` of every level lie in the coric closed ball of radius `π` (`upperSemiCompat`); and for
  every `m' ≥ 1` the closed ball of level `m + m'` contains the subset `itF m' m '' iterDom m' m`
  (the values of the `m'`-th iterate of the log-links) which **surjects, by the inverse of the
  iterate, onto the units of level `m` on which this iterate is defined** (`itF_mem_closedBall`,
  `back_itF`): the surjection "`↠`" of (Ind3) at `v_ℚ ∈ V_ℚ^arc`. The totality of the Kummer images
  (`logKummer`) lies in the coric ball and is invariant under translation (`logKummer_shift`).
* **Tensor packets** (Proposition 3.5(ii)(b) for the packets `⊗_j K_{v_j}` of
  `Iut.LocalConstruct`): the tensor products of Kummer images (automorphisms of the factors) of
  elements of the closed discs of radius `π` lie in the archimedean log-shell `archLogShell` of the
  packet, the closed unit ball of the tensor-product Hermitian metric
  (`tprod_mem_archLogShell`, `tprod_log_mem_archLogShell`).
-/

namespace Iut

namespace LogLink

open Complex Metric
open scoped ComplexConjugate

noncomputable section

/-- **Continuous ring automorphisms of `ℂ` are isometries** (the identity or the complex
conjugation). -/
theorem norm_ringEquiv (τ : ℂ ≃+* ℂ) (h : Continuous τ) (z : ℂ) : ‖τ z‖ = ‖z‖ := by
  rcases Complex.ringHom_eq_id_or_conj_of_continuous (f := τ.toRingHom) h with e | e
  · have := RingHom.congr_fun e z
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply] at this
    rw [this]
  · have := RingHom.congr_fun e z
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, Complex.norm_conj]

/-- Continuous ring automorphisms of `ℂ` preserve the closed balls around `0`. -/
theorem image_closedBall (τ : ℂ ≃+* ℂ) (h : Continuous τ) (r : ℝ) :
    τ '' closedBall (0 : ℂ) r = closedBall 0 r := by
  ext y
  simp only [Set.mem_image, mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [norm_ringEquiv τ h]
  · intro hy
    refine ⟨τ.symm y, ?_, τ.apply_symm_apply y⟩
    rwa [← norm_ringEquiv τ h, τ.apply_symm_apply]

/-- **The logarithm of a unit has norm at most `π`**: `log u = i·arg u` for `‖u‖ = 1`. -/
theorem norm_log_le_pi {u : ℂ} (hu : ‖u‖ = 1) : ‖Complex.log u‖ ≤ Real.pi := by
  have h : Complex.log u = (arg u : ℂ) * I := by
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, hu]
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact abs_arg_le_pi u

/-- **The log-link is a homomorphism up to the deck transformations** `2πiℤ` of the universal
covering `exp : ℂ → ℂˣ`. -/
theorem log_mul_sub_mem {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ n : ℤ, Complex.log (u * v) - Complex.log u - Complex.log v = n * (2 * Real.pi * I) := by
  rw [← Complex.exp_eq_one_iff, Complex.exp_sub, Complex.exp_sub, Complex.exp_log hu,
    Complex.exp_log hv, Complex.exp_log (mul_ne_zero hu hv)]
  field_simp

/-- **Roots of unity go to the deck group of the covering of `Ψ^gp/μ_N`** (IUT III,
Definition 1.1(ii)): `N·log ζ ∈ 2πiℤ` for `ζ^N = 1`. -/
theorem natCast_mul_log_root {ζ : ℂ} {N : ℕ} (h : ζ ^ N = 1) :
    ∃ n : ℤ, (N : ℂ) * Complex.log ζ = n * (2 * Real.pi * I) := by
  by_cases hζ : ζ = 0
  · subst hζ
    exact ⟨0, by simp⟩
  rw [← Complex.exp_eq_one_iff, Complex.exp_nat_mul, Complex.exp_log hζ, h]

/-- The order-two automorphism `z ↦ −z` of (Ind2) at `v ∈ V^arc` is induced by the inversion of
the units. -/
theorem exp_neg_log {u : ℂ} (hu : u ≠ 0) : Complex.exp (-Complex.log u) = u⁻¹ := by
  rw [Complex.exp_neg, Complex.exp_log hu]

/-- The order-two automorphism `z ↦ z̄` of (Ind2) at `v ∈ V^arc` is induced by the conjugation of
the units. -/
theorem exp_conj_log {u : ℂ} (hu : u ≠ 0) : Complex.exp (conj (Complex.log u)) = conj u := by
  rw [Complex.exp_conj, Complex.exp_log hu]

/-- The order-two automorphisms `z ↦ −z`, `z ↦ z̄` preserve the archimedean log-shell. -/
theorem neg_conj_mem_closedBall {y : ℂ} (hy : y ∈ closedBall (0 : ℂ) Real.pi) :
    -y ∈ closedBall (0 : ℂ) Real.pi ∧ conj y ∈ closedBall (0 : ℂ) Real.pi := by
  simp only [mem_closedBall, dist_zero_right, norm_neg, Complex.norm_conj] at hy ⊢
  exact ⟨hy, hy⟩

/-! ### Archimedean log-links -/

/-- **A local archimedean log-link** `†F_v → ‡F_v` (IUT III, Definition 1.1(ii)): the logarithm
on the universal covering of the domain, followed by the poly-isomorphism `log(†F_v) ≅ ‡F_v`,
modelled by a continuous ring automorphism `φ` of `ℂ`. -/
structure ArchLogLink where
  /-- The isomorphism `log(†F_v) ≅ ‡F_v`. -/
  φ : ℂ ≃+* ℂ
  cont : Continuous φ

namespace ArchLogLink

variable (L : ArchLogLink)

/-- The tautological archimedean log-link. -/
def taut : ArchLogLink := ⟨RingEquiv.refl ℂ, continuous_id⟩

/-- The log-link on the units of the domain: `u ↦ φ(log u)`. -/
def toFun (u : ℂ) : ℂ := L.φ (Complex.log u)

@[simp] theorem toFun_one : L.toFun 1 = 0 := by simp [toFun]

/-- **(c_arc)** The images of the units lie in the closed disc of radius `π`. -/
theorem toFun_mem_closedBall {u : ℂ} (hu : ‖u‖ = 1) :
    L.toFun u ∈ closedBall (0 : ℂ) Real.pi := by
  rw [mem_closedBall, dist_zero_right, toFun, norm_ringEquiv L.φ L.cont]
  exact norm_log_le_pi hu

/-- **The inverse of the log-link** on `ℂˣ`: `exp ∘ φ⁻¹`. -/
theorem exp_symm_toFun {u : ℂ} (hu : u ≠ 0) : Complex.exp (L.φ.symm (L.toFun u)) = u := by
  rw [toFun, RingEquiv.symm_apply_apply, Complex.exp_log hu]

/-- **Kummer non-compatibility** (IUT III, Proposition 1.2(iv) at `v ∈ V^arc`). -/
theorem not_ringHom_eq_toFun (κ : ℂ →+* ℂ) : ¬ ∀ u : ℂ, ‖u‖ = 1 → κ u = L.toFun u := by
  intro h
  have := h 1 (by simp)
  rw [map_one, toFun_one] at this
  exact one_ne_zero this

end ArchLogLink

/-! ### Archimedean vertical lines -/

/-- **A vertical line of the log-theta-lattice at a place `v ∈ V^arc`**: log-links `m → m + 1`
between the copies of `ℂ` and the Kummer isomorphisms `κ_m` of the copies with the vertically
coric field. -/
structure ArchColumn where
  /-- The log-link from level `m` to level `m + 1`. -/
  link : ℤ → ArchLogLink
  /-- The Kummer isomorphism of level `m`. -/
  kum : ℤ → ℂ ≃+* ℂ
  kum_cont : ∀ m, Continuous (kum m)

namespace ArchColumn

variable (C : ArchColumn)

/-- The tautological vertical line. -/
def taut : ArchColumn :=
  ⟨fun _ => ArchLogLink.taut, fun _ => RingEquiv.refl ℂ, fun _ => continuous_id⟩

/-- **The domain of the `m'`-th iterate** of the log-links starting at level `m`: the elements
`u` such that `u` and its first `m' − 1` iterated images are units. -/
def iterDom : ℕ → ℤ → Set ℂ
  | 0, _ => Set.univ
  | m' + 1, m => {u | ‖u‖ = 1 ∧ (C.link m).toFun u ∈ iterDom m' (m + 1)}

/-- **The `m'`-th iterate** of the log-links starting at level `m` (landing at level `m + m'`). -/
def itF : ℕ → ℤ → ℂ → ℂ
  | 0, _, u => u
  | m' + 1, m, u => itF m' (m + 1) ((C.link m).toFun u)

/-- **The inverse of the `m'`-th iterate**, from level `m + m'` back to level `m`. -/
def back : ℕ → ℤ → ℂ → ℂ
  | 0, _, y => y
  | m' + 1, m, y => Complex.exp ((C.link m).φ.symm (back m' (m + 1) y))

/-- **The iterates land in the closed ball of radius `π`.** -/
theorem itF_mem_closedBall (m' : ℕ) (m : ℤ) {u : ℂ} (hu : u ∈ C.iterDom (m' + 1) m) :
    C.itF (m' + 1) m u ∈ closedBall (0 : ℂ) Real.pi := by
  induction m' generalizing m u with
  | zero => exact (C.link m).toFun_mem_closedBall hu.1
  | succ m' ih => exact ih (m + 1) hu.2

/-- **The closed ball surjects onto the domain of the iterate**: the inverse of the iterate
recovers every unit on which the iterate is defined. -/
theorem back_itF (m' : ℕ) (m : ℤ) {u : ℂ} (hu : u ∈ C.iterDom m' m) :
    C.back m' m (C.itF m' m u) = u := by
  induction m' generalizing m u with
  | zero => rfl
  | succ m' ih =>
    have hu0 : u ≠ 0 := by
      rintro rfl
      have := hu.1
      simp at this
    change Complex.exp ((C.link m).φ.symm
      (C.back m' (m + 1) (C.itF m' (m + 1) ((C.link m).toFun u)))) = u
    rw [ih (m + 1) hu.2, (C.link m).exp_symm_toFun hu0]

/-- **Proposition 3.5(ii)(b), the surjection**: for `m' ≥ 1`, the closed ball of radius `π` of
level `m + m'` contains a subset which surjects, by the inverse of the `m'`-th iterate, onto the
units of level `m` on which this iterate is defined. -/
theorem exists_surj (m' : ℕ) (m : ℤ) :
    ∃ S ⊆ closedBall (0 : ℂ) Real.pi, C.back (m' + 1) m '' S = C.iterDom (m' + 1) m := by
  refine ⟨C.itF (m' + 1) m '' C.iterDom (m' + 1) m, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact C.itF_mem_closedBall m' m hu
  · rw [Set.image_image]
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      change C.back _ m (C.itF _ m v) ∈ _
      rwa [C.back_itF _ m hv]
    · intro hu
      exact ⟨u, hu, C.back_itF _ m hu⟩

/-- **Upper semi-compatibility at `v ∈ V^arc`** (IUT III, Proposition 3.5(ii)(b); (Ind3)): the
Kummer images of (1) the units and (2) the closed ball of radius `π` of every level lie in the
coric closed ball of radius `π`; so do the Kummer images of all iterates. -/
theorem upperSemiCompat (m : ℤ) :
    C.kum m '' ({u : ℂ | ‖u‖ = 1} ∪ closedBall 0 Real.pi) ⊆ closedBall 0 Real.pi := by
  have hsub : {u : ℂ | ‖u‖ = 1} ∪ closedBall 0 Real.pi ⊆ closedBall 0 Real.pi := by
    refine Set.union_subset (fun u hu => ?_) le_rfl
    rw [mem_closedBall, dist_zero_right, show ‖u‖ = 1 from hu]
    linarith [Real.pi_gt_three]
  rintro _ ⟨x, hx, rfl⟩
  have := hsub hx
  rw [mem_closedBall, dist_zero_right] at this ⊢
  rwa [norm_ringEquiv _ (C.kum_cont m)]

/-- **The archimedean log-Kummer correspondence**: the totality of the Kummer images of the
iterates of all levels. -/
def logKummer : Set ℂ :=
  ⋃ (m' : ℕ) (m : ℤ), C.kum (m + (m' + 1 : ℕ)) '' (C.itF (m' + 1) m '' C.iterDom (m' + 1) m)

theorem logKummer_subset : C.logKummer ⊆ closedBall (0 : ℂ) Real.pi := by
  refine Set.iUnion₂_subset fun m' m => ?_
  rw [← image_closedBall (C.kum _) (C.kum_cont _)]
  refine Set.image_mono ?_
  rintro _ ⟨u, hu, rfl⟩
  exact C.itF_mem_closedBall m' m hu

/-- The column translated by one step. -/
def shift : ArchColumn :=
  ⟨fun m => C.link (m + 1), fun m => C.kum (m + 1), fun m => C.kum_cont (m + 1)⟩

theorem iterDom_shift (m' : ℕ) (m : ℤ) : C.shift.iterDom m' m = C.iterDom m' (m + 1) := by
  induction m' generalizing m with
  | zero => rfl
  | succ m' ih =>
    change {u | ‖u‖ = 1 ∧ (C.link (m + 1)).toFun u ∈ C.shift.iterDom m' (m + 1)} =
      {u | ‖u‖ = 1 ∧ (C.link (m + 1)).toFun u ∈ C.iterDom m' (m + 1 + 1)}
    rw [ih]

theorem itF_shift (m' : ℕ) (m : ℤ) (u : ℂ) : C.shift.itF m' m u = C.itF m' (m + 1) u := by
  induction m' generalizing m u with
  | zero => rfl
  | succ m' ih =>
    simp only [itF, ih]
    rfl

/-- **The archimedean log-Kummer correspondence is invariant under translation.** -/
theorem logKummer_shift : C.shift.logKummer = C.logKummer := by
  ext y
  simp only [logKummer, Set.mem_iUnion]
  have e : ∀ (m' : ℕ) (m : ℤ), C.shift.kum (m + (m' + 1 : ℕ)) = C.kum (m + 1 + (m' + 1 : ℕ)) :=
    fun m' m => by
      change C.kum (m + (m' + 1 : ℕ) + 1) = _
      congr 1
      ring
  have hset : ∀ (m' : ℕ) (m : ℤ), C.shift.itF (m' + 1) m '' C.shift.iterDom (m' + 1) m =
      C.itF (m' + 1) (m + 1) '' C.iterDom (m' + 1) (m + 1) := fun m' m => by
    rw [C.iterDom_shift]
    exact Set.image_congr fun u _ => C.itF_shift _ _ u
  constructor
  · rintro ⟨m', m, h⟩
    rw [e, hset] at h
    exact ⟨m', m + 1, h⟩
  · rintro ⟨m', m, h⟩
    refine ⟨m', m - 1, ?_⟩
    rw [e, hset, sub_add_cancel]
    exact h

end ArchColumn

/-! ### Tensor packets -/

section Packet

open LocalConstruct

variable {K : Type*} [Field K] [NumberField K] {ι : Type} [Fintype ι] (c : ι → Place K)

/-- An element of an archimedean factor whose image in `ℂ` lies in the closed disc of radius `π`
lies in the log-shell of the factor. -/
theorem archAbs_le_pi_of_mem {v : Place K} {y : ArchFactor K v}
    (hy : (archFactorEquiv v y : ℂ) ∈ closedBall (0 : ℂ) Real.pi) : archAbs v y ≤ Real.pi := by
  simpa [archAbs, mem_closedBall, dist_zero_right] using hy

/-- **Upper semi-compatibility for archimedean tensor packets** (IUT III, Proposition 3.5(ii)(b)):
the tensor product of Kummer images (automorphisms `σ_j` of the factors) of elements of the closed
discs of radius `π` lies in the archimedean log-shell of the packet. -/
theorem tprod_mem_archLogShell (σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j))
    (y : ∀ j, ArchFactor K (c j)) (hy : ∀ j, archAbs (c j) (y j) ≤ Real.pi) :
    PiTensorProduct.tprod ℝ (fun j => σ j (y j)) ∈ archLogShell c :=
  archLogShellSet_subset_archLogShell c
    ⟨fun j => σ j (y j), fun j => by rw [archAbs_algEquiv]; exact hy j, rfl⟩

/-- **The tensor products of the Kummer images of units and of their log-link images lie in the
archimedean log-shell of the packet**: elements whose images in `ℂ` are units or values of
archimedean log-links. -/
theorem tprod_log_mem_archLogShell (σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j))
    (y : ∀ j, ArchFactor K (c j))
    (hy : ∀ j, ‖(archFactorEquiv (c j) (y j) : ℂ)‖ = 1 ∨
      ∃ (L : ArchLogLink) (u : ℂ), ‖u‖ = 1 ∧ (archFactorEquiv (c j) (y j) : ℂ) = L.toFun u) :
    PiTensorProduct.tprod ℝ (fun j => σ j (y j)) ∈ archLogShell c := by
  refine tprod_mem_archLogShell c σ y fun j => archAbs_le_pi_of_mem ?_
  rcases hy j with h | ⟨L, u, hu, h⟩
  · rw [mem_closedBall, dist_zero_right, h]
    linarith [Real.pi_gt_three]
  · rw [h]
    exact L.toFun_mem_closedBall hu

end Packet

end

end LogLink

end Iut
