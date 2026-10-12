/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Local

/-!
# Vertical lines of the log-theta-lattice and the log-Kummer correspondence

A **vertical line** (`LogColumn`) at a place `v ∈ V^non`: copies `m ∈ ℤ` of the local field `k`,
log-links `m → m + 1` (`LocalLogLink`, IUT III, Definition 1.1, Proposition 1.2(x): the full
log-links of a column form an infinite chain), and the holomorphic **Kummer isomorphisms**
`κ_m` of the copies with the vertically coric field (the field `Ψ^gp_cns(n,◦D)_v` constructed
from the coric `D`-prime-strip; IUT III, Theorem 1.5(i), Proposition 3.5(i)), modelled by
bicontinuous ring isomorphisms.

## Results

* **Vertical coricity of the holomorphic log-shell** (`kum_image_logShell`): every `κ_m` maps the
  log-shell of the copy `m` onto the one coric log-shell `𝓘 = Iut.logShell k p`.
* **Upper semi-compatibility** (IUT III, Proposition 3.5(ii)(a); Theorem 3.11(ii), (Ind3);
  [LANA], §7.2(c)): `iter m' m` is the set of images, at level `m`, of the units of level
  `m − m'` under the `m'`-th iterate of the log-links (`iter 0 m` = the units of level `m`).
  **The Kummer images of all of them lie in the coric log-shell** (`upperSemiCompat`).
* **Only upper semi-compatibility**: the two routes from the units of level `m` to the coric
  field, `κ_m` and `κ_{m+1} ∘ log`, differ (`kummer_log_ne`, Proposition 1.2(iv)); the images of
  the iterates contain non-units (`exists_iter_one_norm_lt`: `2p`, a non-zero element of norm
  `< 1`), so a container larger than the units is needed — the log-shell.
* **Translation symmetry** (Proposition 1.2(x), 3.5(ii), last paragraph): `shift` (the column
  translated by one step) has the iterates of the original column shifted (`iter_shift`), so the
  log-Kummer correspondence (the totality of the Kummer images) is translation invariant
  (`logKummer_shift`).
* **The log-link and the Gaussian Θ-link do not commute** (IUT III, Definition 1.4: the
  log-theta-lattice is far from commutative; Remark 1.4.1): `log_theta_not_commute`. A Θ-link
  identifies the units (P19, `ThetaLinkIso.unitEquiv`) and sends `q^N ↦ q^{N·j²}` at the label
  `j` (P19, `gaussLink`); the log-link sends some unit to `q^N`. So for `j² ≠ 1` no pair of maps
  with these properties makes the square commute on that unit.
-/

namespace Iut

namespace LogLink

open PadicLogVolume Filter Topology
open scoped Valued

universe u

noncomputable section

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]

variable (k) in
/-- **A vertical line of the log-theta-lattice at a place `v ∈ V^non`**: log-links `m → m + 1`
between the copies of `k` and the Kummer isomorphisms `κ_m` of the copies with the vertically
coric field. -/
structure LogColumn where
  /-- The log-link from level `m` to level `m + 1`. -/
  link : ℤ → LocalLogLink k
  /-- The Kummer isomorphism of level `m`. -/
  kum : ℤ → k ≃+* k
  kum_cont : ∀ m, Continuous (kum m)
  kum_cont_symm : ∀ m, Continuous (kum m).symm

namespace LogColumn

variable (C : LogColumn k)

/-- **The images of the iterates of the log-links**: `iter 0 m` is the unit group `O^×` of
level `m`; `iter (m' + 1) m` is the image, under the log-link `m − 1 → m`, of the principal units
in `iter m' (m − 1)`. -/
def iter : ℕ → ℤ → Set k
  | 0, _ => {u | ‖u‖ = 1}
  | m' + 1, m => {y | ∃ u ∈ iter m' (m - 1), ‖u - 1‖ < 1 ∧ y = (C.link (m - 1)).toFun u}

/-- The column translated by one step. -/
def shift : LogColumn k :=
  ⟨fun m => C.link (m + 1), fun m => C.kum (m + 1), fun m => C.kum_cont (m + 1),
    fun m => C.kum_cont_symm (m + 1)⟩

theorem iter_shift (m' : ℕ) (m : ℤ) : C.shift.iter m' m = C.iter m' (m + 1) := by
  induction m' generalizing m with
  | zero => rfl
  | succ m' ih =>
    have e : m - 1 + 1 = m + 1 - 1 := by ring
    simp only [iter, ih]
    rw [show C.shift.link (m - 1) = C.link (m - 1 + 1) from rfl, e]

/-- **The log-Kummer correspondence**: the totality of the Kummer images of the iterates. -/
def logKummer : Set k := ⋃ (m' : ℕ) (m : ℤ), C.kum m '' C.iter m' m

/-- **The log-Kummer correspondence is invariant under the translation of the column.** -/
theorem logKummer_shift : C.shift.logKummer = C.logKummer := by
  ext y
  simp only [logKummer, Set.mem_iUnion, iter_shift]
  constructor
  · rintro ⟨m', m, h⟩
    exact ⟨m', m + 1, h⟩
  · rintro ⟨m', m, h⟩
    refine ⟨m', m - 1, ?_⟩
    change y ∈ C.kum (m - 1 + 1) '' C.iter m' (m - 1 + 1)
    rw [sub_add_cancel]
    exact h

variable [CompleteSpace k] [CharZero k] {p : ℕ}

/-- **Vertical coricity of the holomorphic log-shell**: every Kummer isomorphism maps the
log-shell of its level onto the coric log-shell. -/
theorem kum_image_logShell (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) (m : ℤ) :
    C.kum m '' logShell k p = logShell k p :=
  LocalLogLink.ringEquiv_image_logShell hp hpk _ (C.kum_cont m) (C.kum_cont_symm m)

/-- The images of the iterates lie in the log-shell of their level. -/
theorem iter_subset_logShell (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) (m' : ℕ) (m : ℤ) :
    C.iter m' m ⊆ logShell k p := by
  cases m' with
  | zero =>
    intro u hu
    exact closedBall_subset_logShell hp hpk (by simp [Metric.mem_closedBall, hu.le])
  | succ m' =>
    rintro y ⟨u, -, hu, rfl⟩
    rw [← (C.link (m - 1)).image_logShell hp hpk]
    exact (C.link (m - 1)).toFun_mem_logShell hp hpk hu

/-- **Upper semi-compatibility** (IUT III, Proposition 3.5(ii)(a); (Ind3)): the Kummer images of
the units of every level and of all their iterated log-link images lie in the coric log-shell. -/
theorem upperSemiCompat (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) (m' : ℕ) (m : ℤ) :
    C.kum m '' C.iter m' m ⊆ logShell k p := by
  rw [← C.kum_image_logShell hp hpk m]
  exact Set.image_mono (C.iter_subset_logShell hp hpk m' m)

theorem logKummer_subset (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) : C.logKummer ⊆ logShell k p :=
  Set.iUnion₂_subset fun m' m => C.upperSemiCompat hp hpk m' m

omit [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [CompleteSpace k] in
/-- **The Kummer isomorphisms are not compatible with the log-links** (Proposition 1.2(iv)): the
two routes `κ_m` and `κ_{m+1} ∘ log` from the units of level `m` to the coric field differ. -/
theorem kummer_log_ne (m : ℤ) : C.kum (m + 1) ((C.link m).toFun 1) ≠ C.kum m 1 := by
  rw [LocalLogLink.toFun_one, map_zero, map_one]
  exact zero_ne_one

/-- **The images of the iterates are not units**: `κ_m` of the first iterate contains `2p`. -/
theorem exists_iter_one_norm_lt (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) (m : ℤ) :
    ∃ y ∈ C.iter 1 m, C.kum m y ≠ 0 ∧ ‖C.kum m y‖ < 1 := by
  set L := C.link (m - 1)
  obtain ⟨u, hu⟩ := L.exists_toFun_eq hp hpk (y := L.φ (2 * (p : k)))
    (by rw [RingEquiv.symm_apply_apply])
  have h2p : (2 * (p : k)) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero)
  refine ⟨L.φ (2 * (p : k)), ⟨pval u, norm_eq_one_of_norm_sub_one_lt u.2, u.2, hu.symm⟩, ?_, ?_⟩
  · simpa using h2p
  · have : C.kum m (L.φ (2 * (p : k))) = 2 * (p : k) := by
      rw [two_mul_natCast, map_natCast, map_natCast]
    rw [this]
    exact norm_two_mul_lt_one hpk

end LogColumn

/-! ### The log-link and the Θ-link do not commute -/

/-- A continuous ring homomorphism preserves `‖x‖ < 1`. -/
theorem norm_map_lt_one (τ : k →+* k) (hτ : Continuous τ) {x : k} (hx : ‖x‖ < 1) :
    ‖τ x‖ < 1 := by
  rw [norm_lt_one_iff_tendsto_pow] at hx ⊢
  have h := (hτ.tendsto 0).comp hx
  rw [map_zero] at h
  exact h.congr fun n => by simp

variable [CompleteSpace k] [CharZero k] {p : ℕ}

/-- **The log-link and the Gaussian Θ-link do not commute.** Let `q ∈ k` with `0 < ‖q‖ < 1` (the
`q`-parameter of the copy at level `m + 1`) and `j² ≠ 1`. There are `N ≥ 1` and a principal unit
`u` of level `m` such that for every map `Θ₀` of level `m` which is the identity on the principal
units (the unit portion of a Θ-link is identified) and every map `Θ₁` of level `m + 1` with
`Θ₁(q^N) = q^{N·j²}` (the Gaussian value at the label `j`), `Θ₁(log u) ≠ log(Θ₀ u)`. -/
theorem log_theta_not_commute (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) (L : LocalLogLink k) {q : k}
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {j : ℕ} (hj : j ^ 2 ≠ 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ u : prinUnits k, ∀ Θ₀ Θ₁ : k → k,
      (∀ v : prinUnits k, Θ₀ (pval v) = pval v) → Θ₁ (q ^ N) = q ^ (N * j ^ 2) →
        Θ₁ (L.toFun (pval u)) ≠ L.toFun (Θ₀ (pval u)) := by
  have hq' : ‖L.φ.symm q‖ < 1 := norm_map_lt_one L.φ.symm.toRingHom L.cont_symm hq
  have h2p : 0 < ‖2 * (p : k)‖ :=
    norm_pos_iff.2 (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero))
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one h2p hq'
  set N := N₀ + 1
  have hN : ‖L.φ.symm (q ^ N)‖ ≤ ‖2 * (p : k)‖ := by
    rw [map_pow, norm_pow, pow_succ]
    exact (mul_le_of_le_one_right (by positivity) hq'.le).trans hN₀.le
  obtain ⟨u, hu⟩ := L.exists_toFun_eq hp hpk hN
  refine ⟨N, Nat.succ_pos _, u, fun Θ₀ Θ₁ h₀ h₁ => ?_⟩
  rw [h₀ u, hu, h₁]
  intro h
  have hn := congrArg norm h
  rw [norm_pow, norm_pow] at hn
  have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq0
  have := pow_right_injective₀ hqn hq.ne hn
  have hN0 : N ≠ 0 := Nat.succ_ne_zero _
  exact hj (by
    have : N * j ^ 2 = N * 1 := by rw [mul_one]; exact this
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN0) this)

end

end LogLink

end Iut
