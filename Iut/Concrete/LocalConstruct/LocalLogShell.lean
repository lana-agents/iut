/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import PadicLogVolume.PadicLog

/-!
# The log-shell of a local field (IUT III, Definition 1.1; Proposition 3.2)

Let `k` be a complete field with a rank-one valuation in `ℤᵐ⁰`, of characteristic `0`, with
residue characteristic `p` (`‖(p : k)‖ < 1`). The **log-shell** of `k` is
`Iut.logShell k p = {(2p)⁻¹ log u | ‖u - 1‖ < 1}`, the image of the principal units under
`(2p)⁻¹·log`, with the `p`-adic logarithm `PadicLogVolume.padicLog`. It is bounded
(`logShell_isBounded`), relatively compact when `k` is proper (`isCompact_closure_logShell`),
contains the ring of integers `{‖y‖ ≤ 1}` (`closedBall_subset_logShell`), and equals it when `p`
is odd and a uniformizer (`logShell_eq_closedBall`).
-/

namespace Iut

open Filter Topology
open scoped Valued
open PadicLogVolume

universe u

noncomputable section

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]

/-! ### The log-shell -/

section LogShell

variable (k) (p : ℕ)

/-- The **log-shell** `𝓘_k = (2p)⁻¹ · log (1 + 𝔪_k)`, the image of the principal units under
`(2p)⁻¹ log` (IUT III, Proposition 3.2; IUT IV, Proposition 1.2). -/
def logShell : Set k := {y | ∃ u : k, ‖u - 1‖ < 1 ∧ y = (2 * (p : k))⁻¹ * padicLog u}

variable {k p}

theorem mem_logShell {y : k} :
    y ∈ logShell k p ↔ ∃ u : k, ‖u - 1‖ < 1 ∧ y = (2 * (p : k))⁻¹ * padicLog u := Iff.rfl

/-- The log-shell is bounded. -/
theorem logShell_isBounded [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    Bornology.IsBounded (logShell k p) := by
  obtain ⟨M, hM0, hM⟩ := exists_forall_norm_padicLog_le hp hpk
  refine isBounded_iff_forall_norm_le.2 ⟨‖(2 * (p : k))⁻¹‖ * M, ?_⟩
  rintro y ⟨u, hu, rfl⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM u hu) (norm_nonneg _)

/-- The log-shell is relatively compact (when `k` is proper, e.g. a finite extension of
`ℚ_p`). -/
theorem isCompact_closure_logShell [CharZero k] [ProperSpace k] (hp : p.Prime)
    (hpk : ‖(p : k)‖ < 1) : IsCompact (closure (logShell k p)) :=
  (logShell_isBounded hp hpk).isCompact_closure

/-- When `p` is odd and `p` is a uniformizer (`‖a‖ < 1 → ‖a‖ ≤ ‖p‖`, i.e. `k/ℚ_p` is
unramified), the log-shell is contained in the ring of integers. -/
theorem logShell_subset_closedBall [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    (hodd : Odd p) (hur : ∀ a : k, ‖a‖ < 1 → ‖a‖ ≤ ‖(p : k)‖) :
    logShell k p ⊆ Metric.closedBall (0 : k) 1 := by
  rintro y ⟨u, hu, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_inv, norm_mul,
    norm_two_eq_one hp hpk hodd, one_mul]
  have hp0 : 0 < ‖(p : k)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  rw [← div_eq_inv_mul, div_le_one hp0]
  exact norm_padicLog_le_norm_p hp hpk (hur _ hu)

variable [CompleteSpace k]

/-- The log-shell contains the ring of integers `{‖y‖ ≤ 1}` (IUT III, Proposition 1.2). -/
theorem closedBall_subset_logShell [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    Metric.closedBall (0 : k) 1 ⊆ logShell k p := by
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  have h2p : (2 * (p : k)) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero)
  obtain ⟨a, ha, hlog⟩ := exists_padicLog_eq hp hpk (y := 2 * (p : k) * y)
    (by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hy)
  refine ⟨1 + a, by simpa using ha.trans_lt (norm_two_mul_lt_one hpk), ?_⟩
  rw [hlog, inv_mul_cancel_left₀ h2p]

/-- The log-shell contains the valuation ring `𝓞_k`. -/
theorem integer_subset_logShell [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    ((Valued.v.integer : Subring k) : Set k) ⊆ logShell k p := fun y hy =>
  closedBall_subset_logShell hp hpk
    (by rw [← Valued.toNormedField.setOf_mem_integer_eq_closedBall]; exact hy)

/-- At an odd prime `p` which is a uniformizer, the log-shell **is** the ring of integers
(IUT I, Definition 5.4.5; IUT IV, Proposition 1.4(iv)). -/
theorem logShell_eq_closedBall [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    (hodd : Odd p) (hur : ∀ a : k, ‖a‖ < 1 → ‖a‖ ≤ ‖(p : k)‖) :
    logShell k p = Metric.closedBall (0 : k) 1 :=
  (logShell_subset_closedBall hp hpk hodd hur).antisymm (closedBall_subset_logShell hp hpk)

theorem logShell_eq_integer [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    (hodd : Odd p) (hur : ∀ a : k, ‖a‖ < 1 → ‖a‖ ≤ ‖(p : k)‖) :
    logShell k p = ((Valued.v.integer : Subring k) : Set k) := by
  rw [logShell_eq_closedBall hp hpk hodd hur]
  ext y
  simp only [Metric.mem_closedBall, dist_zero_right, SetLike.mem_coe, Valuation.mem_integer_iff,
    Valued.toNormedField.norm_le_one_iff]

end LogShell

end

end Iut
