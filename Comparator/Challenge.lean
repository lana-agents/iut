import Mathlib

/-!
# Comparator challenge: nonarchimedean log-error sum

This mathlib-only module states the comparator core from Proposition 1.4(iii).
-/

namespace Iut4Sec1

noncomputable def nonarchimedeanLogError (p e : ℕ) : ℝ :=
  ((⌈(e : ℝ) / (p - 2 : ℕ)⌉ : ℤ) : ℝ) / e - 1 / e

theorem nonarchimedean_logError_sum_le {ι : Type*} [DecidableEq ι]
    (p : ℕ) (I Istar : Finset ι) (e : ι → ℕ)
    (hp : p.Prime) (hp2 : 2 < p) (hIstar : Istar ⊆ I)
    (he : ∀ i ∈ I, 0 < e i)
    (hsmall : ∀ i ∈ I, i ∉ Istar → e i ≤ p - 2) :
    ∑ i ∈ I, nonarchimedeanLogError p (e i) ≤
      4 * (Istar.card : ℝ) / p := by
  sorry

end Iut4Sec1
