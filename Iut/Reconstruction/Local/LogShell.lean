/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Invariants
import Mathlib.GroupTheory.PGroup
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The normalisation of mono-analytic log-volumes (roadmap P17, M3)

[AbsTopIII], Proposition 5.8 (i), (iii): from `G_K` one reconstructs `p`, `f`, `e` and the order
`p^m` of the group `μ_{p^∞}(K)` of `p`-power roots of unity, and hence the normalisation of the
log-volume of the log-shell `𝓘_K = (2p)⁻¹ log(𝒪_Kˣ)`:

`μ^log(𝓘_K) = (−1 − m/f + e · log(p*)/log p) · f log p`, `p* = p` (`p` odd), `p* = 4` (`p = 2`),

i.e. `vol(𝓘_K) = p^{−(f+m)} · (p*)^{[K:ℚ_p]}` for the Haar measure with `vol(𝒪_K) = 1`
(`log` maps `𝒪ˣ` onto a lattice of volume `q⁻¹ p^{−m}`, and `(2p)⁻¹` multiplies volumes by
`(p*)^{[K:ℚ_p]}`).

Here we prove the group-theoretic part: `#μ_{p^k}(K)` is a power of `p` bounded by `q^{e+1}`
(`Iut.Reconstruction.muCard_le`), the exponent `m` (`Iut.Reconstruction.mExp`) is recovered
from `G_K` (`Iut.Reconstruction.recMExp_gal`), and so is the normalising number
(`Iut.Reconstruction.recLogShellConst_gal`, `isGroupTheoretic_recLogShellConst`);
`Iut.Reconstruction.logShellConst_mul` records the volume formula it encodes. The identification
of this number with the Haar log-volume of `Iut.logShell` ([AbsTopIII], Proposition 5.7) is not
formalised here.
-/

open PadicField

namespace Iut.Reconstruction

section Field

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

theorem muCard_mul_eq (k : ℕ) :
    muCard p K k * q p K ^ (k * e p ℚ_[p] K) = powIndex (𝒪 p K)ˣ (p ^ k) :=
  (powIndex_integers_p_pow k).symm

theorem muCard_pos (k : ℕ) : 0 < muCard p K k := by
  have h := powIndex_integers_ne_zero (p := p) (K := K) (pow_ne_zero k hp.out.ne_zero)
  rw [← muCard_mul_eq] at h
  exact Nat.pos_of_ne_zero (left_ne_zero_of_mul h)

/-- `#μ_{p^k}(K)` is a power of `p`. -/
theorem exists_muCard_eq_pow (k : ℕ) : ∃ j, muCard p K k = p ^ j := by
  set T := (powMonoidHom (p ^ k) : (𝒪 p K)ˣ →* (𝒪 p K)ˣ).ker
  haveI : Finite T := Nat.finite_of_card_ne_zero (muCard_pos (p := p) (K := K) k).ne'
  have hT : IsPGroup p T := fun t => ⟨k, Subtype.ext ((MonoidHom.mem_ker).1 t.2)⟩
  exact hT.exists_card_eq

/-- `#μ_{p^k}(K) ≤ q^{e+1}`. -/
theorem muCard_le (k : ℕ) : muCard p K k ≤ q p K ^ (e p ℚ_[p] K + 1) := by
  have h1 := powIndex_p_pow_le_mul (p := p) (K := K) k
  rw [powIndex_p_pow] at h1
  exact Nat.le_of_mul_le_mul_right h1 (pow_pos hp.out.pos _)

variable (p K) in
/-- The order `#μ_{p^∞}(K) = sup_k #μ_{p^k}(K)` of the `p`-power roots of unity. -/
noncomputable def muPInf : ℕ := ⨆ k, muCard p K k

variable (p K) in
/-- The exponent `m` with `#μ_{p^∞}(K) = p^m`. -/
noncomputable def mExp : ℕ := Nat.log p (muPInf p K)

theorem bddAbove_muCard : BddAbove (Set.range (muCard p K)) :=
  ⟨_, by rintro _ ⟨k, rfl⟩; exact muCard_le k⟩

/-- `#μ_{p^∞}(K) = p^m`. -/
theorem muPInf_eq_pow : muPInf p K = p ^ mExp p K := by
  obtain ⟨k, hk⟩ : ∃ k, muCard p K k = muPInf p K := by
    have hne : (Set.range (muCard p K)).Nonempty := ⟨_, ⟨0, rfl⟩⟩
    exact Nat.sSup_mem hne bddAbove_muCard
  obtain ⟨j, hj⟩ := exists_muCard_eq_pow (p := p) (K := K) k
  rw [mExp, ← hk, hj, Nat.log_pow hp.out.one_lt]

end Field

section ShellVolume

/-- `p* = p` for odd `p` and `p* = 4` for `p = 2` ([AbsTopIII], Definition 5.4 (iii)). -/
def pStar (p : ℕ) : ℕ := if p = 2 then 4 else p

/-- The normalised log-volume of the log-shell, `−1 − m/f + e · log(p*)/log p`
([AbsTopIII], Proposition 5.8 (iii)). -/
noncomputable def logShellConst (p f e m : ℕ) : ℝ :=
  -1 - (m : ℝ) / f + e * Real.log (pStar p) / Real.log p

/-- The volume formula encoded by the number: multiplied by `f log p` it is
`−(f + m) log p + e f log p*`, the logarithm of `p^{−(f+m)} (p*)^{ef}`. -/
theorem logShellConst_mul {p f e m : ℕ} (hp : 1 < p) (hf : 0 < f) :
    logShellConst p f e m * (f * Real.log p) =
      -((f + m : ℕ) : ℝ) * Real.log p + (e * f : ℕ) * Real.log (pStar p) := by
  have hlog : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  have hf' : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  rw [logShellConst]
  field_simp
  push_cast
  ring

/-- The reconstructed order of `μ_{p^∞}` of a topological group. -/
noncomputable def recMuPInf (G : Type*) [Group G] [TopologicalSpace G] : ℕ := ⨆ k, recMu G k

/-- The reconstructed exponent `m`. -/
noncomputable def recMExp (G : Type*) [Group G] [TopologicalSpace G] : ℕ :=
  Nat.log (recPrime G) (recMuPInf G)

/-- The reconstructed normalising number of the log-volume of the log-shell. -/
noncomputable def recLogShellConst (G : Type*) [Group G] [TopologicalSpace G] : ℝ :=
  logShellConst (recPrime G) (recF G) (recE G) (recMExp G)

universe u

theorem isGroupTheoretic_recLogShellConst :
    IsGroupTheoretic.{u} fun G _ _ => recLogShellConst G :=
  fun _ _ _ _ _ _ φ => by
    simp only [recLogShellConst, recMExp, recMuPInf, recMu, recF, recE, recDeg, recPrime,
      charCountFun_congr φ]

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

variable (p) in
/-- `recMExp (G_K) = m`. -/
theorem recMExp_gal : recMExp (Ω ≃ₐ[K] Ω) = mExp p K := by
  have h : recMuPInf (Ω ≃ₐ[K] Ω) = muPInf p K := by
    simp only [recMuPInf, muPInf, recMu_gal p]
  rw [recMExp, h, recPrime_gal p, mExp]

variable (p) in
/-- **[AbsTopIII], Proposition 5.8 (iii)** (normalisation): the number
`−1 − m/f + e log(p*)/log p` is recovered from `G_K`. -/
theorem recLogShellConst_gal :
    recLogShellConst (Ω ≃ₐ[K] Ω) = logShellConst p (f p ℚ_[p] K) (e p ℚ_[p] K) (mExp p K) := by
  rw [recLogShellConst, recPrime_gal p, recF_gal p, recE_gal p, recMExp_gal p]

end ShellVolume

end Iut.Reconstruction
