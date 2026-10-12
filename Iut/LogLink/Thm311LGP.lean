/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Thm311
import Iut.LogLink.Split
import Iut.LogLink.Global

/-!
# Theorem 3.11 with LGP-monoids: parts (ii)(b), (ii)(c) and the archimedean (Ind3)

An **LGP-Gaussian log-theta-lattice** (`LGPLattice`, IUT III, Definition 3.8(iii)) is a
log-theta-lattice (`LogThetaLattice`) together with

* the **archimedean vertical lines** (`arc`, `ArchColumn`) at the infinite places of `F_mod`;
* the compatibility of the Kummer isomorphisms of the local vertical lines at the bad places with
  the Gaussian generator `{q_v^{j²}}_j` (`kum_gen`; the Kummer isomorphisms of labeled data of
  IUT II, Corollary 4.6(iii), which induce the vertically coric LGP-monoids of IUT III,
  Proposition 3.5(i)).

At a bad place `w` the column `n` gives an `LGPColumn` (`lgpCol`); its splitting monoids are
`Ψ⊥ = μ_{2ℓ}·{q_v^{j²}}^ℕ`.

## Theorem 3.11 with LGP-monoids (`Thm311LGP`)

`Thm311LGP L K` contains `Thm311` (the parts (i), (ii)(a) with (Ind3) at `v ∈ V^non`, (iii)(a)) and
* **(ii)(b)**: the Kummer isomorphisms of the splitting monoids are isomorphisms onto the one
  coric splitting monoid for every vertex (`splitCoric`); as `m` varies, they are mutually
  compatible relative to the log-links: an element of `Ψ⊥` of level `m` in the domain of the
  log-link is a `2ℓ`-th root of unity and its log-link image is `0` (`splitCompat`); they preserve
  the degrees (`splitDeg`);
* **(ii)(c)**: the nonzero elements of `F_mod` related by the log-links (in the domain of the
  log-links at every place of `V`) are roots of unity with vanishing log-link images
  (`globalCompat`, Proposition 3.10(ii)), and the kernel of the divisor maps on which the
  `F^⊛_MOD`-Frobenioids depend is the group of roots of unity (`modKernel`, Proposition 3.10(iii));
* **(Ind3) at `v ∈ V^arc`** (Proposition 3.5(ii)(b)): the Kummer images of the units and of the
  closed balls of radius `π` lie in the coric closed ball of radius `π` (`arcUpperSemi`), and the
  closed ball surjects onto the units on which the iterated log-links are defined (`arcSurj`).

**`thm311LGP_model`**: all of this holds for every LGP-Gaussian log-theta-lattice and every
unit-induced Kummer data.

## (d) Re-check of Step (xi) and of the distortion

`answerLGP`: with these additions the conclusions of `Thm311.lean` are unchanged — the distortion
is `0` along all arrows, the output law is the identified-copies law, and **Step (xi) is the
Scholze–Stix inequality** (`xi_iff_ss_lgp`). The new structures do not provide a new source of
distortion: the value-group portion of the LGP-monoids is **precisely** Kummer compatible (equality
of the coric splitting monoids, degrees preserved), the elements of the splitting monoids and of
the number fields that the log-links relate are roots of unity with logarithm `0` (no
indeterminacy), and the archimedean (Ind3) is again an inclusion into a log-shell (the closed disc
of radius `π`) together with a surjection — the same shape as at `v ∈ V^non`, which the wall
already quantifies over by its `∃ S`.
-/

namespace Iut

namespace LogLink

open Wall ThetaLink HodgeTheater NumberField Metric
open scoped Valued

noncomputable section

variable {D : InitialThetaData.{0}}

/-- The place of the section over `w ∈ V_mod^bad` is a bad place of `K`. -/
theorem isBadK_sectFin {w : FinitePlace D.Fmod} (hw : w ∈ D.VBad) : IsBadK D (D.V.sectFin w) :=
  ⟨w, hw, D.V.sectFin_liesOver w⟩

/-- **The Gaussian generator is strict**: every entry `q_v^{j²}` has norm in `(0, 1)`. -/
theorem isStrictGen_gaussGen {v : FinitePlace D.Kt} (hv : IsBadK D v) :
    IsStrictGen (gaussGen D v) := fun j => by
  have h0 := norm_qroot_pos D v
  have h1 := norm_qroot_lt_one D hv
  refine ⟨?_, ?_⟩
  · simp only [gaussGen, EtaleTheta.lgpValue, norm_pow]
    positivity
  · simp only [gaussGen, EtaleTheta.lgpValue, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) h1 (by positivity)

/-- `2ℓ ≠ 0`. -/
theorem two_mul_ell_ne_zero (D : InitialThetaData.{0}) : 2 * D.ℓ ≠ 0 := by
  have := D.prime.five_le
  unfold InitialThetaData.ℓ
  omega

variable (D) in
/-- **An LGP-Gaussian log-theta-lattice** (IUT III, Definition 3.8(iii)): a log-theta-lattice with
archimedean vertical lines and Kummer isomorphisms compatible with the Gaussian generators at the
bad places. -/
structure LGPLattice extends LogThetaLattice D where
  /-- The archimedean vertical lines of the `n`-th column at the infinite places. -/
  arc : ℤ → InfinitePlace D.Fmod → ArchColumn
  /-- The Kummer isomorphisms at the bad places fix the Gaussian generator. -/
  kum_gen : ∀ (n : ℤ) (w : FinitePlace D.Fmod), w ∈ D.VBad → ∀ (m : ℤ) (j : Fin (nC D)),
    (loc n w).kum m (gaussGen D (D.V.sectFin w) j) = gaussGen D (D.V.sectFin w) j

namespace LGPLattice

variable (L : LGPLattice D)

/-- **The vertical line of the `n`-th column at a bad place, with its Gaussian data.** -/
def lgpCol (n : ℤ) {w : FinitePlace D.Fmod} (hw : w ∈ D.VBad) : LGPColumn (Kfin D w) (nC D) :=
  { L.loc n w with
    gen := gaussGen D (D.V.sectFin w)
    strict := isStrictGen_gaussGen (isBadK_sectFin hw)
    kum_gen := L.kum_gen n w hw }

theorem lgpCol_toLogColumn (n : ℤ) {w : FinitePlace D.Fmod} (hw : w ∈ D.VBad) :
    (L.lgpCol n hw).toLogColumn = L.loc n w := rfl

variable (D) in
/-- **The LGP-Gaussian lattice of copies of the Hodge theater built from `D`**, with tautological
local vertical lines. -/
def ofData : LGPLattice D where
  toLogThetaLattice := LogThetaLattice.ofData D
  arc _ _ := ArchColumn.taut
  kum_gen _ _ _ _ _ := rfl

end LGPLattice

/-- **IUT III, Theorem 3.11 with LGP-monoids**, for an LGP-Gaussian log-theta-lattice `L` with
Kummer data `K` (see the module docstring). -/
structure Thm311LGP (L : LGPLattice D) (K : LatticeKummer L.toLogThetaLattice) : Prop where
  /-- Theorem 3.11 (i), (ii)(a) with (Ind3) at `v ∈ V^non`, (iii)(a). -/
  base : Thm311 L.toLogThetaLattice K
  /-- (ii)(b) The Kummer images of the splitting monoids of every level are the coric splitting
  monoid. -/
  splitCoric : ∀ (n : ℤ) (w : FinitePlace D.Fmod) (_ : w ∈ D.VBad) (m : ℤ),
    piMap ((L.loc n w).kum m) '' (perpMonoid (2 * D.ℓ) (gaussGen D (D.V.sectFin w)) :
      Set (Fin (nC D) → Kfin D w)) = perpMonoid (2 * D.ℓ) (gaussGen D (D.V.sectFin w))
  /-- (ii)(b) Mutual compatibility relative to the log-links: the elements of `Ψ⊥` in the domain
  of the log-link are roots of unity with log-link image `0`. -/
  splitCompat : ∀ (n : ℤ) (w : FinitePlace D.Fmod) (_ : w ∈ D.VBad) (m : ℤ) {p : ℕ},
    p.Prime → ‖(p : Kfin D w)‖ < 1 → ∀ x ∈ perpMonoid (2 * D.ℓ) (gaussGen D (D.V.sectFin w)),
      ∀ j, ‖x j - 1‖ < 1 → x j ^ (2 * D.ℓ) = 1 ∧
        (L.loc n w).kum (m + 1) (((L.loc n w).link m).toFun (x j)) = 0
  /-- (ii)(b) The Kummer isomorphisms of the Gaussian (and LGP-) monoids preserve degrees. -/
  splitDeg : ∀ (n : ℤ) (w : FinitePlace D.Fmod) (_ : w ∈ D.VBad) (m : ℤ),
    ∀ x ∈ gauss D (D.V.sectFin w), avgDeg (piMap ((L.loc n w).kum m) x) = avgDeg x
  /-- (ii)(c) The log-Kummer correspondence for `F_mod` (Proposition 3.10(ii)). -/
  globalCompat : ∀ (n : ℤ) {x : D.Fmod}, x ≠ 0 →
    (∀ w : FinitePlace D.Fmod, ‖embFin D w x‖ ≤ 1) →
    (∀ w : InfinitePlace D.Fmod, D.V.sectInf w (algebraMap D.Fmod D.Kt x) ≤ 1) →
      (∃ k : ℕ, 0 < k ∧ x ^ k = 1) ∧
        ∀ (w : FinitePlace D.Fmod) (m : ℤ) {p : ℕ}, p.Prime → ‖(p : Kfin D w)‖ < 1 →
          ‖embFin D w x - 1‖ < 1 →
            (L.loc n w).kum (m + 1) (((L.loc n w).link m).toFun (embFin D w x)) = 0
  /-- (ii)(c) The kernel of the divisor maps of `F^⊛_MOD` is the group of roots of unity
  (Proposition 3.10(iii)). -/
  modKernel : ∀ {x : D.Fmod}, x ≠ 0 →
    (((∀ w : FinitePlace D.Fmod, w x = 1) ∧ ∀ v : InfinitePlace D.Fmod, v x = 1) ↔
      ∃ k : ℕ, 0 < k ∧ x ^ k = 1)
  /-- (Ind3) at `v ∈ V^arc`: upper semi-compatibility (Proposition 3.5(ii)(b)). -/
  arcUpperSemi : ∀ (n : ℤ) (w : InfinitePlace D.Fmod) (m : ℤ),
    (L.arc n w).kum m '' ({u : ℂ | ‖u‖ = 1} ∪ closedBall 0 Real.pi) ⊆ closedBall 0 Real.pi
  /-- (Ind3) at `v ∈ V^arc`: the closed ball surjects onto the domain of the iterated
  log-links. -/
  arcSurj : ∀ (n : ℤ) (w : InfinitePlace D.Fmod) (m' : ℕ) (m : ℤ),
    ∃ S ⊆ closedBall (0 : ℂ) Real.pi,
      (L.arc n w).back (m' + 1) m '' S = (L.arc n w).iterDom (m' + 1) m

/-- **Theorem 3.11 with LGP-monoids holds in the model**, for every LGP-Gaussian
log-theta-lattice and every unit-induced Kummer data. -/
theorem thm311LGP_model (L : LGPLattice D) (K : LatticeKummer L.toLogThetaLattice) :
    Thm311LGP L K where
  base := thm311_model L.toLogThetaLattice K
  splitCoric n _ hw m := (L.lgpCol n hw).image_perpKummer _ m
  splitCompat n _ hw m _ hp hpk x hx j hj := by
    obtain ⟨-, h1, h2⟩ := (L.lgpCol n hw).perp_compat hp hpk (two_mul_ell_ne_zero D) m hx hj
    exact ⟨h1, h2⟩
  splitDeg n _ hw m x hx := (L.lgpCol n hw).avgDeg_kum_of_mem_splitMonoid m hx
  globalCompat n _ hx hfin hinf := L.toLogThetaLattice.globalLogKummer n hx hfin hinf
  modKernel hx := divisor_trivial_iff hx
  arcUpperSemi n w m := (L.arc n w).upperSemiCompat m
  arcSurj n w m' m := (L.arc n w).exists_surj m' m

/-! ### (d) Re-check: Step (xi) and the distortion -/

variable {L : LGPLattice D} {K : LatticeKummer L.toLogThetaLattice}

/-- **Step (xi) is still the Scholze–Stix inequality** for LGP-Gaussian lattices. -/
theorem xi_iff_ss_lgp (h : Thm311LGP L K) : XiPrinciple K ↔ SSIneq D := xi_iff_ss h.base

/-- **Theorem 3.11 with LGP-monoids and Step (xi) imply the ABC conjecture** (bookkeeping, as
`classicalABC_of_thm311`). -/
theorem classicalABC_of_thm311LGP (L : ∀ D : InitialThetaData.{0}, LGPLattice D)
    (K : ∀ D, LatticeKummer (L D).toLogThetaLattice) (h : ∀ D, Thm311LGP (L D) (K D))
    (hx : ∀ D, XiPrinciple (K D)) : ClassicalABC :=
  classicalABC_of_thm311 (fun D => (L D).toLogThetaLattice) K (fun D => (h D).base) hx

/-- **The answer (d)** for LGP-Gaussian lattices: zero distortion along horizontal and vertical
arrows, the identified-copies output law, Step (xi) equal to the Scholze–Stix inequality, and no
distortion of the value-group portion of the LGP-monoids along the vertical lines (the Kummer
isomorphisms preserve the degrees of the Gaussian monoids at every bad place). -/
theorem answerLGP (L : LGPLattice D) (K : LatticeKummer L.toLogThetaLattice) :
    (∀ n m, K.model.distortion (n, m) (n + 1, m) = 0) ∧
    (∀ n m, K.model.distortion (n, m) (n, m + 1) = 0) ∧
    K.model.alg.ThetaShift ∧ (XiPrinciple K ↔ SSIneq D) ∧
    (∀ (n : ℤ) (w : FinitePlace D.Fmod) (_ : w ∈ D.VBad) (m : ℤ),
      ∀ x ∈ gauss D (D.V.sectFin w), avgDeg (piMap ((L.loc n w).kum m) x) = avgDeg x) :=
  let h := thm311LGP_model L K
  ⟨K.distortion_horiz, K.distortion_vert, K.model_thetaShift, xi_iff_ss_lgp h, h.splitDeg⟩

end

end LogLink

end Iut
