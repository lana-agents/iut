/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Column
import Iut.ThetaLink.Link

/-!
# The log-theta-lattice (IUT III, Proposition 1.3, Definition 1.4, Theorem 1.5(i)–(iii))

* **Log-links of Hodge theaters** (`LogLinkHT`, Proposition 1.3(i)): a log-link
  `†HT^{Θ^{±ell}NF} → ‡HT^{Θ^{±ell}NF}` is determined by the isomorphism `Ξ` of the associated
  `D-Θ^{±ell}NF`-Hodge theaters over which it lies (the `F`-prime-strips of the bridges are then
  log-linked by the unique lifts of the `D`-prime-strip isomorphisms, IUT I, Corollary 5.3(ii);
  the local log-links are attached through `LogColumn`, see the scope decisions in the README).
  **Coricity** (Proposition 1.3(ii)): `LogLinkHT.dIso`; the full log-link is the full
  poly-isomorphism of the `D-Θ^{±ell}NF`-Hodge theaters (`logLinkEquiv`), which has two elements
  (`card_logLinkHT`, P18's `DThetaPmEllNFHT.card_iso`).
* **The log-theta-lattice** (`LogThetaLattice`, Definition 1.4): Hodge theaters `n,mHT` indexed
  by `ℤ × ℤ`, vertical log-links `n,mHT → n,m+1HT`, horizontal Θ-links `n,mHT → n+1,mHT`
  (P19's `ThetaLinkIso`, the `Θ^{×μ}_gau`-links), and at every finite place the local vertical
  lines `LogColumn` of the `n`-th column.
* **Theorem 1.5**: (i) **vertical coricity** (`vertCoric`, `vertIso`): the vertical arrows induce
  isomorphisms of the associated `D-Θ^{±ell}NF`-Hodge theaters, so a column has one `D`-Hodge
  theater `n,◦HT` up to isomorphism; (ii) **horizontal coricity** (`horizCoric`,
  `horizCoric_full`): each horizontal arrow induces an isomorphism of the `F^{⊢×μ}`-prime-strips,
  and every such isomorphism occurs (P19's `ThetaLinkIso.unitEquiv`); (iii) **bi-coricity**
  (`biCoric`): the `F^{⊢×μ}`-prime-strips of any two vertices are isomorphic.
* The rows are P19 Frobenius-pictures (`row`); `ofData` is a lattice of copies of the Hodge
  theater built from `D` (P18's `ThetaPmEllNFHT.ofData`) with tautological local log-links.

The non-commutativity of the lattice is local: `LogLink.log_theta_not_commute`
(`Column.lean`); `not_commute` restates it for the local lines of a lattice.
-/

namespace Iut

namespace LogLink

open HodgeTheater ThetaLink NumberField
open scoped Valued

noncomputable section

variable (D : InitialThetaData.{0})

/-! ### Log-links of Hodge theaters -/

/-- **A log-link of `Θ^{±ell}NF`-Hodge theaters** (IUT III, Proposition 1.3(i)), recorded by the
isomorphism `Ξ` of the associated `D-Θ^{±ell}NF`-Hodge theaters over which it lies. -/
structure LogLinkHT (H₁ H₂ : ThetaPmEllNFHT D) where
  /-- The isomorphism `Ξ : †HT^{D-Θ^{±ell}NF} ≅ ‡HT^{D-Θ^{±ell}NF}`. -/
  Ξ : H₁.labels.Iso H₂.labels

variable {D}

/-- **Coricity** (Proposition 1.3(ii)): a log-link lies over an isomorphism of the associated
`D-Θ^{±ell}NF`-Hodge theaters. -/
def LogLinkHT.dIso {H₁ H₂ : ThetaPmEllNFHT D} (L : LogLinkHT D H₁ H₂) :
    H₁.labels.Iso H₂.labels := L.Ξ

/-- **The full log-link is the full poly-isomorphism** of the associated `D-Θ^{±ell}NF`-Hodge
theaters: log-links correspond exactly to these isomorphisms. -/
def logLinkEquiv (H₁ H₂ : ThetaPmEllNFHT D) : LogLinkHT D H₁ H₂ ≃ H₁.labels.Iso H₂.labels where
  toFun L := L.dIso
  invFun Ξ := ⟨Ξ⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full log-link has two members (the `{±1}`-torsor of IUT I, Proposition 6.6(iii)). -/
theorem card_logLinkHT (H₁ H₂ : ThetaPmEllNFHT D) : Nat.card (LogLinkHT D H₁ H₂) = 2 := by
  rw [Nat.card_congr (logLinkEquiv H₁ H₂)]
  exact DThetaPmEllNFHT.card_iso _ _

theorem nonempty_logLinkHT (H₁ H₂ : ThetaPmEllNFHT D) : Nonempty (LogLinkHT D H₁ H₂) :=
  (Nat.card_pos_iff.1 (by rw [card_logLinkHT]; norm_num)).1

/-! ### The log-theta-lattice -/

/-- The tautological local vertical line: tautological log-links, identity Kummer
isomorphisms. -/
def LogColumn.taut (k : Type*) [Field k] [Valued k (WithZero (Multiplicative ℤ))] :
    LogColumn k :=
  ⟨fun _ => ⟨RingEquiv.refl k, continuous_id, continuous_id⟩, fun _ => RingEquiv.refl k,
    fun _ => continuous_id, fun _ => continuous_id⟩

variable (D) in
/-- **The (Gaussian) log-theta-lattice** (IUT III, Definition 1.4). -/
structure LogThetaLattice where
  /-- The Hodge theaters `n,mHT^{Θ^{±ell}NF}`. -/
  H : ℤ × ℤ → ThetaPmEllNFHT D
  /-- The vertical log-links `n,mHT → n,m+1HT`. -/
  vert : ∀ n m : ℤ, LogLinkHT D (H (n, m)) (H (n, m + 1))
  /-- The horizontal Θ-links `n,mHT → n+1,mHT` (the `Θ^{×μ}_gau`-links). -/
  horiz : ∀ n m : ℤ, ThetaLinkIso D (H (n, m)) (H (n + 1, m))
  /-- The local vertical lines of the `n`-th column at the finite places. -/
  loc : ℤ → ∀ w : FinitePlace ↥(fieldOfModuli D.F D.E), LogColumn (Kfin D w)

namespace LogThetaLattice

variable (L : LogThetaLattice D)

/-- **Theorem 1.5(i), vertical coricity**: the vertical arrows induce isomorphisms of the
associated `D-Θ^{±ell}NF`-Hodge theaters. -/
def vertIso (n m : ℤ) : (L.H (n, m)).labels.Iso (L.H (n, m + 1)).labels := (L.vert n m).dIso

/-- Any two vertices of a column have isomorphic `D-Θ^{±ell}NF`-Hodge theaters: the column
determines `n,◦HT^{D-Θ^{±ell}NF}` up to isomorphism. -/
theorem vertCoric (n m m' : ℤ) :
    Nonempty ((L.H (n, m)).labels.Iso (L.H (n, m')).labels) :=
  ⟨(logLinkEquiv _ _) (nonempty_logLinkHT _ _).some⟩

/-- **Theorem 1.5(ii), horizontal coricity**: each horizontal arrow induces an isomorphism of the
`F^{⊢×μ}`-prime-strips. -/
def horizCoric (n m : ℤ) : (L.H (n, m)).Fmu.Iso (L.H (n + 1, m)).Fmu :=
  ThetaLinkIso.unitEquiv _ _ (L.horiz n m)

/-- The horizontal arrows are the full poly-isomorphism of the `F^{⊢×μ}`-prime-strips: every
isomorphism is induced by a Θ-link. -/
theorem horizCoric_full (n m : ℤ) (f : (L.H (n, m)).Fmu.Iso (L.H (n + 1, m)).Fmu) :
    ∃ θ : ThetaLinkIso D (L.H (n, m)) (L.H (n + 1, m)), ThetaLinkIso.unitEquiv _ _ θ = f :=
  (ThetaLinkIso.unitEquiv _ _).surjective f

/-- **Theorem 1.5(iii), bi-coricity**: the `F^{⊢×μ}`-prime-strips of any two vertices of the
lattice are isomorphic. -/
theorem biCoric (a b : ℤ × ℤ) : Nonempty ((L.H a).Fmu.Iso (L.H b).Fmu) :=
  PrimeStrip.nonempty_iso _ _

/-- **The `m`-th row**: a Frobenius-picture of Θ-links (P19). -/
def row (m : ℤ) : FrobeniusPicture D := ⟨fun n => L.H (n, m), fun n => L.horiz n m⟩

/-- **The `n`-th column** of Hodge theaters. -/
def col (n : ℤ) : ℤ → ThetaPmEllNFHT D := fun m => L.H (n, m)

/-- **The non-commutativity of the lattice**, at a finite place `w` of the column `n`: for
`q ∈ K_w` with `0 < ‖q‖ < 1` and `j² ≠ 1`, the log-link `n,m → n,m+1` does not commute with any
pair of maps that identify the units and send `q^N ↦ q^{N·j²}` (`log_theta_not_commute`). -/
theorem not_commute (n m : ℤ) (w : FinitePlace ↥(fieldOfModuli D.F D.E)) {p : ℕ}
    (hp : p.Prime) (hpk : ‖(p : Kfin D w)‖ < 1) {q : Kfin D w} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    {j : ℕ} (hj : j ^ 2 ≠ 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ u : prinUnits (Kfin D w), ∀ Θ₀ Θ₁ : Kfin D w → Kfin D w,
      (∀ v : prinUnits (Kfin D w), Θ₀ (pval v) = pval v) → Θ₁ (q ^ N) = q ^ (N * j ^ 2) →
        Θ₁ (((L.loc n w).link m).toFun (pval u)) ≠ ((L.loc n w).link m).toFun (Θ₀ (pval u)) :=
  log_theta_not_commute hp hpk _ hq0 hq hj

variable (D) in
/-- **The lattice of copies of the Hodge theater built from `D`**, with some log-links and
Θ-links and the tautological local vertical lines. -/
def ofData : LogThetaLattice D where
  H _ := ThetaPmEllNFHT.ofData D
  vert _ _ := (nonempty_logLinkHT _ _).some
  horiz _ _ := (nonempty_thetaLink _ _).some
  loc _ w := LogColumn.taut (Kfin D w)

end LogThetaLattice

end

end LogLink

end Iut
