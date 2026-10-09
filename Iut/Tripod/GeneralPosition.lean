/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Tripod.Basic
import Genl.Curves.ProofPackage
import Heights.Local.Bounded

/-!
# [GenEll] Theorem 2.1 (ii) ⇒ (i) for the tripod

The height theory `Iut.Tripod.tripodTheory` has the tripod as its only curve, so Theorem 2.1
of [GenEll] cannot be proved inside it: the proof of (ii) ⇒ (i) passes through all hyperbolic
curves (noncritical Belyi maps `X → ℙ¹` and coverings ramified over the divisor). The genuine
height theory of curves over number fields `Genl.Curves.theory` carries the proof package of
Theorem 2.1 (`Genl.Curves.proofPackage`), hence (ii) ⇒ (i) for it
(`Genl.Curves.statementII_implies_statementI`). This file compares its tripod with
`Iut.Tripod.tripodTheory`:

* the points of the tripod of `Genl.Curves.theory` are the `ℚ̄`-points of `ℚ(λ)` off
  `{0, 1, ∞}`, which correspond to `ℚ̄ ∖ {0, 1}` by `x ↦ λ(x)` (`Iut.Tripod.ptEquiv`), with
  the same degree, the same log-different and the same log-conductor, and heights differing by
  a bounded amount (`ht_{ω_ℙ(C)}` is the Weil height of the divisor `K_ℙ + C`, of degree `1`);
* the compactly bounded subsets of `Genl.Curves.theory`, defined by bounds at the embeddings of
  `ℚ(λ)` into `ℚ̄_p` (`p ∈ V`) and `ℂ`, are contained (on points of degree `≤ d`) in the
  valuation-bounded compactly bounded subsets of `Iut.Tripod.tripodTheory`
  (`Iut.Tripod.ptEquiv_mem_set`).

Hence `tripodTheory.StatementII → Genl.Curves.theory.StatementII`
(`Iut.Tripod.curves_statementII_of_statementII`) and
`Genl.Curves.theory.StatementI → tripodTheory.StatementI`
(`Iut.Tripod.statementI_of_curves_statementI`), and so

`Iut.Tripod.statementI_of_statementII : tripodTheory.StatementII → tripodTheory.StatementI`.
-/

namespace Iut.Tripod

open Genl.Curves Belyi.CurveField Heights.Curve NumberField
open scoped IntermediateField

/-! ### Points -/

/-- The points of the tripod of `Genl.Curves.theory` are the algebraic numbers `λ ∉ {0, 1}`. -/
noncomputable def ptEquiv : Genl.Curves.tripod.Pt ≃ Pt :=
  QbarPoint.equivTripod tgen_isRationalGenerator

theorem ptEquiv_val (y : Genl.Curves.tripod.Pt) :
    (ptEquiv y).1 = y.1.eval tgen (tgen_mem y) := rfl

theorem curves_fieldOf_eq (y : Genl.Curves.tripod.Pt) : y.1.fieldOf = fieldOf (ptEquiv y).1 :=
  QbarPoint.fieldOf_eq_adjoin tgen_isRationalGenerator y.1 (tgen_mem y)

theorem curves_deg_eq (y : Genl.Curves.tripod.Pt) : y.1.deg = deg (ptEquiv y).1 :=
  QbarPoint.deg_eq_natDegree_minpoly tgen_isRationalGenerator y.1 (tgen_mem y)

/-! ### Heights, log-differents and log-conductors -/

theorem discr_congr {F G : IntermediateField ℚ Qbar} [NumberField F] [NumberField G]
    (h : F = G) : discr F = discr G := by
  subst h
  rfl

theorem curves_logDiff_eq (y : Genl.Curves.tripod.Pt) :
    Heights.Curve.logDiff y.1 = logDiff (ptEquiv y) := by
  unfold Heights.Curve.logDiff logDiff
  rw [curves_deg_eq, discr_congr (curves_fieldOf_eq y)]

/-- The height `ht_{ω_ℙ(C)}` of `Genl.Curves.theory` and the height `Iut.Tripod.htCan` of the
tripod differ by a bounded amount. -/
theorem exists_abs_htCan_sub_le :
    ∃ C, ∀ y : Genl.Curves.tripod.Pt,
      |divHeight Genl.Curves.tripod.logCanon y.1 - htCan (ptEquiv y)| ≤ C := by
  obtain ⟨C, hC⟩ := divHeight_logCanon_tripod
  refine ⟨C, fun y => ?_⟩
  have h1 : tupleHeight ![1, tgen] y.1 = htCan (ptEquiv y) := by
    rw [tupleHeight_pair_one_of_mem _ (tgen_mem y), Heights.Absolute.logHeight_one_eq_gen,
      htCan, deg_eq_finrank]
    rfl
  rw [← h1]
  exact hC y.1

open scoped Classical in
/-- A log-conductor sum over the places of a field `F = ℚ(λ)` at which one of `λ`, `λ⁻¹`,
`(1 - λ)⁻¹` has a pole is the log-conductor `Iut.Tripod.logCond`. -/
theorem finsum_div_eq_logCond {F : IntermediateField ℚ Qbar} [FiniteDimensional ℚ F] (z : Pt)
    (hF : F = ℚ⟮z.1⟯) (P : Set (FinitePlace F)) (a : F) (ha : (a : Qbar) = z.1)
    (hP : ∀ w, w ∈ P ↔ (1 < w a ∨ 1 < w a⁻¹ ∨ 1 < w (1 - a)⁻¹)) :
    (∑ᶠ w : FinitePlace F, if w ∈ P then Real.log (Ideal.absNorm w.maximalIdeal.asIdeal)
      else 0) / Module.finrank ℚ F = logCond z := by
  subst hF
  have ha' : a = gen z.1 := Subtype.ext (by rw [ha, coe_gen])
  subst ha'
  unfold logCond
  rw [deg_eq_finrank]
  congr 1
  refine finsum_congr fun w => ?_
  have hiff : w ∈ P ↔ w ∈ badPlaces z.1 := by
    rw [hP, exists_one_lt_iff_tripod w (gen_ne_zero z.2.1) (fun h => z.2.2 (by
      have := congrArg (fun y : fieldOf z.1 => (y : Qbar)) h
      simpa using this))]
    rfl
  by_cases hw : w ∈ P
  · rw [if_pos hw, if_pos (hiff.mp hw)]
  · rw [if_neg hw, if_neg (fun h => hw (hiff.mpr h))]

theorem curves_logCond_eq (y : Genl.Curves.tripod.Pt) :
    theory.logCond Genl.Curves.tripod y = logCond (ptEquiv y) := by
  classical
  have hDne : Genl.Curves.tripod.D.Nonempty := by
    rw [← Finset.card_pos]
    change 0 < (tripodPlaces tgen).card
    rw [card_tripodPlaces tgen_isRationalGenerator]
    norm_num
  rw [theory_logCond_of_nonempty _ hDne]
  have hG : ∀ g ∈ Genl.Curves.tripod.G, g ∈ y.1.P.1 := by
    intro g hg
    have : g ∈ coordRing Genl.Curves.tripod.D := by
      rw [← Genl.Curves.tripod.G_spec hDne]
      exact Algebra.subset_adjoin hg
    exact this _ y.2
  unfold logCondOf
  rw [dif_pos hG]
  set a : y.1.fieldOf := evalF y.1 ⟨tgen, tgen_mem y⟩ with ha
  have hval : ∀ (g : Genl.Curves.tripodK) (hg : g ∈ y.1.P.1) (b : y.1.fieldOf),
      y.1.eval g hg = (b : Qbar) → (⟨y.1.eval g hg, y.1.eval_mem_fieldOf hg⟩ : y.1.fieldOf) = b :=
    fun g hg b h => Subtype.ext h
  refine finsum_div_eq_logCond (ptEquiv y) (curves_fieldOf_eq y) _ a rfl fun w => ?_
  have hz := tgen_mem y
  constructor
  · rintro ⟨g, hg, hlt⟩
    have hg' : g = tgen ∨ g = tgen⁻¹ ∨ g = (1 - tgen)⁻¹ := by
      change g ∈ ({tgen, tgen⁻¹, (1 - tgen)⁻¹} : Finset Genl.Curves.tripodK) at hg
      simpa using hg
    rcases hg' with rfl | rfl | rfl
    · exact Or.inl hlt
    · right; left
      rwa [hval _ _ a⁻¹ (by rw [y.1.eval_inv hz, IntermediateField.coe_inv]; rfl)] at hlt
    · right; right
      rwa [hval _ _ (1 - a)⁻¹ (by
        rw [y.1.eval_inv (sub_mem y.1.P.1.one_mem hz), IntermediateField.coe_inv,
          y.1.eval_sub y.1.P.1.one_mem hz, y.1.eval_one]
        rfl)] at hlt
  · rintro (h | h | h)
    · exact ⟨tgen, by simp [Genl.Curves.tripod], h⟩
    · refine ⟨tgen⁻¹, by simp [Genl.Curves.tripod], ?_⟩
      rwa [hval _ _ a⁻¹ (by rw [y.1.eval_inv hz, IntermediateField.coe_inv]; rfl)]
    · refine ⟨(1 - tgen)⁻¹, by simp [Genl.Curves.tripod], ?_⟩
      rwa [hval _ _ (1 - a)⁻¹ (by
        rw [y.1.eval_inv (sub_mem y.1.P.1.one_mem hz), IntermediateField.coe_inv,
          y.1.eval_sub y.1.P.1.one_mem hz, y.1.eval_one]
        rfl)]

/-! ### Compactly bounded subsets -/

/-- Primes carry their primality as an instance (local). -/
local instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The valuation-bounded compactly bounded subset of `Iut.Tripod.tripodTheory` containing the
points of degree `≤ d` of a compactly bounded subset of `Genl.Curves.theory`. -/
def cbsOf (K : CBSData) (d : ℕ) : CompactlyBounded where
  V := K.V.image fun p : Nat.Primes => (p : ℕ)
  prime p hp := by
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    exact q.2
  two_mem := Finset.mem_image.mpr ⟨_, K.two_mem, rfl⟩
  c := (d + 1) * max K.c 0

theorem mem_set_of_bounds {F : IntermediateField ℚ Qbar} [FiniteDimensional ℚ F] (z : Pt)
    (hF : F = ℚ⟮z.1⟯) (a : F) (ha : (a : Qbar) = z.1) (K : CBSData) (d : ℕ)
    (hd : Module.finrank ℚ F ≤ d)
    (hp : ∀ p ∈ K.V, ∀ τ : F →+* PadicAlgCl (p : ℕ),
      |Real.log ‖τ a‖| ≤ K.c ∧ |Real.log ‖τ a - 1‖| ≤ K.c)
    (hσ : ∀ σ : F →+* ℂ, |Real.log ‖σ a‖| ≤ K.c ∧ |Real.log ‖σ a - 1‖| ≤ K.c) :
    z ∈ (cbsOf K d).set := by
  subst hF
  have ha' : a = gen z.1 := Subtype.ext (by rw [ha, coe_gen])
  subst ha'
  have hc0 : 0 ≤ max K.c 0 := le_max_right _ _
  have hdle : (Module.finrank ℚ ℚ⟮z.1⟯ : ℝ) * max K.c 0 ≤ (d + 1) * max K.c 0 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hd.trans (Nat.le_succ d)) hc0
  have hle1 : max K.c 0 ≤ (d + 1) * max K.c 0 := by
    have : (1 : ℝ) ≤ d + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    nlinarith
  refine ⟨fun v hv => ?_, fun w => ?_⟩
  · obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hv
    have hmem : (((q : ℕ) : ℕ) : 𝓞 ℚ⟮z.1⟯) ∈ v.maximalIdeal.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hqv]
      exact ringChar.Nat.cast_ringChar
    have h1 := Heights.Local.abs_log_finitePlace_le hc0 (y := gen z.1)
      (fun τ => ((hp q hq τ).1).trans (le_max_left _ _)) v hmem
    have h2 := Heights.Local.abs_log_finitePlace_le hc0 (y := gen z.1 - 1)
      (fun τ => by
        rw [map_sub, map_one]
        exact ((hp q hq τ).2).trans (le_max_left _ _)) v hmem
    exact ⟨h1.trans hdle, h2.trans hdle⟩
  · have h1 := Heights.Local.abs_log_infinitePlace_le (y := gen z.1)
      (fun σ => ((hσ σ).1).trans (le_max_left _ (0 : ℝ))) w
    have h2 := Heights.Local.abs_log_infinitePlace_le (y := gen z.1 - 1)
      (fun σ => by
        rw [map_sub, map_one]
        exact ((hσ σ).2).trans (le_max_left _ (0 : ℝ))) w
    exact ⟨h1.trans hle1, h2.trans hle1⟩

/-- A point of degree `≤ d` of a compactly bounded subset of `Genl.Curves.theory` lies in the
corresponding compactly bounded subset of `Iut.Tripod.tripodTheory`. -/
theorem ptEquiv_mem_set (K : CBSData) (d : ℕ) {y : Genl.Curves.tripod.Pt} (hy : y ∈ K.set)
    (hyd : y.1.deg ≤ d) : ptEquiv y ∈ (cbsOf K d).set :=
  mem_set_of_bounds (ptEquiv y) (curves_fieldOf_eq y) (tripodValue y) rfl K d hyd
    (fun p hp τ => hy.1 p hp τ) hy.2

/-! ### Theorem 2.1 (ii) ⇒ (i) for the tripod -/

/-- Statement (ii) for `Iut.Tripod.tripodTheory` implies statement (ii) for
`Genl.Curves.theory`. -/
theorem curves_statementII_of_statementII (h : tripodTheory.StatementII) :
    theory.StatementII := by
  intro d ε hε K
  obtain ⟨C₀, hC₀⟩ := h d ε hε (cbsOf K d)
  obtain ⟨C₁, hC₁⟩ := exists_abs_htCan_sub_le
  have key : ∀ y : Genl.Curves.tripod.Pt, y ∈ CBSData.set K → y.1.deg ≤ d →
      divHeight Genl.Curves.tripod.logCanon y.1 ≤
        (1 + ε) * (Heights.Curve.logDiff y.1 + theory.logCond Genl.Curves.tripod y) +
          (C₀ + C₁) := by
    intro y hy hyd
    have hz : ptEquiv y ∈ (cbsOf K d).set ∩ ptLE d :=
      ⟨ptEquiv_mem_set K d hy hyd, by
        change deg (ptEquiv y).1 ≤ d
        rw [← curves_deg_eq]
        exact hyd⟩
    have h1 : htCan (ptEquiv y) ≤ (1 + ε) * (logDiff (ptEquiv y) + logCond (ptEquiv y)) + C₀ :=
      hC₀ (ptEquiv y) hz
    have h2 := hC₁ y
    rw [abs_le] at h2
    rw [curves_logDiff_eq, curves_logCond_eq]
    linarith [h2.1, h2.2]
  exact ⟨C₀ + C₁, fun y hy => key y hy.1 hy.2⟩

/-- Statement (i) for `Genl.Curves.theory` implies statement (i) for
`Iut.Tripod.tripodTheory`. -/
theorem statementI_of_curves_statementI (h : theory.StatementI) : tripodTheory.StatementI := by
  intro X _ d ε hε
  obtain ⟨C₀, hC₀⟩ := h Genl.Curves.tripod theory.hyperbolic_tripod d ε hε
  obtain ⟨C₁, hC₁⟩ := exists_abs_htCan_sub_le
  have hC₀' : ∀ y : Genl.Curves.tripod.Pt, y.1.deg ≤ d →
      divHeight Genl.Curves.tripod.logCanon y.1 ≤
        (1 + ε) * (Heights.Curve.logDiff y.1 + theory.logCond Genl.Curves.tripod y) + C₀ :=
    fun y hy => hC₀ y hy
  have key : ∀ z : Pt, deg z.1 ≤ d →
      htCan z ≤ (1 + ε) * (logDiff z + logCond z) + (C₀ + C₁) := by
    intro z hz
    have hzy : ptEquiv (ptEquiv.symm z) = z := ptEquiv.apply_symm_apply z
    have hyd : (ptEquiv.symm z).1.deg ≤ d := by
      rw [curves_deg_eq, hzy]
      exact hz
    have h1 := hC₀' _ hyd
    have h2 := hC₁ (ptEquiv.symm z)
    rw [abs_le, hzy] at h2
    rw [curves_logDiff_eq, curves_logCond_eq, hzy] at h1
    linarith [h2.1, h2.2]
  exact ⟨C₀ + C₁, fun z hz => key z hz⟩

/-- **[GenEll] Theorem 2.1, (ii) ⇒ (i), for the tripod**: the ABC inequality on compactly
bounded subsets of `ℙ¹ ∖ {0, 1, ∞}` implies the ABC inequality on all points of bounded
degree. The proof goes through the height theory of all curves over number fields
(`Genl.Curves.statementII_implies_statementI`: noncritical Belyi maps, the compactness
argument, and coverings ramified over the divisor). -/
theorem statementI_of_statementII (h : tripodTheory.StatementII) : tripodTheory.StatementI :=
  statementI_of_curves_statementI
    (Genl.Curves.statementII_implies_statementI (curves_statementII_of_statementII h))

end Iut.Tripod
