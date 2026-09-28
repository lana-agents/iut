/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.CyclicBound
import Iut.Tripod.CyclicTate
import Iut.Tripod.CyclicArch
import Iut.Tripod.TorsionNewton
import Iut.Tripod.Height

/-!
# The isogeny estimate for a cyclic subgroup of the Legendre curve

Let `x` be a point of a compactly bounded subset `K` of the tripod, `E = E_λ/F_λ` its Legendre
curve, `ℓ ≥ 7` a prime and `H ⊆ E(F̄)` a Galois-stable subgroup of order `ℓ` which is the graph
line `μ_ℓ` at every multiplicative place of odd residue characteristic. We prove
(`Iut.Tripod.cyclicGraphOddBound`)

`((ℓ − 2)/24) · (log q_∀(E) − log q_2(E)) ≤ 2 log ℓ + T_K`,

where `log q_2` is the part of `log q_∀` supported over `2` and `T_K` depends only on `K`.

## The proof

Over the ℓ-torsion field `L = F(E[ℓ])`, with the points `T₁ = (0, 0)`, `T₂ = (1, 0)` of
order `2` and their halves `R₁ = (√λ, …)`, `R₂ = (1 + √(1 − λ), …)` (`Iut.CyclicPoints`),
consider the Vélu ratios `r_i = ∏_{Q ∈ H∖0} (x(T_i) − x(R_i + Q))/(x(T_i) − x(Q))`
(`Iut.CyclicPoints.veluRatio`). They are Galois-invariant, so `ρ = r₁r₂ ∈ F`, and nonzero. The
product formula `∑_v log|ρ|_v = 0` over the places of `F` is combined with the local bounds:

* at a multiplicative place `v` of odd residue characteristic, the Tate uniformization at a
  place of `L` above `v` and the graph-line property give `log|ρ|_v ≤ −((ℓ − 1)/4) log|j|_v`
  (`Iut.CyclicTate.ratio_mul_bound`): the point of order `2` reducing to the node makes the
  numerators of `r_i` of size `|q|^{1/4}`;
* at every other finite place, `r_i (x(T_i) − x(R_i))` is a sum of `x`-coordinates of
  `4ℓ`-torsion points, which are almost integral by the Newton bound
  (`Iut.TorsionNewton.apply_x_le_legendre`), with a loss `2 log|ℓ|_v^{-1}` over `ℓ` and a loss
  controlled by `K` over `2`;
* at an archimedean place, the `x`-coordinates of `4ℓ`-torsion points are `O(ℓ²)`
  (`Iut.CyclicArch.legendre_torsion_x_le`, from the complex uniformization of
  `lana-agents/heights`), so `log|ρ|_v ≤ 6 log ℓ + C_K`.

Summing, `((ℓ − 1)/4)(log q_∀ − log q_2) ≤ 10 log ℓ + C_K`.

The places over `2` contribute only a bounded error here, not a gain: the Tate uniformization of
`lana-agents/tate-curves-theta` assumes residue characteristic `≠ 2`, so the graph-line property
(and with it the gain `ℓ · log|q|_v`) is not available at the multiplicative places over `2`.
-/

namespace Iut.Tripod

open Iut Iut.EllipticCurveData Iut.EllipticCurveData.ModEllRepData WeierstrassCurve NumberField
  Iut.Anabelian Iut.CyclicPoints Heights.Velu
open scoped Classical

attribute [local instance 1100] Iut.EllipticCurveData.ModEllRepData.instDecidableEqTorsionFieldR

noncomputable section

namespace Cyclic

variable (P : CurveProviders) (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime)

/-- The ℓ-torsion field `L = F_λ(E_λ[ℓ])`. -/
abbrev L : IntermediateField (P.curve x).F (P.curve x).Fbar := (repOf P x hℓ).torsionField

/-- The curve `E_λ` over `L`. -/
abbrev WL : WeierstrassCurve (L P x hℓ) := curveK (P.curve x).E (L P x hℓ)

/-- `E_λ` over `L` is the Legendre curve of `λ`. -/
lemma WL_eq : WL P x hℓ = legendre (algebraMap (P.curve x).F (L P x hℓ) (genC' P x)) :=
  legendre_map _ _

/-- The subgroup `H ∩ E(L)`. -/
abbrev HL (H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar))) :
    AddSubgroup (WL P x hℓ).toAffine.Point :=
  H.comap (repOf P x hℓ).bcKR

variable {P x hℓ}
variable {H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar))}

/-- A subgroup of order `ℓ` of `E(F̄)` consists of `ℓ`-torsion points. -/
lemma mem_torsion_of_card (hH : Nat.card H = ℓ) {Q : Affine.Point (Affine.baseChange
    (P.curve x).E (P.curve x).Fbar)} (hQ : Q ∈ H) : Q ∈ (repOf P x hℓ).TFbarR := by
  rw [AddSubgroup.torsionBy.nsmul_iff, ← hH]
  have := card_nsmul_eq_zero' (G := H) (x := ⟨Q, hQ⟩)
  have h := congrArg Subtype.val this
  rwa [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero] at h

/-- `H ∩ E(L)` has `ℓ` elements. -/
lemma card_HL (hH : Nat.card H = ℓ) : Nat.card (HL P x hℓ H) = ℓ := by
  refine Eq.trans ?_ hH
  refine Nat.card_congr (Equiv.ofBijective (fun Q => ⟨(repOf P x hℓ).bcKR Q.1, Q.2⟩) ⟨?_, ?_⟩)
  · intro Q Q' h
    exact Subtype.ext ((repOf P x hℓ).bcKR_injective (congrArg Subtype.val h))
  · intro Q
    obtain ⟨P', hP'⟩ := (repOf P x hℓ).exists_bcKR_eq Q.1 (mem_torsion_of_card hH Q.2)
    exact ⟨⟨P', by rw [AddSubgroup.mem_comap, hP']; exact Q.2⟩, Subtype.ext hP'⟩

lemma finite_HL (hH : Nat.card H = ℓ) : Finite (HL P x hℓ H) :=
  Nat.finite_of_card_ne_zero (by rw [card_HL hH]; exact hℓ.ne_zero)

/-! ### Square roots in `F_λ` and the points of order `2` and `4` -/

variable (P x hℓ)

/-- `√λ ∈ F_λ`. -/
def sqrtLam : (P.curve x).F :=
  Classical.choose (exists_sq_eq_genC x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1))

lemma sqrtLam_sq : sqrtLam P x ^ 2 = genC' P x :=
  Classical.choose_spec (exists_sq_eq_genC x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1))

/-- `√(1 − λ) ∈ F_λ`. -/
def sqrtOneSub : (P.curve x).F :=
  Classical.choose (exists_sq_eq_one_sub_genC x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1))

lemma sqrtOneSub_sq : sqrtOneSub P x ^ 2 = 1 - genC' P x :=
  Classical.choose_spec
    (exists_sq_eq_one_sub_genC x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1))

/-- `√−1 ∈ F_λ`. -/
def sqrtNegOne : (P.curve x).F :=
  Classical.choose (sqrt_neg_one x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1))

lemma sqrtNegOne_sq : sqrtNegOne P x ^ 2 = -1 := by
  rw [sq]
  exact (Classical.choose_spec (sqrt_neg_one x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1))).symm

lemma genC'_ne_zero : genC' P x ≠ 0 := gen'_ne_zero x.2.1
lemma genC'_ne_one : genC' P x ≠ 1 := gen'_ne_one x.2.2

/-- `λ` in `L`. -/
abbrev lamL : L P x hℓ := algebraMap (P.curve x).F (L P x hℓ) (genC' P x)

lemma lamL_ne_zero : lamL P x hℓ ≠ 0 := (map_ne_zero _).mpr (genC'_ne_zero P x)
lemma lamL_ne_one : lamL P x hℓ ≠ 1 := by
  rw [ne_eq, ← map_one (algebraMap (P.curve x).F (L P x hℓ)),
    (algebraMap (P.curve x).F (L P x hℓ)).injective.eq_iff]
  exact genC'_ne_one P x

/-- `T₁ = (0, 0)`. -/
def T₁ : (WL P x hℓ).toAffine.Point := pt₁ (WL_eq P x hℓ)
/-- `T₂ = (1, 0)`. -/
def T₂ : (WL P x hℓ).toAffine.Point := pt₂ (WL_eq P x hℓ)
/-- `R₁ = (√λ, √−1 √λ (√λ − 1))`, with `2R₁ = T₁`. -/
def R₁ : (WL P x hℓ).toAffine.Point :=
  half₁ (WL_eq P x hℓ) (s := algebraMap _ (L P x hℓ) (sqrtLam P x))
    (i := algebraMap _ (L P x hℓ) (sqrtNegOne P x)) (by rw [← map_pow, sqrtLam_sq])
    (by rw [← map_pow, sqrtNegOne_sq, map_neg, map_one])
/-- `R₂ = (1 + √(1 − λ), √(1 − λ)(1 + √(1 − λ)))`, with `2R₂ = T₂`. -/
def R₂ : (WL P x hℓ).toAffine.Point :=
  half₂ (WL_eq P x hℓ) (s := algebraMap _ (L P x hℓ) (sqrtOneSub P x))
    (by rw [← map_pow, sqrtOneSub_sq, map_sub, map_one])

lemma T₁_ne_zero : T₁ P x hℓ ≠ 0 := pt₁_ne_zero _
lemma T₂_ne_zero : T₂ P x hℓ ≠ 0 := pt₂_ne_zero _
lemma T₁_add_self : T₁ P x hℓ + T₁ P x hℓ = 0 := pt₁_add_self _
lemma T₂_add_self : T₂ P x hℓ + T₂ P x hℓ = 0 := pt₂_add_self _
lemma R₁_add_self : R₁ P x hℓ + R₁ P x hℓ = T₁ P x hℓ :=
  half₁_add_self _ (lamL_ne_zero P x hℓ) (lamL_ne_one P x hℓ) _ _
lemma R₂_add_self : R₂ P x hℓ + R₂ P x hℓ = T₂ P x hℓ :=
  half₂_add_self _ (lamL_ne_zero P x hℓ) (lamL_ne_one P x hℓ) _
lemma T₁_ne_T₂ : T₁ P x hℓ ≠ T₂ P x hℓ := by
  intro h
  have := congrArg xOf h
  simp only [T₁, T₂, xOf_pt₁, xOf_pt₂] at this
  exact zero_ne_one this

lemma xOf_T₁_sub_R₁ : xOf (T₁ P x hℓ) - xOf (R₁ P x hℓ) =
    -algebraMap _ (L P x hℓ) (sqrtLam P x) := by
  simp [T₁, R₁]

lemma xOf_T₂_sub_R₂ : xOf (T₂ P x hℓ) - xOf (R₂ P x hℓ) =
    -algebraMap _ (L P x hℓ) (sqrtOneSub P x) := by
  simp [T₂, R₂]

/-! ### Galois invariance of the Vélu ratios -/

instance : FiniteDimensional (P.curve x).F (L P x hℓ) :=
  Module.Finite.of_restrictScalars_finite ℚ _ _

lemma xOf_galK (σ : L P x hℓ ≃ₐ[(P.curve x).F] L P x hℓ) (Q : (WL P x hℓ).toAffine.Point) :
    xOf (galK (P.curve x).E (L P x hℓ) σ Q) = σ (xOf Q) := by
  rcases Q with _ | ⟨a, b, h⟩
  · change xOf (galK (P.curve x).E (L P x hℓ) σ 0) = σ (xOf (0 : (WL P x hℓ).toAffine.Point))
    rw [map_zero, xOf_zero, map_zero]
  · rfl

/-- A point with Galois-fixed coordinates is fixed. -/
lemma galK_some_of_fixed (σ : L P x hℓ ≃ₐ[(P.curve x).F] L P x hℓ) {a b : L P x hℓ}
    (h : (WL P x hℓ).toAffine.Nonsingular a b) (ha : σ a = a) (hb : σ b = b) :
    galK (P.curve x).E (L P x hℓ) σ (Affine.Point.some a b h) = Affine.Point.some a b h := by
  show Affine.Point.some (σ a) (σ b) _ = _
  congr 1

lemma galK_T₁ (σ : L P x hℓ ≃ₐ[(P.curve x).F] L P x hℓ) :
    galK (P.curve x).E (L P x hℓ) σ (T₁ P x hℓ) = T₁ P x hℓ := by
  unfold T₁ pt₁ Affine.Point.mk
  exact galK_some_of_fixed P x hℓ σ _ (by simp) (by simp)

lemma galK_T₂ (σ : L P x hℓ ≃ₐ[(P.curve x).F] L P x hℓ) :
    galK (P.curve x).E (L P x hℓ) σ (T₂ P x hℓ) = T₂ P x hℓ := by
  unfold T₂ pt₂ Affine.Point.mk
  exact galK_some_of_fixed P x hℓ σ _ (by simp) (by simp)

lemma galK_R₁ (σ : L P x hℓ ≃ₐ[(P.curve x).F] L P x hℓ) :
    galK (P.curve x).E (L P x hℓ) σ (R₁ P x hℓ) = R₁ P x hℓ := by
  unfold R₁ half₁ Affine.Point.mk
  exact galK_some_of_fixed P x hℓ σ _ (by simp) (by simp)

lemma galK_R₂ (σ : L P x hℓ ≃ₐ[(P.curve x).F] L P x hℓ) :
    galK (P.curve x).E (L P x hℓ) σ (R₂ P x hℓ) = R₂ P x hℓ := by
  unfold R₂ half₂ Affine.Point.mk
  exact galK_some_of_fixed P x hℓ σ _ (by simp) (by simp)

variable {P x hℓ}

/-- A Galois-stable `H` gives a `Gal(L/F)`-stable `H ∩ E(L)`. -/
lemma galK_mem_HL
    (hgal : ∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
      galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H)
    (σ : L P x hℓ ≃ₐ[(P.curve x).F] L P x hℓ) {Q : (WL P x hℓ).toAffine.Point}
    (hQ : Q ∈ HL P x hℓ H) : galK (P.curve x).E (L P x hℓ) σ Q ∈ HL P x hℓ H := by
  obtain ⟨τ, rfl⟩ := (repOf P x hℓ).restrictKR_surjective σ
  rw [AddSubgroup.mem_comap, (repOf P x hℓ).bcKR_galK]
  exact hgal τ _ hQ

/-- **The Vélu ratio is Galois-invariant** for points `T`, `R` fixed by the Galois group. -/
lemma veluRatio_galois [Fintype (HL P x hℓ H)]
    (hgal : ∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
      galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H)
    (σ : L P x hℓ ≃ₐ[(P.curve x).F] L P x hℓ) {T R : (WL P x hℓ).toAffine.Point}
    (hT : galK (P.curve x).E (L P x hℓ) σ T = T) (hR : galK (P.curve x).E (L P x hℓ) σ R = R) :
    σ (veluRatio (HL P x hℓ H) T R) = veluRatio (HL P x hℓ H) T R := by
  set g := galK (P.curve x).E (L P x hℓ) σ
  set g' := galK (P.curve x).E (L P x hℓ) σ.symm
  have hgg' : ∀ Q, g (g' Q) = Q := by
    rintro (_ | ⟨a, b, h⟩)
    · rfl
    · show Affine.Point.some (σ (σ.symm a)) (σ (σ.symm b)) _ = _
      congr 1 <;> simp
  have hg'g : ∀ Q, g' (g Q) = Q := by
    rintro (_ | ⟨a, b, h⟩)
    · rfl
    · show Affine.Point.some (σ.symm (σ a)) (σ.symm (σ b)) _ = _
      congr 1 <;> simp
  unfold veluRatio
  rw [map_prod]
  refine Finset.prod_nbij' (fun Q => ⟨g Q, galK_mem_HL hgal σ Q.2⟩)
    (fun Q => ⟨g' Q, galK_mem_HL hgal σ.symm Q.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro Q hQ
    rw [mem_nonzero] at hQ ⊢
    intro h
    apply hQ
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp only [ZeroMemClass.coe_zero] at this ⊢
    rw [← hg'g Q, this, map_zero]
  · intro Q hQ
    rw [mem_nonzero] at hQ ⊢
    intro h
    apply hQ
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp only [ZeroMemClass.coe_zero] at this ⊢
    rw [← hgg' Q, this, map_zero]
  · intro Q _; exact Subtype.ext (hg'g Q)
  · intro Q _; exact Subtype.ext (hgg' Q)
  · intro Q _
    rw [map_div₀, map_sub, map_sub, ← xOf_galK, ← xOf_galK, ← xOf_galK, map_add, hT, hR]

/-- **The product of the two Vélu ratios lies in `F`.** -/
lemma exists_algebraMap_eq_ratio [Fintype (HL P x hℓ H)]
    (hgal : ∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
      galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H) :
    ∃ ρ : (P.curve x).F, algebraMap _ (L P x hℓ) ρ =
      veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ) *
        veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ) := by
  have hfix : ∀ σ : L P x hℓ ≃ₐ[(P.curve x).F] L P x hℓ,
      σ (veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ) *
        veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ)) =
      veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ) *
        veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ) := by
    intro σ
    rw [map_mul, veluRatio_galois hgal σ (galK_T₁ P x hℓ σ) (galK_R₁ P x hℓ σ),
      veluRatio_galois hgal σ (galK_T₂ P x hℓ σ) (galK_R₂ P x hℓ σ)]
  have hbot := (IsGalois.mem_bot_iff_fixed _).mpr hfix
  obtain ⟨ρ, hρ⟩ := IntermediateField.mem_bot.mp hbot
  exact ⟨ρ, hρ⟩

/-! ### Torsion points in `H ∩ E(L)` translates -/

variable [Fintype (HL P x hℓ H)]

lemma nsmul_ℓ_eq_zero (hH : Nat.card H = ℓ) (Q : HL P x hℓ H) : ℓ • (Q : (WL P x hℓ).toAffine.Point) = 0 := by
  have h := card_nsmul_eq_zero (x := Q)
  rw [Fintype.card_eq_nat_card, card_HL hH] at h
  have := congrArg Subtype.val h
  rwa [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero] at this

lemma odd_card_HL (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) : Odd (Fintype.card (HL P x hℓ H)) := by
  rw [Fintype.card_eq_nat_card, card_HL hH]
  exact hℓ.odd_of_ne_two hℓ2

/-- The translates `T + Q`, `R + Q` (`Q ∈ H ∩ E(L)`) of a point `T` of order `2` and a half `R`
of it are nonzero `4ℓ`-torsion points. -/
lemma translate_torsion (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) {T R : (WL P x hℓ).toAffine.Point}
    (hT0 : T ≠ 0) (hT2 : T + T = 0) (hRT : R + R = T) (Q : HL P x hℓ H) :
    (T + (Q : (WL P x hℓ).toAffine.Point) ≠ 0 ∧
      (4 * ℓ) • (T + (Q : (WL P x hℓ).toAffine.Point)) = 0) ∧
    (R + (Q : (WL P x hℓ).toAffine.Point) ≠ 0 ∧
      (4 * ℓ) • (R + (Q : (WL P x hℓ).toAffine.Point)) = 0) := by
  have hodd := odd_card_HL hH hℓ2
  have hT : T ∉ HL P x hℓ H := notMem_of_add_self _ hodd hT0 hT2
  have hR : R ∉ HL P x hℓ H := fun hR => hT (hRT ▸ (HL P x hℓ H).add_mem hR hR)
  have hQ := nsmul_ℓ_eq_zero hH Q
  have h2T : 2 • T = 0 := by rw [two_nsmul, hT2]
  have h4R : 4 • R = 0 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul, two_nsmul R, hRT, h2T]
  have h4ℓQ : (4 * ℓ) • (Q : (WL P x hℓ).toAffine.Point) = 0 := by
    rw [mul_comm, mul_nsmul, hQ, nsmul_zero]
  refine ⟨⟨fun h => hT ?_, ?_⟩, ⟨fun h => hR ?_, ?_⟩⟩
  · rw [eq_neg_of_add_eq_zero_left h]; exact (HL P x hℓ H).neg_mem Q.2
  · rw [nsmul_add, h4ℓQ, add_zero, show 4 * ℓ = 2 * (2 * ℓ) by ring, mul_nsmul, h2T,
      nsmul_zero]
  · rw [eq_neg_of_add_eq_zero_left h]; exact (HL P x hℓ H).neg_mem Q.2
  · rw [nsmul_add, h4ℓQ, add_zero, mul_nsmul, h4R, nsmul_zero]

/-- The Newton bound for a nonzero `4ℓ`-torsion point of `E(L)`. -/
lemma apply_xOf_le (w : FinitePlace (L P x hℓ)) {S : (WL P x hℓ).toAffine.Point} (hS0 : S ≠ 0)
    (hS : (4 * ℓ) • S = 0) :
    w (((4 * ℓ : ℕ) : L P x hℓ)) ^ 2 * w (xOf S) ≤ max 1 (w (lamL P x hℓ)) ^ 2 := by
  rcases S with _ | ⟨a, b, h⟩
  · exact absurd rfl hS0
  · exact TorsionNewton.apply_x_le_legendre w (WL_eq P x hℓ) (lamL_ne_zero P x hℓ)
      (by have := hℓ.one_lt; omega) h hS

/-- **The crude bound at a finite place of `L`**: `|r|_w |x(T) − x(R)|_w |4ℓ|_w² ≤ max(1, |λ|_w)²`
for the Vélu ratio `r` of a point `T` of order `2` and a half `R`. -/
lemma crude_bound (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) (w : FinitePlace (L P x hℓ))
    {T R : (WL P x hℓ).toAffine.Point} (hT0 : T ≠ 0) (hT2 : T + T = 0) (hRT : R + R = T) :
    w (veluRatio (HL P x hℓ H) T R) * w (xOf T - xOf R) * w (((4 * ℓ : ℕ) : L P x hℓ)) ^ 2 ≤
      max 1 (w (lamL P x hℓ)) ^ 2 := by
  have hodd := odd_card_HL hH hℓ2
  have hmul := veluRatio_mul (two_ne_zero) hodd hT0 hT2 hRT
  have hn0 : 0 < w (((4 * ℓ : ℕ) : L P x hℓ)) := by
    rw [FinitePlace.pos_iff]
    exact_mod_cast (show 4 * ℓ ≠ 0 by have := hℓ.pos; omega)
  set B : ℝ := max 1 (w (lamL P x hℓ)) ^ 2 / w (((4 * ℓ : ℕ) : L P x hℓ)) ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hterm : ∀ S : (WL P x hℓ).toAffine.Point, S ≠ 0 → (4 * ℓ) • S = 0 → w (xOf S) ≤ B := by
    intro S hS0 hS
    rw [hB, le_div_iff₀ (by positivity), mul_comm]
    exact apply_xOf_le w hS0 hS
  have hsum : w (∑ Q : HL P x hℓ H, xOf (T + (Q : (WL P x hℓ).toAffine.Point)) -
      ∑ Q : HL P x hℓ H, xOf (R + (Q : (WL P x hℓ).toAffine.Point))) ≤ B := by
    rw [← Finset.sum_sub_distrib]
    refine TorsionNewton.apply_sum_le w _ _ hB0 fun Q _ => ?_
    obtain ⟨⟨hT0', hT'⟩, ⟨hR0', hR'⟩⟩ := translate_torsion hH hℓ2 hT0 hT2 hRT Q
    rw [sub_eq_add_neg]
    refine (FinitePlace.add_le w _ _).trans (max_le (hterm _ hT0' hT') ?_)
    rw [map_neg_eq_map]
    exact hterm _ hR0' hR'
  rw [← hmul, map_mul] at hsum
  rw [hB, le_div_iff₀ (by positivity)] at hsum
  exact hsum

/-- **The archimedean bound**: at an infinite place `v` of `L` with `|log|λ|_v|,
|log|λ − 1|_v| ≤ c`, `|r|_v |x(T) − x(R)|_v ≤ 2ℓ · C₀ (4ℓ)²`, where `C₀` bounds the torsion
`x`-coordinates of the Legendre curves with parameters bounded by `c`
(`Iut.CyclicArch.legendre_torsion_x_le`). -/
lemma arch_bound (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) {c C₀ : ℝ}
    (hC₀ : ∀ (l : ℂ), |Real.log ‖l‖| ≤ c → |Real.log ‖l - 1‖| ≤ c →
      ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic], W = legendre l →
      ∀ {N : ℕ}, 1 ≤ N → ∀ {a b : ℂ} (h : W.toAffine.Nonsingular a b),
        N • (Affine.Point.some a b h : W.toAffine.Point) = 0 → ‖a‖ ≤ C₀ * N ^ 2)
    (v : InfinitePlace (L P x hℓ)) (hv₁ : |Real.log (v (lamL P x hℓ))| ≤ c)
    (hv₂ : |Real.log (v (lamL P x hℓ - 1))| ≤ c)
    {T R : (WL P x hℓ).toAffine.Point} (hT0 : T ≠ 0) (hT2 : T + T = 0) (hRT : R + R = T) :
    v (veluRatio (HL P x hℓ H) T R) * v (xOf T - xOf R) ≤ 2 * ℓ * (C₀ * (4 * ℓ) ^ 2) := by
  have hodd := odd_card_HL hH hℓ2
  have hmul := veluRatio_mul (two_ne_zero) hodd hT0 hT2 hRT
  set φ := v.embedding
  have hW : (WL P x hℓ).map φ = legendre (φ (lamL P x hℓ)) := by
    rw [WL_eq, legendre_map]
  have hl₁ : |Real.log ‖φ (lamL P x hℓ)‖| ≤ c := by rwa [InfinitePlace.norm_embedding_eq]
  have hl₂ : |Real.log ‖φ (lamL P x hℓ) - 1‖| ≤ c := by
    rwa [← map_one φ, ← map_sub, InfinitePlace.norm_embedding_eq]
  have hterm : ∀ S : (WL P x hℓ).toAffine.Point, S ≠ 0 → (4 * ℓ) • S = 0 →
      v (xOf S) ≤ C₀ * (4 * ℓ) ^ 2 := by
    intro S hS0 hS
    rcases S with _ | ⟨a, b, h⟩
    · exact absurd rfl hS0
    · have hS' : (4 * ℓ) • pointMap (WL P x hℓ) φ (Affine.Point.some a b h) = 0 := by
        rw [← map_nsmul, hS, map_zero]
      rw [pointMap_some] at hS'
      have := hC₀ _ hl₁ hl₂ _ hW (by have := hℓ.one_lt; omega) _ hS'
      rw [← InfinitePlace.norm_embedding_eq]
      exact_mod_cast this
  rw [← map_mul, hmul, ← Finset.sum_sub_distrib, ← InfinitePlace.norm_embedding_eq, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have hcard : (Finset.univ : Finset (HL P x hℓ H)).card = ℓ := by
    rw [Finset.card_univ, Fintype.card_eq_nat_card, card_HL hH]
  calc ∑ Q : HL P x hℓ H, ‖φ (xOf (T + (Q : (WL P x hℓ).toAffine.Point)) -
        xOf (R + (Q : (WL P x hℓ).toAffine.Point)))‖
      ≤ ∑ _Q : HL P x hℓ H, 2 * (C₀ * (4 * ℓ) ^ 2) := by
        refine Finset.sum_le_sum fun Q _ => ?_
        obtain ⟨⟨hT0', hT'⟩, ⟨hR0', hR'⟩⟩ := translate_torsion hH hℓ2 hT0 hT2 hRT Q
        rw [map_sub]
        refine (norm_sub_le _ _).trans ?_
        rw [InfinitePlace.norm_embedding_eq, InfinitePlace.norm_embedding_eq]
        linarith [hterm _ hT0' hT', hterm _ hR0' hR']
    _ = 2 * ℓ * (C₀ * (4 * ℓ) ^ 2) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring

/-- **The gain at a place of `L` over an odd multiplicative place**:
`(|r₁|_w |r₂|_w)⁴ |j|_w^{ℓ − 1} ≤ 1`. -/
lemma tate_bound (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) (hgraph : IsGraphLineOdd P x hℓ hℓ2 H)
    (w : FinitePlace (L P x hℓ))
    (hw : IsBadPlace (P.curve x).E (L P x hℓ) (P.curve x).VBadOdd w) :
    (w (veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ)) *
        w (veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ))) ^ 4 *
      w (algebraMap _ (L P x hℓ) (P.curve x).E.j) ^ (ℓ - 1) ≤ 1 := by
  set S := (tateFamilyOddOf P x hℓ hℓ2).S w hw
  have hodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hcard : Fintype.card (HL P x hℓ H) = ℓ := by rw [Fintype.card_eq_nat_card, card_HL hH]
  have h2 : ‖(2 : localCompletion w)‖ = 1 :=
    norm_two_eq_one_of_notMem (two_notMem_of_isBadPlace (P.curve x).E (L P x hℓ)
      (fun _ hv => hv.1) hw)
  have hgr : ∀ Q ∈ HL P x hℓ H, pointMap (WL P x hℓ) (emb (L P x hℓ) w) Q ∈ S.graphLine ℓ := by
    intro Q hQ
    rw [show HL P x hℓ H = _ from hgraph w hw] at hQ
    exact hQ
  have hmain := CyclicTate.ratio_mul_bound (emb (L P x hℓ) w) S (HL P x hℓ H) hodd hcard h2 hgr
    (T₁_ne_zero P x hℓ) (T₁_add_self P x hℓ) (R₁_add_self P x hℓ)
    (T₂_ne_zero P x hℓ) (T₂_add_self P x hℓ) (R₂_add_self P x hℓ) (T₁_ne_T₂ P x hℓ)
  simp only [emb, FinitePlace.norm_embedding_eq] at hmain
  -- `‖q‖ = |j|_w⁻¹`
  have h12 : (12 : localCompletion w) ≠ 0 := twelve_ne_zero w
  have hjE : (P.curve x).E.j = (P.curve x).E.c₄ ^ 3 / (P.curve x).E.Δ := by
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', div_eq_inv_mul]
  have hΔ0 : (P.curve x).E.Δ ≠ 0 := (P.curve x).E.isUnit_Δ.ne_zero
  have hJeq : S.t.tateJ = emb (L P x hℓ) w (algebraMap _ (L P x hℓ) (P.curve x).E.j) := by
    rw [TateCurvesTheta.TateParameter.tateJ_def, ← S.hC, variableChange_c₄, variableChange_Δ,
      map_c₄, map_Δ, map_c₄, map_Δ, hjE, map_div₀, map_div₀, map_pow, map_pow]
    have hΔ' : emb (L P x hℓ) w (algebraMap _ (L P x hℓ) (P.curve x).E.Δ) ≠ 0 :=
      (map_ne_zero _).mpr ((map_ne_zero _).mpr hΔ0)
    have hu : ((S.C.u⁻¹ : (localCompletion w)ˣ) : localCompletion w) ≠ 0 := Units.ne_zero _
    field_simp
  have hq : ‖(S.t.q : localCompletion w)‖ = (w (algebraMap _ (L P x hℓ) (P.curve x).E.j))⁻¹ := by
    have hJ := S.t.norm_tateJ h12
    rw [hJeq, FinitePlace.norm_embedding_eq] at hJ
    rw [hJ, inv_inv]
  rw [hq, inv_pow] at hmain
  have hj0 : 0 < w (algebraMap _ (L P x hℓ) (P.curve x).E.j) ^ (ℓ - 1) := by
    refine pow_pos ?_ _
    by_contra h0
    have h00 : w (algebraMap _ (L P x hℓ) (P.curve x).E.j) = 0 :=
      le_antisymm (not_lt.mp h0) (apply_nonneg _ _)
    have := S.t.norm_q_pos
    rw [hq, h00, inv_zero] at this
    exact lt_irrefl _ this
  have := mul_le_mul_of_nonneg_right hmain hj0.le
  rwa [inv_mul_cancel₀ hj0.ne'] at this

/-! ### Transport to the places of `F_λ` -/

variable (P x) in
/-- The compactly bounded condition at the infinite places of `F_λ`. -/
lemma abs_log_infinite_le {K : CompactlyBounded} (hx : x ∈ K.set)
    (v : InfinitePlace (P.curve x).F) :
    |Real.log (v (genC' P x))| ≤ K.c ∧ |Real.log (v (genC' P x - 1))| ≤ K.c := by
  let f : tpd P x →+* (P.curve x).F := algebraMap (tpd P x) (P.curve x).F
  let g : fieldOf x.1 →+* tpd P x := ((tpdEquiv P x).symm : fieldOf x.1 ≃+* tpd P x)
  let w₁ : InfinitePlace (fieldOf x.1) := (v.comap f).comap g
  have hg : g (gen x.1) = genT P x := tpdEquiv_symm_gen P x
  have hf : f (genT P x) = genC' P x := algebraMap_genT P x
  have h₁ : w₁ (gen x.1) = v (genC' P x) := by
    rw [InfinitePlace.comap_apply, InfinitePlace.comap_apply, hg, hf]
  have h₂ : w₁ (gen x.1 - 1) = v (genC' P x - 1) := by
    rw [InfinitePlace.comap_apply, InfinitePlace.comap_apply, map_sub, map_one, map_sub, map_one,
      hg, hf]
  rw [← h₁, ← h₂]
  exact hx.2 w₁

variable (P x) in
/-- The compactly bounded condition at the places of `F_λ` over `2`:
`|log|λ|_v|, |log|λ − 1|_v| ≤ c·[F_v : ℚ_2]`. -/
lemma abs_log_two_le {K : CompactlyBounded} (hx : x ∈ K.set) (v : FinitePlace (P.curve x).F)
    (hv : residueChar v = 2) :
    |Real.log (v (genC' P x))| ≤ K.c * localDeg (P.curve x).F v ∧
      |Real.log (v (genC' P x - 1))| ≤ K.c * localDeg (P.curve x).F v := by
  set 𝔭 : FinitePlace (tpd P x) := placeUnder v
  have hv𝔭 : FinitePlace.LiesOver v 𝔭 := liesOver_placeUnder v
  have h𝔭2 : residueChar 𝔭 = 2 := by rw [← residueChar_eq_of_liesOver hv𝔭, hv]
  have hb := hx.1 (tpdPlace P x 𝔭) (by rw [residueChar_tpdPlace, h𝔭2]; exact K.two_mem)
  rw [tpdPlace_gen, tpdPlace_gen_sub_one] at hb
  have hc : 0 ≤ K.c := CompactlyBounded.c_nonneg hx
  have hd : (relLocalDeg v 𝔭 : ℝ) ≤ localDeg (P.curve x).F v := by
    rw [localDeg_eq_mul hv𝔭]
    have : 1 ≤ localDeg (tpd P x) 𝔭 := Nat.mul_pos (ramIdx_pos' 𝔭) (inertDeg_pos' 𝔭)
    exact_mod_cast Nat.le_mul_of_pos_left _ this
  have hlog : ∀ y : tpd P x, y ≠ 0 → |Real.log (v (algebraMap _ (P.curve x).F y))| =
      relLocalDeg v 𝔭 * |Real.log (𝔭 y)| := by
    intro y hy
    rw [apply_algebraMap_eq_pow hv𝔭, Real.log_pow, abs_mul, Nat.abs_cast]
  have e₁ := hlog _ (genT_ne_zero P x)
  have e₂ := hlog _ (genT_sub_one_ne_zero P x)
  rw [algebraMap_genT] at e₁
  rw [map_sub, map_one, algebraMap_genT] at e₂
  rw [e₁, e₂]
  constructor
  · calc (relLocalDeg v 𝔭 : ℝ) * |Real.log (𝔭 (genT P x))| ≤ localDeg (P.curve x).F v * K.c :=
          mul_le_mul hd hb.1 (abs_nonneg _) (by positivity)
      _ = _ := mul_comm _ _
  · calc (relLocalDeg v 𝔭 : ℝ) * |Real.log (𝔭 (genT P x - 1))| ≤ localDeg (P.curve x).F v * K.c :=
          mul_le_mul hd hb.2 (abs_nonneg _) (by positivity)
      _ = _ := mul_comm _ _

/-- `|y|_v = 1` iff `v(y) = 1` for the valuation. -/
lemma apply_eq_one_of_valuation_eq_one {T : Type*} [Field T] [NumberField T] (v : FinitePlace T)
    {y : T} (hy : v.maximalIdeal.valuation T y = 1) : v y = 1 := by
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact zero_ne_one hy
  have hlog := log_apply_eq v hy0
  rw [hy, WithZero.log_one, Int.cast_zero, zero_mul] at hlog
  have hpos : 0 < v y := FinitePlace.pos_iff.mpr hy0
  rw [← Real.exp_log hpos, hlog, Real.exp_zero]

variable (P x) in
/-- **At a place of good reduction of odd residue characteristic, `λ` and `λ − 1` are units.** -/
lemma apply_genC_eq_one {v : FinitePlace (P.curve x).F} (hv : v ∉ (P.curve x).badAll)
    (h2 : residueChar v ≠ 2) : v (genC' P x) = 1 ∧ v (genC' P x - 1) = 1 := by
  have hst := (P.arith x).stable_reduction v
  have hle : v.maximalIdeal.valuation _ (P.curve x).E.j ≤ 1 := by
    by_contra h
    exact hv ((hasMultiplicativeReductionAt_iff_of_stable (P.curve x).E v hst).mpr h)
  have hval : v.maximalIdeal.valuation _ (genC' P x) = 1 ∧
      v.maximalIdeal.valuation _ (genC' P x - 1) = 1 := by
    by_contra h
    rw [not_and_or] at h
    have := one_lt_valuation_legendre_j (v.maximalIdeal.valuation (P.curve x).F)
      (l := genC' P x) (valuation_two_eq_one v h2) h
    exact absurd hle (not_le.mpr this)
  exact ⟨apply_eq_one_of_valuation_eq_one v hval.1, apply_eq_one_of_valuation_eq_one v hval.2⟩

/-! ### The local bounds for `ρ = r₁r₂ ∈ F_λ` -/

/-- `|n|_v ≤ 1` at a finite place. -/
lemma apply_natCast_le_one {T : Type*} [Field T] [NumberField T] (v : FinitePlace T) (n : ℕ) :
    v (n : T) ≤ 1 :=
  IsNonarchimedean.apply_natCast_le_one (f := v) (fun a b => FinitePlace.add_le v a b)

/-- `max(1, a)^d = max(1, a^d)` for `a ≥ 0`. -/
lemma max_one_pow {a : ℝ} (ha : 0 ≤ a) (d : ℕ) : max 1 a ^ d = max 1 (a ^ d) := by
  rcases le_total a 1 with h | h
  · rw [max_eq_left h, one_pow, max_eq_left (pow_le_one₀ ha h)]
  · rw [max_eq_right h, max_eq_right (one_le_pow₀ h)]

section Local

variable {ρ : (P.curve x).F}
  (hρ : algebraMap _ (L P x hℓ) ρ = veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ) *
    veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ))
include hρ

/-- **The crude bound at a finite place of `F_λ`**:
`|ρ|_v |√λ|_v |√(1 − λ)|_v |4ℓ|_v⁴ ≤ max(1, |λ|_v)⁴`. -/
lemma finite_crude (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) (v : FinitePlace (P.curve x).F) :
    v ρ * (v (sqrtLam P x) * v (sqrtOneSub P x) * v (((4 * ℓ : ℕ) : (P.curve x).F)) ^ 4) ≤
      max 1 (v (genC' P x)) ^ 4 := by
  obtain ⟨w, hwv⟩ := FinitePlace.exists_liesOver (K := L P x hℓ) v
  set d := relLocalDeg w v
  have hd : d ≠ 0 := relLocalDeg_ne_zero hwv
  have htr : ∀ y : (P.curve x).F, w (algebraMap _ (L P x hℓ) y) = v y ^ d :=
    apply_algebraMap_eq_pow hwv
  have c₁ := crude_bound (H := H) hH hℓ2 w (T₁_ne_zero P x hℓ) (T₁_add_self P x hℓ)
    (R₁_add_self P x hℓ)
  have c₂ := crude_bound (H := H) hH hℓ2 w (T₂_ne_zero P x hℓ) (T₂_add_self P x hℓ)
    (R₂_add_self P x hℓ)
  rw [xOf_T₁_sub_R₁, map_neg_eq_map, htr] at c₁
  rw [xOf_T₂_sub_R₂, map_neg_eq_map, htr] at c₂
  rw [← map_natCast (algebraMap (P.curve x).F (L P x hℓ)), htr, htr,
    ← max_one_pow (apply_nonneg _ _)] at c₁ c₂
  have hprod : (v ρ * (v (sqrtLam P x) * v (sqrtOneSub P x) *
      v (((4 * ℓ : ℕ) : (P.curve x).F)) ^ 4)) ^ d ≤ (max 1 (v (genC' P x)) ^ 4) ^ d := by
    have hmul := mul_le_mul c₁ c₂ (by positivity) (by positivity)
    rw [mul_pow, ← htr ρ, hρ, map_mul]
    calc _ = (w (veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ)) * v (sqrtLam P x) ^ d *
            (v (((4 * ℓ : ℕ) : (P.curve x).F)) ^ d) ^ 2) *
          (w (veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ)) * v (sqrtOneSub P x) ^ d *
            (v (((4 * ℓ : ℕ) : (P.curve x).F)) ^ d) ^ 2) := by ring
      _ ≤ (max 1 (v (genC' P x)) ^ d) ^ 2 * (max 1 (v (genC' P x)) ^ d) ^ 2 := hmul
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) hd).mp hprod

/-- **The gain at an odd multiplicative place of `F_λ`**: `|ρ|_v⁴ |j|_v^{ℓ − 1} ≤ 1`. -/
lemma finite_tate (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) (hgraph : IsGraphLineOdd P x hℓ hℓ2 H)
    {v : FinitePlace (P.curve x).F} (hv : v ∈ (P.curve x).badAll) (h2 : residueChar v ≠ 2) :
    v ρ ^ 4 * v (P.curve x).E.j ^ (ℓ - 1) ≤ 1 := by
  obtain ⟨w, hwv⟩ := FinitePlace.exists_liesOver (K := L P x hℓ) v
  set d := relLocalDeg w v
  have hd : d ≠ 0 := relLocalDeg_ne_zero hwv
  have htr : ∀ y : (P.curve x).F, w (algebraMap _ (L P x hℓ) y) = v y ^ d :=
    apply_algebraMap_eq_pow hwv
  obtain ⟨v₀, hv₀, hvv₀⟩ := (P.curve x).exists_mem_VBadOdd (P.arith x) hv h2
  have hw : IsBadPlace (P.curve x).E (L P x hℓ) (P.curve x).VBadOdd w :=
    ⟨v₀, hv₀, FinitePlace.liesOver_trans hwv hvv₀⟩
  have hb := tate_bound hH hℓ2 hgraph w hw
  rw [← map_mul, ← hρ, htr, htr] at hb
  have : (v ρ ^ 4 * v (P.curve x).E.j ^ (ℓ - 1)) ^ d ≤ 1 ^ d := by
    rw [one_pow]
    calc (v ρ ^ 4 * v (P.curve x).E.j ^ (ℓ - 1)) ^ d
        = (v ρ ^ d) ^ 4 * (v (P.curve x).E.j ^ d) ^ (ℓ - 1) := by ring
      _ ≤ 1 := hb
  exact (pow_le_pow_iff_left₀ (by positivity) zero_le_one hd).mp this

/-- **The archimedean bound at an infinite place of `F_λ`**:
`|ρ|_v |√λ|_v |√(1 − λ)|_v ≤ (2ℓ C₀ (4ℓ)²)²`. -/
lemma infinite_bound (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) {c C₀ : ℝ}
    (hC₀ : ∀ (l : ℂ), |Real.log ‖l‖| ≤ c → |Real.log ‖l - 1‖| ≤ c →
      ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic], W = legendre l →
      ∀ {N : ℕ}, 1 ≤ N → ∀ {a b : ℂ} (h : W.toAffine.Nonsingular a b),
        N • (Affine.Point.some a b h : W.toAffine.Point) = 0 → ‖a‖ ≤ C₀ * N ^ 2)
    (v : InfinitePlace (P.curve x).F) (hv₁ : |Real.log (v (genC' P x))| ≤ c)
    (hv₂ : |Real.log (v (genC' P x - 1))| ≤ c) :
    v ρ * (v (sqrtLam P x) * v (sqrtOneSub P x)) ≤ (2 * ℓ * (C₀ * (4 * ℓ) ^ 2)) ^ 2 := by
  obtain ⟨w, hwv⟩ := InfinitePlace.comap_surjective (K := L P x hℓ) v
  have htr : ∀ y : (P.curve x).F, w (algebraMap _ (L P x hℓ) y) = v y := by
    intro y; rw [← hwv, InfinitePlace.comap_apply]
  have hw₁ : |Real.log (w (lamL P x hℓ))| ≤ c := by rw [htr]; exact hv₁
  have hw₂ : |Real.log (w (lamL P x hℓ - 1))| ≤ c := by
    rw [← map_one (algebraMap (P.curve x).F (L P x hℓ)), ← map_sub, htr]; exact hv₂
  have a₁ := arch_bound (H := H) hH hℓ2 hC₀ w hw₁ hw₂ (T₁_ne_zero P x hℓ) (T₁_add_self P x hℓ)
    (R₁_add_self P x hℓ)
  have a₂ := arch_bound (H := H) hH hℓ2 hC₀ w hw₁ hw₂ (T₂_ne_zero P x hℓ) (T₂_add_self P x hℓ)
    (R₂_add_self P x hℓ)
  have hneg : ∀ y : L P x hℓ, w (-y) = w y := fun y => by
    rw [← InfinitePlace.norm_embedding_eq, map_neg, norm_neg, InfinitePlace.norm_embedding_eq]
  rw [xOf_T₁_sub_R₁, hneg, htr] at a₁
  rw [xOf_T₂_sub_R₂, hneg, htr] at a₂
  rw [← htr ρ, hρ, map_mul]
  calc w (veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ)) *
        w (veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ)) *
        (v (sqrtLam P x) * v (sqrtOneSub P x))
      = (w (veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ)) * v (sqrtLam P x)) *
        (w (veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ)) * v (sqrtOneSub P x)) := by ring
    _ ≤ (2 * ℓ * (C₀ * (4 * ℓ) ^ 2)) * (2 * ℓ * (C₀ * (4 * ℓ) ^ 2)) :=
        mul_le_mul a₁ a₂ (by positivity) (le_trans (by positivity) a₁)
    _ = _ := by ring

/-- **The local bound in logarithmic form** at a finite place `v` of `F_λ`:
`log|ρ|_v ≤ −[v odd multiplicative]·((ℓ − 1)/4) log|j|_v + [v ∣ 2]·B₂(v) + 4 log|ℓ|_v^{-1}`,
with `B₂(v) = (9/2)|log|λ|_v| + (1/2)|log|λ − 1|_v| + 4 log|4|_v^{-1}`. -/
lemma log_apply_le (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) (hgraph : IsGraphLineOdd P x hℓ hℓ2 H)
    (hρ0 : ρ ≠ 0) (v : FinitePlace (P.curve x).F) :
    Real.log (v ρ) ≤
      (if v ∈ (P.curve x).badAll ∧ residueChar v ≠ 2 then
          -(((ℓ : ℝ) - 1) / 4 * Real.log (v (P.curve x).E.j)) else 0) +
        (if residueChar v = 2 then
          9 / 2 * |Real.log (v (genC' P x))| + 1 / 2 * |Real.log (v (genC' P x - 1))| +
            4 * -Real.log (v (4 : (P.curve x).F)) else 0) +
        4 * -Real.log (v (ℓ : (P.curve x).F)) := by
  have hvρ : 0 < v ρ := FinitePlace.pos_iff.mpr hρ0
  have hℓ0 : (ℓ : (P.curve x).F) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hvℓ : 0 < v (ℓ : (P.curve x).F) := FinitePlace.pos_iff.mpr hℓ0
  have hlogℓ : 0 ≤ -Real.log (v (ℓ : (P.curve x).F)) :=
    neg_nonneg.mpr (Real.log_nonpos hvℓ.le (apply_natCast_le_one v ℓ))
  have hv4 : 0 < v (4 : (P.curve x).F) := FinitePlace.pos_iff.mpr (by norm_num)
  have hlog4 : 0 ≤ -Real.log (v (4 : (P.curve x).F)) :=
    neg_nonneg.mpr (Real.log_nonpos hv4.le (by exact_mod_cast apply_natCast_le_one v 4))
  have hl0 := genC'_ne_zero P x
  have hl1 : genC' P x - 1 ≠ 0 := sub_ne_zero.mpr (genC'_ne_one P x)
  have hvl : 0 < v (genC' P x) := FinitePlace.pos_iff.mpr hl0
  have hvl1 : 0 < v (genC' P x - 1) := FinitePlace.pos_iff.mpr hl1
  have hs₁ : v (sqrtLam P x) ^ 2 = v (genC' P x) := by rw [← map_pow, sqrtLam_sq]
  have hs₂ : v (sqrtOneSub P x) ^ 2 = v (genC' P x - 1) := by
    rw [← map_pow, sqrtOneSub_sq, ← map_neg_eq_map v, neg_sub]
  have hvs₁ : 0 < v (sqrtLam P x) := by
    by_contra h
    have : v (sqrtLam P x) = 0 := le_antisymm (not_lt.mp h) (apply_nonneg _ _)
    rw [this, zero_pow two_ne_zero] at hs₁; linarith
  have hvs₂ : 0 < v (sqrtOneSub P x) := by
    by_contra h
    have : v (sqrtOneSub P x) = 0 := le_antisymm (not_lt.mp h) (apply_nonneg _ _)
    rw [this, zero_pow two_ne_zero] at hs₂; linarith
  have hls₁ : Real.log (v (sqrtLam P x)) = Real.log (v (genC' P x)) / 2 := by
    rw [← hs₁, Real.log_pow]; push_cast; ring
  have hls₂ : Real.log (v (sqrtOneSub P x)) = Real.log (v (genC' P x - 1)) / 2 := by
    rw [← hs₂, Real.log_pow]; push_cast; ring
  by_cases htate : v ∈ (P.curve x).badAll ∧ residueChar v ≠ 2
  · rw [if_pos htate, if_neg htate.2]
    have hb := finite_tate hρ hH hℓ2 hgraph htate.1 htate.2
    have hj1 : 1 < v (P.curve x).E.j := by
      have hpos := posLog_j_eq_of_mem_badAll P x htate.1
      have : 0 < Real.posLog (v (P.curve x).E.j) := by
        rw [hpos]
        have h1 : (0 : ℝ) < (P.tate x).qOrder v htate.1 := by
          exact_mod_cast (P.tate x).qOrder_pos v htate.1
        have h2 : (0 : ℝ) < inertDeg (P.curve x).F v := by exact_mod_cast inertDeg_pos' v
        have h3 : 0 < Real.log (residueChar v) :=
          Real.log_pos (by exact_mod_cast (residueChar_prime v).one_lt)
        positivity
      rw [Real.posLog_apply, lt_max_iff] at this
      rcases this with h | h
      · exact absurd h (lt_irrefl 0)
      · exact (Real.log_pos_iff (apply_nonneg _ _)).mp h
    have hj0 : 0 < v (P.curve x).E.j := lt_trans zero_lt_one hj1
    have hlog := Real.log_le_log (by positivity) hb
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_one] at hlog
    have hℓ1 : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
      rw [Nat.cast_sub hℓ.one_lt.le, Nat.cast_one]
    rw [hℓ1] at hlog
    push_cast at hlog
    have : Real.log (v ρ) ≤ -(((ℓ : ℝ) - 1) / 4 * Real.log (v (P.curve x).E.j)) := by
      nlinarith
    linarith
  · rw [if_neg htate]
    have hc := finite_crude hρ hH hℓ2 v
    have h4ℓ : v (((4 * ℓ : ℕ) : (P.curve x).F)) =
        v (4 : (P.curve x).F) * v (ℓ : (P.curve x).F) := by
      push_cast; rw [map_mul]
    rw [h4ℓ] at hc
    have hlog := Real.log_le_log (by positivity) hc
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_mul (by positivity) (by positivity), hls₁, hls₂] at hlog
    have hmax : Real.log (max 1 (v (genC' P x))) ≤ |Real.log (v (genC' P x))| := by
      rcases le_total (v (genC' P x)) 1 with h | h
      · rw [max_eq_left h, Real.log_one]; exact abs_nonneg _
      · rw [max_eq_right h]; exact le_abs_self _
    push_cast at hlog
    by_cases h2 : residueChar v = 2
    · rw [if_pos h2]
      have ha := neg_abs_le (Real.log (v (genC' P x)))
      have hb := neg_abs_le (Real.log (v (genC' P x - 1)))
      linarith
    · rw [if_neg h2]
      have hbad : v ∉ (P.curve x).badAll := fun hv => htate ⟨hv, h2⟩
      obtain ⟨hl₁, hl₂⟩ := apply_genC_eq_one P x hbad h2
      have hv2 : v (2 : (P.curve x).F) = 1 :=
        apply_eq_one_of_valuation_eq_one v (valuation_two_eq_one v h2)
      have hv4' : v (4 : (P.curve x).F) = 1 := by
        rw [show (4 : (P.curve x).F) = 2 * 2 by norm_num, map_mul, hv2, one_mul]
      rw [hl₁, hl₂, hv4', Real.log_one] at hlog
      rw [hl₁, max_self, Real.log_one] at hmax
      rw [max_self, Real.log_one] at hlog
      linarith

end Local

/-! ### Sums over the finite places -/

section Sums

variable {T : Type*} [Field T] [NumberField T]

/-- `∑_{v ∈ S} log|y|_v = −log|N(y)|` for `S` containing the places where `|y|_v ≠ 1`. -/
lemma sum_log_apply_eq {y : T} (hy : y ≠ 0) {S : Finset (FinitePlace T)}
    (hS : ∀ v : FinitePlace T, v y ≠ 1 → v ∈ S) :
    ∑ v ∈ S, Real.log (v y) = -Real.log |(Algebra.norm ℚ y : ℝ)| := by
  have hprod : ∏ v ∈ S, v y = |(Algebra.norm ℚ y : ℝ)|⁻¹ := by
    have h := FinitePlace.prod_eq_inv_abs_norm hy
    rw [finprod_eq_prod_of_mulSupport_subset _ fun v hv => hS v hv] at h
    rw [h]
    push_cast
    rfl
  rw [← Real.log_prod (fun v _ => (FinitePlace.pos_iff.mpr hy).ne'), hprod, Real.log_inv]

/-- `∑_{v ∈ S} log|n|_v = −[T : ℚ] log n` for a positive integer `n`. -/
lemma sum_log_apply_natCast {n : ℕ} (hn : n ≠ 0) {S : Finset (FinitePlace T)}
    (hS : ∀ v : FinitePlace T, v (n : T) ≠ 1 → v ∈ S) :
    ∑ v ∈ S, Real.log (v (n : T)) = -(Module.finrank ℚ T * Real.log n) := by
  rw [sum_log_apply_eq (by exact_mod_cast hn) hS]
  have : (n : T) = algebraMap ℚ T (n : ℚ) := by simp
  rw [this, Algebra.norm_algebraMap]
  push_cast
  rw [abs_pow, Nat.abs_cast, Real.log_pow]

end Sums

/-! ### The global estimate -/

/-- `[F : ℚ] (log q_∀ − log q₂) = ∑_{v bad, p_v ≠ 2} log|j|_v`. -/
lemma finrank_mul_h_sub (x : Pt) :
    (Module.finrank ℚ (P.curve x).F : ℝ) * (P.h x - (P.localData x).heightEq 2) =
      ∑ v ∈ (P.localData x).bad.filter (fun v => ¬ (P.localData x).p v = 2),
        Real.log ((show FinitePlace (P.curve x).F from v) (P.curve x).E.j) := by
  have hsplit := (P.localData x).height_eq_heightOn_add (fun v => (P.localData x).p v = 2)
  rw [← (P.localData x).heightEq_eq_heightOn] at hsplit
  have hh : P.h x - (P.localData x).heightEq 2 =
      (P.localData x).heightOn (fun v => ¬ (P.localData x).p v = 2) := by
    change (P.localData x).height - _ = _
    rw [hsplit]; ring
  rw [hh]
  unfold LocalHeightData.heightOn
  have hdeg : ((P.localData x).deg : ℝ) = Module.finrank ℚ (P.curve x).F := rfl
  rw [hdeg, mul_div_cancel₀ _ (by exact_mod_cast Module.finrank_pos.ne')]
  refine Finset.sum_congr (by ext v; simp) fun (v : FinitePlace (P.curve x).F) hv => ?_
  rw [Finset.mem_filter] at hv
  have hvb : v ∈ (P.curve x).badAll := (mem_localData_bad_iff P x v).mp hv.1
  have hpos := posLog_j_eq_of_mem_badAll P x hvb
  change ((if h : v ∈ (P.curve x).badAll then (P.tate x).qOrder v h else 0 : ℕ) : ℝ) *
    inertDeg (P.curve x).F v * Real.log (residueChar v) = _
  rw [dif_pos hvb, ← hpos, Real.posLog_apply]
  refine max_eq_right ?_
  have h1 : (0 : ℝ) < (P.tate x).qOrder v hvb := by exact_mod_cast (P.tate x).qOrder_pos v hvb
  have h2 : (0 : ℝ) < inertDeg (P.curve x).F v := by exact_mod_cast inertDeg_pos' v
  have h3 : 0 < Real.log (residueChar v) :=
    Real.log_pos (by exact_mod_cast (residueChar_prime v).one_lt)
  have := posLog_j_eq_of_mem_badAll P x hvb
  rw [Real.posLog_apply] at this
  have h4 : 0 < max 0 (Real.log (v (P.curve x).E.j)) := by rw [this]; positivity
  rcases lt_max_iff.mp h4 with h | h
  · exact absurd h (lt_irrefl 0)
  · exact h.le

/-- **The isogeny estimate**: `((ℓ − 1)/4)(log q_∀ − log q₂) ≤ 10 log ℓ + 2 log(32 C₀) + 6c + 4 log 4`,
for a point of a compactly bounded subset with bound `c` and `C₀ ≥ 1` a bound for the torsion
`x`-coordinates of the Legendre curves over `ℂ` with parameters bounded by `c`. -/
theorem main_bound {K : CompactlyBounded} (hx : x ∈ K.set) (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2)
    (hgal : ∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
      galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H)
    (hgraph : IsGraphLineOdd P x hℓ hℓ2 H) {C₀ : ℝ} (hC₀1 : 1 ≤ C₀)
    (hC₀ : ∀ (l : ℂ), |Real.log ‖l‖| ≤ K.c → |Real.log ‖l - 1‖| ≤ K.c →
      ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic], W = legendre l →
      ∀ {N : ℕ}, 1 ≤ N → ∀ {a b : ℂ} (h : W.toAffine.Nonsingular a b),
        N • (Affine.Point.some a b h : W.toAffine.Point) = 0 → ‖a‖ ≤ C₀ * N ^ 2) :
    ((ℓ : ℝ) - 1) / 4 * (P.h x - (P.localData x).heightEq 2) ≤
      10 * Real.log ℓ + (2 * Real.log (32 * C₀) + 6 * K.c + 4 * Real.log 4) := by
  obtain ⟨ρ, hρ⟩ := exists_algebraMap_eq_ratio (hℓ := hℓ) (H := H) hgal
  have hodd := odd_card_HL hH hℓ2
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, map_zero] at hρ
    exact mul_ne_zero
      (veluRatio_ne_zero hodd (T₁_ne_zero P x hℓ) (T₁_add_self P x hℓ) (R₁_add_self P x hℓ))
      (veluRatio_ne_zero hodd (T₂_ne_zero P x hℓ) (T₂_add_self P x hℓ) (R₂_add_self P x hℓ))
      hρ.symm
  have hc := CompactlyBounded.c_nonneg hx
  set d : ℝ := (Module.finrank ℚ (P.curve x).F : ℝ) with hd
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.one_lt.le
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  -- the finite set of places
  have h4 : (4 : (P.curve x).F) ≠ 0 := by norm_num
  have hℓ0 : (ℓ : (P.curve x).F) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  set S : Finset (FinitePlace (P.curve x).F) := (FinitePlace.hasFiniteMulSupport hρ0).toFinset ∪
    (P.arith x).badAll_finite.toFinset ∪ (FinitePlace.hasFiniteMulSupport h4).toFinset ∪
    (FinitePlace.hasFiniteMulSupport hℓ0).toFinset with hS
  have hSρ : ∀ v : FinitePlace (P.curve x).F, v ρ ≠ 1 → v ∈ S := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      ((Set.Finite.mem_toFinset _).mpr hv)))
  have hS4 : ∀ v : FinitePlace (P.curve x).F, v ((4 : ℕ) : (P.curve x).F) ≠ 1 → v ∈ S :=
    fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _
      ((Set.Finite.mem_toFinset _).mpr (by push_cast at hv; exact hv)))
  have hSℓ : ∀ v : FinitePlace (P.curve x).F, v (ℓ : (P.curve x).F) ≠ 1 → v ∈ S := fun v hv =>
    Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr hv)
  have hSbad : ∀ v ∈ (P.arith x).badAll_finite.toFinset, v ∈ S := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
  -- the product formula
  have hpf := NumberField.prod_abs_eq_one hρ0
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => hSρ v hv] at hpf
  have hlogpf : ∑ w : InfinitePlace (P.curve x).F, (w.mult : ℝ) * Real.log (w ρ) +
      ∑ v ∈ S, Real.log (v ρ) = 0 := by
    have hw : ∀ w : InfinitePlace (P.curve x).F, 0 < w ρ := fun w => w.pos_iff.mpr hρ0
    have hv : ∀ v : FinitePlace (P.curve x).F, 0 < v ρ := fun v => FinitePlace.pos_iff.mpr hρ0
    have := congrArg Real.log hpf
    rw [Real.log_one, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun w _ => (pow_pos (hw w) _).ne')
      (Finset.prod_ne_zero_iff.mpr fun v _ => (hv v).ne'),
      Real.log_prod (fun w _ => (pow_pos (hw w) _).ne'), Real.log_prod (fun v _ => (hv v).ne')]
      at this
    simp only [Real.log_pow] at this
    exact this
  -- the archimedean bound
  have harch : ∀ w : InfinitePlace (P.curve x).F, Real.log (w ρ) ≤
      2 * Real.log (32 * C₀) + 6 * Real.log ℓ + K.c := by
    intro w
    obtain ⟨hw₁, hw₂⟩ := abs_log_infinite_le P x hx w
    have hb := infinite_bound hρ hH hℓ2 hC₀ w hw₁ hw₂
    have hwρ : 0 < w ρ := w.pos_iff.mpr hρ0
    have hwl : 0 < w (genC' P x) := w.pos_iff.mpr (genC'_ne_zero P x)
    have hwl1 : 0 < w (genC' P x - 1) := w.pos_iff.mpr (sub_ne_zero.mpr (genC'_ne_one P x))
    have hs₁ : w (sqrtLam P x) ^ 2 = w (genC' P x) := by rw [← map_pow, sqrtLam_sq]
    have hs₂ : w (sqrtOneSub P x) ^ 2 = w (genC' P x - 1) := by
      rw [← map_pow, sqrtOneSub_sq, ← neg_sub, ← InfinitePlace.norm_embedding_eq, map_neg,
        norm_neg, InfinitePlace.norm_embedding_eq]
    have hws₁ : 0 < w (sqrtLam P x) := by
      by_contra h
      have h0 : w (sqrtLam P x) = 0 := le_antisymm (not_lt.mp h) (apply_nonneg _ _)
      rw [h0, zero_pow two_ne_zero] at hs₁; linarith
    have hws₂ : 0 < w (sqrtOneSub P x) := by
      by_contra h
      have h0 : w (sqrtOneSub P x) = 0 := le_antisymm (not_lt.mp h) (apply_nonneg _ _)
      rw [h0, zero_pow two_ne_zero] at hs₂; linarith
    have hB : 0 < 2 * (ℓ : ℝ) * (C₀ * (4 * ℓ) ^ 2) := by positivity
    have hlog := Real.log_le_log (by positivity) hb
    rw [Real.log_mul hwρ.ne' (by positivity), Real.log_mul hws₁.ne' hws₂.ne', Real.log_pow] at hlog
    have e₁ : Real.log (w (sqrtLam P x)) = Real.log (w (genC' P x)) / 2 := by
      rw [← hs₁, Real.log_pow]; push_cast; ring
    have e₂ : Real.log (w (sqrtOneSub P x)) = Real.log (w (genC' P x - 1)) / 2 := by
      rw [← hs₂, Real.log_pow]; push_cast; ring
    have hBeq : Real.log (2 * (ℓ : ℝ) * (C₀ * (4 * ℓ) ^ 2)) = Real.log (32 * C₀) + 3 * Real.log ℓ := by
      rw [show 2 * (ℓ : ℝ) * (C₀ * (4 * ℓ) ^ 2) = (32 * C₀) * ℓ ^ 3 by ring,
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast; ring
    rw [e₁, e₂, hBeq] at hlog
    have := neg_abs_le (Real.log (w (genC' P x)))
    have := neg_abs_le (Real.log (w (genC' P x - 1)))
    push_cast at hlog
    linarith
  have hsum_arch : ∑ w : InfinitePlace (P.curve x).F, (w.mult : ℝ) * Real.log (w ρ) ≤
      d * (2 * Real.log (32 * C₀) + 6 * Real.log ℓ + K.c) := by
    calc ∑ w : InfinitePlace (P.curve x).F, (w.mult : ℝ) * Real.log (w ρ)
        ≤ ∑ w : InfinitePlace (P.curve x).F, (w.mult : ℝ) * (2 * Real.log (32 * C₀) + 6 * Real.log ℓ + K.c) :=
          Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (harch w) (Nat.cast_nonneg _)
      _ = d * (2 * Real.log (32 * C₀) + 6 * Real.log ℓ + K.c) := by
          rw [← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
  -- the finite bound
  have hfin := Finset.sum_le_sum fun v (_ : v ∈ S) =>
    log_apply_le hρ hH hℓ2 hgraph hρ0 v
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hfin
  -- the gain: the odd multiplicative places
  have hT : ∑ v ∈ S, (if v ∈ (P.curve x).badAll ∧ residueChar v ≠ 2 then
      -(((ℓ : ℝ) - 1) / 4 * Real.log (v (P.curve x).E.j)) else 0) =
      -(((ℓ : ℝ) - 1) / 4 * (d * (P.h x - (P.localData x).heightEq 2))) := by
    rw [← Finset.sum_filter, Finset.sum_neg_distrib, ← Finset.mul_sum, hd, finrank_mul_h_sub]
    congr 2
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext v
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, hv, h2⟩
      exact Finset.mem_filter.mpr ⟨(P.arith x).badAll_finite.mem_toFinset.mpr hv, h2⟩
    · intro h
      obtain ⟨hv, h2⟩ := Finset.mem_filter.mp h
      have hv' : v ∈ (P.curve x).badAll := (P.arith x).badAll_finite.mem_toFinset.mp hv
      exact ⟨hSbad v hv, hv', h2⟩
  -- the places over `2`
  have hlog4 : ∑ v ∈ S, -Real.log (v (4 : (P.curve x).F)) = d * Real.log 4 := by
    have := sum_log_apply_natCast (n := 4) (by norm_num) hS4
    push_cast at this
    rw [Finset.sum_neg_distrib, this, neg_neg, hd]
  have hB2 : ∑ v ∈ S, (if residueChar v = 2 then
      9 / 2 * |Real.log (v (genC' P x))| + 1 / 2 * |Real.log (v (genC' P x - 1))| +
        4 * -Real.log (v (4 : (P.curve x).F)) else 0) ≤
      5 * K.c * d + 4 * (d * Real.log 4) := by
    rw [← Finset.sum_filter]
    have hle : ∀ v ∈ S.filter (fun v => residueChar v = 2),
        9 / 2 * |Real.log (v (genC' P x))| + 1 / 2 * |Real.log (v (genC' P x - 1))| +
          4 * -Real.log (v (4 : (P.curve x).F)) ≤
        5 * K.c * localDeg (P.curve x).F v + 4 * -Real.log (v (4 : (P.curve x).F)) := by
      intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨h₁, h₂⟩ := abs_log_two_le P x hx v hv.2
      linarith
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hdeg : ∑ v ∈ S.filter (fun v => residueChar v = 2), (localDeg (P.curve x).F v : ℝ) ≤ d := by
      rw [hd]; exact_mod_cast sum_localDeg_filter_le S 2
    have hnn : ∀ v ∈ S, 0 ≤ -Real.log (v (4 : (P.curve x).F)) := fun v _ =>
      neg_nonneg.mpr (Real.log_nonpos (apply_nonneg _ _) (by exact_mod_cast apply_natCast_le_one v 4))
    have h4le : ∑ v ∈ S.filter (fun v => residueChar v = 2), -Real.log (v (4 : (P.curve x).F)) ≤
        d * Real.log 4 := by
      rw [← hlog4]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun v hv _ => hnn v hv
    nlinarith
  -- the places over `ℓ`
  have hlogℓ' : ∑ v ∈ S, -Real.log (v (ℓ : (P.curve x).F)) = d * Real.log ℓ := by
    rw [Finset.sum_neg_distrib, sum_log_apply_natCast hℓ.ne_zero hSℓ, neg_neg, hd]
  rw [hT, hlogℓ'] at hfin
  -- combination
  set X := P.h x - (P.localData x).heightEq 2
  have hkey : d * (((ℓ : ℝ) - 1) / 4 * X) ≤ d * (10 * Real.log ℓ +
      (2 * Real.log (32 * C₀) + 6 * K.c + 4 * Real.log 4)) := by
    have e : ((ℓ : ℝ) - 1) / 4 * (d * X) = d * (((ℓ : ℝ) - 1) / 4 * X) := by ring
    rw [e] at hfin
    nlinarith
  exact le_of_mul_le_mul_left hkey hd0

end Cyclic

end

end Iut.Tripod
