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

end Cyclic

end

end Iut.Tripod
