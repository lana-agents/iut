/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.Theater.AutScalar
import Iut.Multiradial.Theater.CuspConj

/-!
# The dihedral action of `π₁(C_K)` on the rank-one quotient `Q ≅ F_ℓ` (MR22 T6, `K`-linear part)

IUT I, Example 4.3 (i) (l.6545–6600 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller
Theory I.txt`) and Definition 6.1 (v) (l.10845–10900): the covering `X̲_K → C_K` is Galois with
group `F_ℓ ⋊ {±1}` acting on the rank-one quotient `Q = E(K)[ℓ]/M ≅ F_ℓ` (the cusps of `X̲_K`),
`C̲_K` is the stabiliser of the cusp `0`, and `X̲_K` the kernel. In the Galois model
`π₁(X) = Aut(Ω / F_X) ⧸ ⟨⟨inertia⟩⟩` (`Genuine.pi1Of`) of the model orbicurves this is explicit:
every `σ ∈ Gal(Ω / k(x))` has `σ(Q_ℓ) = ε Q_ℓ + S` with unique `ε = ±1`, `S ∈ E(k)[ℓ]`
(`act_Qpt_unique`; the generic point is not `2`-torsion, `genericPoint_ne_neg`), and
`σ ↦ (z ↦ ε (z − [S]))` is a homomorphism `rhoGal` to `F_ℓ ⋊ {±1} ⊆ Sym(F_ℓ)` (after an additive
identification `Q ≅ F_ℓ`). By `isCuspPlace_smul` this is the action of `σ` on the cuspidal places
(`isCuspPlace_rhoGal`: `σ` maps a place over the cusp `T` to a place over `ρ(σ)(T)`).

* `rhoGal`: kills `Aut(Ω / F_{X̲})` (`rhoGal_eq_one_iff`), with stabiliser of `0` equal to
  `Aut(Ω / F_{C̲})` (`rhoGal_zero_iff`), containing the translation `z ↦ z + 1`
  (`exists_rhoGal_translation`, from the transitivity of `Gal(Ω / k(x))` on cuspidal places);
* `rhoC`: the induced homomorphism on `π₁(C) = pi1C E 1 0 ±` (the inertia over `E ∖ {0}` fixes
  the division points, `inertia_fixes_division`);
* `isDihedralQuot_rhoC`: with `R` the image of `π₁(C̲)`, `rhoC` is a dihedral quotient in the sense
  of `AutScalar.lean`; `range_pi1MapC_false`: the image of `π₁(X̲)` is the kernel.
-/

noncomputable section

namespace Iut.Multiradial.Theater

open WeierstrassCurve Iut.Anabelian Iut.Anabelian.Genuine Iut.HodgeTheater

universe u

attribute [local instance low] Classical.propDecidable

section Generic

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- **The generic point is not `2`-torsion**: otherwise `2y + a₁x + a₃ = 0` and the Weierstrass
equation makes `x` a root of `4X³ + b₂X² + 2b₄X + b₆`. -/
theorem genericPoint_ne_neg : genericPoint E ≠ -genericPoint E := by
  intro h
  rw [Genuine.genericPoint, Affine.Point.neg_some] at h
  have hy : yG E = (E⁄(Ω E)).toAffine.negY (xG E) (yG E) := (Affine.Point.some.inj h).2
  have heq := (Affine.equation_iff _ _).1 (nonsingular_generic E).1
  have e1 : (E⁄(Ω E)).toAffine.a₁ = algebraMap k (Ω E) E.a₁ := rfl
  have e2 : (E⁄(Ω E)).toAffine.a₂ = algebraMap k (Ω E) E.a₂ := rfl
  have e3 : (E⁄(Ω E)).toAffine.a₃ = algebraMap k (Ω E) E.a₃ := rfl
  have e4 : (E⁄(Ω E)).toAffine.a₄ = algebraMap k (Ω E) E.a₄ := rfl
  have e6 : (E⁄(Ω E)).toAffine.a₆ = algebraMap k (Ω E) E.a₆ := rfl
  rw [Affine.negY, e1, e3] at hy
  rw [e1, e2, e3, e4, e6] at heq
  set x := xG E
  set y := yG E
  have hy' : 2 * y + algebraMap k (Ω E) E.a₁ * x + algebraMap k (Ω E) E.a₃ = 0 := by
    linear_combination hy
  apply transcendental_xG E
  refine ⟨Polynomial.C 4 * Polynomial.X ^ 3 + Polynomial.C (4 * E.a₂ + E.a₁ ^ 2) *
    Polynomial.X ^ 2 + Polynomial.C (4 * E.a₄ + 2 * E.a₁ * E.a₃) * Polynomial.X +
    Polynomial.C (4 * E.a₆ + E.a₃ ^ 2), fun h0 => ?_, ?_⟩
  · have := Polynomial.natDegree_cubic (R := k) (a := 4) (b := 4 * E.a₂ + E.a₁ ^ 2)
      (c := 4 * E.a₄ + 2 * E.a₁ * E.a₃) (d := 4 * E.a₆ + E.a₃ ^ 2) (by norm_num)
    rw [h0, Polynomial.natDegree_zero] at this
    exact absurd this (by norm_num)
  · simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow,
      map_ofNat]
    linear_combination (-4) * heq +
      (2 * y + algebraMap k (Ω E) E.a₁ * x + algebraMap k (Ω E) E.a₃) * hy'

/-- **Uniqueness of the sign and the translation**: `ε Q_ℓ + S = ε' Q_ℓ + S'` with `ε, ε' = ±1`
and `ℓ`-torsion `S, S' ∈ E(k)` forces `ε = ε'`, `S = S'`. -/
theorem act_Qpt_unique {ℓ : ℕ} (hℓ : ℓ ≠ 0) {ε ε' : ℤˣ} {S S' : E.toAffine.Point}
    (hS : ℓ • S = 0) (hS' : ℓ • S' = 0)
    (h : (ε : ℤ) • Qpt E ℓ + base E S = (ε' : ℤ) • Qpt E ℓ + base E S') : ε = ε' ∧ S = S' := by
  have key : ε = ε' := by
    by_contra hne
    have hG : 2 • genericPoint E = 0 := by
      have h2 : (2 : ℤ) • Qpt E ℓ = (ε : ℤ) • (base E S' - base E S) := by
        rcases Int.units_eq_one_or ε with rfl | rfl <;>
          rcases Int.units_eq_one_or ε' with rfl | rfl
        · exact absurd rfl hne
        · simp only [Units.val_one, one_zsmul, Units.val_neg, neg_zsmul] at h ⊢
          calc (2 : ℤ) • Qpt E ℓ = (Qpt E ℓ + base E S) + Qpt E ℓ - base E S := by
                rw [two_zsmul]; abel
            _ = (-Qpt E ℓ + base E S') + Qpt E ℓ - base E S := by rw [h]
            _ = base E S' - base E S := by abel
        · simp only [Units.val_one, one_zsmul, Units.val_neg, neg_zsmul] at h ⊢
          calc (2 : ℤ) • Qpt E ℓ = (Qpt E ℓ + base E S') + Qpt E ℓ - base E S' := by
                rw [two_zsmul]; abel
            _ = (-Qpt E ℓ + base E S) + Qpt E ℓ - base E S' := by rw [h]
            _ = -(base E S' - base E S) := by abel
        · exact absurd rfl hne
      have h3 : ℓ • ((2 : ℤ) • Qpt E ℓ) = 0 := by
        rw [h2, smul_comm, nsmul_sub, ← map_nsmul, ← map_nsmul, hS, hS', sub_self, smul_zero]
      rw [smul_comm, GenuineBaseChange.nsmul_Qpt E hℓ] at h3
      rw [two_nsmul]
      rw [two_zsmul] at h3
      exact h3
    apply genericPoint_ne_neg E
    rw [two_nsmul] at hG
    exact eq_neg_of_add_eq_zero_left hG
  subst key
  have h2 : base E S = base E S' := by
    have := congrArg (fun P => -((ε : ℤ) • Qpt E ℓ) + P) h
    simpa only [neg_add_cancel_left] using this
  exact ⟨rfl, pointMap_injective E _ h2⟩

end Generic

/-! ### The rank-one quotient `Q = E(k)[ℓ]/M ≅ F_ℓ` -/

section Quot

variable {k : Type u} [Field k] {E : WeierstrassCurve k} {ℓ : ℕ}

variable (E ℓ) in
/-- `E(k)[ℓ]`. -/
abbrev Tor : AddSubgroup E.toAffine.Point := AddSubgroup.torsionBy E.toAffine.Point (ℓ : ℤ)

lemma mem_tor {S : E.toAffine.Point} : S ∈ Tor E ℓ ↔ ℓ • S = 0 :=
  AddSubgroup.torsionBy.nsmul_iff

variable (M : AddSubgroup E.toAffine.Point)
  (e : Tor E ℓ ⧸ M.addSubgroupOf (Tor E ℓ) ≃+ ZMod ℓ)

/-- The class of `S ∈ E(k)[ℓ]` in `Q = E(k)[ℓ]/M ≅ F_ℓ`. -/
def qOf (S : Tor E ℓ) : ZMod ℓ := e (QuotientAddGroup.mk S)

lemma qOf_add (S T : Tor E ℓ) : qOf M e (S + T) = qOf M e S + qOf M e T := by
  simp [qOf]

lemma qOf_zsmul (n : ℤ) (S : Tor E ℓ) : qOf M e (n • S) = (n : ZMod ℓ) * qOf M e S := by
  simp [qOf, zsmul_eq_mul]

lemma qOf_zero : qOf M e 0 = 0 := by simp [qOf]

lemma qOf_eq_zero_iff (S : Tor E ℓ) : qOf M e S = 0 ↔ (S : E.toAffine.Point) ∈ M := by
  rw [qOf, AddEquiv.map_eq_zero_iff, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

end Quot

/-! ### The homomorphism `Gal(Ω / k(x)) → F_ℓ ⋊ {±1}` -/

section Rho

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]
  {ℓ : ℕ} [OddPrime ℓ]

lemma ell_ne_zero : ℓ ≠ 0 := (OddPrime.prime (ℓ := ℓ)).ne_zero

lemma effLevel_eq : effLevel ℓ = ℓ := if_neg ell_ne_zero

variable (hcard : Nat.card (Tor E ℓ) = ℓ ^ 2)

include hcard in
lemma exists_sgnTr (σ : Gal E) : ∃ p : ℤˣ × Tor E ℓ,
    act E σ (Qpt E ℓ) = (p.1 : ℤ) • Qpt E ℓ + base E p.2 := by
  obtain ⟨ε, hε, S, hS, h⟩ := act_Qpt_eq E ell_ne_zero hcard σ
  exact ⟨((Int.isUnit_iff.mpr hε).unit, ⟨S, mem_tor.2 hS⟩), by rw [IsUnit.unit_spec]; exact h⟩

/-- **The sign and the translation of `σ`**: `σ(Q_ℓ) = ε Q_ℓ + S`. -/
def sgnTr (σ : Gal E) : ℤˣ × Tor E ℓ := (exists_sgnTr hcard σ).choose

lemma sgnTr_spec (σ : Gal E) :
    act E σ (Qpt E ℓ) = ((sgnTr hcard σ).1 : ℤ) • Qpt E ℓ + base E (sgnTr hcard σ).2 :=
  (exists_sgnTr hcard σ).choose_spec

lemma sgnTr_eq {σ : Gal E} {p : ℤˣ × Tor E ℓ}
    (h : act E σ (Qpt E ℓ) = (p.1 : ℤ) • Qpt E ℓ + base E p.2) : sgnTr hcard σ = p := by
  obtain ⟨h1, h2⟩ := act_Qpt_unique E ell_ne_zero (mem_tor.1 (sgnTr hcard σ).2.2) (mem_tor.1 p.2.2)
    ((sgnTr_spec hcard σ).symm.trans h)
  exact Prod.ext h1 (Subtype.ext h2)

lemma sgnTr_one : sgnTr hcard (1 : Gal E) = (1, 0) :=
  sgnTr_eq hcard (by rw [act_one]; simp)

lemma sgnTr_mul (σ τ : Gal E) : sgnTr hcard (σ * τ) = ((sgnTr hcard σ).1 * (sgnTr hcard τ).1,
    ((sgnTr hcard τ).1 : ℤ) • (sgnTr hcard σ).2 + (sgnTr hcard τ).2) := by
  apply sgnTr_eq
  rw [act_mul, sgnTr_spec hcard τ, map_add, map_zsmul, sgnTr_spec hcard σ, act_base]
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_zsmul, map_add, map_zsmul, Units.val_mul]
  module

variable (M : AddSubgroup E.toAffine.Point)
  (e : Tor E ℓ ⧸ M.addSubgroupOf (Tor E ℓ) ≃+ ZMod ℓ)

/-- **The action of `Gal(Ω / k(x))` on `Q ≅ F_ℓ`**: `σ ↦ (z ↦ ε (z − [S]))` for
`σ(Q_ℓ) = ε Q_ℓ + S`. -/
def rhoGal : Gal E →* Equiv.Perm (ZMod ℓ) where
  toFun σ := affPerm ℓ (sgnTr hcard σ).1 (-(sgn ℓ (sgnTr hcard σ).1 * qOf M e (sgnTr hcard σ).2))
  map_one' := by
    rw [sgnTr_one, qOf_zero, mul_zero, neg_zero]
    exact affPerm_one
  map_mul' σ τ := by
    rw [sgnTr_mul, affPerm_mul]
    congr 1
    rw [qOf_add, qOf_zsmul, sgn_mul]
    have h := sgn_mul_self (ℓ := ℓ) (sgnTr hcard τ).1
    simp only [sgn] at h ⊢
    linear_combination (-((((sgnTr hcard σ).1 : ℤ) : ZMod ℓ)) * qOf M e (sgnTr hcard σ).2) * h

lemma rhoGal_apply (σ : Gal E) (z : ZMod ℓ) : rhoGal hcard M e σ z =
    sgn ℓ (sgnTr hcard σ).1 * z - sgn ℓ (sgnTr hcard σ).1 * qOf M e (sgnTr hcard σ).2 := by
  change affPerm ℓ _ _ z = _
  rw [affPerm_apply]
  ring

lemma rhoGal_mem (σ : Gal E) : rhoGal hcard M e σ ∈ FlSemi ℓ := ⟨_, _, rfl⟩

lemma sgn_ne_zero (u : ℤˣ) : sgn ℓ u ≠ 0 := fun h => by
  have := sgn_mul_self (ℓ := ℓ) u
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- `ρ(σ)` fixes `0` iff the translation of `σ` lies in `M`. -/
lemma rhoGal_zero_iff' (σ : Gal E) :
    rhoGal hcard M e σ 0 = 0 ↔ ((sgnTr hcard σ).2 : E.toAffine.Point) ∈ M := by
  rw [rhoGal_apply, mul_zero, zero_sub, neg_eq_zero, mul_eq_zero, ← qOf_eq_zero_iff M e]
  exact ⟨fun h => h.resolve_left (sgn_ne_zero _), Or.inr⟩

omit [CharZero k] [E.IsElliptic] in
lemma mem_Mbar_iff {T : Pt E} : T ∈ Mbar E ℓ M ↔
    ∃ T₀ : E.toAffine.Point, T₀ ∈ M ∧ T₀ ∈ Tor E ℓ ∧ base E T₀ = T := by
  rw [Mbar, AddSubgroup.mem_map]
  simp only [AddSubgroup.mem_inf, effLevel_eq]
  exact ⟨fun ⟨T₀, ⟨h1, h2⟩, h3⟩ => ⟨T₀, h1, h2, h3⟩, fun ⟨T₀, h1, h2, h3⟩ => ⟨T₀, ⟨h1, h2⟩, h3⟩⟩

/-- An element of `Aut(Ω / F_X)` for `X = (E, ℓ, M, ±)` has sign `±1` (`+1` without `±`) and
translation in `M`. -/
lemma sgnTr_of_mem_Hgp {pm : Bool} {σ : Gal E} (hσ : σ ∈ Hgp E ℓ M pm) :
    ((sgnTr hcard σ).1 = 1 ∨ pm = true) ∧ ((sgnTr hcard σ).2 : E.toAffine.Point) ∈ M := by
  obtain ⟨ε, hε, hT⟩ := hσ
  obtain ⟨T₀, hM, ht, hT₀⟩ := (mem_Mbar_iff M).1 hT
  have hεu : ε = 1 ∨ ε = -1 := by rcases hε with h | ⟨-, h⟩ <;> simp [h]
  have h := sgnTr_eq hcard (σ := σ) (p := ((Int.isUnit_iff.mpr hεu).unit, ⟨T₀, ht⟩)) (by
    rw [IsUnit.unit_spec]
    change _ = ε • Qpt E ℓ + base E T₀
    rw [hT₀]
    abel)
  rw [h]
  refine ⟨?_, hM⟩
  rcases hε with h1 | ⟨h1, -⟩
  · left
    exact Units.ext (by rw [IsUnit.unit_spec, h1, Units.val_one])
  · exact Or.inr h1

lemma mem_Hgp_of_sgnTr {pm : Bool} {σ : Gal E} (h1 : (sgnTr hcard σ).1 = 1 ∨ pm = true)
    (h2 : ((sgnTr hcard σ).2 : E.toAffine.Point) ∈ M) : σ ∈ Hgp E ℓ M pm := by
  refine ⟨(sgnTr hcard σ).1, ?_, (mem_Mbar_iff M).2 ⟨_, h2, (sgnTr hcard σ).2.2, ?_⟩⟩
  · rcases h1 with h | h
    · left; rw [h, Units.val_one]
    · rcases Int.units_eq_one_or (sgnTr hcard σ).1 with h' | h'
      · left; rw [h', Units.val_one]
      · right; exact ⟨h, by rw [h', Units.val_neg, Units.val_one]⟩
  · rw [sgnTr_spec hcard σ]
    abel

/-- **The stabiliser of `0` is `Aut(Ω / F_{C̲})`** (`C̲ = (E, ℓ, M, ±)`). -/
theorem rhoGal_zero_iff (σ : Gal E) : rhoGal hcard M e σ 0 = 0 ↔ σ ∈ Hgp E ℓ M true := by
  rw [rhoGal_zero_iff']
  exact ⟨fun h => mem_Hgp_of_sgnTr hcard M (Or.inr rfl) h, fun h => (sgnTr_of_mem_Hgp hcard M h).2⟩

/-- **The kernel is `Aut(Ω / F_{X̲})`** (`X̲ = (E, ℓ, M)`). -/
theorem rhoGal_eq_one_iff (σ : Gal E) : rhoGal hcard M e σ = 1 ↔ σ ∈ Hgp E ℓ M false := by
  constructor
  · intro h
    have h0 : rhoGal hcard M e σ 0 = 0 := by rw [h]; rfl
    have h1 : rhoGal hcard M e σ 1 = 1 := by rw [h]; rfl
    have hM := (rhoGal_zero_iff' hcard M e σ).1 h0
    rw [rhoGal_apply, (qOf_eq_zero_iff M e _).2 hM, mul_zero, sub_zero, mul_one] at h1
    have hs : (sgnTr hcard σ).1 = 1 := sgn_injective (by rw [h1, sgn_one])
    exact mem_Hgp_of_sgnTr hcard M (Or.inl hs) hM
  · intro h
    obtain ⟨h1, h2⟩ := sgnTr_of_mem_Hgp hcard M h
    have h1 : (sgnTr hcard σ).1 = 1 := h1.resolve_right (by simp)
    ext z
    rw [rhoGal_apply, (qOf_eq_zero_iff M e _).2 h2, h1, sgn_one]
    simp

/-- **`ρ(σ)` is the action of `σ` on the cusps**: `σ` maps a cuspidal place over `T ∈ E(k)[ℓ]` to
a cuspidal place over a `T'` with class `[T'] = ρ(σ)([T])` in `Q ≅ F_ℓ` (`isCuspPlace_smul`). -/
theorem isCuspPlace_rhoGal (σ : Gal E) {T : Tor E ℓ} {W : ValuationSubring (Ω E)}
    (h : IsCuspPlace E ℓ T W) : ∃ T' : Tor E ℓ,
      qOf M e T' = rhoGal hcard M e σ (qOf M e T) ∧ IsCuspPlace E ℓ T' (placeSmul E σ W) := by
  have hε : (((sgnTr hcard σ).1 : ℤ) = 1 ∨ ((sgnTr hcard σ).1 : ℤ) = -1) :=
    Int.isUnit_iff.mp (sgnTr hcard σ).1.isUnit
  refine ⟨((sgnTr hcard σ).1 : ℤ) • (T - (sgnTr hcard σ).2), ?_,
    isCuspPlace_smul hε (sgnTr_spec hcard σ) h⟩
  rw [qOf_zsmul, rhoGal_apply, show T - (sgnTr hcard σ).2 = T + (-1 : ℤ) • (sgnTr hcard σ).2 by
    rw [neg_one_zsmul, sub_eq_add_neg], qOf_add, qOf_zsmul]
  simp only [sgn, Int.cast_neg, Int.cast_one]
  ring

/-- **`ρ` contains the translation `z ↦ z + 1`** (transitivity of `Gal(Ω / k(x))` on the
cuspidal places, `exists_gal_placeSmul`, and the reflection fixing the place over `0`,
`exists_fix_neg`). -/
theorem exists_rhoGal_translation : ∃ σ : Gal E, rhoGal hcard M e σ = affPerm ℓ 1 1 := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (e.symm 1)
  have hqt : qOf M e t = 1 := by rw [qOf, ht, AddEquiv.apply_symm_apply]
  obtain ⟨W₀, hW₀⟩ := exists_isCuspPlace (E := E) (ell_ne_zero (ℓ := ℓ)) (T := 0) (nsmul_zero _)
  obtain ⟨W₁, hW₁⟩ := exists_isCuspPlace (E := E) (ell_ne_zero (ℓ := ℓ)) (mem_tor.1 t.2)
  obtain ⟨σ, hσ⟩ := exists_gal_placeSmul E ell_ne_zero (nsmul_zero _) (mem_tor.1 t.2) hW₀ hW₁
  have hε : (((sgnTr hcard σ).1 : ℤ) = 1 ∨ ((sgnTr hcard σ).1 : ℤ) = -1) :=
    Int.isUnit_iff.mp (sgnTr hcard σ).1.isUnit
  have h' := isCuspPlace_smul hε (sgnTr_spec hcard σ) hW₀
  rw [← hσ] at h'
  have htu := isCuspPlace_unique hW₁ h'
  have htu' : t = ((sgnTr hcard σ).1 : ℤ) • (0 - (sgnTr hcard σ).2) := Subtype.ext (by
    rw [htu, AddSubgroup.coe_zsmul, AddSubgroup.coe_sub, AddSubgroup.coe_zero])
  have hq : -(sgn ℓ (sgnTr hcard σ).1 * qOf M e (sgnTr hcard σ).2) = 1 := by
    rw [← hqt, htu', qOf_zsmul, zero_sub,
      show -(sgnTr hcard σ).2 = (-1 : ℤ) • (sgnTr hcard σ).2 from (neg_one_zsmul _).symm,
      qOf_zsmul]
    simp only [sgn, Int.cast_neg, Int.cast_one]
    ring
  have hρσ : rhoGal hcard M e σ = affPerm ℓ (sgnTr hcard σ).1 1 := by
    change affPerm ℓ _ _ = _
    rw [hq]
  rcases Int.units_eq_one_or (sgnTr hcard σ).1 with h1 | h1
  · exact ⟨σ, by rw [hρσ, h1]⟩
  · obtain ⟨ρ₀, -, hρ₀⟩ := exists_fix_neg E (ell_ne_zero (ℓ := ℓ)) (nsmul_zero _) hW₀
    have hs : sgnTr hcard ρ₀ = (-1, 0) := sgnTr_eq hcard (by
      rw [map_zero, sub_zero] at hρ₀
      rw [hρ₀]
      simp)
    have hρ : rhoGal hcard M e ρ₀ = affPerm ℓ (-1) 0 := by
      change affPerm ℓ _ _ = _
      rw [hs, qOf_zero, mul_zero, neg_zero]
    refine ⟨σ * ρ₀, ?_⟩
    rw [map_mul, hρσ, hρ, h1, affPerm_mul]
    simp

end Rho

/-! ### Descent to `π₁(C)` -/

section Descent

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]
  {ℓ : ℕ} [OddPrime ℓ] (hcard : Nat.card (Tor E ℓ) = ℓ ^ 2) (M : AddSubgroup E.toAffine.Point)
  (e : Tor E ℓ ⧸ M.addSubgroupOf (Tor E ℓ) ≃+ ZMod ℓ)

variable (E) in
/-- Every `σ ∈ Gal(Ω / k(x))` lies in `Aut(Ω / F_C)`, `C = (E ∖ {0})/{±1}`. -/
lemma mem_Hgp_one_bot (σ : Gal E) : σ ∈ Hgp E 1 ⊥ true := by
  have hQ : Qpt E 1 = genericPoint E := by
    have := effLevel_smul_Qpt E (compatible_divSys_of_charZero E) 1
    rwa [show effLevel 1 = 1 from if_neg one_ne_zero, one_smul] at this
  rcases act_genericPoint E σ with h | h
  · exact ⟨1, Or.inl rfl, by rw [hQ, h, one_zsmul, sub_self]; exact zero_mem _⟩
  · exact ⟨-1, Or.inr ⟨rfl, rfl⟩, by rw [hQ, h, neg_one_zsmul, sub_self]; exact zero_mem _⟩

variable (E) in
omit [OddPrime ℓ] in
/-- The inertia over `E ∖ {0}` (and its conjugates) lies in `Aut(Ω / F_{X̲})`. -/
lemma ambientKernel_le_Hgp :
    GaloisPi1.ambientKernel (Hgp E 1 ⊥ true) (SgenC E 1 ⊥) ≤ Hgp E ℓ M false := by
  refine Subgroup.topologicalClosure_minimal _ ?_ (isClosed_Hgp E ℓ M false)
  rw [Subgroup.closure_le]
  rintro _ ⟨h, hh, s, hs, rfl⟩
  rw [SgenC_of_charZero, Sgen_eq_S0] at hs
  obtain ⟨hT, -⟩ := S0_subset_Sgen E ℓ M (conj_mem_S0 E (compatible_divSys_of_charZero E) hh hs)
  exact ⟨1, Or.inl rfl, by rwa [one_zsmul]⟩

/-- **`ρ` on `π₁(C) = Aut(Ω / F_C) ⧸ ⟨⟨inertia⟩⟩`.** -/
def rhoC : pi1C E 1 ⊥ true →* Equiv.Perm (ZMod ℓ) :=
  QuotientGroup.lift (GaloisPi1.kernel (Hgp E 1 ⊥ true) (SgenC E 1 ⊥))
    ((rhoGal hcard M e).comp (Hgp E 1 ⊥ true).subtype) fun _ hx =>
      (MonoidHom.mem_ker).2 ((rhoGal_eq_one_iff hcard M e _).2
        (ambientKernel_le_Hgp E M (Subgroup.mem_subgroupOf.1 hx)))

lemma rhoC_mk (h : Hgp E 1 ⊥ true) :
    rhoC hcard M e (QuotientGroup.mk h : Hgp E 1 ⊥ true ⧸ GaloisPi1.kernel _ _) =
      rhoGal hcard M e h := rfl

lemma pi1MapC_cond (hMT : M ≤ Tor E ℓ) (pm : Bool) :
    Hgp E ℓ M pm ≤ Hgp E 1 ⊥ true ∧ SgenC E ℓ M ⊆ SgenC E 1 ⊥ :=
  ⟨Hgp_le E (compatible_divSys_of_charZero E) (Nat.pos_of_ne_zero (ell_ne_zero (ℓ := ℓ)))
      (mul_one ℓ) (fun P hP => by rw [AddSubgroup.mem_bot]; exact mem_tor.1 (hMT hP))
      (fun _ => rfl),
    by rw [SgenC_of_charZero, SgenC_of_charZero, Sgen_eq_S0, Sgen_eq_S0]⟩

/-- The image of `π₁((E, ℓ, M, ±)) → π₁(C)`: the classes of `Aut(Ω / F_X)`. -/
lemma mem_range_pi1MapC_iff (hMT : M ≤ Tor E ℓ) (pm : Bool) (y : pi1C E 1 ⊥ true) :
    y ∈ (pi1MapC E (ℓ := ℓ) (ℓ' := 1) (M := M) (M' := ⊥) (pm := pm) (pm' := true)).range ↔
      ∃ h : Hgp E 1 ⊥ true, (h : Gal E) ∈ Hgp E ℓ M pm ∧
        (QuotientGroup.mk h : Hgp E 1 ⊥ true ⧸ GaloisPi1.kernel _ _) = y := by
  unfold pi1MapC
  rw [dif_pos (pi1MapC_cond M hMT pm)]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨Subgroup.inclusion (pi1MapC_cond M hMT pm).1 x, x.2, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨(QuotientGroup.mk ⟨h, hh⟩ : Hgp E ℓ M pm ⧸ GaloisPi1.kernel _ _), rfl⟩

/-- **The image of `π₁(C̲) → π₁(C)` is the stabiliser of `0`.** -/
theorem mem_range_pi1MapC_true_iff (hMT : M ≤ Tor E ℓ) (y : pi1C E 1 ⊥ true) :
    y ∈ (pi1MapC E (ℓ := ℓ) (ℓ' := 1) (M := M) (M' := ⊥) (pm := true) (pm' := true)).range ↔
      rhoC hcard M e y 0 = 0 := by
  rw [mem_range_pi1MapC_iff M hMT]
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  rw [rhoC_mk, rhoGal_zero_iff]
  constructor
  · rintro ⟨h', hh', he⟩
    rw [QuotientGroup.eq] at he
    have hk := ambientKernel_le_Hgp E (ℓ := ℓ) M (Subgroup.mem_subgroupOf.1 he)
    have := (Hgp E ℓ M true).mul_mem hh' (Hgp_le E (compatible_divSys_of_charZero E) one_pos
      (one_mul ℓ) (fun P hP => by rwa [one_smul]) (fun _ => rfl) hk)
    simpa using this
  · exact fun hh => ⟨h, hh, rfl⟩

/-- **The image of `π₁(X̲) → π₁(C)` is the kernel of `ρ`.** -/
theorem mem_range_pi1MapC_false_iff (hMT : M ≤ Tor E ℓ) (y : pi1C E 1 ⊥ true) :
    y ∈ (pi1MapC E (ℓ := ℓ) (ℓ' := 1) (M := M) (M' := ⊥) (pm := false) (pm' := true)).range ↔
      rhoC hcard M e y = 1 := by
  rw [mem_range_pi1MapC_iff M hMT]
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  rw [rhoC_mk, rhoGal_eq_one_iff]
  constructor
  · rintro ⟨h', hh', he⟩
    rw [QuotientGroup.eq] at he
    have hk := ambientKernel_le_Hgp E (ℓ := ℓ) M (Subgroup.mem_subgroupOf.1 he)
    have := (Hgp E ℓ M false).mul_mem hh' hk
    simpa using this
  · exact fun hh => ⟨h, hh, rfl⟩

/-- **`π₁(C) → F_ℓ ⋊ {±1}` with stabiliser of `0` the image of `π₁(C̲)`.** -/
theorem isDihedralQuot_rhoC (hMT : M ≤ Tor E ℓ) : IsDihedralQuot (rhoC hcard M e)
    (pi1MapC E (ℓ := ℓ) (ℓ' := 1) (M := M) (M' := ⊥) (pm := true) (pm' := true)).range := by
  refine ⟨fun y => ?_, fun y => mem_range_pi1MapC_true_iff hcard M e hMT y, ?_⟩
  · obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    exact rhoGal_mem hcard M e h
  · obtain ⟨σ, hσ⟩ := exists_rhoGal_translation hcard M e
    exact ⟨(QuotientGroup.mk ⟨σ, mem_Hgp_one_bot E σ⟩ : Hgp E 1 ⊥ true ⧸ GaloisPi1.kernel _ _), hσ⟩

/-- `ρ` contains the reflection `z ↦ −z` (`exists_fix_neg` at a place over `0`). -/
theorem exists_rhoGal_reflection : ∃ σ : Gal E, rhoGal hcard M e σ = affPerm ℓ (-1) 0 := by
  obtain ⟨W₀, hW₀⟩ := exists_isCuspPlace (E := E) (ell_ne_zero (ℓ := ℓ)) (T := 0) (nsmul_zero _)
  obtain ⟨ρ₀, -, hρ₀⟩ := exists_fix_neg E (ell_ne_zero (ℓ := ℓ)) (nsmul_zero _) hW₀
  have hs : sgnTr hcard ρ₀ = (-1, 0) := sgnTr_eq hcard (by
    rw [map_zero, sub_zero] at hρ₀
    rw [hρ₀]
    simp)
  refine ⟨ρ₀, ?_⟩
  change affPerm ℓ _ _ = _
  rw [hs, qOf_zero, mul_zero, neg_zero]

theorem isDihedralFull_rhoC : IsDihedralFull (rhoC hcard M e) := by
  refine ⟨fun y => ?_, ?_, ?_⟩
  · obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    exact rhoGal_mem hcard M e h
  · obtain ⟨σ, hσ⟩ := exists_rhoGal_translation hcard M e
    exact ⟨(QuotientGroup.mk ⟨σ, mem_Hgp_one_bot E σ⟩ : Hgp E 1 ⊥ true ⧸ GaloisPi1.kernel _ _), hσ⟩
  · obtain ⟨σ, hσ⟩ := exists_rhoGal_reflection hcard M e
    exact ⟨(QuotientGroup.mk ⟨σ, mem_Hgp_one_bot E σ⟩ : Hgp E 1 ⊥ true ⧸ GaloisPi1.kernel _ _), hσ⟩

/-- The composite `π₁(X̲) → π₁(C̲) → π₁(C)` is the map of the covering `X̲ → C`. -/
lemma pi1MapC_comp_false (hMT : M ≤ Tor E ℓ) :
    (pi1MapC E (ℓ := ℓ) (ℓ' := 1) (M := M) (M' := ⊥) (pm := true) (pm' := true)).comp
      (pi1MapC E (ℓ := ℓ) (ℓ' := ℓ) (M := M) (M' := M) (pm := false) (pm' := true)) =
    pi1MapC E (ℓ := ℓ) (ℓ' := 1) (M := M) (M' := ⊥) (pm := false) (pm' := true) := by
  have hc : Hgp E ℓ M false ≤ Hgp E ℓ M true ∧ SgenC E ℓ M ⊆ SgenC E ℓ M :=
    ⟨Hgp_le E (compatible_divSys_of_charZero E) one_pos (one_mul ℓ)
      (fun P hP => by rwa [one_smul]) (fun _ => rfl), subset_rfl⟩
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  unfold pi1MapC
  rw [dif_pos hc, dif_pos (pi1MapC_cond M hMT true), dif_pos (pi1MapC_cond M hMT false)]
  rfl

end Descent

/-! ### Model orbicurves -/

section Cover

variable {k : Type u} [Field k] [CharZero k] {ℓ : ℕ} [OddPrime ℓ]

/-- **The dihedral action for a covering `C̲ → C`** of model orbicurves, `C̲` of type
`(1, ℓ-tors)^±` and `C = (E ∖ {0})/{±1}`: given `Q(C̲) ≅ F_ℓ`, there is `ρ : π₁(C) → F_ℓ ⋊ {±1}`
with stabiliser of `0` the image of `π₁(C̲)`. -/
theorem exists_rho_of_cover {X Y : Orbicurve k} (c : Orbicurve.Cover X Y)
    (hX : X.IsTypeOneEllTorsPM ℓ) (hY1 : Y.level = 1) (hY2 : Y.M = ⊥) (hY3 : Y.pm = true)
    (e : X.Q ≃+ ZMod ℓ) :
    ∃ ρ : Y.genuinePi1 →* Equiv.Perm (ZMod ℓ), IsDihedralQuot ρ (genuinePi1Cover c).range := by
  cases X with | @mk E hE ℓX M pm =>
  cases Y with | @mk E' hE' ℓY M' pm' =>
  obtain ⟨h, n, hn, hmul, hM, hpm⟩ := c
  change E = E' at h
  subst h
  change ℓY = 1 at hY1
  change M' = ⊥ at hY2
  change pm' = true at hY3
  subst ℓY M' pm'
  obtain ⟨-, hl, hpmX, hMT, -, hcard⟩ := hX
  change ℓX = ℓ at hl
  change pm = true at hpmX
  subst ℓX pm
  exact ⟨rhoC hcard M e, isDihedralQuot_rhoC hcard M e hMT⟩

/-- **The dihedral action for coverings `X̲ → C̲ → C`**, `X̲` of type `(1, ℓ-tors)`: in addition
to `exists_rho_of_cover`, `ρ` is onto `F_ℓ ⋊ {±1}` on generators and its kernel is the image of
`π₁(X̲)` (`X̲ → C` is Galois with group `F_ℓ ⋊ {±1}`). -/
theorem exists_rho_of_covers {X' X Y : Orbicurve k} (c' : Orbicurve.Cover X' X)
    (c : Orbicurve.Cover X Y) (hX' : X'.IsTypeOneEllTors ℓ) (hX : X.IsTypeOneEllTorsPM ℓ)
    (hY1 : Y.level = 1) (hY2 : Y.M = ⊥) (hY3 : Y.pm = true) (e : X.Q ≃+ ZMod ℓ) :
    ∃ ρ : Y.genuinePi1 →* Equiv.Perm (ZMod ℓ), IsDihedralQuot ρ (genuinePi1Cover c).range ∧
      IsDihedralFull ρ ∧ ∀ y, y ∈ ((genuinePi1Cover c).comp (genuinePi1Cover c')).range ↔
        ρ y = 1 := by
  cases X' with | @mk E'' hE'' ℓX' M'' pm'' =>
  cases X with | @mk E hE ℓX M pm =>
  cases Y with | @mk E' hE' ℓY M' pm' =>
  obtain ⟨h, n, hn, hmul, hM, hpm⟩ := c
  obtain ⟨h', n', hn', hmul', hM', hpm'⟩ := c'
  change E = E' at h
  change E'' = E at h'
  subst E'
  subst E
  change ℓY = 1 at hY1
  change M' = ⊥ at hY2
  change pm' = true at hY3
  subst ℓY M' pm'
  obtain ⟨-, hl, hpmX, hMT, hMc, hcard⟩ := hX
  change ℓX = ℓ at hl
  change pm = true at hpmX
  subst ℓX pm
  obtain ⟨-, hl', hpmX', hMT', hMc', -⟩ := hX'
  change ℓX' = ℓ at hl'
  change pm'' = false at hpmX'
  subst ℓX' pm''
  have hn1 : n' = 1 := by
    have h1 : n' * ℓ = 1 * ℓ := by rw [one_mul]; exact hmul'
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ell_ne_zero) h1
  subst hn1
  have hMM : M'' = M := by
    haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hMc]; exact ell_ne_zero)
    refine AddSubgroup.eq_of_le_of_card_ge (fun P hP => ?_) ?_
    · have := hM' P hP
      rwa [one_smul] at this
    · rw [hMc, hMc']
  subst M
  refine ⟨rhoC hcard M'' e, isDihedralQuot_rhoC hcard M'' e hMT, isDihedralFull_rhoC hcard M'' e,
    fun y => ?_⟩
  have hcomp := pi1MapC_comp_false (E := E'') (ℓ := ℓ) M'' hMT
  change y ∈ ((pi1MapC E'' (ℓ := ℓ) (ℓ' := 1) (M := M'') (M' := ⊥) (pm := true)
    (pm' := true)).comp (pi1MapC E'' (ℓ := ℓ) (ℓ' := ℓ) (M := M'') (M' := M'') (pm := false)
    (pm' := true))).range ↔ _
  rw [hcomp]
  exact mem_range_pi1MapC_false_iff hcard M'' e hMT y

end Cover

end Iut.Multiradial.Theater
