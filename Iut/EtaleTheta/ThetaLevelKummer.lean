/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaLevelUnit
import CurvesJacobian.Kummer.PointRestriction
import CurvesJacobian.Cusp.CoverGaloisData
import CurvesJacobian.Kummer.JacobianPi1

/-!
# The étale theta class at the level `Ÿ'_N` and its restriction to points (MR14, G4 étale)

Let `q` be a Tate parameter over a complete nonarchimedean field `K` of characteristic `0` with
`‖2‖ = 1` (odd residue characteristic, IUT I, Def. 3.1(b)), `s² = q`, `N` even, `E = E_q`,
`Ω = K(Ē)^alg`, `τ = x`. By `exists_thetaLevel_etale` and `exists_thetaLevel_unit`, the level
`Ÿ'_N` is an intermediate field `L' ⊆ Ω`, étale over `X = E ∖ {O}`, carrying the theta level
function `F_N` (`F_N(u) = f_N(u^N)`, `f_N = Θ̈_q/Θ̈_{q^N}^N`) as a unit of its coordinate ring.

This file builds the étale (profinite) version of [EtTh], Prop. 1.3/1.4(iii) for route R-alg of
`MR14-plan.md` (lead decision D5: étale level first, tempered version later):

* `D' = fieldData L'` (`H = H_L = Gal(Ω/L')`), the Galois model of `Ÿ'_N`, and the unit
  `η ∈ Γ(Ÿ'_N, 𝒪^×)` with value `F_N`; the **étale theta class** at level `n ∣ N` is
  `η̈_n = κ_n(η) ∈ H¹(Π_{Ÿ'_N}, μ_n)` (`KummerTheory.Curve.kummerMap`);
* **places over Tate points** (`exists_place_tate`): for `u ∈ Kˣ` with `ψ_{2N}(u) ≠ 0` there is a
  valuation subring `W ⊆ Ω` centred on the `τ`-line whose centre on `L_{2N}` is the kernel of the
  evaluation at `u`; residues at `W` of functions on `L_{2N}` are their values
  (`residue_toΩ_eq`), so `W` is a `K`-rational point of every level `L' ≤ L_{2N}`
  (`rational_of_center`, `exists_ratPoint_tate`);
* **Prop. 1.4(iii) at points** (`exists_etaleThetaClass`, with the per-point statement
  `EtaleThetaAtPoint`): along the section `s_x : Gal(κ(W)/K) → Π_{Ÿ'_N}` of the point `x` over
  `u` (the point `u^N` of `Ÿ'_N`), `s_x^* η̈_n = κ_n(Θ̈(u^N))` for every `n ∣ N`
  (`continuous-kummer-theory`'s `ratSectionMap_kummerMap` and `kummer_thetaLevel`).

Points are parametrised by `u ∈ Kˣ` (so `Ü = u^N` is an `N`-th power in `K`); other `K`-points
of `Ÿ'_N` need a finite extension of `K` (see the MR14 plan, run 4 hand-off).
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta

/-! ### Residues at places centred on a rational point of a coordinate ring -/

section Residue

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {W : ValuationSubring Ω}

theorem toΩ_algebraMap_k (M : IntermediateField (K₀ k t) Ω) (c : k) :
    toΩ t M (algebraMap k (coordRing k t M) c) = algebraMap k Ω c := rfl

/-- If the centre of `W` on `M` is the kernel of a `k`-point `ev` of the coordinate ring, residues
of elements of the coordinate ring are their values. -/
theorem residue_toΩ_eq (hW : IsCentered k t W) (M : IntermediateField (K₀ k t) Ω)
    (ev : coordRing k t M →+* k) (hev : ∀ c, ev (algebraMap k _ c) = c)
    (hQ : centerIdeal hW M = RingHom.ker ev) (b : coordRing k t M) :
    residue W ⟨toΩ t M b, toΩ_mem hW M b⟩ = residue W ⟨algebraMap k Ω (ev b), hW.1 _⟩ := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  have hm : b - algebraMap k _ (ev b) ∈ centerIdeal hW M := by
    rw [hQ, RingHom.mem_ker, RingHom.map_sub, hev, sub_self]
  rw [mem_centerIdeal_iff_mem_nonunits, ← mem_maximalIdeal] at hm
  convert hm using 1
  apply Subtype.ext
  change toΩ t M b - algebraMap k Ω (ev b) = toΩ t M (b - algebraMap k _ (ev b))
  rw [RingHom.map_sub, toΩ_algebraMap_k]

/-- **Rationality at a `k`-point**: elements of `M` integral at `W` have residues in `k`. -/
theorem rational_of_center [CharZero k] (ht : Transcendental k t) (hW : IsCentered k t W)
    (M : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) M]
    (ev : coordRing k t M →+* k) (hev : ∀ c, ev (algebraMap k _ c) = c)
    (hQ : centerIdeal hW M = RingHom.ker ev) (hM : centerIdeal hW M ≠ ⊥) {x : Ω}
    (hxM : x ∈ M) (hxW : x ∈ W) :
    ∃ c : k, residue W ⟨x, hxW⟩ = residue W ⟨algebraMap k Ω c, hW.1 c⟩ := by
  haveI := isSeparable_of_charZero (t := t) M
  obtain ⟨b, s, hs, rfl⟩ := exists_eq_div ht hW M hM hxM hxW
  have hs' : ev s ≠ 0 := by rwa [hQ, RingHom.mem_ker] at hs
  have hs0 : toΩ t M s ≠ 0 := by
    intro h
    apply hs
    rw [← map_zero (toΩ t M)] at h
    rw [toΩ_injective M h]
    exact Ideal.zero_mem _
  refine ⟨ev b / ev s, ?_⟩
  have e1 : (⟨toΩ t M b / toΩ t M s, hxW⟩ : W) * ⟨toΩ t M s, toΩ_mem hW M s⟩ =
      ⟨toΩ t M b, toΩ_mem hW M b⟩ := Subtype.ext (div_mul_cancel₀ _ hs0)
  have e2 : (⟨algebraMap k Ω (ev b / ev s), hW.1 _⟩ : W) * ⟨algebraMap k Ω (ev s), hW.1 _⟩ =
      ⟨algebraMap k Ω (ev b), hW.1 _⟩ := Subtype.ext (by
    change algebraMap k Ω (ev b / ev s) * algebraMap k Ω (ev s) = algebraMap k Ω (ev b)
    rw [← map_mul, div_mul_cancel₀ _ hs'])
  have hr : residue W ⟨algebraMap k Ω (ev s), hW.1 _⟩ ≠ 0 := by
    rw [Ne, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not]
    refine IsUnit.of_mul_eq_one ⟨algebraMap k Ω (ev s)⁻¹, hW.1 _⟩ (Subtype.ext ?_)
    change algebraMap k Ω (ev s) * algebraMap k Ω (ev s)⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hs', map_one]
  have h1 := congrArg (residue W) e1
  have h2 := congrArg (residue W) e2
  rw [map_mul, residue_toΩ_eq hW M ev hev hQ s] at h1
  rw [map_mul] at h2
  rw [residue_toΩ_eq hW M ev hev hQ b] at h1
  exact mul_right_cancel₀ hr (h1.trans h2.symm)

/-- The centre of `W` is nonzero if it is the kernel of a `k`-point (`t` is transcendental). -/
theorem centerIdeal_ne_bot (ht : Transcendental k t) (hW : IsCentered k t W)
    (M : IntermediateField (K₀ k t) Ω) (ev : coordRing k t M →+* k)
    (hev : ∀ c, ev (algebraMap k _ c) = c) (hQ : centerIdeal hW M = RingHom.ker ev) :
    centerIdeal hW M ≠ ⊥ := by
  intro h
  set τ' : coordRing k t M := algebraMap (A₀ k t) (coordRing k t M) ⟨t, Algebra.subset_adjoin rfl⟩
  have hz : τ' - algebraMap k _ (ev τ') ∈ centerIdeal hW M := by
    rw [hQ, RingHom.mem_ker, RingHom.map_sub, hev, sub_self]
  rw [h, Ideal.mem_bot] at hz
  have hz' := congrArg (toΩ t M) hz
  rw [RingHom.map_sub, RingHom.map_zero, toΩ_algebraMap_k, sub_eq_zero] at hz'
  change t = algebraMap k Ω (ev τ') at hz'
  exact ht (by rw [hz']; exact isAlgebraic_algebraMap (ev τ'))

/-- A unit of the Galois model `fieldData L'` from an element of `L'` integral over `k[t]` with
integral inverse. -/
theorem exists_unit_fieldData [IsGalois (K₀ k t) Ω] (ht : Transcendental k t)
    (L' : IntermediateField (K₀ k t) Ω)
    (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))) {z : Ω} (hz : z ∈ L')
    (hz0 : z ≠ 0) (hi : IsIntegral (A₀ k t) z) (hi' : IsIntegral (A₀ k t) z⁻¹) :
    ∃ η : units (CurvesJacobian.Cusp.fieldData ht L' hL'),
      ((((η : (F (CurvesJacobian.Cusp.fieldData ht L' hL'))ˣ) :
        F (CurvesJacobian.Cusp.fieldData ht L' hL')) : Ω)) = z := by
  have hFD : F (CurvesJacobian.Cusp.fieldData ht L' hL') = L' :=
    InfiniteGalois.fixedField_fixingSubgroup L'
  have hzF : z ∈ F (CurvesJacobian.Cusp.fieldData ht L' hL') := (SetLike.ext_iff.mp hFD z).mpr hz
  refine ⟨⟨Units.mk0 ⟨z, hzF⟩ fun h => hz0 (congrArg Subtype.val h),
    (CoordRing.isIntegral_coe_iff (F := F (CurvesJacobian.Cusp.fieldData ht L' hL')) _).1 hi,
    (CoordRing.isIntegral_coe_iff (F := F (CurvesJacobian.Cusp.fieldData ht L' hL')) _).1 ?_⟩, rfl⟩
  rw [Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
  exact hi'

/-- Elements of the function field of `fieldData L'` lie in `L'`. -/
theorem mem_of_mem_F_fieldData [IsGalois (K₀ k t) Ω] (ht : Transcendental k t)
    (L' : IntermediateField (K₀ k t) Ω)
    (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
    (a : F (CurvesJacobian.Cusp.fieldData ht L' hL')) : (a : Ω) ∈ L' := by
  have hFD : F (CurvesJacobian.Cusp.fieldData ht L' hL') = L' :=
    InfiniteGalois.fixedField_fixingSubgroup L'
  exact (SetLike.ext_iff.mp hFD (a : Ω)).mp a.2

end Residue

/-- **Residue fields under algebraic extensions** (a copy of `curves-jacobian`'s
`LocAn.SectionBridge.isIntegral_residueField_of_rational`, whose module is outside iut's build):
let `A` be a place of `Ω`, algebraic over a
subfield `E`, and suppose the residue of every element of `E ∩ A` lies in the image of `k`. Then
`κ(A)` is algebraic over `k`. -/
theorem isIntegral_residueField_of_rational {Ω E k : Type u} [Field Ω] [Field E] [Field k]
    [Algebra E Ω] [Algebra.IsAlgebraic E Ω] (A : ValuationSubring Ω) [Algebra k (ResidueField A)]
    (hrat : ∀ (a : E) (ha : algebraMap E Ω a ∈ A),
      ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c) :
    Algebra.IsIntegral k (ResidueField A) := by
  classical
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective y
  obtain ⟨p, hp0, hpb⟩ := Algebra.IsAlgebraic.isAlgebraic (R := E) (b : Ω)
  obtain ⟨i₀, hi₀, hmax⟩ := p.support.exists_max_image
    (fun i ↦ A.valuation (algebraMap E Ω (p.coeff i))) (Polynomial.nonempty_support_iff.2 hp0)
  set c₀ : E := p.coeff i₀ with hc₀def
  have hc₀ : c₀ ≠ 0 := Polynomial.mem_support_iff.1 hi₀
  have hv₀ : A.valuation (algebraMap E Ω c₀) ≠ 0 := by
    rw [Ne, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap E Ω).injective]
    exact hc₀
  have hd : ∀ i, algebraMap E Ω (p.coeff i / c₀) ∈ A := by
    intro i
    rw [← A.valuation_le_one_iff, map_div₀, map_div₀]
    by_cases hi : i ∈ p.support
    · exact (div_le_one₀ (zero_lt_iff.2 hv₀)).2 (hmax i hi)
    · rw [Polynomial.notMem_support_iff.1 hi, map_zero, map_zero, zero_div]
      exact zero_le
  choose c hc using fun i ↦ hrat (p.coeff i / c₀) (hd i)
  let r : Polynomial k := ∑ i ∈ p.support, Polynomial.monomial i (c i)
  have hr0 : r ≠ 0 := by
    intro h
    have h1 : r.coeff i₀ = c i₀ := by
      simp only [r, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single i₀ (fun j _ hj ↦ if_neg hj) (fun h ↦ absurd hi₀ h), if_pos rfl]
    rw [h, Polynomial.coeff_zero] at h1
    have h2 := hc i₀
    rw [← h1, map_zero] at h2
    have h3 : (⟨algebraMap E Ω (p.coeff i₀ / c₀), hd i₀⟩ : A) = 1 := by
      apply Subtype.ext
      change algebraMap E Ω (p.coeff i₀ / c₀) = 1
      rw [← hc₀def, div_self hc₀, map_one]
    rw [h3, map_one] at h2
    exact one_ne_zero h2
  refine (show IsAlgebraic k (residue A b) from ⟨r, hr0, ?_⟩).isIntegral
  have hsum : (∑ i ∈ p.support, (⟨algebraMap E Ω (p.coeff i / c₀), hd i⟩ : A) * b ^ i) = 0 := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]
    change ∑ i ∈ p.support, algebraMap E Ω (p.coeff i / c₀) * (b : Ω) ^ i = 0
    have : (Polynomial.aeval (b : Ω) p) =
        ∑ i ∈ p.support, algebraMap E Ω (p.coeff i) * (b : Ω) ^ i := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    have h2 : ∑ i ∈ p.support, algebraMap E Ω (p.coeff i / c₀) * (b : Ω) ^ i =
        (Polynomial.aeval (b : Ω) p) * (algebraMap E Ω c₀)⁻¹ := by
      rw [this, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_div₀]
      ring
    rw [h2, hpb, zero_mul]
  have := congrArg (residue A) hsum
  rw [map_zero, map_sum] at this
  rw [← this, map_sum]
  simp only [Polynomial.aeval_monomial, map_mul, map_pow, hc]

/-! ### The point of `L_{2N}` over a Tate point -/

section Level

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateCurvesTheta.TateParameter K}

open CurvesJacobian.Cusp TateCurvesTheta TateParameter

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

section Eval

variable [t.tateCurve.IsElliptic] (m : ℕ) [NeZero m]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem coverEquivCoordRing_algebraMap (c : K) :
    coverEquivCoordRing t.tateCurve m (algebraMap K _ c) = algebraMap K _ c := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_coverEquivCoordRing, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  rfl

/-- **Evaluation of the coordinate ring of `L_m` at the Tate point `u`** (`ψ_m(u) ≠ 0`). -/
def evalLevel {h12 : (12 : K) ≠ 0} {u : Kˣ} (hu : OffOrbit t u)
    (hψ : evalTate t h12 hu (psiN t.tateCurve m) ≠ 0) :
    coordRing K τ (mulByNField t.tateCurve m) →+* K :=
  (evalCover m hu hψ).comp (coverEquivCoordRing t.tateCurve m).symm.toRingHom

variable {h12 : (12 : K) ≠ 0} {u : Kˣ} (hu : OffOrbit t u)
  (hψ : evalTate t h12 hu (psiN t.tateCurve m) ≠ 0)

theorem evalLevel_coverEquiv (b : coverRingN t.tateCurve m) :
    evalLevel m hu hψ (coverEquivCoordRing t.tateCurve m b) = evalCover m hu hψ b := by
  simp [evalLevel]

theorem evalLevel_algebraMap (c : K) : evalLevel m hu hψ (algebraMap K _ c) = c := by
  rw [← coverEquivCoordRing_algebraMap, evalLevel_coverEquiv, evalCover_algebraMap_K]

/-- **A place of `Ω` over the Tate point `u`**: a valuation subring centred on the `τ`-line whose
centre on `L_m` is the kernel of the evaluation at `u`. -/
theorem exists_place_tate :
    ∃ (W : ValuationSubring Ω) (hW : IsCentered K τ W),
      centerIdeal hW (mulByNField t.tateCurve m) = RingHom.ker (evalLevel m hu hψ) := by
  haveI : (RingHom.ker (evalLevel m hu hψ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c => ⟨_, evalLevel_algebraMap m hu hψ c⟩
  exact exists_isCentered_centerIdeal_eq _ _

/-- **The `K`-rational point of `Ÿ'_N` over the Tate point `u`**: for any level
`L' ≤ L_m` with open fixing group, a place `W` over `u` (`exists_place_tate`) is a `K`-rational
point of the Galois model `fieldData L'`, and residues at `W` of functions on `L_m` are their
values at `u`. -/
theorem exists_ratPoint_tate (L' : IntermediateField (K₀ K τ) Ω)
    (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
    (hle : L' ≤ mulByNField t.tateCurve m) :
    ∃ (x : RatPoint (fieldData (transcendental_tau t.tateCurve) L' hL')) (_ : τ ∈ x.A)
      (hmem : ∀ b₀ : coverRingN t.tateCurve m, mulByNEmb t.tateCurve m (algebraMap _ _ b₀) ∈ x.A),
      ∀ b₀ : coverRingN t.tateCurve m,
        residue x.A ⟨_, hmem b₀⟩ = algebraMap K (ResidueField x.A) (evalCover m hu hψ b₀) := by
  obtain ⟨W, hW, hQ⟩ := exists_place_tate m hu hψ
  have hne := centerIdeal_ne_bot (transcendental_tau t.tateCurve) hW _ _
    (evalLevel_algebraMap m hu hψ) hQ
  letI := resAlg W hW.1
  have hrat : ∀ (a : F (fieldData (transcendental_tau t.tateCurve) L' hL')) (ha : (a : Ω) ∈ W),
      ∃ c : K, residue W ⟨_, ha⟩ = algebraMap K (ResidueField W) c := fun a ha =>
    rational_of_center (transcendental_tau t.tateCurve) hW _ _
      (evalLevel_algebraMap m hu hψ) hQ hne
      (hle (mem_of_mem_F_fieldData (transcendental_tau t.tateCurve) L' hL' a)) ha
  haveI : Algebra.IsAlgebraic (F (fieldData (transcendental_tau t.tateCurve) L' hL')) Ω :=
    Algebra.IsAlgebraic.tower_top (K := K₀ K τ) _
  refine ⟨⟨W, hW.1, isIntegral_residueField_of_rational
    (E := F (fieldData (transcendental_tau t.tateCurve) L' hL')) W hrat, hrat⟩, hW.2,
    fun b₀ => toΩ_mem hW _ (coverEquivCoordRing t.tateCurve m b₀), fun b₀ => ?_⟩
  have := residue_toΩ_eq hW _ _ (evalLevel_algebraMap m hu hψ) hQ
    (coverEquivCoordRing t.tateCurve m b₀)
  rw [evalLevel_coverEquiv] at this
  exact this

end Eval

/-! ### The étale theta class at level `Ÿ'_N` and Prop. 1.4(iii) at points -/

/-- The Kummer computation at a rational point: if the unit `η` has the value `f_N(u^N)` at `x`,
then `s_x^* κ_n(η) = κ_n(Θ̈(u^N))` for `n ∣ N`. -/
theorem ratSection_kummer_eq [t.tateCurve.IsElliptic]
    {N : ℕ} [NeZero (2 * N)] (hN : 0 < N) (L' : IntermediateField (K₀ K τ) Ω)
    (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
    (η : units (fieldData (transcendental_tau t.tateCurve) L' hL'))
    (x : RatPoint (fieldData (transcendental_tau t.tateCurve) L' hL')) (hτ : τ ∈ x.A)
    {b : coverRingN t.tateCurve (2 * N)}
    (hη : ((((η : (F (fieldData (transcendental_tau t.tateCurve) L' hL'))ˣ) :
      F (fieldData (transcendental_tau t.tateCurve) L' hL')) : Ω)) =
        mulByNEmb t.tateCurve (2 * N) (algebraMap _ _ b))
    (hbW : mulByNEmb t.tateCurve (2 * N) (algebraMap _ _ b) ∈ x.A) {v : K}
    (hbres : residue x.A ⟨_, hbW⟩ = algebraMap K (ResidueField x.A) v) {u : Kˣ}
    (hval : v = thetaLevel t N hN (u ^ N)) (hU : etaleTheta t (u ^ N) ≠ 0)
    (n : ℕ) [NeZero n] (hn : n ∣ N) :
    haveI := isAlgClosed_residueField x.A x.hk x.hkres
    haveI := isGalois_residueField x.A x.hk x.hkres
    ContH1.map (ratSectionMap (fieldData (transcendental_tau t.tateCurve) L' hL') x.A x.hk
        x.hkres x.hrat rfl hτ)
        (continuous_ratSectionMap (fieldData (transcendental_tau t.tateCurve) L' hL') x.A x.hk
          x.hkres x.hrat rfl hτ)
        (Decomposition.reduceMu x.A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_sectionMap_smul (fieldData (transcendental_tau t.tateCurve) L' hL') x.A x.hk
          x.hkres rfl hτ _ n)
        (kummerMap (fieldData (transcendental_tau t.tateCurve) L' hL') n η) =
      kummer n K (ResidueField x.A) (etaleThetaUnit t (u ^ N) hU) := by
  haveI := isAlgClosed_residueField x.A x.hk x.hkres
  haveI := isGalois_residueField x.A x.hk x.hkres
  obtain ⟨hu₁, hu₂⟩ := units_mem (W := x.A) ⟨x.hk, hτ⟩ η.2
  have hua : residue x.A ⟨_, hu₁⟩ =
      algebraMap K (ResidueField x.A) (thetaLevelUnit t N hN hU : K) := by
    have e : (⟨_, hu₁⟩ : x.A) = ⟨_, hbW⟩ := Subtype.ext hη
    rw [e, hbres, hval]
    rfl
  exact (ratSectionMap_kummerMap (fieldData (transcendental_tau t.tateCurve) L' hL') x.A x.hk
    x.hkres x.hrat rfl hτ n η _ hu₁ hu₂ hua).trans
    (kummer_thetaLevel t N hN n (ResidueField x.A) hn hU)

/-- **The étale theta class at a Tate point** (the conclusion of [EtTh] Prop. 1.4(iii) at a point,
étale version): for the level `L'` with Galois model `fieldData L'` and the unit `η`, the point
`u` (`ψ_{2N}(u) ≠ 0`) has `Θ̈(u^N) ≠ 0`, there is a `K`-rational point `x` of `fieldData L'` over
the Tate point `u` (residues of functions on `L_{2N}` are their values at `u`), and the restriction
of `κ_n(η)` along the section of `x` is `κ_n(Θ̈(u^N))` for every `n ∣ N`. -/
def EtaleThetaAtPoint [t.tateCurve.IsElliptic] (h12 : (12 : K) ≠ 0) (N : ℕ) [NeZero (2 * N)]
    (L' : IntermediateField (K₀ K τ) Ω)
    (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
    (η : units (fieldData (transcendental_tau t.tateCurve) L' hL')) (u : Kˣ) (hu : OffOrbit t u)
    (hψ : evalTate t h12 hu (psiN t.tateCurve (2 * N)) ≠ 0) : Prop :=
  ∃ (hU : etaleTheta t (u ^ N) ≠ 0)
    (x : RatPoint (fieldData (transcendental_tau t.tateCurve) L' hL')) (hτ : τ ∈ x.A),
    ∃ hmem : ∀ b : coverRingN t.tateCurve (2 * N),
        mulByNEmb t.tateCurve (2 * N) (algebraMap _ _ b) ∈ x.A,
      (∀ b : coverRingN t.tateCurve (2 * N), residue x.A ⟨_, hmem b⟩ =
        algebraMap K (ResidueField x.A) (evalCover (2 * N) hu hψ b)) ∧
    ∀ (n : ℕ) [NeZero n], n ∣ N →
      haveI := isAlgClosed_residueField x.A x.hk x.hkres
      haveI := isGalois_residueField x.A x.hk x.hkres
      ContH1.map (ratSectionMap (fieldData (transcendental_tau t.tateCurve) L' hL') x.A x.hk
          x.hkres x.hrat rfl hτ)
          (continuous_ratSectionMap (fieldData (transcendental_tau t.tateCurve) L' hL') x.A
            x.hk x.hkres x.hrat rfl hτ)
          (Decomposition.reduceMu x.A n (NeZero.ne n)) continuous_of_discreteTopology
          (reduceMu_sectionMap_smul (fieldData (transcendental_tau t.tateCurve) L' hL') x.A
            x.hk x.hkres rfl hτ _ n)
          (kummerMap (fieldData (transcendental_tau t.tateCurve) L' hL') n η) =
        kummer n K (ResidueField x.A) (etaleThetaUnit t (u ^ N) hU)

/-- The per-point part of `exists_etaleThetaClass`. -/
theorem etaleThetaClass_points [hE : t.tateCurve.IsElliptic] {N : ℕ} [hN2 : NeZero (2 * N)]
    (hN : 0 < N)
    {h12 : (12 : K) ≠ 0} (L' : IntermediateField (K₀ K τ) Ω)
    (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
    (hle : L' ≤ mulByNField t.tateCurve (2 * N))
    (η : units (fieldData (transcendental_tau t.tateCurve) L' hL'))
    {b : coverRingN t.tateCurve (2 * N)}
    (hη : ((((η : (F (fieldData (transcendental_tau t.tateCurve) L' hL'))ˣ) :
      F (fieldData (transcendental_tau t.tateCurve) L' hL')) : Ω)) =
        mulByNEmb t.tateCurve (2 * N) (algebraMap _ _ b))
    (hpt : ∀ (u : Kˣ) (hu : OffOrbit t u)
      (hψ : evalTate t h12 hu (psiN t.tateCurve (2 * N)) ≠ 0),
        etaleTheta t (u ^ N) ≠ 0 ∧ evalCover (2 * N) hu hψ b = thetaLevel t N hN (u ^ N)) :
    ∀ (u : Kˣ) (hu : OffOrbit t u) (hψ : evalTate t h12 hu (psiN t.tateCurve (2 * N)) ≠ 0),
      EtaleThetaAtPoint h12 N L' hL' η u hu hψ := by
  intro u hu hψ
  obtain ⟨hU, hval⟩ := hpt u hu hψ
  obtain ⟨x, hτ, hmem, hres⟩ := exists_ratPoint_tate (2 * N) hu hψ L' hL' hle
  exact ⟨hU, x, hτ, hmem, hres, fun n _ hn =>
    ratSection_kummer_eq hN L' hL' η x hτ hη (hmem b) (hres b) hval hU n hn⟩

/-- **[EtTh] Prop. 1.3/1.4(iii), étale version at the level `Ÿ'_N`** (route R-alg). For even `N`
there are an intermediate field `L' ⊆ Ω` (the function field of `Ÿ'_N`, finite over `K(τ)`,
`L_X ≤ L'`) with `coordRing L_X → coordRing L'` étale, and a unit `η` of `Ÿ'_N`
(the theta level function `F_N`) such that: for every `u ∈ Kˣ` with `ψ_{2N}(u) ≠ 0` there is a
`K`-rational point `x` of the Galois model `D' = fieldData L'` lying over the Tate point `u` of
`E_q ∖ E_q[2N]` (residues of functions on `L_{2N}` are their values at `u`), at which
`Θ̈(u^N) ≠ 0` and, for every `n ∣ N`, the restriction of the étale theta class
`η̈_n = κ_n(η) ∈ H¹(Π_{Ÿ'_N}, μ_n)` along the section `s_x` of `x` is the Kummer class of the
value `Θ̈(u^N)` of the étale theta function at the point `u^N` of `Ÿ'_N`:
`s_x^* η̈_n = κ_n(Θ̈(u^N))`. -/
theorem exists_etaleThetaClass (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ}
    (hs : s ^ 2 = t.q) {N : ℕ} (hN : 0 < N) (T : TateCurvesTheta.TateParameter K)
    (hT : T.q = s ^ N) (hev : Even N) :
    haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
    haveI : NeZero (2 * N) := ⟨by omega⟩
    ∃ (L' : IntermediateField (K₀ K τ) Ω)
      (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
      (h₁ : (hemiData t.tateCurve).L ≤ L')
      (η : units (fieldData (transcendental_tau t.tateCurve) L' hL')),
      (ringMap τ h₁).toRingHom.Etale ∧
      ∀ (u : Kˣ) (hu : OffOrbit t u) (hψ : evalTate t h12 hu (psiN t.tateCurve (2 * N)) ≠ 0),
        EtaleThetaAtPoint h12 N L' hL' η u hu hψ := by
  haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
  haveI : NeZero (2 * N) := ⟨by omega⟩
  obtain ⟨gX, gY, Fθ, ⟨h₁, het⟩, hFL, ⟨b, b', hb, hb'⟩, hpt⟩ :=
    exists_thetaLevel_unit h2 h12 hs hN T hT hev
  have hle : IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}) ≤
      mulByNField t.tateCurve (2 * N) := adjoin_image_le_mulByNField _ _ _
  haveI hfd : FiniteDimensional (K₀ K τ)
      (IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY})) :=
    finiteDimensional_adjoin_image _ _ _
  generalize IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}) = L'
    at h₁ het hFL hle hfd
  have hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)) := L'.fixingSubgroup_isOpen
  -- `F_N ≠ 0`: it has a nonzero value at a Tate point with `ψ_{2N}(u) ≠ 0`
  have hF0 : Fθ ≠ 0 := by
    by_contra hF
    apply psiN_ne_zero_of_neZero t.tateCurve (2 * N)
    refine eq_zero_of_evalTate (h12 := h12) _ fun u hu => ?_
    by_contra hψ
    obtain ⟨-, -, hl, hv⟩ := hpt u hu hψ
    exact hv.ne_zero hl hF
  have hint : IsIntegral (A₀ K τ) (mulByNEmb t.tateCurve (2 * N) Fθ) := by
    rw [← hb]; exact isIntegral_mulByNEmb _ _ b
  have hint' : IsIntegral (A₀ K τ) (mulByNEmb t.tateCurve (2 * N) Fθ)⁻¹ := by
    rw [← map_inv₀, ← hb']; exact isIntegral_mulByNEmb _ _ b'
  obtain ⟨η, hη⟩ := exists_unit_fieldData (transcendental_tau t.tateCurve) L' hL' hFL
    ((_root_.map_ne_zero _).mpr hF0) hint hint'
  refine ⟨L', hL', h₁, η, het, etaleThetaClass_points hN L' hL' hle η
    (hη.trans (congrArg (mulByNEmb t.tateCurve (2 * N)) hb.symm)) fun u hu hψ => ?_⟩
  obtain ⟨-, hU, -, hv⟩ := hpt u hu hψ
  have h := hasTateValue_cover (2 * N) hu hψ b
  rw [hb] at h
  exact ⟨hU, h.unique hv⟩

end Level

end Iut.EtaleTheta
