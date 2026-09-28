/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Genuine.Realize

/-!
# Covers of model orbicurves are finite étale morphisms of affine orbicurves

For a cover `X = (E, ℓ, M, ±) → Y = (E, ℓ', M', ±')` of model orbicurves (characteristic `0`), the
inclusions of function fields `F_Y ⊆ F_X`, `L_Y ⊆ L_X` induce finite étale morphisms of the
affine orbicurves `realize X → realize Y` (`Iut.Anabelian.Genuine.realizeHom`).

The key input is that `X_M → X_{M'}` is unramified (`ramificationIdx_geom_eq_one`): in a finite
Galois extension `N ⊇ L_X` of `k(x)`, the inertia group of a prime of the normalization of the
`x`-line in `N` fixes the division point `Q_ℓ` (`inertia_fixes_Q`, from
`Iut.Anabelian.Genuine.inertia_fixes_of_nsmul`, applied to the valuation of the prime), hence
fixes `L_X`, and `e = |inertia| / |inertia ∩ Gal(N / L_X)|` (`AffOrbicurve.ramificationIdx_eq_one_iff`).
-/

namespace Iut.Anabelian.Genuine

universe u

open WeierstrassCurve Polynomial AffOrbicurve IntermediateField IntermediateField.algebraAdjoinAdjoin

open scoped Classical

attribute [local instance 2000] Classical.propDecidable

noncomputable section

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-! ### The generic point lies in every `L_X`; `L_X ⊆ k(x, Q_ℓ)` -/

lemma act_generic_of_mem_geom {ℓ : ℕ} {M : AddSubgroup E.toAffine.Point} {σ : Gal E}
    (hσ : σ ∈ Hgp E ℓ M false) : act E σ (genericPoint E) = genericPoint E := by
  obtain ⟨ε, hε, hT⟩ := hσ
  have hε1 : ε = 1 := by rcases hε with h | ⟨h, -⟩; exacts [h, absurd h (by simp)]
  subst hε1
  have hc := compatible_divSys_of_charZero E
  rw [← effLevel_smul_Qpt E hc ℓ, map_nsmul]
  have : act E σ (Qpt E ℓ) = Qpt E ℓ + (act E σ (Qpt E ℓ) - (1 : ℤ) • Qpt E ℓ) := by
    rw [one_smul]; abel
  rw [this, nsmul_add, effLevel_smul_Mbar E hT, add_zero]

lemma xG_yG_mem_geomField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    xG E ∈ geomField E ℓ M ∧ yG E ∈ geomField E ℓ M := by
  have key : ∀ σ ∈ fullSub E ℓ M false, σ (xG E) = xG E ∧ σ (yG E) = yG E := by
    intro σ hσ
    have h : act E (galEquiv E σ) (genericPoint E) = genericPoint E :=
      act_generic_of_mem_geom E hσ
    have h' : act E (galEquiv E σ) (genericPoint E) =
        Affine.Point.some (σ (xG E)) (σ (yG E)) ((Affine.baseChange_nonsingular (W := E)
          (f := σk E (galEquiv E σ)) (σk E (galEquiv E σ)).toRingHom.injective _ _).mpr
          (nonsingular_generic E)) := rfl
    rw [h'] at h
    exact ⟨(Affine.Point.some.inj h).1, (Affine.Point.some.inj h).2⟩
  exact ⟨fun σ => (key σ σ.2).1, fun σ => (key σ σ.2).2⟩

lemma geomField_le_QFieldX (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    geomField E ℓ M ≤ QFieldX E ℓ := by
  have h1 : fixedField (QFieldX E ℓ).fixingSubgroup = QFieldX E ℓ :=
    InfiniteGalois.fixedField_fixingSubgroup (QFieldX E ℓ)
  rw [← h1]
  exact IntermediateField.fixedField_antitone (QFieldX_fixing_le E ℓ M false)

/-! ### Inertia at a prime of the normalization of the `x`-line in a finite extension -/

section Prime

variable {N : IntermediateField (xLine E) (Ω E)} [FiniteDimensional (xLine E) N]

instance separable_of_charZero (L : IntermediateField (xLine E) (Ω E)) :
    Algebra.IsSeparable (xLine E) L := by
  haveI : CharZero (xLine E) := charZero_of_injective_algebraMap (algebraMap k (xLine E)).injective
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- The valuation subring of `N` at a nonzero prime `u` of `coordRing N` (the local ring of the
normalization of the `x`-line in `N` at `u`). -/
def valSub (u : Ideal (coordRing k (xG E) N)) (hu : u.IsPrime) (hu0 : u ≠ ⊥) :
    ValuationSubring N :=
  haveI := isDedekindDomain_ring (xG E) (transcendental_xG E) N
  haveI := isFractionRing_coordRing (xG E) N
  (IsDedekindDomain.HeightOneSpectrum.valuation N ⟨u, hu, hu0⟩).valuationSubring

omit [E.IsElliptic] in
lemma coordRing_mem_valSub (u : Ideal (coordRing k (xG E) N)) (hu : u.IsPrime) (hu0 : u ≠ ⊥)
    (b : coordRing k (xG E) N) : (b : N) ∈ valSub E u hu hu0 := by
  haveI := isDedekindDomain_ring (xG E) (transcendental_xG E) N
  haveI := isFractionRing_coordRing (xG E) N
  exact (⟨u, hu, hu0⟩ : IsDedekindDomain.HeightOneSpectrum (coordRing k (xG E) N)).valuation_le_one (K := N) b

/-- For a valuation `v`, `v x < 1` implies `x` lies in the maximal ideal of `v.valuationSubring`. -/
lemma valuationSubring_valuation_lt_one {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {x : K} (hx : v x < 1) : v.valuationSubring.valuation x < 1 := by
  rw [valuation_lt_one_iff_mem]
  refine ⟨(Valuation.mem_valuationSubring_iff v x).mpr hx.le, ?_⟩
  by_cases h0 : x = 0
  · exact Or.inl h0
  right
  rw [Valuation.mem_valuationSubring_iff, map_inv₀, not_le]
  exact one_lt_inv_iff₀.mpr ⟨(Valuation.pos_iff v).mpr h0, hx⟩

omit [E.IsElliptic] in
lemma valSub_lt_one (u : Ideal (coordRing k (xG E) N)) (hu : u.IsPrime) (hu0 : u ≠ ⊥)
    (b : coordRing k (xG E) N) (hb : b ∈ u) :
    (valSub E u hu hu0).valuation (b : N) < 1 := by
  haveI := isDedekindDomain_ring (xG E) (transcendental_xG E) N
  haveI := isFractionRing_coordRing (xG E) N
  exact valuationSubring_valuation_lt_one _
    (((⟨u, hu, hu0⟩ : IsDedekindDomain.HeightOneSpectrum (coordRing k (xG E) N)).valuation_lt_one_iff_mem
      (K := N) b).mpr hb)

end Prime

/-! ### Inertia fixes `Q_ℓ` (at the level of a finite extension `N`) -/

section InertiaQ

variable {N : IntermediateField (xLine E) (Ω E)} [FiniteDimensional (xLine E) N]

lemma xG_mem_coordRing : (⟨xG E, (N.algebraMap_mem ⟨xG E, xG_mem_xLine E⟩ :)⟩ : N) ∈
    coordRing k (xG E) N := by
  rw [mem_integralClosure_iff]
  have : (⟨xG E, (N.algebraMap_mem ⟨xG E, xG_mem_xLine E⟩ :)⟩ : N) =
      algebraMap (A₀ k (xG E)) N ⟨xG E, Algebra.self_mem_adjoin_singleton k _⟩ := rfl
  rw [this]
  exact isIntegral_algebraMap

/-- The coordinate ring of `N` as a `k`-subalgebra. -/
abbrev coordRingK (N : IntermediateField (xLine E) (Ω E)) : Subalgebra k N :=
  (coordRing k (xG E) N).restrictScalars k

omit [CharZero k] [E.IsElliptic] [FiniteDimensional (xLine E) N] in
set_option synthInstance.maxHeartbeats 400000 in
lemma coordRingK_isIntegrallyClosed (x : N) (hx : _root_.IsIntegral (coordRingK E N) x) :
    x ∈ coordRingK E N := by
  change x ∈ coordRing k (xG E) N
  rw [mem_integralClosure_iff]
  obtain ⟨q, hq, hqx⟩ := hx
  let f : coordRingK E N →+* coordRing k (xG E) N :=
    { toFun := fun a => ⟨a.1, a.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hx' : _root_.IsIntegral (coordRing k (xG E) N) x :=
    ⟨q.map f, hq.map f, by rw [eval₂_map]; exact hqx⟩
  haveI : Algebra.IsIntegral (A₀ k (xG E)) (coordRing k (xG E) N) :=
    ⟨fun b => integralClosure.isIntegral (R := A₀ k (xG E)) (A := N) b⟩
  exact isIntegral_trans (R := A₀ k (xG E)) (A := coordRing k (xG E) N) (B := N) x hx'

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Inertia fixes the division point `Q_ℓ`** (characteristic `0`): an automorphism of `N` over
`k(x)` fixing `y` and lying in the inertia group of a nonzero prime `u` of the normalization of
the `x`-line in `N` fixes the coordinates of `Q_ℓ`, when these lie in `N`. -/
theorem inertia_fixes_Q (ℓ : ℕ) (hN : QFieldX E ℓ ≤ N) (hyN : yG E ∈ N)
    (u : Ideal (coordRing k (xG E) N)) (hu : u.IsPrime) (hu0 : u ≠ ⊥)
    (τ : N ≃ₐ[xLine E] N)
    (hτ : ∀ b : coordRing k (xG E) N, ∃ c ∈ u, ((c : N) : Ω E) = τ (b : N) - (b : N))
    (hτy : τ ⟨yG E, hyN⟩ = ⟨yG E, hyN⟩) :
    ∀ a ∈ QFieldX E ℓ, ∀ ha : a ∈ N, τ ⟨a, ha⟩ = ⟨a, ha⟩ := by
  have hc := compatible_divSys_of_charZero E
  have hnQ := effLevel_smul_Qpt E hc ℓ
  -- the division point is affine, with coordinates in `N`
  obtain ⟨x, y, h, hQ⟩ : ∃ (x y : Ω E) (h : (E⁄(Ω E)).toAffine.Nonsingular x y),
      Qpt E ℓ = Affine.Point.some x y h := by
    rcases hQ : Qpt E ℓ with _ | ⟨x, y, h⟩
    · rw [hQ] at hnQ
      exact absurd hnQ.symm (by
        change genericPoint E ≠ (_ • 0 : Pt E)
        rw [nsmul_zero]; exact Affine.Point.some_ne_zero _)
    · exact ⟨x, y, h, rfl⟩
  have hxQ : x ∈ QFieldX E ℓ := IntermediateField.subset_adjoin _ _ (by simp [hQ, ptX])
  have hyQ : y ∈ QFieldX E ℓ := IntermediateField.subset_adjoin _ _ (by simp [hQ, ptY])
  have hxN : xG E ∈ N := N.algebraMap_mem ⟨xG E, xG_mem_xLine E⟩
  let ι : N →ₐ[k] Ω E := (N.val).restrictScalars k
  have hι : Function.Injective ι := Subtype.val_injective
  -- points over `N`
  have hQN : (E⁄N).toAffine.Nonsingular (⟨x, hN hxQ⟩ : N) ⟨y, hN hyQ⟩ :=
    (Affine.baseChange_nonsingular (W := E) (f := ι) hι _ _).mp h
  have hGN : (E⁄N).toAffine.Nonsingular (⟨xG E, hxN⟩ : N) ⟨yG E, hyN⟩ :=
    (Affine.baseChange_nonsingular (W := E) (f := ι) hι _ _).mp (nonsingular_generic E)
  have hmapQ : Affine.Point.map (W' := E) (S := k) ι (Affine.Point.some _ _ hQN) = Qpt E ℓ := by
    rw [hQ]; rfl
  have hmapG : Affine.Point.map (W' := E) (S := k) ι (Affine.Point.some _ _ hGN) =
      genericPoint E := rfl
  have hnQN : effLevel ℓ • Affine.Point.some _ _ hQN = Affine.Point.some _ _ hGN := by
    apply Affine.Point.map_injective (W' := E) (S := k) ι
    rw [map_nsmul, hmapQ, hmapG, hnQ]
  -- the valuation subring at `u`, and the integrally closed subring `coordRing N`
  let W := valSub E u hu hu0
  let σ : N →ₐ[k] N := τ.toAlgHom.restrictScalars k
  have hRW : (coordRingK E N).toSubring ≤ W.toSubring := fun b hb =>
    coordRing_mem_valSub E u hu hu0 ⟨b, hb⟩
  have hσ : ∀ a ∈ coordRingK E N, W.valuation (σ a - a) < 1 := by
    intro a ha
    obtain ⟨c, hcu, hc⟩ := hτ ⟨a, ha⟩
    have : σ a - a = (c : N) := by
      apply Subtype.ext
      rw [hc]; rfl
    rw [this]
    exact valSub_lt_one E u hu hu0 c hcu
  have hxgR : (⟨xG E, hxN⟩ : N) ∈ coordRingK E N := xG_mem_coordRing E
  have hσG : Affine.Point.map (W' := E) (S := k) σ (Affine.Point.some _ _ hGN) =
      Affine.Point.some _ _ hGN := by
    have h1 : σ ⟨xG E, hxN⟩ = ⟨xG E, hxN⟩ := τ.commutes ⟨xG E, xG_mem_xLine E⟩
    have h2 : σ ⟨yG E, hyN⟩ = ⟨yG E, hyN⟩ := hτy
    exact some_ext h1 h2
  have key := inertia_fixes_of_nsmul E N W (coordRingK E N) (coordRingK_isIntegrallyClosed E)
    hRW σ hσ (effLevel ℓ) (effLevel_pos ℓ) hGN hxgR hσG _ hnQN
  have hx' : σ ⟨x, hN hxQ⟩ = ⟨x, hN hxQ⟩ := (Affine.Point.some.inj key).1
  have hy' : σ ⟨y, hN hyQ⟩ = ⟨y, hN hyQ⟩ := (Affine.Point.some.inj key).2
  -- `τ` fixes `k(x)` and the coordinates of `Q_ℓ`, hence `QFieldX`
  intro a ha haN
  let F' : IntermediateField (xLine E) (Ω E) :=
    { carrier := {b | ∃ hb : b ∈ N, τ ⟨b, hb⟩ = ⟨b, hb⟩}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨mul_mem ha hb, by
          have := congrArg₂ (· * ·) ha' hb'
          simpa [← map_mul] using this⟩
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨add_mem ha hb, by
          have := congrArg₂ (· + ·) ha' hb'
          simpa [← map_add] using this⟩
      algebraMap_mem' := fun c => ⟨N.algebraMap_mem c, τ.commutes c⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have e : (⟨a⁻¹, inv_mem ha⟩ : N) = (⟨a, ha⟩ : N)⁻¹ := rfl
        rw [e, map_inv₀, ha'] }
  have hle : QFieldX E ℓ ≤ F' := by
    rw [QFieldX, IntermediateField.adjoin_le_iff]
    intro b hb
    rcases hb with rfl | rfl
    · rw [hQ]; exact ⟨hN hxQ, hx'⟩
    · rw [hQ]; exact ⟨hN hyQ, hy'⟩
  obtain ⟨_, h⟩ := hle ha
  exact h

end InertiaQ

/-! ### `X_M → X_{M'}` is unramified -/

/-- A finite Galois extension of `k(x)` containing `k(x, Q_ℓ)`. -/
def galClosure (ℓ : ℕ) : IntermediateField (xLine E) (Ω E) :=
  IntermediateField.normalClosure (xLine E) (QFieldX E ℓ) (Ω E)

instance (ℓ : ℕ) : FiniteDimensional (xLine E) (galClosure E ℓ) := by
  unfold galClosure; infer_instance

instance (ℓ : ℕ) : IsGalois (xLine E) (galClosure E ℓ) := by
  unfold galClosure; infer_instance

lemma QFieldX_le_galClosure (ℓ : ℕ) : QFieldX E ℓ ≤ galClosure E ℓ :=
  IntermediateField.le_normalClosure (QFieldX E ℓ)

lemma geomField_le_galClosure (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    geomField E ℓ M ≤ galClosure E ℓ :=
  (geomField_le_QFieldX E ℓ M).trans (QFieldX_le_galClosure E ℓ)

lemma fullSub_le_of_cover {n ℓ ℓ' : ℕ} (hn : 0 < n) (hℓ : n * ℓ' = ℓ)
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M') {pm pm' : Bool}
    (hpm : pm = true → pm' = true) : fullSub E ℓ M pm ≤ fullSub E ℓ' M' pm' :=
  fun _ hσ => Hgp_le E (compatible_divSys_of_charZero E) hn hℓ hM hpm hσ

lemma coarseField_le_of_cover {n ℓ ℓ' : ℕ} (hn : 0 < n) (hℓ : n * ℓ' = ℓ)
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M') {pm pm' : Bool}
    (hpm : pm = true → pm' = true) : coarseField E ℓ' M' pm' ≤ coarseField E ℓ M pm :=
  IntermediateField.fixedField_antitone (fullSub_le_of_cover E hn hℓ hM hpm)

lemma maximal_ne_bot {L : IntermediateField (xLine E) (Ω E)} [FiniteDimensional (xLine E) L]
    (u : Ideal (coordRing k (xG E) L)) (hu : u.IsMaximal) : u ≠ ⊥ := by
  intro h
  subst h
  exact not_isField_ring (xG E) (transcendental_xG E) L
    (Ring.isField_iff_maximal_bot.mpr hu)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **`X_M → X_{M'}` is unramified**: `e(w | v) = 1` for the covers of model orbicurves without
`±`. -/
theorem ramificationIdx_geom_eq_one {n ℓ ℓ' : ℕ} (hn : 0 < n) (hℓ : n * ℓ' = ℓ)
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M')
    (w : Ideal (coordRing k (xG E) (geomField E ℓ M))) (hw : w.IsMaximal) :
    (letI := algRing (xG E) (coarseField_le_of_cover E hn hℓ hM (pm := false) (pm' := false)
      (by simp)); w.ramificationIdx (coordRing k (xG E) (geomField E ℓ' M'))) = 1 := by
  have hFL := coarseField_le_of_cover E hn hℓ hM (pm := false) (pm' := false) (by simp)
  have hLN := geomField_le_galClosure E ℓ M
  set N := galClosure E ℓ
  -- a maximal ideal `u` of `coordRing N` over `w`
  obtain ⟨u, hu, hul⟩ : ∃ u : Ideal (coordRing k (xG E) N), u.IsMaximal ∧
      u.comap (ringMap (xG E) hLN) = w := by
    letI := algRing (xG E) hLN
    haveI : Algebra.IsIntegral (coordRing k (xG E) (geomField E ℓ M)) (coordRing k (xG E) N) :=
      ⟨ringMap_isIntegral _ hLN⟩
    haveI : FaithfulSMul (coordRing k (xG E) (geomField E ℓ M)) (coordRing k (xG E) N) := by
      rw [faithfulSMul_iff_algebraMap_injective]; exact ringMap_injective _ hLN
    obtain ⟨u, hu, hul⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := coordRing k (xG E) N) w
    exact ⟨u, hu, hul.over.symm⟩
  subst hul
  refine (ramificationIdx_eq_one_iff (xG E) (transcendental_xG E) hFL hLN u).mpr ?_
  rintro τ ⟨hτI, hτF⟩ x hx
  have hyN : yG E ∈ N := hLN (hFL (xG_yG_mem_geomField E ℓ' M').2)
  have hτy : τ ⟨yG E, hyN⟩ = ⟨yG E, hyN⟩ := hτF ⟨yG E, hyN⟩ (xG_yG_mem_geomField E ℓ' M').2
  have key := inertia_fixes_Q E ℓ (QFieldX_le_galClosure E ℓ) hyN u hu.isPrime
    (maximal_ne_bot E u hu) τ (fun b => ⟨τ • b - b, hτI b, rfl⟩) hτy
  exact key x (geomField_le_QFieldX E ℓ M hx) x.2

end

end Iut.Anabelian.Genuine
