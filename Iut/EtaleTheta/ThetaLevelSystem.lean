/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaLevelKummer
import Iut.EtaleTheta.ThetaQuotIsogeny

/-!
# The étale theta classes form a projective system in `N` (MR14, run 5)

Let `q` be a Tate parameter over a complete nonarchimedean field `K` of characteristic `0` with
`‖2‖ = 1`, `s² = q`, `E = E_q`, `Ω = K(Ē)^alg`. For even `N` the level `Ÿ'_N = E_{s^N} ∖ C_N` of
[EtTh], §1 is realised (`ThetaLevelKummer.lean`, route R-alg of `MR14-plan.md`) as an intermediate
field `L'_N = K(τ)(φ_{2N}(x_Q∘ψ), φ_{2N}(y_Q∘ψ)) ⊆ Ω`, `φ_{2N} = mulByNEmb E (2N)`, carrying the
unit `η_N` (the theta level function `F_N`, `F_N(u) = f_N(u^N)`). This file shows that these data
form a **projective system** in `N`: for `N' = N·M` with `M` even,

* `L'_N ≤ L'_{N'}` (`levelField_mono`, from the transition `Ÿ'_{N'} → Ÿ'_N`, `u ↦ u^M`, i.e.
  `[M]^*` on `K(E)`, and the compatible choice of the embeddings `mulByNEmb`,
  `mulByNEmb_comp_pb_mul`), so `Π_{Ÿ'_{N'}} ≤ Π_{Ÿ'_N}`;
* `η_{N'} = η_N · γ^N` for a unit `γ` of `Ÿ'_{N'}` (from `thetaLevel_mul`:
  `f_{NM} = f_N · (f^{(q^N)}_M)^N`; `γ` has values `f^{(q^N)}_M(u^{NM})`);
* hence for `n ∣ N` the restriction of `κ_n(η_N) ∈ H¹(Π_{Ÿ'_N}, μ_n)` to `Π_{Ÿ'_{N'}}` is
  `κ_n(η_{N'})` (`resPi_kummerMap`, the naturality of the Kummer map of `continuous-kummer-theory`
  under a change of level).

The main statement is `exists_etaleThetaSystem`: a family `(L'_j, η_j)` indexed by `j`, with
`N_j = 2(j+1)`, satisfying the étale and point statements of `exists_etaleThetaClass` at every level
and the transition statement above.

Ingredients on the Tate side: `hasTateValue_pb` (values of `[m]^*g` at `u` are values of `g` at
`u^m`), `exists_poly_quotX/Y` (`ThetaQuotIsogeny.lean`: `X_Q, Y_Q` are rational in
`X_{Q^M}, Y_{Q^M}`), `thetaLevel_eq_div` for the parameter `q^N` (the factor `γ`).
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta

/-! ### Naturality of the Kummer map of `continuous-kummer-theory` under a change of level -/

section KummerNat

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {D D' : GaloisData k t}

/-- The map `Π_{U'} → Π_U` of a change of level `H' ≤ H`. -/
def piRes (hH : D'.H ≤ D.H) (hS : D'.S ⊆ D.S) : Pi D' →* Pi D :=
  QuotientGroup.map _ _ (Subgroup.inclusion hH) (GaloisPi1.kernel_le_comap hH hS)

theorem continuous_piRes (hH : D'.H ≤ D.H) (hS : D'.S ⊆ D.S) : Continuous (piRes hH hS) := by
  change Continuous (QuotientGroup.map (GaloisPi1.kernel D'.H D'.S) (GaloisPi1.kernel D.H D.S)
    (Subgroup.inclusion hH) (GaloisPi1.kernel_le_comap hH hS))
  rw [(QuotientGroup.isQuotientMap_mk (GaloisPi1.kernel D'.H D'.S)).continuous_iff]
  exact QuotientGroup.continuous_mk.comp (continuous_inclusion hH)

/-- **Restriction** `H¹(Π_U, μ_n) → H¹(Π_{U'}, μ_n)` along a change of level. -/
def resPi [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] (hH : D'.H ≤ D.H)
    (hS : D'.S ⊆ D.S) (n : ℕ) [NeZero n] :
    ContH1 (Pi D) (Mu n Ω) →* ContH1 (Pi D') (Mu n Ω) :=
  ContH1.map (piRes hH hS) (continuous_piRes hH hS) (MonoidHom.id _) continuous_id
    (fun x _ => by induction x using QuotientGroup.induction_on with | H h => rfl)

theorem pow_eq_one_of_mu {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
    [MulDistribMulAction G (Mu n Ω)] (x : ContH1 G (Mu n Ω)) : x ^ n = 1 := by
  induction x using ContH1.induction_on with
  | h c =>
    rw [← map_pow, ContH1.mk_eq_one_iff]
    refine ⟨1, fun g => ?_⟩
    rw [smul_one, div_one, SubgroupClass.coe_pow, Pi.pow_apply]
    exact Mu.ext (by rw [map_one, map_pow, Mu.val_pow_n])

/-- **Naturality of the Kummer map**: for a change of level `H' ≤ H` and a unit `u` of `U` whose
image in `Ω` is the unit `u'` of `U'`, the restriction of `κ_U(u)` is `κ_{U'}(u')`. -/
theorem resPi_kummerMap [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] (hH : D'.H ≤ D.H)
    (hS : D'.S ⊆ D.S) (n : ℕ) [NeZero n] (v : units D) (v' : units D')
    (h : (((v : (F D)ˣ) : F D) : Ω) = (((v' : (F D')ˣ) : F D') : Ω)) :
    resPi hH hS n (kummerMap D n v) = kummerMap D' n v' := by
  apply ContH1.inflation_injective (N := GaloisPi1.kernel D'.H D'.S) (fun _ _ => rfl)
  change inflMu D' n _ = inflMu D' n _
  have step : ∀ x : ContH1 (Pi D) (Mu n Ω), inflMu D' n (resPi hH hS n x) =
      ContH1.map (Subgroup.inclusion hH) (continuous_inclusion hH) (MonoidHom.id _)
        continuous_id (fun _ _ => rfl) (inflMu D n x) := by
    intro x
    induction x using ContH1.induction_on with
    | h c => rfl
  rw [step, inflation_kummerMap, inflation_kummerMap]
  set α := kummerRoot n (F D) Ω (v : (F D)ˣ)
  have hα : α ^ n = Units.map (algebraMap (F D) Ω : F D →* Ω) (v : (F D)ˣ) :=
    kummerRoot_pow n (F D) Ω _
  have hα' : α ^ n = Units.map (algebraMap (F D') Ω : F D' →* Ω) (v' : (F D')ˣ) := by
    rw [hα]; ext; exact h
  rw [kummer_eq _ α hα, kummer_eq _ α hα']
  rfl

end KummerNat

/-! ### Tate side: values of `[m]^*` and the transition of the level data -/

open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K} {h12 : (12 : K) ≠ 0}

/-- **Values of `[m]^*` on `K(E_q)`**: if `ψ_m(u) ≠ 0`, the value of `[m]^* g` at `u` is the
value of `g` at `u^m`. -/
theorem hasTateValue_pb (h2 : ‖(2 : K)‖ = 1) (m : ℕ) [NeZero m] [t.tateCurve.IsElliptic]
    {u : Kˣ} (hu : OffOrbit t u) (hψ : evalTate t h12 hu (psiN t.tateCurve m) ≠ 0) :
    ∃ hum : OffOrbit t (u ^ m), ∀ (g : TateField t) (v : K), HasTateValue t h12 g hum v →
      HasTateValue t h12 (pb t.tateCurve m g) hu v := by
  obtain ⟨hum, hval⟩ := hasTateValue_mulByNHom (h12 := h12) m h2 hu hψ
  refine ⟨hum, fun g v ⟨n, d, hg, hd, hv⟩ => ?_⟩
  have hd0 : algebraMap (TateRing t) (TateField t) d ≠ 0 :=
    algebraMap_ne_zero (ne_zero_of_evalTate_ne_zero hd)
  have e : pb t.tateCurve m g = algebraMap _ (TateField t) (mulByNHom t.tateCurve m n) /
      algebraMap _ (TateField t) (mulByNHom t.tateCurve m d) := by
    rw [algebraMap_mulByNHom_eq_pb, algebraMap_mulByNHom_eq_pb, ← hg, map_mul,
      mul_div_assoc, div_self ((_root_.map_ne_zero _).mpr hd0), mul_one]
  rw [e]
  refine ((hval n).div (hval d) hd).congr ?_
  rw [← hv]
  field_simp

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
/-- `P₁(x) + y·Q₁(x)` over `P₂(x) + y·Q₂(x)` in `K(x, y)`. -/
abbrev ratXY {L : Type*} [Field L] [Algebra K L] (x y : L) (P₁ Q₁ P₂ Q₂ : K[X]) : L :=
  (Polynomial.aeval x P₁ + y * Polynomial.aeval x Q₁) /
    (Polynomial.aeval x P₂ + y * Polynomial.aeval x Q₂)

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem ratXY_mem {L : Type*} [Field L] [Algebra K L] (x y : L) (P₁ Q₁ P₂ Q₂ : K[X]) :
    ratXY x y P₁ Q₁ P₂ Q₂ ∈ IntermediateField.adjoin K ({x, y} : Set L) := by
  have hx : x ∈ IntermediateField.adjoin K ({x, y} : Set L) :=
    IntermediateField.subset_adjoin _ _ (by simp)
  have hy : y ∈ IntermediateField.adjoin K ({x, y} : Set L) :=
    IntermediateField.subset_adjoin _ _ (by simp)
  exact div_mem (add_mem (aeval_mem_adjoin hx P₁) (mul_mem hy (aeval_mem_adjoin hx Q₁)))
    (add_mem (aeval_mem_adjoin hx P₂) (mul_mem hy (aeval_mem_adjoin hx Q₂)))

omit [CharZero K] in
theorem hasTateValue_ratXY {gX gY : TateField t} {u : Kˣ} {hu : OffOrbit t u} {x y : K}
    (hx : HasTateValue t h12 gX hu x) (hy : HasTateValue t h12 gY hu y) (P₁ Q₁ P₂ Q₂ : K[X])
    (hden : P₂.eval x + y * Q₂.eval x ≠ 0) :
    HasTateValue t h12 (ratXY gX gY P₁ Q₁ P₂ Q₂) hu
      ((P₁.eval x + y * Q₁.eval x) / (P₂.eval x + y * Q₂.eval x)) :=
  ((hx.aeval P₁).add (hy.mul (hx.aeval Q₁))).div ((hx.aeval P₂).add (hy.mul (hx.aeval Q₂))) hden

section Level

variable (h2 : ‖(2 : K)‖ = 1) (h12) {s : Kˣ} (hs : s ^ 2 = t.q)

include hs in
omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem norm_sqrt_lt_one : ‖(s : K)‖ < 1 := by
  have h : ‖(s : K)‖ ^ 2 < 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, hs]; exact t.norm_lt_one
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

/-- The Tate parameter `Q = s^N` of the level `Ÿ'_N` (`s² = q`, `N ≥ 1`). -/
def sqrtPow (N : ℕ) (hN : 0 < N) : TateParameter K where
  q := s ^ N
  norm_lt_one := by
    rw [Units.val_pow_eq_pow_val, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (norm_sqrt_lt_one hs) hN.ne'

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
@[simp] theorem sqrtPow_q (N : ℕ) (hN : 0 < N) : (sqrtPow hs N hN).q = s ^ N := rfl

include h2 hs in
/-- **The data of the level `Ÿ'_N` inside `K(E_q)`** (`N` even): `x_Q∘ψ, y_Q∘ψ` and `F_N` with
their values at all `u` with `u^{2N} ∉ q^ℤ`, `F_N ∈ K(x_Q∘ψ, y_Q∘ψ) ⊇ [2N]^*K[E]`, and `F_N^{±1}`
in `K[E][1/ψ_{2N}]`. -/
theorem exists_levelData {N : ℕ} (hN : 0 < N) (hev : Even N) :
    haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
    haveI : NeZero (2 * N) := ⟨by omega⟩
    ∃ (gX gY F : TateField t),
      F ∈ IntermediateField.adjoin K ({gX, gY} : Set (TateField t)) ∧
      (∀ a : TateRing t, algebraMap _ (TateField t) (mulByNHom t.tateCurve (2 * N) a) ∈
        IntermediateField.adjoin K ({gX, gY} : Set (TateField t))) ∧
      (∃ b b' : coverRingN t.tateCurve (2 * N),
        algebraMap _ (TateField t) b = F ∧ algebraMap _ (TateField t) b' = F⁻¹) ∧
      ∀ (u : Kˣ) (hu : OffOrbit t u), OffOrbit t (u ^ (2 * N)) →
        HasTateValue t h12 gX hu ((sqrtPow hs N hN).X (u ^ N)) ∧
        HasTateValue t h12 gY hu ((sqrtPow hs N hN).Y (u ^ N)) ∧
        HasTateValue t h12 F hu (thetaLevel t N hN (u ^ N)) := by
  haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
  haveI : NeZero (2 * N) := ⟨by omega⟩
  set T := sqrtPow hs N hN
  have hT : T.q = s ^ N := rfl
  obtain ⟨gX, gY, F, D, -, hF, hmul, hspec⟩ :=
    exists_levelField_mulByN (h12 := h12) h2 hs hN T hT hev
  obtain ⟨-, -, F₂, -, -, ⟨b, b', hb, hb'⟩, hpt⟩ :=
    exists_thetaLevel_unit h2 h12 hs hN T hT hev
  have key : ∀ (u : Kˣ), OffOrbit t (u ^ (2 * N)) →
      T.theta (-(u ^ N)) ≠ 0 ∧ etaleTheta (tatePow t N hN) (u ^ N) ≠ 0 := fun u hum =>
    ⟨theta_neg_ne_zero T (offOrbit_sqrt_pow hs T hT hum),
      etaleTheta_pow_ne_zero (offOrbit_tatePow hN hum)⟩
  have hFF : F₂ = F := by
    refine eq_of_hasTateValue (h12 := h12) (psiN_ne_zero_of_neZero t.tateCurve (2 * N))
      (G := fun u => thetaLevel t N hN (u ^ N)) (fun u hu hψ => (hpt u hu hψ).2.2.2)
      (fun u hu hψ => ?_)
    obtain ⟨k1, k2⟩ := key u (hpt u hu hψ).1
    exact ((hspec u hu).2 k1).2.2 k2
  subst hFF
  refine ⟨gX, gY, F₂, hF, hmul, ⟨b, b', hb, hb'⟩, fun u hu hum => ?_⟩
  obtain ⟨k1, k2⟩ := key u hum
  obtain ⟨vX, vY, vF⟩ := (hspec u hu).2 k1
  exact ⟨vX, vY, vF k2⟩

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem pow_pow_eq (u : Kˣ) (N M : ℕ) : (u ^ M) ^ N = u ^ (N * M) := by
  rw [← pow_mul, mul_comm]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem pow_pow_two_eq (u : Kˣ) (N M : ℕ) : (u ^ M) ^ (2 * N) = u ^ (2 * (N * M)) := by
  rw [← pow_mul]; congr 1; ring

include h2 hs in
/-- **The transition `Ÿ'_{NM} → Ÿ'_N` on function fields** (`M` even): `[M]^*` maps
`K(x_Q∘ψ_N, y_Q∘ψ_N)` into `K(x_{Q'}∘ψ_{NM}, y_{Q'}∘ψ_{NM})`, and
`F_{NM} = [M]^*F_N · G^N` with `G ∈ K(x_{Q'}∘ψ_{NM}, y_{Q'}∘ψ_{NM})` (values
`f^{(q^N)}_M(u^{NM})`, `thetaLevel_mul`). -/
theorem levelData_transition [t.tateCurve.IsElliptic] {N M N' : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hN' : 0 < N') (hNM : N' = N * M) (hevM : Even M) [NeZero M] [NeZero (2 * N')]
    {gX gY F gX' gY' F' : TateField t}
    (hval : ∀ (u : Kˣ) (hu : OffOrbit t u), OffOrbit t (u ^ (2 * N)) →
      HasTateValue t h12 gX hu ((sqrtPow hs N hN).X (u ^ N)) ∧
      HasTateValue t h12 gY hu ((sqrtPow hs N hN).Y (u ^ N)) ∧
      HasTateValue t h12 F hu (thetaLevel t N hN (u ^ N)))
    (hval' : ∀ (u : Kˣ) (hu : OffOrbit t u), OffOrbit t (u ^ (2 * N')) →
      HasTateValue t h12 gX' hu ((sqrtPow hs N' hN').X (u ^ N')) ∧
      HasTateValue t h12 gY' hu ((sqrtPow hs N' hN').Y (u ^ N')) ∧
      HasTateValue t h12 F' hu (thetaLevel t N' hN' (u ^ N'))) :
    pb t.tateCurve M gX ∈ IntermediateField.adjoin K ({gX', gY'} : Set (TateField t)) ∧
    pb t.tateCurve M gY ∈ IntermediateField.adjoin K ({gX', gY'} : Set (TateField t)) ∧
    ∃ G ∈ IntermediateField.adjoin K ({gX', gY'} : Set (TateField t)),
      F' = pb t.tateCurve M F * G ^ N := by
  subst hNM
  set T := sqrtPow hs N hN
  set T' := sqrtPow hs (N * M) hN'
  have hT : T.q = s ^ N := rfl
  have hT' : T'.q = s ^ (N * M) := rfl
  have hTT : T'.q = T.q ^ M := by rw [hT, hT', pow_mul]
  set D₀ : TateRing t := psiN t.tateCurve (2 * (N * M)) * psiN t.tateCurve M
  have hD₀ : D₀ ≠ 0 :=
    mul_ne_zero (psiN_ne_zero_of_neZero _ _) (psiN_ne_zero_of_neZero _ _)
  -- the common facts at a good point
  have good : ∀ (u : Kˣ) (hu : OffOrbit t u), evalTate t h12 hu D₀ ≠ 0 →
      ∃ hum : OffOrbit t (u ^ M), OffOrbit t (u ^ (2 * (N * M))) ∧
        (∀ (g : TateField t) (v : K), HasTateValue t h12 g hum v →
          HasTateValue t h12 (pb t.tateCurve M g) hu v) ∧
        OffOrbit t ((u ^ M) ^ (2 * N)) ∧ OffOrbit T' (u ^ (N * M)) ∧
        T.theta (-(u ^ (N * M))) ≠ 0 := by
    intro u hu h0
    rw [map_mul] at h0
    obtain ⟨hum2, -⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * (N * M)) h2 hu
      (left_ne_zero_of_mul h0)
    obtain ⟨hum, hpb⟩ := hasTateValue_pb (h12 := h12) h2 M hu (right_ne_zero_of_mul h0)
    have hum2' : OffOrbit t ((u ^ M) ^ (2 * N)) := by rwa [pow_pow_two_eq]
    have hθ := theta_neg_ne_zero T (offOrbit_sqrt_pow hs T hT hum2')
    rw [pow_pow_eq] at hθ
    exact ⟨hum, hum2, hpb, hum2', offOrbit_sqrt_pow hs T' hT' hum2, hθ⟩
  obtain ⟨A₁, B₁, A₂, B₂, hX⟩ := exists_poly_quotX hM hTT h12
  obtain ⟨C₁, E₁, C₂, E₂, hY⟩ := exists_poly_quotY hM hTT h12
  -- the transition of the coordinates
  have coord : ∀ (g : TateField t) (P₁ Q₁ P₂ Q₂ : K[X]) (W : TateParameter K → Kˣ → K),
      (∀ (u : Kˣ) (hu : OffOrbit t u), OffOrbit t (u ^ (2 * N)) →
        HasTateValue t h12 g hu (W T (u ^ N))) →
      (∀ v : Kˣ, OffOrbit T' v →
        (P₂.eval (T'.X v) + T'.Y v * Q₂.eval (T'.X v) ≠ 0 ↔ T.theta (-v) ≠ 0) ∧
        (T.theta (-v) ≠ 0 → W T v = (P₁.eval (T'.X v) + T'.Y v * Q₁.eval (T'.X v)) /
          (P₂.eval (T'.X v) + T'.Y v * Q₂.eval (T'.X v)))) →
      pb t.tateCurve M g = ratXY gX' gY' P₁ Q₁ P₂ Q₂ := by
    intro g P₁ Q₁ P₂ Q₂ W hg hW
    refine eq_of_hasTateValue (h12 := h12) hD₀ (G := fun u => W T (u ^ (N * M)))
      (fun u hu h0 => ?_) (fun u hu h0 => ?_)
    · obtain ⟨hum, -, hpb, hum2', -, -⟩ := good u hu h0
      have := hpb _ _ (hg _ hum hum2')
      rwa [pow_pow_eq] at this
    · obtain ⟨-, hum2, -, -, hv, hθ⟩ := good u hu h0
      obtain ⟨vX, vY, -⟩ := hval' u hu hum2
      obtain ⟨hden, he⟩ := hW _ hv
      exact (hasTateValue_ratXY vX vY P₁ Q₁ P₂ Q₂ (hden.mpr hθ)).congr (he hθ).symm
  have eX := coord gX A₁ B₁ A₂ B₂ (fun T v => T.X v) (fun u hu h => (hval u hu h).1) hX
  have eY := coord gY C₁ E₁ C₂ E₂ (fun T v => T.Y v) (fun u hu h => (hval u hu h).2.1) hY
  refine ⟨eX ▸ ratXY_mem _ _ _ _ _ _, eY ▸ ratXY_mem _ _ _ _ _ _, ?_⟩
  -- the factor `G`
  have hsN : (s ^ N) ^ 2 = (tatePow t N hN).q := by
    rw [tatePow_q, ← hs, ← pow_mul, ← pow_mul, mul_comm]
  obtain ⟨P₁, Q₁, P₂, Q₂, hG⟩ :=
    thetaLevel_eq_div (tatePow t N hN) h12 hsN M hM hevM T' (by rw [hT', pow_mul])
  refine ⟨ratXY gX' gY' P₁ Q₁ P₂ Q₂, ratXY_mem _ _ _ _ _ _, ?_⟩
  refine eq_of_hasTateValue (h12 := h12) hD₀
    (G := fun u => thetaLevel t (N * M) hN' (u ^ (N * M)))
    (fun u hu h0 => (hval' u hu (good u hu h0).2.1).2.2) (fun u hu h0 => ?_)
  obtain ⟨hum, hum2, hpb, hum2', hv, -⟩ := good u hu h0
  obtain ⟨vX, vY, -⟩ := hval' u hu hum2
  obtain ⟨he, hz⟩ := hG _ hv
  have hU : etaleTheta t (u ^ (N * M)) ≠ 0 := etaleTheta_pow_ne_zero hum2
  have hΘ : etaleTheta (tatePow (tatePow t N hN) M hM) (u ^ (N * M)) ≠ 0 := by
    rw [tatePow_tatePow]
    exact etaleTheta_pow_ne_zero (offOrbit_tatePow _ hum2)
  have hden : P₂.eval (T'.X (u ^ (N * M))) + T'.Y (u ^ (N * M)) * Q₂.eval (T'.X (u ^ (N * M)))
      ≠ 0 := fun h => hΘ (hz.mp h)
  have vG := (hasTateValue_ratXY vX vY P₁ Q₁ P₂ Q₂ hden).congr he.symm
  have vF := hpb _ _ ((hval _ hum hum2').2.2)
  rw [pow_pow_eq] at vF
  exact (vF.mul (vG.pow N)).congr (thetaLevel_mul t N hN M hM hU).symm


omit [CompleteSpace K] [IsUltrametricDist K] in
/-- `mulByNEmb (m') ∘ [r]^* = mulByNEmb m` for `r·m = m'`. -/
theorem mulByNEmb_comp_pb_eq [t.tateCurve.IsElliptic] {m r m' : ℕ} [NeZero m] [NeZero r]
    [NeZero m'] (h : r * m = m') :
    (mulByNEmb t.tateCurve m').comp (pb t.tateCurve r) = mulByNEmb t.tateCurve m := by
  subst h; exact mulByNEmb_comp_pb_mul t.tateCurve m r

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **The levels are nested**: if `[r]^*` maps the generators `S` of the level in the source of
`[m]` into `K(S')`, then `K(τ)(φ_m(S)) ≤ K(τ)(φ_{m'}(S'))` for `m' = r·m`. -/
theorem levelField_mono [t.tateCurve.IsElliptic] {m r m' : ℕ} [NeZero m] [NeZero r] [NeZero m']
    (h : r * m = m') {S S' : Set (TateField t)}
    (hS : ∀ g ∈ S, pb t.tateCurve r g ∈ IntermediateField.adjoin K S') :
    IntermediateField.adjoin (K₀ K (coordT (xN t.tateCurve))) (mulByNEmb t.tateCurve m '' S) ≤
      IntermediateField.adjoin (K₀ K (coordT (xN t.tateCurve)))
        (mulByNEmb t.tateCurve m' '' S') := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨g, hg, rfl⟩
  rw [← mulByNEmb_comp_pb_eq h, AlgHom.comp_apply]
  exact mem_adjoin_image _ _ (hS g hg)

end Level

end Iut.EtaleTheta
