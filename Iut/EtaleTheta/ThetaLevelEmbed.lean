/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaCuspTame
import EllipticCurves.FunctionField.MulByNXCoordRatFunc
import EllipticCurves.FunctionField.GenericDoubling

/-!
# The embeddings of the level `Ÿ'_N` over `X`: they are the `2N` translations (MR14, run 15)

Let `s² = q`, `N` even, `Q = s^N`, and `φ : E_Q → E_q`, `Ü ↦ Ü²`, the isogeny of degree `2N`
whose kernel is `{±s^a}` (`cuspElt`, `cuspPt`). Its `x`-coordinate is the element
`R = (A₁ + yB₁)/(A₂ + yB₂)` of `K(E_Q)` of `exists_poly_isogenyX_deg` (values `X_q(Ü²)`, degree
bounds `deg A_i ≤ 2N`, `deg B_i ≤ 2N - 2` from Tate's theorem in weight `4N`).

**Degree count without degree theory.** `R` is fixed by `[-1]^*` (`negT_R_eq`), so the even parts
`E_i = 2A_i - (a₁X + a₃)B_i` and the odd parts `B_i` satisfy `R·E₂(x) = E₁(x)` and `R·B₂(x) = B₁(x)`
(`even_odd_parts`, using `ψ₂ = 2y + a₁x + a₃ ≠ 0`). Hence for every `K`-algebra map
`ρ : K(E_Q) → L` with `ρ(R) = r` (`r` transcendental), `ρ(x)` is a root of the nonzero polynomial
`E₁ - r·E₂` (or `B₁ - r·B₂`) of degree `≤ 2N`, and `ρ(y)` is one of the two roots of the Weierstrass
equation over `ρ(x)`: **all such `ρ` take their values `(ρ x, ρ y)` in one set of at most `4N`
pairs** (`exists_finset_of_eq`).

**The `4N` translations.** `t_w` (`w = ±s^a`, `transT`) and `t_w ∘ [-1]^*` fix `R`
(`transT_R_eq`, `negT_R_eq`), and they act on the generic point `𝒫` of `E_Q` as `𝒫 + P_w` and
`-(𝒫 + P_w)` (`genPointHom_cand`); these points are pairwise distinct (`2𝒫` is not a point over
`K`, and `cuspPt` is injective), so the `4N` maps `ι ∘ cand i` exhaust the set above:
**`eq_cand_of_eq`**: every `K`-algebra map `ρ : K(E_Q) → L` with `ρ(R) = ι(R)` is `ι ∘ t_w` or
`ι ∘ t_w ∘ [-1]^*` for one of the `2N` kernel points `w`. This is the Galois structure of
`Ÿ'_N / X` used in run 15 (`MR14-plan.md`): the geometric Galois group of the level over `X` acts
through the `2N` rational translations.
-/

open Polynomial

noncomputable section

universe u

namespace Iut.EtaleTheta

open CurvesJacobian.Cusp TateCurvesTheta WeierstrassCurve.Affine
  WeierstrassCurve.Affine.CoordinateRing

/-! ### Generic Weierstrass curves: algebra maps out of `F(W)` and a root count -/

section Generic

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} {L : Type*} [Field L]
  [Algebra F L]

/-- `F`-algebra maps out of `F(W)` are determined by the images of `genX`, `genY`. -/
theorem algHom_ext_genXY {φ ψ : W.FunctionField →ₐ[F] L}
    (hx : φ (genX W) = ψ (genX W)) (hy : φ (genY W) = ψ (genY W)) : φ = ψ := by
  have hcr : (φ : W.FunctionField →+* L).comp (genPsi W)
      = (ψ : W.FunctionField →+* L).comp (genPsi W) := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · have hofC : AdjoinRoot.of W.polynomial (C c) = algebraMap F W.CoordinateRing c := by
        rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq,
          ← Polynomial.C_eq_algebraMap]
      simp only [RingHom.comp_apply, hofC, genPsi, ← IsScalarTower.algebraMap_apply,
        AlgHom.coe_toRingHom, AlgHom.commutes]
    · have hx' : φ (genPsi W (mk W (C X))) = ψ (genPsi W (mk W (C X))) := hx
      simpa only [RingHom.comp_apply, show AdjoinRoot.of W.polynomial X = mk W (C X) from rfl,
        AlgHom.coe_toRingHom] using hx'
    · have hy' : φ (genPsi W (AdjoinRoot.root W.polynomial))
          = ψ (genPsi W (AdjoinRoot.root W.polynomial)) := hy
      simpa only [RingHom.comp_apply, AlgHom.coe_toRingHom] using hy'
  refine AlgHom.coe_ringHom_injective ?_
  refine IsFractionRing.ringHom_ext (A := W.CoordinateRing) (fun a => ?_)
  exact congr($hcr a)

/-- The Weierstrass equation of the generic point, in `F(W)`. -/
theorem gen_equation :
    genY W ^ 2 + algebraMap F _ W.a₁ * genX W * genY W + algebraMap F _ W.a₃ * genY W =
      genX W ^ 3 + algebraMap F _ W.a₂ * genX W ^ 2 + algebraMap F _ W.a₄ * genX W +
        algebraMap F _ W.a₆ := by
  have h := (equation_gen (W := W))
  rw [equation_iff] at h
  simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] using h

/-- `ψ₂ = 2y + a₁x + a₃` is nonzero at the generic point. -/
theorem psiTwo_gen_ne_zero [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    2 * genY W + algebraMap F _ W.a₁ * genX W + algebraMap F _ W.a₃ ≠ 0 := by
  intro h
  apply genY_ne_negY_gen (W := W) h2
  rw [negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
  linear_combination h

/-- The `F`-algebra map `F[X] → F(W)`, `X ↦ genX`, on `mk (C P)`. -/
theorem algebraMap_mk_C (P : F[X]) :
    algebraMap W.CoordinateRing W.FunctionField (mk W (C P)) = aeval (genX W) P := by
  rw [show genX W = algebraMap W.CoordinateRing W.FunctionField
      (algebraMap F[X] W.CoordinateRing Polynomial.X) from rfl,
    Polynomial.aeval_algebraMap_apply, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_X_left_apply]
  rfl

/-- `P(x) + y·Q(x)` in `F(W)`. -/
theorem algebraMap_smul_basis (P Q : F[X]) :
    algebraMap W.CoordinateRing W.FunctionField
        (P • (1 : W.CoordinateRing) + Q • mk W Polynomial.X) =
      aeval (genX W) P + genY W * aeval (genX W) Q := by
  rw [CoordinateRing.smul, CoordinateRing.smul, mul_one, map_add, map_mul, algebraMap_mk_C,
    algebraMap_mk_C, mul_comm]
  rfl

variable [W.IsElliptic]

/-- **Even and odd parts of an `[-1]^*`-invariant quotient.** If `R·(P₂ + yQ₂) = P₁ + yQ₁` with
`[-1]^* R = R`, then `R·E₂(x) = E₁(x)`, `E_i = 2P_i - (a₁X + a₃)Q_i`, and `R·Q₂(x) = Q₁(x)`. -/
theorem even_odd_parts (h2 : (2 : F) ≠ 0) {R : W.FunctionField} (hR : negYAlgEquiv W R = R)
    {P₁ Q₁ P₂ Q₂ : F[X]}
    (hRd : R * (aeval (genX W) P₂ + genY W * aeval (genX W) Q₂) =
      aeval (genX W) P₁ + genY W * aeval (genX W) Q₁) :
    R * aeval (genX W) (2 * P₂ - (C W.a₁ * Polynomial.X + C W.a₃) * Q₂) =
        aeval (genX W) (2 * P₁ - (C W.a₁ * Polynomial.X + C W.a₃) * Q₁) ∧
      R * aeval (genX W) Q₂ = aeval (genX W) Q₁ := by
  have hc : ∀ P : F[X], negYAlgEquiv W (aeval (genX W) P) = aeval (genX W) P := fun P => by
    rw [show negYAlgEquiv W (aeval (genX W) P) =
      (negYAlgEquiv W).toAlgHom (aeval (genX W) P) from rfl, ← Polynomial.aeval_algHom_apply]
    exact congrArg (fun z => aeval z P) (negYAlgEquiv_genX W)
  have hn := congrArg (negYAlgEquiv W) hRd
  simp only [map_mul, map_add, hR, hc, negYAlgEquiv_genY', negY, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₃] at hn
  have hψ := psiTwo_gen_ne_zero (W := W) h2
  refine ⟨?_, ?_⟩
  · simp only [map_sub, map_mul, map_add, aeval_C, aeval_X, map_ofNat]
    linear_combination hRd + hn
  · apply mul_left_cancel₀ hψ
    linear_combination hRd - hn

/-- A polynomial `E₁ - r·E₂` with `E₂ ≠ 0` and `r` transcendental is nonzero. -/
theorem map_sub_C_mul_ne_zero {E₁ E₂ : F[X]} (hE : E₂ ≠ 0) {r : L} (hr : Transcendental F r) :
    E₁.map (algebraMap F L) - C r * E₂.map (algebraMap F L) ≠ 0 := by
  intro h0
  obtain ⟨i, hi⟩ : ∃ i, E₂.coeff i ≠ 0 := by
    by_contra h
    push Not at h
    exact hE (Polynomial.ext fun i => by simp [h i])
  have hc := congrArg (fun p => Polynomial.coeff p i) h0
  simp only [coeff_sub, coeff_C_mul, coeff_map, Polynomial.coeff_zero] at hc
  apply hr
  have : r = algebraMap F L (E₁.coeff i / E₂.coeff i) := by
    rw [map_div₀]
    have hne : algebraMap F L (E₂.coeff i) ≠ 0 := (_root_.map_ne_zero _).mpr hi
    field_simp
    linear_combination -hc
  rw [this]
  exact isAlgebraic_algebraMap (A := L) _

open Classical in
/-- The two `y`-roots over a given `x`, as a finset. -/
def yRoots (W : WeierstrassCurve.Affine F) (x : L) : Finset L :=
  (Polynomial.X ^ 2 + C (algebraMap F L W.a₁ * x + algebraMap F L W.a₃) * Polynomial.X -
    C (x ^ 3 + algebraMap F L W.a₂ * x ^ 2 + algebraMap F L W.a₄ * x +
      algebraMap F L W.a₆)).roots.toFinset

omit [W.IsElliptic] in
theorem card_yRoots_le (x : L) : (yRoots W x : Finset L).card ≤ 2 := by
  classical
  unfold yRoots
  refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' (R := L) _).trans ?_)
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · exact (natDegree_X_pow_le 2)
  · exact (natDegree_C_mul_le _ _).trans (by simp)
  · rw [natDegree_C]; omega

omit [W.IsElliptic] in
theorem mem_yRoots {x y : L}
    (h : y ^ 2 + algebraMap F L W.a₁ * x * y + algebraMap F L W.a₃ * y =
      x ^ 3 + algebraMap F L W.a₂ * x ^ 2 + algebraMap F L W.a₄ * x + algebraMap F L W.a₆) :
    y ∈ yRoots W x := by
  classical
  have hne : (Polynomial.X ^ 2 + C (algebraMap F L W.a₁ * x + algebraMap F L W.a₃) * Polynomial.X -
      C (x ^ 3 + algebraMap F L W.a₂ * x ^ 2 + algebraMap F L W.a₄ * x +
        algebraMap F L W.a₆) : L[X]) ≠ 0 := by
    intro h0
    have := congrArg natDegree h0
    rw [natDegree_zero, natDegree_sub_C, natDegree_add_eq_left_of_natDegree_lt] at this
    · simp at this
    · refine (natDegree_C_mul_le _ _).trans_lt ?_
      simp
  rw [yRoots, Multiset.mem_toFinset, mem_roots hne]
  simp only [IsRoot, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  linear_combination h

/-- **The root count**: if `R·(P₂ + yQ₂) = P₁ + yQ₁` with `[-1]^* R = R`, `P₂ + yQ₂ ≠ 0` and the
degree bounds `deg P_i ≤ m`, `deg Q_i + 1 ≤ m`, then for transcendental `r` all `F`-algebra maps
`ρ : F(W) → L` with `ρ R = r` have `(ρ x, ρ y)` in one finset of at most `2m` pairs. -/
theorem exists_finset_of_eq (h2 : (2 : F) ≠ 0) {R : W.FunctionField}
    (hR : negYAlgEquiv W R = R) {P₁ Q₁ P₂ Q₂ : F[X]}
    (hRd : R * (aeval (genX W) P₂ + genY W * aeval (genX W) Q₂) =
      aeval (genX W) P₁ + genY W * aeval (genX W) Q₁)
    (hd : aeval (genX W) P₂ + genY W * aeval (genX W) Q₂ ≠ 0) {m : ℕ}
    (hP₁ : P₁.natDegree ≤ m) (hP₂ : P₂.natDegree ≤ m) (hQ₁ : Q₁.natDegree + 1 ≤ m)
    (hQ₂ : Q₂.natDegree + 1 ≤ m) {r : L} (hr : Transcendental F r) :
    ∃ S : Finset (L × L), S.card ≤ 2 * m ∧
      ∀ ρ : W.FunctionField →ₐ[F] L, ρ R = r → (ρ (genX W), ρ (genY W)) ∈ S := by
  classical
  obtain ⟨hE, hO⟩ := even_odd_parts h2 hR hRd
  -- the polynomial for `ρ x`
  obtain ⟨E₁, E₂, hE₂, hrel, hdeg₁, hdeg₂⟩ : ∃ E₁ E₂ : F[X], E₂ ≠ 0 ∧
      R * aeval (genX W) E₂ = aeval (genX W) E₁ ∧ E₁.natDegree ≤ m ∧ E₂.natDegree ≤ m := by
    have hlin : ∀ P Q : F[X], P.natDegree ≤ m → Q.natDegree + 1 ≤ m →
        (2 * P - (C W.a₁ * Polynomial.X + C W.a₃) * Q).natDegree ≤ m := by
      intro P Q hP hQ
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_mul_le).trans (by
          have : (2 : F[X]).natDegree = 0 := natDegree_ofNat 2
          omega)
      · refine (natDegree_mul_le).trans ?_
        have h1 : (C W.a₁ * Polynomial.X + C W.a₃).natDegree ≤ 1 :=
          (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (by simp))
            (by simp))
        omega
    by_cases hE₂ : 2 * P₂ - (C W.a₁ * Polynomial.X + C W.a₃) * Q₂ = 0
    · refine ⟨Q₁, Q₂, ?_, hO, by omega, by omega⟩
      rintro rfl
      apply hd
      have hP : P₂ = 0 := by
        have : (2 : F[X]) * P₂ = 0 := by simpa using hE₂
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (by simpa using congrArg (fun p => p.coeff 0) h) h2
        · exact h
      simp [hP]
    · exact ⟨_, _, hE₂, hE, hlin P₁ Q₁ hP₁ hQ₁, hlin P₂ Q₂ hP₂ hQ₂⟩
  set p : L[X] := E₁.map (algebraMap F L) - C r * E₂.map (algebraMap F L) with hp
  have hp0 : p ≠ 0 := map_sub_C_mul_ne_zero hE₂ hr
  have hpdeg : p.natDegree ≤ m := by
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_map_le).trans hdeg₁) ?_)
    exact (natDegree_C_mul_le _ _).trans ((natDegree_map_le).trans hdeg₂)
  refine ⟨p.roots.toFinset.biUnion fun x => (yRoots W x).image fun y => (x, y), ?_, ?_⟩
  · refine (Finset.card_biUnion_le).trans ?_
    calc ∑ x ∈ p.roots.toFinset, ((yRoots W x).image fun y => (x, y)).card
        ≤ ∑ _x ∈ p.roots.toFinset, 2 :=
          Finset.sum_le_sum fun x _ => Finset.card_image_le.trans (card_yRoots_le x)
      _ = 2 * p.roots.toFinset.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * m := by
          have := (Multiset.toFinset_card_le p.roots).trans (card_roots' p)
          omega
  · intro ρ hρ
    refine Finset.mem_biUnion.mpr ⟨ρ (genX W), ?_, Finset.mem_image.mpr ⟨ρ (genY W), ?_, rfl⟩⟩
    · rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot, hp, eval_sub, eval_mul, eval_C,
        eval_map_algebraMap, eval_map_algebraMap, Polynomial.aeval_algHom_apply,
        Polynomial.aeval_algHom_apply, ← hρ, ← map_mul, ← hrel, sub_self]
    · apply mem_yRoots
      have h := congrArg ρ (gen_equation (W := W))
      simp only [map_add, map_mul, map_pow, AlgHom.commutes] at h
      exact h

omit [W.IsElliptic] in
theorem genPointHom_id (P : (W.map (algebraMap F W.FunctionField)).Point) :
    genPointHom (AlgHom.id F W.FunctionField) P = P := by
  cases P <;> rfl

end Generic

/-! ### The `4N` translations of `E_Q` over `X` -/

section Tate

open TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {s : Kˣ} {N : ℕ} {T : TateParameter K} (hT : T.q = s ^ N) (hN : 0 < N)
  (h12 : (12 : K) ≠ 0) [T.tateCurve.IsElliptic]

local notation "𝒫" => genericPoint (W := T.tateCurve.toAffine)

open Classical in
/-- The translation point of the kernel element `(-1)^e s^a` (`0` for `e = a = 0`). -/
def basePt (e : Fin 2) (a : Fin N) :
    (T.tateCurve.toAffine.map (algebraMap K (TateField T))).Point :=
  if h : (e, (a : ℕ)) = (0, 0) then 0
  else translatePoint (tateEquation h12 (offOrbit_cuspElt hT hN a.2 h))

open Classical in
/-- The translation `t_w` by the kernel element `w = (-1)^e s^a` (the identity for `w = 1`). -/
def baseAut (e : Fin 2) (a : Fin N) : TateField T ≃ₐ[K] TateField T :=
  if h : (e, (a : ℕ)) = (0, 0) then AlgEquiv.refl
  else transT h12 (offOrbit_cuspElt hT hN a.2 h)

/-- The `4N` candidates `t_w` and `t_w ∘ [-1]^*`. -/
def cand (i : Fin 2 × Fin N × Bool) : TateField T →ₐ[K] TateField T :=
  (baseAut hT hN h12 i.1 i.2.1 : TateField T →ₐ[K] TateField T).comp
    (if i.2.2 then (negT T : TateField T →ₐ[K] TateField T) else AlgHom.id K (TateField T))

theorem genPointHom_baseAut (e : Fin 2) (a : Fin N) :
    genPointHom (baseAut hT hN h12 e a : TateField T →ₐ[K] TateField T) 𝒫 =
      𝒫 + basePt hT hN h12 e a := by
  unfold baseAut basePt
  split_ifs with h
  · rw [add_zero]
    exact genPointHom_id _
  · rw [genericPoint_add_translatePoint]
    conv_lhs => rw [CoordinateRing.genericPoint, genPointHom_some]
    rfl

theorem genPointHom_basePt (φ : TateField T →ₐ[K] TateField T) (e : Fin 2) (a : Fin N) :
    genPointHom φ (basePt hT hN h12 e a) = basePt hT hN h12 e a := by
  unfold basePt
  split_ifs with h
  · exact map_zero _
  · exact genPointHom_translatePoint φ _

theorem genPointHom_cand (i : Fin 2 × Fin N × Bool) :
    genPointHom (cand hT hN h12 i) 𝒫 =
      if i.2.2 then -(𝒫 + basePt hT hN h12 i.1 i.2.1) else 𝒫 + basePt hT hN h12 i.1 i.2.1 := by
  obtain ⟨e, a, b⟩ := i
  cases b
  · simp only [cand, Bool.false_eq_true, if_false]
    rw [AlgHom.comp_id, genPointHom_baseAut]
  · simp only [cand, if_true]
    rw [← genPointHom_comp, genPointHom_negYAlgEquiv_genericPoint, map_neg, genPointHom_baseAut]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- `4 • 𝒫 ≠ 0`. -/
theorem four_nsmul_genericPoint_ne_zero : (4 : ℕ) • 𝒫 ≠ 0 := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  rw [nsmul_genericPoint_eq 4 (transcendental_N T.tateCurve 4)]
  exact Point.some_ne_zero _

/-- `𝒫 + P ≠ -(𝒫 + P')` for translation points `P, P'`: otherwise `[-1]^*` gives `4𝒫 = 0`. -/
theorem add_ne_neg_add (e e' : Fin 2) (a a' : Fin N) :
    𝒫 + basePt hT hN h12 e a ≠ -(𝒫 + basePt hT hN h12 e' a') := by
  intro h
  have h' := congrArg (genPointHom (negT T : TateField T →ₐ[K] TateField T)) h
  simp only [map_add, map_neg, genPointHom_negYAlgEquiv_genericPoint, genPointHom_basePt] at h'
  apply four_nsmul_genericPoint_ne_zero (T := T)
  have e4 : (4 : ℕ) • 𝒫 = ((𝒫 + basePt hT hN h12 e a) - (-𝒫 + basePt hT hN h12 e a)) -
      (-(𝒫 + basePt hT hN h12 e' a') - -(-𝒫 + basePt hT hN h12 e' a')) := by
    abel
  rw [e4, h, h', sub_self]

theorem basePt_injective (h2 : ‖(2 : K)‖ = 1) {e e' : Fin 2} {a a' : Fin N}
    (h : basePt hT hN h12 e a = basePt hT hN h12 e' a') : e = e' ∧ a = a' := by
  unfold basePt at h
  split_ifs at h with h1 h1' h1'
  · simp only [Prod.mk.injEq] at h1 h1'
    exact ⟨h1.1.trans h1'.1.symm, Fin.ext (h1.2.trans h1'.2.symm)⟩
  · exact absurd h.symm (Point.some_ne_zero _)
  · exact absurd h (Point.some_ne_zero _)
  · rw [translatePoint, translatePoint, Point.some.injEq] at h
    obtain ⟨hX, hY⟩ := h
    obtain ⟨n, hn⟩ := exists_zpow_of_coords_eq h12 h2
      (offOrbit_cuspElt hT hN a.2 h1) (offOrbit_cuspElt hT hN a'.2 h1')
      ((algebraMap K (TateField T)).injective hX) ((algebraMap K (TateField T)).injective hY)
    obtain ⟨he, ha⟩ := cuspElt_eq_of hT hN a.2 a'.2 hn
    exact ⟨he, Fin.ext ha⟩

/-- **The `4N` candidates are distinct on the generators.** -/
theorem cand_injective (h2 : ‖(2 : K)‖ = 1) {i i' : Fin 2 × Fin N × Bool}
    (hx : cand hT hN h12 i (genX _) = cand hT hN h12 i' (genX _))
    (hy : cand hT hN h12 i (genY _) = cand hT hN h12 i' (genY _)) : i = i' := by
  have hP : genPointHom (cand hT hN h12 i) 𝒫 = genPointHom (cand hT hN h12 i') 𝒫 := by
    rw [CoordinateRing.genericPoint, genPointHom_some, genPointHom_some, Point.some.injEq]
    exact ⟨hx, hy⟩
  rw [genPointHom_cand, genPointHom_cand] at hP
  obtain ⟨e, a, b⟩ := i
  obtain ⟨e', a', b'⟩ := i'
  cases b <;> cases b' <;> simp only [Bool.false_eq_true, if_false, if_true] at hP
  · obtain ⟨he, ha⟩ := basePt_injective hT hN h12 h2 (add_left_cancel hP)
    rw [he, ha]
  · exact absurd hP (add_ne_neg_add hT hN h12 e e' a a')
  · exact absurd hP.symm (add_ne_neg_add hT hN h12 e' e a' a)
  · obtain ⟨he, ha⟩ := basePt_injective hT hN h12 h2 (add_left_cancel (neg_inj.mp hP))
    rw [he, ha]

variable {t : TateParameter K} (hs : s ^ 2 = t.q) {P₁ Q₁ P₂ Q₂ : K[X]}
  (hR : ∀ v : Kˣ, OffOrbit T v → t.theta (-(v ^ 2)) ≠ 0 →
      P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v) ≠ 0 ∧
      t.X (v ^ 2) = (P₁.eval (T.X v) + T.Y v * Q₁.eval (T.X v)) /
        (P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v)))

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] [T.tateCurve.IsElliptic] in
include hs in
theorem cuspElt_sq (e : Fin 2) (a : ℕ) :
    ∃ k : ℤ, ((cuspElt s e a : Kˣ) : K) ^ 2 = (t.q : K) ^ k := by
  refine ⟨a, ?_⟩
  have hsq : ((-1 : K) ^ (e : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  simp only [cuspElt, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    mul_pow, hsq, one_mul, zpow_natCast]
  rw [← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, hs]

omit [T.tateCurve.IsElliptic] in
include hs hR in
/-- **The candidates fix `R = φ^* x_q`.** -/
theorem cand_R (h2 : ‖(2 : K)‖ = 1) (i : Fin 2 × Fin N × Bool) :
    cand hT hN h12 i (algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
      algebraMap _ (TateField T) (polyXY T P₂ Q₂)) =
    algebraMap _ (TateField T) (polyXY T P₁ Q₁) / algebraMap _ (TateField T) (polyXY T P₂ Q₂) := by
  obtain ⟨e, a, b⟩ := i
  have hbase : ∀ g : TateField T,
      g = algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
        algebraMap _ (TateField T) (polyXY T P₂ Q₂) →
      baseAut hT hN h12 e a g = g := by
    rintro g rfl
    unfold baseAut
    split_ifs with h
    · rfl
    · exact transT_R_eq (h12 := h12) hs hN hT h2 hR _ (cuspElt_sq hs e a)
  cases b
  · simp only [cand, Bool.false_eq_true, if_false, AlgHom.comp_id]
    exact hbase _ rfl
  · simp only [cand, if_true, AlgHom.comp_apply]
    rw [show (negT T : TateField T →ₐ[K] TateField T) _ = negT T _ from rfl,
      negT_R_eq hs hN hT h12 hR]
    exact hbase _ rfl

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] [T.tateCurve.IsElliptic] in
/-- `Y(qⁿ·u) = Y(u)` for `n : ℤ`. -/
theorem Y_zpow_mul (t : TateParameter K) (n : ℤ) (u : Kˣ) : t.Y (t.q ^ n * u) = t.Y u := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, one_mul]
  | succ n ih => rw [zpow_add_one, mul_comm _ t.q, mul_assoc, t.Y_q_smul, ih]
  | pred n ih =>
    rw [← ih, show t.q ^ (-(n : ℤ)) * u = t.q * (t.q ^ (-(n : ℤ) - 1) * u) by
      rw [← mul_assoc, ← zpow_one_add]; ring_nf, t.Y_q_smul]

/-! ### `R_y = φ^* y_q` and the action of the candidates on it -/

variable {C₁ E₁ C₂ E₂ : K[X]}
  (hRy : ∀ v : Kˣ, OffOrbit T v → t.theta (-(v ^ 2)) ≠ 0 →
      C₂.eval (T.X v) + T.Y v * E₂.eval (T.X v) ≠ 0 ∧
      t.Y (v ^ 2) = (C₁.eval (T.X v) + T.Y v * E₁.eval (T.X v)) /
        (C₂.eval (T.X v) + T.Y v * E₂.eval (T.X v)))

omit [CharZero K] [T.tateCurve.IsElliptic] in
include hRy in
/-- The value of `R_y = (C₁ + yE₁)/(C₂ + yE₂)` at `u` (with `u² ∉ qᶻ`) is `Y_q(u²)`. -/
theorem hasTateValue_Ry {u : Kˣ} (hu : OffOrbit T u) (hu2 : OffOrbit t (u ^ 2)) :
    HasTateValue T h12 (algebraMap _ (TateField T) (polyXY T C₁ E₁) /
      algebraMap _ (TateField T) (polyXY T C₂ E₂)) hu (t.Y (u ^ 2)) := by
  obtain ⟨hd, he⟩ := hRy u hu (theta_neg_ne_zero t hu2)
  refine ((HasTateValue.ofRing hu _).div (HasTateValue.ofRing hu _)
    (by rwa [evalTate_polyXY])).congr ?_
  rw [evalTate_polyXY, evalTate_polyXY, he]

omit [CharZero K] [T.tateCurve.IsElliptic] in
include hs hN hT hRy in
/-- **Translation by `w` with `w² ∈ qᶻ` fixes `R_y`.** -/
theorem transT_Ry_eq (h2 : ‖(2 : K)‖ = 1) {w : Kˣ} (hw : OffOrbit T w)
    (hk : ∃ k : ℤ, (w : K) ^ 2 = (t.q : K) ^ k) :
    transT h12 hw (algebraMap _ (TateField T) (polyXY T C₁ E₁) /
      algebraMap _ (TateField T) (polyXY T C₂ E₂)) =
    algebraMap _ (TateField T) (polyXY T C₁ E₁) / algebraMap _ (TateField T) (polyXY T C₂ E₂) := by
  obtain ⟨k, hk⟩ := hk
  have hq : (t.q : K) ≠ 0 := t.q.ne_zero
  have hD : badPoly T s N * (Polynomial.X - C (T.X w)) ≠ 0 :=
    mul_ne_zero badPoly_ne_zero (X_sub_C_ne_zero _)
  have good : ∀ (u : Kˣ) (hu : OffOrbit T u),
      evalTate T h12 hu (mkT T (C (badPoly T s N * (Polynomial.X - C (T.X w))))) ≠ 0 →
      OffOrbit t (u ^ 2) ∧ T.X u ≠ T.X w := by
    intro u hu h0
    rw [evalTate_mk_C, eval_mul, eval_sub, eval_X, eval_C] at h0
    obtain ⟨h0a, h0b⟩ := mul_ne_zero_iff.mp h0
    refine ⟨?_, sub_ne_zero.mp h0b⟩
    by_contra h
    exact h0a (badPoly_eval_eq_zero hs hN hT h)
  refine eq_of_hasTateValue (h12 := h12) (mkT_C_ne_zero h12 hD)
    (G := fun u => t.Y (u ^ 2)) (fun u hu h0 => ?_) (fun u hu h0 => hasTateValue_Ry h12 hRy hu
      (good u hu h0).1)
  obtain ⟨hu2, hx⟩ := good u hu h0
  have huw : OffOrbit T (u * w) := by
    intro n hn
    apply hx
    have e : u = T.q ^ (-n) * w⁻¹ := by
      apply Units.ext
      push_cast at hn ⊢
      have hw0 : (w : K) ≠ 0 := w.ne_zero
      have hT0 : (T.q : K) ≠ 0 := T.q.ne_zero
      rw [zpow_neg]
      field_simp
      linear_combination hn
    rw [e, X_zpow_mul, T.X_inv hw]
  have huw2 : OffOrbit t ((u * w) ^ 2) := by
    intro n hn
    apply hu2 (n + k)
    push_cast at hn ⊢
    rw [zpow_add₀ hq, ← hn, mul_pow, hk]
    ring
  have e2 : (u * w) ^ 2 = t.q ^ k * u ^ 2 :=
    Units.ext (by push_cast; rw [mul_pow, hk]; ring)
  exact hasTateValue_trans h2 hu hw huw hx _ _
    ((hasTateValue_Ry h12 hRy huw huw2).congr (by rw [e2, Y_zpow_mul]))

omit [CharZero K] [T.tateCurve.IsElliptic] in
include hs hN hT h12 hR hRy in
/-- **`[-1]^* R_y = -R_y - R`** (`Y_q(Ü^{-2}) = -Y_q(Ü²) - X_q(Ü²)`). -/
theorem negT_Ry_eq :
    negT T (algebraMap _ (TateField T) (polyXY T C₁ E₁) /
      algebraMap _ (TateField T) (polyXY T C₂ E₂)) =
    -(algebraMap _ (TateField T) (polyXY T C₁ E₁) /
      algebraMap _ (TateField T) (polyXY T C₂ E₂)) -
      algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
        algebraMap _ (TateField T) (polyXY T P₂ Q₂) := by
  have good : ∀ (u : Kˣ) (hu : OffOrbit T u),
      evalTate T h12 hu (mkT T (C (badPoly T s N))) ≠ 0 → OffOrbit t (u ^ 2) := by
    intro u hu h0
    by_contra h
    exact h0 (by rw [evalTate_mk_C]; exact badPoly_eval_eq_zero hs hN hT h)
  refine eq_of_hasTateValue (h12 := h12) (mkT_C_ne_zero h12 badPoly_ne_zero)
    (G := fun u => -t.Y (u ^ 2) - t.X (u ^ 2)) (fun u hu h0 => ?_) (fun u hu h0 =>
      ((hasTateValue_Ry h12 hRy hu (good u hu h0)).neg).sub (hasTateValue_R hR hu (good u hu h0)))
  have hu2 := good u hu h0
  have hi : OffOrbit t (u⁻¹ ^ 2) := by rw [inv_pow]; exact offOrbit_inv t hu2
  exact hasTateValue_negY hu ((hasTateValue_Ry h12 hRy (offOrbit_inv T hu) hi).congr
    (by rw [inv_pow, t.Y_inv hu2]))

omit [T.tateCurve.IsElliptic] in
include hs hR hRy in
/-- **The candidates on `R_y`**: `t_w` fixes it and `t_w ∘ [-1]^*` sends it to `-R_y - R`. -/
theorem cand_Ry (h2 : ‖(2 : K)‖ = 1) (i : Fin 2 × Fin N × Bool) :
    cand hT hN h12 i (algebraMap _ (TateField T) (polyXY T C₁ E₁) /
      algebraMap _ (TateField T) (polyXY T C₂ E₂)) =
    if i.2.2 then -(algebraMap _ (TateField T) (polyXY T C₁ E₁) /
        algebraMap _ (TateField T) (polyXY T C₂ E₂)) -
        algebraMap _ (TateField T) (polyXY T P₁ Q₁) / algebraMap _ (TateField T) (polyXY T P₂ Q₂)
    else algebraMap _ (TateField T) (polyXY T C₁ E₁) /
        algebraMap _ (TateField T) (polyXY T C₂ E₂) := by
  obtain ⟨e, a, b⟩ := i
  have hbase : baseAut hT hN h12 e a (algebraMap _ (TateField T) (polyXY T C₁ E₁) /
      algebraMap _ (TateField T) (polyXY T C₂ E₂)) =
      algebraMap _ (TateField T) (polyXY T C₁ E₁) /
        algebraMap _ (TateField T) (polyXY T C₂ E₂) := by
    unfold baseAut
    split_ifs with h
    · rfl
    · exact transT_Ry_eq hT hN h12 hs hRy h2 _ (cuspElt_sq hs e a)
  have hbaseR : baseAut hT hN h12 e a (algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
      algebraMap _ (TateField T) (polyXY T P₂ Q₂)) =
      algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
        algebraMap _ (TateField T) (polyXY T P₂ Q₂) := by
    unfold baseAut
    split_ifs with h
    · rfl
    · exact transT_R_eq (h12 := h12) hs hN hT h2 hR _ (cuspElt_sq hs e a)
  cases b
  · simp only [cand, Bool.false_eq_true, if_false, AlgHom.comp_id]
    exact hbase
  · simp only [cand, if_true, AlgHom.comp_apply]
    rw [show (negT T : TateField T →ₐ[K] TateField T) _ = negT T _ from rfl,
      negT_Ry_eq hT hN h12 hs hR hRy]
    simp only [AlgEquiv.coe_toAlgHom, map_sub, map_neg, hbase, hbaseR]

/-! ### The classification -/

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem natDegree_le_of_degree_lt {P : K[X]} {m : ℕ} (h : P.degree < (m + 1 : ℕ)) :
    P.natDegree ≤ m := by
  by_cases hP : P = 0
  · simp [hP]
  · exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt hP).mpr h)

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem natDegree_lt_of_degree_lt' {P : K[X]} {m : ℕ} (hm : 0 < m) (h : P.degree < m) :
    P.natDegree < m := by
  by_cases hP : P = 0
  · simp [hP, hm]
  · exact (natDegree_lt_iff_degree_lt hP).mpr h

include hs hR in
/-- **Every `K`-algebra map `ρ : K(E_Q) → L` with `ρ(R) = ι(R)` is `ι ∘ t_w` or `ι ∘ t_w ∘ [-1]^*`**
for one of the `2N` kernel points `w` (`R = φ^* x_q`, degree bounds of
`exists_poly_isogenyX_deg`). -/
theorem eq_cand_of_eq (h2 : ‖(2 : K)‖ = 1) (hP₁ : P₁.degree < ((2 * N * 2) / 2 + 1 : ℕ))
    (hQ₁ : Q₁.degree < ((2 * N * 2 - 1) / 2 : ℕ)) (hP₂ : P₂.degree < ((2 * N * 2) / 2 + 1 : ℕ))
    (hQ₂ : Q₂.degree < ((2 * N * 2 - 1) / 2 : ℕ)) {L : Type*} [Field L] [Algebra K L]
    (ι ρ : TateField T →ₐ[K] L)
    (hr : Transcendental K (ι (algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
      algebraMap _ (TateField T) (polyXY T P₂ Q₂))))
    (hρ : ρ (algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
      algebraMap _ (TateField T) (polyXY T P₂ Q₂)) =
      ι (algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
        algebraMap _ (TateField T) (polyXY T P₂ Q₂))) :
    ∃ i, ρ = ι.comp (cand hT hN h12 i) := by
  classical
  set R := algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
    algebraMap _ (TateField T) (polyXY T P₂ Q₂) with hRdef
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_norm h2
  have hpoly : ∀ P Q : K[X], algebraMap _ (TateField T) (polyXY T P Q) =
      aeval (genX _) P + genY _ * aeval (genX _) Q := fun P Q => algebraMap_smul_basis P Q
  have hd : aeval (genX _) P₂ + genY _ * aeval (genX _) Q₂ ≠ (0 : TateField T) := by
    intro h0
    apply hr
    rw [hRdef, hpoly P₂ Q₂, h0, div_zero, map_zero]
    exact isAlgebraic_zero
  have hRd : R * (aeval (genX _) P₂ + genY _ * aeval (genX _) Q₂) =
      aeval (genX _) P₁ + genY _ * aeval (genX _) Q₁ := by
    rw [hRdef, hpoly, hpoly, div_mul_cancel₀ _ hd]
  have hRneg : negYAlgEquiv _ R = R := negT_R_eq hs hN hT h12 hR
  have hm : (2 * N * 2) / 2 = 2 * N := by omega
  have hm' : (2 * N * 2 - 1) / 2 + 1 ≤ 2 * N := by omega
  rw [hm] at hP₁ hP₂
  obtain ⟨S, hS, hmem⟩ := exists_finset_of_eq (W := T.tateCurve.toAffine) h2K hRneg hRd hd
    (natDegree_le_of_degree_lt hP₁) (natDegree_le_of_degree_lt hP₂)
    (by have := natDegree_lt_of_degree_lt' (by omega) hQ₁; omega)
    (by have := natDegree_lt_of_degree_lt' (by omega) hQ₂; omega) hr
  set f : Fin 2 × Fin N × Bool → L × L :=
    fun i => (ι (cand hT hN h12 i (genX _)), ι (cand hT hN h12 i (genY _))) with hf
  have hιinj : Function.Injective ι := (ι : TateField T →+* L).injective
  have finj : Function.Injective f := fun i i' h =>
    cand_injective hT hN h12 h2 (hιinj (Prod.ext_iff.mp h).1) (hιinj (Prod.ext_iff.mp h).2)
  have hCS : Finset.univ.image f ⊆ S := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact hmem (ι.comp (cand hT hN h12 i)) (by
      rw [AlgHom.comp_apply, hRdef, cand_R hT hN h12 hs hR h2 i])
  have hcard : (Finset.univ.image f).card = 2 * (2 * N) := by
    rw [Finset.card_image_of_injective _ finj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_bool]
    ring
  have hEq := Finset.eq_of_subset_of_card_le hCS (by omega)
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (hEq ▸ hmem ρ hρ)
  refine ⟨i, algHom_ext_genXY ?_ ?_⟩
  · exact (Prod.ext_iff.mp hi).1.symm
  · exact (Prod.ext_iff.mp hi).2.symm

include hs hR hRy in
/-- **The refinement with `R_y`**: if moreover `ρ(R_y) = ι(R_y)` and `ι(2R_y + R) ≠ 0`, then
`ρ = ι ∘ t_w` for one of the `2N` kernel points (the case `t_w ∘ [-1]^*` would give
`2ι(R_y) + ι(R) = 0`). -/
theorem eq_baseAut_of_eq (h2 : ‖(2 : K)‖ = 1) (hP₁ : P₁.degree < ((2 * N * 2) / 2 + 1 : ℕ))
    (hQ₁ : Q₁.degree < ((2 * N * 2 - 1) / 2 : ℕ)) (hP₂ : P₂.degree < ((2 * N * 2) / 2 + 1 : ℕ))
    (hQ₂ : Q₂.degree < ((2 * N * 2 - 1) / 2 : ℕ)) {L : Type*} [Field L] [Algebra K L]
    (ι ρ : TateField T →ₐ[K] L)
    (hr : Transcendental K (ι (algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
      algebraMap _ (TateField T) (polyXY T P₂ Q₂))))
    (hρ : ρ (algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
      algebraMap _ (TateField T) (polyXY T P₂ Q₂)) =
      ι (algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
        algebraMap _ (TateField T) (polyXY T P₂ Q₂)))
    (hρy : ρ (algebraMap _ (TateField T) (polyXY T C₁ E₁) /
      algebraMap _ (TateField T) (polyXY T C₂ E₂)) =
      ι (algebraMap _ (TateField T) (polyXY T C₁ E₁) /
        algebraMap _ (TateField T) (polyXY T C₂ E₂)))
    (hψ : 2 * ι (algebraMap _ (TateField T) (polyXY T C₁ E₁) /
        algebraMap _ (TateField T) (polyXY T C₂ E₂)) +
      ι (algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
        algebraMap _ (TateField T) (polyXY T P₂ Q₂)) ≠ 0) :
    ∃ (e : Fin 2) (a : Fin N),
      ρ = ι.comp (baseAut hT hN h12 e a : TateField T →ₐ[K] TateField T) := by
  obtain ⟨⟨e, a, b⟩, hi⟩ := eq_cand_of_eq hT hN h12 hs hR h2 hP₁ hQ₁ hP₂ hQ₂ ι ρ hr hρ
  cases b
  · refine ⟨e, a, ?_⟩
    rw [hi]
    simp only [cand, Bool.false_eq_true, if_false, AlgHom.comp_id]
  · exfalso
    apply hψ
    have h := hρy
    rw [hi, AlgHom.comp_apply, cand_Ry hT hN h12 hs hR hRy h2] at h
    simp only [if_true, map_sub, map_neg] at h
    linear_combination -h

end Tate

end Iut.EtaleTheta
