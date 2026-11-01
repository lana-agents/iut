/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaClassSystem
import Iut.EtaleTheta.ThetaCuspMain
import Iut.EtaleTheta.ThetaCuspInertia

/-!
# Cusp inertia at the levels `Ÿ'_N`: `κ_n(η_N)` is the tame character (MR14, step B)

[EtTh] Prop. 1.3 in the finite-level form of `ThetaCuspInertia.lean` (the restriction of
`κ_n(η_N)` to the inertia group of every cusp of the level is the tame character mod `n`), for the
levels and units of the étale theta system; the system theorem `exists_etaleThetaSystem` is
stated and proved in `ThetaLevelHeisenberg.lean` (since MR14 run 15, with the translation formula).

* **B1, the pullback** `ι = φ ∘ j : K(E_Q) → K(E_q) → Ω` (`Q = s^N`, `φ = mulByNEmb (2N)`):
  `coordLift` (`K[E_Q] → L` from a point `(x₀, y₀)` of `E_Q` over `L`, `AdjoinRoot.lift`),
  injective if `x₀` is transcendental (`coordLift_injective`: `K[E_Q]` is integral over `K[x]`),
  and `pullbackT`, its extension to `K(E_Q)`. For `x₀ = x_Q∘ψ`, `y₀ = y_Q∘ψ` of
  `exists_levelData`, the equation of `E_Q` holds by values (`isTPoint_of_values`), `x₀` is
  transcendental since `K(x₀, y₀) ∋ [2N]^*x` (`transcendental_of_mem_adjoin`), and values transfer
  (`hasTateValue_pullbackT`: the value of `j g` at `u` is the value of `g` at `u^N`); hence
  `j f = F_N` and `j R = [2N]^*x`, so `ι f = η_N`, `ι R = τ`.
* **B2, places**: a place `W ⊇ K` of `Ω` with `τ ∉ W` restricts to the place of a point `p` of
  `E_Q` with `ord_p R < 0` (`exists_placeOf_comap`, via `elliptic-curves`' `placeOf`); elements
  integral over `K[τ]` are integral wherever `R` is (`mem_of_isIntegral_A₀`), so the unit `η_N`
  gives `ord_p f = 0` where `R` is regular (`divisorProj_eq_zero_of_isIntegral`): the hypothesis
  of `thetaLevel_cusp_orders`, which then gives `ord_p f ∈ {1, 1 - N}`.
* **B3**: `CuspTameAt` (conclusion-only Prop, like `InversionAt`): a uniformiser `π` of `W ∩ F`
  with `κ_n(η)(σ) = σ(π^{1/n})/π^{1/n}` on `I_W ∩ H`; `cuspTameAt_of_order` (generic: from
  `ord_p f ≡ 1 mod n`, with `evalTriv_kummerMap_eq_tame`), **`cuspTameAt_level`** (one level),
  used by `exists_etaleThetaSystem` (`ThetaLevelHeisenberg.lean`).
-/

open Polynomial IsDedekindDomain

noncomputable section

universe u

namespace Iut.EtaleTheta

open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]

section Pullback

variable {T : TateParameter K} {L : Type*} [Field L] [Algebra K L]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
/-- `(x, y)` satisfies the Weierstrass equation of `E_T`. -/
def IsTPoint (T : TateParameter K) (x y : L) : Prop :=
  (T.tateCurve.toAffine.polynomial).eval₂ (aeval x).toRingHom y = 0

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem isTPoint_iff (x y : L) : IsTPoint T x y ↔
    y ^ 2 + algebraMap K L T.tateCurve.a₁ * x * y + algebraMap K L T.tateCurve.a₃ * y +
      algebraMap K L (-1) * (x ^ 3 + algebraMap K L T.tateCurve.a₂ * x ^ 2 +
        algebraMap K L T.tateCurve.a₄ * x + algebraMap K L T.tateCurve.a₆) = 0 := by
  unfold IsTPoint
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_pow,
    aeval_X, aeval_C, map_neg, map_one]
  constructor <;> intro h <;> linear_combination h

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
/-- **The pullback on coordinate rings** `K[E_T] → L`, `x ↦ x₀`, `y ↦ y₀`, for a point
`(x₀, y₀)` of `E_T` with coordinates in `L`. -/
def coordLift (x y : L) (h : IsTPoint T x y) : TateRing T →ₐ[K] L :=
  { AdjoinRoot.lift (f := T.tateCurve.toAffine.polynomial) (aeval x).toRingHom y h with
    commutes' := fun c => by
      change AdjoinRoot.lift (f := T.tateCurve.toAffine.polynomial) (aeval x).toRingHom y h
        (algebraMap K (TateRing T) c) = _
      rw [IsScalarTower.algebraMap_apply K K[X] (TateRing T), AdjoinRoot.algebraMap_eq,
        AdjoinRoot.lift_of]
      simp }

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem coordLift_smul_basis (x y : L) (h : IsTPoint T x y) (p q : K[X]) :
    coordLift x y h (p • (1 : TateRing T) + q • mkT T Polynomial.X) =
      aeval x p + aeval x q * y := by
  rw [CoordinateRing.smul, CoordinateRing.smul, mul_one]
  simp [coordLift, mkT]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem coordLift_comp_algebraMap (x y : L) (h : IsTPoint T x y) :
    ((coordLift x y h).toRingHom.comp (algebraMap K[X] (TateRing T))) = (aeval x).toRingHom := by
  ext p
  · simp [coordLift, AdjoinRoot.algebraMap_eq]
  · simp [coordLift, AdjoinRoot.algebraMap_eq]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
/-- `coordLift` is injective if `x₀` is transcendental (`K[E_T]` is integral over `K[x]`). -/
theorem coordLift_injective (x y : L) (h : IsTPoint T x y) (hx : Transcendental K x) :
    Function.Injective (coordLift x y h) := by
  have hinj : Function.Injective (aeval (R := K) x) := (transcendental_iff_injective).mp hx
  change Function.Injective (coordLift x y h).toRingHom
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hker : RingHom.ker (coordLift x y h).toRingHom = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := K[X]) ?_
    rw [RingHom.comap_ker, coordLift_comp_algebraMap]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have : a ∈ RingHom.ker (coordLift x y h).toRingHom := ha
  rwa [hker, Ideal.mem_bot] at this

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem coordLift_mem_adjoin (x y : L) (h : IsTPoint T x y) (a : TateRing T) :
    coordLift x y h a ∈ IntermediateField.adjoin K ({x, y} : Set L) := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
  rw [coordLift_smul_basis]
  have hx : x ∈ IntermediateField.adjoin K ({x, y} : Set L) :=
    IntermediateField.subset_adjoin _ _ (by simp)
  have hy : y ∈ IntermediateField.adjoin K ({x, y} : Set L) :=
    IntermediateField.subset_adjoin _ _ (by simp)
  exact add_mem (aeval_mem_adjoin hx p) (mul_mem (aeval_mem_adjoin hx q) hy)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- If `K(x₀, y₀)` contains a transcendental element, `x₀` is transcendental (`y₀` is algebraic
over `K(x₀)` by the Weierstrass equation; `2 ≠ 0` in `K`). -/
theorem transcendental_of_mem_adjoin (x y : L) (h : IsTPoint T x y) {z : L}
    (hz : z ∈ IntermediateField.adjoin K ({x, y} : Set L)) (htr : Transcendental K z) :
    Transcendental K x := by
  intro hx
  have hxi : IsIntegral K x := hx.isIntegral
  have e := (isTPoint_iff (T := T) x y).mp h
  have ha : ∀ c : K, IsIntegral K (algebraMap K L c) := fun c => isIntegral_algebraMap
  set w := 2 * y + algebraMap K L T.tateCurve.a₁ * x + algebraMap K L T.tateCurve.a₃ with hw
  have hw2 : w ^ 2 = 4 * (x ^ 3 + algebraMap K L T.tateCurve.a₂ * x ^ 2 +
      algebraMap K L T.tateCurve.a₄ * x + algebraMap K L T.tateCurve.a₆) +
      (algebraMap K L T.tateCurve.a₁ * x + algebraMap K L T.tateCurve.a₃) ^ 2 := by
    rw [hw, map_neg, map_one] at *
    linear_combination 4 * e
  have h4 : (4 : L) = algebraMap K L 4 := (map_ofNat (algebraMap K L) 4).symm
  have hwi : IsIntegral K w := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hw2, h4]
    exact ((ha 4).mul (((hxi.pow 3).add ((ha _).mul (hxi.pow 2))).add ((ha _).mul hxi) |>.add
      (ha _))).add ((((ha _).mul hxi).add (ha _)).pow 2)
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hy : y = algebraMap K L (2⁻¹) *
      (w - algebraMap K L T.tateCurve.a₁ * x - algebraMap K L T.tateCurve.a₃) := by
    have h2' : algebraMap K L 2 = 2 := map_ofNat (algebraMap K L) 2
    have h2L : (2 : L) ≠ 0 := by rw [← h2']; exact (_root_.map_ne_zero _).mpr h2
    rw [hw, map_inv₀, h2']
    field_simp
    ring
  have hyi : IsIntegral K y := by
    rw [hy]; exact (ha _).mul ((hwi.sub ((ha _).mul hxi)).sub (ha _))
  have halg : Algebra.IsAlgebraic K (IntermediateField.adjoin K ({x, y} : Set L)) := by
    refine IntermediateField.isAlgebraic_adjoin fun a ha' => ?_
    rcases ha' with rfl | ha'
    · exact hxi
    · rw [Set.mem_singleton_iff] at ha'; rw [ha']; exact hyi
  exact htr ((Algebra.IsAlgebraic.isAlgebraic (⟨z, hz⟩ :
    IntermediateField.adjoin K ({x, y} : Set L))).algHom (IntermediateField.val _))

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
/-- **The pullback** `K(E_T) → L` of the point `(x₀, y₀)` with `x₀` transcendental. -/
def pullbackT (x y : L) (h : IsTPoint T x y) (hx : Transcendental K x) : TateField T →ₐ[K] L :=
  IsFractionRing.liftAlgHom (K := TateField T) (coordLift_injective x y h hx)

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem pullbackT_algebraMap (x y : L) (h : IsTPoint T x y) (hx : Transcendental K x)
    (a : TateRing T) :
    pullbackT x y h hx (algebraMap (TateRing T) (TateField T) a) = coordLift x y h a :=
  IsFractionRing.liftAlgHom_apply _ _ |>.trans (IsFractionRing.lift_algebraMap _ _)

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem pullbackT_genX (x y : L) (h : IsTPoint T x y) (hx : Transcendental K x) :
    pullbackT x y h hx (algebraMap (TateRing T) (TateField T) (mkT T (C X))) = x := by
  rw [pullbackT_algebraMap]
  simp [coordLift, mkT]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem pullbackT_genY (x y : L) (h : IsTPoint T x y) (hx : Transcendental K x) :
    pullbackT x y h hx (algebraMap (TateRing T) (TateField T) (mkT T Polynomial.X)) = y := by
  rw [pullbackT_algebraMap]
  simp [coordLift, mkT]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem pullbackT_mem_adjoin (x y : L) (h : IsTPoint T x y) (hx : Transcendental K x)
    (g : TateField T) : pullbackT x y h hx g ∈ IntermediateField.adjoin K ({x, y} : Set L) := by
  obtain ⟨n, d, -, rfl⟩ := IsFractionRing.div_surjective (A := TateRing T) g
  rw [map_div₀, pullbackT_algebraMap, pullbackT_algebraMap]
  exact div_mem (coordLift_mem_adjoin x y h n) (coordLift_mem_adjoin x y h d)

end Pullback

/-! ### Values of the pullback at Tate points -/

section Values

variable {t T : TateParameter K} {h12 : (12 : K) ≠ 0}

omit [CharZero K] in
theorem hasTateValue_coordLift {gX gY : TateField t} (h : IsTPoint T gX gY) {u v : Kˣ}
    {hu : OffOrbit t u} (hv : OffOrbit T v) (hX : HasTateValue t h12 gX hu (T.X v))
    (hY : HasTateValue t h12 gY hu (T.Y v)) (a : TateRing T) :
    HasTateValue t h12 (coordLift gX gY h a) hu (evalTate T h12 hv a) := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
  rw [coordLift_smul_basis, evalTate_smul_basis]
  exact ((hX.aeval p).add ((hX.aeval q).mul hY)).congr (by ring)

omit [CharZero K] in
/-- **Values of the pullback**: the value of `ι g` at `u` is the value of `g` at `v`, if `ι` maps
the coordinates of `E_T` to functions with the values `X_T(v)`, `Y_T(v)` at `u`. -/
theorem hasTateValue_pullbackT {gX gY : TateField t} (h : IsTPoint T gX gY)
    (hx : Transcendental K gX) {u v : Kˣ} {hu : OffOrbit t u} (hv : OffOrbit T v)
    (hX : HasTateValue t h12 gX hu (T.X v)) (hY : HasTateValue t h12 gY hu (T.Y v))
    {g : TateField T} {c : K} (hg : HasTateValue T h12 g hv c) :
    HasTateValue t h12 (pullbackT gX gY h hx g) hu c := by
  obtain ⟨n, d, hgd, hd, hc⟩ := hg
  have hd0 : algebraMap (TateRing T) (TateField T) d ≠ 0 :=
    algebraMap_ne_zero (ne_zero_of_evalTate_ne_zero hd)
  have e : g = algebraMap (TateRing T) (TateField T) n /
      algebraMap (TateRing T) (TateField T) d := by
    rw [← hgd, mul_div_assoc, div_self hd0, mul_one]
  rw [e, map_div₀, pullbackT_algebraMap, pullbackT_algebraMap]
  refine ((hasTateValue_coordLift h hv hX hY n).div (hasTateValue_coordLift h hv hX hY d) hd).congr
    ?_
  rw [← hc]; field_simp

omit [CharZero K] in
/-- The Weierstrass equation of `E_T` for `(gX, gY)` from values. -/
theorem isTPoint_of_values {gX gY : TateField t} {D₀ : TateRing t} (hD₀ : D₀ ≠ 0) (V : Kˣ → Kˣ)
    (h : ∀ (u : Kˣ) (hu : OffOrbit t u), evalTate t h12 hu D₀ ≠ 0 →
      ∃ _ : OffOrbit T (V u), HasTateValue t h12 gX hu (T.X (V u)) ∧
        HasTateValue t h12 gY hu (T.Y (V u))) :
    IsTPoint T gX gY := by
  rw [isTPoint_iff]
  refine eq_zero_of_hasTateValue (h12 := h12) hD₀ fun u hu h0 => ?_
  obtain ⟨hv, hX, hY⟩ := h u hu h0
  have e := (WeierstrassCurve.Affine.equation_iff _ _).mp (T.tatePoint_mem' h12 hv)
  have C := fun c : K => HasTateValue.const (t := t) (h12 := h12) hu c
  refine ((((hY.pow 2).add (((C _).mul hX).mul hY)).add ((C _).mul hY)).add ((C (-1)).mul
    ((((hX.pow 3).add ((C _).mul (hX.pow 2))).add ((C _).mul hX)).add (C _)))).congr ?_
  linear_combination e

end Values

/-! ### Places of `Ω` over a function field of an elliptic curve -/

section Places

open AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {E' : WeierstrassCurve.Affine k}
  [IsDedekindDomain E'.CoordinateRing]

/-- **A place of `Ω` where `ι R` is not integral restricts to a pole of `R`**: for a place
`W ⊇ k` of `Ω` and `ι : k(E') → Ω`, `W ∩ k(E')` is the place of a point `p` of `E'`, and
`ord_p R < 0` if `ι R ∉ W`. -/
theorem exists_placeOf_comap (ι : E'.FunctionField →ₐ[k] Ω) (W : ValuationSubring Ω)
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) {R : E'.FunctionField} (hR : ι R ∉ W) :
    ∃ p, placeOf E' p = W.comap ι.toRingHom ∧ divisorProj E' R p < 0 := by
  have hkV : ∀ c : k, algebraMap k E'.FunctionField c ∈ W.comap ι.toRingHom := fun c => by
    rw [ValuationSubring.mem_comap]
    change ι (algebraMap k _ c) ∈ W
    rw [ι.commutes]; exact hk c
  have hRV : R ∉ W.comap ι.toRingHom := hR
  have hne : W.comap ι.toRingHom ≠ ⊤ := fun h => hRV (h ▸ ValuationSubring.mem_top _)
  obtain ⟨p, hp⟩ := exists_placeOf_eq _ hkV hne
  have hR0 : R ≠ 0 := by
    rintro rfl; exact hR (by rw [map_zero]; exact W.zero_mem)
  refine ⟨p, hp, ?_⟩
  by_contra hle
  exact hRV (hp ▸ (mem_placeOf_iff_divisorProj_nonneg p hR0).mpr (not_lt.mp hle))

omit [IsDedekindDomain E'.CoordinateRing] in
/-- **Integral elements over `k[τ]` are integral at places containing a preimage of `τ`**: if
`ι R = τ` (`τ` transcendental), `R ∈ V`, `V ⊇ k`, and `ι g` is integral over `k[τ]`, then
`g ∈ V`. -/
theorem mem_of_isIntegral_A₀ (ι : E'.FunctionField →ₐ[k] Ω) {V : ValuationSubring E'.FunctionField}
    (hV : ∀ c : k, algebraMap k _ c ∈ V) {R : E'.FunctionField} (hR : R ∈ V) {τ : Ω}
    (hτ : Transcendental k τ) (hRτ : ι R = τ) {g : E'.FunctionField}
    (hg : IsIntegral (A₀ k τ) (ι g)) : g ∈ V := by
  obtain ⟨P, hPm, hP⟩ := hg
  let c : k →+* V := (algebraMap k E'.FunctionField).codRestrict V.toSubring hV
  let ρ : A₀ k τ →+* V := (Polynomial.eval₂RingHom c ⟨R, hR⟩).comp
    (Polynomial.algEquivOfTranscendental k τ hτ).symm.toRingEquiv.toRingHom
  have hρ : ∀ s : A₀ k τ, ι ((ρ s : V) : E'.FunctionField) = (s : Ω) := by
    intro s
    obtain ⟨q, rfl⟩ := (Polynomial.algEquivOfTranscendental k τ hτ).surjective s
    have e1 : ρ (Polynomial.algEquivOfTranscendental k τ hτ q) =
        Polynomial.eval₂ c ⟨R, hR⟩ q := by
      simp [ρ]
    rw [e1, Polynomial.algEquivOfTranscendental_apply]
    rw [show ((Polynomial.eval₂ c ⟨R, hR⟩ q : V) : E'.FunctionField) =
        Polynomial.eval₂ (V.subtype.comp c) R q from Polynomial.hom_eval₂ q c V.subtype ⟨R, hR⟩]
    rw [show ι (Polynomial.eval₂ (V.subtype.comp c) R q) =
        Polynomial.eval₂ (ι.toRingHom.comp (V.subtype.comp c)) (ι R) q from
          Polynomial.hom_eval₂ q _ ι.toRingHom R]
    have hc : ι.toRingHom.comp (V.subtype.comp c) = algebraMap k Ω := by
      ext a; exact ι.commutes a
    rw [hc, hRτ]
    change _ = ((Polynomial.aeval (⟨τ, Algebra.self_mem_adjoin_singleton k τ⟩ : A₀ k τ) q :
      A₀ k τ) : Ω)
    rw [← Subalgebra.aeval_coe]
    rfl
  have hint : IsIntegral V g := by
    refine ⟨P.map ρ, hPm.map ρ, ?_⟩
    apply ι.toRingHom.injective
    rw [map_zero, Polynomial.eval₂_map, Polynomial.hom_eval₂]
    have hc : ι.toRingHom.comp ((algebraMap V E'.FunctionField).comp ρ) =
        algebraMap (A₀ k τ) Ω := by
      ext s; exact hρ s
    rw [hc]; exact hP
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]; exact y.2

/-- **Units over `k[τ]` have order `0` where `R` is regular** (`ι R = τ`). -/
theorem divisorProj_eq_zero_of_isIntegral (ι : E'.FunctionField →ₐ[k] Ω) {R : E'.FunctionField}
    (hR0 : R ≠ 0) {τ : Ω} (hτ : Transcendental k τ) (hRτ : ι R = τ) {f : E'.FunctionField}
    (hf0 : f ≠ 0) (hf : IsIntegral (A₀ k τ) (ι f)) (hf' : IsIntegral (A₀ k τ) (ι f)⁻¹)
    (p : ProjPoint E') (hp : 0 ≤ divisorProj E' R p) : divisorProj E' f p = 0 := by
  have hRp : R ∈ placeOf E' p := (mem_placeOf_iff_divisorProj_nonneg p hR0).mpr hp
  have h1 := mem_of_isIntegral_A₀ ι (algebraMap_mem_placeOf p) hRp hτ hRτ hf
  have h2 := mem_of_isIntegral_A₀ ι (g := f⁻¹) (algebraMap_mem_placeOf p) hRp hτ hRτ
    (by rwa [map_inv₀])
  rw [mem_placeOf_iff_divisorProj_nonneg p hf0] at h1
  rw [mem_placeOf_iff_divisorProj_nonneg p (inv_ne_zero hf0), divisorProj_inv] at h2
  simp only [Finsupp.coe_neg, Pi.neg_apply, Left.nonneg_neg_iff] at h2
  omega

end Places

/-! ### Cusp inertia and the tame character -/

section Tame

open AffOrbicurve KummerTheory KummerTheory.Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t₀ : Ω} [CharZero k]
  [IsGalois (K₀ k t₀) Ω] [IsSepClosed Ω]

/-- **`κ_n(η)` is the tame character on the inertia group of the place `W`** (conclusion-only
Prop, like `InversionAt`): there is a uniformiser `π` of `W ∩ F` (in the sense of
continuous-kummer-theory's `exists_inertia_evalTriv_kummerMap_eq`) such that for every
`σ ∈ I_W ∩ H`, `κ_n(η)(σ)` is the Kummer character `σ ↦ σ(π^{1/n})/π^{1/n}` of `π` at `σ`
(the tame character of `W` mod `n`; by `evalTriv_tame_eq_of_unit` it does not depend on the
uniformiser). -/
def CuspTameAt (D : Pi1.Orbifold.GaloisData k t₀) (η : units D) (W : ValuationSubring Ω)
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (n : ℕ) [NeZero n] : Prop :=
  ∃ π : (F D)ˣ, W.valuation ((π : F D) : Ω) < 1 ∧
    (∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω)) ∧
    ∀ (σ : D.H) (hσ : (σ : Ω ≃ₐ[K₀ k t₀] Ω) ∈ GaloisPi1.inertia W),
      ContH1.evalTriv (σ : Pi D) (pi_inertia_smul_mu hk hσ n) (kummerMap D n η) =
        ContH1.evalTriv σ (inertia_smul_mu hk hσ n) (resMu D n (kummer n (F D) Ω π))

omit [CharZero k] [IsGalois (K₀ k t₀) Ω] [IsSepClosed Ω] in
theorem valuation_lt_one_iff_inv_notMem (W : ValuationSubring Ω) {x : Ω} (hx : x ≠ 0) :
    W.valuation x < 1 ↔ x⁻¹ ∉ W := by
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀,
    inv_le_one₀ ((Valuation.pos_iff _).mpr hx), not_le]

omit [CharZero k] [IsGalois (K₀ k t₀) Ω] [IsSepClosed Ω] in
/-- A unit of `F` is a nonzero element of `Ω`. -/
theorem coe_unit_ne_zero {D : Pi1.Orbifold.GaloisData k t₀} (v : (F D)ˣ) : ((v : F D) : Ω) ≠ 0 :=
  fun h => v.ne_zero (Subtype.ext h)

/-- **The tame character at a place `W` from the order of `η` at its centre**: if `F ⊆ ι(k(E'))`,
`η = ι f`, the centre of `W` on `k(E')` is the point `p`, and `ord_p f ≡ 1 mod n`, then
`CuspTameAt`. -/
theorem cuspTameAt_of_order {E' : WeierstrassCurve.Affine k} [IsDedekindDomain E'.CoordinateRing]
    (D : Pi1.Orbifold.GaloisData k t₀) (η : units D) (W : ValuationSubring Ω)
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (n : ℕ) [NeZero n] (ι : E'.FunctionField →ₐ[k] Ω)
    (hrange : ∀ z ∈ F D, ∃ g, ι g = z) (hmem : ∀ g, ι g ∈ F D) {f : E'.FunctionField}
    (hf : ι f = (((η : (F D)ˣ) : F D) : Ω)) (p : ProjPoint E')
    (hp : placeOf E' p = W.comap ι.toRingHom) (m : ℤ) (hm : divisorProj E' f p = m)
    (hnm : (n : ℤ) ∣ m - 1) : CuspTameAt D η W hk n := by
  obtain ⟨π₀, hπ0, hπ1⟩ := exists_divisorProj_eq_one p
  have mem : ∀ g, g ≠ 0 → (ι g ∈ W ↔ 0 ≤ divisorProj E' g p) := fun g hg => by
    rw [← mem_placeOf_iff_divisorProj_nonneg p hg, hp]; rfl
  have hι0 : ∀ g, g ≠ 0 → ι g ≠ 0 := fun g hg =>
    (map_ne_zero_iff _ ι.toRingHom.injective).mpr hg
  have lt : ∀ g, g ≠ 0 → (W.valuation (ι g) < 1 ↔ 0 < divisorProj E' g p) := fun g hg => by
    rw [valuation_lt_one_iff_inv_notMem W (hι0 g hg), ← map_inv₀, mem _ (inv_ne_zero hg),
      divisorProj_inv]
    simp only [Finsupp.coe_neg, Pi.neg_apply, Left.nonneg_neg_iff, not_le]
  have hf0 : f ≠ 0 := by
    rintro rfl; rw [map_zero] at hf; exact coe_unit_ne_zero _ hf.symm
  let π : (F D)ˣ := Units.mk0 ⟨ι π₀, hmem π₀⟩ (fun h => hι0 π₀ hπ0 (congrArg Subtype.val h))
  have hπval : ((π : F D) : Ω) = ι π₀ := rfl
  have hπι := hι0 π₀ hπ0
  refine ⟨π, ?_, ?_, fun σ hσ => ?_⟩
  · rw [hπval, lt π₀ hπ0, hπ1]; exact one_pos
  · intro z hz hzlt
    obtain ⟨g, rfl⟩ := hrange z hz
    by_cases hg : g = 0
    · subst hg; simp
    rw [lt g hg] at hzlt
    rw [hπval, ← div_le_one₀ ((Valuation.pos_iff _).mpr hπι), ← map_div₀, ← map_div₀,
      ValuationSubring.valuation_le_one_iff, mem _ (div_ne_zero hg hπ0), divisorProj_div hg hπ0]
    simp only [Finsupp.coe_sub, Pi.sub_apply, hπ1]
    omega
  · have hu0 : f * π₀ ^ (-m) ≠ 0 := mul_ne_zero hf0 (zpow_ne_zero _ hπ0)
    have hord : divisorProj E' (f * π₀ ^ (-m)) p = 0 := by
      rw [divisorProj_mul hf0 (zpow_ne_zero _ hπ0), divisorProj_zpow]
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, hm, hπ1,
        smul_eq_mul, mul_one]
      ring
    have hv : ((((η : (F D)ˣ) * π ^ (-m) : (F D)ˣ) : F D) : Ω) = ι (f * π₀ ^ (-m)) := by
      have e : ((((η : (F D)ˣ) * π ^ (-m) : (F D)ˣ) : F D) : Ω) =
          IntermediateField.val (F D) (((η : (F D)ˣ) : F D) * (π : F D) ^ (-m)) := by
        rw [Units.val_mul, Units.val_zpow_eq_zpow_val]; rfl
      rw [e, map_mul, map_zpow₀, map_mul, map_zpow₀, hf, ← hπval]
      rfl
    refine evalTriv_kummerMap_eq_tame hk hσ n η π m ?_ ?_ hnm
    · rw [hv, mem _ hu0, hord]
    · rw [Units.val_inv_eq_inv_val, IntermediateField.coe_inv, hv, ← map_inv₀,
        mem _ (inv_ne_zero hu0), divisorProj_inv]
      simp only [Finsupp.coe_neg, Pi.neg_apply, hord, neg_zero, le_refl]

end Tame

/-! ### The cusps of the levels `Ÿ'_N` of the étale theta system -/

section Level

open CategoryTheory AlgebraicGeometry Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer

variable {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

/-- **Cusp inertia at a level `Ÿ'_N`** ([EtTh] Prop. 1.3 in the finite-level form of
`ThetaCuspInertia.lean`, with [EtTh] Prop. 1.4(i) through `thetaLevel_cusp_orders`): for the level
data `x_Q∘ψ, y_Q∘ψ, F_N` of `exists_levelData`, the level `L = K(τ)(φ(x_Q∘ψ), φ(y_Q∘ψ))`
(`φ = mulByNEmb (2N)`) and the unit `η = φ(F_N)`, at every place `W ⊇ K` of `Ω` with `τ ∉ W`
(a cusp of the level) and every `n ∣ N`, `κ_n(η)` is the tame character on `I_W ∩ H`. -/
theorem cuspTameAt_level (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q)
    {N : ℕ} (hN : 0 < N) (hev : Even N) [t.tateCurve.IsElliptic] [NeZero (2 * N)]
    {gX gY Fθ : TateField t}
    (hmul : ∀ a : TateRing t, algebraMap _ (TateField t) (mulByNHom t.tateCurve (2 * N) a) ∈
      IntermediateField.adjoin K ({gX, gY} : Set (TateField t)))
    (hval : ∀ (u : Kˣ) (hu : OffOrbit t u), OffOrbit t (u ^ (2 * N)) →
      HasTateValue t h12 gX hu ((sqrtPow hs N hN).X (u ^ N)) ∧
      HasTateValue t h12 gY hu ((sqrtPow hs N hN).Y (u ^ N)) ∧
      HasTateValue t h12 Fθ hu (thetaLevel t N hN (u ^ N)))
    {L : IntermediateField (K₀ K τ) Ω}
    (hLd : L = IntermediateField.adjoin (K₀ K τ) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}))
    (hL : IsOpen (L.fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
    (η : units (fieldData (transcendental_tau t.tateCurve) L hL))
    (hη : ((((η : (F (fieldData (transcendental_tau t.tateCurve) L hL))ˣ) :
        F (fieldData (transcendental_tau t.tateCurve) L hL)) : Ω)) =
      mulByNEmb t.tateCurve (2 * N) Fθ)
    (W : ValuationSubring Ω) (hk : ∀ c : K, algebraMap K Ω c ∈ W) (hτ : τ ∉ W)
    (n : ℕ) [NeZero n] (hn : n ∣ N) :
    CuspTameAt (fieldData (transcendental_tau t.tateCurve) L hL) η W hk n := by
  set T := sqrtPow hs N hN with hTdef
  haveI : T.tateCurve.IsElliptic := T.tateCurve_isElliptic h12
  have hN2 : 2 ≤ N := by obtain ⟨r, hr⟩ := hev; omega
  have hψ0 := psiN_ne_zero_of_neZero t.tateCurve (2 * N)
  have hpts : ∀ (u : Kˣ) (hu : OffOrbit t u),
      evalTate t h12 hu (psiN t.tateCurve (2 * N)) ≠ 0 → OffOrbit t (u ^ (2 * N)) :=
    fun u hu hψ => (hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu hψ).1
  have hpt : IsTPoint T gX gY := isTPoint_of_values (h12 := h12) hψ0 (fun u => u ^ N)
    fun u hu hψ => ⟨offOrbit_sqrt_pow hs T rfl (hpts u hu hψ), (hval u hu (hpts u hu hψ)).1,
      (hval u hu (hpts u hu hψ)).2.1⟩
  -- `τ = φ([2N]^* x)`
  set Rt : TateField t := algebraMap (coverRingN t.tateCurve (2 * N)) (TateField t)
    (mulByNHom t.tateCurve (2 * N) (xE t.tateCurve)) with hRtdef
  have hRt : mulByNEmb t.tateCurve (2 * N) Rt = τ := tau_eq t.tateCurve (2 * N)
  have htrR : Transcendental K Rt := fun h =>
    transcendental_tau t.tateCurve (hRt ▸ h.algHom (mulByNEmb t.tateCurve (2 * N)))
  have htr : Transcendental K gX := transcendental_of_mem_adjoin gX gY hpt (hmul _) htrR
  set j := pullbackT gX gY hpt htr with hjdef
  set ι : TateField T →ₐ[K] Ω := (mulByNEmb t.tateCurve (2 * N)).comp j with hιdef
  obtain ⟨f, R, hfv, hRv, hord⟩ := thetaLevel_cusp_orders t h12 h2 hs hN hN2 hev T rfl
  have htrans : ∀ (u : Kˣ) (hu : OffOrbit t u) (hum : OffOrbit t (u ^ (2 * N)))
      {g : TateField T} {c : K}, HasTateValue T h12 g (offOrbit_sqrt_pow hs T rfl hum) c →
      HasTateValue t h12 (j g) hu c := fun u hu hum _ _ hg =>
    hasTateValue_pullbackT hpt htr _ (hval u hu hum).1 (hval u hu hum).2.1 hg
  have hjf : j f = Fθ := eq_of_hasTateValue (h12 := h12) hψ0
    (G := fun u => thetaLevel t N hN (u ^ N))
    (fun u hu hψ => htrans u hu (hpts u hu hψ)
      (hfv _ _ (etaleTheta_pow_ne_zero (offOrbit_tatePow hN (hpts u hu hψ)))))
    (fun u hu hψ => (hval u hu (hpts u hu hψ)).2.2)
  have hjR : j R = Rt := by
    refine eq_of_hasTateValue (h12 := h12) hψ0 (G := fun u => t.X (u ^ (2 * N)))
      (fun u hu hψ => ?_) (fun u hu hψ => ?_)
    · have hum := hpts u hu hψ
      have e : (u ^ N) ^ 2 = u ^ (2 * N) := by rw [← pow_mul, mul_comm]
      have hum2 : OffOrbit t ((u ^ N) ^ 2) := by rw [e]; exact hum
      exact (htrans u hu hum (hRv _ _ hum2)).congr (by rw [e])
    · obtain ⟨hum, hv⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu hψ
      exact (hv (xE t.tateCurve)).congr (by
        rw [show xE t.tateCurve = mkT t (C X) from rfl, evalTate_mk_C, eval_X])
  have hιf : ι f = (((η : (F (fieldData (transcendental_tau t.tateCurve) L hL))ˣ) :
      F (fieldData (transcendental_tau t.tateCurve) L hL)) : Ω) := by
    rw [hιdef, AlgHom.comp_apply, hjf, hη]
  have hιR : ι R = τ := by rw [hιdef, AlgHom.comp_apply, hjR, hRt]
  have hFD : F (fieldData (transcendental_tau t.tateCurve) L hL) = L :=
    InfiniteGalois.fixedField_fixingSubgroup L
  have hmem : ∀ g, ι g ∈ F (fieldData (transcendental_tau t.tateCurve) L hL) := fun g => by
    refine (SetLike.ext_iff.mp hFD _).mpr ?_
    rw [hLd, hιdef, AlgHom.comp_apply]
    exact mem_adjoin_image t.tateCurve (2 * N) (pullbackT_mem_adjoin gX gY hpt htr g)
  have hK₀ : K₀ K τ ≤ ι.fieldRange :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ⟨R, hιR⟩)
  have hrange : ∀ z ∈ F (fieldData (transcendental_tau t.tateCurve) L hL), ∃ g, ι g = z := by
    intro z hz
    replace hz := (SetLike.ext_iff.mp hFD z).mp hz
    rw [hLd] at hz
    let M : IntermediateField (K₀ K τ) Ω :=
      ι.fieldRange.toSubfield.toIntermediateField fun x => hK₀ x.2
    have hle : IntermediateField.adjoin (K₀ K τ)
        (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}) ≤ M := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨g, hg, rfl⟩
      rcases hg with rfl | hg
      · exact ⟨algebraMap (TateRing T) (TateField T) (mkT T (C X)), by
          change mulByNEmb t.tateCurve (2 * N)
            (j (algebraMap (TateRing T) (TateField T) (mkT T (C X)))) = _
          rw [hjdef, pullbackT_genX]⟩
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        exact ⟨algebraMap (TateRing T) (TateField T) (mkT T Polynomial.X), by
          change mulByNEmb t.tateCurve (2 * N)
            (j (algebraMap (TateRing T) (TateField T) (mkT T Polynomial.X))) = _
          rw [hjdef, pullbackT_genY]⟩
    exact hle hz
  obtain ⟨p, hp, hneg⟩ := exists_placeOf_comap ι W hk (R := R) (by rw [hιR]; exact hτ)
  have hR0 : R ≠ 0 := by
    rintro rfl
    rw [map_zero] at hιR
    exact transcendental_tau t.tateCurve (hιR ▸ isAlgebraic_zero)
  have hf0 : f ≠ 0 := by
    rintro rfl; rw [map_zero] at hιf; exact coe_unit_ne_zero _ hιf.symm
  have hi : IsIntegral (A₀ K τ) (ι f) := by
    rw [hιf]; exact (CoordRing.isIntegral_coe_iff _).2 η.2.1
  have hi' : IsIntegral (A₀ K τ) (ι f)⁻¹ := by
    have h := (CoordRing.isIntegral_coe_iff _).2 η.2.2
    rwa [Units.val_inv_eq_inv_val, IntermediateField.coe_inv, ← hιf] at h
  obtain ⟨-, hm⟩ := hord hR0 (fun q hq => divisorProj_eq_zero_of_isIntegral ι hR0
    (transcendental_tau t.tateCurve) hιR hf0 hi hi' q hq) p hneg
  refine cuspTameAt_of_order _ η W hk n ι hrange hmem hιf p hp _ rfl ?_
  rcases hm with ⟨-, -, h1⟩ | ⟨-, h1⟩
  · rw [h1]; simp
  · rw [h1]
    obtain ⟨c, hc⟩ := hn
    exact ⟨-c, by rw [hc]; push_cast; ring⟩

end Level

end Iut.EtaleTheta
