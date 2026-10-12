/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Arakelov.LineBundle

/-!
# The fractional ideal of an arithmetic line bundle, and the arithmetic Picard group

For an arithmetic line bundle `L` in idelic form (`Iut/Arakelov/LineBundle.lean`: local
components `a_w ∈ K_w^×` and metrics `r_v`), the integer `ord_w(a_w) = −log_{ℤᵐ⁰}(v_w(a_w))`
(`ArithLineBundle.ord`; Mathlib's valuation on the adic completion has `v(π_w) = exp(−1)`) gives
the **fractional ideal of the divisor of the section**

  `I(L) = ∏_w 𝔭_w^{ord_w(a_w)}`  (`ArithLineBundle.fracIdeal`, a `FractionalIdeal (𝓞 K)⁰ K`).

The lattice of `L` (the sections `x·s` integral at all finite places, `{x : ‖x‖_w ≤ ‖a_w‖_w⁻¹}`)
is `I(L)⁻¹`.

## Results

* `norm_fin_eq`: `‖a_w‖_w = N(𝔭_w)^{−ord_w(a_w)}`, `finDeg_eq_ord`:
  `−log‖a_w‖_w = ord_w(a_w)·log N(𝔭_w)`;
* `count_fracIdeal`: `ord_𝔭(I(L)) = ord_w(a_w)` (Mathlib's `FractionalIdeal.count`), for **all**
  bundles;
* **`finsum_finDeg_eq_log_absNorm`**: the finite part of the degree is
  `Σ_w −log‖a_w‖_w = log N(I(L)) = −log N(I(L)⁻¹)` (`finsum_finDeg_eq_neg_log_absNorm_inv`; sign
  convention of `LineBundle.lean`: the degree of `L` is minus the log-norm of its lattice), with
  `FractionalIdeal.absNorm`, `FractionalIdeal.coeIdeal_absNorm` and `Ideal.absNorm`;
  hence **`deg_eq_log_absNorm`**: `deg L = log N(I(L)) − Σ_v [K_v : ℝ]·log r_v`;
* `fracIdeal_principal`: `I(principal x) = (x)` (Mathlib's
  `finprod_heightOneSpectrum_factorization_principal_fraction`); `fracIdeal_mul`; this recovers
  `finsum_finDeg_principal_eq_absNorm`;
* **the arithmetic Picard group**: `ArithLineBundle.Rel` (`M ≈ L` iff `M` and `L·(x)` have the same
  local norms and metrics for some `x ∈ K^×`: isomorphic bundles, or a change of the chosen
  section) is an equivalence relation (`setoid`); `ArithPic K` is the quotient, and the degree
  and the normalized degree descend to it (`ArithPic.deg`, `ArithPic.degNorm`, by the product
  formula); **`ArithPic.idealClass`**: the class of `I(L)` in `ClassGroup (𝓞 K)` is well defined
  on `ArithPic K` (`idealClass_principal`: principal bundles have trivial class).
-/

namespace Iut

namespace Arakelov

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The absolute norm `N(𝔭_w) = #(𝓞_K/𝔭_w)` of the prime of a finite place, as a real number. -/
noncomputable def primeNorm (w : FinitePlace K) : ℝ := (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ)

lemma one_lt_primeNorm (w : FinitePlace K) : 1 < primeNorm w := by
  unfold primeNorm
  exact_mod_cast HeightOneSpectrum.one_lt_absNorm w.maximalIdeal

lemma primeNorm_pos (w : FinitePlace K) : 0 < primeNorm w := one_pos.trans (one_lt_primeNorm w)

/-- `‖x‖_w = N(𝔭_w)^{log v_w(x)}` on `K_w^×`. -/
lemma norm_eq_primeNorm_zpow (w : FinitePlace K) (x : completionAt K w) (hx : x ≠ 0) :
    ‖x‖ = primeNorm w ^ WithZero.log (Valued.v x) := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  set m := WithZero.log (Valued.v x) with hm
  have hm' : Valued.v x = WithZero.exp m := (WithZero.exp_log hv).symm
  rw [FinitePlace.norm_def, hm', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have h : (WithZero.unzero (WithZero.exp_ne_zero (a := m))).toAdd = m := rfl
  rw [h, NNReal.coe_zpow, NNReal.coe_natCast]
  rfl

namespace ArithLineBundle

/-- **The order `ord_w(a_w) ∈ ℤ`** of the finite component (`v_w(a_w) = exp(−ord_w(a_w))`). -/
noncomputable def ord (L : ArithLineBundle K) (w : FinitePlace K) : ℤ :=
  -WithZero.log (Valued.v (L.fin w))

lemma norm_fin_eq (L : ArithLineBundle K) (w : FinitePlace K) :
    ‖L.fin w‖ = primeNorm w ^ (-L.ord w) := by
  rw [norm_eq_primeNorm_zpow w _ (L.fin_ne_zero w), ord, neg_neg]

/-- `−log‖a_w‖_w = ord_w(a_w)·log N(𝔭_w)`. -/
lemma finDeg_eq_ord (L : ArithLineBundle K) (w : FinitePlace K) :
    L.finDeg w = L.ord w * Real.log (primeNorm w) := by
  rw [finDeg, norm_fin_eq, Real.log_zpow]
  push_cast
  ring

/-- The order is determined by the local norm. -/
lemma ord_eq_of_norm_eq (L M : ArithLineBundle K) (w : FinitePlace K)
    (h : ‖L.fin w‖ = ‖M.fin w‖) : L.ord w = M.ord w := by
  have h1 : L.finDeg w = M.finDeg w := by rw [finDeg, finDeg, h]
  rw [finDeg_eq_ord, finDeg_eq_ord] at h1
  have hl : Real.log (primeNorm w) ≠ 0 := (Real.log_pos (one_lt_primeNorm w)).ne'
  exact_mod_cast mul_right_cancel₀ hl h1

lemma ord_eq_zero_of_norm (L : ArithLineBundle K) (w : FinitePlace K) (h : ‖L.fin w‖ = 1) :
    L.ord w = 0 := by
  have h1 : L.finDeg w = 0 := by rw [finDeg, h, Real.log_one, neg_zero]
  rw [finDeg_eq_ord] at h1
  have hl : Real.log (primeNorm w) ≠ 0 := (Real.log_pos (one_lt_primeNorm w)).ne'
  exact_mod_cast (mul_eq_zero.mp h1).resolve_right hl

lemma finite_support_ord (L : ArithLineBundle K) : (Function.support L.ord).Finite :=
  L.finite_fin.subset fun w hw => by
    by_contra h
    simp only [Set.mem_setOf_eq, not_not] at h
    exact hw (L.ord_eq_zero_of_norm w h)

/-- The factor `𝔭_w^{ord_w(a_w)}`. -/
noncomputable def idealFactor (L : ArithLineBundle K) (w : FinitePlace K) :
    FractionalIdeal (𝓞 K)⁰ K :=
  (w.maximalIdeal.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ L.ord w

lemma hasFiniteMulSupport_idealFactor (L : ArithLineBundle K) :
    Function.HasFiniteMulSupport L.idealFactor :=
  L.finite_support_ord.subset fun w hw => by
    rw [Function.mem_mulSupport] at hw
    rw [Function.mem_support]
    intro h
    exact hw (by rw [idealFactor, h, zpow_zero])

/-- **The fractional ideal of the divisor of the section**: `I(L) = ∏_w 𝔭_w^{ord_w(a_w)}`. -/
noncomputable def fracIdeal (L : ArithLineBundle K) : FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ w, L.idealFactor w

/-- `I(L)` indexed by the height-one primes of `𝓞_K`. -/
lemma fracIdeal_eq_finprod_heightOneSpectrum (L : ArithLineBundle K) :
    L.fracIdeal = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ L.ord (FinitePlace.mk v) := by
  rw [fracIdeal, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum]
  refine finprod_congr fun w => ?_
  simp [idealFactor, FinitePlace.mk_maximalIdeal]

/-- **`ord_𝔭(I(L)) = ord_w(a_w)`** at every height-one prime `𝔭 = 𝔭_w`. -/
theorem count_fracIdeal (L : ArithLineBundle K) (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v L.fracIdeal = L.ord (FinitePlace.mk v) := by
  rw [fracIdeal_eq_finprod_heightOneSpectrum]
  refine FractionalIdeal.count_finprod K v _ ?_
  rw [Filter.eventually_cofinite]
  refine (L.finite_support_ord.preimage
    (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn)).subset fun v hv => ?_
  exact hv

/-- **The norm of `I(L)`**: `N(I(L)) = ∏_w N(𝔭_w)^{ord_w(a_w)}`. -/
theorem absNorm_fracIdeal (L : ArithLineBundle K) :
    ((FractionalIdeal.absNorm L.fracIdeal : ℚ) : ℝ) = ∏ᶠ w, primeNorm w ^ L.ord w := by
  have hq : Function.HasFiniteMulSupport fun w : FinitePlace K =>
      FractionalIdeal.absNorm (L.idealFactor w) :=
    L.hasFiniteMulSupport_idealFactor.comp (map_one _)
  rw [fracIdeal, map_finprod _ L.hasFiniteMulSupport_idealFactor]
  change (Rat.castHom ℝ) _ = _
  rw [map_finprod (Rat.castHom ℝ) hq]
  refine finprod_congr fun w => ?_
  simp [idealFactor, map_zpow₀, FractionalIdeal.coeIdeal_absNorm, primeNorm]

lemma absNorm_fracIdeal_pos (L : ArithLineBundle K) :
    (0 : ℝ) < (FractionalIdeal.absNorm L.fracIdeal : ℚ) := by
  rw [absNorm_fracIdeal]
  exact finprod_induction (fun y => 0 < y) one_pos (fun _ _ => mul_pos)
    fun w => zpow_pos (primeNorm_pos w) _

lemma fracIdeal_ne_zero (L : ArithLineBundle K) : L.fracIdeal ≠ 0 := by
  intro h
  have := L.absNorm_fracIdeal_pos
  rw [h, map_zero, Rat.cast_zero] at this
  exact lt_irrefl _ this

/-- **The finite part of the degree is the log-norm of `I(L)`**:
`Σ_w −log‖a_w‖_w = Σ_w ord_w(a_w)·log N(𝔭_w) = log N(I(L))`. -/
theorem finsum_finDeg_eq_log_absNorm (L : ArithLineBundle K) :
    ∑ᶠ w, L.finDeg w = Real.log ((FractionalIdeal.absNorm L.fracIdeal : ℚ) : ℝ) := by
  have hf : Function.HasFiniteMulSupport fun w => primeNorm w ^ L.ord w :=
    L.finite_support_ord.subset fun w hw => by
      rw [Function.mem_mulSupport] at hw
      rw [Function.mem_support]
      intro h
      exact hw (by rw [h, zpow_zero])
  rw [absNorm_fracIdeal, ← finsum_log_eq_log_finprod hf fun w => zpow_pos (primeNorm_pos w) _]
  refine finsum_congr fun w => ?_
  rw [finDeg_eq_ord, Real.log_zpow]

/-- **The finite part of the degree is minus the log-norm of the lattice `I(L)⁻¹`.** -/
theorem finsum_finDeg_eq_neg_log_absNorm_inv (L : ArithLineBundle K) :
    ∑ᶠ w, L.finDeg w = -Real.log ((FractionalIdeal.absNorm L.fracIdeal⁻¹ : ℚ) : ℝ) := by
  rw [finsum_finDeg_eq_log_absNorm, map_inv₀, Rat.cast_inv, Real.log_inv, neg_neg]

/-- **`deg L = log N(I(L)) − Σ_v [K_v : ℝ]·log r_v`.** -/
theorem deg_eq_log_absNorm (L : ArithLineBundle K) :
    L.deg = Real.log ((FractionalIdeal.absNorm L.fracIdeal : ℚ) : ℝ) -
      ∑ v, (v.mult : ℝ) * Real.log (L.inf v) := by
  rw [deg, finsum_finDeg_eq_log_absNorm, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  rfl

lemma ord_mul (L M : ArithLineBundle K) (w : FinitePlace K) :
    (L.mul M).ord w = L.ord w + M.ord w := by
  have h := L.finDeg_mul M w
  rw [finDeg_eq_ord, finDeg_eq_ord, finDeg_eq_ord, ← add_mul] at h
  have hl : Real.log (primeNorm w) ≠ 0 := (Real.log_pos (one_lt_primeNorm w)).ne'
  exact_mod_cast mul_right_cancel₀ hl h

/-- `I(L·M) = I(L)·I(M)`. -/
theorem fracIdeal_mul (L M : ArithLineBundle K) :
    (L.mul M).fracIdeal = L.fracIdeal * M.fracIdeal := by
  rw [fracIdeal, fracIdeal, fracIdeal, ← finprod_mul_distrib L.hasFiniteMulSupport_idealFactor
    M.hasFiniteMulSupport_idealFactor]
  refine finprod_congr fun w => ?_
  have hp : (w.maximalIdeal.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr w.maximalIdeal.ne_bot
  rw [idealFactor, idealFactor, idealFactor, ord_mul, zpow_add₀ hp]

/-- **`I(principal x) = (x)`**: the divisor of the principal bundle is the principal fractional
ideal. -/
theorem fracIdeal_principal (x : K) (hx : x ≠ 0) :
    (principal x hx).fracIdeal = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (𝓞 K)⁰ x
  change IsLocalization.mk' K n d = x at hnd
  subst hnd
  have hn : n ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization_principal_fraction hn d,
    fracIdeal_eq_finprod_heightOneSpectrum]
  refine finprod_congr fun v => ?_
  congr 1
  have hd : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  change -WithZero.log (Valued.v (FinitePlace.embedding (FinitePlace.mk v).maximalIdeal
    (IsLocalization.mk' K n d))) = _
  rw [FinitePlace.maximalIdeal_mk, FinitePlace.embedding_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_mk',
    HeightOneSpectrum.intValuation_if_neg _ hn, HeightOneSpectrum.intValuation_if_neg _ hd,
    WithZero.log_div WithZero.exp_ne_zero WithZero.exp_ne_zero, WithZero.log_exp,
    WithZero.log_exp]
  ring

/-! ### The arithmetic Picard group -/

/-- **Isomorphism of arithmetic line bundles** (or a change of the chosen section): `M ≈ L` iff
`M` has the local norms and metrics of `L·(x)` for some `x ∈ K^×`. -/
def Rel (L M : ArithLineBundle K) : Prop :=
  ∃ x : K, x ≠ 0 ∧ (∀ w : FinitePlace K, ‖M.fin w‖ = ‖L.fin w‖ * w x) ∧
    ∀ v : InfinitePlace K, M.inf v = L.inf v * v x

lemma rel_iff_mul_principal (L M : ArithLineBundle K) :
    Rel L M ↔ ∃ (x : K) (hx : x ≠ 0), (∀ w, ‖M.fin w‖ = ‖(L.mul (principal x hx)).fin w‖) ∧
      ∀ v, M.inf v = (L.mul (principal x hx)).inf v := by
  constructor
  · rintro ⟨x, hx, hf, hi⟩
    refine ⟨x, hx, fun w => ?_, hi⟩
    rw [hf w]
    simp [mul, principal, norm_mul, FinitePlace.norm_embedding_eq]
  · rintro ⟨x, hx, hf, hi⟩
    refine ⟨x, hx, fun w => ?_, hi⟩
    rw [hf w]
    simp [mul, principal, norm_mul, FinitePlace.norm_embedding_eq]

/-- `Rel` is an equivalence relation. -/
def setoid : Setoid (ArithLineBundle K) where
  r := Rel
  iseqv := by
    refine ⟨fun L => ⟨1, one_ne_zero, fun w => by simp, fun v => by simp⟩, ?_, ?_⟩
    · rintro L M ⟨x, hx, hf, hi⟩
      refine ⟨x⁻¹, inv_ne_zero hx, fun w => ?_, fun v => ?_⟩
      · have hw : w x ≠ 0 := (FinitePlace.pos_iff.mpr hx).ne'
        rw [hf w, map_inv₀, mul_assoc, mul_inv_cancel₀ hw, mul_one]
      · have hv : v x ≠ 0 := (InfinitePlace.pos_iff.mpr hx).ne'
        rw [hi v, map_inv₀, mul_assoc, mul_inv_cancel₀ hv, mul_one]
    · rintro L M N ⟨x, hx, hf, hi⟩ ⟨y, hy, hf', hi'⟩
      refine ⟨x * y, mul_ne_zero hx hy, fun w => ?_, fun v => ?_⟩
      · rw [hf' w, hf w, map_mul, mul_assoc]
      · rw [hi' v, hi v, map_mul, mul_assoc]

/-- **Isomorphic bundles have the same degree** (product formula). -/
theorem deg_eq_of_rel {L M : ArithLineBundle K} (h : Rel L M) : M.deg = L.deg := by
  obtain ⟨x, hx, hf, hi⟩ := (rel_iff_mul_principal L M).mp h
  rw [deg_congr M _ hf hi, deg_mul_principal]

/-- **The ideal classes agree**: `I(M) = I(L)·(x)` for `M ≈ L`. -/
theorem fracIdeal_eq_of_rel {L M : ArithLineBundle K} (h : Rel L M) :
    ∃ x : K, x ≠ 0 ∧ M.fracIdeal = L.fracIdeal * FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
  obtain ⟨x, hx, hf, _⟩ := (rel_iff_mul_principal L M).mp h
  refine ⟨x, hx, ?_⟩
  rw [← fracIdeal_principal x hx, ← fracIdeal_mul, fracIdeal, fracIdeal]
  refine finprod_congr fun w => ?_
  rw [idealFactor, idealFactor, ord_eq_of_norm_eq M _ w (hf w)]

/-- The ideal class `[I(L)] ∈ Cl(𝓞_K)`. -/
noncomputable def idealClass (L : ArithLineBundle K) : ClassGroup (𝓞 K) :=
  ClassGroup.mk (K := K) (Units.mk0 L.fracIdeal L.fracIdeal_ne_zero)

lemma classGroup_mk_spanSingleton (x : K) (hx : x ≠ 0) :
    ClassGroup.mk (K := K) (Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)) = 1 := by
  rw [ClassGroup.mk_eq_one_iff, Units.val_mk0, FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨x, rfl⟩⟩

theorem idealClass_eq_of_rel {L M : ArithLineBundle K} (h : Rel L M) :
    M.idealClass = L.idealClass := by
  obtain ⟨x, hx, hI⟩ := fracIdeal_eq_of_rel h
  have hu : Units.mk0 M.fracIdeal M.fracIdeal_ne_zero =
      Units.mk0 L.fracIdeal L.fracIdeal_ne_zero *
        Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) := by
    ext
    simp [hI]
  rw [idealClass, idealClass, hu, map_mul, classGroup_mk_spanSingleton x hx, mul_one]

/-- **Principal bundles have trivial ideal class.** -/
theorem idealClass_principal (x : K) (hx : x ≠ 0) : (principal x hx).idealClass = 1 := by
  have hu : Units.mk0 (principal x hx).fracIdeal (principal x hx).fracIdeal_ne_zero =
      Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) := by
    ext
    simp [fracIdeal_principal]
  rw [idealClass, hu, classGroup_mk_spanSingleton x hx]

end ArithLineBundle

variable (K) in
/-- **The arithmetic Picard group** (as a set): arithmetic line bundles modulo isomorphism
(equivalently, modulo principal bundles). -/
def ArithPic : Type u := Quotient (ArithLineBundle.setoid (K := K))

namespace ArithPic

/-- The class of a bundle. -/
def mk (L : ArithLineBundle K) : ArithPic K := Quotient.mk _ L

/-- **The degree on the arithmetic Picard group** (well defined by the product formula). -/
noncomputable def deg : ArithPic K → ℝ :=
  Quotient.lift ArithLineBundle.deg fun _ _ h => (ArithLineBundle.deg_eq_of_rel h).symm

/-- The normalized degree on the arithmetic Picard group. -/
noncomputable def degNorm (P : ArithPic K) : ℝ := P.deg / Module.finrank ℚ K

@[simp] lemma deg_mk (L : ArithLineBundle K) : (mk L).deg = L.deg := rfl

@[simp] lemma degNorm_mk (L : ArithLineBundle K) : (mk L).degNorm = L.degNorm := rfl

/-- **The ideal class on the arithmetic Picard group**: `[L] ↦ [I(L)] ∈ Cl(𝓞_K)`. -/
noncomputable def idealClass : ArithPic K → ClassGroup (𝓞 K) :=
  Quotient.lift ArithLineBundle.idealClass fun _ _ h =>
    (ArithLineBundle.idealClass_eq_of_rel h).symm

@[simp] lemma idealClass_mk (L : ArithLineBundle K) : (mk L).idealClass = L.idealClass := rfl

/-- Principal bundles are trivial in `ArithPic K`. -/
lemma mk_principal (x : K) (hx : x ≠ 0) :
    mk (ArithLineBundle.principal x hx) = mk ArithLineBundle.one :=
  Quotient.sound ⟨x⁻¹, inv_ne_zero hx, fun w => by
    simp only [ArithLineBundle.one, ArithLineBundle.principal, FinitePlace.norm_embedding_eq,
      map_inv₀, norm_one]
    rw [mul_inv_cancel₀ (FinitePlace.pos_iff.mpr hx).ne'], fun v => by
    simp only [ArithLineBundle.one, ArithLineBundle.principal, map_inv₀]
    rw [mul_inv_cancel₀ (InfinitePlace.pos_iff.mpr hx).ne']⟩

end ArithPic

end Arakelov

end Iut
