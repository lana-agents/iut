/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.RatFunRad
import Iut.Frobenioid.Tempered.PadicEmbed
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The elliptic prime log-divisors and the divisor map of B-an (MR18 T7b)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*
(text `~/iut-scratch/wall/txt/The Etale Theta Function …txt`, cited by line).

The analytic model (route B-an) of the universal combinatorial covering `Ÿ_∞` of the Tate curve is
`𝔾_m^an` with coordinate `Ü` over a complete ultrametric field `K` (`Mero K = Frac E(K)`,
`RatFunMero.lean`). Its special fibre is a chain of projective lines labelled by `ℤ`
([EtTh] l.661–670, l.1022–1027), the component labelled `a` being the circle
`|Ü| = ‖q‖^{a/2} = ‖s‖^a` (`s² = q`; [EtTh] Prop 1.4(ii), l.1326–1328), and its cusps are the
points `Ü` with `Ü² ∈ q^ℤ` (the zeros of `Θ̈`, [EtTh] Prop 1.4(i), l.1322).

## Coefficients `Λ = ℚ`, normalised by `ord(q) = 1`

* [EtTh] Def 3.1(i) (l.5340–5365): log-divisors are divisors on `Z_∞` supported on the special
  fibre and the cusps; `Φ₀` is built from the effective Cartier ones (Def 3.3(iii), l.5552ff).
* [EtTh] Prop 3.2(i) (l.5378–5392): `Div₊(Z_∞)^pf ≅ DIV₊(Z_∞)^pf`, "a direct product of copies of
  `ℚ_{≥0}`, indexed by the cusps … and irreducible components of the special fiber".
* [EtTh] Ex 3.9(iii) (l.6109–6111): the monoid `Φ_W` of the theta Frobenioids is "the
  perfection of the monoid `Φ₀`"; on perf-saturations the prime divisors of the various
  universal combinatorial coverings are identified (l.6144–6149: "chains of copies of the
  projective line").

So the coefficients are `ℚ` (perfection of `ℤ`-valued Cartier divisors). The normalisation of
the component coefficients follows [EtTh] §1: the divisor `D_N` "corresponds to the function
`j ↦ j²·log(q_X)/2N`", i.e. "at the irreducible component labeled `j`, … the schematic zero locus
of `q_X^{j²/2N}`" (l.1028–1034). Thus a component coefficient is measured in units of `ord(q)`:
the coefficient of `f` along the component `a` is `log_{‖q‖} |f|_{‖s‖^a}` (`compOrdR`), equal to
`1` for `f = q`, and the pole divisor of `Θ̈` is `D_1 = (j ↦ j²/2)` ([EtTh] Prop 1.4(i), l.1323).
At a cusp the coefficient is the order of vanishing.

## Main definitions and results

* `Cusp t` (the cusps `Ü² ∈ q^ℤ`) and `EllPrime t = ℤ ⊕ Cusp t`: **the elliptic prime set** (the
  prime log-divisors of `Ÿ_∞`: components ⊕ cusps, as `PrimeDiv`'s `Pₙ ⊕ P_c`).
* `ValueGroupRat q`: the value group of `K` lies in `‖q‖^ℚ` (true for `ℂ_p` and finite `L/ℚ_p`);
  under it `compOrdR` is rational (`exists_compOrdR_eq_rat`).
* `ellDiv t s x : EllPrime t → ℚ`, **the divisor map** `Mero → (P → ℚ)`; `ellDiv_mul`,
  `ellDiv_const`, `ellDiv_const_q` (`ord(q) = 1`), `ellDiv_mono` (`div Ü`).
* `Mero.scale`: the deck transformations `Ü ↦ c·Ü`; `Deck t` (the `c` with `c² ∈ q^ℤ`) acts on
  `EllPrime t` (`a ↦ a + idx c`, `α ↦ c·α`), and **`ellDiv_scale`**:
  `div(f(c·Ü)) = div(f) ∘ (c • ·)`; for `c = s` this is the translation `U ↦ qU`.
* **`ellDiv_thetaDd`**: `div Θ̈ = (a ↦ -a²/2 on components, 1 at every cusp)`.
* The radical layer: `rEllDiv` on radicals `y ∈ R ⊇ Mero K` (`rEllDiv_ι`, `rEllDiv_eq`:
  `div y = div(yⁿ)/n`, `rEllDiv_mul`), and the `l`-th roots of `Θ̈` (`rEllDiv_thetaDd_root`).
* `ellDiv_eq_zero_iff`, `ellDiv_nonneg_iff`: [EtTh] Prop 3.4(ii) in this form for
  log-meromorphic functions (`IsLogMero`).
* `PrimeAct π`: `EllPrime t` with the action of a group `G` through a permutation action
  `π : G →* Perm (EllPrime t)` (the explicit T7c input, until `tempered-fundamental-groups`
  provides the `Π^tp`-set of components and cusps); `PrimeVia ρ` for `π` through the deck
  group, `ρ : G →* Deck t`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open TateCurvesTheta TateParameter Polynomial

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! ### Scaling as a ring homomorphism -/

namespace Entire

/-- `Ü ↦ c·Ü` as a ring endomorphism of `E(K)`. -/
def scaleHom (c : Kˣ) : Entire K →+* Entire K where
  toFun := scale c
  map_one' := Subtype.ext (funext fun u => by rw [coe_scale]; rfl)
  map_mul' f g := Subtype.ext (funext fun u => by
    rw [coe_mul, Pi.mul_apply, coe_scale, coe_scale, coe_scale]; rfl)
  map_zero' := Subtype.ext (funext fun u => by rw [coe_scale]; rfl)
  map_add' f g := Subtype.ext (funext fun u => by
    rw [coe_add, Pi.add_apply, coe_scale, coe_scale, coe_scale]; rfl)

lemma scaleHom_apply (c : Kˣ) (f : Entire K) : scaleHom c f = scale c f := rfl

lemma scale_scale (c d : Kˣ) (f : Entire K) : scale c (scale d f) = scale (d * c) f :=
  Subtype.ext (funext fun u => by rw [coe_scale, coe_scale, coe_scale, mul_assoc])

lemma scale_one (f : Entire K) : scale 1 f = f :=
  Subtype.ext (funext fun u => by rw [coe_scale, one_mul])

lemma scaleHom_injective (c : Kˣ) : Function.Injective (scaleHom (K := K) c) := fun f g h => by
  have := congrArg (scale c⁻¹) h
  rwa [scaleHom_apply, scaleHom_apply, scale_scale, scale_scale, mul_inv_cancel, scale_one,
    scale_one] at this

lemma scale_polyE_lin (c α : Kˣ) :
    scale c (polyE (lin ((c : K) * α))) = (c : K) • polyE (lin (α : K)) :=
  Subtype.ext (funext fun u => by
    rw [coe_scale]
    change (polyE (lin ((c : K) * α)) : Kˣ → K) (c * u) = (c : K) * (polyE (lin (α : K)) : Kˣ → K) u
    rw [coe_polyE, coe_polyE]
    simp only [eval_sub, eval_X, eval_C, Units.val_mul]
    ring)

/-- **Orders under scaling**: `ord_α (f(c·Ü)) = ord_{cα} f`. -/
theorem ord_scale (c : Kˣ) (f : Entire K) (α : Kˣ) : ord (scale c f) α = ord f (c * α) := by
  by_cases hf : f = 0
  · subst hf
    rw [show scale c (0 : Entire K) = 0 from (scaleHom c).map_zero]
    simp [ord]
  obtain ⟨g, hg, hgα⟩ := hasOrderAt_ord hf (c * α)
  refine ord_eq_of_hasOrderAt ⟨(c : K) ^ ord f (c * α) • scale c g, ?_, ?_⟩
  · conv_lhs => rw [hg]
    rw [← scaleHom_apply, map_mul, map_pow, scaleHom_apply, scaleHom_apply, Units.val_mul,
      scale_polyE_lin, smul_pow, smul_mul_assoc, mul_smul_comm]
  · change (c : K) ^ ord f (c * α) * (scale c g : Kˣ → K) α ≠ 0
    rw [coe_scale]
    exact mul_ne_zero (pow_ne_zero _ c.ne_zero) hgα

end Entire

namespace Mero

/-- **The deck transformation `Ü ↦ c·Ü`** on `Mero K = Frac E(K)`. -/
def scale (c : Kˣ) : Mero K →+* Mero K :=
  IsFractionRing.lift (K := Mero K) (g := (algebraMap (Entire K) (Mero K)).comp
    (Entire.scaleHom c)) (ofE_injective.comp (Entire.scaleHom_injective c))

lemma scale_ofE (c : Kˣ) (f : Entire K) : scale c (ofE f) = ofE (Entire.scale c f) :=
  IsFractionRing.lift_algebraMap _ _

lemma scale_div (c : Kˣ) (g h : Entire K) :
    scale c (ofE g / ofE h) = ofE (Entire.scale c g) / ofE (Entire.scale c h) := by
  rw [map_div₀, scale_ofE, scale_ofE]

lemma scale_ne_zero (c : Kˣ) {x : Mero K} (hx : x ≠ 0) : scale c x ≠ 0 :=
  (map_ne_zero_iff _ (scale c).injective).mpr hx

lemma entire_scale_ne_zero (c : Kˣ) {f : Entire K} (hf : f ≠ 0) : Entire.scale c f ≠ 0 :=
  (map_ne_zero_iff _ (Entire.scaleHom_injective c)).mpr hf

lemma ord_scale {x : Mero K} (hx : x ≠ 0) (c α : Kˣ) :
    ord (scale c x) α = ord x (c * α) := by
  have hn := num_ne_zero hx
  have hd := den_ne_zero x
  conv_lhs => rw [eq_num_div_den x]
  rw [scale_div, ord_div (entire_scale_ne_zero c hn) (entire_scale_ne_zero c hd),
    Entire.ord_scale, Entire.ord_scale, ord]

lemma gn_scale (c : Kˣ) (x : Mero K) {r : ℝ} (hr : 0 < r) :
    gn (scale c x) r = gn x (‖(c : K)‖ * r) := by
  have hd := den_ne_zero x
  have hcr : 0 < ‖(c : K)‖ * r := mul_pos (norm_pos_iff.mpr c.ne_zero) hr
  conv_lhs => rw [eq_num_div_den x]
  rw [scale_div, gn_div (entire_scale_ne_zero c hd) hr, Entire.gn_scale, Entire.gn_scale, gn]

end Mero

/-! ### The elliptic prime set -/

variable (t : TateParameter K)

/-- **The cusps of `Ÿ_∞`**: the points `Ü` with `Ü² ∈ q^ℤ` ([EtTh] Prop 1.4(i), l.1322). -/
abbrev Cusp : Type _ := {α : Kˣ // ∃ k : ℤ, (α : K) ^ 2 = (t.q : K) ^ k}

/-- **The elliptic prime set** `P = ℤ ⊕ Cusps`: the irreducible components of the special fibre
of `Ÿ_∞` (labelled by `ℤ`, [EtTh] l.1022–1027) and its cusps ([EtTh] Prop 3.2(i), l.5389–5391). -/
abbrev EllPrime : Type _ := ℤ ⊕ Cusp t

lemma logb_zpow' {b x : ℝ} (hx : 0 < x) (k : ℤ) : Real.logb b (x ^ k) = k * Real.logb b x := by
  rw [← Real.rpow_intCast, Real.logb_rpow_eq_mul_logb_of_pos hx]

/-- `log_{‖q‖}` is the normalisation `ord(q) = 1`. -/
lemma logb_q_self : Real.logb ‖(t.q : K)‖ ‖(t.q : K)‖ = 1 :=
  Real.logb_self_eq_one_iff.mpr ⟨t.norm_q_pos.ne', t.norm_lt_one.ne, by
    have := t.norm_q_pos; intro h; linarith⟩

variable {t}

lemma norm_s_sq {s : Kˣ} (hs : (s : K) ^ 2 = t.q) : ‖(s : K)‖ ^ 2 = ‖(t.q : K)‖ := by
  rw [← norm_pow, hs]

lemma norm_s_pos (s : Kˣ) : 0 < ‖(s : K)‖ := norm_pos_iff.mpr s.ne_zero

/-- `log_{‖q‖} ‖s‖ = 1/2`. -/
lemma logb_q_s {s : Kˣ} (hs : (s : K) ^ 2 = t.q) : Real.logb ‖(t.q : K)‖ ‖(s : K)‖ = 1 / 2 := by
  have h := logb_q_self t
  rw [← norm_s_sq hs, Real.logb_pow] at h
  rw [← norm_s_sq hs]
  push_cast at h
  linarith

variable (t) in
/-- **The coefficient of `x` along the component labelled `a`** (`|Ü| = ‖s‖^a`), in units of
`ord(q)`: `log_{‖q‖} |x|_{‖s‖^a}` ([EtTh] l.1028–1034). -/
def compOrdR (s : Kˣ) (x : Mero K) (a : ℤ) : ℝ :=
  Real.logb ‖(t.q : K)‖ (Mero.gn x (‖(s : K)‖ ^ a))

variable (t) in
/-- **The value group of `K` lies in `‖q‖^ℚ`** (equivalently in `p^ℚ` for `q` with
`‖q‖ ∈ p^ℚ`): the condition under which the component coefficients are rational. It holds for
`ℂ_p` and for finite extensions of `ℚ_p`. -/
def ValueGroupRat : Prop := ∀ c : K, c ≠ 0 → ∃ m : ℚ, Real.logb ‖(t.q : K)‖ ‖c‖ = m

lemma exists_logb_gn_eq_rat (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    {f : Entire K} (hf : f ≠ 0) (a : ℤ) :
    ∃ m : ℚ, Real.logb ‖(t.q : K)‖ (Entire.gn f (‖(s : K)‖ ^ a)) = m := by
  have hr : 0 < ‖(s : K)‖ ^ a := zpow_pos (norm_s_pos s) a
  have hc := Entire.isEntire_coeff f
  have hc0 := Entire.coeff_ne_zero hf
  set k := lo (Entire.coeff f) (‖(s : K)‖ ^ a)
  have hk := tnorm_lo hc hc0 hr
  have hck : Entire.coeff f k ≠ 0 := coeff_lo_ne_zero hc hc0 hr
  obtain ⟨m, hm⟩ := hval _ hck
  refine ⟨m + a * k / 2, ?_⟩
  rw [Entire.gn, ← hk, tnorm, Real.logb_mul (norm_ne_zero_iff.mpr hck)
    (zpow_pos hr k).ne', ← zpow_mul, logb_zpow' (norm_s_pos s), logb_q_s hs, hm]
  push_cast
  ring

lemma exists_compOrdR_eq_rat (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    {x : Mero K} (hx : x ≠ 0) (a : ℤ) : ∃ m : ℚ, compOrdR t s x a = m := by
  have hr : 0 < ‖(s : K)‖ ^ a := zpow_pos (norm_s_pos s) a
  obtain ⟨m, hm⟩ := exists_logb_gn_eq_rat hval hs (Mero.num_ne_zero hx) a
  obtain ⟨m', hm'⟩ := exists_logb_gn_eq_rat hval hs (Mero.den_ne_zero x) a
  refine ⟨m - m', ?_⟩
  rw [compOrdR, Mero.gn, Real.logb_div
    (gnorm_pos (Entire.isEntire_coeff _) (Entire.coeff_ne_zero (Mero.num_ne_zero hx)) hr).ne'
    (gnorm_pos (Entire.isEntire_coeff _) (Entire.coeff_ne_zero (Mero.den_ne_zero x)) hr).ne',
    hm, hm']
  push_cast
  ring

open Classical in
variable (t) in
/-- The component coefficient as an element of `ℚ` (`0` if it is not rational, which does not
happen under `ValueGroupRat`). -/
def compOrd (s : Kˣ) (x : Mero K) (a : ℤ) : ℚ :=
  if h : ∃ m : ℚ, compOrdR t s x a = m then h.choose else 0

lemma compOrd_eq {s : Kˣ} {x : Mero K} {a : ℤ} {m : ℚ} (h : compOrdR t s x a = m) :
    compOrd t s x a = m := by
  have h' : ∃ m : ℚ, compOrdR t s x a = m := ⟨m, h⟩
  rw [compOrd, dif_pos h']
  exact_mod_cast h'.choose_spec.symm.trans h

lemma coe_compOrd (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {x : Mero K}
    (hx : x ≠ 0) (a : ℤ) : (compOrd t s x a : ℝ) = compOrdR t s x a := by
  obtain ⟨m, hm⟩ := exists_compOrdR_eq_rat hval hs hx a
  rw [compOrd_eq hm, hm]

variable (t) in
/-- **The divisor map** `Mero K → (P → ℚ)`: component coefficients (Gauss norms, normalised by
`ord(q) = 1`) and orders at the cusps. -/
def ellDiv (s : Kˣ) (x : Mero K) : EllPrime t → ℚ
  | .inl a => compOrd t s x a
  | .inr α => Mero.ord x α.1

lemma ellDiv_inl (s : Kˣ) (x : Mero K) (a : ℤ) : ellDiv t s x (.inl a) = compOrd t s x a := rfl

lemma ellDiv_inr (s : Kˣ) (x : Mero K) (α : Cusp t) :
    ellDiv t s x (.inr α) = Mero.ord x α.1 := rfl

/-- **The divisor map is a homomorphism.** -/
theorem ellDiv_mul (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {x y : Mero K}
    (hx : x ≠ 0) (hy : y ≠ 0) : ellDiv t s (x * y) = ellDiv t s x + ellDiv t s y := by
  funext p
  rcases p with a | α
  · have hr : 0 < ‖(s : K)‖ ^ a := zpow_pos (norm_s_pos s) a
    simp only [ellDiv_inl, Pi.add_apply]
    have := coe_compOrd hval hs (mul_ne_zero hx hy) a
    rw [compOrdR, Mero.gn_mul _ _ hr, Real.logb_mul (Mero.gn_pos hx hr).ne'
      (Mero.gn_pos hy hr).ne', ← compOrdR, ← compOrdR, ← coe_compOrd hval hs hx,
      ← coe_compOrd hval hs hy] at this
    exact_mod_cast this
  · simp only [ellDiv_inr, Pi.add_apply, Mero.ord_mul hx hy]
    push_cast
    rfl

/-- The divisor of a nonzero scalar: `log_{‖q‖} ‖c‖` on every component, `0` at the cusps. -/
theorem ellDiv_const {s : Kˣ} {c : K} (hc : c ≠ 0) {m : ℚ}
    (hm : Real.logb ‖(t.q : K)‖ ‖c‖ = m) :
    ellDiv t s (Mero.const c) = (Sum.elim (fun _ => m) fun _ => 0 : EllPrime t → ℚ) := by
  funext p
  rcases p with a | α
  · exact compOrd_eq (m := m)
      (by rw [compOrdR, Mero.gn_const c (zpow_pos (norm_s_pos s) a), hm])
  · simp [ellDiv_inr, Mero.ord_const hc]

/-- **The normalisation `ord(q) = 1`**: `div(q)` is `1` on every component, `0` at the cusps. -/
theorem ellDiv_const_q (s : Kˣ) :
    ellDiv t s (Mero.const (t.q : K)) = (Sum.elim (fun _ => 1) fun _ => 0 : EllPrime t → ℚ) :=
  ellDiv_const t.q.ne_zero (by rw [logb_q_self]; norm_num)

/-- `div(s) = div(q^{1/2})` is `1/2` on every component. -/
theorem ellDiv_const_s {s : Kˣ} (hs : (s : K) ^ 2 = t.q) :
    ellDiv t s (Mero.const (s : K)) = (Sum.elim (fun _ => 1 / 2) fun _ => 0 : EllPrime t → ℚ) :=
  ellDiv_const s.ne_zero (by rw [logb_q_s hs]; norm_num)

/-- **`div(Ü)`**: `a/2` on the component `a` (`|Ü| = ‖q‖^{a/2}`), `0` at the cusps. -/
theorem ellDiv_mono {s : Kˣ} (hs : (s : K) ^ 2 = t.q) :
    ellDiv t s (Mero.ofE (Entire.mono 1)) =
      (Sum.elim (fun a : ℤ => (a : ℚ) / 2) fun _ => 0 : EllPrime t → ℚ) := by
  have h0 : (Entire.mono 1 : Entire K) ≠ 0 := fun h => by
    have := congrFun (congrArg Subtype.val h) 1
    simp [Entire.coe_mono] at this
  funext p
  rcases p with a | α
  · simp only [ellDiv_inl, Sum.elim_inl]
    refine compOrd_eq ?_
    rw [compOrdR, Mero.gn_ofE _ (zpow_pos (norm_s_pos s) a), Entire.gn_mono _
      (zpow_pos (norm_s_pos s) a), zpow_one, logb_zpow' (norm_s_pos s), logb_q_s hs]
    push_cast
    ring
  · simp only [ellDiv_inr, Sum.elim_inr, Mero.ord_ofE h0, Int.cast_eq_zero]
    exact_mod_cast (ord_eq_zero_iff h0 α.1).mpr (by
      simp only [Entire.coe_mono, zpow_one]; exact α.1.ne_zero)

/-! ### The deck transformations -/

variable (t) in
/-- **The deck group of `Ÿ_∞`** in the model: the scalings `Ü ↦ c·Ü` preserving the cusps,
`c² ∈ q^ℤ` (`c = ±q^{a/2}`; [EtTh] Prop 1.4(ii), l.1325–1328). -/
def Deck : Subgroup Kˣ where
  carrier := {c | ∃ k : ℤ, ((c : Kˣ) : K) ^ 2 = (t.q : K) ^ k}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro c d ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, by rw [Units.val_mul, mul_pow, hk, hl, zpow_add₀ t.q.ne_zero]⟩
  inv_mem' := by
    rintro c ⟨k, hk⟩
    exact ⟨-k, by rw [Units.val_inv_eq_inv_val, inv_pow, hk, zpow_neg]⟩

lemma zpow_q_injective : Function.Injective fun k : ℤ => (t.q : K) ^ k := fun k l h => by
  have h' : ‖(t.q : K)‖ ^ k = ‖(t.q : K)‖ ^ l := by
    simp only at h; rw [← norm_zpow, ← norm_zpow, h]
  exact zpow_right_injective₀ t.norm_q_pos t.norm_lt_one.ne h'

open Classical in
/-- The translation index of a deck transformation: `c² = q^{idx c}`. -/
def Deck.idx (c : Deck t) : ℤ := c.2.choose

lemma Deck.idx_spec (c : Deck t) : ((c : Kˣ) : K) ^ 2 = (t.q : K) ^ Deck.idx c := c.2.choose_spec

lemma Deck.idx_eq {c : Deck t} {k : ℤ} (h : ((c : Kˣ) : K) ^ 2 = (t.q : K) ^ k) :
    Deck.idx c = k := zpow_q_injective ((Deck.idx_spec c).symm.trans h)

lemma Deck.idx_one : Deck.idx (1 : Deck t) = 0 := Deck.idx_eq (by simp)

lemma Deck.idx_mul (c d : Deck t) : Deck.idx (c * d) = Deck.idx c + Deck.idx d :=
  Deck.idx_eq (by
    rw [Subgroup.coe_mul, Units.val_mul, mul_pow, Deck.idx_spec, Deck.idx_spec,
      zpow_add₀ t.q.ne_zero])

lemma Deck.norm_eq {c : Deck t} {s : Kˣ} (hs : (s : K) ^ 2 = t.q) :
    ‖((c : Kˣ) : K)‖ = ‖(s : K)‖ ^ Deck.idx c := by
  have h : ‖((c : Kˣ) : K)‖ ^ 2 = (‖(s : K)‖ ^ Deck.idx c) ^ 2 := by
    rw [← norm_pow, Deck.idx_spec, norm_zpow, ← norm_s_sq hs, ← zpow_natCast, ← zpow_mul,
      ← zpow_natCast (‖(s : K)‖ ^ Deck.idx c), ← zpow_mul, mul_comm]
  exact (pow_left_inj₀ (norm_nonneg _) (zpow_pos (norm_s_pos s) _).le two_ne_zero).mp h

/-- `c·α` is a cusp for a deck transformation `c` and a cusp `α`. -/
def Cusp.smul (c : Deck t) (α : Cusp t) : Cusp t :=
  ⟨(c : Kˣ) * α.1, by
    obtain ⟨k, hk⟩ := α.2
    exact ⟨Deck.idx c + k, by
      rw [Units.val_mul, mul_pow, Deck.idx_spec, hk, zpow_add₀ t.q.ne_zero]⟩⟩

/-- **The action of the deck group on the elliptic prime set**: `c` moves the component `a` to
`a + idx c` and the cusp `α` to `c·α`. -/
instance : MulAction (Deck t) (EllPrime t) where
  smul c p := Sum.elim (fun a => .inl (a + Deck.idx c)) (fun α => .inr (Cusp.smul c α)) p
  one_smul p := by
    rcases p with a | α
    · change Sum.inl (a + Deck.idx (1 : Deck t)) = _; rw [Deck.idx_one, add_zero]
    · change Sum.inr (Cusp.smul 1 α) = _
      congr 1; exact Subtype.ext (one_mul _)
  mul_smul c d p := by
    rcases p with a | α
    · change Sum.inl (a + Deck.idx (c * d)) = Sum.inl (a + Deck.idx d + Deck.idx c)
      rw [Deck.idx_mul]; congr 1; ring
    · change Sum.inr (Cusp.smul (c * d) α) = Sum.inr (Cusp.smul c (Cusp.smul d α))
      congr 1; exact Subtype.ext (by simp [Cusp.smul, mul_assoc])

lemma Deck.smul_inl (c : Deck t) (a : ℤ) :
    c • (Sum.inl a : EllPrime t) = Sum.inl (a + Deck.idx c) := rfl

lemma Deck.smul_inr (c : Deck t) (α : Cusp t) :
    c • (Sum.inr α : EllPrime t) = Sum.inr (Cusp.smul c α) := rfl

/-- **Compatibility of the divisor map with the deck transformations**: the divisor of
`f(c·Ü)` is the divisor of `f` composed with the action of `c` on `P`. -/
theorem ellDiv_scale {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (c : Deck t) {x : Mero K}
    (hx : x ≠ 0) (p : EllPrime t) :
    ellDiv t s (Mero.scale (c : Kˣ) x) p = ellDiv t s x (c • p) := by
  rcases p with a | α
  · rw [Deck.smul_inl, ellDiv_inl, ellDiv_inl]
    have h : compOrdR t s (Mero.scale (c : Kˣ) x) a = compOrdR t s x (a + Deck.idx c) := by
      rw [compOrdR, compOrdR, Mero.gn_scale _ _ (zpow_pos (norm_s_pos s) a), Deck.norm_eq hs,
        ← zpow_add₀ (norm_s_pos s).ne', add_comm]
    rw [compOrd, compOrd, h]
  · rw [Deck.smul_inr, ellDiv_inr, ellDiv_inr, Mero.ord_scale hx]
    rfl

variable (t) in
/-- The deck generator `s` (`s² = q`, i.e. `U ↦ qU` on `U = Ü²`). -/
def Deck.gen {s : Kˣ} (hs : (s : K) ^ 2 = t.q) : Deck t := ⟨s, 1, by rw [hs, zpow_one]⟩

lemma Deck.idx_gen {s : Kˣ} (hs : (s : K) ^ 2 = t.q) : Deck.idx (Deck.gen t hs) = 1 :=
  Deck.idx_eq (by rw [zpow_one]; exact hs)

/-- **The translation `U ↦ qU`** (`Ü ↦ sÜ`) shifts the components by one. -/
theorem ellDiv_scale_gen {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {x : Mero K} (hx : x ≠ 0) (a : ℤ) :
    ellDiv t s (Mero.scale s x) (.inl a) = ellDiv t s x (.inl (a + 1)) := by
  have := ellDiv_scale hs (Deck.gen t hs) hx (.inl a)
  rwa [Deck.smul_inl, Deck.idx_gen] at this

/-! ### The divisor of `Θ̈` -/

lemma eq_or_eq_neg_of_cusp {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {α : Kˣ} {k : ℤ}
    (hk : (α : K) ^ 2 = (t.q : K) ^ k) : α = s ^ k ∨ α = -(s ^ k) := by
  have h : ((α : K) / (s : K) ^ k) ^ 2 = 1 := by
    rw [div_pow, hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs,
      div_self (zpow_ne_zero _ t.q.ne_zero)]
  have hs0 : (s : K) ^ k ≠ 0 := zpow_ne_zero _ s.ne_zero
  have h' : (α : K) / (s : K) ^ k * ((α : K) / (s : K) ^ k) = 1 := by rw [← sq]; exact h
  rcases mul_self_eq_one_iff.mp h' with h | h
  · left
    exact Units.ext (by rw [Units.val_zpow_eq_zpow_val]; exact (div_eq_one_iff_eq hs0).mp h)
  · right
    refine Units.ext ?_
    rw [Units.val_neg, Units.val_zpow_eq_zpow_val]
    rw [div_eq_iff hs0] at h
    rw [h, neg_one_mul]

/-- **[EtTh] Proposition 1.4(i) in divisor form**: `div Θ̈` is `-a²/2` on the component `a`
(the pole divisor `D_1 = (j ↦ j²/2)`, l.1323, l.1028–1034) and `1` at every cusp. -/
theorem ellDiv_thetaDd (h2 : (2 : K) ≠ 0) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) :
    ellDiv t s (Mero.ofE (thetaDd t)) =
      (Sum.elim (fun a : ℤ => -((a : ℚ) ^ 2) / 2) fun _ => 1 : EllPrime t → ℚ) := by
  funext p
  rcases p with a | α
  · simp only [ellDiv_inl, Sum.elim_inl]
    refine compOrd_eq ?_
    rw [compOrdR, Mero.gn_ofE _ (zpow_pos (norm_s_pos s) a), gn_thetaDd hs,
      logb_zpow' (norm_s_pos s),
      logb_q_s hs]
    push_cast
    ring
  · obtain ⟨k, hk⟩ := α.2
    simp only [ellDiv_inr, Sum.elim_inr, Mero.ord_ofE (thetaDd_ne_zero t)]
    rw [ord_thetaDd_cusp t h2 hs k (eq_or_eq_neg_of_cusp hs hk)]
    rfl

/-! ### The value group hypothesis for `ℂ_p` -/

/-- If all nonzero norms of `K` are rational powers of some `B > 0`, `B ≠ 1`, then
`ValueGroupRat t`. -/
lemma valueGroupRat_of_rpow {B : ℝ} (hB : 0 < B) (hB1 : B ≠ 1)
    (h : ∀ c : K, c ≠ 0 → ∃ m : ℚ, ‖c‖ = B ^ (m : ℝ)) : ValueGroupRat t := by
  obtain ⟨mq, hmq⟩ := h _ t.q.ne_zero
  have hlogB : Real.log B ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hB hB1
  have hmq0 : (mq : ℝ) ≠ 0 := by
    intro h0
    rw [h0, Real.rpow_zero] at hmq
    exact t.norm_lt_one.ne hmq
  intro c hc
  obtain ⟨m, hm⟩ := h c hc
  refine ⟨m / mq, ?_⟩
  rw [Real.logb, hm, hmq, Real.log_rpow hB, Real.log_rpow hB]
  push_cast
  field_simp

/-- **`ValueGroupRat` holds over `ℂ_p`** (value group `p^ℚ`,
`PadicEmbed.exists_norm_eq_rpow_padicComplex`). -/
theorem valueGroupRat_padicComplex (p : ℕ) [Fact p.Prime] (t : TateParameter ℂ_[p]) :
    ValueGroupRat t :=
  valueGroupRat_of_rpow (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)
    (by exact_mod_cast (Fact.out : p.Prime).one_lt.ne')
    (PadicEmbed.exists_norm_eq_rpow_padicComplex p)

/-! ### Log-meromorphic functions and [EtTh] Prop 3.4(ii) in divisor form -/

variable (t) in
/-- **Log-meromorphic functions** ([EtTh] Def 3.1(ii), l.5368–5375): nonzero, with zeros and poles
only at the cusps. -/
def IsLogMero (x : Mero K) : Prop :=
  x ≠ 0 ∧ ∀ α : Kˣ, (¬ ∃ k : ℤ, (α : K) ^ 2 = (t.q : K) ^ k) → Mero.ord x α = 0

lemma IsLogMero.ord_eq_zero_iff {x : Mero K} (hx : IsLogMero t x) {s : Kˣ} :
    (∀ α : Kˣ, Mero.ord x α = 0) ↔ ∀ α : Cusp t, ellDiv t s x (.inr α) = 0 := by
  constructor
  · intro h α
    rw [ellDiv_inr, h, Int.cast_zero]
  · intro h α
    by_cases hα : ∃ k : ℤ, (α : K) ^ 2 = (t.q : K) ^ k
    · have := h ⟨α, hα⟩
      rw [ellDiv_inr] at this
      exact_mod_cast this
    · exact hx.2 α hα

lemma gn_q_zpow_eq {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (a : ℤ) :
    ‖(t.q : K)‖ ^ a = ‖(s : K)‖ ^ (2 * a) := by
  rw [← norm_s_sq hs, ← zpow_natCast, ← zpow_mul]
  norm_num

/-- **[EtTh] Proposition 3.4(ii), kernel, in divisor form**: a log-meromorphic function has
divisor `0` iff it is a scalar of norm `1` (`O_K^×`). -/
theorem ellDiv_eq_zero_iff [IsAlgClosed K] (hval : ValueGroupRat t) {s : Kˣ}
    (hs : (s : K) ^ 2 = t.q) {x : Mero K} (hx : IsLogMero t x) :
    ellDiv t s x = 0 ↔ ∃ c : K, ‖c‖ = 1 ∧ x = Mero.const c := by
  rw [← Mero.ker_iff hx.1 t.norm_q_pos t.norm_lt_one]
  constructor
  · intro h
    refine ⟨(hx.ord_eq_zero_iff (s := s)).mpr fun α => by rw [h]; rfl, fun a => ?_⟩
    have h1 := congrFun h (.inl (2 * a))
    rw [ellDiv_inl, Pi.zero_apply] at h1
    have h2 := coe_compOrd hval hs hx.1 (2 * a)
    rw [h1, Rat.cast_zero, compOrdR, ← gn_q_zpow_eq hs, eq_comm, Real.logb_eq_zero] at h2
    have hpos := Mero.gn_pos hx.1 (zpow_pos t.norm_q_pos a)
    have hq := t.norm_q_pos
    have hq1 := t.norm_lt_one
    rcases h2 with h2 | h2 | h2 | h2 | h2 | h2
    · linarith
    · linarith
    · linarith
    · linarith
    · exact h2
    · linarith
  · intro hker
    obtain ⟨c, hc, rfl⟩ := (Mero.ker_iff hx.1 t.norm_q_pos t.norm_lt_one).mp hker
    have hc0 : c ≠ 0 := fun h => by rw [h, norm_zero] at hc; exact zero_ne_one hc
    rw [ellDiv_const hc0 (m := 0) (by rw [hc, Real.logb_one]; simp)]
    funext p
    rcases p with a | α <;> rfl

/-! ### The radical layer -/

section Rad

variable {R : Type*} [Field R] [Algebra (Mero K) R]

variable (t) in
/-- The component coefficient of a radical: `log_{‖q‖} |y|_{‖s‖^a}`. -/
def rCompOrdR (s : Kˣ) (y : R) (a : ℤ) : ℝ :=
  Real.logb ‖(t.q : K)‖ (Mero.rgn K y (‖(s : K)‖ ^ a))

open Classical in
variable (t) in
/-- The component coefficient of a radical, in `ℚ`. -/
def rCompOrd (s : Kˣ) (y : R) (a : ℤ) : ℚ :=
  if h : ∃ m : ℚ, rCompOrdR t s y a = m then h.choose else 0

lemma rCompOrd_eq {s : Kˣ} {y : R} {a : ℤ} {m : ℚ} (h : rCompOrdR t s y a = m) :
    rCompOrd t s y a = m := by
  have h' : ∃ m : ℚ, rCompOrdR t s y a = m := ⟨m, h⟩
  rw [rCompOrd, dif_pos h']
  exact_mod_cast h'.choose_spec.symm.trans h

variable (t) in
/-- **The divisor of a radical** (ramified coverings, [EtTh] Ex 3.9(iii) perfection):
`ℚ`-valued, `div(y) = div(yⁿ)/n`. -/
def rEllDiv (s : Kˣ) (y : R) : EllPrime t → ℚ
  | .inl a => rCompOrd t s y a
  | .inr α => Mero.rord y α.1

lemma rCompOrdR_eq {s : Kˣ} {y : R} (hy : y ≠ 0) {n : ℕ} (hn : 0 < n) {x : Mero K}
    (hx : Mero.ι R x = y ^ n) (a : ℤ) : rCompOrdR t s y a = compOrdR t s x a / n := by
  have hr : 0 < ‖(s : K)‖ ^ a := zpow_pos (norm_s_pos s) a
  rw [rCompOrdR, Mero.rgn_eq hy hn hx hr, Real.logb_rpow_eq_mul_logb_of_pos
    (Mero.gn_pos (Mero.ne_zero_of_ι_eq hy hx) hr), compOrdR]
  ring

/-- **The divisor of a radical** `y`, `yⁿ = x`: `div(y) = div(x)/n`. -/
theorem rEllDiv_eq (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {y : R}
    (hy : y ≠ 0) {n : ℕ} (hn : 0 < n) {x : Mero K} (hx : Mero.ι R x = y ^ n) :
    rEllDiv t s y = fun p => ellDiv t s x p / n := by
  funext p
  rcases p with a | α
  · refine rCompOrd_eq ?_
    rw [rCompOrdR_eq hy hn hx, ← coe_compOrd hval hs (Mero.ne_zero_of_ι_eq hy hx)]
    push_cast
    rfl
  · exact Mero.rord_eq hy hn hx α.1

/-- The radical divisor extends the divisor map. -/
theorem rEllDiv_ι (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {x : Mero K}
    (hx : x ≠ 0) : rEllDiv t s (Mero.ι R x) = ellDiv t s x := by
  rw [rEllDiv_eq hval hs (Mero.ι_ne_zero hx) one_pos (pow_one _).symm]
  funext p
  simp

lemma ellDiv_pow (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {x : Mero K}
    (hx : x ≠ 0) (n : ℕ) : ellDiv t s (x ^ n) = (n : ℚ) • ellDiv t s x := by
  induction n with
  | zero =>
    have h1 := ellDiv_mul hval hs (one_ne_zero (α := Mero K)) (one_ne_zero (α := Mero K))
    rw [one_mul] at h1
    rw [pow_zero, Nat.cast_zero, zero_smul]
    funext p
    have := congrFun h1 p
    simp only [Pi.add_apply] at this
    simp only [Pi.zero_apply]
    linarith
  | succ n ih =>
    rw [pow_succ, ellDiv_mul hval hs (pow_ne_zero n hx) hx, ih]
    funext p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

/-- **The radical divisor is a homomorphism.** -/
theorem rEllDiv_mul (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {y z : R}
    (hy0 : y ≠ 0) (hz0 : z ≠ 0) (hy : Mero.IsRad K y) (hz : Mero.IsRad K z) :
    rEllDiv t s (y * z) = rEllDiv t s y + rEllDiv t s z := by
  obtain ⟨n, hn, x, hx⟩ := hy
  obtain ⟨m, hm, x', hx'⟩ := hz
  have hx0 := Mero.ne_zero_of_ι_eq hy0 hx
  have hx0' := Mero.ne_zero_of_ι_eq hz0 hx'
  have hxy : Mero.ι R (x ^ m * x' ^ n) = (y * z) ^ (n * m) := by
    rw [Mero.ι_mul, Mero.ι_pow, Mero.ι_pow, hx, hx', mul_pow, ← pow_mul, ← pow_mul,
      mul_comm m n]
  rw [rEllDiv_eq hval hs (mul_ne_zero hy0 hz0) (Nat.mul_pos hn hm) hxy,
    rEllDiv_eq hval hs hy0 hn hx, rEllDiv_eq hval hs hz0 hm hx',
    ellDiv_mul hval hs (pow_ne_zero _ hx0) (pow_ne_zero _ hx0'), ellDiv_pow hval hs hx0,
    ellDiv_pow hval hs hx0']
  funext p
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

/-- **An `l`-th root of `Θ̈`** (I1 Ex 3.2(ii); [EtTh] Thm 5.7) in divisor form:
`-a²/(2l)` on the component `a`, `1/l` at every cusp. -/
theorem rEllDiv_thetaDd_root [IsAlgClosed K] [IsAlgClosed R] (h2 : (2 : K) ≠ 0) {s : Kˣ}
    (hs : (s : K) ^ 2 = t.q) {l : ℕ} (hl : 0 < l) :
    ∃ y : R, y ≠ 0 ∧ Mero.IsRad K y ∧ y ^ l = Mero.ι R (Mero.ofE (thetaDd t)) ∧
      rEllDiv t s y =
        (Sum.elim (fun a : ℤ => -((a : ℚ) ^ 2) / (2 * l)) fun _ => 1 / l : EllPrime t → ℚ) := by
  have hθ := Mero.ofE_ne_zero (thetaDd_ne_zero t)
  obtain ⟨y, hy0, hyr, hy, -, -⟩ := Mero.exists_rad_root (R := R) hθ hl
  refine ⟨y, hy0, hyr, hy, funext fun p => ?_⟩
  have hD := ellDiv_thetaDd h2 hs
  rcases p with a | α
  · simp only [Sum.elim_inl]
    refine rCompOrd_eq ?_
    have hc : compOrdR t s (Mero.ofE (thetaDd t)) a = ((-((a : ℚ) ^ 2) / 2 : ℚ) : ℝ) := by
      rw [compOrdR, Mero.gn_ofE _ (zpow_pos (norm_s_pos s) a), gn_thetaDd hs,
        logb_zpow' (norm_s_pos s), logb_q_s hs]
      push_cast
      ring
    rw [rCompOrdR_eq hy0 hl hy.symm, hc]
    push_cast
    field_simp
  · simp only [Sum.elim_inr]
    change Mero.rord y α.1 = 1 / l
    rw [Mero.rord_eq hy0 hl hy.symm, ← ellDiv_inr (s := s), hD]
    simp

end Rad

/-! ### The action of a group through the deck transformations -/

/-- **`EllPrime t` as a `G`-set through a permutation action `π : G →* Perm (EllPrime t)`.**
The homomorphism `π` is the explicit input standing for the action of `Π^tp` on the components
and cusps of `Ÿ_∞` (MR18 T7c: to be identified with `tempered-fundamental-groups`' `temperedPi1`
once it provides that set); the genuine analytic actions factor through the deck group
(`PrimeVia`) or the Galois × deck group (`EllGal.lean`). -/
def PrimeAct {G : Type*} [Group G] (_π : G →* Equiv.Perm (EllPrime t)) : Type _ := EllPrime t

instance {G : Type*} [Group G] (π : G →* Equiv.Perm (EllPrime t)) : MulAction G (PrimeAct π) :=
  MulAction.compHom (EllPrime t) π

lemma PrimeAct.smul_def {G : Type*} [Group G] (π : G →* Equiv.Perm (EllPrime t)) (g : G)
    (p : PrimeAct π) :
    g • p = (show PrimeAct π from (π g (show EllPrime t from p) : EllPrime t)) := rfl

variable (t) in
/-- The deck group as permutations of the elliptic prime set. -/
abbrev Deck.permHom : Deck t →* Equiv.Perm (EllPrime t) := MulAction.toPermHom _ _

/-- **`EllPrime t` as a `G`-set through `ρ : G →* Deck t`.** -/
abbrev PrimeVia {G : Type*} [Group G] (ρ : G →* Deck t) : Type _ :=
  PrimeAct ((Deck.permHom t).comp ρ)

lemma PrimeVia.smul_def {G : Type*} [Group G] (ρ : G →* Deck t) (g : G) (p : PrimeVia ρ) :
    g • p = (show PrimeVia ρ from (ρ g • (show EllPrime t from p) : EllPrime t)) := rfl

end Iut.Frobenioid.BAn
