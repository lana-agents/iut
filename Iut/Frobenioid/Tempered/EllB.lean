/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered
import Iut.Frobenioid.Tempered.EllDiv

/-!
# `B₀` as the Galois invariants of the radical layer (MR18 T10 preparation, route B-an)

[EtTh] Def 3.3(iii) and Ex 3.9(iii): for a connected tempered covering `Y = G/H`, `B(Y)` consists
of the `Gal(Z_∞/Y)`-invariant log-meromorphic functions on the coverings `Z_∞`, and the divisor
map `B → Φ^gp` takes values in the `Gal`-invariant divisors. In route B-an every such function
is (up to `L^×`) a radical of a meromorphic function on `𝔾_m^an` (MR18 plan, run 7), so we model
`B(G/H)` inside a field `R ⊇ Mero K` (the radical layer, `RatFunRad.lean`) as

  `B(G/H) = {y ∈ R^× radical, zeros and poles only at cusps, fixed by H}`,

with the divisor `rEllDiv` (`EllDiv.lean`) transported to `Φ^gp(G/H)` =
`G`-invariant functions `(G/H) × P → ℚ`, `P = ℤ ⊕ Cusps`.

## Explicit inputs (MR18 T7c / T10 obligations)

* `π : G →* Equiv.Perm (EllPrime t)`: the action of `G = Π^tp` on the prime set `P`
  (`PrimeAct π`; through the deck group `π = Deck.permHom ∘ ρ`, through the Galois × deck group
  `π = galDeckPerm ∘ γ`, `EllGal.lean`);
* `[MulSemiringAction G R]`: the action of `G` on the radical layer (Galois and deck
  transformations; its extension from `Mero K` to the algebraic closure is not canonical);
* `hact : ActCompat t s π R`: the two actions are compatible — `G` maps log-meromorphic radicals
  to log-meromorphic radicals and transports divisors along `π`. This is a hypothesis on the
  input data, to be discharged when the actions are constructed (T7c). For the deck action
  `deckAction ρ` of `G` on the unramified layer `R = Mero K` it is a theorem
  (`actCompat_deck`, from `ellDiv_scale`), and for the Galois × deck action as well
  (`actCompat_galDeck`, `EllGal.lean`).

## Main definitions and results

* `radB t s π R : GrpOn (OrbitObj G)` with `radB.obj (G/H)` the `H`-fixed log-meromorphic
  radicals (additively), pull-backs `y ↦ g₀ • y` along `G/H → G/H'`, `gH ↦ g g₀ H'`;
* `radDiv : DivHom (radB …) (PrimeDiv.divMonoid G (PrimeAct π) ℚ).toGrpOn`, **the divisor map**;
* `radData : TemperedFrobenioidData G`, `radData_isFrobenioid`;
* `radDiv_eq_zero_iff`: **the kernel of the divisor map is `O_K^×`** ([EtTh] Prop 3.4(ii), on
  the radical layer, `K` algebraically closed): the genuine version of the arbitrary unit group
  `U` of `TateTheta.lean`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open CategoryTheory TateCurvesTheta

universe u

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  (t : TateParameter K) (s : Kˣ)
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (π : G →* Equiv.Perm (EllPrime t))
  (R : Type u) [Field R] [Algebra (Mero K) R] [MulSemiringAction G R]

variable {R} in
/-- A radical is **log-meromorphic** if its zeros and poles lie at the cusps
([EtTh] Def 3.1(ii)). -/
def IsLogRad (y : R) : Prop :=
  ∀ α : Kˣ, (¬ ∃ k : ℤ, (α : K) ^ 2 = (t.q : K) ^ k) → Mero.rord y α = 0

/-- **The compatibility of the actions of `G` on `R` and on `P = PrimeAct π`** (explicit input):
`g` maps nonzero log-meromorphic radicals to such, and `div(g • y) = div(y) ∘ g⁻¹`. -/
def ActCompat : Prop :=
  ∀ (g : G) (y : R), y ≠ 0 → Mero.IsRad K y → IsLogRad t y →
    Mero.IsRad K (g • y) ∧ IsLogRad t (g • y) ∧
      ∀ p : PrimeAct π, rEllDiv t s (g • y) p = rEllDiv t s y (show EllPrime t from g⁻¹ • p)

/-! ### Elementary facts -/

variable {t R}

lemma isRad_one : Mero.IsRad K (1 : R) := ⟨1, one_pos, 1, by rw [Mero.ι, map_one, pow_one]⟩

lemma rord_one (α : Kˣ) : Mero.rord (1 : R) α = 0 := by
  have h := Mero.rord_ι (R := R) (one_ne_zero (α := Mero K)) α
  rw [Mero.ι, map_one] at h
  rw [h, Mero.ord_one, Int.cast_zero]

lemma isRad_inv {y : R} (hy : Mero.IsRad K y) : Mero.IsRad K y⁻¹ := by
  obtain ⟨n, hn, x, hx⟩ := hy
  exact ⟨n, hn, x⁻¹, by rw [Mero.ι, map_inv₀, ← Mero.ι, hx, inv_pow]⟩

lemma rord_inv {y : R} (hy0 : y ≠ 0) (hy : Mero.IsRad K y) (α : Kˣ) :
    Mero.rord y⁻¹ α = -Mero.rord y α := by
  have h := Mero.rord_mul hy0 (inv_ne_zero hy0) hy (isRad_inv hy) α
  rw [mul_inv_cancel₀ hy0, rord_one] at h
  linarith

variable (t) in
lemma isLogRad_one : IsLogRad t (1 : R) := fun α _ => rord_one α

lemma IsLogRad.mul {y z : R} (hy0 : y ≠ 0) (hz0 : z ≠ 0) (hy : Mero.IsRad K y)
    (hz : Mero.IsRad K z) (hly : IsLogRad t y) (hlz : IsLogRad t z) : IsLogRad t (y * z) :=
  fun α hα => by rw [Mero.rord_mul hy0 hz0 hy hz, hly α hα, hlz α hα, add_zero]

lemma IsLogRad.inv {y : R} (hy0 : y ≠ 0) (hy : Mero.IsRad K y) (hly : IsLogRad t y) :
    IsLogRad t y⁻¹ := fun α hα => by rw [rord_inv hy0 hy, hly α hα, neg_zero]

/-! ### The groups `B(G/H)` -/

variable (t) in
/-- **`B(G/H)`**: the nonzero log-meromorphic radicals fixed by `H`. -/
def radSub (H : Subgroup G) : Subgroup Rˣ where
  carrier := {u | Mero.IsRad K (u : R) ∧ IsLogRad t (u : R) ∧ ∀ h ∈ H, h • (u : R) = u}
  one_mem' := ⟨isRad_one, isLogRad_one t, fun h _ => smul_one h⟩
  mul_mem' {u v} hu hv := ⟨hu.1.mul hv.1,
    IsLogRad.mul u.ne_zero v.ne_zero hu.1 hv.1 hu.2.1 hv.2.1,
    fun h hh => by rw [Units.val_mul, smul_mul', hu.2.2 h hh, hv.2.2 h hh]⟩
  inv_mem' {u} hu := ⟨by rw [Units.val_inv_eq_inv_val]; exact isRad_inv hu.1,
    by rw [Units.val_inv_eq_inv_val]; exact IsLogRad.inv u.ne_zero hu.1 hu.2.1,
    fun h hh => by rw [Units.val_inv_eq_inv_val, smul_inv'', hu.2.2 h hh]⟩

/-- `a • y = b • y` for `y` fixed by `H` and `aH = bH`. -/
lemma smul_eq_of_mk_eq {H : Subgroup G} {y : R} (hy : ∀ h ∈ H, h • y = y) {a b : G}
    (hab : (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk b) : a • y = b • y := by
  have hm : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
  rw [show b = a * (a⁻¹ * b) by group, mul_smul, hy _ hm]

/-- A representative `g₀` of `f(H)`: `f(gH) = g g₀ H'`. -/
def rep {A B : OrbitObj G} (f : A ⟶ B) : G := Quotient.out (f.toFun (QuotientGroup.mk 1))

lemma mk_rep {A B : OrbitObj G} (f : A ⟶ B) :
    (QuotientGroup.mk (rep f) : G ⧸ B.H) = f.toFun (QuotientGroup.mk 1) :=
  QuotientGroup.out_eq' _

lemma apply_mk_rep {A B : OrbitObj G} (f : A ⟶ B) (g : G) :
    f.toFun (QuotientGroup.mk g) = QuotientGroup.mk (g * rep f) :=
  OrbitHom.apply_mk_of_eq f (mk_rep f).symm g

lemma conj_rep_mem {A B : OrbitObj G} (f : A ⟶ B) {h : G} (hh : h ∈ A.H) :
    (rep f)⁻¹ * h * rep f ∈ B.H := by
  have e : (QuotientGroup.mk h : G ⧸ A.H) = QuotientGroup.mk 1 :=
    QuotientGroup.eq.mpr (by simpa using A.H.inv_mem hh)
  have := congrArg f.toFun e
  rw [apply_mk_rep, apply_mk_rep, one_mul] at this
  have := QuotientGroup.eq.mp this.symm
  rwa [← mul_assoc] at this

lemma smul_rep_fix {A B : OrbitObj G} (f : A ⟶ B) {y : R} (hy : ∀ h ∈ B.H, h • y = y) :
    ∀ h ∈ A.H, h • (rep f • y) = rep f • y := fun h hh => by
  rw [← mul_smul, show h * rep f = rep f * ((rep f)⁻¹ * h * rep f) by group, mul_smul,
    hy _ (conj_rep_mem f hh)]

/-- The pull-back `B(G/H') → B(G/H)`, `y ↦ g₀ • y`. -/
def radPb (hact : ActCompat t s π R) {A B : OrbitObj G} (f : A ⟶ B) :
    radSub t (R := R) B.H →* radSub t (R := R) A.H where
  toFun u := ⟨Units.map (MulSemiringAction.toRingHom G R (rep f)).toMonoidHom u, by
    obtain ⟨h1, h2, -⟩ := hact (rep f) ((u : Rˣ) : R) (u.1.ne_zero) u.2.1 u.2.2.1
    exact ⟨h1, h2, smul_rep_fix f u.2.2.2⟩⟩
  map_one' := Subtype.ext (Units.ext (smul_one _))
  map_mul' u v := Subtype.ext (Units.ext (smul_mul' _ _ _))

lemma coe_radPb (hact : ActCompat t s π R) {A B : OrbitObj G} (f : A ⟶ B)
    (u : radSub t (R := R) B.H) : ((radPb s π hact f u : Rˣ) : R) = rep f • ((u : Rˣ) : R) :=
  rfl

/-- The underlying element of `R` of an element of `B(G/H)`. -/
abbrev rv {H : Subgroup G} (x : Additive (radSub t (R := R) H)) : R :=
  (((Additive.toMul x : radSub t (R := R) H) : Rˣ) : R)

lemma rv_ne_zero {H : Subgroup G} (x : Additive (radSub t (R := R) H)) : rv x ≠ 0 :=
  (Additive.toMul x : radSub t (R := R) H).1.ne_zero

lemma rv_isRad {H : Subgroup G} (x : Additive (radSub t (R := R) H)) : Mero.IsRad K (rv x) :=
  (Additive.toMul x : radSub t (R := R) H).2.1

lemma rv_isLogRad {H : Subgroup G} (x : Additive (radSub t (R := R) H)) : IsLogRad t (rv x) :=
  (Additive.toMul x : radSub t (R := R) H).2.2.1

lemma rv_fix {H : Subgroup G} (x : Additive (radSub t (R := R) H)) :
    ∀ h ∈ H, h • rv x = rv x :=
  (Additive.toMul x : radSub t (R := R) H).2.2.2

lemma rv_injective {H : Subgroup G} : Function.Injective (rv (t := t) (R := R) (H := H)) :=
  fun _ _ h => Additive.toMul.injective (Subtype.ext (Units.ext h))

variable (R) in
/-- **The group-like monoid `B`** on `B^temp(G)⁰` (written additively). -/
def radB (hact : ActCompat t s π R) : GrpOn.{u} (OrbitObj G) where
  obj A := Additive (radSub t (R := R) A.H)
  pb f := (radPb s π hact f).toAdditive
  pb_id A x := by
    apply rv_injective
    change rep (𝟙 A) • rv x = _
    refine (smul_eq_of_mk_eq (rv_fix x) ?_).trans (one_smul _ _)
    rw [mk_rep]; rfl
  pb_comp f g x := by
    apply rv_injective
    change rep (f ≫ g) • rv x = rep f • rep g • rv x
    rw [← mul_smul]
    refine smul_eq_of_mk_eq (rv_fix x) ?_
    rw [mk_rep, OrbitHom.comp_toFun, Function.comp_apply, ← mk_rep f, apply_mk_rep]
  pb_injective f x y h := by
    have h' : rep f • rv x = rep f • rv y := congrArg rv h
    exact rv_injective (smul_left_cancel _ h')
  pb_bijective_of_fsm {A B} f hf := by
    refine ⟨fun x y h => ?_, fun y => ?_⟩
    · have h' : rep f • rv x = rep f • rv y := congrArg rv h
      exact rv_injective (smul_left_cancel _ h')
    · have hb := OrbitHom.bijective_of_isFSM hf
      have hmem : ∀ b ∈ B.H, rep f * b * (rep f)⁻¹ ∈ A.H := fun b hb' => by
        have e : f.toFun (QuotientGroup.mk (rep f * b * (rep f)⁻¹)) =
            f.toFun (QuotientGroup.mk 1) := by
          rw [apply_mk_rep, apply_mk_rep, one_mul, inv_mul_cancel_right]
          refine QuotientGroup.eq.mpr ?_
          rw [mul_inv_rev, inv_mul_cancel_right]
          exact B.H.inv_mem hb'
        have := QuotientGroup.eq.mp (hb.1 e)
        simpa using A.H.inv_mem this
      obtain ⟨h1, h2, -⟩ := hact (rep f)⁻¹ (rv y) (rv_ne_zero y) (rv_isRad y) (rv_isLogRad y)
      refine ⟨Additive.ofMul ⟨Units.map (MulSemiringAction.toRingHom G R (rep f)⁻¹).toMonoidHom
        (Additive.toMul y : radSub t (R := R) A.H), h1, h2, fun b hb' => ?_⟩, ?_⟩
      · change b • ((rep f)⁻¹ • rv y) = (rep f)⁻¹ • rv y
        rw [← mul_smul, show b * (rep f)⁻¹ = (rep f)⁻¹ * (rep f * b * (rep f)⁻¹) by group,
          mul_smul, rv_fix y _ (hmem b hb')]
      · apply rv_injective
        change rep f • (rep f)⁻¹ • rv y = rv y
        rw [smul_inv_smul]

/-! ### The divisor map -/

variable {s π}

lemma rEllDiv_smul_of_fix (hact : ActCompat t s π R) {H : Subgroup G} {y : R} (hy0 : y ≠ 0)
    (hr : Mero.IsRad K y) (hl : IsLogRad t y) (hfix : ∀ h ∈ H, h • y = y) {h : G} (hh : h ∈ H)
    (p : PrimeAct π) :
    rEllDiv t s y (show EllPrime t from h • p) = rEllDiv t s y (show EllPrime t from p) := by
  have := (hact h⁻¹ y hy0 hr hl).2.2 p
  rw [hfix _ (H.inv_mem hh), inv_inv] at this
  exact this.symm

variable (s π) in
/-- The divisor of `y` as a function on `(G/H) × P`: `(gH, p) ↦ div(y)(g⁻¹ • p)`. -/
def radDivFun (H : Subgroup G) (y : R) : (G ⧸ H) × PrimeAct π → ℚ :=
  fun z => rEllDiv t s y (show EllPrime t from (Quotient.out z.1)⁻¹ • z.2)

lemma radDivFun_mk (hact : ActCompat t s π R) {H : Subgroup G} {y : R} (hy0 : y ≠ 0)
    (hr : Mero.IsRad K y) (hl : IsLogRad t y) (hfix : ∀ h ∈ H, h • y = y) (g : G)
    (p : PrimeAct π) :
    radDivFun s π H y (QuotientGroup.mk g, p) = rEllDiv t s y (show EllPrime t from g⁻¹ • p) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  change rEllDiv t s y (show EllPrime t from (Quotient.out (QuotientGroup.mk g : G ⧸ H))⁻¹ • p) = _
  rw [hh, mul_inv_rev, mul_smul]
  exact rEllDiv_smul_of_fix hact hy0 hr hl hfix (H.inv_mem h.2) _

variable (hval : ValueGroupRat t) (hs : (s : K) ^ 2 = t.q)

include hval hs in
variable (s π R) in
/-- **The divisor map `B → Φ^gp`** of the radical layer, into
`PrimeDiv.divMonoid G (PrimeAct π) ℚ`. -/
def radDiv (hact : ActCompat t s π R) :
    DivHom (radB s π R hact) (PrimeDiv.divMonoid G (PrimeAct π) ℚ).toGrpOn where
  app A := AddMonoidHom.mk' (fun u => ⟨radDivFun s π A.H (rv u),
    fun g z => by
      obtain ⟨x, p⟩ := z
      induction x using QuotientGroup.induction_on with
      | H g' =>
        change radDivFun s π A.H (rv u) (QuotientGroup.mk (g * g'), g • p) = _
        rw [radDivFun_mk hact (rv_ne_zero u) (rv_isRad u) (rv_isLogRad u) (rv_fix u),
          radDivFun_mk hact (rv_ne_zero u) (rv_isRad u) (rv_isLogRad u) (rv_fix u), mul_inv_rev,
          mul_smul, inv_smul_smul]⟩)
    (fun u v => by
      apply Subtype.ext
      funext z
      change rEllDiv t s (rv u * rv v) _ = rEllDiv t s (rv u) _ + rEllDiv t s (rv v) _
      rw [rEllDiv_mul hval hs (rv_ne_zero u) (rv_ne_zero v) (rv_isRad u) (rv_isRad v)]
      rfl)
  natural {A B} f x := by
    apply Subtype.ext
    funext ⟨z, p⟩
    induction z using QuotientGroup.induction_on with
    | H g =>
      have hfix := smul_rep_fix f (rv_fix x)
      obtain ⟨h1, h2, h3⟩ := hact (rep f) (rv x) (rv_ne_zero x) (rv_isRad x) (rv_isLogRad x)
      change radDivFun s π A.H (rep f • rv x) (QuotientGroup.mk g, p) =
        radDivFun s π B.H (rv x) (f.toFun (QuotientGroup.mk g), p)
      rw [radDivFun_mk hact ((smul_ne_zero_iff_ne _).mpr (rv_ne_zero x)) h1 h2 hfix, h3,
        apply_mk_rep, radDivFun_mk hact (rv_ne_zero x) (rv_isRad x) (rv_isLogRad x) (rv_fix x),
        mul_inv_rev, mul_smul]

include hval hs in
variable (s π R) in
/-- **The tempered Frobenioid of the radical layer** (B-an): `Φ₀` the `ℚ`-divisors on the
elliptic prime set, `B₀` the fixed log-meromorphic radicals, `div₀ = radDiv`. -/
def radData (hact : ActCompat t s π R) : TemperedFrobenioidData G where
  Φ₀ := PrimeDiv.divMonoid G (PrimeAct π) ℚ
  B₀ := radB s π R hact
  div₀ := radDiv s π R hval hs hact

/-- **It is a Frobenioid.** -/
theorem radData_isFrobenioid (hact : ActCompat t s π R) :
    IsFrobenioid (Model.toElem (radData s π R hval hs hact).Φ₀ (radData s π R hval hs hact).B₀
      (radData s π R hval hs hact).div₀) :=
  (radData s π R hval hs hact).isFrobenioid

/-! ### The kernel of the divisor map is `O_K^×` -/

omit [IsTopologicalGroup G] in
lemma rgn_pos {y : R} (hy0 : y ≠ 0) (hy : Mero.IsRad K y) {r : ℝ} (hr : 0 < r) :
    0 < Mero.rgn K y r := by
  obtain ⟨n, hn, x, hx⟩ := hy
  rw [Mero.rgn_eq hy0 hn hx hr]
  exact Real.rpow_pos_of_pos (Mero.gn_pos (Mero.ne_zero_of_ι_eq hy0 hx) hr) _

include hval hs in
omit [IsTopologicalGroup G] in
lemma coe_rCompOrd {y : R} (hy0 : y ≠ 0) (hy : Mero.IsRad K y) (a : ℤ) :
    (rCompOrd t s y a : ℝ) = rCompOrdR t s y a := by
  obtain ⟨n, hn, x, hx⟩ := hy
  have h := rCompOrdR_eq (t := t) (s := s) hy0 hn hx a
  rw [← coe_compOrd hval hs (Mero.ne_zero_of_ι_eq hy0 hx)] at h
  have h' : rCompOrdR t s y a = ((compOrd t s x a / n : ℚ) : ℝ) := by rw [h]; push_cast; rfl
  rw [rCompOrd_eq h', h']

include hval hs in
omit [IsTopologicalGroup G] in
/-- **[EtTh] Proposition 3.4(ii) on the radical layer, in divisor form**: a log-meromorphic
radical has divisor `0` iff it is a scalar of norm `1`. -/
theorem rEllDiv_eq_zero_iff [IsAlgClosed K] {y : R} (hy0 : y ≠ 0) (hy : Mero.IsRad K y)
    (hl : IsLogRad t y) :
    rEllDiv t s y = 0 ↔ ∃ c : K, ‖c‖ = 1 ∧ y = Mero.ι R (Mero.const c) := by
  rw [← Mero.rad_ker_iff hy0 hy t.norm_q_pos t.norm_lt_one]
  constructor
  · intro h
    refine ⟨fun α => ?_, fun a => ?_⟩
    · by_cases hα : ∃ k : ℤ, (α : K) ^ 2 = (t.q : K) ^ k
      · exact congrFun h (.inr ⟨α, hα⟩)
      · exact hl α hα
    · have h1 : rCompOrd t s y (2 * a) = 0 := congrFun h (.inl (2 * a))
      have h2 := coe_rCompOrd hval hs hy0 hy (2 * a)
      rw [h1, Rat.cast_zero, rCompOrdR, ← gn_q_zpow_eq hs, eq_comm, Real.logb_eq_zero] at h2
      have hpos := rgn_pos hy0 hy (zpow_pos t.norm_q_pos a)
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
    obtain ⟨c, hc, rfl⟩ := (Mero.rad_ker_iff hy0 hy t.norm_q_pos t.norm_lt_one).mp hker
    have hc0 : c ≠ 0 := fun h => by rw [h, norm_zero] at hc; exact zero_ne_one hc
    rw [rEllDiv_ι hval hs (Mero.const_ne_zero hc0),
      ellDiv_const hc0 (m := 0) (by rw [hc, Real.logb_one]; simp)]
    funext p
    rcases p with a | α <;> rfl

/-- **The kernel of the divisor map `B(G/H) → Φ^gp(G/H)` is `O_K^×`** ([EtTh] Def 3.3, Prop
3.4(ii)): the genuine form of the unit group `U` of `TateTheta.lean`. -/
theorem radDiv_eq_zero_iff [IsAlgClosed K] (hact : ActCompat t s π R) {A : OrbitObj G}
    (x : (radB s π R hact).obj A) :
    (radDiv s π R hval hs hact).app A x = 0 ↔
      ∃ c : K, ‖c‖ = 1 ∧ rv x = Mero.ι R (Mero.const c) := by
  rw [← rEllDiv_eq_zero_iff hval hs (rv_ne_zero x) (rv_isRad x) (rv_isLogRad x)]
  constructor
  · intro h
    funext p
    have := congrArg (fun v : PrimeDiv.divGp G (PrimeAct π) ℚ A => v.1
      (QuotientGroup.mk 1, show PrimeAct π from p)) h
    change radDivFun s π A.H (rv x) (QuotientGroup.mk 1, _) = 0 at this
    rw [radDivFun_mk hact (rv_ne_zero x) (rv_isRad x) (rv_isLogRad x) (rv_fix x), inv_one,
      one_smul] at this
    exact this
  · intro h
    apply Subtype.ext
    funext ⟨z, p⟩
    induction z using QuotientGroup.induction_on with
    | H g =>
      change radDivFun s π A.H (rv x) (QuotientGroup.mk g, p) = 0
      rw [radDivFun_mk hact (rv_ne_zero x) (rv_isRad x) (rv_isLogRad x) (rv_fix x), h]
      rfl

/-! ### The deck action on `Mero K` satisfies `ActCompat` (the unramified, geometric case) -/

variable (ρ : G →* Deck t)

namespace Mero

lemma scale_scale (c d : Kˣ) (x : Mero K) : scale c (scale d x) = scale (d * c) x := by
  have : (scale c).comp (scale d) = scale (K := K) (d * c) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (Entire K)) (RingHom.ext fun f => by
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← ofE, scale_ofE, scale_ofE, scale_ofE, Entire.scale_scale])
  exact RingHom.congr_fun this x

lemma scale_one (x : Mero K) : scale 1 x = x := by
  have : scale (K := K) 1 = RingHom.id _ :=
    IsLocalization.ringHom_ext (nonZeroDivisors (Entire K)) (RingHom.ext fun f => by
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [← ofE, scale_ofE, Entire.scale_one])
  exact RingHom.congr_fun this x

end Mero

/-- `Ü ↦ c·Ü` as a ring automorphism of `Mero K`. -/
def scaleEquiv (c : Kˣ) : Mero K ≃+* Mero K :=
  RingEquiv.ofRingHom (Mero.scale c) (Mero.scale c⁻¹)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, Mero.scale_scale, inv_mul_cancel, Mero.scale_one]; rfl)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, Mero.scale_scale, mul_inv_cancel, Mero.scale_one]; rfl)

lemma scaleEquiv_apply (c : Kˣ) (x : Mero K) : scaleEquiv c x = Mero.scale c x := rfl

omit [IsTopologicalGroup G] in
/-- `g ↦ (f ↦ f(ρ(g)⁻¹·Ü))`. -/
def deckHom : G →* RingAut (Mero K) where
  toFun g := scaleEquiv (((ρ g)⁻¹ : Deck t) : Kˣ)
  map_one' := RingEquiv.ext fun x => by
    rw [scaleEquiv_apply, map_one, inv_one, Subgroup.coe_one, Mero.scale_one]; rfl
  map_mul' g h := RingEquiv.ext fun x => by
    rw [scaleEquiv_apply, RingAut.mul_apply, scaleEquiv_apply, scaleEquiv_apply,
      Mero.scale_scale, map_mul, mul_inv_rev, Subgroup.coe_mul]

/-- **The deck action of `G` on `Mero K` through `ρ`**: `(g • f)(Ü) = f(ρ(g)⁻¹·Ü)`. -/
abbrev deckAction : MulSemiringAction G (Mero K) := MulSemiringAction.compHom (Mero K) (deckHom ρ)

include hval hs in
omit [IsTopologicalGroup G] in
/-- **`ActCompat` holds for the deck action on the unramified layer `R = Mero K`** (by
`ellDiv_scale`): the explicit input of `radB` is satisfiable in the geometric case. -/
theorem actCompat_deck :
    letI := deckAction ρ; ActCompat t s ((Deck.permHom t).comp ρ) (Mero K) := by
  letI := deckAction ρ
  intro g y hy0 _ hl
  set c : Kˣ := (((ρ g)⁻¹ : Deck t) : Kˣ)
  have hgy : g • y = Mero.scale c y := rfl
  have hι : ∀ z : Mero K, Mero.ι (Mero K) z = z := fun _ => rfl
  have hne : Mero.scale c y ≠ 0 := Mero.scale_ne_zero c hy0
  refine ⟨⟨1, one_pos, g • y, (pow_one _).symm⟩, fun α hα => ?_, fun p => ?_⟩
  · rw [hgy, ← hι (Mero.scale c y), Mero.rord_ι hne, Mero.ord_scale hy0]
    have hcα : ¬ ∃ k : ℤ, ((c * α : Kˣ) : K) ^ 2 = (t.q : K) ^ k := by
      rintro ⟨k, hk⟩
      refine hα ⟨k - Deck.idx ((ρ g)⁻¹), ?_⟩
      rw [Units.val_mul, mul_pow, Deck.idx_spec] at hk
      rw [zpow_sub₀ t.q.ne_zero, ← hk, mul_div_cancel_left₀ _ (zpow_ne_zero _ t.q.ne_zero)]
    have := hl (c * α) hcα
    rw [← hι y, Mero.rord_ι hy0] at this
    exact_mod_cast this
  · have e1 : rEllDiv t s (g • y) = ellDiv t s (Mero.scale c y) := by
      rw [hgy]; exact rEllDiv_ι (R := Mero K) hval hs hne
    have e2 : rEllDiv t s y = ellDiv t s y := rEllDiv_ι (R := Mero K) hval hs hy0
    rw [e1, e2, ellDiv_scale hs _ hy0]
    change ellDiv t s y (((ρ g)⁻¹ : Deck t) • (show EllPrime t from p)) =
      ellDiv t s y (ρ g⁻¹ • (show EllPrime t from p))
    rw [map_inv]

/-- **`Mero K` with the deck action of `G` through `ρ`** (`deckAction ρ`), as a type, so that
`radB`/`radData` can be applied to it with instance arguments. -/
def DeckMero {G : Type u} [Group G] (_ρ : G →* Deck t) : Type u := Mero K

instance : Field (DeckMero ρ) := inferInstanceAs (Field (Mero K))

instance : Algebra (Mero K) (DeckMero ρ) := inferInstanceAs (Algebra (Mero K) (Mero K))

instance : MulSemiringAction G (DeckMero ρ) := deckAction ρ

include hval hs in
omit [IsTopologicalGroup G] in
/-- `ActCompat` for `DeckMero ρ` (`actCompat_deck`). -/
theorem actCompat_deckMero : ActCompat t s ((Deck.permHom t).comp ρ) (DeckMero ρ) :=
  actCompat_deck hval hs ρ

end Iut.Frobenioid.BAn
