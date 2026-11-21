/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.Labels
import Iut.Cor312.ThetaData.Basic

/-!
# Cusp labels of the models `D^⊚` and `D^⊚±` (MR22 T5)

IUT I, Definition 4.1 (v), Example 4.5 (ii), Definition 6.1 (v), (vi), on the model side: for
initial Θ-data `D`, with `C̲_K` of type `(1, ℓ-tors)^±` and `X̲_K` of type `(1, ℓ-tors)`
(`Iut.OrbicurveData`),

* the rank-one quotient `Q` of `C̲_K` has `ℓ` elements (`card_Q_CKu`), and the chosen element
  `q` (giving the distinguished cusp `ε`) is a generator: `qChart : Q ≃+ F_ℓ`, `q ↦ 1`;
* **`LabCusp(D^⊚)`** of the model `D^⊚ = B(C̲_K)⁰` (`labCuspCirc`): the nonzero cusps of `C̲_K`
  (`Q/{±1}` minus the zero cusp), an `F_ℓ^*`-torsor via `Q/{±1} ≃ |F_ℓ|` and
  `|F_ℓ| ∖ {0} ≃ F_ℓ^*`; the chart is compatible with the natural action of `F_ℓ^×` on the
  `ℓ`-torsion group `Q` (`labCuspCirc_chart_smul`), and the class `[ε]` maps to `1`
  (`chart_epsClass`, IUT I, Example 4.5 (ii));
* **`LabCusp^±(D^⊚±)`** of the model `D^⊚± = B(X̲_K)⁰` (`labCuspPmCirc`; Definition 6.1 (vi)):
  the cusps of `X̲_K` (no `±`, so the cusps are `Q(X̲_K)`), an `F_ℓ^±`-torsor through the
  identification `Q(X̲_K) ≅ Q(C̲_K)` given by the cover `X̲_K → C̲_K` (of degree `n = 1`,
  `XKu_to_CKu_n`; same curve and same `M` by the cartesian square);
* the projection `cuspPmToCirc : Cusp(X̲_K) → Cusp(C̲_K)` (`Q → Q/{±1}`), which maps the nonzero
  `±`-labels onto `LabCusp(D^⊚)` (`cuspPmToCircNZ`, `cuspPmToCircNZ_surjective`) compatibly with
  the charts (`starToAbs_chart_cuspPmToCircNZ`: `|·|` of the `±`-chart is the `⋇`-chart).

## Nonvanishing of `q`

`OrbicurveData.QIso : Q ≃+ ZMod ℓ` is additive, so its field `q_ne_zero : QIso q ≠ 0` gives
`q ≠ 0` in `Q` (`q_ne_zero_Q`; IUT I, Definition 3.1 (f): `ε` arises from a *nonzero* element of
`Q`).
-/

namespace Iut.Multiradial.Theater

open Iut.Anabelian Iut.HodgeTheater

universe u

noncomputable section

/-! ### Generic model orbicurves -/

namespace LabCuspModel

variable {k : Type u} [Field k] (X : Orbicurve k)

open scoped Classical in
/-- **Lagrange for the rank-one quotient**: if `M ≤ E[ℓ]`, `|M| = ℓ` and `|E[ℓ]| = ℓ²`, then
`|Q| = ℓ`. -/
lemma card_Q_eq {ℓ : ℕ} (hM : X.M ≤ X.torsion) (hMc : Nat.card X.M = ℓ)
    (hT : Nat.card X.torsion = ℓ ^ 2) (hℓ : 0 < ℓ) : Nat.card X.Q = ℓ := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (X.M.addSubgroupOf X.torsion)
  rw [Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hM).toEquiv, hMc, hT] at h
  have h' : Nat.card X.Q * ℓ = ℓ * ℓ := by rw [← sq]; exact h.symm
  exact Nat.eq_of_mul_eq_mul_right hℓ h'

variable {X} {ℓ : ℕ}

open scoped Classical in
/-- Every element of a group of order `ℓ` is killed by `ℓ`. -/
lemma nsmul_eq_zero_of_card (hc : Nat.card X.Q = ℓ) (x : X.Q) : ℓ • x = 0 :=
  hc ▸ card_nsmul_eq_zero'

open scoped Classical in
/-- The predicate "is the zero cusp" on cusps. -/
def IsZeroCusp (X : Orbicurve k) : X.Cusp → Prop :=
  Quot.lift (fun y : X.Q => y = 0) (by
    rintro a b (rfl | ⟨-, rfl⟩)
    · rfl
    · exact propext neg_eq_zero)

open scoped Classical in
lemma cuspOf_eq_cuspOf_zero_iff (x : X.Q) : X.cuspOf x = X.cuspOf 0 ↔ x = 0 := by
  constructor
  · intro h
    have key : IsZeroCusp X (X.cuspOf x) = IsZeroCusp X (X.cuspOf 0) := congrArg _ h
    change (x = 0) = ((0 : X.Q) = 0) at key
    exact key ▸ rfl
  · rintro rfl
    rfl

open scoped Classical in
/-- **The cusps of a model without `±` are `Q`.** -/
def cuspEquivQ (hpm : X.pm = false) : X.Cusp ≃ X.Q where
  toFun := Quot.lift id (by
    rintro a b (h | ⟨h, -⟩)
    · exact h
    · exact absurd (hpm.symm.trans h) Bool.false_ne_true)
  invFun := X.cuspOf
  left_inv c := Quot.inductionOn c fun _ => rfl
  right_inv _ := rfl

open scoped Classical in
lemma cuspEquivQ_cuspOf (hpm : X.pm = false) (x : X.Q) : cuspEquivQ hpm (X.cuspOf x) = x := rfl

open scoped Classical in
/-- **The rank-one quotients of two models with the same curve, level and `M` agree.** -/
def qTransport {Y : Orbicurve k} (h : X.E = Y.E) (hl : X.level = Y.level)
    (hM : Orbicurve.transportM h X.M = Y.M) : X.Q ≃+ Y.Q := by
  obtain ⟨E, l, M, pm⟩ := X
  obtain ⟨E', l', M', pm'⟩ := Y
  dsimp only at h hl hM
  subst h hl
  subst hM
  exact AddEquiv.refl _

open scoped Classical in
lemma ne_zero_of_cuspOf_ne (e : X.Q ≃+ ZMod ℓ) {x : X.Q} (hx : X.cuspOf x ≠ X.cuspOf 0) :
    e x ≠ 0 := by
  rw [Ne, AddEquivClass.map_eq_zero_iff, ← cuspOf_eq_cuspOf_zero_iff]
  exact hx

variable [OddPrime ℓ]

open scoped Classical in
/-- The natural action of `F_ℓ^×` on an `ℓ`-torsion group, read in an additive chart: the
`ZMod.val u`-fold multiple goes to multiplication by `u`. -/
lemma chart_val_nsmul (e : X.Q ≃+ ZMod ℓ) (u : (ZMod ℓ)ˣ) (x : X.Q) :
    e (ZMod.val (u : ZMod ℓ) • x) = (u : ZMod ℓ) * e x := by
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

open scoped Classical in
/-- The homomorphism `F_ℓ → Q`, `k ↦ k • q`, for `q` killed by `ℓ`. -/
def qHom (q : X.Q) (hq : ℓ • q = 0) : ZMod ℓ →+ X.Q :=
  ZMod.lift ℓ ⟨zmultiplesHom X.Q q, by simp [natCast_zsmul, hq]⟩

open scoped Classical in
lemma qHom_intCast (q : X.Q) (hq : ℓ • q = 0) (m : ℤ) : qHom q hq (m : ZMod ℓ) = m • q :=
  ZMod.lift_coe _ _ m

open scoped Classical in
lemma qHom_one (q : X.Q) (hq : ℓ • q = 0) : qHom q hq 1 = q := by
  simpa using qHom_intCast q hq 1

open scoped Classical in
lemma qHom_injective (q : X.Q) (hq : ℓ • q = 0) (hq0 : q ≠ 0) :
    Function.Injective (qHom q hq) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
  rw [qHom_intCast] at hz
  have ho : addOrderOf q = ℓ := addOrderOf_eq_prime hq hq0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← ho]
  exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz

open scoped Classical in
lemma qHom_bijective (hc : Nat.card X.Q = ℓ) (q : X.Q) (hq0 : q ≠ 0) :
    Function.Bijective (qHom q (nsmul_eq_zero_of_card hc q)) := by
  haveI : Finite X.Q := Nat.finite_of_card_ne_zero (by rw [hc]; exact NeZero.ne ℓ)
  exact (qHom_injective q _ hq0).bijective_of_nat_card_le (by rw [hc, Nat.card_zmod])

open scoped Classical in
/-- **The chart `Q ≃+ F_ℓ` sending a nonzero `q` to `1`**, for `Q` of order `ℓ`. -/
def qChartOf (hc : Nat.card X.Q = ℓ) (q : X.Q) (hq0 : q ≠ 0) : X.Q ≃+ ZMod ℓ :=
  (AddEquiv.ofBijective _ (qHom_bijective hc q hq0)).symm

open scoped Classical in
lemma qChartOf_q (hc : Nat.card X.Q = ℓ) (q : X.Q) (hq0 : q ≠ 0) : qChartOf hc q hq0 q = 1 :=
  (AddEquiv.symm_apply_eq _).mpr (qHom_one q (nsmul_eq_zero_of_card hc q)).symm

open scoped Classical in
/-- **`Q/{±1} ≃ |F_ℓ|`** for a model orbicurve with the `±`-flag, from an additive chart of `Q`. -/
def cuspAbsOf (hpm : X.pm = true) (e : X.Q ≃+ ZMod ℓ) : X.Cusp ≃ AbsFl ℓ where
  toFun := Quot.lift (fun x => AbsFl.mk (e x)) (by
    rintro a b (rfl | ⟨-, rfl⟩)
    · rfl
    · rw [map_neg, AbsFl.mk_neg])
  invFun := Quotient.lift (fun z => X.cuspOf (e.symm z)) (by
    intro a b h
    rcases (h : a = b ∨ a = -b) with rfl | rfl
    · rfl
    · change X.cuspOf (e.symm (-b)) = X.cuspOf (e.symm b)
      rw [map_neg, X.cuspOf_neg hpm])
  left_inv c := Quot.inductionOn c fun x => by
    change X.cuspOf (e.symm (e x)) = X.cuspOf x
    rw [e.symm_apply_apply]
  right_inv z := Quotient.inductionOn z fun w => by
    change AbsFl.mk (e (e.symm w)) = AbsFl.mk w
    rw [e.apply_symm_apply]

open scoped Classical in
lemma cuspAbsOf_cuspOf (hpm : X.pm = true) (e : X.Q ≃+ ZMod ℓ) (x : X.Q) :
    cuspAbsOf hpm e (X.cuspOf x) = AbsFl.mk (e x) := rfl

open scoped Classical in
lemma cuspAbsOf_eq_zero_iff (hpm : X.pm = true) (e : X.Q ≃+ ZMod ℓ) (c : X.Cusp) :
    cuspAbsOf hpm e c = 0 ↔ c = X.cuspOf 0 :=
  Quot.inductionOn c fun x => by
    change AbsFl.mk (e x) = 0 ↔ X.cuspOf x = X.cuspOf 0
    rw [AbsFl.mk_eq_zero, cuspOf_eq_cuspOf_zero_iff, AddEquivClass.map_eq_zero_iff]

open scoped Classical in
/-- **The nonzero cusps of a `±`-model are an `F_ℓ^*`-torsor**: the chart
`Q/{±1} ∖ {0} ≃ |F_ℓ| ∖ {0} ≃ F_ℓ^*`. -/
def starOf (hpm : X.pm = true) (e : X.Q ≃+ ZMod ℓ) :
    {c : X.Cusp // c ≠ X.cuspOf 0} ≃ FlStar ℓ :=
  (Equiv.subtypeEquiv (cuspAbsOf hpm e) fun c => by
    rw [Ne, Ne, cuspAbsOf_eq_zero_iff]).trans (nonzeroAbsEquiv ℓ)

variable (ℓ) in
open scoped Classical in
/-- `|z| ∈ |F_ℓ| ∖ {0}` corresponds to the class of the unit `z` in `F_ℓ^*`. -/
lemma nonzeroAbsEquiv_mk (z : ZMod ℓ) (hz : z ≠ 0) (h : AbsFl.mk z ≠ 0) :
    nonzeroAbsEquiv ℓ ⟨AbsFl.mk z, h⟩ = ((Units.mk0 z hz : (ZMod ℓ)ˣ) : FlStar ℓ) :=
  starToAbs_injective ℓ (by rw [starToAbs_nonzeroAbsEquiv, starToAbs_mk, Units.val_mk0])

open scoped Classical in
lemma starOf_cuspOf (hpm : X.pm = true) (e : X.Q ≃+ ZMod ℓ) (x : X.Q)
    (hx : X.cuspOf x ≠ X.cuspOf 0) :
    starOf hpm e ⟨X.cuspOf x, hx⟩ =
      ((Units.mk0 (e x) (ne_zero_of_cuspOf_ne e hx) : (ZMod ℓ)ˣ) : FlStar ℓ) :=
  nonzeroAbsEquiv_mk ℓ _ _ _

open scoped Classical in
/-- **Equivariance of the `F_ℓ^*`-chart**: the natural action of `u ∈ F_ℓ^×` on `Q` becomes
multiplication by the class of `u` in `F_ℓ^*`. -/
lemma starOf_smul (hpm : X.pm = true) (e : X.Q ≃+ ZMod ℓ) (u : (ZMod ℓ)ˣ) (x : X.Q)
    (h₁ : X.cuspOf (ZMod.val (u : ZMod ℓ) • x) ≠ X.cuspOf 0) (h₂ : X.cuspOf x ≠ X.cuspOf 0) :
    starOf hpm e ⟨X.cuspOf (ZMod.val (u : ZMod ℓ) • x), h₁⟩ =
      (u : FlStar ℓ) * starOf hpm e ⟨X.cuspOf x, h₂⟩ := by
  rw [starOf_cuspOf, starOf_cuspOf, ← QuotientGroup.mk_mul]
  congr 1
  exact Units.ext (by rw [Units.val_mk0, Units.val_mul, Units.val_mk0, chart_val_nsmul])

end LabCuspModel

open LabCuspModel

/-! ### The models of initial Θ-data -/

open scoped Classical in
/-- The prime `ℓ` of initial Θ-data is an odd prime (`≥ 5`). -/
local instance oddPrimeEll (D : InitialThetaData.{u}) : OddPrime D.ℓ :=
  ⟨D.prime.ℓ_prime, by have := D.prime.five_le; change 2 < D.prime.ℓ; omega⟩

/-- The classical decidable equality on `K`, as used by the model orbicurves (as in
`Iut.Anabelian.Torsion`). -/
local instance (priority := high) instDecidableEqKLab (D : InitialThetaData.{u}) :
    DecidableEq ↥D.prime.torsionField :=
  fun a b => Classical.propDecidable (a = b)

variable (D : InitialThetaData.{0})

open scoped Classical in
/-- The `ℓ` of the Θ-data is the `ℓ` of its admissible-prime data, hence the `ℓ` of the types of
`C̲_K` and `X̲_K`. -/
lemma ell_eq : D.ℓ = D.prime.ℓ := rfl

open scoped Classical in
lemma CKu_pm : D.orb.CKu.pm = true := D.orb.CKu_type.2.2.1

open scoped Classical in
lemma XKu_pm : D.orb.XKu.pm = false := D.orb.XKu_type.2.2.1

open scoped Classical in
/-- **`|Q(C̲_K)| = ℓ`.** -/
theorem card_Q_CKu : Nat.card D.orb.CKu.Q = D.ℓ := by
  obtain ⟨hp, -, -, hM, hMc, hT⟩ := D.orb.CKu_type
  exact card_Q_eq _ hM hMc hT hp.pos

open scoped Classical in
/-- **The chosen `q` is nonzero in `Q`** (`QIso` is additive). -/
lemma q_ne_zero_Q : D.orb.q ≠ 0 := fun h => D.orb.q_ne_zero (by rw [h, map_zero])

open scoped Classical in
/-- **The chart `Q(C̲_K) ≃+ F_ℓ` with `q ↦ 1`** (`q ≠ 0`: `q_ne_zero_Q`). -/
def qChart : D.orb.CKu.Q ≃+ ZMod D.ℓ :=
  qChartOf (card_Q_CKu D) D.orb.q (q_ne_zero_Q D)

open scoped Classical in
lemma qChart_q : qChart D D.orb.q = 1 := qChartOf_q _ _ _

open scoped Classical in
/-- **`Cusp(C̲_K) = Q/{±1} ≃ |F_ℓ|`** (IUT I, Example 4.4 (i): `LabCusp(D^⊚) ∪ {0} = |F_ℓ|`). -/
def cuspAbs : D.orb.CKu.Cusp ≃ AbsFl D.ℓ :=
  cuspAbsOf (CKu_pm D) (qChart D)

open scoped Classical in
/-- **`LabCusp(D^⊚)`** of the model `D^⊚ = B(C̲_K)⁰` (IUT I, Definition 4.1 (v), Example 4.5 (ii)):
the nonzero cusps of `C̲_K`, an `F_ℓ^*`-torsor via `Q/{±1} ∖ {0} ≃ F_ℓ^*`. -/
def labCuspCirc : StarTorsor D.ℓ :=
  ⟨{c : D.orb.CKu.Cusp // c ≠ D.orb.CKu.cuspOf 0}, starOf (CKu_pm D) (qChart D)⟩

open scoped Classical in
lemma labCuspCirc_chart_cuspOf (x : D.orb.CKu.Q)
    (hx : D.orb.CKu.cuspOf x ≠ D.orb.CKu.cuspOf 0) :
    (labCuspCirc D).chart ⟨D.orb.CKu.cuspOf x, hx⟩ =
      ((Units.mk0 (qChart D x) (ne_zero_of_cuspOf_ne _ hx) : (ZMod D.ℓ)ˣ) : FlStar D.ℓ) :=
  starOf_cuspOf _ _ _ _

open scoped Classical in
/-- **The chart of `LabCusp(D^⊚)` is `F_ℓ^×`-equivariant**: for `x ≠ 0` in `Q`, the cusp of
`u • x` (the natural action of `u ∈ F_ℓ^×` on the `ℓ`-torsion group `Q`) has chart
`[u] · chart([x])`. -/
lemma labCuspCirc_chart_smul (u : (ZMod D.ℓ)ˣ) (x : D.orb.CKu.Q)
    (h₁ : D.orb.CKu.cuspOf (ZMod.val (u : ZMod D.ℓ) • x) ≠ D.orb.CKu.cuspOf 0)
    (h₂ : D.orb.CKu.cuspOf x ≠ D.orb.CKu.cuspOf 0) :
    (labCuspCirc D).chart ⟨D.orb.CKu.cuspOf (ZMod.val (u : ZMod D.ℓ) • x), h₁⟩ =
      (u : FlStar D.ℓ) * (labCuspCirc D).chart ⟨D.orb.CKu.cuspOf x, h₂⟩ :=
  starOf_smul _ _ _ _ _ _

open scoped Classical in
/-- **The class `[ε] ∈ LabCusp(D^⊚)`** of the distinguished cusp (IUT I, Example 4.5 (ii)). -/
def epsClass : (labCuspCirc D).carrier :=
  ⟨D.orb.epsilon, by
    rw [D.orb.epsilon_spec, Ne, cuspOf_eq_cuspOf_zero_iff]
    exact q_ne_zero_Q D⟩

open scoped Classical in
/-- **`[ε] ↦ 1`** (IUT I, Example 4.5 (ii)). -/
theorem chart_epsClass : (labCuspCirc D).chart (epsClass D) = 1 := by
  have hx : D.orb.CKu.cuspOf D.orb.q ≠ D.orb.CKu.cuspOf 0 := by
    rw [Ne, cuspOf_eq_cuspOf_zero_iff]
    exact q_ne_zero_Q D
  have he : epsClass D = ⟨D.orb.CKu.cuspOf D.orb.q, hx⟩ := Subtype.ext D.orb.epsilon_spec
  rw [he, labCuspCirc_chart_cuspOf]
  change _ = ((1 : (ZMod D.ℓ)ˣ) : FlStar D.ℓ)
  congr 1
  exact Units.ext (by rw [Units.val_mk0, qChart_q, Units.val_one])

open scoped Classical in
/-- **The cover `X̲_K → C̲_K` has degree `n = 1`** (both levels are `ℓ`). -/
lemma XKu_to_CKu_n : D.orb.XKu_to_CKu.n = 1 := by
  have h := D.orb.XKu_to_CKu.mul
  rw [D.orb.XKu_type.2.1, D.orb.CKu_type.2.1] at h
  exact Nat.eq_of_mul_eq_mul_right D.prime.ℓ_prime.pos (h.trans (one_mul _).symm)

open scoped Classical in
/-- **`Q(X̲_K) ≅ Q(C̲_K)`**: the identification induced by the cover `X̲_K → C̲_K` (degree one,
same curve, and same `M` by the cartesian square of IUT I, Definition 3.1 (d)). -/
def qXC : D.orb.XKu.Q ≃+ D.orb.CKu.Q :=
  qTransport D.orb.XKu_to_CKu.E_eq D.orb.diagram_cartesian.2.2.2.2.1
    D.orb.diagram_cartesian.2.2.2.2.2.2.1

open scoped Classical in
/-- **`LabCusp^±(D^⊚±)`** of the model `D^⊚± = B(X̲_K)⁰` (IUT I, Definition 6.1 (vi)): the cusps
of `X̲_K` (`= Q(X̲_K)`, no `±`), an `F_ℓ^±`-torsor via `Q(X̲_K) ≅ Q(C̲_K) ≃+ F_ℓ`. -/
def labCuspPmCirc : PmTorsor D.ℓ :=
  ⟨D.orb.XKu.Cusp, (cuspEquivQ (XKu_pm D)).trans ((qXC D).toEquiv.trans (qChart D).toEquiv)⟩

open scoped Classical in
lemma labCuspPmCirc_chart_cuspOf (x : D.orb.XKu.Q) :
    (labCuspPmCirc D).chart (D.orb.XKu.cuspOf x) = qChart D (qXC D x) := rfl

open scoped Classical in
/-- The zero of the `F_ℓ^±`-group `LabCusp^±(D^⊚±)` is the zero cusp. -/
lemma labCuspPmCirc_chart_eq_zero_iff (c : D.orb.XKu.Cusp) :
    (labCuspPmCirc D).chart c = 0 ↔ c = D.orb.XKu.cuspOf 0 :=
  Quot.inductionOn c fun x => by
    change qChart D (qXC D x) = 0 ↔ D.orb.XKu.cuspOf x = D.orb.XKu.cuspOf 0
    rw [AddEquivClass.map_eq_zero_iff, AddEquivClass.map_eq_zero_iff,
      cuspOf_eq_cuspOf_zero_iff]

open scoped Classical in
/-- **The projection `Cusp(X̲_K) = Q → Q/{±1} = Cusp(C̲_K)`**, induced by the cover
`X̲_K → C̲_K` (the model of the map from `±`-labels to `⋇`-labels). -/
def cuspPmToCirc (c : D.orb.XKu.Cusp) : D.orb.CKu.Cusp :=
  D.orb.CKu.cuspOf (qXC D (cuspEquivQ (XKu_pm D) c))

open scoped Classical in
lemma cuspPmToCirc_cuspOf (x : D.orb.XKu.Q) :
    cuspPmToCirc D (D.orb.XKu.cuspOf x) = D.orb.CKu.cuspOf (qXC D x) := rfl

open scoped Classical in
lemma cuspPmToCirc_surjective : Function.Surjective (cuspPmToCirc D) := by
  intro c
  obtain ⟨y, rfl⟩ := Quot.exists_rep c
  exact ⟨D.orb.XKu.cuspOf ((qXC D).symm y), by
    rw [cuspPmToCirc_cuspOf, AddEquiv.apply_symm_apply]
    rfl⟩

open scoped Classical in
lemma cuspPmToCirc_eq_zero_iff (c : D.orb.XKu.Cusp) :
    cuspPmToCirc D c = D.orb.CKu.cuspOf 0 ↔ c = D.orb.XKu.cuspOf 0 :=
  Quot.inductionOn c fun x => by
    change cuspPmToCirc D (D.orb.XKu.cuspOf x) = _ ↔ D.orb.XKu.cuspOf x = _
    rw [cuspPmToCirc_cuspOf, cuspOf_eq_cuspOf_zero_iff, cuspOf_eq_cuspOf_zero_iff,
      AddEquivClass.map_eq_zero_iff]

open scoped Classical in
/-- **Nonzero `±`-labels go to `LabCusp(D^⊚)`.** -/
def cuspPmToCircNZ (c : {c : D.orb.XKu.Cusp // c ≠ D.orb.XKu.cuspOf 0}) :
    (labCuspCirc D).carrier :=
  ⟨cuspPmToCirc D c.1, by rw [Ne, cuspPmToCirc_eq_zero_iff]; exact c.2⟩

open scoped Classical in
lemma cuspPmToCircNZ_surjective :
    Function.Surjective (cuspPmToCircNZ D) := by
  rintro ⟨c, hc⟩
  obtain ⟨c', rfl⟩ := cuspPmToCirc_surjective D c
  exact ⟨⟨c', by rwa [Ne, ← cuspPmToCirc_eq_zero_iff]⟩, rfl⟩

open scoped Classical in
/-- **Compatibility of the charts**: for a nonzero `±`-label `c`, the image in `|F_ℓ|` of the
`⋇`-chart of its projection is `|·|` of its `±`-chart. -/
theorem starToAbs_chart_cuspPmToCircNZ
    (c : {c : D.orb.XKu.Cusp // c ≠ D.orb.XKu.cuspOf 0}) :
    starToAbs D.ℓ ((labCuspCirc D).chart (cuspPmToCircNZ D c)) =
      AbsFl.mk ((labCuspPmCirc D).chart c.1) :=
  starToAbs_nonzeroAbsEquiv D.ℓ _

end

end Iut.Multiradial.Theater
