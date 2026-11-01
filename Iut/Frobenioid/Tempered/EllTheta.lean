/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.EllB

/-!
# The theta instance of the tempered Frobenioid: `B₀` = log-meromorphic functions (MR18)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*
(text `~/iut-scratch/wall/txt/The Etale Theta Function …txt`, cited by line).

For a character `χ : G → ℤ` (the `ℤ`-covering `Y → X`, `Gal(Y/X) = ℤ`) and the analytic model
`Ÿ_∞ = 𝔾_m^an` over `K` (Tate parameter `t`, `s² = q`), the theta instance of the tempered
Frobenioid ([EtTh] Def 3.3, Ex 3.9) is `radData` (`EllB.lean`) for the **deck action** of `G` on
`R = Mero K` through `χ` (`g • f = f(s^{-χ(g)}·Ü)`, `DeckMero (chiDeck χ hs)`), whose
compatibility with the action on the elliptic prime set is a theorem (`actCompat_deckMero`):

* `thetaData χ hval hs`: `Φ₀ = ellDivMonoid χ hs` (`ℚ`-divisors on `ℤ ⊕ Cusps`), `B₀(G/H)` = the
  `H`-fixed nonzero log-meromorphic functions in `Mero K`, `div₀ = radDiv`;
  `thetaData_isFrobenioid`. Its kernel is `O_K^×` (`radDiv_eq_zero_iff`, `K` algebraically
  closed), the genuine form of the former arbitrary unit group `U`.
* On `Y = G/ker χ` every log-meromorphic `f ∈ Mero K` is an element `thetaElt f` of `B₀(Y)`, and
  `div₀ (thetaElt f) = ofDiv (ellDiv f)` (`div_thetaElt`). In particular `bOne = q^{1/2}`,
  `bU = Ü`, `bTheta = Θ̈` are genuine elements of `B₀(Y)`.
* **Comparison with the former theta-monomial group**: the divisor of the theta monomial
  `q^{a/2} Ü^b Θ̈^{-c}` (`thetaMono a b c`) has the shape `(a + b·j + c·j²)/2` on the component
  labelled `j` and `-c` at the cusps (`isThetaShape_div_thetaMono`), and every divisor of that
  shape is such a divisor (`eq_div_thetaMono_of_isThetaShape`). So the former `B₀(Y)` (the
  theta-shape divisors) is exactly the image under `div₀` of the subgroup of theta monomials.
* **[EtTh] Prop 1.4(ii) in `B₀`** (l.1324–1328: `Θ̈(q^{a/2}Ü) = (-1)^a q^{-a²/2} Ü^{-2a} Θ̈(Ü)`):
  `pb_deck_bTheta`, the pull-back of `Θ̈` along the deck transformation `τ_d` of `Y` (`a = χ(d)`)
  is `(-1)^a · Θ̈ · Ü^{2a} · q^{-a²/2}` as an element of `B₀(Y)`; in divisor form
  `div_pb_deck_bTheta`.
* `tateThetaData`: the instance for `G = temperedPi1` of the Tate curve and `χ` its character.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid

open CategoryTheory BAn TateCurvesTheta

universe u

section Theta

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (χ : G →* Multiplicative ℤ)
  {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K} {s : Kˣ} (hval : ValueGroupRat t) (hs : (s : K) ^ 2 = t.q)

/-- `Mero K` with the deck action of `G` through `χ`: `g • f = f(s^{-χ(g)}·Ü)`. -/
abbrev ThetaR : Type u := DeckMero (chiDeck χ hs)

/-- **The tempered Frobenioid of the `ℤ`-covering defined by `χ`** ([EtTh] Def 3.3, 3.6,
Ex 3.9): `Φ₀` the `ℚ`-divisors on the elliptic prime set, `B₀` the fixed log-meromorphic
functions on `Ÿ_∞ = 𝔾_m^an` under the deck action, `div₀` their divisor. -/
abbrev thetaData : TemperedFrobenioidData G :=
  radData s ((Deck.permHom t).comp (chiDeck χ hs)) (ThetaR χ hs) hval hs
    (actCompat_deckMero (ρ := chiDeck χ hs) hval hs)

/-- **The theta tempered Frobenioid is a Frobenioid.** -/
theorem thetaData_isFrobenioid :
    IsFrobenioid (Model.toElem (thetaData χ hval hs).Φ₀ (thetaData χ hval hs).B₀
      (thetaData χ hval hs).div₀) :=
  (thetaData χ hval hs).isFrobenioid

/-- The kernel of `χ` acts trivially on `Mero K`. -/
lemma smul_thetaR_of_mem_ker {g : G} (hg : g ∈ χ.ker) (y : ThetaR χ hs) : g • y = y := by
  change Mero.scale (((chiDeck χ hs g)⁻¹ : Deck t) : Kˣ) (y : Mero K) = y
  rw [chiDeck_apply, MonoidHom.mem_ker.mp hg, toAdd_one, zpow_zero, inv_one]
  exact Mero.scale_one _

/-! ### Log-meromorphic functions as elements of `B₀(Y)` -/

lemma isLogMero_const {c : K} (hc : c ≠ 0) : IsLogMero t (Mero.const c) :=
  ⟨Mero.const_ne_zero hc, fun α _ => Mero.ord_const hc α⟩

lemma mono_one_ne_zero : (Entire.mono 1 : Entire K) ≠ 0 := fun h => by
  have := congrFun (congrArg Subtype.val h) 1
  simp [Entire.coe_mono] at this

lemma isLogMero_mono : IsLogMero t (Mero.ofE (Entire.mono 1 : Entire K)) :=
  ⟨Mero.ofE_ne_zero mono_one_ne_zero, fun α _ => by
    rw [Mero.ord_ofE mono_one_ne_zero]
    exact_mod_cast (ord_eq_zero_iff mono_one_ne_zero α).mpr (by
      simp only [Entire.coe_mono, zpow_one]; exact α.ne_zero)⟩

lemma isLogMero_thetaDd : IsLogMero t (Mero.ofE (thetaDd t)) :=
  ⟨Mero.ofE_ne_zero (thetaDd_ne_zero t), fun α hα => by
    rw [Mero.ord_ofE (thetaDd_ne_zero t), ord_thetaDd_of_not_cusp t hα, Nat.cast_zero]⟩

variable {χ} (hχ : Continuous χ)

lemma isLogRad_thetaR {f : Mero K} (hf : IsLogMero t f) :
    IsLogRad t (show ThetaR χ hs from f) := fun α hα => by
  have h := Mero.rord_ι (R := ThetaR χ hs) hf.1 α
  rw [hf.2 α hα, Int.cast_zero] at h
  exact h

/-- **A log-meromorphic function on `Ÿ_∞` as an element of `B₀(Y)`** (`ker χ` acts trivially). -/
def thetaElt (f : Mero K) (hf : IsLogMero t f) : (thetaData χ hval hs).B₀.obj (objY hχ) :=
  Additive.ofMul ⟨Units.mk0 (show ThetaR χ hs from f) hf.1,
    ⟨1, one_pos, f, (pow_one _).symm⟩, isLogRad_thetaR hs hf,
    fun _ hh => smul_thetaR_of_mem_ker χ hs hh _⟩

lemma rv_thetaElt (f : Mero K) (hf : IsLogMero t f) :
    rv (thetaElt hval hs hχ f hf) = (show ThetaR χ hs from f) := rfl

/-- **The divisor of `thetaElt f` is the divisor of `f`**, transported to `Y` (`ofDiv`). -/
theorem div_thetaElt (f : Mero K) (hf : IsLogMero t f) :
    (thetaData χ hval hs).div₀.app (objY hχ) (thetaElt hval hs hχ f hf) =
      ofDiv hs hχ (ellDiv t s f) := by
  apply Subtype.ext
  funext ⟨x, p⟩
  induction x using QuotientGroup.induction_on with
  | H g =>
    change radDivFun s ((Deck.permHom t).comp (chiDeck χ hs)) χ.ker
      (show ThetaR χ hs from f) (QuotientGroup.mk g, p) = _
    rw [radDivFun_mk (actCompat_deckMero (G := G) (ρ := chiDeck χ hs) hval hs) hf.1
      ⟨1, one_pos, f, (pow_one _).symm⟩ (isLogRad_thetaR hs hf)
      (fun _ hh => smul_thetaR_of_mem_ker χ hs hh _)]
    have e : rEllDiv t s (show ThetaR χ hs from f) = ellDiv t s f :=
      rEllDiv_ι (R := ThetaR χ hs) hval hs hf.1
    rw [e]
    change ellDiv t s f (chiDeck χ hs g⁻¹ • (show EllPrime t from p)) =
      ellDiv t s f ((Deck.gen t hs) ^ (-labY (χ := χ) (QuotientGroup.mk g)) •
        (show EllPrime t from p))
    rw [labY_mk, chiDeck_apply, map_inv, toAdd_inv]

/-- `q^{1/2} = s ∈ B₀(Y)`. -/
def bOne : (thetaData χ hval hs).B₀.obj (objY hχ) :=
  thetaElt hval hs hχ (Mero.const (s : K)) (isLogMero_const s.ne_zero)

/-- `Ü ∈ B₀(Y)`. -/
def bU : (thetaData χ hval hs).B₀.obj (objY hχ) :=
  thetaElt hval hs hχ (Mero.ofE (Entire.mono 1)) isLogMero_mono

/-- **`Θ̈ ∈ B₀(Y)`** ([EtTh] Prop 1.4(i): zeros exactly at the cusps). -/
def bTheta : (thetaData χ hval hs).B₀.obj (objY hχ) :=
  thetaElt hval hs hχ (Mero.ofE (thetaDd t)) isLogMero_thetaDd

/-- A nonzero scalar `c ∈ B₀(Y)`. -/
def bConst {c : K} (hc : c ≠ 0) : (thetaData χ hval hs).B₀.obj (objY hχ) :=
  thetaElt hval hs hχ (Mero.const c) (isLogMero_const hc)

/-- **The theta monomial `q^{a/2} Ü^b Θ̈^{-c}`** in `B₀(Y)` (written additively). -/
def thetaMono (a b c : ℤ) : (thetaData χ hval hs).B₀.obj (objY hχ) :=
  a • bOne hval hs hχ + b • bU hval hs hχ - c • bTheta hval hs hχ

/-! ### Comparison with the former theta-monomial divisor group -/

variable (χ) in
/-- The divisors of shape `(a + b·j + c·j²)/2` on the component `n` (`j = n - χ(g)` its label
seen from the sheet `g`) and `-c` at every cusp (the former `B₀(Y)`). -/
def IsThetaShape (f : (G ⧸ χ.ker) × ThetaP χ hs → ℚ) (a b c : ℤ) : Prop :=
  (∀ (g : G) (n : ℤ), f (QuotientGroup.mk g, ThetaP.cmp χ hs n) =
      ((a + b * (n - (χ g).toAdd) + c * (n - (χ g).toAdd) ^ 2 : ℤ) : ℚ) / 2) ∧
    ∀ (x : G ⧸ χ.ker) (α : Cusp t), f (x, ThetaP.csp χ hs α) = -c

lemma div_thetaMono_apply (a b c : ℤ) (z : (G ⧸ χ.ker) × ThetaP χ hs) :
    ((thetaData χ hval hs).div₀.app (objY hχ) (thetaMono hval hs hχ a b c)).1 z =
      a * (ofDiv hs hχ (ellDiv t s (Mero.const (s : K)))).1 z +
        b * (ofDiv hs hχ (ellDiv t s (Mero.ofE (Entire.mono 1)))).1 z -
        c * (ofDiv hs hχ (ellDiv t s (Mero.ofE (thetaDd t)))).1 z := by
  rw [thetaMono, map_sub, map_add, map_zsmul, map_zsmul, map_zsmul, bOne, bU, bTheta,
    div_thetaElt, div_thetaElt, div_thetaElt]
  change a • (ofDiv hs hχ (ellDiv t s (Mero.const (s : K)))).1 z +
      b • (ofDiv hs hχ (ellDiv t s (Mero.ofE (Entire.mono 1)))).1 z -
      c • (ofDiv hs hχ (ellDiv t s (Mero.ofE (thetaDd t)))).1 z = _
  rw [zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul]

/-- **The divisor of the theta monomial `q^{a/2} Ü^b Θ̈^{-c}` has theta shape `(a, b, c)`.** -/
theorem isThetaShape_div_thetaMono (h2 : (2 : K) ≠ 0) (a b c : ℤ) :
    IsThetaShape χ hs ((thetaData χ hval hs).div₀.app (objY hχ) (thetaMono hval hs hχ a b c)).1
      a b c := by
  refine ⟨fun g n => ?_, fun x α => ?_⟩
  · rw [div_thetaMono_apply, ofDiv_cmp, ofDiv_cmp, ofDiv_cmp, ellDiv_const_s hs, ellDiv_mono hs,
      ellDiv_thetaDd h2 hs]
    simp only [Sum.elim_inl]
    push_cast
    ring
  · rw [div_thetaMono_apply, ofDiv_csp, ofDiv_csp, ofDiv_csp, ellDiv_const_s hs, ellDiv_mono hs,
      ellDiv_thetaDd h2 hs]
    simp

/-- **Every divisor of theta shape is the divisor of a theta monomial**: the former `B₀(Y)` is
the image of the theta monomials under `div₀`. -/
theorem eq_div_thetaMono_of_isThetaShape (h2 : (2 : K) ≠ 0)
    {f : PrimeDiv.divGp G (ThetaP χ hs) ℚ (objY hχ)} {a b c : ℤ}
    (hf : IsThetaShape χ hs f.1 a b c) :
    f = (thetaData χ hval hs).div₀.app (objY hχ) (thetaMono hval hs hχ a b c) := by
  obtain ⟨h1, h2'⟩ := isThetaShape_div_thetaMono hval hs hχ h2 a b c
  apply Subtype.ext
  funext ⟨x, p⟩
  induction x using QuotientGroup.induction_on with
  | H g =>
    rcases ThetaP.cases χ hs p with ⟨n, rfl⟩ | ⟨α, rfl⟩
    · rw [hf.1 g n, h1 g n]
    · rw [hf.2 _ α, h2' _ α]

/-! ### [EtTh] Prop 1.4(ii) in `B₀(Y)` -/

lemma rv_add' {H : Subgroup G} (x y : Additive (radSub t (R := ThetaR χ hs) H)) :
    rv (x + y) = rv x * rv y := rfl

lemma rv_zsmul' {H : Subgroup G} (n : ℤ) (x : Additive (radSub t (R := ThetaR χ hs) H)) :
    rv (n • x) = rv x ^ n := by
  change (((Additive.toMul x ^ n : radSub t (R := ThetaR χ hs) H) : (ThetaR χ hs)ˣ) :
    ThetaR χ hs) = _
  rw [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val]

lemma ofE_mono_eq_zpow (k : ℤ) :
    Mero.ofE (Entire.mono k : Entire K) = Mero.ofE (Entire.mono 1) ^ k := by
  have h0 : Mero.ofE (Entire.mono 1 : Entire K) ≠ 0 := Mero.ofE_ne_zero mono_one_ne_zero
  induction k using Int.induction_on with
  | zero => rw [Entire.mono_zero, Mero.ofE_one, zpow_zero]
  | succ k ih => rw [Entire.mono_add, Mero.ofE_mul, ih, zpow_add_one₀ h0]
  | pred k ih =>
    rw [zpow_sub_one₀ h0, ← ih, eq_mul_inv_iff_mul_eq₀ h0, ← Mero.ofE_mul, ← Entire.mono_add,
      sub_add_cancel]

lemma const_zpow (c : K) (n : ℤ) : Mero.const (c ^ n) = Mero.const c ^ n :=
  map_zpow₀ ((algebraMap (Entire K) (Mero K)).comp (algebraMap K (Entire K))) c n

lemma chi_rep_deck (d : G) : χ (rep (deck hχ d)) = χ d := by
  have h := mk_rep (deck hχ d)
  change (QuotientGroup.mk (rep (deck hχ d)) : G ⧸ χ.ker) = QuotientGroup.mk 1 * QuotientGroup.mk d
    at h
  rw [← QuotientGroup.mk_mul, one_mul] at h
  have := MonoidHom.mem_ker.mp (QuotientGroup.eq.mp h)
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this

include hs in
/-- [EtTh] Prop 1.4(ii) in `Mero K`: `Θ̈(s^{-a}Ü) = (-1)^{-a} Θ̈ Ü^{2a} s^{-a²}`. -/
lemma scale_thetaDd_mero (a : ℤ) :
    Mero.scale (s ^ (-a)) (Mero.ofE (thetaDd t)) =
      Mero.const ((-1 : K) ^ (-a)) * Mero.ofE (thetaDd t) *
        Mero.ofE (Entire.mono 1) ^ (2 * a) * Mero.const (s : K) ^ (-(a ^ 2)) := by
  rw [Mero.scale_ofE, scale_thetaDd t hs, Algebra.smul_def, map_mul, Mero.ofE_mul, Mero.ofE_mul,
    Mero.ofE_mul, ← const_zpow, ← ofE_mono_eq_zpow, neg_sq, show -(2 * -a) = 2 * a by ring]
  ring

/-- **[EtTh] Prop 1.4(ii) in `B₀(Y)`** (l.1324–1328): along the deck transformation `τ_d` of `Y`
(`a = χ(d)`), the pull-back of `Θ̈` is `Θ̈(s^{-a}Ü) = (-1)^{-a} · Θ̈ · Ü^{2a} · q^{-a²/2}`. -/
theorem pb_deck_bTheta (d : G) :
    (thetaData χ hval hs).B₀.pb (deck hχ d) (bTheta hval hs hχ) =
      bConst hval hs hχ (zpow_ne_zero (-(χ d).toAdd) (by norm_num : (-1 : K) ≠ 0)) +
        bTheta hval hs hχ + (2 * (χ d).toAdd) • bU hval hs hχ +
        (-((χ d).toAdd ^ 2)) • bOne hval hs hχ := by
  apply rv_injective
  erw [rv_add', rv_add', rv_add', rv_zsmul', rv_zsmul']
  change rep (deck hχ d) • (show ThetaR χ hs from Mero.ofE (thetaDd t)) = _
  change Mero.scale (((chiDeck χ hs (rep (deck hχ d)))⁻¹ : Deck t) : Kˣ)
    (Mero.ofE (thetaDd t)) = _
  rw [chiDeck_apply, chi_rep_deck, ← zpow_neg, Subgroup.coe_zpow]
  exact scale_thetaDd_mero hs _

/-- **[EtTh] Prop 1.4(ii), divisor form**: `τ_d^* div(Θ̈) = div(Θ̈) + 2a·div(Ü) - a²·div(√q)`. -/
theorem div_pb_deck_bTheta (d : G) :
    (thetaData χ hval hs).Φ₀.toGrpOn.pb (deck hχ d)
        ((thetaData χ hval hs).div₀.app (objY hχ) (bTheta hval hs hχ)) =
      (thetaData χ hval hs).div₀.app (objY hχ) (bTheta hval hs hχ) +
        (2 * (χ d).toAdd) • (thetaData χ hval hs).div₀.app (objY hχ) (bU hval hs hχ) -
        ((χ d).toAdd ^ 2) • (thetaData χ hval hs).div₀.app (objY hχ) (bOne hval hs hχ) := by
  rw [← (thetaData χ hval hs).div₀.natural, pb_deck_bTheta, map_add, map_add, map_add,
    map_zsmul, map_zsmul, bConst, div_thetaElt,
    ellDiv_const (zpow_ne_zero _ (by norm_num : (-1 : K) ≠ 0)) (m := 0) (by
      rw [norm_zpow, norm_neg, norm_one, one_zpow, Real.logb_one]; simp)]
  have h0 : ofDiv hs hχ (Sum.elim (fun _ => (0 : ℚ)) fun _ => 0 : EllPrime t → ℚ) = 0 := by
    apply Subtype.ext
    funext ⟨x, p⟩
    rcases p with n | α <;> rfl
  rw [h0]
  change (0 : PrimeDiv.divGp G (ThetaP χ hs) ℚ (objY hχ)) + _ + _ + _ = _
  rw [zero_add, neg_smul, sub_eq_add_neg]
  rfl

end Theta

/-! ### The tempered fundamental group of the Tate curve -/

section Tate

open TemperedFundamentalGroups

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A] (T : TateObject.Data O R)
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

variable {𝕂 : Type u} [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂] [IsUltrametricDist 𝕂]
  {t : TateCurvesTheta.TateParameter 𝕂} {s : 𝕂ˣ} (hval : BAn.ValueGroupRat t)
  (hs : (s : 𝕂) ^ 2 = t.q)

/-- **The theta tempered Frobenioid of the Tate curve**: `D₀ = B^temp(Π^tp_X)⁰` for the tempered
fundamental group `Π^tp_X = temperedPi1 O R A V hV` of `tempered-fundamental-groups`, `Φ₀` the
`ℚ`-divisors on the elliptic prime set and `B₀` the log-meromorphic functions on the analytic
model `Ÿ_∞ = 𝔾_m^an` over `𝕂`, `Π^tp_X` acting through its `ℤ`-quotient
`TateObject.character` (the identification of `t` with the Tate parameter of `T`, and of the
full `Π^tp_X`-action, is MR18 T7c). -/
abbrev tateThetaData : TemperedFrobenioidData (temperedPi1 O R A V hV) :=
  thetaData (TateObject.character (A := A) T V hV) hval hs

/-- **The theta tempered Frobenioid of the Tate curve is a Frobenioid.** -/
theorem tateThetaData_isFrobenioid :
    IsFrobenioid (Model.toElem (tateThetaData T V hV hval hs).Φ₀
      (tateThetaData T V hV hval hs).B₀ (tateThetaData (A := A) T V hV hval hs).div₀) :=
  (tateThetaData T V hV hval hs).isFrobenioid

end Tate

end Iut.Frobenioid
